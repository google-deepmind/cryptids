/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.HaltShared

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

@[simp] theorem isFlipped_tm : BusyBeaver.RleStackEngine.isFlipped target_tm = false := rfl

namespace Solution

open BusyBeaver.RleStackEngine

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def F : Fin 6 := 5

@[simp] theorem init_nil : (init ([] : List (Fin 2))) = ⟨some A, ⟨0, default, default⟩⟩ := rfl

def cfg_Halt (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some F, ⟨1, l, r⟩⟩

macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, listblank_append_cons,
    listblank_append_nil, zero_cons_default, encLeft_nil, encRight_nil, encLeft_cons_one,
    encRight_cons_one, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, multiStep_zero]
  try rfl))
macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, listblank_append_cons,
    listblank_append_nil, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head]
  apply step_stepStar_stepPlus (by rfl)
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
    listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
    Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail]))
macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

theorem init_reaches_stack : (init []) [target_tm]⊢⁺ (cfg_B target_tm [0] []) := by
  rw [init_nil]; unfold cfg_B; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_zero, encLeft_nil, encRight_nil]; execute 1

theorem rule_B_nil (L : List ℕ) :
    (cfg_B target_tm L []) [target_tm]⊢⁺ (cfg_C target_tm (bumpHead L) []) := by
  unfold cfg_B cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_nil]; execute 1

theorem rule_B_zero (L R : List ℕ) :
    (cfg_B target_tm L (0 :: R)) [target_tm]⊢⁺ (cfg_B target_tm (0 :: L) R) := by
  unfold cfg_B; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_zero R, encLeft_zero L];
      execute 4

theorem rule_B_succ (d : ℕ) (L R : List ℕ) :
    (cfg_B target_tm L ((d + 1) :: R)) [target_tm]⊢⁺ (cfg_BR target_tm L (0 :: d :: R)) := by
  unfold cfg_B cfg_BR; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_succ d R, encRight_zero (d :: R), encRight_expose d R]; execute 2

theorem rule_BR_nil (L : List ℕ) :
    (cfg_BR target_tm L []) [target_tm]⊢⁺ (cfg_C target_tm (bumpHead L) []) :=
  rule_B_nil L

theorem rule_BR_zero (L R : List ℕ) :
    (cfg_BR target_tm L (0 :: R)) [target_tm]⊢⁺ (cfg_BR target_tm (0 :: L) R) := by
  unfold cfg_BR; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_zero R, encLeft_zero L];
      execute 2

theorem rule_BR_one (L R : List ℕ) :
    (cfg_BR target_tm L (1 :: R)) [target_tm]⊢⁺ (cfg_DR0 target_tm L (bumpHead R)) := by
  unfold cfg_BR cfg_DR0; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_succ 0 R,
      encRight_zero R]; execute 4

theorem rule_BR_add_two (d : ℕ) (L R : List ℕ) :
    (cfg_BR target_tm L ((d + 2) :: R)) [target_tm]⊢⁺ (cfg_B target_tm (bumpHead L) (d :: R)) :=
        by
  unfold cfg_BR cfg_B; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encRight_succ (d + 1) R, encRight_succ d R, encRight_expose d R]; execute 5

theorem rule_DR0_nil (R : List ℕ) :
    (cfg_DR0 target_tm [] R) [target_tm]⊢⁺ (cfg_C target_tm [1] R) := by
  unfold cfg_DR0 cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_nil, encLeft_succ 0 [], encLeft_zero [], encLeft_nil]; execute 3

theorem rule_DR0_zero (L R : List ℕ) :
    (cfg_DR0 target_tm (0 :: L) R) [target_tm]⊢⁺ (cfg_DR0 target_tm L (0 :: R)) := by
  unfold cfg_DR0; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_zero L, encRight_zero R];
      execute 4

theorem rule_DR0_succ (a : ℕ) (L R : List ℕ) :
    (cfg_DR0 target_tm ((a + 1) :: L) R) [target_tm]⊢⁺ (cfg_C target_tm (a :: L) (0 :: R)) := by
  unfold cfg_DR0 cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_succ a L,
      encRight_zero R]; execute 3

theorem rule_C_nil (R : List ℕ) :
    (cfg_C target_tm [] R) [target_tm]⊢⁺ (cfg_DR0 target_tm [] R) := by
  unfold cfg_C cfg_DR0; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_nil]; execute 1

theorem rule_C_zero_nil (R : List ℕ) :
    (cfg_C target_tm [0] R) [target_tm]⊢⁺ (cfg_C target_tm [] (1 :: R)) := by
  unfold cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_zero [], encLeft_nil, encRight_succ 0 R, encRight_zero R]; execute 3

theorem rule_C_zero_zero (L R : List ℕ) :
    (cfg_C target_tm (0 :: 0 :: L) R) [target_tm]⊢⁺ (cfg_C target_tm (bumpHead L) (1 :: R)) := by
  unfold cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_zero (0 :: L), encLeft_zero L, encRight_succ 0 R, encRight_zero R]; execute 5

theorem rule_C_zero_one (L R : List ℕ) :
    (cfg_C target_tm (0 :: 1 :: L) R) [target_tm]⊢⁺
    (cfg_C target_tm (bumpHead (bumpHead L)) (0 :: bumpHead R)) := by
  unfold cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_zero (1 :: L), encLeft_succ 0 L, encLeft_zero L, encRight_zero (bumpHead R)]
  execute 17

theorem rule_C_zero_add_two (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (0 :: (a + 2) :: L) R) [target_tm]⊢⁺ (cfg_BR target_tm (a :: L) (0 :: 1 ::
        R)) := by
  unfold cfg_C cfg_BR; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_zero ((a + 2) :: L), encLeft_succ (a + 1) L, encLeft_succ a L,
    encRight_zero (1 :: R), encRight_succ 0 R, encRight_zero R]; execute 4

theorem rule_C_one_nil (R : List ℕ) :
    (cfg_C target_tm [1] R) [target_tm]⊢⁺ (cfg_B target_tm [0] (1 :: R)) := by
  unfold cfg_C cfg_B; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_succ 0 [], encLeft_zero [], encLeft_nil, encRight_succ 0 R, encRight_zero R]
  execute 5

theorem rule_C_one_zero (L R : List ℕ) :
    (cfg_C target_tm (1 :: 0 :: L) R) [target_tm]⊢⁺ (cfg_DR0 target_tm L (2 :: R)) := by
  unfold cfg_C cfg_DR0; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_succ 0 (0 :: L), encLeft_zero (0 :: L), encLeft_zero L,
    encRight_succ 1 R, encRight_succ 0 R, encRight_zero R]; execute 7

theorem rule_C_one_succ (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm (1 :: (a + 1) :: L) R) [target_tm]⊢⁺ (cfg_C target_tm (a :: L) (2 :: R)) :=
        by
  unfold cfg_C; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_succ 0 ((a + 1) :: L), encLeft_zero ((a + 1) :: L), encLeft_succ a L,
    encRight_succ 1 R, encRight_succ 0 R, encRight_zero R]; execute 6

theorem rule_C_add_two_step (a : ℕ) (L R : List ℕ) :
    (cfg_C target_tm ((a + 2) :: L) R) [target_tm]⊢⁺
    (cfg_Halt ((([1] : List (Fin 2)) ^ a) +> ((encLeft1 L).cons 0))
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight1 R)) := by
  unfold cfg_C cfg_Halt; dsimp only [isFlipped_tm, ite_true, ite_false]
  rw [encLeft_succ (a + 1) L, encLeft_succ a L, encLeft_expose a L]; execute 3

theorem rule_C_add_two_halt (a : ℕ) (L R : List ℕ) :
    ∃ cfg', ((cfg_C target_tm ((a + 2) :: L) R) [target_tm]⊢⁺ cfg') ∧
      (step target_tm cfg').isNone :=
  ⟨cfg_Halt ((([1] : List (Fin 2)) ^ a) +> ((encLeft1 L).cons 0))
    ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight1 R),
   rule_C_add_two_step a L R, rfl⟩


instance : HasRleStackRules target_tm where
  rule_B_nil := rule_B_nil
  rule_B_zero := rule_B_zero
  rule_B_succ := rule_B_succ
  rule_BR_nil := rule_BR_nil
  rule_BR_zero := rule_BR_zero
  rule_BR_one := rule_BR_one
  rule_BR_add_two := rule_BR_add_two
  rule_DR0_nil := rule_DR0_nil
  rule_DR0_zero := rule_DR0_zero
  rule_DR0_succ := rule_DR0_succ
  rule_C_nil := rule_C_nil
  rule_C_zero_nil := rule_C_zero_nil
  rule_C_zero_zero := rule_C_zero_zero
  rule_C_zero_one := rule_C_zero_one
  rule_C_zero_add_two := rule_C_zero_add_two
  rule_C_one_nil := rule_C_one_nil
  rule_C_one_zero := rule_C_one_zero
  rule_C_one_succ := rule_C_one_succ
  rule_C_add_two_halt := rule_C_add_two_halt

def ckpt0 : RleFullState := ⟨.B, .raw [.z 1], [], false⟩

def ckpt5 : RleFullState := ⟨.B, .clean 0 [(10160322, 1), (2037954, 13), (2824386, 1619), (3086530
    , 1), (3610818, 3653), (2037954, 1), (25368770, 1), (42145986, 2872), (58923202, 1), (92477634
    , 812), (12785858, 1), (1275271362, 28), (3666548930, 1), (5101263042, 71), (15178199234, 1),
    (20405054658, 116), (25977842882, 1), (81620331714, 22), (248318268209, 1), (300302521103, 1)]
    3842700283260, [.z 1, .k 8126655 6, .k 2031599 1, .k 2031615 34318, .k 1507327 1, .k 1245183
    24417, .k 2031615 1, .k 458751 473610, .k 196607 1, .k 65535 2829536, .k 3071 1, .k 7167
    3190216, .k 3071 1, .k 1023 323903800, .k 511 1, .k 255 4583538500, .k 127 1, .k 63
    26276947360, .k 31 1, .k 15 56657308304, .z 3, .d 1, .z 2, .d 2, .d 1, .k 3 133852318911, .z 3
    , .d 3, .d 1, .k 0 56344583818, .d 2], false⟩

def ckpt10 : RleFullState := ⟨.C, .raw [.z 1, .k 20401242237 24417, .k 24696209533 1, .k
    33286144125 34307, .k 41607680637 1, .k 8321537661 9, .k 8321472125 1, .k 33286821501 6, .k
    41616709245 1, .k 8347489917 13, .k 11568715389 1619, .k 12642457213 1, .k 14789940861 3653,
    .k 8347489917 1, .k 103910512253 1, .k 172629988989 2872, .k 241349465725 1, .k 378788419197
    812, .k 52370904701 1, .k 5223511529085 28, .k 15018184447613 1, .k 20894773450365 71, .k
    62169904092797 1, .k 83579103909501 27, .k 233893724569877 1, .k 334316415637929 88, .k
    425620977899945 1, .k 1337267514923433 4, .k 110188252487541 1, .k 19633268198974271 1, .z 2]
    , [.k 33286144125 1, .k 7516340349 473610, .k 3221373053 1, .k 1073889405 2829536, .k 50479229
    1, .k 117588093 3190216, .k 50479229 1, .k 16924797 323903800, .k 8536189 1, .k 4341885
    1304636057, .k 1720010 1, .k 1085472 3278902442, .k 561184 1, .k 299040 16080887479, .k 283151
    1, .k 74763 10196059880, .k 41995 1, .k 25611 49220528784, .k 22411 1, .k 223 1, .k 1623
    7436779519, .k 791 1, .k 663 190196902731, .k 535 1, .k 471 91416876092, .k 279 3607090573272
    , .k 151 1, .k 87 1247148618371, .k 55 1, .k 39 8777991210832, .k 31 1, .k 27 41052276700161,
    .k 87 1, .k 69 68860916608490, .k 117 1, .k 21 65433277186752, .k 8 1, .k 6 78474749496209, .k
    4 1, .k 3 9575881408811365, .k 6 1, .k 0 1295188808094044, .d 2], false⟩

def ckpt15 : RleFullState := ⟨.B, .clean 0 [(26230647, 49220528784), (43007863, 1), (76562295,
    10196059880), (289951607, 1), (306221943, 16080887479), (574657399, 1), (1111528311,
    3278902442), (1761295223, 1), (4446095223, 285528470), (10774804343, 1), (17784372087,
    1019107586), (34964241271, 1), (69323979639, 323903800), (206762933111, 1), (481640840055,
    3190216), (206762933111, 1), (4398651014007, 2829536), (13194744036215, 1), (30786930080631,
    473610), (136340046347127, 1), (83563488213879, 24417), (101155674258295, 1), (136340046347127
    , 34307), (170425059900279, 1), (34085018270583, 9), (34084749835127, 1), (136342820879223, 6)
    , (170462041078647, 1), (34191318711159, 13), (47385458244471, 1619), (51783504755575, 1),
    (60579597777783, 3653), (34191318711159, 1), (425617458199415, 1), (707092434910071, 2872),
    (988567411620727, 1), (1551517365042039, 812), (214511225666423, 1), (21395503223143287, 28),
    (61514483497433975, 1), (85584992052706167, 71), (254647927164107639, 1), (342340009613327223
    , 27), (958028695838227319, 1), (1369360038452968311, 31), (82168436419292535, 1),
    (20595065632538812535, 1), (21909760615247478903, 43), (7991561740213130739, 1),
    (222691182000549570631, 1), (63, 1), (5608898717503354593279, 1)] 2468328002243313095983, [.d
    1, .d 1, .k 5738461 1, .k 58333 1, .k 416733 7436779519, .k 203741 1, .k 170973 190196902731,
    .k 138205 1, .k 121821 91416876092, .k 72669 3607090573272, .k 39901 1, .k 23517 1247148618371
    , .k 15325 1, .k 11229 8777991210832, .k 9181 1, .k 8157 41052276700161, .k 23517 1, .k 18909
    31671798164438, .k 14813 1, .k 4701 37189118444051, .k 7773 1, .k 1629 65433277186752, .k 797
    1, .k 669 78474749496209, .k 541 1, .k 477 9575881408811365, .k 669 1, .k 285
    17162295816727413, .k 477 1, .k 93 246018113982395612, .k 61 1, .k 45 631165860194629366, .k
    32 1, .k 12 4791268012535596513, .k 10 1, .k 9 22342849281290009221, .k 12 1, .k 6
    7588671874192736443, .k 9 1, .k 3 108596472271926337351, .k 6 1, .k 0 206332718429699986606,
    .d 2], false⟩

-- Each chunk reduces 100 (or 80) RLE batches in the kernel via `rfl`.
set_option maxRecDepth 2000000 in
theorem chunk_0 : runBatches 100 ckpt0 = ckpt5 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_1 : runBatches 100 ckpt5 = ckpt10 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_2 : runBatches 100 ckpt10 = ckpt15 := rfl
set_option maxRecDepth 2000000 in
theorem chunk_3 : (runBatches 80 ckpt15).halted = true := rfl

theorem reach_15 : StateHalts target_tm ckpt15 :=
  runBatches_halts 80 ckpt15 (Or.inl chunk_3)
theorem reach_10 : StateHalts target_tm ckpt10 := chunk_back_batches chunk_2 reach_15
theorem reach_5 : StateHalts target_tm ckpt5 := chunk_back_batches chunk_1 reach_10
theorem reach_0 : StateHalts target_tm ckpt0 := chunk_back_batches chunk_0 reach_5

end Solution

public section

open Solution BusyBeaver.RleStackEngine in
theorem is_halt : IsHalt target := by
  rcases reach_0 with hfalse | hcan
  · simp [ckpt0] at hfalse
  · exact canHalt_of_stepPlus init_reaches_stack hcan

end

end BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH
