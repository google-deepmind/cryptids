/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.SharedDonorsA

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RB1LD_0RC1RC_1LA1RE_HHH1LE_1RF0RC_0RB0LF


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_0RC1RC_1LA1RE_HHH1LE_1RF0RC_0RB0LF"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


open BusyBeaver.Counter
open TM1Donor

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

set_option maxRecDepth 2000000
-- 5. Stem `init [] ⊢* Kr 979 17 34 22 9`, Transient to `Ev 6431 20`, and Goal
-- ============================================================================

def symInit : SymState := ⟨.q0, .right, [], [], false⟩

def stem_mid0 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 8 .v0, SymTok.b0,
      SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.pow .w11 1 .v0])

theorem stem_cert0 : checkSym false 6303 symInit stem_mid0 = true := by
  decide

def symKr979 : SymState :=
  mkSymKr (
    segConst (G ++ [1]) 979 ++
    segConst [0] 17 ++
    segConst [0, 1, 1, 0] 34 ++
    segConst [0, 0, 0, 0, 0, 0, 1] 22 ++
    segConst [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 ++
    krTailToks)

def stem_mid1 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 186 .v0, SymTok.b0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 5 .v0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 13 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.pow .w11 6 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1])

def stem_mid2 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 311 .v0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.pow .w11 17 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0,
      SymTok.pow .w11 19 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 1 .v0])

def stem_mid3 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 435 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1,
      SymTok.pow .w11 37 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1,
      SymTok.pow .w11 9 .v0])

def stem_mid4 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 558 .v0, SymTok.b0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 16 .v0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 22 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 10 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 6 .v0,
      SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1,
      SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid5 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 681 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1,
      SymTok.pow .w11 65 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.b1, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1])

def stem_mid6 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 792 .v0, SymTok.b0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 46 .v0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.pow .w11 17 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0,
      SymTok.pow .w11 10 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 9 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid7 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 885 .v0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 32 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.b1, SymTok.pow .w11 24 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b0, SymTok.pow .w11 24 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.pow .w11 6 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid8 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 970 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 16 .v0, SymTok.b0,
      SymTok.b0, SymTok.pow .w11 36 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1,
      SymTok.pow .w11 21 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0,
      SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 9 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1,
      SymTok.pow .w11 1 .v0])

theorem stem_cert1 : checkMid true 8499 stem_mid0 stem_mid1 = true := by
  decide

theorem stem_cert2 : checkMid true 8465 stem_mid1 stem_mid2 = true := by
  decide

theorem stem_cert3 : checkMid true 8493 stem_mid2 stem_mid3 = true := by
  decide

theorem stem_cert4 : checkMid true 8477 stem_mid3 stem_mid4 = true := by
  decide

theorem stem_cert5 : checkMid true 8431 stem_mid4 stem_mid5 = true := by
  decide

theorem stem_cert6 : checkMid true 8422 stem_mid5 stem_mid6 = true := by
  decide

theorem stem_cert7 : checkMid true 8286 stem_mid6 stem_mid7 = true := by
  decide

theorem stem_cert8 : checkMid true 8494 stem_mid7 stem_mid8 = true := by
  decide

theorem stem_cert_end : checkSym true 226 stem_mid8 symKr979 = true := by
  decide


theorem init_to_kr979 : (init []) [tm1]⊢* Kr 979 17 34 22 9 := by
  have h :=
      stepPlus_stepStar (stepStar_stepPlus_trans (stepPlus_stepStar (checkSym_sound 0 0 0 0 0
      stem_cert0)) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert1)
      (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert2) (stepStar_stepPlus_trans
      (checkMid_sound 0 0 0 0 0 stem_cert3) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0
      stem_cert4) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert5)
      (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert6) (stepStar_stepPlus_trans
      (checkMid_sound 0 0 0 0 0 stem_cert7) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0
      stem_cert8) (checkSym_sound 0 0 0 0 0 stem_cert_end))))))))))
  have h1 : evalState 0 0 0 0 0 symInit = init [] := rfl
  have h2 : evalState 0 0 0 0 0 symKr979 = Kr 979 17 34 22 9 := by
    simp only [symKr979, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segConst, evalHalf_map_bit_end, evalHalf,
      listblank_append_assoc]
  rwa [h1, h2] at h

theorem kr979_to_ev : (Kr 979 17 34 22 9) [tm1]⊢* Ev 6431 20 :=
  stepStar_trans (S_iter 4 979 0 31 19 8) <|
  stepStar_trans (stepPlus_stepStar (TO 1075 1 4 8)) <|
  stepStar_trans (S_iter 4 1369 2 45 14 8) <|
  stepStar_trans (stepPlus_stepStar (T6 1465 15 0 8)) <|
  stepStar_trans (S_iter 6 1761 3 45 14 8) <|
  stepStar_trans (stepPlus_stepStar (T8 1905 16 11)) <|
  stepStar_trans (S_iter 5 2175 2 40 41 8) <|
  stepStar_trans (stepPlus_stepStar (T6 2295 12 27 10)) <|
  stepStar_trans (S_iter 12 2591 3 47 14 8) <|
  stepStar_trans (stepPlus_stepStar (T8 2879 30 23)) <|
  stepStar_trans (S_iter 9 3149 0 40 53 8) <|
  stepStar_trans (stepPlus_stepStar (TO 3365 20 38 18)) <|
  stepStar_trans (S_iter 17 3659 3 55 14 8) <|
  stepStar_trans (stepPlus_stepStar (T8 4067 48 33)) <|
  stepStar_trans (S_iter 13 4337 2 40 63 8) <|
  stepStar_trans (stepPlus_stepStar (T6 4649 28 49 26)) <|
  stepStar_trans (S_iter 22 4945 1 63 14 8) <|
  stepStar_trans (stepPlus_stepStar (TE 5473 66 43)) <|
  stepStar_trans (S_iter 16 5751 2 38 75 8) <|
  stepPlus_stepStar (T6 6135 32 61 32)

theorem init_to_ev : (init []) [target_tm]⊢* Ev 6431 20 :=
  stepStar_trans init_to_kr979 kr979_to_ev


theorem is_does_not_halt : IsNotHalt target_tm := by
  refine IsNotHalt.of_reachesPlus_invariant (P := Inv) init_to_ev ⟨6431, 20, rfl⟩ ?_
  rintro _ ⟨N, X, rfl⟩
  exact ⟨Ev (48 * X + 716 + N) (4 + X), DC N X, 48 * X + 716 + N, 4 + X, rfl⟩

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB1LD_0RC1RC_1LA1RE_HHH1LE_1RF0RC_0RB0LF
