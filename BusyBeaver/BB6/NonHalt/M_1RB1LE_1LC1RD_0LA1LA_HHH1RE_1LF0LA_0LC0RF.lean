module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.SharedDonorsA

open Mathlib Relation Nat Turing BusyBeaver SixState

@[expose] public section

namespace BusyBeaver.M_1RB1LE_1LC1RD_0LA1LA_HHH1RE_1LF0LA_0LC0RF

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1LC1RD_0LA1LA_HHH1RE_1LF0LA_0LC0RF"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RB1LE_1LC1RD_0LA1LA_HHH1RE_1LF0LA_0LC0RF

end

namespace BusyBeaver.M_1RB1LE_1LC1RD_0LA1LA_HHH1RE_1LF0LA_0LC0RF

open BusyBeaver.Counter
open TM1Donor

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

set_option maxRecDepth 2000000
def phi : Fin 6 → Fin 6
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5

def mirrorCfg (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map phi, ⟨c.tape.1, c.tape.3, c.tape.2⟩⟩

theorem step_mirrorCfg (c : Cfg (Fin 2) (Fin 6)) :
    step tm1 (mirrorCfg c) = (step target_tm c).map mirrorCfg := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q, hq⟩, ⟨⟨_ | _ | h, hh⟩, l, r⟩⟩ <;>
    first | rfl | omega

theorem multiStep_mirrorCfg (n : Nat) (c : Cfg (Fin 2) (Fin 6)) :
    multiStep tm1 (mirrorCfg c) n = (multiStep target_tm c n).map mirrorCfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [multiStep_succ, multiStep_succ, step_mirrorCfg]
    rcases step target_tm c with _ | c'
    · rfl
    · exact ih c'

theorem reachesStar_mirrorCfg {c c' : Cfg (Fin 2) (Fin 6)}
    (h : c [target_tm]⊢* c') :
    (mirrorCfg c) [tm1]⊢* (mirrorCfg c') := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [multiStep_mirrorCfg, hn]
  rfl

theorem isSome_step_of_mirrorCfg {c : Cfg (Fin 2) (Fin 6)}
    (h : (step tm1 (mirrorCfg c)).isSome) :
    (step target_tm c).isSome := by
  rw [step_mirrorCfg, Option.isSome_map] at h
  exact h

def initC : Cfg (Fin 2) (Fin 6) :=
  (default : ListBlank (Fin 2)) {{(2 : Fin 6)}}> default

theorem mirrorCfg_init : mirrorCfg (init []) = initC :=
  rfl

-- 5. Stem `initC ⊢* Kr 976 17 34 22 9`, Transient to `Ev 6428 20`, and Goal
-- ============================================================================

def symInitC : SymState := ⟨.q2, .right, [], [], false⟩

def stem_mid0 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 11 .v0, SymTok.b0,
      SymTok.pow .w11 4 .v0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.pow .w11 2 .v0,
      SymTok.b0, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.pow .w11 1 .v0])

theorem stem_cert0 : checkSym false 5986 symInitC stem_mid0 = true := by
  decide

def symKr976 : SymState :=
  mkSymKr (
    segConst (G ++ [1]) 976 ++
    segConst [0] 17 ++
    segConst [0, 1, 1, 0] 34 ++
    segConst [0, 0, 0, 0, 0, 0, 1] 22 ++
    segConst [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 ++
    krTailToks)

def stem_mid1 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 167 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 10 .v0, SymTok.b0,
      SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b0, SymTok.b1, SymTok.pow .w11 9 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0,
      SymTok.pow .w11 4 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 1 .v0])

def stem_mid2 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 281 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 20 .v0, SymTok.b0,
      SymTok.b0, SymTok.pow .w11 14 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid3 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 401 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 32 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 9 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b1, SymTok.pow .w11 7 .v0, SymTok.b0, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid4 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 539 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 20 .v0, SymTok.b0,
      SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b0, SymTok.b1, SymTok.pow .w11 17 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0,
      SymTok.pow .w11 11 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid5 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 653 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0,
      SymTok.pow .w11 28 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.pow .w11 38 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0,
      SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid6 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 775 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 48 .v0, SymTok.b0,
      SymTok.b0, SymTok.pow .w11 20 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1,
      SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 9 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 10 .v0])

def stem_mid7 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 870 .v0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 34 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 23 .v0, SymTok.b0,
      SymTok.pow .w11 22 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.pow .w11 4 .v0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1])

def stem_mid8 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 955 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 18 .v0, SymTok.b0,
      SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b0, SymTok.b1, SymTok.pow .w11 31 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0,
      SymTok.pow .w11 22 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.pow .w11 9 .v0])

theorem stem_cert1 : checkMid true 8266 stem_mid0 stem_mid1 = true := by
  decide

theorem stem_cert2 : checkMid true 8218 stem_mid1 stem_mid2 = true := by
  decide

theorem stem_cert3 : checkMid true 8330 stem_mid2 stem_mid3 = true := by
  decide

theorem stem_cert4 : checkMid true 8520 stem_mid3 stem_mid4 = true := by
  decide

theorem stem_cert5 : checkMid true 8239 stem_mid4 stem_mid5 = true := by
  decide

theorem stem_cert6 : checkMid true 8570 stem_mid5 stem_mid6 = true := by
  decide

theorem stem_cert7 : checkMid true 8210 stem_mid6 stem_mid7 = true := by
  decide

theorem stem_cert8 : checkMid true 8598 stem_mid7 stem_mid8 = true := by
  decide

theorem stem_cert_end : checkSym true 1347 stem_mid8 symKr976 = true := by
  decide

theorem initC_to_kr976 : initC [tm1]⊢* Kr 976 17 34 22 9 := by
  have h :=
      stepPlus_stepStar (stepStar_stepPlus_trans (stepPlus_stepStar (checkSym_sound 0 0 0 0 0
      stem_cert0)) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert1)
      (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert2) (stepStar_stepPlus_trans
      (checkMid_sound 0 0 0 0 0 stem_cert3) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0
      stem_cert4) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert5)
      (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert6) (stepStar_stepPlus_trans
      (checkMid_sound 0 0 0 0 0 stem_cert7) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0
      stem_cert8) (checkSym_sound 0 0 0 0 0 stem_cert_end))))))))))
  have h1 : evalState 0 0 0 0 0 symInitC = initC := rfl
  have h2 : evalState 0 0 0 0 0 symKr976 = Kr 976 17 34 22 9 := by
    simp only [symKr976, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segConst, evalHalf_map_bit_end, evalHalf,
      listblank_append_assoc]
  rwa [h1, h2] at h

theorem kr976_to_ev : (Kr 976 17 34 22 9) [tm1]⊢* Ev 6428 20 :=
  stepStar_trans (S_iter 4 976 0 31 19 8) <|
  stepStar_trans (stepPlus_stepStar (TO 1072 1 4 8)) <|
  stepStar_trans (S_iter 4 1366 2 45 14 8) <|
  stepStar_trans (stepPlus_stepStar (T6 1462 15 0 8)) <|
  stepStar_trans (S_iter 6 1758 3 45 14 8) <|
  stepStar_trans (stepPlus_stepStar (T8 1902 16 11)) <|
  stepStar_trans (S_iter 5 2172 2 40 41 8) <|
  stepStar_trans (stepPlus_stepStar (T6 2292 12 27 10)) <|
  stepStar_trans (S_iter 12 2588 3 47 14 8) <|
  stepStar_trans (stepPlus_stepStar (T8 2876 30 23)) <|
  stepStar_trans (S_iter 9 3146 0 40 53 8) <|
  stepStar_trans (stepPlus_stepStar (TO 3362 20 38 18)) <|
  stepStar_trans (S_iter 17 3656 3 55 14 8) <|
  stepStar_trans (stepPlus_stepStar (T8 4064 48 33)) <|
  stepStar_trans (S_iter 13 4334 2 40 63 8) <|
  stepStar_trans (stepPlus_stepStar (T6 4646 28 49 26)) <|
  stepStar_trans (S_iter 22 4942 1 63 14 8) <|
  stepStar_trans (stepPlus_stepStar (TE 5470 66 43)) <|
  stepStar_trans (S_iter 16 5748 2 38 75 8) <|
  stepPlus_stepStar (T6 6132 32 61 32)

theorem initC_to_ev : initC [tm1]⊢* Ev 6428 20 :=
  stepStar_trans initC_to_kr976 kr976_to_ev


theorem neverHalts_ev6428 : NeverHaltsFrom tm1 (Ev 6428 20) := by
  refine NeverHaltsFrom.of_reachesPlus_invariant (P := Inv) ?_ ⟨6428, 20, rfl⟩
  rintro _ ⟨N, X, rfl⟩
  exact ⟨Ev (48 * X + 716 + N) (4 + X), DC N X, 48 * X + 716 + N, 4 + X, rfl⟩

theorem neverHalts_initC : NeverHaltsFrom tm1 initC := by
  obtain ⟨k₀, hk₀⟩ := initC_to_ev
  intro cfg ⟨k, hk⟩
  rcases Nat.lt_or_ge k k₀ with hlt | hge
  · rcases hstep_cfg : step tm1 cfg with _ | _
    · have hnone : (step tm1 cfg).isNone := by simp [hstep_cfg]
      have hnone_k₀ : multiStep tm1 initC k₀ = none := by
        have hsplit : k₀ = k + (k₀ - k) := by omega
        rw [hsplit]
        exact multiStep_eq_none_of_isNone hk hnone (by omega)
      rw [hnone_k₀] at hk₀
      cases hk₀
    · rfl
  · have hsplit : k = k₀ + (k - k₀) := by omega
    rw [hsplit, multiStep_add, hk₀, Option.bind_some] at hk
    exact neverHalts_ev6428 cfg ⟨k - k₀, hk⟩



theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg hreach
  apply isSome_step_of_mirrorCfg
  have hmir := reachesStar_mirrorCfg hreach
  rw [mirrorCfg_init] at hmir
  exact neverHalts_initC (mirrorCfg cfg) hmir

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB1LE_1LC1RD_0LA1LA_HHH1RE_1LF0LA_0LC0RF
