/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.SharedDonorsA

open Mathlib Relation Nat Turing BusyBeaver SixState


namespace BusyBeaver.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end


open BusyBeaver.Excursion
open M240

abbrev target_tm : Machine (Fin 2) (Fin 6) := target



variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

theorem fixed64 (Lrem : T) :
    (K qA (([0, 1, 1] : List (Fin 2)) ^ 4 +> Lrem) 0 default) [tm]⊢^{64}
      K qB (([1] : List (Fin 2)) ^ 10 +> Lrem) 1 (([1] : List (Fin 2)) ^ 4 +> default) := by
  run_steps 64

theorem bev3_nil_to_bodd0 :
    (Bev 3 [] 3 [4]) [tm]⊢⁺ Bodd 0 [] 9 [] := by
  unfold Bev Bodd
  rw [encL_nil, show (([1] : List (Fin 2)) ^ (2 * 3 + 1) +> (default : T)) =
    ([1] : List (Fin 2)) ^ (2 * 3 + 1) +>
        ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> default) by simp]
  refine sp_trans (b1_three_zeros 6 default (([1] : List (Fin 2)) ^ 3 +> encS [4])) ?_
  refine ss_sp_trans (a0_cascade 3 ((0 : Fin 2) >> default) (encS [4])) ?_
  simp only [z_cons_def, encS_cons, encS_nil]
  exact stepN_to_sp (n := 82) (by decide) (by run_steps 82)

theorem bounce7_to_beq0 :
    (Bounce 7 [] [8]) [tm]⊢⁺ Beq 0 [(5, 7)] := by
  unfold Bounce Beq
  rw [encL_nil, encL_cons, encL_nil, encS_cons, encS_nil]
  exact stepN_to_sp (n := 14) (by decide) (by run_steps 14)

theorem beq0_to_bev0 :
    (Beq 0 [(5, 7)]) [tm]⊢⁺ Bev 0 [(3, 7)] 4 [] := by
  unfold Beq Bev
  rw [encL_cons, encL_cons, encL_nil, encS_nil]
  exact stepN_to_sp (n := 19) (by decide) (by run_steps 19)

theorem amega_to_bev0 (z w : ℕ) (l : List (ℕ × ℕ)) :
    (Amega z w l 4 []) [tm]⊢⁺ Bev 0 ((z, w) :: l) 3 [] := by
  unfold Amega Bev
  rw [encL_cons, zeros1, ones1 3, encS_nil]
  exact stepN_to_sp (n := 1) (by decide) (by run_steps 1)

theorem bev3_to_beq4 (z w : ℕ) (l' : List (ℕ × ℕ)) :
    (Bev 3 ((z + 2, w) :: l') 3 []) [tm]⊢⁺ Beq 4 ((z, w) :: l') := by
  unfold Bev Beq
  rw [encL_cons, encL_cons, zeros3, zeros1, encS_nil]
  refine sp_trans (b1_three_zeros 6 _ _) ?_
  refine ss_sp_trans (a0_cascade 3 _ default) ?_
  exact stepN_to_sp (n := 64) (by decide) (fixed64 _)

theorem beq4_to_bev0 (z w : ℕ) (l' : List (ℕ × ℕ)) :
    (Beq 4 ((z + 2, w) :: l')) [tm]⊢⁺ Bev 0 ((z, w) :: l') 12 [4] := by
  unfold Beq Bev
  rw [encL_cons, encL_cons, zeros3, zeros1, encS_cons, encS_nil]
  have e0 : 2 * 4 + 2 = 9 + 1 := rfl
  rw [e0]
  refine sp_trans (b1_three_zeros 9 _ _) ?_
  have e1 : 9 + 1 = (2 * 3 + 1) + 3 := rfl
  rw [e1, zeros3']
  rw [show (4 : ℕ) = 3 + 1 from rfl]
  set Y : T :=
      (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l'))) with hY
  refine sp_trans (a0_odd_zeros 3 0 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  refine sp_trans (ebounce_zero 3 ((0 : Fin 2) >> Y) default) ?_
  refine ss_sp_trans (a0_cascade 3 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  refine ss_sp_trans (stepN_to_ss (fixed64 _)) ?_
  rw [hY]
  have h :=
      b1_two_zeros_one 10 ((1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l')))) (([1] : List (Fin 2)) ^ 4 +> default)
  simp only [Nat.mul_zero, Nat.zero_add, ones_one]
  exact h

theorem bounce8_to_beq0 (l : List (ℕ × ℕ)) :
    (Bounce 8 l [4]) [tm]⊢⁺ Beq 0 ((1, 8) :: l) := by
  unfold Bounce Beq
  rw [encL_cons, encS_cons, encS_nil]
  exact stepN_to_sp (n := 10) (by decide) (by run_steps 10)

theorem bodd_s0_eq_nil (k : ℕ) (l : List (ℕ × ℕ)) (m : ℕ) :
    Bodd k l m [0] = Bodd k l m [] := by
  unfold Bodd
  rw [encS_cons, encS_nil, p_zero_list, lb_append_nil, z_cons_def]

def c0_756 : Cfg (Fin 2) (Fin 6) := K qD default 0 default

theorem entry_756_part1 : c0_756 [tm]⊢⁺ Bodd 8 [] 18 [4] := by
  have h50 : c0_756 [tm]⊢^{50} Bev 0 [] 3 [4] := by
    unfold c0_756 Bev; rw [encL_nil, encS_cons, encS_nil]; run_steps 50
  refine sp_trans (stepN_to_sp (by decide) h50) ?_
  refine ss_sp_trans (R4nil_iter 3 0 0 [4]) ?_
  refine sp_trans bev3_nil_to_bodd0 ?_
  refine sp_trans (R8nil 0 4 []) ?_
  refine sp_trans (bev0_nil_bounce 7 [8]) ?_
  refine sp_trans bounce7_to_beq0 ?_
  refine sp_trans beq0_to_bev0 ?_
  refine sp_trans (R4 0 3 1 7 [] []) ?_
  exact R7 1 4 7 [] []

theorem entry_756_part2 : (Bodd 8 [] 18 [4]) [tm]⊢⁺ Bodd 27 [] 42 [4] := by
  refine sp_trans (R8nil 8 5 [4]) ?_
  refine sp_trans (bev0_nil_bounce 23 [17, 4]) ?_
  refine sp_trans (R15 23 14 4 [] []) ?_
  refine sp_trans (amega_to_bev0 14 23 []) ?_
  refine ss_sp_trans (R4_iter 3 0 0 8 23 [] []) ?_
  refine sp_trans (bev3_to_beq4 6 23 []) ?_
  refine sp_trans (beq4_to_bev0 4 23 []) ?_
  refine ss_sp_trans (R4_iter 2 0 10 0 23 [] [4]) ?_
  exact R6 2 12 23 [] [4]

theorem entry_756_part3 : (Bodd 27 [] 42 [4]) [tm]⊢⁺ Bodd 9 [(2, 61)] 18 [] := by
  refine sp_trans (R8nil 27 10 [4]) ?_
  refine sp_trans (bev0_nil_bounce 61 [41, 4]) ?_
  refine sp_trans (R15 61 38 4 [] []) ?_
  refine sp_trans (amega_to_bev0 38 61 []) ?_
  refine ss_sp_trans (R4_iter 3 0 0 32 61 [] []) ?_
  refine sp_trans (bev3_to_beq4 30 61 []) ?_
  refine sp_trans (beq4_to_bev0 28 61 []) ?_
  refine ss_sp_trans (R4_iter 12 0 0 4 61 [] [4]) ?_
  refine sp_trans (R5 8 2 61 [] [4]) ?_
  refine sp_trans (bounce8_to_beq0 [(2, 61)]) ?_
  rw [← bodd_s0_eq_nil 9 [(2, 61)] 18]
  exact R3 0 8 [(2, 61)]

theorem entry_756_part4 : (Bodd 9 [(2, 61)] 18 []) [tm]⊢⁺ Beq 5 [(2, 33), (118, 275)] := by
  refine sp_trans (R8 9 4 0 61 [] []) ?_
  refine sp_trans (R6 0 29 61 [] [17]) ?_
  refine sp_trans (R8nil 63 29 [17]) ?_
  refine sp_trans (bev0_nil_bounce 133 [96, 17]) ?_
  refine sp_trans (R15 133 93 17 [] []) ?_
  refine sp_trans (R9 12 59 133 [] []) ?_
  refine sp_trans (R12 12 [(59, 133)]) ?_
  refine sp_trans (R1 12 57 133 []) ?_
  refine ss_sp_trans (R4_iter 28 0 10 1 133 [] [17]) ?_
  refine sp_trans (R7 28 38 133 [] [17]) ?_
  refine sp_trans (R8nil 134 59 [38, 17]) ?_
  refine sp_trans (bev0_nil_bounce 275 [197, 38, 17]) ?_
  refine sp_trans (R15 275 194 38 [] [17]) ?_
  refine sp_trans (R9 33 118 275 [] [17]) ?_
  exact R14 33 2 [(118, 275)]

theorem entry_756 : c0_756 [tm]⊢⁺ Beq 5 [(2, 33), (118, 275)] :=
  sp_trans entry_756_part1 (sp_trans entry_756_part2 (sp_trans entry_756_part3 entry_756_part4))

-- E1 Table Isomorphism Bridge from `target_tm` (#756) to `tm` (#240)
def sigma756 : Fin 6 → Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 1
  | 3 => 2
  | 4 => 5
  | 5 => 0

def flipTape (t : Tape (Fin 2)) : Tape (Fin 2) :=
  ⟨t.1, t.3, t.2⟩

def mapCfg756 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map sigma756, flipTape c.tape⟩

theorem mapCfg756_init : mapCfg756 (init ([] : List (Fin 2))) = c0_756 := rfl

theorem fin6_cases (P : Fin 6 → Prop)
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) :
    ∀ q : Fin 6, P q
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3
  | ⟨4, _⟩ => h4
  | ⟨5, _⟩ => h5
  | ⟨n + 6, h⟩ => by omega

theorem fin2_cases (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) : ∀ a : Fin 2, P a
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨n + 2, h⟩ => by omega

theorem step_mapCfg756 (c c' : Cfg (Fin 2) (Fin 6)) (h : c [target_tm]⊢ c') :
    (mapCfg756 c) [tm]⊢ (mapCfg756 c') := by
  rcases c with ⟨_ | q, ⟨hd, l, r⟩⟩
  · cases h
  · revert h
    refine fin6_cases (fun q =>
      (⟨some q, ⟨hd, l, r⟩⟩ [target_tm]⊢ c') →
      ((mapCfg756 ⟨some q, ⟨hd, l, r⟩⟩) [tm]⊢ (mapCfg756 c'))) ?_ ?_ ?_ ?_ ?_ ?_ q
    all_goals
      refine fin2_cases (fun hd =>
        (⟨some _, ⟨hd, l, r⟩⟩ [target_tm]⊢ c') →
        ((mapCfg756 ⟨some _, ⟨hd, l, r⟩⟩) [tm]⊢ (mapCfg756 c'))) ?_ ?_ hd
      all_goals
        intro h; cases h <;> rfl

theorem multiStep_mapCfg756 (n : ℕ) : ∀ (c c' : Cfg (Fin 2) (Fin 6)),
    (c [target_tm]⊢^{n} c') → ((mapCfg756 c) [tm]⊢^{n} (mapCfg756 c')) := by
  induction n with
  | zero =>
    intro c c' h
    rw [ms_zero] at h ⊢
    cases h; rfl
  | succ n ih =>
    intro c c' h
    rw [ms_succ, Option.bind_eq_some_iff] at h
    rcases h with ⟨c_mid, h1, h2⟩
    exact ms_trans tm _ _ _ n 1 (ih c c_mid h1) (step_mapCfg756 c_mid c' h2)

theorem stepStar_mapCfg756 {c c' : Cfg (Fin 2) (Fin 6)} (h : c [target_tm]⊢* c') :
    (mapCfg756 c) [tm]⊢* (mapCfg756 c') := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, multiStep_mapCfg756 n c c' hn⟩

theorem step_isNone_mapCfg756 (c : Cfg (Fin 2) (Fin 6))
    (h : (step target_tm c).isNone) : (step tm (mapCfg756 c)).isNone := by
  rcases c with ⟨_ | q, ⟨hd, l, r⟩⟩
  · rfl
  · revert h
    refine fin6_cases (fun q =>
      (step target_tm ⟨some q, ⟨hd, l, r⟩⟩).isNone →
      (step tm (mapCfg756 ⟨some q, ⟨hd, l, r⟩⟩)).isNone) ?_ ?_ ?_ ?_ ?_ ?_ q
    all_goals
      refine fin2_cases (fun hd =>
        (step target_tm ⟨some _, ⟨hd, l, r⟩⟩).isNone →
        (step tm (mapCfg756 ⟨some _, ⟨hd, l, r⟩⟩)).isNone) ?_ ?_ hd
      all_goals
        intro h; first | rfl | cases h




theorem is_does_not_halt : IsNotHalt target_tm := by
  have h_inv0 : RootInv (Beq 5 [(2, 33), (118, 275)]) :=
    root_of_5 (validL_cons (by omega) (validL_cons (by omega) validL_nil))
  intro cfg ⟨n, hn⟩
  cases h_step : step target_tm cfg with
  | some _ => rfl
  | none =>
    have h_ms : c0_756 [tm]⊢^{n} mapCfg756 cfg := by
      rw [← mapCfg756_init]
      exact multiStep_mapCfg756 n (init []) cfg hn
    have h_halt_c0 : BusyBeaver.Excursion.HaltsIn tm c0_756 n :=
      ⟨mapCfg756 cfg, h_ms, step_isNone_mapCfg756 cfg (by simp [h_step])⟩
    rcases BusyBeaver.Excursion.haltsIn_reduce_stepStar
      (sp_to_ss entry_756) h_halt_c0 with ⟨m, _, h_halt_m⟩
    exact False.elim (BusyBeaver.Excursion.not_haltsIn_of_advances
      root_advances m _ h_inv0 h_halt_m)

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF
