/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0LBHHH

open Mathlib Relation Nat Turing BusyBeaver SixState WordCalculus Word ChoiceE
open BusyBeaver.M_1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0LBHHH.Solution

namespace BusyBeaver.M_1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LAHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LAHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

end

namespace Solution

def callState_1la : Call -> Fin 6
  | .ch => A
  | .cj => D
  | .cp => D
  | .ca => D

def cfgR_1la (l : HalfTape) (c : Call) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (r <{{callState_1la c}} (callWord c +> l))

def cfgL_1la (l : HalfTape) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  ((r <+ [0]) {{B}}> l)

syntax "run_1la" : tactic
macro_rules
  | `(tactic| run_1la) =>
    `(tactic| (
      dsimp [cfgR_1la, cfgL_1la, callWord, callState_1la, t, d0, d1, one]
      try simp only [List.cons_append, List.nil_append, append_cons, append_nil]
      execute))

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Justification: symbolic execution of all 15 elementary segment transitions for target_tm.
theorem segRules_1la : SegRules (CallStep target_tm cfgR_1la cfgL_1la) where
  cp_t := seg_step1 (fun _ _ => by run_1la)
  cj_t := seg_step2 (mid := [1, 0, 1, 0]) (fun _ _ => by run_1la) (fun _ _ => by run_1la)
  ch_t := seg_step3 (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
    (fun _ _ => by run_1la) (fun _ _ => by run_1la) (fun _ _ => by run_1la)
  cp_d1_d0 := seg_step1 (fun _ _ => by run_1la)
  ch_t_one := seg_step3 (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
    (fun _ _ => by run_1la) (fun _ _ => by run_1la) (fun _ _ => by run_1la)
  cj_d1_d0 := seg_step2 (mid := [1, 0, 1, 0]) (fun _ _ => by run_1la) (fun _ _ => by run_1la)
  cp_d1_d1 := seg_step2 (mid := [1, 0, 1, 0]) (fun _ _ => by run_1la) (fun _ _ => by run_1la)
  cj_d1_d1 := seg_step3 (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
    (fun _ _ => by run_1la) (fun _ _ => by run_1la) (fun _ _ => by run_1la)
  cj_d0 := seg_step1 (fun _ _ => by run_1la)
  ch_d0_one := seg_step1 (fun _ _ => by run_1la)
  ch_d1_one := seg_step2 (mid := [1, 1]) (fun _ _ => by run_1la) (fun _ _ => by run_1la)
  cj_d1 := seg_step2 (mid := [1, 1]) (fun _ _ => by run_1la) (fun _ _ => by run_1la)
  ch_d0 := seg_step1 (fun _ _ => by run_1la)
  ch_d1 := seg_step2 (mid := [1, 1]) (fun _ _ => by run_1la) (fun _ _ => by run_1la)
  ca_nil := seg_step3_eq (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
    (fun _ _ => by
      dsimp [cfgR_1la, callWord, callState_1la]; try simp only [append_cons, append_nil])
    (fun _ _ => by run_1la) (fun _ _ => by run_1la)

theorem cl_to_cf_1la (r : HalfTape) :
    (cfgL_1la lh r) [target_tm]⊢⁺ (cfgR_1la lh .ca r) := by
  dsimp [cfgL_1la, cfgR_1la, lh, callWord, callState_1la]
  try simp only [append_cons, append_nil]
  execute

def r_init_1la : HalfTape :=
  t +> (t +> (t +> (d0 +> (d1 +> (t +> default)))))

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Justification: symbolic execution of 4-stage initial transition to canonical configuration.
theorem init_to_cf_1la :
    (init []) [target_tm]⊢⁺ (cfgR_1la lh .ca r_init_1la) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  have h1 : (init []) [target_tm]⊢⁺
      (([0, 0, 1, 0, 1] +> default) {{B}}> ([0, 1, 1, 1, 0, 1, 0, 1, 0, 1] +> default)) := by
    rw [h_init]; simp only [append_cons, append_nil]; execute
  have h2 : (([0, 0, 1, 0, 1] +> default) {{B}}> ([0, 1, 1, 1, 0, 1, 0, 1, 0, 1] +> default))
      [target_tm]⊢⁺
      (([0, 1, 0, 0, 0, 0, 1] +> default) {{B}}>
        ([1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] +> default)) := by
    simp only [append_cons, append_nil]; execute
  have h3 : (([0, 1, 0, 0, 0, 0, 1] +> default) {{B}}>
        ([1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] +> default)) [target_tm]⊢⁺
      (([0, 0, 0, 1, 1] +> default) {{A}}>
        ([0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] +> default)) := by
    simp only [append_cons, append_nil]; execute
  have h4 : (([0, 0, 0, 1, 1] +> default) {{A}}>
        ([0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] +> default)) [target_tm]⊢⁺
      (cfgR_1la lh .ca r_init_1la) := by
    unfold cfgR_1la r_init_1la lh callWord callState_1la t d0 d1
    simp only [append_cons, append_nil]
    execute
  exact stepPlus_trans h1 (stepPlus_trans h2 (stepPlus_trans h3 h4))

def initWords_1la : WordList := [V, V, V, K, Q, V]

def initCodes_1la : List CodeE := [
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CS00 4 (.More CS11 1 (.More CT 2 (.More CS10 0 (.Stop
      0)))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CS00 8 (.More CS11 3 (.More CT 6 (.More
      CS11 2 (.More CP0 4 (.Stop 4)))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CS00 16 (.More CS11 7 (.More
      CT 14 (.More CS11 6 (.More CT 12 (.More CP0 23 (.More CP0 45 (.Stop 45))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CS00 32 (.More
      CS11 15 (.More CT 30 (.More CS11 14 (.More CT 28 (.More CT 55 (.More CT 109 (.More CS00 54
      (.More CP1 107 (.More CP0 214 (.More CP0 427 (.Stop 427)))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More
      CS00 64 (.More CS11 31 (.More CT 62 (.More CS11 30 (.More CT 60 (.More CT 119 (.More CT 237
      (.More CS00 118 (.More CT 235 (.More CT 469 (.More CT 937 (.More CS00 468 (.More CS10 233
      (.More CS01 116 (.More CP0 232 (.More CP0 463 (.More CS01 231 (.More CP0 462 (.Stop
      462)))))))))))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More CT
      257 (.More CS00 128 (.More CS11 63 (.More CT 126 (.More CS11 62 (.More CT 124 (.More CT 247
      (.More CT 493 (.More CS00 246 (.More CT 491 (.More CT 981 (.More CT 1961 (.More CS00 980
      (.More CP0 1959 (.More CT 3917 (.More CT 7833 (.More CS00 3916 (.More CT 7831 (.More CS01 3915
      (.More CP1 7830 (.More CP0 15660 (.More CS10 7829 (.More CP1 15657 (.More CP0 31314 (.Stop
      31314)))))))))))))))))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More CT
      257 (.More CT 513 (.More CS00 256 (.More CS11 127 (.More CT 254 (.More CS11 126 (.More CT 252
      (.More CT 503 (.More CT 1005 (.More CS00 502 (.More CT 1003 (.More CT 2005 (.More CT 4009
      (.More CS00 2004 (.More CT 4007 (.More CT 8013 (.More CT 16025 (.More CS00 8012 (.More CT
      16023 (.More CS00 8011 (.More CT 16021 (.More CT 32041 (.More CS01 16020 (.More CT 32040
      (.More CT 64079 (.More CS01 32039 (.More CP0 64078 (.More CS10 32038 (.More CP0 64075 (.More
      CP0 128149 (.More CS00 64074 (.More CP0 128147 (.More CS01 64073 (.More CP1 128146 (.More CP0
      256292 (.Stop 256292))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More CT
      257 (.More CT 513 (.More CT 1025 (.More CS00 512 (.More CS11 255 (.More CT 510 (.More CS11 254
      (.More CT 508 (.More CT 1015 (.More CT 2029 (.More CS00 1014 (.More CT 2027 (.More CT 4053
      (.More CT 8105 (.More CS00 4052 (.More CT 8103 (.More CT 16205 (.More CT 32409 (.More CS00
      16204 (.More CT 32407 (.More CS00 16203 (.More CT 32405 (.More CT 64809 (.More CS00 32404
      (.More CT 64807 (.More CT 129613 (.More CS00 64806 (.More CT 129611 (.More CS01 64805 (.More
      CT 129610 (.More CT 259219 (.More CS00 129609 (.More CT 259217 (.More CS00 129608 (.More CT
      259215 (.More CT 518429 (.More CP0 1036857 (.More CP0 2073713 (.More CS00 1036856 (.More CP0
      2073711 (.More CS00 1036855 (.More CP0 2073709 (.More CS00 1036854 (.More CP0 2073707 (.More
      CP1 4147413 (.More CP1 8294826 (.More CP0 16589652 (.Stop
      16589652)))))))))))))))))))))))))))))))))))))))))))))))))))))))
]

def initU_1la : WordList :=
    [V, V, V, V, V, V, V, V, V, V, V, K, Q, V, Q, V, V, V, K, V, V, V, K, V, V, V, K, V, K, V, V, K,
        V, V, K, V, K, V, V, K, V, K, V, V, V, V, K, V, K, V, K, V, V, V, V]

def initDs_1la : WordList :=
    [Q, K, Q, K, Q, K, Q, K, Q, Q, K, K, K, Q, K, K, Q, K, Q, Q, Q, Q, Q, Q]


set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
-- Justification: kernel evaluation of 8-round CodeE trace certificate.
theorem init_rounds_1la :
    Rounds r_init_1la (evalWords (initU_1la ++ initDs_1la) default) := by
  have h1 : Rounds (evalWords initWords_1la default)
      (evalWords (initU_1la ++ initDs_1la) default) := by
    apply rounds_of_evalCodeList initCodes_1la
    decide
  simpa [initWords_1la, r_init_1la, evalWords] using h1

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
-- Justification: rational arithmetic evaluation of wordMass and wordScale on 79-word list.
theorem init_bgood_1la :
    BGood (initU_1la ++ initDs_1la) := by
  apply bgood_of_checks initU_1la initDs_1la 10
  · decide
  · norm_num [initU_1la, initDs_1la, wordScale]
  · decide
  · decide
  · decide
  · decide
  · norm_num [initU_1la, initDs_1la, wordMass, wordMassK, wordScale]

end Solution

@[expose] public section

open Solution in
theorem is_does_not_halt : IsNotHalt target_tm :=
  does_not_halt_of_segRules segRules_1la cl_to_cf_1la init_to_cf_1la init_rounds_1la init_bgood_1la

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LAHHH
