/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB1LD_1LC1RA_0LD0LC_0RE1RB_1RD0RF_0RBHHH

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LAHHH_1LA1LF

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LAHHH_1LA1LF"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

open BusyBeaver.M_1RB1LD_1LC1RA_0LD0LC_0RE1RB_1RD0RF_0RBHHH.Solution

theorem rule_left_carry (l r : ListBlank (Fin 2)) (j : Nat) :
    (((l <+ ([0] : List (Fin 2))) <+ (([1] : List (Fin 2)) ^ (1 + j))) <{{A}} r) [target]⊢*
    (l <{{A}} ((([1] : List (Fin 2)) ^ (2 + j)) +> r)) := by
  have hj : 1 + j = j + 1 := by omega
  rw [hj, pow_succ_list, ← listblank_append_append]
  have h1 : ((((l <+ ([0] : List (Fin 2))) <+ (([1] : List (Fin 2)) ^ j)) <+
      ([1] : List (Fin 2))) <{{A}} r) [target]⊢*
      (((l <+ ([0] : List (Fin 2))) <+ (([1] : List (Fin 2)) ^ j)) <{{F}}
        (([1] : List (Fin 2)) +> r)) := by execute
  have h2 : (((l <+ ([0] : List (Fin 2))) <+ (([1] : List (Fin 2)) ^ j)) <{{F}}
      (([1] : List (Fin 2)) +> r)) [target]⊢*
      ((l <+ ([0] : List (Fin 2))) <{{F}}
        ((([1] : List (Fin 2)) ^ j) +> (([1] : List (Fin 2)) +> r))) := by
    clear hj h1
    induction j generalizing r with
    | zero => exact ⟨0, rfl⟩
    | succ j ih =>
      rw [pow_succ_list, ← listblank_append_append]
      have hs : (((((l <+ ([0] : List (Fin 2))) <+ (([1] : List (Fin 2)) ^ j)) <+
          ([1] : List (Fin 2))) <{{F}} (([1] : List (Fin 2)) +> r))) [target]⊢*
          (((l <+ ([0] : List (Fin 2))) <+ (([1] : List (Fin 2)) ^ j)) <{{F}}
            (([1] : List (Fin 2)) +> (([1] : List (Fin 2)) +> r))) := by execute
      have hi := ih (([1] : List (Fin 2)) +> r)
      rw [listblank_append_append (([1] : List (Fin 2)) +> r) ([1] : List (Fin 2))
        (([1] : List (Fin 2)) ^ j), list_pow_append_one] at hi
      exact stepStar_trans hs hi
  have h3 : ((l <+ ([0] : List (Fin 2))) <{{F}}
      ((([1] : List (Fin 2)) ^ j) +> (([1] : List (Fin 2)) +> r))) [target]⊢*
      (l <{{A}} (([1] : List (Fin 2)) +>
        ((([1] : List (Fin 2)) ^ j) +> (([1] : List (Fin 2)) +> r)))) := by execute
  have hrew1 : ((([1] : List (Fin 2)) ^ j) +> (([1] : List (Fin 2)) +> r)) =
      ((([1] : List (Fin 2)) ^ (j + 1)) +> r) := by
    rw [listblank_append_append r ([1] : List (Fin 2)) (([1] : List (Fin 2)) ^ j),
      list_pow_append_one]
  have hrew2 : (([1] : List (Fin 2)) +> ((([1] : List (Fin 2)) ^ (j + 1)) +> r)) =
      ((([1] : List (Fin 2)) ^ (2 + j)) +> r) := by
    have : 2 + j = (j + 1) + 1 := by omega
    rw [← pow_succ_append_right, this]
  rw [hrew1] at h2 h3
  rw [hrew2] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem tm249_rules : PairCounter.Rules target B A C :=
  PairCounter.mkRules
    (fun _ _ => by execute)
    rule_left_carry
    (fun _ _ => by execute)
    (fun _ _ => by execute)
    (fun _ _ => by execute)
    (fun _ _ => by execute)
    (fun _ _ => by execute)
    (fun _ _ => by execute)
    (fun _ _ => by execute)
    (fun _ _ => by execute)
    (fun _ _ => by execute)
    (fun _ _ => by execute)
    (fun _ _ => by execute)
    (fun _ _ => by execute)

theorem tm249_init :
    (init []) [target]⊢* ((default <+ ([1] : List (Fin 2))) {{B}}> PairCounter.right_tape 1 0) := by
  unfold PairCounter.right_tape
  execute

public section

theorem is_not_halt : IsNotHalt target := by
  refine PairCounter.nonhalt_from tm249_rules tm249_init ?_ (PairCounter.Num.one
      PairCounter.Num.nil)
  exact PairCounter.Safe.main PairCounter.Normal.D ⟨by decide, fun _ => by decide⟩

end

end BusyBeaver.M_1RB1LF_0RC0RB_0LD1LA_1LC0LE_0LAHHH_1LA1LF
