/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_HHH0RB

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_HHH0RB"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)

attribute [local simp] pow_zero_list pow_succ_list listblank_append_nil listblank_append_cons

@[simp] theorem tape_mk1_nil : Tape.mk₁ ([] : List (Fin 2)) = ⟨0, default, default⟩ := rfl

theorem str_app_assoc (l₁ l₂ : List (Fin 2)) (s : zB) :
    l₁ +> (l₂ +> s) = (l₁ ++ l₂) +> s :=
  ListBlank.append_append s l₂ l₁

macro "finish" : tactic => `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine ReachesPlus.to_star ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [listblank_append_cons, listblank_append_nil,
        Turing.ListBlank.head_cons, ListBlank.head_default_fin]); rfl) ?_ <;>
    simp only [listblank_append_cons, listblank_append_nil, Turing.Tape.move,
        Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
        ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default])
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;>
      (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;>
      (any_goals (first | finish | step)))
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;>
      execute5 <;> execute5)

-- Shift rules (`⊢*`)

theorem SW (k : Nat) (l r : zB) :
    ((([1, 0] : zF) ^ k +> l) <{{C}} r) [target_tm]⊢* (l <{{C}} (([0, 1] : zF) ^ k +> r)) := by
  induction k generalizing r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : ((([1, 0] : zF) +> (([1, 0] : zF) ^ k +> l)) <{{C}} r) [target_tm]⊢⁺
              ((([1, 0] : zF) ^ k +> l) <{{C}} (([0, 1] : zF) +> r)) := by
      execute
    rw [pow_succ_list, ← str_app_assoc]
    have h2 := ih (([0, 1] : zF) +> r)
    rw [str_app_assoc, list_pow_append_one] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)

theorem TT (j : Nat) (l r : zB) :
    ((([1, 1, 1] : zF) ^ j +> l) <{{C}} r) [target_tm]⊢* (l <{{C}} (([0, 1, 1] : zF) ^ j +> r)) :=
        by
  induction j generalizing r with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    have h1 : ((([1, 1, 1] : zF) +> (([1, 1, 1] : zF) ^ j +> l)) <{{C}} r) [target_tm]⊢⁺
              ((([1, 1, 1] : zF) ^ j +> l) <{{C}} (([0, 1, 1] : zF) +> r)) := by
      execute
    rw [pow_succ_list, ← str_app_assoc]
    have h2 := ih (([0, 1, 1] : zF) +> r)
    rw [str_app_assoc, list_pow_append_one] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)

theorem PS (b : Nat) (l r : zB) :
    ((([1, 1, 0] : zF) +> l) {{B}}> (([1, 0] : zF) ^ b +> r)) [target_tm]⊢*
    ((([1, 1] : zF) +> (([0, 1] : zF) ^ b +> (([0] : zF) +> l))) {{B}}> r) := by
  induction b generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ b ih =>
    have h1 : ((([1, 1, 0] : zF) +> l) {{B}}> (([1, 0] : zF) +> (([1,
        0] : zF) ^ b +> r))) [target_tm]⊢⁺
              ((([1, 1, 0] : zF) +> (([1, 0] : zF) +> l)) {{B}}> (([1, 0] : zF) ^ b +> r)) := by
      execute
    rw [pow_succ_list, ← str_app_assoc]
    have h2 := ih (([1, 0] : zF) +> l)
    have heq : (([1, 1] : zF) +> (([0, 1] : zF) ^ b +> (([0] : zF) +> (([1, 0] : zF) +> l)))) =
               (([1, 1] : zF) +> (([0, 1] : zF) ^ (b + 1) +> (([0] : zF) +> l))) := by
      have hpow : (([0, 1] : zF) ^ b +> (([0] : zF) +> (([1, 0] : zF) +> l))) =
                  (([0, 1] : zF) ^ (b + 1) +> (([0] : zF) +> l)) := by
        change (([0, 1] : zF) ^ b +> (([0, 1] : zF) +> (([0] : zF) +> l))) = _
        rw [str_app_assoc, list_pow_append_one]
      rw [hpow]
    rw [heq] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)

theorem BR3 (j : Nat) (l r : zB) :
    (l {{B}}> (([1, 1, 1] : zF) ^ j +> r)) [target_tm]⊢* ((([1, 1, 1] : zF) ^ j +> l) {{B}}> r) :=
        by
  induction j generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    have h1 : (l {{B}}> (([1, 1, 1] : zF) +> (([1, 1, 1] : zF) ^ j +> r))) [target_tm]⊢⁺
              ((([1, 1, 1] : zF) +> l) {{B}}> (([1, 1, 1] : zF) ^ j +> r)) := by
      execute
    rw [pow_succ_list, ← str_app_assoc]
    have h2 := ih (([1, 1, 1] : zF) +> l)
    rw [str_app_assoc, list_pow_append_one] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)

theorem E_push (k : Nat) (l r : zB) :
    ((([0, 0] : zF) +> l) {{E}}> (([1, 1, 0] : zF) ^ k +> r)) [target_tm]⊢*
    ((([0, 0] : zF) +> (([1, 0, 0] : zF) ^ k +> l)) {{E}}> r) := by
  induction k generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : ((([0, 0] : zF) +> l) {{E}}> (([1, 1, 0] : zF) +> (([1, 1,
        0] : zF) ^ k +> r))) [target_tm]⊢⁺
              ((([0, 0] : zF) +> (([1, 0, 0] : zF) +> l)) {{E}}> (([1, 1, 0] : zF) ^ k +> r)) := by
      execute
    rw [pow_succ_list, ← str_app_assoc]
    have h2 := ih (([1, 0, 0] : zF) +> l)
    have heq : (([0, 0] : zF) +> (([1, 0, 0] : zF) ^ k +> (([1, 0, 0] : zF) +> l))) =
               (([0, 0] : zF) +> (([1, 0, 0] : zF) ^ (k + 1) +> l)) := by
      rw [str_app_assoc (([1, 0, 0] : zF) ^ k), list_pow_append_one]
    rw [heq] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)

theorem lpow_rot2 (n : Nat) (a b : Fin 2) (s : zB) :
    ([a, b] : zF) ^ n +> ([a] +> s) = [a] +> (([b, a] : zF) ^ n +> s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list, ← str_app_assoc, ih]
    rfl

theorem PS' (b : Nat) (l r : zB) :
    ((([1, 1, 0] : zF) +> l) {{B}}> (([1, 0] : zF) ^ b +> r)) [target_tm]⊢*
    ((([1, 1, 0] : zF) +> (([1, 0] : zF) ^ b +> l)) {{B}}> r) := by
  have h := PS b l r
  rw [lpow_rot2 b 0 1 l] at h
  exact h

theorem ones_comm (b : Nat) : ([1, 1] : zF) ++ ([1, 1, 1] : zF) ^ b = ([1, 1, 1] : zF) ^ b ++ [1,
    1] :=
    by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [pow_succ_list]
    change ([1, 1, 1] : zF) ++ (([1, 1] : zF) ++ ([1, 1, 1] : zF) ^ b) = _
    rw [ih, List.append_assoc]

theorem one_comm (b : Nat) : ([1] : zF) ++ ([1, 1, 1] : zF) ^ b = ([1, 1, 1] : zF) ^ b ++ [1] := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [pow_succ_list]
    change ([1, 1, 1] : zF) ++ (([1] : zF) ++ ([1, 1, 1] : zF) ^ b) = _
    rw [ih, List.append_assoc]

theorem sh110 (b : Nat) : ([1, 1] : zF) ++ ([0, 1, 1] : zF) ^ b = ([1, 1, 0] : zF) ^ b ++ [1, 1] :=
    by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [pow_succ_list, pow_succ_list]
    change ([1, 1, 0] : zF) ++ (([1, 1] : zF) ++ ([0, 1, 1] : zF) ^ b) = _
    rw [ih, List.append_assoc]

theorem S_ones2 (b : Nat) (s : zB) :
    ([1, 1] : zF) +> (([1, 1, 1] : zF) ^ b +> s) = ([1, 1, 1] : zF) ^ b +> (([1, 1] : zF) +> s) :=
        by
  rw [str_app_assoc, ones_comm, ← str_app_assoc]

theorem S_ones1 (b : Nat) (s : zB) :
    ([1] : zF) +> (([1, 1, 1] : zF) ^ b +> s) = ([1, 1, 1] : zF) ^ b +> (([1] : zF) +> s) := by
  rw [str_app_assoc, one_comm, ← str_app_assoc]

theorem S_sh110 (b : Nat) (s : zB) :
    ([1, 1] : zF) +> (([0, 1, 1] : zF) ^ b +> s) = ([1, 1, 0] : zF) ^ b +> (([1, 1] : zF) +> s) :=
        by
  rw [str_app_assoc, sh110, ← str_app_assoc]

theorem C_left_right (l r : zB) :
    ((([0] : zF) +> l) <{{C}} (([0] : zF) +> r)) = (l {{C}}> (([0, 0] : zF) +> r)) := by
  simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem RND2 (q j : Nat) (l r : zB) :
    (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (q + 3) +> (([1, 1, 1] : zF) ^ j +> (([1, 1,
        0] : zF) +> r))))) [target_tm]⊢⁺
    ((([1, 0, 1, 0] : zF) +> l) {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (q + 1) +> (([1, 1,
        0] : zF) ^ j +> (([1, 1, 1] : zF) +> r))))) := by
  rw [Nat.add_comm q 3, list_pow_add, ← str_app_assoc]
  set R0 : zB := ([1, 1, 1] : zF) ^ j +> (([1, 1, 0] : zF) +> r)
  set L0 : zB := ([0, 1, 0, 1, 0] : zF) +> l
  have h1 : (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ 3 +> (([1, 0] : zF) ^ q +> R0))))
      [target_tm]⊢⁺
            ((([1, 1, 0] : zF) +> L0) {{B}}> (([1, 0] : zF) ^ q +> R0)) := by
    change (l {{C}}> (([0, 0] : zF) +> (([1, 0, 1, 0, 1, 0] : zF) +> (([1,
        0] : zF) ^ q +> R0)))) [target_tm]⊢⁺ _
    execute
  have h2 := PS' q L0 R0
  set L1 : zB := ([1, 0] : zF) ^ q +> L0
  have h3 := BR3 j (([1, 1, 0] : zF) +> L1) (([1, 1, 0] : zF) +> r)
  have h4 : ((([1, 1, 1] : zF) ^ j +> (([1, 1, 0] : zF) +> L1)) {{B}}> (([1, 1,
      0] : zF) +> r)) [target_tm]⊢⁺
            ((([1, 1] : zF) +> (([1, 1, 1] : zF) ^ j +> (([1, 1,
                0] : zF) +> L1))) <{{C}} (([1] : zF) +> r)) := by
    execute
  rw [S_ones2] at h4
  have h5 := TT j (([1, 1] : zF) +> (([1, 1, 0] : zF) +> L1)) (([1] : zF) +> r)
  set R2 : zB := ([0, 1, 1] : zF) ^ j +> (([1] : zF) +> r)
  have h6 : ((([1, 1] : zF) +> (([1, 1, 0] : zF) +> L1)) <{{C}} R2) [target_tm]⊢⁺
            (L1 <{{C}} (([0, 1, 0, 1, 1] : zF) +> R2)) := by
    execute
  have h7 := SW q L0 (([0, 1, 0, 1, 1] : zF) +> R2)
  have h8 : (L0 <{{C}} (([0, 1] : zF) ^ q +> (([0, 1, 0, 1, 1] : zF) +> R2))) =
            ((([1, 0, 1, 0] : zF) +> l) {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (q + 1) +> (([1,
                1,
                0] : zF) ^ j +> (([1, 1, 1] : zF) +> r))))) := by
    have hrot : (([0, 1] : zF) ^ q +> (([0, 1, 0, 1, 1] : zF) +> R2)) =
                ([0] : zF) +> (([1, 0] : zF) ^ (q + 1) +> (([1, 1, 0] : zF) ^ j +> (([1, 1,
                    1] : zF) +> r))) := by
      change (([0, 1] : zF) ^ q +> (([0] : zF) +> (([1, 0] : zF) +> (([1, 1] : zF) +> (([0, 1,
          1] : zF) ^ j +> (([1] : zF) +> r)))))) = _
      rw [lpow_rot2 q 0 1, S_sh110 j (([1] : zF) +> r), str_app_assoc (([1, 0] : zF) ^ q) ([1,
          0] : zF), list_pow_append_one]
      rfl
    rw [hrot]
    exact C_left_right (([1, 0, 1, 0] : zF) +> l) _
  rw [h8] at h7
  exact ReachesPlus.trans_star (ReachesPlus.trans_star (ReachesPlus.trans_star
      (ReachesPlus.trans_star (ReachesPlus.trans_star h1 h2) h3) (ReachesPlus.to_star h4)) h5)
      (ReachesPlus.trans_star h6 h7 |> ReachesPlus.to_star)

theorem RND1 (q j : Nat) (l r : zB) :
    (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (q + 3) +> (([1, 1, 1] : zF) ^ j +> (([1, 1, 1, 1,
        0] : zF) +> r))))) [target_tm]⊢⁺
    ((([1, 0, 1, 0] : zF) +> l) {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (q + 1) +> (([1, 1, 1,
        1] : zF) +> (([0, 1, 1] : zF) ^ j +> (([1] : zF) +> r)))))) := by
  rw [Nat.add_comm q 3, list_pow_add, ← str_app_assoc]
  set R0 : zB := ([1, 1, 1] : zF) ^ j +> (([1, 1, 1, 1, 0] : zF) +> r)
  set L0 : zB := ([0, 1, 0, 1, 0] : zF) +> l
  have h1 : (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ 3 +> (([1, 0] : zF) ^ q +> R0))))
      [target_tm]⊢⁺
            ((([1, 1, 0] : zF) +> L0) {{B}}> (([1, 0] : zF) ^ q +> R0)) := by
    change (l {{C}}> (([0, 0] : zF) +> (([1, 0, 1, 0, 1, 0] : zF) +> (([1,
        0] : zF) ^ q +> R0)))) [target_tm]⊢⁺ _
    execute
  have h2 := PS' q L0 R0
  set L1 : zB := ([1, 0] : zF) ^ q +> L0
  have h3 := BR3 j (([1, 1, 0] : zF) +> L1) (([1, 1, 1, 1, 0] : zF) +> r)
  have h4 : ((([1, 1, 1] : zF) ^ j +> (([1, 1, 0] : zF) +> L1)) {{B}}> (([1, 1, 1, 1,
      0] : zF) +> r)) [target_tm]⊢⁺
            ((([1, 1] : zF) +> (([1, 1] : zF) +> (([1, 1, 1] : zF) ^ j +> (([1, 1,
                0] : zF) +> L1)))) <{{C}} (([1] : zF) +> r)) := by
    execute
  rw [S_ones2, S_ones2] at h4
  have h5 := TT j (([1, 1] : zF) +> (([1, 1] : zF) +> (([1, 1, 0] : zF) +> L1))) (([1] : zF) +> r)
  set R2 : zB := ([0, 1, 1] : zF) ^ j +> (([1] : zF) +> r)
  have h6 : ((([1, 1] : zF) +> (([1, 1] : zF) +> (([1, 1, 0] : zF) +> L1))) <{{C}} R2) [target_tm]⊢⁺
            (L1 <{{C}} (([0, 1, 0, 1, 1, 1, 1] : zF) +> R2)) := by
    execute
  have h7 := SW q L0 (([0, 1, 0, 1, 1, 1, 1] : zF) +> R2)
  have h8 : (L0 <{{C}} (([0, 1] : zF) ^ q +> (([0, 1, 0, 1, 1, 1, 1] : zF) +> R2))) =
            ((([1, 0, 1, 0] : zF) +> l) {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (q + 1) +> (([1,
                1,
                1, 1] : zF) +> (([0, 1, 1] : zF) ^ j +> (([1] : zF) +> r)))))) := by
    have hrot : (([0, 1] : zF) ^ q +> (([0, 1, 0, 1, 1, 1, 1] : zF) +> R2)) =
                ([0] : zF) +> (([1, 0] : zF) ^ (q + 1) +> (([1, 1, 1, 1] : zF) +> R2)) := by
      change (([0, 1] : zF) ^ q +> (([0] : zF) +> (([1, 0] : zF) +> (([1, 1, 1, 1] : zF) +> R2))))
          = _
      rw [lpow_rot2 q 0 1, str_app_assoc (([1, 0] : zF) ^ q) ([1, 0] : zF), list_pow_append_one]
    rw [hrot]
    exact C_left_right (([1, 0, 1, 0] : zF) +> l) _
  rw [h8] at h7
  exact ReachesPlus.trans_star (ReachesPlus.trans_star (ReachesPlus.trans_star
      (ReachesPlus.trans_star (ReachesPlus.trans_star h1 h2) h3) (ReachesPlus.to_star h4)) h5)
      (ReachesPlus.trans_star h6 h7 |> ReachesPlus.to_star)

theorem RND0 (q j : Nat) (l r : zB) :
    (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (q + 3) +> (([1, 1, 1] : zF) ^ j +> (([1, 1, 1,
        0] : zF) +> r))))) [target_tm]⊢⁺
    ((([1, 0, 1, 0] : zF) +> l) {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ q +> (([1, 1, 1, 1,
        1] : zF) +> (([0, 1, 1] : zF) ^ j +> (([1] : zF) +> r)))))) := by
  rw [Nat.add_comm q 3, list_pow_add, ← str_app_assoc]
  set R0 : zB := ([1, 1, 1] : zF) ^ j +> (([1, 1, 1, 0] : zF) +> r)
  set L0 : zB := ([0, 1, 0, 1, 0] : zF) +> l
  have h1 : (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ 3 +> (([1, 0] : zF) ^ q +> R0))))
      [target_tm]⊢⁺
            ((([1, 1, 0] : zF) +> L0) {{B}}> (([1, 0] : zF) ^ q +> R0)) := by
    change (l {{C}}> (([0, 0] : zF) +> (([1, 0, 1, 0, 1, 0] : zF) +> (([1,
        0] : zF) ^ q +> R0)))) [target_tm]⊢⁺ _
    execute
  have h2 := PS' q L0 R0
  set L1 : zB := ([1, 0] : zF) ^ q +> L0
  have h3 := BR3 j (([1, 1, 0] : zF) +> L1) (([1, 1, 1, 0] : zF) +> r)
  have h4 : ((([1, 1, 1] : zF) ^ j +> (([1, 1, 0] : zF) +> L1)) {{B}}> (([1, 1, 1,
      0] : zF) +> r)) [target_tm]⊢⁺
            ((([1] : zF) +> (([1, 1] : zF) +> (([1, 1, 1] : zF) ^ j +> (([1, 1,
                0] : zF) +> L1)))) <{{C}} (([1] : zF) +> r)) := by
    execute
  rw [S_ones2, S_ones1] at h4
  have h5 := TT j (([1] : zF) +> (([1, 1] : zF) +> (([1, 1, 0] : zF) +> L1))) (([1] : zF) +> r)
  set R2 : zB := ([0, 1, 1] : zF) ^ j +> (([1] : zF) +> r)
  have h6 : ((([1] : zF) +> (([1, 1] : zF) +> (([1, 1, 0] : zF) +> L1))) <{{C}} R2) [target_tm]⊢⁺
            (L1 <{{C}} (([0, 1, 1, 1, 1, 1] : zF) +> R2)) := by
    execute
  have h7 := SW q L0 (([0, 1, 1, 1, 1, 1] : zF) +> R2)
  have h8 : (L0 <{{C}} (([0, 1] : zF) ^ q +> (([0, 1, 1, 1, 1, 1] : zF) +> R2))) =
            ((([1, 0, 1, 0] : zF) +> l) {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ q +> (([1, 1, 1,
                1,
                1] : zF) +> (([0, 1, 1] : zF) ^ j +> (([1] : zF) +> r)))))) := by
    have hrot : (([0, 1] : zF) ^ q +> (([0, 1, 1, 1, 1, 1] : zF) +> R2)) =
                ([0] : zF) +> (([1, 0] : zF) ^ q +> (([1, 1, 1, 1, 1] : zF) +> R2)) := by
      change (([0, 1] : zF) ^ q +> (([0] : zF) +> (([1, 1, 1, 1, 1] : zF) +> R2))) = _
      rw [lpow_rot2 q 0 1]
    rw [hrot]
    exact C_left_right (([1, 0, 1, 0] : zF) +> l) _
  rw [h8] at h7
  exact ReachesPlus.trans_star (ReachesPlus.trans_star (ReachesPlus.trans_star
      (ReachesPlus.trans_star (ReachesPlus.trans_star h1 h2) h3) (ReachesPlus.to_star h4)) h5)
      (ReachesPlus.trans_star h6 h7 |> ReachesPlus.to_star)

theorem PUSH (k : Nat) (l r : zB) :
    (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ 2 +> (([1, 1, 0] : zF) ^ k +> (([1, 1,
        1] : zF) +> r))))) [target_tm]⊢⁺
    ((([1, 0, 0] : zF) ^ k +> (([1, 0, 1, 0] : zF) +> l)) {{C}}> (([0, 0] : zF) +> (([1,
        0] : zF) +> (([1] : zF) +> r)))) := by
  have h1 : (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ 2 +> (([1, 1, 0] : zF) ^ k +> (([1, 1,
      1] : zF) +> r))))) [target_tm]⊢⁺
            ((([0, 0] : zF) +> (([1, 0, 1, 0] : zF) +> l)) {{E}}> (([1, 1, 0] : zF) ^ k +> (([1, 1,
                1] : zF) +> r))) := by
    change (l {{C}}> (([0, 0] : zF) +> (([1, 0, 1, 0] : zF) +> (([1, 1, 0] : zF) ^ k +> (([1, 1,
        1] : zF) +> r))))) [target_tm]⊢⁺ _
    execute
  have h2 := E_push k (([1, 0, 1, 0] : zF) +> l) (([1, 1, 1] : zF) +> r)
  have h3 : ((([0, 0] : zF) +> (([1, 0, 0] : zF) ^ k +> (([1, 0, 1, 0] : zF) +> l))) {{E}}> (([1, 1,
      1] : zF) +> r)) [target_tm]⊢⁺
            ((([1, 0, 0] : zF) ^ k +> (([1, 0, 1, 0] : zF) +> l)) {{C}}> (([0, 0] : zF) +> (([1,
                0] : zF) +> (([1] : zF) +> r)))) := by
    execute
  exact ReachesPlus.trans_star (ReachesPlus.trans_star h1 h2) (ReachesPlus.to_star h3)

theorem BITE1 (p : Nat) (l r : zB) :
    ((([1] : zF) +> (([0, 1] : zF) ^ p +> (([0, 0] : zF) +> l))) {{C}}> (([0, 0] : zF) +> (([1,
        0] : zF) +> (([1, 1] : zF) +> r)))) [target_tm]⊢⁺
    (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (p + 3) +> (([1] : zF) +> r)))) := by
  have hrotL : (([1] : zF) +> (([0, 1] : zF) ^ p +> (([0, 0] : zF) +> l))) =
               (([1, 0] : zF) +> (([1, 0] : zF) ^ p +> (([0] : zF) +> l))) := by
    change ([1] : zF) +> (([0, 1] : zF) ^ p +> (([0] : zF) +> (([0] : zF) +> l))) = _
    rw [lpow_rot2 p 0 1]
    rfl
  rw [hrotL]
  have h1 : ((([1, 0] : zF) +> (([1, 0] : zF) ^ p +> (([0] : zF) +> l))) {{C}}> (([0,
      0] : zF) +> (([1, 0] : zF) +> (([1, 1] : zF) +> r)))) [target_tm]⊢⁺
            ((([1, 0] : zF) ^ p +> (([0] : zF) +> l)) <{{C}} (([0, 1, 0, 1, 0, 1, 0,
                1] : zF) +> r)) := by
    execute
  have h2 := SW p (([0] : zF) +> l) (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> r)
  have h3 : ((([0] : zF) +> l) <{{C}} (([0, 1] : zF) ^ p +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +>
      r))) =
            (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (p + 3) +> (([1] : zF) +> r)))) := by
    have hrotR : (([0, 1] : zF) ^ p +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> r)) =
                 ([0] : zF) +> (([1, 0] : zF) ^ (p + 3) +> (([1] : zF) +> r)) := by
      change (([0, 1] : zF) ^ p +> (([0] : zF) +> (([1, 0] : zF) ^ 3 +> (([1] : zF) +> r)))) = _
      rw [lpow_rot2 p 0 1, str_app_assoc (([1, 0] : zF) ^ p) (([1, 0] : zF) ^ 3), ← list_pow_add]
    rw [hrotR]
    exact C_left_right l _
  rw [h3] at h2
  exact ReachesPlus.trans_star h1 h2

theorem BITE0 (p j : Nat) (l r : zB) :
    ((([1] : zF) +> (([0, 1] : zF) ^ p +> (([0, 0] : zF) +> l))) {{C}}> (([0, 0] : zF) +> (([1, 1,
        1] : zF) ^ j +> (([1, 1, 0] : zF) +> r)))) [target_tm]⊢⁺
    (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (p + 2) +> (([1] : zF) +> (([0, 1,
        1] : zF) ^ j +> (([1] : zF) +> r)))))) := by
  have hrotL : (([1] : zF) +> (([0, 1] : zF) ^ p +> (([0, 0] : zF) +> l))) =
               (([1, 0] : zF) +> (([1, 0] : zF) ^ p +> (([0] : zF) +> l))) := by
    change ([1] : zF) +> (([0, 1] : zF) ^ p +> (([0] : zF) +> (([0] : zF) +> l))) = _
    rw [lpow_rot2 p 0 1]
    rfl
  rw [hrotL]
  set L0 : zB := ([1, 0] : zF) +> (([1, 0] : zF) ^ p +> (([0] : zF) +> l))
  have hcommR : (([1, 1, 1] : zF) ^ j +> (([1, 1, 0] : zF) +> r)) =
                ([1] : zF) +> (([1, 1, 1] : zF) ^ j +> (([1, 0] : zF) +> r)) := by
    change (([1, 1, 1] : zF) ^ j +> (([1] : zF) +> (([1, 0] : zF) +> r))) = _
    rw [← S_ones1]
  rw [hcommR]
  have h1 : (L0 {{C}}> (([0, 0] : zF) +> (([1] : zF) +> (([1, 1, 1] : zF) ^ j +> (([1,
      0] : zF) +> r))))) [target_tm]⊢⁺
            ((([0, 1, 0] : zF) +> L0) {{B}}> (([1, 1, 1] : zF) ^ j +> (([1, 0] : zF) +> r))) := by
    execute
  have h2 := BR3 j (([0, 1, 0] : zF) +> L0) (([1, 0] : zF) +> r)
  have h3 : ((([1, 1, 1] : zF) ^ j +> (([0, 1, 0] : zF) +> L0)) {{B}}> (([1,
      0] : zF) +> r)) [target_tm]⊢⁺
            ((([1] : zF) +> (([1, 1, 1] : zF) ^ j +> (([0, 1,
                0] : zF) +> L0))) <{{C}} (([1] : zF) +> r)) := by
    execute
  rw [S_ones1] at h3
  have h4 := TT j (([1] : zF) +> (([0, 1, 0] : zF) +> L0)) (([1] : zF) +> r)
  set R2 : zB := ([0, 1, 1] : zF) ^ j +> (([1] : zF) +> r)
  have h5 : ((([1] : zF) +> (([0, 1, 0] : zF) +> L0)) <{{C}} R2) [target_tm]⊢⁺
            ((([1, 0] : zF) ^ p +> (([0] : zF) +> l)) <{{C}} (([0, 1, 0, 1, 0, 1] : zF) +> R2)) :=
                by
    dsimp [L0]
    execute
  have h6 := SW p (([0] : zF) +> l) (([0, 1, 0, 1, 0, 1] : zF) +> R2)
  have h7 : ((([0] : zF) +> l) <{{C}} (([0, 1] : zF) ^ p +> (([0, 1, 0, 1, 0, 1] : zF) +> R2))) =
            (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (p + 2) +> (([1] : zF) +> R2)))) := by
    have hrotR : (([0, 1] : zF) ^ p +> (([0, 1, 0, 1, 0, 1] : zF) +> R2)) =
                 ([0] : zF) +> (([1, 0] : zF) ^ (p + 2) +> (([1] : zF) +> R2)) := by
      change (([0, 1] : zF) ^ p +> (([0] : zF) +> (([1, 0] : zF) ^ 2 +> (([1] : zF) +> R2)))) = _
      rw [lpow_rot2 p 0 1, str_app_assoc (([1, 0] : zF) ^ p) (([1, 0] : zF) ^ 2), ← list_pow_add]
    rw [hrotR]
    exact C_left_right l _
  rw [h7] at h6
  exact ReachesPlus.trans_star (ReachesPlus.trans_star (ReachesPlus.trans_star
      (ReachesPlus.trans_star h1 h2) (ReachesPlus.to_star h3)) h4) (ReachesPlus.trans_star h5 h6
      |> ReachesPlus.to_star)

theorem BITE0c (p j : Nat) (l r : zB) :
    ((([1] : zF) +> (([0, 1] : zF) ^ p +> (([0, 0] : zF) +> l))) {{C}}> (([0, 0] : zF) +> (([1, 1,
        1] : zF) ^ j +> (([1, 1, 1, 1, 1, 1, 0] : zF) +> r)))) [target_tm]⊢⁺
    (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (p + 2) +> (([1, 1, 1] : zF) +> (([1, 1,
        0] : zF) ^ j +> (([1, 1, 1] : zF) +> r)))))) := by
  have hrotL : (([1] : zF) +> (([0, 1] : zF) ^ p +> (([0, 0] : zF) +> l))) =
               (([1, 0] : zF) +> (([1, 0] : zF) ^ p +> (([0] : zF) +> l))) := by
    change ([1] : zF) +> (([0, 1] : zF) ^ p +> (([0] : zF) +> (([0] : zF) +> l))) = _
    rw [lpow_rot2 p 0 1]
    rfl
  rw [hrotL]
  set L0 : zB := ([1, 0] : zF) +> (([1, 0] : zF) ^ p +> (([0] : zF) +> l))
  have hcommR : (([1, 1, 1] : zF) ^ j +> (([1, 1, 1, 1, 1, 1, 0] : zF) +> r)) =
                ([1] : zF) +> (([1, 1, 1] : zF) ^ j +> (([1, 1, 1, 1, 1, 0] : zF) +> r)) := by
    change (([1, 1, 1] : zF) ^ j +> (([1] : zF) +> (([1, 1, 1, 1, 1, 0] : zF) +> r))) = _
    rw [← S_ones1]
  rw [hcommR]
  have h1 : (L0 {{C}}> (([0, 0] : zF) +> (([1] : zF) +> (([1, 1, 1] : zF) ^ j +> (([1, 1, 1, 1, 1,
      0] : zF) +> r))))) [target_tm]⊢⁺
            ((([0, 1, 0] : zF) +> L0) {{B}}> (([1, 1, 1] : zF) ^ j +> (([1, 1, 1, 1, 1,
                0] : zF) +> r))) := by
    execute
  have h2 := BR3 j (([0, 1, 0] : zF) +> L0) (([1, 1, 1, 1, 1, 0] : zF) +> r)
  have h3 : ((([1, 1, 1] : zF) ^ j +> (([0, 1, 0] : zF) +> L0)) {{B}}> (([1, 1, 1, 1, 1,
      0] : zF) +> r)) [target_tm]⊢⁺
            ((([1] : zF) +> (([1, 1] : zF) +> (([1, 1] : zF) +> (([1, 1, 1] : zF) ^ j +> (([0, 1,
                0] : zF) +> L0))))) <{{C}} (([1] : zF) +> r)) := by
    execute
  rw [S_ones2, S_ones2, S_ones1] at h3
  have h4 :=
      TT j (([1] : zF) +> (([1, 1] : zF) +> (([1, 1] : zF) +> (([0, 1,
      0] : zF) +> L0)))) (([1] : zF) +> r)
  set R2 : zB := ([0, 1, 1] : zF) ^ j +> (([1] : zF) +> r)
  have h5 : ((([1] : zF) +> (([1, 1] : zF) +> (([1, 1] : zF) +> (([0, 1,
      0] : zF) +> L0)))) <{{C}} R2) [target_tm]⊢⁺
            ((([1, 0] : zF) ^ p +> (([0] : zF) +> l)) <{{C}} (([0, 1, 0, 1, 0, 1, 1, 1, 1,
                1] : zF) +> R2)) := by
    dsimp [L0]
    execute
  have h6 := SW p (([0] : zF) +> l) (([0, 1, 0, 1, 0, 1, 1, 1, 1, 1] : zF) +> R2)
  have h7 : ((([0] : zF) +> l) <{{C}} (([0, 1] : zF) ^ p +> (([0, 1, 0, 1, 0, 1, 1, 1, 1,
      1] : zF) +> R2))) =
            (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (p + 2) +> (([1, 1, 1] : zF) +> (([1, 1,
                0] : zF) ^ j +> (([1, 1, 1] : zF) +> r)))))) := by
    have hrotR : (([0, 1] : zF) ^ p +> (([0, 1, 0, 1, 0, 1, 1, 1, 1, 1] : zF) +> R2)) =
                 ([0] : zF) +> (([1, 0] : zF) ^ (p + 2) +> (([1, 1, 1] : zF) +> (([1, 1,
                     0] : zF) ^ j +> (([1, 1, 1] : zF) +> r)))) := by
      change (([0, 1] : zF) ^ p +> (([0] : zF) +> (([1, 0] : zF) ^ 2 +> (([1, 1, 1] : zF) +> (([1,
          1] : zF) +> (([0, 1, 1] : zF) ^ j +> (([1] : zF) +> r))))))) = _
      rw [lpow_rot2 p 0 1, S_sh110 j (([1] : zF) +> r), str_app_assoc (([1, 0] : zF) ^ p) (([1,
          0] : zF) ^ 2), ← list_pow_add]
      rfl
    rw [hrotR]
    exact C_left_right l _
  rw [h7] at h6
  exact ReachesPlus.trans_star (ReachesPlus.trans_star (ReachesPlus.trans_star
      (ReachesPlus.trans_star h1 h2) (ReachesPlus.to_star h3)) h4) (ReachesPlus.trans_star h5 h6
      |> ReachesPlus.to_star)

theorem BITE0c3 (p : Nat) (l r : zB) :
    ((([1] : zF) +> (([0, 1] : zF) ^ p +> (([0, 0] : zF) +> l))) {{C}}> (([0, 0] : zF) +> (([1, 1,
        1,
        0, 0] : zF) +> r))) [target_tm]⊢⁺
    (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (p + 1) +> (([1, 1, 1, 1, 1, 1] : zF) +> r)))) :=
        by
  have hrotL : (([1] : zF) +> (([0, 1] : zF) ^ p +> (([0, 0] : zF) +> l))) =
               (([1, 0] : zF) +> (([1, 0] : zF) ^ p +> (([0] : zF) +> l))) := by
    change ([1] : zF) +> (([0, 1] : zF) ^ p +> (([0] : zF) +> (([0] : zF) +> l))) = _
    rw [lpow_rot2 p 0 1]
    rfl
  rw [hrotL]
  have h1 : ((([1, 0] : zF) +> (([1, 0] : zF) ^ p +> (([0] : zF) +> l))) {{C}}> (([0,
      0] : zF) +> (([1, 1, 1, 0, 0] : zF) +> r))) [target_tm]⊢⁺
            ((([1, 0] : zF) ^ p +> (([0] : zF) +> l)) <{{C}} (([0, 1, 0, 1, 1, 1, 1, 1,
                1] : zF) +> r)) := by
    execute
  have h2 := SW p (([0] : zF) +> l) (([0, 1, 0, 1, 1, 1, 1, 1, 1] : zF) +> r)
  have h3 : ((([0] : zF) +> l) <{{C}} (([0, 1] : zF) ^ p +> (([0, 1, 0, 1, 1, 1, 1, 1,
      1] : zF) +> r))) =
            (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (p + 1) +> (([1, 1, 1, 1, 1,
                1] : zF) +> r)))) := by
    have hrotR : (([0, 1] : zF) ^ p +> (([0, 1, 0, 1, 1, 1, 1, 1, 1] : zF) +> r)) =
                 ([0] : zF) +> (([1, 0] : zF) ^ (p + 1) +> (([1, 1, 1, 1, 1, 1] : zF) +> r)) := by
      change (([0, 1] : zF) ^ p +> (([0] : zF) +> (([1, 0] : zF) +> (([1, 1, 1, 1, 1,
          1] : zF) +> r)))) = _
      rw [lpow_rot2 p 0 1, str_app_assoc (([1, 0] : zF) ^ p) ([1, 0] : zF), list_pow_append_one]
    rw [hrotR]
    exact C_left_right l _
  rw [h3] at h2
  exact ReachesPlus.trans_star h1 h2

-- Zone and Digit Lemmas

def bitc (v : Nat) : Fin 2 := if v % 2 = 1 then 0 else 1

def dg : Nat → Nat → zF
  | 0, _ => []
  | L + 1, v => [1, 1, bitc v] ++ dg L (v / 2)

def zone (r L v : Nat) : zF := ([1] : zF) ^ r ++ dg L v ++ [1, 1, 1]

theorem bitc_even (v : Nat) : bitc (2 * v) = 1 := by
  unfold bitc
  have h : (2 * v) % 2 = 0 := by omega
  simp [h]

theorem bitc_odd (v : Nat) : bitc (2 * v + 1) = 0 := by
  unfold bitc
  have h : (2 * v + 1) % 2 = 1 := by omega
  simp [h]

theorem div2_odd (v : Nat) : (2 * v + 1) / 2 = v := by omega

theorem dg_even (L v : Nat) : dg (L + 1) (2 * v) = [1, 1, 1] ++ dg L v := by
  simp [dg, bitc_even]

theorem dg_odd (L v : Nat) : dg (L + 1) (2 * v + 1) = [1, 1, 0] ++ dg L v := by
  simp [dg, bitc_odd, div2_odd]

theorem pow_pos (P : Nat) : 1 ≤ 2 ^ P := Nat.one_le_two_pow

theorem pow2_succ (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by ring

theorem dg_zero (L : Nat) : dg L 0 = ([1, 1, 1] : zF) ^ L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [dg, show bitc 0 = 1 from rfl, show 0 / 2 = 0 from rfl, ih, pow_succ_list]

theorem dg_full (L : Nat) : dg L (2 ^ L - 1) = ([1, 1, 0] : zF) ^ L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    have h1 : 2 ^ (L + 1) - 1 = 2 * (2 ^ L - 1) + 1 := by
      have := pow_pos L
      rw [pow2_succ]
      omega
    rw [h1, dg_odd, ih, pow_succ_list]

theorem dg_low (b L o : Nat) :
    dg (b + (L + 1)) (2 ^ b * (2 * o + 1)) = ([1, 1, 1] : zF) ^ b ++ [1, 1, 0] ++ dg L o := by
  induction b with
  | zero =>
    rw [Nat.zero_add, Nat.pow_zero, Nat.one_mul, dg_odd]
    rfl
  | succ b ih =>
    have h1 : 2 ^ (b + 1) * (2 * o + 1) = 2 * (2 ^ b * (2 * o + 1)) := by ring
    rw [Nat.succ_add, h1, dg_even, ih, pow_succ_list]
    simp only [List.append_assoc]

theorem dg_lowones (k L o : Nat) :
    dg (k + (L + 1)) (2 ^ k - 1 + 2 ^ (k + 1) * o) = ([1, 1, 0] : zF) ^ k ++ [1, 1, 1] ++ dg L o :=
        by
  induction k with
  | zero =>
    have h1 : 2 ^ 0 - 1 + 2 ^ 1 * o = 2 * o := by omega
    rw [Nat.zero_add, h1, dg_even]
    rfl
  | succ k ih =>
    have h1 : 2 ^ (k + 1) - 1 + 2 ^ (k + 2) * o = 2 * (2 ^ k - 1 + 2 ^ (k + 1) * o) + 1 := by
      have := pow_pos k
      have : 2 ^ (k + 1) = 2 * 2 ^ k := pow2_succ k
      have : 2 ^ (k + 2) * o = 4 * (2 ^ k * o) := by rw [pow2_succ, pow2_succ]; ring
      have : 2 ^ (k + 1) * o = 2 * (2 ^ k * o) := by rw [pow2_succ]; ring
      omega
    rw [Nat.succ_add, h1, dg_odd, ih, pow_succ_list]
    simp only [List.append_assoc]

theorem nat_strong_ind {P : Nat → Prop} (h : ∀ n, (∀ m < n, P m) → P n) (n : Nat) : P n :=
  h n (fun m _ => nat_strong_ind h m)

theorem lowbit (x : Nat) (hx : x ≠ 0) : ∃ P o, x = 2 ^ P * (2 * o + 1) := by
  refine @nat_strong_ind (fun x => x ≠ 0 → ∃ P o, x = 2 ^ P * (2 * o + 1)) (fun x ih hx => ?_) x hx
  rcases Nat.even_or_odd' x with ⟨x', rfl | rfl⟩
  · rcases ih x' (by omega) (by omega) with ⟨P, o, ho⟩
    exact ⟨P + 1, o, by rw [ho]; ring⟩
  · exact ⟨0, x', by ring⟩

theorem lowbit_lt (b o L : Nat) (h : 2 ^ b * (2 * o + 1) < 2 ^ L) : b < L ∧ o < 2 ^ (L - b - 1) :=
    by
  have hb : b < L := by
    by_cases hlt : b < L
    · exact hlt
    · have hle : 2 ^ L ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
      have hp := pow_pos b
      nlinarith
  refine ⟨hb, ?_⟩
  have hL : L = b + (L - b - 1 + 1) := by omega
  rw [hL, Nat.pow_add, pow2_succ] at h
  have hp := pow_pos b
  nlinarith

theorem default_zero : (default : zB) = ([0] : zF) +> default := ListBlank.cons_zero_default.symm

def RT (l : zB) (q : Nat) (Z : zF) : Cfg (Fin 2) (Fin 6) :=
  l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ q +> (Z +> default)))

theorem R1z (l : zB) (q L v : Nat) (h1 : 1 ≤ v) (h2 : v < 2 ^ L) :
    (RT l (q + 3) (zone 0 L v)) [target_tm]⊢⁺ (RT (([1, 0, 1,
        0] : zF) +> l) (q + 1) (zone 0 L (v - 1))) := by
  rcases lowbit v (by omega) with ⟨b, o, rfl⟩
  rcases lowbit_lt b o L h2 with ⟨hb, ho⟩
  set L' := L - b - 1
  have hL : L = b + (L' + 1) := by omega
  have hv : 2 ^ b * (2 * o + 1) - 1 = 2 ^ b - 1 + 2 ^ (b + 1) * o := by
    have : 2 ^ b * (2 * o + 1) = 2 ^ b + 2 ^ (b + 1) * o := by ring
    have := pow_pos b
    omega
  rw [hL, hv]
  unfold RT zone
  rw [dg_low, dg_lowones]
  simp only [← str_app_assoc, pow_zero_list, listblank_append_nil]
  exact RND2 q b l (dg L' o +> (([1, 1, 1] : zF) +> default))

theorem R1t (l : zB) (q L v : Nat) (h1 : 1 ≤ v) (h2 : v < 2 ^ L) :
    (RT l (q + 3) (zone 2 L v)) [target_tm]⊢⁺ (RT (([1, 0, 1,
        0] : zF) +> l) (q + 1) (zone 2 L (v - 1))) := by
  rcases lowbit v (by omega) with ⟨b, o, rfl⟩
  rcases lowbit_lt b o L h2 with ⟨hb, ho⟩
  set L' := L - b - 1
  have hL : L = b + (L' + 1) := by omega
  have hv : 2 ^ b * (2 * o + 1) - 1 = 2 ^ b - 1 + 2 ^ (b + 1) * o := by
    have : 2 ^ b * (2 * o + 1) = 2 ^ b + 2 ^ (b + 1) * o := by ring
    have := pow_pos b
    omega
  rw [hL, hv]
  unfold RT zone
  rw [dg_low, dg_lowones]
  simp only [← str_app_assoc]
  set R : zB := dg L' o +> (([1, 1, 1] : zF) +> default)
  have hLHS : (([1] : zF) ^ 2 +> (([1, 1, 1] : zF) ^ b +> (([1, 1, 0] : zF) +> R))) =
              (([1, 1, 1] : zF) ^ b +> (([1, 1, 1, 1, 0] : zF) +> R)) := by
    change (([1, 1] : zF) +> (([1, 1, 1] : zF) ^ b +> (([1, 1, 0] : zF) +> R))) = _
    rw [S_ones2, str_app_assoc ([1, 1] : zF) ([1, 1, 0] : zF)]
    rfl
  have hRHS : (([1, 1, 1, 1] : zF) +> (([0, 1, 1] : zF) ^ b +> (([1] : zF) +> R))) =
              (([1] : zF) ^ 2 +> (([1, 1, 0] : zF) ^ b +> (([1, 1, 1] : zF) +> R))) := by
    change (([1, 1] : zF) +> (([1, 1] : zF) +> (([0, 1, 1] : zF) ^ b +> (([1] : zF) +> R)))) =
           (([1, 1] : zF) +> (([1, 1, 0] : zF) ^ b +> (([1, 1, 1] : zF) +> R)))
    rw [S_sh110 b (([1] : zF) +> R), str_app_assoc ([1, 1] : zF) ([1] : zF)]
    rfl
  rw [hLHS, ← hRHS]
  exact RND1 q b l R

theorem R2r (l : zB) (q L v : Nat) (h1 : 1 ≤ v) (h2 : v < 2 ^ L) :
    (RT l (q + 3) (zone 1 L v)) [target_tm]⊢⁺ (RT (([1, 0, 1,
        0] : zF) +> l) q (zone 0 (L + 1) (2 * v - 2))) := by
  rcases lowbit v (by omega) with ⟨b, o, rfl⟩
  rcases lowbit_lt b o L h2 with ⟨hb, ho⟩
  set L' := L - b - 1
  have hL : L = b + (L' + 1) := by omega
  have hv : 2 * (2 ^ b * (2 * o + 1)) - 2 = 2 * (2 ^ b - 1 + 2 ^ (b + 1) * o) := by
    have : 2 ^ b * (2 * o + 1) = 2 ^ b + 2 ^ (b + 1) * o := by ring
    have := pow_pos b
    omega
  rw [hL, hv]
  unfold RT zone
  rw [dg_low, dg_even, dg_lowones]
  simp only [← str_app_assoc, pow_zero_list, listblank_append_nil]
  set R : zB := dg L' o +> (([1, 1, 1] : zF) +> default)
  have hLHS : (([1] : zF) ^ 1 +> (([1, 1, 1] : zF) ^ b +> (([1, 1, 0] : zF) +> R))) =
              (([1, 1, 1] : zF) ^ b +> (([1, 1, 1, 0] : zF) +> R)) := by
    change (([1] : zF) +> (([1, 1, 1] : zF) ^ b +> (([1, 1, 0] : zF) +> R))) = _
    rw [S_ones1, str_app_assoc ([1] : zF) ([1, 1, 0] : zF)]
    rfl
  have hRHS : (([1, 1, 1, 1, 1] : zF) +> (([0, 1, 1] : zF) ^ b +> (([1] : zF) +> R))) =
              (([1, 1, 1] : zF) +> (([1, 1, 0] : zF) ^ b +> (([1, 1, 1] : zF) +> R))) := by
    change (([1, 1, 1] : zF) +> (([1, 1] : zF) +> (([0, 1, 1] : zF) ^ b +> (([1] : zF) +> R)))) = _
    rw [S_sh110 b (([1] : zF) +> R), str_app_assoc ([1, 1] : zF) ([1] : zF)]
    rfl
  rw [hLHS, ← hRHS]
  exact RND0 q b l R

theorem O2r (l : zB) (q L : Nat) :
    (RT l (q + 3) (zone 2 L 0)) [target_tm]⊢⁺ (RT (([1, 0, 1,
        0] : zF) +> l) (q + 1) (zone 0 (L + 1) (2 ^ (L + 1) - 1))) := by
  unfold RT zone
  rw [dg_zero, dg_full]
  simp only [← str_app_assoc, pow_zero_list, listblank_append_nil]
  have hE : (([1] : zF) ^ 2 +> (([1, 1, 1] : zF) ^ L +> (([1, 1, 1] : zF) +> default))) =
            (([1, 1, 1] : zF) ^ (L + 1) +> (([1, 1, 0] : zF) +> default)) := by
    change (([1, 1] : zF) +> (([1, 1, 1] : zF) ^ L +> (([1, 1, 1] : zF) +> default))) = _
    rw [S_ones2, str_app_assoc ([1, 1] : zF) ([1, 1, 1] : zF)]
    change (([1, 1, 1] : zF) ^ L +> (([1, 1, 1] : zF) +> (([1, 1] : zF) +> default))) = _
    rw [str_app_assoc (([1, 1, 1] : zF) ^ L) ([1, 1, 1] : zF), list_pow_append_one]
    conv_lhs => rw [default_zero]
    rw [str_app_assoc ([1, 1] : zF) ([0] : zF)]
    rfl
  rw [hE]
  exact RND2 q (L + 1) l default

theorem O1r (l : zB) (q L : Nat) :
    (RT l (q + 3) (zone 1 L 0)) [target_tm]⊢⁺ (RT (([1, 0, 1,
        0] : zF) +> l) (q + 1) (zone 2 L (2 ^ L - 1))) := by
  unfold RT zone
  rw [dg_zero, dg_full]
  simp only [← str_app_assoc]
  have hLHS : (([1] : zF) ^ 1 +> (([1, 1, 1] : zF) ^ L +> (([1, 1, 1] : zF) +> default))) =
              (([1, 1, 1] : zF) ^ L +> (([1, 1, 1, 1, 0] : zF) +> default)) := by
    change (([1] : zF) +> (([1, 1, 1] : zF) ^ L +> (([1, 1, 1] : zF) +> default))) = _
    rw [S_ones1]
    conv_lhs => rw [default_zero]
    rfl
  have hRHS : (([1, 1, 1, 1] : zF) +> (([0, 1, 1] : zF) ^ L +> (([1] : zF) +> default))) =
              (([1] : zF) ^ 2 +> (([1, 1, 0] : zF) ^ L +> (([1, 1, 1] : zF) +> default))) := by
    change (([1, 1] : zF) +> (([1, 1] : zF) +> (([0, 1, 1] : zF) ^ L +> (([1] : zF) +> default)))) =
           (([1, 1] : zF) +> (([1, 1, 0] : zF) ^ L +> (([1, 1, 1] : zF) +> default)))
    rw [S_sh110 L (([1] : zF) +> default), str_app_assoc ([1, 1] : zF) ([1] : zF)]
    rfl
  rw [hLHS, ← hRHS]
  exact RND1 q L l default

theorem O0r (l : zB) (q L : Nat) :
    (RT l (q + 3) (zone 0 L 0)) [target_tm]⊢⁺ (RT (([1, 0, 1,
        0] : zF) +> l) q (zone 0 (L + 1) (2 ^ (L + 1) - 2))) := by
  have hv : 2 ^ (L + 1) - 2 = 2 * (2 ^ L - 1) := by
    have := pow_pos L
    rw [pow2_succ]
    omega
  rw [hv]
  unfold RT zone
  rw [dg_zero, dg_even, dg_full]
  simp only [← str_app_assoc, pow_zero_list, listblank_append_nil]
  have hLHS : (([1, 1, 1] : zF) ^ L +> (([1, 1, 1] : zF) +> default)) =
              (([1, 1, 1] : zF) ^ L +> (([1, 1, 1, 0] : zF) +> default)) := by
    conv_lhs => rw [default_zero]
    rw [str_app_assoc ([1, 1, 1] : zF) ([0] : zF)]
    rfl
  have hRHS : (([1, 1, 1, 1, 1] : zF) +> (([0, 1, 1] : zF) ^ L +> (([1] : zF) +> default))) =
              (([1, 1, 1] : zF) +> (([1, 1, 0] : zF) ^ L +> (([1, 1, 1] : zF) +> default))) := by
    change (([1, 1, 1] : zF) +> (([1, 1] : zF) +> (([0, 1,
        1] : zF) ^ L +> (([1] : zF) +> default)))) = _
    rw [S_sh110 L (([1] : zF) +> default), str_app_assoc ([1, 1] : zF) ([1] : zF)]
    rfl
  rw [hLHS, ← hRHS]
  exact RND0 q L l default

def FR (p : Nat) (l : zB) : zB := ([1] : zF) +> (([0, 1] : zF) ^ p +> (([0, 0] : zF) +> l))

theorem PUSHr (l : zB) (k L o : Nat) :
    (RT l 2 (zone 0 (k + (L + 1)) (2 ^ k - 1 + 2 ^ (k + 1) * o))) [target_tm]⊢⁺
    (RT (([1, 0, 0] : zF) ^ k +> (([1, 0, 1, 0] : zF) +> l)) 1 (zone 1 L o)) := by
  unfold RT zone
  rw [dg_lowones]
  simp only [← str_app_assoc, pow_zero_list, listblank_append_nil]
  exact PUSH k l (dg L o +> (([1, 1, 1] : zF) +> default))

theorem B1z0 (p : Nat) (l : zB) (L v : Nat) :
    (RT (FR p l) 1 (zone 0 (L + 1) (2 * v))) [target_tm]⊢⁺ (RT l (p + 3) (zone 2 L v)) := by
  unfold RT FR zone
  rw [dg_even]
  simp only [← str_app_assoc, pow_zero_list, listblank_append_nil]
  exact BITE1 p l (([1] : zF) +> (dg L v +> (([1, 1, 1] : zF) +> default)))

theorem B1z1 (p : Nat) (l : zB) (L v : Nat) :
    (RT (FR p l) 1 (zone 0 (L + 1) (2 * v + 1))) [target_tm]⊢⁺ (RT l (p + 4) (zone 0 L v)) := by
  unfold RT FR zone
  rw [dg_odd]
  simp only [← str_app_assoc, pow_zero_list, listblank_append_nil]
  have h1 := BITE1 p l (([0] : zF) +> (dg L v +> (([1, 1, 1] : zF) +> default)))
  have h2 : (([1, 0] : zF) ^ (p + 3) +> (([1] : zF) +> (([0] : zF) +> (dg L v +> (([1, 1,
      1] : zF) +> default))))) =
            (([1, 0] : zF) ^ (p + 4) +> (dg L v +> (([1, 1, 1] : zF) +> default))) := by
    change (([1, 0] : zF) ^ (p + 3) +> (([1, 0] : zF) +> (dg L v +> (([1, 1,
        1] : zF) +> default)))) = _
    rw [str_app_assoc (([1, 0] : zF) ^ (p + 3)) ([1, 0] : zF), list_pow_append_one]
  rw [h2] at h1
  exact h1

theorem B1o (p : Nat) (l : zB) (L v : Nat) :
    (RT (FR p l) 1 (zone 1 L v)) [target_tm]⊢⁺ (RT l (p + 3) (zone 0 L v)) := by
  unfold RT FR zone
  cases L with
  | zero =>
    dsimp [dg]
    exact BITE1 p l (([1, 1] : zF) +> default)
  | succ L =>
    dsimp [dg]
    simp only [← str_app_assoc]
    exact BITE1 p l (([1, bitc v] : zF) +> (dg L (v / 2) +> (([1, 1, 1] : zF) +> default)))

theorem B1t (p : Nat) (l : zB) (L v : Nat) :
    (RT (FR p l) 1 (zone 2 L v)) [target_tm]⊢⁺ (RT l (p + 3) (zone 1 L v)) := by
  unfold RT FR zone
  simp only [← str_app_assoc]
  exact BITE1 p l (dg L v +> (([1, 1, 1] : zF) +> default))

theorem B0r (p : Nat) (l : zB) (b L o : Nat) :
    (RT (FR p l) 0 (zone 0 (b + 1 + (L + 1)) (2 ^ (b + 1) * (2 * o + 1)))) [target_tm]⊢⁺
    (RT l (p + 3) (zone 0 (b + (L + 1)) (2 ^ b - 1 + 2 ^ (b + 1) * o))) := by
  unfold RT FR zone
  rw [dg_low, dg_lowones]
  simp only [← str_app_assoc, pow_zero_list, listblank_append_nil]
  set R : zB := dg L o +> (([1, 1, 1] : zF) +> default)
  have h1 := BITE0 p (b + 1) l R
  have h2 : (([1, 0] : zF) ^ (p + 2) +> (([1] : zF) +> (([0, 1,
      1] : zF) ^ (b + 1) +> (([1] : zF) +> R)))) =
            (([1, 0] : zF) ^ (p + 3) +> (([1, 1, 0] : zF) ^ b +> (([1, 1, 1] : zF) +> R))) := by
    rw [pow_succ_list ([0, 1, 1] : zF) b, ← str_app_assoc ([0, 1, 1] : zF)]
    change (([1, 0] : zF) ^ (p + 2) +> (([1, 0] : zF) +> (([1, 1] : zF) +> (([0, 1,
        1] : zF) ^ b +> (([1] : zF) +> R))))) = _
    rw [S_sh110 b (([1] : zF) +> R)]
    change (([1, 0] : zF) ^ (p + 2) +> (([1, 0] : zF) +> (([1, 1, 0] : zF) ^ b +> (([1, 1,
        1] : zF) +> R)))) = _
    rw [str_app_assoc (([1, 0] : zF) ^ (p + 2)) ([1, 0] : zF), list_pow_append_one]
  rw [h2] at h1
  exact h1

theorem B0cr (p : Nat) (l : zB) (L : Nat) :
    (RT (FR p l) 0 (zone 0 (L + 1) 0)) [target_tm]⊢⁺ (RT l (p + 2) (zone 0 (L + 1) (2 ^ (L + 1) -
        2))) := by
  have hv : 2 ^ (L + 1) - 2 = 2 * (2 ^ L - 1) := by
    have := pow_pos L
    rw [pow2_succ]
    omega
  rw [hv]
  unfold RT FR zone
  rw [dg_zero, dg_even, dg_full]
  simp only [← str_app_assoc, pow_zero_list, listblank_append_nil]
  have hE : (([1, 1, 1] : zF) ^ (L + 1) +> (([1, 1, 1] : zF) +> default)) =
            (([1, 1, 1] : zF) ^ L +> (([1, 1, 1, 1, 1, 1, 0] : zF) +> default)) := by
    rw [← list_pow_append_one, ← str_app_assoc (([1, 1, 1] : zF) ^ L) ([1, 1, 1] : zF)]
    conv_lhs => rw [default_zero]
    rfl
  rw [hE]
  exact BITE0c p L l default

theorem B0c3r (p : Nat) (l : zB) :
    (RT (FR p l) 0 (zone 0 0 0)) [target_tm]⊢⁺ (RT l (p + 1) (zone 0 1 0)) := by
  unfold RT FR
  change ((([1] : zF) +> (([0, 1] : zF) ^ p +> (([0, 0] : zF) +> l))) {{C}}>
          (([0, 0] : zF) +> (([1, 0] : zF) ^ 0 +> (([1, 1, 1] : zF) +> default)))) [target_tm]⊢⁺
         (l {{C}}> (([0, 0] : zF) +> (([1, 0] : zF) ^ (p + 1) +> (([1, 1, 1, 1, 1,
             1] : zF) +> default))))
  simp only [pow_zero_list, listblank_append_nil]
  have hE : (([1, 1, 1] : zF) +> default) = (([1, 1, 1, 0, 0] : zF) +> default) := by
    conv_lhs => rw [default_zero]
    conv_lhs => rw [default_zero]
    rfl
  rw [hE]
  exact BITE0c3 p l default

theorem FR_round (p : Nat) (l : zB) :
    (([1, 0, 1, 0] : zF) +> FR p l) = FR (p + 2) l := by
  unfold FR
  have hp : p + 2 = (p + 1) + 1 := rfl
  rw [hp, pow_succ_list, pow_succ_list, ← str_app_assoc, ← str_app_assoc]
  rfl

theorem init_step : (init []) [target_tm]⊢* RT default 6 (zone 2 0 0) := by
  have h1 : (init []) [target_tm]⊢⁺ (default {{C}}> (([0, 0, 1, 0, 1, 0, 1] : zF) +> default)) := by
    unfold init
    rw [tape_mk1_nil]
    change (default {{A}}> default) [target_tm]⊢⁺ _
    execute
  have h2 : (default {{C}}> (([0, 0, 1, 0, 1, 0, 1] : zF) +> default)) [target_tm]⊢⁺
            RT default 3 (zone 0 0 0) := by
    unfold RT zone dg
    execute
  have hFR1 : (([1, 0, 1, 0] : zF) +> default) = FR 1 default := by
    unfold FR
    conv_lhs => rw [default_zero]
    rfl
  have h3 := O0r default 0 0
  rw [hFR1] at h3
  have h4 := B0cr 1 default 0
  have h5 := O0r default 0 1
  rw [hFR1] at h5
  have h6 := B0r 1 default 0 0 0
  have h7 := O0r default 1 1
  rw [hFR1] at h7
  have h8 := B1z0 1 default 1 1
  have h9 := R1t default 1 1 1 (by omega) (by decide)
  rw [hFR1] at h9
  have h10 : (RT (FR 1 default) 2 (zone 2 1 0)) [target_tm]⊢⁺ RT default 6 (zone 2 0 0) := by
    unfold RT FR zone dg
    execute
  exact ReachesPlus.to_star (stepPlus_trans h1 (stepPlus_trans h2 (stepPlus_trans h3
      (stepPlus_trans h4
    (stepPlus_trans h5 (stepPlus_trans h6 (stepPlus_trans h7 (stepPlus_trans h8
    (stepPlus_trans h9 h10)))))))))

def lev (P : Nat) (l : zB) : zB :=
  match P with
  | 0 => l
  | p + 1 => FR p l

def okL (P : Nat) (l : zB) : Prop := P = 0 → l = default

theorem lev_round (P : Nat) (l : zB) (h : okL P l) :
    (([1, 0, 1, 0] : zF) +> lev P l) = lev (P + 2) l := by
  cases P with
  | zero =>
    have hl := h rfl
    subst hl
    unfold lev FR
    conv_lhs => rw [default_zero]
    rfl
  | succ p =>
    change (([1, 0, 1, 0] : zF) +> FR p l) = FR (p + 2) l
    exact FR_round p l

theorem okL_S (P : Nat) (l : zB) : okL (P + 1) l := by
  intro h
  omega

inductive Rnd : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop where
  | RR1z (q L v : Nat) (h : 1 ≤ v) : Rnd (q + 3) 0 L v (q + 1) 0 L (v - 1)
  | RR1t (q L v : Nat) (h : 1 ≤ v) : Rnd (q + 3) 2 L v (q + 1) 2 L (v - 1)
  | RR2 (q L v : Nat) (h : 1 ≤ v) : Rnd (q + 3) 1 L v q 0 (L + 1) (2 * v - 2)
  | RO2 (q L : Nat) : Rnd (q + 3) 2 L 0 (q + 1) 0 (L + 1) (2 ^ (L + 1) - 1)
  | RO1 (q L : Nat) : Rnd (q + 3) 1 L 0 (q + 1) 2 L (2 ^ L - 1)
  | RO0 (q L : Nat) : Rnd (q + 3) 0 L 0 q 0 (L + 1) (2 ^ (L + 1) - 2)

theorem Rnd_tape (q r L v q' r' L' v' P : Nat) (l : zB)
    (h : Rnd q r L v q' r' L' v') (hv : v < 2 ^ L) (hl : okL P l) :
    (RT (lev P l) q (zone r L v)) [target_tm]⊢⁺ (RT (lev (P + 2) l) q' (zone r' L' v')) := by
  rw [← lev_round P l hl]
  cases h with
  | RR1z q0 _ _ h1 => exact R1z (lev P l) q0 L v h1 hv
  | RR1t q0 _ _ h1 => exact R1t (lev P l) q0 L v h1 hv
  | RR2 _ _ _ h1 => exact R2r (lev P l) q' L v h1 hv
  | RO2 q0 _ => exact O2r (lev P l) q0 L
  | RO1 q0 _ => exact O1r (lev P l) q0 L
  | RO0 _ _ => exact O0r (lev P l) q' L

theorem Rnd_valid (q r L v q' r' L' v' : Nat)
    (h : Rnd q r L v q' r' L' v') (hv : v < 2 ^ L) (hr : r < 3) :
    v' < 2 ^ L' ∧ r' < 3 := by
  have hL := pow_pos L
  cases h <;> (try simp only [pow2_succ] at *) <;> omega

theorem Rnd_exists (q r L v : Nat) (hq : 3 ≤ q) (hr : r < 3) :
    ∃ q' r' L' v', Rnd q r L v q' r' L' v' := by
  have hq' : q = (q - 3) + 3 := by omega
  rw [hq']
  by_cases hv : v = 0
  · subst hv
    rcases r with _ | _ | _ | r
    · exact ⟨_, _, _, _, Rnd.RO0 (q - 3) L⟩
    · exact ⟨_, _, _, _, Rnd.RO1 (q - 3) L⟩
    · exact ⟨_, _, _, _, Rnd.RO2 (q - 3) L⟩
    · omega
  · rcases r with _ | _ | _ | r
    · exact ⟨_, _, _, _, Rnd.RR1z (q - 3) L v (by omega)⟩
    · exact ⟨_, _, _, _, Rnd.RR2 (q - 3) L v (by omega)⟩
    · exact ⟨_, _, _, _, Rnd.RR1t (q - 3) L v (by omega)⟩
    · omega

theorem okL_ge (P : Nat) (l : zB) (h : 1 ≤ P) : okL P l := by
  cases P with
  | zero => omega
  | succ p => exact okL_S p l

-- High-Level Invariants and Induction (`cap`, `Kst`, `Jst`, `Mv`, `Qv`, `Ist`, `EB`, `safe`, `U`,
-- `cycles`)

def cap (r L : Nat) : Nat :=
  match r with
  | 1 => L + 1
  | _ => L

@[simp] theorem cap0 (L : Nat) : cap 0 L = L := rfl
@[simp] theorem cap1 (L : Nat) : cap 1 L = L + 1 := rfl
@[simp] theorem cap2 (L : Nat) : cap 2 L = L := rfl

theorem pow2_1 (L : Nat) : 2 ^ (L + 1) = 2 * 2 ^ L := pow2_succ L
theorem pow2_2 (L : Nat) : 2 ^ (L + 2) = 4 * 2 ^ L := by
  rw [show L + 2 = (L + 1) + 1 by omega, pow2_succ, pow2_succ]; ring
theorem pow2_3 (L : Nat) : 2 ^ (L + 3) = 8 * 2 ^ L := by
  rw [show L + 3 = (L + 2) + 1 by omega, pow2_succ, pow2_2]; ring
theorem pow2_4 (L : Nat) : 2 ^ (L + 4) = 16 * 2 ^ L := by
  rw [show L + 4 = (L + 3) + 1 by omega, pow2_succ, pow2_3]; ring

def Kst (n r L : Nat) : Prop := 2 ^ (cap r L + 1) + 2 ≤ n

def Jst (n r : Nat) : Prop := 3 ≤ n ∧ (r ≠ 0 → n % 2 = 1)

def Mv (n r L v : Nat) : Nat :=
  match r with
  | 1 => (n + v + 2 * 2 ^ (L + 3)) % 3
  | _ => (n + 2 * v + 2 * 2 ^ (L + 2)) % 3

@[simp] theorem Mv0 (n L v : Nat) : Mv n 0 L v = (n + 2 * v + 2 * 2 ^ (L + 2)) % 3 := rfl
@[simp] theorem Mv1 (n L v : Nat) : Mv n 1 L v = (n + v + 2 * 2 ^ (L + 3)) % 3 := rfl
@[simp] theorem Mv2 (n L v : Nat) : Mv n 2 L v = (n + 2 * v + 2 * 2 ^ (L + 2)) % 3 := rfl

def Qv (P q r L v : Nat) : Nat := (Mv q r L v + 2 * P) % 3

def Ist (n r L v : Nat) : Prop :=
  r < 3 ∧ v < 2 ^ L ∧ Kst n r L ∧ Mv n r L v ≠ 0 ∧ ¬ (n = 6 ∧ r = 1 ∧ L = 0 ∧ v = 0)

theorem init_I : Ist 6 2 0 0 := by
  unfold Ist Kst Mv cap
  decide

theorem Rnd_sign (P q r L v q' r' L' v' : Nat) (h : Rnd q r L v q' r' L' v') :
    Qv P q r L v = Qv (P + 2) q' r' L' v' := by
  unfold Qv
  have hL := pow_pos L
  cases h <;> simp only [Mv0, Mv1, Mv2, pow2_1] at * <;> omega

inductive EB : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop where
  | EB1z0 (L v : Nat) : EB 1 0 (L + 1) (2 * v) 2 2 L v
  | EB1z1 (L v : Nat) : EB 1 0 (L + 1) (2 * v + 1) 3 0 L v
  | EB1o (L v : Nat) : EB 1 1 L v 2 0 L v
  | EB1t (L v : Nat) : EB 1 2 L v 2 1 L v
  | EB0 (b L o : Nat) : EB 0 0 (b + 1 + (L + 1)) (2 ^ (b + 1) * (2 * o + 1)) 2 0 (b + (L + 1)) (2 ^
      b -
      1 + 2 ^ (b + 1) * o)
  | EB0c (L : Nat) : EB 0 0 (L + 1) 0 1 0 (L + 1) (2 ^ (L + 1) - 2)
  | EB0c3 : EB 0 0 0 0 0 0 1 0

theorem EB_tape (q r L v e r' L' v' p : Nat) (l : zB) (h : EB q r L v e r' L' v') :
    (RT (FR p l) q (zone r L v)) [target_tm]⊢⁺ (RT l (p + 1 + e) (zone r' L' v')) := by
  cases h with
  | EB1z0 =>
    rw [show p + 1 + 2 = p + 3 by omega]
    exact B1z0 p l L' v'
  | EB1z1 =>
    rw [show p + 1 + 3 = p + 4 by omega]
    exact B1z1 p l L' v'
  | EB1o =>
    rw [show p + 1 + 2 = p + 3 by omega]
    exact B1o p l L v
  | EB1t =>
    rw [show p + 1 + 2 = p + 3 by omega]
    exact B1t p l L v
  | EB0 b L0 o =>
    rw [show p + 1 + 2 = p + 3 by omega]
    exact B0r p l b L0 o
  | EB0c L0 =>
    rw [show p + 1 + 1 = p + 2 by omega]
    exact B0cr p l L0
  | EB0c3 =>
    rw [show p + 1 + 0 = p + 1 by omega]
    exact B0c3r p l

theorem EB_sign (q r L v e r' L' v' P : Nat) (h : EB q r L v e r' L' v') :
    (Mv (P + e) r' L' v' + Qv P q r L v) % 3 = 0 := by
  unfold Qv
  cases h with
  | EB1z0 =>
    have := pow_pos L'
    simp only [Mv0, Mv2, pow2_1] at *
    omega
  | EB1z1 =>
    have := pow_pos L'
    simp only [Mv0, pow2_1] at *
    omega
  | EB1o =>
    have := pow_pos L
    simp only [Mv0, Mv1, pow2_1] at *
    omega
  | EB1t =>
    have := pow_pos L
    simp only [Mv1, Mv2, pow2_1] at *
    omega
  | EB0 b L0 o =>
    have hb := pow_pos b
    have hL := pow_pos (b + L0)
    have h1 : 2 ^ (b + 1) * (2 * o + 1) = 4 * (2 ^ b * o) + 2 * 2 ^ b := by
      rw [pow2_succ]; ring
    have h2 : 2 ^ b - 1 + 2 ^ (b + 1) * o = 2 ^ b - 1 + 2 * (2 ^ b * o) := by
      rw [pow2_succ]; ring
    have h3 : 2 ^ (b + 1 + (L0 + 1) + 2) = 16 * 2 ^ (b + L0) := by
      rw [show b + 1 + (L0 + 1) + 2 = (b + L0) + 4 by omega, pow2_4]
    have h4 : 2 ^ (b + (L0 + 1) + 2) = 8 * 2 ^ (b + L0) := by
      rw [show b + (L0 + 1) + 2 = (b + L0) + 3 by omega, pow2_3]
    simp only [Mv0]
    rw [h1, h2, h3, h4]
    omega
  | EB0c L0 =>
    have := pow_pos L0
    simp only [Mv0, pow2_1] at *
    omega
  | EB0c3 =>
    simp only [Mv0]
    omega

theorem iter_FR0 (k : Nat) (X : zB) :
    (([1, 0, 0] : zF) ^ k +> X) = (FR 0)^[k] X := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, pow_succ_list, ← str_app_assoc, ih]
    rfl

theorem PUSH_lev (k L o P : Nat) (l : zB) (hl : okL P l) :
    (RT (lev P l) 2 (zone 0 (k + (L + 1)) (2 ^ k - 1 + 2 ^ (k + 1) * o))) [target_tm]⊢⁺
    (RT ((FR 0)^[k] (lev (P + 2) l)) 1 (zone 1 L o)) := by
  rw [← lev_round P l hl, ← iter_FR0]
  exact PUSHr (lev P l) k L o

theorem inner1 (k L o : Nat) (X : zB) :
    (RT ((FR 0)^[k + 1] X) 1 (zone 1 L o)) [target_tm]⊢⁺ (RT ((FR 0)^[k] X) 3 (zone 0 L o)) := by
  rw [Function.iterate_succ', Function.comp_apply]
  exact EB_tape 1 1 L o 2 0 L o 0 ((FR 0)^[k] X) (EB.EB1o L o)

def safe (c : Cfg (Fin 2) (Fin 6)) (N : Nat) : Prop :=
  ∀ M ≤ N, ∀ cfg, multiStep target_tm c M = some cfg → (step target_tm cfg).isSome

theorem safe_mono (c : Cfg (Fin 2) (Fin 6)) (N N' : Nat) (h : safe c N) (hle : N' ≤ N) : safe c
    N' := by
  intro M hM cfg hrun
  exact h M (by omega) cfg hrun

theorem multiStep_lt_isSome {c c' cfg : Cfg (Fin 2) (Fin 6)} {n M : Nat}
    (hn : c [target_tm]⊢^{n} c') (hM : c [target_tm]⊢^{M} cfg) (hlt : M < n) :
    (step target_tm cfg).isSome := by
  have hsplit : n = (M + 1) + (n - (M + 1)) := by omega
  rw [hsplit, multiStep_add, multiStep_succ', hM] at hn
  dsimp [Option.bind] at hn
  cases hstep : step target_tm cfg with
  | none => rw [hstep] at hn; simp at hn
  | some c2 => rfl

theorem multiStep_ge_drop {c c' cfg : Cfg (Fin 2) (Fin 6)} {n M : Nat}
    (hn : c [target_tm]⊢^{n} c') (hM : c [target_tm]⊢^{M} cfg) (hle : n ≤ M) :
    c' [target_tm]⊢^{M - n} cfg := by
  have hsplit : M = n + (M - n) := by omega
  rw [hsplit, multiStep_add, hn] at hM
  exact hM

theorem safe_ev (c c' : Cfg (Fin 2) (Fin 6)) (N : Nat)
    (h : c [target_tm]⊢* c') (hN : safe c' N) : safe c N := by
  rcases h with ⟨n, hn⟩
  intro M hM cfg hrun
  by_cases hle : n ≤ M
  · exact hN (M - n) (by omega) cfg (multiStep_ge_drop hn hrun hle)
  · exact multiStep_lt_isSome hn hrun (by omega)

theorem safe_prog (c c' : Cfg (Fin 2) (Fin 6)) (N : Nat)
    (h : c [target_tm]⊢⁺ c') (hN : safe c' (N - 1)) : safe c N := by
  rcases h with ⟨n, hn_pos, hn⟩
  intro M hM cfg hrun
  by_cases hle : n ≤ M
  · exact hN (M - n) (by omega) cfg (multiStep_ge_drop hn hrun hle)
  · exact multiStep_lt_isSome hn hrun (by omega)

theorem safe_prog0 (c c' : Cfg (Fin 2) (Fin 6))
    (h : c [target_tm]⊢⁺ c') : safe c 0 := by
  rcases h with ⟨n, hn_pos, hn⟩
  intro M hM cfg hrun
  exact multiStep_lt_isSome hn hrun (by omega)

theorem safe_RT0 (l : zB) (q : Nat) (Z : zF) : safe (RT l q Z) 0 := by
  intro M hM cfg hrun
  have hM0 : M = 0 := by omega
  subst hM0
  change some (RT l q Z) = some cfg at hrun
  injection hrun with hcfg
  subst hcfg
  unfold RT
  simp only [step, listblank_append_cons, Turing.ListBlank.head_cons]
  rfl

theorem phase (Inv : Nat → Nat → Nat → Nat → Nat → Prop)
    (Hstep : ∀ j q r L v q' r' L' v', Rnd q r L v q' r' L' v' → v < 2 ^ L →
       Inv j q r L v → Inv (j + 2) q' r' L' v')
    (q j P : Nat) (l : zB) (r L v : Nat)
    (hl : okL (P + j) l) (hr : r < 3) (hv : v < 2 ^ L) (hI : Inv j q r L v) :
    ∃ j' q' r' L' v', q' ≤ 2 ∧ r' < 3 ∧ v' < 2 ^ L' ∧ Inv j' q' r' L' v' ∧
      j ≤ j' ∧ (3 ≤ q → j + 2 ≤ j') ∧
      ((RT (lev (P + j) l) q (zone r L v)) [target_tm]⊢* (RT (lev (P + j') l) q' (zone r' L'
          v'))) := by
  by_cases hq : q ≤ 2
  · exact ⟨j, q, r, L, v, hq, hr, hv, hI, by omega, by omega, ⟨0, rfl⟩⟩
  · rcases Rnd_exists q r L v (by omega) hr with ⟨q', r', L', v', hR⟩
    have hq' : q' < q := by cases hR <;> omega
    rcases Rnd_valid q r L v q' r' L' v' hR hv hr with ⟨hv', hr'⟩
    have hl' : okL (P + (j + 2)) l := okL_ge (P + (j + 2)) l (by omega)
    rcases phase Inv Hstep q' (j + 2) P l r' L' v' hl' hr' hv' (Hstep j q r L v q' r' L' v' hR hv
        hI) with
      ⟨j2, q2, r2, L2, v2, h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨j2, q2, r2, L2, v2, h1, h2, h3, h4, by omega, by omega, ?_⟩
    have hstep := Rnd_tape q r L v q' r' L' v' (P + j) l hR hv hl
    rw [show (P + j) + 2 = P + (j + 2) by omega] at hstep
    exact stepStar_trans (ReachesPlus.to_star hstep) h7
termination_by q

theorem pow0 (L : Nat) (h : L = 0) : 2 ^ L = 1 := by subst h; rfl

def Kx (n r L v : Nat) : Prop :=
  Kst n r L ∧ ¬ (r = 2 ∧ v = 2 ^ L - 1 ∧ n = 2 ^ (L + 1) + 2) ∧
  ¬ (n = 6 ∧ r = 1 ∧ L = 0 ∧ v = 0)

def Pre (n r L v : Nat) : Prop := Jst n r ∨ Kx n r L v

def Saf (q r L v : Nat) : Prop :=
  match r with
  | 0 => (L = 0 → 3 ≤ q) ∧ ¬ (q = 2 ∧ v = 2 ^ L - 1) ∧ (q = 0 → v % 2 = 0)
  | 1 => 3 ≤ q ∧ (v = 0 → q ≤ 2 ^ (L + 1) + 2 → q % 2 = 1) ∧ (v = 0 → q ≠ 2 ^ (L + 1) + 4)
  | _ + 2 => (q ≤ 2 * v + 2 → q % 2 = 1) ∧ q ≠ 2 * v + 4

@[simp] theorem Saf0 (q L v : Nat) :
    Saf q 0 L v = ((L = 0 → 3 ≤ q) ∧ ¬ (q = 2 ∧ v = 2 ^ L - 1) ∧ (q = 0 → v % 2 = 0)) := rfl
@[simp] theorem Saf1 (q L v : Nat) :
    Saf q 1 L v = (3 ≤ q ∧ (v = 0 → q ≤ 2 ^ (L + 1) + 2 → q % 2 = 1) ∧ (v = 0 → q ≠ 2 ^ (L + 1) +
        4)) :=
        rfl
@[simp] theorem Saf2 (q L v : Nat) :
    Saf q 2 L v = ((q ≤ 2 * v + 2 → q % 2 = 1) ∧ q ≠ 2 * v + 4) := rfl

def KI (j q r L v : Nat) : Prop :=
  match r with
  | 0 => 2 ^ L ≤ j + q ∧ (2 ^ (L + 1) ≤ j + 2 * v + 2 ∨ 2 ^ (L + 1) + 1 ≤ j + q) ∧
         (q = 0 → v ≠ 0) ∧ (L = 0 → 4 ≤ q)
  | 1 => 2 ^ (L + 2) + 2 ≤ q ∧ (v = 0 → 2 ^ (L + 1) + 5 ≤ q)
  | _ + 2 => 2 ^ (L + 1) + 2 ≤ j + q ∧ 2 * v + 5 ≤ q

@[simp] theorem KI0 (j q L v : Nat) :
    KI j q 0 L v = (2 ^ L ≤ j + q ∧ (2 ^ (L + 1) ≤ j + 2 * v + 2 ∨ 2 ^ (L + 1) + 1 ≤ j + q) ∧
      (q = 0 → v ≠ 0) ∧ (L = 0 → 4 ≤ q)) := rfl
@[simp] theorem KI1 (j q L v : Nat) :
    KI j q 1 L v = (2 ^ (L + 2) + 2 ≤ q ∧ (v = 0 → 2 ^ (L + 1) + 5 ≤ q)) := rfl
@[simp] theorem KI2 (j q L v : Nat) :
    KI j q 2 L v = (2 ^ (L + 1) + 2 ≤ j + q ∧ 2 * v + 5 ≤ q) := rfl

def ZI (C q r L v : Nat) : Prop :=
  1 ≤ C ∧
  match r with
  | 0 => L ≤ C + 1 ∧ q + 2 ^ (L + 2) + C ≤ 2 * v + L + 2 ^ (C + 3) + 1 ∧
         (q = 0 → v = 0 → L ≤ C)
  | 1 => L + 2 ≤ C ∧ q ≤ 2 ^ (L + 2) + 1 ∧ 3 ≤ q
  | _ + 2 => L + 1 ≤ C ∧ q ≤ 2 * v + 2 ^ (L + 1) + 1

@[simp] theorem ZI0 (C q L v : Nat) :
    ZI C q 0 L v = (1 ≤ C ∧ L ≤ C + 1 ∧ q + 2 ^ (L + 2) + C ≤ 2 * v + L + 2 ^ (C + 3) + 1 ∧
      (q = 0 → v = 0 → L ≤ C)) := rfl
@[simp] theorem ZI1 (C q L v : Nat) :
    ZI C q 1 L v = (1 ≤ C ∧ L + 2 ≤ C ∧ q ≤ 2 ^ (L + 2) + 1 ∧ 3 ≤ q) := rfl
@[simp] theorem ZI2 (C q L v : Nat) :
    ZI C q 2 L v = (1 ≤ C ∧ L + 1 ≤ C ∧ q ≤ 2 * v + 2 ^ (L + 1) + 1) := rfl

theorem true_imp {P : Prop} : (True → P) = P := propext ⟨fun h => h trivial, fun h _ => h⟩
theorem true_and_eq {P : Prop} : (True ∧ P) = P := propext ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
theorem one_add_one : 1 + 1 = 2 := rfl

theorem Saf_step (q r L v q' r' L' v' : Nat)
    (h : Rnd q r L v q' r' L' v') (hv : v < 2 ^ L) (hS : Saf q r L v) :
    Saf q' r' L' v' := by
  have hL := pow_pos L
  have h0 := pow0 L
  cases h <;> simp only [Saf0, Saf1, Saf2, pow2_1, true_imp] at * <;> omega

theorem KI_step (j q r L v q' r' L' v' : Nat)
    (h : Rnd q r L v q' r' L' v') (hv : v < 2 ^ L) (hK : KI j q r L v) :
    KI (j + 2) q' r' L' v' := by
  have hL := pow_pos L
  have h0 := pow0 L
  cases h with
  | RO0 =>
    cases L with
    | zero => simp only [KI0, pow2_1, Nat.pow_zero, true_imp] at *; omega
    | succ L0 =>
      have := pow_pos L0
      simp only [KI0, pow2_1] at *
      omega
  | _ => simp only [KI0, KI1, KI2, pow2_1, true_imp] at *; omega

theorem pow_mono (a b : Nat) (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

theorem pow_lin (a : Nat) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => decide
  | succ a ih => rw [pow2_succ]; omega

theorem ZI_step (C q r L v q' r' L' v' : Nat)
    (h : Rnd q r L v q' r' L' v') (hv : v < 2 ^ L) (hZ : ZI C q r L v) :
    ZI C q' r' L' v' := by
  have hL := pow_pos L
  have hlC := pow_lin C
  have h0 := pow0 L
  cases h with
  | RR1z q0 _ _ h1 =>
    simp only [ZI0, pow2_1] at *; omega
  | RR1t q0 _ _ h1 =>
    simp only [ZI2, pow2_1] at *; omega
  | RR2 _ _ _ h1 =>
    simp only [ZI0, ZI1] at *
    have hm := pow_mono (L + 2) C (by omega)
    simp only [pow2_1] at *; omega
  | RO2 q0 _ =>
    simp only [ZI0, ZI2] at *
    have hm := pow_mono (L + 1) C (by omega)
    simp only [pow2_1] at *; omega
  | RO1 q0 _ =>
    simp only [ZI1, ZI2, pow2_1] at *; omega
  | RO0 _ _ =>
    simp only [ZI0] at *
    by_cases hE : L = C + 1
    · subst hE; simp only [pow2_1] at *; omega
    · cases L with
      | zero => simp only [pow2_1, Nat.pow_zero] at *; omega
      | succ L0 => have := pow_pos L0; simp only [pow2_1] at *; omega

def PI (n r L v j q r' L' v' : Nat) : Prop :=
  j % 2 = 0 ∧ Qv j q r' L' v' = Mv n r L v ∧
  (r' = 1 → j = 0) ∧ (r' = 2 → L' = 0 → j ≤ 2) ∧
  Saf q r' L' v' ∧ (Kx n r L v → KI j q r' L' v') ∧
  (Jst n r → ¬ Kst n r L → ZI (cap r L + 1) q r' L' v')

theorem PI_step (n r L v j q r1 L1 v1 q' r' L' v' : Nat)
    (h : Rnd q r1 L1 v1 q' r' L' v') (hv : v1 < 2 ^ L1) (hP : PI n r L v j q r1 L1 v1) :
    PI n r L v (j + 2) q' r' L' v' := by
  rcases hP with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨by omega, ?_, ?_, ?_, Saf_step q r1 L1 v1 q' r' L' v' h hv h5,
    fun hK => KI_step j q r1 L1 v1 q' r' L' v' h hv (h6 hK),
    fun hJ hK => ZI_step (cap r L + 1) q r1 L1 v1 q' r' L' v' h hv (h7 hJ hK)⟩
  · rw [← h2]
    exact (Rnd_sign j q r1 L1 v1 q' r' L' v' h).symm
  · intro hE
    cases h <;> omega
  · intro hE1 hE2
    cases h with
    | RR1t q L1 v1 h1 =>
      subst hE2
      simp at hv
      omega
    | RO1 q L1 =>
      have := h3 rfl
      omega
    | _ => omega

theorem Mv_lt3 (n r L v : Nat) : Mv n r L v < 3 := by
  rcases r with _ | _ | r <;> simp only [Mv] <;> omega

theorem Qv0 (q r L v : Nat) : Qv 0 q r L v = Mv q r L v := by
  unfold Qv
  have := Mv_lt3 q r L v
  omega

theorem Pre_n3 (n r L v : Nat) (h : Pre n r L v) : 3 ≤ n := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · exact h
  · unfold Kst at h
    have := pow_pos (cap r L + 1)
    omega

theorem Saf_start (n r L v : Nat) (hr : r < 3) (hv : v < 2 ^ L) (hP : Pre n r L v) :
    Saf n r L v := by
  have hL := pow_pos L
  have h0 := pow0 L
  rcases hP with ⟨hn, hp⟩ | ⟨hK, hT, h6⟩
  · rcases r with _ | _ | _ | r <;> (try simp only [Nat.zero_add, one_add_one, Saf0, Saf1, Saf2,
    pow2_1] at *) <;> omega
  · unfold Kst at hK
    rcases r with _ | _ | _ | r
    · simp only [Saf0, cap0, pow2_1] at *; omega
    · simp only [Nat.zero_add, Saf1, cap1, pow2_1, true_and_eq] at *
      cases L with
      | zero => simp only [Nat.pow_zero, true_imp, true_and_eq] at *; omega
      | succ L0 => have := pow_pos L0; simp only [pow2_1] at *; omega
    · simp only [Nat.zero_add, one_add_one, Saf2, cap2, pow2_1, true_and_eq] at *; omega
    · omega

theorem KI_start (n r L v : Nat) (hr : r < 3) (hv : v < 2 ^ L) (hK : Kx n r L v) :
    KI 0 n r L v := by
  rcases hK with ⟨hK, hT, h6⟩
  have hL := pow_pos L
  have h0 := pow0 L
  unfold Kst at hK
  rcases r with _ | _ | _ | r
  · simp only [Nat.zero_add, KI0, cap0, pow2_1] at *; omega
  · simp only [Nat.zero_add, KI1, cap1, pow2_1, true_and_eq] at *
    cases L with
    | zero => simp only [Nat.pow_zero, true_imp, true_and_eq] at *; omega
    | succ L0 => have := pow_pos L0; simp only [pow2_1] at *; omega
  · simp only [Nat.zero_add, one_add_one, KI2, cap2, pow2_1, true_and_eq] at *; omega
  · omega

theorem ZI_start (n r L v : Nat) (hr : r < 3) (hv : v < 2 ^ L) (hJ : Jst n r) (hK : ¬ Kst n r L) :
    ZI (cap r L + 1) n r L v := by
  rcases hJ with ⟨hn, hp⟩
  have hL := pow_pos L
  have h0 := pow0 L
  unfold Kst at hK
  rcases r with _ | _ | _ | r <;> (try simp only [Nat.zero_add, one_add_one, ZI0, ZI1, ZI2, cap0,
    cap1, cap2, pow2_1] at *) <;> omega

theorem PI_start (n r L v : Nat) (hr : r < 3) (hv : v < 2 ^ L) (hP : Pre n r L v) :
    PI n r L v 0 n r L v :=
  ⟨rfl, Qv0 n r L v, fun _ => rfl, fun _ _ => by omega,
   Saf_start n r L v hr hv hP,
   fun hK => KI_start n r L v hr hv hK,
   fun hJ hK => ZI_start n r L v hr hv hJ hK⟩

def Post (n r L v n' r' L' v' : Nat) : Prop :=
  r' < 3 ∧ v' < 2 ^ L' ∧
  (Jst n r → Jst (n' + 1) r') ∧
  (Kx n r L v → Kst n' r' L') ∧
  (Jst n r → ¬ Kst n r L → Kst (n' + 1) r' L' ∨ cap r' L' ≤ cap r L + 1) ∧
  (Mv n' r' L' v' + Mv n r L v) % 3 = 0 ∧
  (r' = 1 → L' = 0 → v' = 0 → n' = 4 ∨ 8 ≤ n')

def U (N : Nat) : Prop :=
  ∀ P l n r L v, okL P l → r < 3 → v < 2 ^ L → Pre n r L v →
  (∀ n' r' L' v', Post n r L v n' r' L' v' → safe (RT l (P + n') (zone r' L' v')) (N - 1)) →
  safe (RT (lev P l) n (zone r L v)) N

theorem lowones (L : Nat) : ∀ v, v < 2 ^ L → v ≠ 2 ^ L - 1 →
    ∃ k L' o, L = k + (L' + 1) ∧ v = 2 ^ k - 1 + 2 ^ (k + 1) * o ∧ o < 2 ^ L' := by
  induction L with
  | zero =>
    intro v hv hne
    simp at hv hne
    omega
  | succ L ih =>
    intro v hv hne
    rw [pow2_succ] at hv hne
    rcases Nat.even_or_odd' v with ⟨o, rfl | rfl⟩
    · exact ⟨0, L, o, by omega, by omega, by omega⟩
    · rcases ih o (by omega) (by omega) with ⟨k, L', o', rfl, rfl, ho'⟩
      refine ⟨k + 1, L', o', by omega, ?_, ho'⟩
      have := pow_pos k
      have : 2 ^ (k + 1) = 2 * 2 ^ k := pow2_succ k
      have : 2 ^ (k + 1 + 1) * o' = 4 * (2 ^ k * o') := by rw [pow2_succ, pow2_succ]; ring
      have : 2 ^ (k + 1) * o' = 2 * (2 ^ k * o') := by rw [pow2_succ]; ring
      omega

theorem bite_shape (j qb rb Lb vb : Nat)
    (hq : qb ≤ 2) (hr : rb < 3) (hv : vb < 2 ^ Lb) (hS : Saf qb rb Lb vb)
    (hj : 2 ≤ j) (h1 : rb = 1 → j = 0) :
    (∃ e r' L' v', EB qb rb Lb vb e r' L' v') ∨
    (qb = 2 ∧ rb = 0 ∧ ∃ k L' o, Lb = k + (L' + 1) ∧ vb = 2 ^ k - 1 + 2 ^ (k + 1) * o ∧ o < 2 ^ L')
        := by
  rcases rb with _ | _ | _ | rb
  · simp only [Saf0] at hS
    rcases hS with ⟨hS1, hS2, hS3⟩
    rcases qb with _ | _ | _ | qb
    · cases Lb with
      | zero => omega
      | succ Lb =>
        left
        by_cases hne : vb = 0
        · subst hne; exact ⟨_, _, _, _, EB.EB0c Lb⟩
        · rcases lowbit vb hne with ⟨b, o, rfl⟩
          cases b with
          | zero => have := hS3 rfl; omega
          | succ b =>
            rcases lowbit_lt (b + 1) o (Lb + 1) hv with ⟨hb, ho⟩
            rw [show Lb + 1 = (b + 1) + (Lb - b - 1 + 1) by omega]
            exact ⟨_, _, _, _, EB.EB0 b (Lb - b - 1) o⟩
    · cases Lb with
      | zero => omega
      | succ Lb =>
        left
        rcases Nat.even_or_odd' vb with ⟨w, rfl | rfl⟩
        · exact ⟨_, _, _, _, EB.EB1z0 Lb w⟩
        · exact ⟨_, _, _, _, EB.EB1z1 Lb w⟩
    · right
      exact ⟨rfl, rfl, lowones Lb vb hv (fun hE => hS2 ⟨rfl, hE⟩)⟩
    · omega
  · omega
  · simp only [Nat.zero_add, one_add_one, Saf2] at hS
    have hqb : qb = 1 := by omega
    subst hqb
    exact Or.inl ⟨_, _, _, _, EB.EB1t Lb vb⟩
  · omega

theorem EB_valid (q r L v e r' L' v' : Nat)
    (h : EB q r L v e r' L' v') (hv : v < 2 ^ L) :
    r' < 3 ∧ v' < 2 ^ L' := by
  cases h with
  | EB1z0 L v =>
    rw [pow2_succ] at hv
    exact ⟨by omega, by omega⟩
  | EB1z1 L v =>
    rw [pow2_succ] at hv
    exact ⟨by omega, by omega⟩
  | EB1o L v =>
    exact ⟨by omega, hv⟩
  | EB1t L v =>
    exact ⟨by omega, hv⟩
  | EB0 b L o =>
    refine ⟨by omega, ?_⟩
    have hb := pow_pos b
    have h1 : 2 ^ (b + 1) * (2 * o + 1) = 2 * (2 ^ b + 2 ^ (b + 1) * o) := by
      rw [pow2_succ]; ring
    have h2 : 2 ^ (b + 1 + (L + 1)) = 2 * 2 ^ (b + (L + 1)) := by
      rw [Nat.succ_add, pow2_succ]
    rw [h1, h2] at hv
    omega
  | EB0c L =>
    have := pow_pos L
    rw [pow2_succ]
    exact ⟨by omega, by omega⟩
  | EB0c3 =>
    exact ⟨by omega, by decide⟩

theorem EB_lev (q r L v e r' L' v' P : Nat) (l : zB)
    (hP : 1 ≤ P) (h : EB q r L v e r' L' v') :
    (RT (lev P l) q (zone r L v)) [target_tm]⊢⁺ (RT l (P + e) (zone r' L' v')) := by
  cases P with
  | zero => omega
  | succ p => exact EB_tape q r L v e r' L' v' p l h

theorem Kst_mono (n n' r L : Nat) (h : Kst n r L) (hle : n ≤ n') : Kst n' r L := by
  unfold Kst at *
  omega

theorem ending (n r L v j qb rb Lb vb e r' L' v' : Nat)
    (h : EB qb rb Lb vb e r' L' v') (hP : PI n r L v j qb rb Lb vb)
    (hj : 2 ≤ j) (hvb : vb < 2 ^ Lb) :
    Post n r L v (j + e) r' L' v' := by
  rcases hP with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  rcases EB_valid qb rb Lb vb e r' L' v' h hvb with ⟨hr', hv'⟩
  have hS := EB_sign qb rb Lb vb e r' L' v' j h
  rw [h2] at hS
  refine ⟨hr', hv', ?_, ?_, ?_, hS, ?_⟩
  · intro _
    unfold Jst
    cases h <;> omega
  · intro hK
    have hKI := h6 hK
    unfold Kst
    cases h with
    | EB1z0 =>
      have := pow_pos L'
      simp only [KI0, cap2, pow2_1] at *
      omega
    | EB1z1 =>
      have := pow_pos L'
      simp only [KI0, cap0, pow2_1] at *
      omega
    | EB1o =>
      have := pow_pos L
      simp only [KI1, cap0, pow2_1, true_imp] at *
      omega
    | EB1t =>
      have := pow_pos L
      simp only [KI2, cap1, pow2_1, true_imp] at *
      omega
    | EB0 b L0 o =>
      simp only [KI0, cap0, true_imp] at *
      rw [show b + (L0 + 1) + 1 = b + 1 + (L0 + 1) by omega]
      omega
    | EB0c L0 =>
      simp only [KI0, cap0, true_imp] at *
      omega
    | EB0c3 =>
      simp only [KI0, cap0, true_imp] at *
      omega
  · intro hJ hK
    have hZ := h7 hJ hK
    right
    cases h <;> simp only [ZI0, ZI1, ZI2, cap0, cap1, cap2, true_imp] at * <;> omega
  · intro hE1 hE2 hE3
    cases h with
    | EB1t _ _ =>
      subst hE2 hE3
      have := h4 rfl rfl
      omega
    | _ => omega

theorem ending_B2 (n r L v j L' o : Nat)
    (hP : PI n r L v j 2 0 (0 + (L' + 1)) (2 ^ 0 - 1 + 2 ^ 1 * o))
    (hj : 2 ≤ j) (ho : o < 2 ^ L') :
    Post n r L v (j + 4) 0 L' o := by
  rcases hP with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  simp only [Nat.zero_add, Nat.pow_zero, Nat.pow_one] at *
  refine ⟨by omega, ho, fun _ => by unfold Jst; omega, ?_, ?_, ?_, fun hE => by omega⟩
  · intro hK
    have hKI := h6 hK
    unfold Kst
    have := pow_pos L'
    simp only [KI0, cap0, pow2_1] at *
    omega
  · intro hJ hK
    have hZ := h7 hJ hK
    right
    simp only [ZI0, cap0] at *
    omega
  · rw [← h2]
    unfold Qv
    have := pow_pos L'
    simp only [Mv0, pow2_1] at *
    omega

def Budget (n r L C : Nat) : Prop := Kst n r L ∨ cap r L ≤ C

def SR (j a b : Nat) : Prop :=
  (j % 2 = 0 → b = a) ∧ (j % 2 = 1 → (a + b + 2) % 3 = 0)

theorem JK (n r L v : Nat) (hJ : Jst n r) (hK : Kst n r L) : Kx n r L v := by
  rcases hJ with ⟨hn, hp⟩
  refine ⟨hK, ?_, ?_⟩
  · rintro ⟨rfl, _, rfl⟩
    have := hp (by omega)
    rw [pow2_succ] at this
    omega
  · rintro ⟨rfl, rfl, _⟩
    have := hp (by omega)
    omega

theorem Budget_step (n r L v C n' r' L' v' : Nat)
    (hJ : Jst n r) (hB : Budget n r L C) (hP : Post n r L v n' r' L' v') :
    Budget (n' + 1) r' L' (C + 1) := by
  rcases hP with ⟨_, _, _, hU2, hU3, _⟩
  by_cases hK : 2 ^ (cap r L + 1) + 2 ≤ n
  · left
    exact Kst_mono n' (n' + 1) r' L' (hU2 (JK n r L v hJ hK)) (by omega)
  · rcases hB with hB | hB
    · unfold Kst at hB; omega
    · rcases hU3 hJ hK with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)

theorem Mv_shift (a n r L v : Nat) : Mv (a + n) r L v = (Mv n r L v + a) % 3 := by
  rcases r with _ | _ | r <;> simp only [Mv] <;> omega

theorem SR_step (j n r L v n' r' L' v' b : Nat)
    (hb : b < 3) (hP : Post n r L v n' r' L' v') (hSR : SR j (Mv (n' + 1) r' L' v') b) :
    SR (j + 1) (Mv n r L v) b := by
  rcases hP with ⟨_, _, _, _, _, hU4, _⟩
  rcases hSR with ⟨hE, hO⟩
  rw [show n' + 1 = 1 + n' by omega, Mv_shift] at hE hO
  have := Mv_lt3 n r L v
  have := Mv_lt3 n' r' L' v'
  exact ⟨fun hj => by omega, fun hj => by omega⟩

theorem pow2_mod3 (k : Nat) : ∃ x, 2 ^ k = 3 * x + 1 + k % 2 := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rcases ih with ⟨x, hx⟩
    refine ⟨2 * x + k % 2, ?_⟩
    rw [pow2_succ, hx]
    omega

theorem QvN (j k L o : Nat) :
    (k % 2 = 0 →
        Qv j 2 0 (k + 1 + (L + 1)) (2 ^ (k + 1) - 1 + 2 ^ (k + 2) * o) = (Mv 3 0 L o + 1 + 2 * j) %
            3) ∧
    (k % 2 = 1 →
        Qv j 2 0 (k + 1 + (L + 1)) (2 ^ (k + 1) - 1 + 2 ^ (k + 2) * o) =
        (2 * (Mv 3 0 L o + 1) + 2 * j) % 3) := by
  rcases pow2_mod3 k with ⟨x, hx⟩
  have hL := pow_pos L
  unfold Qv
  simp only [Mv0]
  have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow2_succ]
  have h2 : 2 ^ (k + 2) * o = 4 * (2 ^ k * o) := by rw [pow2_succ, pow2_succ]; ring
  have h3 : 2 ^ (k + 1 + (L + 1) + 2) = 16 * (2 ^ k * 2 ^ L) := by
    rw [show k + 1 + (L + 1) + 2 = (k + L) + 4 by omega, pow2_4, Nat.pow_add]
  have h4 : 2 ^ (L + 2) = 4 * 2 ^ L := pow2_2 L
  have h2k : 2 ^ k ≥ 1 := pow_pos k
  have hmul1 : 2 ^ k * o = 3 * (x * o) + o + (k % 2) * o := by
    calc 2 ^ k * o = (3 * x + 1 + k % 2) * o := by rw [hx]
    _ = 3 * (x * o) + o + (k % 2) * o := by ring
  have hmul2 : 2 ^ k * 2 ^ L = 3 * (x * 2 ^ L) + 2 ^ L + (k % 2) * 2 ^ L := by
    calc 2 ^ k * 2 ^ L = (3 * x + 1 + k % 2) * 2 ^ L := by rw [hx]
    _ = 3 * (x * 2 ^ L) + 2 ^ L + (k % 2) * 2 ^ L := by ring
  rw [h1, h2, h3, h4, hmul1, hmul2, hx]
  constructor <;> intro hk <;> rw [hk] <;> simp only [Nat.zero_mul, Nat.one_mul] <;> omega

theorem compose (n r L v j k L' o n1 r1 L1 v1 n3 r3 L3 v3 : Nat)
    (hPI : PI n r L v j 2 0 (k + 1 + (L' + 1)) (2 ^ (k + 1) - 1 + 2 ^ (k + 2) * o))
    (hj : 2 ≤ j) (hJ1 : Jst n1 r1) (hB1 : Budget n1 r1 L1 (L' + k))
    (hSR : SR k (Mv 3 0 L' o) (Mv n1 r1 L1 v1))
    (hP : Post n1 r1 L1 v1 n3 r3 L3 v3) :
    Post n r L v (j + 2 + n3) r3 L3 v3 := by
  have hB3 := Budget_step n1 r1 L1 v1 (L' + k) n3 r3 L3 v3 hJ1 hB1 hP
  rcases hPI with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  rcases hP with ⟨hr3, hv3, hU1, hU2, hU3, hU4, hU5⟩
  rcases hU1 hJ1 with ⟨hn3, hp3⟩
  refine ⟨hr3, hv3, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    refine ⟨by omega, fun hE => ?_⟩
    have := hp3 hE
    omega
  · intro hK
    have hKI := h6 hK
    simp only [KI0] at hKI
    unfold Kst
    rcases hB3 with hB3 | hB3
    · unfold Kst at hB3; omega
    · have hm := pow_mono (cap r3 L3 + 1) (k + 1 + (L' + 1)) (by omega)
      omega
  · intro hJ hK
    have hZ := h7 hJ hK
    simp only [ZI0] at hZ
    rcases hB3 with hB3 | hB3
    · exact Or.inl (Kst_mono (n3 + 1) (j + 2 + n3 + 1) r3 L3 hB3 (by omega))
    · exact Or.inr (by omega)
  · rw [Mv_shift (j + 2) n3]
    rcases hSR with ⟨hE, hO⟩
    rcases QvN j k L' o with ⟨hQE, hQO⟩
    have := Mv_lt3 n3 r3 L3 v3
    have := Mv_lt3 n1 r1 L1 v1
    have := Mv_lt3 3 0 L' o
    rw [← h2]
    by_cases hk : k % 2 = 0
    · rw [hQE hk]; have := hE hk; omega
    · have hk1 : k % 2 = 1 := by omega
      rw [hQO hk1]; have := hO hk1; omega
  · intro hE1 hE2 hE3
    right
    have := hU5 hE1 hE2 hE3
    omega

theorem STK (j B : Nat) (hU : ∀ B', B' ≤ B → U B') (n r L v C : Nat) (X : zB)
    (hJ : Jst n r) (hB : Budget n r L C) (hr : r < 3) (hv : v < 2 ^ L)
    (hk : ∀ n1 r1 L1 v1, Jst n1 r1 → Budget n1 r1 L1 (C + j) → r1 < 3 → v1 < 2 ^ L1 →
       SR j (Mv n r L v) (Mv n1 r1 L1 v1) → safe (RT X n1 (zone r1 L1 v1)) (B - j)) :
    safe (RT ((FR 0)^[j] X) n (zone r L v)) B := by
  induction j generalizing B n r L v C with
  | zero =>
    have h := hk n r L v hJ (by rw [Nat.add_zero]; exact hB) hr hv ⟨fun _ => rfl, fun h => by omega⟩
    rw [Nat.sub_zero] at h
    exact h
  | succ j ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    change safe (RT (lev 1 ((FR 0)^[j] X)) n (zone r L v)) B
    apply hU B (Nat.le_refl B) 1 ((FR 0)^[j] X) n r L v (okL_S 0 _) hr hv (Or.inl hJ)
    intro n' r' L' v' hP
    rw [show 1 + n' = n' + 1 by omega]
    have ⟨hr', hv', hU1, _⟩ := hP
    apply ih (B - 1) (fun B' hB' => hU B' (by omega)) (n' + 1) r' L' v' (C + 1) (hU1 hJ)
      (Budget_step n r L v C n' r' L' v' hJ hB hP) hr' hv'
    intro n1 r1 L1 v1 hJ1 hB1 hr1 hv1 hS1
    rw [show B - 1 - j = B - (j + 1) by omega]
    apply hk n1 r1 L1 v1 hJ1 (by rw [show C + (j + 1) = (C + 1) + j by omega]; exact hB1) hr1 hv1
    exact SR_step j n r L v n' r' L' v' (Mv n1 r1 L1 v1) (Mv_lt3 n1 r1 L1 v1) hP hS1

theorem U_all (N : Nat) : U N := by
  refine nat_strong_ind (fun N ih => ?_) N
  intro P l n r L v hl hr hv hpre hk
  have hn := Pre_n3 n r L v hpre
  cases N with
  | zero =>
    rcases Rnd_exists n r L v hn hr with ⟨q', r', L', v', hR⟩
    exact safe_prog0 _ _ (Rnd_tape n r L v q' r' L' v' P l hR hv hl)
  | succ N' =>
    rcases phase (PI n r L v) (PI_step n r L v) n 0 P l r L v
      (by rw [Nat.add_zero]; exact hl) hr hv (PI_start n r L v hr hv hpre) with
      ⟨j, qb, rb, Lb, vb, hqb, hrb, hvb, hI, _, hj_fn, hrun⟩
    have hj := hj_fn hn
    rw [Nat.add_zero] at hrun
    rw [Nat.zero_add] at hj
    apply safe_ev _ _ (N' + 1) hrun
    have hlP : okL (P + j) l := okL_ge (P + j) l (by omega)
    have ⟨_, _, hI3, _, hI5, _⟩ := hI
    rcases bite_shape j qb rb Lb vb hqb hrb hvb hI5 hj hI3 with
      ⟨e, r', L', v', hE⟩ | ⟨rfl, rfl, k, L', o, rfl, rfl, ho⟩
    · apply safe_prog _ _ (N' + 1) (EB_lev qb rb Lb vb e r' L' v' (P + j) l (by omega) hE)
      rw [show P + j + e = P + (j + e) by omega]
      exact hk (j + e) r' L' v' (ending n r L v j qb rb Lb vb e r' L' v' hE hI hj hvb)
    · cases k with
      | zero =>
        have hstep1 := PUSH_lev 0 L' o (P + j) l hlP
        have hstep2 := EB_lev 1 1 L' o 2 0 L' o (P + j + 2) l (by omega) (EB.EB1o L' o)
        apply safe_prog _ _ (N' + 1) (stepPlus_trans hstep1 hstep2)
        rw [show P + j + 2 + 2 = P + (j + 4) by omega]
        exact hk (j + 4) 0 L' o (ending_B2 n r L v j L' o hI hj ho)
      | succ k =>
        have hpush :=
            stepPlus_trans (PUSH_lev (k + 1) L' o (P + j) l hlP) (inner1 k L' o (lev (P + j + 2) l))
        apply safe_prog _ _ (N' + 1) hpush
        rw [show N' + 1 - 1 = N' by omega]
        apply STK k N' (fun B hB => ih B (by omega)) 3 0 L' o L' (lev (P + j + 2) l)
          ⟨by omega, fun hE => by omega⟩ (Or.inr (by rw [cap0])) (by omega) ho
        intro n1 r1 L1 v1 hJ1 hB1 hr1 hv1 hS1
        apply ih (N' - k) (by omega) (P + j + 2) l n1 r1 L1 v1
          (okL_ge (P + j + 2) l (by omega)) hr1 hv1 (Or.inl hJ1)
        intro n3 r3 L3 v3 hP3
        rw [show P + j + 2 + n3 = P + (j + 2 + n3) by omega]
        apply safe_mono _ (N' + 1 - 1) (N' - k - 1)
          (hk (j + 2 + n3) r3 L3 v3 (compose n r L v j k L' o n1 r1 L1 v1 n3 r3 L3 v3 hI hj hJ1 hB1
              hS1 hP3))
          (by omega)

theorem Ist_Kx (n r L v : Nat) (h : Ist n r L v) : Kx n r L v := by
  rcases h with ⟨hr, hv, hK, hM, h6⟩
  refine ⟨hK, ?_, h6⟩
  rintro ⟨rfl, rfl, rfl⟩
  apply hM
  have := pow_pos L
  simp only [Mv2, pow2_1] at *
  omega

theorem cycles (N : Nat) : ∀ n r L v, Ist n r L v → safe (RT default n (zone r L v)) N := by
  refine @nat_strong_ind (fun N =>
      ∀ n r L v, Ist n r L v → safe (RT default n (zone r L v)) N) (fun N ih n r L v hI => ?_) N
  have hK := Ist_Kx n r L v hI
  rcases hI with ⟨hr, hv, hKs, hM, h6⟩
  apply U_all N 0 default n r L v (fun _ => rfl) hr hv (Or.inr hK)
  intro n' r' L' v' ⟨hr', hv', _, hU2, _, hU4, hU5⟩
  cases N with
  | zero => exact safe_RT0 default (0 + n') (zone r' L' v')
  | succ N' =>
    rw [show N' + 1 - 1 = N' by omega, Nat.zero_add]
    apply ih N' (by omega) n' r' L' v'
    have := Mv_lt3 n r L v
    have := Mv_lt3 n' r' L' v'
    refine ⟨hr', hv', hU2 hK, by omega, ?_⟩
    rintro ⟨rfl, rfl, rfl, rfl⟩
    have := hU5 rfl rfl rfl
    omega



public section

theorem is_not_halt : IsNotHalt target := by
  intro cfg ⟨N, hrun⟩
  have hsafe := safe_ev (init []) (RT default 6 (zone 2 0 0)) N init_step (cycles N 6 2 0 0 init_I)
  exact hsafe N (Nat.le_refl N) cfg hrun

end

end BusyBeaver.M_1RB0RC_1LC1RB_0RE1LD_0LC1LA_1RF1RA_HHH0RB
