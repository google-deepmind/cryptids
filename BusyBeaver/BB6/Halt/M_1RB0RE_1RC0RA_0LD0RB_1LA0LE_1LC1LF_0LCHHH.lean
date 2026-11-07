/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Longitudinal

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RE_1RC0RA_0LD0RB_1LA0LE_1LC1LF_0LCHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1RC0RA_0LD0RB_1LA0LE_1LC1LF_0LCHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

namespace Solution

open BusyBeaver.Longitudinal
open BusyBeaver.Longitudinal.BoundedConfig (all0_spec segRLs_c_spec)

abbrev tm : Machine (Fin 2) (Fin 6) := flipTM target_tm

abbrev U : List (Fin 2) := [1, 0, 0]
abbrev Z : List (Fin 2) := [0, 0, 0]
abbrev O : List (Fin 2) := [1, 0, 1]
abbrev P : List (Fin 2) := [0, 0, 1]

abbrev h : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [((C, [0]), (C, [1]))]
abbrev g : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [((E, [0, 0]), (C, [1]))]
abbrev j : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [((D, [0, 0]), (C, [1]))]
abbrev e : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [((E, [0, 0, 0]), (C, [1]))]
abbrev q : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [((D, [0]), (C, [1]))]
abbrev qb : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) := [((D, [0]), (B, [1]))]

theorem H0 : SegRLs tm h j [0] [] := segRLs_c_spec tm (T := 100) (by decide)
theorem H1 : SegRLs tm h [] [1] [0] := segRLs_c_spec tm (T := 100) (by decide)
theorem J1 : SegRLs tm j e [1] [] := segRLs_c_spec tm (T := 100) (by decide)
theorem QB00 : SegRLs tm qb [] [0, 0] [0, 1] := segRLs_c_spec tm (T := 100) (by decide)
theorem Q01 : SegRLs tm q h [0, 1] [0, 1] := segRLs_c_spec tm (T := 100) (by decide)
theorem QU : SegRLs tm q q U U := segRLs_c_spec tm (T := 100) (by decide)
theorem QUB : SegRLs tm q qb U O := segRLs_c_spec tm (T := 100) (by decide)
theorem QO : SegRLs tm q [] O U := segRLs_c_spec tm (T := 100) (by decide)
theorem Q110 : SegRLs tm q h [1, 1, 0] U := segRLs_c_spec tm (T := 100) (by decide)
theorem GU : SegRLs tm g j U U := segRLs_c_spec tm (T := 100) (by decide)
theorem JU : SegRLs tm j (q ++ j) U U := segRLs_c_spec tm (T := 100) (by decide)
theorem JO : SegRLs tm j j O U := segRLs_c_spec tm (T := 100) (by decide)
theorem J110 : SegRLs tm j (h ++ j) [1, 1, 0] U := segRLs_c_spec tm (T := 100) (by decide)

macro "tm_step" : tactic =>
  `(tactic| (
    first
    | refine ReachesPlus.head (by
        try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
          List.cons_append, List.nil_append, List.append_nil,
          ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons,
          ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
          ListBlank.cons_default_default, ListBlank.cons_zero_default, flipStmt, flipDir]
        rfl) ?_
    | refine ReachesStar.head (by
        try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
          List.cons_append, List.nil_append, List.append_nil,
          ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons,
          ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
          ListBlank.cons_default_default, ListBlank.cons_zero_default, flipStmt, flipDir]
        rfl) ?_
    try simp only [Tape.write, Tape.move, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
      ListBlank.cons_default_default, ListBlank.cons_zero_default, flipStmt, flipDir]))

macro "tm_steps" : tactic =>
  `(tactic| repeat (first | bb_refl | tm_step))

theorem G11 (l r : ListBlank (Fin 2)) :
    HaltsFrom tm (toDHCfg ((E, [0, 0]), .right) l ([1, 1] +> r)) := by
  refine ⟨([1, 0, 0] +> l) {{F}}> ([1] +> r), ?_, ?_⟩
  · dsimp [toDHCfg]; tm_steps
  · bb_halt

theorem L11 (l r : ListBlank (Fin 2)) :
    HaltsFrom tm (toDHCfg ((E, [0, 0, 0]), .right) l ([1, 1] +> r)) := by
  refine ⟨([1, 0, 0, 0] +> l) {{F}}> ([1] +> r), ?_, ?_⟩
  · dsimp [toDHCfg]; tm_steps
  · bb_halt

theorem Q111 (l r : ListBlank (Fin 2)) :
    HaltsFrom tm (toDHCfg ((D, [0]), .right) l ([1, 1, 1] +> r)) := by
  refine ⟨([1, 0, 0] +> l) {{F}}> ([1] +> r), ?_, ?_⟩
  · dsimp [toDHCfg]; tm_steps
  · bb_halt

theorem Qrun (a : ℕ) : SegRLs tm q q (U ^ a) (U ^ a) := by
  induction a with
  | zero => exact SegRLs.empty tm q
  | succ a ih => exact QU.concat ih

theorem Qrun01 (a : ℕ) : SegRLs tm q h (U ^ a ++ [0, 1]) (U ^ a ++ [0, 1]) :=
  (Qrun a).concat Q01

theorem T01 (a : ℕ) : SegRLs tm j (h ^ (1 + a)) (U ^ a ++ [0, 1]) (U ^ (1 + a)) := by
  induction a with
  | zero => exact segRLs_c_spec tm (T := 100) (by decide)
  | succ a ih =>
    have h_pow : h ^ (1 + (a + 1)) = h ++ h ^ (1 + a) := by
      have hk : 1 + (a + 1) = (1 + a) + 1 := by omega
      rw [hk, pow_succ_list]
    have h_u1 : U ^ (a + 1) ++ [0, 1] = U ++ (U ^ a ++ [0, 1]) := by
      rw [pow_succ_list, List.append_assoc]
    have h_u2 : U ^ (1 + (a + 1)) = U ++ U ^ (1 + a) := by
      have hk : 1 + (a + 1) = (1 + a) + 1 := by omega
      rw [hk, pow_succ_list]
    rw [h_pow, h_u1, h_u2]
    exact JU.concat ((Qrun01 a).trans ih)

theorem QrunO (a : ℕ) : SegRLs tm q [] (U ^ a ++ O) (U ^ (1 + a)) := by
  have hk : 1 + a = a + 1 := by omega
  rw [hk, pow_succ_list']
  exact (Qrun a).concat QO

theorem Qrun00 (a : ℕ) : SegRLs tm q [] (U ^ (1 + a) ++ [0, 0]) (U ^ a ++ O ++ [0, 1]) := by
  have hk : 1 + a = a + 1 := by omega
  rw [hk, pow_succ_list', List.append_assoc, List.append_assoc]
  exact (Qrun a).concat (QUB.concat QB00)

inductive Result (X : Type) where
  | failed
  | stopped
  | returned (x : X)
deriving DecidableEq

def map_result {X Y : Type} (f : X → Y) : Result X → Result Y
  | .failed => .failed
  | .stopped => .stopped
  | .returned x => .returned (f x)

def then_result {X Y : Type} (o : Result X) (f : X → Result Y) : Result Y :=
  match o with
  | .failed => .failed
  | .stopped => .stopped
  | .returned x => f x

def Spec {X : Type} (den : X → ListBlank (Fin 2))
    (hs : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)))
    (r : ListBlank (Fin 2)) (o : Result X) : Prop :=
  match o with
  | .failed => True
  | .stopped => SideRLsHalt tm hs r
  | .returned x => SideRLs tm hs r (den x)

theorem rule_spec {X : Type} (den : X → ListBlank (Fin 2))
    {hs hs' : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {w v : List (Fin 2)} {r : ListBlank (Fin 2)} {o : Result X}
    (hR : SegRLs tm hs hs' w v) (hS : Spec den hs' r o) :
    Spec (fun x => v +> den x) hs (w +> r) o := by
  cases o with
  | failed => trivial
  | stopped => exact hR.sideRLsHalt_concat hS
  | returned x => exact hR.sideRLs_concat hS

theorem lift_rule {X Y : Type} (dx : X → ListBlank (Fin 2)) (dy : Y → ListBlank (Fin 2))
    {hs hs' : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {w v : List (Fin 2)} {r : ListBlank (Fin 2)} {o : Result X} {f : X → Y}
    (hR : SegRLs tm hs hs' w v) (hF : ∀ x, dy (f x) = v +> dx x)
    (hS : Spec dx hs' r o) :
    Spec dy hs (w +> r) (map_result f o) := by
  cases o with
  | failed => trivial
  | stopped => exact hR.sideRLsHalt_concat hS
  | returned x =>
    dsimp [Spec, map_result]
    rw [hF x]
    exact hR.sideRLs_concat hS

theorem bind_spec {X Y : Type} (dx : X → ListBlank (Fin 2)) (dy : Y → ListBlank (Fin 2))
    {hs hs' : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {r : ListBlank (Fin 2)} {o : Result X} {f : X → Result Y}
    (hS : Spec dx hs r o) (hF : ∀ x, Spec dy hs' (dx x) (f x)) :
    Spec dy (hs ++ hs') r (then_result o f) := by
  cases o with
  | failed => trivial
  | stopped => exact SideRLsHalt.app_left hS
  | returned x =>
    have hfx := hF x
    dsimp [then_result]
    cases hfx_eq : f x with
    | failed => trivial
    | stopped =>
      rw [hfx_eq] at hfx
      exact SideRLsHalt.app_right hS hfx
    | returned y =>
      rw [hfx_eq] at hfx
      exact hS.trans hfx

theorem after_spec {X : Type} (den : X → ListBlank (Fin 2))
    {hs hs' : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {r s : ListBlank (Fin 2)} {o : Result X}
    (hSide : SideRLs tm hs r s) (hS : Spec den hs' s o) :
    Spec den (hs ++ hs') r o := by
  cases o with
  | failed => trivial
  | stopped => exact SideRLsHalt.app_right hSide hS
  | returned x => exact hSide.trans hS

theorem TO {X : Type} (den : X → ListBlank (Fin 2)) (a : ℕ) (r : ListBlank (Fin 2)) (o : Result X)
    (hS : Spec den j (U ^ a +> r) o) :
    Spec (fun x => U +> den x) j (U ^ a +> (O +> r)) o := by
  rcases a with _ | a
  · dsimp only [pow_zero_list, append_nil] at hS ⊢
    exact rule_spec den JO hS
  · rw [pow_succ_list U a, append_assoc, ← append_assoc (U ^ a) O r]
    have hQ : SideRLs tm q ((U ^ a ++ O) +> r) (U ^ (1 + a) +> r) :=
      (QrunO a).sideRLs_concat (.nil r)
    have ha : 1 + a = a + 1 := by omega
    rw [ha] at hQ
    exact rule_spec den JU (after_spec den hQ hS)

theorem T00 {X : Type} (den : X → ListBlank (Fin 2)) (a : ℕ) (r : ListBlank (Fin 2)) (o : Result X)
    (hS : Spec den (h ^ (1 + a)) r o) :
    Spec (fun x => U ^ (3 + a) +> den x) j (U ^ (2 + a) +> ([0, 0] +> r)) o := by
  have hT := rule_spec den (T01 a) hS
  rw [append_assoc] at hT
  have hT' := TO (fun x => U ^ (1 + a) +> den x) a ([0, 1] +> r) o hT
  have hQ : SideRLs tm q ((U ^ (1 + a) ++ [0, 0]) +> r) ((U ^ a ++ O ++ [0, 1]) +> r) :=
    (Qrun00 a).sideRLs_concat (.nil r)
  have h_in : U ^ (2 + a) +> ([0, 0] +> r) = U +> ((U ^ (1 + a) ++ [0, 0]) +> r) := by
    have h2 : 2 + a = (1 + a) + 1 := by omega
    rw [h2, pow_succ_list, append_assoc, append_assoc]
  rw [h_in]
  have h_mid : (U ^ a ++ O ++ [0, 1]) +> r = U ^ a +> (O +> ([0, 1] +> r)) := by
    rw [List.append_assoc, append_assoc, append_assoc]
  rw [h_mid] at hQ
  have h_res := rule_spec (fun x => U +> (U ^ (1 + a) +> den x)) JU (after_spec _ hQ hT')
  have h_fn : (fun x => U +> (U +> (U ^ (1 + a) +> den x))) = (fun x => U ^ (3 + a) +> den x) := by
    funext x
    have h3 : 3 + a = ((1 + a) + 1) + 1 := by omega
    rw [h3, pow_succ_list, pow_succ_list, append_assoc, append_assoc]
  rwa [h_fn] at h_res

theorem T00zero : SegRLs tm j [] [0, 0] O := segRLs_c_spec tm (T := 100) (by decide)
theorem T00one : SegRLs tm j [] (U ++ [0, 0]) (U ++ P) := segRLs_c_spec tm (T := 100) (by decide)

theorem Qrun110 (a : ℕ) : SegRLs tm q h (U ^ a ++ [1, 1, 0]) (U ^ (1 + a)) := by
  have hk : 1 + a = a + 1 := by omega
  rw [hk, pow_succ_list']
  exact (Qrun a).concat Q110

theorem T110_return {X : Type} (den : X → ListBlank (Fin 2)) (a : ℕ)
    (r s : ListBlank (Fin 2)) (o : Result X)
    (hH : SideRLs tm h r s) (hT : Spec den j (U ^ a +> s) o) :
    Spec (fun x => U +> den x) j (U ^ a +> ([1, 1, 0] +> r)) o := by
  rcases a with _ | a
  · dsimp only [pow_zero_list, append_nil] at hT ⊢
    exact rule_spec den J110 (after_spec den hH hT)
  · rw [pow_succ_list U a, append_assoc, ← append_assoc (U ^ a) [1, 1, 0] r]
    have hQ : SideRLs tm q ((U ^ a ++ [1, 1, 0]) +> r) (U ^ (1 + a) +> s) :=
      (Qrun110 a).sideRLs_concat hH
    have ha : 1 + a = a + 1 := by omega
    rw [ha] at hQ
    exact rule_spec den JU (after_spec den hQ hT)

theorem T110_halt (a : ℕ) (r : ListBlank (Fin 2)) (hH : SideRLsHalt tm h r) :
    SideRLsHalt tm j (U ^ a +> ([1, 1, 0] +> r)) := by
  rcases a with _ | a
  · dsimp only [pow_zero_list, append_nil]
    exact J110.sideRLsHalt_concat (SideRLsHalt.app_left hH)
  · rw [pow_succ_list U a, append_assoc, ← append_assoc (U ^ a) [1, 1, 0] r]
    exact JU.sideRLsHalt_concat (SideRLsHalt.app_left ((Qrun110 a).sideRLsHalt_concat hH))

theorem T111 (a : ℕ) (r : ListBlank (Fin 2)) :
    SideRLsHalt tm j (U ^ a +> ([1, 1, 1] +> r)) := by
  rcases a with _ | a
  · change SideRLsHalt tm j ([1] +> ([1, 1] +> r))
    exact J1.sideRLsHalt_concat (.here (E, [0, 0, 0]) (C, [1]) [] ([1, 1] +> r) (fun l => L11 l r))
  · rw [pow_succ_list U a, append_assoc]
    refine JU.sideRLsHalt_concat (SideRLsHalt.app_left ?_)
    exact (Qrun a).sideRLsHalt_concat (.here (D, [0]) (C, [1]) [] ([1, 1, 1] +> r) (fun l =>
        Q111 l r))

def digit (p : ℕ) : List (Fin 2) :=
  match p with
  | 0 => U
  | 1 => Z
  | 2 => O
  | _ => P

theorem digit_cycle (p : ℕ) (hp : p < 4) :
    SegRLs tm (h ^ 4) h (digit p) (digit p) := by
  rcases p with _ | _ | _ | _ | p
  · exact segRLs_c_spec tm (T := 100) (by decide)
  · exact segRLs_c_spec tm (T := 100) (by decide)
  · exact segRLs_c_spec tm (T := 100) (by decide)
  · exact segRLs_c_spec tm (T := 100) (by decide)
  · omega

theorem digit_short (p n : ℕ) (hp : p < 4) (hn : n < 4) :
    SegRLs tm (h ^ n) (h ^ ((p + n) / 4)) (digit p) (digit ((p + n) % 4)) := by
  rcases p with _ | _ | _ | _ | p <;> try omega
  all_goals
    rcases n with _ | _ | _ | _ | n <;> try omega
    all_goals exact segRLs_c_spec tm (T := 100) (by decide)

theorem digit_count (p n : ℕ) (hp : p < 4) :
    SegRLs tm (h ^ n) (h ^ ((p + n) / 4)) (digit p) (digit ((p + n) % 4)) := by
  have hs := digit_short p (n % 4) hp (by omega)
  have hc := digit_cycle ((p + n % 4) % 4) (by omega)
  have h_am := SegRLs.addmul (x := n / 4) hs hc
  have h1 : (n / 4) * 4 + n % 4 = n := by omega
  have h2 : (n / 4) + (p + n % 4) / 4 = (p + n) / 4 := by omega
  have h3 : (p + n % 4) % 4 = (p + n) % 4 := by omega
  rwa [h1, h2, h3] at h_am

def bits (w : List (Fin 2)) : ListBlank (Fin 2) := w +> default

theorem zero_cons_default' : (0 : Fin 2) >> (default : ListBlank (Fin 2)) = default :=
  all0_spec (a := [0]) (by decide)


/-! ## Pure-Kernel Arithmetic Tape Encoding & Fused Multi-Width SWAR Evaluator (v3) -/

private theorem land_pow2_sub1 (m k : Nat) : Nat.land m (2 ^ k - 1) = m % 2 ^ k := by
  change m &&& (2 ^ k - 1) = m % 2 ^ k
  exact Nat.and_two_pow_sub_one_eq_mod m k

private theorem land_1 (m : Nat) : Nat.land m 1 = m % 2 := land_pow2_sub1 m 1
private theorem land_3 (m : Nat) : Nat.land m 3 = m % 4 := land_pow2_sub1 m 2
private theorem land_7 (m : Nat) : Nat.land m 7 = m % 8 := land_pow2_sub1 m 3
private theorem land_15 (m : Nat) : Nat.land m 15 = m % 16 := land_pow2_sub1 m 4
private theorem land_63 (m : Nat) : Nat.land m 63 = m % 64 := land_pow2_sub1 m 6
private theorem land_255 (m : Nat) : Nat.land m 255 = m % 256 := land_pow2_sub1 m 8
private theorem land_4095 (m : Nat) : Nat.land m 4095 = m % 4096 := land_pow2_sub1 m 12
private theorem land_16777215 (m : Nat) : Nat.land m 16777215 = m % 16777216 := land_pow2_sub1 m 24
private theorem land_68719476735 (m : Nat) : Nat.land m 68719476735 = m % 68719476736 :=
    land_pow2_sub1 m 36
private theorem land_281474976710655 (m : Nat) : Nat.land m 281474976710655 = m % 281474976710656 :=
    land_pow2_sub1 m 48

private theorem land_mask_mod (m k mask : Nat) (hm : (2 ^ k - 1) &&& mask = mask) :
    Nat.land m mask = Nat.land (m % 2 ^ k) mask := by
  change m &&& mask = (m % 2 ^ k) &&& mask
  calc m &&& mask
    _ = m &&& ((2 ^ k - 1) &&& mask) := by rw [hm]
    _ = (m &&& (2 ^ k - 1)) &&& mask := (Nat.and_assoc m (2 ^ k - 1) mask).symm
    _ = (m % 2 ^ k) &&& mask := by rw [Nat.and_two_pow_sub_one_eq_mod]

private theorem land_2 (m : Nat) : Nat.land m 2 = Nat.land (m % 4) 2 := land_mask_mod m 2 2 rfl
private theorem land_2_8 (m : Nat) : Nat.land m 2 = Nat.land (m % 8) 2 := land_mask_mod m 3 2 rfl
private theorem land_18 (m : Nat) : Nat.land m 18 = Nat.land (m % 64) 18 := land_mask_mod m 6 18 rfl
private theorem land_1170 (m : Nat) : Nat.land m 1170 = Nat.land (m % 4096) 1170 :=
    land_mask_mod m 12 1170 rfl

private theorem shr_eq (m k : Nat) : Nat.shiftRight m k = m / 2 ^ k := Nat.shiftRight_eq_div_pow m k
private theorem shl_eq (m k : Nat) : Nat.shiftLeft m k = 2 ^ k * m := by
  change m <<< k = 2 ^ k * m
  rw [Nat.shiftLeft_eq, Nat.mul_comm]

private theorem shr_1 (m : Nat) : Nat.shiftRight m 1 = m / 2 := shr_eq m 1
private theorem shr_2 (m : Nat) : Nat.shiftRight m 2 = m / 4 := shr_eq m 2
private theorem shr_3 (m : Nat) : Nat.shiftRight m 3 = m / 8 := shr_eq m 3
private theorem shr_4 (m : Nat) : Nat.shiftRight m 4 = m / 16 := shr_eq m 4
private theorem shr_6 (m : Nat) : Nat.shiftRight m 6 = m / 64 := shr_eq m 6
private theorem shr_8 (m : Nat) : Nat.shiftRight m 8 = m / 256 := shr_eq m 8
private theorem shr_12 (m : Nat) : Nat.shiftRight m 12 = m / 4096 := shr_eq m 12
private theorem shr_16 (m : Nat) : Nat.shiftRight m 16 = m / 65536 := shr_eq m 16
private theorem shr_24 (m : Nat) : Nat.shiftRight m 24 = m / 16777216 := shr_eq m 24
private theorem shr_36 (m : Nat) : Nat.shiftRight m 36 = m / 68719476736 := shr_eq m 36

private theorem shl_2 (m : Nat) : Nat.shiftLeft m 2 = 4 * m := shl_eq m 2
private theorem shl_3 (m : Nat) : Nat.shiftLeft m 3 = 8 * m := shl_eq m 3
private theorem shl_5 (m : Nat) : Nat.shiftLeft m 5 = 32 * m := shl_eq m 5
private theorem shl_6 (m : Nat) : Nat.shiftLeft m 6 = 64 * m := shl_eq m 6
private theorem shl_8 (m : Nat) : Nat.shiftLeft m 8 = 256 * m := shl_eq m 8
private theorem shl_12 (m : Nat) : Nat.shiftLeft m 12 = 4096 * m := shl_eq m 12
private theorem shl_16 (m : Nat) : Nat.shiftLeft m 16 = 65536 * m := shl_eq m 16
private theorem shl_24 (m : Nat) : Nat.shiftLeft m 24 = 16777216 * m := shl_eq m 24
private theorem shl_36 (m : Nat) : Nat.shiftLeft m 36 = 68719476736 * m := shl_eq m 36

def b2f (b : Nat) : Fin 2 := if Nat.beq b 1 then 1 else 0

def toBitsAux : Nat → Nat → List (Fin 2)
  | 0, _ => []
  | k + 1, m => b2f (Nat.mod m 2) :: toBitsAux k (Nat.div m 2)

def bitsM (m : Nat) : ListBlank (Fin 2) := bits (toBitsAux m m)

theorem toBitsAux_zero (k : Nat) : bits (toBitsAux k 0) = default := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (0 : Fin 2) >> bits (toBitsAux k 0) = default
    rw [ih]
    exact zero_cons_default'

theorem bits_toBitsAux_ge (m : Nat) : ∀ k, m ≤ k → bits (toBitsAux k m) = bitsM m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro k hmk
    rcases m with _ | m'
    · rw [toBitsAux_zero k]; exact (toBitsAux_zero 0).symm
    · rcases k with _ | k'
      · omega
      · unfold bitsM
        change b2f ((m' + 1) % 2) >> bits (toBitsAux k' ((m' + 1) / 2)) =
               b2f ((m' + 1) % 2) >> bits (toBitsAux m' ((m' + 1) / 2))
        rw [ih ((m' + 1) / 2) (by omega) k' (by omega),
            ih ((m' + 1) / 2) (by omega) m' (by omega)]

theorem bitsM_zero : bitsM 0 = default := rfl

theorem bitsM_unfold (m : Nat) :
    bitsM m = b2f (m % 2) >> bitsM (m / 2) := by
  rcases m with _ | m'
  · change (default : ListBlank (Fin 2)) = (0 : Fin 2) >> (default : ListBlank (Fin 2))
    exact zero_cons_default'.symm
  · change b2f ((m' + 1) % 2) >> bits (toBitsAux m' ((m' + 1) / 2)) =
           b2f ((m' + 1) % 2) >> bitsM ((m' + 1) / 2)
    rw [bits_toBitsAux_ge ((m' + 1) / 2) m' (by omega)]

theorem bitsM_bit0 (r : Nat) : bitsM (2 * r) = (0 : Fin 2) >> bitsM r := by
  rw [bitsM_unfold (2 * r)]
  have h1 : (2 * r) % 2 = 0 := by omega
  have h2 : (2 * r) / 2 = r := by omega
  rw [h1, h2]; rfl

theorem bitsM_bit1 (r : Nat) : bitsM (1 + 2 * r) = (1 : Fin 2) >> bitsM r := by
  rw [bitsM_unfold (1 + 2 * r)]
  have h1 : (1 + 2 * r) % 2 = 1 := by omega
  have h2 : (1 + 2 * r) / 2 = r := by omega
  rw [h1, h2]; rfl

theorem bitsM_00 (y : Nat) : bitsM (4 * y) = ([0, 0] : List (Fin 2)) +> bitsM y := by
  have h : 4 * y = 2 * (2 * y) := by omega
  rw [h, bitsM_bit0, bitsM_bit0]; rfl

theorem bitsM_10 (y : Nat) : bitsM (1 + 4 * y) = ([1, 0] : List (Fin 2)) +> bitsM y := by
  have h : 1 + 4 * y = 1 + 2 * (2 * y) := by omega
  rw [h, bitsM_bit1, bitsM_bit0]; rfl

theorem bitsM_01 (y : Nat) : bitsM (2 + 4 * y) = ([0, 1] : List (Fin 2)) +> bitsM y := by
  have h : 2 + 4 * y = 2 * (1 + 2 * y) := by omega
  rw [h, bitsM_bit0, bitsM_bit1]; rfl

theorem bitsM_11 (y : Nat) : bitsM (3 + 4 * y) = ([1, 1] : List (Fin 2)) +> bitsM y := by
  have h : 3 + 4 * y = 1 + 2 * (1 + 2 * y) := by omega
  rw [h, bitsM_bit1, bitsM_bit1]; rfl

abbrev W6 : List (Fin 2) := [0, 1, 1]

theorem bitsM_Z (z : Nat) : bitsM (8 * z) = Z +> bitsM z := by
  have h : 8 * z = 2 * (4 * z) := by omega
  rw [h, bitsM_bit0, bitsM_00]; rfl

theorem bitsM_U (z : Nat) : bitsM (1 + 8 * z) = U +> bitsM z := by
  have h : 1 + 8 * z = 1 + 2 * (4 * z) := by omega
  rw [h, bitsM_bit1, bitsM_00]; rfl

theorem bitsM_110 (z : Nat) : bitsM (3 + 8 * z) = ([1, 1, 0] : List (Fin 2)) +> bitsM z := by
  have h : 3 + 8 * z = 3 + 4 * (2 * z) := by omega
  rw [h, bitsM_11, bitsM_bit0]; rfl

theorem bitsM_P (z : Nat) : bitsM (4 + 8 * z) = P +> bitsM z := by
  have h : 4 + 8 * z = 4 * (1 + 2 * z) := by omega
  rw [h, bitsM_00, bitsM_bit1]; rfl

theorem bitsM_O (z : Nat) : bitsM (5 + 8 * z) = O +> bitsM z := by
  have h : 5 + 8 * z = 1 + 4 * (1 + 2 * z) := by omega
  rw [h, bitsM_10, bitsM_bit1]; rfl

theorem bitsM_W6 (z : Nat) : bitsM (6 + 8 * z) = W6 +> bitsM z := by
  have h : 6 + 8 * z = 2 + 4 * (1 + 2 * z) := by omega
  rw [h, bitsM_01, bitsM_bit1]; rfl

theorem bitsM_111 (z : Nat) : bitsM (7 + 8 * z) = ([1, 1, 1] : List (Fin 2)) +> bitsM z := by
  have h : 7 + 8 * z = 3 + 4 * (1 + 2 * z) := by omega
  rw [h, bitsM_11, bitsM_bit1]; rfl

theorem bitsM_0000 (w : Nat) : bitsM (16 * w) = ([0, 0, 0, 0] : List (Fin 2)) +> bitsM w := by
  have h : 16 * w = 4 * (4 * w) := by omega
  rw [h, bitsM_00, bitsM_00]; rfl

theorem bitsM_0100 (w : Nat) : bitsM (2 + 16 * w) = ([0, 1, 0, 0] : List (Fin 2)) +> bitsM w := by
  have h : 2 + 16 * w = 2 + 4 * (4 * w) := by omega
  rw [h, bitsM_01, bitsM_00]; rfl

theorem bitsM_0001 (w : Nat) : bitsM (8 + 16 * w) = ([0, 0, 0, 1] : List (Fin 2)) +> bitsM w := by
  have h : 8 + 16 * w = 4 * (2 + 4 * w) := by omega
  rw [h, bitsM_00, bitsM_01]; rfl

theorem bitsM_0101 (w : Nat) : bitsM (10 + 16 * w) = ([0, 1, 0, 1] : List (Fin 2)) +> bitsM w := by
  have h : 10 + 16 * w = 2 + 4 * (2 + 4 * w) := by omega
  rw [h, bitsM_01, bitsM_01]; rfl

theorem bitsM_17_32 (r : Nat) : bitsM (17 + 32 * r) = ([1, 0, 0, 0, 1] : List (Fin 2)) +> bitsM r :=
    by
  have h : 17 + 32 * r = 1 + 2 * (8 + 16 * r) := by omega
  rw [h, bitsM_bit1, bitsM_0001]; rfl

theorem bitsM_21_32 (r : Nat) : bitsM (21 + 32 * r) = ([1, 0, 1, 0, 1] : List (Fin 2)) +> bitsM r :=
    by
  have h : 21 + 32 * r = 5 + 8 * (2 + 4 * r) := by omega
  rw [h, bitsM_O, bitsM_01]; rfl

theorem bitsM_33_64 (r : Nat) : bitsM (33 + 64 * r) = ([1, 0, 0, 0, 0,
    1] : List (Fin 2)) +> bitsM r := by
  have h : 33 + 64 * r = 1 + 4 * (8 + 16 * r) := by omega
  rw [h, bitsM_10, bitsM_0001]; rfl

theorem bitsM_41_64 (r : Nat) : bitsM (41 + 64 * r) = ([1, 0, 0, 1, 0,
    1] : List (Fin 2)) +> bitsM r := by
  have h : 41 + 64 * r = 1 + 8 * (5 + 8 * r) := by omega
  rw [h, bitsM_U, bitsM_O]; rfl

theorem bitsM_P2 (q : Nat) : bitsM (36 + 64 * q) = P ^ 2 +> bitsM q := by
  have h : 36 + 64 * q = 4 + 8 * (4 + 8 * q) := by omega
  rw [h, bitsM_P, bitsM_P]; rfl

theorem bitsM_P4 (q : Nat) : bitsM (2340 + 4096 * q) = P ^ 4 +> bitsM q := by
  have h : 2340 + 4096 * q = 4 + 8 * (4 + 8 * (4 + 8 * (4 + 8 * q))) := by omega
  rw [h, bitsM_P, bitsM_P, bitsM_P, bitsM_P]; rfl

theorem bitsM_P16 (q : Nat) :
    bitsM (160842843834660 + 281474976710656 * q) = P ^ 16 +> bitsM q := by
  have h : 160842843834660 + 281474976710656 * q =
      2340 + 4096 * (2340 + 4096 * (2340 + 4096 * (2340 + 4096 * q))) := by ring
  rw [h, bitsM_P4, bitsM_P4, bitsM_P4, bitsM_P4]
  simp only [← append_assoc, ← pow_add_list]

theorem bitsM_O4 (q : Nat) : bitsM (2925 + 4096 * q) = O ^ 4 +> bitsM q := by
  have h : 2925 + 4096 * q = 5 + 8 * (5 + 8 * (5 + 8 * (5 + 8 * q))) := by omega
  rw [h, bitsM_O, bitsM_O, bitsM_O, bitsM_O]; rfl

theorem bitsM_W6_2 (q : Nat) : bitsM (54 + 64 * q) = W6 ^ 2 +> bitsM q := by
  have h : 54 + 64 * q = 6 + 8 * (6 + 8 * q) := by omega
  rw [h, bitsM_W6, bitsM_W6]; rfl

theorem bitsM_W6_4 (q : Nat) : bitsM (3510 + 4096 * q) = W6 ^ 4 +> bitsM q := by
  have h : 3510 + 4096 * q = 6 + 8 * (6 + 8 * (6 + 8 * (6 + 8 * q))) := by omega
  rw [h, bitsM_W6, bitsM_W6, bitsM_W6, bitsM_W6]; rfl

theorem bitsM_W6_16 (q : Nat) :
    bitsM (241264265751990 + 281474976710656 * q) = W6 ^ 16 +> bitsM q := by
  have h : 241264265751990 + 281474976710656 * q =
      3510 + 4096 * (3510 + 4096 * (3510 + 4096 * (3510 + 4096 * q))) := by ring
  rw [h, bitsM_W6_4, bitsM_W6_4, bitsM_W6_4, bitsM_W6_4]
  simp only [← append_assoc, ← pow_add_list]

theorem bitsM_U4 (q : Nat) : bitsM (585 + 4096 * q) = U ^ 4 +> bitsM q := by
  have h : 585 + 4096 * q = 1 + 8 * (1 + 8 * (1 + 8 * (1 + 8 * q))) := by omega
  rw [h, bitsM_U, bitsM_U, bitsM_U, bitsM_U]; rfl

theorem bitsM_U16 (q : Nat) :
    bitsM (40210710958665 + 281474976710656 * q) = U ^ 16 +> bitsM q := by
  have h : 40210710958665 + 281474976710656 * q =
      585 + 4096 * (585 + 4096 * (585 + 4096 * (585 + 4096 * q))) := by ring
  rw [h, bitsM_U4, bitsM_U4, bitsM_U4, bitsM_U4]
  simp only [← append_assoc, ← pow_add_list]

private theorem bitsM_eq_of_eq (x : Nat) {y : Nat} {rhs : ListBlank (Fin 2)} (hxy : x =
    y) (hy : bitsM y = rhs) :
    bitsM x = rhs := hxy ▸ hy

/-! ## Evaluator Definitions (Fused `retUH` + Small `Bool.rec` Helpers + SWAR) -/

inductive ResP where
  | failed
  | stopped
  | ret (a m : Nat)

inductive ResL where
  | failed
  | stopped
  | retU (k r : Nat)
  | retUH (k c z : Nat)

inductive ModeM where
  | G
  | L
  | H (n : Nat)

noncomputable def retM (x : Nat) : Result Nat :=
  Nat.rec .failed (fun v _ => .returned v) (Nat.succ x)

noncomputable def retLU (k r : Nat) : ResL :=
  Nat.rec .failed (fun vk _ =>
    Nat.rec .failed (fun vr _ => .retU vk vr) (Nat.succ r)) (Nat.succ k)

noncomputable def retLUH (k c z : Nat) : ResL :=
  Nat.rec .failed (fun vk _ =>
    Nat.rec .failed (fun vc _ =>
      Nat.rec .failed (fun vz _ => .retUH vk vc vz) (Nat.succ z)) (Nat.succ c)) (Nat.succ k)

noncomputable def retP (a m : Nat) : ResP :=
  Nat.rec .failed (fun va _ =>
    Nat.rec .failed (fun vm _ => .ret va vm) (Nat.succ m)) (Nat.succ a)

noncomputable def callM (rec : ModeM → Nat → Result Nat) (md : ModeM) (m : Nat) : Result Nat :=
  Nat.rec .failed (fun vm _ => rec md vm) (Nat.succ m)

noncomputable def callH (rec : ModeM → Nat → Result Nat) (n m : Nat) : Result Nat :=
  Nat.rec .failed (fun vn _ =>
    Nat.rec .failed (fun vm _ => rec (.H vn) vm) (Nat.succ m)) (Nat.succ n)

noncomputable def mapRetM (o : Result Nat) (k : Nat → Result Nat) : Result Nat :=
  Result.rec .failed .stopped k o

noncomputable def mapRetL (o : Result Nat) (k : Nat → ResL) : ResL :=
  Result.rec .failed .stopped k o

noncomputable def prependU_pos (k r : Nat) : Nat :=
  let sh := Nat.mul 3 k
  let p8 := Nat.shiftLeft 1 sh
  Nat.add (Nat.div (Nat.sub p8 1) 7) (Nat.shiftLeft r sh)

noncomputable def prependU (k r : Nat) : Nat :=
  Bool.rec (prependU_pos k r) r (Nat.beq k 0)

def enc1 (rem : Nat) : Nat :=
  Nat.lor (Nat.xor (Nat.land rem 1) 1) (Nat.shiftLeft (Nat.land rem 2) 1)

def dec1 (d3 : Nat) : Nat :=
  Nat.add (Nat.sub 1 (Nat.land d3 1)) (Nat.mul 2 (Nat.shiftRight d3 2))

def dec2 (lo6 : Nat) : Nat :=
  let x := Nat.xor lo6 9
  let y := Nat.lor (Nat.land x 9) (Nat.land (Nat.shiftRight x 1) 18)
  Nat.lor (Nat.land y 3) (Nat.land (Nat.shiftRight y 1) 12)

def enc2 (b4 : Nat) : Nat :=
  let u := Nat.lor (Nat.land b4 3) (Nat.shiftLeft (Nat.land b4 12) 1)
  Nat.lor (Nat.xor (Nat.land u 9) 9) (Nat.shiftLeft (Nat.land u 18) 1)

def dec4 (lo12 : Nat) : Nat :=
  let x := Nat.xor lo12 585
  let y := Nat.lor (Nat.land x 585) (Nat.land (Nat.shiftRight x 1) 1170)
  Nat.lor
    (Nat.lor (Nat.land y 3) (Nat.land (Nat.shiftRight y 1) 12))
    (Nat.lor (Nat.land (Nat.shiftRight y 2) 48) (Nat.land (Nat.shiftRight y 3) 192))

def enc4 (b8 : Nat) : Nat :=
  let u := Nat.lor
    (Nat.lor (Nat.land b8 3) (Nat.shiftLeft (Nat.land b8 12) 1))
    (Nat.lor (Nat.shiftLeft (Nat.land b8 48) 2) (Nat.shiftLeft (Nat.land b8 192) 3))
  Nat.lor (Nat.xor (Nat.land u 585) 585) (Nat.shiftLeft (Nat.land u 1170) 1)

def dec12_3x4 (lo36 : Nat) : Nat :=
  Nat.add (dec4 (Nat.land lo36 4095))
    (Nat.add (Nat.shiftLeft (dec4 (Nat.land (Nat.shiftRight lo36 12) 4095)) 8)
             (Nat.shiftLeft (dec4 (Nat.land (Nat.shiftRight lo36 24) 4095)) 16))

def enc12_3x4 (b24 : Nat) : Nat :=
  Nat.add (enc4 (Nat.land b24 255))
    (Nat.add (Nat.shiftLeft (enc4 (Nat.land (Nat.shiftRight b24 8) 255)) 12)
             (Nat.shiftLeft (enc4 (Nat.land (Nat.shiftRight b24 16) 255)) 24))

noncomputable def prependDigitsK_12 (rec : Nat → Nat → Nat → Nat) (k n r2 : Nat) : Nat :=
  let d12 := enc12_3x4 (Nat.land n 16777215)
  let qn := Nat.shiftRight n 24
  let k2 := Nat.sub k 12
  Bool.rec
    (Nat.add d12 (Nat.shiftLeft (rec k2 qn r2) 36))
    (Nat.add d12 (Nat.shiftLeft (prependU k2 r2) 36))
    (Nat.beq qn 0)

noncomputable def prependDigitsK_4 (rec : Nat → Nat → Nat → Nat) (k n r2 : Nat) : Nat :=
  let d4 := enc4 (Nat.land n 255)
  let qn := Nat.shiftRight n 8
  let k2 := Nat.sub k 4
  Bool.rec
    (Nat.add d4 (Nat.shiftLeft (rec k2 qn r2) 12))
    (Nat.add d4 (Nat.shiftLeft (prependU k2 r2) 12))
    (Nat.beq qn 0)

noncomputable def prependDigitsK_2 (rec : Nat → Nat → Nat → Nat) (k n r2 : Nat) : Nat :=
  let d2 := enc2 (Nat.land n 15)
  let qn := Nat.shiftRight n 4
  let k2 := Nat.sub k 2
  Bool.rec
    (Nat.add d2 (Nat.shiftLeft (rec k2 qn r2) 6))
    (Nat.add d2 (Nat.shiftLeft (prependU k2 r2) 6))
    (Nat.beq qn 0)

noncomputable def prependDigitsK_step (rec : Nat → Nat → Nat → Nat) (k n r2 : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec
        (Bool.rec
          (Bool.rec
            (Nat.add (enc1 (Nat.land n 3)) (Nat.shiftLeft r2 3))
            (prependDigitsK_2 rec k n r2)
            (Nat.ble 2 k))
          (prependDigitsK_4 rec k n r2)
          (Nat.ble 4 k))
        (prependDigitsK_12 rec k n r2)
        (Nat.ble 12 k))
      (prependU k r2)
      (Nat.beq n 0))
    r2
    (Nat.beq k 0)

noncomputable def prependDigitsK_aux (fuel : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun k _ r2 => prependU k r2) (fun _ => prependDigitsK_step) fuel

noncomputable def prependDigitsK (k n r2 : Nat) : Nat :=
  prependDigitsK_aux k k n r2

def carryK (k n : Nat) : Nat :=
  Nat.shiftRight n (Nat.mul 2 k)

noncomputable def ok12_hi (m0 : Nat) : Bool :=
  Bool.rec false
    (Nat.beq (Nat.land (Nat.shiftRight m0 24) 1170) 0)
    (Nat.beq (Nat.land (Nat.shiftRight m0 12) 1170) 0)

noncomputable def sweepP_hit {α : Type} (rec : Nat → Nat → α) (k m : Nat) : α :=
  Bool.rec
    (Bool.rec
      (rec (Nat.add k 1) (Nat.shiftRight m 3))
      (rec (Nat.add k 4) (Nat.shiftRight m 12))
      (Nat.beq (Nat.land m 4095) 2340))
    (rec (Nat.add k 16) (Nat.shiftRight m 48))
    (Nat.beq (Nat.land m 281474976710655) 160842843834660)

noncomputable def sweepP_step {α : Type} (cont : Nat → Nat → α)
    (rec : Nat → Nat → α) (k m : Nat) : α :=
  Bool.rec (cont k m) (sweepP_hit rec k m) (Nat.beq (Nat.land m 7) 4)

noncomputable def sweepP {α : Type} (fuel : Nat) (cont : Nat → Nat → α) : Nat → Nat → α :=
  Nat.rec cont (fun _ => sweepP_step cont) fuel

noncomputable def sweep6_hit {α : Type} (rec : Nat → Nat → α) (k m : Nat) : α :=
  Bool.rec
    (Bool.rec
      (Bool.rec
        (rec (Nat.add k 1) (Nat.shiftRight m 3))
        (rec (Nat.add k 2) (Nat.shiftRight m 6))
        (Nat.beq (Nat.land m 63) 54))
      (rec (Nat.add k 4) (Nat.shiftRight m 12))
      (Nat.beq (Nat.land m 4095) 3510))
    (rec (Nat.add k 16) (Nat.shiftRight m 48))
    (Nat.beq (Nat.land m 281474976710655) 241264265751990)

noncomputable def sweep6_step {α : Type} (cont : Nat → Nat → α)
    (rec : Nat → Nat → α) (k m : Nat) : α :=
  Bool.rec (cont k m) (sweep6_hit rec k m) (Nat.beq (Nat.land m 7) 6)

noncomputable def sweep6 {α : Type} (fuel : Nat) (cont : Nat → Nat → α) : Nat → Nat → α :=
  Nat.rec cont (fun _ => sweep6_step cont) fuel

noncomputable def sweepLP_p {α : Type} (rec : Nat → Nat → Nat → α) (kp ku m : Nat) : α :=
  Bool.rec
    (Bool.rec
      (Bool.rec
        (rec (Nat.add kp 1) ku (Nat.shiftRight m 3))
        (rec (Nat.add kp 2) ku (Nat.shiftRight m 6))
        (Nat.beq (Nat.land m 63) 36))
      (rec (Nat.add kp 4) ku (Nat.shiftRight m 12))
      (Nat.beq (Nat.land m 4095) 2340))
    (rec (Nat.add kp 16) ku (Nat.shiftRight m 48))
    (Nat.beq (Nat.land m 281474976710655) 160842843834660)

noncomputable def sweepLP_w6 {α : Type} (rec : Nat → Nat → Nat → α) (kp ku m : Nat) : α :=
  Bool.rec
    (Bool.rec
      (Bool.rec
        (rec kp (Nat.add ku 1) (Nat.shiftRight m 3))
        (rec kp (Nat.add ku 2) (Nat.shiftRight m 6))
        (Nat.beq (Nat.land m 63) 54))
      (rec kp (Nat.add ku 4) (Nat.shiftRight m 12))
      (Nat.beq (Nat.land m 4095) 3510))
    (rec kp (Nat.add ku 16) (Nat.shiftRight m 48))
    (Nat.beq (Nat.land m 281474976710655) 241264265751990)

noncomputable def sweepLP_step {α : Type} (cont : Nat → Nat → Nat → α)
    (rec : Nat → Nat → Nat → α) (kp ku m : Nat) : α :=
  let d3 := Nat.land m 7
  Bool.rec
    (Bool.rec (cont kp ku m) (sweepLP_w6 rec kp ku m) (Nat.beq d3 6))
    (sweepLP_p rec kp ku m)
    (Nat.beq d3 4)

noncomputable def sweepLP {α : Type} (fuel : Nat) (cont : Nat → Nat → Nat → α) : Nat → Nat → Nat →
    α :=
  Nat.rec cont (fun _ => sweepLP_step cont) fuel

noncomputable def sweepO_hit {α : Type} (rec : Nat → Nat → α) (k m : Nat) : α :=
  Bool.rec
    (rec (Nat.add k 1) (Nat.shiftRight m 3))
    (rec (Nat.add k 4) (Nat.shiftRight m 12))
    (Nat.beq (Nat.land m 4095) 2925)

noncomputable def sweepO_step {α : Type} (cont : Nat → Nat → α)
    (rec : Nat → Nat → α) (k m : Nat) : α :=
  Bool.rec (cont k m) (sweepO_hit rec k m) (Nat.beq (Nat.land m 7) 5)

noncomputable def sweepO {α : Type} (fuel : Nat) (cont : Nat → Nat → α) : Nat → Nat → α :=
  Nat.rec cont (fun _ => sweepO_step cont) fuel

noncomputable def collectM_hit {α : Type} (rec : Nat → Nat → α) (acc m : Nat) : α :=
  Bool.rec
    (Bool.rec
      (rec (Nat.add acc 1) (Nat.shiftRight m 3))
      (rec (Nat.add acc 4) (Nat.shiftRight m 12))
      (Nat.beq (Nat.land m 4095) 585))
    (rec (Nat.add acc 16) (Nat.shiftRight m 48))
    (Nat.beq (Nat.land m 281474976710655) 40210710958665)

noncomputable def collectM_step {α : Type} (cont : Nat → Nat → α)
    (rec : Nat → Nat → α) (acc m : Nat) : α :=
  Bool.rec (cont acc m) (collectM_hit rec acc m) (Nat.beq (Nat.land m 7) 1)

noncomputable def collectM {α : Type} (fuel : Nat) (cont : Nat → Nat → α) : Nat → Nat → α :=
  Nat.rec cont (fun _ => collectM_step cont) fuel

noncomputable def evalG_b00 (rec : ModeM → Nat → Result Nat) (k m : Nat) : Result Nat :=
  let b23 := Nat.land (Nat.shiftRight m 2) 3
  Bool.rec
    (Bool.rec
      (retM (prependU k (Nat.add 21 (Nat.shiftLeft (Nat.shiftRight m 4) 5))))
      (mapRetM (callH rec 1 (Nat.shiftRight m 4))
        (fun r => retM (prependU k (Nat.add 17 (Nat.shiftLeft r 5)))))
      (Nat.beq b23 2))
    (mapRetM (callM rec .G (Nat.shiftRight m 3))
      (fun r => retM (prependU k (Nat.add 1 (Nat.shiftLeft r 3)))))
    (Nat.beq (Nat.land b23 1) 1)

noncomputable def evalG_k (rec : ModeM → Nat → Result Nat) (k m : Nat) : Result Nat :=
  let b01 := Nat.land m 3
  Bool.rec
    (Bool.rec
      (Bool.rec
        (evalG_b00 rec k m)
        (retM (prependU k (Nat.add 1 (Nat.shiftLeft (Nat.shiftRight m 2) 3))))
        (Nat.beq b01 2))
      (mapRetM (callH rec 1 (Nat.shiftRight m 2))
        (fun r => retM (prependU k (Nat.add 1 (Nat.shiftLeft r 3)))))
      (Nat.beq b01 1))
    .stopped
    (Nat.beq b01 3)

noncomputable def evalG (rec : ModeM → Nat → Result Nat) (m0 : Nat) : Result Nat :=
  Bool.rec
    (evalG_k rec 0 m0)
    (sweepP 64 (evalG_k rec) 1 (Nat.shiftRight m0 3))
    (Nat.beq (Nat.land m0 7) 4)

noncomputable def evalJ_k (rec : ModeM → Nat → Result Nat) (k m : Nat) : Result Nat :=
  Bool.rec
    (Bool.rec
      (retM (prependU k (Nat.add 5 (Nat.shiftLeft (Nat.shiftRight m 2) 3))))
      (mapRetM (callH rec 1 (Nat.shiftRight m 2))
        (fun r => retM (prependU k (Nat.add 1 (Nat.shiftLeft r 3)))))
      (Nat.beq (Nat.land m 2) 2))
    (mapRetM (callM rec .L (Nat.shiftRight m 1))
      (fun out0 => retM (prependU k out0)))
    (Nat.beq (Nat.land m 1) 1)

noncomputable def evalJ (rec : ModeM → Nat → Result Nat) (m0 : Nat) : Result Nat :=
  Bool.rec
    (evalJ_k rec 0 m0)
    (sweepO 64 (evalJ_k rec) 1 (Nat.shiftRight m0 3))
    (Nat.beq (Nat.land m0 7) 5)

noncomputable def evalL_u_p_md0 (kp ku ms : Nat) : ResL :=
  let kout := Nat.add ku (Nat.add kp 3)
  let z := Nat.shiftRight ms 4
  Bool.rec
    (retLUH kout (Nat.add kp 3) z)
    (retLUH kout (Nat.add kp 1) z)
    (Nat.beq (Nat.land ms 15) 0)

noncomputable def evalL_u_p_md2 (kp ku ms : Nat) : ResL :=
  let z := Nat.shiftRight ms 4
  Bool.rec
    (retLUH (Nat.add ku (Nat.add kp 3)) (Nat.add kp 2) z)
    (Bool.rec
      (retLUH (Nat.add ku (Nat.add kp 3)) kp z)
      (retLU (Nat.add ku 1) (Nat.add 33 (Nat.shiftLeft z 6)))
      (Nat.beq kp 0))
    (Nat.beq (Nat.land ms 15) 2)

noncomputable def evalL_u_p_gen (rec : ModeM → Nat → Result Nat) (kp ku ms : Nat) : ResL :=
  mapRetL (evalG rec ms)
    (fun r => mapRetL (evalJ rec (prependU kp r))
      (fun r2 => retLU (Nat.add ku 1) r2))

noncomputable def evalL_u_p (rec : ModeM → Nat → Result Nat) (kp ku ms : Nat) : ResL :=
  let md3 := Nat.land ms 7
  Bool.rec
    (Bool.rec (evalL_u_p_gen rec kp ku ms) (evalL_u_p_md2 kp ku ms) (Nat.beq md3 2))
    (evalL_u_p_md0 kp ku ms)
    (Nat.beq md3 0)

noncomputable def evalL_u_k_non4 (rec : ModeM → Nat → Result Nat) (ku0 m : Nat) : ResL :=
  let b01 := Nat.land m 3
  Bool.rec
    (Bool.rec
      (Bool.rec
        (Bool.rec
          (retLU ku0 (Nat.add 33 (Nat.shiftLeft (Nat.shiftRight m 4) 6)))
          (retLUH (Nat.add ku0 2) 2 (Nat.shiftRight m 4))
          (Nat.beq (Nat.land m 15) 8))
        (Bool.rec
          (mapRetL (evalJ rec (Nat.shiftRight m 2))
            (fun r2 => retLU (Nat.add ku0 1) r2))
          (retLU ku0 (Nat.add 41 (Nat.shiftLeft (Nat.shiftRight m 4) 6)))
          (Nat.beq (Nat.land m 15) 2))
        (Nat.beq b01 2))
      (mapRetL (callH rec 1 (Nat.shiftRight m 2))
        (fun r => mapRetL (evalJ rec r)
          (fun r2 => retLU (Nat.add ku0 1) r2)))
      (Nat.beq b01 1))
    .stopped
    (Nat.beq b01 3)

noncomputable def evalL_u_k (rec : ModeM → Nat → Result Nat) (ku0 m : Nat) : ResL :=
  Bool.rec
    (evalL_u_k_non4 rec ku0 m)
    (sweepLP 64 (evalL_u_p rec) 0 ku0 (Nat.shiftRight m 3))
    (Nat.beq (Nat.land m 7) 4)

noncomputable def evalL_u (rec : ModeM → Nat → Result Nat) (m0 : Nat) : ResL :=
  Bool.rec
    (evalL_u_k rec 0 m0)
    (sweep6 64 (evalL_u_k rec) 1 (Nat.shiftRight m0 3))
    (Nat.beq (Nat.land m0 7) 6)

noncomputable def evalL (rec : ModeM → Nat → Result Nat) (m0 : Nat) : Result Nat :=
  ResL.rec .failed .stopped
    (fun k x => retM (prependU k x))
    (fun k c z =>
      Bool.rec
        (mapRetM (callH rec c z) (fun r => retM (prependU k r)))
        (retM (prependU k z))
        (Nat.beq c 0))
    (evalL_u rec m0)

noncomputable def finishUH (rec : ModeM → Nat → Result Nat) (k c n z : Nat) : Result Nat :=
  let ctot := Nat.add c (carryK k n)
  Bool.rec
    (mapRetM (callH rec ctot z) (fun r2 => retM (prependDigitsK k n r2)))
    (retM (prependDigitsK k n z))
    (Nat.beq ctot 0)

noncomputable def evalHL_fast2 (rec : ModeM → Nat → Result Nat) (base n z2 : Nat) : Result Nat :=
  let s2 := Nat.add base n
  let dig2 := enc2 (Nat.land s2 15)
  let qn2 := Nat.shiftRight s2 4
  Bool.rec
    (mapRetM (callH rec qn2 z2) (fun r2 => retM (Nat.add dig2 (Nat.shiftLeft r2 6))))
    (retM (Nat.add dig2 (Nat.shiftLeft z2 6)))
    (Nat.beq qn2 0)

noncomputable def evalHL_gen (rec : ModeM → Nat → Result Nat) (n y : Nat) : Result Nat :=
  ResL.rec .failed .stopped
    (fun k x => finishUH rec k 0 n x)
    (fun k c z => finishUH rec k c n z)
    (evalL_u rec y)

noncomputable def evalHL (rec : ModeM → Nat → Result Nat) (n y : Nat) : Result Nat :=
  let d4 := Nat.land y 15
  Bool.rec
    (Bool.rec
      (evalHL_gen rec n y)
      (evalHL_fast2 rec 12 n (Nat.shiftRight y 4))
      (Nat.beq d4 0))
    (evalHL_fast2 rec 8 n (Nat.shiftRight y 4))
    (Nat.beq d4 2)

noncomputable def evalH_inv (rec : ModeM → Nat → Result Nat) (n m0 : Nat) : Result Nat :=
  Bool.rec
    (evalHL rec (Nat.sub n 1) (Nat.shiftRight m0 2))
    (Bool.rec
      (evalHL rec (Nat.sub n 2) (Nat.shiftRight m0 2))
      (retM (Nat.add 2 (Nat.shiftLeft (Nat.shiftRight m0 2) 2)))
      (Nat.beq n 1))
    (Nat.beq (Nat.land m0 1) 1)

noncomputable def evalH_w1 (rec : ModeM → Nat → Result Nat) (s z : Nat) : Result Nat :=
  let dig := enc1 (Nat.land s 3)
  mapRetM (evalH_inv rec (Nat.shiftRight s 2) z)
    (fun r2 => retM (Nat.add dig (Nat.shiftLeft r2 3)))

noncomputable def evalH_w2 (rec : ModeM → Nat → Result Nat) (n m0 : Nat) : Result Nat :=
  let s2 := Nat.add (dec2 (Nat.land m0 63)) n
  let dig2 := enc2 (Nat.land s2 15)
  let qn2 := Nat.shiftRight s2 4
  let z2 := Nat.shiftRight m0 6
  Bool.rec
    (Bool.rec
      (mapRetM (evalH_inv rec qn2 z2) (fun r2 => retM (Nat.add dig2 (Nat.shiftLeft r2 6))))
      (mapRetM (callH rec qn2 z2) (fun r2 => retM (Nat.add dig2 (Nat.shiftLeft r2 6))))
      (Nat.beq (Nat.land z2 2) 0))
    (retM (Nat.add dig2 (Nat.shiftLeft z2 6)))
    (Nat.beq qn2 0)

noncomputable def evalH_w4 (rec : ModeM → Nat → Result Nat) (n m0 : Nat) : Result Nat :=
  let s4 := Nat.add (dec4 (Nat.land m0 4095)) n
  let dig4 := enc4 (Nat.land s4 255)
  let qn4 := Nat.shiftRight s4 8
  let z4 := Nat.shiftRight m0 12
  Bool.rec
    (mapRetM (callH rec qn4 z4) (fun r2 => retM (Nat.add dig4 (Nat.shiftLeft r2 12))))
    (retM (Nat.add dig4 (Nat.shiftLeft z4 12)))
    (Nat.beq qn4 0)

noncomputable def evalH_w12 (rec : ModeM → Nat → Result Nat) (n m0 : Nat) : Result Nat :=
  let s12 := Nat.add (dec12_3x4 (Nat.land m0 68719476735)) n
  let dig12 := enc12_3x4 (Nat.land s12 16777215)
  let qn12 := Nat.shiftRight s12 24
  let z12 := Nat.shiftRight m0 36
  Bool.rec
    (mapRetM (callH rec qn12 z12) (fun r2 => retM (Nat.add dig12 (Nat.shiftLeft r2 36))))
    (retM (Nat.add dig12 (Nat.shiftLeft z12 36)))
    (Nat.beq qn12 0)

noncomputable def evalH_wide (rec : ModeM → Nat → Result Nat) (n m0 : Nat) : Result Nat :=
  Bool.rec
    (evalH_w1 rec (Nat.add (dec1 (Nat.land m0 7)) n) (Nat.shiftRight m0 3))
    (Bool.rec
      (evalH_w2 rec n m0)
      (Bool.rec
        (evalH_w4 rec n m0)
        (evalH_w12 rec n m0)
        (Bool.rec false (ok12_hi m0) (Nat.ble 256 n)))
      (Nat.beq (Nat.land m0 1170) 0))
    (Nat.beq (Nat.land m0 18) 0)

noncomputable def evalH_valid (rec : ModeM → Nat → Result Nat) (n m0 : Nat) : Result Nat :=
  let s := Nat.add (dec1 (Nat.land m0 7)) n
  Bool.rec
    (evalH_wide rec n m0)
    (retM (Nat.add (enc1 s) (Nat.shiftLeft (Nat.shiftRight m0 3) 3)))
    (Nat.ble s 3)

noncomputable def evalH (rec : ModeM → Nat → Result Nat) (n m0 : Nat) : Result Nat :=
  Bool.rec
    (Bool.rec (evalH_inv rec n m0) (evalH_valid rec n m0) (Nat.beq (Nat.land m0 2) 0))
    (retM m0)
    (Nat.beq n 0)

noncomputable def evalT_step (rec : ModeM → Nat →
    Result Nat) (md : ModeM) (m0 : Nat) : Result Nat :=
  ModeM.rec (evalG rec m0) (evalL rec m0) (fun n => evalH rec n m0) md

noncomputable def evalT (fuel : Nat) : ModeM → Nat → Result Nat :=
  Nat.rec (fun _ _ => .failed) (fun _ => evalT_step) fuel

noncomputable def mapRetP (o : ResP) (k : Nat → Nat → ResP) : ResP :=
  ResP.rec .failed .stopped k o

noncomputable def evalToP (o : Result Nat) (k : Nat → ResP) : ResP :=
  Result.rec .failed .stopped k o

noncomputable def tcallT_even (ev : ModeM → Nat → Result Nat) (a ko m1 : Nat) : ResP :=
  let y := Nat.shiftRight m1 2
  Bool.rec
    (evalToP (evalH ev (Nat.add a 1) y)
      (fun s => retP (Nat.add ko (Nat.add a 1)) s))
    (Bool.rec
      (Bool.rec
        (evalToP (evalH ev (Nat.sub a 1) y)
          (fun s => retP (Nat.add ko (Nat.add a 1)) s))
        (retP (Nat.add ko 1) (Nat.add 4 (Nat.shiftLeft y 3)))
        (Nat.beq a 1))
      (retP ko (Nat.add 5 (Nat.shiftLeft y 3)))
      (Nat.beq a 0))
    (Nat.beq (Nat.land m1 3) 0)

noncomputable def tcallT_odd (ev : ModeM → Nat → Result Nat) (rec : Nat → Nat →
    ResP) (a ko m1 : Nat) : ResP :=
  let d3 := Nat.land m1 7
  let z := Nat.shiftRight m1 3
  Bool.rec
    (Bool.rec
      (Bool.rec
        .stopped
        (evalToP (evalH ev 1 z)
          (fun r => mapRetP (rec a r)
            (fun pa pm => retP (Nat.add (Nat.add ko 1) pa) pm)))
        (Nat.beq d3 3))
      (mapRetP (rec a z)
        (fun pa pm => retP (Nat.add (Nat.add ko 1) pa) pm))
      (Nat.beq d3 5))
    (collectM 64 (fun ku zm => mapRetP (rec (Nat.add a ku) zm) (fun pa pm =>
        retP (Nat.add ko pa) pm)) 1 z)
    (Nat.beq d3 1)

noncomputable def tcallT_k (ev : ModeM → Nat → Result Nat) (rec : Nat → Nat →
    ResP) (a ko m1 : Nat) : ResP :=
  Bool.rec
    (tcallT_odd ev rec a ko m1)
    (tcallT_even ev a ko m1)
    (Nat.beq (Nat.land m1 1) 0)

noncomputable def tcallT_step (ev : ModeM → Nat → Result Nat) (rec : Nat → Nat →
    ResP) (a m : Nat) : ResP :=
  Bool.rec
    (tcallT_k ev rec a 0 m)
    (sweepO 64 (tcallT_k ev rec a) 1 (Nat.shiftRight m 3))
    (Nat.beq (Nat.land m 7) 5)

noncomputable def tcallT (fuel : Nat) (ev : ModeM → Nat → Result Nat) : Nat → Nat → ResP :=
  Nat.rec (fun _ _ => .failed) (fun _ => tcallT_step ev) fuel

noncomputable def roundT_col1 (pa ca cm : Nat) : ResP :=
  retP (Nat.add (Nat.add 1 pa) ca) cm

noncomputable def roundT_finish (pa pm : Nat) : ResP :=
  Bool.rec
    (retP (Nat.add 1 pa) pm)
    (collectM 64 (roundT_col1 pa) 1 (Nat.shiftRight pm 3))
    (Nat.beq (Nat.land pm 7) 1)

noncomputable def roundT_tcall (tfuel : Nat) (ev : ModeM → Nat → Result Nat) (a m : Nat) : ResP :=
  mapRetP (tcallT tfuel ev (Nat.sub a 1) m) roundT_finish

noncomputable def roundT_fast00 (ev : ModeM → Nat → Result Nat) (a m : Nat) : ResP :=
  evalToP (evalH ev (Nat.sub a 2) (Nat.shiftRight m 2)) (roundT_finish a)

noncomputable def roundT_a0 (ev : ModeM → Nat → Result Nat) (m : Nat) : ResP :=
  evalToP (evalG ev m) (fun r => collectM 64 retP 0 r)

noncomputable def roundT (tfuel : Nat) (ev : ModeM → Nat → Result Nat) (a m : Nat) : ResP :=
  Bool.rec
    (Bool.rec (roundT_tcall tfuel ev a m) (roundT_fast00 ev a m) (Nat.beq (Nat.land m 3) 0))
    (Bool.rec (roundT_tcall tfuel ev a m) (roundT_a0 ev m) (Nat.beq a 0))
    (Nat.ble a 2)

noncomputable def runT_step (tfuel : Nat) (ev : ModeM → Nat → Result Nat) (rec : Nat → Nat →
    ResP) (a m : Nat) : ResP :=
  mapRetP (roundT tfuel ev a m) rec

noncomputable def runT (fuel tfuel efuel : Nat) : Nat → Nat → ResP :=
  Nat.rec (motive := fun _ => Nat → Nat → ResP) retP (fun _ => runT_step tfuel (evalT efuel)) fuel

noncomputable def runT_chk (fuel a m ta tm_exp : Nat) : Bool :=
  ResP.rec false false
    (fun a' m' => Bool.rec false (Nat.beq m' tm_exp) (Nat.beq a' ta))
    (runT fuel 64 256 a m)

noncomputable def runT_halt (fuel a m : Nat) : Bool :=
  ResP.rec false true (fun _ _ => false) (runT fuel 64 256 a m)

/-! ## Soundness Proofs for `prependU`, `prependDigitsK`, Multi-Width SWAR, and Sweeps -/

private theorem retM_eq (x : Nat) : retM x = .returned x := rfl
private theorem retLU_eq (k r : Nat) : retLU k r = .retU k r := rfl
private theorem retLUH_eq (k c z : Nat) : retLUH k c z = .retUH k c z := rfl
private theorem retP_eq (a m : Nat) : retP a m = .ret a m := rfl
private theorem callM_eq (rec : ModeM → Nat → Result Nat) (md : ModeM) (m : Nat) :
    callM rec md m = rec md m := rfl
private theorem callH_eq (rec : ModeM → Nat → Result Nat) (n m : Nat) :
    callH rec n m = rec (.H n) m := rfl

private def prependU_raw (k r : Nat) : Nat := (8 ^ k - 1) / 7 + 8 ^ k * r

private theorem pow2_3k (k : Nat) : 2 ^ (3 * k) = 8 ^ k := by
  rw [Nat.pow_mul]

private theorem prependU_eq_raw (k r : Nat) : prependU k r = prependU_raw k r := by
  rcases k with _ | k
  · simp [prependU, prependU_raw]
  · change (Nat.shiftLeft 1 (3 * (k + 1)) - 1) / 7 + Nat.shiftLeft r (3 * (k + 1)) =
      (8 ^ (k + 1) - 1) / 7 + 8 ^ (k + 1) * r
    rw [shl_eq, shl_eq, pow2_3k, Nat.mul_one]

private theorem pow8_mod7 (k : Nat) : 8 ^ k % 7 = 1 ∧ 1 ≤ 8 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

private theorem prependU_raw_succ (k r : Nat) :
    prependU_raw (k + 1) r = 1 + 8 * prependU_raw k r := by
  unfold prependU_raw
  rw [Nat.pow_succ]
  obtain ⟨hm, hp⟩ := pow8_mod7 k
  have hmul : (8 ^ k * 8) * r = 8 * (8 ^ k * r) := by ring
  rw [hmul]
  omega

theorem bitsM_prependU (k r : Nat) : bitsM (prependU k r) = U ^ k +> bitsM r := by
  rw [prependU_eq_raw]
  induction k with
  | zero => simp [prependU_raw]
  | succ k ih =>
    rw [prependU_raw_succ, bitsM_U, ih, pow_succ_list, append_assoc]

theorem bitsM_enc1 (p z : Nat) (hp : p < 4) :
    bitsM (enc1 p + 8 * z) = digit p +> bitsM z := by
  rcases p with _ | _ | _ | _ | p <;> try omega
  · exact bitsM_U z
  · change bitsM (0 + 8 * z) = Z +> bitsM z
    rw [Nat.zero_add]; exact bitsM_Z z
  · exact bitsM_O z
  · exact bitsM_P z

theorem dec1_lt4 (d3 : Nat) (hd : d3 < 8) (hm : Nat.land d3 2 = 0) :
    dec1 d3 < 4 ∧ enc1 (dec1 d3) = d3 := by
  rcases d3 with _ | _ | _ | _ | _ | _ | _ | _ | d3 <;> try omega
  all_goals
    revert hm
    decide

def digits2 (v : Nat) : List (Fin 2) := digit (v % 4) ++ digit (v / 4)
def digits4 (v : Nat) : List (Fin 2) := digits2 (v % 16) ++ digits2 (v / 16)
def digits12 (v : Nat) : List (Fin 2) :=
  digits4 (v % 256) ++ (digits4 ((v / 256) % 256) ++ digits4 (v / 65536))

private theorem enc2_fin : ∀ v : Fin 16, enc2 v.val = enc1 (v.val % 4) + 8 * enc1 (v.val / 4) := by
  decide +kernel

private theorem dec2_fin : ∀ x : Fin 64,
    Nat.land x.val 18 = 0 → dec2 x.val < 16 ∧ enc2 (dec2 x.val) = x.val := by
  decide +kernel

private theorem enc4_fin : ∀ v : Fin 256, enc4 v.val = enc2 (v.val % 16) + 64 * enc2 (v.val / 16) :=
    by
  decide +kernel

private theorem dec4_fin : ∀ hi : Fin 64, ∀ lo : Fin 64,
    Nat.land (64 * hi.val + lo.val) 1170 = 0 →
    dec4 (64 * hi.val + lo.val) < 256 ∧ enc4 (dec4 (64 * hi.val + lo.val)) = 64 * hi.val + lo.val :=
        by
  decide +kernel

theorem bitsM_enc2 (v z : Nat) (hv : v < 16) :
    bitsM (enc2 v + 64 * z) = digits2 v +> bitsM z := by
  have hf := enc2_fin ⟨v, hv⟩
  dsimp only at hf
  have heq : enc2 v + 64 * z = enc1 (v % 4) + 8 * (enc1 (v / 4) + 8 * z) := by omega
  unfold digits2
  rw [heq, bitsM_enc1 (v % 4) _ (by omega), bitsM_enc1 (v / 4) z (by omega), append_assoc]

theorem bitsM_dec2 (m0 : Nat) (hm : Nat.land m0 18 = 0) :
    dec2 (m0 % 64) < 16 ∧ bitsM m0 = digits2 (dec2 (m0 % 64)) +> bitsM (m0 / 64) := by
  have hm' : Nat.land (m0 % 64) 18 = 0 := by rw [← land_18]; exact hm
  obtain ⟨hlt, henc⟩ := dec2_fin ⟨m0 % 64, by omega⟩ hm'
  dsimp only at hlt henc
  refine ⟨hlt, ?_⟩
  exact bitsM_eq_of_eq m0 (by omega) (bitsM_enc2 (dec2 (m0 % 64)) (m0 / 64) hlt)

theorem bitsM_enc4 (v z : Nat) (hv : v < 256) :
    bitsM (enc4 v + 4096 * z) = digits4 v +> bitsM z := by
  have hf := enc4_fin ⟨v, hv⟩
  dsimp only at hf
  have heq : enc4 v + 4096 * z = enc2 (v % 16) + 64 * (enc2 (v / 16) + 64 * z) := by omega
  unfold digits4
  rw [heq, bitsM_enc2 (v % 16) _ (by omega), bitsM_enc2 (v / 16) z (by omega), append_assoc]

theorem bitsM_dec4 (m0 : Nat) (hm : Nat.land m0 1170 = 0) :
    dec4 (m0 % 4096) < 256 ∧ bitsM m0 = digits4 (dec4 (m0 % 4096)) +> bitsM (m0 / 4096) := by
  have hsplit : 64 * ((m0 % 4096) / 64) + (m0 % 4096) % 64 = m0 % 4096 := by omega
  have hm' : Nat.land (64 * ((m0 % 4096) / 64) + (m0 % 4096) % 64) 1170 = 0 := by
    rw [hsplit, ← land_1170]; exact hm
  obtain ⟨hlt, henc⟩ := dec4_fin ⟨(m0 % 4096) / 64, by omega⟩ ⟨(m0 % 4096) % 64, by omega⟩ hm'
  dsimp only at hlt henc
  rw [hsplit] at hlt henc
  refine ⟨hlt, ?_⟩
  exact bitsM_eq_of_eq m0 (by omega) (bitsM_enc4 (dec4 (m0 % 4096)) (m0 / 4096) hlt)

theorem bitsM_enc12 (v z : Nat) (hv : v < 16777216) :
    bitsM (enc12_3x4 v + 68719476736 * z) = digits12 v +> bitsM z := by
  unfold enc12_3x4 digits12
  simp only [Nat.add_eq, shr_8, shr_16, shl_12, shl_24, land_255]
  have htop : (v / 65536) % 256 = v / 65536 := Nat.mod_eq_of_lt (by omega)
  rw [htop]
  have heq2 : enc4 (v % 256) + (4096 * enc4 ((v / 256) % 256) + 16777216 * enc4 (v / 65536)) +
      68719476736 * z =
      enc4 (v % 256) + 4096 * (enc4 ((v / 256) % 256) + 4096 * (enc4 (v / 65536) + 4096 * z)) := by
    ring
  rw [heq2,
      bitsM_enc4 (v % 256) _ (by omega),
      bitsM_enc4 ((v / 256) % 256) _ (by omega),
      bitsM_enc4 (v / 65536) z (by omega),
      append_assoc, append_assoc]

theorem ok12_hi_elim {m0 : Nat} (hok : ok12_hi m0 = true) :
    Nat.land (m0 / 4096) 1170 = 0 ∧
    Nat.land (m0 / 16777216) 1170 = 0 := by
  unfold ok12_hi at hok
  simp only [shr_12, shr_24] at hok
  cases h1 : Nat.beq (Nat.land (m0 / 4096) 1170) 0 with
  | false => rw [h1] at hok; cases hok
  | true =>
    rw [h1] at hok; dsimp only at hok
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true hok⟩

theorem bitsM_dec12 (m0 : Nat) (hm0 : Nat.land m0 1170 = 0) (hok : ok12_hi m0 = true) :
    dec12_3x4 (Nat.land m0 68719476735) < 16777216 ∧
    bitsM m0 = digits12 (dec12_3x4 (Nat.land m0 68719476735)) +> bitsM (m0 / 68719476736) := by
  obtain ⟨hm1, hm2⟩ := ok12_hi_elim hok
  obtain ⟨hv0, hb0⟩ := bitsM_dec4 m0 hm0
  obtain ⟨hv1, hb1⟩ := bitsM_dec4 (m0 / 4096) hm1
  obtain ⟨hv2, hb2⟩ := bitsM_dec4 (m0 / 16777216) hm2
  have hd : dec12_3x4 (Nat.land m0 68719476735) =
      dec4 (m0 % 4096) + 256 * dec4 ((m0 / 4096) % 4096) + 65536 * dec4 ((m0 / 16777216) % 4096) :=
          by
    unfold dec12_3x4
    simp only [Nat.add_eq, shr_12, shr_24, shl_8, shl_16, land_68719476735, land_4095]
    have e0 : (m0 % 68719476736) % 4096 = m0 % 4096 := by omega
    have e1 : ((m0 % 68719476736) / 4096) % 4096 = (m0 / 4096) % 4096 := by omega
    have e2 : ((m0 % 68719476736) / 16777216) % 4096 = (m0 / 16777216) % 4096 := by omega
    rw [e0, e1, e2]; omega
  refine ⟨by omega, ?_⟩
  rw [hd]
  unfold digits12
  have f0 : (dec4 (m0 % 4096) + 256 * dec4 ((m0 / 4096) % 4096) + 65536 * dec4 ((m0 / 16777216) %
      4096)) % 256 =
      dec4 (m0 % 4096) := by omega
  have f1 : ((dec4 (m0 % 4096) + 256 * dec4 ((m0 / 4096) % 4096) + 65536 * dec4 ((m0 / 16777216) %
      4096)) / 256) % 256 =
      dec4 ((m0 / 4096) % 4096) := by omega
  have f2 : (dec4 (m0 % 4096) + 256 * dec4 ((m0 / 4096) % 4096) + 65536 * dec4 ((m0 / 16777216) %
      4096)) / 65536 =
      dec4 ((m0 / 16777216) % 4096) := by omega
  have g1 : (m0 / 4096) / 4096 = m0 / 16777216 := by omega
  have g2 : (m0 / 16777216) / 4096 = m0 / 68719476736 := by omega
  rw [f0, f1, f2, hb0, hb1, g1, hb2, g2, append_assoc, append_assoc]

theorem digits2_count (v n : ℕ) (hv : v < 16) :
    SegRLs tm (h ^ n) (h ^ ((v + n) / 16)) (digits2 v) (digits2 ((v + n) % 16)) := by
  unfold digits2
  have h0 := digit_count (v % 4) n (by omega)
  have h1 := digit_count (v / 4) ((v % 4 + n) / 4) (by omega)
  have hc := h0.concat h1
  have e1 : (v / 4 + (v % 4 + n) / 4) / 4 = (v + n) / 16 := by omega
  have e2 : (v % 4 + n) % 4 = ((v + n) % 16) % 4 := by omega
  have e3 : (v / 4 + (v % 4 + n) / 4) % 4 = ((v + n) % 16) / 4 := by omega
  rwa [e1, e2, e3] at hc

theorem digits4_count (v n : ℕ) (hv : v < 256) :
    SegRLs tm (h ^ n) (h ^ ((v + n) / 256)) (digits4 v) (digits4 ((v + n) % 256)) := by
  unfold digits4
  have h0 := digits2_count (v % 16) n (by omega)
  have h1 := digits2_count (v / 16) ((v % 16 + n) / 16) (by omega)
  have hc := h0.concat h1
  have e1 : (v / 16 + (v % 16 + n) / 16) / 16 = (v + n) / 256 := by omega
  have e2 : (v % 16 + n) % 16 = ((v + n) % 256) % 16 := by omega
  have e3 : (v / 16 + (v % 16 + n) / 16) % 16 = ((v + n) % 256) / 16 := by omega
  rwa [e1, e2, e3] at hc

theorem digits12_count (v n : ℕ) (hv : v < 16777216) :
    SegRLs tm (h ^ n) (h ^ ((v + n) / 16777216)) (digits12 v) (digits12 ((v + n) % 16777216)) := by
  unfold digits12
  have h0 := digits4_count (v % 256) n (by omega)
  have h1 := digits4_count ((v / 256) % 256) ((v % 256 + n) / 256) (by omega)
  have h2 := digits4_count (v / 65536) (((v / 256) % 256 + (v % 256 + n) / 256) / 256) (by omega)
  have hc := h0.concat (h1.concat h2)
  have e1 : (v / 65536 + ((v / 256) % 256 + (v % 256 + n) / 256) / 256) / 256 =
      (v + n) / 16777216 := by omega
  have e2 : (v % 256 + n) % 256 = ((v + n) % 16777216) % 256 := by omega
  have e3 : ((v / 256) % 256 + (v % 256 + n) / 256) % 256 = (((v + n) % 16777216) / 256) % 256 := by
    omega
  have e4 : (v / 65536 + ((v / 256) % 256 + (v % 256 + n) / 256) / 256) % 256 =
      ((v + n) % 16777216) / 65536 := by omega
  rwa [e1, e2, e3, e4] at hc

private theorem carryK_eq (k n : Nat) : carryK k n = n / 2 ^ (2 * k) := by
  unfold carryK
  rw [Nat.mul_eq, shr_eq]

private theorem div_pow_step (n d k : Nat) (hdk : d ≤ k) :
    (n / 2 ^ (2 * d)) / 2 ^ (2 * (k - d)) = n / 2 ^ (2 * k) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have he : 2 * d + 2 * (k - d) = 2 * k := by omega
  rw [he]

private theorem prependDigitsK_aux_spec (fuel k n : Nat) (hfk : k ≤ fuel) :
    ∃ v : List (Fin 2),
      SegRLs tm (h ^ n) (h ^ (n / 2 ^ (2 * k))) (U ^ k) v ∧
      ∀ r2, bitsM (prependDigitsK_aux fuel k n r2) = v +> bitsM r2 := by
  induction fuel generalizing k n with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    refine ⟨[], ?_, fun r2 => by simp [prependDigitsK_aux, prependU]⟩
    simpa using SegRLs.empty tm (h ^ n)
  | succ fuel ih =>
    change ∃ v, SegRLs tm (h ^ n) (h ^ (n / 2 ^ (2 * k))) (U ^ k) v ∧
      ∀ r2, bitsM (prependDigitsK_step (prependDigitsK_aux fuel) k n r2) = v +> bitsM r2
    unfold prependDigitsK_step
    rcases k with _ | k0
    · refine ⟨[], ?_, fun r2 => rfl⟩
      simpa using SegRLs.empty tm (h ^ n)
    · have hk0_f : Nat.beq (k0 + 1) 0 = false := rfl
      simp only [hk0_f]
      rcases n with _ | n0
      · simp only [Nat.beq, Nat.zero_div]
        exact ⟨U ^ (k0 + 1), .nil (U ^ (k0 + 1)), fun r2 => bitsM_prependU (k0 + 1) r2⟩
      · have hn0_f : Nat.beq (n0 + 1) 0 = false := rfl
        simp only [hn0_f]
        set k := k0 + 1
        set n := n0 + 1
        cases hk12 : Nat.ble 12 k with
        | true =>
          dsimp only [prependDigitsK_12]
          have hle12 := Nat.ble_eq.mp hk12
          simp only [Nat.add_eq, Nat.sub_eq, shr_24, shl_36, land_16777215]
          have hu12 : U ^ k = digits12 0 ++ U ^ (k - 12) := by
            have hk : k = 12 + (k - 12) := by omega
            conv_lhs => rw [hk, pow_add_list]
            rfl
          have hdc12 := digits12_count 0 n (by decide)
          rw [Nat.zero_add] at hdc12
          have hdiv := div_pow_step n 12 k hle12
          change (n / 16777216) / 2 ^ (2 * (k - 12)) = n / 2 ^ (2 * k) at hdiv
          cases hqn : Nat.beq (n / 16777216) 0 with
          | true =>
            have hq0 := Nat.eq_of_beq_eq_true hqn
            have htot0 : n / 2 ^ (2 * k) = 0 := by rw [← hdiv, hq0, Nat.zero_div]
            rw [hq0] at hdc12
            refine ⟨digits12 (n % 16777216) ++ U ^ (k - 12), ?_, fun r2 => ?_⟩
            · rw [hu12, htot0]
              exact hdc12.concat (.nil (U ^ (k - 12)))
            · dsimp only
              rw [bitsM_enc12 (n % 16777216) _ (by omega), bitsM_prependU, append_assoc]
          | false =>
            obtain ⟨v2, hseg2, hb2⟩ := ih (k - 12) (n / 16777216) (by omega)
            refine ⟨digits12 (n % 16777216) ++ v2, ?_, fun r2 => ?_⟩
            · rw [hu12, ← hdiv]
              exact hdc12.concat hseg2
            · dsimp only
              rw [bitsM_enc12 (n % 16777216) _ (by omega), hb2, append_assoc]
        | false =>
          dsimp only
          cases hk4 : Nat.ble 4 k with
          | true =>
            dsimp only [prependDigitsK_4]
            have hle4 := Nat.ble_eq.mp hk4
            simp only [Nat.add_eq, Nat.sub_eq, shr_8, shl_12, land_255]
            have hu4 : U ^ k = digits4 0 ++ U ^ (k - 4) := by
              have hk : k = 4 + (k - 4) := by omega
              conv_lhs => rw [hk, pow_add_list]
              rfl
            have hdc4 := digits4_count 0 n (by decide)
            rw [Nat.zero_add] at hdc4
            have hdiv := div_pow_step n 4 k hle4
            change (n / 256) / 2 ^ (2 * (k - 4)) = n / 2 ^ (2 * k) at hdiv
            cases hqn : Nat.beq (n / 256) 0 with
            | true =>
              have hq0 := Nat.eq_of_beq_eq_true hqn
              have htot0 : n / 2 ^ (2 * k) = 0 := by rw [← hdiv, hq0, Nat.zero_div]
              rw [hq0] at hdc4
              refine ⟨digits4 (n % 256) ++ U ^ (k - 4), ?_, fun r2 => ?_⟩
              · rw [hu4, htot0]
                exact hdc4.concat (.nil (U ^ (k - 4)))
              · dsimp only
                rw [bitsM_enc4 (n % 256) _ (by omega), bitsM_prependU, append_assoc]
            | false =>
              obtain ⟨v2, hseg2, hb2⟩ := ih (k - 4) (n / 256) (by omega)
              refine ⟨digits4 (n % 256) ++ v2, ?_, fun r2 => ?_⟩
              · rw [hu4, ← hdiv]
                exact hdc4.concat hseg2
              · dsimp only
                rw [bitsM_enc4 (n % 256) _ (by omega), hb2, append_assoc]
          | false =>
            dsimp only
            cases hk2 : Nat.ble 2 k with
            | true =>
              dsimp only [prependDigitsK_2]
              have hle2 := Nat.ble_eq.mp hk2
              simp only [Nat.add_eq, Nat.sub_eq, shr_4, shl_6, land_15]
              have hu2 : U ^ k = digits2 0 ++ U ^ (k - 2) := by
                have hk : k = 2 + (k - 2) := by omega
                conv_lhs => rw [hk, pow_add_list]
                rfl
              have hdc2 := digits2_count 0 n (by decide)
              rw [Nat.zero_add] at hdc2
              have hdiv := div_pow_step n 2 k hle2
              change (n / 16) / 2 ^ (2 * (k - 2)) = n / 2 ^ (2 * k) at hdiv
              cases hqn : Nat.beq (n / 16) 0 with
              | true =>
                have hq0 := Nat.eq_of_beq_eq_true hqn
                have htot0 : n / 2 ^ (2 * k) = 0 := by rw [← hdiv, hq0, Nat.zero_div]
                rw [hq0] at hdc2
                refine ⟨digits2 (n % 16) ++ U ^ (k - 2), ?_, fun r2 => ?_⟩
                · rw [hu2, htot0]
                  exact hdc2.concat (.nil (U ^ (k - 2)))
                · dsimp only
                  rw [bitsM_enc2 (n % 16) _ (by omega), bitsM_prependU, append_assoc]
              | false =>
                obtain ⟨v2, hseg2, hb2⟩ := ih (k - 2) (n / 16) (by omega)
                refine ⟨digits2 (n % 16) ++ v2, ?_, fun r2 => ?_⟩
                · rw [hu2, ← hdiv]
                  exact hdc2.concat hseg2
                · dsimp only
                  rw [bitsM_enc2 (n % 16) _ (by omega), hb2, append_assoc]
            | false =>
              dsimp only
              have hk1 : k = 1 := by
                rcases (by omega : k = 1 ∨ 2 ≤ k) with h1 | h2
                · exact h1
                · rw [Nat.ble_eq.mpr h2] at hk2; cases hk2
              simp only [Nat.add_eq, shl_3, land_3]
              refine ⟨digit (n % 4), ?_, fun r2 => bitsM_enc1 (n % 4) r2 (by omega)⟩
              rw [hk1, pow_one_list]
              have hdc1 := digit_count 0 n (by decide)
              rw [Nat.zero_add] at hdc1
              exact hdc1

theorem digitsK_spec (k n : Nat) :
    ∃ v : List (Fin 2),
      SegRLs tm (h ^ n) (h ^ (carryK k n)) (U ^ k) v ∧
      ∀ r2, bitsM (prependDigitsK k n r2) = v +> bitsM r2 := by
  rw [carryK_eq]
  exact prependDigitsK_aux_spec k k n (Nat.le_refl k)

theorem GP : SegRLs tm g g P U := segRLs_c_spec tm (T := 100) (by decide)
theorem G01 : SegRLs tm g [] [0, 1] U := segRLs_c_spec tm (T := 100) (by decide)
theorem G10 : SegRLs tm g h [1, 0] U := segRLs_c_spec tm (T := 100) (by decide)
theorem G0000 : SegRLs tm g [] [0, 0, 0, 0] [1, 0, 1, 0, 1] := segRLs_c_spec tm (T :=
    100) (by decide)
theorem G0001 : SegRLs tm g h [0, 0, 0, 1] [1, 0, 0, 0, 1] := segRLs_c_spec tm (T :=
    100) (by decide)

theorem J00 : SegRLs tm j [] [0, 0] O := segRLs_c_spec tm (T := 100) (by decide)
theorem J01 : SegRLs tm j h [0, 1] U := segRLs_c_spec tm (T := 100) (by decide)

theorem L01 : SegRLs tm e j [0, 1] U := segRLs_c_spec tm (T := 100) (by decide)
theorem L011 : SegRLs tm e e W6 U := segRLs_c_spec tm (T := 100) (by decide)
theorem L10 : SegRLs tm e (h ++ j) [1, 0] U := segRLs_c_spec tm (T := 100) (by decide)
theorem LP : SegRLs tm e (g ++ j) P U := segRLs_c_spec tm (T := 100) (by decide)
theorem L0000 : SegRLs tm e [] [0, 0, 0, 0] [1, 0, 0, 0, 0, 1] := segRLs_c_spec tm (T :=
    100) (by decide)
theorem L0100 : SegRLs tm e [] [0, 1, 0, 0] [1, 0, 0, 1, 0, 1] := segRLs_c_spec tm (T :=
    100) (by decide)
theorem L0001 : SegRLs tm e (h ^ 2) [0, 0, 0, 1] (U ++ U) := segRLs_c_spec tm (T := 100) (by decide)

theorem H01rest (n : ℕ) : SegRLs tm (h ++ h ^ n) (e ++ h ^ n) [0, 1] [] :=
  (H0.concat J1).trans (SegRLs.empty tm (h ^ n))

theorem GP_run (k : ℕ) : SegRLs tm g g (P ^ k) (U ^ k) := by
  induction k with
  | zero => exact SegRLs.empty tm g
  | succ k ih => exact GP.concat ih

theorem JO_run (k : ℕ) : SegRLs tm j j (O ^ k) (U ^ k) := by
  induction k with
  | zero => exact SegRLs.empty tm j
  | succ k ih => exact JO.concat ih

theorem L011_run (k : ℕ) : SegRLs tm e e (W6 ^ k) (U ^ k) := by
  induction k with
  | zero => exact SegRLs.empty tm e
  | succ k ih => exact L011.concat ih

theorem U_pow_append_1 (k : ℕ) : U ^ k ++ ([1] : List (Fin 2)) = ([1] : List (Fin 2)) ++ P ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_list U k, List.append_assoc, ih, pow_succ_list P k]
    rfl

theorem GJP_011 {X : Type} (den : X →
    ListBlank (Fin 2)) (kp : ℕ) (r : ListBlank (Fin 2)) (o : Result X)
    (hS : Spec den (g ++ j) (P ^ kp +> r) o) :
    Spec (fun x => U +> den x) (g ++ j) (P ^ kp +> (W6 +> r)) o := by
  have hG0 : SideRLs tm g ((P ^ kp ++ [0, 1]) +> (([1] : List (Fin 2)) +> r))
      ((U ^ kp ++ U) +> (([1] : List (Fin 2)) +> r)) :=
    ((GP_run kp).concat G01).sideRLs_concat (.nil (([1] : List (Fin 2)) +> r))
  have hin : (P ^ kp ++ [0, 1]) +> (([1] : List (Fin 2)) +> r) = P ^ kp +> (W6 +> r) := by
    rw [append_assoc]; rfl
  have hout : (U ^ kp ++ U) +> (([1] : List (Fin 2)) +> r) =
      ([1, 0, 0, 1] : List (Fin 2)) +> (P ^ kp +> r) := by
    rw [← pow_succ_list' U kp, ← append_assoc (U ^ (kp + 1)) [1] r,
        U_pow_append_1 (kp + 1), pow_succ_list P kp, ← List.append_assoc [1] P (P ^ kp),
        append_assoc]
    rfl
  rw [hin, hout] at hG0
  have hJP : SegRLs tm j (g ++ j) [1, 0, 0, 1] U := J1.concat LP
  exact after_spec (fun x => U +> den x) hG0 (rule_spec den hJP hS)

theorem GJP_011_seg {hs' : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {w v : List (Fin 2)} (kp : ℕ)
    (hS : SegRLs tm (g ++ j) hs' (P ^ kp ++ w) v) :
    SegRLs tm (g ++ j) hs' (P ^ kp ++ (W6 ++ w)) (U ++ v) := by
  have hG0 : SegRLs tm g [] ((P ^ kp ++ [0, 1]) ++ ([1] ++ w)) ((U ^ kp ++ U) ++ ([1] ++ w)) :=
    ((GP_run kp).concat G01).concat (.nil ([1] ++ w))
  have hin : (P ^ kp ++ [0, 1]) ++ ([1] ++ w) = P ^ kp ++ (W6 ++ w) := by
    simp only [List.append_assoc]; rfl
  have hout : (U ^ kp ++ U) ++ ([1] ++ w) = ([1, 0, 0, 1] : List (Fin 2)) ++ (P ^ kp ++ w) := by
    rw [← pow_succ_list' U kp, ← List.append_assoc (U ^ (kp + 1)) [1] w,
        U_pow_append_1 (kp + 1), pow_succ_list P kp]
    simp only [List.append_assoc]; rfl
  rw [hin, hout] at hG0
  have hJP : SegRLs tm j (g ++ j) [1, 0, 0, 1] U := J1.concat LP
  exact hG0.trans (hJP.concat hS)

theorem TO_seg {hs' : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {w v : List (Fin 2)} (a : ℕ)
    (hS : SegRLs tm j hs' (U ^ a ++ w) v) :
    SegRLs tm j hs' (U ^ a ++ (O ++ w)) (U ++ v) := by
  rcases a with _ | a
  · exact JO.concat hS
  · have hQ : SegRLs tm q [] ((U ^ a ++ O) ++ w) (U ^ (a + 1) ++ w) := by
      have h1 := (QrunO a).concat (.nil w)
      have ha : 1 + a = a + 1 := by omega
      rwa [ha] at h1
    have hmid := JU.concat (hQ.trans hS)
    have hin : U ++ ((U ^ a ++ O) ++ w) = U ^ (a + 1) ++ (O ++ w) := by
      rw [pow_succ_list U a]; simp only [List.append_assoc]
    rwa [hin] at hmid

theorem T00_seg (a : ℕ) :
    SegRLs tm j (h ^ (1 + a)) (U ^ (2 + a) ++ [0, 0]) (U ^ (3 + a)) := by
  have hQ : SegRLs tm q [] (U ^ (1 + a) ++ [0, 0]) (U ^ a ++ (O ++ [0, 1])) := by
    simpa only [List.append_assoc] using Qrun00 a
  have hJ : SegRLs tm j (h ^ (1 + a)) (U ^ a ++ (O ++ [0, 1])) (U ++ U ^ (1 + a)) :=
    TO_seg a (T01 a)
  have hmid := JU.concat (hQ.trans hJ)
  have hin : U ++ (U ^ (1 + a) ++ [0, 0]) = U ^ (2 + a) ++ [0, 0] := by
    have h2 : 2 + a = (1 + a) + 1 := by omega
    rw [h2, pow_succ_list U (1 + a), List.append_assoc]
  have hout : U ++ (U ++ U ^ (1 + a)) = U ^ (3 + a) := by
    have h3 : 3 + a = ((1 + a) + 1) + 1 := by omega
    rw [h3, pow_succ_list U ((1 + a) + 1), pow_succ_list U (1 + a)]
  rwa [hin, hout] at hmid

private theorem spec_of_eq {X : Type} {den : X → ListBlank (Fin 2)}
    {hs : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {r : ListBlank (Fin 2)} {o1 o2 : Result X}
    (hS : Spec den hs r o1) (heq : o1 = o2) : Spec den hs r o2 :=
  heq ▸ hS

theorem sweepP_inv {α : Type} (P_ok : ListBlank (Fin 2) → α → Prop)
    (cont : Nat → Nat → α)
    (hcont : ∀ k m, P_ok (P ^ k +> bitsM m) (cont k m))
    (fuel k m : Nat) :
    P_ok (P ^ k +> bitsM m) (sweepP fuel cont k m) := by
  induction fuel generalizing k m with
  | zero => exact hcont k m
  | succ fuel ih =>
    change P_ok (P ^ k +> bitsM m) (sweepP_step cont (sweepP fuel cont) k m)
    unfold sweepP_step sweepP_hit
    simp only [Nat.add_eq, shr_eq, land_7, land_4095, land_281474976710655]
    cases hd3 : Nat.beq (m % 8) 4 with
    | false => exact hcont k m
    | true =>
      dsimp only
      have hm1 := Nat.eq_of_beq_eq_true hd3
      cases hd16 : Nat.beq (m % 281474976710656) 160842843834660 with
      | true =>
        dsimp only
        have hm16 := Nat.eq_of_beq_eq_true hd16
        have heq : P ^ k +> bitsM m = P ^ (k + 16) +> bitsM (m / 281474976710656) := by
          rw [bitsM_eq_of_eq m (by omega) (bitsM_P16 (m / 281474976710656)), ← append_assoc,
              ← pow_add_list]
        rw [heq]
        exact ih (k + 16) (m / 281474976710656)
      | false =>
        dsimp only
        cases hd4 : Nat.beq (m % 4096) 2340 with
        | true =>
          dsimp only
          have hm4 := Nat.eq_of_beq_eq_true hd4
          have heq : P ^ k +> bitsM m = P ^ (k + 4) +> bitsM (m / 4096) := by
            rw [bitsM_eq_of_eq m (by omega) (bitsM_P4 (m / 4096)), ← append_assoc, ← pow_add_list]
          rw [heq]
          exact ih (k + 4) (m / 4096)
        | false =>
          dsimp only
          have heq : P ^ k +> bitsM m = P ^ (k + 1) +> bitsM (m / 8) := by
            rw [bitsM_eq_of_eq m (by omega) (bitsM_P (m / 8)), ← append_assoc, ← pow_succ_list']
          rw [heq]
          exact ih (k + 1) (m / 8)

theorem sweepO_inv {α : Type} (P_ok : ListBlank (Fin 2) → α → Prop)
    (cont : Nat → Nat → α)
    (hcont : ∀ k m, P_ok (O ^ k +> bitsM m) (cont k m))
    (fuel k m : Nat) :
    P_ok (O ^ k +> bitsM m) (sweepO fuel cont k m) := by
  induction fuel generalizing k m with
  | zero => exact hcont k m
  | succ fuel ih =>
    change P_ok (O ^ k +> bitsM m) (sweepO_step cont (sweepO fuel cont) k m)
    unfold sweepO_step sweepO_hit
    simp only [Nat.add_eq, shr_eq, land_7, land_4095]
    cases hd3 : Nat.beq (m % 8) 5 with
    | false => exact hcont k m
    | true =>
      dsimp only
      have hm1 := Nat.eq_of_beq_eq_true hd3
      cases hd4 : Nat.beq (m % 4096) 2925 with
      | true =>
        dsimp only
        have hm4 := Nat.eq_of_beq_eq_true hd4
        have heq : O ^ k +> bitsM m = O ^ (k + 4) +> bitsM (m / 4096) := by
          rw [bitsM_eq_of_eq m (by omega) (bitsM_O4 (m / 4096)), ← append_assoc, ← pow_add_list]
        rw [heq]
        exact ih (k + 4) (m / 4096)
      | false =>
        dsimp only
        have heq : O ^ k +> bitsM m = O ^ (k + 1) +> bitsM (m / 8) := by
          rw [bitsM_eq_of_eq m (by omega) (bitsM_O (m / 8)), ← append_assoc, ← pow_succ_list']
        rw [heq]
        exact ih (k + 1) (m / 8)

theorem sweep6_inv {α : Type} (P_ok : ListBlank (Fin 2) → α → Prop)
    (cont : Nat → Nat → α)
    (hcont : ∀ k m, P_ok (W6 ^ k +> bitsM m) (cont k m))
    (fuel k m : Nat) :
    P_ok (W6 ^ k +> bitsM m) (sweep6 fuel cont k m) := by
  induction fuel generalizing k m with
  | zero => exact hcont k m
  | succ fuel ih =>
    change P_ok (W6 ^ k +> bitsM m) (sweep6_step cont (sweep6 fuel cont) k m)
    unfold sweep6_step sweep6_hit
    simp only [Nat.add_eq, shr_eq, land_7, land_63, land_4095, land_281474976710655]
    cases hd3 : Nat.beq (m % 8) 6 with
    | false => exact hcont k m
    | true =>
      dsimp only
      have hm1 := Nat.eq_of_beq_eq_true hd3
      cases hd16 : Nat.beq (m % 281474976710656) 241264265751990 with
      | true =>
        dsimp only
        have hm16 := Nat.eq_of_beq_eq_true hd16
        have heq : W6 ^ k +> bitsM m = W6 ^ (k + 16) +> bitsM (m / 281474976710656) := by
          rw [bitsM_eq_of_eq m (by omega) (bitsM_W6_16 (m / 281474976710656)), ← append_assoc,
              ← pow_add_list]
        rw [heq]
        exact ih (k + 16) (m / 281474976710656)
      | false =>
        dsimp only
        cases hd4 : Nat.beq (m % 4096) 3510 with
        | true =>
          dsimp only
          have hm4 := Nat.eq_of_beq_eq_true hd4
          have heq : W6 ^ k +> bitsM m = W6 ^ (k + 4) +> bitsM (m / 4096) := by
            rw [bitsM_eq_of_eq m (by omega) (bitsM_W6_4 (m / 4096)), ← append_assoc, ← pow_add_list]
          rw [heq]
          exact ih (k + 4) (m / 4096)
        | false =>
          dsimp only
          cases hd2 : Nat.beq (m % 64) 54 with
          | true =>
            dsimp only
            have hm2 := Nat.eq_of_beq_eq_true hd2
            have heq : W6 ^ k +> bitsM m = W6 ^ (k + 2) +> bitsM (m / 64) := by
              rw [bitsM_eq_of_eq m (by omega) (bitsM_W6_2 (m / 64)), ← append_assoc, ← pow_add_list]
            rw [heq]
            exact ih (k + 2) (m / 64)
          | false =>
            dsimp only
            have heq : W6 ^ k +> bitsM m = W6 ^ (k + 1) +> bitsM (m / 8) := by
              rw [bitsM_eq_of_eq m (by omega) (bitsM_W6 (m / 8)), ← append_assoc, ← pow_succ_list']
            rw [heq]
            exact ih (k + 1) (m / 8)

/-! ## `SpecL` / `SpecLP` Specification for `sweepLP` and `evalL_u` -/

def SpecL (hs : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)))
    (r : ListBlank (Fin 2)) (o : ResL) : Prop :=
  match o with
  | .failed => True
  | .stopped => SideRLsHalt tm hs r
  | .retU k x => SideRLs tm hs r (U ^ k +> bitsM x)
  | .retUH k c z => ∃ w, r = w +> bitsM z ∧ SegRLs tm hs (h ^ c) w (U ^ k)

def SpecLP (kp ku : Nat) (r : ListBlank (Fin 2)) (o : ResL) : Prop :=
  match o with
  | .failed => True
  | .stopped => SideRLsHalt tm (g ++ j) (P ^ kp +> r)
  | .retU kout x => ∃ d, kout = ku + d ∧ SideRLs tm (g ++ j) (P ^ kp +> r) (U ^ d +> bitsM x)
  | .retUH kout c z =>
    ∃ d w, kout = ku + d ∧ r = w +> bitsM z ∧ SegRLs tm (g ++ j) (h ^ c) (P ^ kp ++ w) (U ^ d)

private theorem specLP_shiftP {s kp ku : Nat} {r : ListBlank (Fin 2)} {o : ResL}
    (hS : SpecLP (kp + s) ku r o) :
    SpecLP kp ku (P ^ s +> r) o := by
  cases o with
  | failed => trivial
  | stopped =>
    dsimp only [SpecLP] at hS ⊢
    rwa [← append_assoc, ← pow_add_list]
  | retU kout x =>
    obtain ⟨d, hk, hs⟩ := hS
    refine ⟨d, hk, ?_⟩
    rwa [← append_assoc, ← pow_add_list]
  | retUH kout c z =>
    obtain ⟨d, w, hk, hr, hseg⟩ := hS
    refine ⟨d, P ^ s ++ w, hk, by rw [hr, ← append_assoc], ?_⟩
    rwa [← List.append_assoc, ← pow_add_list]

private theorem specLP_w6 {kp ku : Nat} {r : ListBlank (Fin 2)} {o : ResL}
    (hS : SpecLP kp (ku + 1) r o) :
    SpecLP kp ku (W6 +> r) o := by
  cases o with
  | failed => trivial
  | stopped => exact GJP_011 (fun _ : Nat => default) kp r (.stopped : Result Nat) hS
  | retU kout x =>
    obtain ⟨d, hkout, hSide⟩ := hS
    have h1 : SideRLs tm (g ++ j) (P ^ kp +> (W6 +> r)) (U +> (U ^ d +> bitsM x)) :=
      GJP_011 (fun _ : Unit => U ^ d +> bitsM x) kp r (.returned ()) hSide
    refine ⟨1 + d, by omega, ?_⟩
    rw [pow_add_list, pow_one_list, append_assoc]
    exact h1
  | retUH kout c z =>
    obtain ⟨d, w, hkout, hr, hseg⟩ := hS
    refine ⟨1 + d, W6 ++ w, by omega, by rw [hr, ← append_assoc], ?_⟩
    rw [pow_add_list, pow_one_list]
    exact GJP_011_seg kp hseg

private theorem specLP_w6_2 {kp ku : Nat} {r : ListBlank (Fin 2)} {o : ResL}
    (hS : SpecLP kp (ku + 2) r o) :
    SpecLP kp ku (W6 ^ 2 +> r) o := by
  have h1 := specLP_w6 (ku := ku + 1) (by simpa [Nat.add_assoc] using hS)
  have h2 := specLP_w6 (ku := ku) h1
  have hw : W6 ^ 2 +> r = W6 +> (W6 +> r) := rfl
  rwa [hw]

private theorem specLP_w6_4 {kp ku : Nat} {r : ListBlank (Fin 2)} {o : ResL}
    (hS : SpecLP kp (ku + 4) r o) :
    SpecLP kp ku (W6 ^ 4 +> r) o := by
  have h1 := specLP_w6_2 (ku := ku + 2) (by simpa [Nat.add_assoc] using hS)
  have h2 := specLP_w6_2 (ku := ku) h1
  have hw : W6 ^ 4 +> r = W6 ^ 2 +> (W6 ^ 2 +> r) := by
    rw [← append_assoc]; rfl
  rwa [hw]

private theorem specLP_w6_16 {kp ku : Nat} {r : ListBlank (Fin 2)} {o : ResL}
    (hS : SpecLP kp (ku + 16) r o) :
    SpecLP kp ku (W6 ^ 16 +> r) o := by
  have h1 := specLP_w6_4 (ku := ku + 12) (by simpa [Nat.add_assoc] using hS)
  have h2 := specLP_w6_4 (ku := ku + 8) (by simpa [Nat.add_assoc] using h1)
  have h3 := specLP_w6_4 (ku := ku + 4) (by simpa [Nat.add_assoc] using h2)
  have h4 := specLP_w6_4 (ku := ku) h3
  have hw : W6 ^ 16 +> r = W6 ^ 4 +> (W6 ^ 4 +> (W6 ^ 4 +> (W6 ^ 4 +> r))) := by
    simp only [← append_assoc, ← pow_add_list]
  rwa [hw]

private theorem specLP_to_specL {ku0 : Nat} {r : ListBlank (Fin 2)} {o : ResL}
    (hS : SpecLP 0 (ku0 + 1) r o) :
    SpecL e (W6 ^ ku0 +> (P +> r)) o := by
  have hpre : SegRLs tm e (g ++ j) (W6 ^ ku0 ++ P) (U ^ (ku0 + 1)) := by
    rw [pow_add_list, pow_one_list]
    exact (L011_run ku0).concat LP
  rw [← append_assoc (W6 ^ ku0) P r]
  cases o with
  | failed => trivial
  | stopped =>
    dsimp only [SpecLP, pow_zero_list, append_nil] at hS
    exact hpre.sideRLsHalt_concat hS
  | retU kout x =>
    obtain ⟨d, hk, hs⟩ := hS
    dsimp only [pow_zero_list, append_nil] at hs
    dsimp only [SpecL]
    rw [hk, pow_add_list, append_assoc (U ^ (ku0 + 1)) (U ^ d)]
    exact hpre.sideRLs_concat hs
  | retUH kout c z =>
    obtain ⟨d, w, hk, hr, hseg⟩ := hS
    dsimp only [pow_zero_list, List.nil_append] at hseg
    refine ⟨(W6 ^ ku0 ++ P) ++ w, by rw [hr, ← append_assoc], ?_⟩
    rw [hk, pow_add_list]
    exact hpre.concat hseg

theorem sweepLP_spec (cont : Nat → Nat → Nat → ResL)
    (hcont : ∀ kp ku ms, SpecLP kp (ku + 1) (bitsM ms) (cont kp ku ms))
    (fuel kp ku m : Nat) :
    SpecLP kp (ku + 1) (bitsM m) (sweepLP fuel cont kp ku m) := by
  induction fuel generalizing kp ku m with
  | zero => exact hcont kp ku m
  | succ fuel ih =>
    change SpecLP kp (ku + 1) (bitsM m) (sweepLP_step cont (sweepLP fuel cont) kp ku m)
    unfold sweepLP_step sweepLP_p sweepLP_w6
    simp only [Nat.add_eq, shr_eq, land_7, land_63, land_4095, land_281474976710655]
    cases hd4 : Nat.beq (m % 8) 4 with
    | true =>
      dsimp only
      have hm1 := Nat.eq_of_beq_eq_true hd4
      cases hp16 : Nat.beq (m % 281474976710656) 160842843834660 with
      | true =>
        dsimp only
        have hm16 := Nat.eq_of_beq_eq_true hp16
        rw [bitsM_eq_of_eq m (by omega) (bitsM_P16 (m / 281474976710656))]
        exact specLP_shiftP (ih (kp + 16) ku (m / 281474976710656))
      | false =>
        dsimp only
        cases hp4 : Nat.beq (m % 4096) 2340 with
        | true =>
          dsimp only
          have hm4 := Nat.eq_of_beq_eq_true hp4
          rw [bitsM_eq_of_eq m (by omega) (bitsM_P4 (m / 4096))]
          exact specLP_shiftP (ih (kp + 4) ku (m / 4096))
        | false =>
          dsimp only
          cases hp2 : Nat.beq (m % 64) 36 with
          | true =>
            dsimp only
            have hm2 := Nat.eq_of_beq_eq_true hp2
            rw [bitsM_eq_of_eq m (by omega) (bitsM_P2 (m / 64))]
            exact specLP_shiftP (ih (kp + 2) ku (m / 64))
          | false =>
            dsimp only
            rw [bitsM_eq_of_eq m (by omega) (bitsM_P (m / 8))]
            exact specLP_shiftP (s := 1) (ih (kp + 1) ku (m / 8))
    | false =>
      dsimp only
      cases hd6 : Nat.beq (m % 8) 6 with
      | false => exact hcont kp ku m
      | true =>
        dsimp only
        have hm6 := Nat.eq_of_beq_eq_true hd6
        cases hw16 : Nat.beq (m % 281474976710656) 241264265751990 with
        | true =>
          dsimp only
          have hm16 := Nat.eq_of_beq_eq_true hw16
          rw [bitsM_eq_of_eq m (by omega) (bitsM_W6_16 (m / 281474976710656))]
          have hsub := ih kp (ku + 16) (m / 281474976710656)
          have hadd : ku + 16 + 1 = (ku + 1) + 16 := by omega
          rw [hadd] at hsub
          exact specLP_w6_16 hsub
        | false =>
          dsimp only
          cases hw4 : Nat.beq (m % 4096) 3510 with
          | true =>
            dsimp only
            have hm4 := Nat.eq_of_beq_eq_true hw4
            rw [bitsM_eq_of_eq m (by omega) (bitsM_W6_4 (m / 4096))]
            have hsub := ih kp (ku + 4) (m / 4096)
            have hadd : ku + 4 + 1 = (ku + 1) + 4 := by omega
            rw [hadd] at hsub
            exact specLP_w6_4 hsub
          | false =>
            dsimp only
            cases hw2 : Nat.beq (m % 64) 54 with
            | true =>
              dsimp only
              have hm2 := Nat.eq_of_beq_eq_true hw2
              rw [bitsM_eq_of_eq m (by omega) (bitsM_W6_2 (m / 64))]
              have hsub := ih kp (ku + 2) (m / 64)
              have hadd : ku + 2 + 1 = (ku + 1) + 2 := by omega
              rw [hadd] at hsub
              exact specLP_w6_2 hsub
            | false =>
              dsimp only
              rw [bitsM_eq_of_eq m (by omega) (bitsM_W6 (m / 8))]
              have hsub := ih kp (ku + 1) (m / 8)
              have hadd : ku + 1 + 1 = (ku + 1) + 1 := by omega
              rw [hadd] at hsub
              exact specLP_w6 hsub

/-! ## Soundness of `evalG`, `evalJ`, `evalL_u`, `evalL` -/

def signalsM : ModeM → List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))
  | .G => g
  | .L => e
  | .H n => h ^ n

def EvalSpec (ev : ModeM → Nat → Result Nat) : Prop :=
  ∀ mode m0, Spec bitsM (signalsM mode) (bitsM m0) (ev mode m0)

private theorem wrap_prependU_spec (k : Nat)
    {hs : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {w : List (Fin 2)} {r : ListBlank (Fin 2)} {o : Result Nat} {f : Nat → Nat}
    (hRun : SegRLs tm hs hs w (U ^ k))
    (hS : Spec bitsM hs r (map_result f o)) :
    Spec bitsM hs (w +> r) (map_result (fun x => prependU k (f x)) o) := by
  have hL := lift_rule bitsM bitsM hRun (fun x => bitsM_prependU k x) hS
  cases o <;> exact hL

theorem evalG_k_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec) (k m : Nat) :
    Spec bitsM g (P ^ k +> bitsM m) (evalG_k rec k m) := by
  unfold evalG_k evalG_b00
  simp only [Nat.add_eq, shr_2, shr_3, shr_4, shl_3, shl_5, land_1, land_3, retM_eq, callM_eq,
      callH_eq]
  have hb01 : m % 4 = 3 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 0 := by omega
  rcases hb01 with h3 | h1 | h2 | h0
  · simp only [h3, Nat.beq]
    dsimp only [Spec]
    rw [bitsM_eq_of_eq m (by omega) (bitsM_11 (m / 4))]
    exact (GP_run k).sideRLsHalt_concat
      (.here (E, [0, 0]) (C, [1]) [] ([1, 1] +> bitsM (m / 4)) (fun l => G11 l (bitsM (m / 4))))
  · simp only [h1, Nat.beq]
    rw [bitsM_eq_of_eq m (by omega) (bitsM_10 (m / 4))]
    have hih := hev (.H 1) (m / 4)
    dsimp only [signalsM] at hih
    have hW := wrap_prependU_spec k (GP_run k) (lift_rule bitsM bitsM G10 bitsM_U hih)
    exact spec_of_eq hW (by cases rec (.H 1) (m / 4) <;> rfl)
  · simp only [h2, Nat.beq]
    dsimp only [Spec]
    rw [bitsM_eq_of_eq m (by omega) (bitsM_01 (m / 4)), bitsM_prependU, bitsM_U]
    exact (GP_run k).sideRLs_concat (G01.sideRLs_concat (.nil (bitsM (m / 4))))
  · simp only [h0, Nat.beq]
    have hb23 : ((m / 4) % 4) % 2 = 1 ∨ (m / 4) % 4 = 2 ∨ (m / 4) % 4 = 0 := by omega
    rcases hb23 with hp | h0001 | h0000
    · simp only [hp, Nat.beq]
      rw [bitsM_eq_of_eq m (by omega) (bitsM_P (m / 8))]
      have hW := wrap_prependU_spec k (GP_run k) (lift_rule bitsM bitsM GP bitsM_U (hev .G (m / 8)))
      exact spec_of_eq hW (by cases rec .G (m / 8) <;> rfl)
    · simp only [h0001, Nat.beq]
      rw [bitsM_eq_of_eq m (by omega) (bitsM_0001 (m / 16))]
      have hih := hev (.H 1) (m / 16)
      dsimp only [signalsM] at hih
      have hW := wrap_prependU_spec k (GP_run k) (lift_rule bitsM bitsM G0001 bitsM_17_32 hih)
      exact spec_of_eq hW (by cases rec (.H 1) (m / 16) <;> rfl)
    · have hp0 : ((m / 4) % 4) % 2 = 0 := by omega
      have h2f : Nat.beq ((m / 4) % 4) 2 = false := by rw [h0000]; rfl
      simp only [hp0, h2f, Nat.beq]
      dsimp only [Spec]
      rw [bitsM_eq_of_eq m (by omega) (bitsM_0000 (m / 16)), bitsM_prependU, bitsM_21_32]
      exact (GP_run k).sideRLs_concat (G0000.sideRLs_concat (.nil (bitsM (m / 16))))

theorem evalG_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec) (m0 : Nat) :
    Spec bitsM g (bitsM m0) (evalG rec m0) := by
  unfold evalG
  simp only [shr_3, land_7]
  cases hd4 : Nat.beq (m0 % 8) 4 with
  | false =>
    dsimp only
    simpa using evalG_k_spec hev 0 m0
  | true =>
    dsimp only
    have hm := Nat.eq_of_beq_eq_true hd4
    have heq : bitsM m0 = P ^ 1 +> bitsM (m0 / 8) := by
      rw [bitsM_eq_of_eq m0 (by omega) (bitsM_P (m0 / 8))]; rfl
    rw [heq]
    exact sweepP_inv (fun r o => Spec bitsM g r o) (evalG_k rec) (evalG_k_spec hev) 64 1 (m0 / 8)

theorem evalJ_k_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec) (k m : Nat) :
    Spec bitsM j (O ^ k +> bitsM m) (evalJ_k rec k m) := by
  unfold evalJ_k
  simp only [Nat.add_eq, shr_1, shr_2, shl_3, land_1, retM_eq, callM_eq, callH_eq]
  rw [land_2 m]
  have hm4 : m % 4 = 1 ∨ m % 4 = 3 ∨ m % 4 = 2 ∨ m % 4 = 0 := by omega
  rcases hm4 with h1 | h3 | h2 | h0
  · have hm2 : m % 2 = 1 := by omega
    simp only [hm2, Nat.beq]
    rw [bitsM_eq_of_eq m (by omega) (bitsM_bit1 (m / 2))]
    change Spec bitsM j (O ^ k +> (([1] : List (Fin 2)) +> bitsM (m / 2))) _
    have hSub : Spec bitsM j (([1] : List (Fin 2)) +>
        bitsM (m / 2)) (map_result id (rec .L (m / 2))) :=
      lift_rule bitsM bitsM J1 (fun _ => rfl) (hev .L (m / 2))
    have hW := wrap_prependU_spec k (JO_run k) hSub
    exact spec_of_eq hW (by cases rec .L (m / 2) <;> rfl)
  · have hm2 : m % 2 = 1 := by omega
    simp only [hm2, Nat.beq]
    rw [bitsM_eq_of_eq m (by omega) (bitsM_bit1 (m / 2))]
    change Spec bitsM j (O ^ k +> (([1] : List (Fin 2)) +> bitsM (m / 2))) _
    have hSub : Spec bitsM j (([1] : List (Fin 2)) +>
        bitsM (m / 2)) (map_result id (rec .L (m / 2))) :=
      lift_rule bitsM bitsM J1 (fun _ => rfl) (hev .L (m / 2))
    have hW := wrap_prependU_spec k (JO_run k) hSub
    exact spec_of_eq hW (by cases rec .L (m / 2) <;> rfl)
  · have hm2 : m % 2 = 0 := by omega
    have hl2 : Nat.beq (Nat.land 2 2) 2 = true := rfl
    simp only [hm2, h2, Nat.beq, hl2]
    rw [bitsM_eq_of_eq m (by omega) (bitsM_01 (m / 4))]
    have hih := hev (.H 1) (m / 4)
    dsimp only [signalsM] at hih
    have hW := wrap_prependU_spec k (JO_run k) (lift_rule bitsM bitsM J01 bitsM_U hih)
    exact spec_of_eq hW (by cases rec (.H 1) (m / 4) <;> rfl)
  · have hm2 : m % 2 = 0 := by omega
    have hl0 : Nat.beq (Nat.land 0 2) 2 = false := rfl
    simp only [hm2, h0, Nat.beq, hl0]
    dsimp only [Spec]
    rw [bitsM_eq_of_eq m (by omega) (bitsM_00 (m / 4)), bitsM_prependU, bitsM_O]
    exact (JO_run k).sideRLs_concat (J00.sideRLs_concat (.nil (bitsM (m / 4))))

theorem evalJ_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec) (m0 : Nat) :
    Spec bitsM j (bitsM m0) (evalJ rec m0) := by
  unfold evalJ
  simp only [shr_3, land_7]
  cases hd5 : Nat.beq (m0 % 8) 5 with
  | false =>
    dsimp only
    simpa using evalJ_k_spec hev 0 m0
  | true =>
    dsimp only
    have hm := Nat.eq_of_beq_eq_true hd5
    have heq : bitsM m0 = O ^ 1 +> bitsM (m0 / 8) := by
      rw [bitsM_eq_of_eq m0 (by omega) (bitsM_O (m0 / 8))]; rfl
    rw [heq]
    exact sweepO_inv (fun r o => Spec bitsM j r o) (evalJ_k rec) (evalJ_k_spec hev) 64 1 (m0 / 8)

def unary (a : ℕ) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  U ^ a +> r

theorem T00N {X : Type} (den : X → ListBlank (Fin 2)) (a : ℕ) (r : ListBlank (Fin 2)) (o : Result X)
    (ha : 2 ≤ a) (hS : Spec den (h ^ (a - 1)) r o) :
    Spec (fun x => unary (a + 1) (den x)) j (unary a ([0, 0] +> r)) o := by
  unfold unary
  have ea : a = 2 + (a - 2) := by omega
  have eo : a + 1 = 3 + (a - 2) := by omega
  have eh : a - 1 = 1 + (a - 2) := by omega
  rw [eh] at hS
  have hT := T00 den (a - 2) r o hS
  rwa [← ea, ← eo] at hT

theorem T01N {X : Type} (den : X → ListBlank (Fin 2)) (a : ℕ) (r : ListBlank (Fin 2)) (o : Result X)
    (hS : Spec den (h ^ (a + 1)) r o) :
    Spec (fun x => unary (a + 1) (den x)) j (unary a ([0, 1] +> r)) o := by
  unfold unary
  have ha : a + 1 = 1 + a := by omega
  rw [ha] at hS ⊢
  rw [← append_assoc (U ^ a) [0, 1] r]
  exact rule_spec den (T01 a) hS

theorem map_spec {X Y : Type} (dx : X → ListBlank (Fin 2)) (dy : Y → ListBlank (Fin 2))
    {hs : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {r : ListBlank (Fin 2)} {o : Result X} {f : X → Y}
    (hE : ∀ x, dy (f x) = dx x) (hS : Spec dx hs r o) :
    Spec dy hs r (map_result f o) := by
  cases o with
  | failed => trivial
  | stopped => exact hS
  | returned x =>
    dsimp [Spec, map_result]
    rw [hE x]
    exact hS

theorem TO_pow {X : Type} (den : X → ListBlank (Fin 2)) (a ko : ℕ) (r : ListBlank (Fin 2))
    (o : Result X) (hS : Spec den j (U ^ a +> r) o) :
    Spec (fun x => U ^ ko +> den x) j (U ^ a +> (O ^ ko +> r)) o := by
  induction ko with
  | zero => exact hS
  | succ ko ih =>
    rw [pow_succ_list O ko, append_assoc]
    have hT := TO (fun x => U ^ ko +> den x) a (O ^ ko +> r) o ih
    have hf : (fun x => U +> (U ^ ko +> den x)) = (fun x => U ^ (ko + 1) +> den x) := by
      funext x
      rw [pow_succ_list U ko, append_assoc]
    rwa [hf] at hT

theorem evalL_u_p_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec) (kp ku ms : Nat) :
    SpecLP kp (ku + 1) (bitsM ms) (evalL_u_p rec kp ku ms) := by
  unfold evalL_u_p evalL_u_p_md0 evalL_u_p_md2 evalL_u_p_gen
  simp only [Nat.add_eq, shr_4, shl_6, land_7, land_15, retLU_eq, retLUH_eq]
  cases hd0 : Nat.beq (ms % 8) 0 with
  | true =>
    dsimp only
    have hm8 := Nat.eq_of_beq_eq_true hd0
    have hm16 : ms % 16 = 0 ∨ ms % 16 = 8 := by omega
    rcases hm16 with h0000 | h0001
    · simp only [h0000, Nat.beq]
      dsimp only [SpecLP]
      refine ⟨kp + 2, [0, 0, 0, 0], by omega, bitsM_eq_of_eq ms (by omega) (bitsM_0000 (ms / 16)),
          ?_⟩
      have hG : SegRLs tm g [] (P ^ kp ++ [0, 0, 0, 0]) (U ^ kp ++ (O ++ [0, 1])) := by
        have hc := (GP_run kp).concat G0000
        have hw : U ^ kp ++ [1, 0, 1, 0, 1] = U ^ kp ++ (O ++ [0, 1]) := rfl
        rwa [hw] at hc
      have hJ : SegRLs tm j (h ^ (1 + kp)) (U ^ kp ++ (O ++ [0, 1])) (U ++ U ^ (1 + kp)) :=
        TO_seg kp (T01 kp)
      have hTile := hG.trans hJ
      have hk1 : [] ++ h ^ (1 + kp) = h ^ (kp + 1) := by
        have hk : 1 + kp = kp + 1 := by omega
        rw [List.nil_append, hk]
      have hk2 : U ++ U ^ (1 + kp) = U ^ (kp + 2) := by
        have hk : kp + 2 = (1 + kp) + 1 := by omega
        rw [hk, pow_succ_list]
      rwa [hk1, hk2] at hTile
    · simp only [h0001, Nat.beq]
      dsimp only [SpecLP]
      refine ⟨kp + 2, [0, 0, 0, 1], by omega, bitsM_eq_of_eq ms (by omega) (bitsM_0001 (ms / 16)),
          ?_⟩
      have hG : SegRLs tm g h (P ^ kp ++ [0, 0, 0, 1]) (U ^ (kp + 1) ++ [0, 1]) := by
        have hc := (GP_run kp).concat G0001
        have hw : U ^ kp ++ [1, 0, 0, 0, 1] = U ^ (kp + 1) ++ [0, 1] := by
          rw [pow_succ_list' U kp, List.append_assoc]; rfl
        rwa [hw] at hc
      have hJ : SegRLs tm j (h ^ (1 + (kp + 1))) (U ^ (kp + 1) ++ [0, 1]) (U ^ (1 + (kp + 1))) :=
        T01 (kp + 1)
      have hTile := hG.trans hJ
      have hsig : h ++ h ^ (1 + (kp + 1)) = h ^ (kp + 3) := by
        have hk : kp + 3 = (1 + (kp + 1)) + 1 := by omega
        rw [hk, pow_succ_list]
      have hout : U ^ (1 + (kp + 1)) = U ^ (kp + 2) := by
        have hk : 1 + (kp + 1) = kp + 2 := by omega
        rw [hk]
      rwa [hsig, hout] at hTile
  | false =>
    dsimp only
    cases hd2 : Nat.beq (ms % 8) 2 with
    | true =>
      dsimp only
      have hm8 := Nat.eq_of_beq_eq_true hd2
      have hm16 : ms % 16 = 2 ∨ ms % 16 = 10 := by omega
      rcases hm16 with h0100 | h0101
      · simp only [h0100, Nat.beq]
        rcases kp with _ | kp'
        · simp only [Nat.beq]
          dsimp only [SpecLP, pow_zero_list, append_nil]
          rw [bitsM_eq_of_eq ms (by omega) (bitsM_0100 (ms / 16))]
          have hG0 : SideRLs tm g (([0, 1, 0, 0] : List (Fin 2)) +> bitsM (ms / 16))
              ((U ++ [0, 0]) +> bitsM (ms / 16)) := by
            have := G01.sideRLs_concat (.nil (([0, 0] : List (Fin 2)) +> bitsM (ms / 16)))
            rwa [append_assoc]
          have hJ0 : SideRLs tm j ((U ++ [0, 0]) +> bitsM (ms / 16))
              ((U ++ P) +> bitsM (ms / 16)) :=
            T00one.sideRLs_concat (.nil (bitsM (ms / 16)))
          refine ⟨0, by omega, ?_⟩
          dsimp only [pow_zero_list, append_nil]
          rw [bitsM_33_64]
          exact hG0.trans hJ0
        · have hkp0 : Nat.beq (kp' + 1) 0 = false := rfl
          simp only [hkp0]
          dsimp only [SpecLP]
          refine ⟨kp' + 3, [0, 1, 0, 0], by omega,
            bitsM_eq_of_eq ms (by omega) (bitsM_0100 (ms / 16)), ?_⟩
          have hG : SegRLs tm g [] ((P ^ (kp' + 1) ++ [0, 1]) ++ [0, 0]) (U ^ (2 + kp') ++ [0,
              0]) := by
            have h1 := ((GP_run (kp' + 1)).concat G01).concat (.nil [0, 0])
            have he : U ^ (kp' + 1) ++ U = U ^ (2 + kp') := by
              have hk : 2 + kp' = (kp' + 1) + 1 := by omega
              rw [hk, pow_succ_list' U (kp' + 1)]
            rwa [he] at h1
          have hin : (P ^ (kp' + 1) ++ [0, 1]) ++ [0, 0] = P ^ (kp' + 1) ++ [0, 1, 0, 0] := by
            rw [List.append_assoc]; rfl
          rw [hin] at hG
          have hTile := hG.trans (T00_seg kp')
          have hsig : [] ++ h ^ (1 + kp') = h ^ (kp' + 1) := by
            have hk : 1 + kp' = kp' + 1 := by omega
            rw [List.nil_append, hk]
          have hout : U ^ (3 + kp') = U ^ (kp' + 3) := by
            have hk : 3 + kp' = kp' + 3 := by omega
            rw [hk]
          rwa [hsig, hout] at hTile
      · simp only [h0101, Nat.beq]
        dsimp only [SpecLP]
        refine ⟨kp + 2, [0, 1, 0, 1], by omega,
          bitsM_eq_of_eq ms (by omega) (bitsM_0101 (ms / 16)), ?_⟩
        have hG : SegRLs tm g [] ((P ^ kp ++ [0, 1]) ++ [0, 1]) (U ^ (kp + 1) ++ [0, 1]) := by
          have h1 := ((GP_run kp).concat G01).concat (.nil [0, 1])
          rwa [← pow_succ_list' U kp] at h1
        have hin : (P ^ kp ++ [0, 1]) ++ [0, 1] = P ^ kp ++ [0, 1, 0, 1] := by
          rw [List.append_assoc]; rfl
        rw [hin] at hG
        have hTile := hG.trans (T01 (kp + 1))
        have hsig : [] ++ h ^ (1 + (kp + 1)) = h ^ (kp + 2) := by
          have hk : 1 + (kp + 1) = kp + 2 := by omega
          rw [List.nil_append, hk]
        have hout : U ^ (1 + (kp + 1)) = U ^ (kp + 2) := by
          have hk : 1 + (kp + 1) = kp + 2 := by omega
          rw [hk]
        rwa [hsig, hout] at hTile
    | false =>
      dsimp only
      have hG :=
          lift_rule bitsM bitsM (GP_run kp) (fun r => bitsM_prependU kp r) (evalG_spec hev ms)
      have hseq := bind_spec bitsM bitsM hG (fun x => evalJ_spec hev x)
      cases hg : evalG rec ms with
      | failed => trivial
      | stopped => rw [hg] at hseq; exact hseq
      | returned r =>
        rw [hg] at hseq
        dsimp only [then_result, map_result, mapRetL] at hseq ⊢
        cases hj : evalJ rec (prependU kp r) with
        | failed => trivial
        | stopped => rw [hj] at hseq; exact hseq
        | returned r2 =>
          rw [hj] at hseq
          dsimp only [SpecLP, Spec] at hseq ⊢
          exact ⟨0, by omega, hseq⟩

theorem evalL_u_k_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec) (ku0 m : Nat) :
    SpecL e (W6 ^ ku0 +> bitsM m) (evalL_u_k rec ku0 m) := by
  unfold evalL_u_k evalL_u_k_non4
  simp only [Nat.add_eq, shr_2, shr_3, shr_4, shl_6, land_3, land_7, land_15,
             retLU_eq, retLUH_eq, callH_eq]
  cases hd4 : Nat.beq (m % 8) 4 with
  | true =>
    dsimp only
    have hm8 := Nat.eq_of_beq_eq_true hd4
    rw [bitsM_eq_of_eq m (by omega) (bitsM_P (m / 8))]
    exact specLP_to_specL (sweepLP_spec (evalL_u_p rec) (evalL_u_p_spec hev) 64 0 ku0 (m / 8))
  | false =>
    dsimp only
    have hb01 : m % 4 = 3 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 0 := by omega
    rcases hb01 with h3 | h1 | h2 | h0
    · simp only [h3, Nat.beq]
      dsimp only [SpecL]
      rw [bitsM_eq_of_eq m (by omega) (bitsM_11 (m / 4))]
      exact (L011_run ku0).sideRLsHalt_concat
        (.here (E, [0, 0, 0]) (C, [1]) [] ([1, 1] +> bitsM (m / 4)) (fun l =>
            L11 l (bitsM (m / 4))))
    · simp only [h1, Nat.beq]
      rw [bitsM_eq_of_eq m (by omega) (bitsM_10 (m / 4))]
      have h1s := hev (.H 1) (m / 4)
      dsimp only [signalsM] at h1s
      have hseq := bind_spec bitsM bitsM h1s (fun r => evalJ_spec hev r)
      cases hh : rec (.H 1) (m / 4) with
      | failed => trivial
      | stopped =>
        rw [hh] at hseq
        exact (L011_run ku0).sideRLsHalt_concat (L10.sideRLsHalt_concat hseq)
      | returned r =>
        rw [hh] at hseq
        dsimp only [then_result, mapRetL] at hseq ⊢
        cases hj : evalJ rec r with
        | failed => trivial
        | stopped =>
          rw [hj] at hseq
          exact (L011_run ku0).sideRLsHalt_concat (L10.sideRLsHalt_concat hseq)
        | returned r2 =>
          rw [hj] at hseq
          dsimp only [SpecL, Spec] at hseq ⊢
          rw [pow_add_list, pow_one_list, append_assoc]
          exact (L011_run ku0).sideRLs_concat (L10.sideRLs_concat hseq)
    · simp only [h2, Nat.beq]
      cases hm16_2 : Nat.beq (m % 16) 2 with
      | true =>
        dsimp only [SpecL]
        have hm2 := Nat.eq_of_beq_eq_true hm16_2
        rw [bitsM_eq_of_eq m (by omega) (bitsM_0100 (m / 16)), bitsM_41_64]
        exact (L011_run ku0).sideRLs_concat (L0100.sideRLs_concat (.nil (bitsM (m / 16))))
      | false =>
        dsimp only
        rw [bitsM_eq_of_eq m (by omega) (bitsM_01 (m / 4))]
        have hjs := evalJ_spec hev (m / 4)
        cases hj : evalJ rec (m / 4) with
        | failed => trivial
        | stopped =>
          rw [hj] at hjs
          exact (L011_run ku0).sideRLsHalt_concat (L01.sideRLsHalt_concat hjs)
        | returned r2 =>
          rw [hj] at hjs
          dsimp only [mapRetL, SpecL, Spec] at hjs ⊢
          rw [pow_add_list, pow_one_list, append_assoc]
          exact (L011_run ku0).sideRLs_concat (L01.sideRLs_concat hjs)
    · simp only [h0, Nat.beq]
      have hm8_0 : m % 8 = 0 := by
        rcases (by omega : m % 8 = 0 ∨ m % 8 = 4) with h_0 | h_4
        · exact h_0
        · rw [h_4] at hd4; cases hd4
      have hm16 : m % 16 = 8 ∨ m % 16 = 0 := by omega
      rcases hm16 with h0001 | h0000
      · simp only [h0001, Nat.beq]
        dsimp only [SpecL]
        refine ⟨W6 ^ ku0 ++ [0, 0, 0, 1], ?_, ?_⟩
        · rw [bitsM_eq_of_eq m (by omega) (bitsM_0001 (m / 16)), ← append_assoc]
        · have hc := (L011_run ku0).concat L0001
          have hout : U ^ ku0 ++ (U ++ U) = U ^ (ku0 + 2) := by
            rw [pow_add_list]; rfl
          rwa [hout] at hc
      · simp only [h0000, Nat.beq]
        dsimp only [SpecL]
        rw [bitsM_eq_of_eq m (by omega) (bitsM_0000 (m / 16)), bitsM_33_64]
        exact (L011_run ku0).sideRLs_concat (L0000.sideRLs_concat (.nil (bitsM (m / 16))))

theorem evalL_u_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec) (m0 : Nat) :
    SpecL e (bitsM m0) (evalL_u rec m0) := by
  unfold evalL_u
  simp only [shr_3, land_7]
  cases hd6 : Nat.beq (m0 % 8) 6 with
  | false =>
    dsimp only
    simpa using evalL_u_k_spec hev 0 m0
  | true =>
    dsimp only
    have hm := Nat.eq_of_beq_eq_true hd6
    have heq : bitsM m0 = W6 ^ 1 +> bitsM (m0 / 8) := by
      rw [bitsM_eq_of_eq m0 (by omega) (bitsM_W6 (m0 / 8))]; rfl
    rw [heq]
    exact sweep6_inv (fun r o => SpecL e r o) (evalL_u_k rec) (evalL_u_k_spec hev) 64 1 (m0 / 8)

theorem evalL_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec) (m0 : Nat) :
    Spec bitsM e (bitsM m0) (evalL rec m0) := by
  unfold evalL
  have hLu := evalL_u_spec hev m0
  cases hres : evalL_u rec m0 with
  | failed => trivial
  | stopped => rw [hres] at hLu; exact hLu
  | retU k x =>
    rw [hres] at hLu
    dsimp only [retM_eq, Spec]
    rw [bitsM_prependU]
    exact hLu
  | retUH k c z =>
    rw [hres] at hLu
    obtain ⟨w, hbm, hseg⟩ := hLu
    dsimp only [retM_eq, callH_eq]
    rw [hbm]
    cases hc0 : Nat.beq c 0 with
    | true =>
      dsimp only [Spec]
      rw [Nat.eq_of_beq_eq_true hc0] at hseg
      rw [bitsM_prependU]
      exact hseg.sideRLs_concat (.nil (bitsM z))
    | false =>
      dsimp only
      have hL := lift_rule bitsM bitsM hseg (fun r => bitsM_prependU k r) (hev (.H c) z)
      exact spec_of_eq hL (by cases rec (.H c) z <;> rfl)

/-! ## Soundness of `finishUH`, `evalHL`, `evalH`, `evalT`, `tcallT`, `roundT`, `runT` -/

theorem finishUH_u_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec)
    (k n z : Nat) :
    Spec bitsM (h ^ n) (U ^ k +> bitsM z) (finishUH rec k 0 n z) := by
  unfold finishUH
  simp only [Nat.add_eq, Nat.zero_add, retM_eq, callH_eq]
  obtain ⟨v, hSeg, hb⟩ := digitsK_spec k n
  cases hc : Nat.beq (carryK k n) 0 with
  | true =>
    dsimp only [Spec]
    rw [Nat.eq_of_beq_eq_true hc] at hSeg
    rw [hb z]
    exact hSeg.sideRLs_concat (.nil (bitsM z))
  | false =>
    dsimp only
    have hL := lift_rule bitsM bitsM hSeg hb (hev (.H (carryK k n)) z)
    exact spec_of_eq hL (by cases rec (.H (carryK k n)) z <;> rfl)

theorem finishUH_uh_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec)
    {w : List (Fin 2)} (k c n z : Nat)
    (hSegE : SegRLs tm e (h ^ c) w (U ^ k)) :
    Spec bitsM (e ++ h ^ n) (w +> bitsM z) (finishUH rec k c n z) := by
  unfold finishUH
  simp only [Nat.add_eq, retM_eq, callH_eq]
  obtain ⟨v, hSegD, hb⟩ := digitsK_spec k n
  have hTot : SegRLs tm (e ++ h ^ n) (h ^ (c + carryK k n)) w v := by
    rw [pow_add_list]
    exact hSegE.trans hSegD
  cases hc : Nat.beq (c + carryK k n) 0 with
  | true =>
    dsimp only [Spec]
    rw [Nat.eq_of_beq_eq_true hc] at hTot
    rw [hb z]
    exact hTot.sideRLs_concat (.nil (bitsM z))
  | false =>
    dsimp only
    have hL := lift_rule bitsM bitsM hTot hb (hev (.H (c + carryK k n)) z)
    exact spec_of_eq hL (by cases rec (.H (c + carryK k n)) z <;> rfl)

theorem evalHL_fast2_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec)
    {w : List (Fin 2)} (base n z2 : Nat) (hbase : base < 16)
    (hL0 : SegRLs tm e [] w (digits2 base)) :
    Spec bitsM (e ++ h ^ n) (w +> bitsM z2) (evalHL_fast2 rec base n z2) := by
  unfold evalHL_fast2
  simp only [Nat.add_eq, shr_4, shl_6, land_15, retM_eq, callH_eq]
  have hRule : SegRLs tm (e ++ h ^ n) (h ^ ((base + n) / 16)) w (digits2 ((base + n) % 16)) :=
    hL0.trans (digits2_count base n hbase)
  cases hqn2 : Nat.beq ((base + n) / 16) 0 with
  | true =>
    dsimp only [Spec]
    rw [Nat.eq_of_beq_eq_true hqn2] at hRule
    rw [bitsM_enc2 ((base + n) % 16) z2 (by omega)]
    exact hRule.sideRLs_concat (.nil (bitsM z2))
  | false =>
    dsimp only
    have hL := lift_rule bitsM bitsM hRule
      (fun r2 => bitsM_enc2 ((base + n) % 16) r2 (by omega))
      (hev (.H ((base + n) / 16)) z2)
    exact spec_of_eq hL (by cases rec (.H ((base + n) / 16)) z2 <;> rfl)

theorem evalHL_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec) (n y : Nat) :
    Spec bitsM (e ++ h ^ n) (bitsM y) (evalHL rec n y) := by
  unfold evalHL evalHL_gen
  simp only [shr_4, land_15]
  cases hd2 : Nat.beq (y % 16) 2 with
  | true =>
    dsimp only
    have hy2 := Nat.eq_of_beq_eq_true hd2
    rw [bitsM_eq_of_eq y (by omega) (bitsM_0100 (y / 16))]
    exact evalHL_fast2_spec hev 8 n (y / 16) (by decide) L0100
  | false =>
    dsimp only
    cases hd0 : Nat.beq (y % 16) 0 with
    | true =>
      dsimp only
      have hy0 := Nat.eq_of_beq_eq_true hd0
      rw [bitsM_eq_of_eq y (by omega) (bitsM_0000 (y / 16))]
      exact evalHL_fast2_spec hev 12 n (y / 16) (by decide) L0000
    | false =>
      dsimp only
      have hLu := evalL_u_spec hev y
      cases hres : evalL_u rec y with
      | failed => trivial
      | stopped => rw [hres] at hLu; exact SideRLsHalt.app_left hLu
      | retU k x =>
        rw [hres] at hLu
        exact after_spec bitsM hLu (finishUH_u_spec hev k n x)
      | retUH k c z =>
        rw [hres] at hLu
        obtain ⟨w, hbm, hSegE⟩ := hLu
        rw [hbm]
        exact finishUH_uh_spec hev k c n z hSegE

private theorem land_div8_2_fin : ∀ x : Fin 64,
    Nat.land x.val 2 = 0 → Nat.beq (Nat.land x.val 18) 0 = false →
    Nat.beq (Nat.land (x.val / 8) 2) 0 = false := by
  decide +kernel

private theorem land_div8_2_ne0 (m0 : Nat)
    (hm2 : Nat.land m0 2 = 0) (hm18 : Nat.beq (Nat.land m0 18) 0 = false) :
    Nat.beq (Nat.land (m0 / 8) 2) 0 = false := by
  have h1 : Nat.land (m0 % 64) 2 = 0 := by
    rw [land_2] at hm2 ⊢
    have e : (m0 % 64) % 4 = m0 % 4 := by omega
    rwa [e]
  have h2 : Nat.beq (Nat.land (m0 % 64) 18) 0 = false := by
    rwa [← land_18]
  have hf := land_div8_2_fin ⟨m0 % 64, by omega⟩ h1 h2
  dsimp only at hf
  rw [land_2] at hf ⊢
  have e2 : ((m0 % 64) / 8) % 4 = (m0 / 8) % 4 := by omega
  rwa [← e2]

theorem evalH_inv_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec)
    (n m0 : Nat) (hn : 1 ≤ n) (hm2 : Nat.beq (Nat.land m0 2) 0 = false) :
    Spec bitsM (h ^ n) (bitsM m0) (evalH_inv rec n m0) := by
  rcases n with _ | n0
  · omega
  unfold evalH_inv
  simp only [Nat.add_eq, Nat.sub_eq, shr_2, shl_2, land_1, retM_eq]
  have h_b1 : m0 % 4 = 2 ∨ m0 % 4 = 3 := by
    rw [land_2] at hm2
    rcases (by omega : m0 % 4 = 0 ∨ m0 % 4 = 1 ∨ m0 % 4 = 2 ∨ m0 % 4 = 3) with h0 | h1 | h2 | h3
    · rw [h0] at hm2; cases hm2
    · rw [h1] at hm2; cases hm2
    · exact Or.inl h2
    · exact Or.inr h3
  rcases h_b1 with h01 | h11
  · have hm0_1 : m0 % 2 = 0 := by omega
    simp only [hm0_1, Nat.beq, Nat.add_sub_cancel]
    rw [bitsM_eq_of_eq m0 (by omega) (bitsM_01 (m0 / 4)), pow_succ_list h n0]
    exact rule_spec bitsM (H01rest n0) (evalHL_spec hev n0 (m0 / 4))
  · have hm0_1 : m0 % 2 = 1 := by omega
    simp only [hm0_1, Nat.beq]
    rcases n0 with _ | n1
    · simp only [Nat.beq]
      dsimp only [Spec]
      have hb_in : bitsM m0 = ([1] : List (Fin 2)) +> (([1] : List (Fin 2)) +> bitsM (m0 / 4)) := by
        rw [bitsM_eq_of_eq m0 (by omega) (bitsM_11 (m0 / 4))]; rfl
      rw [hb_in, bitsM_01 (m0 / 4)]
      exact H1.sideRLs_concat (.nil (([1] : List (Fin 2)) +> bitsM (m0 / 4)))
    · have hsub2 : n1 + 1 + 1 - 2 = n1 := by omega
      simp only [hsub2]
      have hb_in : bitsM m0 = ([1] : List (Fin 2)) +> (([1] : List (Fin 2)) +> bitsM (m0 / 4)) := by
        rw [bitsM_eq_of_eq m0 (by omega) (bitsM_11 (m0 / 4))]; rfl
      have hH1 : SideRLs tm h (bitsM m0) (([0, 1] : List (Fin 2)) +> bitsM (m0 / 4)) := by
        rw [hb_in]
        exact H1.sideRLs_concat (.nil (([1] : List (Fin 2)) +> bitsM (m0 / 4)))
      have hR' : Spec bitsM (h ^ (n1 + 1)) (([0, 1] : List (Fin 2)) +> bitsM (m0 / 4))
          (evalHL rec n1 (m0 / 4)) := by
        rw [pow_succ_list h n1]
        exact rule_spec bitsM (H01rest n1) (evalHL_spec hev n1 (m0 / 4))
      rw [pow_succ_list h (n1 + 1)]
      exact after_spec bitsM hH1 hR'

theorem evalH_spec {rec : ModeM → Nat → Result Nat} (hev : EvalSpec rec) (n m0 : Nat) :
    Spec bitsM (h ^ n) (bitsM m0) (evalH rec n m0) := by
  unfold evalH evalH_valid evalH_wide evalH_w1 evalH_w2 evalH_w4 evalH_w12
  simp only [Nat.add_eq,
             shr_2, shr_3, shr_4, shr_6, shr_8, shr_12, shr_24, shr_36,
             shl_3, shl_6, shl_12, shl_36,
             land_3, land_7, land_15, land_63, land_255, land_4095, land_16777215,
             retM_eq, callH_eq]
  rcases n with _ | n0
  · exact .nil (bitsM m0)
  · have hne0 : Nat.beq (n0 + 1) 0 = false := rfl
    simp only [hne0]
    cases hm2 : Nat.beq (Nat.land m0 2) 0 with
    | false =>
      dsimp only
      exact evalH_inv_spec hev (n0 + 1) m0 (by omega) hm2
    | true =>
      dsimp only
      have hm2_eq := Nat.eq_of_beq_eq_true hm2
      have hm2_0 : Nat.land (m0 % 8) 2 = 0 := by
        rwa [← land_2_8]
      obtain ⟨hp_lt, henc_d3⟩ := dec1_lt4 (m0 % 8) (by omega) hm2_0
      have hb_m0 : bitsM m0 = digit (dec1 (m0 % 8)) +> bitsM (m0 / 8) :=
        bitsM_eq_of_eq m0 (by omega) (bitsM_enc1 (dec1 (m0 % 8)) (m0 / 8) hp_lt)
      set p := dec1 (m0 % 8)
      set n := n0 + 1
      cases hs3 : Nat.ble (p + n) 3 with
      | true =>
        dsimp only [Spec]
        have hle := Nat.ble_eq.mp hs3
        have hq0 : (p + n) / 4 = 0 := by omega
        have hrem : (p + n) % 4 = p + n := by omega
        have hdc := digit_count p n hp_lt
        rw [hq0, hrem] at hdc
        rw [hb_m0, bitsM_enc1 (p + n) (m0 / 8) (by omega)]
        exact hdc.sideRLs_concat (.nil (bitsM (m0 / 8)))
      | false =>
        dsimp only
        have hs4 : 4 ≤ p + n := by
          rcases (by omega : p + n ≤ 3 ∨ 4 ≤ p + n) with hle | hge
          · rw [Nat.ble_eq.mpr hle] at hs3; cases hs3
          · exact hge
        cases h2 : Nat.beq (Nat.land m0 18) 0 with
        | false =>
          dsimp only
          rw [hb_m0]
          have hinv := evalH_inv_spec hev ((p + n) / 4) (m0 / 8) (by omega)
            (land_div8_2_ne0 m0 hm2_eq h2)
          have hL := lift_rule bitsM bitsM (digit_count p n hp_lt)
            (fun r2 => bitsM_enc1 ((p + n) % 4) r2 (by omega))
            hinv
          exact spec_of_eq hL (by cases evalH_inv rec ((p + n) / 4) (m0 / 8) <;> rfl)
        | true =>
          dsimp only
          cases h4 : Nat.beq (Nat.land m0 1170) 0 with
          | false =>
            dsimp only
            obtain ⟨hv2, hb2⟩ := bitsM_dec2 m0 (Nat.eq_of_beq_eq_true h2)
            set v2 := dec2 (m0 % 64)
            rw [hb2]
            have hdc2 := digits2_count v2 n hv2
            cases hqn2 : Nat.beq ((v2 + n) / 16) 0 with
            | true =>
              dsimp only [Spec]
              rw [Nat.eq_of_beq_eq_true hqn2] at hdc2
              rw [bitsM_enc2 ((v2 + n) % 16) (m0 / 64) (by omega)]
              exact hdc2.sideRLs_concat (.nil (bitsM (m0 / 64)))
            | false =>
              dsimp only
              have hqn2_pos : 1 ≤ (v2 + n) / 16 := by
                rcases hq : (v2 + n) / 16 with _ | q'
                · rw [hq] at hqn2; cases hqn2
                · omega
              cases hz2 : Nat.beq (Nat.land (m0 / 64) 2) 0 with
              | true =>
                dsimp only
                have hL := lift_rule bitsM bitsM hdc2
                  (fun r2 => bitsM_enc2 ((v2 + n) % 16) r2 (by omega))
                  (hev (.H ((v2 + n) / 16)) (m0 / 64))
                exact spec_of_eq hL (by cases rec (.H ((v2 + n) / 16)) (m0 / 64) <;> rfl)
              | false =>
                dsimp only
                have hinv := evalH_inv_spec hev ((v2 + n) / 16) (m0 / 64) hqn2_pos hz2
                have hL := lift_rule bitsM bitsM hdc2
                  (fun r2 => bitsM_enc2 ((v2 + n) % 16) r2 (by omega))
                  hinv
                exact spec_of_eq hL (by cases evalH_inv rec ((v2 + n) / 16) (m0 / 64) <;> rfl)
          | true =>
            dsimp only
            cases h12 : Bool.rec (motive := fun _ => Bool) false (ok12_hi m0) (Nat.ble 256 n) with
            | true =>
              dsimp only
              have hok : ok12_hi m0 = true := by
                cases hble : Nat.ble 256 n with
                | false => rw [hble] at h12; cases h12
                | true => rw [hble] at h12; exact h12
              obtain ⟨hv12, hb12⟩ := bitsM_dec12 m0 (Nat.eq_of_beq_eq_true h4) hok
              set v12 := dec12_3x4 (Nat.land m0 68719476735)
              rw [hb12]
              have hdc12 := digits12_count v12 n hv12
              cases hqn12 : Nat.beq ((v12 + n) / 16777216) 0 with
              | true =>
                dsimp only [Spec]
                rw [Nat.eq_of_beq_eq_true hqn12] at hdc12
                rw [bitsM_enc12 ((v12 + n) % 16777216) (m0 / 68719476736) (by omega)]
                exact hdc12.sideRLs_concat (.nil (bitsM (m0 / 68719476736)))
              | false =>
                dsimp only
                have hL := lift_rule bitsM bitsM hdc12
                  (fun r2 => bitsM_enc12 ((v12 + n) % 16777216) r2 (by omega))
                  (hev (.H ((v12 + n) / 16777216)) (m0 / 68719476736))
                exact spec_of_eq hL (by cases rec (.H ((v12 + n) / 16777216)) (m0 / 68719476736) <;>
                    rfl)
            | false =>
              dsimp only
              obtain ⟨hv4, hb4⟩ := bitsM_dec4 m0 (Nat.eq_of_beq_eq_true h4)
              set v4 := dec4 (m0 % 4096)
              rw [hb4]
              have hdc4 := digits4_count v4 n hv4
              cases hqn4 : Nat.beq ((v4 + n) / 256) 0 with
              | true =>
                dsimp only [Spec]
                rw [Nat.eq_of_beq_eq_true hqn4] at hdc4
                rw [bitsM_enc4 ((v4 + n) % 256) (m0 / 4096) (by omega)]
                exact hdc4.sideRLs_concat (.nil (bitsM (m0 / 4096)))
              | false =>
                dsimp only
                have hL := lift_rule bitsM bitsM hdc4
                  (fun r2 => bitsM_enc4 ((v4 + n) % 256) r2 (by omega))
                  (hev (.H ((v4 + n) / 256)) (m0 / 4096))
                exact spec_of_eq hL (by cases rec (.H ((v4 + n) / 256)) (m0 / 4096) <;> rfl)

theorem evalT_spec (fuel : Nat) : EvalSpec (evalT fuel) := by
  induction fuel with
  | zero => intro _ _; trivial
  | succ fuel ih =>
    intro mode m0
    cases mode with
    | G => exact evalG_spec ih m0
    | L => exact evalL_spec ih m0
    | H n => exact evalH_spec ih n m0

def pairM_side (x : Nat × Nat) : ListBlank (Fin 2) :=
  unary x.1 (bitsM x.2)

theorem add_unaryM_spec (b : Nat) (x : Nat × Nat) :
    pairM_side (b + x.1, x.2) = unary b (pairM_side x) := by
  unfold pairM_side unary
  dsimp only
  rw [pow_add_list, append_assoc]

def toResultP : ResP → Result (Nat × Nat)
  | .failed => .failed
  | .stopped => .stopped
  | .ret a m => .returned (a, m)

theorem collectM_inv {α : Type} (P_ok : ListBlank (Fin 2) → α → Prop)
    (cont : Nat → Nat → α)
    (hcont : ∀ acc m, P_ok (unary acc (bitsM m)) (cont acc m))
    (fuel acc m : Nat) :
    P_ok (unary acc (bitsM m)) (collectM fuel cont acc m) := by
  induction fuel generalizing acc m with
  | zero => exact hcont acc m
  | succ fuel ih =>
    change P_ok (unary acc (bitsM m)) (collectM_step cont (collectM fuel cont) acc m)
    unfold collectM_step collectM_hit
    simp only [Nat.add_eq, shr_eq, land_7, land_4095, land_281474976710655]
    cases hd1 : Nat.beq (m % 8) 1 with
    | false => exact hcont acc m
    | true =>
      dsimp only
      have hm1 := Nat.eq_of_beq_eq_true hd1
      cases hd16 : Nat.beq (m % 281474976710656) 40210710958665 with
      | true =>
        dsimp only
        have hm16 := Nat.eq_of_beq_eq_true hd16
        have heq : unary acc (bitsM m) = unary (acc + 16) (bitsM (m / 281474976710656)) := by
          unfold unary
          rw [bitsM_eq_of_eq m (by omega) (bitsM_U16 (m / 281474976710656)), ← append_assoc,
              ← pow_add_list]
        rw [heq]
        exact ih (acc + 16) (m / 281474976710656)
      | false =>
        dsimp only
        cases hd4 : Nat.beq (m % 4096) 585 with
        | true =>
          dsimp only
          have hm4 := Nat.eq_of_beq_eq_true hd4
          have heq : unary acc (bitsM m) = unary (acc + 4) (bitsM (m / 4096)) := by
            unfold unary
            rw [bitsM_eq_of_eq m (by omega) (bitsM_U4 (m / 4096)), ← append_assoc, ← pow_add_list]
          rw [heq]
          exact ih (acc + 4) (m / 4096)
        | false =>
          dsimp only
          have heq : unary acc (bitsM m) = unary (acc + 1) (bitsM (m / 8)) := by
            unfold unary
            rw [bitsM_eq_of_eq m (by omega) (bitsM_U (m / 8)), ← append_assoc, ← pow_succ_list']
          rw [heq]
          exact ih (acc + 1) (m / 8)

def TCallSpec (rec : Nat → Nat → ResP) : Prop :=
  ∀ a m, Spec pairM_side j (unary a (bitsM m)) (toResultP (rec a m))

theorem tcallT_k_spec {ev : ModeM → Nat → Result Nat} {rec : Nat → Nat → ResP}
    (hev : EvalSpec ev) (hrec : TCallSpec rec) (a ko m1 : Nat) :
    Spec pairM_side j (unary a (O ^ ko +> bitsM m1)) (toResultP (tcallT_k ev rec a ko m1)) := by
  unfold tcallT_k tcallT_even tcallT_odd
  simp only [Nat.add_eq, Nat.sub_eq, shr_2, shr_3, shl_3, land_1, land_3, land_7, retP_eq]
  have hcase : m1 % 4 = 0 ∨ m1 % 4 = 2 ∨ m1 % 8 = 1 ∨ m1 % 8 = 5 ∨ m1 % 8 = 3 ∨ m1 % 8 = 7 := by
    omega
  rcases hcase with h00 | h01 | h100 | h101 | h110 | h111
  · have hm2 : m1 % 2 = 0 := by omega
    simp only [hm2, h00, Nat.beq]
    rw [bitsM_eq_of_eq m1 (by omega) (bitsM_00 (m1 / 4))]
    rcases a with _ | _ | a2
    · simp only [Nat.beq]
      have h0 : Spec pairM_side j (U ^ 0 +> (([0, 0] : List (Fin 2)) +> bitsM (m1 / 4)))
          (.returned (0, 5 + 8 * (m1 / 4))) := by
        dsimp [Spec, pairM_side, unary]
        rw [bitsM_O]
        exact T00zero.sideRLs_concat (.nil (bitsM (m1 / 4)))
      have hT := TO_pow pairM_side 0 ko _ _ h0
      exact map_spec (f := fun p => (ko + p.1, p.2))
        (fun p => U ^ ko +> pairM_side p) pairM_side (fun p => add_unaryM_spec ko p) hT
    · simp only [Nat.beq]
      have h0 : Spec pairM_side j (U ^ 1 +> (([0, 0] : List (Fin 2)) +> bitsM (m1 / 4)))
          (.returned (1, 4 + 8 * (m1 / 4))) := by
        dsimp [Spec, pairM_side, unary]
        rw [bitsM_P]
        simpa [append_assoc] using T00one.sideRLs_concat (.nil (bitsM (m1 / 4)))
      have hT := TO_pow pairM_side 1 ko _ _ h0
      exact map_spec (f := fun p => (ko + p.1, p.2))
        (fun p => U ^ ko +> pairM_side p) pairM_side (fun p => add_unaryM_spec ko p) hT
    · have ha0 : Nat.beq (a2 + 2) 0 = false := rfl
      have ha1 : Nat.beq (a2 + 2) 1 = false := rfl
      simp only [ha0, ha1]
      have hevH := evalH_spec hev (a2 + 2 - 1) (m1 / 4)
      have hT0 := T00N bitsM (a2 + 2) (bitsM (m1 / 4)) _ (by omega) hevH
      have hM0 := map_spec (f := fun s => (a2 + 2 + 1, s))
        (fun s => unary (a2 + 2 + 1) (bitsM s)) pairM_side (fun _ => rfl) hT0
      have hT := TO_pow pairM_side (a2 + 2) ko _ _ hM0
      have hM := map_spec (f := fun p => (ko + p.1, p.2))
        (fun p => U ^ ko +> pairM_side p) pairM_side (fun p => add_unaryM_spec ko p) hT
      exact spec_of_eq hM (by cases evalH ev (a2 + 2 - 1) (m1 / 4) <;> rfl)
  · have hm2 : m1 % 2 = 0 := by omega
    simp only [hm2, h01, Nat.beq]
    rw [bitsM_eq_of_eq m1 (by omega) (bitsM_01 (m1 / 4))]
    have hevH := evalH_spec hev (a + 1) (m1 / 4)
    have hT0 := T01N bitsM a (bitsM (m1 / 4)) _ hevH
    have hM0 := map_spec (f := fun s => (a + 1, s))
      (fun s => unary (a + 1) (bitsM s)) pairM_side (fun _ => rfl) hT0
    have hT := TO_pow pairM_side a ko _ _ hM0
    have hM := map_spec (f := fun p => (ko + p.1, p.2))
      (fun p => U ^ ko +> pairM_side p) pairM_side (fun p => add_unaryM_spec ko p) hT
    exact spec_of_eq hM (by cases evalH ev (a + 1) (m1 / 4) <;> rfl)
  · have hm2 : m1 % 2 = 1 := by omega
    simp only [hm2, h100, Nat.beq]
    have hb : bitsM m1 = unary 1 (bitsM (m1 / 8)) := by
      rw [bitsM_eq_of_eq m1 (by omega) (bitsM_U (m1 / 8))]; rfl
    rw [hb]
    exact collectM_inv
      (fun sub o => Spec pairM_side j (unary a (O ^ ko +> sub)) (toResultP o))
      (fun ku zm => mapRetP (rec (a + ku) zm) (fun pa pm => .ret (ko + pa) pm))
      (fun ku zm => by
        have hu : U ^ (a + ku) +> bitsM zm = U ^ a +> unary ku (bitsM zm) := by
          unfold unary; rw [pow_add_list, append_assoc]
        have h0 : Spec pairM_side j (U ^ a +> unary ku (bitsM zm)) (toResultP (rec (a + ku) zm)) :=
            by
          rw [← hu]; exact hrec (a + ku) zm
        have hT := TO_pow pairM_side a ko _ _ h0
        have hM := map_spec (f := fun p => (ko + p.1, p.2))
          (fun p => U ^ ko +> pairM_side p) pairM_side (fun p => add_unaryM_spec ko p) hT
        exact spec_of_eq hM (by cases rec (a + ku) zm <;> rfl))
      64 1 (m1 / 8)
  · have hm2 : m1 % 2 = 1 := by omega
    simp only [hm2, h101, Nat.beq]
    rw [bitsM_eq_of_eq m1 (by omega) (bitsM_O (m1 / 8))]
    have hSub := TO pairM_side a (bitsM (m1 / 8)) _ (hrec a (m1 / 8))
    have hT := TO_pow (fun p => U +> pairM_side p) a ko _ _ hSub
    have hM := map_spec (f := fun p => ((ko + 1) + p.1, p.2))
      (fun p => U ^ ko +> (U +> pairM_side p)) pairM_side
      (fun p => by
        unfold pairM_side unary
        dsimp only
        rw [pow_add_list, pow_succ_list', append_assoc, append_assoc])
      hT
    exact spec_of_eq hM (by cases rec a (m1 / 8) <;> rfl)
  · have hm2 : m1 % 2 = 1 := by omega
    simp only [hm2, h110, Nat.beq]
    rw [bitsM_eq_of_eq m1 (by omega) (bitsM_110 (m1 / 8))]
    have hevH := evalH_spec hev 1 (m1 / 8)
    cases h_res : evalH ev 1 (m1 / 8) with
    | failed => trivial
    | stopped =>
      rw [h_res] at hevH
      exact TO_pow pairM_side a ko _ (.stopped : Result (Nat × Nat))
        (T110_halt a (bitsM (m1 / 8)) hevH)
    | returned r =>
      rw [h_res] at hevH
      dsimp only [evalToP]
      have hSub := T110_return pairM_side a (bitsM (m1 / 8)) (bitsM r) _ hevH (hrec a r)
      have hT := TO_pow (fun p => U +> pairM_side p) a ko _ _ hSub
      have hM := map_spec (f := fun p => ((ko + 1) + p.1, p.2))
        (fun p => U ^ ko +> (U +> pairM_side p)) pairM_side
        (fun p => by
          unfold pairM_side unary
          dsimp only
          rw [pow_add_list, pow_succ_list', append_assoc, append_assoc])
        hT
      exact spec_of_eq hM (by cases rec a r <;> rfl)
  · have hm2 : m1 % 2 = 1 := by omega
    simp only [hm2, h111, Nat.beq]
    rw [bitsM_eq_of_eq m1 (by omega) (bitsM_111 (m1 / 8))]
    exact TO_pow pairM_side a ko _ (.stopped : Result (Nat × Nat)) (T111 a (bitsM (m1 / 8)))

theorem tcallT_step_spec {ev : ModeM → Nat → Result Nat} {rec : Nat → Nat → ResP}
    (hev : EvalSpec ev) (hrec : TCallSpec rec) : TCallSpec (tcallT_step ev rec) := by
  intro a m
  unfold tcallT_step
  simp only [shr_3, land_7]
  cases hd5 : Nat.beq (m % 8) 5 with
  | false =>
    dsimp only
    simpa using tcallT_k_spec hev hrec a 0 m
  | true =>
    dsimp only
    have hm := Nat.eq_of_beq_eq_true hd5
    have heq : bitsM m = O ^ 1 +> bitsM (m / 8) := by
      rw [bitsM_eq_of_eq m (by omega) (bitsM_O (m / 8))]; rfl
    rw [heq]
    exact sweepO_inv (fun r o => Spec pairM_side j (unary a r) (toResultP o))
      (tcallT_k ev rec a) (tcallT_k_spec hev hrec a) 64 1 (m / 8)

theorem tcallT_spec {ev : ModeM → Nat → Result Nat} (hev : EvalSpec ev) (fuel : Nat) :
    TCallSpec (tcallT fuel ev) := by
  induction fuel with
  | zero => intro _ _; trivial
  | succ fuel ih => exact tcallT_step_spec hev ih

private theorem collect_tail_side {hs : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {r : ListBlank (Fin 2)} (pa pm : Nat)
    (hSide : SideRLs tm hs r (U +> unary pa (bitsM pm))) :
    Spec pairM_side hs r (toResultP (Bool.rec (retP (1 + pa) pm)
      (collectM 64 (roundT_col1 pa) 1 (pm / 8)) (Nat.beq (pm % 8) 1))) := by
  have h1 : U +> unary pa (bitsM pm) = pairM_side (1 + pa, pm) := by
    unfold pairM_side unary
    dsimp only
    have he : 1 + pa = pa + 1 := by omega
    rw [he, pow_succ_list, append_assoc]
  rw [h1] at hSide
  cases hd1 : Nat.beq (pm % 8) 1 with
  | false => exact hSide
  | true =>
    dsimp only
    have hm1 := Nat.eq_of_beq_eq_true hd1
    exact collectM_inv
      (fun sub o =>
          U ^ (1 + pa) +> sub = pairM_side (1 + pa, pm) → Spec pairM_side hs r (toResultP o))
      (roundT_col1 pa)
      (fun ca cm heq => by
        unfold roundT_col1
        rw [retP_eq]
        dsimp only [toResultP, Spec, pairM_side, unary]
        dsimp only [unary] at heq
        rw [Nat.add_eq, Nat.add_eq, pow_add_list, append_assoc, heq]
        exact hSide)
      64 1 (pm / 8)
      (by
        unfold pairM_side unary
        dsimp only
        rw [bitsM_eq_of_eq pm (by omega) (bitsM_U (pm / 8))]
        rfl)

theorem roundT_spec {ev : ModeM → Nat → Result Nat} (hev : EvalSpec ev) (tfuel a m : Nat) :
    Spec pairM_side g (pairM_side (a, m)) (toResultP (roundT tfuel ev a m)) := by
  unfold roundT roundT_a0 roundT_tcall roundT_fast00 roundT_finish
  simp only [Nat.add_eq, Nat.sub_eq, shr_2, shr_3, land_3, land_7]
  cases hle2 : Nat.ble a 2 with
  | true =>
    dsimp only
    rcases a with _ | a0
    · simp only [Nat.beq]
      have hevG := evalG_spec hev m
      cases hg : evalG ev m with
      | failed => trivial
      | stopped => rw [hg] at hevG; exact hevG
      | returned r =>
        rw [hg] at hevG
        dsimp only [evalToP, Spec] at hevG ⊢
        exact collectM_inv
          (fun sub o => sub = bitsM r → Spec pairM_side g (pairM_side (0, m)) (toResultP o))
          retP
          (fun ca cm heq => by
            rw [retP_eq]
            dsimp only [toResultP, Spec, pairM_side]
            rw [heq]
            exact hevG)
          64 0 r rfl
    · have ha0_ne : Nat.beq (a0 + 1) 0 = false := rfl
      simp only [ha0_ne, Nat.add_sub_cancel]
      have htc := tcallT_spec hev tfuel a0 m
      have hun : pairM_side (a0 + 1, m) = U +> unary a0 (bitsM m) := by
        unfold pairM_side unary; dsimp only; rw [pow_succ_list, append_assoc]
      rw [hun]
      have hR := rule_spec pairM_side GU htc
      cases htc_res : tcallT tfuel ev a0 m with
      | failed => trivial
      | stopped => rw [htc_res] at hR; exact hR
      | ret pa pm =>
        rw [htc_res] at hR
        dsimp only [mapRetP, toResultP, Spec] at hR ⊢
        exact collect_tail_side pa pm hR
  | false =>
    dsimp only
    have ha3 : 3 ≤ a := by
      rcases (by omega : a ≤ 2 ∨ 3 ≤ a) with h2 | h3
      · rw [Nat.ble_eq.mpr h2] at hle2; cases hle2
      · exact h3
    cases hm4 : Nat.beq (m % 4) 0 with
    | true =>
      dsimp only
      have hm0 := Nat.eq_of_beq_eq_true hm4
      have hun : pairM_side (a, m) = U +> unary (a - 1) (([0,
          0] : List (Fin 2)) +> bitsM (m / 4)) := by
        unfold pairM_side unary
        dsimp only
        have ha1 : a = (a - 1) + 1 := by omega
        rw [bitsM_eq_of_eq m (by omega) (bitsM_00 (m / 4))]
        conv_lhs => rw [ha1, pow_succ_list, append_assoc]
      rw [hun]
      have hevH := evalH_spec hev (a - 2) (m / 4)
      have hsub : (a - 1) - 1 = a - 2 := by omega
      have hadd1 : (a - 1) + 1 = a := by omega
      have hT := T00N bitsM (a - 1) (bitsM (m / 4)) (evalH ev (a - 2) (m / 4)) (by omega)
        (by rwa [hsub])
      rw [hadd1] at hT
      have hR := rule_spec (fun pm => unary a (bitsM pm)) GU hT
      cases hh : evalH ev (a - 2) (m / 4) with
      | failed => trivial
      | stopped => rw [hh] at hR; exact hR
      | returned pm =>
        rw [hh] at hR
        dsimp only [evalToP, Spec] at hR ⊢
        exact collect_tail_side a pm hR
    | false =>
      dsimp only
      have htc := tcallT_spec hev tfuel (a - 1) m
      have hun : pairM_side (a, m) = U +> unary (a - 1) (bitsM m) := by
        unfold pairM_side unary
        dsimp only
        have ha1 : a = (a - 1) + 1 := by omega
        conv_lhs => rw [ha1, pow_succ_list, append_assoc]
      rw [hun]
      have hR := rule_spec pairM_side GU htc
      cases htc_res : tcallT tfuel ev (a - 1) m with
      | failed => trivial
      | stopped => rw [htc_res] at hR; exact hR
      | ret pa pm =>
        rw [htc_res] at hR
        dsimp only [mapRetP, toResultP, Spec] at hR ⊢
        exact collect_tail_side pa pm hR

def rootM (a m : Nat) : Cfg (Fin 2) (Fin 6) :=
  default <{{C}} ([1] +> pairM_side (a, m))

theorem emit (r : ListBlank (Fin 2)) :
    (default <{{C}} ([1] +> r)) [tm]⊢⁺ (toDHCfg ((E, [0, 0]), .right) default r) := by
  dsimp [toDHCfg]
  tm_steps

theorem init_reaches_rootM :
    (init []) [tm]⊢* (rootM 0 1) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  have hb1 : bitsM 1 = ([1] : List (Fin 2)) +> default := by
    exact (bitsM_bit1 0).trans (by rw [bitsM_zero]; rfl)
  rw [h_init]
  unfold rootM pairM_side unary
  rw [hb1]
  dsimp [U]
  tm_steps

def machineM_spec (a m : Nat) (o : ResP) : Prop :=
  match o with
  | .failed => True
  | .stopped => HaltsFrom tm (rootM a m)
  | .ret a' m' => (rootM a m) [tm]⊢* (rootM a' m')

theorem roundT_machine (tfuel efuel a m : Nat) :
    machineM_spec a m (roundT tfuel (evalT efuel) a m) := by
  have H := roundT_spec (evalT_spec efuel) tfuel a m
  cases hr : roundT tfuel (evalT efuel) a m with
  | failed => trivial
  | stopped =>
    rw [hr] at H
    exact HaltsFrom.of_reachesStar (stepPlus_to_stepStar (emit (pairM_side (a, m))))
      (H.elim_single default)
  | ret a' m' =>
    rw [hr] at H
    exact stepPlus_to_stepStar (stepPlus_trans (emit (pairM_side (a, m))) (H.elim_single default))

theorem runT_spec (fuel tfuel efuel a m : Nat) :
    machineM_spec a m (runT fuel tfuel efuel a m) := by
  induction fuel generalizing a m with
  | zero => exact stepStar_refl tm (rootM a m)
  | succ fuel ih =>
    change machineM_spec a m (runT_step tfuel (evalT efuel) (runT fuel tfuel efuel) a m)
    unfold runT_step
    have hr := roundT_machine tfuel efuel a m
    cases hrm : roundT tfuel (evalT efuel) a m with
    | failed => trivial
    | stopped => rw [hrm] at hr; exact hr
    | ret a' m' =>
      rw [hrm] at hr
      dsimp only [mapRetP]
      have hnext := ih a' m'
      cases hrun : runT fuel tfuel efuel a' m' with
      | failed => trivial
      | stopped => rw [hrun] at hnext; exact HaltsFrom.of_reachesStar hr hnext
      | ret a2 m2 => rw [hrun] at hnext; exact stepStar_trans hr hnext

theorem runT_chk_step {fuel a m ta tm_exp : Nat}
    (hchk : runT_chk fuel a m ta tm_exp = true)
    (htgt : HaltsFrom tm (rootM ta tm_exp)) :
    HaltsFrom tm (rootM a m) := by
  unfold runT_chk at hchk
  have hs := runT_spec fuel 64 256 a m
  cases hr : runT fuel 64 256 a m with
  | failed => rw [hr] at hchk; cases hchk
  | stopped => rw [hr] at hchk; cases hchk
  | ret a' m' =>
    rw [hr] at hchk hs
    dsimp only at hchk
    cases ha : Nat.beq a' ta with
    | false => rw [ha] at hchk; cases hchk
    | true =>
      rw [ha] at hchk; dsimp only at hchk
      rw [Nat.eq_of_beq_eq_true ha, Nat.eq_of_beq_eq_true hchk] at hs
      exact HaltsFrom.of_reachesStar hs htgt

theorem runT_halt_spec {fuel a m : Nat}
    (hhalt : runT_halt fuel a m = true) :
    HaltsFrom tm (rootM a m) := by
  unfold runT_halt at hhalt
  have hs := runT_spec fuel 64 256 a m
  cases hr : runT fuel 64 256 a m with
  | failed => rw [hr] at hhalt; cases hhalt
  | ret _ _ => rw [hr] at hhalt; cases hhalt
  | stopped => rw [hr] at hs; exact hs

theorem halt_of_rootM01 (H : HaltsFrom tm (rootM 0 1)) : IsHalt target_tm := by
  obtain ⟨cfg, h_reach, h_none⟩ := HaltsFrom.of_reachesStar init_reaches_rootM H
  refine ⟨flipCfg cfg, ?_, ?_⟩
  · exact stepStar_unflipTM h_reach
  · rw [Option.isNone_iff_eq_none] at h_none ⊢
    have h_step := step_flipTM tm cfg
    rw [flipTM_flipTM, h_none] at h_step
    exact h_step

private theorem chunk_0 : runT_chk 6400 0 1 12593 8818796 = true := by decide +kernel
private theorem chunk_1 : runT_chk 6400 12593 8818796 25235 11704360 = true := by decide +kernel
private theorem chunk_2 : runT_chk 6400 25235 11704360 37998 10754093 = true := by decide +kernel
private theorem chunk_3 : runT_chk 6400 37998 10754093 50947 11829824 = true := by decide +kernel
private theorem chunk_4 : runT_chk 6400 50947 11829824 63532 2396997 = true := by decide +kernel
private theorem chunk_5 : runT_chk 6400 63532 2396997 76241 353398852384 = true := by decide +kernel
private theorem chunk_6 : runT_chk 6400 76241 353398852384 88987 8819213 = true := by decide +kernel
private theorem chunk_7 : runT_chk 6400 88987 8819213 101756 1315396 = true := by decide +kernel
private theorem chunk_8 : runT_chk 6400 101756 1315396 114527 11847680 = true := by decide +kernel
private theorem chunk_9 : runT_chk 6400 114527 11847680 127285 537970789 = true := by decide +kernel
private theorem chunk_10 : runT_chk 6400 127285 537970789 140058 35655045632 = true := by
  decide +kernel
private theorem chunk_11 : runT_chk 6400 140058 35655045632 152712 20748 = true := by decide +kernel
private theorem chunk_12 : runT_chk 6400 152712 20748 165515 689178664 = true := by decide +kernel
private theorem chunk_13 : runT_chk 6400 165515 689178664 178517 4524654600 = true := by
  decide +kernel
private theorem chunk_14 : runT_chk 6400 178517 4524654600 191204 699828256 = true := by
  decide +kernel
private theorem chunk_15 : runT_chk 6400 191204 699828256 203927 682803276 = true := by
  decide +kernel
private theorem chunk_16 : runT_chk 6400 203927 682803276 216710 738611813 = true := by
  decide +kernel
private theorem chunk_17 : runT_chk 6400 216710 738611813 229298 87033928 = true := by
  decide +kernel
private theorem chunk_18 : runT_chk 6400 229298 87033928 242036 1731955742471522852 = true := by
  decide +kernel
private theorem chunk_19 : runT_chk 6400 242036 1731955742471522852 254784 682935085 = true := by
  decide +kernel
private theorem chunk_20 : runT_chk 6400 254784 682935085 267535 10652420 = true := by
  decide +kernel
private theorem chunk_21 : runT_chk 6400 267535 10652420 280239 556030828 = true := by
  decide +kernel
private theorem chunk_22 : runT_chk 6400 280239 556030828 292798 679533316 = true := by
  decide +kernel
private theorem chunk_23 : runT_chk 6400 292798 679533316 305363 4323711789 = true := by
  decide +kernel
private theorem chunk_24 : runT_chk 6400 305363 4323711789 317940 755141476 = true := by
  decide +kernel
private theorem chunk_25 : runT_chk 6400 317940 755141476 330603 565348416 = true := by
  decide +kernel
private theorem chunk_26 : runT_chk 6400 330603 565348416 343499 741364261 = true := by
  decide +kernel
private theorem chunk_27 : runT_chk 6400 343499 741364261 356222 763511141 = true := by
  decide +kernel
private theorem chunk_28 : runT_chk 6400 356222 763511141 368743 681612077 = true := by
  decide +kernel
private theorem chunk_29 : runT_chk 6400 368743 681612077 381601 739660069 = true := by
  decide +kernel
private theorem chunk_30 : runT_chk 6400 381601 739660069 394329 755143424 = true := by
  decide +kernel
private theorem chunk_31 : runT_chk 6400 394329 755143424 407198 564155213 = true := by
  decide +kernel
private theorem chunk_32 : runT_chk 6400 407198 564155213 419930 557224448 = true := by
  decide +kernel
private theorem chunk_33 : runT_chk 6400 419930 557224448 432658 70539852 = true := by
  decide +kernel
private theorem chunk_34 : runT_chk 6400 432658 70539852 445371 629459752 = true := by
  decide +kernel
private theorem chunk_35 : runT_chk 6400 445371 629459752 458224 691159368 = true := by
  decide +kernel
private theorem chunk_36 : runT_chk 6400 458224 691159368 471175 757109024 = true := by
  decide +kernel
private theorem chunk_37 : runT_chk 6400 471175 757109024 483802 5596271148 = true := by
  decide +kernel
private theorem chunk_38 : runT_chk 6400 483802 5596271148 496578 755030028 = true := by
  decide +kernel
private theorem chunk_39 : runT_chk 6400 496578 755030028 509523 547373677 = true := by
  decide +kernel
private theorem chunk_40 : runT_chk 6400 509523 547373677 522244 673597733 = true := by
  decide +kernel
private theorem chunk_41 : runT_chk 6400 522244 673597733 535122 2759134204000 = true := by
  decide +kernel
private theorem chunk_42 : runT_chk 6400 535122 2759134204000 547837 538101804 = true := by
  decide +kernel
private theorem chunk_43 : runT_chk 6400 547837 538101804 560792 1130926791088716 = true := by
  decide +kernel
private theorem chunk_44 : runT_chk 6400 560792 1130926791088716 573724 614767372 = true := by
  decide +kernel
private theorem chunk_45 : runT_chk 6400 573724 614767372 586487 629574496 = true := by
  decide +kernel
private theorem chunk_46 : runT_chk 6400 586487 629574496 599316 631652965 = true := by
  decide +kernel
private theorem chunk_47 : runT_chk 6400 599316 631652965 612071 629166341 = true := by
  decide +kernel
private theorem chunk_48 : runT_chk 6400 612071 629166341 624737 631523884 = true := by
  decide +kernel
private theorem chunk_49 : runT_chk 6400 624737 631523884 637630 5453814568 = true := by
  decide +kernel
private theorem chunk_50 : runT_chk 6400 637630 5453814568 650335 44704337920 = true := by
  decide +kernel
private theorem chunk_51 : runT_chk 6400 650335 44704337920 663130 607277132 = true := by
  decide +kernel
private theorem chunk_52 : runT_chk 6400 663130 607277132 675912 740332388 = true := by
  decide +kernel
private theorem chunk_53 : runT_chk 6400 675912 740332388 688663 765481224 = true := by
  decide +kernel
private theorem chunk_54 : runT_chk 6400 688663 765481224 701509 18221091787016 = true := by
  decide +kernel
private theorem chunk_55 : runT_chk 6400 701509 18221091787016 714323 6133422189 = true := by
  decide +kernel
private theorem chunk_56 : runT_chk 6400 714323 6133422189 727195 698405696 = true := by
  decide +kernel
private theorem chunk_57 : runT_chk 6400 727195 698405696 739929 691406880 = true := by
  decide +kernel
private theorem chunk_58 : runT_chk 6400 739929 691406880 752893 5595470181 = true := by
  decide +kernel
private theorem chunk_59 : runT_chk 6400 752893 5595470181 765593 5505178124 = true := by
  decide +kernel
private theorem chunk_60 : runT_chk 6400 765593 5505178124 778344 36180246637 = true := by
  decide +kernel
private theorem chunk_61 : runT_chk 6400 778344 36180246637 791032 5504402028 = true := by
  decide +kernel
private theorem chunk_62 : runT_chk 6400 791032 5504402028 803867 5438968416 = true := by
  decide +kernel
private theorem chunk_63 : runT_chk 6400 803867 5438968416 816770 5041740044 = true := by
  decide +kernel
private theorem chunk_64 : runT_chk 6400 816770 5041740044 829360 1688521324 = true := by
  decide +kernel
private theorem chunk_65 : runT_chk 6400 829360 1688521324 842050 5462444292 = true := by
  decide +kernel
private theorem chunk_66 : runT_chk 6400 842050 5462444292 854658 35503132677 = true := by
  decide +kernel
private theorem chunk_67 : runT_chk 6400 854658 35503132677 867544 4857037096 = true := by
  decide +kernel
private theorem chunk_68 : runT_chk 6400 867544 4857037096 880465 5924606060 = true := by
  decide +kernel
private theorem chunk_69 : runT_chk 6400 880465 5924606060 893181 696423200 = true := by
  decide +kernel
private theorem chunk_70 : runT_chk 6400 893181 696423200 905958 5570465829 = true := by
  decide +kernel
private theorem chunk_71 : runT_chk 6400 905958 5570465829 918560 5587126316 = true := by
  decide +kernel
private theorem chunk_72 : runT_chk 6400 918560 5587126316 931438 697752109 = true := by
  decide +kernel
private theorem chunk_73 : runT_chk 6400 931438 697752109 944197 5908859468 = true := by
  decide +kernel
private theorem chunk_74 : runT_chk 6400 944197 5908859468 956812 5452763429 = true := by
  decide +kernel
private theorem chunk_75 : runT_chk 6400 956812 5452763429 969696 5916197124 = true := by
  decide +kernel
private theorem chunk_76 : runT_chk 6400 969696 5916197124 982467 671240740 = true := by
  decide +kernel
private theorem chunk_77 : runT_chk 6400 982467 671240740 995065 95476069 = true := by
  decide +kernel
private theorem chunk_78 : runT_chk 6400 995065 95476069 1007858 739379520 = true := by
  decide +kernel
private theorem chunk_79 : runT_chk 6400 1007858 739379520 1020513 5372168296 = true := by
  decide +kernel
private theorem chunk_80 : runT_chk 6400 1020513 5372168296 1033229 671371533 = true := by
  decide +kernel
private theorem chunk_81 : runT_chk 6400 1033229 671371533 1046044 6116526605 = true := by
  decide +kernel
private theorem chunk_82 : runT_chk 6400 1046044 6116526605 1058729 672547620 = true := by
  decide +kernel
private theorem chunk_83 : runT_chk 6400 1058729 672547620 1071541 672192588 = true := by
  decide +kernel
private theorem chunk_84 : runT_chk 6400 1071541 672192588 1084175 21925272956179430431533 = true :=
    by decide +kernel
private theorem chunk_85 : runT_chk 6400 1084175 21925272956179430431533 1096957 48481092160 =
    true := by decide +kernel
private theorem chunk_86 : runT_chk 6400 1096957 48481092160 1109745 688311080 = true := by
  decide +kernel
private theorem chunk_87 : runT_chk 6400 1109745 688311080 1122300 5371250952 = true := by
  decide +kernel
private theorem chunk_88 : runT_chk 6400 1122300 5371250952 1135104 283627389740 = true := by
  decide +kernel
private theorem chunk_89 : runT_chk 6400 1135104 283627389740 1147873 5521054028 = true := by
  decide +kernel
private theorem chunk_90 : runT_chk 6400 1147873 5521054028 1160581 94666764 = true := by
  decide +kernel
private theorem chunk_91 : runT_chk 6400 1160581 94666764 1173249 4457765476 = true := by
  decide +kernel
private theorem chunk_92 : runT_chk 6400 1173249 4457765476 1186166 6048598341 = true := by
  decide +kernel
private theorem chunk_93 : runT_chk 6400 1186166 6048598341 1198988 1822839592 = true := by
  decide +kernel
private theorem chunk_94 : runT_chk 6400 1198988 1822839592 1211753 6059858757 = true := by
  decide +kernel
private theorem chunk_95 : runT_halt 6400 1211753 6059858757 = true := by decide +kernel

end Solution



public section

theorem is_halt : IsHalt target := by
  have h95 : HaltsFrom Solution.tm (Solution.rootM 1211753 6059858757) :=
      Solution.runT_halt_spec Solution.chunk_95
  have h94 : HaltsFrom Solution.tm (Solution.rootM 1198988 1822839592) :=
      Solution.runT_chk_step Solution.chunk_94 h95
  have h93 : HaltsFrom Solution.tm (Solution.rootM 1186166 6048598341) :=
      Solution.runT_chk_step Solution.chunk_93 h94
  have h92 : HaltsFrom Solution.tm (Solution.rootM 1173249 4457765476) :=
      Solution.runT_chk_step Solution.chunk_92 h93
  have h91 : HaltsFrom Solution.tm (Solution.rootM 1160581 94666764) :=
      Solution.runT_chk_step Solution.chunk_91 h92
  have h90 : HaltsFrom Solution.tm (Solution.rootM 1147873 5521054028) :=
      Solution.runT_chk_step Solution.chunk_90 h91
  have h89 : HaltsFrom Solution.tm (Solution.rootM 1135104 283627389740) :=
      Solution.runT_chk_step Solution.chunk_89 h90
  have h88 : HaltsFrom Solution.tm (Solution.rootM 1122300 5371250952) :=
      Solution.runT_chk_step Solution.chunk_88 h89
  have h87 : HaltsFrom Solution.tm (Solution.rootM 1109745 688311080) :=
      Solution.runT_chk_step Solution.chunk_87 h88
  have h86 : HaltsFrom Solution.tm (Solution.rootM 1096957 48481092160) :=
      Solution.runT_chk_step Solution.chunk_86 h87
  have h85 : HaltsFrom Solution.tm (Solution.rootM 1084175 21925272956179430431533) :=
      Solution.runT_chk_step Solution.chunk_85 h86
  have h84 : HaltsFrom Solution.tm (Solution.rootM 1071541 672192588) :=
      Solution.runT_chk_step Solution.chunk_84 h85
  have h83 : HaltsFrom Solution.tm (Solution.rootM 1058729 672547620) :=
      Solution.runT_chk_step Solution.chunk_83 h84
  have h82 : HaltsFrom Solution.tm (Solution.rootM 1046044 6116526605) :=
      Solution.runT_chk_step Solution.chunk_82 h83
  have h81 : HaltsFrom Solution.tm (Solution.rootM 1033229 671371533) :=
      Solution.runT_chk_step Solution.chunk_81 h82
  have h80 : HaltsFrom Solution.tm (Solution.rootM 1020513 5372168296) :=
      Solution.runT_chk_step Solution.chunk_80 h81
  have h79 : HaltsFrom Solution.tm (Solution.rootM 1007858 739379520) :=
      Solution.runT_chk_step Solution.chunk_79 h80
  have h78 : HaltsFrom Solution.tm (Solution.rootM 995065 95476069) :=
      Solution.runT_chk_step Solution.chunk_78 h79
  have h77 : HaltsFrom Solution.tm (Solution.rootM 982467 671240740) :=
      Solution.runT_chk_step Solution.chunk_77 h78
  have h76 : HaltsFrom Solution.tm (Solution.rootM 969696 5916197124) :=
      Solution.runT_chk_step Solution.chunk_76 h77
  have h75 : HaltsFrom Solution.tm (Solution.rootM 956812 5452763429) :=
      Solution.runT_chk_step Solution.chunk_75 h76
  have h74 : HaltsFrom Solution.tm (Solution.rootM 944197 5908859468) :=
      Solution.runT_chk_step Solution.chunk_74 h75
  have h73 : HaltsFrom Solution.tm (Solution.rootM 931438 697752109) :=
      Solution.runT_chk_step Solution.chunk_73 h74
  have h72 : HaltsFrom Solution.tm (Solution.rootM 918560 5587126316) :=
      Solution.runT_chk_step Solution.chunk_72 h73
  have h71 : HaltsFrom Solution.tm (Solution.rootM 905958 5570465829) :=
      Solution.runT_chk_step Solution.chunk_71 h72
  have h70 : HaltsFrom Solution.tm (Solution.rootM 893181 696423200) :=
      Solution.runT_chk_step Solution.chunk_70 h71
  have h69 : HaltsFrom Solution.tm (Solution.rootM 880465 5924606060) :=
      Solution.runT_chk_step Solution.chunk_69 h70
  have h68 : HaltsFrom Solution.tm (Solution.rootM 867544 4857037096) :=
      Solution.runT_chk_step Solution.chunk_68 h69
  have h67 : HaltsFrom Solution.tm (Solution.rootM 854658 35503132677) :=
      Solution.runT_chk_step Solution.chunk_67 h68
  have h66 : HaltsFrom Solution.tm (Solution.rootM 842050 5462444292) :=
      Solution.runT_chk_step Solution.chunk_66 h67
  have h65 : HaltsFrom Solution.tm (Solution.rootM 829360 1688521324) :=
      Solution.runT_chk_step Solution.chunk_65 h66
  have h64 : HaltsFrom Solution.tm (Solution.rootM 816770 5041740044) :=
      Solution.runT_chk_step Solution.chunk_64 h65
  have h63 : HaltsFrom Solution.tm (Solution.rootM 803867 5438968416) :=
      Solution.runT_chk_step Solution.chunk_63 h64
  have h62 : HaltsFrom Solution.tm (Solution.rootM 791032 5504402028) :=
      Solution.runT_chk_step Solution.chunk_62 h63
  have h61 : HaltsFrom Solution.tm (Solution.rootM 778344 36180246637) :=
      Solution.runT_chk_step Solution.chunk_61 h62
  have h60 : HaltsFrom Solution.tm (Solution.rootM 765593 5505178124) :=
      Solution.runT_chk_step Solution.chunk_60 h61
  have h59 : HaltsFrom Solution.tm (Solution.rootM 752893 5595470181) :=
      Solution.runT_chk_step Solution.chunk_59 h60
  have h58 : HaltsFrom Solution.tm (Solution.rootM 739929 691406880) :=
      Solution.runT_chk_step Solution.chunk_58 h59
  have h57 : HaltsFrom Solution.tm (Solution.rootM 727195 698405696) :=
      Solution.runT_chk_step Solution.chunk_57 h58
  have h56 : HaltsFrom Solution.tm (Solution.rootM 714323 6133422189) :=
      Solution.runT_chk_step Solution.chunk_56 h57
  have h55 : HaltsFrom Solution.tm (Solution.rootM 701509 18221091787016) :=
      Solution.runT_chk_step Solution.chunk_55 h56
  have h54 : HaltsFrom Solution.tm (Solution.rootM 688663 765481224) :=
      Solution.runT_chk_step Solution.chunk_54 h55
  have h53 : HaltsFrom Solution.tm (Solution.rootM 675912 740332388) :=
      Solution.runT_chk_step Solution.chunk_53 h54
  have h52 : HaltsFrom Solution.tm (Solution.rootM 663130 607277132) :=
      Solution.runT_chk_step Solution.chunk_52 h53
  have h51 : HaltsFrom Solution.tm (Solution.rootM 650335 44704337920) :=
      Solution.runT_chk_step Solution.chunk_51 h52
  have h50 : HaltsFrom Solution.tm (Solution.rootM 637630 5453814568) :=
      Solution.runT_chk_step Solution.chunk_50 h51
  have h49 : HaltsFrom Solution.tm (Solution.rootM 624737 631523884) :=
      Solution.runT_chk_step Solution.chunk_49 h50
  have h48 : HaltsFrom Solution.tm (Solution.rootM 612071 629166341) :=
      Solution.runT_chk_step Solution.chunk_48 h49
  have h47 : HaltsFrom Solution.tm (Solution.rootM 599316 631652965) :=
      Solution.runT_chk_step Solution.chunk_47 h48
  have h46 : HaltsFrom Solution.tm (Solution.rootM 586487 629574496) :=
      Solution.runT_chk_step Solution.chunk_46 h47
  have h45 : HaltsFrom Solution.tm (Solution.rootM 573724 614767372) :=
      Solution.runT_chk_step Solution.chunk_45 h46
  have h44 : HaltsFrom Solution.tm (Solution.rootM 560792 1130926791088716) :=
      Solution.runT_chk_step Solution.chunk_44 h45
  have h43 : HaltsFrom Solution.tm (Solution.rootM 547837 538101804) :=
      Solution.runT_chk_step Solution.chunk_43 h44
  have h42 : HaltsFrom Solution.tm (Solution.rootM 535122 2759134204000) :=
      Solution.runT_chk_step Solution.chunk_42 h43
  have h41 : HaltsFrom Solution.tm (Solution.rootM 522244 673597733) :=
      Solution.runT_chk_step Solution.chunk_41 h42
  have h40 : HaltsFrom Solution.tm (Solution.rootM 509523 547373677) :=
      Solution.runT_chk_step Solution.chunk_40 h41
  have h39 : HaltsFrom Solution.tm (Solution.rootM 496578 755030028) :=
      Solution.runT_chk_step Solution.chunk_39 h40
  have h38 : HaltsFrom Solution.tm (Solution.rootM 483802 5596271148) :=
      Solution.runT_chk_step Solution.chunk_38 h39
  have h37 : HaltsFrom Solution.tm (Solution.rootM 471175 757109024) :=
      Solution.runT_chk_step Solution.chunk_37 h38
  have h36 : HaltsFrom Solution.tm (Solution.rootM 458224 691159368) :=
      Solution.runT_chk_step Solution.chunk_36 h37
  have h35 : HaltsFrom Solution.tm (Solution.rootM 445371 629459752) :=
      Solution.runT_chk_step Solution.chunk_35 h36
  have h34 : HaltsFrom Solution.tm (Solution.rootM 432658 70539852) :=
      Solution.runT_chk_step Solution.chunk_34 h35
  have h33 : HaltsFrom Solution.tm (Solution.rootM 419930 557224448) :=
      Solution.runT_chk_step Solution.chunk_33 h34
  have h32 : HaltsFrom Solution.tm (Solution.rootM 407198 564155213) :=
      Solution.runT_chk_step Solution.chunk_32 h33
  have h31 : HaltsFrom Solution.tm (Solution.rootM 394329 755143424) :=
      Solution.runT_chk_step Solution.chunk_31 h32
  have h30 : HaltsFrom Solution.tm (Solution.rootM 381601 739660069) :=
      Solution.runT_chk_step Solution.chunk_30 h31
  have h29 : HaltsFrom Solution.tm (Solution.rootM 368743 681612077) :=
      Solution.runT_chk_step Solution.chunk_29 h30
  have h28 : HaltsFrom Solution.tm (Solution.rootM 356222 763511141) :=
      Solution.runT_chk_step Solution.chunk_28 h29
  have h27 : HaltsFrom Solution.tm (Solution.rootM 343499 741364261) :=
      Solution.runT_chk_step Solution.chunk_27 h28
  have h26 : HaltsFrom Solution.tm (Solution.rootM 330603 565348416) :=
      Solution.runT_chk_step Solution.chunk_26 h27
  have h25 : HaltsFrom Solution.tm (Solution.rootM 317940 755141476) :=
      Solution.runT_chk_step Solution.chunk_25 h26
  have h24 : HaltsFrom Solution.tm (Solution.rootM 305363 4323711789) :=
      Solution.runT_chk_step Solution.chunk_24 h25
  have h23 : HaltsFrom Solution.tm (Solution.rootM 292798 679533316) :=
      Solution.runT_chk_step Solution.chunk_23 h24
  have h22 : HaltsFrom Solution.tm (Solution.rootM 280239 556030828) :=
      Solution.runT_chk_step Solution.chunk_22 h23
  have h21 : HaltsFrom Solution.tm (Solution.rootM 267535 10652420) :=
      Solution.runT_chk_step Solution.chunk_21 h22
  have h20 : HaltsFrom Solution.tm (Solution.rootM 254784 682935085) :=
      Solution.runT_chk_step Solution.chunk_20 h21
  have h19 : HaltsFrom Solution.tm (Solution.rootM 242036 1731955742471522852) :=
      Solution.runT_chk_step Solution.chunk_19 h20
  have h18 : HaltsFrom Solution.tm (Solution.rootM 229298 87033928) :=
      Solution.runT_chk_step Solution.chunk_18 h19
  have h17 : HaltsFrom Solution.tm (Solution.rootM 216710 738611813) :=
      Solution.runT_chk_step Solution.chunk_17 h18
  have h16 : HaltsFrom Solution.tm (Solution.rootM 203927 682803276) :=
      Solution.runT_chk_step Solution.chunk_16 h17
  have h15 : HaltsFrom Solution.tm (Solution.rootM 191204 699828256) :=
      Solution.runT_chk_step Solution.chunk_15 h16
  have h14 : HaltsFrom Solution.tm (Solution.rootM 178517 4524654600) :=
      Solution.runT_chk_step Solution.chunk_14 h15
  have h13 : HaltsFrom Solution.tm (Solution.rootM 165515 689178664) :=
      Solution.runT_chk_step Solution.chunk_13 h14
  have h12 : HaltsFrom Solution.tm (Solution.rootM 152712 20748) :=
      Solution.runT_chk_step Solution.chunk_12 h13
  have h11 : HaltsFrom Solution.tm (Solution.rootM 140058 35655045632) :=
      Solution.runT_chk_step Solution.chunk_11 h12
  have h10 : HaltsFrom Solution.tm (Solution.rootM 127285 537970789) :=
      Solution.runT_chk_step Solution.chunk_10 h11
  have h9 : HaltsFrom Solution.tm (Solution.rootM 114527 11847680) :=
      Solution.runT_chk_step Solution.chunk_9 h10
  have h8 : HaltsFrom Solution.tm (Solution.rootM 101756 1315396) :=
      Solution.runT_chk_step Solution.chunk_8 h9
  have h7 : HaltsFrom Solution.tm (Solution.rootM 88987 8819213) :=
      Solution.runT_chk_step Solution.chunk_7 h8
  have h6 : HaltsFrom Solution.tm (Solution.rootM 76241 353398852384) :=
      Solution.runT_chk_step Solution.chunk_6 h7
  have h5 : HaltsFrom Solution.tm (Solution.rootM 63532 2396997) :=
      Solution.runT_chk_step Solution.chunk_5 h6
  have h4 : HaltsFrom Solution.tm (Solution.rootM 50947 11829824) :=
      Solution.runT_chk_step Solution.chunk_4 h5
  have h3 : HaltsFrom Solution.tm (Solution.rootM 37998 10754093) :=
      Solution.runT_chk_step Solution.chunk_3 h4
  have h2 : HaltsFrom Solution.tm (Solution.rootM 25235 11704360) :=
      Solution.runT_chk_step Solution.chunk_2 h3
  have h1 : HaltsFrom Solution.tm (Solution.rootM 12593 8818796) :=
      Solution.runT_chk_step Solution.chunk_1 h2
  have h0 : HaltsFrom Solution.tm (Solution.rootM 0 1) := Solution.runT_chk_step Solution.chunk_0 h1
  exact Solution.halt_of_rootM01 h0

end

end BusyBeaver.M_1RB0RE_1RC0RA_0LD0RB_1LA0LE_1LC1LF_0LCHHH
