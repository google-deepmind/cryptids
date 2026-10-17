/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BusyBeaver.Basic
public import BusyBeaver.Bridge
/-!
# Busy Beaver Holdout `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD`
## Collatz-like Acceleration Rules
Canonical configurations.
-/
@[expose] public section
namespace BusyBeaver.M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD
open Turing
local notation "A" => (0 : Fin 6)
local notation "B" => (1 : Fin 6)
local notation "C" => (2 : Fin 6)
local notation "D" => (3 : Fin 6)
local notation "E" => (4 : Fin 6)
local notation "F" => (5 : Fin 6)
def machine : ConjectureMachines.Machine 6 2 := load_rle_machine%
      "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
local notation c₁ " ⊢⁺ " c₂ => ReachesPlus target c₁ c₂
local notation c₁ " ⊢* " c₂ => ReachesStar target c₁ c₂
local notation c₁ " ⊢ " c₂ => step target c₁ = some c₂
local notation l " {{" s "}} " r => (⟨s, l, r⟩ : Tape _)
local notation:67 s:67 " << " a:68 => ListBlank.cons a s
local infixr:67 " >> " => ListBlank.cons
local notation:67 s:67 " <+ " l:68 => ListBlank.append l s
local infixr:67 " +> " => ListBlank.append
local notation l " {{" q "}}> " r => Cfg.headRight q l r
local notation l " <{{" q "}} " r => Cfg.headLeft q l r
@[simp] lemma list_pow_zero (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma list_pow_succ (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma list_cons_app (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++
  ys) := rfl
@[simp] lemma list_app_nil (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma listblank_nil_app (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_cons_app (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x
  :: xs) +> b
      = x >> (xs +> b) := rfl
@[simp] lemma listblank_zero_cons_def : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma listblank_head_def : (default : ListBlank (Fin 2)).head = (0 : Fin 2) := rfl
@[simp] lemma listblank_tail_def : (default : ListBlank (Fin 2)).tail = default := rfl
lemma list_pow_add_c (u : List (Fin 2)) (n m : Nat) : u ^ (n + m) = u ^ n ++ u ^ m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add]
    change u ++ u ^ (n + m) = u ++ u ^ n ++ u ^ m
    rw [ih, List.append_assoc]
lemma list_pow_comm (u : List (Fin 2)) (n m : Nat) : u ^ n ++ u ^ m = u ^ m ++ u ^ n := by
  rw [<- list_pow_add_c, Nat.add_comm, list_pow_add_c]
  
lemma listblank_app_assoc (s : ListBlank (Fin 2)) (l₁ l₂ : List (Fin 2)) :
    (s <+ l₁) <+ l₂ = s <+ (l₂ ++ l₁) := by
  exact (ListBlank.append_assoc l₂ l₁ s).symm
lemma list_pow_add_one (u : List (Fin 2)) (k : Nat) :
    u^k ++ u = u^(k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    change u ++ u^k ++ u = u ++ u^(k + 1)
    rw [List.append_assoc, ih]
lemma list_pow_app_right (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add_c, <- listblank_app_assoc]
lemma list_pow_succ_right (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [list_pow_succ, <- listblank_app_assoc]
lemma listblank_app_pow (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [listblank_app_assoc, <- list_pow_add_c, Nat.add_comm]
lemma list_pow_app_one (u : List (Fin 2)) (k : Nat) (r : ListBlank (Fin 2)) :
    (u ^ k) +> (u +> r) = (u ^ (k + 1)) +> r := by
  rw [listblank_app_assoc, list_pow_add_one]
lemma listblank_app_pow_left (l : ListBlank (Fin 2)) (u : List (Fin 2)) (k : Nat) :
    (l <+ u) <+ (u ^ k) = l <+ (u ^ (k + 1)) := by
  rw [listblank_app_assoc, list_pow_add_one]
lemma append_zero_pow_01 (s : ListBlank (Fin 2)) (k : Nat) :
    (s <+ [0]) <+ ([0, 1] : List (Fin 2)) ^ k = (s <+ ([1, 0] : List (Fin 2)) ^ k) <+ [0] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ([0, 1] : List (Fin 2)) +> (([0, 1] : List (Fin 2)) ^ k +> ([0] +> s))
      = [0] +> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> s))
    rw [ih]
    rfl
lemma default_pow_01 (c : Nat) :
    (default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ c =
    (default <+ ([1, 0] : List (Fin 2)) ^ c) <+ [0] := by
  have h0 : (default : ListBlank (Fin 2)) = default <+ [0] := by
    apply ListBlank.ext; intro i; cases i <;> rfl
  conv_lhs => rw [h0]
  exact append_zero_pow_01 default c
lemma pow_11_eq_pow_1_mul2 (k : Nat) :
    ([1, 1] : List (Fin 2)) ^ k = ([1] : List (Fin 2)) ^ (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [list_pow_succ, ih, h2, list_pow_add_c]
    rfl
lemma pow_1111_eq_pow_1_mul4 (k : Nat) :
    ([1, 1, 1, 1] : List (Fin 2)) ^ k = ([1] : List (Fin 2)) ^ (4 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h4 : 4 * (k + 1) = 4 + 4 * k := by omega
    rw [list_pow_succ, ih, h4, list_pow_add_c]
    rfl
lemma pow_01_mul2_eq_pow_0101 (m : Nat) :
    ([0, 1] : List (Fin 2)) ^ (2 * m) = ([0, 1, 0, 1] : List (Fin 2)) ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h2 : 2 * (m + 1) = 2 + 2 * m := by omega
    rw [h2, list_pow_add_c, ih, list_pow_succ]
    rfl
lemma pow_10_append_1 (k : Nat) (r : ListBlank (Fin 2)) :
    (([1, 0] : List (Fin 2)) ^ k) +> ([1] +> r) =
    [1] +> ((([0, 1] : List (Fin 2)) ^ k) +> r) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    change ([1, 0] : List (Fin 2)) +> (([1, 0] : List (Fin 2)) ^ k +> ([1] +> r))
      = [1] +> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ k +> r))
    rw [ih]
    rfl
lemma shift_C_right (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{C}}> (([0, 1] : List (Fin 2)) ^ k +> r)) ⊢*
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, listblank_nil_app]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [list_pow_succ_right]
    have h1 : (l {{C}}> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ k +> r)))
        ⊢*
        ((l <+ [0, 1]) {{C}}> (([0, 1] : List (Fin 2)) ^ k +> r)) := by
      dsimp [ListBlank.append]
      try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
        ListBlank.tail_default]
      bb_steps
    have h2 := ih (l <+ [0, 1]) r
    rw [listblank_app_pow_left] at h2
    exact ReachesStar.trans h1 h2
lemma shift_DC_left (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{D}}> ([0] +> r)) ⊢*
    (l {{D}}> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, listblank_nil_app]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [list_pow_succ, <- listblank_app_assoc]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) {{D}}> ([0] +> r))
        ⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{D}}> ([0] +> ([1, 0] +> r))) := by
      dsimp [ListBlank.append]
      try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
        ListBlank.tail_default]
      bb_steps
    have h2 := ih l (([1, 0] : List (Fin 2)) +> r)
    rw [list_pow_app_one] at h2
    exact ReachesStar.trans h1 h2
lemma shift_C_left_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{C}}> ([1] +> r)) ⊢*
    (l {{C}}> ([1] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, listblank_nil_app]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [list_pow_succ, <- listblank_app_assoc]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) {{C}}> ([1] +> r))
        ⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{C}}> ([1] +> ([1, 1] +> r))) := by
      dsimp [ListBlank.append]
      try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
        ListBlank.tail_default]
      bb_steps
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    rw [list_pow_app_one] at h2
    exact ReachesStar.trans h1 h2
lemma shift_E_0101 (m : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)) ⊢*
    ((l <+ ([1, 1, 1, 1] : List (Fin 2)) ^ m) {{E}}> r) := by
  induction m generalizing l r with
  | zero =>
    simp only [list_pow_zero, listblank_nil_app]
    exact ⟨0, rfl⟩
  | succ m ih =>
    rw [list_pow_succ_right]
    have h1 : (l {{E}}> ([0, 1, 0, 1] +> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)))
        ⊢*
        ((l <+ [1, 1, 1, 1]) {{E}}> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)) := by
      dsimp [ListBlank.append]
      try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
        ListBlank.tail_default]
      bb_steps
    have h2 := ih (l <+ [1, 1, 1, 1]) r
    rw [listblank_app_pow_left] at h2
    exact ReachesStar.trans h1 h2
def cfg_D (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  (default : ListBlank (Fin 2)) {{D}}> (([0, 1] : List (Fin 2)) ^ a +> (([1] : List (Fin 2)) ^ b +>
      default))
def cfg_A (l : ListBlank (Fin 2)) (k j c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (l <+ ([1] : List (Fin 2)) ^ k) {{D}}>
    ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> (([1] : List (Fin 2)) ^ c +> default)))
def l_hat : ListBlank (Fin 2) :=
  ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]
def cfg_C001 (l : ListBlank (Fin 2)) (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  l {{C}}> ([0, 0, 1] +> (([0, 1] : List (Fin 2)) ^ a +> (([1] : List (Fin 2)) ^ b +> default)))
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1] 0 (.rep [0, 1, 1, 1] 1 .default)
    head  := some D
    right := .sym 1 (.sym 1 (.rep [0, 1] 2 (.rep [1] 3 .default))) }
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .not (.ge_const 1 2))]
lemma eval_pat_A (vars : Nat -> Nat) :
    evalTapePattern pat_A vars =
    cfg_A (default <+ ([0, 1, 1, 1] : List (Fin 2)) ^ (vars 1)) (vars 0) (vars 2) (vars 3) := rfl
lemma in_ps_S_def (k j c : Nat) : IsInPatternSet ps (cfg_A default k j c) := by
  refine ⟨(pat_A, .not (.ge_const 1 2)), List.Mem.head _,
    fun i => match i with | 0 => k | 1 => 0 | 2 => j | 3 => c | _ => 0, rfl, ?_⟩
  simp [evalVarCond]
lemma in_ps_S_hat (k j c : Nat) : IsInPatternSet ps (cfg_A l_hat k j c) := by
  refine ⟨(pat_A, .not (.ge_const 1 2)), List.Mem.head _,
    fun i => match i with | 0 => k | 1 => 1 | 2 => j | 3 => c | _ => 0, rfl, ?_⟩
  simp [evalVarCond]
lemma in_ps_S_ones3 (k j c : Nat) :
    IsInPatternSet ps (cfg_A (default <+ ([1] : List (Fin 2)) ^ 3) k j c) := by
  unfold cfg_A
  rw [<- listblank_app_pow default ([1] : List (Fin 2)) 3 k]
  exact in_ps_S_def (3 + k) j c
lemma step_C001_even_to_E (l : ListBlank (Fin 2)) (m : Nat) (r : ListBlank (Fin 2)) :
    (l {{C}}> ([0, 0, 1] +> (([0, 1] : List (Fin 2)) ^ (2 * m) +> r))) ⊢⁺
    ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}> r) := by
  rw [pow_01_mul2_eq_pow_0101 m]
  have h1 : (l {{C}}> ([0, 0, 1] +> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)))
      ⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ 3) {{E}}> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)) := by
    dsimp [HPow.hPow, ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  have h2 := shift_E_0101 m (l <+ ([1] : List (Fin 2)) ^ 3) r
  rw [pow_1111_eq_pow_1_mul4 m, <- listblank_app_pow l ([1] : List (Fin 2)) 3 (4 * m)] at h2
  have hm : 3 + 4 * m = 4 * m + 3 := by omega
  rw [hm] at h2
  exact ReachesPlus.trans_star h1 h2
theorem step_C001_even_b0_halt (l : ListBlank (Fin 2)) (m : Nat) :
    ∃ cfg', ((cfg_C001 l (2 * m) 0) ⊢⁺ cfg') /\ (step target cfg').isNone := by
  refine ⟨(((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ [1]) {{F}}> default), ?_,
    by rfl⟩
  unfold cfg_C001
  simp only [list_pow_zero, listblank_nil_app]
  have h1 := step_C001_even_to_E l m default
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}> default)
      ⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ [1]) {{F}}> default) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  exact ReachesPlus.trans h1 h2
theorem step_C001_even_b1 (l : ListBlank (Fin 2)) (m : Nat) :
    (cfg_C001 l (2 * m) 1) ⊢⁺ (cfg_A l (4 * m + 2) 0 0) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, listblank_nil_app]
  have h1 := step_C001_even_to_E l m (([1] : List (Fin 2)) ^ 1 +> default)
  have hm : 4 * m + 3 = (4 * m + 2) + 1 := by omega
  rw [hm, listblank_app_pow l ([1] : List (Fin 2)) (4 * m + 2) 1] at h1
  have h2 : (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) <+ ([1] : List (Fin 2)) ^ 1) {{E}}>
      (([1] : List (Fin 2)) ^ 1 +> default))
      ⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) {{D}}> ([1, 1] +> default)) := by
    dsimp [HPow.hPow, ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  exact ReachesPlus.trans h1 h2
theorem step_C001_even_b2 (l : ListBlank (Fin 2)) (m : Nat) :
    (cfg_C001 l (2 * m) 2) ⊢⁺ (cfg_A l (4 * m + 2) 0 3) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, listblank_nil_app]
  have h1 := step_C001_even_to_E l m (([1] : List (Fin 2)) ^ 2 +> default)
  have hm : 4 * m + 3 = (4 * m + 2) + 1 := by omega
  rw [hm, listblank_app_pow l ([1] : List (Fin 2)) (4 * m + 2) 1] at h1
  have h2 : (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) <+ ([1] : List (Fin 2)) ^ 1) {{E}}>
      (([1] : List (Fin 2)) ^ 2 +> default))
      ⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    dsimp [HPow.hPow, ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  exact ReachesPlus.trans h1 h2
theorem step_C001_even_b3 (l : ListBlank (Fin 2)) (m c : Nat) :
    (cfg_C001 l (2 * m) (c + 3)) ⊢⁺ (cfg_A l (4 * m + 4) 0 c) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, listblank_nil_app]
  have hc : c + 3 = 3 + c := by omega
  rw [hc, list_pow_app_right ([1] : List (Fin 2)) 3 c default]
  have h1 := step_C001_even_to_E l m (([1] : List (Fin 2)) ^ 3 +> (([1] : List (Fin 2)) ^ c +>
      default))
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}>
      (([1] : List (Fin 2)) ^ 3 +> (([1] : List (Fin 2)) ^ c +> default)))
      ⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ c +> default))) := by
    dsimp [HPow.hPow, ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- listblank_app_pow l ([1] : List (Fin 2)) (4 * m + 3) 1] at h2
  have hm : (4 * m + 3) + 1 = 4 * m + 4 := by omega
  rw [hm] at h2
  exact ReachesPlus.trans h1 h2
theorem step_C001_odd_b0 (l : ListBlank (Fin 2)) (m : Nat) :
    (cfg_C001 l (2 * m + 1) 0) ⊢⁺ (cfg_A l (4 * m + 4) 0 1) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, listblank_nil_app]
  rw [list_pow_app_right ([0, 1] : List (Fin 2)) (2 * m) 1 default]
  have h1 := step_C001_even_to_E l m (([0, 1] : List (Fin 2)) ^ 1 +> default)
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}> (([0, 1] : List (Fin 2)) ^ 1 +>
      default))
      ⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    dsimp [HPow.hPow, ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- listblank_app_pow l ([1] : List (Fin 2)) (4 * m + 3) 1] at h2
  have hm : (4 * m + 3) + 1 = 4 * m + 4 := by omega
  rw [hm] at h2
  exact ReachesPlus.trans h1 h2
theorem step_C001_odd_b1 (l : ListBlank (Fin 2)) (m c : Nat) :
    (cfg_C001 l (2 * m + 1) (c + 1)) ⊢⁺ (cfg_A l (4 * m + 3) 0 (c + 1)) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, listblank_nil_app]
  rw [list_pow_app_right ([0, 1] : List (Fin 2)) (2 * m) 1 (([1] : List (Fin 2)) ^ (c + 1) +>
    default),
    list_pow_succ_right ([1] : List (Fin 2)) c default]
  have h1 := step_C001_even_to_E l m (([0, 1] : List (Fin 2)) ^ 1 +> ([1] +>
      (([1] : List (Fin 2)) ^ c +> default)))
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}>
      (([0, 1] : List (Fin 2)) ^ 1 +> ([1] +> (([1] : List (Fin 2)) ^ c +> default))))
      ⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{D}}>
        ([1, 1] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    dsimp [HPow.hPow, ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  exact ReachesPlus.trans h1 h2
theorem step_C001_all (l : ListBlank (Fin 2))
    (hl : ∀ k j c, IsInPatternSet ps (cfg_A l k j c)) (a b : Nat) :
    ∃ cfg', ((cfg_C001 l a b) ⊢⁺ cfg') /\
            (IsInPatternSet ps cfg' \/ (step target cfg').isNone) := by
  have ha : ∃ m, a = 2 * m \/ a = 2 * m + 1 := ⟨a / 2, by omega⟩
  rcases ha with ⟨m, rfl | rfl⟩
  · rcases b with _ | _ | _ | c
    · obtain ⟨cfg', h_plus, h_halt⟩ := step_C001_even_b0_halt l m
      exact ⟨cfg', h_plus, Or.inr h_halt⟩
    · exact ⟨_, step_C001_even_b1 l m, Or.inl (hl (4 * m + 2) 0 0)⟩
    · exact ⟨_, step_C001_even_b2 l m, Or.inl (hl (4 * m + 2) 0 3)⟩
    · exact ⟨_, step_C001_even_b3 l m c, Or.inl (hl (4 * m + 4) 0 c)⟩
  · rcases b with _ | c
    · exact ⟨_, step_C001_odd_b0 l m, Or.inl (hl (4 * m + 4) 0 1)⟩
    · exact ⟨_, step_C001_odd_b1 l m c, Or.inl (hl (4 * m + 3) 0 (c + 1))⟩
theorem step_D_succ_to_cfg_C001 (a b : Nat) :
    (cfg_D (a + 1) b) ⊢⁺ (cfg_C001 default a b) := by
  unfold cfg_D cfg_C001
  rw [list_pow_succ_right ([0, 1] : List (Fin 2)) a (([1] : List (Fin 2)) ^ b +> default)]
  dsimp [ListBlank.append]
  try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
    ListBlank.tail_default]
  bb_steps
theorem step_S_def_k0_jsucc_to_cfg_C001 (j c : Nat) :
    (cfg_A default 0 (j + 1) c) ⊢⁺ (cfg_C001 l_hat j c) := by
  unfold cfg_A cfg_C001 l_hat
  simp only [list_pow_zero, listblank_nil_app]
  rw [list_pow_succ_right ([0, 1] : List (Fin 2)) j (([1] : List (Fin 2)) ^ c +> default)]
  dsimp [HPow.hPow, ListBlank.append]
  try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
    ListBlank.tail_default]
  bb_steps
theorem step_S_hat_k0_jsucc (j c : Nat) :
    (cfg_A l_hat 0 (j + 1) c) ⊢⁺ (cfg_A default 6 (j + 1) c) := by
  unfold cfg_A l_hat
  simp only [list_pow_zero, listblank_nil_app]
  rw [list_pow_succ_right ([0, 1] : List (Fin 2)) j (([1] : List (Fin 2)) ^ c +> default)]
  dsimp [HPow.hPow, ListBlank.append]
  try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
    ListBlank.tail_default]
  bb_steps
theorem step_S_hat_k1_c0 (j : Nat) :
    (cfg_A l_hat 1 j 0) ⊢⁺ (cfg_A default 1 1 (2 * j + 5)) := by
  unfold cfg_A
  simp only [list_pow_zero, listblank_nil_app]
  have h1 : ((l_hat <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default)))
      ⊢⁺
      ((l_hat <+ [0]) {{C}}> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default))) := by
    dsimp [HPow.hPow, ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- list_pow_succ_right ([0, 1] : List (Fin 2)) j default] at h1
  have h2 := shift_C_right (j + 1) (l_hat <+ [0]) default
  rw [append_zero_pow_01 l_hat (j + 1)] at h2
  have h3 : (((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}> default)
      ⊢⁺
      ((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  have h4 := shift_C_left_10 (j + 1) l_hat (([1] : List (Fin 2)) ^ 3 +> default)
  rw [pow_11_eq_pow_1_mul2 (j + 1),
    <- list_pow_app_right ([1] : List (Fin 2)) (2 * (j + 1)) 3 default] at h4
  have hj : 2 * (j + 1) + 3 = 2 * j + 5 := by omega
  rw [hj] at h4
  have h5 : (l_hat {{C}}> ([1] +> (([1] : List (Fin 2)) ^ (2 * j + 5) +> default)))
      ⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([0, 1] : List (Fin 2)) ^ 1 +> (([1] : List (Fin 2)) ^ (2 * j + 5) +>
      default)))) := by
    unfold l_hat
    dsimp [HPow.hPow, ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5
theorem step_S_hat_k1_csucc_to_cfg_C001 (j c : Nat) :
    (cfg_A l_hat 1 j (c + 1)) ⊢⁺
    (cfg_C001 (default <+ ([1] : List (Fin 2)) ^ 3) (j + 1) c) := by
  unfold cfg_A cfg_C001
  rw [list_pow_succ_right ([1] : List (Fin 2)) c default]
  have h1 : ((l_hat <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      ⊢⁺
      ((l_hat <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [HPow.hPow, ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- list_pow_succ_right ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1) (l_hat <+ [0])
      ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_zero_pow_01 l_hat (j + 1)] at h2
  have h3 : (((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      ⊢⁺
      ((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  have h4 := shift_DC_left (j + 1) l_hat ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [pow_10_append_1 (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : (l_hat {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      ⊢⁺
      ((default <+ ([1] : List (Fin 2)) ^ 3) {{C}}>
        ([0, 0, 1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))) := by
    unfold l_hat
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5
theorem step_SL_stride3 (l : ListBlank (Fin 2)) (k j c : Nat) :
    (cfg_A l (k + 3) j (c + 1)) ⊢⁺ (cfg_A l k (j + 2) c) := by
  unfold cfg_A
  have hk : k + 3 = (k + 2) + 1 := by omega
  rw [hk, listblank_app_pow l ([1] : List (Fin 2)) (k + 2) 1,
    list_pow_succ_right ([1] : List (Fin 2)) c default]
  have h1 : (((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      ⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- list_pow_succ_right ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1) ((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ [0])
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_zero_pow_01 (l <+ ([1] : List (Fin 2)) ^ (k + 2)) (j + 1)] at h2
  have h3 : ((((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      ⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  have h4 := shift_DC_left (j + 1) (l <+ ([1] : List (Fin 2)) ^ (k + 2))
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [pow_10_append_1 (j + 1) (([1] : List (Fin 2)) ^ c +> default),
    listblank_app_pow l ([1] : List (Fin 2)) k 2] at h4
  have h5 : (((l <+ ([1] : List (Fin 2)) ^ k) <+ ([1] : List (Fin 2)) ^ 2) {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      ⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ k) {{D}}>
        ([1, 1] +> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- list_pow_succ_right ([0, 1] : List (Fin 2)) (j + 1) (([1] : List (Fin 2)) ^ c +>
    default)] at h5
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5
theorem step_SL_c0_k2 (l : ListBlank (Fin 2)) (k j : Nat) :
    (cfg_A l (k + 2) j 0) ⊢⁺ (cfg_A l k 0 (2 * j + 5)) := by
  unfold cfg_A
  simp only [list_pow_zero, listblank_nil_app]
  have hk : k + 2 = (k + 1) + 1 := by omega
  rw [hk, listblank_app_pow l ([1] : List (Fin 2)) (k + 1) 1]
  have h1 : (((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default)))
      ⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- list_pow_succ_right ([0, 1] : List (Fin 2)) j default] at h1
  have h2 := shift_C_right (j + 1) ((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ [0]) default
  rw [append_zero_pow_01 (l <+ ([1] : List (Fin 2)) ^ (k + 1)) (j + 1)] at h2
  have h3 : ((((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}> default)
      ⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  have h4 := shift_C_left_10 (j + 1) (l <+ ([1] : List (Fin 2)) ^ (k + 1))
      (([1] : List (Fin 2)) ^ 3 +> default)
  rw [pow_11_eq_pow_1_mul2 (j + 1),
    <- list_pow_app_right ([1] : List (Fin 2)) (2 * (j + 1)) 3 default,
    listblank_app_pow l ([1] : List (Fin 2)) k 1] at h4
  have hj : 2 * (j + 1) + 3 = 2 * j + 5 := by omega
  rw [hj] at h4
  have h5 : (((l <+ ([1] : List (Fin 2)) ^ k) <+ ([1] : List (Fin 2)) ^ 1) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * j + 5) +> default)))
      ⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ k) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ (2 * j + 5) +> default))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5
theorem step_S_k1_c0 (j : Nat) :
    (cfg_A default 1 j 0) ⊢⁺ (cfg_A default 0 0 (2 * j + 3)) := by
  unfold cfg_A
  simp only [list_pow_zero, listblank_nil_app]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default)))
      ⊢⁺
      ((default : ListBlank (Fin 2)) {{C}}> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +>
      default))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- list_pow_succ_right ([0, 1] : List (Fin 2)) j default] at h1
  have h2 := shift_C_right (j + 1) default default
  have h12 := ReachesPlus.trans_star h1 h2
  have hj1 : j + 1 = 1 + j := by omega
  rw [hj1, listblank_app_pow default ([0, 1] : List (Fin 2)) 1 j] at h12
  change (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default))) ⊢⁺
      ((((default <+ ([1] : List (Fin 2)) ^ 1) <+ [0]) <+ ([0,
      1] : List (Fin 2)) ^ j) {{C}}> default) at h12
  rw [append_zero_pow_01 (default <+ ([1] : List (Fin 2)) ^ 1) j] at h12
  have h3 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ j) <+ [0]) {{C}}> default)
      ⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ j) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  have h4 := shift_C_left_10 j ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1)
      (([1] : List (Fin 2)) ^ 3 +> default)
  rw [pow_11_eq_pow_1_mul2 j,
    <- list_pow_app_right ([1] : List (Fin 2)) (2 * j) 3 default] at h4
  have h5 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * j + 3) +> default)))
      ⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ (2 * j + 3) +> default))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans h12 h3) h4) h5
theorem step_S_k1_csucc (j c : Nat) :
    (cfg_A default 1 j (c + 1)) ⊢⁺ (cfg_D (j + 2) c) := by
  unfold cfg_A cfg_D
  rw [list_pow_succ_right ([1] : List (Fin 2)) c default]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      ⊢⁺
      ((default : ListBlank (Fin 2)) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- list_pow_succ_right ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1) default ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [default_pow_01 (j + 1)] at h2
  have h3 : ((((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      ⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  have h4 := shift_DC_left (j + 1) default ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [pow_10_append_1 (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : ([0] : List (Fin 2)) +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +>
      (([1] : List (Fin 2)) ^ c +> default))) =
      ([0, 1] : List (Fin 2)) ^ (j + 2) +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [list_pow_succ_right ([0, 1] : List (Fin 2)) (j + 1)]
    rfl
  rw [h5] at h4
  exact ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3) h4
theorem step_S_k2_csucc (j c : Nat) :
    (cfg_A default 2 j (c + 1)) ⊢⁺ (cfg_D (j + 3) c) := by
  unfold cfg_A cfg_D
  rw [list_pow_succ_right ([1] : List (Fin 2)) c default]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      ⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- list_pow_succ_right ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1)
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ [0])
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) (j + 1)] at h2
  have h3 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      ⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  have h4 := shift_DC_left (j + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1)
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [pow_10_append_1 (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      ⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}>
        (([0, 1] : List (Fin 2)) ^ 2 +> (([0, 1] : List (Fin 2)) ^ (j + 1) +>
      (([1] : List (Fin 2)) ^ c +> default)))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- list_pow_app_right ([0, 1] : List (Fin 2)) 2 (j + 1) (([1] : List (Fin 2)) ^ c +>
    default)] at h5
  have hj : 2 + (j + 1) = j + 3 := by omega
  rw [hj] at h5
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5
theorem step_S_k0_j0 (c : Nat) :
    (cfg_A default 0 0 c) ⊢⁺ (cfg_D 1 (c + 2)) := by
  unfold cfg_A cfg_D
  rw [Nat.add_comm c 2, list_pow_app_right ([1] : List (Fin 2)) 2 c default]
  dsimp [HPow.hPow, ListBlank.append]
  try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
    ListBlank.tail_default]
  bb_steps
theorem step_SL_hat_k2_csucc (j c : Nat) :
    (cfg_A l_hat 2 j (c + 1)) ⊢⁺ (cfg_A default 1 (j + 3) c) := by
  unfold cfg_A l_hat
  rw [list_pow_succ_right ([1] : List (Fin 2)) c default]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List
      (Fin 2)) ^ 2) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      ⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin
      2)) ^ 1) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- list_pow_succ_right ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1)
    (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin 2))
      ^ 1) <+ [0])
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_zero_pow_01 ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+
      ([1] : List (Fin 2)) ^ 1) (j + 1)] at h2
  have h3 : ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List
      (Fin 2)) ^ 1) <+
      ([1, 0] : List (Fin 2)) ^ (j + 1) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      ⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin
      2)) ^ 1) <+
        ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  have h4 := shift_DC_left (j + 1)
    ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin 2)) ^
      1)
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [pow_10_append_1 (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List
      (Fin 2)) ^ 1) {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      ⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([0, 1] : List (Fin 2)) ^ 2 +> (([0, 1] : List (Fin 2)) ^ (j + 1) +>
      (([1] : List (Fin 2)) ^ c +> default))))) := by
    dsimp [ListBlank.append]
    try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
      ListBlank.tail_default]
    bb_steps
  rw [<- list_pow_app_right ([0, 1] : List (Fin 2)) 2 (j + 1) (([1] : List (Fin 2)) ^ c +>
    default)] at h5
  have hj : 2 + (j + 1) = j + 3 := by omega
  rw [hj] at h5
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5
theorem step_SL_hat_k0_j0 (c : Nat) :
    (cfg_A l_hat 0 0 c) ⊢⁺ (cfg_A default 2 0 (c + 2)) := by
  unfold cfg_A l_hat
  rw [Nat.add_comm c 2, list_pow_app_right ([1] : List (Fin 2)) 2 c default]
  dsimp [HPow.hPow, ListBlank.append]
  try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
    ListBlank.tail_default]
  bb_steps
theorem init_to_cfg_D : (init []) ⊢⁺ (cfg_D 1 1) := by
  unfold init cfg_D
  simp only [Tape.mk₁, list_pow_zero, list_pow_succ]
  try dsimp only [ListBlank.append, ListBlank.cons_zero_default, ListBlank.head_default,
    ListBlank.tail_default]
  bb_steps
theorem init_reaches_S : (init []) ⊢* (cfg_A default 2 0 0) :=
  ReachesPlus.to_star
    (ReachesPlus.trans (ReachesPlus.trans init_to_cfg_D (step_D_succ_to_cfg_C001 0 1))
      (step_C001_even_b1 default 0))
theorem step_S_def_all (k j c : Nat) :
    ∃ cfg', ((cfg_A default k j c) ⊢⁺ cfg') /\
            (IsInPatternSet ps cfg' \/ (step target cfg').isNone) := by
  rcases k with _ | _ | _ | k'
  · rcases j with _ | j'
    · have h12 := ReachesPlus.trans (step_S_k0_j0 c) (step_D_succ_to_cfg_C001 0 (c + 2))
      obtain ⟨cfg', h3, h_end⟩ := step_C001_all default in_ps_S_def 0 (c + 2)
      exact ⟨cfg', ReachesPlus.trans h12 h3, h_end⟩
    · have h1 := step_S_def_k0_jsucc_to_cfg_C001 j' c
      obtain ⟨cfg', h2, h_end⟩ := step_C001_all l_hat in_ps_S_hat j' c
      exact ⟨cfg', ReachesPlus.trans h1 h2, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_S_k1_c0 j, Or.inl (in_ps_S_def 0 0 (2 * j + 3))⟩
    · have h12 := ReachesPlus.trans (step_S_k1_csucc j c') (step_D_succ_to_cfg_C001 (j + 1) c')
      obtain ⟨cfg', h3, h_end⟩ := step_C001_all default in_ps_S_def (j + 1) c'
      exact ⟨cfg', ReachesPlus.trans h12 h3, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 default 0 j, Or.inl (in_ps_S_def 0 0 (2 * j + 5))⟩
    · have h12 := ReachesPlus.trans (step_S_k2_csucc j c') (step_D_succ_to_cfg_C001 (j + 2) c')
      obtain ⟨cfg', h3, h_end⟩ := step_C001_all default in_ps_S_def (j + 2) c'
      exact ⟨cfg', ReachesPlus.trans h12 h3, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 default (k' + 1) j, Or.inl (in_ps_S_def (k' + 1) 0 (2 * j + 5))⟩
    · exact ⟨_, step_SL_stride3 default k' j c', Or.inl (in_ps_S_def k' (j + 2) c')⟩
theorem step_S_hat_all (k j c : Nat) :
    ∃ cfg', ((cfg_A l_hat k j c) ⊢⁺ cfg') /\
            (IsInPatternSet ps cfg' \/ (step target cfg').isNone) := by
  rcases k with _ | _ | _ | k'
  · rcases j with _ | j'
    · exact ⟨_, step_SL_hat_k0_j0 c, Or.inl (in_ps_S_def 2 0 (c + 2))⟩
    · exact ⟨_, step_S_hat_k0_jsucc j' c, Or.inl (in_ps_S_def 6 (j' + 1) c)⟩
  · rcases c with _ | c'
    · exact ⟨_, step_S_hat_k1_c0 j, Or.inl (in_ps_S_def 1 1 (2 * j + 5))⟩
    · have h1 := step_S_hat_k1_csucc_to_cfg_C001 j c'
      obtain ⟨cfg', h2,
      h_end⟩ := step_C001_all (default <+ ([1] : List (Fin 2)) ^ 3) in_ps_S_ones3 (j + 1) c'
      exact ⟨cfg', ReachesPlus.trans h1 h2, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 l_hat 0 j, Or.inl (in_ps_S_hat 0 0 (2 * j + 5))⟩
    · exact ⟨_, step_SL_hat_k2_csucc j c', Or.inl (in_ps_S_def 1 (j + 3) c')⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 l_hat (k' + 1) j, Or.inl (in_ps_S_hat (k' + 1) 0 (2 * j + 5))⟩
    · exact ⟨_, step_SL_stride3 l_hat k' j c', Or.inl (in_ps_S_hat k' (j + 2) c')⟩


theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A default 2 0 0, init_reaches_S, in_ps_S_def 2 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · rw [eval_pat_A]
    change ¬ (vars 1 >= 2) at h_cond
    have hp : vars 1 = 0 ∨ vars 1 = 1 := by omega
    rcases hp with h0 | h1
    · rw [h0]
      exact step_S_def_all (vars 0) (vars 2) (vars 3)
    · rw [h1]
      exact step_S_hat_all (vars 0) (vars 2) (vars 3)
  · nomatch h_mem
theorem has_collatz_reduction : HasCollatzReduction target := ⟨ps, is_closed_pattern_set⟩

end BusyBeaver.M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD
