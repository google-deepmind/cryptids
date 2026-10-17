/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Relation
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`

## Collatz-like Acceleration Rules
A canonical configuration accelerates:
```
def cfg_A (b k c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))
    (ListBlank.append [0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
      (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
```
-/

@[expose] public section


namespace BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC

open SixState Turing

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC"

abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

notation3 c₁ " [" M "]⊢ " c₂ => step M c₁ = some c₂
notation3 c₁ " [" M "]⊢^{" n "} " c₂ => multiStep M c₁ n = some c₂
notation3 c₁ " [" M "]⊢* " c₂ => ∃ n, multiStep M c₁ n = some c₂
notation3 c₁ " [" M "]⊢⁺ " c₂ => ∃ n > 0, multiStep M c₁ n = some c₂

notation l " {{" s "}} " r => (⟨s, l, r⟩ : Tape _)
notation:67 s:67 " << " a:68 => ListBlank.cons a s
infixr:67 " >> " => ListBlank.cons
notation:67 s:67 " <+ " l:68 => ListBlank.append l s
infixr:67 " +> " => ListBlank.append
notation3 l " {{" q "}}> " r => (⟨some q, ⟨ListBlank.head r, l, ListBlank.tail r⟩⟩ : Cfg _ _)
notation3 l " <{{" q "}} " r => (⟨some q, ⟨ListBlank.head l, ListBlank.tail l, r⟩⟩ : Cfg _ _)

@[simp]
def list_nat_repeat (l : List Γ) (n : Nat) := match n with
  | 0 => []
  | n + 1 => List.append l (list_nat_repeat l n)

local instance instHPowListNat : HPow (List Γ) Nat (List Γ) := ⟨list_nat_repeat⟩

omit [Inhabited Γ] in
@[simp] lemma bb_hpow_eq_local_hpow (l : List Γ) (n : ℕ) :
  @HPow.hPow _ _ _ BusyBeaver.instHPowListNat l n = l ^ n := by
  change (List.replicate n l).flatten = list_nat_repeat l n
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold list_nat_repeat
    rw [List.replicate_succ, List.flatten_cons, ih]
    rfl




-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

def holdout_0082_mod : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 0 => none
  | 3, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 4, Stmt.write 0 Dir.left)
@[simp] lemma zMz (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] lemma zPz (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma zPsl (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma zCal (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma zAnl (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma zLan (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma zLac (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x >>
    (xs +> b) := rfl
@[simp] lemma zZcd : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma zDt : (default : ListBlank (Fin 2)).tail = default := rfl
omit [Inhabited Γ] in
@[simp]
theorem zLpa (l : List Γ) (n m : Nat) : l^(n + m) = l^n ++ l^m := match m with
  | 0 => by simp_rw [HPow.hPow, add_zero, list_nat_repeat, List.append_nil]
  | m + 1 => by
    rw [add_comm m 1, <- add_assoc, add_comm 1 m, zLpa]
    simp only [HPow.hPow, list_nat_repeat, List.append_eq, List.append_assoc]
    rw [<- List.append_assoc, <- List.append_assoc, List.append_cancel_right_eq]
    induction n with
    | zero => simp
    | succ n ih => simpa
omit [Inhabited Γ] in
theorem zLpc (l : List Γ) (n m : Nat) : l^n ++ l^m = l^m ++ l^n := by
  rw [<- zLpa, add_comm, zLpa]
lemma zLaa (s : ListBlank Γ) (l₁ l₂ : List Γ) :
    (s <+ l₁) <+ l₂ = s <+ (l₂ ++ l₁) := by
  unfold ListBlank.append
  split
  · split
    · next h => simp_all
    · simp_all
  · rename_i _ l₂ l₁
    refine (congr_arg _ ?_).symm
    exact ListBlank.append_assoc l₁ _ s
lemma zLp1 (u : List (Fin 2)) (k : Nat) :
    u^k ++ u = u^(k + 1) := by
  have h := zLpc u k 1
  dsimp [HPow.hPow, list_nat_repeat] at h ⊢
  rw [List.append_nil] at h
  exact h
lemma zPar (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [zLpa, <- zLaa]
lemma zPsr (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [zPsl, <- zLaa]
lemma zPl (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [zLaa, <- zLpa, add_comm]
lemma zPa1 (u : List (Fin 2)) (k : Nat) (r : ListBlank (Fin 2)) :
    (u ^ k) +> (u +> r) = (u ^ (k + 1)) +> r := by
  rw [zLaa, zLp1]
lemma zPal (l : ListBlank (Fin 2)) (u : List (Fin 2)) (k : Nat) :
    (l <+ u) <+ (u ^ k) = l <+ (u ^ (k + 1)) := by
  rw [zLaa, zLp1]
lemma append_zero_pow_01 (s : ListBlank (Fin 2)) (k : Nat) :
    (s <+ [0]) <+ ([0, 1] : List (Fin 2)) ^ k = (s <+ ([1, 0] : List (Fin 2)) ^ k) <+ [0] := by
  induction k with
  | zero =>
    simp only [zPz, zLan]
  | succ k ih =>
    rw [zPl (s <+ [0]) [0, 1] k 1, ih]
    have h1 : ((s <+ ([1, 0] : List (Fin 2)) ^ k) <+ [0]) <+ ([0, 1] : List (Fin 2)) ^ 1 =
        ((s <+ ([1, 0] : List (Fin 2)) ^ k) <+ ([1, 0] : List (Fin 2)) ^ 1) <+ [0] := rfl
    rw [h1, <- zPl s [1, 0] k 1]
lemma default_pow_01 (c : Nat) :
    (default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ c =
    (default <+ ([1, 0] : List (Fin 2)) ^ c) <+ [0] := by
  have h0 : (default : ListBlank (Fin 2)) = default <+ [0] := zZcd.symm
  conv_lhs => rw [h0]
  exact append_zero_pow_01 default c
lemma append_one_pow_10 (s : ListBlank (Fin 2)) (k : Nat) :
    (s <+ [1]) <+ ([1, 0] : List (Fin 2)) ^ k = (s <+ ([0, 1] : List (Fin 2)) ^ k) <+ [1] := by
  induction k with
  | zero =>
    simp only [zPz, zLan]
  | succ k ih =>
    rw [zPl (s <+ [1]) [1, 0] k 1, ih]
    have h1 : ((s <+ ([0, 1] : List (Fin 2)) ^ k) <+ [1]) <+ ([1, 0] : List (Fin 2)) ^ 1 =
        ((s <+ ([0, 1] : List (Fin 2)) ^ k) <+ ([0, 1] : List (Fin 2)) ^ 1) <+ [1] := rfl
    rw [h1, <- zPl s [0, 1] k 1]
lemma pow_11_eq_pow_1_mul2 (k : Nat) :
    ([1, 1] : List (Fin 2)) ^ k = ([1] : List (Fin 2)) ^ (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [zPsl, ih, h2, zLpa]
    rfl
lemma pow_01_append_0 (k : Nat) (r : ListBlank (Fin 2)) :
    (([0, 1] : List (Fin 2)) ^ k) +> ([0] +> r) =
    [0] +> ((([1, 0] : List (Fin 2)) ^ k) +> r) := by
  induction k generalizing r with
  | zero =>
    simp only [zPz, zLan]
  | succ k ih =>
    rw [zPsr, ih]
    have h1 : ([0, 1] : List (Fin 2)) +> ([0] +> ((([1, 0] : List (Fin 2)) ^ k) +> r)) =
        [0] +> (([1, 0] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ k) +> r)) := rfl
    rw [h1, <- zPsr]
lemma zSm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c_1 c_2 : Cfg Γ Λ) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
lemma step_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c_1 c_2 : Cfg Γ Λ) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢* c_2 := ⟨1, zSm tm c_1 c_2 h⟩
lemma zSp2 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c_1 c_2 : Cfg Γ Λ) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1, by decide, zSm tm c_1 c_2 h⟩
lemma zMa {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c_1 : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c_1 c_2 c_3 : Cfg Γ Λ) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa, h₁]; simp [h₂]
lemma zSt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢* c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPs {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 : Cfg Γ Λ} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma zPsp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zSpp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 :=
  zPsp h₁ (zPs h₂)
lemma zSsp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  zPsp (zSp2 tm c_1 c_2 h₁) h₂
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine zSsp (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    Tape.write, zZcd, zDh, zDt])
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;>
    (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals
    (first | finish | step)))
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)
lemma shift_E_ones_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (([1] : List (Fin 2)) ^ k +> r)) [holdout_0082_mod]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ k) {{E}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsr]
    have h1 : (l {{E}}> ([1] +> (([1] : List (Fin 2)) ^ k +> r)))
        [holdout_0082_mod]⊢*
        ((l <+ [1]) {{E}}> (([1] : List (Fin 2)) ^ k +> r)) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih (l <+ [1]) r
    rw [zPal] at h2
    exact zSt h1 h2
lemma shift_CB_left_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> ([1] +> r)) [holdout_0082_mod]⊢*
    (l {{C}}> ([1] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsl, <- zLaa]
    have h1 : (((l <+ ([0, 1] : List (Fin 2)) ^ k) <+ [0, 1]) {{C}}> ([1] +> r))
        [holdout_0082_mod]⊢*
        ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> ([1] +> ([1, 1] +> r))) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    rw [zPa1] at h2
    exact zSt h1 h2
lemma shift_D_right_100_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) [holdout_0082_mod]⊢*
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}> ([1, 0, 0] +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsr]
    have h1 : (l {{D}}> ([1, 0, 0] +> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
        [holdout_0082_mod]⊢*
        ((l <+ [0, 1]) {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih (l <+ [0, 1]) r
    rw [zPal] at h2
    exact zSt h1 h2
lemma shift_FA_left_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{F}}> ([0] +> r)) [holdout_0082_mod]⊢*
    (l {{F}}> ([0] +> (([0, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsl, <- zLaa]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) {{F}}> ([0] +> r))
        [holdout_0082_mod]⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{F}}> ([0] +> ([0, 1] +> r))) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih l (([0, 1] : List (Fin 2)) +> r)
    rw [zPa1] at h2
    exact zSt h1 h2
def E_0082 (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ a)
    {{E}}> default
def F_R (b k : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k)
    {{F}}>
    ([0, 0] +> r)
def F_0082 (b k c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k)
    {{F}}>
    ([0, 0] +> (([1] : List (Fin 2)) ^ c +> default))
lemma F_0082_eq_F_R (b k c : Nat) :
    F_0082 b k c = F_R b k (([1] : List (Fin 2)) ^ c +> default) := rfl
def Closes (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ cfg', (cfg [holdout_0082_mod]⊢⁺ cfg') /\
          ((∃ b k c, cfg' = F_0082 b k c) \/ (step holdout_0082_mod cfg').isNone)
lemma in_ps_F (b k c : Nat) : ∃ b' k' c', F_0082 b k c = F_0082 b' k' c' :=
  ⟨b, k, c, rfl⟩
lemma closes_of_in_ps {cfg cfg' : Cfg (Fin 2) (Fin 6)}
    (h_step : cfg [holdout_0082_mod]⊢⁺ cfg') (h_in : ∃ b k c, cfg' = F_0082 b k c) :
    Closes cfg :=
  ⟨cfg', h_step, Or.inl h_in⟩
lemma closes_of_halt {cfg cfg' : Cfg (Fin 2) (Fin 6)}
    (h_step : cfg [holdout_0082_mod]⊢⁺ cfg') (h_halt : (step holdout_0082_mod cfg').isNone) :
    Closes cfg :=
  ⟨cfg', h_step, Or.inr h_halt⟩
lemma closes_of_stepPlus {cfg₁ cfg₂ : Cfg (Fin 2) (Fin 6)}
    (h_step : cfg₁ [holdout_0082_mod]⊢⁺ cfg₂) (h_close : Closes cfg₂) :
    Closes cfg₁ := by
  rcases h_close with ⟨cfg', h_step', h_end⟩
  exact ⟨cfg', zPt h_step h_step', h_end⟩
lemma closes_of_stepStar {cfg₁ cfg₂ : Cfg (Fin 2) (Fin 6)}
    (h_step : cfg₁ [holdout_0082_mod]⊢* cfg₂) (h_close : Closes cfg₂) :
    Closes cfg₁ := by
  rcases h_close with ⟨cfg', h_step', h_end⟩
  exact ⟨cfg', zSpp h_step h_step', h_end⟩
theorem init_to_E_0082 : (init []) [holdout_0082_mod]⊢⁺ (E_0082 0 4) := by
  unfold init E_0082
  simp only [Tape.mk₁, zPz, zPsl, zCal, zAnl,
    zLan, zLac]
  execute
theorem step_E_b0_0082 (a : Nat) :
    (E_0082 a 0) [holdout_0082_mod]⊢⁺ (E_0082 0 (2 * a + 4)) := by
  unfold E_0082
  simp only [zPz, zLan]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ a) {{E}}> default)
      [holdout_0082_mod]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ a) <+ [0]) {{C}}> ([1] +> ([1]
    +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- default_pow_01 a] at h1
  have h2 := shift_CB_left_0082 a default ([1] +> default)
  rw [pow_11_eq_pow_1_mul2 a] at h2
  have h3 : ((default : ListBlank (Fin 2)) {{C}}> ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1]
    +> default))))
      [holdout_0082_mod]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) {{E}}>
        ((([1] : List (Fin 2)) ^ (2 * a)) +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- zPar ([1] : List (Fin 2)) (2 * a) 1 default] at h3
  have h4 := shift_E_ones_0082 (2 * a + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2))
    ^ 3) default
  rw [<- zPl default ([1] : List (Fin 2)) 3 (2 * a + 1)] at h4
  have ha : 3 + (2 * a + 1) = 2 * a + 4 := by omega
  rw [ha] at h4
  exact zPsp (zPt (zPsp h1 h2) h3) h4
theorem step_E_b1_0082 (a : Nat) :
    (E_0082 a 1) [holdout_0082_mod]⊢⁺ (E_0082 0 (2 * a + 6)) := by
  unfold E_0082
  simp only [zPz, zLan]
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1, 0] : List (Fin
    2)) ^ a) {{E}}> default)
      [holdout_0082_mod]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1, 0] : List (Fin 2)) ^
    a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) a] at h1
  have h2 := shift_CB_left_0082 a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+
    [0]) ([1] +> default)
  rw [pow_11_eq_pow_1_mul2 a] at h2
  have h3 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [holdout_0082_mod]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{E}}>
        ((([1] : List (Fin 2)) ^ (2 * a)) +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- zPar ([1] : List (Fin 2)) (2 * a) 1 default] at h3
  have h4 := shift_E_ones_0082 (2 * a + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2))
    ^ 5) default
  rw [<- zPl default ([1] : List (Fin 2)) 5 (2 * a + 1)] at h4
  have ha : 5 + (2 * a + 1) = 2 * a + 6 := by omega
  rw [ha] at h4
  exact zPsp (zPt (zPsp h1 h2) h3) h4
theorem step_E_b2_to_D_halt_0082 (a : Nat) :
    (E_0082 a 2) [holdout_0082_mod]⊢⁺
    ((default : ListBlank (Fin 2)) {{D}}> ([0, 0] +> (([1] : List (Fin 2)) ^ (2 * a + 4) +>
    default))) := by
  unfold E_0082
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ ([1, 0] : List (Fin
    2)) ^ a) {{E}}> default)
      [holdout_0082_mod]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ ([1, 0] : List (Fin 2)) ^
    a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) a] at h1
  have h2 := shift_CB_left_0082 a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+
    [0]) ([1] +> default)
  rw [pow_11_eq_pow_1_mul2 a] at h2
  have h3 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [holdout_0082_mod]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}>
        ([0, 0] +> (([1] : List (Fin 2)) ^ 3 +> (([1] : List (Fin 2)) ^ (2 * a) +> (([1] : List
    (Fin 2)) ^ 1 +> default))))) := by
    dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
    execute
  rw [<- zPar ([1] : List (Fin 2)) (2 * a) 1 default,
    <- zPar ([1] : List (Fin 2)) 3 (2 * a + 1) default] at h3
  have ha : 3 + (2 * a + 1) = 2 * a + 4 := by omega
  rw [ha] at h3
  exact zPt (zPsp h1 h2) h3
theorem step_E_b3_to_F_0082 (a b : Nat) :
    (E_0082 a (b + 3)) [holdout_0082_mod]⊢⁺ (F_0082 (b + 1) 0 (2 * a + 3)) := by
  unfold E_0082 F_0082
  simp only [zPz, zLan]
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) <+ ([1, 0] : List
    (Fin 2)) ^ a) {{E}}> default)
      [holdout_0082_mod]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) <+ ([1, 0] : List (Fin
    2)) ^ a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) a]
    at h1
  have h2 := shift_CB_left_0082 a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b +
    3)) <+ [0]) ([1] +> default)
  rw [pow_11_eq_pow_1_mul2 a] at h2
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, zPl default ([1] : List (Fin 2)) (b + 1) 2] at h1 h2
  have h3 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1] : List
    (Fin 2)) ^ 2) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [holdout_0082_mod]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) {{F}}>
        ([0, 0] +> (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * a) +> (([1] : List
    (Fin 2)) ^ 1 +> default))))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- zPar ([1] : List (Fin 2)) (2 * a) 1 default,
    <- zPar ([1] : List (Fin 2)) 2 (2 * a + 1) default] at h3
  have ha : 2 + (2 * a + 1) = 2 * a + 3 := by omega
  rw [ha] at h3
  exact zPt (zPsp h1 h2) h3
theorem step_F_b2_k0_0082 (c : Nat) :
    (F_0082 2 0 (c + 1)) [holdout_0082_mod]⊢⁺ (F_0082 5 0 c) := by
  unfold F_0082
  rw [zPsr ([1] : List (Fin 2)) c default]
  dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
  execute
theorem init_reaches_F_502 :
    (init []) [holdout_0082_mod]⊢* (F_0082 5 0 2) :=
  zPs
    (zPt init_to_E_0082
      (zPt (step_E_b3_to_F_0082 0 1) (step_F_b2_k0_0082 2)))
lemma isNone_step_D_00 (l r : ListBlank (Fin 2)) :
    (step holdout_0082_mod (l {{D}}> ([0, 0] +> r))).isNone = true := by
  simp only [step, D, holdout_0082_mod, zLac, zLan,
    Turing.ListBlank.head_cons]
  rfl
lemma closes_E (a b : Nat) : Closes (E_0082 a b) := by
  rcases b with _ | _ | _ | b'
  · have h1 := step_E_b0_0082 a
    have hb : 2 * a + 4 = (2 * a + 1) + 3 := by omega
    rw [hb] at h1
    exact closes_of_in_ps (zPt h1 (step_E_b3_to_F_0082 0 (2 * a + 1)))
      (in_ps_F (2 * a + 2) 0 3)
  · have h1 := step_E_b1_0082 a
    have hb : 2 * a + 6 = (2 * a + 3) + 3 := by omega
    rw [hb] at h1
    exact closes_of_in_ps (zPt h1 (step_E_b3_to_F_0082 0 (2 * a + 3)))
      (in_ps_F (2 * a + 4) 0 3)
  · exact closes_of_halt (step_E_b2_to_D_halt_0082 a) (isNone_step_D_00 _ _)
  · exact closes_of_in_ps (step_E_b3_to_F_0082 a b') (in_ps_F (b' + 1) 0 (2 * a + 3))
def D100 (b k : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k) <+
    [0]) {{D}}>
    ([1, 0, 0] +> r)
def C_bounce (b : Nat) (s : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) {{C}}> ([1] +> s)
lemma step_F0_sweep_right_0082 (k : Nat) (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{F}}> ([0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))
    [holdout_0082_mod]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}> ([1, 0, 0] +> r)) := by
  have h1 : ((default : ListBlank (Fin 2)) {{F}}> ([0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))
      [holdout_0082_mod]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
    dsimp [ListBlank.append]
    execute
  have h2 := shift_D_right_100_0082 k default r
  exact zPsp h1 h2
lemma F_R_b0_to_D100 (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 0 k r) [holdout_0082_mod]⊢⁺ (D100 0 k r) := by
  unfold F_R D100
  simp only [zPz, zLan]
  have h1 := shift_FA_left_0082 k default ([0] +> r)
  rw [pow_01_append_0 k r] at h1
  have h2 := step_F0_sweep_right_0082 k r
  rw [default_pow_01 k] at h2
  exact zSpp h1 h2
lemma F_R_b1_to_D100 (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 1 k r) [holdout_0082_mod]⊢⁺ (D100 0 (k + 1) r) := by
  unfold F_R D100
  simp only [zPz, zLan]
  have h1 := shift_FA_left_0082 k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) ([0]
    +> r)
  rw [pow_01_append_0 k r] at h1
  have h2 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{F}}>
      ([0] +> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
      [holdout_0082_mod]⊢⁺
      ((default : ListBlank (Fin 2)) {{F}}>
        ([0, 0] +> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))) := by
    dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
    execute
  rw [<- zPsr ([1, 0] : List (Fin 2)) k r] at h2
  have h3 := step_F0_sweep_right_0082 (k + 1) r
  rw [default_pow_01 (k + 1)] at h3
  exact zPt (zSpp h1 h2) h3
lemma F_R_b3_to_D100 (b k : Nat) (r : ListBlank (Fin 2)) :
    (F_R (b + 3) k r) [holdout_0082_mod]⊢⁺ (D100 (b + 1) k r) := by
  unfold F_R D100
  have h1 := shift_FA_left_0082 k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b +
    3)) ([0] +> r)
  rw [pow_01_append_0 k r] at h1
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, zPl default ([1] : List (Fin 2)) (b + 1) 2] at h1
  have h2 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1] : List
    (Fin 2)) ^ 2) {{F}}>
      ([0] +> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
      [holdout_0082_mod]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ [0]) {{D}}>
        ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
    dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
    execute
  have h3 := shift_D_right_100_0082 k
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ [0]) r
  rw [append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) k] at h3
  exact zPsp (zSpp h1 h2) h3
lemma D100_0_11 (k : Nat) (r : ListBlank (Fin 2)) :
    (D100 0 k ([1, 1] +> r)) [holdout_0082_mod]⊢⁺ (F_R 1 (k + 1) r) := by
  unfold D100 F_R
  simp only [zPz, zLan]
  rw [<- default_pow_01 k]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([1, 1] +> r)))
      [holdout_0082_mod]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) <+ ([0, 1] : List (Fin 2))
    ^ 1) <+ [1]) {{F}}>
        ([0, 0] +> r)) := by
    dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
    execute
  rw [<- zPl default ([0, 1] : List (Fin 2)) k 1,
    <- append_one_pow_10 default (k + 1)] at h1
  exact h1
lemma D100_succ_11 (b k : Nat) (r : ListBlank (Fin 2)) :
    (D100 (b + 1) k ([1, 1] +> r)) [holdout_0082_mod]⊢⁺ (F_R (b + 1) (k + 2) r) := by
  unfold D100 F_R
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1, 0] : List
    (Fin 2)) ^ k) <+ [0]) {{D}}>
      ([1, 0, 0] +> ([1, 1] +> r)))
      [holdout_0082_mod]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1, 0] : List (Fin
    2)) ^ k) <+
        ([1, 0] : List (Fin 2)) ^ 2) {{F}}>
        ([0, 0] +> r)) := by
    dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
    execute
  rw [<- zPl ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) ([1, 0] : List (Fin
    2)) k 2] at h1
  exact h1
lemma D100_nil_to_C_bounce (b k : Nat) :
    (D100 b k default) [holdout_0082_mod]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 3) +> default)) := by
  unfold D100 C_bounce
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) k]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
    List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> default))
      [holdout_0082_mod]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
    (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 1) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
    execute
  rw [<- zPl (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) ([0, 1] : List
    (Fin 2)) k 1] at h1
  have h2 := shift_CB_left_0082 (k + 1) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
    b) <+ [0])
    (([1] : List (Fin 2)) ^ 1 +> default)
  rw [pow_11_eq_pow_1_mul2 (k + 1),
    <- zPar ([1] : List (Fin 2)) (2 * (k + 1)) 1 default] at h2
  have hk : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  rw [hk] at h2
  exact zPsp h1 h2
lemma D100_one_to_C_bounce (b k : Nat) :
    (D100 b k ([1] +> default)) [holdout_0082_mod]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 5) +> default)) := by
  unfold D100 C_bounce
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) k]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
    List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([1] +> default)))
      [holdout_0082_mod]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
    (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 2) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
    execute
  rw [<- zPl (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) ([0, 1] : List
    (Fin 2)) k 2] at h1
  have h2 := shift_CB_left_0082 (k + 2) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
    b) <+ [0])
    (([1] : List (Fin 2)) ^ 1 +> default)
  rw [pow_11_eq_pow_1_mul2 (k + 2),
    <- zPar ([1] : List (Fin 2)) (2 * (k + 2)) 1 default] at h2
  have hk : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
  rw [hk] at h2
  exact zPsp h1 h2
lemma D100_01_to_C_bounce (b k : Nat) (r : ListBlank (Fin 2)) :
    (D100 b k ([0, 1] +> r)) [holdout_0082_mod]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 4) +> r)) := by
  unfold D100 C_bounce
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) k]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
    List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([0, 1] +> r)))
      [holdout_0082_mod]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
    (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 1) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 2 +> r))) := by
    dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
    execute
  rw [<- zPl (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) ([0, 1] : List
    (Fin 2)) k 1] at h1
  have h2 := shift_CB_left_0082 (k + 1) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
    b) <+ [0])
    (([1] : List (Fin 2)) ^ 2 +> r)
  rw [pow_11_eq_pow_1_mul2 (k + 1),
    <- zPar ([1] : List (Fin 2)) (2 * (k + 1)) 2 r] at h2
  have hk : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
  rw [hk] at h2
  exact zPsp h1 h2
lemma C_bounce_0 (s : ListBlank (Fin 2)) :
    (C_bounce 0 s) [holdout_0082_mod]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) {{E}}> s) := by
  unfold C_bounce
  simp only [zPz, zLan]
  dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
  execute
lemma C_bounce_1 (s : ListBlank (Fin 2)) :
    (C_bounce 1 s) [holdout_0082_mod]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{E}}> s) := by
  unfold C_bounce
  dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
  execute
lemma C_bounce_2 (s : ListBlank (Fin 2)) :
    (C_bounce 2 s) [holdout_0082_mod]⊢⁺
    ((default : ListBlank (Fin 2)) {{D}}> ([0, 0] +> (([1] : List (Fin 2)) ^ 3 +> s))) := by
  unfold C_bounce
  dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
  execute
lemma C_bounce_3 (b : Nat) (s : ListBlank (Fin 2)) :
    (C_bounce (b + 3) s) [holdout_0082_mod]⊢⁺
    (F_R (b + 1) 0 (([1] : List (Fin 2)) ^ 2 +> s)) := by
  unfold C_bounce F_R
  simp only [zPz, zLan]
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, zPl default ([1] : List (Fin 2)) (b + 1) 2]
  dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
  execute
lemma step_F_ksucc_c0 (b k : Nat) :
    (F_0082 b (k + 1) 0) [holdout_0082_mod]⊢⁺ (F_0082 b k 1) := by
  unfold F_0082
  rw [zPl ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) ([1, 0] : List (Fin 2)) k 1]
  dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
  execute
lemma step_F_b2_k0_c0 :
    (F_0082 2 0 0) [holdout_0082_mod]⊢⁺ (F_0082 3 0 3) := by
  unfold F_0082
  dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
  execute
lemma C_bounce_0_ones (n : Nat) :
    (C_bounce 0 (([1] : List (Fin 2)) ^ n +> default)) [holdout_0082_mod]⊢⁺
    (F_0082 (n + 1) 0 3) := by
  have h1 := C_bounce_0 (([1] : List (Fin 2)) ^ n +> default)
  have h2 := shift_E_ones_0082 n ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) default
  rw [<- zPl default ([1] : List (Fin 2)) 3 n] at h2
  have hn : 3 + n = n + 3 := by omega
  rw [hn] at h2
  have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (n + 3)) {{E}}> default) =
      E_0082 0 (n + 3) := rfl
  rw [h_eq] at h2
  exact zPt (zPsp h1 h2) (step_E_b3_to_F_0082 0 n)

lemma C_bounce_1_ones (n : Nat) :
    (C_bounce 1 (([1] : List (Fin 2)) ^ n +> default)) [holdout_0082_mod]⊢⁺
    (F_0082 (n + 3) 0 3) := by
  have h1 := C_bounce_1 (([1] : List (Fin 2)) ^ n +> default)
  have h2 := shift_E_ones_0082 n ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) default
  rw [<- zPl default ([1] : List (Fin 2)) 5 n] at h2
  have hn : 5 + n = (n + 2) + 3 := by omega
  rw [hn] at h2
  have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ ((n + 2) + 3)) {{E}}>
    default) =
      E_0082 0 ((n + 2) + 3) := rfl
  rw [h_eq] at h2
  have h3 := step_E_b3_to_F_0082 0 (n + 2)
  have hn2 : (n + 2) + 1 = n + 3 := by omega
  rw [hn2] at h3
  exact zPt (zPsp h1 h2) h3

lemma C_bounce_2_ones_halt (n : Nat) :
    ∃ cfg', ((C_bounce 2 (([1] : List (Fin 2)) ^ n +> default)) [holdout_0082_mod]⊢⁺ cfg') ∧
            (step holdout_0082_mod cfg').isNone :=
  ⟨_, C_bounce_2 (([1] : List (Fin 2)) ^ n +> default), isNone_step_D_00 _ _⟩

lemma C_bounce_3_ones (b n : Nat) :
    (C_bounce (b + 3) (([1] : List (Fin 2)) ^ n +> default)) [holdout_0082_mod]⊢⁺
    (F_0082 (b + 1) 0 (n + 2)) := by
  have h1 := C_bounce_3 b (([1] : List (Fin 2)) ^ n +> default)
  rw [<- zPar ([1] : List (Fin 2)) 2 n default, <- F_0082_eq_F_R] at h1
  have hn : 2 + n = n + 2 := by omega
  rwa [hn] at h1

-- ============================================================================
-- Explicit Hub-to-Hub Macro-Transition Rules on `F_0082`
-- ============================================================================

theorem rule_F_ksucc_c0 (b k : Nat) :
    (F_0082 b (k + 1) 0) [holdout_0082_mod]⊢⁺ (F_0082 b k 1) :=
  step_F_ksucc_c0 b k

theorem rule_F_b0_k0_c0 :
    (F_0082 0 0 0) [holdout_0082_mod]⊢⁺ (F_0082 4 0 3) :=
  zPt (zPt (F_R_b0_to_D100 0 default) (D100_nil_to_C_bounce 0 0)) (C_bounce_0_ones 3)

theorem rule_F_b1_k0_c0 :
    (F_0082 1 0 0) [holdout_0082_mod]⊢⁺ (F_0082 6 0 3) :=
  zPt (zPt (F_R_b1_to_D100 0 default) (D100_nil_to_C_bounce 0 1)) (C_bounce_0_ones 5)

theorem rule_F_b2_k0_c0 :
    (F_0082 2 0 0) [holdout_0082_mod]⊢⁺ (F_0082 3 0 3) :=
  step_F_b2_k0_c0

theorem rule_F_b3_k0_c0 :
    (F_0082 3 0 0) [holdout_0082_mod]⊢⁺ (F_0082 6 0 3) :=
  zPt (zPt (F_R_b3_to_D100 0 0 default) (D100_nil_to_C_bounce 1 0)) (C_bounce_1_ones 3)

theorem rule_F_b4_k0_c0_halt :
    ∃ cfg', ((F_0082 4 0 0) [holdout_0082_mod]⊢⁺ cfg') ∧ (step holdout_0082_mod cfg').isNone := by
  obtain ⟨cfg', h_step, h_halt⟩ := C_bounce_2_ones_halt 3
  exact ⟨cfg', zPt (zPt (F_R_b3_to_D100 1 0 default) (D100_nil_to_C_bounce 2 0)) h_step, h_halt⟩

theorem rule_F_b5_k0_c0 (b : Nat) :
    (F_0082 (b + 5) 0 0) [holdout_0082_mod]⊢⁺ (F_0082 (b + 1) 0 5) := by
  have hb : b + 5 = (b + 2) + 3 := by omega
  rw [hb]
  exact zPt (zPt (F_R_b3_to_D100 (b + 2) 0 default) (D100_nil_to_C_bounce (b + 3) 0))
    (C_bounce_3_ones b 3)

theorem rule_F_b0_c1 (k : Nat) :
    (F_0082 0 k 1) [holdout_0082_mod]⊢⁺ (F_0082 (2 * k + 6) 0 3) :=
  zPt (zPt (F_R_b0_to_D100 k ([1] +> default)) (D100_one_to_C_bounce 0 k))
    (C_bounce_0_ones (2 * k + 5))

theorem rule_F_b1_c1 (k : Nat) :
    (F_0082 1 k 1) [holdout_0082_mod]⊢⁺ (F_0082 (2 * k + 8) 0 3) := by
  have h := zPt (zPt (F_R_b1_to_D100 k ([1] +> default)) (D100_one_to_C_bounce 0 (k + 1)))
    (C_bounce_0_ones (2 * (k + 1) + 5))
  have hk : (2 * (k + 1) + 5) + 1 = 2 * k + 8 := by omega
  rwa [hk] at h

theorem rule_F_b2_k0_c1 (c : Nat) :
    (F_0082 2 0 (c + 1)) [holdout_0082_mod]⊢⁺ (F_0082 5 0 c) :=
  step_F_b2_k0_0082 c

theorem rule_F_b3_c1 (k : Nat) :
    (F_0082 3 k 1) [holdout_0082_mod]⊢⁺ (F_0082 (2 * k + 8) 0 3) := by
  have h := zPt (zPt (F_R_b3_to_D100 0 k ([1] +> default)) (D100_one_to_C_bounce 1 k))
    (C_bounce_1_ones (2 * k + 5))
  have hk : (2 * k + 5) + 3 = 2 * k + 8 := by omega
  rwa [hk] at h

theorem rule_F_b4_c1_halt (k : Nat) :
    ∃ cfg', ((F_0082 4 k 1) [holdout_0082_mod]⊢⁺ cfg') ∧ (step holdout_0082_mod cfg').isNone := by
  obtain ⟨cfg', h_step, h_halt⟩ := C_bounce_2_ones_halt (2 * k + 5)
  exact ⟨cfg', zPt (zPt (F_R_b3_to_D100 1 k ([1] +> default)) (D100_one_to_C_bounce 2 k)) h_step,
    h_halt⟩

theorem rule_F_b5_c1 (b k : Nat) :
    (F_0082 (b + 5) k 1) [holdout_0082_mod]⊢⁺ (F_0082 (b + 1) 0 (2 * k + 7)) := by
  have hb : b + 5 = (b + 2) + 3 := by omega
  rw [hb]
  have h := zPt (zPt (F_R_b3_to_D100 (b + 2) k ([1] +> default)) (D100_one_to_C_bounce (b + 3) k))
    (C_bounce_3_ones b (2 * k + 5))
  have hk : (2 * k + 5) + 2 = 2 * k + 7 := by omega
  rwa [hk] at h

theorem rule_F_b0_c2 (k c : Nat) :
    (F_0082 0 k (c + 2)) [holdout_0082_mod]⊢⁺ (F_0082 1 (k + 1) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, zPar ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b0_to_D100 k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_0_11 k (([1] : List (Fin 2)) ^ c +> default)
  exact zPt h1 h2

theorem rule_F_b1_c2 (k c : Nat) :
    (F_0082 1 k (c + 2)) [holdout_0082_mod]⊢⁺ (F_0082 1 (k + 2) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, zPar ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ c +> default)
  exact zPt h1 h2

theorem rule_F_b3_c2 (b k c : Nat) :
    (F_0082 (b + 3) k (c + 2)) [holdout_0082_mod]⊢⁺ (F_0082 (b + 1) (k + 2) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, zPar ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b3_to_D100 b k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_succ_11 b k (([1] : List (Fin 2)) ^ c +> default)
  exact zPt h1 h2

lemma closes_C_bounce_ones (b n : Nat) :
    Closes (C_bounce b (([1] : List (Fin 2)) ^ n +> default)) := by
  rcases b with _ | _ | _ | b'
  · exact closes_of_in_ps (C_bounce_0_ones n) (in_ps_F (n + 1) 0 3)
  · exact closes_of_in_ps (C_bounce_1_ones n) (in_ps_F (n + 3) 0 3)
  · obtain ⟨cfg', h_step, h_halt⟩ := C_bounce_2_ones_halt n
    exact closes_of_halt h_step h_halt
  · exact closes_of_in_ps (C_bounce_3_ones b' n) (in_ps_F (b' + 1) 0 (n + 2))

lemma closes_F_c0 (b k : Nat) : Closes (F_0082 b k 0) := by
  rcases k with _ | k'
  · rcases b with _ | _ | _ | _ | _ | b'
    · exact closes_of_in_ps rule_F_b0_k0_c0 (in_ps_F 4 0 3)
    · exact closes_of_in_ps rule_F_b1_k0_c0 (in_ps_F 6 0 3)
    · exact closes_of_in_ps rule_F_b2_k0_c0 (in_ps_F 3 0 3)
    · exact closes_of_in_ps rule_F_b3_k0_c0 (in_ps_F 6 0 3)
    · obtain ⟨cfg', h_step, h_halt⟩ := rule_F_b4_k0_c0_halt
      exact closes_of_halt h_step h_halt
    · exact closes_of_in_ps (rule_F_b5_k0_c0 b') (in_ps_F (b' + 1) 0 5)
  · exact closes_of_in_ps (rule_F_ksucc_c0 b k') (in_ps_F b k' 1)

lemma closes_F_b0 (k c : Nat) : Closes (F_0082 0 k c) := by
  rcases c with _ | _ | c'
  · exact closes_F_c0 0 k
  · exact closes_of_in_ps (rule_F_b0_c1 k) (in_ps_F (2 * k + 6) 0 3)
  · exact closes_of_in_ps (rule_F_b0_c2 k c') (in_ps_F 1 (k + 1) c')

lemma closes_F_b1 (k c : Nat) : Closes (F_0082 1 k c) := by
  rcases c with _ | _ | c'
  · exact closes_F_c0 1 k
  · exact closes_of_in_ps (rule_F_b1_c1 k) (in_ps_F (2 * k + 8) 0 3)
  · exact closes_of_in_ps (rule_F_b1_c2 k c') (in_ps_F 1 (k + 2) c')

lemma closes_F_b3 (b k c : Nat) : Closes (F_0082 (b + 3) k c) := by
  rcases c with _ | _ | c'
  · exact closes_F_c0 (b + 3) k
  · rcases b with _ | _ | b'
    · exact closes_of_in_ps (rule_F_b3_c1 k) (in_ps_F (2 * k + 8) 0 3)
    · obtain ⟨cfg', h_step, h_halt⟩ := rule_F_b4_c1_halt k
      exact closes_of_halt h_step h_halt
    · exact closes_of_in_ps (rule_F_b5_c1 b' k) (in_ps_F (b' + 1) 0 (2 * k + 7))
  · exact closes_of_in_ps (rule_F_b3_c2 b k c') (in_ps_F (b + 1) (k + 2) c')
lemma step_F_R_b2_one (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 2 k ([1] +> r)) [holdout_0082_mod]⊢⁺
    (F_R 5 0 (([0, 1] : List (Fin 2)) ^ k +> r)) := by
  unfold F_R
  simp only [zPz, zLan]
  have h1 := shift_FA_left_0082 k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) ([0,
    1] +> r)
  have h2 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) {{F}}>
      ([0] +> (([0, 1] : List (Fin 2)) ^ k +> ([0, 1] +> r))))
      [holdout_0082_mod]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{F}}>
        ([0, 0] +> (([0, 1] : List (Fin 2)) ^ k +> r))) := by
    rw [zPa1 ([0, 1] : List (Fin 2)) k r,
      zPsr ([0, 1] : List (Fin 2)) k r]
    dsimp [HPow.hPow, list_nat_repeat, ListBlank.append]
    execute
  exact zSpp h1 h2
lemma step_E_01_to_F_R (b : Nat) (r : ListBlank (Fin 2)) :
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) {{E}}> ([0, 1] +> r))
    [holdout_0082_mod]⊢⁺
    (F_R b 0 r) := by
  unfold F_R
  simp only [zPz, zLan]
  dsimp [ListBlank.append]
  execute
lemma closes_E_01_tail (b m c : Nat)
    (ih : ∀ m' < m + 1, ∀ p k, Closes (F_R (2 * p + 1) k (([0, 1] : List (Fin 2)) ^ m' +> (([1] :
    List (Fin 2)) ^ c +> default)))) :
    Closes (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b + 1)) {{E}}>
      (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))) := by
  rcases m with _ | m'
  · simp only [zPz, zLan]
    have h1 := shift_E_ones_0082 c ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b
    + 1)) default
    rw [<- zPl default ([1] : List (Fin 2)) (2 * b + 1) c] at h1
    have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b + 1 + c)) {{E}}>
    default) =
        E_0082 0 (2 * b + 1 + c) := rfl
    rw [h_eq] at h1
    exact closes_of_stepStar h1 (closes_E 0 (2 * b + 1 + c))
  · rw [zPsr ([0, 1] : List (Fin 2)) m']
    have h1 := step_E_01_to_F_R (2 * b + 1) (([0, 1] : List (Fin 2)) ^ m' +> (([1] : List (Fin 2))
    ^ c +> default))
    exact closes_of_stepPlus h1 (ih m' (by omega) b 0)
lemma closes_odd_even_ones (n : Nat) (r : ListBlank (Fin 2))
    (h_base : ∀ p k, Closes (F_R (2 * p + 1) k r)) :
    ∀ p k, Closes (F_R (2 * p + 1) k (([1] : List (Fin 2)) ^ (2 * n) +> r)) := by
  induction n with
  | zero =>
    intro p k
    simp only [Nat.mul_zero, zPz, zLan]
    exact h_base p k
  | succ n ih =>
    intro p k
    have hn : 2 * (n + 1) = 2 + 2 * n := by omega
    rw [hn, zPar ([1] : List (Fin 2)) 2 (2 * n) r]
    rcases p with _ | p'
    · have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * n) +>
    r))
      have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ (2 * n) +> r)
      exact closes_of_stepPlus (zPt h1 h2) (ih 0 (k + 2))
    · have hp : 2 * (p' + 1) + 1 = (2 * p') + 3 := by omega
      rw [hp]
      have h1 := F_R_b3_to_D100 (2 * p') k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2
    * n) +> r))
      have h2 := D100_succ_11 (2 * p') k (([1] : List (Fin 2)) ^ (2 * n) +> r)
      exact closes_of_stepPlus (zPt h1 h2) (ih p' (k + 2))
lemma closes_odd_m (m : Nat) (c : Nat) :
    ∀ p k, Closes (F_R (2 * p + 1) k (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +>
    default))) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro p k
    rcases m with _ | m'
    · simp only [zPz, zLan, <- F_0082_eq_F_R]
      rcases p with _ | p'
      · exact closes_F_b1 k c
      · have hp : 2 * (p' + 1) + 1 = (2 * p') + 3 := by omega
        rw [hp]
        exact closes_F_b3 (2 * p') k c
    · rw [zPsr ([0, 1] : List (Fin 2)) m']
      set r' := (([0, 1] : List (Fin 2)) ^ m' +> (([1] : List (Fin 2)) ^ c +> default))
      rcases p with _ | _ | p''
      · have h1 := F_R_b1_to_D100 k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce 0 (k + 1) r'
        have h3 := C_bounce_0 (([1] : List (Fin 2)) ^ (2 * (k + 1) + 4) +> r')
        have h4 := shift_E_ones_0082 (2 * (k + 1) + 4) ((default : ListBlank (Fin 2)) <+ ([1] :
    List (Fin 2)) ^ 3) r'
        rw [<- zPl default ([1] : List (Fin 2)) 3 (2 * (k + 1) + 4)] at h4
        have hk : 3 + (2 * (k + 1) + 4) = 2 * (k + 4) + 1 := by omega
        rw [hk] at h4
        exact closes_of_stepPlus
          (zPsp (zPt (zPt h1 h2) h3) h4)
          (closes_E_01_tail (k + 4) m' c ih)
      · have h1 := F_R_b3_to_D100 0 k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce 1 k r'
        have h3 := C_bounce_1 (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
        have h4 := shift_E_ones_0082 (2 * k + 4) ((default : ListBlank (Fin 2)) <+ ([1] : List
    (Fin 2)) ^ 5) r'
        rw [<- zPl default ([1] : List (Fin 2)) 5 (2 * k + 4)] at h4
        have hk : 5 + (2 * k + 4) = 2 * (k + 4) + 1 := by omega
        rw [hk] at h4
        exact closes_of_stepPlus
          (zPsp (zPt (zPt h1 h2) h3) h4)
          (closes_E_01_tail (k + 4) m' c ih)
      · have hp : 2 * (p'' + 2) + 1 = (2 * p'' + 2) + 3 := by omega
        rw [hp]
        have h1 := F_R_b3_to_D100 (2 * p'' + 2) k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce (2 * p'' + 3) k r'
        have h3 := C_bounce_3 (2 * p'') (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
        rw [<- zPar ([1] : List (Fin 2)) 2 (2 * k + 4) r'] at h3
        have hk : 2 + (2 * k + 4) = 2 * (k + 3) := by omega
        rw [hk] at h3
        exact closes_of_stepPlus (zPt (zPt h1 h2) h3)
          (closes_odd_even_ones (k + 3) r' (ih m' (by omega)) p'' 0)
lemma closes_F_b2 (k c : Nat) : Closes (F_0082 2 k c) := by
  rcases c with _ | c'
  · exact closes_F_c0 2 k
  · rw [F_0082_eq_F_R, zPsr ([1] : List (Fin 2)) c' default]
    have h1 := step_F_R_b2_one k (([1] : List (Fin 2)) ^ c' +> default)
    exact closes_of_stepPlus h1 (closes_odd_m k c' 2 0)
lemma closes_F_all (b k c : Nat) : Closes (F_0082 b k c) := by
  rcases b with _ | _ | _ | b'
  · exact closes_F_b0 k c
  · exact closes_F_b1 k c
  · exact closes_F_b2 k c
  · exact closes_F_b3 b' k c
def π : Fin 6 -> Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 3
  | 4 => 4
  | 5 => 0
def mirrorTape : Tape (Fin 2) -> Tape (Fin 2)
  | ⟨head, l, r⟩ => ⟨head, r, l⟩
def mirrorCfg (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map π, mirrorTape c.tape⟩
lemma step_mirror (c : Cfg (Fin 2) (Fin 6)) :
    step target (mirrorCfg c) = (step holdout_0082_mod c).map mirrorCfg := by
  rcases c with ⟨_ | q, ⟨head, l, r⟩⟩
  · rfl
  · rcases q with ⟨_ | _ | _ | _ | _ | _ | q, hq⟩ <;>
    rcases head with ⟨_ | _ | head, hhead⟩ <;>
    first | rfl | omega
lemma multiStep_mirror (n : Nat) (c : Cfg (Fin 2) (Fin 6)) :
    multiStep target (mirrorCfg c) n = (multiStep holdout_0082_mod c n).map mirrorCfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [zMs, zMs, ih]
    cases multiStep holdout_0082_mod c n with
    | none => rfl
    | some c' =>
      simp only [Option.map_some, Option.bind_some]
      exact step_mirror c'
lemma stepPlus_mirror {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h : c_1 [holdout_0082_mod]⊢⁺ c_2) :
    (mirrorCfg c_1) [target]⊢⁺ (mirrorCfg c_2) := by
  rcases h with ⟨n, hn, hstep⟩
  refine ⟨n, hn, ?_⟩
  rw [multiStep_mirror, hstep]
  rfl
lemma stepStar_mirror {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h : c_1 [holdout_0082_mod]⊢* c_2) :
    (mirrorCfg c_1) [target]⊢* (mirrorCfg c_2) := by
  rcases h with ⟨n, hstep⟩
  refine ⟨n, ?_⟩
  rw [multiStep_mirror, hstep]
  rfl
lemma isNone_step_mirror {c : Cfg (Fin 2) (Fin 6)}
    (h : (step holdout_0082_mod c).isNone) :
    (step target (mirrorCfg c)).isNone := by
  rw [step_mirror]
  revert h
  cases step holdout_0082_mod c <;> intro h <;> first | rfl | cases h
def cfg_A (b k c : Nat) : Cfg (Fin 2) (Fin 6) :=
  mirrorCfg (F_0082 b k c)
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .sym 0 (.rep [1] 2 .default)
    head  := some A
    right := .sym 0 (.rep [1, 0] 1 (.rep [1] 0 .default)) }
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]
lemma eval_pat_A (vars : Nat -> Nat) :
    evalTapePattern pat_A vars = mirrorCfg (F_0082 (vars 0) (vars 1) (vars 2)) := by
  unfold evalTapePattern pat_A mirrorCfg mirrorTape F_0082 evalTapeExpr π A F
  simp only [evalTapeExpr, bb_hpow_eq_local_hpow, zLac, zLan, Turing.ListBlank.head_cons,
    Turing.ListBlank.tail_cons, Option.map_some]
  try rfl
lemma in_ps_A (b k c : Nat) : IsInPatternSet ps (mirrorCfg (F_0082 b k c)) := by
  refine ⟨(pat_A, .true), List.Mem.head _, fun i => match i with | 0 => b | 1 => k | _ => c, ?_,
    trivial⟩
  exact (eval_pat_A (fun i => match i with | 0 => b | 1 => k | _ => c)).symm
lemma mirrorCfg_F_403_eq :
    mirrorCfg (F_0082 4 0 3) =
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) {{A}}>
      ([0] +> (([1] : List (Fin 2)) ^ 4 +> default)) := rfl
theorem init_reaches_A_403 :
    (init []) [target]⊢* mirrorCfg (F_0082 4 0 3) := by
  rw [mirrorCfg_F_403_eq]
  refine zPs ?_
  unfold init
  simp only [Tape.mk₁, zPz, zPsl, zCal,
    zAnl, zLan, zLac]
  execute

theorem audit_ps_nonempty : ∃ cfg, IsInPatternSet ps cfg :=
  ⟨mirrorCfg (F_0082 4 0 3), in_ps_A 4 0 3⟩

theorem audit_init_neq_cfg0 :
    init [] ≠ mirrorCfg (F_0082 4 0 3) := by
  intro h
  have h1 : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)).tape.right.head =
      (mirrorCfg (F_0082 4 0 3)).tape.right.head := congrArg (fun c => c.tape.right.head) h
  revert h1
  decide





theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨mirrorCfg (F_0082 4 0 3), init_reaches_A_403, in_ps_A 4 0 3⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  subst h_mem
  rw [eval_pat_A]
  rcases closes_F_all (vars 0) (vars 1) (vars 2) with ⟨cfg', h_step, h_end⟩
  refine ⟨mirrorCfg cfg', stepPlus_mirror h_step, ?_⟩
  rcases h_end with ⟨b', k', c', rfl⟩ | h_halt
  · exact Or.inl (in_ps_A b' k' c')
  · exact Or.inr (isNone_step_mirror h_halt)


-- ============================================================================
-- Higher-Order Countdown, Multiplicative Slice & 2^n Exponential Accelerations
-- ============================================================================

/-- All-`k` drain from `c = 0` when `b ≥ 5`: combines `rule_F_ksucc_c0` and `rule_F_b5_c1`. -/
theorem rule_F_b5_ksucc_c0 (b k : Nat) :
    (F_0082 (b + 5) (k + 1) 0) [holdout_0082_mod]⊢⁺ (F_0082 (b + 1) 0 (2 * k + 7)) :=
  zPt (rule_F_ksucc_c0 (b + 5) k) (rule_F_b5_c1 b k)

/-- Multi-step `(b, c) → k` countdown drain on `F_0082` (`⊢*`). -/
theorem drain_F_bc (m b k c : Nat) :
    (F_0082 (b + 2 * m + 1) k (c + 2 * m)) [holdout_0082_mod]⊢*
    (F_0082 (b + 1) (k + 2 * m) c) := by
  induction m generalizing b k c with
  | zero =>
    have hb : b + 2 * 0 + 1 = b + 1 := by omega
    have hc : c + 2 * 0 = c := by omega
    have hk : k + 2 * 0 = k := by omega
    rw [hb, hc, hk]
    exact ⟨0, rfl⟩
  | succ m ih =>
    have hb : b + 2 * (m + 1) + 1 = (b + 2 * m) + 3 := by omega
    have hc : c + 2 * (m + 1) = (c + 2 * m) + 2 := by omega
    rw [hb, hc]
    have h1 := rule_F_b3_c2 (b + 2 * m) k (c + 2 * m)
    have h2 := ih b (k + 2) c
    have hk : (k + 2) + 2 * m = k + 2 * (m + 1) := by omega
    rw [hk] at h2
    exact zPs (zPsp h1 h2)

/-- Strict positive-progress (`⊢⁺`) `(b, c) → k` countdown on `F_0082` for `m + 1` rounds. -/
theorem countdown_F_bc (m b k c : Nat) :
    (F_0082 (b + 2 * m + 3) k (c + 2 * m + 2)) [holdout_0082_mod]⊢⁺
    (F_0082 (b + 1) (k + 2 * m + 2) c) := by
  have hb : b + 2 * m + 3 = (b + 2 * m) + 3 := by omega
  have hc : c + 2 * m + 2 = (c + 2 * m) + 2 := by omega
  rw [hb, hc]
  have h1 := rule_F_b3_c2 (b + 2 * m) k (c + 2 * m)
  have h2 := drain_F_bc m b (k + 2) c
  have hk : (k + 2) + 2 * m = k + 2 * m + 2 := by omega
  rw [hk] at h2
  exact zPsp h1 h2

/-- Multi-step `c → k` countdown drain on `F_0082` at `b = 1` (`⊢*`). -/
theorem drain_F_b1_c (m k c : Nat) :
    (F_0082 1 k (c + 2 * m)) [holdout_0082_mod]⊢*
    (F_0082 1 (k + 2 * m) c) := by
  induction m generalizing k c with
  | zero =>
    have hc : c + 2 * 0 = c := by omega
    have hk : k + 2 * 0 = k := by omega
    rw [hc, hk]
    exact ⟨0, rfl⟩
  | succ m ih =>
    have hc : c + 2 * (m + 1) = (c + 2 * m) + 2 := by omega
    rw [hc]
    have h1 := rule_F_b1_c2 k (c + 2 * m)
    have h2 := ih (k + 2) c
    have hk : (k + 2) + 2 * m = k + 2 * (m + 1) := by omega
    rw [hk] at h2
    exact zPs (zPsp h1 h2)

/-- Strict positive-progress (`⊢⁺`) `c → k` countdown on `F_0082` at `b = 1` for `m + 1` rounds. -/
theorem countdown_F_b1_c (m k c : Nat) :
    (F_0082 1 k (c + 2 * m + 2)) [holdout_0082_mod]⊢⁺
    (F_0082 1 (k + 2 * m + 2) c) := by
  have hc : c + 2 * m + 2 = (c + 2 * m) + 2 := by omega
  rw [hc]
  have h1 := rule_F_b1_c2 k (c + 2 * m)
  have h2 := drain_F_b1_c m (k + 2) c
  have hk : (k + 2) + 2 * m = k + 2 * m + 2 := by omega
  rw [hk] at h2
  exact zPsp h1 h2

/-- Full odd-`c` multiplicative slice on `F_0082`. -/
theorem accel_F_odd_c (b k m : Nat) :
    (F_0082 (b + 2 * m + 5) k (2 * m + 1)) [holdout_0082_mod]⊢⁺
    (F_0082 (b + 1) 0 (2 * k + 4 * m + 7)) := by
  have h1 := drain_F_bc m (b + 4) k 1
  have hb1 : (b + 4) + 2 * m + 1 = b + 2 * m + 5 := by omega
  have hb2 : (b + 4) + 1 = b + 5 := by omega
  have hc1 : 1 + 2 * m = 2 * m + 1 := by omega
  rw [hb1, hb2, hc1] at h1
  have h2 := rule_F_b5_c1 b (k + 2 * m)
  have hc2 : 2 * (k + 2 * m) + 7 = 2 * k + 4 * m + 7 := by omega
  rw [hc2] at h2
  exact zSpp h1 h2

/-- 1-round multiplicative doubling transition on `F_0082` (`c = 2 * m + 1 ↦ 4 * m + 7` at `k =
    0`). -/
theorem double_F (b m : Nat) :
    (F_0082 (b + 2 * m + 5) 0 (2 * m + 1)) [holdout_0082_mod]⊢⁺
    (F_0082 (b + 1) 0 (4 * m + 7)) := by
  have h := accel_F_odd_c b 0 m
  have hc : 2 * 0 + 4 * m + 7 = 4 * m + 7 := by omega
  rwa [hc] at h

/-- Full even-`c` (`c = 2 * m + 2`) multiplicative slice on `F_0082`. -/
theorem accel_F_even_c (b k m : Nat) :
    (F_0082 (b + 2 * m + 7) k (2 * m + 2)) [holdout_0082_mod]⊢⁺
    (F_0082 (b + 1) 0 (2 * k + 4 * m + 9)) := by
  have h1 := countdown_F_bc m (b + 4) k 0
  have hb1 : (b + 4) + 2 * m + 3 = b + 2 * m + 7 := by omega
  have hb2 : (b + 4) + 1 = b + 5 := by omega
  have hc1 : 0 + 2 * m + 2 = 2 * m + 2 := by omega
  have hk1 : k + 2 * m + 2 = (k + 2 * m + 1) + 1 := by omega
  rw [hb1, hb2, hc1, hk1] at h1
  have h2 := rule_F_b5_ksucc_c0 b (k + 2 * m + 1)
  have hc2 : 2 * (k + 2 * m + 1) + 7 = 2 * k + 4 * m + 9 := by omega
  rw [hc2] at h2
  exact zPt h1 h2

/-- Full `b = 1` reload slice on `F_0082` for odd `c = 2 * m + 1`. -/
theorem accel_F_b1_odd_c (k m : Nat) :
    (F_0082 1 k (2 * m + 1)) [holdout_0082_mod]⊢⁺
    (F_0082 (2 * k + 4 * m + 8) 0 3) := by
  have h1 := drain_F_b1_c m k 1
  have hc1 : 1 + 2 * m = 2 * m + 1 := by omega
  rw [hc1] at h1
  have h2 := rule_F_b1_c1 (k + 2 * m)
  have hb : 2 * (k + 2 * m) + 8 = 2 * k + 4 * m + 8 := by omega
  rw [hb] at h2
  exact zSpp h1 h2

/-- Full `b = 1` reload slice on `F_0082` for even `c = 2 * m + 2`. -/
theorem accel_F_b1_even_c (k m : Nat) :
    (F_0082 1 k (2 * m + 2)) [holdout_0082_mod]⊢⁺
    (F_0082 (2 * k + 4 * m + 10) 0 3) := by
  have h1 := countdown_F_b1_c m k 0
  have hc1 : 0 + 2 * m + 2 = 2 * m + 2 := by omega
  have hk1 : k + 2 * m + 2 = (k + 2 * m + 1) + 1 := by omega
  rw [hc1, hk1] at h1
  have h2 := rule_F_ksucc_c0 1 (k + 2 * m + 1)
  have h3 := rule_F_b1_c1 (k + 2 * m + 1)
  have hb : 2 * (k + 2 * m + 1) + 8 = 2 * k + 4 * m + 10 := by omega
  rw [hb] at h3
  exact zPt (zPt h1 h2) h3

lemma mul_pow2_ge (k n : Nat) : k * 2 ^ n ≥ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : k * 2 ^ (n + 1) = k * 2 ^ n * 2 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
    omega

/-- Closed-form `2^n` exponential macro-transition on `F_0082` (`n` rounds of `double_F`). -/
theorem exp_step_F (n b m : Nat) :
    (F_0082 (b + 2 * (m + 3) * 2 ^ n + 1) 0 (2 * m + 1)) [holdout_0082_mod]⊢*
    (F_0082 (b + 2 * (m + 3) + 2 * n + 1) 0 (2 * (m + 3) * 2 ^ n - 5)) := by
  induction n generalizing b m with
  | zero =>
    have hb : b + 2 * (m + 3) * 2 ^ 0 + 1 = b + 2 * (m + 3) + 2 * 0 + 1 := by simp
    have hc : 2 * m + 1 = 2 * (m + 3) * 2 ^ 0 - 5 := by simp; omega
    rw [hb, hc]
    exact ⟨0, rfl⟩
  | succ n ih =>
    set k := (m + 3) * 2 ^ n
    have hk : k ≥ m + 3 := mul_pow2_ge (m + 3) n
    have h2k : 2 * (m + 3) * 2 ^ n = 2 * k :=
      Nat.mul_assoc 2 (m + 3) (2 ^ n)
    have hpow : 2 * (m + 3) * 2 ^ (n + 1) = 4 * k := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, h2k]
      omega
    have hb_in : b + 2 * (m + 3) * 2 ^ (n + 1) + 1 =
        (b + 2 * k) + 2 * (m + 3) * 2 ^ n + 1 := by
      rw [hpow, h2k]; omega
    rw [hb_in]
    have h1 := ih (b + 2 * k) m
    have hb_mid : (b + 2 * k) + 2 * (m + 3) + 2 * n + 1 =
        (b + 2 * (m + 3) + 2 * n + 2) + 2 * (k - 3) + 5 := by omega
    have hc_mid : 2 * (m + 3) * 2 ^ n - 5 = 2 * (k - 3) + 1 := by
      rw [h2k]; omega
    rw [hb_mid, hc_mid] at h1
    have h2 := double_F (b + 2 * (m + 3) + 2 * n + 2) (k - 3)
    have hb_out : (b + 2 * (m + 3) + 2 * n + 2) + 1 =
        b + 2 * (m + 3) + 2 * (n + 1) + 1 := by omega
    have hc_out : 4 * (k - 3) + 7 = 2 * (m + 3) * 2 ^ (n + 1) - 5 := by
      rw [hpow]; omega
    rw [hb_out, hc_out] at h2
    exact zSt h1 (zPs h2)

/-- Guarded fuel-subtraction form of the `2^n` exponential macro-transition on `F_0082`. -/
theorem exp_step_F_fuel (n b m : Nat)
    (hb : b ≥ 2 * (m + 3) * 2 ^ n + 1) :
    (F_0082 b 0 (2 * m + 1)) [holdout_0082_mod]⊢*
    (F_0082 (b - 2 * (m + 3) * 2 ^ n + 2 * (m + 3) + 2 * n) 0 (2 * (m + 3) * 2 ^ n - 5)) := by
  have h := exp_step_F n (b - (2 * (m + 3) * 2 ^ n + 1)) m
  have hb1 : (b - (2 * (m + 3) * 2 ^ n + 1)) + 2 * (m + 3) * 2 ^ n + 1 = b := by omega
  have hb2 : (b - (2 * (m + 3) * 2 ^ n + 1)) + 2 * (m + 3) + 2 * n + 1 =
      b - 2 * (m + 3) * 2 ^ n + 2 * (m + 3) + 2 * n := by omega
  rwa [hb1, hb2] at h

/-- Concrete `n = 2` instantiation of `exp_step_F`. -/
theorem exp_step_F_example :
    (F_0082 33 0 3) [holdout_0082_mod]⊢* (F_0082 13 0 27) :=
  exp_step_F 2 0 1

-- ============================================================================
-- Transported Hub-to-Hub Rules & Accelerations on `target` (`cfg_A`)
-- ============================================================================

theorem rule_A_ksucc_c0 (b k : Nat) :
    (cfg_A b (k + 1) 0) [target]⊢⁺ (cfg_A b k 1) :=
  stepPlus_mirror (rule_F_ksucc_c0 b k)

theorem rule_A_b0_k0_c0 :
    (cfg_A 0 0 0) [target]⊢⁺ (cfg_A 4 0 3) :=
  stepPlus_mirror rule_F_b0_k0_c0

theorem rule_A_b1_k0_c0 :
    (cfg_A 1 0 0) [target]⊢⁺ (cfg_A 6 0 3) :=
  stepPlus_mirror rule_F_b1_k0_c0

theorem rule_A_b2_k0_c0 :
    (cfg_A 2 0 0) [target]⊢⁺ (cfg_A 3 0 3) :=
  stepPlus_mirror rule_F_b2_k0_c0

theorem rule_A_b3_k0_c0 :
    (cfg_A 3 0 0) [target]⊢⁺ (cfg_A 6 0 3) :=
  stepPlus_mirror rule_F_b3_k0_c0

theorem rule_A_b4_k0_c0_halt :
    ∃ cfg', ((cfg_A 4 0 0) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  obtain ⟨cfg', h_step, h_halt⟩ := rule_F_b4_k0_c0_halt
  exact ⟨mirrorCfg cfg', stepPlus_mirror h_step, isNone_step_mirror h_halt⟩

theorem rule_A_b5_k0_c0 (b : Nat) :
    (cfg_A (b + 5) 0 0) [target]⊢⁺ (cfg_A (b + 1) 0 5) :=
  stepPlus_mirror (rule_F_b5_k0_c0 b)

theorem rule_A_b0_c1 (k : Nat) :
    (cfg_A 0 k 1) [target]⊢⁺ (cfg_A (2 * k + 6) 0 3) :=
  stepPlus_mirror (rule_F_b0_c1 k)

theorem rule_A_b1_c1 (k : Nat) :
    (cfg_A 1 k 1) [target]⊢⁺ (cfg_A (2 * k + 8) 0 3) :=
  stepPlus_mirror (rule_F_b1_c1 k)

theorem rule_A_b2_k0_c1 (c : Nat) :
    (cfg_A 2 0 (c + 1)) [target]⊢⁺ (cfg_A 5 0 c) :=
  stepPlus_mirror (rule_F_b2_k0_c1 c)

theorem rule_A_b3_c1 (k : Nat) :
    (cfg_A 3 k 1) [target]⊢⁺ (cfg_A (2 * k + 8) 0 3) :=
  stepPlus_mirror (rule_F_b3_c1 k)

theorem rule_A_b4_c1_halt (k : Nat) :
    ∃ cfg', ((cfg_A 4 k 1) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  obtain ⟨cfg', h_step, h_halt⟩ := rule_F_b4_c1_halt k
  exact ⟨mirrorCfg cfg', stepPlus_mirror h_step, isNone_step_mirror h_halt⟩

theorem rule_A_b5_c1 (b k : Nat) :
    (cfg_A (b + 5) k 1) [target]⊢⁺ (cfg_A (b + 1) 0 (2 * k + 7)) :=
  stepPlus_mirror (rule_F_b5_c1 b k)

theorem rule_A_b5_ksucc_c0 (b k : Nat) :
    (cfg_A (b + 5) (k + 1) 0) [target]⊢⁺ (cfg_A (b + 1) 0 (2 * k + 7)) :=
  stepPlus_mirror (rule_F_b5_ksucc_c0 b k)

theorem rule_A_b0_c2 (k c : Nat) :
    (cfg_A 0 k (c + 2)) [target]⊢⁺ (cfg_A 1 (k + 1) c) :=
  stepPlus_mirror (rule_F_b0_c2 k c)

theorem rule_A_b1_c2 (k c : Nat) :
    (cfg_A 1 k (c + 2)) [target]⊢⁺ (cfg_A 1 (k + 2) c) :=
  stepPlus_mirror (rule_F_b1_c2 k c)

theorem rule_A_b3_c2 (b k c : Nat) :
    (cfg_A (b + 3) k (c + 2)) [target]⊢⁺ (cfg_A (b + 1) (k + 2) c) :=
  stepPlus_mirror (rule_F_b3_c2 b k c)

theorem drain_A_bc (m b k c : Nat) :
    (cfg_A (b + 2 * m + 1) k (c + 2 * m)) [target]⊢*
    (cfg_A (b + 1) (k + 2 * m) c) :=
  stepStar_mirror (drain_F_bc m b k c)

theorem countdown_A_bc (m b k c : Nat) :
    (cfg_A (b + 2 * m + 3) k (c + 2 * m + 2)) [target]⊢⁺
    (cfg_A (b + 1) (k + 2 * m + 2) c) :=
  stepPlus_mirror (countdown_F_bc m b k c)

theorem drain_A_b1_c (m k c : Nat) :
    (cfg_A 1 k (c + 2 * m)) [target]⊢*
    (cfg_A 1 (k + 2 * m) c) :=
  stepStar_mirror (drain_F_b1_c m k c)

theorem countdown_A_b1_c (m k c : Nat) :
    (cfg_A 1 k (c + 2 * m + 2)) [target]⊢⁺
    (cfg_A 1 (k + 2 * m + 2) c) :=
  stepPlus_mirror (countdown_F_b1_c m k c)

theorem accel_A_odd_c (b k m : Nat) :
    (cfg_A (b + 2 * m + 5) k (2 * m + 1)) [target]⊢⁺
    (cfg_A (b + 1) 0 (2 * k + 4 * m + 7)) :=
  stepPlus_mirror (accel_F_odd_c b k m)

theorem double_A (b m : Nat) :
    (cfg_A (b + 2 * m + 5) 0 (2 * m + 1)) [target]⊢⁺
    (cfg_A (b + 1) 0 (4 * m + 7)) :=
  stepPlus_mirror (double_F b m)

theorem accel_A_even_c (b k m : Nat) :
    (cfg_A (b + 2 * m + 7) k (2 * m + 2)) [target]⊢⁺
    (cfg_A (b + 1) 0 (2 * k + 4 * m + 9)) :=
  stepPlus_mirror (accel_F_even_c b k m)

theorem accel_A_b1_odd_c (k m : Nat) :
    (cfg_A 1 k (2 * m + 1)) [target]⊢⁺
    (cfg_A (2 * k + 4 * m + 8) 0 3) :=
  stepPlus_mirror (accel_F_b1_odd_c k m)

theorem accel_A_b1_even_c (k m : Nat) :
    (cfg_A 1 k (2 * m + 2)) [target]⊢⁺
    (cfg_A (2 * k + 4 * m + 10) 0 3) :=
  stepPlus_mirror (accel_F_b1_even_c k m)

theorem exp_step_A (n b m : Nat) :
    (cfg_A (b + 2 * (m + 3) * 2 ^ n + 1) 0 (2 * m + 1)) [target]⊢*
    (cfg_A (b + 2 * (m + 3) + 2 * n + 1) 0 (2 * (m + 3) * 2 ^ n - 5)) :=
  stepStar_mirror (exp_step_F n b m)

theorem exp_step_A_fuel (n b m : Nat)
    (hb : b ≥ 2 * (m + 3) * 2 ^ n + 1) :
    (cfg_A b 0 (2 * m + 1)) [target]⊢*
    (cfg_A (b - 2 * (m + 3) * 2 ^ n + 2 * (m + 3) + 2 * n) 0 (2 * (m + 3) * 2 ^ n - 5)) :=
  stepStar_mirror (exp_step_F_fuel n b m hb)

theorem exp_step_A_example :
    (cfg_A 33 0 3) [target]⊢* (cfg_A 13 0 27) :=
  stepStar_mirror exp_step_F_example


theorem has_collatz_reduction : HasCollatzReduction target := ⟨ps, is_closed_pattern_set⟩

end BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC


