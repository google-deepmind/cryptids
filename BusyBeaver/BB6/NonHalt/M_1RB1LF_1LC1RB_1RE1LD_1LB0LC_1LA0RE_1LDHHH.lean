/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LF_1LC1RB_1RE1LD_1LB0LC_1LA0RE_1LD---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LF_1LC1RB_1RE1LD_1LB0LC_1LA0RE_1LD---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LF_1LC1RB_1RE1LD_1LB0LC_1LA0RE_1LDHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LF_1LC1RB_1RE1LD_1LB0LC_1LA0RE_1LD---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
def z00 : Machine (Fin 2) (Fin 6)
  | 0,0 => some (some 1,Stmt.write 1 Dir.left)
  | 0,1 => some (some 5,Stmt.write 1 Dir.right)
  | 1,0 => some (some 2,Stmt.write 1 Dir.right)
  | 1,1 => some (some 1,Stmt.write 1 Dir.left)
  | 2,0 => some (some 4,Stmt.write 1 Dir.left)
  | 2,1 => some (some 3,Stmt.write 1 Dir.right)
  | 3,0 => some (some 1,Stmt.write 1 Dir.right)
  | 3,1 => some (some 2,Stmt.write 0 Dir.right)
  | 4,0 => some (some 0,Stmt.write 1 Dir.right)
  | 4,1 => some (some 4,Stmt.write 0 Dir.left)
  | 5,0 => some (some 3,Stmt.write 1 Dir.right)
  | 5,1 => none
@[simp] lemma zMz (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine zG_ zL_) (config : Cfg zG_ zL_) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep,Function.iterate_succ',Function.comp_apply,multiStep]
lemma z01 (M : Machine zG_ zL_) (config : Cfg zG_ zL_) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (step M config) (fun c' => multiStep M c' n) := by
  induction n generalizing config with
  | zero => simp [zMo,zMz]
  | succ n ih =>
    rw [zMs,ih]
    cases step M config <;> simp [zMs]
lemma zSm {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
lemma z02 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢* c_2 := ⟨1,zSm tm c_1 c_2 h⟩
lemma z03 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1,by decide +kernel,zSm tm c_1 c_2 h⟩
lemma zMa {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 : Cfg zG_ zL_) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ,zMs,ih,Option.bind_assoc]
    simp_rw [zMs]
lemma zMt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 c_3 : Cfg zG_ zL_) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa,h₁]; simp [h₂]
lemma z04 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} (c : Cfg zG_ zL_) : c [tm]⊢* c := ⟨0,rfl⟩
lemma zSt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢* c_3 := by
  obtain ⟨n,hn⟩ := h₁; obtain ⟨m,hm⟩ := h₂
  exact ⟨n + m,zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,n_pos,hn⟩ := h₁; obtain ⟨m,_,hm⟩ := h₂
  exact ⟨n + m,lt_of_lt_of_le n_pos (Nat.le_add_right n m),zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPs {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 : Cfg zG_ zL_} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n,_,hn⟩ := h; exact ⟨n,hn⟩
lemma z05 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,n_pos,hn⟩ := h₁; obtain ⟨m,hm⟩ := h₂
  exact ⟨n + m,lt_of_lt_of_le n_pos (Nat.le_add_right n m),zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z06 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,hn⟩ := h₁; obtain ⟨m,m_pos,hm⟩ := h₂
  exact ⟨n + m,lt_of_lt_of_le m_pos (Nat.le_add_left m n),zMt tm c_1 c_2 c_3 n m hn hm⟩
@[simp] lemma z07 : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : zB).head = 0 := rfl
@[simp] lemma zDt : (default : zB).tail = default := rfl
@[simp] lemma head_cons (a : Fin 2) (s : zB) : (a >> s).head = a := ListBlank.head_cons a s
@[simp] lemma tail_cons (a : Fin 2) (s : zB) : (a >> s).tail = s := ListBlank.tail_cons a s
@[simp] lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[simp] lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[simp] lemma append_assoc (l₁ l₂ : zF) (s : zB) :
    (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s) := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih => simp [ih]
@[simp] lemma zPz (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma z08 (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
lemma z09 (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih => simp [z08,Nat.succ_add,ih,List.append_assoc]
lemma z0a (l : List α) (n : Nat) : l ^ n ++ l = l ^ (n + 1) := by
  induction n with
  | zero => simp [z08]
  | succ n ih => simp [z08,List.append_assoc,ih]
lemma z0b (a b : List α) (n : Nat) : (a ++ b) ^ n ++ a = a ++ (b ++ a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [z08,List.append_assoc,ih,z08]
    simp only [List.append_assoc]
lemma z0c (a b : zF) (i : Nat) (s : zB) :
    a +> ((b ++ a) ^ i) +> (b +> s) = ((a ++ b) ^ (i + 1)) +> s := by
  rw [<- append_assoc,<- append_assoc,<- z0b,List.append_assoc,z0a]
lemma z0d (w : List α) (b : Nat) : w ^ (b * 2) = (w ++ w) ^ b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have h1 : (b + 1) * 2 = (b * 2 + 1) + 1 := by omega
    rw [h1,z08,z08,ih,z08,List.append_assoc]
lemma z0e (w : List α) (b : Nat) : w ^ (b * 3) = (w ++ w ++ w) ^ b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have h1 : (b + 1) * 3 = ((b * 3 + 1) + 1) + 1 := by omega
    rw [h1,z08,z08,z08,ih,z08]
    simp [List.append_assoc]
lemma z0f (w : List α) (b : Nat) : w ^ (b * 6) = (w ^ 6) ^ b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    have h1 : (b + 1) * 6 = 6 + b * 6 := by omega
    rw [h1,z09,ih]
    rfl
lemma z0g : ∀ (n : Nat),(([0] : zF) ^ n) +> (default : zB) = default
  | 0 => rfl
  | n + 1 => by simp [z08,z0g n]
lemma z0h (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n
def z0i (d0 d1 : zF) : Nat -> Nat -> zB -> zB
  | 0,_,r => r
  | len + 1,n,r => (if n % 2 = 0 then d1 else d0) +> z0i d0 d1 len (n / 2) r
def z0j (d0 d1 : zF) : Nat -> zB
  | 0 => default
  | n + 1 =>
    let m := n + 1
    (if m % 2 = 0 then d0 else d1) +> z0j d0 d1 (m / 2)
lemma z0k (d0 d1 : zF) (n : Nat) (r : zB) :
    z0i d0 d1 0 n r = r := rfl
lemma z0l (d0 d1 : zF) (len n : Nat) (r : zB) :
    z0i d0 d1 (len + 1) (n * 2) r = d1 +> z0i d0 d1 len n r := by
  simp only [z0i]
  have h1 : (n * 2) % 2 = 0 := by omega
  have h2 : (n * 2) / 2 = n := by omega
  simp [h1,h2]
lemma z0m (d0 d1 : zF) (len n : Nat) (r : zB) :
    z0i d0 d1 (len + 1) (n * 2 + 1) r = d0 +> z0i d0 d1 len n r := by
  simp only [z0i]
  have h1 : (n * 2 + 1) % 2 = 1 := by omega
  have h2 : (n * 2 + 1) / 2 = n := by omega
  simp [h1,h2]
lemma z0n (d0 d1 : zF) (len : Nat) (r : zB) :
    z0i d0 d1 len 0 r = (d1 ^ len) +> r := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have h := z0l d0 d1 len 0 r
    simp only [Nat.zero_mul] at h
    rw [h,ih,z08,append_assoc]
lemma z0o (d0 d1 : zF) (len : Nat) (r : zB) :
    z0i d0 d1 len (2 ^ len - 1) r = (d0 ^ len) +> r := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have hp := z0h len
    have h1 : 2 ^ (len + 1) - 1 = (2 ^ len - 1) * 2 + 1 := by
      rw [Nat.pow_succ]; omega
    rw [h1,z0m,ih,z08,append_assoc]
lemma z0p (d0 d1 : zF) (len n i : Nat) (r : zB) :
    z0i d0 d1 (len + i) (n * 2 ^ i) r = (d1 ^ i) +> z0i d0 d1 len n r := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : len + (i + 1) = (len + i) + 1 := by omega
    have h2 : n * 2 ^ (i + 1) = (n * 2 ^ i) * 2 := by rw [Nat.pow_succ,<- Nat.mul_assoc]
    rw [h1,h2,z0l,ih,z08,append_assoc]
lemma z0q (d0 d1 : zF) (len n i : Nat) (r : zB) :
    z0i d0 d1 (len + 1 + i) ((n * 2 + 1) * 2 ^ i - 1) r =
    (d0 ^ i) +> d1 +> z0i d0 d1 len n r := by
  induction i with
  | zero =>
    have h1 : (n * 2 + 1) * 2 ^ 0 - 1 = n * 2 := by simp
    simp [h1,z0l]
  | succ i ih =>
    have hp := z0h i
    have hpos : 1 <= (n * 2 + 1) * 2 ^ i := Nat.mul_pos (by omega) hp
    have h1 : len + 1 + (i + 1) = (len + 1 + i) + 1 := by omega
    have h2 : (n * 2 + 1) * 2 ^ (i + 1) - 1 = ((n * 2 + 1) * 2 ^ i - 1) * 2 + 1 := by
      rw [Nat.pow_succ,<- Nat.mul_assoc]
      omega
    rw [h1,h2,z0m,ih,z08,append_assoc]
lemma z0r (d0 d1 : zF) : z0j d0 d1 0 = default := by simp [z0j]
lemma z0s (d0 d1 : zF) : z0j d0 d1 1 = d1 +> default := by simp [z0j]
lemma z0t {d0 d1 : zF} (hd0 : d0 +> default = default) (n : Nat) :
    z0j d0 d1 (n * 2) = d0 +> z0j d0 d1 n := by
  cases n with
  | zero => simp [z0j,hd0]
  | succ k =>
    conv_lhs =>
      rw [show (k + 1) * 2 = (k * 2 + 1) + 1 by omega]
      unfold z0j
    simp only [show (k * 2 + 1 + 1) % 2 = 0 by omega,show (k * 2 + 1 + 1) / 2 = k + 1 by omega,↓reduceIte]
lemma z0u (d0 d1 : zF) (n : Nat) :
    z0j d0 d1 (n * 2 + 1) = d1 +> z0j d0 d1 n := by
  simp only [z0j]
  have h1 : (n * 2 + 1) % 2 = 1 := by omega
  have h2 : (n * 2 + 1) / 2 = n := by omega
  simp [h1,h2]
lemma z0v {d0 d1 : zF} (hd0 : d0 +> default = default) (n i : Nat) :
    z0j d0 d1 (n * 2 ^ i) = (d0 ^ i) +> z0j d0 d1 n := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : n * 2 ^ (i + 1) = (n * 2 ^ i) * 2 := by rw [Nat.pow_succ,<- Nat.mul_assoc]
    rw [h1,z0t hd0,ih,z08,append_assoc]
lemma z0w {d0 d1 : zF} (hd0 : d0 +> default = default) (i : Nat) :
    z0j d0 d1 (2 ^ i) = (d0 ^ i) +> d1 +> default := by
  have h1 : 2 ^ i = 1 * 2 ^ i := by omega
  rw [h1,z0v hd0,z0s]
lemma z0x (d0 d1 : zF) (len n : Nat) (r : zB)
    (h : 1 + n < 2 ^ len) :
    ∃ (i : Nat) (s : zB),
      z0i d0 d1 len (1 + n) r = (d1 ^ i) +> d0 +> s /\
      z0i d0 d1 len n r = (d0 ^ i) +> d1 +> s := by
  induction len generalizing n with
  | zero => simp at h
  | succ len ih =>
    have hp : 2 ^ (len + 1) = 2 ^ len * 2 := Nat.pow_succ 2 len
    let k := n / 2
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · have h_even : n = k * 2 := by omega
      have h_odd : 1 + n = k * 2 + 1 := by omega
      refine ⟨0,z0i d0 d1 len k r,?_,?_⟩
      · rw [h_odd,z0m]; rfl
      · rw [h_even,z0l]; rfl
    · have h_odd : n = k * 2 + 1 := by omega
      have h_even : 1 + n = (1 + k) * 2 := by omega
      have h_lt : 1 + k < 2 ^ len := by omega
      rcases ih k h_lt with ⟨i,s,hi1,hi0⟩
      refine ⟨i + 1,s,?_,?_⟩
      · rw [h_even,z0l,hi1,z08,append_assoc]
      · rw [h_odd,z0m,hi0,z08,append_assoc]
lemma z0y {d0 d1 : zF} (hd0 : d0 +> default = default) (n : Nat) :
    ∃ (i : Nat) (s : zB),
      z0j d0 d1 n = (d1 ^ i) +> d0 +> s /\
      z0j d0 d1 (1 + n) = (d0 ^ i) +> d1 +> s := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let k := n / 2
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · have h_even : n = k * 2 := by omega
      have h_odd : 1 + n = k * 2 + 1 := by omega
      refine ⟨0,z0j d0 d1 k,?_,?_⟩
      · rw [h_even,z0t hd0]; rfl
      · rw [h_odd,z0u]; rfl
    · have h_odd : n = k * 2 + 1 := by omega
      have h_even : 1 + n = (1 + k) * 2 := by omega
      have h_lt : k < n := by omega
      rcases ih k h_lt with ⟨i,s,hi0,hi1⟩
      refine ⟨i + 1,s,?_,?_⟩
      · rw [h_odd,z0u,hi0,z08,append_assoc]
      · rw [h_even,z0t hd0,hi1,z08,append_assoc]
def z0z' (tm : Machine (Fin 2) (Fin 6)) (p : Bool) (c0 c1 : Cfg (Fin 2) (Fin 6)) : Prop :=
  if p then c0 [tm]⊢⁺ c1 else c0 [tm]⊢* c1
lemma z0A (tm : Machine (Fin 2) (Fin 6)) (b1 b2 b3 : Bool)
    (c1 c2 c3 : Cfg (Fin 2) (Fin 6))
    (hb : (!b3 || (b1 || b2)) = true)
    (h1 : z0z' tm b1 c1 c2) (h2 : z0z' tm b2 c2 c3) :
    z0z' tm b3 c1 c3 := by
  cases b1 <;> cases b2 <;> cases b3
  · exact zSt h1 h2
  · cases hb
  · exact zSt h1 (zPs h2)
  · exact z06 h1 h2
  · exact zSt (zPs h1) h2
  · exact z05 h1 h2
  · exact zPs (zPt h1 h2)
  · exact zPt h1 h2
lemma z0B (tm : Machine (Fin 2) (Fin 6)) (q : Fin 6) (l0 w0 w0' : zF)
    (H : ∀ l r,((w0 +> l) <{{q}} (l0 +> r)) [tm]⊢* (l <{{q}} (l0 +> w0' +> r)))
    (n : Nat) (l r : zB) :
    (((w0 ^ n) +> l) <{{q}} (l0 +> r)) [tm]⊢* (l <{{q}} (l0 +> (w0' ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [z08,append_assoc]
    have h1 := H ((w0 ^ n) +> l) r
    have h2 := ih l (w0' +> r)
    rw [<- append_assoc (w0' ^ n) w0' r,z0a] at h2
    exact zSt h1 h2
lemma z0C (tm : Machine (Fin 2) (Fin 6)) (q : Fin 6) (l0 w0 w0' : zF)
    (H : ∀ l r,((l0 +> l) {{q}}> (w0 +> r)) [tm]⊢* ((l0 +> w0' +> l) {{q}}> r))
    (n : Nat) (l r : zB) :
    ((l0 +> l) {{q}}> ((w0 ^ n) +> r)) [tm]⊢* ((l0 +> (w0' ^ n) +> l) {{q}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [z08,append_assoc]
    have h1 := H l ((w0 ^ n) +> r)
    have h2 := ih (w0' +> l) r
    rw [<- append_assoc (w0' ^ n) w0' l,z0a] at h2
    exact zSt h1 h2
@[simp] def dirBeq : Dir -> Dir -> Bool
  | .left, .left => true
  | .right, .right => true
  | _, _ => false
lemma dirBeq_eq_true {a b : Dir} (h : dirBeq a b = true) : a = b := by
  cases a <;> cases b <;> cases h <;> rfl
structure z0D where
  l : zF
  r : zF
  s : Fin 6
  sgn : Dir
def z0D.zTcf (x : z0D) (l0 r0 : zB) : Cfg (Fin 2) (Fin 6) :=
  match x.sgn with
  | .left  => (x.r +> l0) <{{x.s}} (x.l +> r0)
  | .right => (x.l +> l0) {{x.s}}> (x.r +> r0)
def z0D.step (tm : Machine (Fin 2) (Fin 6)) (x : z0D) : Option z0D :=
  match x.r with
  | [] => none
  | m :: r0 =>
    match tm x.s m with
    | none => none
    | some (some s',Stmt.write m' sgn') =>
      if dirBeq x.sgn sgn' then
        some ⟨m' :: x.l,r0,s',sgn'⟩
      else
        some ⟨m' :: r0,x.l,s',sgn'⟩
    | some (none,_) => none
def z0D.steps (tm : Machine (Fin 2) (Fin 6)) : Nat -> z0D -> Option z0D
  | 0,x =>
    match z0D.step tm x with
    | none => some x
    | some _ => none
  | n + 1,x =>
    match z0D.step tm x with
    | none => some x
    | some x' => z0D.steps tm n x'
lemma z0D.step_spec (tm : Machine (Fin 2) (Fin 6)) {x x' : z0D}
    (h : z0D.step tm x = some x') (l0 r0 : zB) :
    (z0D.zTcf x l0 r0) [tm]⊢ (z0D.zTcf x' l0 r0) := by
  rcases x with ⟨l,_ | ⟨m,r⟩,s,sgn⟩
  · cases h
  · dsimp [z0D.step] at h
    cases htm : tm s m with
    | none => rw [htm] at h; cases h
    | some val =>
      rcases val with ⟨_ | s',m'd⟩
      · rw [htm] at h; cases h
      · rcases m'd with ⟨m',sgn'⟩
        rw [htm] at h
        cases sgn <;> cases sgn' <;>
        · dsimp at h
          injection h with h'
          subst h'
          simp [z0D.zTcf,BusyBeaver.step,htm,Tape.write,Tape.move]
lemma z0D.steps_spec (tm : Machine (Fin 2) (Fin 6)) :
    ∀ (n : Nat) {x x' : z0D},
      z0D.steps tm n x = some x' ->
      ∀ (l0 r0 : zB),
        (z0D.zTcf x l0 r0) [tm]⊢* (z0D.zTcf x' l0 r0)
  | 0,x,x',h,l0,r0 => by
    dsimp [z0D.steps] at h
    cases hs : z0D.step tm x with
    | none => rw [hs] at h; injection h with h'; subst h'; exact ⟨0,rfl⟩
    | some _ => rw [hs] at h; cases h
  | n + 1,x,x',h,l0,r0 => by
    dsimp [z0D.steps] at h
    cases hs : z0D.step tm x with
    | none => rw [hs] at h; injection h with h'; subst h'; exact ⟨0,rfl⟩
    | some x1 =>
      rw [hs] at h
      exact zSt
        (z02 tm _ _ (z0D.step_spec tm hs l0 r0))
        (z0D.steps_spec tm n h l0 r0)
inductive vside where
  | cons (h : Fin 2) (t : vside)
  | app (h : zF) (n : Nat) (t : vside)
  | zinf
  | var (i : Nat)
  deriving DecidableEq
inductive vconfig where
  | L (l r : vside) (q : Fin 6)
  | R (l r : vside) (q : Fin 6)
  | mid (l r : vside) (m : Fin 2) (q : Fin 6)
  deriving DecidableEq
@[simp] def zTs (nmp : Nat -> Nat) (smp : Nat -> zB) : vside -> zB
  | .cons h t => h >> zTs nmp smp t
  | .app h n t => (h ^ nmp n) +> zTs nmp smp t
  | .zinf => default
  | .var i => smp i
@[simp] def zTcf (nmp : Nat -> Nat) (smp : Nat -> zB) : vconfig -> Cfg (Fin 2) (Fin 6)
  | .L l r q => (zTs nmp smp l) <{{q}} (zTs nmp smp r)
  | .R l r q => (zTs nmp smp l) {{q}}> (zTs nmp smp r)
  | .mid l r m q => ⟨some q,⟨m,zTs nmp smp l,zTs nmp smp r⟩⟩
def z0E : vconfig -> vconfig
  | .L (.cons m l) r q => .mid l r m q
  | .L .zinf r q => .mid .zinf r 0 q
  | .R l (.cons m r) q => .mid l r m q
  | .R l .zinf q => .mid l .zinf 0 q
  | x => x
lemma z0F (nmp : Nat -> Nat) (smp : Nat -> zB) (x : vconfig) :
    zTcf nmp smp (z0E x) = zTcf nmp smp x := by
  cases x with
  | L l r q => cases l <;> simp [z0E,zTcf,zTs]
  | R l r q => cases r <;> simp [z0E,zTcf,zTs]
  | mid l r m q => rfl
def z0G (h : Fin 2) (t : vside) : vside :=
  match t with
  | .zinf => if h == 0 then .zinf else .cons h t
  | _ => .cons h t
lemma z0H (nmp : Nat -> Nat) (smp : Nat -> zB) (h : Fin 2) (x : vside) :
    zTs nmp smp (z0G h x) = h >> zTs nmp smp x := by
  cases x with
  | zinf =>
    dsimp [z0G]
    rcases h with ⟨_ | _ | h,hh⟩
    · simp [zTs]
    · rfl
    · omega
  | _ => rfl
lemma z0I (h0 : Fin 2) (h1 : zF) (m : Nat) (s : zB) :
    ((h0 :: h1) ^ m) +> (h0 >> s) = h0 >> (((h1 ++ [h0]) ^ m) +> s) := by
  have h_eq : h0 >> s = [h0] +> s := rfl
  rw [h_eq,<- append_assoc,show h0 :: h1 = [h0] ++ h1 from rfl,z0b [h0] h1 m,append_assoc]
  rfl
def z0J' (h : zF) (n : Nat) : vside -> vside
  | .cons h' t =>
    match h with
    | [] => .app [] n (.cons h' t)
    | h0 :: h1 =>
      if h0 == h' then .cons h0 (z0J' (h1 ++ [h0]) n t)
      else .app (h0 :: h1) n (.cons h' t)
  | x => .app h n x
lemma z0K (nmp : Nat -> Nat) (smp : Nat -> zB)
    (h : zF) (n : Nat) (x : vside) :
    zTs nmp smp (z0J' h n x) = zTs nmp smp (.app h n x) := by
  induction x generalizing h with
  | cons h' t ih =>
    cases h with
    | nil => rfl
    | cons h0 h1 =>
      dsimp [z0J']
      by_cases heq : h0 = h'
      · subst heq
        simp only [beq_self_eq_true,↓reduceIte,zTs,ih (h1 ++ [h0])]
        exact (z0I h0 h1 (nmp n) (zTs nmp smp t)).symm
      · have hbeq : (h0 == h') = false := beq_false_of_ne heq
        simp [hbeq,zTs]
  | _ => rfl
def z0J : vside -> vside
  | .cons h t => z0G h (z0J t)
  | .app h n t => z0J' h n (z0J t)
  | x => x
lemma z0L (nmp : Nat -> Nat) (smp : Nat -> zB) (x : vside) :
    zTs nmp smp (z0J x) = zTs nmp smp x := by
  induction x with
  | cons h t ih =>
    simp only [z0J,z0H,ih,zTs]
  | app h n t ih =>
    simp only [z0J,z0K,zTs,ih]
  | _ => rfl
def z0M : vconfig -> vconfig
  | .L l r q => .L (z0J l) (z0J r) q
  | .R l r q => .R (z0J l) (z0J r) q
  | .mid l r m q => .mid (z0J l) (z0J r) m q
lemma z0N (nmp : Nat -> Nat) (smp : Nat -> zB) (x : vconfig) :
    zTcf nmp smp (z0M x) = zTcf nmp smp x := by
  cases x <;> simp [z0M,zTcf,z0L]
def z0O (tm : Machine (Fin 2) (Fin 6)) : vconfig -> Option vconfig
  | .mid l r m q =>
    match tm q m with
    | none => none
    | some (some q',Stmt.write m' .left) => some (.L l (.cons m' r) q')
    | some (some q',Stmt.write m' .right) => some (.R (.cons m' l) r q')
    | some (none,_) => none
  | _ => none
lemma z0P (tm : Machine (Fin 2) (Fin 6)) (nmp : Nat -> Nat) (smp : Nat -> zB)
    {x x0 : vconfig} (h : z0O tm x = some x0) :
    z0z' tm true (zTcf nmp smp x) (zTcf nmp smp x0) := by
  cases x with
  | mid l r m q =>
    dsimp [z0O] at h
    cases htm : tm q m with
    | none => rw [htm] at h; cases h
    | some val =>
      rcases val with ⟨_ | q',m'd⟩
      · rw [htm] at h; cases h
      · rcases m'd with ⟨m',_ | _⟩
        · rw [htm] at h; injection h with h'; subst h'
          exact z03 tm _ _ (by simp [zTcf,zTs,step,htm,Tape.write,Tape.move])
        · rw [htm] at h; injection h with h'; subst h'
          exact z03 tm _ _ (by simp [zTcf,zTs,step,htm,Tape.write,Tape.move])
  | _ => cases h
def z0Q (tm : Machine (Fin 2) (Fin 6)) : Nat -> vconfig -> vconfig -> Bool -> Option (vconfig × vconfig × Bool)
  | 0,x,y,b => some (x,y,b)
  | T + 1,x,y,b =>
    let x0 := z0E x
    if (x0 == y) && (!b) then none
    else
      match z0O tm x0 with
      | some x1 => z0Q tm T x1 y false
      | none => some (x0,y,b)
lemma z0R (tm : Machine (Fin 2) (Fin 6)) (nmp : Nat -> Nat) (smp : Nat -> zB) :
    ∀ (T : Nat) (x y : vconfig) (b : Bool),
      match z0Q tm T x y b with
      | none => z0z' tm b (zTcf nmp smp x) (zTcf nmp smp y)
      | some (x',y',b') =>
        z0z' tm b' (zTcf nmp smp x') (zTcf nmp smp y') ->
        z0z' tm b (zTcf nmp smp x) (zTcf nmp smp y)
  | 0,x,y,b => id
  | T + 1,x,y,b => by
    dsimp only [z0Q]
    set x0 := z0E x
    have hx0 : zTcf nmp smp x0 = zTcf nmp smp x := z0F nmp smp x
    by_cases hcond : ((x0 == y) && (!b)) = true
    · simp only [hcond,↓reduceIte]
      rw [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hcond
      rcases hcond with ⟨rfl,rfl⟩
      rw [<- hx0]
      exact ⟨0,rfl⟩
    · have hcond_f : ((x0 == y) && (!b)) = false := Bool.eq_false_iff.mpr hcond
      simp only [hcond_f,Bool.false_eq_true,↓reduceIte]
      cases hs : z0O tm x0 with
      | none =>
        dsimp only
        intro h
        rwa [<- hx0]
      | some x1 =>
        dsimp only
        have hstep := z0P tm nmp smp hs
        rw [hx0] at hstep
        have ih := z0R tm nmp smp T x1 y false
        cases h_rec : z0Q tm T x1 y false with
        | none =>
          rw [h_rec] at ih
          exact z0A tm true false b _ _ _ (by cases b <;> rfl) hstep ih
        | some res =>
          rcases res with ⟨x',y',b'⟩
          rw [h_rec] at ih
          intro h'
          exact z0A tm true false b _ _ _ (by cases b <;> rfl) hstep (ih h')
def z0S : vside -> Nat -> Option (vside × zF)
  | x,0 => some (x,[])
  | .cons h t,n + 1 =>
    match z0S t n with
    | some (x0,x1) => some (x0,h :: x1)
    | none => none
  | .zinf,n + 1 => some (.zinf,([0] : zF) ^ (n + 1))
  | _,_ + 1 => none
def z0T : zF -> vside -> vside
  | [],x0 => x0
  | h :: t,x0 => .cons h (z0T t x0)
abbrev vlit (w : zF) (t : vside) : vside := z0T w t
@[simp] lemma z0U (nmp : Nat -> Nat) (smp : Nat -> zB)
    (seg : zF) (x0 : vside) :
    zTs nmp smp (z0T seg x0) = seg +> zTs nmp smp x0 := by
  induction seg with
  | nil => rfl
  | cons h t ih => simp [z0T,zTs,ih]
lemma z0V (nmp : Nat -> Nat) (smp : Nat -> zB) :
    ∀ (n : Nat) (x x1 : vside) (x0 : zF),
      z0S x n = some (x1,x0) ->
      zTs nmp smp x = x0 +> zTs nmp smp x1
  | 0,x,x1,x0,h => by
    cases x <;> { injection h with hpair; cases hpair; rfl }
  | n + 1,.cons a t,x1,x0,h => by
    dsimp [z0S] at h
    cases hs : z0S t n with
    | none => rw [hs] at h; cases h
    | some pair =>
      rcases pair with ⟨x1',x0'⟩
      rw [hs] at h
      injection h with hpair
      cases hpair
      have ih := z0V nmp smp n t _ _ hs
      simp [zTs,ih]
  | n + 1,.zinf,x1,x0,h => by
    dsimp [z0S] at h
    injection h with hpair
    cases hpair
    simp only [zTs]
    exact (z0g (n + 1)).symm
  | _ + 1,.app _ _ _,_,_,h => by cases h
  | _ + 1,.var _,_,_,h => by cases h
def z0W (tm : Machine (Fin 2) (Fin 6)) (l0 : zF) (l1 r : vside) (q : Fin 6) (d : Dir) (T : Nat) : Option vconfig :=
  match r with
  | .app r0 i r1 =>
    match z0D.steps tm T ⟨l0,r0,q,d⟩ with
    | some ⟨l0',r0',q',d'⟩ =>
      if (dirBeq d d') && (q == q') && (r0' == []) && (l0'.take l0.length == l0) then
        let l' := z0T l0 (.app (l0'.drop l0.length) i l1)
        match d with
        | .left  => some (.L r1 l' q)
        | .right => some (.R l' r1 q)
      else none
    | none => none
  | _ => none
lemma z0X (tm : Machine (Fin 2) (Fin 6)) (nmp : Nat -> Nat) (smp : Nat -> zB)
    {l0 : zF} {l1 r : vside} {q : Fin 6} {d : Dir} {T : Nat} {res : vconfig}
    (h : z0W tm l0 l1 r q d T = some res) :
    (zTcf nmp smp (match d with | .left => .L r (z0T l0 l1) q | .right => .R (z0T l0 l1) r q))
      [tm]⊢* (zTcf nmp smp res) := by
  cases r with
  | app r0 i r1 =>
    dsimp only [z0W] at h
    cases hs : z0D.steps tm T ⟨l0,r0,q,d⟩ with
    | none => rw [hs] at h; cases h
    | some cfg' =>
      rcases cfg' with ⟨l0',r0',q',d'⟩
      rw [hs] at h
      dsimp only at h
      split_ifs at h with hcond
      simp only [Bool.and_eq_true,beq_iff_eq] at hcond
      rcases hcond with ⟨⟨⟨hd,rfl⟩,rfl⟩,htake⟩
      cases dirBeq_eq_true hd
      have h_steps := z0D.steps_spec tm T hs
      have h_split : l0 ++ l0'.drop l0.length = l0' := by
        conv_rhs => rw [<- List.take_append_drop l0.length l0',htake]
      cases d
      · injection h with hres; subst hres
        dsimp [zTcf,zTs]
        rw [z0U,z0U]
        dsimp [zTs]
        refine z0B tm q l0 r0 (l0'.drop l0.length) (fun l' r' => ?_) (nmp i)
          (zTs nmp smp r1) (zTs nmp smp l1)
        have h1 := h_steps l' r'
        dsimp [z0D.zTcf] at h1
        rwa [<- h_split,append_assoc] at h1
      · injection h with hres; subst hres
        dsimp [zTcf,zTs]
        rw [z0U,z0U]
        dsimp [zTs]
        refine z0C tm q l0 r0 (l0'.drop l0.length) (fun l' r' => ?_) (nmp i)
          (zTs nmp smp l1) (zTs nmp smp r1)
        have h1 := h_steps l' r'
        dsimp [z0D.zTcf] at h1
        rwa [<- h_split,append_assoc] at h1
  | _ => cases h
def z0Y (tm : Machine (Fin 2) (Fin 6)) (l r : vside) (q : Fin 6) (d : Dir) : Nat -> Nat -> Nat -> Option vconfig
  | 0,_,_ => none
  | n + 1,n',T =>
    match z0S l n' with
    | some (l1,l0) =>
      match z0W tm l0 l1 r q d T with
      | some res => some res
      | none => z0Y tm l r q d n (n' + 1) T
    | none => none
lemma z0Z (tm : Machine (Fin 2) (Fin 6)) (nmp : Nat -> Nat) (smp : Nat -> zB)
    (l r : vside) (q : Fin 6) (d : Dir) :
    ∀ (n n' T : Nat) {res : vconfig},
      z0Y tm l r q d n n' T = some res ->
      (zTcf nmp smp (match d with | .left => .L r l q | .right => .R l r q))
        [tm]⊢* (zTcf nmp smp res)
  | 0,_,_,_,h => by cases h
  | n + 1,n',T,res,h => by
    dsimp [z0Y] at h
    cases hs : z0S l n' with
    | none => rw [hs] at h; cases h
    | some pair =>
      rcases pair with ⟨l1,l0⟩
      rw [hs] at h
      dsimp only at h
      have hsplit := z0V nmp smp n' l l1 l0 hs
      cases hc : z0W tm l0 l1 r q d T with
      | some res' =>
        rw [hc] at h; injection h with h'; subst h'
        have hchk := z0X tm nmp smp hc
        cases d <;>
        · dsimp [zTcf] at hchk ⊢
          rw [z0U,<- hsplit] at hchk
          exact hchk
      | none =>
        rw [hc] at h
        exact z0Z tm nmp smp l r q d n (n' + 1) T h
def z10 (tm : Machine (Fin 2) (Fin 6)) (x : vconfig) (T : Nat) : Option vconfig :=
  match x with
  | .L l r q => z0Y tm r l q .left T 0 T
  | .R l r q => z0Y tm l r q .right T 0 T
  | .mid _ _ _ _ => none
lemma z11 (tm : Machine (Fin 2) (Fin 6)) (nmp : Nat -> Nat) (smp : Nat -> zB)
    {x res : vconfig} {T : Nat} (h : z10 tm x T = some res) :
    z0z' tm false (zTcf nmp smp x) (zTcf nmp smp res) := by
  cases x with
  | L l r q => exact z0Z tm nmp smp r l q .left T 0 T h
  | R l r q => exact z0Z tm nmp smp l r q .right T 0 T h
  | mid _ _ _ _ => cases h
def z12 (tm : Machine (Fin 2) (Fin 6)) (x y : vconfig) (b : Bool) (T : Nat) : Option (vconfig × vconfig × Bool) :=
  z0Q tm T (z0M x) y b
lemma z13 (tm : Machine (Fin 2) (Fin 6)) (nmp : Nat -> Nat) (smp : Nat -> zB)
    (x y : vconfig) (b : Bool) (T : Nat) :
    match z12 tm x y b T with
    | none => z0z' tm b (zTcf nmp smp x) (zTcf nmp smp y)
    | some (x0,y0,b0) =>
      z0z' tm b0 (zTcf nmp smp x0) (zTcf nmp smp y0) ->
      z0z' tm b (zTcf nmp smp x) (zTcf nmp smp y) := by
  unfold z12
  have h := z0R tm nmp smp T (z0M x) y b
  rw [z0N] at h
  exact h
def z14 (tm : Machine (Fin 2) (Fin 6)) : Nat -> vconfig -> vconfig -> Bool -> Nat -> Nat -> Option (vconfig × vconfig × Bool)
  | 0,x,y,b,_,_ => some (x,y,b)
  | T_out + 1,x,y,b,T_step,T_sr =>
    match z12 tm x y b T_step with
    | none => none
    | some (x0,y0,b0) =>
      match z10 tm x0 T_sr with
      | none => some (x0,y0,b0)
      | some x1 => z14 tm T_out x1 y0 b0 T_step T_sr
lemma z15 (tm : Machine (Fin 2) (Fin 6)) (nmp : Nat -> Nat) (smp : Nat -> zB) :
    ∀ (T_out : Nat) (x y : vconfig) (b : Bool) (T_step T_sr : Nat),
      z14 tm T_out x y b T_step T_sr = none ->
      z0z' tm b (zTcf nmp smp x) (zTcf nmp smp y)
  | 0,_,_,_,_,_,h => by cases h
  | T_out + 1,x,y,b,T_step,T_sr,h => by
    dsimp [z14] at h
    have her := z13 tm nmp smp x y b T_step
    cases he : z12 tm x y b T_step with
    | none => rw [he] at her; exact her
    | some trip =>
      rcases trip with ⟨x0,y0,b0⟩
      rw [he] at h her
      dsimp only at h her
      cases hs : z10 tm x0 T_sr with
      | none => rw [hs] at h; cases h
      | some x1 =>
        rw [hs] at h
        have hsr := z11 tm nmp smp hs
        have ih := z15 tm nmp smp T_out x1 y0 b0 T_step T_sr h
        exact her (z0A tm false b0 b0 _ _ _ (by cases b0 <;> rfl) hsr ih)
def z16 (tm : Machine (Fin 2) (Fin 6)) (x y : vconfig) (b : Bool) (T_out T_step T_sr : Nat) : Option (vconfig × vconfig × Bool) :=
  let y1 := z0E (z0M y)
  z14 tm T_out x y1 b T_step T_sr
lemma z17 (tm : Machine (Fin 2) (Fin 6)) (nmp : Nat -> Nat) (smp : Nat -> zB)
    (x y : vconfig) (b : Bool) (T_out T_step T_sr : Nat)
    (h : z16 tm x y b T_out T_step T_sr = none) :
    z0z' tm b (zTcf nmp smp x) (zTcf nmp smp y) := by
  have h1 := z15 tm nmp smp T_out x (z0E (z0M y)) b T_step T_sr h
  rwa [z0F,z0N] at h1
abbrev o1 : zF := [1]
abbrev ld0 : zF := [0,1]
abbrev ld1 : zF := [1,1]
abbrev ldh : zB := [1] +> default
abbrev z : zF := [0,0,0]
abbrev d : zF := [1,0,0]
def z18 (l r : zB) : Cfg (Fin 2) (Fin 6) :=
  l <{{B}} ([1,1,1,0,0] +> r)
def z19 (l r : zB) : Cfg (Fin 2) (Fin 6) :=
  ([1,1,1,0,1] +> l) {{C}}> r
def z1a (a : Nat) : Nat -> Nat | 0 => a | _ => 0
def z1b (a b : Nat) : Nat -> Nat | 0 => a | 1 => b | _ => 0
def z1c (l : zB) : Nat -> zB | 0 => l | _ => default
def z1d (l r : zB) : Nat -> zB | 0 => l | 1 => r | _ => default
lemma z1e (b : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (1 + b * 2)) +> z +> (o1 ^ 4) +> default)) [z00]⊢*
    (z18 ((o1 ^ 5) +> (([1,0] ^ b) +> l)) default) := by
  have h := z17 z00 (z1a b) (z1c l)
    (.R (.var 0) (vlit [1] (.app [1,1] 0 (vlit [0,0,0,1,1,1,1] .zinf))) D)
    (.L (vlit [1,1,1,1,1] (.app [1,0] 0 (.var 0))) (vlit [1,1,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z18,z09,z0d,append_assoc] using h
lemma z1f (b c : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (3 + b * 2)) +> z +> (o1 ^ (6 + c * 2)) +> default)) [z00]⊢*
    (z19 ((ld0 ^ (4 + c)) +> [1] +> (([1,0] ^ b) +> l)) default) := by
  have h := z17 z00 (z1b b c) (z1c l)
    (.R (.var 0) (vlit [1,1,1] (.app [1,1] 0 (vlit [0,0,0,1,1,1,1,1,1] (.app [1,1] 1 .zinf)))) D)
    (.R (vlit [1,1,1,0,1] (vlit (ld0 ^ 4) (.app ld0 1 (vlit [1] (.app [1,0] 0 (.var 0)))))) .zinf C)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z19,z09,z0d,append_assoc] using h
lemma z1g (b c : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (3 + b * 2)) +> z +> (o1 ^ (3 + c * 2)) +> default)) [z00]⊢*
    (z18 ((ld0 ^ (2 + c)) +> [1] +> (([1,0] ^ b) +> l)) ([0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1b b c) (z1c l)
    (.R (.var 0) (vlit [1,1,1] (.app [1,1] 0 (vlit [0,0,0,1,1,1] (.app [1,1] 1 .zinf)))) D)
    (.L (vlit (ld0 ^ 2) (.app ld0 1 (vlit [1] (.app [1,0] 0 (.var 0))))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z18,z09,z0d,append_assoc] using h
lemma z1h (n : Nat) (l r : zB) :
    (z18 ((ld1 ^ n) +> [1,0,1] +> l) r) [z00]⊢*
    (((ld1 ^ 2) +> (ld0 ^ (1 + n)) +> ld1 +> l) {{D}}> r) := by
  have h := z17 z00 (z1a n) (z1d l r)
    (.L (.app ld1 0 (vlit [1,0,1] (.var 0))) (vlit [1,1,1,0,0] (.var 1)) B)
    (.R (vlit (ld1 ^ 2) (vlit ld0 (.app ld0 0 (vlit ld1 (.var 0))))) (.var 1) D)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1d,z18,z09,append_assoc] using h
lemma z1i (h_idx : Nat) (l r : zB) :
    (((ld1 ^ 2) +> (ld0 ^ 2) +> l) {{D}}> ((d ^ h_idx) +> z +> r)) [z00]⊢*
    (z18 (ld0 +> l) ((z ^ (1 + h_idx)) +> [1] +> r)) := by
  have h := z17 z00 (z1a h_idx) (z1d l r)
    (.R (vlit (ld1 ^ 2) (vlit (ld0 ^ 2) (.var 0))) (.app d 0 (vlit z (.var 1))) D)
    (.L (vlit ld0 (.var 0)) (vlit [1,1,1,0,0] (vlit z (.app z 0 (vlit [1] (.var 1))))) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1d,z18,z09,append_assoc] using h
lemma z1j (b c : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (4 + b * 2)) +> z +> (o1 ^ (4 + c * 2)) +> default)) [z00]⊢*
    (z19 ((ld0 ^ (1 + c)) +> ld1 +> [1,0,1,1] +> (([1,0] ^ b) +> l)) default) := by
  have h := z17 z00 (z1b b c) (z1c l)
    (.R (.var 0) (vlit [1,1,1,1] (.app [1,1] 0 (vlit [0,0,0,1,1,1,1] (.app [1,1] 1 .zinf)))) D)
    (.R (vlit [1,1,1,0,1] (vlit ld0 (.app ld0 1 (vlit ld1 (vlit [1,0,1,1] (.app [1,0] 0 (.var 0))))))) .zinf C)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z19,z09,z0d,append_assoc] using h
lemma z1k (b c : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (4 + b * 2)) +> z +> (o1 ^ (5 + c * 2)) +> default)) [z00]⊢*
    (z18 ((ld0 ^ (1 + c)) +> ld1 +> [1,0,1,1] +> (([1,0] ^ b) +> l)) ([0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1b b c) (z1c l)
    (.R (.var 0) (vlit [1,1,1,1] (.app [1,1] 0 (vlit [0,0,0,1,1,1,1,1] (.app [1,1] 1 .zinf)))) D)
    (.L (vlit ld0 (.app ld0 1 (vlit ld1 (vlit [1,0,1,1] (.app [1,0] 0 (.var 0)))))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z18,z09,z0d,append_assoc] using h
lemma z1l (b : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (1 + b * 2)) +> [0,0,0,1,1] +> default)) [z00]⊢*
    (z18 ((o1 ^ 3) +> (([1,0] ^ b) +> l)) default) := by
  have h := z17 z00 (z1a b) (z1c l)
    (.R (.var 0) (vlit [1] (.app [1,1] 0 (vlit [0,0,0,1,1] .zinf))) D)
    (.L (vlit [1,1,1] (.app [1,0] 0 (.var 0))) (vlit [1,1,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z18,z09,z0d,append_assoc] using h
lemma z1m (b : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (4 + b * 2)) +> [0,0,0,1,1] +> default)) [z00]⊢*
    (z18 (ld0 +> [1,0,1,1] +> (([1,0] ^ b) +> l)) default) := by
  have h := z17 z00 (z1a b) (z1c l)
    (.R (.var 0) (vlit [1,1,1,1] (.app [1,1] 0 (vlit [0,0,0,1,1] .zinf))) D)
    (.L (vlit ld0 (vlit [1,0,1,1] (.app [1,0] 0 (.var 0)))) (vlit [1,1,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z18,z09,z0d,append_assoc] using h
lemma z1n (a c : Nat) (l : zB) :
    (((o1 ^ (4 + a * 2)) +> ld0 +> l) {{D}}> ([1,0,0,0] +> (o1 ^ (2 + c * 2)) +> default)) [z00]⊢*
    (z18 ((ld0 ^ (3 + a + c)) +> ld1 +> l) ([0,0,0,1,0,0] +> default)) := by
  rcases c with _ | _ | c
  · have h := z17 z00 (z1a a) (z1c l)
      (.R (vlit [1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1,1] .zinf) D)
      (.L (vlit (ld0 ^ 3) (.app ld0 0 (vlit ld1 (.var 0)))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
      false 15 60 25 (by decide +kernel)
    simpa [z0z',z1a,z1c,z18,z09,z0d,append_assoc] using h
  · have h := z17 z00 (z1a a) (z1c l)
      (.R (vlit [1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1,1,1,1] .zinf) D)
      (.L (vlit (ld0 ^ 4) (.app ld0 0 (vlit ld1 (.var 0)))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
      false 15 60 25 (by decide +kernel)
    have h1 : 3 + a + 1 = 4 + a := by omega
    rw [h1]
    simpa [z0z',z1a,z1c,z18,z09,z0d,append_assoc] using h
  · have h := z17 z00 (z1b a c) (z1c l)
      (.R (vlit [1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1,1,1,1,1,1] (.app [1,1] 1 .zinf)) D)
      (.L (vlit (ld0 ^ 5) (.app ld0 1 (.app ld0 0 (vlit ld1 (.var 0))))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
      false 15 60 25 (by decide +kernel)
    have h1 : 2 + (c + 1 + 1) * 2 = 6 + c * 2 := by omega
    have h2 : 3 + a + (c + 1 + 1) = 5 + c + a := by omega
    rw [h1,h2]
    simpa [z0z',z1b,z1c,z18,z09,z0d,append_assoc] using h
lemma z1o (a c : Nat) (l : zB) :
    (((o1 ^ (4 + a * 2)) +> ld0 +> l) {{D}}> ([1,0,0,0] +> (o1 ^ (1 + c * 2)) +> default)) [z00]⊢*
    (z19 ((ld0 ^ (3 + a + c)) +> ld1 +> l) default) := by
  rcases c with _ | _ | c
  · have h := z17 z00 (z1a a) (z1c l)
      (.R (vlit [1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1] .zinf) D)
      (.R (vlit [1,1,1,0,1] (vlit (ld0 ^ 3) (.app ld0 0 (vlit ld1 (.var 0))))) .zinf C)
      false 15 60 25 (by decide +kernel)
    simpa [z0z',z1a,z1c,z19,z09,z0d,append_assoc] using h
  · have h := z17 z00 (z1a a) (z1c l)
      (.R (vlit [1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1,1,1] .zinf) D)
      (.R (vlit [1,1,1,0,1] (vlit (ld0 ^ 4) (.app ld0 0 (vlit ld1 (.var 0))))) .zinf C)
      false 15 60 25 (by decide +kernel)
    have h1 : 3 + a + 1 = 4 + a := by omega
    rw [h1]
    simpa [z0z',z1a,z1c,z19,z09,z0d,append_assoc] using h
  · have h := z17 z00 (z1b a c) (z1c l)
      (.R (vlit [1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1,1,1,1,1] (.app [1,1] 1 .zinf)) D)
      (.R (vlit [1,1,1,0,1] (vlit (ld0 ^ 5) (.app ld0 1 (.app ld0 0 (vlit ld1 (.var 0)))))) .zinf C)
      false 15 60 25 (by decide +kernel)
    have h1 : 1 + (c + 1 + 1) * 2 = 5 + c * 2 := by omega
    have h2 : 3 + a + (c + 1 + 1) = 5 + c + a := by omega
    rw [h1,h2]
    simpa [z0z',z1b,z1c,z19,z09,z0d,append_assoc] using h
lemma z1p (a c : Nat) (l : zB) :
    (((o1 ^ (5 + a * 2)) +> ld0 +> l) {{D}}> ([1,0,0,0] +> (o1 ^ (2 + c * 2)) +> default)) [z00]⊢*
    (z19 ((ld0 ^ (4 + a + c)) +> ld1 +> l) default) := by
  rcases c with _ | _ | c
  · have h := z17 z00 (z1a a) (z1c l)
      (.R (vlit [1,1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1,1] .zinf) D)
      (.R (vlit [1,1,1,0,1] (vlit (ld0 ^ 4) (.app ld0 0 (vlit ld1 (.var 0))))) .zinf C)
      false 15 60 25 (by decide +kernel)
    simpa [z0z',z1a,z1c,z19,z09,z0d,append_assoc] using h
  · have h := z17 z00 (z1a a) (z1c l)
      (.R (vlit [1,1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1,1,1,1] .zinf) D)
      (.R (vlit [1,1,1,0,1] (vlit (ld0 ^ 5) (.app ld0 0 (vlit ld1 (.var 0))))) .zinf C)
      false 15 60 25 (by decide +kernel)
    have h1 : 4 + a + 1 = 5 + a := by omega
    rw [h1]
    simpa [z0z',z1a,z1c,z19,z09,z0d,append_assoc] using h
  · have h := z17 z00 (z1b a c) (z1c l)
      (.R (vlit [1,1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1,1,1,1,1,1] (.app [1,1] 1 .zinf)) D)
      (.R (vlit [1,1,1,0,1] (vlit (ld0 ^ 6) (.app ld0 1 (.app ld0 0 (vlit ld1 (.var 0)))))) .zinf C)
      false 15 60 25 (by decide +kernel)
    have h1 : 2 + (c + 1 + 1) * 2 = 6 + c * 2 := by omega
    have h2 : 4 + a + (c + 1 + 1) = 6 + c + a := by omega
    rw [h1,h2]
    simpa [z0z',z1b,z1c,z19,z09,z0d,append_assoc] using h
lemma z1q (a c : Nat) (l : zB) :
    (((o1 ^ (5 + a * 2)) +> ld0 +> l) {{D}}> ([1,0,0,0] +> (o1 ^ (1 + c * 2)) +> default)) [z00]⊢*
    (z18 ((ld0 ^ (3 + a + c)) +> ld1 +> l) ([0,0,0,1,0,0] +> default)) := by
  rcases c with _ | _ | c
  · have h := z17 z00 (z1a a) (z1c l)
      (.R (vlit [1,1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1] .zinf) D)
      (.L (vlit (ld0 ^ 3) (.app ld0 0 (vlit ld1 (.var 0)))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
      false 15 60 25 (by decide +kernel)
    simpa [z0z',z1a,z1c,z18,z09,z0d,append_assoc] using h
  · have h := z17 z00 (z1a a) (z1c l)
      (.R (vlit [1,1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1,1,1] .zinf) D)
      (.L (vlit (ld0 ^ 4) (.app ld0 0 (vlit ld1 (.var 0)))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
      false 15 60 25 (by decide +kernel)
    have h1 : 3 + a + 1 = 4 + a := by omega
    rw [h1]
    simpa [z0z',z1a,z1c,z18,z09,z0d,append_assoc] using h
  · have h := z17 z00 (z1b a c) (z1c l)
      (.R (vlit [1,1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,0,0,0,1,1,1,1,1] (.app [1,1] 1 .zinf)) D)
      (.L (vlit (ld0 ^ 5) (.app ld0 1 (.app ld0 0 (vlit ld1 (.var 0))))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
      false 15 60 25 (by decide +kernel)
    have h1 : 1 + (c + 1 + 1) * 2 = 5 + c * 2 := by omega
    have h2 : 3 + a + (c + 1 + 1) = 5 + c + a := by omega
    rw [h1,h2]
    simpa [z0z',z1b,z1c,z18,z09,z0d,append_assoc] using h
lemma z1r (a c : Nat) (l : zB) :
    (((o1 ^ (4 + a * 2)) +> ld0 +> l) {{D}}> ([1,1,0,0,0] +> (o1 ^ (4 + c * 2)) +> default)) [z00]⊢*
    (z18 ((ld0 ^ (1 + c)) +> ld1 +> [1,0,1] +> (ld0 ^ (1 + a)) +> ld1 +> l) ([0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1b a c) (z1c l)
    (.R (vlit [1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,1,0,0,0,1,1,1,1] (.app [1,1] 1 .zinf)) D)
    (.L (vlit ld0 (.app ld0 1 (vlit ld1 (vlit [1,0,1] (vlit ld0 (.app ld0 0 (vlit ld1 (.var 0)))))))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z18,z09,z0d,append_assoc] using h
lemma z1s (a c : Nat) (l : zB) :
    (((o1 ^ (4 + a * 2)) +> ld0 +> l) {{D}}> ([1,1,0,0,0] +> (o1 ^ (5 + c * 2)) +> default)) [z00]⊢*
    (z19 ((ld0 ^ (2 + c)) +> ld1 +> [1,0,1] +> (ld0 ^ (1 + a)) +> ld1 +> l) default) := by
  have h := z17 z00 (z1b a c) (z1c l)
    (.R (vlit [1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,1,0,0,0,1,1,1,1,1] (.app [1,1] 1 .zinf)) D)
    (.R (vlit [1,1,1,0,1] (vlit (ld0 ^ 2) (.app ld0 1 (vlit ld1 (vlit [1,0,1] (vlit ld0 (.app ld0 0 (vlit ld1 (.var 0))))))))) .zinf C)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z19,z09,z0d,append_assoc] using h
lemma z1t (a c : Nat) (l : zB) :
    (((o1 ^ (5 + a * 2)) +> ld0 +> l) {{D}}> ([1,1,0,0,0] +> (o1 ^ (4 + c * 2)) +> default)) [z00]⊢*
    (z19 ((ld0 ^ (1 + c)) +> ld1 +> [1,0,1] +> (ld0 ^ (2 + a)) +> ld1 +> l) default) := by
  have h := z17 z00 (z1b a c) (z1c l)
    (.R (vlit [1,1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,1,0,0,0,1,1,1,1] (.app [1,1] 1 .zinf)) D)
    (.R (vlit [1,1,1,0,1] (vlit ld0 (.app ld0 1 (vlit ld1 (vlit [1,0,1] (vlit (ld0 ^ 2) (.app ld0 0 (vlit ld1 (.var 0))))))))) .zinf C)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z19,z09,z0d,append_assoc] using h
lemma z1u (a c : Nat) (l : zB) :
    (((o1 ^ (5 + a * 2)) +> ld0 +> l) {{D}}> ([1,1,0,0,0] +> (o1 ^ (5 + c * 2)) +> default)) [z00]⊢*
    (z18 ((ld0 ^ (1 + c)) +> ld1 +> [1,0,1] +> (ld0 ^ (2 + a)) +> ld1 +> l) ([0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1b a c) (z1c l)
    (.R (vlit [1,1,1,1,1] (.app [1,1] 0 (vlit ld0 (.var 0)))) (vlit [1,1,0,0,0,1,1,1,1,1] (.app [1,1] 1 .zinf)) D)
    (.L (vlit ld0 (.app ld0 1 (vlit ld1 (vlit [1,0,1] (vlit (ld0 ^ 2) (.app ld0 0 (vlit ld1 (.var 0)))))))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z18,z09,z0d,append_assoc] using h
lemma z1v (l : zB) :
    (([1] +> l) {{D}}> ([1,1] +> default)) [z00]⊢*
    (z19 l default) := by
  have h := z17 z00 (z1a 0) (z1c l)
    (.R (vlit [1] (.var 0)) (vlit [1,1] .zinf) D)
    (.R (vlit [1,1,1,0,1] (.var 0)) .zinf C)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z19,append_assoc] using h
lemma z1w (l : zB) :
    (([1] +> l) {{D}}> ([1,1,1] +> default)) [z00]⊢*
    (z18 l ([0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1a 0) (z1c l)
    (.R (vlit [1] (.var 0)) (vlit [1,1,1] .zinf) D)
    (.L (.var 0) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z18,append_assoc] using h
lemma z1x (b : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (4 + b * 2)) +> default)) [z00]⊢*
    (z19 ([0] +> (([1,0] ^ b) +> l)) default) := by
  have h := z17 z00 (z1a b) (z1c l)
    (.R (.var 0) (vlit [1,1,1,1] (.app [1,1] 0 .zinf)) D)
    (.R (vlit [1,1,1,0,1,0] (.app [1,0] 0 (.var 0))) .zinf C)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z19,z09,z0d,append_assoc] using h
lemma z1y (b : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (5 + b * 2)) +> default)) [z00]⊢*
    (z18 ([0] +> (([1,0] ^ b) +> l)) ([0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1a b) (z1c l)
    (.R (.var 0) (vlit [1,1,1,1,1] (.app [1,1] 0 .zinf)) D)
    (.L (vlit [0] (.app [1,0] 0 (.var 0))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z18,z09,z0d,append_assoc] using h
lemma z1z (n : Nat) (l : zB) :
    (((o1 ^ (4 + n * 3)) +> ld0 +> l) {{D}}> ([1] +> default)) [z00]⊢*
    (z18 l ((z ^ (2 + n)) +> d +> default)) := by
  have h := z17 z00 (z1a n) (z1c l)
    (.R (vlit [1,1,1,1] (.app [1,1,1] 0 (vlit ld0 (.var 0)))) (vlit [1] .zinf) D)
    (.L (.var 0) (vlit [1,1,1,0,0] (vlit (z ^ 2) (.app z 0 (vlit d .zinf)))) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z18,z09,z0e,append_assoc] using h
lemma z1A (b c : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (3 + b * 2)) +> z +> (o1 ^ (1 + c * 2)) +> z +> d +> default)) [z00]⊢*
    (z18 (ld0 +> ld1 +> (ld0 ^ (1 + c)) +> [1] +> (([1,0] ^ b) +> l)) ([0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1b b c) (z1c l)
    (.R (.var 0) (vlit [1,1,1] (.app [1,1] 0 (vlit [0,0,0,1] (.app [1,1] 1 (vlit [0,0,0,1,0,0] .zinf))))) D)
    (.L (vlit ld0 (vlit ld1 (vlit ld0 (.app ld0 1 (vlit [1] (.app [1,0] 0 (.var 0))))))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z18,z09,z0d,append_assoc] using h
lemma z1B (b c : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (3 + b * 2)) +> z +> (o1 ^ (2 + c * 2)) +> z +> d +> default)) [z00]⊢*
    (z18 (ld1 +> (ld0 ^ (1 + c)) +> [1] +> (([1,0] ^ b) +> l)) ([0,0,0,0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1b b c) (z1c l)
    (.R (.var 0) (vlit [1,1,1] (.app [1,1] 0 (vlit [0,0,0,1,1] (.app [1,1] 1 (vlit [0,0,0,1,0,0] .zinf))))) D)
    (.L (vlit ld1 (vlit ld0 (.app ld0 1 (vlit [1] (.app [1,0] 0 (.var 0)))))) (vlit [1,1,1,0,0,0,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z18,z09,z0d,append_assoc] using h
lemma z1C (b c : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (4 + b * 2)) +> z +> (o1 ^ (3 + c * 2)) +> z +> d +> default)) [z00]⊢*
    (z18 (ld0 +> ld1 +> (ld0 ^ c) +> ld1 +> [1,0,1,1] +> (([1,0] ^ b) +> l)) ([0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1b b c) (z1c l)
    (.R (.var 0) (vlit [1,1,1,1] (.app [1,1] 0 (vlit [0,0,0,1,1,1] (.app [1,1] 1 (vlit [0,0,0,1,0,0] .zinf))))) D)
    (.L (vlit ld0 (vlit ld1 (.app ld0 1 (vlit ld1 (vlit [1,0,1,1] (.app [1,0] 0 (.var 0))))))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z18,z09,z0d,append_assoc] using h
lemma z1D (b c : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (4 + b * 2)) +> z +> (o1 ^ (4 + c * 2)) +> z +> d +> default)) [z00]⊢*
    (z18 (ld1 +> (ld0 ^ c) +> ld1 +> [1,0,1,1] +> (([1,0] ^ b) +> l)) ([0,0,0,0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1b b c) (z1c l)
    (.R (.var 0) (vlit [1,1,1,1] (.app [1,1] 0 (vlit [0,0,0,1,1,1,1] (.app [1,1] 1 (vlit [0,0,0,1,0,0] .zinf))))) D)
    (.L (vlit ld1 (.app ld0 1 (vlit ld1 (vlit [1,0,1,1] (.app [1,0] 0 (.var 0)))))) (vlit [1,1,1,0,0,0,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1c,z18,z09,z0d,append_assoc] using h
lemma z1E (b : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (3 + b * 2)) +> [0,0,0,1] +> default)) [z00]⊢*
    (z18 (ld0 +> [1] +> (([1,0] ^ b) +> l)) ([0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1a b) (z1c l)
    (.R (.var 0) (vlit [1,1,1] (.app [1,1] 0 (vlit [0,0,0,1] .zinf))) D)
    (.L (vlit ld0 (vlit [1] (.app [1,0] 0 (.var 0)))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z18,z09,z0d,append_assoc] using h
lemma z1F (b : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (4 + b * 2)) +> [0,0,0,1] +> default)) [z00]⊢*
    (z18 ([1] +> (([1,0] ^ b) +> l)) ([0,0,0,0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1a b) (z1c l)
    (.R (.var 0) (vlit [1,1,1,1] (.app [1,1] 0 (vlit [0,0,0,1] .zinf))) D)
    (.L (vlit [1] (.app [1,0] 0 (.var 0))) (vlit [1,1,1,0,0,0,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z18,z09,z0d,append_assoc] using h
lemma z1G (b : Nat) (l : zB) :
    (l {{D}}> ((o1 ^ (4 + b * 2)) +> [0,0,0,1,1,1] +> default)) [z00]⊢*
    (z18 (ld1 +> [1,0,1,1] +> (([1,0] ^ b) +> l)) ([0,0,0,1,0,0] +> default)) := by
  have h := z17 z00 (z1a b) (z1c l)
    (.R (.var 0) (vlit [1,1,1,1] (.app [1,1] 0 (vlit [0,0,0,1,1,1] .zinf))) D)
    (.L (vlit ld1 (vlit [1,0,1,1] (.app [1,0] 0 (.var 0)))) (vlit [1,1,1,0,0,0,0,0,1,0,0] .zinf) B)
    false 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z18,z09,z0d,append_assoc] using h
lemma z1H (l r : zB) (n : Nat) :
    (z18 ((ld1 ^ n) +> ld0 +> l) r) [z00]⊢⁺
    (z19 ((ld0 ^ n) +> ld1 +> l) r) := by
  have h := z17 z00 (z1a n) (z1d l r)
    (.L (.app ld1 0 (vlit ld0 (.var 0))) (vlit [1,1,1,0,0] (.var 1)) B)
    (.R (vlit [1,1,1,0,1] (.app ld0 0 (vlit ld1 (.var 0)))) (.var 1) C)
    true 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1d,z18,z19,append_assoc] using h
lemma z1I (l r : zB) (n : Nat) :
    (z19 l ((d ^ n) +> [0] +> r)) [z00]⊢⁺
    (z18 l ((z ^ n) +> [1] +> r)) := by
  have h := z17 z00 (z1a n) (z1d l r)
    (.R (vlit [1,1,1,0,1] (.var 0)) (.app d 0 (vlit [0] (.var 1))) C)
    (.L (.var 0) (vlit [1,1,1,0,0] (.app z 0 (vlit [1] (.var 1)))) B)
    true 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1d,z18,z19,append_assoc] using h
lemma LOv (r : zB) (n m : Nat) :
    (z18 ((ld1 ^ n) +> ldh) ((d ^ m) +> z +> r)) [z00]⊢⁺
    (z18 ((ld0 ^ n) +> ldh) ((z ^ (m + 1)) +> [1] +> r)) := by
  have h := z17 z00 (z1b n m) (z1c r)
    (.L (.app ld1 0 (vlit [1] .zinf)) (vlit [1,1,1,0,0] (.app d 1 (vlit z (.var 0)))) B)
    (.L (.app ld0 0 (vlit [1] .zinf)) (vlit [1,1,1,0,0] (.app z 1 (vlit z (vlit [1] (.var 0))))) B)
    true 15 60 25 (by decide +kernel)
  rw [<- z0a z m,append_assoc]
  simpa [z0z',z1b,z1c,z18,ldh,append_assoc] using h
lemma z1J (l r : zB) (p i : Nat) :
    (z19 l ((d ^ p) +> [1] +> (d ^ i) +> z +> r)) [z00]⊢⁺
    (z18 l ((z ^ (1 + p + i)) +> [1] +> r)) := by
  have h := z17 z00 (z1b p i) (z1d l r)
    (.R (vlit [1,1,1,0,1] (.var 0)) (.app d 0 (vlit [1] (.app d 1 (vlit z (.var 1))))) C)
    (.L (.var 0) (vlit [1,1,1,0,0] (vlit z (.app z 0 (.app z 1 (vlit [1] (.var 1)))))) B)
    true 15 60 25 (by decide +kernel)
  have hpi : 1 + p + i = 1 + (p + i) := by omega
  rw [hpi]
  simpa [z0z',z1b,z1d,z18,z19,z09,append_assoc] using h
lemma z1K (l r : zB) (a b : Nat) :
    (z19 l ((d ^ (a * 2)) +> [1] +> (d ^ b) +> r)) [z00]⊢⁺
    (((o1 ^ (4 + b * 3 + a * 6)) +> ld0 +> l) {{D}}> r) := by
  have h := z17 z00 (z1b a b) (z1d l r)
    (.R (vlit [1,1,1,0,1] (.var 0)) (.app (d ++ d) 0 (vlit [1] (.app d 1 (.var 1)))) C)
    (.R (vlit [1,1,1,1] (.app [1,1,1] 1 (.app (o1 ^ 6) 0 (vlit ld0 (.var 0))))) (.var 1) D)
    true 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1d,z19,z09,z0d,z0e,z0f,append_assoc] using h
lemma z1L (l r : zB) (a b : Nat) :
    (z19 l ((d ^ (1 + a * 2)) +> [1] +> (d ^ b) +> r)) [z00]⊢⁺
    (((o1 ^ (7 + b * 3 + a * 6)) +> ld0 +> l) {{D}}> r) := by
  have h := z17 z00 (z1b a b) (z1d l r)
    (.R (vlit [1,1,1,0,1] (.var 0)) (vlit d (.app (d ++ d) 0 (vlit [1] (.app d 1 (.var 1))))) C)
    (.R (vlit (o1 ^ 7) (.app [1,1,1] 1 (.app (o1 ^ 6) 0 (vlit ld0 (.var 0))))) (.var 1) D)
    true 15 60 25 (by decide +kernel)
  simpa [z0z',z1b,z1d,z19,z09,z0d,z0e,z0f,append_assoc] using h
lemma z1M (n : Nat) (r : zB) :
    (z18 ((ld1 ^ n) +> ldh) ((d ^ n) +> r)) [z00]⊢⁺
    (((o1 ^ (4 + n * 3)) +> ld0 +> (ld0 ^ n) +> ldh) {{D}}> r) := by
  have h := z17 z00 (z1a n) (z1c r)
    (.L (.app ld1 0 (vlit [1] .zinf)) (vlit [1,1,1,0,0] (.app d 0 (.var 0))) B)
    (.R (vlit [1,1,1,1] (.app [1,1,1] 0 (vlit ld0 (.app ld0 0 (vlit [1] .zinf))))) (.var 0) D)
    true 15 60 25 (by decide +kernel)
  simpa [z0z',z1a,z1c,z18,ldh,z09,z0e,append_assoc] using h
def z1N : zF := d ++ z ++ d ++ z ++ (d ^ 3)
set_option maxRecDepth 4000000 in
lemma z1O :
    (init []) [z00]⊢* (z18 ((ld1 ^ 7) +> ldh) (z1N +> default)) := by
  have h := z17 z00 (z1a 0) (z1c default)
    (.R .zinf .zinf A)
    (.L (vlit (o1 ^ 15) .zinf) (vlit ([1,1,1,0,0] ++ z1N) .zinf) B)
    false 1 3005 1 (by decide +kernel)
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  have h_lhs : (ld1 ^ 7) +> ldh = (o1 ^ 15) +> default := rfl
  rw [h_init,h_lhs]
  simpa [z0z',z1a,z1c,z18,append_assoc] using h
def z1P (t u : Nat) : Prop := t * 8 + 9 <= u \/ u * 8 <= t + 5
lemma z1Q (old current r tail gap : Nat)
    (h1 : 16 <= old) (h2 : old * 125 <= current * 8) (h3 : r <= old)
    (h4 : tail <= old + 8) (h5 : current * 3 <= gap * 2 + 4) :
    (r + tail) * 8 + 9 <= gap := by
  omega
lemma z1R (n : Nat) : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
lemma z1S (a b : Nat) : 2 ^ (a + b) = 2 ^ a * 2 ^ b := Nat.pow_add 2 a b
lemma z1T {a b : Nat} (h : a <= b) : 2 ^ a <= 2 ^ b :=
  Nat.pow_le_pow_right (by omega) h
lemma z1U : z +> (default : zB) = default := by
  simpa using z0g 3
lemma z1V (l r : zB) (n : Nat) :
    (z19 l ((d ^ n) +> z +> r)) [z00]⊢⁺ (z18 l ((z ^ n) +> d +> r)) := by
  have h1 : z +> r = [0] +> ([0,0] +> r) := rfl
  have h2 : d +> r = [1] +> ([0,0] +> r) := rfl
  rw [h1,h2]
  exact z1I l ([0,0] +> r) n
inductive zDg : Nat -> Nat -> zF -> Prop
  | nil : zDg 0 0 []
  | zero (n v : Nat) (w : zF) : zDg n v w -> zDg (n + 1) (v * 2) (z ++ w)
  | one (n v : Nat) (w : zF) : zDg n v w -> zDg (n + 1) (v * 2 + 1) (d ++ w)
lemma z1W {n v : Nat} {w : zF} (h : zDg n v w) : v < 2 ^ n := by
  induction h with
  | nil => simp
  | zero n v w _ ih =>
    have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
    omega
  | one n v w _ ih =>
    have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
    omega
lemma z1X : ∀ (n : Nat),zDg n 0 (z ^ n)
  | 0 => .nil
  | n + 1 => by
    rw [z08]
    exact zDg.zero n 0 (z ^ n) (z1X n)
lemma z1Y : ∀ (n : Nat),zDg n (2 ^ n - 1) (d ^ n)
  | 0 => .nil
  | n + 1 => by
    have hp := z0h n
    have h2 : 2 ^ (n + 1) - 1 = (2 ^ n - 1) * 2 + 1 := by rw [Nat.pow_succ]; omega
    rw [z08,h2]
    exact zDg.one n (2 ^ n - 1) (d ^ n) (z1Y n)
lemma z1Z {n v : Nat} {w : zF} (h : zDg n v w) (hv : v = 2 ^ n - 1) :
    w = d ^ n := by
  induction h with
  | nil => rfl
  | zero n v w _ _ =>
    have hp := z0h n
    have hp2 : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
    omega
  | one n v w _ ih =>
    have hp := z0h n
    have hp2 : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
    have hv' : v = 2 ^ n - 1 := by omega
    rw [z08,ih hv']
lemma z20 {n v : Nat} {w : zF} (h : zDg n v w) (hv : 1 + v < 2 ^ n) :
    ∃ i j m s,n = i + 1 + j /\ v = (m * 2 + 1) * 2 ^ i - 1 /\
      w = (d ^ i) ++ z ++ s /\ zDg j m s := by
  induction h with
  | nil => simp at hv
  | zero n v w h _ =>
    exact ⟨0,n,v,w,by omega,by omega,rfl,h⟩
  | one n v w h ih =>
    have hp2 : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
    rcases ih (by omega) with ⟨i,j,m,s,hn,hx,hw,hs⟩
    refine ⟨i + 1,j,m,s,by omega,?_,?_,hs⟩
    · have hpi := z0h i
      have hpos : 1 <= (m * 2 + 1) * 2 ^ i := Nat.mul_pos (by omega) hpi
      have hpi2 : 2 ^ (i + 1) = 2 ^ i * 2 := Nat.pow_succ 2 i
      rw [hpi2,<- Nat.mul_assoc]
      omega
    · simp [z08,hw,List.append_assoc]
lemma z21 : ∀ (i j m : Nat) (s : zF),
    zDg j m s -> zDg (i + j) (m * 2 ^ i) ((z ^ i) ++ s)
  | 0,j,m,s,h => by simpa using h
  | i + 1,j,m,s,h => by
    have ih := z21 i j m s h
    have h1 : i + 1 + j = (i + j) + 1 := by omega
    have h2 : m * 2 ^ (i + 1) = (m * 2 ^ i) * 2 := by rw [Nat.pow_succ,<- Nat.mul_assoc]
    rw [h1,h2,z08,List.append_assoc]
    exact zDg.zero (i + j) (m * 2 ^ i) ((z ^ i) ++ s) ih
lemma z22 {n v : Nat} {w : zF} (h : zDg n v w) (hv : 1 + v < 2 ^ n) :
    ∃ w',zDg n (1 + v) w' /\
      ∀ l r,(z19 l (w +> r)) [z00]⊢⁺ (z18 l (w' +> r)) := by
  rcases z20 h hv with ⟨i,j,m,s,hn,hx,hw,hs⟩
  refine ⟨(z ^ i) ++ d ++ s,?_,?_⟩
  · subst hn hx
    have hpi := z0h i
    have hpos : 1 <= (m * 2 + 1) * 2 ^ i := Nat.mul_pos (by omega) hpi
    have h1 : 1 + ((m * 2 + 1) * 2 ^ i - 1) = (m * 2 + 1) * 2 ^ i := by omega
    have h2 : i + 1 + j = i + (j + 1) := by omega
    rw [h1,h2,List.append_assoc]
    exact z21 i (j + 1) (m * 2 + 1) (d ++ s) (zDg.one j m s hs)
  · intro l r
    rw [hw,append_assoc,append_assoc,append_assoc,append_assoc]
    exact z1V l (s +> r) i
inductive Marked : Nat -> Nat -> zF -> Prop
  | mk (p j u m : Nat) (a b : zF) :
      zDg p u a -> zDg j m b -> (j = 0 \/ m < 2 ^ (j - 1)) ->
      Marked (p + j) ((m * 2 + 1) * 2 ^ p + u) (a ++ [1] ++ b)
lemma z23 (i j m v : Nat) (hv : v = (m * 2 + 1) * 2 ^ i - 1) (htop : v < 2 ^ (i + j)) :
    j = 0 \/ m < 2 ^ (j - 1) := by
  cases j with
  | zero => exact Or.inl rfl
  | succ j =>
    right
    have hj : j + 1 - 1 = j := by omega
    rw [hj]
    have hpi := z0h i
    have hpos : 1 <= (m * 2 + 1) * 2 ^ i := Nat.mul_pos (by omega) hpi
    have hp : 2 ^ (i + (j + 1)) = (2 ^ j * 2) * 2 ^ i := by
      rw [Nat.pow_add,Nat.pow_succ]; ring
    rw [hp] at htop
    have hle : (m * 2 + 1) * 2 ^ i <= (2 ^ j * 2) * 2 ^ i := by omega
    have hlt : m * 2 + 1 <= 2 ^ j * 2 := Nat.le_of_mul_le_mul_right hle hpi
    omega
lemma z24 (p j u m : Nat) (hu : u < 2 ^ p) (hm : m < 2 ^ (j - 1)) (hj : 0 < j) :
    (m * 2 + 1) * 2 ^ p + u < 2 ^ (p + j) := by
  cases j with
  | zero => omega
  | succ j =>
    have hj' : j + 1 - 1 = j := by omega
    rw [hj'] at hm
    have hp : 2 ^ (p + (j + 1)) = (2 ^ j * 2) * 2 ^ p := by
      rw [Nat.pow_add,Nat.pow_succ]; ring
    have hle : m * 2 + 1 + 1 <= 2 ^ j * 2 := by omega
    have hmul : (m * 2 + 1 + 1) * 2 ^ p <= (2 ^ j * 2) * 2 ^ p :=
      Nat.mul_le_mul_right (2 ^ p) hle
    rw [Nat.add_mul,Nat.one_mul] at hmul
    omega
lemma z25 {J V : Nat} {w : zF} (h : Marked J V w) (hV : 2 ^ J <= V) :
    ∃ u a,V = 2 ^ J + u /\ zDg J u a /\ w = a ++ [1] := by
  rcases h with ⟨p,j,u,m,a,b,ha,hb,htop⟩
  cases j with
  | zero =>
    cases hb
    refine ⟨u,a,?_,?_,?_⟩
    · simp
    · simpa using ha
    · simp
  | succ j =>
    have hu := z1W ha
    have hm : m < 2 ^ (j + 1 - 1) := by
      rcases htop with h0 | hm
      · omega
      · exact hm
    have hlt := z24 p (j + 1) u m hu hm (by omega)
    omega
lemma z26 {J V : Nat} {w : zF} (h : Marked J V w) (hv : 1 + V < 2 ^ (J + 1)) :
    ∃ w',Marked J (1 + V) w' /\
      ∀ l r,(z19 l (w +> r)) [z00]⊢⁺ (z18 l (w' +> r)) := by
  rcases h with ⟨p,j,u,m,a,b,ha,hb,htop⟩
  have hu := z1W ha
  by_cases hlow : 1 + u < 2 ^ p
  · rcases z22 ha hlow with ⟨a',ha',hr⟩
    refine ⟨a' ++ [1] ++ b,?_,?_⟩
    · have h1 : 1 + ((m * 2 + 1) * 2 ^ p + u) = (m * 2 + 1) * 2 ^ p + (1 + u) := by omega
      rw [h1]
      exact Marked.mk p j (1 + u) m a' b ha' hb htop
    · intro l r
      rw [append_assoc,append_assoc,append_assoc,append_assoc]
      exact hr l ([1] +> b +> r)
  · have huf : u = 2 ^ p - 1 := by omega
    have hj : 0 < j := by
      cases j with
      | zero =>
        cases hb
        have hp : 2 ^ (p + 0 + 1) = 2 ^ p * 2 := by rw [Nat.add_zero,Nat.pow_succ]
        have hpp := z0h p
        omega
      | succ j => omega
    have hm_inc : 1 + m < 2 ^ j := by
      cases j with
      | zero => omega
      | succ j =>
        rcases htop with h0 | hm
        · omega
        · have hj' : j + 1 - 1 = j := by omega
          rw [hj'] at hm
          rw [Nat.pow_succ]
          omega
    rcases z20 hb hm_inc with ⟨i,k,v,s,hjk,hm,hword,hs⟩
    have hnewtop : k = 0 \/ v < 2 ^ (k - 1) := by
      apply z23 i k v m hm
      have hik : i + k = j - 1 := by omega
      rw [hik]
      rcases htop with h0 | hlt
      · omega
      · exact hlt
    refine ⟨(z ^ (p + i + 1)) ++ [1] ++ s,?_,?_⟩
    · have hpj : p + j = (p + i + 1) + k := by omega
      have hval : 1 + ((m * 2 + 1) * 2 ^ p + u) = (v * 2 + 1) * 2 ^ (p + i + 1) + 0 := by
        have hpp := z0h p
        have hpi := z0h i
        have hpos : 1 <= (v * 2 + 1) * 2 ^ i := Nat.mul_pos (by omega) hpi
        have hm1 : m + 1 = (v * 2 + 1) * 2 ^ i := by omega
        have hp_split : 2 ^ (p + i + 1) = 2 ^ i * 2 * 2 ^ p := by
          rw [Nat.pow_add,Nat.pow_add,Nat.pow_one]; ring
        rw [hp_split,huf]
        have hdist : (m + 1) * 2 * 2 ^ p = (m * 2 + 1) * 2 ^ p + 2 ^ p := by ring
        calc 1 + ((m * 2 + 1) * 2 ^ p + (2 ^ p - 1))
            = (m + 1) * 2 * 2 ^ p := by rw [hdist]; omega
          _ = ((v * 2 + 1) * 2 ^ i) * 2 * 2 ^ p := by rw [hm1]
          _ = (v * 2 + 1) * (2 ^ i * 2 * 2 ^ p) + 0 := by ring
      rw [hpj,hval]
      exact Marked.mk (p + i + 1) k 0 v (z ^ (p + i + 1)) s (z1X (p + i + 1)) hs hnewtop
    · intro l r
      rw [z1Z ha huf,hword]
      have hpi : p + i + 1 = 1 + p + i := by omega
      rw [hpi]
      simpa [append_assoc] using z1J l (s +> r) p i
def LC (len k : Nat) (l : zB) : zB :=
  z0i ld0 ld1 len k l
lemma z27 (len k : Nat) (l r : zB) (h : 1 + k < 2 ^ len) :
    (z18 (LC len (1 + k) l) r) [z00]⊢⁺ (z19 (LC len k l) r) := by
  rcases z0x ld0 ld1 len k l h with ⟨i,s,h1,h0⟩
  unfold LC
  rw [h1,h0]
  exact z1H s r i
lemma z28 (len k c J V : Nat) (w : zF) (l r : zB)
    (hk : k + c < 2 ^ len) (hV : V + c < 2 ^ (J + 1)) (hm : Marked J V w) :
    ∃ w',Marked J (V + c) w' /\
      (z18 (LC len (k + c) l) (w +> r)) [z00]⊢* (z18 (LC len k l) (w' +> r)) := by
  induction c generalizing V w with
  | zero =>
    refine ⟨w,by simpa using hm,by simp; exact ⟨0,rfl⟩⟩
  | succ c ih =>
    rcases z26 hm (by omega) with ⟨w1,hm1,hr⟩
    rcases ih (1 + V) w1 (by omega) (by omega) hm1 with ⟨w',hm',hrun⟩
    have hvc : 1 + V + c = V + (c + 1) := by omega
    rw [hvc] at hm'
    refine ⟨w',hm',?_⟩
    have hkc : k + (c + 1) = 1 + (k + c) := by omega
    rw [hkc]
    exact zSt (zPs (z27 len (k + c) l (w +> r) (by omega)))
      (zSt (zPs (hr (LC len (k + c) l) r)) hrun)
lemma z29 (len k J V : Nat) (w : zF) (l r : zB)
    (hk : k < 2 ^ len) (hlo : 2 ^ J <= V + k) (hhi : V + k < 2 ^ (J + 1)) (hm : Marked J V w) :
    ∃ a,zDg J (V + k - 2 ^ J) a /\
      (z18 (LC len k l) (w +> r)) [z00]⊢* (z18 (LC len 0 l) (a +> [1] +> r)) := by
  rcases z28 len 0 k J V w l r (by omega) hhi hm with ⟨w',hm',hrun⟩
  rcases z25 hm' hlo with ⟨u,a,hV,ha,hw⟩
  have hu : V + k - 2 ^ J = u := by omega
  refine ⟨a,by rw [hu]; exact ha,?_⟩
  rw [hw,append_assoc] at hrun
  simpa using hrun
lemma z2a (J n : Nat) (h : n * 2 + 1 < 2 ^ J) : n < 2 ^ (J - 1) := by
  cases J with
  | zero => simp at h
  | succ J =>
    have hj : J + 1 - 1 = J := by omega
    rw [hj]
    rw [Nat.pow_succ] at h
    omega
lemma z2b (len J n : Nat) (w : zF) (r : zB)
    (hd : zDg J n w) (hn : n * 2 + 1 < 2 ^ J) :
    ∃ w',Marked J (n * 2 + 2) w' /\
      (z18 (LC len 0 ldh) (w +> r)) [z00]⊢⁺ (z18 (LC len (2 ^ len - 1) ldh) (w' +> r)) := by
  rcases z20 hd (by omega) with ⟨i,j,m,s,hJ,hn0,hw,hs⟩
  have htop : j = 0 \/ m < 2 ^ (j - 1) := by
    apply z23 i j m n hn0
    have hij : i + j = J - 1 := by omega
    rw [hij]
    exact z2a J n hn
  refine ⟨(z ^ (i + 1)) ++ [1] ++ s,?_,?_⟩
  · have hJ' : J = (i + 1) + j := by omega
    have hval : n * 2 + 2 = (m * 2 + 1) * 2 ^ (i + 1) + 0 := by
      have hpi := z0h i
      have hpos : 1 <= (m * 2 + 1) * 2 ^ i := Nat.mul_pos (by omega) hpi
      rw [Nat.pow_succ,<- Nat.mul_assoc]
      omega
    rw [hJ',hval]
    exact Marked.mk (i + 1) j 0 m (z ^ (i + 1)) s (z1X (i + 1)) hs htop
  · unfold LC
    rw [z0n,z0o,hw]
    simpa [append_assoc] using LOv (s +> r) len i
lemma z2c (L n : Nat) (w : zF) (r : zB)
    (hd : zDg L n w) (hn : n * 2 + 1 < 2 ^ L) :
    ∃ a,zDg L (n * 2 + 1) a /\
      (z18 (LC L 0 ldh) (w +> r)) [z00]⊢⁺ (z18 (LC L 0 ldh) (a +> [1] +> r)) := by
  rcases z2b L L n w r hd hn with ⟨w',hm,hstart⟩
  have hp := z0h L
  have hcap : 2 ^ L - 1 < 2 ^ L := by omega
  have hlo : 2 ^ L <= n * 2 + 2 + (2 ^ L - 1) := by omega
  have hhi : n * 2 + 2 + (2 ^ L - 1) < 2 ^ (L + 1) := by rw [Nat.pow_succ]; omega
  rcases z29 L (2 ^ L - 1) L (n * 2 + 2) w' ldh r hcap hlo hhi hm with ⟨a,ha,hrun⟩
  have hval : n * 2 + 2 + (2 ^ L - 1) - 2 ^ L = n * 2 + 1 := by omega
  rw [hval] at ha
  exact ⟨a,ha,z05 hstart hrun⟩
lemma z2d {n v : Nat} {w : zF} (h : zDg n v w) :
    zDg (n + 1) v (w ++ z) := by
  induction h with
  | nil => exact zDg.zero 0 0 [] .nil
  | zero n v w _ ih =>
    rw [List.append_assoc]
    exact zDg.zero (n + 1) v (w ++ z) ih
  | one n v w _ ih =>
    rw [List.append_assoc]
    exact zDg.one (n + 1) v (w ++ z) ih
lemma z2e {n v : Nat} {w : zF} (h : zDg n v w) :
    ∀ j,n = j + 1 -> v < 2 ^ j -> ∃ a,zDg j v a /\ w = a ++ z := by
  induction h with
  | nil => intro j hn _; omega
  | zero n v w h ih =>
    intro j hn hv
    cases j with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0
      cases h
      exact ⟨[],.nil,rfl⟩
    | succ j =>
      have hp : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
      rcases ih j (by omega) (by omega) with ⟨a,ha,hw⟩
      refine ⟨z ++ a,zDg.zero j v a ha,by rw [hw,List.append_assoc]⟩
  | one n v w h ih =>
    intro j hn hv
    cases j with
    | zero => simp at hv
    | succ j =>
      have hp : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
      rcases ih j (by omega) (by omega) with ⟨a,ha,hw⟩
      refine ⟨d ++ a,zDg.one j v a ha,by rw [hw,List.append_assoc]⟩
lemma z2f (L n : Nat) (w : zF) (r : zB)
    (hd : zDg L n w) (hn : 2 ^ L <= n * 2 + 1) :
    ∃ a,zDg L (n * 2 + 1 - 2 ^ L) a /\
      (z18 (LC L 0 ldh) (w +> z +> r)) [z00]⊢⁺ (z18 (LC L 0 ldh) (a +> z +> [1] +> r)) := by
  have hbound := z1W hd
  have hupper : n * 2 + 1 < 2 ^ (L + 1) := by rw [Nat.pow_succ]; omega
  rcases z2b L (L + 1) n (w ++ z) r (z2d hd) hupper with ⟨w',hm,hstart⟩
  have hp := z0h L
  have hcap : 2 ^ L - 1 < 2 ^ L := by omega
  have hlo : 2 ^ (L + 1) <= n * 2 + 2 + (2 ^ L - 1) := by rw [Nat.pow_succ]; omega
  have hhi : n * 2 + 2 + (2 ^ L - 1) < 2 ^ (L + 1 + 1) := by rw [Nat.pow_succ,Nat.pow_succ]; omega
  rcases z29 L (2 ^ L - 1) (L + 1) (n * 2 + 2) w' ldh r hcap hlo hhi hm with ⟨a,ha,hrun⟩
  have hval : n * 2 + 2 + (2 ^ L - 1) - 2 ^ (L + 1) = n * 2 + 1 - 2 ^ L := by rw [Nat.pow_succ]; omega
  rw [hval] at ha
  rcases z2e ha L rfl (by omega) with ⟨b,hb,hab⟩
  refine ⟨b,hb,?_⟩
  rw [append_assoc] at hstart
  rw [hab,append_assoc] at hrun
  exact z05 hstart hrun
lemma z2g (l r : zB) (J b : Nat) :
    (z19 l ((d ^ J) +> [1] +> (d ^ b) +> r)) [z00]⊢⁺
    (((o1 ^ (4 + (J + b) * 3)) +> ld0 +> l) {{D}}> r) := by
  let a := J / 2
  rcases Nat.mod_two_eq_zero_or_one J with h0 | h1
  · have hJ : J = a * 2 := by omega
    have h_exp : 4 + (J + b) * 3 = 4 + b * 3 + a * 6 := by omega
    rw [h_exp,hJ]
    exact z1K l r a b
  · have hJ : J = 1 + a * 2 := by omega
    have h_exp : 4 + (J + b) * 3 = 7 + b * 3 + a * 6 := by omega
    rw [h_exp,hJ]
    exact z1L l r a b
lemma z2h (n : Nat) (r : zB) :
    (z18 (LC n 0 ldh) ((d ^ n) +> r)) [z00]⊢⁺
    (((o1 ^ (4 + n * 3)) +> ld0 +> LC n (2 ^ n - 1) ldh) {{D}}> r) := by
  unfold LC
  rw [z0n,z0o]
  exact z1M n r
lemma z2i (J k n : Nat) (w : zF) (r : zB)
    (hd : zDg J n w) (hn : n * 2 + 1 < 2 ^ J) (hk : 0 < k) :
    (z18 (LC (J + k) 0 ldh) (w +> (d ^ k) +> r)) [z00]⊢⁺
    (((o1 ^ (4 + (J + k) * 3)) +> ld0 +> LC (J + k) (2 ^ (J + k) - 2 ^ (J + 1) + n * 2 + 1) ldh) {{D}}> r) := by
  have hp : 2 ^ (J + 1) <= 2 ^ (J + k) := z1T (by omega)
  have hpow := z0h J
  have hpow1 := z0h (J + 1)
  let V := n * 2 + 2
  let c := 2 ^ (J + 1) - 1 - V
  let K := 2 ^ (J + k) - 2 ^ (J + 1) + n * 2 + 1
  have hvalue : V + c = 2 ^ (J + 1) - 1 := by
    have : 2 ^ (J + 1) = 2 ^ J * 2 := Nat.pow_succ 2 J
    omega
  have hbudget : K + 1 + c = 2 ^ (J + k) - 1 := by
    have : 2 ^ (J + 1) = 2 ^ J * 2 := Nat.pow_succ 2 J
    omega
  rcases z2b (J + k) J n w ((d ^ k) +> r) hd hn with ⟨s,hm,hstart⟩
  rcases z28 (J + k) (K + 1) c J V s ldh ((d ^ k) +> r) (by omega) (by omega) hm with ⟨s',hm',hrun⟩
  rcases z25 hm' (by have : 2 ^ (J + 1) = 2 ^ J * 2 := Nat.pow_succ 2 J; omega) with ⟨u,a,hu,ha,hs⟩
  have huf : u = 2 ^ J - 1 := by
    have : 2 ^ (J + 1) = 2 ^ J * 2 := Nat.pow_succ 2 J
    omega
  rw [z1Z ha huf] at hs
  rw [hbudget] at hrun
  have h1 := z05 hstart hrun
  rw [hs,append_assoc] at h1
  have hK1 : K + 1 = 1 + K := by omega
  rw [hK1] at h1
  have h2 := zPt h1 (z27 (J + k) K ldh ((d ^ J) +> [1] +> (d ^ k) +> r) (by omega))
  exact zPt h2 (z2g (LC (J + k) K ldh) r J k)
lemma z2j {n v : Nat} {w : zF} (h : zDg n v w) (hv : v < 2 ^ n - 1) :
    ∃ j u a k,n = j + k /\ 1 <= j /\ u * 2 + 1 < 2 ^ j /\ w = a ++ (d ^ k) /\
      zDg j u a /\ v = 2 ^ n - 2 ^ j + u := by
  induction h with
  | nil => simp at hv
  | zero n v w h ih =>
    by_cases hsmall : v < 2 ^ n - 1
    · rcases ih hsmall with ⟨j,u,a,k,hn,hj,hu,hw,ha,heq⟩
      have hp : 2 ^ j <= 2 ^ n := z1T (by omega)
      have hp1 : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
      have hpn : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
      refine ⟨j + 1,u * 2,z ++ a,k,by omega,by omega,by omega,?_,zDg.zero j u a ha,by omega⟩
      rw [hw,List.append_assoc]
    · have hbound := z1W h
      have heq : v = 2 ^ n - 1 := by omega
      have hpn : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
      have hpn_pos := z0h n
      refine ⟨1,0,z,n,by omega,by omega,by simp,?_,zDg.zero 0 0 [] .nil,by omega⟩
      rw [z1Z h heq]
  | one n v w h ih =>
    have hpn : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
    have hpn_pos := z0h n
    rcases ih (by omega) with ⟨j,u,a,k,hn,hj,hu,hw,ha,heq⟩
    have hp : 2 ^ j <= 2 ^ n := z1T (by omega)
    have hp1 : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
    refine ⟨j + 1,u * 2 + 1,d ++ a,k,by omega,by omega,by omega,?_,zDg.one j u a ha,by omega⟩
    rw [hw,List.append_assoc]
lemma z2k (L n : Nat) (w : zF) (r : zB)
    (hd : zDg L n w) (hn : 2 ^ L <= n * 2 + 1) :
    (z18 (LC L 0 ldh) (w +> r)) [z00]⊢⁺
    (((o1 ^ (4 + L * 3)) +> ld0 +> LC L (n * 2 + 1 - 2 ^ L) ldh) {{D}}> r) := by
  have hbound := z1W hd
  by_cases hsmall : n < 2 ^ L - 1
  · rcases z2j hd hsmall with ⟨J,u,a,k,hL,hJ,hu,hw,ha,heq⟩
    have hk : 0 < k := by
      rcases k with _ | k
      · simp only [Nat.add_zero] at hL; subst hL; omega
      · omega
    subst hL
    have hp : 2 ^ (J + 1) <= 2 ^ (J + k) := z1T (by omega)
    have hpJ : 2 ^ J <= 2 ^ (J + k) := z1T (by omega)
    have hpJ1 : 2 ^ (J + 1) = 2 ^ J * 2 := Nat.pow_succ 2 J
    have hval : n * 2 + 1 - 2 ^ (J + k) = 2 ^ (J + k) - 2 ^ (J + 1) + u * 2 + 1 := by omega
    rw [hw,append_assoc,hval]
    exact z2i J k u a r ha hu hk
  · have heq : n = 2 ^ L - 1 := by omega
    have hval : n * 2 + 1 - 2 ^ L = 2 ^ L - 1 := by omega
    rw [z1Z hd heq,hval]
    exact z2h L r
lemma z2l :
    (init []) [z00]⊢* (z18 (LC 7 0 ldh) (z1N +> default)) := by
  unfold LC
  rw [z0n]
  exact z1O
def RC (n : Nat) : zB := z0j z d n
lemma z2m {n v : Nat} {w : zF} (h : zDg n v w) :
    ∀ m,w +> RC m = RC (v + 2 ^ n * m) := by
  induction h with
  | nil =>
    intro m
    simp
  | zero n v w _ ih =>
    intro m
    rw [append_assoc,ih]
    unfold RC
    rw [<- z0t z1U]
    have h1 : (v + 2 ^ n * m) * 2 = v * 2 + 2 ^ (n + 1) * m := by
      rw [Nat.pow_succ]; ring
    rw [h1]
  | one n v w _ ih =>
    intro m
    rw [append_assoc,ih]
    unfold RC
    rw [<- z0u]
    have h1 : (v + 2 ^ n * m) * 2 + 1 = v * 2 + 1 + 2 ^ (n + 1) * m := by
      rw [Nat.pow_succ]; ring
    rw [h1]
lemma z2n : ∀ (n v : Nat),v < 2 ^ n -> ∃ w,zDg n v w
  | 0,v,hv => by
    have hv0 : v = 0 := by simp at hv; omega
    subst hv0
    exact ⟨[],.nil⟩
  | n + 1,v,hv => by
    have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
    let k := v / 2
    rcases Nat.mod_two_eq_zero_or_one v with h0 | h1
    · rcases z2n n k (by omega) with ⟨w,hw⟩
      have hv_eq : v = k * 2 := by omega
      rw [hv_eq]
      exact ⟨z ++ w,zDg.zero n k w hw⟩
    · rcases z2n n k (by omega) with ⟨w,hw⟩
      have hv_eq : v = k * 2 + 1 := by omega
      rw [hv_eq]
      exact ⟨d ++ w,zDg.one n k w hw⟩
lemma z2o (n : Nat) (l : zB) :
    (z19 l (RC n)) [z00]⊢⁺ (z18 l (RC (1 + n))) := by
  rcases z0y z1U n with ⟨i,s,h0,h1⟩
  unfold RC
  rw [h0,h1]
  exact z1V l s i
lemma z2p (len k c v : Nat) (l : zB) (hk : k + c < 2 ^ len) :
    (z18 (LC len (k + c) l) (RC v)) [z00]⊢* (z18 (LC len k l) (RC (v + c))) := by
  induction c generalizing v with
  | zero => simp; exact ⟨0,rfl⟩
  | succ c ih =>
    have hkc : k + (c + 1) = 1 + (k + c) := by omega
    rw [hkc]
    have h1 := zPs (z27 len (k + c) l (RC v) (by omega))
    have h2 := zPs (z2o v (LC len (k + c) l))
    have h3 := ih (1 + v) (by omega)
    have hvc : 1 + v + c = v + (c + 1) := by omega
    rw [hvc] at h3
    exact zSt h1 (zSt h2 h3)
lemma z2q (len k v : Nat) (l : zB) (hk : k < 2 ^ len) :
    (z19 (LC len k l) (RC v)) [z00]⊢* (z18 (LC len 0 l) (RC (k + v + 1))) := by
  have h1 := zPs (z2o v (LC len k l))
  have h2 := z2p len 0 k (1 + v) l (by omega)
  have hkv : 0 + k = k := by omega
  have hkv2 : 1 + v + k = k + v + 1 := by omega
  rw [hkv] at h2
  rw [hkv2] at h2
  exact zSt h1 h2
lemma z2r (m i : Nat) (l r : zB) :
    (z18 ((ld1 ^ (1 + m)) +> [1,0,1] +> l) ((d ^ i) +> z +> r)) [z00]⊢*
    (z18 ((ld0 ^ (1 + m)) +> ld1 +> l) ((z ^ (1 + i)) +> [1] +> r)) := by
  have h1 := z1h (1 + m) l ((d ^ i) +> z +> r)
  have hm : 1 + (1 + m) = 2 + m := by omega
  rw [hm,z09 ld0 2 m,append_assoc] at h1
  have h2 := z1i i ((ld0 ^ m) +> ld1 +> l) r
  have hld0 : (ld0 ^ 1 : zF) = ld0 := rfl
  rw [z09 ld0 1 m,hld0,append_assoc]
  exact zSt h1 h2
lemma z2s (m J v : Nat) (w : zF) (l r : zB)
    (hm : 0 < m) (hd : zDg J v w) (hv : v * 2 + 1 < 2 ^ J) :
    ∃ w',Marked J (v * 2 + 2) w' /\
      (z18 (LC m 0 ([1,0,1] +> l)) (w +> r)) [z00]⊢*
      (z18 (LC m (2 ^ m - 1) (ld1 +> l)) (w' +> r)) := by
  rcases z20 hd (by omega) with ⟨i,j,u,s,hJ,hval,hw,hs⟩
  have htop : j = 0 \/ u < 2 ^ (j - 1) := by
    apply z23 i j u v hval
    have hij : i + j = J - 1 := by omega
    rw [hij]
    exact z2a J v hv
  refine ⟨(z ^ (i + 1)) ++ [1] ++ s,?_,?_⟩
  · have hJ' : J = (i + 1) + j := by omega
    have hval2 : v * 2 + 2 = (u * 2 + 1) * 2 ^ (i + 1) + 0 := by
      have hpi := z0h i
      have hpos : 1 <= (u * 2 + 1) * 2 ^ i := Nat.mul_pos (by omega) hpi
      rw [Nat.pow_succ,<- Nat.mul_assoc]
      omega
    rw [hJ',hval2]
    exact Marked.mk (i + 1) j 0 u (z ^ (i + 1)) s (z1X (i + 1)) hs htop
  · unfold LC
    rw [z0n,z0o,hw]
    cases m with
    | zero => omega
    | succ m' =>
      have hm' : m' + 1 = 1 + m' := by omega
      have hi' : i + 1 = 1 + i := by omega
      rw [hm',hi']
      simpa [append_assoc] using z2r m' i l (s +> r)
lemma z2t : ([1] : zF) +> default = RC 1 := by
  unfold RC
  rw [z0s]
  have hd : (d : zF) +> default = [1] +> ([0,0] +> default) := rfl
  have hz : ([0,0] : zF) +> default = default := by
    simpa using z0g 2
  rw [hd,hz]
lemma z2u (len k J V : Nat) (w : zF) (l : zB)
    (hk : k < 2 ^ len) (hV : V < 2 ^ (J + 1)) (hlo : 2 ^ J <= V + k) (hm : Marked J V w) :
    (z18 (LC len k l) (w +> default)) [z00]⊢* (z18 (LC len 0 l) (RC (V + k))) := by
  let c := 2 ^ J - V
  have hc : c <= k := by omega
  have hpJ : 2 ^ (J + 1) = 2 ^ J * 2 := Nat.pow_succ 2 J
  have hvc_lo : 2 ^ J <= V + c := by omega
  have hvc_hi : V + c < 2 ^ (J + 1) := by omega
  rcases z28 len (k - c) c J V w l default (by omega) hvc_hi hm with ⟨a,ha,hrun⟩
  rcases z25 ha hvc_lo with ⟨u,b,hu,hb,hab⟩
  have hkc : k - c + c = k := by omega
  rw [hkc,hab,append_assoc,z2t,z2m hb 1] at hrun
  have h2 := z2p len 0 (k - c) (u + 2 ^ J * 1) l (by omega)
  have h0kc : 0 + (k - c) = k - c := by omega
  have hval : u + 2 ^ J * 1 + (k - c) = V + k := by omega
  rw [h0kc,hval] at h2
  exact zSt hrun h2
lemma z2v (m J v : Nat) (l : zB)
    (hm : 0 < m) (hv : v * 2 + 1 < 2 ^ J) :
    ∃ w,Marked J (v * 2 + 2) w /\
      (z18 (LC m 0 ([1,0,1] +> l)) (RC v)) [z00]⊢*
      (z18 (LC m (2 ^ m - 1) (ld1 +> l)) (w +> default)) := by
  rcases z2n J v (by omega) with ⟨a,ha⟩
  rcases z2s m J v a l default hm ha hv with ⟨w,hw,hrun⟩
  refine ⟨w,hw,?_⟩
  have hrc0 : (default : zB) = RC 0 := by simp [RC,z0r]
  have ha_rc : a +> (default : zB) = RC v := by
    rw [hrc0,z2m ha 0]; simp
  rw [<- ha_rc]
  exact hrun
lemma z2w (len k n : Nat) (l : zB) :
    (ld0 ^ n) +> ld1 +> LC len k l = LC (len + 1 + n) ((k * 2 + 1) * 2 ^ n - 1) l := by
  unfold LC
  exact (z0q ld0 ld1 len k n l).symm
lemma z2x (len k n : Nat) (hk : k < 2 ^ len) :
    (k * 2 + 1) * 2 ^ n - 1 < 2 ^ (len + 1 + n) := by
  have hpn := z0h n
  have hpos : 1 <= (k * 2 + 1) * 2 ^ n := Nat.mul_pos (by omega) hpn
  have hp : 2 ^ (len + 1 + n) = (2 ^ len * 2) * 2 ^ n := by
    rw [Nat.pow_add,Nat.pow_succ]
  have hle : (k * 2 + 1) * 2 ^ n <= (2 ^ len * 2) * 2 ^ n :=
    Nat.mul_le_mul_right (2 ^ n) (by omega)
  omega
lemma z2y (len k n v : Nat) (l : zB) (hk : k < 2 ^ len) :
    (z18 ((ld0 ^ n) +> ld1 +> LC len k l) (RC v)) [z00]⊢*
    (z18 (LC (len + 1 + n) 0 l) (RC ((k * 2 + 1) * 2 ^ n - 1 + v))) := by
  rw [z2w]
  have h1 := z2p (len + 1 + n) 0 ((k * 2 + 1) * 2 ^ n - 1) v l (by simpa using z2x len k n hk)
  have h2 : 0 + ((k * 2 + 1) * 2 ^ n - 1) = (k * 2 + 1) * 2 ^ n - 1 := by omega
  have h3 : v + ((k * 2 + 1) * 2 ^ n - 1) = (k * 2 + 1) * 2 ^ n - 1 + v := by omega
  rw [h2,h3] at h1
  exact h1
lemma z2z (len k n v : Nat) (l : zB) (hk : k < 2 ^ len) :
    (z19 ((ld0 ^ n) +> ld1 +> LC len k l) (RC v)) [z00]⊢*
    (z18 (LC (len + 1 + n) 0 l) (RC ((k * 2 + 1) * 2 ^ n + v))) := by
  rw [z2w]
  have h1 := z2q (len + 1 + n) ((k * 2 + 1) * 2 ^ n - 1) v l (z2x len k n hk)
  have hpn := z0h n
  have hpos : 1 <= (k * 2 + 1) * 2 ^ n := Nat.mul_pos (by omega) hpn
  have h2 : (k * 2 + 1) * 2 ^ n - 1 + v + 1 = (k * 2 + 1) * 2 ^ n + v := by omega
  rw [h2] at h1
  exact h1
lemma z2A (m v : Nat) (l : zB) (hm : 0 < m) (hv : v * 2 + 1 < 2 ^ m) :
    (z18 (LC m 0 ([1,0,1] +> l)) (RC v)) [z00]⊢*
    (z18 (LC m 0 (ld1 +> l)) (RC (2 ^ m + v * 2 + 1))) := by
  rcases z2v m m v l hm hv with ⟨w,hw,hrun⟩
  have hpm := z0h m
  have hpm1 : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
  have h2 := z2u m (2 ^ m - 1) m (v * 2 + 2) w (ld1 +> l) (by omega) (by omega) (by omega) hw
  have hval : v * 2 + 2 + (2 ^ m - 1) = 2 ^ m + v * 2 + 1 := by omega
  rw [hval] at h2
  exact zSt hrun h2
lemma z2B (len k n v : Nat) (l : zB) (hv : v < 2 ^ n) :
    LC n v (LC len k l) = LC (len + n) (k * 2 ^ n + v) l := by
  induction n generalizing v with
  | zero =>
    have hv0 : v = 0 := by simp at hv; omega
    subst hv0
    unfold LC
    simp [z0i]
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
    let q := v / 2
    have hlen : len + (n + 1) = (len + n) + 1 := by omega
    rcases Nat.mod_two_eq_zero_or_one v with h0 | h1
    · have hv_eq : v = q * 2 := by omega
      have hval : k * 2 ^ (n + 1) + q * 2 = (k * 2 ^ n + q) * 2 := by rw [Nat.pow_succ]; ring
      unfold LC at *
      rw [hv_eq,hlen,hval,z0l,z0l,ih q (by omega)]
    · have hv_eq : v = q * 2 + 1 := by omega
      have hval : k * 2 ^ (n + 1) + (q * 2 + 1) = (k * 2 ^ n + q) * 2 + 1 := by rw [Nat.pow_succ]; ring
      unfold LC at *
      rw [hv_eq,hlen,hval,z0m,z0m,ih q (by omega)]
lemma z2C (len k m v : Nat) (l : zB)
    (hk : k < 2 ^ len) (hm : 0 < m) (hv : v * 2 + 1 < 2 ^ m) :
    (z18 (LC m 0 ([1,0,1] +> LC len k l)) (RC v)) [z00]⊢*
    (z18 (LC (len + 1 + m) 0 l) (RC (k * 2 ^ (m + 1) + 2 ^ m + v * 2 + 1))) := by
  have h1 := z2A m v (LC len k l) hm hv
  have h_ld1 : ld1 +> LC len k l = LC (len + 1) (k * 2) l := by
    unfold LC; exact (z0l ld0 ld1 len k l).symm
  rw [h_ld1,z2B (len + 1) (k * 2) m 0 l (z0h m)] at h1
  have hbound : k * 2 * 2 ^ m + 0 < 2 ^ (len + 1 + m) := by
    have hpm := z0h m
    have hp : 2 ^ (len + 1 + m) = (2 ^ len * 2) * 2 ^ m := by rw [Nat.pow_add,Nat.pow_succ]
    have hle : (k * 2 + 1) * 2 ^ m <= (2 ^ len * 2) * 2 ^ m :=
      Nat.mul_le_mul_right (2 ^ m) (by omega)
    rw [Nat.add_mul,Nat.one_mul] at hle
    omega
  have h2 := z2p (len + 1 + m) 0 (k * 2 * 2 ^ m + 0) (2 ^ m + v * 2 + 1) l (by omega)
  have h0 : 0 + (k * 2 * 2 ^ m + 0) = k * 2 * 2 ^ m + 0 := by omega
  have hval : 2 ^ m + v * 2 + 1 + (k * 2 * 2 ^ m + 0) = k * 2 ^ (m + 1) + 2 ^ m + v * 2 + 1 := by
    rw [Nat.pow_succ]; ring
  rw [h0,hval] at h2
  exact zSt h1 h2
lemma z2D (len k a m v : Nat) (l : zB)
    (hk : k < 2 ^ len) (ha : 1 <= a) (hm : 0 < m) (hv : v * 2 + 1 < 2 ^ (m + 1)) :
    (z18 (LC m 0 ([1,0,1] +> (ld0 ^ a) +> ld1 +> LC len k l)) (RC v)) [z00]⊢*
    (z18 (LC (len + 1 + a + 1 + m) 0 l)
      (RC ((((k * 2 + 1) * 2 ^ a - 1) * 2 + 1) * 2 ^ m - 1 + v * 2 + 2))) := by
  rcases z2v m (m + 1) v ((ld0 ^ a) +> ld1 +> LC len k l) hm hv with ⟨w,hw,hrun⟩
  have h_rhs : LC m (2 ^ m - 1) (ld1 +> (ld0 ^ a) +> ld1 +> LC len k l) =
      LC (len + 1 + a + 1 + m) ((((k * 2 + 1) * 2 ^ a - 1) * 2 + 1) * 2 ^ m - 1) l := by
    have h_full : LC m (2 ^ m - 1) (ld1 +> (ld0 ^ a) +> ld1 +> LC len k l) =
        (ld0 ^ m) +> ld1 +> (ld0 ^ a) +> ld1 +> LC len k l := by
      unfold LC; rw [z0o]
    rw [h_full,z2w len k a l,z2w (len + 1 + a) ((k * 2 + 1) * 2 ^ a - 1) m l]
  rw [h_rhs] at hrun
  have hbound1 := z2x len k a hk
  have hbound2 := z2x (len + 1 + a) ((k * 2 + 1) * 2 ^ a - 1) m hbound1
  have hV_hi : v * 2 + 2 < 2 ^ (m + 1 + 1) := by rw [Nat.pow_succ]; omega
  have hlo : 2 ^ (m + 1) <= v * 2 + 2 + ((((k * 2 + 1) * 2 ^ a - 1) * 2 + 1) * 2 ^ m - 1) := by
    have hpa : 2 <= 2 ^ a := by
      have : 2 ^ 1 <= 2 ^ a := z1T ha
      simpa using this
    have hpm := z0h m
    have h1 : 2 <= (k * 2 + 1) * 2 ^ a := by
      have : 1 * 2 <= (k * 2 + 1) * 2 ^ a := Nat.mul_le_mul (by omega) hpa
      omega
    have h2 : 2 <= ((k * 2 + 1) * 2 ^ a - 1) * 2 + 1 := by omega
    have h3 : 2 * 2 ^ m <= (((k * 2 + 1) * 2 ^ a - 1) * 2 + 1) * 2 ^ m :=
      Nat.mul_le_mul_right (2 ^ m) h2
    rw [Nat.pow_succ]
    omega
  have h2 := z2u (len + 1 + a + 1 + m) ((((k * 2 + 1) * 2 ^ a - 1) * 2 + 1) * 2 ^ m - 1)
    (m + 1) (v * 2 + 2) w l hbound2 hV_hi hlo hw
  have hval : v * 2 + 2 + ((((k * 2 + 1) * 2 ^ a - 1) * 2 + 1) * 2 ^ m - 1) =
      (((k * 2 + 1) * 2 ^ a - 1) * 2 + 1) * 2 ^ m - 1 + v * 2 + 2 := by omega
  rw [hval] at h2
  exact zSt hrun h2
lemma z2E (n : Nat) (l : zB) :
    (ld0 ^ n) +> ld1 +> l = LC (1 + n) (2 ^ n - 1) l := by
  have h := z2w 0 0 n l
  unfold LC at h ⊢
  simp [z0i] at h
  exact h
lemma z2F (len k a c e : Nat) (l : zB)
    (hk : k < 2 ^ len) (ha : 1 <= a) (hc : 1 <= c) (he : e <= 1) :
    (z18 (LC (1 + c) 0 ([1,0,1] +> (ld0 ^ a) +> ld1 +> LC len k l)) (RC (2 ^ c + e))) [z00]⊢*
    (z18 (LC (len + a + c + 3) 0 l) (RC ((k * 2 + 1) * 2 ^ (a + c + 2) + (e * 2 + 1)))) := by
  have hpow : 2 <= 2 ^ c := by
    have : 2 ^ 1 <= 2 ^ c := z1T hc
    simpa using this
  have hv : (2 ^ c + e) * 2 + 1 < 2 ^ (1 + c + 1) := by
    have : 1 + c + 1 = c + 1 + 1 := by omega
    rw [this,Nat.pow_succ,Nat.pow_succ]
    omega
  have h1 := z2D len k a (1 + c) (2 ^ c + e) l hk ha (by omega) hv
  have hlen : len + 1 + a + 1 + (1 + c) = len + a + c + 3 := by omega
  have hval : (((k * 2 + 1) * 2 ^ a - 1) * 2 + 1) * 2 ^ (1 + c) - 1 + (2 ^ c + e) * 2 + 2 =
      (k * 2 + 1) * 2 ^ (a + c + 2) + (e * 2 + 1) := by
    have hpa := z0h a
    have hpc := z0h c
    have hpos1 : 1 <= (k * 2 + 1) * 2 ^ a := Nat.mul_pos (by omega) hpa
    have hp_ac : (k * 2 + 1) * 2 ^ (a + c + 2) = ((k * 2 + 1) * 2 ^ a) * 2 ^ c * 4 := by
      have : a + c + 2 = a + c + 1 + 1 := by omega
      rw [this,Nat.pow_succ,Nat.pow_succ,Nat.pow_add]; ring
    have hp_1c : 2 ^ (1 + c) = 2 ^ c * 2 := by rw [Nat.add_comm 1 c,Nat.pow_succ]
    rw [hp_ac,hp_1c]
    have hsub : ((k * 2 + 1) * 2 ^ a - 1) * 2 + 1 = (k * 2 + 1) * 2 ^ a * 2 - 1 := by omega
    have hmul : ((k * 2 + 1) * 2 ^ a * 2) * (2 ^ c * 2) = ((k * 2 + 1) * 2 ^ a) * 2 ^ c * 4 := by ring
    have hge : 2 ^ c <= ((k * 2 + 1) * 2 ^ a) * 2 ^ c := Nat.le_mul_of_pos_left _ hpos1
    rw [hsub,Nat.sub_mul,Nat.one_mul,hmul]
    omega
  rw [hlen,hval] at h1
  exact h1
lemma z2G (len k a c : Nat) (l : zB)
    (hk : k < 2 ^ len) (ha : 1 <= a) (hc : 1 <= c) :
    (z19 ((ld0 ^ c) +> ld1 +> [1,0,1] +> (ld0 ^ a) +> ld1 +> LC len k l) (RC 0)) [z00]⊢*
    (z18 (LC (len + a + c + 3) 0 l) (RC ((k * 2 + 1) * 2 ^ (a + c + 2) + 1))) := by
  rw [z2E c ([1,0,1] +> (ld0 ^ a) +> ld1 +> LC len k l)]
  have hpc := z0h c
  have hbound : 2 ^ c - 1 < 2 ^ (1 + c) := by rw [Nat.add_comm 1 c,Nat.pow_succ]; omega
  have h1 := z2q (1 + c) (2 ^ c - 1) 0 ([1,0,1] +> (ld0 ^ a) +> ld1 +> LC len k l) hbound
  have hval1 : 2 ^ c - 1 + 0 + 1 = 2 ^ c + 0 := by omega
  rw [hval1] at h1
  have h2 := z2F len k a c 0 l hk ha hc (by omega)
  exact zSt h1 h2
lemma z2H (len k a c : Nat) (l : zB)
    (hk : k < 2 ^ len) (ha : 1 <= a) (hc : 1 <= c) :
    (z18 ((ld0 ^ c) +> ld1 +> [1,0,1] +> (ld0 ^ a) +> ld1 +> LC len k l) (RC 2)) [z00]⊢*
    (z18 (LC (len + a + c + 3) 0 l) (RC ((k * 2 + 1) * 2 ^ (a + c + 2) + 3))) := by
  rw [z2E c ([1,0,1] +> (ld0 ^ a) +> ld1 +> LC len k l)]
  have hpc := z0h c
  have hbound : 0 + (2 ^ c - 1) < 2 ^ (1 + c) := by rw [Nat.add_comm 1 c,Nat.pow_succ]; omega
  have h1 := z2p (1 + c) 0 (2 ^ c - 1) 2 ([1,0,1] +> (ld0 ^ a) +> ld1 +> LC len k l) hbound
  have h0 : 0 + (2 ^ c - 1) = 2 ^ c - 1 := by omega
  have hval1 : 2 + (2 ^ c - 1) = 2 ^ c + 1 := by omega
  rw [h0,hval1] at h1
  have h2 := z2F len k a c 1 l hk ha hc (by omega)
  exact zSt h1 h2
lemma z2I : ([0,0,0,1,0,0] : zF) +> default = RC 2 := by
  have h : RC 2 = z +> z0j z d 1 := z0t z1U 1
  rw [h,z0s]; rfl
lemma z2J : ([0,0,0,0,0,0,1,0,0] : zF) +> default = RC 4 := by
  have h1 : RC 4 = z +> z0j z d 2 := z0t z1U 2
  have h2 : z0j z d 2 = z +> z0j z d 1 := z0t z1U 1
  rw [h1,h2,z0s]; rfl
lemma z2K : (default : zB) = RC 0 := by
  simp [RC,z0r]
lemma z2L (len k a c : Nat) (l : zB) (hk : k < 2 ^ len) :
    (((o1 ^ (4 + a * 2)) +> ld0 +> LC len k l) {{D}}>
      ([1,0,0,0] +> (o1 ^ (2 + c * 2)) +> default)) [z00]⊢*
    (z18 (LC (len + 1 + (3 + a + c)) 0 l) (RC ((k * 2 + 1) * 2 ^ (3 + a + c) + 1))) := by
  have h1 := z1n a c (LC len k l)
  rw [z2I] at h1
  have h2 := z2y len k (3 + a + c) 2 l hk
  have hp := z0h (3 + a + c)
  have hpos : 1 <= (k * 2 + 1) * 2 ^ (3 + a + c) := Nat.mul_pos (by omega) hp
  have hval : (k * 2 + 1) * 2 ^ (3 + a + c) - 1 + 2 = (k * 2 + 1) * 2 ^ (3 + a + c) + 1 := by omega
  rw [hval] at h2
  exact zSt h1 h2
lemma z2M (len k a c : Nat) (l : zB) (hk : k < 2 ^ len) :
    (((o1 ^ (4 + a * 2)) +> ld0 +> LC len k l) {{D}}>
      ([1,0,0,0] +> (o1 ^ (1 + c * 2)) +> default)) [z00]⊢*
    (z18 (LC (len + 1 + (3 + a + c)) 0 l) (RC ((k * 2 + 1) * 2 ^ (3 + a + c)))) := by
  have h1 := z1o a c (LC len k l)
  have h2 := z2z len k (3 + a + c) 0 l hk
  rw [<- z2K] at h2
  simp only [Nat.add_zero] at h2
  exact zSt h1 h2
lemma z2N (len k a c : Nat) (l : zB) (hk : k < 2 ^ len) :
    (((o1 ^ (5 + a * 2)) +> ld0 +> LC len k l) {{D}}>
      ([1,0,0,0] +> (o1 ^ (2 + c * 2)) +> default)) [z00]⊢*
    (z18 (LC (len + 1 + (4 + a + c)) 0 l) (RC ((k * 2 + 1) * 2 ^ (4 + a + c)))) := by
  have h1 := z1p a c (LC len k l)
  have h2 := z2z len k (4 + a + c) 0 l hk
  rw [<- z2K] at h2
  simp only [Nat.add_zero] at h2
  exact zSt h1 h2
lemma z2O (len k a c : Nat) (l : zB) (hk : k < 2 ^ len) :
    (((o1 ^ (5 + a * 2)) +> ld0 +> LC len k l) {{D}}>
      ([1,0,0,0] +> (o1 ^ (1 + c * 2)) +> default)) [z00]⊢*
    (z18 (LC (len + 1 + (3 + a + c)) 0 l) (RC ((k * 2 + 1) * 2 ^ (3 + a + c) + 1))) := by
  have h1 := z1q a c (LC len k l)
  rw [z2I] at h1
  have h2 := z2y len k (3 + a + c) 2 l hk
  have hp := z0h (3 + a + c)
  have hpos : 1 <= (k * 2 + 1) * 2 ^ (3 + a + c) := Nat.mul_pos (by omega) hp
  have hval : (k * 2 + 1) * 2 ^ (3 + a + c) - 1 + 2 = (k * 2 + 1) * 2 ^ (3 + a + c) + 1 := by omega
  rw [hval] at h2
  exact zSt h1 h2
lemma z2P (len k t s e : Nat) (l : zB)
    (hk : k < 2 ^ len) (ht : 0 < t) (he : e <= 1) (hs : len * 3 + t + 7 = s * 2 + e) :
    (((o1 ^ (4 + len * 3)) +> ld0 +> LC len k l) {{D}}>
      ([1,0,0,0] +> (o1 ^ t) +> default)) [z00]⊢*
    (z18 (LC (len + s) 0 l) (RC (k * 2 ^ s + 2 ^ (s - 1) + e))) := by
  let a := len / 2
  let c := t / 2
  rcases Nat.mod_two_eq_zero_or_one len with hlen0 | hlen1 <;>
    rcases Nat.mod_two_eq_zero_or_one t with ht0 | ht1
  · cases hc_eq : c with
    | zero => omega
    | succ c' =>
      have h_len : 4 + len * 3 = 4 + (a * 3) * 2 := by omega
      have h_t : t = 2 + c' * 2 := by omega
      have he_eq : e = 1 := by omega
      have hs_eq : s = 4 + a * 3 + c' := by omega
      rw [h_len,h_t]
      have h1 := z2L len k (a * 3) c' l hk
      have hlen_s : len + 1 + (3 + a * 3 + c') = len + s := by omega
      have hval : (k * 2 + 1) * 2 ^ (3 + a * 3 + c') + 1 = k * 2 ^ s + 2 ^ (s - 1) + e := by
        have hs1 : s - 1 = 3 + a * 3 + c' := by omega
        have hs2 : s = (3 + a * 3 + c') + 1 := by omega
        rw [hs1,hs2,he_eq,Nat.pow_succ]; ring
      rw [hlen_s,hval] at h1
      exact h1
  · have h_len : 4 + len * 3 = 4 + (a * 3) * 2 := by omega
    have h_t : t = 1 + c * 2 := by omega
    have he_eq : e = 0 := by omega
    have hs_eq : s = 4 + a * 3 + c := by omega
    rw [h_len,h_t]
    have h1 := z2M len k (a * 3) c l hk
    have hlen_s : len + 1 + (3 + a * 3 + c) = len + s := by omega
    have hval : (k * 2 + 1) * 2 ^ (3 + a * 3 + c) = k * 2 ^ s + 2 ^ (s - 1) + e := by
      have hs1 : s - 1 = 3 + a * 3 + c := by omega
      have hs2 : s = (3 + a * 3 + c) + 1 := by omega
      rw [hs1,hs2,he_eq,Nat.pow_succ]; ring
    rw [hlen_s,hval] at h1
    exact h1
  · cases hc_eq : c with
    | zero => omega
    | succ c' =>
      have h_len : 4 + len * 3 = 5 + (1 + a * 3) * 2 := by omega
      have h_t : t = 2 + c' * 2 := by omega
      have he_eq : e = 0 := by omega
      have hs_eq : s = 6 + a * 3 + c' := by omega
      rw [h_len,h_t]
      have h1 := z2N len k (1 + a * 3) c' l hk
      have hlen_s : len + 1 + (4 + (1 + a * 3) + c') = len + s := by omega
      have hval : (k * 2 + 1) * 2 ^ (4 + (1 + a * 3) + c') = k * 2 ^ s + 2 ^ (s - 1) + e := by
        have hs1 : s - 1 = 4 + (1 + a * 3) + c' := by omega
        have hs2 : s = (4 + (1 + a * 3) + c') + 1 := by omega
        rw [hs1,hs2,he_eq,Nat.pow_succ]; ring
      rw [hlen_s,hval] at h1
      exact h1
  · have h_len : 4 + len * 3 = 5 + (1 + a * 3) * 2 := by omega
    have h_t : t = 1 + c * 2 := by omega
    have he_eq : e = 1 := by omega
    have hs_eq : s = 5 + a * 3 + c := by omega
    rw [h_len,h_t]
    have h1 := z2O len k (1 + a * 3) c l hk
    have hlen_s : len + 1 + (3 + (1 + a * 3) + c) = len + s := by omega
    have hval : (k * 2 + 1) * 2 ^ (3 + (1 + a * 3) + c) + 1 = k * 2 ^ s + 2 ^ (s - 1) + e := by
      have hs1 : s - 1 = 3 + (1 + a * 3) + c := by omega
      have hs2 : s = (3 + (1 + a * 3) + c) + 1 := by omega
      rw [hs1,hs2,he_eq,Nat.pow_succ]; ring
    rw [hlen_s,hval] at h1
    exact h1
lemma z2Q (len k t s e : Nat) (l : zB)
    (hk : k < 2 ^ len) (ht : 4 <= t) (he : e <= 1) (hs : len * 3 + t + 7 = s * 2 + e) :
    (((o1 ^ (4 + len * 3)) +> ld0 +> LC len k l) {{D}}>
      ([1,1,0,0,0] +> (o1 ^ t) +> default)) [z00]⊢*
    (z18 (LC (len + s) 0 l) (RC (k * 2 ^ s + 2 ^ (s - 1) + e * 2 + 1))) := by
  let a := len / 2
  let c0 := t - 4
  let c := c0 / 2
  rcases Nat.mod_two_eq_zero_or_one len with hlen0 | hlen1 <;>
    rcases Nat.mod_two_eq_zero_or_one c0 with hc0 | hc1
  · have h_len : 4 + len * 3 = 4 + (a * 3) * 2 := by omega
    have h_t : t = 4 + c * 2 := by omega
    have he_eq : e = 1 := by omega
    have hs_eq : s = 5 + a * 3 + c := by omega
    rw [h_len,h_t]
    have h1 := z1r (a * 3) c (LC len k l)
    rw [z2I] at h1
    have h2 := z2H len k (1 + a * 3) (1 + c) l hk (by omega) (by omega)
    have hlen_s : len + (1 + a * 3) + (1 + c) + 3 = len + s := by omega
    have hval : (k * 2 + 1) * 2 ^ ((1 + a * 3) + (1 + c) + 2) + 3 =
        k * 2 ^ s + 2 ^ (s - 1) + e * 2 + 1 := by
      have hs1 : s - 1 = (1 + a * 3) + (1 + c) + 2 := by omega
      have hs2 : s = ((1 + a * 3) + (1 + c) + 2) + 1 := by omega
      rw [hs1,hs2,he_eq,Nat.pow_succ]; ring
    rw [hlen_s,hval] at h2
    exact zSt h1 h2
  · have h_len : 4 + len * 3 = 4 + (a * 3) * 2 := by omega
    have h_t : t = 5 + c * 2 := by omega
    have he_eq : e = 0 := by omega
    have hs_eq : s = 6 + a * 3 + c := by omega
    rw [h_len,h_t]
    have h1 := z1s (a * 3) c (LC len k l)
    have h2 := z2G len k (1 + a * 3) (2 + c) l hk (by omega) (by omega)
    rw [<- z2K] at h2
    have hlen_s : len + (1 + a * 3) + (2 + c) + 3 = len + s := by omega
    have hval : (k * 2 + 1) * 2 ^ ((1 + a * 3) + (2 + c) + 2) + 1 =
        k * 2 ^ s + 2 ^ (s - 1) + e * 2 + 1 := by
      have hs1 : s - 1 = (1 + a * 3) + (2 + c) + 2 := by omega
      have hs2 : s = ((1 + a * 3) + (2 + c) + 2) + 1 := by omega
      rw [hs1,hs2,he_eq,Nat.pow_succ]; ring
    rw [hlen_s,hval] at h2
    exact zSt h1 h2
  · have h_len : 4 + len * 3 = 5 + (1 + a * 3) * 2 := by omega
    have h_t : t = 4 + c * 2 := by omega
    have he_eq : e = 0 := by omega
    have hs_eq : s = 7 + a * 3 + c := by omega
    rw [h_len,h_t]
    have h1 := z1t (1 + a * 3) c (LC len k l)
    have h2 := z2G len k (2 + (1 + a * 3)) (1 + c) l hk (by omega) (by omega)
    rw [<- z2K] at h2
    have hlen_s : len + (2 + (1 + a * 3)) + (1 + c) + 3 = len + s := by omega
    have hval : (k * 2 + 1) * 2 ^ ((2 + (1 + a * 3)) + (1 + c) + 2) + 1 =
        k * 2 ^ s + 2 ^ (s - 1) + e * 2 + 1 := by
      have hs1 : s - 1 = (2 + (1 + a * 3)) + (1 + c) + 2 := by omega
      have hs2 : s = ((2 + (1 + a * 3)) + (1 + c) + 2) + 1 := by omega
      rw [hs1,hs2,he_eq,Nat.pow_succ]; ring
    rw [hlen_s,hval] at h2
    exact zSt h1 h2
  · have h_len : 4 + len * 3 = 5 + (1 + a * 3) * 2 := by omega
    have h_t : t = 5 + c * 2 := by omega
    have he_eq : e = 1 := by omega
    have hs_eq : s = 7 + a * 3 + c := by omega
    rw [h_len,h_t]
    have h1 := z1u (1 + a * 3) c (LC len k l)
    rw [z2I] at h1
    have h2 := z2H len k (2 + (1 + a * 3)) (1 + c) l hk (by omega) (by omega)
    have hlen_s : len + (2 + (1 + a * 3)) + (1 + c) + 3 = len + s := by omega
    have hval : (k * 2 + 1) * 2 ^ ((2 + (1 + a * 3)) + (1 + c) + 2) + 3 =
        k * 2 ^ s + 2 ^ (s - 1) + e * 2 + 1 := by
      have hs1 : s - 1 = (2 + (1 + a * 3)) + (1 + c) + 2 := by omega
      have hs2 : s = ((2 + (1 + a * 3)) + (1 + c) + 2) + 1 := by omega
      rw [hs1,hs2,he_eq,Nat.pow_succ]; ring
    rw [hlen_s,hval] at h2
    exact zSt h1 h2
def zDb (len k : Nat) (l : zB) : zB :=
  (o1 ^ (len * 3 + 3)) +> ld0 +> LC len k l
lemma z2R (len k n : Nat) (l : zB) :
    (ld1 ^ n) +> ld0 +> LC len k l = LC (len + 1 + n) ((k * 2 + 1) * 2 ^ n) l := by
  unfold LC
  rw [z0p ld0 ld1 (len + 1) (k * 2 + 1) n l,z0m]
lemma z2S (a k : Nat) (l : zB) :
    zDb (a * 2 + 1) k l = LC (a * 2 + 1 + 1 + (a * 3 + 3)) ((k * 2 + 1) * 2 ^ (a * 3 + 3)) l := by
  unfold zDb
  have h1 : (a * 2 + 1) * 3 + 3 = (a * 3 + 3) * 2 := by omega
  have h2 : (o1 ++ o1) = ld1 := rfl
  rw [h1,z0d,h2]
  exact z2R (a * 2 + 1) k (a * 3 + 3) l
lemma z2T (a k : Nat) (l : zB) :
    zDb (a * 2) k l = LC (a * 3 + 1) 0 ([1,0,1] +> LC (a * 2) k l) := by
  unfold zDb LC
  rw [z0n]
  have h1 : a * 2 * 3 + 3 = (a * 3 + 1) * 2 + 1 := by omega
  have h2 : (o1 ++ o1) = ld1 := rfl
  rw [h1,z09 o1 ((a * 3 + 1) * 2) 1,z0d,h2,append_assoc]
  rfl
lemma z2U (a k n v r : Nat) (l : zB)
    (hk : k < 2 ^ (a * 2 + 1)) (hv : v < 2 ^ n) :
    (z18 (LC n v (zDb (a * 2 + 1) k l)) (RC r)) [z00]⊢*
    (z18 (LC (a * 2 + 1 + (a * 3 + 4 + n)) 0 l)
      (RC ((k * 2 + 1) * 2 ^ (a * 3 + 3 + n) + v + r))) := by
  rw [z2S,z2B _ _ _ _ _ hv]
  have hbound : ((k * 2 + 1) * 2 ^ (a * 3 + 3)) * 2 ^ n + v < 2 ^ (a * 2 + 1 + 1 + (a * 3 + 3) + n) := by
    have hp : 2 ^ (a * 2 + 1 + 1 + (a * 3 + 3) + n) =
        (2 ^ (a * 2 + 1) * 2) * 2 ^ (a * 3 + 3) * 2 ^ n := by
      rw [Nat.pow_add,Nat.pow_add,Nat.pow_succ]
    have hle1 : k * 2 + 1 + 1 <= 2 ^ (a * 2 + 1) * 2 := by omega
    have hle2 : (k * 2 + 1 + 1) * (2 ^ (a * 3 + 3) * 2 ^ n) <=
        (2 ^ (a * 2 + 1) * 2) * (2 ^ (a * 3 + 3) * 2 ^ n) :=
      Nat.mul_le_mul_right _ hle1
    rw [Nat.add_mul,Nat.one_mul,<- Nat.mul_assoc,<- Nat.mul_assoc] at hle2
    have hpos : 0 < 2 ^ (a * 3 + 3) := z0h (a * 3 + 3)
    have hv_lt : v < 2 ^ (a * 3 + 3) * 2 ^ n := by
      have : 1 * 2 ^ n <= 2 ^ (a * 3 + 3) * 2 ^ n := Nat.mul_le_mul_right (2 ^ n) hpos
      omega
    omega
  have h1 := z2p (a * 2 + 1 + 1 + (a * 3 + 3) + n) 0
    (((k * 2 + 1) * 2 ^ (a * 3 + 3)) * 2 ^ n + v) r l (by omega)
  have h0 : 0 + (((k * 2 + 1) * 2 ^ (a * 3 + 3)) * 2 ^ n + v) =
      ((k * 2 + 1) * 2 ^ (a * 3 + 3)) * 2 ^ n + v := by omega
  have hlen : a * 2 + 1 + 1 + (a * 3 + 3) + n = a * 2 + 1 + (a * 3 + 4 + n) := by omega
  have hval : r + (((k * 2 + 1) * 2 ^ (a * 3 + 3)) * 2 ^ n + v) =
      (k * 2 + 1) * 2 ^ (a * 3 + 3 + n) + v + r := by
    rw [Nat.pow_add]; ring
  rw [h0,hlen,hval] at h1
  rw [hlen]
  exact h1
lemma z2V (a k n v r : Nat) (l : zB)
    (ha : 0 < a) (hk : k < 2 ^ (a * 2)) (hv : v < 2 ^ n) (hvr : v + r < 2 ^ (n + 2)) :
    (z18 (LC n v (zDb (a * 2) k l)) (RC r)) [z00]⊢*
    (z18 (LC (a * 2 + (a * 3 + 2 + n)) 0 l)
      (RC ((k * 2 + 1) * 2 ^ (a * 3 + 1 + n) + (v + r) * 2 + 1))) := by
  rw [z2T,z2B _ _ _ _ _ hv]
  have h0v : 0 * 2 ^ n + v = v := by simp
  rw [h0v]
  have hn_le : 2 ^ n <= 2 ^ (a * 3 + 1 + n) := z1T (by omega)
  have h1 := z2p (a * 3 + 1 + n) 0 v r ([1,0,1] +> LC (a * 2) k l) (by omega)
  have h0 : 0 + v = v := by omega
  rw [h0] at h1
  have hvr_bound : (r + v) * 2 + 1 < 2 ^ (a * 3 + 1 + n) := by
    have hp : 2 ^ (n + 2 + 1) <= 2 ^ (a * 3 + 1 + n) := z1T (by omega)
    rw [Nat.pow_succ] at hp
    omega
  have h2 := z2C (a * 2) k (a * 3 + 1 + n) (r + v) l hk (by omega) hvr_bound
  have hlen : a * 2 + 1 + (a * 3 + 1 + n) = a * 2 + (a * 3 + 2 + n) := by omega
  have hval : k * 2 ^ (a * 3 + 1 + n + 1) + 2 ^ (a * 3 + 1 + n) + (r + v) * 2 + 1 =
      (k * 2 + 1) * 2 ^ (a * 3 + 1 + n) + (v + r) * 2 + 1 := by
    rw [Nat.pow_succ]; ring
  rw [hlen,hval] at h2
  exact zSt h1 h2
lemma z2W (a b : Nat) (l : zB) :
    [1] +> (([1,0] ^ b) +> (o1 ^ (1 + a)) +> l) =
    ld1 +> (ld0 ^ b) +> (o1 ^ a) +> l := by
  rw [z09 o1 1 a]
  have h1 : (o1 ^ 1 : zF) = [1] := rfl
  have hrot : (([1,0] : zF) ^ b) +> ([1] +> ((o1 ^ a) +> l)) =
      [1] +> ((ld0 ^ b) +> ((o1 ^ a) +> l)) := by
    have h10 : ([1,0] : zF) = [1] ++ [0] := rfl
    rw [<- append_assoc,h10,z0b [1] [0] b,append_assoc]; rfl
  rw [h1,append_assoc,hrot]
  rfl
lemma z2X (len b : Nat) (l : zB) :
    [1] +> (([1,0] ^ b) +> (o1 ^ (4 + len * 3)) +> l) =
    ld1 +> (ld0 ^ b) +> (o1 ^ (len * 3 + 3)) +> l := by
  have hlen : 4 + len * 3 = 1 + (len * 3 + 3) := by omega
  rw [hlen]
  exact z2W (len * 3 + 3) b l
lemma z2Y (b c : Nat) (l : zB) :
    (ld0 ^ c) +> ld1 +> (ld0 ^ b) +> l =
    LC (b + 1 + c) ((2 ^ (b + 1) - 1) * 2 ^ c - 1) l := by
  have hpb := z0h b
  have h1 : (2 ^ (b + 1) - 1) * 2 ^ c - 1 = ((2 ^ b - 1) * 2 + 1) * 2 ^ c - 1 := by
    rw [Nat.pow_succ]
    have : 2 ^ b * 2 - 1 = (2 ^ b - 1) * 2 + 1 := by omega
    rw [this]
  rw [h1,<- z2w b (2 ^ b - 1) c l]
  unfold LC
  rw [z0o]
lemma z2Z (b c : Nat) : (2 ^ (b + 1) - 1) * 2 ^ c - 1 < 2 ^ (b + 1 + c) := by
  have hpb := z0h (b + 1)
  have hpc := z0h c
  have hpos : 1 <= (2 ^ (b + 1) - 1) * 2 ^ c := Nat.mul_pos (by omega) hpc
  have hp : 2 ^ (b + 1 + c) = 2 ^ (b + 1) * 2 ^ c := Nat.pow_add 2 (b + 1) c
  have hle : (2 ^ (b + 1) - 1) * 2 ^ c <= 2 ^ (b + 1) * 2 ^ c :=
    Nat.mul_le_mul_right (2 ^ c) (by omega)
  omega
lemma z30 (len k b c : Nat) (l : zB) :
    (((o1 ^ (4 + len * 3)) +> ld0 +> LC len k l) {{D}}>
      ((o1 ^ (3 + b * 2)) +> z +> (o1 ^ (3 + c * 2)) +> default)) [z00]⊢*
    (z18 (LC (b + 1 + (2 + c)) ((2 ^ (b + 1) - 1) * 2 ^ (2 + c) - 1) (zDb len k l)) (RC 2)) := by
  have h1 := z1g b c ((o1 ^ (4 + len * 3)) +> ld0 +> LC len k l)
  rw [z2X len b (ld0 +> LC len k l)] at h1
  have hdb : (o1 ^ (len * 3 + 3)) +> ld0 +> LC len k l = zDb len k l := rfl
  rw [hdb,z2Y b (2 + c) (zDb len k l),z2I] at h1
  exact h1
lemma z31 (a q h k n v r : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q))
    (hv : v < 2 ^ n) (hvr : v + r < 2 ^ (n + 2)) :
    let s := a * 3 + 2 + q * 2 + n
    (z18 (LC n v (zDb (a * 2 + q) k l)) (RC r)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + (v + r) * (1 + h) + h))) := by
  intro s
  rcases q with _ | _ | q
  · have hh : h = 1 := by omega
    subst hh
    have hq0 : a * 2 + 0 = a * 2 := by omega
    have hs_eq : s = a * 3 + 2 + n := by omega
    rw [hq0] at hk ⊢
    have h1 := z2V a k n v r l (by omega) hk hv hvr
    have hlen : a * 2 + (a * 3 + 2 + n) = a * 2 + s := by omega
    have hval : (k * 2 + 1) * 2 ^ (a * 3 + 1 + n) + (v + r) * 2 + 1 =
        k * 2 ^ s + 2 ^ (s - 1) + (v + r) * (1 + 1) + 1 := by
      have hs1 : s - 1 = a * 3 + 1 + n := by omega
      have hs2 : s = (a * 3 + 1 + n) + 1 := by omega
      rw [hs1,hs2,Nat.pow_succ]; ring
    rw [hlen,hval] at h1
    exact h1
  · have hh : h = 0 := by omega
    subst hh
    have hs_eq : s = a * 3 + 4 + n := by omega
    have h1 := z2U a k n v r l hk hv
    have hlen : a * 2 + 1 + (a * 3 + 4 + n) = a * 2 + 1 + s := by omega
    have hval : (k * 2 + 1) * 2 ^ (a * 3 + 3 + n) + v + r =
        k * 2 ^ s + 2 ^ (s - 1) + (v + r) * (1 + 0) + 0 := by
      have hs1 : s - 1 = a * 3 + 3 + n := by omega
      have hs2 : s = (a * 3 + 3 + n) + 1 := by omega
      rw [hs1,hs2,Nat.pow_succ]; ring
    rw [hlen,hval] at h1
    exact h1
  · omega
lemma z32 (a q h k b c : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let s := a * 3 + 2 + q * 2 + (b + 1 + (2 + c))
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (3 + b * 2)) +> z +> (o1 ^ (3 + c * 2)) +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 ^ (2 + c) + 1) * (1 + h) + h))) := by
  intro s
  have h1 := z30 (a * 2 + q) k b c l
  have hv := z2Z b (2 + c)
  have hvr : (2 ^ (b + 1) - 1) * 2 ^ (2 + c) - 1 + 2 < 2 ^ (b + 1 + (2 + c) + 2) := by
    have hp := z0h (b + 1 + (2 + c))
    rw [Nat.pow_add 2 (b + 1 + (2 + c)) 2]
    omega
  have h2 := z31 a q h k (b + 1 + (2 + c)) ((2 ^ (b + 1) - 1) * 2 ^ (2 + c) - 1) 2 l
    hqh hL hk hv hvr
  have hpb := z0h b
  have hpc := z0h (2 + c)
  have hpos1 : 2 <= 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
  have hpos2 : 1 <= (2 ^ (b + 1) - 1) * 2 ^ (2 + c) := Nat.mul_pos (by omega) hpc
  have hval : (2 ^ (b + 1) - 1) * 2 ^ (2 + c) - 1 + 2 = (2 ^ (b + 1) - 1) * 2 ^ (2 + c) + 1 := by omega
  rw [hval] at h2
  exact zSt h1 h2
lemma z33 (a q h k b c r : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q))
    (hr1 : 1 <= r) (hr2 : r <= 2) :
    let s := a * 3 + 2 + q * 2 + (b + 1 + c)
    (z18 (LC (b + 1 + c) ((2 ^ (b + 1) - 1) * 2 ^ c - 1) (zDb (a * 2 + q) k l)) (RC r)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 ^ c + (r - 1)) * (1 + h) + h))) := by
  intro s
  have hv := z2Z b c
  have hvr : (2 ^ (b + 1) - 1) * 2 ^ c - 1 + r < 2 ^ (b + 1 + c + 2) := by
    have hp := z0h (b + 1 + c)
    rw [Nat.pow_add 2 (b + 1 + c) 2]
    omega
  have h1 := z31 a q h k (b + 1 + c) ((2 ^ (b + 1) - 1) * 2 ^ c - 1) r l hqh hL hk hv hvr
  have hpb := z0h b
  have hpc := z0h c
  have hpos1 : 2 <= 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
  have hpos2 : 1 <= (2 ^ (b + 1) - 1) * 2 ^ c := Nat.mul_pos (by omega) hpc
  have hval : (2 ^ (b + 1) - 1) * 2 ^ c - 1 + r = (2 ^ (b + 1) - 1) * 2 ^ c + (r - 1) := by omega
  rw [hval] at h1
  exact h1
lemma z34 (a q h k b c : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let s := a * 3 + 2 + q * 2 + (b + 1 + (4 + c))
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (3 + b * 2)) +> z +> (o1 ^ (6 + c * 2)) +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 ^ (4 + c)) * (1 + h) + h))) := by
  intro s
  have h1 := z1f b c ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  rw [z2X (a * 2 + q) b (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  rw [hdb,z2Y b (4 + c) (zDb (a * 2 + q) k l)] at h1
  have h2 := zPs (z2o 0 (LC (b + 1 + (4 + c)) ((2 ^ (b + 1) - 1) * 2 ^ (4 + c) - 1) (zDb (a * 2 + q) k l)))
  rw [<- z2K] at h2
  have h3 := z33 a q h k b (4 + c) 1 l hqh hL hk (by omega) (by omega)
  simp only [Nat.sub_self,Nat.add_zero] at h3
  exact zSt h1 (zSt h2 h3)
lemma z35 (a q h k b : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let s := a * 3 + 2 + q * 2 + (b + 1 + 1)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (3 + b * 2)) +> z +> [1] +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 + 1) * (1 + h) + h))) := by
  intro s
  have h1 := z1E b ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  have h_r : (o1 ^ (3 + b * 2)) +> [0,0,0,1] +> (default : zB) =
      (o1 ^ (3 + b * 2)) +> z +> [1] +> default := rfl
  rw [h_r,z2X (a * 2 + q) b (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  have hld0 : ld0 +> ld1 +> (ld0 ^ b) +> zDb (a * 2 + q) k l =
      (ld0 ^ 1) +> ld1 +> (ld0 ^ b) +> zDb (a * 2 + q) k l := rfl
  rw [hdb,hld0,z2Y b 1 (zDb (a * 2 + q) k l),z2I] at h1
  have h2 := z33 a q h k b 1 2 l hqh hL hk (by omega) (by omega)
  simp only [Nat.pow_one] at h2
  exact zSt h1 h2
lemma z36 (b c : Nat) (l : zB) :
    (ld1 ^ c) +> (ld0 ^ b) +> l = LC (b + c) ((2 ^ b - 1) * 2 ^ c) l := by
  unfold LC
  rw [z0p,z0o]
lemma z37 (a q h k b c : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let s := a * 3 + 2 + q * 2 + (b + c)
    (z18 ((ld1 ^ c) +> (ld0 ^ b) +> zDb (a * 2 + q) k l) (RC 0)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ b - 1) * 2 ^ c) * (1 + h) + h))) := by
  intro s
  rw [z36]
  have hpb := z0h b
  have hpc := z0h c
  have hv : (2 ^ b - 1) * 2 ^ c < 2 ^ (b + c) := by
    rw [Nat.pow_add]
    have hlt : 2 ^ b - 1 < 2 ^ b := by omega
    exact Nat.mul_lt_mul_of_pos_right hlt hpc
  have hvr : (2 ^ b - 1) * 2 ^ c + 0 < 2 ^ (b + c + 2) := by
    rw [Nat.pow_add 2 (b + c) 2]
    have hp := z0h (b + c)
    omega
  have h1 := z31 a q h k (b + c) ((2 ^ b - 1) * 2 ^ c) 0 l hqh hL hk hv hvr
  simp only [Nat.add_zero] at h1
  exact h1
lemma z38 (a b c : Nat) (l : zB) :
    (o1 ^ (1 + c * 2)) +> (([1,0] ^ b) +> (o1 ^ (1 + a)) +> l) =
    (ld1 ^ (1 + c)) +> (ld0 ^ b) +> (o1 ^ a) +> l := by
  have hc1 : 1 + c * 2 = c * 2 + 1 := by omega
  have hc2 : 1 + c = c + 1 := by omega
  have hld1 : (o1 ++ o1) = ld1 := rfl
  rw [hc1,z09 o1 (c * 2) 1,z0d,hld1]
  have ho1 : (o1 ^ 1 : zF) = [1] := rfl
  rw [ho1,append_assoc,z2W,<- append_assoc (ld1 ^ c) ld1,z0a,hc2]
lemma z39 (len b c : Nat) (l : zB) :
    (o1 ^ (1 + c * 2)) +> (([1,0] ^ b) +> (o1 ^ (4 + len * 3)) +> l) =
    (ld1 ^ (1 + c)) +> (ld0 ^ b) +> (o1 ^ (len * 3 + 3)) +> l := by
  have hlen : 4 + len * 3 = 1 + (len * 3 + 3) := by omega
  rw [hlen]
  exact z38 (len * 3 + 3) b c l
lemma z3a (a q h k b : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let s := a * 3 + 2 + q * 2 + (b + 2)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (1 + b * 2)) +> z +> [1,1] +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ b - 1) * 4) * (1 + h) + h))) := by
  intro s
  have h1 := z1l b ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  have hr : (o1 ^ (1 + b * 2)) +> [0,0,0,1,1] +> (default : zB) =
      (o1 ^ (1 + b * 2)) +> z +> [1,1] +> default := rfl
  have ho3 : (o1 ^ 3 : zF) = o1 ^ (1 + 1 * 2) := rfl
  rw [hr,ho3,z39 (a * 2 + q) b 1 (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  rw [hdb] at h1
  have h2 := z37 a q h k b 2 l hqh hL hk
  rw [<- z2K] at h2
  exact zSt h1 h2
lemma z3b (a q h k b : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let s := a * 3 + 2 + q * 2 + (b + 3)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (1 + b * 2)) +> z +> (o1 ^ 4) +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ b - 1) * 8) * (1 + h) + h))) := by
  intro s
  have h1 := z1e b ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  have ho5 : (o1 ^ 5 : zF) = o1 ^ (1 + 2 * 2) := rfl
  rw [ho5,z39 (a * 2 + q) b 2 (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  rw [hdb] at h1
  have h2 := z37 a q h k b 3 l hqh hL hk
  rw [<- z2K] at h2
  exact zSt h1 h2
lemma z3c (a b : Nat) (l : zB) :
    [0] +> (([1,0] ^ b) +> (o1 ^ (1 + a)) +> l) =
    (ld0 ^ (1 + b)) +> (o1 ^ a) +> l := by
  rw [z09 o1 1 a]
  have h1 : (o1 ^ 1 : zF) = [1] := rfl
  have hrot : (([1,0] : zF) ^ b) +> ([1] +> ((o1 ^ a) +> l)) =
      [1] +> ((ld0 ^ b) +> ((o1 ^ a) +> l)) := by
    have h10 : ([1,0] : zF) = [1] ++ [0] := rfl
    rw [<- append_assoc,h10,z0b [1] [0] b,append_assoc]; rfl
  have hb : 1 + b = b + 1 := by omega
  rw [h1,append_assoc,hrot,hb,z08,append_assoc]
  rfl
lemma z3d (a j : Nat) (l : zB) :
    (((o1 ^ (1 + a)) +> l) {{D}}> ((o1 ^ (2 + j * 2)) +> default)) [z00]⊢*
    (z19 ((ld0 ^ j) +> (o1 ^ a) +> l) (RC 0)) := by
  cases j with
  | zero =>
    rw [z09 o1 1 a]
    have h1 : (o1 ^ 1 : zF) = [1] := rfl
    have h2 : (o1 ^ (2 + 0 * 2) : zF) = [1,1] := rfl
    rw [h1,h2,append_assoc,<- z2K]
    simpa using z1v ((o1 ^ a) +> l)
  | succ j =>
    have hj : 2 + (j + 1) * 2 = 4 + j * 2 := by omega
    rw [hj]
    have h1 := z1x j ((o1 ^ (1 + a)) +> l)
    rw [z3c a j l] at h1
    have hj1 : 1 + j = j + 1 := by omega
    rw [hj1] at h1
    rw [<- z2K]
    exact h1
lemma z3e (a j : Nat) (l : zB) :
    (((o1 ^ (1 + a)) +> l) {{D}}> ((o1 ^ (3 + j * 2)) +> default)) [z00]⊢*
    (z18 ((ld0 ^ j) +> (o1 ^ a) +> l) (RC 2)) := by
  cases j with
  | zero =>
    rw [z09 o1 1 a]
    have h1 : (o1 ^ 1 : zF) = [1] := rfl
    have h2 : (o1 ^ (3 + 0 * 2) : zF) = [1,1,1] := rfl
    rw [h1,h2,append_assoc,<- z2I]
    simpa using z1w ((o1 ^ a) +> l)
  | succ j =>
    have hj : 3 + (j + 1) * 2 = 5 + j * 2 := by omega
    rw [hj]
    have h1 := z1y j ((o1 ^ (1 + a)) +> l)
    rw [z3c a j l,z2I] at h1
    have hj1 : 1 + j = j + 1 := by omega
    rw [hj1] at h1
    exact h1
lemma z3f (len k j p : Nat) (l : zB) (hp : p <= 1) :
    (((o1 ^ (4 + len * 3)) +> ld0 +> LC len k l) {{D}}>
      ((o1 ^ (2 + j * 2 + p)) +> default)) [z00]⊢*
    (z18 (LC j (2 ^ j - 1) (zDb len k l)) (RC (1 + p))) := by
  have hfull : LC j (2 ^ j - 1) (zDb len k l) = (ld0 ^ j) +> (o1 ^ (len * 3 + 3)) +> ld0 +> LC len k l := by
    unfold zDb
    rw [LC,z0o]
  rw [hfull]
  have hlen : 4 + len * 3 = 1 + (len * 3 + 3) := by omega
  rw [hlen]
  rcases p with _ | _ | p
  · simp only [Nat.add_zero]
    have h1 := z3d (len * 3 + 3) j (ld0 +> LC len k l)
    have h2 := zPs (z2o 0 ((ld0 ^ j) +> (o1 ^ (len * 3 + 3)) +> ld0 +> LC len k l))
    exact zSt h1 h2
  · have hp1 : 2 + j * 2 + 1 = 3 + j * 2 := by omega
    rw [hp1]
    exact z3e (len * 3 + 3) j (ld0 +> LC len k l)
  · omega
lemma z3g (a q h k j p : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) (hp : p <= 1) :
    let s := a * 3 + 2 + q * 2 + j
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (2 + j * 2 + p)) +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + (2 ^ j + p) * (1 + h) + h))) := by
  intro s
  have h1 := z3f (a * 2 + q) k j p l hp
  have hpj := z0h j
  have hv : 2 ^ j - 1 < 2 ^ j := by omega
  have hvr : 2 ^ j - 1 + (1 + p) < 2 ^ (j + 2) := by
    rw [Nat.pow_add 2 j 2]; omega
  have h2 := z31 a q h k j (2 ^ j - 1) (1 + p) l hqh hL hk hv hvr
  have hval : 2 ^ j - 1 + (1 + p) = 2 ^ j + p := by omega
  rw [hval] at h2
  exact zSt h1 h2
lemma z3h (len k : Nat) (l : zB) (hk : k < 2 ^ len) :
    (((o1 ^ (4 + len * 3)) +> ld0 +> LC len k l) {{D}}> ([1] +> default)) [z00]⊢*
    (z18 (LC len 0 l) (RC (k + 2 ^ (len + 2)))) := by
  have h1 := z1z len (LC len k l)
  have hlen : 2 + len = len + 2 := by omega
  have hrc_pow : (z ^ (len + 2)) +> d +> default = RC (2 ^ (len + 2)) := by
    unfold RC
    exact (z0w z1U (len + 2)).symm
  rw [hlen,hrc_pow] at h1
  have h2 := z2p len 0 k (2 ^ (len + 2)) l (by omega)
  have h0 : 0 + k = k := by omega
  have hval : 2 ^ (len + 2) + k = k + 2 ^ (len + 2) := by omega
  rw [h0,hval] at h2
  exact zSt h1 h2
lemma z3i (len k : Nat) (w : zF) (l : zB)
    (hw : zDg len k w) :
    (((o1 ^ (4 + len * 3)) +> ld0 +> LC len k l) {{D}}> ([1] +> default)) [z00]⊢*
    (z18 (LC len 0 l) (w +> RC 4)) := by
  have hk := z1W hw
  have h1 := z3h len k l hk
  have h2 := z2m hw 4
  have hval : k + 2 ^ len * 4 = k + 2 ^ (len + 2) := by
    rw [Nat.pow_add]
  rw [hval] at h2
  rw [<- h2] at h1
  exact h1
lemma z3j (a q h k b : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let s := a * 3 + 2 + q * 2 + (b + 1)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (4 + b * 2)) +> z +> [1] +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + (2 ^ (b + 1) + 2) * (1 + h) + h))) := by
  intro s
  have h1 := z1F b ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  have hr : (o1 ^ (4 + b * 2)) +> [0,0,0,1] +> (default : zB) =
      (o1 ^ (4 + b * 2)) +> z +> [1] +> default := rfl
  rw [hr,z2X (a * 2 + q) b (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  have hld1 : ld1 +> (ld0 ^ b) +> zDb (a * 2 + q) k l =
      (ld1 ^ 1) +> (ld0 ^ b) +> zDb (a * 2 + q) k l := rfl
  rw [hdb,hld1,z36 b 1 (zDb (a * 2 + q) k l),z2J] at h1
  have hpb := z0h b
  have hv : (2 ^ b - 1) * 2 ^ 1 < 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
  have hvr : (2 ^ b - 1) * 2 ^ 1 + 4 < 2 ^ (b + 1 + 2) := by
    rw [Nat.pow_add 2 (b + 1) 2,Nat.pow_succ]; omega
  have h2 := z31 a q h k (b + 1) ((2 ^ b - 1) * 2 ^ 1) 4 l hqh hL hk hv hvr
  have hval : (2 ^ b - 1) * 2 ^ 1 + 4 = 2 ^ (b + 1) + 2 := by rw [Nat.pow_succ]; omega
  rw [hval] at h2
  exact zSt h1 h2
lemma z3k (n k m J v : Nat) (l : zB)
    (hk : k < 2 ^ n) (hm : 0 < m) (hv : v * 2 + 1 < 2 ^ J)
    (hsum : 2 ^ J <= ((k * 2 + 1) * 2 ^ m - 1) + (v * 2 + 2)) :
    (z18 (LC m 0 ([1,0,1] +> LC n k l)) (RC v)) [z00]⊢*
    (z18 (LC (n + 1 + m) 0 l) (RC ((k * 2 + 1) * 2 ^ m - 1 + v * 2 + 2))) := by
  rcases z2v m J v (LC n k l) hm hv with ⟨w,hw,hrun⟩
  have hfull : LC m (2 ^ m - 1) (ld1 +> LC n k l) = (ld0 ^ m) +> ld1 +> LC n k l := by
    unfold LC; rw [z0o]
  rw [hfull,z2w n k m l] at hrun
  have hbound := z2x n k m hk
  have hV_hi : v * 2 + 2 < 2 ^ (J + 1) := by rw [Nat.pow_succ]; omega
  have hlo : 2 ^ J <= (v * 2 + 2) + ((k * 2 + 1) * 2 ^ m - 1) := by omega
  have h2 := z2u (n + 1 + m) ((k * 2 + 1) * 2 ^ m - 1) J (v * 2 + 2) w l hbound hV_hi hlo hw
  have hval : (v * 2 + 2) + ((k * 2 + 1) * 2 ^ m - 1) = (k * 2 + 1) * 2 ^ m - 1 + v * 2 + 2 := by omega
  rw [hval] at h2
  exact zSt hrun h2
lemma z3l (b c e : Nat) (l : zB)
    (he : e <= 1) (hc : 1 <= c \/ e = 0) :
    (z18 (LC (1 + c) 0 ([1,0,1] +> ld1 +> (ld0 ^ b) +> l)) (RC (2 ^ c + e))) [z00]⊢*
    (z18 (LC (b + c + 3) 0 l) (RC ((2 ^ (b + 1) - 1) * 2 ^ (c + 2) + (e * 2 + 1)))) := by
  have hld1 : [1,0,1] +> ld1 +> (ld0 ^ b) +> l = [1,0,1] +> (ld1 ^ 1) +> (ld0 ^ b) +> l := rfl
  rw [hld1,z36 b 1 l]
  have hpb := z0h b
  have hpc := z0h c
  have hk : (2 ^ b - 1) * 2 ^ 1 < 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
  have hsmall : (2 ^ c + e) * 2 + 1 < 2 ^ (c + 2) := by
    rw [Nat.pow_add 2 c 2]
    rcases hc with hc1 | he0
    · have : 2 <= 2 ^ c := by
        have hle := z1T hc1
        simpa using hle
      omega
    · omega
  have hsum : 2 ^ (c + 2) <= (((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * 2 ^ (1 + c) - 1) + ((2 ^ c + e) * 2 + 2) := by
    have h1 : 1 <= ((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * 2 ^ (1 + c) := by
      have hp1c := z0h (1 + c)
      exact Nat.mul_pos (by omega) hp1c
    have h2 : 1 * 2 ^ (1 + c) <= ((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * 2 ^ (1 + c) :=
      Nat.mul_le_mul_right (2 ^ (1 + c)) (by omega)
    have hp1c_eq : 2 ^ (1 + c) = 2 ^ c * 2 := by rw [Nat.add_comm 1 c,Nat.pow_succ]
    have hpc2_eq : 2 ^ (c + 2) = 2 ^ c * 4 := by rw [Nat.pow_add]
    omega
  have h1 := z3k (b + 1) ((2 ^ b - 1) * 2 ^ 1) (1 + c) (c + 2) (2 ^ c + e) l
    hk (by omega) hsmall hsum
  have hlen : b + 1 + 1 + (1 + c) = b + c + 3 := by omega
  have hval : ((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * 2 ^ (1 + c) - 1 + (2 ^ c + e) * 2 + 2 =
      (2 ^ (b + 1) - 1) * 2 ^ (c + 2) + (e * 2 + 1) := by
    have hp1c_eq : 2 ^ (1 + c) = 2 ^ c * 2 := by rw [Nat.add_comm 1 c,Nat.pow_succ]
    have hpc2_eq : 2 ^ (c + 2) = 2 ^ c * 4 := by rw [Nat.pow_add]
    have hpb1_eq : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
    rw [hp1c_eq,hpc2_eq,hpb1_eq]
    have hsub : (2 ^ b - 1) * 2 ^ 1 * 2 + 1 = 2 ^ b * 4 - 3 := by omega
    have hmul1 : (2 ^ b * 4) * (2 ^ c * 2) = (2 ^ b * 2 ^ c) * 8 := by ring
    have hmul2 : (2 ^ b * 2) * (2 ^ c * 4) = (2 ^ b * 2 ^ c) * 8 := by ring
    have hbc : 2 ^ c <= 2 ^ b * 2 ^ c := Nat.le_mul_of_pos_left _ hpb
    rw [hsub,Nat.sub_mul,Nat.sub_mul,hmul1,hmul2]
    omega
  rw [hlen,hval] at h1
  exact h1
lemma z3m (b c : Nat) (l : zB) :
    (z19 ((ld0 ^ c) +> ld1 +> [1,0,1] +> ld1 +> (ld0 ^ b) +> l) (RC 0)) [z00]⊢*
    (z18 (LC (b + c + 3) 0 l) (RC ((2 ^ (b + 1) - 1) * 2 ^ (c + 2) + 1))) := by
  rw [z2E c ([1,0,1] +> ld1 +> (ld0 ^ b) +> l)]
  have hpc := z0h c
  have hbound : 2 ^ c - 1 < 2 ^ (1 + c) := by rw [Nat.add_comm 1 c,Nat.pow_succ]; omega
  have h1 := z2q (1 + c) (2 ^ c - 1) 0 ([1,0,1] +> ld1 +> (ld0 ^ b) +> l) hbound
  have hval1 : 2 ^ c - 1 + 0 + 1 = 2 ^ c + 0 := by omega
  rw [hval1] at h1
  have h2 := z3l b c 0 l (by omega) (Or.inr rfl)
  exact zSt h1 h2
lemma z3n (b c : Nat) (l : zB) (hc : 1 <= c) :
    (z18 ((ld0 ^ c) +> ld1 +> [1,0,1] +> ld1 +> (ld0 ^ b) +> l) (RC 2)) [z00]⊢*
    (z18 (LC (b + c + 3) 0 l) (RC ((2 ^ (b + 1) - 1) * 2 ^ (c + 2) + 3))) := by
  rw [z2E c ([1,0,1] +> ld1 +> (ld0 ^ b) +> l)]
  have hpc := z0h c
  have hbound : 0 + (2 ^ c - 1) < 2 ^ (1 + c) := by rw [Nat.add_comm 1 c,Nat.pow_succ]; omega
  have h1 := z2p (1 + c) 0 (2 ^ c - 1) 2 ([1,0,1] +> ld1 +> (ld0 ^ b) +> l) hbound
  have h0 : 0 + (2 ^ c - 1) = 2 ^ c - 1 := by omega
  have hval1 : 2 + (2 ^ c - 1) = 2 ^ c + 1 := by omega
  rw [h0,hval1] at h1
  have h2 := z3l b c 1 l (by omega) (Or.inl hc)
  exact zSt h1 h2
lemma z3o (a b : Nat) (l : zB) :
    [1,0,1,1] +> (([1,0] ^ b) +> (o1 ^ (1 + a)) +> l) =
    [1,0,1] +> ld1 +> (ld0 ^ b) +> (o1 ^ a) +> l := by
  have h1 : ([1,0,1,1] : zF) = [1,0,1] ++ [1] := rfl
  rw [h1,append_assoc,z2W]
lemma z3p (len b : Nat) (l : zB) :
    [1,0,1,1] +> (([1,0] ^ b) +> (o1 ^ (4 + len * 3)) +> l) =
    [1,0,1] +> ld1 +> (ld0 ^ b) +> (o1 ^ (len * 3 + 3)) +> l := by
  have hlen : 4 + len * 3 = 1 + (len * 3 + 3) := by omega
  rw [hlen]
  exact z3o (len * 3 + 3) b l
lemma z3q (b c e : Nat) (he : e <= 1) :
    (2 ^ (b + 1) - 1) * 2 ^ (c + 2) + (e * 2 + 1) < 2 ^ (b + c + 3 + 2) := by
  have hpb := z0h b
  have hpc := z0h c
  have hp1 : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
  have hp2 : 2 ^ (c + 2) = 2 ^ c * 4 := by rw [Nat.pow_add]
  have hp3 : 2 ^ (b + c + 3 + 2) = (2 ^ b * 2) * (2 ^ c * 4) * 4 := by
    have : b + c + 3 + 2 = (b + 1) + (c + 2) + 2 := by omega
    rw [this,Nat.pow_add,Nat.pow_add,hp1,hp2]
  rw [hp3,hp1,hp2]
  have hle : (2 ^ b * 2 - 1) * (2 ^ c * 4) + 4 <= (2 ^ b * 2) * (2 ^ c * 4) := by
    rw [Nat.sub_mul,Nat.one_mul]
    have : 4 <= (2 ^ b * 2) * (2 ^ c * 4) := by
      have : 2 * 4 <= (2 ^ b * 2) * (2 ^ c * 4) := Nat.mul_le_mul (by omega) (by omega)
      omega
    omega
  omega
lemma z3r (a q h k b c e : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) (he : e <= 1) :
    let s := a * 3 + 2 + q * 2 + (b + c + 3)
    (z18 (LC (b + c + 3) 0 (zDb (a * 2 + q) k l)) (RC ((2 ^ (b + 1) - 1) * 2 ^ (c + 2) + (e * 2 + 1)))) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 ^ (c + 2) + (e * 2 + 1)) * (1 + h) + h))) := by
  intro s
  have hv : 0 < 2 ^ (b + c + 3) := z0h (b + c + 3)
  have hvr : 0 + ((2 ^ (b + 1) - 1) * 2 ^ (c + 2) + (e * 2 + 1)) < 2 ^ (b + c + 3 + 2) := by
    simpa using z3q b c e he
  have h1 := z31 a q h k (b + c + 3) 0 ((2 ^ (b + 1) - 1) * 2 ^ (c + 2) + (e * 2 + 1)) l
    hqh hL hk hv hvr
  simp only [Nat.zero_add] at h1
  exact h1
lemma z3s (a q h k b c : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let s := a * 3 + 2 + q * 2 + (b + (1 + c) + 3)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (4 + b * 2)) +> z +> (o1 ^ (4 + c * 2)) +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 ^ (1 + c + 2) + 1) * (1 + h) + h))) := by
  intro s
  have h1 := z1j b c ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  rw [z3p (a * 2 + q) b (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  rw [hdb] at h1
  have h2 := z3m b (1 + c) (zDb (a * 2 + q) k l)
  rw [<- z2K] at h2
  have h3 := z3r a q h k b (1 + c) 0 l hqh hL hk (by omega)
  exact zSt h1 (zSt h2 h3)
lemma z3t (a q h k b c : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let s := a * 3 + 2 + q * 2 + (b + (1 + c) + 3)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (4 + b * 2)) +> z +> (o1 ^ (5 + c * 2)) +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 ^ (1 + c + 2) + 3) * (1 + h) + h))) := by
  intro s
  have h1 := z1k b c ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  rw [z3p (a * 2 + q) b (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  rw [hdb,z2I] at h1
  have h2 := z3n b (1 + c) (zDb (a * 2 + q) k l) (by omega)
  have h3 := z3r a q h k b (1 + c) 1 l hqh hL hk (by omega)
  exact zSt h1 (zSt h2 h3)
lemma z3u (l : zB) : ld0 +> l = LC 1 1 l := by
  unfold LC; rfl
lemma z3v (l : zB) : ld1 +> l = LC 1 0 l := by
  unfold LC; rfl
lemma z3w (a q h k b : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let s := a * 3 + 2 + q * 2 + (b + 0 + 3)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (4 + b * 2)) +> z +> [1,1] +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 4 + 1) * (1 + h) + h))) := by
  intro s
  have h1 := z1m b ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  have hr : (o1 ^ (4 + b * 2)) +> [0,0,0,1,1] +> (default : zB) =
      (o1 ^ (4 + b * 2)) +> z +> [1,1] +> default := rfl
  rw [hr,z3p (a * 2 + q) b (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  rw [hdb] at h1
  have h2 := z2p 1 0 1 0 ([1,0,1] +> ld1 +> (ld0 ^ b) +> zDb (a * 2 + q) k l) (by decide +kernel)
  rw [<- z3u,<- z2K] at h2
  have h3 := z3l b 0 0 (zDb (a * 2 + q) k l) (by omega) (Or.inr rfl)
  have h4 := z3r a q h k b 0 0 l hqh hL hk (by omega)
  exact zSt h1 (zSt h2 (zSt h3 h4))
lemma z3x (b : Nat) (l : zB) (hb : 1 <= b) :
    (z18 (LC 1 0 ([1,0,1] +> ld1 +> (ld0 ^ b) +> l)) (RC 2)) [z00]⊢*
    (z18 (LC (b + 3) 0 l) (RC ((2 ^ (b + 1) - 1) * 4 + 3))) := by
  have hld1 : [1,0,1] +> ld1 +> (ld0 ^ b) +> l = [1,0,1] +> (ld1 ^ 1) +> (ld0 ^ b) +> l := rfl
  rw [hld1,z36 b 1 l]
  have hpb : 2 <= 2 ^ b := by
    have := z1T hb
    simpa using this
  have hk : (2 ^ b - 1) * 2 ^ 1 < 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
  have hsum : 2 ^ 3 <= (((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * 2 ^ 1 - 1) + (2 * 2 + 2) := by omega
  have h1 := z3k (b + 1) ((2 ^ b - 1) * 2 ^ 1) 1 3 2 l hk (by omega) (by decide +kernel) hsum
  have hlen : b + 1 + 1 + 1 = b + 3 := by omega
  have hval : ((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * 2 ^ 1 - 1 + 2 * 2 + 2 = (2 ^ (b + 1) - 1) * 4 + 3 := by
    rw [Nat.pow_succ]; omega
  rw [hlen,hval] at h1
  exact h1
lemma z3y (a q h k b : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) (hb : 1 <= b) :
    let s := a * 3 + 2 + q * 2 + (b + 0 + 3)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (4 + b * 2)) +> z +> [1,1,1] +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 4 + 3) * (1 + h) + h))) := by
  intro s
  have h1 := z1G b ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  have hr : (o1 ^ (4 + b * 2)) +> [0,0,0,1,1,1] +> (default : zB) =
      (o1 ^ (4 + b * 2)) +> z +> [1,1,1] +> default := rfl
  rw [hr,z3p (a * 2 + q) b (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  rw [hdb,z2I] at h1
  have h2 := z3x b (zDb (a * 2 + q) k l) hb
  rw [<- z3v] at h2
  have h3 := z3r a q h k b 0 1 l hqh hL hk (by omega)
  exact zSt h1 (zSt h2 h3)
lemma z3z (n k : Nat) (l : zB) :
    ld1 +> LC n k l = LC (n + 1) (k * 2) l := by
  unfold LC
  exact (z0l ld0 ld1 n k l).symm
lemma z3A (n k r : Nat) (hn : 1 <= n) (hk : k < 2 ^ n) (hr : r <= 4) :
    k + r < 2 ^ (n + 2) := by
  have hp : 2 <= 2 ^ n := by
    have := z1T hn
    simpa using this
  rw [Nat.pow_add 2 n 2]
  omega
lemma z3B (a q h k b c : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let n := b + 1 + (1 + c)
    let s := a * 3 + 2 + q * 2 + (n + 1 + 1)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (3 + b * 2)) +> z +> (o1 ^ (1 + c * 2)) +> z +> d +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 ^ (1 + c + 2) - 1) * (1 + h) + h))) := by
  intro n s
  have h1 := z1A b c ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  rw [z2X (a * 2 + q) b (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  rw [hdb,z2Y b (1 + c) (zDb (a * 2 + q) k l)] at h1
  let v := (2 ^ (b + 1) - 1) * 2 ^ (1 + c) - 1
  have hv : v < 2 ^ n := z2Z b (1 + c)
  have hld0 : ld0 +> ld1 +> LC n v (zDb (a * 2 + q) k l) =
      (ld0 ^ 1) +> ld1 +> LC n v (zDb (a * 2 + q) k l) := rfl
  rw [hld0,z2w n v 1 (zDb (a * 2 + q) k l),z2I] at h1
  have hv2 := z2x n v 1 hv
  have hvr := z3A (n + 1 + 1) ((v * 2 + 1) * 2 ^ 1 - 1) 2 (by omega) hv2 (by omega)
  have h2 := z31 a q h k (n + 1 + 1) ((v * 2 + 1) * 2 ^ 1 - 1) 2 l hqh hL hk hv2 hvr
  have hval : (v * 2 + 1) * 2 ^ 1 - 1 + 2 = (2 ^ (b + 1) - 1) * 2 ^ (1 + c + 2) - 1 := by
    have hpb := z0h b
    have hpc := z0h (1 + c)
    have hpos1 : 2 <= 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
    have hpos2 : 1 <= (2 ^ (b + 1) - 1) * 2 ^ (1 + c) := Nat.mul_pos (by omega) hpc
    have hp_c2 : 2 ^ (1 + c + 2) = 2 ^ (1 + c) * 4 := by rw [Nat.pow_add]
    rw [hp_c2,<- Nat.mul_assoc]
    dsimp [v]
    omega
  rw [hval] at h2
  exact zSt h1 h2
lemma z3C (a q h k b c : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let n := b + 1 + (1 + c)
    let s := a * 3 + 2 + q * 2 + (n + 1)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (3 + b * 2)) +> z +> (o1 ^ (2 + c * 2)) +> z +> d +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 ^ (1 + c + 1) + 2) * (1 + h) + h))) := by
  intro n s
  have h1 := z1B b c ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  rw [z2X (a * 2 + q) b (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  rw [hdb,z2Y b (1 + c) (zDb (a * 2 + q) k l),z3z,z2J] at h1
  let v := (2 ^ (b + 1) - 1) * 2 ^ (1 + c) - 1
  have hv : v < 2 ^ n := z2Z b (1 + c)
  have hv2 : v * 2 < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
  have hvr := z3A (n + 1) (v * 2) 4 (by omega) hv2 (by omega)
  have h2 := z31 a q h k (n + 1) (v * 2) 4 l hqh hL hk hv2 hvr
  have hval : v * 2 + 4 = (2 ^ (b + 1) - 1) * 2 ^ (1 + c + 1) + 2 := by
    have hpb := z0h b
    have hpc := z0h (1 + c)
    have hpos1 : 2 <= 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
    have hpos2 : 1 <= (2 ^ (b + 1) - 1) * 2 ^ (1 + c) := Nat.mul_pos (by omega) hpc
    rw [Nat.pow_succ 2 (1 + c),<- Nat.mul_assoc]
    dsimp [v]
    omega
  rw [hval] at h2
  exact zSt h1 h2
lemma z3D (c : Nat) (l : zB) :
    ld0 +> ld1 +> (ld0 ^ c) +> ld1 +> l = LC (c + 3) ((2 ^ c - 1) * 4 + 1) l := by
  have hld0 : ld0 +> ld1 +> (ld0 ^ c) +> ld1 +> l = (ld0 ^ 1) +> ld1 +> ((ld0 ^ c) +> ld1 +> l) := rfl
  rw [hld0,z2E c l,z2w (1 + c) (2 ^ c - 1) 1 l]
  have h1 : 1 + c + 1 + 1 = c + 3 := by omega
  have hpc := z0h c
  have h2 : ((2 ^ c - 1) * 2 + 1) * 2 ^ 1 - 1 = (2 ^ c - 1) * 4 + 1 := by omega
  rw [h1,h2]
lemma z3E (c : Nat) (l : zB) :
    ld1 +> (ld0 ^ c) +> ld1 +> l = LC (c + 2) ((2 ^ c - 1) * 2) l := by
  rw [z2E c l,z3z (1 + c) (2 ^ c - 1) l]
  have h1 : 1 + c + 1 = c + 2 := by omega
  rw [h1]
lemma z3F (b c : Nat) (l : zB) :
    (z18 (LC (c + 3) 0 ([1,0,1] +> ld1 +> (ld0 ^ b) +> l)) (RC (2 ^ (c + 2) - 1))) [z00]⊢*
    (z18 (LC (b + c + 5) 0 l) (RC ((2 ^ (b + 1) - 1) * 2 ^ (c + 4) - 1))) := by
  have hld1 : [1,0,1] +> ld1 +> (ld0 ^ b) +> l = [1,0,1] +> (ld1 ^ 1) +> (ld0 ^ b) +> l := rfl
  rw [hld1,z36 b 1 l]
  have hpb := z0h b
  have hpc := z0h c
  have hk : (2 ^ b - 1) * 2 ^ 1 < 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
  have hv : (2 ^ (c + 2) - 1) * 2 + 1 < 2 ^ (c + 3) := by
    have hp2 : 2 ^ (c + 2) = 2 ^ c * 4 := by rw [Nat.pow_add]
    have hp3 : 2 ^ (c + 3) = 2 ^ c * 8 := by rw [Nat.pow_add]
    rw [hp2,hp3]; omega
  have hsum : 2 ^ (c + 3) <= (((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * 2 ^ (c + 3) - 1) + ((2 ^ (c + 2) - 1) * 2 + 2) := by
    have hp := z0h (c + 3)
    have hp2 := z0h (c + 2)
    have h1 : 1 * 2 ^ (c + 3) <= ((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * 2 ^ (c + 3) :=
      Nat.mul_le_mul_right (2 ^ (c + 3)) (by omega)
    omega
  have h1 := z3k (b + 1) ((2 ^ b - 1) * 2 ^ 1) (c + 3) (c + 3) (2 ^ (c + 2) - 1) l
    hk (by omega) hv hsum
  have hlen : b + 1 + 1 + (c + 3) = b + c + 5 := by omega
  have hval : ((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * 2 ^ (c + 3) - 1 + (2 ^ (c + 2) - 1) * 2 + 2 =
      (2 ^ (b + 1) - 1) * 2 ^ (c + 4) - 1 := by
    have hp_c3 : 2 ^ (c + 3) = 2 ^ c * 8 := by rw [Nat.pow_add]
    have hp_c4 : 2 ^ (c + 4) = 2 ^ c * 16 := by rw [Nat.pow_add]
    have hp_c2 : 2 ^ (c + 2) = 2 ^ c * 4 := by rw [Nat.pow_add]
    have hp_b1 : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
    rw [hp_c3,hp_c4,hp_c2,hp_b1]
    have hsub1 : (2 ^ b - 1) * 2 ^ 1 * 2 + 1 = 2 ^ b * 4 - 3 := by omega
    have hmul1 : (2 ^ b * 4) * (2 ^ c * 8) = (2 ^ b * 2 ^ c) * 32 := by ring
    have hmul2 : (2 ^ b * 2) * (2 ^ c * 16) = (2 ^ b * 2 ^ c) * 32 := by ring
    have hbc : 2 ^ c <= 2 ^ b * 2 ^ c := Nat.le_mul_of_pos_left _ hpb
    rw [hsub1,Nat.sub_mul,Nat.sub_mul,Nat.sub_mul,hmul1,hmul2]
    omega
  rw [hlen,hval] at h1
  exact h1
lemma z3G (b c : Nat) (l : zB) (hb : 1 <= b) :
    (z18 (LC (c + 2) 0 ([1,0,1] +> ld1 +> (ld0 ^ b) +> l)) (RC (2 ^ (c + 1) + 2))) [z00]⊢*
    (z18 (LC (b + c + 4) 0 l) (RC ((2 ^ (b + 1) - 1) * 2 ^ (c + 3) + 5))) := by
  have hld1 : [1,0,1] +> ld1 +> (ld0 ^ b) +> l = [1,0,1] +> (ld1 ^ 1) +> (ld0 ^ b) +> l := rfl
  rw [hld1,z36 b 1 l]
  have hpb : 2 <= 2 ^ b := by
    have := z1T hb
    simpa using this
  have hpc := z0h c
  have hk : (2 ^ b - 1) * 2 ^ 1 < 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
  have hv : (2 ^ (c + 1) + 2) * 2 + 1 < 2 ^ (c + 4) := by
    have hp4 : 2 ^ (c + 4) = 2 ^ c * 16 := by rw [Nat.pow_add]
    have hp1 : 2 ^ (c + 1) = 2 ^ c * 2 := by rw [Nat.pow_add]
    rw [hp4,hp1]; omega
  have hsum : 2 ^ (c + 4) <= (((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * 2 ^ (c + 2) - 1) + ((2 ^ (c + 1) + 2) * 2 + 2) := by
    have hp4 : 2 ^ (c + 4) = 2 ^ c * 16 := by rw [Nat.pow_add]
    have hp2 : 2 ^ (c + 2) = 2 ^ c * 4 := by rw [Nat.pow_add]
    have hp1 : 2 ^ (c + 1) = 2 ^ c * 2 := by rw [Nat.pow_add]
    rw [hp4,hp2,hp1]
    have h1 : 5 * (2 ^ c * 4) <= ((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * (2 ^ c * 4) :=
      Nat.mul_le_mul_right (2 ^ c * 4) (by omega)
    omega
  have h1 := z3k (b + 1) ((2 ^ b - 1) * 2 ^ 1) (c + 2) (c + 4) (2 ^ (c + 1) + 2) l
    hk (by omega) hv hsum
  have hlen : b + 1 + 1 + (c + 2) = b + c + 4 := by omega
  have hval : ((2 ^ b - 1) * 2 ^ 1 * 2 + 1) * 2 ^ (c + 2) - 1 + (2 ^ (c + 1) + 2) * 2 + 2 =
      (2 ^ (b + 1) - 1) * 2 ^ (c + 3) + 5 := by
    have hp_c2 : 2 ^ (c + 2) = 2 ^ c * 4 := by rw [Nat.pow_add]
    have hp_c3 : 2 ^ (c + 3) = 2 ^ c * 8 := by rw [Nat.pow_add]
    have hp_c1 : 2 ^ (c + 1) = 2 ^ c * 2 := by rw [Nat.pow_add]
    have hp_b1 : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
    rw [hp_c2,hp_c3,hp_c1,hp_b1]
    have hsub1 : (2 ^ b - 1) * 2 ^ 1 * 2 + 1 = 2 ^ b * 4 - 3 := by omega
    have hmul1 : (2 ^ b * 4) * (2 ^ c * 4) = (2 ^ b * 2 ^ c) * 16 := by ring
    have hmul2 : (2 ^ b * 2) * (2 ^ c * 8) = (2 ^ b * 2 ^ c) * 16 := by ring
    have hbc : 2 ^ c <= 2 ^ b * 2 ^ c := Nat.le_mul_of_pos_left _ (by omega)
    rw [hsub1,Nat.sub_mul,Nat.sub_mul,hmul1,hmul2]
    omega
  rw [hlen,hval] at h1
  exact h1
lemma z3H (a q h k b c : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) :
    let s := a * 3 + 2 + q * 2 + (b + c + 5)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (4 + b * 2)) +> z +> (o1 ^ (3 + c * 2)) +> z +> d +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 ^ (c + 4) - 1) * (1 + h) + h))) := by
  intro s
  have h1 := z1C b c ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  rw [z3p (a * 2 + q) b (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  rw [hdb,z3D c ([1,0,1] +> ld1 +> (ld0 ^ b) +> zDb (a * 2 + q) k l),z2I] at h1
  have hpc := z0h c
  have hbound : 0 + ((2 ^ c - 1) * 4 + 1) < 2 ^ (c + 3) := by
    have : 2 ^ (c + 3) = 2 ^ c * 8 := by rw [Nat.pow_add]
    rw [this]; omega
  have h2 := z2p (c + 3) 0 ((2 ^ c - 1) * 4 + 1) 2 ([1,0,1] +> ld1 +> (ld0 ^ b) +> zDb (a * 2 + q) k l) hbound
  have h0 : 0 + ((2 ^ c - 1) * 4 + 1) = (2 ^ c - 1) * 4 + 1 := by omega
  have hval1 : 2 + ((2 ^ c - 1) * 4 + 1) = 2 ^ (c + 2) - 1 := by
    have : 2 ^ (c + 2) = 2 ^ c * 4 := by rw [Nat.pow_add]
    rw [this]; omega
  rw [h0,hval1] at h2
  have h3 := z3F b c (zDb (a * 2 + q) k l)
  have hv : 0 < 2 ^ (b + c + 5) := z0h (b + c + 5)
  have hvr : 0 + ((2 ^ (b + 1) - 1) * 2 ^ (c + 4) - 1) < 2 ^ (b + c + 5 + 2) := by
    have hpb := z0h b
    have hp1 : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
    have hp2 : 2 ^ (c + 4) = 2 ^ c * 16 := by rw [Nat.pow_add]
    have hp3 : 2 ^ (b + c + 5 + 2) = (2 ^ b * 2) * (2 ^ c * 16) * 4 := by
      have : b + c + 5 + 2 = (b + 1) + (c + 4) + 2 := by omega
      rw [this,Nat.pow_add,Nat.pow_add,hp1,hp2]
    rw [hp3,hp1,hp2]
    have hpos : 0 < (2 ^ b * 2) * (2 ^ c * 16) := Nat.mul_pos (by omega) (by omega)
    have hle : (2 ^ b * 2 - 1) * (2 ^ c * 16) <= (2 ^ b * 2) * (2 ^ c * 16) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h4 := z31 a q h k (b + c + 5) 0 ((2 ^ (b + 1) - 1) * 2 ^ (c + 4) - 1) l hqh hL hk hv hvr
  simp only [Nat.zero_add] at h4
  exact zSt h1 (zSt h2 (zSt h3 h4))
lemma z3I (a q h k b c : Nat) (l : zB)
    (hqh : q + h = 1) (hL : 0 < a * 2 + q) (hk : k < 2 ^ (a * 2 + q)) (hb : 1 <= b) :
    let s := a * 3 + 2 + q * 2 + (b + c + 4)
    (((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l) {{D}}>
      ((o1 ^ (4 + b * 2)) +> z +> (o1 ^ (4 + c * 2)) +> z +> d +> default)) [z00]⊢*
    (z18 (LC (a * 2 + q + s) 0 l)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 ^ (c + 3) + 5) * (1 + h) + h))) := by
  intro s
  have h1 := z1D b c ((o1 ^ (4 + (a * 2 + q) * 3)) +> ld0 +> LC (a * 2 + q) k l)
  rw [z3p (a * 2 + q) b (ld0 +> LC (a * 2 + q) k l)] at h1
  have hdb : (o1 ^ ((a * 2 + q) * 3 + 3)) +> ld0 +> LC (a * 2 + q) k l = zDb (a * 2 + q) k l := rfl
  rw [hdb,z3E c ([1,0,1] +> ld1 +> (ld0 ^ b) +> zDb (a * 2 + q) k l),z2J] at h1
  have hpc := z0h c
  have hbound : 0 + (2 ^ c - 1) * 2 < 2 ^ (c + 2) := by
    have : 2 ^ (c + 2) = 2 ^ c * 4 := by rw [Nat.pow_add]
    rw [this]; omega
  have h2 := z2p (c + 2) 0 ((2 ^ c - 1) * 2) 4 ([1,0,1] +> ld1 +> (ld0 ^ b) +> zDb (a * 2 + q) k l) hbound
  have h0 : 0 + (2 ^ c - 1) * 2 = (2 ^ c - 1) * 2 := by omega
  have hval1 : 4 + (2 ^ c - 1) * 2 = 2 ^ (c + 1) + 2 := by
    have : 2 ^ (c + 1) = 2 ^ c * 2 := by rw [Nat.pow_add]
    rw [this]; omega
  rw [h0,hval1] at h2
  have h3 := z3G b c (zDb (a * 2 + q) k l) hb
  have hv : 0 < 2 ^ (b + c + 4) := z0h (b + c + 4)
  have hvr : 0 + ((2 ^ (b + 1) - 1) * 2 ^ (c + 3) + 5) < 2 ^ (b + c + 4 + 2) := by
    have hpb := z0h b
    have hp1 : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
    have hp2 : 2 ^ (c + 3) = 2 ^ c * 8 := by rw [Nat.pow_add]
    have hp3 : 2 ^ (b + c + 4 + 2) = (2 ^ b * 2) * (2 ^ c * 8) * 4 := by
      have : b + c + 4 + 2 = (b + 1) + (c + 3) + 2 := by omega
      rw [this,Nat.pow_add,Nat.pow_add,hp1,hp2]
    rw [hp3,hp1,hp2]
    have hle : (2 ^ b * 2 - 1) * (2 ^ c * 8) + 8 <= (2 ^ b * 2) * (2 ^ c * 8) := by
      rw [Nat.sub_mul,Nat.one_mul]
      have : 8 <= (2 ^ b * 2) * (2 ^ c * 8) := by
        have : 2 * 8 <= (2 ^ b * 2) * (2 ^ c * 8) := Nat.mul_le_mul (by omega) (by omega)
        omega
      omega
    omega
  have h4 := z31 a q h k (b + c + 4) 0 ((2 ^ (b + 1) - 1) * 2 ^ (c + 3) + 5) l hqh hL hk hv hvr
  simp only [Nat.zero_add] at h4
  exact zSt h1 (zSt h2 (zSt h3 h4))
namespace Queue
abbrev cell := Nat × Nat
def danger : cell := (0,1)
def main (p : cell) : Prop := 3 <= p.1 /\ p.1 * 8 + 9 <= p.2
def allowed (p : cell) : Prop := 0 < p.2 /\ (p.1 = 0 \/ z1P p.1 p.2)
def link (p : cell) (l : List cell) : Prop :=
  p = danger -> match l with | [] => True | q :: _ => main q
inductive good : List cell -> Prop
  | nil : good []
  | cons (p : cell) (l : List cell) : allowed p -> link p l -> good l -> good (p :: l)
lemma z3J (p : cell) (h : main p) : allowed p /\ p ≠ danger := by
  rcases p with ⟨t,u⟩
  rcases h with ⟨ht,hu⟩
  refine ⟨⟨by omega,Or.inr (Or.inl hu)⟩,?_⟩
  intro heq
  injection heq with ht0 hu1
  omega
lemma z3K {p : cell} {l : List cell} (h : good (p :: l)) : good l := by
  cases h with
  | cons _ _ _ _ hl => exact hl
lemma z3L (l : List cell) (p : cell) (r : List cell)
    (hl : good l) (hp : main p) (hr : good r) : good (l ++ p :: r) := by
  rcases z3J p hp with ⟨ha,hne⟩
  induction hl with
  | nil =>
    refine good.cons p r ha ?_ hr
    intro heq
    exact False.elim (hne heq)
  | cons q l hq hlink _ ih =>
    refine good.cons q (l ++ p :: r) hq ?_ ih
    intro heq
    have hm := hlink heq
    cases l with
    | nil => exact hp
    | cons q' l' => exact hm
def weight (p : cell) : Nat := p.1 + p.2 + 1
def mass : List cell -> Nat
  | [] => 0
  | p :: r => weight p + mass r
lemma mass_app (l r : List cell) : mass (l ++ r) = mass l + mass r := by
  induction l with
  | nil => simp [mass]
  | cons p l ih => simp only [List.cons_append,mass,ih]; omega
lemma length_mass (l : List cell) : l.length <= mass l := by
  induction l with
  | nil => simp [mass]
  | cons p l ih => simp only [List.length_cons,mass,weight]; omega
lemma z3M : ∀ (n : Nat) (l : List cell),mass (l.drop n) <= mass l
  | 0,_ => by simp
  | _ + 1,[] => by simp [mass]
  | n + 1,p :: l => by
    simp only [List.drop_succ_cons,mass]
    have := z3M n l
    omega
lemma z3N : ∀ (n : Nat) (l : List cell),n < l.length -> mass (l.take n) < mass l
  | _,[],h => by simp at h
  | 0,p :: l,_ => by
    simp only [List.take_zero,mass,weight]
    omega
  | n + 1,p :: l,h => by
    simp only [List.length_cons] at h
    simp only [List.take_succ_cons,mass]
    have := z3N n l (by omega)
    omega
inductive cut : List cell -> List cell -> Nat -> Nat -> Prop
  | one (p : cell) (l : List cell) : allowed p -> p ≠ danger -> cut (p :: l) l (weight p) 1
  | two (p : cell) (l : List cell) : main p -> cut (danger :: p :: l) l (2 + weight p) 2
lemma z3O (l : List cell) (hl : good l) (hlen : 2 <= l.length) :
    ∃ r n k,cut l r n k := by
  cases hl with
  | nil => simp at hlen
  | cons p l ha hlink hgood =>
    by_cases hd : p = danger
    · subst hd
      cases l with
      | nil => simp at hlen
      | cons q l' =>
        have hmain : main q := hlink rfl
        exact ⟨l',2 + weight q,2,cut.two q l' hmain⟩
    · exact ⟨l,weight p,1,cut.one p l ha hd⟩
lemma z3P {l r : List cell} {n k : Nat} (hl : good l) (hc : cut l r n k) : good r := by
  cases hc with
  | one _ _ _ _ => exact z3K hl
  | two _ _ _ => exact z3K (z3K hl)
lemma z3Q {l r : List cell} {n k : Nat} (hc : cut l r n k) :
    1 <= k /\ k <= 2 /\ r = l.drop k /\ n = mass (l.take k) := by
  cases hc with
  | one p l _ _ =>
    simp [mass]
  | two p l _ =>
    simp [mass,danger,weight]
def advance (l r : List cell) : Prop :=
  ∃ k a,k <= 2 /\ r = l.drop k ++ a
inductive path : Nat -> List cell -> List cell -> Prop
  | zero (l : List cell) : path 0 l l
  | next (n : Nat) (l r s : List cell) : path n l r -> advance r s -> path (n + 1) l s
lemma z3R : ∀ (n k : Nat) (l r a : List cell),n + k <= l.length ->
    (l.drop n ++ r).drop k ++ a = l.drop (n + k) ++ (r ++ a)
  | 0,k,l,r,a,h => by
    simp only [Nat.zero_add,List.drop_zero] at h ⊢
    induction k generalizing l with
    | zero => simp [List.append_assoc]
    | succ k ih =>
      cases l with
      | nil => simp at h
      | cons p l =>
        simp only [List.length_cons] at h
        simp only [List.cons_append,List.drop_succ_cons]
        exact ih l (by omega)
  | n + 1,k,[],r,a,h => by simp at h
  | n + 1,k,p :: l,r,a,h => by
    simp only [List.length_cons] at h
    simp only [List.drop_succ_cons,Nat.succ_add]
    exact z3R n k l r a (by omega)
lemma z3S : ∀ (k : Nat) (l1 l2 : List cell),k <= l1.length ->
    (l1 ++ l2).take k = l1.take k
  | 0,_,_,_ => by simp
  | k + 1,[],_,h => by simp at h
  | k + 1,p :: l1,l2,h => by
    simp only [List.length_cons] at h
    simp only [List.cons_append,List.take_succ_cons]
    rw [z3S k l1 l2 (by omega)]
lemma z3T {n : Nat} {l r : List cell} (hp : path n l r) (hlen : n * 2 <= l.length) :
    ∃ k a,k <= n * 2 /\ r = l.drop k ++ a := by
  induction hp with
  | zero l =>
    exact ⟨0,[],by omega,by simp⟩
  | next n l r s hp ha ih =>
    rcases ih (by omega) with ⟨k,a,hk,hr⟩
    rcases ha with ⟨j,b,hj,hs⟩
    refine ⟨k + j,a ++ b,by omega,?_⟩
    rw [hs,hr,z3R k j l a b (by omega)]
lemma z3U {l r s : List cell} {n k : Nat}
    (hp : path 3 l r) (hlen : 9 <= l.length) (hc : cut r s n k) :
    n < mass l := by
  rcases z3T hp (by omega) with ⟨d,a,hd,hr⟩
  rcases z3Q hc with ⟨hk1,hk2,_,hn⟩
  have hlen_drop : (l.drop d).length = l.length - d := List.length_drop
  have hshort : k < (l.drop d).length := by omega
  rw [hn,hr,z3S k (l.drop d) a (by omega)]
  have h1 := z3N k (l.drop d) hshort
  have h2 := z3M d l
  omega
lemma z3V (a b c d : Nat)
    (h1 : a * 5 <= b * 2) (h2 : b * 5 <= c * 2) (h3 : c * 5 <= d * 2) :
    a * 125 <= d * 8 := by
  omega
lemma z3W {l r : List cell} {n k : Nat} {p : cell} {a : List cell}
    (hl : good l) (hc : cut l r n k) (hp : main p) (ha : good a) (hsize : k <= 1 + a.length) :
    good (r ++ p :: a) /\ l.length <= (r ++ p :: a).length := by
  refine ⟨z3L r p a (z3P hl hc) hp ha,?_⟩
  cases hc with
  | one q r' _ _ =>
    simp only [List.length_append,List.length_cons]
    omega
  | two q r' _ =>
    simp only [List.length_append,List.length_cons]
    omega
lemma z3X {l r : List cell} {n k : Nat} (hc : cut l r n k) : 3 <= n := by
  cases hc with
  | one p l ha hne =>
    rcases p with ⟨t,u⟩
    rcases ha with ⟨hu,ht | hsep⟩
    · subst ht
      have hu2 : 2 <= u := by
        rcases u with _ | _ | u
        · omega
        · exfalso; exact hne rfl
        · omega
      simp only [weight]; omega
    · rcases hsep with h1 | h2 <;> (simp only [weight]; omega)
  | two p l hp =>
    rcases p with ⟨t,u⟩
    rcases hp with ⟨ht,hu⟩
    simp only [weight]; omega
structure frame where
  cells : List cell
  trailing : Nat
def width (f : frame) : Nat := mass f.cells + f.trailing - 1
def edge (f g : frame) : Prop :=
  advance f.cells g.cells /\ width f * 5 <= width g * 2 /\ f.cells.length <= g.cells.length
structure history (f0 f1 f2 f3 : frame) : Prop where
  edge01 : edge f0 f1
  edge12 : edge f1 f2
  edge23 : edge f2 f3
  old_width : 16 <= width f0
  old_count : 9 <= f0.cells.length
  tail_bound : f3.trailing <= width f0 + 8
  current_good : good f3.cells
def z3Y (f g : frame) : Prop :=
  ∃ r n k gap a,
    cut f.cells r n k /\
    g.cells = r ++ (n + f.trailing,gap) :: a /\
    good a /\
    k <= 1 + a.length /\
    width f * 5 <= width g * 2 /\
    width f * 3 <= gap * 2 + 4 /\
    g.trailing <= n + 8
lemma z3Z (f : frame) : mass f.cells <= width f + 1 := by
  unfold width; omega
lemma z40 {f0 f1 f2 f3 : frame} (h : history f0 f1 f2 f3) :
    path 3 f0.cells f3.cells := by
  have h0 : path 0 f0.cells f0.cells := path.zero f0.cells
  have h1 : path 1 f0.cells f1.cells := path.next 0 f0.cells f0.cells f1.cells h0 h.edge01.1
  have h2 : path 2 f0.cells f2.cells := path.next 1 f0.cells f1.cells f2.cells h1 h.edge12.1
  exact path.next 2 f0.cells f2.cells f3.cells h2 h.edge23.1
lemma z41 {f0 f1 f2 f3 : frame} {r : List cell} {n k : Nat}
    (h : history f0 f1 f2 f3) (hc : cut f3.cells r n k) :
    n <= width f0 := by
  have hlt := z3U (z40 h) h.old_count hc
  have hm := z3Z f0
  omega
theorem history_next {f0 f1 f2 f3 f4 : frame}
    (h : history f0 f1 f2 f3) (hem : z3Y f3 f4) :
    history f1 f2 f3 f4 := by
  rcases hem with ⟨r,n,k,gap,a,hcut,hcells,ha,hsize,hg,hgap,htail⟩
  have hprefix := z41 h hcut
  have hmain : main (n + f3.trailing,gap) := by
    refine ⟨?_,?_⟩
    · have := z3X hcut; dsimp; omega
    · dsimp
      apply z1Q (width f0) (width f3) n f3.trailing gap
        h.old_width
        (z3V (width f0) (width f1) (width f2) (width f3) h.edge01.2.1 h.edge12.2.1 h.edge23.2.1)
        hprefix h.tail_bound hgap
  rcases z3W h.current_good hcut hmain ha hsize with ⟨hgood4,hcount4⟩
  have hg4 : good f4.cells := by rw [hcells]; exact hgood4
  have hn4 : f3.cells.length <= f4.cells.length := by rw [hcells]; exact hcount4
  rcases z3Q hcut with ⟨hk1,hk2,hr,_⟩
  have hadv : advance f3.cells f4.cells := ⟨k,(n + f3.trailing,gap) :: a,hk2,by rw [hcells,hr]⟩
  have hw0 := h.old_width
  have hc0 := h.old_count
  have he01_w := h.edge01.2.1
  have he01_c := h.edge01.2.2
  exact {
    edge01 := h.edge12
    edge12 := h.edge23
    edge23 := ⟨hadv,hg,hn4⟩
    old_width := by omega
    old_count := by omega
    tail_bound := by omega
    current_good := hg4
  }
lemma history_ready {f0 f1 f2 f3 : frame} (h : history f0 f1 f2 f3) :
    good f3.cells /\ 9 <= f3.cells.length := by
  have hc0 := h.old_count
  have c01 := h.edge01.2.2
  have c12 := h.edge12.2.2
  have c23 := h.edge23.2.2
  exact ⟨h.current_good,by omega⟩
def zSi (extra : Bool) (t u : Nat) : Prop :=
  if extra then main (t,u) else allowed (t,u) /\ (t,u) ≠ danger
inductive block : Bool -> Nat -> Nat -> Nat -> Nat -> List cell -> Nat -> Prop
  | zero2 (l q h : Nat) : q + h = 1 ->
      block false (l * 2 + q) 0 2 ((l + q) * 3 - 1) [] (1 + h)
  | zero3 (l q h : Nat) : q + h = 1 ->
      block false (l * 2 + q) 0 3 ((l + q) * 3 - 2) [danger] h
  | zero5 (l q h : Nat) : q + h = 1 ->
      block false (l * 2 + q) 0 5 ((l + q) * 3 - 1) [] (2 + h)
  | zero (l q h j p : Nat) : q + h = 1 -> p <= 1 -> 1 + p <= j ->
      block false (l * 2 + q) 0 (j * 2 + 2 + p) ((l + q) * 3 - 1) [(0,j - p)] (p + h)
  | short (L t u s e : Nat) : 0 < t -> (u = 1 \/ u = 2) -> e <= 1 -> L * 3 + t + 7 = s * 2 + e ->
      block false L t u (s - 1 - (e + u - 1)) [] (e + u - 1)
  | one_odd (l q h b : Nat) : q + h = 1 ->
      block false (l * 2 + q) 1 (b * 2 + 1) ((l + q) * 3) [] (b + 1 + h)
  | one_even (l q h j : Nat) : q + h = 1 ->
      block false (l * 2 + q) 1 (j * 2 + 2) ((l + q) * 3 - 1) [(0,j - 2),danger] h
  | full (l q h a b p e : Nat) : q + h = 1 -> p <= 1 -> e <= 1 -> 1 <= a -> 1 <= b -> a + p = e ->
      block false (l * 2 + q) (a * 2 + e) (b * 2 + 2 - p) ((l + q) * 3) [] (b + a + 1 + h)
  | split (l q h a b p e : Nat) : q + h = 1 -> p <= 1 -> e <= 1 -> 1 <= a -> 1 <= b -> e < a + p ->
      block false (l * 2 + q) (a * 2 + e) (b * 2 + 2 - p) ((l + q) * 3) [(b - 1,a + p - e)] (1 - p + e + h)
  | extra_odd (l q h a b p : Nat) : q + h = 1 -> p <= 1 ->
      block true (l * 2 + q) (a * 2 + 1) (b * 2 + 2 - p) ((l + q) * 3) [(b - 2,1)] (a + 3 + h)
  | extra_even_odd (l q h a b : Nat) : q + h = 1 ->
      block true (l * 2 + q) (a * 2) (b * 2 + 1) ((l + q) * 3) [(b - 1,a - 1),danger] h
  | extra_four (l q h b : Nat) : q + h = 1 ->
      block true (l * 2 + q) 4 (b * 2 + 2) ((l + q) * 3) [(b,1)] (1 + h)
  | extra_even_even (l q h a b : Nat) : q + h = 1 -> 3 <= a ->
      block true (l * 2 + q) (a * 2) (b * 2 + 2) ((l + q) * 3) [(b - 1,a - 2),danger] (1 + h)
lemma z42 {extra : Bool} {L t u gap : Nat} {a : List cell} {E : Nat}
    (hb : block extra L t u gap a E) (hL : 16 <= L) (hsafe : zSi extra t u) :
    0 < gap /\ L * 3 <= gap * 2 + 4 /\ L * 3 <= (gap + mass a + E + 1) * 2 /\
      E <= t + u + (if extra then 11 else 9) /\ (if extra then 1 else 0) <= a.length := by
  revert hL hsafe
  induction hb <;>
    intro hL hsafe <;>
    simp [zSi,main,allowed,z1P,mass,weight,danger] at hL hsafe ⊢ <;>
    omega
lemma z43 (t u : Nat) (hu : 0 < u) (hs : t = 0 \/ z1P t u) : good [(t,u)] := by
  refine good.cons (t,u) [] ⟨hu,hs⟩ (fun _ => trivial) good.nil
lemma z44 (t u : Nat) (hu : 0 < u) (hs : t = 0 \/ z1P t u) (hne : (t,u) ≠ danger) :
    good [(t,u),danger] := by
  refine good.cons (t,u) [danger] ⟨hu,hs⟩ (fun heq => False.elim (hne heq)) ?_
  exact z43 0 1 (by omega) (Or.inl rfl)
lemma z45 {extra : Bool} {L t u gap : Nat} {a : List cell} {E : Nat}
    (hb : block extra L t u gap a E) (hsafe : zSi extra t u) : good a := by
  revert hsafe
  induction hb with
  | zero2 _ _ _ _ => intro _; exact good.nil
  | zero3 _ _ _ _ => intro _; exact z43 0 1 (by omega) (Or.inl rfl)
  | zero5 _ _ _ _ => intro _; exact good.nil
  | zero l q h j p hqh hp hj =>
    intro _
    exact z43 0 (j - p) (by omega) (Or.inl rfl)
  | short _ _ _ _ _ _ _ _ _ => intro _; exact good.nil
  | one_odd _ _ _ _ _ => intro _; exact good.nil
  | one_even l q h j hqh =>
    intro hsafe
    simp [zSi,allowed,z1P,danger] at hsafe
    refine z44 0 (j - 2) (by omega) (Or.inl rfl) ?_
    intro heq
    injection heq with _ h2
    omega
  | full _ _ _ _ _ _ _ _ _ _ _ _ _ => intro _; exact good.nil
  | split l q h a b p e hqh hp he ha hb hlt =>
    intro hsafe
    simp [zSi,allowed,z1P,danger] at hsafe
    exact z43 (b - 1) (a + p - e) (by omega) (by unfold z1P at *; omega)
  | extra_odd l q h a b p hqh hp =>
    intro hsafe
    simp [zSi,main] at hsafe
    exact z43 (b - 2) 1 (by omega) (by unfold z1P; omega)
  | extra_even_odd l q h a b hqh =>
    intro hsafe
    simp [zSi,main] at hsafe
    refine z44 (b - 1) (a - 1) (by omega) (by unfold z1P; omega) ?_
    intro heq
    injection heq with h1 h2
    omega
  | extra_four l q h b hqh =>
    intro hsafe
    simp [zSi,main] at hsafe
    exact z43 b 1 (by omega) (by unfold z1P; omega)
  | extra_even_even l q h a b hqh ha =>
    intro hsafe
    simp [zSi,main] at hsafe
    refine z44 (b - 1) (a - 2) (by omega) (by unfold z1P; omega) ?_
    intro heq
    injection heq with h1 h2
    omega
lemma z46 {l r : List cell} {n k : Nat} (hc : cut l r n k) : mass l = n + mass r := by
  cases hc with
  | one p l _ _ => simp [mass]
  | two p l _ => simp [mass,danger,weight]; omega
lemma z47 (f : frame) (r : List cell) (n k gap : Nat) (a : List cell) (E : Nat)
    (hc : cut f.cells r n k) :
    width ⟨r ++ (n + f.trailing,gap) :: a,E⟩ = width f + gap + mass a + E + 1 := by
  have hm := z46 hc
  have hl := z3X hc
  simp only [width,mass_app,mass,weight]
  omega
lemma z48 (f : frame) (r : List cell) (n k : Nat) (extra : Bool) (t u gap : Nat)
    (a : List cell) (E : Nat)
    (hcut : cut f.cells r n k)
    (hn : n = t + u + (if extra then 3 else 1))
    (hk : k = (if extra then 2 else 1))
    (hL : 16 <= width f)
    (hsafe : zSi extra t u)
    (hb : block extra (width f) t u gap a E) :
    z3Y f ⟨r ++ (n + f.trailing,gap) :: a,E⟩ := by
  rcases z42 hb hL hsafe with ⟨hpos,hgap,hg,hE,hcount⟩
  refine ⟨r,n,k,gap,a,hcut,rfl,z45 hb hsafe,?_,?_,hgap,?_⟩
  · cases extra <;> (simp only [ Bool.false_eq_true,↓reduceIte] at hk hcount ⊢; omega)
  · rw [z47 f r n k gap a E hcut]
    omega
  · dsimp
    cases extra <;> (simp only [Bool.false_eq_true,↓reduceIte] at hn hE ⊢; omega)
lemma z49 (n : Nat) : ∃ a e,n = a * 2 + e /\ e <= 1 :=
  ⟨n / 2,n % 2,by omega,by omega⟩
lemma z4a (n : Nat) (hn : 0 < n) : ∃ b p,n = b * 2 + 2 - p /\ p <= 1 := by
  rcases z49 (n - 1) with ⟨b,e,he,hbit⟩
  exact ⟨b,1 - e,by omega,by omega⟩
lemma z4b (extra : Bool) (L t u : Nat) (hsafe : zSi extra t u) :
    ∃ gap a E,block extra L t u gap a E := by
  rcases z49 L with ⟨l,q,hL_eq,hq⟩
  subst hL_eq
  have hpad : q + (1 - q) = 1 := by omega
  cases extra with
  | true =>
    simp [zSi,main] at hsafe
    rcases z49 t with ⟨a,e,ht_eq,he⟩
    rcases z4a u (by omega) with ⟨b,p,hu_eq,hp⟩
    rcases e with _ | _ | e
    · have ht0 : t = a * 2 := by omega
      subst ht0
      rcases p with _ | _ | p
      · have hu0 : u = b * 2 + 2 := by omega
        subst hu0
        by_cases ha2 : a = 2
        · subst ha2
          exact ⟨(l + q) * 3,[(b,1)],1 + (1 - q),block.extra_four l q (1 - q) b hpad⟩
        · exact ⟨(l + q) * 3,[(b - 1,a - 2),danger],1 + (1 - q),
            block.extra_even_even l q (1 - q) a b hpad (by omega)⟩
      · have hu1 : u = b * 2 + 1 := by omega
        subst hu1
        exact ⟨(l + q) * 3,[(b - 1,a - 1),danger],1 - q,
          block.extra_even_odd l q (1 - q) a b hpad⟩
      · omega
    · have ht1 : t = a * 2 + 1 := by omega
      rw [ht1,hu_eq]
      exact ⟨(l + q) * 3,[(b - 2,1)],a + 3 + (1 - q),
        block.extra_odd l q (1 - q) a b p hpad hp⟩
    · omega
  | false =>
    simp [zSi,allowed,z1P,danger] at hsafe
    by_cases ht0 : t = 0
    · subst ht0
      simp at hsafe
      have hu2 : 2 <= u := by omega
      by_cases hu_eq2 : u = 2
      · subst hu_eq2
        exact ⟨(l + q) * 3 - 1,[],1 + (1 - q),block.zero2 l q (1 - q) hpad⟩
      · by_cases hu_eq3 : u = 3
        · subst hu_eq3
          exact ⟨(l + q) * 3 - 2,[danger],1 - q,block.zero3 l q (1 - q) hpad⟩
        · by_cases hu_eq5 : u = 5
          · subst hu_eq5
            exact ⟨(l + q) * 3 - 1,[],2 + (1 - q),block.zero5 l q (1 - q) hpad⟩
          · rcases z49 (u - 2) with ⟨j,p,hu_eq,hp⟩
            have hu_rw : u = j * 2 + 2 + p := by omega
            rw [hu_rw]
            exact ⟨(l + q) * 3 - 1,[(0,j - p)],p + (1 - q),
              block.zero l q (1 - q) j p hpad hp (by omega)⟩
    · by_cases hu_le2 : u <= 2
      · rcases z49 ((l * 2 + q) * 3 + t + 7) with ⟨s,e,hs,he⟩
        exact ⟨s - 1 - (e + u - 1),[],e + u - 1,
          block.short (l * 2 + q) t u s e (by omega) (by omega) he hs⟩
      · rcases z4a u (by omega) with ⟨b,p,hu_eq,hp⟩
        by_cases ht1 : t = 1
        · subst ht1
          rcases p with _ | _ | p
          · have hu0 : u = b * 2 + 2 := by omega
            subst hu0
            exact ⟨(l + q) * 3 - 1,[(0,b - 2),danger],1 - q,
              block.one_even l q (1 - q) b hpad⟩
          · have hu1 : u = b * 2 + 1 := by omega
            subst hu1
            exact ⟨(l + q) * 3,[],b + 1 + (1 - q),
              block.one_odd l q (1 - q) b hpad⟩
          · omega
        · rcases z49 t with ⟨a,e,ht_eq,he⟩
          rw [ht_eq,hu_eq]
          by_cases hape : a + p = e
          · exact ⟨(l + q) * 3,[],b + a + 1 + (1 - q),
              block.full l q (1 - q) a b p e hpad hp he (by omega) (by omega) hape⟩
          · exact ⟨(l + q) * 3,[(b - 1,a + p - e)],1 - p + e + (1 - q),
              block.split l q (1 - q) a b p e hpad hp he (by omega) (by omega) (by omega)⟩
inductive consume : Bool -> Nat -> Nat -> List cell -> List cell -> Prop
  | one (t u : Nat) (r : List cell) : consume false t u ((t,u) :: r) r
  | two (t u : Nat) (r : List cell) : consume true t u (danger :: (t,u) :: r) r
lemma z4c {extra : Bool} {t u : Nat} {l r : List cell}
    (hc : consume extra t u l r) (hsafe : zSi extra t u) :
    cut l r (t + u + (if extra then 3 else 1)) (if extra then 2 else 1) := by
  cases hc with
  | one t u r =>
    simp only [Bool.false_eq_true,↓reduceIte]
    exact cut.one (t,u) r hsafe.1 hsafe.2
  | two t u r =>
    simp only [↓reduceIte]
    have hw : t + u + 3 = 2 + weight (t,u) := by simp [weight]; omega
    rw [hw]
    exact cut.two (t,u) r hsafe
lemma z4d (l : List cell) (hl : good l) (hlen : 2 <= l.length) :
    ∃ extra t u r,consume extra t u l r /\ zSi extra t u := by
  rcases z3O l hl hlen with ⟨r,n,k,hcut⟩
  cases hcut with
  | one p r hp hne =>
    rcases p with ⟨t,u⟩
    exact ⟨false,t,u,r,consume.one t u r,⟨hp,hne⟩⟩
  | two p r hp =>
    rcases p with ⟨t,u⟩
    exact ⟨true,t,u,r,consume.two t u r,hp⟩
def block_step (f g : frame) : Prop :=
  ∃ extra t u r gap a E,
    consume extra t u f.cells r /\
    zSi extra t u /\
    block extra (width f) t u gap a E /\
    g = ⟨r ++ (t + u + (if extra then 3 else 1) + f.trailing,gap) :: a,E⟩
lemma z4e (f : frame) (hgood : good f.cells) (hlen : 2 <= f.cells.length) :
    ∃ g,block_step f g := by
  rcases z4d f.cells hgood hlen with ⟨extra,t,u,r,hc,hsafe⟩
  rcases z4b extra (width f) t u hsafe with ⟨gap,a,E,hb⟩
  exact ⟨_,extra,t,u,r,gap,a,E,hc,hsafe,hb,rfl⟩
lemma z4f {f g : frame} (hbs : block_step f g) (hL : 16 <= width f) :
    z3Y f g := by
  rcases hbs with ⟨extra,t,u,r,gap,a,E,hc,hsafe,hb,rfl⟩
  exact z48 f r (t + u + (if extra then 3 else 1)) (if extra then 2 else 1)
    extra t u gap a E (z4c hc hsafe) rfl rfl hL hsafe hb
lemma history_width {f0 f1 f2 f3 : frame} (h : history f0 f1 f2 f3) : 16 <= width f3 := by
  have hw0 := h.old_width
  have h01 := h.edge01.2.1
  have h12 := h.edge12.2.1
  have h23 := h.edge23.2.1
  omega
theorem history_progress {f0 f1 f2 f3 : frame} (h : history f0 f1 f2 f3) :
    ∃ f4,block_step f3 f4 /\ history f1 f2 f3 f4 := by
  rcases history_ready h with ⟨hgood,hlen⟩
  rcases z4e f3 hgood (by omega) with ⟨f4,hstep⟩
  exact ⟨f4,hstep,history_next h (z4f hstep (history_width h))⟩
end Queue
lemma z4g {n v : Nat} {w : zF} (h : zDg n v w) :
    ∀ {a : zF},zDg n v a -> w = a := by
  induction h with
  | nil =>
    intro a ha
    cases ha
    rfl
  | zero n v w h ih =>
    intro a ha
    generalize hv : v * 2 = x at ha
    cases ha with
    | zero _ v' a' ha' =>
      have hv' : v' = v := by omega
      subst hv'
      rw [ih ha']
    | one _ v' a' ha' => omega
  | one n v w h ih =>
    intro a ha
    generalize hv : v * 2 + 1 = x at ha
    cases ha with
    | zero _ v' a' ha' => omega
    | one _ v' a' ha' =>
      have hv' : v' = v := by omega
      subst hv'
      rw [ih ha']
lemma z4h {n v : Nat} {w : zF} {j u : Nat} {a : zF}
    (h : zDg n v w) (ha : zDg j u a) :
    zDg (n + j) (v + 2 ^ n * u) (w ++ a) := by
  induction h with
  | nil =>
    simp only [Nat.zero_add,Nat.pow_zero,Nat.one_mul,List.nil_append]
    exact ha
  | zero n v w _ ih =>
    have hlen : n + 1 + j = (n + j) + 1 := by omega
    have hval : v * 2 + 2 ^ (n + 1) * u = (v + 2 ^ n * u) * 2 := by
      rw [Nat.pow_succ]; ring
    rw [hlen,hval,List.append_assoc]
    exact zDg.zero (n + j) (v + 2 ^ n * u) (w ++ a) ih
  | one n v w _ ih =>
    have hlen : n + 1 + j = (n + j) + 1 := by omega
    have hval : v * 2 + 1 + 2 ^ (n + 1) * u = (v + 2 ^ n * u) * 2 + 1 := by
      rw [Nat.pow_succ]; ring
    rw [hlen,hval,List.append_assoc]
    exact zDg.one (n + j) (v + 2 ^ n * u) (w ++ a) ih
lemma z4i {n v : Nat} {w : zF} (h : zDg n v w) :
    zDg (n + 1) (v + 2 ^ n) (w ++ d) := by
  have h1 : v + 2 ^ n = v + 2 ^ n * 1 := by omega
  rw [h1]
  exact z4h h (zDg.one 0 0 [] .nil)
lemma z4j {n v : Nat} {w : zF} (r : zB) (h : zDg n v w) :
    (z18 (LC (n + 1) 0 ldh) (w +> z +> r)) [z00]⊢⁺
    (z18 (LC (n + 1) 0 ldh) (d +> w +> [1] +> r)) := by
  have hv := z1W h
  have hlt : v * 2 + 1 < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
  rcases z2c (n + 1) v (w ++ z) r (z2d h) hlt with ⟨a,ha,hrun⟩
  have heq : a = d ++ w := z4g ha (zDg.one n v w h)
  rw [heq] at hrun
  simpa [append_assoc] using hrun
lemma z4k {n v : Nat} {w : zF} (r : zB) (h : zDg n v w) :
    (z18 (LC (n + 1) 0 ldh) (w +> d +> z +> r)) [z00]⊢⁺
    (z18 (LC (n + 1) 0 ldh) (d +> w +> z +> [1] +> r)) := by
  have hv := z1W h
  have hge : 2 ^ (n + 1) <= (v + 2 ^ n) * 2 + 1 := by rw [Nat.pow_succ]; omega
  rcases z2f (n + 1) (v + 2 ^ n) (w ++ d) r (z4i h) hge with ⟨a,ha,hrun⟩
  have hval : (v + 2 ^ n) * 2 + 1 - 2 ^ (n + 1) = v * 2 + 1 := by rw [Nat.pow_succ]; omega
  rw [hval] at ha
  have heq : a = d ++ w := z4g ha (zDg.one n v w h)
  rw [heq] at hrun
  simpa [append_assoc] using hrun
lemma z4l {n v : Nat} {w : zF} (r : zB) (h : zDg n v w) :
    (z18 (LC (n + 1) 0 ldh) (w +> d +> r)) [z00]⊢⁺
    (((o1 ^ (4 + (n + 1) * 3)) +> ld0 +> LC (n + 1) (v * 2 + 1) ldh) {{D}}> r) := by
  have hge : 2 ^ (n + 1) <= (v + 2 ^ n) * 2 + 1 := by rw [Nat.pow_succ]; omega
  have hrun := z2k (n + 1) (v + 2 ^ n) (w ++ d) r (z4i h) hge
  have hval : (v + 2 ^ n) * 2 + 1 - 2 ^ (n + 1) = v * 2 + 1 := by rw [Nat.pow_succ]; omega
  rw [hval,append_assoc] at hrun
  exact hrun
lemma z4m : ∀ (t n v : Nat) (w : zF) (r : zB),
    zDg n v w ->
    (z18 (LC (n + t) 0 ldh) (w +> (d ^ t) +> z +> r)) [z00]⊢*
    (z18 (LC (n + t) 0 ldh) ((d ^ t) +> w +> z +> (o1 ^ t) +> r))
  | 0,n,v,w,r,_ => by simp; exact ⟨0,rfl⟩
  | t + 1,n,v,w,r,h => by
    have htop := z4i h
    have hrun := z4m t (n + 1) (v + 2 ^ n) (w ++ d) r htop
    have hlen1 : n + 1 + t = n + (t + 1) := by omega
    rw [hlen1] at hrun
    simp only [append_assoc] at hrun
    have hlow := z4h (z1Y t) h
    have hstep := zPs (z4k ((o1 ^ t) +> r) hlow)
    have hlen2 : t + n + 1 = n + (t + 1) := by omega
    rw [hlen2] at hstep
    simp only [append_assoc] at hstep
    have h1 : (d ^ (t + 1) : zF) +> z +> r = d +> (d ^ t) +> z +> r := by
      rw [z08,append_assoc]
    have h2 : (d ^ (t + 1) : zF) +> w +> z +> (o1 ^ (t + 1)) +> r =
        d +> (d ^ t) +> w +> z +> [1] +> (o1 ^ t) +> r := by
      rw [z08 d t,z08 o1 t,append_assoc,append_assoc]
    rw [h1,h2]
    exact zSt hrun hstep
lemma z4n : ∀ (u n v : Nat) (w : zF) (r : zB),
    zDg n v w ->
    (z18 (LC (n + u) 0 ldh) (w +> (z ^ u) +> r)) [z00]⊢*
    (z18 (LC (n + u) 0 ldh) ((d ^ u) +> w +> (o1 ^ u) +> r))
  | 0,n,v,w,r,_ => by simp; exact ⟨0,rfl⟩
  | u + 1,n,v,w,r,h => by
    have htop := z2d h
    have hrun := z4n u (n + 1) v (w ++ z) r htop
    have hlen1 : n + 1 + u = n + (u + 1) := by omega
    rw [hlen1] at hrun
    simp only [append_assoc] at hrun
    have hlow := z4h (z1Y u) h
    have hstep := zPs (z4j ((o1 ^ u) +> r) hlow)
    have hlen2 : u + n + 1 = n + (u + 1) := by omega
    rw [hlen2] at hstep
    simp only [append_assoc] at hstep
    have h1 : (z ^ (u + 1) : zF) +> r = z +> (z ^ u) +> r := by
      rw [z08,append_assoc]
    have h2 : (d ^ (u + 1) : zF) +> w +> (o1 ^ (u + 1)) +> r =
        d +> (d ^ u) +> w +> [1] +> (o1 ^ u) +> r := by
      rw [z08 d u,z08 o1 u,append_assoc,append_assoc]
    rw [h1,h2]
    exact zSt hrun hstep
lemma z4o (t u j v : Nat) (w : zF) (r : zB) (h : zDg j v w) :
    let L := j + 1 + u + t
    let K := (v + 1) * 2 ^ (1 + u + t) - 1
    (z18 (LC L 0 ldh) (w +> d +> (z ^ u) +> (d ^ t) +> z +> r)) [z00]⊢⁺
    (((o1 ^ (4 + L * 3)) +> ld0 +> LC L K ldh) {{D}}> ((o1 ^ u) +> z +> (o1 ^ t) +> r)) := by
  intro L K
  have hwd := z4i h
  have hmid := z4h hwd (z1X u)
  have hfirst := z4m t (j + 1 + u) (v + 2 ^ j + 2 ^ (j + 1) * 0) (w ++ d ++ (z ^ u)) r hmid
  simp only [append_assoc] at hfirst
  have hprefix := z4h (z1Y t) hwd
  have hsecond := z4n u (t + (j + 1)) (2 ^ t - 1 + 2 ^ t * (v + 2 ^ j))
    ((d ^ t) ++ (w ++ d)) (z +> (o1 ^ t) +> r) hprefix
  have hlen2 : t + (j + 1) + u = L := by omega
  rw [hlen2] at hsecond
  simp only [append_assoc] at hsecond
  have hlow := z4h (z1Y (u + t)) h
  have hlast := z4l ((o1 ^ u) +> z +> (o1 ^ t) +> r) hlow
  have hlen3 : u + t + j + 1 = L := by omega
  have hval3 : (2 ^ (u + t) - 1 + 2 ^ (u + t) * v) * 2 + 1 = K := by
    dsimp only [K]
    have hp := z0h (u + t)
    have hp1 : 2 ^ (1 + u + t) = 2 ^ (u + t) * 2 := by
      rw [show 1 + u + t = (u + t) + 1 by omega,Nat.pow_succ]
    have hcalc1 : (2 ^ (u + t) - 1 + 2 ^ (u + t) * v) * 2 =
        (2 ^ (u + t) - 1) * 2 + 2 ^ (u + t) * v * 2 := by ring
    have hcalc2 : (v + 1) * (2 ^ (u + t) * 2) =
        2 ^ (u + t) * 2 + 2 ^ (u + t) * v * 2 := by ring
    rw [hp1,hcalc1,hcalc2]
    omega
  rw [hlen3,hval3,z09 d u t,append_assoc,append_assoc] at hlast
  exact z06 hfirst (z06 hsecond hlast)
lemma z4p (r j v : Nat) (w : zF) (h : zDg j v w) :
    zDg (j + r) ((v + 1) * 2 ^ r - 1) ((d ^ r) ++ w) := by
  have hlen : j + r = r + j := by omega
  have hpr := z0h r
  have hval : (v + 1) * 2 ^ r - 1 = 2 ^ r - 1 + 2 ^ r * v := by
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm v (2 ^ r)]
    omega
  rw [hlen,hval]
  exact z4h (z1Y r) h
lemma z4q : z +> (default : zB) = default := z1U
lemma z4r (t u j v : Nat) (w : zF) (h : zDg j v w) :
    let L := j + 1 + u + t
    let K := (v + 1) * 2 ^ (1 + u + t) - 1
    (z18 (LC L 0 ldh) (w +> d +> (z ^ u) +> (d ^ t) +> default)) [z00]⊢⁺
    (((o1 ^ (4 + L * 3)) +> ld0 +> LC L K ldh) {{D}}> ((o1 ^ u) +> z +> (o1 ^ t) +> default)) := by
  intro L K
  have hrun := z4o t u j v w default h
  rw [z4q] at hrun
  exact hrun
lemma z4s (j v : Nat) (w : zF) (h : zDg j v w) :
    (z18 (LC (j + 2) 0 ldh) (w +> d +> z +> default)) [z00]⊢⁺
    (z18 (LC (j + 2) 0 ldh) ((d ^ 2) +> w +> RC 4)) := by
  have hfirst := z4r 0 1 j v w h
  dsimp only at hfirst
  have hlen : j + 1 + 1 + 0 = j + 2 := by omega
  have hr1 : (z ^ 1 : zF) +> (d ^ 0) +> (default : zB) = z +> default := rfl
  have hr2 : (o1 ^ 1 : zF) +> z +> (o1 ^ 0) +> (default : zB) = [1] +> default := by
    have : (o1 ^ 1 : zF) = [1] := rfl
    have : (o1 ^ 0 : zF) = [] := rfl
    simp
  rw [hlen,hr1,hr2] at hfirst
  have hK := z4p 2 j v w h
  have hlast := z3i (j + 2) ((v + 1) * 2 ^ 2 - 1) ((d ^ 2) ++ w) ldh hK
  rw [append_assoc] at hlast
  exact z05 hfirst hlast
lemma z4t (t u j v : Nat) (w : zF) (h : zDg j v w) :
    let L := j + 3 + u + t
    let K := (v + 1) * 2 ^ (3 + u + t) - 1
    (z18 (LC L 0 ldh) (w +> d +> (z ^ u) +> (d ^ t) +> d +> z +> default)) [z00]⊢⁺
    (((o1 ^ (4 + L * 3)) +> ld0 +> LC L K ldh) {{D}}> ((o1 ^ u) +> z +> (o1 ^ t) +> z +> d +> default)) := by
  intro L K
  have hmid := z4h (z4i h) (z1X u)
  have hhigh := z4h hmid (z1Y t)
  have hfirst := z4s (j + 1 + u + t) _ ((w ++ d ++ (z ^ u)) ++ (d ^ t)) hhigh
  have hlen1 : j + 1 + u + t + 2 = L := by omega
  rw [hlen1] at hfirst
  simp only [append_assoc] at hfirst
  have hlast := z4o t u (j + 2) ((v + 1) * 2 ^ 2 - 1) ((d ^ 2) ++ w) (z +> d +> default)
    (z4p 2 j v w h)
  dsimp only at hlast
  have hlen2 : j + 2 + 1 + u + t = L := by omega
  have hval2 : ((v + 1) * 2 ^ 2 - 1 + 1) * 2 ^ (1 + u + t) - 1 = K := by
    dsimp only [K]
    have hpos : 1 <= (v + 1) * 2 ^ 2 := by omega
    have hsub : (v + 1) * 2 ^ 2 - 1 + 1 = (v + 1) * 2 ^ 2 := by omega
    have hp : 2 ^ (3 + u + t) = 2 ^ 2 * 2 ^ (1 + u + t) := by
      rw [show 3 + u + t = 2 + (1 + u + t) by omega,Nat.pow_add]
    rw [hsub,hp,Nat.mul_assoc]
  have hrc4 : (RC 4 : zB) = z +> z +> d +> default := by
    rw [<- z2J]; rfl
  rw [hlen2,hval2,append_assoc] at hlast
  rw [hrc4] at hfirst
  exact zPt hfirst hlast
def zRw : List Queue.cell -> Nat -> zF
  | [],E => d ^ E
  | (t,u) :: r,E => zRw r E ++ (z ^ u) ++ (d ^ (t + 1))
def zRv : List Queue.cell -> Nat -> Nat
  | [],E => 2 ^ E - 1
  | (t,u) :: r,E => zRv r E + 2 ^ (Queue.mass r + E + u) * (2 ^ (t + 1) - 1)
def zFw (f : Queue.frame) : zF :=
  match f.cells with
  | [] => d ^ (f.trailing - 1)
  | (t,u) :: r => zRw r f.trailing ++ (z ^ u) ++ (d ^ t)
def config (f : Queue.frame) : Cfg (Fin 2) (Fin 6) :=
  z18 (LC (Queue.width f) 0 ldh) (zFw f +> default)
lemma z4u {n v : Nat} {w : zF} (u t : Nat) (h : zDg n v w) :
    zDg (n + u + t) (v + 2 ^ (n + u) * (2 ^ t - 1)) (w ++ (z ^ u) ++ (d ^ t)) := by
  have hz := z4h h (z1X u)
  simp only [Nat.mul_zero,Nat.add_zero] at hz
  exact z4h hz (z1Y t)
lemma z4v : ∀ (l : List Queue.cell) (E : Nat),
    zDg (Queue.mass l + E) (zRv l E) (zRw l E)
  | [],E => by
    simp only [Queue.mass,Nat.zero_add,zRv,zRw]
    exact z1Y E
  | (t,u) :: r,E => by
    simp only [Queue.mass,Queue.weight,zRv,zRw]
    have h := z4u u (t + 1) (z4v r E)
    have hlen : Queue.mass r + E + u + (t + 1) = t + u + 1 + Queue.mass r + E := by omega
    rw [hlen] at h
    exact h
lemma z4w (l : List Queue.cell) (E : Nat) :
    ∃ v,zDg (Queue.mass l + E) v (zRw l E) :=
  ⟨zRv l E,z4v l E⟩
lemma z4x (f : Queue.frame) (hne : f.cells ≠ []) :
    ∃ v,zDg (Queue.width f) v (zFw f) := by
  rcases f with ⟨_ | ⟨⟨t,u⟩,r⟩,E⟩
  · contradiction
  · rcases z4w r E with ⟨v,hv⟩
    refine ⟨v + 2 ^ (Queue.mass r + E + u) * (2 ^ t - 1),?_⟩
    have h := z4u u t hv
    have hlen : Queue.mass r + E + u + t = Queue.width ⟨(t,u) :: r,E⟩ := by
      simp only [Queue.width,Queue.mass,Queue.weight]; omega
    rw [<- hlen]
    exact h
lemma z4y (l : List Queue.cell) (E : Nat) (hne : l ≠ []) :
    zRw l E = zFw ⟨l,E⟩ ++ d := by
  rcases l with _ | ⟨⟨t,u⟩,r⟩
  · contradiction
  · simp only [zRw,zFw]
    rw [show t + 1 = t + 1 by rfl,<- z0a d t]
    simp [List.append_assoc]
lemma z4z (t u : Nat) (r : List Queue.cell) (E : Nat) (hr : r ≠ []) :
    zFw ⟨(t,u) :: r,E⟩ = zFw ⟨r,E⟩ ++ d ++ (z ^ u) ++ (d ^ t) := by
  change zRw r E ++ (z ^ u) ++ (d ^ t) = zFw ⟨r,E⟩ ++ d ++ (z ^ u) ++ (d ^ t)
  rw [z4y r E hr]
lemma z4A (t u : Nat) (r : List Queue.cell) (E : Nat) (hr : r ≠ []) :
    zFw ⟨Queue.danger :: (t,u) :: r,E⟩ =
      zFw ⟨r,E⟩ ++ d ++ (z ^ u) ++ (d ^ t) ++ d ++ z := by
  unfold Queue.danger
  rw [z4z 0 1 ((t,u) :: r) E (by simp),z4z t u r E hr]
  have hd0 : (d ^ 0 : zF) = [] := rfl
  have hz1 : (z ^ 1 : zF) = z := rfl
  rw [hd0,hz1,List.append_nil]
lemma z4B : ∀ (l r : List Queue.cell) (E : Nat),
    zRw (l ++ r) E = zRw r E ++ zRw l 0
  | [],r,E => by simp [zRw]
  | (t,u) :: l,r,E => by
    simp only [List.cons_append,zRw,z4B l r E,List.append_assoc]
lemma z4C : ∀ (l : List Queue.cell) (E : Nat),
    zRw l E = (d ^ E) ++ zRw l 0
  | [],E => by simp [zRw]
  | (t,u) :: l,E => by
    simp only [zRw]
    rw [z4C l E]
    simp [List.append_assoc]
lemma z4D (l r : List Queue.cell) (E : Nat) (hl : l ≠ []) :
    zFw ⟨l ++ r,E⟩ = zRw r E ++ zFw ⟨l,0⟩ := by
  rcases l with _ | ⟨⟨t,u⟩,l⟩
  · contradiction
  · simp only [List.cons_append,zFw,z4B,List.append_assoc]
lemma z4E (l : List Queue.cell) (E : Nat) (hl : l ≠ []) :
    zFw ⟨l,E⟩ = (d ^ E) ++ zFw ⟨l,0⟩ := by
  rcases l with _ | ⟨⟨t,u⟩,l⟩
  · contradiction
  · simp only [zFw]
    rw [z4C l E]
    simp [List.append_assoc]
def z4F (gap : Nat) (a : List Queue.cell) (E : Nat) : zF :=
  zRw a E ++ (z ^ gap) ++ d
def zPw (gap : Nat) (a : List Queue.cell) (E : Nat) : Nat :=
  gap + Queue.mass a + E + 1
def zPv (gap : Nat) (a : List Queue.cell) (E : Nat) : Nat :=
  zRv a E + 2 ^ (Queue.mass a + E + gap)
lemma z4G (gap : Nat) (a : List Queue.cell) (E : Nat) :
    zDg (zPw gap a E) (zPv gap a E) (z4F gap a E) := by
  have h := z4u gap 1 (z4v a E)
  have hd1 : (d ^ 1 : zF) = d := rfl
  have hlen : Queue.mass a + E + gap + 1 = zPw gap a E := by
    unfold zPw; omega
  have hval : zRv a E + 2 ^ (Queue.mass a + E + gap) * (2 ^ 1 - 1) = zPv gap a E := by
    unfold zPv; omega
  rw [hd1,hlen,hval] at h
  exact h
lemma z4H (gap : Nat) (a : List Queue.cell) (E k : Nat) :
    z4F gap a E +> RC k = RC (k * 2 ^ (zPw gap a E) + zPv gap a E) := by
  rw [z2m (z4G gap a E) k]
  congr 1
  ring
lemma z4I (r : List Queue.cell) (E n gap : Nat) (a : List Queue.cell) (E' : Nat)
    (hr : r ≠ []) :
    zFw ⟨r ++ (n + E,gap) :: a,E'⟩ =
      z4F gap a E' ++ (d ^ n) ++ zFw ⟨r,E⟩ := by
  rw [z4D r ((n + E,gap) :: a) E' hr]
  unfold z4F
  simp only [zRw]
  rw [z4E r E hr]
  have hpow : (d ^ (n + E + 1) : zF) = d ++ (d ^ n) ++ (d ^ E) := by
    rw [show n + E + 1 = 1 + n + E by omega,z09,z09]
    rfl
  rw [hpow]
  simp [List.append_assoc]
lemma z4J {extra : Bool} {t u : Nat} {l r : List Queue.cell} (E : Nat)
    (hc : Queue.consume extra t u l r) (hr : r ≠ []) :
    Queue.width ⟨l,E⟩ = Queue.width ⟨r,E⟩ + t + u + (if extra then 3 else 1) := by
  cases hc <;>
  · rcases r with _ | ⟨⟨x,y⟩,r⟩
    · contradiction
    · simp only [Queue.width,Queue.mass,Queue.weight,Queue.danger,Bool.false_eq_true,↓reduceIte]; omega
def zDc (extra : Bool) (L k t u : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((o1 ^ (4 + L * 3)) +> ld0 +> LC L k ldh) {{D}}>
    ((o1 ^ u) +> z +> (o1 ^ t) +> (if extra then z +> d +> default else default)))
lemma z4K {extra : Bool} {t u : Nat} {l r : List Queue.cell} (E v : Nat)
    (hc : Queue.consume extra t u l r) (hr : r ≠ [])
    (hd : zDg (Queue.width ⟨r,E⟩) v (zFw ⟨r,E⟩)) :
    (config ⟨l,E⟩) [z00]⊢⁺
    (zDc extra (Queue.width ⟨l,E⟩) ((v + 1) * 2 ^ (t + u + (if extra then 3 else 1)) - 1) t u) := by
  have hw := z4J E hc hr
  cases hc with
  | one t u r =>
    unfold config zDc
    rw [z4z t u r E hr]
    simp only [append_assoc,Bool.false_eq_true,↓reduceIte] at hw ⊢
    have h1 := z4r t u (Queue.width ⟨r,E⟩) v (zFw ⟨r,E⟩) hd
    dsimp only at h1
    have hlen : Queue.width ⟨r,E⟩ + 1 + u + t = Queue.width ⟨(t,u) :: r,E⟩ := by omega
    have hexp : 1 + u + t = t + u + 1 := by omega
    rw [hlen,hexp] at h1
    exact h1
  | two t u r =>
    unfold config zDc
    rw [z4A t u r E hr]
    simp only [append_assoc,↓reduceIte] at hw ⊢
    have h1 := z4t t u (Queue.width ⟨r,E⟩) v (zFw ⟨r,E⟩) hd
    dsimp only at h1
    have hlen : Queue.width ⟨r,E⟩ + 3 + u + t = Queue.width ⟨Queue.danger :: (t,u) :: r,E⟩ := by omega
    have hexp : 3 + u + t = t + u + 3 := by omega
    rw [hlen,hexp] at h1
    exact h1
def zDr (extra : Bool) (L t u gap : Nat) (a : List Queue.cell) (E : Nat) : Prop :=
  ∀ k,k < 2 ^ L ->
    (zDc extra L k t u) [z00]⊢*
    (z18 (LC (L + zPw gap a E) 0 ldh) (z4F gap a E +> RC k))
lemma z4L {extra : Bool} {t u : Nat} {l r : List Queue.cell}
    (E gap : Nat) (a : List Queue.cell) (E' : Nat)
    (hc : Queue.consume extra t u l r) (hr : r ≠ []) :
    Queue.width ⟨r ++ (t + u + (if extra then 3 else 1) + E,gap) :: a,E'⟩ =
      Queue.width ⟨l,E⟩ + zPw gap a E' := by
  have hw := z4J E hc hr
  have hm : 0 < Queue.mass r := by
    have := Queue.length_mass r
    rcases r with _ | ⟨p,r⟩
    · contradiction
    · simp at this; omega
  simp only [Queue.width,Queue.mass_app,Queue.mass,Queue.weight,zPw] at hw ⊢
  omega
lemma z4M {extra : Bool} {t u : Nat} {l r : List Queue.cell}
    (E gap : Nat) (a : List Queue.cell) (E' : Nat)
    (hc : Queue.consume extra t u l r) (hr : r ≠ [])
    (hreturn : zDr extra (Queue.width ⟨l,E⟩) t u gap a E') :
    (config ⟨l,E⟩) [z00]⊢⁺
    (config ⟨r ++ (t + u + (if extra then 3 else 1) + E,gap) :: a,E'⟩) := by
  rcases z4x ⟨r,E⟩ hr with ⟨v,hv⟩
  have hw := z4J E hc hr
  let n := t + u + (if extra then 3 else 1)
  have hw' : Queue.width ⟨r,E⟩ + n = Queue.width ⟨l,E⟩ := by dsimp [n]; omega
  have hK := z4p n (Queue.width ⟨r,E⟩) v (zFw ⟨r,E⟩) hv
  rw [hw'] at hK
  have h1 := z4K E v hc hr hv
  have h2 := hreturn ((v + 1) * 2 ^ n - 1) (z1W hK)
  have hword := z2m hK 0
  simp only [Nat.mul_zero,Nat.add_zero,append_assoc] at hword
  rw [<- z2K] at hword
  rw [<- hword] at h2
  have hg := z4L E gap a E' hc hr
  have hcfg : config ⟨r ++ (n + E,gap) :: a,E'⟩ =
      z18 (LC (Queue.width ⟨l,E⟩ + zPw gap a E') 0 ldh)
        (z4F gap a E' +> (d ^ n) +> zFw ⟨r,E⟩ +> default) := by
    unfold config
    rw [hg,z4I r E n gap a E' hr,append_assoc,append_assoc]
  rw [hcfg]
  exact z05 h1 h2
lemma z4N (extra : Bool) (L t u gap : Nat) (a : List Queue.cell) (E s v : Nat)
    (hs : s = zPw gap a E)
    (hv : zPv gap a E = 2 ^ (s - 1) + v)
    (hrun : ∀ k,k < 2 ^ L ->
      (zDc extra L k t u) [z00]⊢*
      (z18 (LC (L + s) 0 ldh) (RC (k * 2 ^ s + 2 ^ (s - 1) + v)))) :
    zDr extra L t u gap a E := by
  subst hs
  intro k hk
  rw [z4H,hv]
  have hassoc : k * 2 ^ zPw gap a E + (2 ^ (zPw gap a E - 1) + v) =
      k * 2 ^ zPw gap a E + 2 ^ (zPw gap a E - 1) + v := by omega
  rw [hassoc]
  exact hrun k hk
lemma z4O (l q h k j p : Nat)
    (hqh : q + h = 1) (hL : 0 < l * 2 + q) (hk : k < 2 ^ (l * 2 + q)) (hp : p <= 1) :
    let s := l * 3 + 2 + q * 2 + j
    (zDc false (l * 2 + q) k 0 (2 + j * 2 + p)) [z00]⊢*
    (z18 (LC (l * 2 + q + s) 0 ldh) (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ j + p) * (1 + h) + h)))) := by
  intro s
  unfold zDc
  have hr : z +> (o1 ^ 0) +> (if false then z +> d +> default else (default : zB)) = default := by
    simp
  rw [hr]
  have hrun := z3g l q h k j p ldh hqh hL hk hp
  dsimp only at hrun
  have hval : k * 2 ^ s + 2 ^ (s - 1) + (2 ^ j + p) * (1 + h) + h =
      k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ j + p) * (1 + h) + h) := by omega
  rw [<- hval]
  exact hrun
lemma z4P (l q h : Nat) (hqh : q + h = 1) (hL : 16 <= l * 2 + q) :
    zDr false (l * 2 + q) 0 2 ((l + q) * 3 - 1) [] (1 + h) := by
  refine z4N false (l * 2 + q) 0 2 ((l + q) * 3 - 1) [] (1 + h)
    (l * 3 + 2 + q * 2 + 0) ((2 ^ 0 + 0) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.mass]; omega
  · simp only [zPv,zRv,Queue.mass]
    have hexp : 0 + (1 + h) + ((l + q) * 3 - 1) = l * 3 + 2 + q * 2 + 0 - 1 := by omega
    rw [hexp]
    rcases h with _ | _ | h <;> omega
  · intro k hk
    exact z4O l q h k 0 0 hqh (by omega) hk (by omega)
lemma z4Q (l q h : Nat) (hqh : q + h = 1) (hL : 16 <= l * 2 + q) :
    zDr false (l * 2 + q) 0 3 ((l + q) * 3 - 2) [Queue.danger] h := by
  refine z4N false (l * 2 + q) 0 3 ((l + q) * 3 - 2) [Queue.danger] h
    (l * 3 + 2 + q * 2 + 0) ((2 ^ 0 + 1) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.danger,Queue.mass,Queue.weight]; omega
  · simp only [zPv,Queue.danger,zRv,Queue.mass,Queue.weight]
    have hexp : (0 + 1 + 1 + 0) + h + ((l + q) * 3 - 2) = l * 3 + 2 + q * 2 + 0 - 1 := by omega
    rw [hexp]
    rcases h with _ | _ | h <;> omega
  · intro k hk
    exact z4O l q h k 0 1 hqh (by omega) hk (by omega)
lemma z4R (l q h : Nat) (hqh : q + h = 1) (hL : 16 <= l * 2 + q) :
    zDr false (l * 2 + q) 0 5 ((l + q) * 3 - 1) [] (2 + h) := by
  refine z4N false (l * 2 + q) 0 5 ((l + q) * 3 - 1) [] (2 + h)
    (l * 3 + 2 + q * 2 + 1) ((2 ^ 1 + 1) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.mass]; omega
  · simp only [zPv,zRv,Queue.mass]
    have hexp : 0 + (2 + h) + ((l + q) * 3 - 1) = l * 3 + 2 + q * 2 + 1 - 1 := by omega
    rw [hexp]
    rcases h with _ | _ | h <;> omega
  · intro k hk
    exact z4O l q h k 1 1 hqh (by omega) hk (by omega)
lemma z4S (l q h j p : Nat) (hqh : q + h = 1) (hL : 16 <= l * 2 + q)
    (hp : p <= 1) (hj : 1 + p <= j) :
    zDr false (l * 2 + q) 0 (j * 2 + 2 + p) ((l + q) * 3 - 1) [(0,j - p)] (p + h) := by
  refine z4N false (l * 2 + q) 0 (j * 2 + 2 + p) ((l + q) * 3 - 1) [(0,j - p)] (p + h)
    (l * 3 + 2 + q * 2 + j) ((2 ^ j + p) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.mass,Queue.weight]; omega
  · simp only [zPv,zRv,Queue.mass,Queue.weight]
    have hexp1 : (0 + (j - p) + 1 + 0) + (p + h) + ((l + q) * 3 - 1) = l * 3 + 2 + q * 2 + j - 1 := by omega
    have hexp2 : 0 + (p + h) + (j - p) = j + h := by omega
    have hpow : 2 ^ (j + h) = 2 ^ j * 2 ^ h := Nat.pow_add 2 j h
    rw [hexp1,hexp2,hpow]
    rcases p with _ | _ | p <;> rcases h with _ | _ | h <;>
      (simp only [Nat.reduceAdd,Nat.reducePow,Nat.reduceSub]; omega)
  · intro k hk
    have hu : j * 2 + 2 + p = 2 + j * 2 + p := by omega
    rw [hu]
    exact z4O l q h k j p hqh (by omega) hk hp
lemma z4T (L t u s e : Nat) (hL : 0 < L) (hshort : u = 2 -> 4 <= t)
    (ht : 0 < t) (hu : u = 1 \/ u = 2) (he : e <= 1) (hs : L * 3 + t + 7 = s * 2 + e) :
    zDr false L t u (s - 1 - (e + u - 1)) [] (e + u - 1) := by
  refine z4N false L t u (s - 1 - (e + u - 1)) [] (e + u - 1)
    s (2 ^ (e + u - 1) - 1) ?_ ?_ ?_
  · rcases hu with rfl | rfl <;> (simp [zPw,Queue.mass]; omega)
  · simp only [zPv,zRv,Queue.mass]
    have hexp : 0 + (e + u - 1) + (s - 1 - (e + u - 1)) = s - 1 := by
      rcases hu with rfl | rfl <;> omega
    rw [hexp]; omega
  · intro k hk
    rcases hu with rfl | rfl
    · rcases e with _ | _ | e
      · unfold zDc
        have hr : (o1 ^ 1 : zF) +> z +> (o1 ^ t) +>
            (if false then z +> d +> default else (default : zB)) =
            [1,0,0,0] +> (o1 ^ t) +> default := rfl
        rw [hr]
        exact z2P L k t s 0 ldh hk ht (by omega) hs
      · unfold zDc
        have hr : (o1 ^ 1 : zF) +> z +> (o1 ^ t) +>
            (if false then z +> d +> default else (default : zB)) =
            [1,0,0,0] +> (o1 ^ t) +> default := rfl
        rw [hr]
        exact z2P L k t s 1 ldh hk ht (by omega) hs
      · omega
    · have hv : 2 ^ (e + 2 - 1) - 1 = e * 2 + 1 := by
        rcases e with _ | _ | e <;> omega
      have hassoc : k * 2 ^ s + 2 ^ (s - 1) + (e * 2 + 1) = k * 2 ^ s + 2 ^ (s - 1) + e * 2 + 1 := by omega
      rw [hv,hassoc]
      unfold zDc
      have hr : (o1 ^ 2 : zF) +> z +> (o1 ^ t) +>
          (if false then z +> d +> default else (default : zB)) =
          [1,1,0,0,0] +> (o1 ^ t) +> default := rfl
      rw [hr]
      exact z2Q L k t s e ldh hk (hshort rfl) he hs
lemma z4U (l q h b : Nat) (hqh : q + h = 1) (hL : 16 <= l * 2 + q) :
    zDr false (l * 2 + q) 1 (3 + b * 2) ((l + q) * 3) [] (b + 2 + h) := by
  let s := l * 3 + 2 + q * 2 + (b + 1 + 1)
  refine z4N false (l * 2 + q) 1 (3 + b * 2) ((l + q) * 3) [] (b + 2 + h)
    s (((2 ^ (b + 1) - 1) * 2 + 1) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.mass,s]; omega
  · simp only [zPv,zRv,Queue.mass]
    have hexp : 0 + (b + 2 + h) + (l + q) * 3 = s - 1 := by dsimp [s]; omega
    rw [hexp]
    have hpb := z0h (b + 1)
    rcases h with _ | _ | h
    · have : b + 2 + 0 = (b + 1) + 1 := by omega
      rw [this,Nat.pow_succ]; omega
    · have : b + 2 + 1 = (b + 1) + 2 := by omega
      rw [this,Nat.pow_add]; omega
    · omega
  · intro k hk
    have hassoc : k * 2 ^ s + 2 ^ (s - 1) + (((2 ^ (b + 1) - 1) * 2 + 1) * (1 + h) + h) =
        k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) - 1) * 2 + 1) * (1 + h) + h := by omega
    rw [hassoc]
    unfold zDc
    have hr : (o1 ^ (3 + b * 2) : zF) +> z +> (o1 ^ 1) +>
        (if false then z +> d +> default else (default : zB)) =
        (o1 ^ (3 + b * 2)) +> z +> [1] +> default := rfl
    rw [hr]
    exact z35 l q h k b ldh hqh (by omega) hk
lemma z4V (l q h b : Nat) (hqh : q + h = 1) (hL : 16 <= l * 2 + q) (hb : 1 <= b) :
    zDr false (l * 2 + q) 1 (4 + b * 2) ((l + q) * 3 - 1) [(0,b - 1),Queue.danger] h := by
  let s := l * 3 + 2 + q * 2 + (b + 1)
  refine z4N false (l * 2 + q) 1 (4 + b * 2) ((l + q) * 3 - 1)
    [(0,b - 1),Queue.danger] h s ((2 ^ (b + 1) + 2) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.danger,Queue.mass,Queue.weight,s]; omega
  · simp only [zPv,Queue.danger,zRv,Queue.mass,Queue.weight]
    have hexp1 : (0 + (b - 1) + 1 + (0 + 1 + 1 + 0)) + h + ((l + q) * 3 - 1) = s - 1 := by
      dsimp [s]; omega
    have hexp2 : (0 + 1 + 1 + 0) + h + (b - 1) = b + 1 + h := by omega
    rw [hexp1,hexp2]
    rcases h with _ | _ | h
    · simp; omega
    · rw [Nat.pow_succ]; simp; omega
    · omega
  · intro k hk
    have hassoc : k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ (b + 1) + 2) * (1 + h) + h) =
        k * 2 ^ s + 2 ^ (s - 1) + (2 ^ (b + 1) + 2) * (1 + h) + h := by omega
    rw [hassoc]
    unfold zDc
    have hr : (o1 ^ (4 + b * 2) : zF) +> z +> (o1 ^ 1) +>
        (if false then z +> d +> default else (default : zB)) =
        (o1 ^ (4 + b * 2)) +> z +> [1] +> default := rfl
    rw [hr]
    exact z3j l q h k b ldh hqh (by omega) hk
lemma z4W (extra : Bool) (L k t u s v h t' u' s' v' : Nat)
    (ht : t = t') (hu : u = u') (hs : s = s') (hv : v = v')
    (hrun : (zDc extra L k t' u') [z00]⊢*
      (z18 (LC (L + s') 0 ldh) (RC (k * 2 ^ s' + 2 ^ (s' - 1) + v' * (1 + h) + h)))) :
    (zDc extra L k t u) [z00]⊢*
      (z18 (LC (L + s) 0 ldh) (RC (k * 2 ^ s + 2 ^ (s - 1) + v * (1 + h) + h))) := by
  subst ht; subst hu; subst hs; subst hv; exact hrun
lemma z4X (l q h k a b p e : Nat)
    (hqh : q + h = 1) (hL : 0 < l * 2 + q) (hk : k < 2 ^ (l * 2 + q))
    (hp : p <= 1) (he : e <= 1) (ha : 1 <= a) (hb : 1 <= b)
    (hex : a = 1 -> e = 1 -> p = 0 -> 2 <= b) :
    let s := l * 3 + 2 + q * 2 + (a + b + 1)
    (zDc false (l * 2 + q) k (a * 2 + e) (b * 2 + 2 - p)) [z00]⊢*
    (z18 (LC (l * 2 + q + s) 0 ldh)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ b - 1) * 2 ^ (a + 1) + (2 ^ (1 - p + e) - 1)) * (1 + h) + h))) := by
  intro s
  rcases p with _ | _ | p <;> rcases e with _ | _ | e <;> try omega
  · rcases a with _ | a; · omega
    rcases b with _ | b; · omega
    rcases a with _ | a
    · refine z4W false (l * 2 + q) k _ _ s _ h
        2 (4 + b * 2) (l * 3 + 2 + q * 2 + (b + 0 + 3)) ((2 ^ (b + 1) - 1) * 4 + 1)
        (by omega) (by omega) (by dsimp [s]; omega) rfl ?_
      unfold zDc
      have hr : (o1 ^ (4 + b * 2) : zF) +> z +> (o1 ^ 2) +>
          (if false then z +> d +> default else (default : zB)) =
          (o1 ^ (4 + b * 2)) +> z +> [1,1] +> default := rfl
      rw [hr]
      exact z3w l q h k b ldh hqh hL hk
    · refine z4W false (l * 2 + q) k _ _ s _ h
        (4 + a * 2) (4 + b * 2) (l * 3 + 2 + q * 2 + (b + (1 + a) + 3))
        ((2 ^ (b + 1) - 1) * 2 ^ (1 + a + 2) + 1)
        (by omega) (by omega) (by dsimp [s]; omega) ?_ ?_
      · rw [show 1 + a + 2 = a + 1 + 1 + 1 by omega]; rfl
      · unfold zDc
        exact z3s l q h k b a ldh hqh hL hk
  · rcases a with _ | a; · omega
    rcases b with _ | b; · omega
    rcases a with _ | a
    · have hb1 : 1 <= b := by have := hex rfl rfl rfl; omega
      refine z4W false (l * 2 + q) k _ _ s _ h
        3 (4 + b * 2) (l * 3 + 2 + q * 2 + (b + 0 + 3)) ((2 ^ (b + 1) - 1) * 4 + 3)
        (by omega) (by omega) (by dsimp [s]; omega) rfl ?_
      unfold zDc
      have hr : (o1 ^ (4 + b * 2) : zF) +> z +> (o1 ^ 3) +>
          (if false then z +> d +> default else (default : zB)) =
          (o1 ^ (4 + b * 2)) +> z +> [1,1,1] +> default := rfl
      rw [hr]
      exact z3y l q h k b ldh hqh hL hk hb1
    · refine z4W false (l * 2 + q) k _ _ s _ h
        (5 + a * 2) (4 + b * 2) (l * 3 + 2 + q * 2 + (b + (1 + a) + 3))
        ((2 ^ (b + 1) - 1) * 2 ^ (1 + a + 2) + 3)
        (by omega) (by omega) (by dsimp [s]; omega) ?_ ?_
      · rw [show 1 + a + 2 = a + 1 + 1 + 1 by omega]; rfl
      · unfold zDc
        exact z3t l q h k b a ldh hqh hL hk
  · rcases a with _ | a; · omega
    rcases b with _ | b; · omega
    rcases a with _ | _ | a
    · refine z4W false (l * 2 + q) k _ _ s _ h
        2 (1 + (b + 1) * 2) (l * 3 + 2 + q * 2 + ((b + 1) + 2)) ((2 ^ (b + 1) - 1) * 4)
        (by omega) (by omega) (by dsimp [s]; omega) (by simp) ?_
      unfold zDc
      have hr : (o1 ^ (1 + (b + 1) * 2) : zF) +> z +> (o1 ^ 2) +>
          (if false then z +> d +> default else (default : zB)) =
          (o1 ^ (1 + (b + 1) * 2)) +> z +> [1,1] +> default := rfl
      rw [hr]
      exact z3a l q h k (b + 1) ldh hqh hL hk
    · refine z4W false (l * 2 + q) k _ _ s _ h
        4 (1 + (b + 1) * 2) (l * 3 + 2 + q * 2 + ((b + 1) + 3)) ((2 ^ (b + 1) - 1) * 8)
        (by omega) (by omega) (by dsimp [s]; omega) (by simp) ?_
      unfold zDc
      exact z3b l q h k (b + 1) ldh hqh hL hk
    · refine z4W false (l * 2 + q) k _ _ s _ h
        (6 + a * 2) (3 + b * 2) (l * 3 + 2 + q * 2 + (b + 1 + (4 + a)))
        ((2 ^ (b + 1) - 1) * 2 ^ (4 + a))
        (by omega) (by omega) (by dsimp [s]; omega) ?_ ?_
      · rw [show 4 + a = a + 1 + 1 + 1 + 1 by omega]; simp
      · unfold zDc
        exact z34 l q h k b a ldh hqh hL hk
  · rcases a with _ | a; · omega
    rcases b with _ | b; · omega
    refine z4W false (l * 2 + q) k _ _ s _ h
      (3 + a * 2) (3 + b * 2) (l * 3 + 2 + q * 2 + (b + 1 + (2 + a)))
      ((2 ^ (b + 1) - 1) * 2 ^ (2 + a) + 1)
      (by omega) (by omega) (by dsimp [s]; omega) ?_ ?_
    · rw [show 2 + a = a + 1 + 1 by omega]; rfl
    · unfold zDc
      exact z32 l q h k b a ldh hqh hL hk
lemma z4Y (b x f h : Nat) (hh : h <= 1) :
    2 ^ (f + h) - 1 + 2 ^ (x + h) * (2 ^ b - 1) =
      ((2 ^ b - 1) * 2 ^ x + (2 ^ f - 1)) * (1 + h) + h := by
  have hpf := z0h f
  have hpb := z0h b
  rcases h with _ | _ | h
  · simp [Nat.mul_comm]; omega
  · rw [Nat.pow_succ,Nat.pow_succ]
    have h1 : 2 ^ f * 2 - 1 = (2 ^ f - 1) * 2 + 1 := by omega
    rw [h1]
    ring
  · omega
lemma z4Z (l q h a b p e : Nat)
    (hqh : q + h = 1) (hL : 16 <= l * 2 + q)
    (hp : p <= 1) (he : e <= 1) (ha : 1 <= a) (hb : 1 <= b) (hfull : a + p = e)
    (hsafe : a = 1 -> e = 1 -> p = 0 -> 2 <= b) :
    zDr false (l * 2 + q) (a * 2 + e) (b * 2 + 2 - p) ((l + q) * 3) [] (b + a + 1 + h) := by
  have ha1 : a = 1 := by omega
  have hp0 : p = 0 := by omega
  have he1 : e = 1 := by omega
  subst ha1; subst hp0; subst he1
  let s := l * 3 + 2 + q * 2 + (1 + b + 1)
  refine z4N false (l * 2 + q) (1 * 2 + 1) (b * 2 + 2 - 0) ((l + q) * 3) []
    (b + 1 + 1 + h) s (((2 ^ b - 1) * 2 ^ (1 + 1) + (2 ^ (1 - 0 + 1) - 1)) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.mass,s]; omega
  · simp only [zPv,zRv,Queue.mass]
    have hexp : 0 + (b + 1 + 1 + h) + (l + q) * 3 = s - 1 := by dsimp [s]; omega
    rw [hexp]
    have hpb := z0h b
    rcases h with _ | _ | h
    · have : b + 1 + 1 + 0 = b + 2 := by omega
      rw [this,Nat.pow_add]; omega
    · have : b + 1 + 1 + 1 = b + 3 := by omega
      rw [this,Nat.pow_add]; omega
    · omega
  · intro k hk
    have hassoc : k * 2 ^ s + 2 ^ (s - 1) + (((2 ^ b - 1) * 2 ^ (1 + 1) + (2 ^ (1 - 0 + 1) - 1)) * (1 + h) + h) =
        k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ b - 1) * 2 ^ (1 + 1) + (2 ^ (1 - 0 + 1) - 1)) * (1 + h) + h := by omega
    rw [hassoc]
    exact z4X l q h k 1 b 0 1 hqh (by omega) hk (by omega) (by omega) (by omega) hb hsafe
lemma z50 (l q h a b p e : Nat)
    (hqh : q + h = 1) (hL : 16 <= l * 2 + q)
    (hp : p <= 1) (he : e <= 1) (ha : 1 <= a) (hb : 1 <= b) (hsplit : e < a + p)
    (hsafe : a = 1 -> e = 1 -> p = 0 -> 2 <= b) :
    zDr false (l * 2 + q) (a * 2 + e) (b * 2 + 2 - p) ((l + q) * 3)
      [(b - 1,a + p - e)] (1 - p + e + h) := by
  let s := l * 3 + 2 + q * 2 + (a + b + 1)
  refine z4N false (l * 2 + q) (a * 2 + e) (b * 2 + 2 - p) ((l + q) * 3)
    [(b - 1,a + p - e)] (1 - p + e + h) s
    (((2 ^ b - 1) * 2 ^ (a + 1) + (2 ^ (1 - p + e) - 1)) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.mass,Queue.weight,s]; omega
  · simp only [zPv,zRv,Queue.mass,Queue.weight]
    have hb1 : b - 1 + 1 = b := by omega
    have hexp1 : (b - 1 + (a + p - e) + 1 + 0) + (1 - p + e + h) + (l + q) * 3 = s - 1 := by
      dsimp [s]; omega
    have hexp2 : 0 + (1 - p + e + h) + (a + p - e) = a + 1 + h := by omega
    have hexp3 : 1 - p + e + h = (1 - p + e) + h := by omega
    rw [hb1,hexp1,hexp2,hexp3,z4Y b (a + 1) (1 - p + e) h (by omega)]
    omega
  · intro k hk
    have hassoc : k * 2 ^ s + 2 ^ (s - 1) + (((2 ^ b - 1) * 2 ^ (a + 1) + (2 ^ (1 - p + e) - 1)) * (1 + h) + h) =
        k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ b - 1) * 2 ^ (a + 1) + (2 ^ (1 - p + e) - 1)) * (1 + h) + h := by omega
    rw [hassoc]
    exact z4X l q h k a b p e hqh (by omega) hk hp he ha hb hsafe
lemma z51 (l q h k a b p : Nat)
    (hqh : q + h = 1) (hL : 0 < l * 2 + q) (hk : k < 2 ^ (l * 2 + q))
    (ha : 1 <= a) (hb : 1 <= b) (hp : p <= 1) :
    let s := l * 3 + 2 + q * 2 + (a + b + 3)
    (zDc true (l * 2 + q) k (a * 2 + 1) (b * 2 + 2 - p)) [z00]⊢*
    (z18 (LC (l * 2 + q + s) 0 ldh)
      (RC (k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ b - 1) * 2 ^ (a + 3) - 1) * (1 + h) + h))) := by
  intro s
  rcases a with _ | a; · omega
  rcases b with _ | b; · omega
  rcases p with _ | _ | p <;> try omega
  · refine z4W true (l * 2 + q) k _ _ s _ h
      (3 + a * 2) (4 + b * 2) (l * 3 + 2 + q * 2 + (b + a + 5))
      ((2 ^ (b + 1) - 1) * 2 ^ (a + 4) - 1)
      (by omega) (by omega) (by dsimp [s]; omega) ?_ ?_
    · rw [show a + 1 + 3 = a + 4 by omega]
    · unfold zDc
      exact z3H l q h k b a ldh hqh hL hk
  · refine z4W true (l * 2 + q) k _ _ s _ h
      (1 + (a + 1) * 2) (3 + b * 2) (l * 3 + 2 + q * 2 + (b + 1 + (1 + (a + 1)) + 1 + 1))
      ((2 ^ (b + 1) - 1) * 2 ^ (1 + (a + 1) + 2) - 1)
      (by omega) (by omega) (by dsimp [s]; omega) ?_ ?_
    · rw [show 1 + (a + 1) + 2 = a + 1 + 3 by omega]
    · unfold zDc
      exact z3B l q h k b (a + 1) ldh hqh hL hk
lemma z52 (l q h a b p : Nat)
    (hqh : q + h = 1) (hL : 16 <= l * 2 + q) (ha : 1 <= a) (hb : 2 <= b) (hp : p <= 1) :
    zDr true (l * 2 + q) (a * 2 + 1) (b * 2 + 2 - p) ((l + q) * 3) [(b - 2,1)] (a + 3 + h) := by
  let s := l * 3 + 2 + q * 2 + (a + b + 3)
  refine z4N true (l * 2 + q) (a * 2 + 1) (b * 2 + 2 - p) ((l + q) * 3)
    [(b - 2,1)] (a + 3 + h) s (((2 ^ b - 1) * 2 ^ (a + 3) - 1) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.mass,Queue.weight,s]; omega
  · simp only [zPv,zRv,Queue.mass,Queue.weight]
    have hb2 : b - 2 + 1 = b - 1 := by omega
    have hexp1 : (b - 2 + 1 + 1 + 0) + (a + 3 + h) + (l + q) * 3 = s - 1 := by
      dsimp [s]; omega
    have hexp2 : 0 + (a + 3 + h) + 1 = (a + 3 + 1) + h := by omega
    have hpa := z0h (a + 3)
    have hpb1 := z0h (b - 1)
    have hb_pow : 2 ^ b = 2 ^ (b - 1) * 2 := by
      calc 2 ^ b = 2 ^ ((b - 1) + 1) := by congr 1; omega
        _ = 2 ^ (b - 1) * 2 := Nat.pow_succ 2 (b - 1)
    have hsub : 2 ^ b - 1 = (2 ^ (b - 1) - 1) * 2 + 1 := by omega
    have hp1 : 2 ^ (a + 3 + 1) = 2 ^ (a + 3) * 2 := Nat.pow_succ 2 (a + 3)
    have hring : (2 ^ (b - 1) - 1) * (2 ^ (a + 3) * 2) + 2 ^ (a + 3) =
        (2 ^ b - 1) * 2 ^ (a + 3) := by
      rw [hsub]; ring
    have hbase : (2 ^ (b - 1) - 1) * 2 ^ (a + 3 + 1) + (2 ^ (a + 3) - 1) =
        (2 ^ b - 1) * 2 ^ (a + 3) - 1 := by
      rw [hp1]; omega
    rw [hexp1,hb2,hexp2,z4Y (b - 1) (a + 3 + 1) (a + 3) h (by omega),hbase]
    omega
  · intro k hk
    have hassoc : k * 2 ^ s + 2 ^ (s - 1) + ((((2 ^ b - 1) * 2 ^ (a + 3) - 1) * (1 + h) + h)) =
        k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ b - 1) * 2 ^ (a + 3) - 1) * (1 + h) + h := by omega
    rw [hassoc]
    exact z51 l q h k a b p hqh (by omega) hk ha (by omega) hp
lemma z53 (l q h a b : Nat)
    (hqh : q + h = 1) (hL : 16 <= l * 2 + q) (ha : 1 <= a) (hb : 1 <= b) :
    zDr true (l * 2 + q) (a * 2) (b * 2 + 1) ((l + q) * 3) [(b - 1,a - 1),Queue.danger] h := by
  let s := l * 3 + 2 + q * 2 + (a + b + 1)
  refine z4N true (l * 2 + q) (a * 2) (b * 2 + 1) ((l + q) * 3)
    [(b - 1,a - 1),Queue.danger] h s (((2 ^ b - 1) * 2 ^ (a + 1) + 2) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.danger,Queue.mass,Queue.weight,s]; omega
  · simp only [zPv,Queue.danger,zRv,Queue.mass,Queue.weight]
    have hb1 : b - 1 + 1 = b := by omega
    have hexp1 : (b - 1 + (a - 1) + 1 + (0 + 1 + 1 + 0)) + h + (l + q) * 3 = s - 1 := by
      dsimp [s]; omega
    have hexp2 : (0 + 1 + 1 + 0) + h + (a - 1) = a + 1 + h := by omega
    rw [hb1,hexp1,hexp2]
    rcases h with _ | _ | h
    · simp; ring
    · rw [show a + 1 + 1 = (a + 1) + 1 by omega,Nat.pow_succ]
      simp; ring
    · omega
  · intro k hk
    have hassoc : k * 2 ^ s + 2 ^ (s - 1) + ((((2 ^ b - 1) * 2 ^ (a + 1) + 2) * (1 + h) + h)) =
        k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ b - 1) * 2 ^ (a + 1) + 2) * (1 + h) + h := by omega
    rw [hassoc]
    refine z4W true (l * 2 + q) k _ _ s _ h
      (2 + (a - 1) * 2) (3 + (b - 1) * 2) (l * 3 + 2 + q * 2 + ((b - 1) + 1 + (1 + (a - 1)) + 1))
      ((2 ^ ((b - 1) + 1) - 1) * 2 ^ (1 + (a - 1) + 1) + 2)
      (by omega) (by omega) (by dsimp [s]; omega) ?_ ?_
    · rw [show (b - 1) + 1 = b by omega,show 1 + (a - 1) + 1 = a + 1 by omega]
    · unfold zDc
      exact z3C l q h k (b - 1) (a - 1) ldh hqh (by omega) hk
lemma z54 (l q h b : Nat)
    (hqh : q + h = 1) (hL : 16 <= l * 2 + q) (hb : 2 <= b) :
    zDr true (l * 2 + q) 4 (b * 2 + 2) ((l + q) * 3) [(b,1)] (1 + h) := by
  let s := l * 3 + 2 + q * 2 + (b + 3)
  refine z4N true (l * 2 + q) 4 (b * 2 + 2) ((l + q) * 3)
    [(b,1)] (1 + h) s (((2 ^ b - 1) * 8 + 5) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.mass,Queue.weight,s]; omega
  · simp only [zPv,zRv,Queue.mass,Queue.weight]
    have hexp1 : (b + 1 + 1 + 0) + (1 + h) + (l + q) * 3 = s - 1 := by
      dsimp [s]; omega
    rw [hexp1,Nat.pow_succ 2 b]
    have hpb := z0h b
    rcases h with _ | _ | h
    · simp; omega
    · simp; omega
    · omega
  · intro k hk
    have hassoc : k * 2 ^ s + 2 ^ (s - 1) + ((((2 ^ b - 1) * 8 + 5) * (1 + h) + h)) =
        k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ b - 1) * 8 + 5) * (1 + h) + h := by omega
    rw [hassoc]
    refine z4W true (l * 2 + q) k _ _ s _ h
      (4 + 0 * 2) (4 + (b - 1) * 2) (l * 3 + 2 + q * 2 + ((b - 1) + 0 + 4))
      ((2 ^ ((b - 1) + 1) - 1) * 2 ^ (0 + 3) + 5)
      (by omega) (by omega) (by dsimp [s]; omega) ?_ ?_
    · rw [show (b - 1) + 1 = b by omega]; rfl
    · unfold zDc
      exact z3I l q h k (b - 1) 0 ldh hqh (by omega) hk (by omega)
lemma z55 (l q h a b : Nat)
    (hqh : q + h = 1) (hL : 16 <= l * 2 + q) (ha : 3 <= a) (hb : 2 <= b) :
    zDr true (l * 2 + q) (a * 2) (b * 2 + 2) ((l + q) * 3) [(b - 1,a - 2),Queue.danger] (1 + h) := by
  let s := l * 3 + 2 + q * 2 + (a + b + 1)
  refine z4N true (l * 2 + q) (a * 2) (b * 2 + 2) ((l + q) * 3)
    [(b - 1,a - 2),Queue.danger] (1 + h) s (((2 ^ b - 1) * 2 ^ (a + 1) + 5) * (1 + h) + h) ?_ ?_ ?_
  · simp [zPw,Queue.danger,Queue.mass,Queue.weight,s]; omega
  · simp only [zPv,Queue.danger,zRv,Queue.mass,Queue.weight]
    have hb1 : b - 1 + 1 = b := by omega
    have hexp1 : (b - 1 + (a - 2) + 1 + (0 + 1 + 1 + 0)) + (1 + h) + (l + q) * 3 = s - 1 := by
      dsimp [s]; omega
    have hexp2 : (0 + 1 + 1 + 0) + (1 + h) + (a - 2) = a + 1 + h := by omega
    rw [hb1,hexp1,hexp2]
    rcases h with _ | _ | h
    · simp; ring
    · rw [show a + 1 + 1 = (a + 1) + 1 by omega,Nat.pow_succ]
      simp; ring
    · omega
  · intro k hk
    have hassoc : k * 2 ^ s + 2 ^ (s - 1) + ((((2 ^ b - 1) * 2 ^ (a + 1) + 5) * (1 + h) + h)) =
        k * 2 ^ s + 2 ^ (s - 1) + ((2 ^ b - 1) * 2 ^ (a + 1) + 5) * (1 + h) + h := by omega
    rw [hassoc]
    refine z4W true (l * 2 + q) k _ _ s _ h
      (4 + (a - 2) * 2) (4 + (b - 1) * 2) (l * 3 + 2 + q * 2 + ((b - 1) + (a - 2) + 4))
      ((2 ^ ((b - 1) + 1) - 1) * 2 ^ ((a - 2) + 3) + 5)
      (by omega) (by omega) (by dsimp [s]; omega) ?_ ?_
    · rw [show (b - 1) + 1 = b by omega,show (a - 2) + 3 = a + 1 by omega]
    · unfold zDc
      exact z3I l q h k (b - 1) (a - 2) ldh hqh (by omega) hk (by omega)
def zLi (extra : Bool) (t u : Nat) : Prop :=
  if extra then 3 <= t /\ 6 <= u else
    0 < u /\ (u = 1 -> 0 < t) /\ (u = 2 -> t = 0 \/ 4 <= t) /\
      (t = 1 -> 3 <= u /\ u ≠ 4) /\ (t = 3 -> u ≠ 4)
lemma z56 (extra : Bool) (t u : Nat) (h : Queue.zSi extra t u) :
    zLi extra t u := by
  cases extra with
  | true =>
    simp only [Queue.zSi,Queue.main,zLi,↓reduceIte] at h ⊢
    omega
  | false =>
    simp only [Queue.zSi,Queue.allowed,z1P,Queue.danger,zLi,Bool.false_eq_true,↓reduceIte] at h ⊢
    rcases h with ⟨⟨hu,ht0 | hsep⟩,hne⟩
    · subst ht0
      have hu2 : 2 <= u := by
        rcases u with _ | _ | u
        · omega
        · exfalso; exact hne rfl
        · omega
      omega
    · omega
theorem block_returns_local {extra : Bool} {L t u gap : Nat} {a : List Queue.cell} {E : Nat}
    (hblock : Queue.block extra L t u gap a E) (hL : 16 <= L) (hsafe : zLi extra t u) :
    zDr extra L t u gap a E := by
  revert hL hsafe
  induction hblock with
  | zero2 l q h hqh =>
    intro hL _
    exact z4P l q h hqh hL
  | zero3 l q h hqh =>
    intro hL _
    exact z4Q l q h hqh hL
  | zero5 l q h hqh =>
    intro hL _
    exact z4R l q h hqh hL
  | zero l q h j p hqh hp hj =>
    intro hL _
    exact z4S l q h j p hqh hL hp hj
  | short L t u s e ht hu he hs =>
    intro hL hsafe
    simp [zLi] at hsafe
    exact z4T L t u s e (by omega) (by omega) ht hu he hs
  | one_odd l q h b hqh =>
    intro hL hsafe
    simp [zLi] at hsafe
    have hb : 1 <= b := by omega
    have h1 : b * 2 + 1 = 3 + (b - 1) * 2 := by omega
    have h2 : b + 1 + h = (b - 1) + 2 + h := by omega
    rw [h1,h2]
    exact z4U l q h (b - 1) hqh hL
  | one_even l q h j hqh =>
    intro hL hsafe
    simp [zLi] at hsafe
    have hj : 2 <= j := by omega
    have h1 : j * 2 + 2 = 4 + (j - 1) * 2 := by omega
    have h2 : j - 2 = (j - 1) - 1 := by omega
    rw [h1,h2]
    exact z4V l q h (j - 1) hqh hL (by omega)
  | full l q h a b p e hqh hp he ha hb hfull =>
    intro hL hsafe
    simp [zLi] at hsafe
    exact z4Z l q h a b p e hqh hL hp he ha hb hfull (by omega)
  | split l q h a b p e hqh hp he ha hb hsplit =>
    intro hL hsafe
    simp [zLi] at hsafe
    exact z50 l q h a b p e hqh hL hp he ha hb hsplit (by omega)
  | extra_odd l q h a b p hqh hp =>
    intro hL hsafe
    simp [zLi] at hsafe
    exact z52 l q h a b p hqh hL (by omega) (by omega) hp
  | extra_even_odd l q h a b hqh =>
    intro hL hsafe
    simp [zLi] at hsafe
    exact z53 l q h a b hqh hL (by omega) (by omega)
  | extra_four l q h b hqh =>
    intro hL hsafe
    simp [zLi] at hsafe
    exact z54 l q h b hqh hL (by omega)
  | extra_even_even l q h a b hqh ha =>
    intro hL hsafe
    simp [zLi] at hsafe
    exact z55 l q h a b hqh hL ha (by omega)
theorem block_returns {extra : Bool} {L t u gap : Nat} {a : List Queue.cell} {E : Nat}
    (hblock : Queue.block extra L t u gap a E) (hL : 16 <= L) (hsafe : Queue.zSi extra t u) :
    zDr extra L t u gap a E :=
  block_returns_local hblock hL (z56 extra t u hsafe)
theorem block_step_spec {f g : Queue.frame}
    (hbs : Queue.block_step f g) (hL : 16 <= Queue.width f) (hlen : 3 <= f.cells.length) :
    (config f) [z00]⊢⁺ (config g) := by
  rcases f with ⟨l,E⟩
  rcases hbs with ⟨extra,t,u,r,gap,a,E',hc,hsafe,hblock,rfl⟩
  have hr : r ≠ [] := by
    intro hr0
    subst hr0
    cases hc <;> simp at hlen
  exact z4M E gap a E' hc hr (block_returns hblock hL hsafe)
def z57 (M : Machine zG_ zL_) (c : Cfg zG_ zL_) : Prop :=
  ∀ k,∃ c',multiStep M c k = some c'
lemma z58 {M : Machine zG_ zL_} {c_1 c_3 : Cfg zG_ zL_} (k m : Nat)
    (h : multiStep M c_1 (k + m) = some c_3) :
    ∃ c_2,multiStep M c_1 k = some c_2 := by
  rw [zMa] at h
  cases h1 : multiStep M c_1 k with
  | none => rw [h1] at h; simp at h
  | some c_2 => exact ⟨c_2,rfl⟩
lemma z59 {M : Machine zG_ zL_} {c_1 c_2 : Cfg zG_ zL_}
    (h12 : c_1 [M]⊢* c_2) (h2 : z57 M c_2) : z57 M c_1 := by
  rcases h12 with ⟨m,hm⟩
  intro k
  rcases h2 k with ⟨c_3,hc₃⟩
  have hmk : multiStep M c_1 (k + m) = some c_3 := by
    rw [Nat.add_comm,zMa,hm]
    exact hc₃
  exact z58 k m hmk
lemma z5a {α : Type*} {M : Machine zG_ zL_} (P : α -> Prop) (cfg_of : α -> Cfg zG_ zL_)
    (hstep : ∀ x,P x -> ∃ y,P y /\ ((cfg_of x) [M]⊢⁺ (cfg_of y))) :
    ∀ (k : Nat) (x : α),P x -> ∃ y m,k <= m /\ P y /\ multiStep M (cfg_of x) m = some (cfg_of y)
  | 0,x,hx => ⟨x,0,Nat.le_refl 0,hx,rfl⟩
  | k + 1,x,hx => by
    rcases z5a P cfg_of hstep k x hx with ⟨y₁,m₁,hm₁,hy₁,hrun₁⟩
    rcases hstep y₁ hy₁ with ⟨y₂,hy₂,d,hd_pos,hrun₂⟩
    refine ⟨y₂,m₁ + d,by omega,hy₂,?_⟩
    exact zMt M (cfg_of x) (cfg_of y₁) (cfg_of y₂) m₁ d hrun₁ hrun₂
lemma z5b {α : Type*} {M : Machine zG_ zL_} (P : α -> Prop) (cfg_of : α -> Cfg zG_ zL_)
    (hstep : ∀ x,P x -> ∃ y,P y /\ ((cfg_of x) [M]⊢⁺ (cfg_of y)))
    (x : α) (hx : P x) : z57 M (cfg_of x) := by
  intro k
  rcases z5a P cfg_of hstep k x hx with ⟨y,m,hm,_,hrun⟩
  have hkm : m = k + (m - k) := by omega
  rw [hkm] at hrun
  exact z58 k (m - k) hrun
theorem history_nonhalt {f0 f1 f2 f3 : Queue.frame} (h : Queue.history f0 f1 f2 f3) :
    z57 z00 (config f3) := by
  refine z5b (fun f => ∃ a b c,Queue.history a b c f) config ?_ f3 ⟨f0,f1,f2,h⟩
  intro f ⟨a,b,c,hhist⟩
  rcases Queue.history_progress hhist with ⟨g,hstep,hnext⟩
  refine ⟨g,⟨b,c,f,hnext⟩,?_⟩
  rcases Queue.history_ready hhist with ⟨_,hlen⟩
  exact block_step_spec hstep (Queue.history_width hhist) (by omega)
def z5c : Queue.frame := ⟨[(3,1),Queue.danger],1⟩
def z5d : Queue.frame := ⟨[Queue.danger,(6,13)],1⟩
def z5e : Queue.frame := ⟨[(23,33),(5,2),Queue.danger],1⟩
lemma z5f : (init []) [z00]⊢* (config z5c) := z2l
lemma z5g : (config z5c) [z00]⊢⁺ (config z5d) := by
  refine z4M 1 13 [] 1 (Queue.consume.one 3 1 [Queue.danger]) (by simp) ?_
  exact z4T 7 3 1 15 1 (by omega) (by omega) (by omega) (Or.inl rfl) (by omega) (by omega)
lemma z5h : (config z5d) [z00]⊢⁺ (config z5e) := by
  have hfirst := z4t 6 13 0 0 [] .nil
  dsimp only at hfirst
  have h_init1 : config z5d =
      z18 (LC (0 + 3 + 13 + 6) 0 ldh) ([] +> d +> (z ^ 13) +> (d ^ 6) +> d +> z +> default) := by
    simp only [<- append_assoc]
    rfl
  rw [<- h_init1] at hfirst
  have hlen : 0 + 3 + 13 + 6 = 22 := rfl
  have hval : (0 + 1) * 2 ^ (3 + 13 + 6) - 1 = 2 ^ 22 - 1 := rfl
  rw [hlen,hval] at hfirst
  have hr : zDr true 22 6 13 33 [(5,2),Queue.danger] 1 :=
    z53 11 0 1 3 6 (by omega) (by omega) (by omega) (by omega)
  have h2 := hr (2 ^ 22 - 1) (z1W (z1Y 22))
  have hw := z2m (z1Y 22) 0
  simp only [Nat.mul_zero,Nat.add_zero] at hw
  rw [<- z2K] at hw
  rw [<- hw] at h2
  have h_init2 : z18 (LC (22 + zPw 33 [(5,2),Queue.danger] 1) 0 ldh)
      (z4F 33 [(5,2),Queue.danger] 1 +> (d ^ 22) +> default) = config z5e := by
    unfold config z5e
    simp only [<- append_assoc]
    rfl
  rw [h_init2] at h2
  exact z05 hfirst h2
theorem init_two_frames : (init []) [z00]⊢* (config z5e) :=
  zSt z5f
    (zSt (zPs z5g) (zPs z5h))
namespace Check
inductive certificate where
  | Zero2 (l q h : Nat)
  | Zero3 (l q h : Nat)
  | Zero5 (l q h : Nat)
  | Zero (l q h j p : Nat)
  | Short (L t u s e : Nat)
  | OneOdd (l q h b : Nat)
  | OneEven (l q h j : Nat)
  | Full (l q h a b p e : Nat)
  | Split (l q h a b p e : Nat)
  | ExtraOdd (l q h a b p : Nat)
  | ExtraEvenOdd (l q h a b : Nat)
  | ExtraFour (l q h b : Nat)
  | ExtraEvenEven (l q h a b : Nat)
structure claim where
  extra : Bool
  old_width : Nat
  ones : Nat
  zeros : Nat
  gap : Nat
  residual : List Queue.cell
  tail : Nat
  guard : Bool
def z5i (c : certificate) : claim :=
  match c with
  | .Zero2 l q h => ⟨false,l * 2 + q,0,2,(l + q) * 3 - 1,[],1 + h,decide (q + h = 1)⟩
  | .Zero3 l q h => ⟨false,l * 2 + q,0,3,(l + q) * 3 - 2,[(0,1)],h,decide (q + h = 1)⟩
  | .Zero5 l q h => ⟨false,l * 2 + q,0,5,(l + q) * 3 - 1,[],2 + h,decide (q + h = 1)⟩
  | .Zero l q h j p => ⟨false,l * 2 + q,0,j * 2 + 2 + p,(l + q) * 3 - 1,[(0,j - p)],p + h,
      decide (q + h = 1) && decide (p <= 1) && decide (1 + p <= j)⟩
  | .Short w t u s e => ⟨false,w,t,u,s - 1 - (e + u - 1),[],e + u - 1,
      decide (0 < t) && (decide (u = 1) || decide (u = 2)) && decide (e <= 1) && decide (w * 3 + t + 7 = s * 2 + e)⟩
  | .OneOdd l q h b => ⟨false,l * 2 + q,1,b * 2 + 1,(l + q) * 3,[],b + 1 + h,decide (q + h = 1)⟩
  | .OneEven l q h j => ⟨false,l * 2 + q,1,j * 2 + 2,(l + q) * 3 - 1,[(0,j - 2),(0,1)],h,decide (q + h = 1)⟩
  | .Full l q h a b p e => ⟨false,l * 2 + q,a * 2 + e,b * 2 + 2 - p,(l + q) * 3,[],b + a + 1 + h,
      decide (q + h = 1) && decide (p <= 1) && decide (e <= 1) && decide (1 <= a) && decide (1 <= b) && decide (a + p = e)⟩
  | .Split l q h a b p e => ⟨false,l * 2 + q,a * 2 + e,b * 2 + 2 - p,(l + q) * 3,[(b - 1,a + p - e)],1 - p + e + h,
      decide (q + h = 1) && decide (p <= 1) && decide (e <= 1) && decide (1 <= a) && decide (1 <= b) && decide (e < a + p)⟩
  | .ExtraOdd l q h a b p => ⟨true,l * 2 + q,a * 2 + 1,b * 2 + 2 - p,(l + q) * 3,[(b - 2,1)],a + 3 + h,
      decide (q + h = 1) && decide (p <= 1)⟩
  | .ExtraEvenOdd l q h a b => ⟨true,l * 2 + q,a * 2,b * 2 + 1,(l + q) * 3,[(b - 1,a - 1),(0,1)],h,decide (q + h = 1)⟩
  | .ExtraFour l q h b => ⟨true,l * 2 + q,4,b * 2 + 2,(l + q) * 3,[(b,1)],1 + h,decide (q + h = 1)⟩
  | .ExtraEvenEven l q h a b => ⟨true,l * 2 + q,a * 2,b * 2 + 2,(l + q) * 3,[(b - 1,a - 2),(0,1)],1 + h,
      decide (q + h = 1) && decide (3 <= a)⟩
lemma z5j (c : certificate) (h : (z5i c).guard = true) :
  Queue.block (z5i c).extra (z5i c).old_width (z5i c).ones (z5i c).zeros
    (z5i c).gap (z5i c).residual (z5i c).tail := by
  cases c <;>
    simp only [z5i,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h ⊢
  · exact Queue.block.zero2 _ _ _ h
  · exact Queue.block.zero3 _ _ _ h
  · exact Queue.block.zero5 _ _ _ h
  · exact Queue.block.zero _ _ _ _ _ h.1.1 h.1.2 h.2
  · exact Queue.block.short _ _ _ _ _ h.1.1.1 h.1.1.2 h.1.2 h.2
  · exact Queue.block.one_odd _ _ _ _ h
  · exact Queue.block.one_even _ _ _ _ h
  · exact Queue.block.full _ _ _ _ _ _ _ h.1.1.1.1.1 h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 h.1.2 h.2
  · exact Queue.block.split _ _ _ _ _ _ _ h.1.1.1.1.1 h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 h.1.2 h.2
  · exact Queue.block.extra_odd _ _ _ _ _ _ h.1 h.2
  · exact Queue.block.extra_even_odd _ _ _ _ _ h
  · exact Queue.block.extra_four _ _ _ _ h
  · exact Queue.block.extra_even_even _ _ _ _ _ h.1 h.2
def z5k (x : Bool) (L t u : Nat) : certificate :=
  let l := L / 2
  let q := L % 2
  let h := 1 - q
  let a := t / 2
  let b := (u - 1) / 2
  let p := u % 2
  let e := t % 2
  if x then
    if decide (e = 1) then .ExtraOdd l q h a b p else
    if decide (p = 1) then .ExtraEvenOdd l q h a b else
    if decide (a = 2) then .ExtraFour l q h b else .ExtraEvenEven l q h a b
  else if decide (t = 0) then
    if decide (u = 2) then .Zero2 l q h else
    if decide (u = 3) then .Zero3 l q h else
    if decide (u = 5) then .Zero5 l q h else .Zero l q h ((u - 2) / 2) p
  else if decide (u <= 2) then .Short L t u ((L * 3 + t + 7) / 2) ((L * 3 + t + 7) % 2)
  else if decide (t = 1) then
    if decide (p = 1) then .OneOdd l q h b else .OneEven l q h ((u - 2) / 2)
  else if decide (a + p = e) then .Full l q h a b p e else .Split l q h a b p e
def z5l (x : Bool) (t u : Nat) : Bool :=
  if x then decide (3 <= t) && decide (6 <= u) else
  decide (0 < u) && (decide (u ≠ 1) || decide (0 < t)) &&
    (decide (u ≠ 2) || decide (t = 0) || decide (4 <= t)) &&
    (decide (t ≠ 1) || (decide (3 <= u) && decide (u ≠ 4))) &&
    (decide (t ≠ 3) || decide (u ≠ 4))
lemma z5m (x : Bool) (t u : Nat) (h : z5l x t u = true) :
    zLi x t u := by
  cases x <;>
    simp only [z5l,zLi,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,
      Bool.false_eq_true,↓reduceIte] at h ⊢ <;>
    omega
def z5n (x : Bool) (t u : Nat) (r : List Queue.cell) (f : Queue.frame) (c : certificate) :
    Option Queue.frame :=
  let v := z5i c
  if v.guard && decide (x = v.extra) && decide (Queue.width f = v.old_width) &&
    decide (t = v.ones) && decide (u = v.zeros) && decide (16 <= Queue.width f) && z5l x t u then
    some ⟨r ++ (t + u + (if x then 3 else 1) + f.trailing,v.gap) :: v.residual,v.tail⟩
  else none
lemma z5o (x : Bool) (t u : Nat) (r : List Queue.cell) (f : Queue.frame)
    (c : certificate) (g : Queue.frame)
    (hc : Queue.consume x t u f.cells r) (hr : r ≠ [])
    (ha : z5n x t u r f c = some g) :
    (config f) [z00]⊢⁺ (config g) := by
  unfold z5n at ha
  dsimp only at ha
  split at ha
  · next hcond =>
    injection ha with hg
    subst hg
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hcond
    rcases hcond with ⟨⟨⟨⟨⟨⟨hguard,hx⟩,hw⟩,ht⟩,hu⟩,h16⟩,hloc⟩
    subst hx
    have hloc_in := z5m (z5i c).extra t u hloc
    refine z4M f.trailing (z5i c).gap (z5i c).residual (z5i c).tail hc hr ?_
    rw [hw,ht,hu]
    exact block_returns_local (z5j c hguard) (by omega) (by rw [<- ht,<- hu]; exact hloc_in)
  · cases ha
def next (f : Queue.frame) : Option Queue.frame :=
  match f.cells with
  | [] => none
  | (t,u) :: r =>
    if decide (t = 0) && decide (u = 1) then
      match r with
      | (t',u') :: p :: r' => z5n true t' u' (p :: r') f (z5k true (Queue.width f) t' u')
      | _ => none
    else match r with
      | [] => none
      | _ :: _ => z5n false t u r f (z5k false (Queue.width f) t u)
lemma z5p (f g : Queue.frame) (h : next f = some g) :
    (config f) [z00]⊢⁺ (config g) := by
  unfold next at h
  rcases hf : f.cells with _ | ⟨⟨t,u⟩,r⟩
  · rw [hf] at h; cases h
  · rw [hf] at h
    dsimp only at h
    split at h
    · next hdanger =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hdanger
      rcases hdanger with ⟨rfl,rfl⟩
      rcases r with _ | ⟨⟨t',u'⟩,_ | ⟨p,r'⟩⟩
      · cases h
      · cases h
      · refine z5o true t' u' (p :: r') f _ g ?_ (by simp) h
        rw [hf]
        exact Queue.consume.two t' u' (p :: r')
    · rcases r with _ | ⟨p,r'⟩
      · cases h
      · refine z5o false t u (p :: r') f _ g ?_ (by simp) h
        rw [hf]
        exact Queue.consume.one t u (p :: r')
def z5q (p : Queue.cell) : Bool :=
  decide (3 <= p.1) && decide (p.1 * 8 + 9 <= p.2)
def z5r (p : Queue.cell) : Bool :=
  decide (0 < p.2) &&
    (decide (p.1 = 0) || decide (p.1 * 8 + 9 <= p.2) || decide (p.2 * 8 <= p.1 + 5))
def z5s (p : Queue.cell) (xs : List Queue.cell) : Bool :=
  if decide (p.1 = 0) && decide (p.2 = 1) then
    match xs with | [] => true | q :: _ => z5q q
  else true
def z5t : List Queue.cell -> Bool
  | [] => true
  | p :: r => z5r p && z5s p r && z5t r
lemma z5u (p : Queue.cell) (h : z5q p = true) : Queue.main p := by
  simp only [z5q,Queue.main,Bool.and_eq_true,decide_eq_true_eq] at h ⊢
  exact h
lemma z5v (p : Queue.cell) (h : z5r p = true) : Queue.allowed p := by
  simp only [z5r,Queue.allowed,z1P,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h ⊢
  omega
lemma z5w (p : Queue.cell) (xs : List Queue.cell) (h : z5s p xs = true) :
    Queue.link p xs := by
  rcases p with ⟨t,u⟩
  unfold z5s at h
  intro heq
  injection heq with ht hu
  subst ht; subst hu
  simp only [decide_true,Bool.and_self,↓reduceIte] at h
  cases xs with
  | nil => trivial
  | cons q xs => exact z5u q h
lemma z5x : ∀ (xs : List Queue.cell),z5t xs = true -> Queue.good xs
  | [],_ => Queue.good.nil
  | p :: xs,h => by
    simp only [z5t,Bool.and_eq_true] at h
    exact Queue.good.cons p xs (z5v p h.1.1) (z5w p xs h.1.2) (z5x xs h.2)
def z5y : List Queue.cell -> List Queue.cell -> Bool
  | [],_ => true
  | (t,u) :: xs,(a,b) :: ys => decide (t = a) && decide (u = b) && z5y xs ys
  | _,_ => false
lemma z5z : ∀ (xs ys : List Queue.cell),z5y xs ys = true -> ∃ a,ys = xs ++ a
  | [],ys,_ => ⟨ys,rfl⟩
  | (t,u) :: xs,[],h => by cases h
  | (t,u) :: xs,(a,b) :: ys,h => by
    simp only [z5y,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with ⟨⟨rfl,rfl⟩,hpref⟩
    rcases z5z xs ys hpref with ⟨r,rfl⟩
    exact ⟨r,rfl⟩
def z5A (xs ys : List Queue.cell) : Bool :=
  z5y (xs.drop 1) ys || z5y (xs.drop 2) ys
lemma z5B (xs ys : List Queue.cell) (h : z5A xs ys = true) :
    Queue.advance xs ys := by
  simp only [z5A,Bool.or_eq_true] at h
  rcases h with h1 | h2
  · rcases z5z (xs.drop 1) ys h1 with ⟨a,rfl⟩
    exact ⟨1,a,by omega,rfl⟩
  · rcases z5z (xs.drop 2) ys h2 with ⟨a,rfl⟩
    exact ⟨2,a,by omega,rfl⟩
def z5C (f g : Queue.frame) : Bool :=
  z5A f.cells g.cells && decide (Queue.width f * 5 <= Queue.width g * 2) &&
    decide (f.cells.length <= g.cells.length)
lemma z5D (f g : Queue.frame) (h : z5C f g = true) : Queue.edge f g := by
  simp only [z5C,Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨z5B f.cells g.cells h.1.1,h.1.2,h.2⟩
def z5E (f0 f1 f2 f3 : Queue.frame) : Bool :=
  z5C f0 f1 && z5C f1 f2 && z5C f2 f3 &&
    decide (16 <= Queue.width f0) && decide (9 <= f0.cells.length) &&
    decide (f3.trailing <= Queue.width f0 + 8) && z5t f3.cells
lemma z5F (f0 f1 f2 f3 : Queue.frame) (h : z5E f0 f1 f2 f3 = true) :
    Queue.history f0 f1 f2 f3 := by
  simp only [z5E,Bool.and_eq_true,decide_eq_true_eq] at h
  exact {
    edge01 := z5D f0 f1 h.1.1.1.1.1.1
    edge12 := z5D f1 f2 h.1.1.1.1.1.2
    edge23 := z5D f2 f3 h.1.1.1.1.2
    old_width := h.1.1.1.2
    old_count := h.1.1.2
    tail_bound := h.1.2
    current_good := z5x f3.cells h.2
  }
def run : Nat -> Queue.frame -> Queue.frame -> Queue.frame -> Queue.frame -> Bool
  | 0,f0,f1,f2,f3 => z5E f0 f1 f2 f3
  | fuel + 1,_f0,f1,f2,f3 =>
    match next f3 with
    | some f4 => run fuel f1 f2 f3 f4
    | none => false
theorem run_spec : ∀ (fuel : Nat) (f0 f1 f2 f3 : Queue.frame),
    run fuel f0 f1 f2 f3 = true -> z57 z00 (config f3)
  | 0,f0,f1,f2,f3,h => history_nonhalt (z5F f0 f1 f2 f3 h)
  | fuel + 1,_f0,f1,f2,f3,h => by
    unfold run at h
    cases hnext : next f3 with
    | none => rw [hnext] at h; cases h
    | some f4 =>
      rw [hnext] at h
      exact z59 (zPs (z5p f3 f4 hnext))
        (run_spec fuel f1 f2 f3 f4 h)
def z5G : Queue.frame := z5e
set_option maxRecDepth 4000000 in
lemma seed_nonhalt : z57 z00 (config z5G) :=
  run_spec 216 z5G z5G z5G z5G (by decide +kernel)
end Check
theorem tm51_nonhalt : z57 z00 (init []) :=
  z59 init_two_frames Check.seed_nonhalt
def z5H : Dir -> Dir
  | .left => .right
  | .right => .left
def z5I (T : Tape (Fin 2)) : Tape (Fin 2) :=
  ⟨T.1,T.right,T.left⟩
def z5J (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q,z5I c.tape⟩
lemma z5K (q : Fin 6) (s : Fin 2) :
    target_tm q s =
      (z00 q s).map (fun ⟨q',Stmt.write a d⟩ => ⟨q',Stmt.write a (z5H d)⟩) := by
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1 | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl
lemma z5L (T : Tape (Fin 2)) (a : Fin 2) :
    (z5I T).write a = z5I (T.write a) := rfl
lemma z5M (T : Tape (Fin 2)) (d : Dir) :
    (z5I T).move (z5H d) = z5I (T.move d) := by
  cases d <;> rfl
lemma z5N (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (z5J c) = (step z00 c).map z5J := by
  rcases c with ⟨_ | q,T⟩
  · rfl
  · dsimp [z5J,step]
    have htm := z5K q T.1
    have hhead : (z5I T).1 = T.1 := rfl
    rw [hhead,htm]
    cases z00 q T.1 with
    | none => rfl
    | some val =>
      rcases val with ⟨q',⟨a,d⟩⟩
      dsimp [Option.map,z5J]
      rw [z5L,z5M]
lemma z5O : ∀ (n : Nat) (c : Cfg (Fin 2) (Fin 6)),
    multiStep target_tm (z5J c) n = (multiStep z00 c n).map z5J
  | 0,c => rfl
  | n + 1,c => by
    rw [zMs,zMs,z5O n c]
    cases multiStep z00 c n with
    | none => rfl
    | some c' =>
      dsimp [Option.map,Option.bind]
      exact z5N c'

end Solution

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000
open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg ⟨n,hn⟩
  have hinit : (init [] : Cfg (Fin 2) (Fin 6)) = z5J (init []) := rfl
  rcases tm51_nonhalt (n + 1) with ⟨c',hc'⟩
  have hstep : multiStep target_tm (init []) (n + 1) = some (z5J c') := by
    rw [hinit,z5O (n + 1) (init []),hc']
    rfl
  rw [zMs,hn] at hstep
  dsimp [Option.bind] at hstep
  rw [hstep]
  rfl

end BusyBeaver.M_1RB1LF_1LC1RB_1RE1LD_1LB0LC_1LA0RE_1LDHHH
