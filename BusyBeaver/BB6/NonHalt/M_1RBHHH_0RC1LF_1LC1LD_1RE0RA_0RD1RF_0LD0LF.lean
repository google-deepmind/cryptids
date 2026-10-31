/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RBHHH_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB---_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => none
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 5, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
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
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
@[simp] lemma zMz (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine zG_ zL_) (config : Cfg zG_ zL_) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep,Function.iterate_succ',Function.comp_apply,multiStep]
@[simp] lemma z00 : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : zB).head = 0 := rfl
@[simp] lemma zDt : (default : zB).tail = default := rfl
@[simp] lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[simp] lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[simp] lemma append_assoc (l₁ l₂ : zF) (s : zB) :
    (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s) := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih => simp [ih]
set_option maxHeartbeats 8000000
@[simp] lemma zPz (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma z01 (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
lemma pow_add (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp [Nat.zero_add]
  | succ m ih => simp [z01,Nat.succ_add,ih,List.append_assoc]
lemma z02 (l : List α) (n : Nat) : l ^ n ++ l = l ^ (n + 1) := by
  induction n with
  | zero => simp [z01]
  | succ n ih => simp [z01,List.append_assoc,ih]
lemma z03 (x : α) (n : Nat) : ([x] : List α) ^ (n * 2) = [x,x] ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h1,pow_add,ih]
    rfl
lemma z04 (x : α) (n : Nat) (ys : List α) : [x] ^ n ++ x :: ys = [x] ^ (n + 1) ++ ys := by
  have h : x :: ys = [x] ++ ys := rfl
  rw [h,<- List.append_assoc,z02]
lemma zSm {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
lemma z05 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1,by decide,zSm tm c_1 c_2 h⟩
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
lemma z06 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} (c : Cfg zG_ zL_) : c [tm]⊢* c := ⟨0,rfl⟩
lemma zPs {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 : Cfg zG_ zL_} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n,_,hn⟩ := h; exact ⟨n,hn⟩
lemma zSt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢* c_3 := by
  obtain ⟨n,hn⟩ := h₁; obtain ⟨m,hm⟩ := h₂
  exact ⟨n + m,zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z07 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,n_pos,hn⟩ := h₁; obtain ⟨m,hm⟩ := h₂
  exact ⟨n + m,lt_of_lt_of_le n_pos (Nat.le_add_right n m),zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z08 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,hn⟩ := h₁; obtain ⟨m,m_pos,hm⟩ := h₂
  exact ⟨n + m,lt_of_lt_of_le m_pos (Nat.le_add_left m n),zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 :=
  z07 h₁ (zPs h₂)
lemma z09 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  z07 (z05 tm c_1 c_2 h₁) h₂
lemma z0a {c_1 c_1' c_2 c_2' : Cfg (Fin 2) (Fin 6)}
    (h : c_1 [target_tm]⊢* c_2) (h₁ : c_1 = c_1') (h₂ : c_2 = c_2') :
    c_1' [target_tm]⊢* c_2' := h₁ ▸ h₂ ▸ h
lemma z0b {c_1 c_1' c_2 c_2' : Cfg (Fin 2) (Fin 6)}
    (h : c_1 [target_tm]⊢⁺ c_2) (h₁ : c_1 = c_1') (h₂ : c_2 = c_2') :
    c_1' [target_tm]⊢⁺ c_2' := h₁ ▸ h₂ ▸ h
macro "finish" : tactic =>
  `(tactic| exact ⟨0,rfl⟩)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z09 (by (try simp only [Turing.ListBlank.head_cons,zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,z00,zDh,zDt,append_cons,append_nil])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))
abbrev z4 : zF := [0,0,0,0]
inductive Token where
  | a
  | b
deriving DecidableEq
@[simp] def tk : Token -> zF
  | .a => [1,0]
  | .b => [1,0,0]
@[simp] def rr : Token -> zF
  | .a => [1,0]
  | .b => [1,1,0]
@[simp] def em : Token -> zF
  | .a => [1,0]
  | .b => [0,1,0]
@[simp] def enc : List Token -> zF
  | [] => []
  | t :: ts => tk t ++ enc ts
@[simp] def ems : List Token -> zF
  | [] => []
  | t :: ts => em t ++ ems ts
@[simp] def z0c : List Token -> zB -> zB
  | [],l => l
  | t :: ts,l => z0c ts (l <+ rr t)
@[simp] lemma z0d (xs ys : List Token) : enc (xs ++ ys) = enc xs ++ enc ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih,List.append_assoc]
@[simp] lemma z0e (xs ys : List Token) : ems (xs ++ ys) = ems xs ++ ems ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih,List.append_assoc]
lemma z0f (ts : List Token) (n : Nat) : enc (ts ^ n) = (enc ts) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : ts ^ (n + 1) = ts ++ ts ^ n := rfl
    rw [h,z0d,ih,z01]
lemma z0g (ts : List Token) (n : Nat) : ems (ts ^ n) = (ems ts) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : ts ^ (n + 1) = ts ++ ts ^ n := rfl
    rw [h,z0e,ih,z01]
lemma z0h (l r : zB) :
    (l {{D}}> [1,0,0,1,0,1] +> r) [target_tm]⊢*
    ((l <+ rr .a) {{D}}> [1,0,0,1] +> r) := by
  dsimp [rr,D]; execute
lemma z0i (l r : zB) :
    (l {{D}}> [1,0,0,1,0,0] +> r) [target_tm]⊢*
    ((l <+ rr .b) {{D}}> [1,0,0] +> r) := by
  dsimp [rr,D]; execute
lemma ls (t : Token) (l r : zB) :
    ((l <+ rr t) <{{D}} z4 +> r) [target_tm]⊢*
    (l <{{D}} z4 +> em t +> r) := by
  cases t <;> (dsimp [rr,em,z4,D]; execute)
lemma z0j (l r : zB) :
    ((l <+ [1,1,1,0]) <{{D}} z4 +> r) [target_tm]⊢*
    (l <{{D}} z4 +> [0,0,1,0] +> r) := by
  dsimp [z4,D]; execute
lemma le1 (l r : zB) :
    (l {{D}}> [0,0,0,0,0,1,0,1] +> r) [target_tm]⊢*
    ((l <+ [0,1,0,1]) {{D}}> [1,0,0,1] +> r) := by
  dsimp [D]; execute
lemma le0 (l r : zB) :
    (l {{D}}> [0,0,0,0,0,1,0,0] +> r) [target_tm]⊢*
    ((l <+ [1,0,1,0,1]) {{D}}> [1,0,0] +> r) := by
  dsimp [D]; execute
lemma evG (l r : zB) :
    (l {{D}}> [1,0,0,1,1] +> r) [target_tm]⊢⁺
    (l <{{D}} z4 +> [0] +> r) := by
  dsimp [z4,D]; execute
lemma evT (l r : zB) :
    ((l <+ rr .b) {{D}}> [1,0,0,0] +> r) [target_tm]⊢⁺
    (l <{{D}} z4 +> [0,0,1] +> r) := by
  dsimp [rr,z4,D]; execute
lemma z0k (ts : List Token) (l r : zB) :
    (l {{D}}> [1,0,0] +> enc ts +> [1] +> r) [target_tm]⊢*
    (z0c ts l {{D}}> [1,0,0,1] +> r) := by
  induction ts generalizing l r with
  | nil => exact z06 _
  | cons t ts ih =>
    cases t with
    | a =>
      cases ts with
      | nil => exact z0h l r
      | cons t2 ts2 =>
        cases t2 with
        | a => exact zSt (z0h l ([0] +> enc ts2 +> [1] +> r)) (ih (l <+ rr .a) r)
        | b => exact zSt (z0h l ([0,0] +> enc ts2 +> [1] +> r)) (ih (l <+ rr .a) r)
    | b =>
      exact zSt (z0i l (enc ts +> [1] +> r)) (ih (l <+ rr .b) r)
lemma z0l (ts : List Token) (l r : zB) :
    (l {{D}}> [1,0,0] +> enc (ts ++ [.b]) +> r) [target_tm]⊢*
    ((z0c ts l <+ rr .b) {{D}}> [1,0,0] +> r) := by
  have h1 := z0k ts l ([0,0] +> r)
  have h2 := z0i (z0c ts l) r
  refine zSt (z0a h1 ?_ rfl) h2
  simp
lemma z0m (ts : List Token) (l r : zB) :
    (z0c ts l <{{D}} z4 +> r) [target_tm]⊢*
    (l <{{D}} z4 +> ems ts +> r) := by
  induction ts generalizing l r with
  | nil => exact z06 _
  | cons t ts ih =>
    cases t <;> exact zSt (ih (l <+ _) r) (ls _ l (ems ts +> r))
lemma z0n (ts : List Token) (l r : zB) :
    (l {{D}}> [1,0,0] +> enc ts +> [1,1] +> r) [target_tm]⊢⁺
    (l <{{D}} z4 +> ems ts +> [0] +> r) := by
  have h1 := z0k ts l ([1] +> r)
  have h2 := evG (z0c ts l) r
  have h3 := z0m ts l ([0] +> r)
  exact z08 h1 (z07 h2 h3)
lemma z0o (ts : List Token) (l r : zB) :
    (l {{D}}> [1,0,0] +> enc (ts ++ [.b]) +> [0] +> r) [target_tm]⊢⁺
    (l <{{D}} z4 +> ems ts +> [0,0,1] +> r) := by
  have h1 := z0l ts l ([0] +> r)
  have h2 := evT (z0c ts l) r
  have h3 := z0m ts l ([0,0,1] +> r)
  exact z08 h1 (z07 h2 h3)
lemma z0p (xs : List Token) : ems (.a :: xs) ++ [0] = enc (xs ++ [.b]) := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
    have ih' : (1 : Fin 2) :: 0 :: (ems xs ++ [0]) = enc (xs ++ [.b]) := ih
    cases t <;> {
      dsimp [ems,em,enc,tk]
      rw [<- ih']
    }
lemma z0q (xs : List Token) : ems (.b :: xs) ++ [0] = 0 :: enc (xs ++ [.b]) := by
  have h := congrArg (List.cons (0 : Fin 2)) (z0p xs)
  exact h
lemma z0r (ts : List Token) (r : zB) :
    ∃ r',enc ts +> [1] +> r = [1] +> r' := by
  cases ts with
  | nil => exact ⟨r,rfl⟩
  | cons t ts => cases t <;> exact ⟨_,rfl⟩
lemma z0s (ts : List Token) (t : Token) (r : zB) :
    ∃ r',enc (ts ++ [t]) +> r = [1] +> r' := by
  cases ts with
  | nil => cases t <;> exact ⟨_,rfl⟩
  | cons x ts => cases x <;> exact ⟨_,rfl⟩
lemma z0t (ys : List Token) (l r : zB) :
    (l {{D}}> [0] +> z4 +> enc (.a :: ys) +> [1,1] +> r) [target_tm]⊢⁺
    ((l <+ [1,0,1]) {{D}}> [0] +> z4 +> ems ys +> [0] +> r) := by
  obtain ⟨r',hr'⟩ := z0r ys ([1] +> r)
  have h1 := le1 l r'
  have h2 := z0n ys (l <+ [0,1,0,1]) r
  refine z08 (z0a h1 ?_ rfl) (z0b h2 ?_ (by simp))
  · simp [z4,enc,tk] at hr' ⊢; rw [hr']
  · simp at hr' ⊢; rw [hr']
lemma z0u (ys : List Token) (l r : zB) :
    (l {{D}}> [0] +> z4 +> enc (.a :: (ys ++ [.b])) +> [0] +> r) [target_tm]⊢⁺
    ((l <+ [1,0,1]) {{D}}> [0] +> z4 +> ems ys +> [0,0,1] +> r) := by
  obtain ⟨r',hr'⟩ := z0s ys .b ([0] +> r)
  have h1 := le1 l r'
  have h2 := z0o ys (l <+ [0,1,0,1]) r
  refine z08 (z0a h1 ?_ rfl) (z0b h2 ?_ (by simp))
  · simp [z4,enc,tk] at hr' ⊢; rw [hr']
  · simp at hr' ⊢; rw [hr']
lemma z0v (j : Nat) (r : zB) :
    ((default <+ ([1,0,1] ^ j) <+ [1]) <{{D}} z4 +> r) [target_tm]⊢*
    (default {{D}}> [0] +> z4 +> [1,0] +> ([0,1,0] ^ j) +> r) := by
  induction j generalizing r with
  | zero =>
    dsimp [z4,D]; execute
  | succ j ih =>
    have h1 := ls .b (default <+ ([1,0,1] ^ j) <+ [1]) r
    have h2 := ih ([0,1,0] +> r)
    refine zSt h1 (z0a h2 rfl ?_)
    rw [<- z02 [0,1,0] j]; simp
lemma z0w (k : Nat) (l r : zB) :
    ((l <+ ([1,0,1,0,1] ^ k) <+ [1]) <{{D}} z4 +> r) [target_tm]⊢*
    ((l <+ [1]) <{{D}} z4 +> ([1,0,0,1,0] ^ k) +> r) := by
  induction k generalizing l r with
  | zero => exact z06 _
  | succ k ih =>
    have h1 := ls .b (l <+ ([1,0,1,0,1] ^ k) <+ [1,0,1]) r
    have h2 := ls .a (l <+ ([1,0,1,0,1] ^ k) <+ [1]) ([0,1,0] +> r)
    have h3 := ih l ([1,0,0,1,0] +> r)
    refine zSt h1 (zSt h2 (z0a h3 rfl ?_))
    rw [<- z02 [1,0,0,1,0] k]; simp
lemma z0x (j : Nat) (r : zB) :
    ((default <+ ([1,0,1] ^ j) <+ [1,0,1,0,1]) <{{D}} z4 +> r) [target_tm]⊢*
    (default {{D}}> [0] +> z4 +> [1,0] +> ([0,1,0] ^ j) +> [1,0,1,0] +> r) := by
  have h1 := ls .a (default <+ ([1,0,1] ^ j) <+ [1,0,1]) r
  have h2 := ls .a (default <+ ([1,0,1] ^ j) <+ [1]) ([1,0] +> r)
  have h3 := z0v j ([1,0,1,0] +> r)
  exact zSt h1 (zSt h2 h3)
lemma z0y (j : Nat) (r : zB) :
    [1,0] +> ([0,1,0] ^ j) +> r = ([1,0,0] ^ j) +> [1,0] +> r := by
  induction j generalizing r with
  | zero => rfl
  | succ j ih =>
    have h := ih r
    simp only [z01,append_assoc,append_cons,append_nil] at h ⊢
    rw [h]
lemma z0z (j : Nat) (r : zB) :
    (1 : Fin 2) >> 0 >> (([0,1,0] ^ j) +> r) = ([1,0,0] ^ j) +> (1 >> 0 >> r) :=
  z0y j r
lemma z0A (k : Nat) (r : zB) :
    [1,0] +> ([1,0,0,1,0] ^ k) +> r = ([1,0,1,0,0] ^ k) +> [1,0] +> r := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    have h := ih r
    simp only [z01,append_assoc,append_cons,append_nil] at h ⊢
    rw [h]
lemma z0B (n : Nat) (r : zB) :
    ([0,1,0] ^ n) +> [0] +> r = [0] +> ([1,0,0] ^ n) +> r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have h := ih r
    simp only [z01,append_assoc,append_cons,append_nil] at h ⊢
    rw [h]
lemma z0C (xs : List Token) (r : zB) :
    [1,0] +> ems xs +> [0] +> r = enc (xs ++ [.b]) +> r := by
  have h := congrArg (fun l => l +> r) (z0p xs)
  dsimp [ems,em] at h
  simp only [append_assoc,append_cons,append_nil] at h ⊢
  exact h
lemma z0D (xs : List Token) (r : zB) :
    (1 : Fin 2) >> (0 : Fin 2) >> (ems xs +> ((0 : Fin 2) >> r)) = enc (xs ++ [.b]) +> r :=
  z0C xs r
lemma z0E (xs : List Token) (r : zB) :
    [0,1,0] +> ems xs +> [0] +> r = [0] +> enc (xs ++ [.b]) +> r := by
  have h := z0C xs r
  simp only [append_cons,append_nil] at h ⊢
  rw [h]
inductive Ev : List Token -> zF -> List Token -> zF -> Prop
  | EvG (ts : List Token) (m : zF) : Ev ts ([1,1] ++ m) (ts ++ [.b]) m
  | EvT (ts : List Token) (m : zF) : Ev (ts ++ [.b]) (0 :: m) (ts ++ [.b]) (0 :: 1 :: m)
lemma z0F (p ts : List Token) (m : zF) (ts' : List Token) (m' : zF)
    (h : Ev ts m ts' m') : Ev (p ++ ts) m (p ++ ts') m' := by
  cases h with
  | EvG => rw [<- List.append_assoc]; exact Ev.EvG (p ++ ts) m'
  | EvT ts m0 => rw [<- List.append_assoc]; exact Ev.EvT (p ++ ts) m0
lemma z0G (ts : List Token) (m : zF) (ts' : List Token) (m' : zF)
    (l r : zB) (h : Ev ts m ts' m') :
    (l {{D}}> [0] +> z4 +> enc (.a :: .a :: ts) +> m +> r) [target_tm]⊢⁺
    ((l <+ [1,0,1]) {{D}}> [0] +> z4 +> enc ts' +> m' +> r) := by
  cases h with
  | EvG =>
    have h1 := z0t (.a :: ts) l (m' +> r)
    refine z0b h1 (by simp) ?_
    dsimp [ems,em]
    simp only [append_assoc,append_cons,append_nil,z0D]
  | EvT ts m0 =>
    have h1 := z0u (.a :: ts) l (m0 +> r)
    refine z0b h1 (by simp) ?_
    dsimp [ems,em]
    simp only [append_assoc,append_cons,append_nil,z0D]
lemma z0H (j : Nat) (ts : List Token) (m : zF) (ts' : List Token) (m' : zF)
    (r : zB) (h : Ev ts m ts' m') :
    ((default <+ ([1,0,1] ^ j)) {{D}}> [0] +> z4 +> enc (.b :: ts) +> m +> r) [target_tm]⊢⁺
    (default {{D}}> [0] +> z4 +> enc ([.b] ^ j ++ [.a,.a] ++ ts') +> m' +> r) := by
  cases h with
  | EvG =>
    have h1 := le0 (default <+ ([1,0,1] ^ j)) (enc ts +> [1,1] +> m' +> r)
    have h2 := z0n ts (default <+ ([1,0,1] ^ j) <+ [1,0,1,0,1]) (m' +> r)
    have h3 := z0x j (ems ts +> [0] +> m' +> r)
    refine z08 (z0a h1 (by simp [z4,enc,tk]) rfl) (z07 h2 (z0a h3 rfl ?_))
    rw [z0d,z0d,z0f]; dsimp [enc,tk]
    simp only [append_assoc,append_cons,append_nil,z0z,z0D]
  | EvT ts m0 =>
    have h1 := le0 (default <+ ([1,0,1] ^ j)) (enc (ts ++ [.b]) +> [0] +> m0 +> r)
    have h2 := z0o ts (default <+ ([1,0,1] ^ j) <+ [1,0,1,0,1]) (m0 +> r)
    have h3 := z0x j (ems ts +> [0,0,1] +> m0 +> r)
    refine z08 (z0a h1 (by simp [z4,enc,tk]) rfl) (z07 h2 (z0a h3 rfl ?_))
    rw [z0d,z0d,z0f]; dsimp [enc,tk]
    simp only [append_assoc,append_cons,append_nil,z0z,z0D]
def Evs : Nat -> List Token -> zF -> List Token -> zF -> Prop
  | 0,ts,m,ts',m' => ts' = ts /\ m' = m
  | n + 1,ts,m,ts',m' => ∃ ts1 m1,Ev ts m ts1 m1 /\ Evs n ts1 m1 ts' m'
lemma z0I (n : Nat) (p ts : List Token) (m : zF) (ts' : List Token) (m' : zF)
    (h : Evs n ts m ts' m') : Evs n (p ++ ts) m (p ++ ts') m' := by
  induction n generalizing ts m ts' m' with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact ⟨rfl,rfl⟩
  | succ n ih =>
    obtain ⟨ts1,m1,h1,h2⟩ := h
    exact ⟨p ++ ts1,m1,z0F p ts m ts1 m1 h1,ih ts1 m1 ts' m' h2⟩
lemma z0J (n k : Nat) (ts : List Token) (m : zF) (ts' : List Token) (m' : zF)
    (h : Evs (n + k) ts m ts' m') :
    ∃ ts1 m1,Evs n ts m ts1 m1 /\ Evs k ts1 m1 ts' m' := by
  induction n generalizing ts m with
  | zero =>
    rw [Nat.zero_add] at h
    exact ⟨ts,m,⟨rfl,rfl⟩,h⟩
  | succ n ih =>
    rw [Nat.succ_add] at h
    obtain ⟨ts0,m0,h0,h1⟩ := h
    obtain ⟨ts1,m1,h2,h3⟩ := ih ts0 m0 h1
    exact ⟨ts1,m1,⟨ts0,m0,h0,h2⟩,h3⟩
lemma z0K (t j : Nat) (ts : List Token) (m : zF) (ts' : List Token) (m' : zF)
    (r : zB) (h : Evs (t + 1) ts m ts' m') :
    ((default <+ ([1,0,1] ^ j)) {{D}}> [0] +> z4 +> enc ([.a,.a] ^ t ++ .b :: ts) +> m +> r) [target_tm]⊢⁺
    (default {{D}}> [0] +> z4 +> enc ([.b] ^ (j + t) ++ [.a,.a] ++ ts') +> m' +> r) := by
  induction t generalizing j ts m ts' m' with
  | zero =>
    obtain ⟨ts1,m1,h1,rfl,rfl⟩ := h
    simp only [Nat.add_zero,zPz,List.nil_append]
    exact z0H j ts m ts' m' r h1
  | succ t ih =>
    obtain ⟨ts1,m1,h1,h2⟩ := h
    have hp : Ev ([.a,.a] ^ t ++ [.b] ++ ts) m ([.a,.a] ^ t ++ [.b] ++ ts1) m1 := by
      rw [List.append_assoc,List.append_assoc]
      exact z0F ([.a,.a] ^ t) (.b :: ts) m (.b :: ts1) m1 (z0F [.b] ts m ts1 m1 h1)
    have hs1 := z0G ([.a,.a] ^ t ++ [.b] ++ ts) m ([.a,.a] ^ t ++ [.b] ++ ts1) m1 (default <+ ([1,0,1] ^ j)) r hp
    have hs2 := ih (j + 1) ts1 m1 ts' m' h2
    refine zPt (z0b hs1 ?_ rfl) (z0b hs2 ?_ ?_)
    · simp [z01,List.append_assoc]
    · have hj : ([1,0,1] : zF) ^ (j + 1) = [1,0,1] ++ ([1,0,1] ^ j) := rfl
      rw [hj]; simp [List.append_assoc]
    · have hj : j + 1 + t = j + (t + 1) := by omega
      rw [hj]
lemma z0L (n : Nat) (ts : List Token) (k : Nat) (m : zF) :
    Evs n ts ([1,1] ^ (n + k) ++ m) (ts ++ [.b] ^ n) ([1,1] ^ k ++ m) := by
  induction n generalizing ts with
  | zero =>
    simp [Evs]
  | succ n ih =>
    refine ⟨ts ++ [.b],[1,1] ^ (n + k) ++ m,?_,?_⟩
    · have h1 : (n + 1 + k) = 1 + (n + k) := by omega
      rw [h1,pow_add]
      exact Ev.EvG ts ([1,1] ^ (n + k) ++ m)
    · have h2 := ih (ts ++ [.b])
      have h3 : (ts ++ [.b]) ++ [.b] ^ n = ts ++ [.b] ^ (n + 1) := by
        rw [List.append_assoc]; rfl
      rw [h3] at h2
      exact h2
lemma z0M (n : Nat) (ts : List Token) (k : Nat) (m : zF) :
    Evs n (ts ++ [.b]) (0 :: ([1] ^ k ++ m)) (ts ++ [.b]) (0 :: ([1] ^ (n + k) ++ m)) := by
  induction n generalizing k with
  | zero =>
    simp [Evs]
  | succ n ih =>
    refine ⟨ts ++ [.b],0 :: 1 :: ([1] ^ k ++ m),Ev.EvT ts ([1] ^ k ++ m),?_⟩
    have h1 : (1 : Fin 2) :: ([1] ^ k ++ m) = [1] ^ (k + 1) ++ m := rfl
    rw [h1]
    have h2 : n + (k + 1) = n + 1 + k := by omega
    have h3 := ih (k + 1)
    rw [h2] at h3
    exact h3
inductive Num : Nat -> Nat -> Nat -> List Token -> Prop
  | Num_O : Num 0 0 0 []
  | Num_0 (w n p : Nat) (xs : List Token) : Num w n p xs -> Num (w + 1) (n * 2) p (.b :: xs)
  | Num_1 (w n p : Nat) (xs : List Token) : Num w n p xs -> Num (w + 1) (n * 2 + 1) (p + 1) (.a :: .a :: xs)
lemma z0N {w n p : Nat} {xs : List Token} (h : Num w n p xs) : n < 2 ^ w /\ p <= w := by
  induction h with
  | Num_O => simp
  | Num_0 w n p xs _ ih =>
    have : 2 ^ (w + 1) = 2 ^ w * 2 := by rw [Nat.pow_succ]
    omega
  | Num_1 w n p xs _ ih =>
    have : 2 ^ (w + 1) = 2 ^ w * 2 := by rw [Nat.pow_succ]
    omega
lemma z0O {w n p : Nat} {xs : List Token} (h : Num w n p xs) :
    ∀ {w' m q : Nat} {ys : List Token},Num w' m q ys -> w' = w -> m = n -> p = q /\ xs = ys := by
  induction h with
  | Num_O =>
    intro w' m q ys h' hw hm
    cases h' with
    | Num_O => exact ⟨rfl,rfl⟩
    | Num_0 _ _ _ _ _ => omega
    | Num_1 _ _ _ _ _ => omega
  | Num_0 w n p xs h ih =>
    intro w' m q ys h' hw hm
    cases h' with
    | Num_O => omega
    | Num_0 w0 n0 q0 ys0 h0 =>
      obtain ⟨rfl,rfl⟩ := ih h0 (by omega) (by omega)
      exact ⟨rfl,rfl⟩
    | Num_1 w0 n0 q0 ys0 h0 =>
      omega
  | Num_1 w n p xs h ih =>
    intro w' m q ys h' hw hm
    cases h' with
    | Num_O => omega
    | Num_0 w0 n0 q0 ys0 h0 =>
      omega
    | Num_1 w0 n0 q0 ys0 h0 =>
      obtain ⟨rfl,rfl⟩ := ih h0 (by omega) (by omega)
      exact ⟨rfl,rfl⟩
lemma z0P {w n p : Nat} {xs : List Token} (h : Num w n p xs)
    {q : Nat} {ys : List Token} (h' : Num w n q ys) : p = q /\ xs = ys :=
  z0O h h' rfl rfl
lemma z0Q {w w' n n' p p' : Nat} {xs xs' : List Token}
    (h : Num w n p xs) (hw : w = w') (hn : n = n') (hp : p = p') (hxs : xs = xs') :
    Num w' n' p' xs' := hw ▸ hn ▸ hp ▸ hxs ▸ h
lemma z0R {w n p : Nat} {xs : List Token} {v m q : Nat} {ys : List Token}
    (h1 : Num w n p xs) (h2 : Num v m q ys) :
    Num (w + v) (n + 2 ^ w * m) (p + q) (xs ++ ys) := by
  induction h1 with
  | Num_O =>
    refine z0Q h2 (by omega) (by simp) (by omega) rfl
  | Num_0 w n p xs h ih =>
    refine z0Q (Num.Num_0 (w + v) (n + 2 ^ w * m) (p + q) (xs ++ ys) ih) (by omega) ?_ rfl rfl
    rw [Nat.pow_succ,Nat.add_mul,Nat.mul_right_comm]
  | Num_1 w n p xs h ih =>
    refine z0Q (Num.Num_1 (w + v) (n + 2 ^ w * m) (p + q) (xs ++ ys) ih) (by omega) ?_ (by omega) rfl
    rw [Nat.pow_succ,Nat.add_mul,Nat.mul_right_comm]; omega
lemma z0S (w : Nat) : Num w 0 0 ([.b] ^ w) := by
  induction w with
  | zero => exact Num.Num_O
  | succ w ih => exact Num.Num_0 w 0 0 ([.b] ^ w) ih
lemma z0T (w : Nat) : Num w (2 ^ w - 1) w ([.a,.a] ^ w) := by
  induction w with
  | zero => exact Num.Num_O
  | succ w ih =>
    have h := Num.Num_1 w (2 ^ w - 1) w ([.a,.a] ^ w) ih
    have hpow : 2 ^ w >= 1 := Nat.one_le_two_pow
    have hpow2 : 2 ^ (w + 1) = 2 ^ w * 2 := Nat.pow_succ 2 w
    refine z0Q h rfl ?_ rfl rfl
    omega
lemma z0U {w n p : Nat} {xs : List Token} (h : Num w n p xs) (hn : n + 1 < 2 ^ w) :
    ∃ t rest p',xs = [.a,.a] ^ t ++ .b :: rest /\
      Num w (n + 1) p' ([.b] ^ t ++ [.a,.a] ++ rest) /\ p' + t = p + 1 := by
  induction h with
  | Num_O => omega
  | Num_0 w n p xs h ih =>
    exact ⟨0,xs,p + 1,rfl,Num.Num_1 w n p xs h,by omega⟩
  | Num_1 w n p xs h ih =>
    have hpow : 2 ^ (w + 1) = 2 ^ w * 2 := Nat.pow_succ 2 w
    obtain ⟨t,rest,p',rfl,h1,h2⟩ := ih (by omega)
    refine ⟨t + 1,rest,p',rfl,?_,by omega⟩
    have h0 := Num.Num_0 w (n + 1) p' ([.b] ^ t ++ [.a,.a] ++ rest) h1
    refine z0Q h0 rfl (by omega) rfl rfl
def ck (xs ts : List Token) (m : zF) : Cfg (Fin 2) (Fin 6) :=
  default {{D}}> [0] +> z4 +> enc (xs ++ ts) +> m +> default
lemma z0V {w n p : Nat} {xs : List Token} (h : Num w n p xs) (hn : n + 1 < 2 ^ w) :
    ∃ f p' ys,0 < f /\ Num w (n + 1) p' ys /\ f + p' = p + 2 /\
      ∀ ts m ts' m',Evs f ts m ts' m' -> ((ck xs ts m) [target_tm]⊢⁺ (ck ys ts' m')) := by
  obtain ⟨t,rest,p',rfl,h1,h2⟩ := z0U h hn
  refine ⟨t + 1,p',[.b] ^ t ++ [.a,.a] ++ rest,by omega,h1,by omega,?_⟩
  intro ts m ts' m' he
  have hc := z0K t 0 (rest ++ ts) m (rest ++ ts') m' default (z0I (t + 1) rest ts m ts' m' he)
  refine z0b hc ?_ ?_
  · dsimp [ck]; simp [List.append_assoc]
  · dsimp [ck]; simp [List.append_assoc]
lemma z0W (k : Nat) {w n p : Nat} {xs : List Token} (h : Num w n p xs) (hn : n + k < 2 ^ w) :
    ∃ f q ys,Num w (n + k) q ys /\ k <= f /\ f + q = p + k * 2 /\
      ∀ ts m ts' m',Evs f ts m ts' m' -> ((ck xs ts m) [target_tm]⊢* (ck ys ts' m')) := by
  induction k generalizing n p xs with
  | zero =>
    refine ⟨0,p,xs,by simpa using h,by omega,by omega,?_⟩
    intro ts m ts' m' ⟨rfl,rfl⟩
    exact z06 _
  | succ k ih =>
    obtain ⟨f1,p1,xs1,hf1,hn1,hc1,hs1⟩ := z0V h (by omega)
    obtain ⟨f2,q,ys,hn2,hf2,hc2,hs2⟩ := ih hn1 (by omega)
    refine ⟨f1 + f2,q,ys,z0Q hn2 rfl (by omega) rfl rfl,by omega,by omega,?_⟩
    intro ts m ts' m' he
    obtain ⟨ts1,m1,he1,he2⟩ := z0J f1 f2 ts m ts' m' he
    exact zSt (zPs (hs1 ts m ts1 m1 he1)) (hs2 ts1 m1 ts' m' he2)
lemma z0X {w n k p q : Nat} {xs ys : List Token} {f : Nat} {ts : List Token} {m : zF}
    {ts' : List Token} {m' : zF}
    (hn : Num w n p xs) (hn' : Num w (n + k) q ys) (hc : f + q = p + k * 2)
    (he : Evs f ts m ts' m') :
    (ck xs ts m) [target_tm]⊢* (ck ys ts' m') := by
  have hb := (z0N hn').1
  obtain ⟨f',q',ys',hn1,_,hc1,hs⟩ := z0W k hn hb
  obtain ⟨rfl,rfl⟩ := z0P hn' hn1
  have hf : f' = f := by omega
  subst hf
  exact hs ts m ts' m' he
lemma z0Y {w n k p q : Nat} {xs ys : List Token} {f : Nat} {ts : List Token} {rem : Nat} {m : zF}
    (hn : Num w n p xs) (hn' : Num w (n + k) q ys) (hc : f + q = p + k * 2) :
    (ck xs ts ([1,1] ^ (f + rem) ++ m)) [target_tm]⊢*
    (ck ys (ts ++ [.b] ^ f) ([1,1] ^ rem ++ m)) :=
  z0X hn hn' hc (z0L f ts rem m)
def OV (j : Nat) (ts : List Token) (m : zF) : Cfg (Fin 2) (Fin 6) :=
  (default <+ ([1,0,1] ^ j)) {{D}}> [0] +> z4 +> [0] +> enc ts +> m +> default
lemma z0Z (l r : zB) :
    (l {{D}}> [0,0,0,0,0,0,1,0,0] +> r) [target_tm]⊢*
    ((l <+ [0,1,0,1,0,1]) {{D}}> [1,0,0] +> r) := by
  dsimp [D]; execute
lemma z10 (n : Nat) (l r : zB) :
    (l {{D}}> [0] +> z4 +> [0] +> ([1,0,0] ^ (2 + n * 2)) +> [0] +> r) [target_tm]⊢⁺
    ((l <+ [1,0,1,0,1]) {{D}}> [0] +> z4 +> [0] +> ([1,0,0] ^ (n * 2)) +> [0,1] +> r) := by
  have h1 := z0Z l (([1,0,0] ^ (1 + n * 2)) +> [0] +> r)
  have h2 := z0o ([.b] ^ (n * 2)) (l <+ [0,1,0,1,0,1]) r
  refine z08 (z0a h1 ?_ rfl) (z0b h2 ?_ ?_)
  · have hp : ([1,0,0] : zF) ^ (2 + n * 2) = [1,0,0] ++ ([1,0,0] ^ (1 + n * 2)) := by
      have : 2 + n * 2 = 1 + (1 + n * 2) := by omega
      rw [this,pow_add]; rfl
    rw [hp]; simp [z4]
  · rw [z0d,z0f]; dsimp [enc,tk]
    rw [z02 [1,0,0] (n * 2)]
    have : n * 2 + 1 = 1 + n * 2 := by omega
    rw [this]
  · rw [z0g]; dsimp [ems,em]
    have hs := z0B (n * 2) ([0,1] +> r)
    simp only [append_cons,append_nil] at hs
    simp only [z4,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,append_cons,append_nil]
    rw [hs]
lemma z11 (n : Nat) (l r : zB) :
    (l {{D}}> [0] +> z4 +> [0] +> ([1,0,0] ^ (n * 2)) +> [0] +> r) [target_tm]⊢*
    ((l <+ ([1,0,1,0,1] ^ n)) {{D}}> [0] +> z4 +> [0,0] +> ([1] ^ n) +> r) := by
  induction n generalizing l r with
  | zero => exact z06 _
  | succ n ih =>
    have h1 := z10 n l r
    have h2 := ih (l <+ [1,0,1,0,1]) ([1] +> r)
    refine zSt (zPs (z0b h1 ?_ rfl)) (z0a h2 ?_ ?_)
    · have : (n + 1) * 2 = 2 + n * 2 := by omega
      rw [this]
    · simp
    · rw [<- z02 [1,0,1,0,1] n,<- z02 [1] n]
      simp
lemma z12 (l r : zB) :
    (l {{D}}> [0] +> z4 +> [0,0,1,1] +> r) [target_tm]⊢⁺
    ((l <+ [1,0,1,0,1]) <{{D}} z4 +> r) := by
  dsimp [z4,D]; execute
lemma z13 (j k : Nat) (r : zB) :
    ((default <+ ([1,0,1] ^ j) <+ ([1,0,1,0,1] ^ k)) {{D}}> [0] +> z4 +> [0,0,1,1] +> r) [target_tm]⊢⁺
    (default {{D}}> [0] +> z4 +> ([1,0,0] ^ j) +> ([1,0,1,0,0] ^ k) +> [1,0,1,0,1,0] +> r) := by
  have h1 := z12 (default <+ ([1,0,1] ^ j) <+ ([1,0,1,0,1] ^ k)) r
  have h2 := ls .a (default <+ ([1,0,1] ^ j) <+ ([1,0,1,0,1] ^ k) <+ [1,0,1]) r
  have h3 := ls .a (default <+ ([1,0,1] ^ j) <+ ([1,0,1,0,1] ^ k) <+ [1]) ([1,0] +> r)
  have h4 := z0w k (default <+ ([1,0,1] ^ j)) ([1,0,1,0] +> r)
  have h5 := z0v j (([1,0,0,1,0] ^ k) +> [1,0,1,0] +> r)
  refine z07 h1 (zSt h2 (zSt h3 (zSt h4 (z0a h5 rfl ?_))))
  rw [z0y,z0A]
  rfl
lemma o01 (j k p : Nat) (m : zF) (hp : 2 <= p + k) :
    (OV j ([.b] ^ (k * 2)) (0 :: ([1] ^ p ++ m))) [target_tm]⊢⁺
    (ck ([.b] ^ j) ([.a,.b] ^ k ++ [.a,.a,.a]) ([1] ^ (p + k - 2) ++ m)) := by
  have h1 := z11 k (default <+ ([1,0,1] ^ j)) (([1] ^ p) +> m +> default)
  have h2 := z13 j k (([1] ^ (p + k - 2)) +> m +> default)
  refine z08 (z0a h1 ?_ rfl) (z0b h2 ?_ ?_)
  · dsimp [OV]; rw [z0f]; dsimp [enc,tk]; simp
  · have hpk : ([1] : zF) ^ k ++ ([1] ^ p) = [1,1] ++ ([1] ^ (p + k - 2)) := by
      have h1 : k + p = 2 + (p + k - 2) := by omega
      rw [<- pow_add,h1,pow_add [1] 2 (p + k - 2)]
      rfl
    have hpk' := congrArg (fun l => l +> m +> (default : zB)) hpk
    simp only [append_assoc,append_cons,append_nil] at hpk' ⊢
    rw [hpk']
  · dsimp [ck]
    rw [z0d,z0d,z0f,z0f]
    dsimp [enc,tk]
    simp
lemma z14 (l r : zB) :
    (l {{D}}> [0] +> z4 +> [0] +> [1,0,1,0,0] +> r) [target_tm]⊢*
    ((l <+ [1,0,1,1,0,1,0,1]) {{D}}> [1,0,0] +> r) := by
  dsimp [z4,D]; execute
lemma z15 (j : Nat) (r : zB) :
    ((default <+ ([1,0,1] ^ j) <+ [1,0,1,1,0,1,0,1]) <{{D}} z4 +> r) [target_tm]⊢*
    (default {{D}}> [0] +> z4 +> ([1,0,0] ^ j) +> enc [.a,.b,.a,.a] +> r) := by
  have h1 := ls .a (default <+ ([1,0,1] ^ j) <+ [1,1,0,1,0,1]) r
  have h2 := ls .b (default <+ ([1,0,1] ^ j) <+ [1,0,1]) ([1,0] +> r)
  have h3 := ls .a (default <+ ([1,0,1] ^ j) <+ [1]) ([0,1,0,1,0] +> r)
  have h4 := z0v j ([1,0,0,1,0,1,0] +> r)
  refine zSt h1 (zSt h2 (zSt h3 (z0a h4 rfl ?_)))
  rw [z0y]
  rfl
lemma o2 (j : Nat) (ts : List Token) (m : zF) :
    (OV j (.a :: .b :: (ts ++ [.b])) (0 :: m)) [target_tm]⊢⁺
    (ck ([.b] ^ j) (.a :: .b :: .a :: (ts ++ [.b])) (0 :: 1 :: m)) := by
  have h1 := z14 (default <+ ([1,0,1] ^ j)) (enc (ts ++ [.b]) +> [0] +> m +> default)
  have h2 := z0o ts (default <+ ([1,0,1] ^ j) <+ [1,0,1,1,0,1,0,1]) (m +> default)
  have h3 := z15 j (ems ts +> [0,0,1] +> m +> default)
  refine z08 (z0a h1 ?_ rfl) (z07 h2 (z0a h3 rfl ?_))
  · simp [OV,enc,tk]
  · dsimp [ck]; rw [z0d,z0f]; dsimp [enc,tk]
    simp only [append_assoc,append_cons,append_nil,z0D]
lemma z16 (l r : zB) :
    (l {{D}}> [0] +> z4 +> [0] +> [1,0,1,0,1] +> r) [target_tm]⊢*
    ((l <+ [0,1,1,0,1,0,1]) {{D}}> [1,0,0,1] +> r) := by
  dsimp [z4,D]; execute
lemma z17 (ts : List Token) (l r : zB) :
    (l {{D}}> [0] +> z4 +> [0] +> enc (.a :: .a :: .b :: (ts ++ [.b])) +> [0] +> r) [target_tm]⊢⁺
    ((l <+ [1,1,0,1,0,1]) {{D}}> [0] +> z4 +> [0] +> enc (ts ++ [.b]) +> [0,1] +> r) := by
  have h1 := z16 l ([0,0] +> enc (ts ++ [.b]) +> [0] +> r)
  have h2 := z0o (.b :: ts) (l <+ [0,1,1,0,1,0,1]) r
  refine z08 (z0a h1 ?_ rfl) (z0b h2 ?_ ?_)
  · simp [enc,tk]
  · simp [enc,tk]
  · dsimp [ems,em]
    simp only [z4,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,append_assoc,append_cons,append_nil,z0D]
lemma z18 (j : Nat) (r : zB) :
    ((default <+ ([1,0,1] ^ j) <+ [1,1,0,1,0,1] <+ [1,0,1,1,0,1,0,1]) <{{D}} z4 +> r) [target_tm]⊢*
    (default {{D}}> [0] +> z4 +> ([1,0,0] ^ j) +> enc [.a,.b] +> [0] +> enc [.a,.b,.a,.a] +> r) := by
  have h1 := ls .a (default <+ ([1,0,1] ^ j) <+ [1,1,0,1,0,1] <+ [1,1,0,1,0,1]) r
  have h2 := ls .b (default <+ ([1,0,1] ^ j) <+ [1,1,0,1,0,1] <+ [1,0,1]) ([1,0] +> r)
  have h3 := ls .a (default <+ ([1,0,1] ^ j) <+ [1,1,0,1,0,1] <+ [1]) ([0,1,0,1,0] +> r)
  have h4 := z0j (default <+ ([1,0,1] ^ j) <+ [1,0,1]) ([1,0,0,1,0,1,0] +> r)
  have h5 := ls .a (default <+ ([1,0,1] ^ j) <+ [1]) ([0,0,1,0,1,0,0,1,0,1,0] +> r)
  have h6 := z0v j ([1,0,0,0,1,0,1,0,0,1,0,1,0] +> r)
  refine zSt h1 (zSt h2 (zSt h3 (zSt h4 (zSt h5 (z0a h6 rfl ?_)))))
  rw [z0y]
  rfl
lemma o3 (j : Nat) (ts : List Token) (m : zF) :
    (OV j (.a :: .a :: .b :: .a :: .b :: (ts ++ [.b])) (0 :: m)) [target_tm]⊢⁺
    (ck ([.b] ^ j) [.a,.b] (0 :: (enc (.a :: .b :: .a :: (ts ++ [.b])) ++ [0,1,1] ++ m))) := by
  have h1 := z17 (.a :: .b :: ts) (default <+ ([1,0,1] ^ j)) (m +> default)
  have h2 := z14 (default <+ ([1,0,1] ^ j) <+ [1,1,0,1,0,1]) (enc (ts ++ [.b]) +> [0,1] +> m +> default)
  have h3 := z0o ts (default <+ ([1,0,1] ^ j) <+ [1,1,0,1,0,1] <+ [1,0,1,1,0,1,0,1]) ([1] +> m +> default)
  have h4 := z18 j (ems ts +> [0,0,1,1] +> m +> default)
  refine zPt (z0b h1 ?_ rfl) (z08 (z0a h2 ?_ rfl) (z07 (z0b h3 ?_ ?_) (z0a h4 rfl ?_)))
  · dsimp [OV]
  · simp [enc,tk]
  · simp [enc,tk]
  · rfl
  · dsimp [ck]; rw [z0d,z0f]; dsimp [enc,tk]
    simp only [append_assoc,append_cons,append_nil,z0D]
def z19 (ts : List Token) : Prop := ts = [] \/ ∃ us,ts = us ++ [.b]
lemma z1a {ts : List Token} (m : zF) (ht : z19 ts) :
    Ev (.b :: ts) (0 :: m) (.b :: ts) (0 :: 1 :: m) := by
  rcases ht with rfl | ⟨us,rfl⟩
  · exact Ev.EvT [] m
  · exact Ev.EvT (.b :: us) m
lemma z1b {ts : List Token} (l r : zB) (ht : z19 ts) :
    (l {{D}}> [0] +> z4 +> enc (.a :: .b :: ts) +> [0] +> r) [target_tm]⊢⁺
    ((l <+ [1,0,1]) {{D}}> [0] +> z4 +> [0] +> enc ts +> [0,1] +> r) := by
  rcases ht with rfl | ⟨us,rfl⟩
  · exact z0u [] l r
  · have h1 := z0u (.b :: us) l r
    refine z0b h1 rfl ?_
    dsimp [ems,em]
    simp only [append_assoc,append_cons,append_nil,z0D]
lemma z1c (w j : Nat) {ts : List Token} (p : Nat) (m : zF) (ht : z19 ts) :
    ((default <+ ([1,0,1] ^ j)) {{D}}> [0] +> z4 +> enc ([.a,.a] ^ w ++ .a :: .b :: ts) +> (0 :: ([1] ^ p ++ m)) +> default) [target_tm]⊢⁺
    (OV (j + w + 1) ts (0 :: ([1] ^ (w + 1 + p) ++ m))) := by
  induction w generalizing j p with
  | zero =>
    have h1 := z1b (default <+ ([1,0,1] ^ j)) (([1] ^ p) +> m +> default) ht
    refine z0b h1 (by simp) ?_
    dsimp [OV]
    have hp : 0 + 1 + p = 1 + p := by omega
    rw [hp,pow_add [1] 1 p]
    simp
  | succ w ih =>
    have hev : Ev ([.a,.a] ^ w ++ .a :: .b :: ts) (0 :: ([1] ^ p ++ m)) ([.a,.a] ^ w ++ .a :: .b :: ts) (0 :: 1 :: ([1] ^ p ++ m)) := by
      have hpre := z0F ([.a,.a] ^ w ++ [.a]) (.b :: ts) (0 :: ([1] ^ p ++ m)) (.b :: ts) (0 :: 1 :: ([1] ^ p ++ m)) (z1a ([1] ^ p ++ m) ht)
      simpa [List.append_assoc] using hpre
    have h1 := z0G ([.a,.a] ^ w ++ .a :: .b :: ts) (0 :: ([1] ^ p ++ m)) ([.a,.a] ^ w ++ .a :: .b :: ts) (0 :: 1 :: ([1] ^ p ++ m)) (default <+ ([1,0,1] ^ j)) default hev
    have h2 := ih (j + 1) (p + 1)
    refine zPt (z0b h1 ?_ rfl) (z0b h2 ?_ ?_)
    · simp [z01,List.append_assoc]
    · have hj : ([1,0,1] : zF) ^ (j + 1) = [1,0,1] ++ ([1,0,1] ^ j) := rfl
      have hp : ([1] : zF) ^ (p + 1) = 1 :: ([1] ^ p) := rfl
      rw [hj,hp]; simp
    · dsimp [OV]
      have hj : j + 1 + w = j + (w + 1) := by omega
      have hp : w + 1 + (p + 1) = w + 1 + 1 + p := by omega
      rw [hj,hp]
lemma z1d (w : Nat) {ts : List Token} (p : Nat) (m : zF) (ht : z19 ts) :
    (ck ([.a,.a] ^ w) (.a :: .b :: ts) (0 :: ([1] ^ p ++ m))) [target_tm]⊢⁺
    (OV (w + 1) ts (0 :: ([1] ^ (w + 1 + p) ++ m))) := by
  have h := z1c w 0 p m ht
  have hw : 0 + w = w := Nat.zero_add w
  refine z0b h (by simp [ck]) (by dsimp [OV]; rw [hw])
lemma z1e (n : Nat) {ts : List Token} (k : Nat) (m : zF) (ht : z19 ts) :
    Evs n (.a :: .b :: ts) (0 :: ([1] ^ k ++ m)) (.a :: .b :: ts) (0 :: ([1] ^ (n + k) ++ m)) := by
  rcases ht with rfl | ⟨us,rfl⟩
  · exact z0M n [.a] k m
  · exact z0M n (.a :: .b :: us) k m
lemma z1f {w n p : Nat} {xs ts : List Token} (k : Nat) (m : zF) (f : Nat)
    (hn : Num w n p xs) (ht : z19 ts) (hf : f + 1 + n * 2 = 2 ^ w * 2 + p) :
    (ck xs (.a :: .b :: ts) (0 :: ([1] ^ k ++ m))) [target_tm]⊢⁺
    (OV (w + 1) ts (0 :: ([1] ^ (f + k) ++ m))) := by
  have hb := (z0N hn).1
  have hlt : n + (2 ^ w - 1 - n) < 2 ^ w := by omega
  obtain ⟨g,q,ys,hn1,_,hc,hs⟩ := z0W (2 ^ w - 1 - n) hn hlt
  have hneq : n + (2 ^ w - 1 - n) = 2 ^ w - 1 := by omega
  rw [hneq] at hn1
  obtain ⟨rfl,rfl⟩ := z0P (z0T w) hn1
  have h1 := hs (.a :: .b :: ts) (0 :: ([1] ^ k ++ m)) (.a :: .b :: ts) (0 :: ([1] ^ (g + k) ++ m)) (z1e g k m ht)
  have h2 := z1d w (g + k) m ht
  refine z08 h1 (z0b h2 rfl ?_)
  dsimp [OV]
  have hfg : w + 1 + (g + k) = f + k := by omega
  rw [hfg]
lemma z1g : Num 1 1 1 [.a,.a] := Num.Num_1 0 0 0 [] Num.Num_O
lemma z1h (u v : Nat) :
    Num (u + v + 2) (2 ^ u + 2 ^ (u + v + 1)) 2 ([.b] ^ u ++ [.a,.a] ++ [.b] ^ v ++ [.a,.a]) := by
  have h1 := z0R (z0S v) z1g
  have h2 := z0R z1g h1
  have h3 := z0R (z0S u) h2
  refine z0Q h3 (by omega) ?_ (by omega) (by simp [List.append_assoc])
  rw [Nat.pow_add,Nat.pow_add,Nat.pow_one]
  simp [Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
lemma z1i (j : Nat) :
    Num (j + 6) (2 ^ j * 7) 3 ([.b] ^ j ++ [.a,.a] ^ 3 ++ [.b] ^ 3) := by
  have h1 := z0R (z0T 3) (z0S 3)
  have h2 := z0R (z0S j) h1
  refine z0Q h2 (by omega) (by omega) (by omega) (by simp [List.append_assoc])
set_option allowUnsafeReducibility true
abbrev o1 : zF := [1]
abbrev z1 : zF := [0]
abbrev p101 : zF := [1,0,1]
abbrev p100 : zF := [1,0,0]
abbrev tb : List Token := [Token.b]
abbrev tab : List Token := [Token.a,Token.b]
lemma z1j (l : List α) : l ^ (1 : Nat) = l := by simp
lemma z1k (l : List α) : l ^ (2 : Nat) = l ++ l := by simp
lemma z1l (l : List α) : l ^ (3 : Nat) = l ++ l ++ l := by simp
lemma z1m (n : Nat) (xs : List Token) :
    (tb ^ n) ++ (Token.b :: xs) = (tb ^ (n + 1)) ++ xs := by
  rw [<- z02 tb n,List.append_assoc]; rfl
lemma z1n {n : Nat} {ts1 ts1' : List Token} {m1 m1' : zF} {ts2 ts2' : List Token} {m2 m2' : zF}
    (h : Evs n ts1 m1 ts2 m2) (h1 : ts1 = ts1') (h2 : m1 = m1') (h3 : ts2 = ts2') (h4 : m2 = m2') :
    Evs n ts1' m1' ts2' m2' := h1 ▸ h2 ▸ h3 ▸ h4 ▸ h
lemma z1o {k k' : Nat} {m1 m2 : zF} (hk : k = k') (hm : m1 = m2) :
    ck ([.a,.a] ++ tb ^ k) ([.a,.a,.a] ++ [.b]) m1 =
    ck ([.a,.a] ++ tb ^ k' ++ [.a,.a]) [.a,.b] m2 := by
  subst hk; subst hm; dsimp [ck]; simp only [List.append_assoc,List.cons_append,List.nil_append]
lemma z1p (rest ts qs : List Token) (m : zF) :
    (ck (.a :: .a :: .b :: rest) ts ([1,1] ++ enc (qs ++ [.b]) ++ [0] ++ m)) [target_tm]⊢⁺
    (ck (.b :: .a :: .a :: rest) (ts ++ [.b] ++ qs ++ [.b]) (0 :: 1 :: m)) := by
  have hev1 : Ev (.b :: (rest ++ ts)) ([1,1] ++ (enc (qs ++ [.b]) ++ [0] ++ m)) (.b :: (rest ++ ts) ++ [.b]) (enc (qs ++ [.b]) ++ [0] ++ m) :=
    Ev.EvG (.b :: (rest ++ ts)) (enc (qs ++ [.b]) ++ [0] ++ m)
  have h1 := z0G (.b :: (rest ++ ts)) ([1,1] ++ (enc (qs ++ [.b]) ++ [0] ++ m)) (.b :: (rest ++ ts) ++ [.b]) (enc (qs ++ [.b]) ++ [0] ++ m) default default hev1
  have hev2 : Ev (rest ++ ts ++ [.b] ++ qs ++ [.b]) (0 :: m) (rest ++ ts ++ [.b] ++ qs ++ [.b]) (0 :: 1 :: m) :=
    Ev.EvT (rest ++ ts ++ [.b] ++ qs) m
  have h2 := z0H 1 (rest ++ ts ++ [.b] ++ qs ++ [.b]) (0 :: m) (rest ++ ts ++ [.b] ++ qs ++ [.b]) (0 :: 1 :: m) default hev2
  refine zPt (z0b h1 ?_ rfl) (z0b h2 ?_ ?_)
  · dsimp [ck]
  · dsimp [ck]; simp only [z0d,enc,tk,append_assoc,append_cons,append_nil,List.append_assoc,List.cons_append,List.nil_append]
  · dsimp [ck]; simp only [z0d,z0f,z01,zPz,enc,tk,append_assoc,append_cons,append_nil,List.append_assoc,List.cons_append,List.nil_append]
lemma z1q (xs ts : List Token) (m : zF) :
    (ck (.b :: xs) ts ([1,1] ++ m)) [target_tm]⊢⁺ (ck ([.a,.a] ++ xs) (ts ++ [.b]) m) := by
  have hev : Ev (xs ++ ts) ([1,1] ++ m) ((xs ++ ts) ++ [.b]) m := Ev.EvG (xs ++ ts) m
  have h1 := z0H 0 (xs ++ ts) ([1,1] ++ m) ((xs ++ ts) ++ [.b]) m default hev
  refine z0b h1 ?_ ?_
  · dsimp [ck]
  · dsimp [ck]; simp only [z0d,enc,tk,zPz,append_assoc,append_cons,append_nil,List.append_assoc,List.cons_append,List.nil_append]
@[simp] lemma z1r (xs ts : List Token) (m : zF) :
    ck xs ts (m ++ [0]) = ck xs ts m := by
  dsimp [ck]; simp
@[simp] lemma z1s (j : Nat) (ts : List Token) (m : zF) :
    OV j ts (m ++ [0]) = OV j ts m := by
  dsimp [OV]; simp
lemma z1t : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
macro "prep_exec" : tactic =>
  `(tactic| simp only [A,B,C,D,E,F,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,z00,zDh,zDt,append_cons,append_nil])
abbrev cfg_of_loc := @Counter.cfg_of (Fin 2) (Fin 6)

@[simp] lemma append_nil_loc (l : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> l = l := rfl
@[simp] lemma append_cons_loc (a : Fin 2) (as : List (Fin 2)) (l : ListBlank (Fin 2)) :
    (a :: as) +> l = a >> (as +> l) := rfl

abbrev LocalStateLoc := Counter.LocalState (Fin 2) (Fin 6)
abbrev step_local_loc := @Counter.step_local (Fin 2) (Fin 6)
abbrev step_local_spec_loc := @Counter.step_local_spec (Fin 2) (Fin 6) _ _
abbrev run_local_loc := @Counter.run_local (Fin 2) (Fin 6)
abbrev run_local_spec_loc := @Counter.run_local_spec (Fin 2) (Fin 6) _ _
abbrev run_local_plus_eq_loc := @Counter.run_local_plus_eq (Fin 2) (Fin 6) _ _

def s_loc_0 : LocalStateLoc := ⟨[(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 0, .right⟩
def s_loc_1 : LocalStateLoc := ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 5, .right⟩
def s_loc_2 : LocalStateLoc := ⟨[(0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 3, .left⟩
def s_loc_3 : LocalStateLoc := ⟨[(1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 4, .right⟩
def s_loc_4 : LocalStateLoc := ⟨[(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 3, .left⟩

lemma step_loc_01 : ((default {{0}}> default) : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
    (cfg_of_loc s_loc_1.q s_loc_1.d (s_loc_1.l +> default) (s_loc_1.r +> default)) :=
  run_local_plus_eq_loc (n := 199) (s1 := s_loc_0) (s2 := s_loc_1) default default rfl
    (by simp only [s_loc_0, cfg_of_loc, Counter.cfg_of, append_cons_loc, append_nil_loc, z00]) rfl
lemma step_loc_12 : (cfg_of_loc s_loc_1.q s_loc_1.d (s_loc_1.l +> default) (s_loc_1.r +> default)) [target_tm]⊢⁺
    (cfg_of_loc s_loc_2.q s_loc_2.d (s_loc_2.l +> default) (s_loc_2.r +> default)) :=
  run_local_plus_eq_loc (n := 199) (s1 := s_loc_1) (s2 := s_loc_2) default default rfl rfl rfl
lemma step_loc_23 : (cfg_of_loc s_loc_2.q s_loc_2.d (s_loc_2.l +> default) (s_loc_2.r +> default)) [target_tm]⊢⁺
    (cfg_of_loc s_loc_3.q s_loc_3.d (s_loc_3.l +> default) (s_loc_3.r +> default)) :=
  run_local_plus_eq_loc (n := 199) (s1 := s_loc_2) (s2 := s_loc_3) default default rfl rfl rfl
lemma step_loc_34 : (cfg_of_loc s_loc_3.q s_loc_3.d (s_loc_3.l +> default) (s_loc_3.r +> default)) [target_tm]⊢⁺
    (ck [.a,.a,.b,.b,.a,.a] [.a,.b] [0,1]) :=
  run_local_plus_eq_loc (n := 206) (s1 := s_loc_3) (s2 := s_loc_4) default default rfl rfl
    (by simp only [s_loc_4, cfg_of_loc, Counter.cfg_of, ck, enc, tk, z4, D, append_cons_loc, append_nil_loc, append_cons, append_nil, List.append_assoc, List.cons_append, List.nil_append, z00, zDh, zDt]; rfl)

lemma z1W :
    (init []) [target_tm]⊢* (ck [.a,.a,.b,.b,.a,.a] [.a,.b] [0,1]) :=
  zPs (zPt step_loc_01 (zPt step_loc_12 (zPt step_loc_23 step_loc_34)))
set_option maxRecDepth 4000000 in attribute [-simp] list_nat_repeat
set_option maxRecDepth 4000000 in attribute [-simp] z01
def z1X (j : Nat) (ts : List Token) (z : Nat) (rest : zF) : Cfg (Fin 2) (Fin 6) :=
  ck ([.a,.a] ++ tb ^ (j + 5) ++ [.a,.a]) [.a,.b]
    (o1 ^ (2 ^ (j + 6) - 4) ++ z1 ++ enc ts ++ z1 ++ o1 ^ z ++ rest)
def z1Y : zF := enc ([.a,.a] ++ tb ^ 28) ++ z1 ++ o1 ^ 741
lemma z1Z {w n p : Nat} {xs : List Token} {n' q : Nat} {ys : List Token}
    {f : Nat} {ts : List Token} {rem : Nat} {m : zF}
    (hn : Num w n p xs) (hn' : Num w n' q ys) (hle : n <= n') (hf : f + q = p + (n' - n) * 2) :
    (ck xs ts (o1 ^ ((f + rem) * 2) ++ m)) [target_tm]⊢*
    (ck ys (ts ++ tb ^ f) (o1 ^ (rem * 2) ++ m)) := by
  dsimp only [o1,tb]
  rw [z03 1 (f + rem),z03 1 rem]
  have hn'' : Num w (n + (n' - n)) q ys := z0Q hn' rfl (by omega) rfl rfl
  exact z0Y hn hn'' hf
lemma z20 (n : Nat) : z19 (tb ^ n) := by
  cases n with
  | zero => exact Or.inl (zPz tb)
  | succ n => exact Or.inr ⟨tb ^ n,(z02 tb n).symm⟩
lemma z21 (j k : Nat) : 2 ^ (j + k) = 2 ^ j * 2 ^ k := Nat.pow_add 2 j k
lemma z22 :
    (ck [.a,.a,.b,.b,.a,.a] [.a,.b] [0,1]) [target_tm]⊢*
    (ck ([.a,.a] ++ tb ^ 4 ++ [.a,.a]) [.a,.b] (o1 ^ 12)) := by
  have hn : Num 4 9 2 [.a,.a,.b,.b,.a,.a] :=
    Num.Num_1 3 4 1 [.b,.b,.a,.a] (Num.Num_0 2 2 1 [.b,.a,.a] (Num.Num_0 1 1 1 [.a,.a] z1g))
  have h1 := z1f (ts := []) 1 [] 15 hn (Or.inl rfl) (by decide)
  have h2 := o01 5 0 16 [] (by decide)
  have h3 := z1q (tb ^ 4) [.a,.a,.a] (o1 ^ 12)
  exact zPs (zPt h1 (zPt h2 h3))
lemma z23 :
    (ck ([.a,.a] ++ tb ^ 4 ++ [.a,.a]) [.a,.b] (o1 ^ 12)) [target_tm]⊢*
    (ck (tb ^ 7) (tab ^ 3 ++ [.a,.a,.a]) (o1 ^ 58)) := by
  have hn0 : Num 6 33 2 ([.a,.a] ++ tb ^ 4 ++ [.a,.a]) :=
    z0Q (z1h 0 4) rfl rfl rfl rfl
  have hn1 : Num 6 36 2 (tb ^ 2 ++ [.a,.a] ++ tb ^ 2 ++ [.a,.a]) :=
    z0Q (z1h 2 2) rfl rfl rfl rfl
  have hg := z1Z (f := 6) (ts := [.a,.b]) (rem := 0) (m := [0]) hn0 hn1 (by decide) (by decide)
  have hto := z1f (ts := tb ^ 6) 0 [] 57 hn1 (z20 6) (by decide)
  have ho := o01 7 3 57 [] (by decide)
  refine zSt (z0a hg ?_ rfl) (zPs (zPt (z0b hto rfl rfl) (z0b ho rfl ?_)))
  · exact z1r _ _ (o1 ^ 12)
  · exact List.append_nil (o1 ^ 58) ▸ rfl
lemma z24 :
    (ck (tb ^ 7) (tab ^ 3 ++ [.a,.a,.a]) (o1 ^ 58)) [target_tm]⊢*
    (OV 8 (tab ^ 2 ++ [.a,.a,.a] ++ tb ^ 29) (0 :: o1 ^ 226)) := by
  have hn15 : Num 7 15 4 ([.a,.a] ^ 4 ++ tb ^ 3) := by
    have h := z0R (z0T 4) (z0S 3)
    exact z0Q h rfl rfl rfl rfl
  have hn16 : Num 7 16 1 (tb ^ 4 ++ [.a,.a] ++ tb ^ 2) := by
    have h := z0R (z0S 4) (z0R z1g (z0S 2))
    exact z0Q h rfl rfl rfl rfl
  have hg := z1Z (f := 26) (ts := tab ^ 3 ++ [.a,.a,.a]) (rem := 3) (m := [0])
    (z0S 7) hn15 (by decide) (by decide)
  have hevs : Evs 5 (tb ^ 2 ++ (tab ^ 3 ++ [.a,.a,.a] ++ tb ^ 26)) (([1,1] : zF) ^ 3 ++ [0])
      (tb ^ 2 ++ (tab ^ 3 ++ [.a,.a,.a] ++ tb ^ 29)) (0 :: o1 ^ 2) := by
    have hg3 := z0L 3 (tb ^ 2 ++ (tab ^ 3 ++ [.a,.a,.a] ++ tb ^ 26)) 0 [0]
    have ht2 := z0M 2 (tb ^ 2 ++ (tab ^ 3 ++ [.a,.a,.a] ++ tb ^ 28)) 0 []
    obtain ⟨tsa,ma,ha1,tsb,mb,ha2,tsc,mc,ha3,htsc,hmc⟩ := hg3
    refine ⟨tsa,ma,ha1,tsb,mb,ha2,tsc,mc,ha3,z1n ht2 ?_ ?_ (by decide) (by decide)⟩
    · rw [<- htsc]; decide
    · rw [<- hmc]; decide
  have hc := z0K 4 0 (tb ^ 2 ++ (tab ^ 3 ++ [.a,.a,.a] ++ tb ^ 26)) (([1,1] : zF) ^ 3 ++ [0])
    (tb ^ 2 ++ (tab ^ 3 ++ [.a,.a,.a] ++ tb ^ 29)) (0 :: o1 ^ 2) default hevs
  have hend : z19 (tab ^ 2 ++ [.a,.a,.a] ++ tb ^ 29) :=
    Or.inr ⟨tab ^ 2 ++ [.a,.a,.a] ++ tb ^ 28,rfl⟩
  have hto := z1f (ts := tab ^ 2 ++ [.a,.a,.a] ++ tb ^ 29) 2 [] 224 hn16 hend (by decide)
  refine zSt (z0a hg ?_ rfl) (zPs (zPt (z0b hc rfl rfl) (z0b hto rfl ?_)))
  · exact z1r _ _ (o1 ^ 58)
  · dsimp only [o1]; rw [List.append_nil]
set_option maxRecDepth 4000000 in attribute [irreducible] list_nat_repeat
lemma z25 (j : Nat) (r : zB) :
    ((default <+ (p101 ^ j) <+ [1,1,0,1,0,1] <+ [1,1,0,1,0,1] <+ [1,0,1,0,1]) <{{D}} z4 +> r) [target_tm]⊢*
    (default {{D}}> [0] +> z4 +> (p100 ^ j) +> [1,0,1,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0] +> r) := by
  have h1 := ls .a (default <+ (p101 ^ j) <+ [1,1,0,1,0,1] <+ [1,1,0,1,0,1] <+ [1,0,1]) r
  have h2 := ls .a (default <+ (p101 ^ j) <+ [1,1,0,1,0,1] <+ [1,1,0,1,0,1] <+ [1]) ([1,0] +> r)
  have h3 := z0j (default <+ (p101 ^ j) <+ [1,1,0,1,0,1] <+ [1,0,1]) ([1,0,1,0] +> r)
  have h4 := ls .a (default <+ (p101 ^ j) <+ [1,1,0,1,0,1] <+ [1]) ([0,0,1,0,1,0,1,0] +> r)
  have h5 := z0j (default <+ (p101 ^ j) <+ [1,0,1]) ([1,0,0,0,1,0,1,0,1,0] +> r)
  have h6 := ls .a (default <+ (p101 ^ j) <+ [1]) ([0,0,1,0,1,0,0,0,1,0,1,0,1,0] +> r)
  have h7 := z0v j ([1,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0] +> r)
  refine zSt h1 (zSt h2 (zSt h3 (zSt h4 (zSt h5 (zSt h6 (z0a h7 rfl ?_))))))
  dsimp only [p100]
  rw [z0y]
  rfl
lemma z26 :
    (OV 8 (tab ^ 2 ++ [.a,.a,.a] ++ tb ^ 29) (0 :: o1 ^ 226)) [target_tm]⊢*
    (OV 9 ([.a,.a,.b,.a,.a,.a] ++ tb ^ 29) (0 :: o1 ^ 738)) := by
  have h1 := o2 8 ([.a,.b,.a,.a,.a] ++ tb ^ 28) (o1 ^ 226)
  have hend : z19 ([.a,.a,.b,.a,.a,.a] ++ tb ^ 29) := by
    refine Or.inr ⟨[.a,.a,.b,.a,.a,.a] ++ tb ^ 28,?_⟩
    have h29 : tb ^ 29 = tb ^ 28 ++ tb := (z02 tb 28).symm
    dsimp only [tb] at h29 ⊢
    simp only [h29,List.append_assoc,List.cons_append,List.nil_append]
  have h2 := z1f (ts := [.a,.a,.b,.a,.a,.a] ++ tb ^ 29) 227 [] 511 (z0S 8) hend (by decide)
  refine zPs (zPt (z0b h1 ?_ rfl) (z0b h2 ?_ ?_))
  · have h29 : tb ^ 29 = tb ^ 28 ++ tb := (z02 tb 28).symm
    dsimp only [tab,tb] at h29 ⊢
    simp only [z1k,h29,List.append_assoc,List.cons_append,List.nil_append]
  · have h29 : tb ^ 29 = tb ^ 28 ++ tb := (z02 tb 28).symm
    have h227 : (1 : Fin 2) :: (o1 ^ 226) = o1 ^ 227 ++ [] := by
      rw [List.append_nil]
      exact (z01 o1 226).symm
    dsimp only [o1,tb] at h29 h227 ⊢
    simp only [h29,h227,List.append_assoc,List.cons_append,List.nil_append]
  · dsimp only [o1]; rw [List.append_nil]
lemma z27 :
    (OV 9 ([.a,.a,.b,.a,.a,.a] ++ tb ^ 29) (0 :: o1 ^ 738)) [target_tm]⊢*
    (ck (tb ^ 9) [.a,.b] (0 :: (enc [.a,.b] ++ z1 ++ z1Y))) := by
  have h1 := z17 ([.a,.a,.a] ++ tb ^ 28) (default <+ (p101 ^ 9)) ((o1 ^ 738) +> default)
  have h2 := z16 (default <+ (p101 ^ 9) <+ [1,1,0,1,0,1]) ([0] +> enc (tb ^ 29) +> [0,1] +> (o1 ^ 738) +> default)
  have h3 := z0o ([.a] ++ tb ^ 28) (default <+ (p101 ^ 9) <+ [1,1,0,1,0,1] <+ [0,1,1,0,1,0,1]) ([1] +> (o1 ^ 738) +> default)
  have h4 := le0 (default <+ (p101 ^ 9) <+ [1,1,0,1,0,1] <+ [1,1,0,1,0,1]) (enc (tb ^ 27 ++ [.b]) +> [0,1,1] +> (o1 ^ 738) +> default)
  have h5 := z0o (tb ^ 27) (default <+ (p101 ^ 9) <+ [1,1,0,1,0,1] <+ [1,1,0,1,0,1] <+ [1,0,1,0,1]) ([1,1] +> (o1 ^ 738) +> default)
  have h6 := z25 9 (ems (tb ^ 27) +> [0,0,1,1,1] +> (o1 ^ 738) +> default)
  refine zPs (zPt (z0b h1 ?_ rfl) (z08 (z0a h2 ?_ rfl) (zPt (z0b h3 ?_ ?_) (z08 h4 (z07 (z0b h5 ?_ rfl) (z0a h6 rfl ?_))))))
  · have h29 : tb ^ 29 = tb ^ 28 ++ tb := (z02 tb 28).symm
    dsimp only [OV,tb,p101] at h29 ⊢
    simp only [h29,z0d,enc,tk,append_assoc,append_cons,append_nil,List.append_assoc,List.cons_append,List.nil_append]
  · have h29 : tb ^ 29 = tb ^ 28 ++ tb := (z02 tb 28).symm
    dsimp only [tb] at h29 ⊢
    simp only [h29,z0d,enc,tk,append_assoc,append_cons,append_nil,List.append_assoc,List.cons_append,List.nil_append]
  · have h29 : tb ^ 29 = tb ^ 28 ++ tb := (z02 tb 28).symm
    dsimp only [tb] at h29 ⊢
    simp only [h29,z0d,enc,tk,append_assoc,append_cons,append_nil,List.append_assoc,List.cons_append,List.nil_append]
  · have h28 : tb ^ 28 = tb ++ tb ^ 27 := z01 tb 27
    simp only [List.cons_append,List.nil_append,ems,em,z4,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,append_assoc,append_cons,append_nil,z0D]
    rw [h28]; dsimp only [tb]; simp only [z0d,enc,tk,append_assoc,append_cons,append_nil,List.append_assoc,List.cons_append,List.nil_append]
  · simp only [z0d,enc,tk,append_assoc,append_cons,append_nil,List.append_assoc,List.cons_append,List.nil_append]
  · dsimp only [ck,z1Y,z1,tb,p100]
    have hs := z0B 27 ([0,1,1,1] +> (o1 ^ 738) +> default)
    simp only [append_cons,append_nil] at hs
    have h741 : o1 ^ 741 = [1,1,1] ++ o1 ^ 738 := by
      have : (741 : Nat) = 3 + 738 := rfl
      rw [this,pow_add o1 3 738,z1l]
      rfl
    have h28 : ([Token.b] : List Token) ^ 28 = [Token.b] ++ [Token.b] ^ 27 := z01 [Token.b] 27
    rw [h741, h28]
    simp only [z0d, z0f, z0g, ems, em, enc, tk, List.append_assoc, List.cons_append, List.nil_append]
    generalize o1 ^ 738 = g738 at hs ⊢
    generalize ([1,0,0] : zF) ^ 27 = g27 at hs ⊢
    generalize ([0,1,0] : zF) ^ 27 = g27' at hs ⊢
    simp only [append_assoc,append_cons,append_nil,List.append_assoc,List.cons_append,List.nil_append,hs]
set_option maxRecDepth 4000000 in attribute [irreducible] ck OV
lemma z28 :
    (ck (tb ^ 9) [.a,.b] (0 :: (enc [.a,.b] ++ z1 ++ z1Y))) [target_tm]⊢*
    (z1X 4 [.b] 0 z1Y) := by
  have h1 := z1f (ts := []) 0 (enc [.a,.b] ++ z1 ++ z1Y) 1023 (z0S 9) (Or.inl rfl) (by decide)
  have h2 := o01 10 0 1023 (enc [.a,.b] ++ z1 ++ z1Y) (by decide)
  have h3 := z1q (tb ^ 9) [.a,.a,.a] (o1 ^ 1019 ++ enc [.a,.b] ++ z1 ++ z1Y)
  refine zPs (zPt (z0b h1 ?_ rfl) (zPt (z0b h2 ?_ rfl) (z0b h3 ?_ ?_)))
  · dsimp only [tb]
    simp only [zPz,List.append_assoc,List.cons_append,List.nil_append]
  · simp only [Nat.zero_mul,zPz]
  · have h10 : tb ^ 10 = .b :: (tb ^ 9) := z01 tb 9
    have h1021 : ([1] : zF) ^ 1021 = [1,1] ++ o1 ^ 1019 := by
      have : (1021 : Nat) = 2 + 1019 := rfl
      rw [this,pow_add [1] 2 1019,z1k]
      rfl
    rw [h10, h1021]
    generalize o1 ^ 1019 = g1019
    generalize z1Y = gz1Y
    dsimp only [tb,o1]
    simp only [zPz,List.append_assoc,List.cons_append,List.nil_append]
  · dsimp only [z1X]
    refine z1o rfl ?_
    have h1020 : (2 ^ (4 + 6) - 4 : Nat) = 1020 := rfl
    have hp := z04 (1 : Fin 2) 1019 (0 :: [1,0,0,0] ++ z1Y)
    generalize z1Y = gz1Y at hp ⊢
    rw [h1020]
    generalize ([1] : zF) ^ 1019 = g1019 at hp ⊢
    generalize ([1] : zF) ^ 1020 = g1020 at hp ⊢
    dsimp only [enc,tk,o1,z1] at hp ⊢
    simp only [zPz,List.append_assoc,List.cons_append,List.nil_append] at hp ⊢
    exact hp
lemma z29 (j : Nat) (q : List Token) (z : Nat) (rest : zF) :
    (z1X j q z rest) [target_tm]⊢⁺
    (ck (tb ^ (j + 8)) (tab ^ (2 ^ j * 16 - 1) ++ [.a,.a,.a])
      (o1 ^ (2 ^ j * 112 - 2) ++ enc q ++ z1 ++ o1 ^ z ++ rest)) := by
  have h2j : 2 ^ j >= 1 := Nat.one_le_two_pow
  have H0 : Num (j + 7) (1 + 2 ^ j * 64) 2 ([.a,.a] ++ tb ^ (j + 5) ++ [.a,.a]) := by
    have h := z1h 0 (j + 5)
    have hp : 2 ^ (0 + (j + 5) + 1) = 2 ^ j * 64 := by
      have : 0 + (j + 5) + 1 = j + 6 := by omega
      rw [this,z21 j 6]; rfl
    refine z0Q h (by omega) (by rw [hp]; omega) rfl ?_
    dsimp only [tb]
    simp only [zPz,List.append_assoc,List.cons_append,List.nil_append]
  have H1 : Num (j + 7) (2 ^ j * 80) 2 (tb ^ (j + 4) ++ [.a,.a] ++ tb ++ [.a,.a]) := by
    have h := z1h (j + 4) 1
    have hp1 : 2 ^ (j + 4) = 2 ^ j * 16 := by rw [z21 j 4]; rfl
    have hp2 : 2 ^ (j + 4 + 1 + 1) = 2 ^ j * 64 := by
      have : j + 4 + 1 + 1 = j + 6 := by omega
      rw [this,z21 j 6]; rfl
    refine z0Q h (by omega) (by rw [hp1,hp2]; omega) rfl ?_
    dsimp only [tb]
    simp only [z1j,List.append_assoc,List.cons_append,List.nil_append]
  have hp6 : 2 ^ (j + 6) = 2 ^ j * 64 := by rw [z21 j 6]; rfl
  have hp7 : 2 ^ (j + 7) = 2 ^ j * 128 := by rw [z21 j 7]; rfl
  have hg := z1Z (f := 2 ^ j * 32 - 2) (ts := [.a,.b]) (rem := 0)
    (m := z1 ++ enc q ++ z1 ++ o1 ^ z ++ rest) H0 H1 (by omega) (by omega)
  have hto := z1f (ts := tb ^ (2 ^ j * 32 - 2)) 0 (enc q ++ z1 ++ o1 ^ z ++ rest) (2 ^ j * 96 + 1)
    H1 (z20 _) (by omega)
  have ho := o01 (j + 8) (2 ^ j * 16 - 1) (2 ^ j * 96 + 1) (enc q ++ z1 ++ o1 ^ z ++ rest) (by omega)
  refine z08 (z0a hg ?_ rfl) (zPt (z0b hto ?_ rfl) (z0b ho ?_ ?_))
  · dsimp only [z1X]
    have hlen : (2 ^ j * 32 - 2 + 0) * 2 = 2 ^ (j + 6) - 4 := by omega
    simp only [hlen,List.append_assoc]
  · dsimp only [o1,z1]
    simp only [Nat.zero_mul,zPz,List.append_assoc,List.cons_append,List.nil_append]
  · have hw : j + 7 + 1 = j + 8 := by omega
    have hk : 2 ^ j * 32 - 2 = (2 ^ j * 16 - 1) * 2 := by omega
    have hf : 2 ^ j * 96 + 1 + 0 = 2 ^ j * 96 + 1 := by omega
    dsimp only [tb]
    simp only [hw,hk,hf]
  · have hp : 2 ^ j * 96 + 1 + (2 ^ j * 16 - 1) - 2 = 2 ^ j * 112 - 2 := by omega
    dsimp only [o1,tb,tab]
    simp only [hp,List.append_assoc]
lemma z2a (j : Nat) (q : List Token) (z : Nat) (rest : zF) :
    (ck (tb ^ (j + 8)) (tab ^ (2 ^ j * 16 - 1) ++ [.a,.a,.a])
      (o1 ^ (2 ^ j * 112 - 2) ++ enc (q ++ [.b]) ++ z1 ++ o1 ^ z ++ rest)) [target_tm]⊢⁺
    (OV (j + 9) (tab ^ (2 ^ j * 16 - 2) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q ++ [.b])
      (0 :: (o1 ^ (z + 2 ^ j * 456) ++ rest))) := by
  have h2j : 2 ^ j >= 1 := Nat.one_le_two_pow
  have hp8 : 2 ^ (j + 8) = 2 ^ j * 256 := by rw [z21 j 8]; rfl
  have H1 : Num (j + 8) (2 ^ j * 28 + 1) 4 (.a :: .a :: .b :: (tb ^ j ++ [.a,.a] ^ 3 ++ tb ^ 3)) := by
    have h := Num.Num_1 (j + 7) (2 ^ j * 14) 3 (.b :: (tb ^ j ++ [.a,.a] ^ 3 ++ tb ^ 3))
      (z0Q (Num.Num_0 (j + 6) (2 ^ j * 7) 3 (tb ^ j ++ [.a,.a] ^ 3 ++ tb ^ 3) (z1i j)) (by omega) (by omega) rfl rfl)
    exact z0Q h (by omega) (by omega) (by omega) rfl
  have H2 : Num (j + 8) (2 ^ j * 28 + 2) 4 (.b :: .a :: .a :: (tb ^ j ++ [.a,.a] ^ 3 ++ tb ^ 3)) := by
    have h := Num.Num_0 (j + 7) (2 ^ j * 14 + 1) 4 (.a :: .a :: (tb ^ j ++ [.a,.a] ^ 3 ++ tb ^ 3))
      (z0Q (Num.Num_1 (j + 6) (2 ^ j * 7) 3 (tb ^ j ++ [.a,.a] ^ 3 ++ tb ^ 3) (z1i j)) (by omega) (by omega) (by omega) rfl)
    exact z0Q h (by omega) (by omega) rfl rfl
  have hg := z1Z (f := 2 ^ j * 56 - 2) (ts := tab ^ (2 ^ j * 16 - 1) ++ [.a,.a,.a]) (rem := 1)
    (m := enc (q ++ [.b]) ++ z1 ++ o1 ^ z ++ rest) (z0S (j + 8)) H1 (by omega) (by omega)
  have hsw := z1p (tb ^ j ++ [.a,.a] ^ 3 ++ tb ^ 3)
    (tab ^ (2 ^ j * 16 - 1) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 2)) q (o1 ^ z ++ rest)
  have hts : (tab ^ (2 ^ j * 16 - 1) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 2)) ++ [.b] ++ q ++ [.b] =
      .a :: .b :: (tab ^ (2 ^ j * 16 - 2) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q ++ [.b]) := by
    have hk1 : 2 ^ j * 16 - 1 = 1 + (2 ^ j * 16 - 2) := by omega
    have hk2 : 2 ^ j * 56 - 2 + 1 = 2 ^ j * 56 - 1 := by omega
    rw [hk1,pow_add tab 1 (2 ^ j * 16 - 2)]
    dsimp only [tab]
    simp only [z1j,List.append_assoc,List.cons_append,List.nil_append,z1m,hk2]
  have hend : z19 (tab ^ (2 ^ j * 16 - 2) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q ++ [.b]) :=
    Or.inr ⟨tab ^ (2 ^ j * 16 - 2) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q,rfl⟩
  have hto := z1f (ts := tab ^ (2 ^ j * 16 - 2) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q ++ [.b])
    (z + 1) rest (2 ^ j * 456 - 1) H2 hend (by omega)
  refine z08 (z0a hg ?_ rfl) (zPt (z0b hsw ?_ rfl) (z0b hto ?_ ?_))
  · have hlen : (2 ^ j * 56 - 2 + 1) * 2 = 2 ^ j * 112 - 2 := by omega
    dsimp only [tb]
    simp only [hlen,List.append_assoc]
  · dsimp only [o1,z1]
    simp only [Nat.one_mul,z1k,List.append_assoc,List.cons_append,List.nil_append]
  · rw [hts]
    have hz : (1 : Fin 2) :: (o1 ^ z ++ rest) = o1 ^ (z + 1) ++ rest := by
      rw [z01 o1 z]; rfl
    dsimp only [o1] at hz ⊢
    rw [hz]
  · have hw : j + 8 + 1 = j + 9 := by omega
    have hf : 2 ^ j * 456 - 1 + (z + 1) = z + 2 ^ j * 456 := by omega
    dsimp only [o1]
    simp only [hw,hf]
def nq (j : Nat) (q : List Token) : List Token :=
  .b :: .a :: (tab ^ (2 ^ j * 16 - 5) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q)
lemma z2b (j : Nat) (q : List Token) (y : Nat) (rest : zF) :
    (OV (j + 9) (tab ^ (2 ^ j * 16 - 2) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q ++ [.b])
      (0 :: (o1 ^ y ++ rest))) [target_tm]⊢⁺
    (ck (tb ^ (j + 10)) [.a,.b]
      (0 :: (enc (.a :: (nq j q ++ [.b])) ++ z1 ++ o1 ^ (y + 2 ^ j * 1024 + 2) ++ rest))) := by
  have h2j : 2 ^ j >= 1 := Nat.one_le_two_pow
  have hp9 : 2 ^ (j + 9) = 2 ^ j * 512 := by rw [z21 j 9]; rfl
  have h1 := o2 (j + 9) (tab ^ (2 ^ j * 16 - 3) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q) (o1 ^ y ++ rest)
  have hend : z19 (.a :: .a :: .b :: .a :: .b :: (tab ^ (2 ^ j * 16 - 5) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q ++ [.b])) := by
    refine Or.inr ⟨.a :: .a :: .b :: .a :: .b :: (tab ^ (2 ^ j * 16 - 5) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q),?_⟩
    simp only [List.append_assoc,List.cons_append]
  have h2 := z1f (ts := .a :: .a :: .b :: .a :: .b :: (tab ^ (2 ^ j * 16 - 5) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q ++ [.b]))
    (y + 1) rest (2 ^ j * 1024 - 1) (z0S (j + 9)) hend (by omega)
  have h3 := o3 (j + 10) (tab ^ (2 ^ j * 16 - 5) ++ [.a,.a,.a] ++ tb ^ (2 ^ j * 56 - 1) ++ q) (o1 ^ (y + 2 ^ j * 1024) ++ rest)
  refine zPt (z0b h1 ?_ rfl) (zPt (z0b h2 ?_ rfl) (z0b h3 ?_ ?_))
  · have hk : 2 ^ j * 16 - 2 = 1 + (2 ^ j * 16 - 3) := by omega
    rw [hk,pow_add tab 1 (2 ^ j * 16 - 3)]
    dsimp only [tab]
    simp only [z1j,List.append_assoc,List.cons_append,List.nil_append]
  · have hk : 2 ^ j * 16 - 3 = 2 + (2 ^ j * 16 - 5) := by omega
    rw [hk,pow_add tab 2 (2 ^ j * 16 - 5)]
    have hy : (1 : Fin 2) :: (o1 ^ y ++ rest) = o1 ^ (y + 1) ++ rest := by
      rw [z01 o1 y]; rfl
    dsimp only [o1,tab] at hy ⊢
    rw [hy]
    simp only [z1k,List.append_assoc,List.cons_append,List.nil_append]
  · have hw : j + 9 + 1 = j + 10 := by omega
    have hf : 2 ^ j * 1024 - 1 + (y + 1) = y + 2 ^ j * 1024 := by omega
    dsimp only [o1]
    simp only [hw,hf]
  · dsimp only [nq,o1,z1,tb]
    have hy : (1 : Fin 2) :: 1 :: ([1] ^ (y + 2 ^ j * 1024) ++ rest) = [1] ^ (y + 2 ^ j * 1024 + 2) ++ rest := by
      have : y + 2 ^ j * 1024 + 2 = 2 + (y + 2 ^ j * 1024) := by omega
      rw [this,pow_add [1] 2 (y + 2 ^ j * 1024),z1k]
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    simp only [List.append_assoc,List.cons_append,List.nil_append,hy]
lemma z2c (j : Nat) (q : List Token) (z : Nat) (rest : zF) :
    (ck (tb ^ (j + 10)) [.a,.b]
      (0 :: (enc (.a :: (q ++ [.b])) ++ z1 ++ o1 ^ z ++ rest))) [target_tm]⊢⁺
    (z1X (j + 5) (q ++ [.b]) z rest) := by
  have h2j : 2 ^ j >= 1 := Nat.one_le_two_pow
  have hp10 : 2 ^ (j + 10) = 2 ^ j * 1024 := by rw [z21 j 10]; rfl
  have hp11 : 2 ^ (j + 5 + 6) = 2 ^ j * 2048 := by
    have : j + 5 + 6 = j + 11 := by omega
    rw [this,z21 j 11]; rfl
  have h1 := z1f (ts := []) 0 (enc (.a :: (q ++ [.b])) ++ z1 ++ o1 ^ z ++ rest) (2 ^ j * 2048 - 1)
    (z0S (j + 10)) (Or.inl rfl) (by omega)
  have h2 := o01 (j + 11) 0 (2 ^ j * 2048 - 1) (enc (.a :: (q ++ [.b])) ++ z1 ++ o1 ^ z ++ rest) (by omega)
  have h3 := z1q (tb ^ (j + 10)) [.a,.a,.a] (o1 ^ (2 ^ j * 2048 - 5) ++ enc (.a :: (q ++ [.b])) ++ z1 ++ o1 ^ z ++ rest)
  refine zPt (z0b h1 ?_ rfl) (zPt (z0b h2 ?_ rfl) (z0b h3 ?_ ?_))
  · dsimp only [tb]
    simp only [zPz,List.append_assoc,List.cons_append,List.nil_append]
  · have hw : j + 10 + 1 = j + 11 := by omega
    have hf : 2 ^ j * 2048 - 1 + 0 = 2 ^ j * 2048 - 1 := by omega
    simp only [hw,hf,Nat.zero_mul,zPz]
  · have hj : j + 11 = 1 + (j + 10) := by omega
    have hp : 2 ^ j * 2048 - 1 + 0 - 2 = 2 + (2 ^ j * 2048 - 5) := by omega
    rw [hj,pow_add [Token.b] 1 (j + 10),hp,pow_add [1] 2 (2 ^ j * 2048 - 5)]
    dsimp only [o1,tb]
    simp only [zPz,z1j,z1k,List.append_assoc,List.cons_append,List.nil_append]
  · dsimp only [z1X]
    refine z1o (by omega) ?_
    have hp := z04 (1 : Fin 2) (2 ^ j * 2048 - 5) (0 :: (enc (q ++ [.b]) ++ [0] ++ o1 ^ z ++ rest))
    have hlen : 2 ^ j * 2048 - 5 + 1 = 2 ^ (j + 5 + 6) - 4 := by omega
    dsimp only [enc,tk,o1,z1] at hp ⊢
    simp only [hlen,List.append_assoc,List.cons_append,List.nil_append] at hp ⊢
    exact hp
lemma z2d (j : Nat) (q : List Token) (z : Nat) (rest : zF) :
    (z1X j (q ++ [.b]) z rest) [target_tm]⊢⁺
    (z1X (j + 5) (nq j q ++ [.b]) (z + 2 ^ j * 1480 + 2) rest) := by
  have h0 := z29 j (q ++ [.b]) z rest
  have h1 := z2a j q z rest
  have h2 := z2b j q (z + 2 ^ j * 456) rest
  have h3 := z2c j (nq j q) (z + 2 ^ j * 1480 + 2) rest
  refine zPt h0 (zPt h1 (zPt (z0b h2 rfl ?_) h3))
  have hz : z + 2 ^ j * 456 + 2 ^ j * 1024 + 2 = z + 2 ^ j * 1480 + 2 := by omega
  simp only [hz]
lemma z2e :
    (init []) [target_tm]⊢* (z1X 4 [.b] 0 z1Y) :=
  zSt z1W
    (zSt z22
      (zSt z23
        (zSt z24
          (zSt z26
            (zSt z27 z28)))))
lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
def Inv (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ j q z,c = z1X j (q ++ [.b]) z z1Y
lemma z2f (m : Nat) :
    ∃ N ≥ m,∃ c,multiStep target_tm (init []) N = some c /\ Inv c := by
  induction m with
  | zero =>
    rcases z2e with ⟨k,hk⟩
    exact ⟨k,Nat.zero_le k,_,hk,⟨4,[],0,rfl⟩⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,c,h_ms,⟨j,q,z,rfl⟩⟩
    rcases z2d j q z z1Y with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,_,zMt target_tm _ _ _ N k h_ms h_step_k,⟨j + 5,nq j q,z + 2 ^ j * 1480 + 2,rfl⟩⟩

end Solution
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases z2f (n + 1) with ⟨N,hN,c',h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

end BusyBeaver.M_1RBHHH_0RC1LF_1LC1LD_1RE0RA_0RD1RF_0LD0LF
