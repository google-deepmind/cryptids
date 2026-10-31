/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LC_1RC1LB_1LD0RB_0LE1RD_---0LF_0LA1LF` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LC_1RC1LB_1LD0RB_0LE1RD_---0LF_0LA1LF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LC_1RC1LB_1LD0RB_0LE1RD_HHH0LF_0LA1LF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LC_1RC1LB_1LD0RB_0LE1RD_---0LF_0LA1LF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 4, 0 => none
  | 4, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 5, Stmt.write 1 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev stC : Fin 6 := 2
abbrev stD : Fin 6 := 3
abbrev stF : Fin 6 := 5
abbrev s0 : Fin 2 := 0
abbrev s1 : Fin 2 := 1
abbrev bot : ℕ := 1
@[reducible] def tm : Machine (Fin 2) (Fin 6) := target_tm
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
local infixr:67 " ∷ " => ListBlank.cons
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2000000

@[simp] lemma zMz (M : Machine zG_ zL_) (config : Cfg zG_ zL_) :
    multiStep M config 0 = some config := rfl
lemma zMs (M : Machine zG_ zL_) (config : Cfg zG_ zL_) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] lemma z00 : s0 ∷ (default : zB) = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : zB).head = 0 := rfl
@[simp] lemma zDt : (default : zB).tail = default := rfl
@[simp] lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[simp] lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = a ∷ (l +> s) := rfl
@[simp] lemma append_assoc (l1 l2 : zF) (s : zB) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, append_cons, ih]

lemma zSm {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (M : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [M]⊢ c_2) :
    c_1 [M]⊢^{1} c_2 := by simp [zMs, h]
lemma z01 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (M : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [M]⊢ c_2) :
    c_1 [M]⊢⁺ c_2 := ⟨1, by decide, zSm M c_1 c_2 h⟩
lemma zMa {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (M : Machine zG_ zL_) (c_1 : Cfg zG_ zL_) (n m : Nat) :
    multiStep M c_1 (n + m) = (multiStep M c_1 n).bind (fun c_2 => multiStep M c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (M : Machine zG_ zL_) (c_1 c_2 c_3 : Cfg zG_ zL_) (n m : Nat)
    (h1 : c_1 [M]⊢^{n} c_2) (h2 : c_2 [M]⊢^{m} c_3) :
    c_1 [M]⊢^{n+m} c_3 := by
  rw [zMa, h1]; simp [h2]
lemma zPs {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {M : Machine zG_ zL_} {c_1 c_2 : Cfg zG_ zL_} (h : c_1 [M]⊢⁺ c_2) :
    c_1 [M]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma zPt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {M : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h1 : c_1 [M]⊢⁺ c_2) (h2 : c_2 [M]⊢⁺ c_3) : c_1 [M]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h1; obtain ⟨m, m_pos, hm⟩ := h2
  exact ⟨n + m, by omega, zMt M c_1 c_2 c_3 n m hn hm⟩
lemma z02 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {M : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h1 : c_1 [M]⊢⁺ c_2) (h2 : c_2 [M]⊢* c_3) : c_1 [M]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h1; obtain ⟨m, hm⟩ := h2
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt M c_1 c_2 c_3 n m hn hm⟩
lemma z03 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {M : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h1 : c_1 [M]⊢ c_2) (h2 : c_2 [M]⊢* c_3) : c_1 [M]⊢⁺ c_3 :=
  z02 (z01 M c_1 c_2 h1) h2
lemma zStP {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {M : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h1 : c_1 [M]⊢* c_2) (h2 : c_2 [M]⊢⁺ c_3) : c_1 [M]⊢⁺ c_3 := by
  obtain ⟨n, hn⟩ := h1; obtain ⟨m, m_pos, hm⟩ := h2
  exact ⟨n + m, by omega, zMt M c_1 c_2 c_3 n m hn hm⟩

@[simp] lemma pow_zero_eq (l : zF) : l ^ 0 = [] := rfl
@[simp] lemma pow_succ_eq (l : zF) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl

local macro "finish" : tactic =>
  `(tactic| exists 0 <;> rfl)
local macro "gstep" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by
      (try simp only [pow_zero_eq, pow_succ_eq, List.singleton_append, List.cons_append,
        List.nil_append, append_nil, append_cons, Turing.ListBlank.head_cons, zDh]);
      rfl) ?_ <;>
    simp only [pow_zero_eq, pow_succ_eq, List.singleton_append, List.cons_append, List.nil_append,
      append_nil, append_cons, Turing.Tape.move, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons, Tape.write, z00, zDh, zDt])
local macro "execute" : tactic =>
  `(tactic| iterate 20 (try (any_goals (first | finish | gstep))))

/-! ## Section 1: Stack Encoding `D_cfg` & Four Atomic Transition Rules -/

def encL : List ℕ → zB
  | [] => default
  | k :: L => ([s1] ^ k) +> (s0 ∷ encL L)

def D_cfg (L : List ℕ) (R : zB) : Cfg (Fin 2) (Fin 6) :=
  ⟨some stD, ⟨s0, encL L, R⟩⟩

lemma ones_zero_eq (s : zB) : ([s1] ^ 0) +> s = s := rfl
lemma ones_succ_eq (n : ℕ) (s : zB) :
    ([s1] ^ (n + 1)) +> s = s1 ∷ (([s1] ^ n) +> s) := rfl
lemma ones_add_merge (a b : ℕ) (s : zB) :
    ([s1] ^ a) +> (([s1] ^ b) +> s) = ([s1] ^ (a + b)) +> s := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [Nat.add_right_comm, ones_succ_eq, ih, ← ones_succ_eq]

lemma zeros_succ_eq (n : ℕ) (s : zB) :
    ([s0] ^ (n + 1)) +> s = s0 ∷ (([s0] ^ n) +> s) := rfl
lemma zeros_add_merge (a b : ℕ) (s : zB) :
    ([s0] ^ a) +> (([s0] ^ b) +> s) = ([s0] ^ (a + b)) +> s := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [Nat.add_right_comm, zeros_succ_eq, ih, ← zeros_succ_eq]

lemma scanL_F' (a : ℕ) (l r : zB) :
    (⟨some stF, ⟨s1, ([s1] ^ a) +> (s0 ∷ l), r⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺
    (⟨some stF, ⟨s0, l, ([s1] ^ (a + 1)) +> r⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
  induction a generalizing r with
  | zero => simp only [ones_zero_eq, list_nat_repeat, List.singleton_append, List.nil_append,
      append_cons, append_nil]; execute
  | succ a ih =>
    rw [ones_succ_eq]
    have h1 : (⟨some stF, ⟨s1, s1 ∷ (([s1] ^ a) +> (s0 ∷ l)), r⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺
        (⟨some stF, ⟨s1, ([s1] ^ a) +> (s0 ∷ l), s1 ∷ r⟩⟩ : Cfg (Fin 2) (Fin 6)) := by execute
    have h2 := ih (s1 ∷ r)
    have heq : ([s1] ^ (a + 1)) +> (s1 ∷ r) = ([s1] ^ (a + 2)) +> r := by
      have : s1 ∷ r = ([s1] ^ 1) +> r := rfl
      rw [this, ones_add_merge]
    rw [heq] at h2
    exact zPt h1 h2

lemma walkR_BBC (a : ℕ) (l r : zB) :
    (⟨some stC, ⟨s1, l, ([s1] ^ a) +> (s0 ∷ r)⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢*
    (⟨some stC, ⟨s1, ([s1] ^ a) +> l, s0 ∷ r⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
  induction a generalizing l with
  | zero => exists 0
  | succ a ih =>
    rw [ones_succ_eq]
    have h1 : (⟨some stC, ⟨s1, l, s1 ∷ (([s1] ^ a) +> (s0 ∷ r))⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺
        (⟨some stC, ⟨s1, s1 ∷ l, ([s1] ^ a) +> (s0 ∷ r)⟩⟩ : Cfg (Fin 2) (Fin 6)) := by execute
    have h2 := ih (s1 ∷ l)
    have heq : ([s1] ^ a) +> (s1 ∷ l) = ([s1] ^ (a + 1)) +> l := by
      have : s1 ∷ l = ([s1] ^ 1) +> l := rfl
      rw [this, ones_add_merge]
    rw [heq] at h2
    exact zPs (z02 h1 h2)

lemma scanR_D (d : ℕ) (l r : zB) :
    (⟨some stD, ⟨s1, l, ([s1] ^ d) +> (s0 ∷ r)⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺
    (⟨some stD, ⟨s0, ([s1] ^ (d + 1)) +> l, r⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
  induction d generalizing l with
  | zero => simp only [ones_zero_eq, list_nat_repeat, List.singleton_append, List.nil_append,
      append_cons, append_nil]; execute
  | succ d ih =>
    rw [ones_succ_eq]
    have h1 : (⟨some stD, ⟨s1, l, s1 ∷ (([s1] ^ d) +> (s0 ∷ r))⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺
        (⟨some stD, ⟨s1, s1 ∷ l, ([s1] ^ d) +> (s0 ∷ r)⟩⟩ : Cfg (Fin 2) (Fin 6)) := by execute
    have h2 := ih (s1 ∷ l)
    have heq : ([s1] ^ (d + 1)) +> (s1 ∷ l) = ([s1] ^ (d + 2)) +> l := by
      have : s1 ∷ l = ([s1] ^ 1) +> l := rfl
      rw [this, ones_add_merge]
    rw [heq] at h2
    exact zPt h1 h2

lemma rule_merge (a b : ℕ) (L : List ℕ) (R : zB) :
    (D_cfg ((a + 2) :: 1 :: (b + 2) :: L) R) [tm]⊢⁺
    (D_cfg ((b + 4) :: L) (([s1] ^ (a + 1)) +> ([s0, s0] +> R))) := by
  simp only [D_cfg, encL]
  rw [ones_succ_eq (a + 1), ones_succ_eq a, ones_succ_eq (b + 1)]
  have h1 : (⟨some stD, ⟨s0, s1 ∷ (s1 ∷ (([s1] ^ a) +> (s0 ∷ (([s1] ^ 1) +>
      (s0 ∷ (s1 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L)))))))), R⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺
      (⟨some stF, ⟨s1, ([s1] ^ a) +> (s0 ∷ (([s1] ^ 1) +>
        (s0 ∷ (s1 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L)))))), [s0, s0] +> R⟩⟩ : Cfg (Fin 2) (Fin 6)) :=
    by execute
  have h2 := scanL_F' a (([s1] ^ 1) +> (s0 ∷ (s1 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L)))))
    ([s0, s0] +> R)
  refine zPt (zPt h1 h2) ?_
  rw [ones_succ_eq (b + 3), ones_succ_eq (b + 2), ones_succ_eq (b + 1)]
  execute

lemma rule_push (a : ℕ) (L : List ℕ) (R : zB) :
    (D_cfg ((a + 2) :: 1 :: 1 :: L) R) [tm]⊢⁺
    (D_cfg (3 :: L) (([s1] ^ (a + 1)) +> ([s0, s0] +> R))) := by
  simp only [D_cfg, encL]
  rw [ones_succ_eq (a + 1), ones_succ_eq a]
  have h1 : (⟨some stD, ⟨s0, s1 ∷ (s1 ∷ (([s1] ^ a) +> (s0 ∷ (([s1] ^ 1) +>
      (s0 ∷ (([s1] ^ 1) +> (s0 ∷ encL L))))))), R⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺
      (⟨some stF, ⟨s1, ([s1] ^ a) +> (s0 ∷ (([s1] ^ 1) +>
        (s0 ∷ (([s1] ^ 1) +> (s0 ∷ encL L))))), [s0, s0] +> R⟩⟩ : Cfg (Fin 2) (Fin 6)) :=
    by execute
  have h2 := scanL_F' a (([s1] ^ 1) +> (s0 ∷ (([s1] ^ 1) +> (s0 ∷ encL L)))) ([s0, s0] +> R)
  refine zPt (zPt h1 h2) ?_
  execute

lemma rule_pop (a b d : ℕ) (L : List ℕ) (R : zB) :
    (D_cfg ((a + 2) :: (b + 2) :: L) (([s1] ^ d) +> (s0 ∷ R))) [tm]⊢⁺
    (D_cfg ((d + 2) :: (a + 1) :: (b + 1) :: L) R) := by
  simp only [D_cfg, encL]
  rw [ones_succ_eq (a + 1), ones_succ_eq a, ones_succ_eq (b + 1), ones_succ_eq b]
  set r0 := ([s1] ^ d) +> (s0 ∷ R)
  have h1 : (⟨some stD, ⟨s0, s1 ∷ (s1 ∷ (([s1] ^ a) +>
      (s0 ∷ (s1 ∷ (s1 ∷ (([s1] ^ b) +> (s0 ∷ encL L))))))), r0⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺
      (⟨some stF, ⟨s1, ([s1] ^ a) +> (s0 ∷ (s1 ∷ (s1 ∷ (([s1] ^ b) +> (s0 ∷ encL L))))),
        [s0, s0] +> r0⟩⟩ : Cfg (Fin 2) (Fin 6)) := by execute
  have h2 := scanL_F' a (s1 ∷ (s1 ∷ (([s1] ^ b) +> (s0 ∷ encL L)))) ([s0, s0] +> r0)
  rw [ones_succ_eq a] at h2
  have h3 : (⟨some stF, ⟨s0, s1 ∷ (s1 ∷ (([s1] ^ b) +> (s0 ∷ encL L))),
      s1 ∷ (([s1] ^ a) +> ([s0, s0] +> r0))⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺
      (⟨some stC, ⟨s1, s1 ∷ (s0 ∷ (s1 ∷ (([s1] ^ b) +> (s0 ∷ encL L)))),
        ([s1] ^ a) +> (s0 ∷ (s0 ∷ r0))⟩⟩ : Cfg (Fin 2) (Fin 6)) := by execute
  have h4 := walkR_BBC a (s1 ∷ (s0 ∷ (s1 ∷ (([s1] ^ b) +> (s0 ∷ encL L))))) (s0 ∷ r0)
  have h4_eq : ([s1] ^ a) +> (s1 ∷ (s0 ∷ (s1 ∷ (([s1] ^ b) +> (s0 ∷ encL L))))) =
      ([s1] ^ (a + 1)) +> (s0 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L))) := by
    rw [← ones_succ_eq b]
    have : s1 ∷ (s0 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L))) =
        ([s1] ^ 1) +> (s0 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L))) := rfl
    rw [this, ones_add_merge]
  rw [h4_eq] at h4
  have h5 : (⟨some stC, ⟨s1, ([s1] ^ (a + 1)) +> (s0 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L))),
      s0 ∷ (s0 ∷ r0)⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺
      (⟨some stD, ⟨s1, s1 ∷ (s0 ∷ (([s1] ^ (a + 1)) +> (s0 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L))))),
        r0⟩⟩ : Cfg (Fin 2) (Fin 6)) := by execute
  have h6 := scanR_D d
      (s1 ∷ (s0 ∷ (([s1] ^ (a + 1)) +> (s0 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L)))))) R
  have h6_eq : ([s1] ^ (d + 1)) +>
      (s1 ∷ (s0 ∷ (([s1] ^ (a + 1)) +> (s0 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L)))))) =
      ([s1] ^ (d + 2)) +>
        (s0 ∷ (([s1] ^ (a + 1)) +> (s0 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L))))) := by
    have : s1 ∷ (s0 ∷ (([s1] ^ (a + 1)) +> (s0 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L))))) =
        ([s1] ^ 1) +>
          (s0 ∷ (([s1] ^ (a + 1)) +> (s0 ∷ (([s1] ^ (b + 1)) +> (s0 ∷ encL L))))) := rfl
    rw [this, ones_add_merge]
  rw [h6_eq] at h6
  exact zPt (z02 (zPt (zPt h1 h2) h3) h4) (zPt h5 h6)

lemma rule_edge (d : ℕ) (R : zB) :
    (D_cfg [bot + 3] (([s1] ^ d) +> (s0 ∷ R))) [tm]⊢⁺ (D_cfg [d + 2, bot + 3] R) := by
  simp only [D_cfg, encL]
  set r0 := ([s1] ^ d) +> (s0 ∷ R)
  have h1 : (⟨some stD, ⟨s0, ([s1] ^ (bot + 3)) +> (s0 ∷ default), r0⟩⟩ : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺
      (⟨some stD, ⟨s1, s1 ∷ (s0 ∷ (([s1] ^ (bot + 3)) +> (s0 ∷ default))), r0⟩⟩ : Cfg (Fin 2) (Fin 6)) :=
    by execute
  have h2 := scanR_D d (s1 ∷ (s0 ∷ (([s1] ^ (bot + 3)) +> (s0 ∷ default)))) R
  have h2_eq : ([s1] ^ (d + 1)) +> (s1 ∷ (s0 ∷ (([s1] ^ (bot + 3)) +> (s0 ∷ default)))) =
      ([s1] ^ (d + 2)) +> (s0 ∷ (([s1] ^ (bot + 3)) +> (s0 ∷ default))) := by
    have : s1 ∷ (s0 ∷ (([s1] ^ (bot + 3)) +> (s0 ∷ default))) =
        ([s1] ^ 1) +> (s0 ∷ (([s1] ^ (bot + 3)) +> (s0 ∷ default))) := rfl
    rw [this, ones_add_merge]
  rw [h2_eq] at h2
  exact zPt h1 h2

lemma rule_pop_end (a b : ℕ) (L : List ℕ) :
    (D_cfg ((a + 2) :: (b + 2) :: L) default) [tm]⊢⁺
    (D_cfg (2 :: (a + 1) :: (b + 1) :: L) default) := by
  have h := rule_pop a b 0 L default
  simp only [ones_zero_eq, z00] at h
  exact h

def encR : List ℕ → zB → zB
  | [], rest => rest
  | d :: R, rest => ([s1] ^ d) +> (s0 ∷ encR R rest)

lemma r_merge (a b : ℕ) (L R : List ℕ) (rest : zB) :
    (D_cfg ((a + 2) :: 1 :: (b + 2) :: L) (encR R rest)) [tm]⊢⁺
    (D_cfg ((b + 4) :: L) (encR ((a + 1) :: 0 :: R) rest)) :=
  rule_merge a b L (encR R rest)

lemma r_push (a : ℕ) (L R : List ℕ) (rest : zB) :
    (D_cfg ((a + 2) :: 1 :: 1 :: L) (encR R rest)) [tm]⊢⁺
    (D_cfg (3 :: L) (encR ((a + 1) :: 0 :: R) rest)) :=
  rule_push a L (encR R rest)

lemma r_pop (a b d : ℕ) (L R : List ℕ) (rest : zB) :
    (D_cfg ((a + 2) :: (b + 2) :: L) (encR (d :: R) rest)) [tm]⊢⁺
    (D_cfg ((d + 2) :: (a + 1) :: (b + 1) :: L) (encR R rest)) :=
  rule_pop a b d L (encR R rest)

lemma r_edge (d : ℕ) (R : List ℕ) (rest : zB) :
    (D_cfg [bot + 3] (encR (d :: R) rest)) [tm]⊢⁺
    (D_cfg [d + 2, bot + 3] (encR R rest)) :=
  rule_edge d (encR R rest)

lemma r_mp (a z : ℕ) (L R : List ℕ) (rest : zB) :
    (D_cfg ((a + 2) :: 1 :: (z + 1) :: L) (encR R rest)) [tm]⊢⁺
    (D_cfg ((z + 3) :: L) (encR ((a + 1) :: 0 :: R) rest)) := by
  cases z with
  | zero => exact r_push a L R rest
  | succ b => exact r_merge a b L R rest

lemma D_cfg_congr {L1 L2 : List ℕ} {R1 R2 : zB} (hL : L1 = L2) (hR : R1 = R2) :
    D_cfg L1 R1 = D_cfg L2 R2 := by
  subst hL; subst hR; rfl

def dStep (L R : List ℕ) : Option (List ℕ × List ℕ) :=
  match L with
  | [] => none
  | [x] =>
    match R with
    | [] => none
    | d :: R0 => if x == bot + 3 then some ([d + 2, bot + 3], R0) else none
  | x :: y :: L2 =>
    match x, y with
    | a + 2, 1 =>
      match L2 with
      | (z + 1) :: L0 => some ((z + 3) :: L0, (a + 1) :: 0 :: R)
      | _ => none
    | a + 2, b + 2 =>
      match R with
      | [] => none
      | d :: R0 => some ((d + 2) :: (a + 1) :: (b + 1) :: L2, R0)
    | _, _ => none

def dRun : ℕ → List ℕ → List ℕ → Option (List ℕ × List ℕ)
  | 0, L, R => some (L, R)
  | n + 1, L, R =>
      match dStep L R with
      | none => none
      | some (L', R') => dRun n L' R'

lemma dStep_sound (L R L' R' : List ℕ) (rest : zB) (h : dStep L R = some (L', R')) :
    (D_cfg L (encR R rest)) [tm]⊢⁺ (D_cfg L' (encR R' rest)) := by
  unfold dStep at h
  cases L with
  | nil => simp at h
  | cons x L1 =>
    cases L1 with
    | nil =>
      cases R with
      | nil => simp at h
      | cons d R0 =>
        simp only at h
        split at h
        · rename_i hx
          have hx' : x = bot + 3 := beq_iff_eq.mp hx
          subst hx'
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact r_edge d R0 rest
        · simp at h
    | cons y L2 =>
      simp only at h
      cases x with
      | zero => simp at h
      | succ x1 =>
        cases x1 with
        | zero => simp at h
        | succ a =>
          cases y with
          | zero => simp at h
          | succ y1 =>
            cases y1 with
            | zero =>
              cases L2 with
              | nil => simp at h
              | cons z1 L0 =>
                cases z1 with
                | zero => simp at h
                | succ z =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact r_mp a z L0 R rest
            | succ b =>
              cases R with
              | nil => simp at h
              | cons d R0 =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact r_pop a b d L2 R0 rest

lemma dRun_sound : ∀ (n : ℕ) (L R L' R' : List ℕ) (rest : zB),
    dRun (n + 1) L R = some (L', R') →
    (D_cfg L (encR R rest)) [tm]⊢⁺ (D_cfg L' (encR R' rest)) := by
  intro n
  induction n with
  | zero =>
    intro L R L' R' rest h
    simp only [dRun] at h
    cases hs : dStep L R with
    | none => rw [hs] at h; cases h
    | some p =>
      obtain ⟨Lp, Rp⟩ := p
      rw [hs] at h
      simp only [dRun, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact dStep_sound L R Lp Rp rest hs
  | succ n ih =>
    intro L R L' R' rest h
    simp only [dRun] at h
    cases hs : dStep L R with
    | none => rw [hs] at h; cases h
    | some p =>
      rw [hs] at h
      exact zPt (dStep_sound L R p.1 p.2 rest hs) (ih p.1 p.2 L' R' rest h)

lemma dRun_eq (n : ℕ) (L R L1 R1 : List ℕ) (rest : zB) {c1 c2 : Cfg (Fin 2) (Fin 6)}
    (hr : dRun (n + 1) L R = some (L1, R1))
    (hc1 : D_cfg L (encR R rest) = c1)
    (hc2 : D_cfg L1 (encR R1 rest) = c2) :
    c1 [tm]⊢⁺ c2 := by
  rw [← hc1, ← hc2]
  exact dRun_sound n L R L1 R1 rest hr

lemma pow_add_split (a b : ℕ) (s : zB) :
    ([s1] ^ (a + b)) +> s = ([s1] ^ a) +> (([s1] ^ b) +> s) :=
  (ones_add_merge a b s).symm
lemma ones_two (s : zB) : ([s1] ^ 2) +> s = s1 ∷ (s1 ∷ s) := rfl
lemma ones_four (s : zB) : ([s1] ^ 4) +> s = s1 ∷ (s1 ∷ (s1 ∷ (s1 ∷ s))) := rfl
lemma pow_two_add (n : ℕ) (s : zB) :
    ([s1] ^ (2 + n)) +> s = s1 ∷ (s1 ∷ (([s1] ^ n) +> s)) := by
  rw [pow_add_split, ones_two]
lemma pow_four_add (n : ℕ) (s : zB) :
    ([s1] ^ (4 + n)) +> s = s1 ∷ (s1 ∷ (s1 ∷ (s1 ∷ (([s1] ^ n) +> s)))) := by
  rw [pow_add_split, ones_four]

local macro "rclose_eq" : tactic =>
  `(tactic| refine D_cfg_congr
      (by simp only [Bool.toNat, cond_false, cond_true, List.append_eq, List.cons_append,
        List.nil_append, List.singleton_append]; try ring_nf)
      (by simp only [encR, ones_zero_eq, ones_add_merge, pow_succ_eq, pow_zero_eq,
        List.append_eq, List.cons_append, List.nil_append, List.singleton_append,
        append_cons, append_nil, z00]
          try ring_nf
          try simp only [pow_two_add, pow_four_add, ones_two, ones_four, pow_succ_eq,
            pow_zero_eq, List.singleton_append, List.nil_append, append_cons, append_nil, z00]))

local macro "run_d" n:num L:term "," R:term "," rest:term : tactic =>
  `(tactic| refine dRun_eq $n $L $R _ _ $rest rfl (by rclose_eq) (by rclose_eq))

/-! ## Section 2: Bitstring Encoding & Linear Stack-Peeling Engine -/

def pairVal : Bool → Bool → ℕ
  | false, false => 2
  | false, true  => 1
  | true,  false => 3
  | true,  true  => 2

def pairValPred : Bool → Bool → ℕ
  | false, false => 1
  | false, true  => 0
  | true,  false => 2
  | true,  true  => 1

def encS : Bool → List Bool → List ℕ
  | _, [] => []
  | prev, b :: bs => 2 :: pairVal prev b :: encS b bs

def bitW : Bool → ℕ
  | false => 2
  | true  => 1

def weight2 : List Bool → ℕ
  | [] => 0
  | b :: bs => bitW b + weight2 bs

def dropChain : Bool → List Bool → ℕ
  | _, [] => 0
  | cc, b :: bs => bitW cc + dropChain b bs

def lastAfter : Bool → List Bool → Bool
  | prev, [] => prev
  | _, b :: bs => lastAfter b bs

def lastBit (s : List Bool) : Bool := lastAfter false s

def bitTape : Bool → zF
  | false => [s0, s0]
  | true  => [s1, s0, s0]

def peelTape : List Bool → zB → zB
  | [], acc => acc
  | b :: bs, acc => peelTape bs (bitTape b +> acc)

def stackTape : List Bool → zB → zB
  | [], R0 => R0
  | b :: bs, R0 => bitTape b +> stackTape bs R0

def peelCfg : Bool → ℕ → ℕ → List ℕ → zB → Cfg (Fin 2) (Fin 6)
  | false, k, w, tailL, acc =>
      D_cfg ([w + 2, 1, 1] ++ tailL) (([s1] ^ (2 * k)) +> (s0 ∷ acc))
  | true, 0, w, tailL, acc =>
      D_cfg ([3, 1] ++ tailL) (([s1] ^ (w + 1)) +> ([s0, s0] +> acc))
  | true, k' + 1, w, tailL, acc =>
      D_cfg ([3, 1] ++ tailL) (([s1] ^ (w + 1)) +> ([s0, s0] +> (([s1] ^ (2 * k')) +> acc)))

lemma peelCfg_true_encR (k' w : ℕ) (tailL : List ℕ) (acc0 : zB) :
    peelCfg true (k' + 1) w tailL ([s1, s0, s0] +> acc0) =
    D_cfg ([3, 1] ++ tailL) (encR [w + 1, 0, 2 * k' + 1, 0] acc0) := by
  dsimp only [peelCfg, encR]
  have hm : ([s1] ^ (2 * k')) +> ([s1, s0, s0] +> acc0) =
      ([s1] ^ (2 * k' + 1)) +> ([s0, s0] +> acc0) := by
    change ([s1] ^ (2 * k')) +> (([s1] ^ 1) +> ([s0, s0] +> acc0)) = _
    rw [ones_add_merge]
  rw [hm]; rfl

lemma peel_step_00 (k w : ℕ) (tailL : List ℕ) (acc : zB) :
    (peelCfg false k w (2 :: 2 :: tailL) acc) [tm]⊢⁺
    (peelCfg false (k + 1) (w + 2) tailL ([s0, s0] +> acc)) := by
  dsimp only [peelCfg]
  run_d 9 ((w + 2) :: 1 :: 1 :: 2 :: 2 :: tailL), [2 * k], acc

lemma peel_step_01 (k w : ℕ) (tailL : List ℕ) (acc : zB) :
    (peelCfg false k w (2 :: 1 :: tailL) acc) [tm]⊢⁺
    (peelCfg true (k + 1) (w + 1) tailL ([s1, s0, s0] +> acc)) := by
  rw [peelCfg_true_encR]; dsimp only [peelCfg]
  run_d 5 ((w + 2) :: 1 :: 1 :: 2 :: 1 :: tailL), [2 * k], acc

lemma peel_step_10 (k' w : ℕ) (tailL : List ℕ) (acc0 : zB) :
    (peelCfg true (k' + 1) w (2 :: 3 :: tailL) ([s1, s0, s0] +> acc0)) [tm]⊢⁺
    (peelCfg false (k' + 2) (w + 2) tailL ([s0, s0] +> ([s1, s0, s0] +> acc0))) := by
  rw [peelCfg_true_encR]; dsimp only [peelCfg]
  have hr : ([s1] ^ (2 * (k' + 2))) +> (s0 ∷ ([s0, s0] +> ([s1, s0, s0] +> acc0))) =
      encR [2 * (k' + 2), 0, 0, 1, 0] acc0 := rfl
  rw [hr]
  run_d 22 ([3, 1, 2, 3] ++ tailL), [w + 1, 0, 2 * k' + 1, 0], acc0

lemma peel_step_11 (k' w : ℕ) (tailL : List ℕ) (acc0 : zB) :
    (peelCfg true (k' + 1) w (2 :: 2 :: tailL) ([s1, s0, s0] +> acc0)) [tm]⊢⁺
    (peelCfg true (k' + 2) (w + 1) tailL ([s1, s0, s0] +> ([s1, s0, s0] +> acc0))) := by
  rw [peelCfg_true_encR, peelCfg_true_encR]
  run_d 18 ([3, 1, 2, 2] ++ tailL), [w + 1, 0, 2 * k' + 1, 0], acc0

lemma peel_all (s : List Bool) (prev : Bool) (k w : ℕ) (tailL : List ℕ) (acc : zB)
    (h_inv : prev = true → ∃ k' acc0, k = k' + 1 ∧ acc = [s1, s0, s0] +> acc0) :
    (peelCfg prev k w (encS prev s ++ tailL) acc) [tm]⊢*
    (peelCfg (lastAfter prev s) (k + s.length) (w + weight2 s) tailL (peelTape s acc)) := by
  induction s generalizing prev k w acc with
  | nil =>
    simp only [encS, List.nil_append, lastAfter, List.length_nil, Nat.add_zero, weight2, peelTape]
    exists 0
  | cons b bs ih =>
    simp only [encS, List.cons_append, lastAfter, List.length_cons, weight2, peelTape]
    cases prev <;> cases b
    · have h1 := peel_step_00 k w (encS false bs ++ tailL) acc
      have h2 := ih false (k + 1) (w + 2) ([s0, s0] +> acc) (fun h => by cases h)
      have hk : k + 1 + bs.length = k + (bs.length + 1) := by omega
      have hw : w + 2 + weight2 bs = w + (bitW false + weight2 bs) := by dsimp only [bitW]; omega
      rw [hk, hw] at h2
      exact zPs (z02 h1 h2)
    · have h1 := peel_step_01 k w (encS true bs ++ tailL) acc
      have h2 := ih true (k + 1) (w + 1) ([s1, s0, s0] +> acc) (fun _ => ⟨k, acc, rfl, rfl⟩)
      have hk : k + 1 + bs.length = k + (bs.length + 1) := by omega
      have hw : w + 1 + weight2 bs = w + (bitW true + weight2 bs) := by dsimp only [bitW]; omega
      rw [hk, hw] at h2
      exact zPs (z02 h1 h2)
    · obtain ⟨k', acc0, rfl, rfl⟩ := h_inv rfl
      have h1 := peel_step_10 k' w (encS false bs ++ tailL) acc0
      have h2 := ih false (k' + 2) (w + 2) ([s0, s0] +> ([s1, s0, s0] +> acc0)) (fun h => by cases h)
      have hk : k' + 2 + bs.length = k' + 1 + (bs.length + 1) := by omega
      have hw : w + 2 + weight2 bs = w + (bitW false + weight2 bs) := by dsimp only [bitW]; omega
      rw [hk, hw] at h2
      exact zPs (z02 h1 h2)
    · obtain ⟨k', acc0, rfl, rfl⟩ := h_inv rfl
      have h1 := peel_step_11 k' w (encS true bs ++ tailL) acc0
      have h2 := ih true (k' + 2) (w + 1) ([s1, s0, s0] +> ([s1, s0, s0] +> acc0))
        (fun _ => ⟨k' + 1, [s1, s0, s0] +> acc0, rfl, rfl⟩)
      have hk : k' + 2 + bs.length = k' + 1 + (bs.length + 1) := by omega
      have hw : w + 1 + weight2 bs = w + (bitW true + weight2 bs) := by dsimp only [bitW]; omega
      rw [hk, hw] at h2
      exact zPs (z02 h1 h2)

lemma peelTape_eq_stack (s stk : List Bool) (R0 : zB) :
    peelTape s (stackTape stk R0) = stackTape (s.reverse ++ stk) R0 := by
  induction s generalizing stk with
  | nil => simp [peelTape]
  | cons b bs ih =>
    simp only [peelTape, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact ih (b :: stk)

lemma lastAfter_snoc (prev : Bool) (u : List Bool) (x : Bool) :
    lastAfter prev (u ++ [x]) = x := by
  induction u generalizing prev with
  | nil => rfl
  | cons b bs ih => exact ih b

lemma lastAfter_eq_last_rev (prev : Bool) (s : List Bool) :
    ∀ b0 sb, s.reverse = b0 :: sb → lastAfter prev s = b0 := by
  induction s generalizing prev with
  | nil => intro b0 sb h; cases h
  | cons x xs ih =>
    intro b0 sb h
    simp only [List.reverse_cons] at h
    cases h_rev : xs.reverse with
    | nil =>
      rw [h_rev] at h
      have hxs : xs = [] := List.reverse_eq_nil_iff.mp h_rev
      subst hxs
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, _⟩ := h
      rfl
    | cons y ys =>
      rw [h_rev, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ih x y ys h_rev

/-! ## Section 3: Finite Boundary Blocks & `Sweep0` Strong Induction -/

lemma sweep0_r0 (c : Bool) (A B : ℕ) (tail : List ℕ) (R_rest : zB) :
    (D_cfg ([2 + c.toNat, 1, 1, A + 3, B + 2] ++ tail) (s0 ∷ R_rest)) [tm]⊢⁺
    (D_cfg ([2, 2, 2, 1 + c.toNat, A + 1, B + 1] ++ tail) R_rest) := by
  cases c
  · run_d 15 ([2, 1, 1, A + 3, B + 2] ++ tail), [0], R_rest
  · run_d 15 ([3, 1, 1, A + 3, B + 2] ++ tail), [0], R_rest

lemma sweep0_r1_false (c : Bool) (A B : ℕ) (tail : List ℕ) (R_rest : zB) :
    (D_cfg ([2 + c.toNat, 1, 1, 2, 2, A + 3, B + 2] ++ tail) (s0 ∷ R_rest)) [tm]⊢⁺
    (D_cfg ([2, 2, 2, 1, 2, 2 + c.toNat, A + 1, B + 1] ++ tail) R_rest) := by
  cases c
  · run_d 42 ([2, 1, 1, 2, 2, A + 3, B + 2] ++ tail), [0], R_rest
  · run_d 42 ([3, 1, 1, 2, 2, A + 3, B + 2] ++ tail), [0], R_rest

lemma sweep0_r1_true (c : Bool) (A B : ℕ) (tail : List ℕ) (R_rest : zB) :
    (D_cfg ([2 + c.toNat, 1, 1, 2, 1, A + 3, B + 3] ++ tail) (s0 ∷ R_rest)) [tm]⊢⁺
    (D_cfg ([2, 2, 2, 2, 2, 1 + c.toNat, A + 1, B + 1] ++ tail) R_rest) := by
  cases c
  · run_d 51 ([2, 1, 1, 2, 1, A + 3, B + 3] ++ tail), [0], R_rest
  · run_d 51 ([3, 1, 1, 2, 1, A + 3, B + 3] ++ tail), [0], R_rest

lemma mid_finish_false (r' w A B : ℕ) (tail : List ℕ) (rest : zB) :
    (peelCfg false (r' + 2) w ([A + 3, B + 2] ++ tail) ([s0, s0] +> rest)) [tm]⊢⁺
    (D_cfg ([2, 1, 1, 2 * r' + 6, w + 1, A + 1, B + 1] ++ tail) (s0 ∷ rest)) := by
  dsimp only [peelCfg]
  run_d 16 ((w + 2) :: 1 :: 1 :: (A + 3) :: (B + 2) :: tail), [2 * (r' + 2), 0, 0], rest

lemma mid_finish_true (r' w A B : ℕ) (tail : List ℕ) (rest : zB) :
    (peelCfg true (r' + 2) w ([A + 3, B + 3] ++ tail) ([s1, s0, s0] +> rest)) [tm]⊢⁺
    (D_cfg ([3, 1, 1, 2 * r' + 6, w + 1, A + 1, B + 1] ++ tail) (s0 ∷ rest)) := by
  rw [peelCfg_true_encR]
  run_d 29 ([3, 1, A + 3, B + 3] ++ tail), [w + 1, 0, 2 * r' + 3, 0], rest

lemma end_finish_era (r' w : ℕ) (rest : zB) :
    (peelCfg false (r' + 2) w [2, 1, bot + 1] ([s0, s0] +> rest)) [tm]⊢⁺
    (D_cfg [bot + 3]
      ([s1, s1, s0, s0] +>
        (([s1] ^ (w + 2)) +> ([s0, s0] +> (([s1] ^ (2 * r' + 5)) +> ([s0, s0, s0, s0] +> rest)))))) := by
  dsimp only [peelCfg]
  run_d 6 [w + 2, 1, 1, 2, 1, bot + 1], [2 * (r' + 2), 0, 0], rest

lemma end_finish_era0 (r' w : ℕ) (rest : zB) :
    (peelCfg true (r' + 2) w [2, 2, bot + 1] ([s1, s0, s0] +> rest)) [tm]⊢⁺
    (D_cfg [bot + 3]
      ([s1, s1, s0, s0] +>
        (([s1] ^ (w + 2)) +>
          ([s0, s0] +> (([s1] ^ (2 * r' + 5)) +> ([s0, s0, s1, s0, s0] +> rest)))))) := by
  rw [peelCfg_true_encR]
  run_d 19 [3, 1, 2, 2, bot + 1], [w + 1, 0, 2 * r' + 3, 0], rest

lemma bounce1_header (np d : ℕ) (R_in : zB) :
    (D_cfg [bot + 3]
      (([s1] ^ (2 * np + 3)) +> ([s0, s0] +> (([s1] ^ (d + 2)) +> ([s0, s0, s1, s0] +> R_in))))) [tm]⊢⁺
    (D_cfg [3, 1, 1, d + 3, 2 * np + 2, bot + 1] R_in) := by
  run_d 10 [bot + 3], [2 * np + 3, 0, d + 2, 0, 1], R_in

lemma bounce2 (p q : ℕ) (R_tail : zB) :
    (D_cfg [bot + 3]
      ([s1, s1, s0, s0] +>
        (([s1] ^ (p + 2)) +> ([s0, s0] +> (([s1] ^ (q + 1)) +> ([s0, s0] +> R_tail)))))) [tm]⊢⁺
    (D_cfg [bot + 3]
      (([s1] ^ (p + 3)) +>
        ([s0, s0] +> (([s1] ^ (q + 3)) +> ([s0, s0, s1, s0, s0] +> R_tail))))) := by
  run_d 17 [bot + 3], [2, 0, p + 2, 0, q + 1, 0], R_tail

/-! ## Section 4: `coreS`, `run_rounds`, and `Sweep0` -/

def runChain (stepFn : Bool → List Bool → List Bool) :
    Bool → List Bool → List Bool → List Bool
  | c, cur, [] => stepFn c cur
  | c, cur, b :: bs => runChain stepFn b (stepFn c cur) bs

def coreSFuel : ℕ → List Bool → List Bool
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, s =>
      match s.reverse with
      | [] => []
      | b0 :: sb => runChain (fun c cur => coreSFuel fuel cur ++ [!c]) b0 [] sb

def coreS (s : List Bool) : List Bool := coreSFuel s.length s

lemma coreSFuel_length : ∀ fuel (s : List Bool),
    s.length ≤ fuel → (coreSFuel fuel s).length = s.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs; cases s with | nil => rfl | cons _ _ => simp at hs
  | succ fuel ih =>
    intro s hs
    cases s with
    | nil => rfl
    | cons x xs =>
      simp only [coreSFuel]
      cases h_rev : (x :: xs).reverse with
      | nil => cases List.reverse_eq_nil_iff.mp h_rev
      | cons b0 sb =>
        have h_len_rev : sb.length = xs.length := by
          have := congrArg List.length h_rev; simp at this; omega
        have h_chain : ∀ c (cur bs : List Bool),
            cur.length + bs.length ≤ fuel →
            (runChain (fun c' u => coreSFuel fuel u ++ [!c']) c cur bs).length =
              cur.length + bs.length + 1 := by
          intro c cur bs
          induction bs generalizing c cur with
          | nil =>
            intro hb
            simp only [List.length_nil] at hb
            simp only [runChain, List.length_append, List.length_singleton, List.length_nil]
            rw [ih cur (by omega)]
          | cons b bs ihb =>
            intro hb
            simp only [List.length_cons] at hb
            simp only [runChain, List.length_cons]
            have hu : (coreSFuel fuel cur ++ [!c]).length = cur.length + 1 := by
              simp only [List.length_append, List.length_singleton]
              rw [ih cur (by omega)]
            have := ihb b (coreSFuel fuel cur ++ [!c]) (by omega)
            omega
        have := h_chain b0 [] sb (by simp [h_len_rev] at hs ⊢; omega)
        simp [h_len_rev] at this ⊢
        exact this

lemma coreSFuel_eq_of_ge : ∀ f1 f2 (s : List Bool),
    s.length ≤ f1 → s.length ≤ f2 → coreSFuel f1 s = coreSFuel f2 s := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 s h1 _; cases s with | nil => cases f2 <;> rfl | cons _ _ => simp at h1
  | succ f1 ih =>
    intro f2 s h1 h2
    cases f2 with
    | zero => cases s with | nil => rfl | cons _ _ => simp at h2
    | succ f2 =>
      cases s with
      | nil => rfl
      | cons x xs =>
        simp only [coreSFuel]
        cases h_rev : (x :: xs).reverse with
        | nil => cases List.reverse_eq_nil_iff.mp h_rev
        | cons b0 sb =>
          have h_len_rev : sb.length = xs.length := by
            have := congrArg List.length h_rev; simp at this; omega
          have h_chain : ∀ c (cur bs : List Bool),
              cur.length + bs.length ≤ xs.length →
              runChain (fun c' u => coreSFuel f1 u ++ [!c']) c cur bs =
              runChain (fun c' u => coreSFuel f2 u ++ [!c']) c cur bs := by
            intro c cur bs
            induction bs generalizing c cur with
            | nil =>
              intro hb; simp only [List.length_nil] at hb; simp only [runChain]
              rw [ih f2 cur (by simp at h1; omega) (by simp at h2; omega)]
            | cons b bs ihb =>
              intro hb; simp only [List.length_cons] at hb; simp only [runChain]
              rw [ih f2 cur (by simp at h1; omega) (by simp at h2; omega)]
              have hlen2 : (coreSFuel f2 cur ++ [!c]).length = cur.length + 1 := by
                simp only [List.length_append, List.length_singleton]
                rw [coreSFuel_length f2 cur (by simp at h2; omega)]
              exact ihb b (coreSFuel f2 cur ++ [!c]) (by omega)
          exact h_chain b0 [] sb (by simp [h_len_rev])

lemma coreS_length (s : List Bool) : (coreS s).length = s.length :=
  coreSFuel_length s.length s (Nat.le_refl _)

lemma runChain_length (cc : Bool) (cur bs : List Bool) :
    (runChain (fun c' u => coreS u ++ [!c']) cc cur bs).length = cur.length + bs.length + 1 := by
  induction bs generalizing cc cur with
  | nil => simp [runChain, coreS_length]
  | cons b bs ih => simp [runChain, ih, coreS_length]; omega

lemma coreS_unfold {s : List Bool} {b0 : Bool} {sb : List Bool}
    (h_rev : s.reverse = b0 :: sb) :
    coreS s = runChain (fun c cur => coreS cur ++ [!c]) b0 [] sb := by
  have hs_len : s.length = sb.length + 1 := by
    have := congrArg List.length h_rev; simp at this; omega
  unfold coreS
  cases h_s : s with
  | nil => simp [h_s] at h_rev
  | cons x xs =>
    have hf : xs.length = sb.length := by simp [h_s] at hs_len; exact hs_len
    simp only [List.length_cons, coreSFuel, h_s ▸ h_rev]
    have h_chain : ∀ c (cur bs : List Bool),
        cur.length + bs.length ≤ xs.length →
        runChain (fun c' u => coreSFuel xs.length u ++ [!c']) c cur bs =
        runChain (fun c' u => coreS u ++ [!c']) c cur bs := by
      intro c cur bs
      induction bs generalizing c cur with
      | nil =>
        intro hb; simp only [List.length_nil] at hb; simp only [runChain]
        rw [coreSFuel_eq_of_ge xs.length cur.length cur (by omega) (Nat.le_refl _)]
        rfl
      | cons b bs ihb =>
        intro hb; simp only [List.length_cons] at hb; simp only [runChain]
        rw [coreSFuel_eq_of_ge xs.length cur.length cur (by omega) (Nat.le_refl _)]
        have hlen2 : (coreS cur ++ [!c]).length = cur.length + 1 := by simp [coreS_length]
        exact ihb b (coreS cur ++ [!c]) (by omega)
    exact h_chain b0 [] sb (by simp [hf])

lemma encS_snoc (prev : Bool) (u : List Bool) (x : Bool) :
    encS prev (u ++ [x]) = encS prev u ++ [2, pairVal (lastAfter prev u) x] := by
  induction u generalizing prev with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append, encS, lastAfter]; rw [ih b]

lemma bitTape_as_ones (b : Bool) (R0 : zB) :
    bitTape b +> R0 = ([s1] ^ b.toNat) +> (s0 ∷ (s0 ∷ R0)) := by
  cases b <;> rfl

lemma weight2_append (u v : List Bool) :
    weight2 (u ++ v) = weight2 u + weight2 v := by
  induction u with
  | nil => simp [weight2]
  | cons b bs ih => simp [weight2, ih]; omega

lemma weight2_reverse (s : List Bool) : weight2 s.reverse = weight2 s := by
  induction s with
  | nil => rfl
  | cons b bs ih => simp [List.reverse_cons, weight2_append, weight2, ih]; omega

lemma dropChain_snoc (cc : Bool) (mid : List Bool) (x : Bool) :
    dropChain cc (mid ++ [x]) = bitW cc + weight2 mid := by
  induction mid generalizing cc with
  | nil => simp [dropChain, weight2]
  | cons y ys ih => simp [dropChain, weight2, ih]

lemma runChain_lastAfter (prev cc : Bool) (cur mid : List Bool) (x : Bool) :
    lastAfter prev (runChain (fun c' u => coreS u ++ [!c']) cc cur (mid ++ [x])) = !x := by
  induction mid generalizing cc cur with
  | nil => simp [runChain, lastAfter_snoc]
  | cons y ys ih =>
    simp only [List.cons_append, runChain]
    exact ih y (coreS cur ++ [!cc])

lemma run_rounds (N : ℕ)
    (h_sweep : ∀ s, s.length ≤ N → ∀ c A B tail R_rest,
      (D_cfg ([2 + c.toNat, 1, 1] ++ encS false s ++
        [A + 3, B + (1 + (lastBit s).toNat) + 1] ++ tail) (s0 ∷ R_rest)) [tm]⊢⁺
      (D_cfg ([2, 2] ++ encS false (coreS s ++ [!c]) ++ [A + 1, B + 1] ++ tail) R_rest))
    (cc : Bool) (cur bs : List Bool) (A_base B_rem : ℕ) (tail : List ℕ) (R_after : zB)
    (hbound : cur.length + bs.length ≤ N) :
    (D_cfg ([2 + cc.toNat, 1, 1] ++ encS false cur ++
      [2 * bs.length + A_base + 3,
        B_rem + (1 + (lastBit cur).toNat) + dropChain cc bs + 1] ++ tail)
      (s0 ∷ stackTape bs R_after)) [tm]⊢⁺
    (D_cfg ([2, 2] ++ encS false (runChain (fun c' u => coreS u ++ [!c']) cc cur bs) ++
      [A_base + 1, B_rem + 1] ++ tail) R_after) := by
  induction bs generalizing cc cur with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, dropChain, Nat.add_zero,
      stackTape, runChain] at hbound ⊢
    exact h_sweep cur (by omega) cc A_base B_rem tail R_after
  | cons b_next bs_rem ih_bs =>
    simp only [List.length_cons, dropChain, stackTape, runChain] at hbound ⊢
    have h1 := h_sweep cur (by omega) cc (2 * bs_rem.length + A_base + 2)
      (B_rem + (bitW cc + dropChain b_next bs_rem)) tail
      (bitTape b_next +> stackTape bs_rem R_after)
    have hA : 2 * bs_rem.length + A_base + 2 + 3 = 2 * (bs_rem.length + 1) + A_base + 3 := by
      omega
    have hB : B_rem + (bitW cc + dropChain b_next bs_rem) + (1 + (lastBit cur).toNat) + 1 =
        B_rem + (1 + (lastBit cur).toNat) + (bitW cc + dropChain b_next bs_rem) + 1 := by
      omega
    rw [hA, hB] at h1
    let u_next := coreS cur ++ [!cc]
    have h_pop : (D_cfg ([2, 2] ++ encS false u_next ++
        [2 * bs_rem.length + A_base + 3,
          B_rem + (bitW cc + dropChain b_next bs_rem) + 1] ++ tail)
        (bitTape b_next +> stackTape bs_rem R_after)) [tm]⊢⁺
        (D_cfg ([2 + b_next.toNat, 1, 1] ++ encS false u_next ++
          [2 * bs_rem.length + A_base + 3,
            B_rem + (bitW cc + dropChain b_next bs_rem) + 1] ++ tail)
          (s0 ∷ stackTape bs_rem R_after)) := by
      rw [bitTape_as_ones]
      have hp := rule_pop 0 0 b_next.toNat
        (encS false u_next ++
          [2 * bs_rem.length + A_base + 3,
            B_rem + (bitW cc + dropChain b_next bs_rem) + 1] ++ tail)
        (s0 ∷ stackTape bs_rem R_after)
      simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.zero_add,
        Nat.add_comm b_next.toNat 2] at hp ⊢
      exact hp
    have hu_len : u_next.length = cur.length + 1 := by simp [u_next, coreS_length]
    have hu_last : 1 + (lastBit u_next).toNat = bitW cc := by
      have hl : lastBit u_next = !cc := lastAfter_snoc false (coreS cur) (!cc)
      rw [hl]; cases cc <;> rfl
    have h3 := ih_bs b_next u_next (by omega)
    rw [hu_last, Nat.add_assoc B_rem (bitW cc) (dropChain b_next bs_rem)] at h3
    have hA1 : 2 * bs_rem.length + A_base + 2 + 1 = 2 * bs_rem.length + A_base + 3 := by omega
    rw [hA1] at h1
    exact zPt (zPt h1 h_pop) h3

theorem Sweep0 : ∀ (n : ℕ) (s : List Bool), s.length ≤ n →
    ∀ (c : Bool) (A B : ℕ) (tail : List ℕ) (R_rest : zB),
    (D_cfg ([2 + c.toNat, 1, 1] ++ encS false s ++
      [A + 3, B + (1 + (lastBit s).toNat) + 1] ++ tail) (s0 ∷ R_rest)) [tm]⊢⁺
    (D_cfg ([2, 2] ++ encS false (coreS s ++ [!c]) ++ [A + 1, B + 1] ++ tail) R_rest) := by
  intro n
  induction n with
  | zero =>
    intro s hs c A B tail R_rest
    cases s with
    | nil =>
      cases c
      · exact sweep0_r0 false A B tail R_rest
      · exact sweep0_r0 true A B tail R_rest
    | cons _ _ => simp at hs
  | succ n ih =>
    intro s hs c A B tail R_rest
    cases s with
    | nil =>
      cases c
      · exact sweep0_r0 false A B tail R_rest
      · exact sweep0_r0 true A B tail R_rest
    | cons x1 s1 =>
      cases s1 with
      | nil =>
        cases x1
        · cases c
          · exact sweep0_r1_false false A B tail R_rest
          · exact sweep0_r1_false true A B tail R_rest
        · cases c
          · exact sweep0_r1_true false A B tail R_rest
          · exact sweep0_r1_true true A B tail R_rest
      | cons x2 xs =>
        let r' := xs.length
        cases h_rev2 : (x2 :: xs).reverse with
        | nil => cases List.reverse_eq_nil_iff.mp h_rev2
        | cons b0 mid =>
          have hmid_len : mid.length = r' := by
            have := congrArg List.length h_rev2; simp [r'] at this; omega
          have h_rev : (x1 :: x2 :: xs).reverse = b0 :: (mid ++ [x1]) := by
            simp [List.reverse_cons, h_rev2]
          have h_last : lastBit (x1 :: x2 :: xs) = b0 :=
            lastAfter_eq_last_rev false (x1 :: x2 :: xs) b0 (mid ++ [x1]) h_rev
          have h_peel := peel_all (x1 :: x2 :: xs) false 0 c.toNat
            ([A + 3, B + (1 + b0.toNat) + 1] ++ tail) R_rest (fun h => by cases h)
          have h_tape : peelTape (x1 :: x2 :: xs) R_rest =
              bitTape b0 +> stackTape (mid ++ [x1]) R_rest := by
            simpa [stackTape, h_rev] using peelTape_eq_stack (x1 :: x2 :: xs) [] R_rest
          have h_la : lastAfter false (x1 :: x2 :: xs) = b0 := h_last
          have h_len_s : (x1 :: x2 :: xs).length = r' + 2 := by simp [r']
          rw [h_la, Nat.zero_add, h_len_s, h_tape] at h_peel
          have h_mid : (peelCfg b0 (r' + 2) (c.toNat + weight2 (x1 :: x2 :: xs))
              ([A + 3, B + (1 + b0.toNat) + 1] ++ tail)
              (bitTape b0 +> stackTape (mid ++ [x1]) R_rest)) [tm]⊢⁺
              (D_cfg ([b0.toNat + 2, 1, 1, 2 * r' + 6,
                c.toNat + weight2 (x1 :: x2 :: xs) + 1, A + 1, B + 1] ++ tail)
                (s0 ∷ stackTape (mid ++ [x1]) R_rest)) := by
            cases b0
            · exact mid_finish_false r' (c.toNat + weight2 (x1 :: x2 :: xs)) A B tail
                (stackTape (mid ++ [x1]) R_rest)
            · exact mid_finish_true r' (c.toNat + weight2 (x1 :: x2 :: xs)) A B tail
                (stackTape (mid ++ [x1]) R_rest)
          have h_p1 : (D_cfg ([2 + c.toNat, 1, 1] ++ encS false (x1 :: x2 :: xs) ++
              [A + 3, B + (1 + (lastBit (x1 :: x2 :: xs)).toNat) + 1] ++ tail)
              (s0 ∷ R_rest)) [tm]⊢⁺
              (D_cfg ([2 + b0.toNat, 1, 1, 2 * r' + 6,
                c.toNat + weight2 (x1 :: x2 :: xs) + 1, A + 1, B + 1] ++ tail)
                (s0 ∷ stackTape (mid ++ [x1]) R_rest)) := by
            rw [h_last]
            have h0 : peelCfg false 0 c.toNat
                (encS false (x1 :: x2 :: xs) ++ ([A + 3, B + (1 + b0.toNat) + 1] ++ tail)) R_rest =
                D_cfg ([2 + c.toNat, 1, 1] ++ encS false (x1 :: x2 :: xs) ++
                  [A + 3, B + (1 + b0.toNat) + 1] ++ tail) (s0 ∷ R_rest) := by
              unfold peelCfg
              simp only [List.append_assoc, Nat.mul_zero, ones_zero_eq, Nat.add_comm c.toNat 2]
            rw [← h0, Nat.add_comm 2 b0.toNat]
            exact zStP h_peel h_mid
          have h_sub := run_rounds n ih b0 [] (mid ++ [x1]) 1 (pairValPred (!x1) (!c))
            ((A + 1) :: (B + 1) :: tail) R_rest (by simp [r', hmid_len] at hs ⊢; omega)
          have hA_eq : 2 * (mid ++ [x1]).length + 1 + 3 = 2 * r' + 6 := by
            simp [hmid_len]; omega
          have hB_eq : pairValPred (!x1) (!c) + (1 + (lastBit []).toNat) +
              dropChain b0 (mid ++ [x1]) + 1 =
              c.toNat + weight2 (x1 :: x2 :: xs) + 1 := by
            have hd := dropChain_snoc b0 mid x1
            have hw2 := weight2_reverse (x2 :: xs)
            rw [h_rev2] at hw2
            simp only [weight2] at hw2 ⊢
            have hpv : pairValPred (!x1) (!c) + 1 = c.toNat + bitW x1 := by
              cases x1 <;> cases c <;> rfl
            have hl0 : (lastBit []).toNat = 0 := rfl
            omega
          simp only [encS, List.nil_append] at h_sub
          rw [hA_eq, hB_eq] at h_sub
          have h_end_eq : D_cfg ([2, 2] ++
              encS false (runChain (fun c' u => coreS u ++ [!c']) b0 [] (mid ++ [x1])) ++
              [2, pairValPred (!x1) (!c) + 1] ++ ((A + 1) :: (B + 1) :: tail)) R_rest =
              D_cfg ([2, 2] ++ encS false (coreS (x1 :: x2 :: xs) ++ [!c]) ++
                [A + 1, B + 1] ++ tail) R_rest := by
            rw [← coreS_unfold h_rev, encS_snoc]
            have hla : lastAfter false (coreS (x1 :: x2 :: xs)) = !x1 := by
              rw [coreS_unfold h_rev]
              exact runChain_lastAfter false b0 [] mid x1
            have hpv : pairValPred (!x1) (!c) + 1 = pairVal (!x1) (!c) := by
              cases x1 <;> cases c <;> rfl
            rw [hla, hpv]
            simp only [List.append_assoc, List.cons_append, List.nil_append]
          rw [h_end_eq] at h_sub
          exact zPt h_p1 h_sub

/-! ## Section 5: Theorem 1 (`coreS_book_le`) & Theorem 2 (`hamming_coreS_and_chain`) -/

lemma rc_snoc (cc : Bool) (cur xs : List Bool) (b : Bool) :
    runChain (fun c u => coreS u ++ [!c]) cc cur (xs ++ [b]) =
    coreS (runChain (fun c u => coreS u ++ [!c]) cc cur xs) ++ [!b] := by
  induction xs generalizing cc cur with
  | nil => rfl
  | cons y ys ih => exact ih y (coreS cur ++ [!cc])

lemma coreS_book_le : ∀ (M d : ℕ), d ≤ M →
    coreS (true :: (List.replicate d false ++ [true])) =
      true :: List.replicate (d + 1) false := by
  intro M
  induction M with
  | zero =>
    intro d hd
    have : d = 0 := by omega
    subst this; rfl
  | succ M ih =>
    intro d hd
    cases d with
    | zero => rfl
    | succ d' =>
      have h_pal : (true :: (List.replicate (d' + 1) false ++ [true])).reverse =
          true :: (List.replicate (d' + 1) false ++ [true]) := by
        simp [List.reverse_append, List.reverse_replicate]
      rw [coreS_unfold h_pal]
      have h_z : ∀ k, k ≤ d' →
          runChain (fun c u => coreS u ++ [!c]) true [] (List.replicate (k + 1) false) =
            true :: (List.replicate k false ++ [true]) := by
        intro k
        induction k with
        | zero => intro _; rfl
        | succ k ihk =>
          intro hk
          have h_rep : List.replicate (k + 2) false =
              List.replicate (k + 1) false ++ [false] := by
            rw [List.replicate_succ']
          rw [h_rep, rc_snoc, ihk (by omega), ih k (by omega)]
          simp
      rw [rc_snoc, h_z d' (Nat.le_refl _), ih d' (by omega)]
      simp [List.replicate_succ']

theorem era0_chain (k : ℕ) :
    runChain (fun c u => coreS u ++ [!c]) true [] (List.replicate (k + 1) false) =
      true :: (List.replicate k false ++ [true]) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_rep : List.replicate (k + 2) false = List.replicate (k + 1) false ++ [false] := by
      rw [List.replicate_succ']
    rw [h_rep, rc_snoc, ih, coreS_book_le k k (Nat.le_refl _)]
    simp

def bitDiff (a b : Bool) : ℕ := if a == b then 0 else 1

def hamming : List Bool → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => bitDiff x y + hamming xs ys

lemma bitDiff_not (a b : Bool) : bitDiff (!a) (!b) = bitDiff a b := by
  cases a <;> cases b <;> rfl

lemma hamming_self (xs : List Bool) : hamming xs xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [hamming, bitDiff, ih]

lemma hamming_snoc (xs ys : List Bool) (a b : Bool) (h : xs.length = ys.length) :
    hamming (xs ++ [a]) (ys ++ [b]) = hamming xs ys + bitDiff a b := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [hamming]
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons] at h
      simp only [List.cons_append, hamming, ih ys (by omega), Nat.add_assoc]

lemma hamming_reverse (xs ys : List Bool) (h : xs.length = ys.length) :
    hamming xs.reverse ys.reverse = hamming xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons] at h
      have hlen' : xs.length = ys.length := by omega
      simp only [List.reverse_cons, hamming]
      rw [hamming_snoc xs.reverse ys.reverse x y (by simp [hlen'])]
      rw [ih ys hlen']
      omega

theorem hamming_coreS_and_chain : ∀ (M : ℕ),
    (∀ (s1 s2 : List Bool), s1.length ≤ M → s1.length = s2.length →
      hamming (coreS s1) (coreS s2) = hamming s1 s2) ∧
    (∀ cc1 cc2 (u1 u2 bs1 bs2 : List Bool),
      u1.length = u2.length → bs1.length = bs2.length →
      u1.length + bs1.length ≤ M →
      hamming (runChain (fun c u => coreS u ++ [!c]) cc1 u1 bs1)
              (runChain (fun c u => coreS u ++ [!c]) cc2 u2 bs2) =
        bitDiff cc1 cc2 + hamming u1 u2 + hamming bs1 bs2) := by
  have h_chain_of : ∀ (M : ℕ)
      (ih_core : ∀ (s1 s2 : List Bool), s1.length ≤ M → s1.length = s2.length →
        hamming (coreS s1) (coreS s2) = hamming s1 s2),
      ∀ cc1 cc2 (u1 u2 bs1 bs2 : List Bool),
      u1.length = u2.length → bs1.length = bs2.length →
      u1.length + bs1.length ≤ M →
      hamming (runChain (fun c u => coreS u ++ [!c]) cc1 u1 bs1)
              (runChain (fun c u => coreS u ++ [!c]) cc2 u2 bs2) =
        bitDiff cc1 cc2 + hamming u1 u2 + hamming bs1 bs2 := by
    intro M ih_core cc1 cc2 u1 u2 bs1
    induction bs1 generalizing cc1 cc2 u1 u2 with
    | nil =>
      intro bs2 hu hbs hM
      cases bs2 with
      | nil =>
        simp only [List.length_nil] at hM
        simp only [runChain, hamming]
        rw [hamming_snoc (coreS u1) (coreS u2) (!cc1) (!cc2) (by simp [coreS_length, hu]),
            ih_core u1 u2 (by omega) hu, bitDiff_not]
        omega
      | cons _ _ => simp at hbs
    | cons y1 ys1 ihb =>
      intro bs2 hu hbs hM
      cases bs2 with
      | nil => simp at hbs
      | cons y2 ys2 =>
        simp only [List.length_cons] at hbs hM
        simp only [runChain, hamming]
        have hu' : (coreS u1 ++ [!cc1]).length = (coreS u2 ++ [!cc2]).length := by
          simp [coreS_length, hu]
        have h_rec := ihb y1 y2 (coreS u1 ++ [!cc1]) (coreS u2 ++ [!cc2]) ys2
          hu' (by omega) (by simp [coreS_length] at *; omega)
        have h_ham_u : hamming (coreS u1 ++ [!cc1]) (coreS u2 ++ [!cc2]) =
            hamming u1 u2 + bitDiff cc1 cc2 := by
          rw [hamming_snoc (coreS u1) (coreS u2) (!cc1) (!cc2) (by simp [coreS_length, hu]),
              ih_core u1 u2 (by omega) hu, bitDiff_not]
        rw [h_rec, h_ham_u]
        omega
  intro M
  induction M with
  | zero =>
    have hc0 : ∀ (s1 s2 : List Bool), s1.length ≤ 0 → s1.length = s2.length →
        hamming (coreS s1) (coreS s2) = hamming s1 s2 := by
      intro s1 s2 h1 _
      cases s1 with
      | nil => cases s2 <;> simp [hamming, coreS, coreSFuel]
      | cons _ _ => simp at h1
    exact ⟨hc0, h_chain_of 0 hc0⟩
  | succ M ih =>
    have hcS : ∀ (s1 s2 : List Bool), s1.length ≤ M + 1 → s1.length = s2.length →
        hamming (coreS s1) (coreS s2) = hamming s1 s2 := by
      intro s1 s2 h1 hlen
      cases s1 with
      | nil =>
        cases s2 with
        | nil => rfl
        | cons _ _ => simp at hlen
      | cons x1 xs1 =>
        cases s2 with
        | nil => simp at hlen
        | cons x2 xs2 =>
          have h_rev_len : (x1 :: xs1).reverse.length = (x2 :: xs2).reverse.length := by
            rw [List.length_reverse, List.length_reverse, hlen]
          cases hr1 : (x1 :: xs1).reverse with
          | nil => cases List.reverse_eq_nil_iff.mp hr1
          | cons b0 sb1 =>
            cases hr2 : (x2 :: xs2).reverse with
            | nil => cases List.reverse_eq_nil_iff.mp hr2
            | cons c0 sb2 =>
              rw [hr1, hr2] at h_rev_len
              simp only [List.length_cons] at h_rev_len
              have hsb1_len : sb1.length ≤ M := by
                have := congrArg List.length hr1; simp at this h1; omega
              rw [coreS_unfold hr1, coreS_unfold hr2]
              have h_tot := ih.2 b0 c0 [] [] sb1 sb2 rfl (by omega) (by simp [hsb1_len])
              have h_rev_ham := hamming_reverse (x1 :: xs1) (x2 :: xs2) hlen
              rw [hr1, hr2] at h_rev_ham
              simp only [hamming] at h_tot h_rev_ham ⊢
              omega
    exact ⟨hcS, h_chain_of (M + 1) hcS⟩

lemma hamming_single_true (u' v' : ℕ) :
    hamming (List.replicate u' false ++ (true :: List.replicate v' false))
      (List.replicate (u' + v' + 1) false) = 1 := by
  induction u' with
  | zero =>
    simp [List.replicate_succ, hamming, bitDiff, hamming_self]
  | succ u' ih =>
    have heq : List.replicate (u' + 1 + v' + 1) false =
        false :: List.replicate (u' + v' + 1) false := by
      rw [show u' + 1 + v' + 1 = (u' + v' + 1) + 1 by omega, List.replicate_succ]
    rw [heq]
    simp only [List.replicate_succ, List.cons_append, hamming, bitDiff, beq_self_eq_true,
      ↓reduceIte, Nat.zero_add]
    exact ih

lemma hamming_zero_rep : ∀ (k : ℕ) (xs : List Bool),
    xs.length = k → hamming xs (List.replicate k false) = 0 →
    xs = List.replicate k false := by
  intro k
  induction k with
  | zero =>
    intro xs hlen _; cases xs with | nil => rfl | cons _ _ => simp at hlen
  | succ k ih =>
    intro xs hlen hham
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      simp only [List.length_cons] at hlen
      simp only [List.replicate_succ, hamming] at hham ⊢
      cases x
      · simp only [bitDiff, beq_self_eq_true, ↓reduceIte, Nat.zero_add] at hham
        rw [ih xs (by omega) hham]
      · simp [bitDiff] at hham

lemma hamming_one_rep : ∀ (k : ℕ) (xs : List Bool),
    xs.length = k → hamming xs (List.replicate k false) = 1 →
    ∃ a b, a + b + 1 = k ∧ xs = List.replicate a false ++ (true :: List.replicate b false) := by
  intro k
  induction k with
  | zero =>
    intro xs hlen hham; cases xs with | nil => simp [hamming] at hham | cons _ _ => simp at hlen
  | succ k ih =>
    intro xs hlen hham
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      simp only [List.length_cons] at hlen
      simp only [List.replicate_succ, hamming] at hham
      cases x
      · simp only [bitDiff, beq_self_eq_true, ↓reduceIte, Nat.zero_add] at hham
        obtain ⟨a, b, hab, rfl⟩ := ih xs (by omega) hham
        exact ⟨a + 1, b, by omega, by simp [List.replicate_succ]⟩
      · have h0 : hamming xs (List.replicate k false) = 0 := by simp [bitDiff] at hham; omega
        rw [hamming_zero_rep k xs (by omega) h0]
        exact ⟨0, k, by omega, rfl⟩

/-! ## Section 6: Canonical Closed Invariant `GoodCfg` & Full `IsNotHalt` Proof -/

def Era0_cfg (m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  D_cfg [bot + 3]
    (([s1] ^ (2 * m + 1)) +> ([s0, s0] +> (([s1] ^ (2 * m + 1)) +> ([s0, s0, s1] +> default))))

def Era_cfg (u v : ℕ) : Cfg (Fin 2) (Fin 6) :=
  let m := u + v
  D_cfg [bot + 3]
    (([s1] ^ (2 * m + 1)) +> ([s0, s0] +> (([s1] ^ (2 * m + 3)) +>
      ([s0, s0, s1] +> (([s0] ^ (2 * u)) +> ([s1] +> (([s0] ^ (2 * v)) +> ([s1] +> default))))))))

inductive GoodCfg : Cfg (Fin 2) (Fin 6) → Prop
  | era0 (m : ℕ) (hm : 1 ≤ m) : GoodCfg (Era0_cfg m)
  | era (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) : GoodCfg (Era_cfg u v)

lemma stackTape_append (xs ys : List Bool) (R0 : zB) :
    stackTape (xs ++ ys) R0 = stackTape xs (stackTape ys R0) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [stackTape, ih]

lemma stackTape_rep_false_default (k : ℕ) :
    stackTape (List.replicate k false) default = default := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, stackTape, bitTape, ih]

lemma stackTape_rep_false (k : ℕ) (R0 : zB) :
    stackTape (List.replicate k false) R0 = ([s0] ^ (2 * k)) +> R0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, stackTape, bitTape, ih]
    have h0 : [s0, s0] +> (([s0] ^ (2 * k)) +> R0) = ([s0] ^ 2) +> (([s0] ^ (2 * k)) +> R0) := rfl
    rw [h0, zeros_add_merge, show 2 + 2 * k = 2 * (k + 1) by omega]

lemma weight2_rep_false (k : ℕ) : weight2 (List.replicate k false) = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, weight2, bitW, ih]; omega

lemma dropChain_rep_false (k : ℕ) :
    dropChain true (List.replicate (k + 1) false) = 1 + 2 * k := by
  rw [List.replicate_succ', dropChain_snoc, weight2_rep_false]; rfl

lemma init_to_hit0 : (init []) [tm]⊢⁺ (D_cfg [bot + 3] (s1 ∷ default)) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{0}}> (s0 ∷ default)) := by
    simp only [init, Tape.mk₁, Tape.mk₂, Tape.mk', z00, zDh, zDt]
    congr 1 <;> (apply Turing.ListBlank.ext; intro _; rfl)
  rw [h0]
  have h1 : (default {{0}}> (s0 ∷ default)) [tm]⊢⁺ (D_cfg [bot + 2] default) := by
    simp only [D_cfg, encL, pow_succ_eq, pow_zero_eq, append_cons, append_nil, z00]
    iterate 10 (try (any_goals (first | finish | gstep)))
  have h2 : (D_cfg [bot + 2] default) [tm]⊢⁺ (D_cfg [2, bot + 2] default) := by
    simp only [D_cfg, encL, pow_succ_eq, pow_zero_eq, append_cons, append_nil, z00]
    iterate 30 (try (any_goals (first | finish | gstep)))
  have h3 : (D_cfg [2, bot + 2] default) [tm]⊢⁺ (D_cfg [2, 1, bot + 1] default) := by
    simp only [D_cfg, encL, pow_succ_eq, pow_zero_eq, append_cons, append_nil, z00]
    iterate 30 (try (any_goals (first | finish | gstep)))
  have h4 : (D_cfg [2, 1, bot + 1] default) [tm]⊢⁺ (D_cfg [bot + 3] (s1 ∷ default)) := by
    simp only [D_cfg, encL, pow_succ_eq, pow_zero_eq, append_cons, append_nil, z00]
    iterate 30 (try (any_goals (first | finish | gstep)))
  exact zPt (zPt (zPt h1 h2) h3) h4

lemma hit0_to_era0_1 : (D_cfg [bot + 3] (s1 ∷ default)) [tm]⊢⁺ (Era0_cfg 1) := by
  unfold Era0_cfg
  run_d 44 [bot + 3], [1, 0, 0, 0, 0, 0], default

lemma era0_1_to_2 : (Era0_cfg 1) [tm]⊢⁺ (Era0_cfg 2) := by
  unfold Era0_cfg
  run_d 62 [bot + 3], [3, 0, 3, 0, 1, 0, 0, 0], default

lemma step_era0_succ (k : ℕ) :
    (Era0_cfg (k + 2)) [tm]⊢⁺ (Era_cfg 1 (k + 1)) := by
  let m := k + 2
  have h_hdr : (Era0_cfg m) [tm]⊢⁺ (D_cfg [3, 1, 1, 2 * m + 2, 2 * m, bot + 1] default) := by
    unfold Era0_cfg
    have h := bounce1_header (k + 1) (2 * k + 3) default
    have hm1 : 2 * (k + 1) + 3 = 2 * m + 1 := by omega
    have hm2 : 2 * k + 3 + 2 = 2 * m + 1 := by omega
    have hm3 : 2 * k + 3 + 3 = 2 * m + 2 := by omega
    have hm4 : 2 * (k + 1) + 2 = 2 * m := by omega
    rw [hm1, hm2, hm3, hm4] at h
    simp only [append_cons, append_nil, z00] at h ⊢
    exact h
  let cs := List.replicate (k + 1) false
  let sf := true :: (List.replicate k false ++ [true])
  have h_rnd : (D_cfg [3, 1, 1, 2 * m + 2, 2 * m, bot + 1] default) [tm]⊢⁺
      (D_cfg ([2, 2] ++ encS false sf ++ [2, 2, bot + 1]) default) := by
    have hr := run_rounds m (Sweep0 m) true [] cs 1 1 [bot + 1] default
      (by simp [cs, m])
    have hcs_tape : s0 ∷ stackTape cs default = default := by
      rw [stackTape_rep_false_default]; exact z00
    have hA : 2 * cs.length + 1 + 3 = 2 * m + 2 := by simp [cs, m]; omega
    have hB : 1 + (1 + (lastBit []).toNat) + dropChain true cs + 1 = 2 * m := by
      have hdc := dropChain_rep_false k
      have hl0 : (lastBit []).toNat = 0 := rfl
      simp only [cs] at hdc ⊢
      omega
    simp only [encS, List.nil_append] at hr
    rw [hcs_tape, hA, hB, era0_chain k] at hr
    simpa [sf, List.append_assoc] using hr
  have h_pop0 : (D_cfg ([2, 2] ++ encS false sf ++ [2, 2, bot + 1]) default) [tm]⊢⁺
      (peelCfg false 0 0 (encS false sf ++ [2, 2, bot + 1]) default) := by
    unfold peelCfg
    simp only [List.cons_append, List.nil_append, Nat.mul_zero, ones_zero_eq, z00]
    exact rule_pop_end 0 0 (encS false sf ++ [2, 2, bot + 1])
  have h_peel := peel_all sf false 0 0 [2, 2, bot + 1] default (fun h => by cases h)
  have h_sf_la : lastAfter false sf = true := by
    simp [sf, lastAfter, lastAfter_snoc]
  have h_sf_len : 0 + sf.length = k + 2 := by simp [sf]
  have h_sf_w : 0 + weight2 sf = 2 * k + 2 := by
    simp [sf, weight2, weight2_append, weight2_rep_false, bitW]; omega
  let tail_era0 : zB := ([s0] ^ (2 * k)) +> ([s1] +> default)
  have h_sf_tape : peelTape sf default = [s1, s0, s0] +> tail_era0 := by
    have hp := peelTape_eq_stack sf [] default
    dsimp only [stackTape] at hp
    have hrev : sf.reverse = true :: (List.replicate k false ++ [true]) := by
      simp [sf, List.reverse_append, List.reverse_replicate]
    rw [hrev, List.append_nil] at hp
    rw [hp]
    have hst : stackTape (List.replicate k false ++ [true]) default = tail_era0 := by
      rw [stackTape_append, stackTape_rep_false]
      simp [stackTape, bitTape, tail_era0]
    simp [stackTape, bitTape, hst]
  rw [h_sf_la, h_sf_len, h_sf_w, h_sf_tape] at h_peel
  have h_end := end_finish_era0 k (2 * k + 2) tail_era0
  have h_b2 := bounce2 (2 * k + 2) (2 * k + 4) ([s1, s0, s0] +> tail_era0)
  have h_mid_eq : D_cfg [bot + 3]
      ([s1, s1, s0, s0] +> (([s1] ^ (2 * k + 2 + 2)) +>
        ([s0, s0] +> (([s1] ^ (2 * k + 5)) +> ([s0, s0, s1, s0, s0] +> tail_era0))))) =
      D_cfg [bot + 3]
        ([s1, s1, s0, s0] +> (([s1] ^ (2 * k + 2 + 2)) +>
          ([s0, s0] +> (([s1] ^ (2 * k + 4 + 1)) +> ([s0, s0] +> ([s1, s0, s0] +> tail_era0)))))) := by
    congr 1
  rw [h_mid_eq] at h_end
  have h_target : D_cfg [bot + 3]
      (([s1] ^ (2 * k + 2 + 3)) +>
        ([s0, s0] +> (([s1] ^ (2 * k + 4 + 3)) +>
          ([s0, s0, s1, s0, s0] +> ([s1, s0, s0] +> tail_era0))))) = Era_cfg 1 (k + 1) := by
    unfold Era_cfg
    dsimp only [tail_era0]
    have h1 : 2 * (1 + (k + 1)) + 1 = 2 * k + 2 + 3 := by omega
    have h2 : 2 * (1 + (k + 1)) + 3 = 2 * k + 4 + 3 := by omega
    rw [h1, h2]
    congr 1
  rw [h_target] at h_b2
  exact zPt (zPt (zPt h_hdr h_rnd) h_pop0) (zStP h_peel (zPt h_end h_b2))

lemma step_era (u' v' : ℕ) :
    ∃ c', ((Era_cfg (u' + 1) (v' + 1)) [tm]⊢⁺ c') ∧ GoodCfg c' := by
  let m' := u' + v'
  let cs_mid := List.replicate u' false ++ (true :: List.replicate v' false)
  let cs := cs_mid ++ [true]
  have hcs_len : cs.length = m' + 2 := by simp [cs, cs_mid, m']; omega
  have h_hdr : (Era_cfg (u' + 1) (v' + 1)) [tm]⊢⁺
      (D_cfg [3, 1, 1, 2 * m' + 8, 2 * m' + 4, bot + 1] (s0 ∷ stackTape cs default)) := by
    have h := bounce1_header (m' + 1) (2 * m' + 5) (s0 ∷ stackTape cs default)
    have h_in_eq : D_cfg [bot + 3]
        (([s1] ^ (2 * (m' + 1) + 3)) +> ([s0, s0] +> (([s1] ^ (2 * m' + 5 + 2)) +>
          ([s0, s0, s1, s0] +> (s0 ∷ stackTape cs default))))) =
        Era_cfg (u' + 1) (v' + 1) := by
      unfold Era_cfg
      have he1 : 2 * (m' + 1) + 3 = 2 * (u' + 1 + (v' + 1)) + 1 := by omega
      have he2 : 2 * m' + 5 + 2 = 2 * (u' + 1 + (v' + 1)) + 3 := by omega
      have hst : stackTape cs default =
          ([s0] ^ (2 * u')) +> ([s1] +> (([s0] ^ (2 * (v' + 1))) +> ([s1] +> default))) := by
        simp only [cs, cs_mid, List.append_assoc, List.cons_append, stackTape_append,
          stackTape_rep_false, stackTape, bitTape, z00, append_cons, append_nil]
        have hv_eq : s0 ∷ (s0 ∷ (([s0] ^ (2 * v')) +> (s1 ∷ default))) =
            ([s0] ^ (2 * (v' + 1))) +> ([s1] +> default) := by
          change ([s0] ^ 2) +> (([s0] ^ (2 * v')) +> ([s1] +> default)) = _
          rw [zeros_add_merge, show 2 + 2 * v' = 2 * (v' + 1) by omega]
        rw [hv_eq]
        rfl
      have htop : [s0, s0, s1, s0] +> (s0 ∷
          (([s0] ^ (2 * u')) +> ([s1] +> (([s0] ^ (2 * (v' + 1))) +> ([s1] +> default))))) =
          [s0, s0, s1] +> (([s0] ^ (2 * (u' + 1))) +>
            ([s1] +> (([s0] ^ (2 * (v' + 1))) +> ([s1] +> default)))) := by
        change [s0, s0, s1] +> (([s0] ^ 2) +> (([s0] ^ (2 * u')) +>
          ([s1] +> (([s0] ^ (2 * (v' + 1))) +> ([s1] +> default))))) = _
        rw [zeros_add_merge, show 2 + 2 * u' = 2 * (u' + 1) by omega]
      rw [he1, he2, hst, htop]
    rw [h_in_eq] at h
    rw [show 2 * m' + 5 + 3 = 2 * m' + 8 by omega,
        show 2 * (m' + 1) + 2 = 2 * m' + 4 by omega] at h
    exact h
  let sf := runChain (fun c' u => coreS u ++ [!c']) true [] cs
  have h_rnd : (D_cfg [3, 1, 1, 2 * m' + 8, 2 * m' + 4, bot + 1] (s0 ∷ stackTape cs default)) [tm]⊢⁺
      (D_cfg ([2, 2] ++ encS false sf ++ [2, 1, bot + 1]) default) := by
    have hr := run_rounds (m' + 2) (Sweep0 (m' + 2)) true [] cs 1 0 [bot + 1] default
      (by simp [hcs_len])
    have hA : 2 * cs.length + 1 + 3 = 2 * m' + 8 := by rw [hcs_len]; omega
    have hB : 0 + (1 + (lastBit []).toNat) + dropChain true cs + 1 = 2 * m' + 4 := by
      have hdc : dropChain true cs = 2 * m' + 2 := by
        rw [dropChain_snoc]
        simp only [cs_mid, weight2_append, weight2, weight2_rep_false, bitW]
        omega
      have hl0 : (lastBit []).toNat = 0 := rfl
      omega
    simp only [encS, List.nil_append] at hr
    rw [hA, hB] at hr
    simpa [sf, List.append_assoc] using hr
  have h_pop0 : (D_cfg ([2, 2] ++ encS false sf ++ [2, 1, bot + 1]) default) [tm]⊢⁺
      (peelCfg false 0 0 (encS false sf ++ [2, 1, bot + 1]) default) := by
    unfold peelCfg
    simp only [List.cons_append, List.nil_append, Nat.mul_zero, ones_zero_eq, z00]
    exact rule_pop_end 0 0 (encS false sf ++ [2, 1, bot + 1])
  have h_sf_la : lastAfter false sf = false := runChain_lastAfter false true [] cs_mid true
  have h_sf_len : sf.length = m' + 3 := by
    rw [runChain_length, hcs_len]; simp
  let cs_ref := List.replicate (m' + 1) false ++ [true]
  let sf_ref := runChain (fun c' u => coreS u ++ [!c']) true [] cs_ref
  have h_sf_ref : sf_ref = true :: List.replicate (m' + 2) false := by
    dsimp only [sf_ref, cs_ref]
    rw [rc_snoc, era0_chain m', coreS_book_le m' m' (Nat.le_refl _)]
    simp only [Bool.not_true, List.cons_append, ← List.replicate_succ']
  have h_ham_cs : hamming cs cs_ref = 1 := by
    dsimp only [cs, cs_ref]
    rw [hamming_snoc cs_mid (List.replicate (m' + 1) false) true true
      (by simp [cs_mid, m']; omega)]
    rw [hamming_single_true u' v']
    simp [bitDiff]
  have h_ham_sf : hamming sf (true :: List.replicate (m' + 2) false) = 1 := by
    rw [← h_sf_ref]
    have hch := (hamming_coreS_and_chain (m' + 2)).2 true true [] [] cs cs_ref
      rfl (by simp [hcs_len, cs_ref]) (by simp [hcs_len])
    simp only [bitDiff, beq_self_eq_true, ↓reduceIte, hamming, h_ham_cs] at hch
    exact hch
  cases h_head : sf with
  | nil => rw [h_head] at h_sf_len; simp at h_sf_len
  | cons h sf_tail =>
    rw [h_head] at h_sf_len h_ham_sf
    simp only [List.length_cons] at h_sf_len
    cases h
    · simp [hamming, bitDiff] at h_ham_sf
      have htail_eq := hamming_zero_rep (m' + 2) sf_tail (by omega) h_ham_sf
      have hsf_rep : sf = List.replicate (m' + 3) false := by
        rw [h_head, htail_eq]; rfl
      have h_peel := peel_all sf false 0 0 [2, 1, bot + 1] default (fun hh => by cases hh)
      have h_w : 0 + weight2 sf = 2 * m' + 6 := by
        rw [hsf_rep, weight2_rep_false]; omega
      have h_tape : peelTape sf default = [s0, s0] +> default := by
        have hp := peelTape_eq_stack sf [] default
        dsimp only [stackTape] at hp
        rw [List.append_nil] at hp
        rw [hp, hsf_rep, List.reverse_replicate, stackTape_rep_false_default]
        simp [z00]
      rw [h_sf_la, show 0 + sf.length = m' + 3 by rw [hsf_rep]; simp, h_w, h_tape] at h_peel
      have h_end := end_finish_era (m' + 1) (2 * m' + 6) default
      have h_b2 := bounce2 (2 * m' + 6) (2 * m' + 6) default
      have h_end_eq : D_cfg [bot + 3]
          ([s1, s1, s0, s0] +> (([s1] ^ (2 * m' + 6 + 2)) +>
            ([s0, s0] +> (([s1] ^ (2 * (m' + 1) + 5)) +> ([s0, s0, s0, s0] +> default))))) =
          D_cfg [bot + 3]
            ([s1, s1, s0, s0] +> (([s1] ^ (2 * m' + 6 + 2)) +>
              ([s0, s0] +> (([s1] ^ (2 * m' + 6 + 1)) +> ([s0, s0] +> default))))) := by
        have : 2 * (m' + 1) + 5 = 2 * m' + 6 + 1 := by omega
        rw [this]; simp [z00]
      rw [h_end_eq] at h_end
      have h_tgt : D_cfg [bot + 3]
          (([s1] ^ (2 * m' + 6 + 3)) +> ([s0, s0] +> (([s1] ^ (2 * m' + 6 + 3)) +>
            ([s0, s0, s1, s0, s0] +> default)))) = Era0_cfg (m' + 4) := by
        unfold Era0_cfg
        have : 2 * (m' + 4) + 1 = 2 * m' + 6 + 3 := by omega
        rw [this]; simp [z00]
      rw [h_tgt] at h_b2
      exact ⟨Era0_cfg (m' + 4),
        zPt (zPt (zPt h_hdr h_rnd) h_pop0) (zStP h_peel (zPt h_end h_b2)),
        GoodCfg.era0 (m' + 4) (by omega)⟩
    · simp [hamming, bitDiff] at h_ham_sf
      obtain ⟨a, b, hab, htail_eq⟩ := hamming_one_rep (m' + 2) sf_tail (by omega) h_ham_sf
      cases b with
      | zero =>
        have h_la' := h_sf_la
        rw [h_head, htail_eq] at h_la'
        simp [lastAfter, lastAfter_snoc] at h_la'
      | succ b' =>
        have hab' : a + b' = m' := by omega
        have h_peel := peel_all sf false 0 0 [2, 1, bot + 1] default (fun hh => by cases hh)
        have h_w : 0 + weight2 sf = 2 * m' + 4 := by
          rw [h_head, htail_eq]
          simp [weight2, weight2_append, weight2_rep_false, bitW]
          omega
        let mid_bits := List.replicate b' false ++ ([true] ++ (List.replicate a false ++ [true]))
        let rest : zB := stackTape mid_bits default
        have h_tape : peelTape sf default = [s0, s0] +> rest := by
          have hp := peelTape_eq_stack sf [] default
          dsimp only [stackTape] at hp
          have hrev : sf.reverse = false :: mid_bits := by
            have hsf_form : sf =
                ([true] ++ List.replicate a false ++ [true] ++ List.replicate b' false) ++ [false] := by
              rw [h_head, htail_eq, List.replicate_succ']
              simp [List.append_assoc]
            rw [hsf_form]
            simp [mid_bits, List.reverse_append, List.reverse_replicate, List.append_assoc]
          rw [List.append_nil, hrev] at hp
          simpa [stackTape, bitTape] using hp
        rw [h_sf_la, show 0 + sf.length = m' + 3 by rw [h_head]; simp; omega, h_w, h_tape] at h_peel
        have h_end := end_finish_era (m' + 1) (2 * m' + 4) rest
        have h_b2 := bounce2 (2 * m' + 4) (2 * m' + 6) ([s0, s0] +> rest)
        have h_end_eq : D_cfg [bot + 3]
            ([s1, s1, s0, s0] +> (([s1] ^ (2 * m' + 4 + 2)) +>
              ([s0, s0] +> (([s1] ^ (2 * (m' + 1) + 5)) +> ([s0, s0, s0, s0] +> rest))))) =
            D_cfg [bot + 3]
              ([s1, s1, s0, s0] +> (([s1] ^ (2 * m' + 4 + 2)) +>
                ([s0, s0] +> (([s1] ^ (2 * m' + 6 + 1)) +> ([s0, s0] +> ([s0, s0] +> rest)))))) := by
          have : 2 * (m' + 1) + 5 = 2 * m' + 6 + 1 := by omega
          rw [this]; rfl
        rw [h_end_eq] at h_end
        have h_tgt : D_cfg [bot + 3]
            (([s1] ^ (2 * m' + 4 + 3)) +> ([s0, s0] +> (([s1] ^ (2 * m' + 6 + 3)) +>
              ([s0, s0, s1, s0, s0] +> ([s0, s0] +> rest))))) =
            Era_cfg (b' + 2) (a + 1) := by
          dsimp only [Era_cfg]
          have he1 : 2 * (b' + 2 + (a + 1)) + 1 = 2 * m' + 4 + 3 := by omega
          have he2 : 2 * (b' + 2 + (a + 1)) + 3 = 2 * m' + 6 + 3 := by omega
          have hrest : rest =
              ([s0] ^ (2 * b')) +> ([s1] +> (([s0] ^ (2 * (a + 1))) +> ([s1] +> default))) := by
            simp only [rest, mid_bits, stackTape_append, stackTape_rep_false, stackTape, bitTape,
              z00, append_cons, append_nil]
            have ha_eq : s0 ∷ (s0 ∷ (([s0] ^ (2 * a)) +> (s1 ∷ default))) =
                ([s0] ^ (2 * (a + 1))) +> ([s1] +> default) := by
              change ([s0] ^ 2) +> (([s0] ^ (2 * a)) +> ([s1] +> default)) = _
              rw [zeros_add_merge, show 2 + 2 * a = 2 * (a + 1) by omega]
            rw [ha_eq]
            rfl
          have htop : [s0, s0, s1, s0, s0] +> ([s0, s0] +>
              (([s0] ^ (2 * b')) +> ([s1] +> (([s0] ^ (2 * (a + 1))) +> ([s1] +> default))))) =
              [s0, s0, s1] +> (([s0] ^ (2 * (b' + 2))) +>
                ([s1] +> (([s0] ^ (2 * (a + 1))) +> ([s1] +> default)))) := by
            change [s0, s0, s1] +> (([s0] ^ 2) +> (([s0] ^ 2) +> (([s0] ^ (2 * b')) +>
              ([s1] +> (([s0] ^ (2 * (a + 1))) +> ([s1] +> default)))))) = _
            rw [zeros_add_merge, zeros_add_merge, show 2 + 2 + 2 * b' = 2 * (b' + 2) by omega]
          rw [he1, he2, hrest, htop]
        rw [h_tgt] at h_b2
        exact ⟨Era_cfg (b' + 2) (a + 1),
          zPt (zPt (zPt h_hdr h_rnd) h_pop0) (zStP h_peel (zPt h_end h_b2)),
          GoodCfg.era (b' + 2) (a + 1) (by omega) (by omega)⟩

lemma good_step (c : Cfg (Fin 2) (Fin 6)) (hc : GoodCfg c) :
    ∃ c', (c [tm]⊢⁺ c') ∧ GoodCfg c' := by
  cases hc with
  | era0 m hm =>
    cases m with
    | zero => omega
    | succ m1 =>
      cases m1 with
      | zero => exact ⟨Era0_cfg 2, era0_1_to_2, GoodCfg.era0 2 (by omega)⟩
      | succ k => exact ⟨Era_cfg 1 (k + 1), step_era0_succ k, GoodCfg.era 1 (k + 1) (by omega) (by omega)⟩
  | era u v hu hv =>
    cases u with
    | zero => omega
    | succ u' =>
      cases v with
      | zero => omega
      | succ v' => exact step_era u' v'

lemma reach_N : ∀ k : ℕ, ∃ m c, k ≤ m ∧ ((init []) [tm]⊢^{m} c) ∧ GoodCfg c := by
  intro k
  induction k with
  | zero =>
    obtain ⟨m, _, hm⟩ := zPt init_to_hit0 hit0_to_era0_1
    exact ⟨m, Era0_cfg 1, Nat.zero_le m, hm, GoodCfg.era0 1 (Nat.le_refl 1)⟩
  | succ k ih =>
    obtain ⟨m, c, _, hm, hc⟩ := ih
    obtain ⟨c', ⟨d, hd, hstep⟩, hc'⟩ := good_step c hc
    exact ⟨m + d, c', by omega, zMt tm (init []) c c' m d hm hstep, hc'⟩

lemma multiStep_none_of_step_none (cfg : Cfg (Fin 2) (Fin 6)) (h0 : step tm cfg = none) :
    ∀ r : ℕ, multiStep tm cfg (r + 1) = none := by
  intro r
  induction r with
  | zero => simp [zMs, h0]
  | succ r ih => rw [zMs, ih]; rfl

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg ⟨n, hn⟩
  obtain ⟨m, c, hnm, hm, _⟩ := reach_N (n + 1)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hsplit : n + 1 + r = n + (r + 1) := by omega
  rw [hsplit, zMa, hn] at hm
  dsimp only [Option.bind] at hm
  cases hstep : step tm cfg with
  | none =>
    rw [multiStep_none_of_step_none cfg hstep r] at hm
    cases hm
  | some _ => rfl

end BusyBeaver.M_1RB1LC_1RC1LB_1LD0RB_0LE1RD_HHH0LF_0LA1LF
