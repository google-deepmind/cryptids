/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LD_0RC0RB_0LD1RE_0LA1LC_0RB0RF_1LC---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LD_0RC0RB_0LD1RE_0LA1LC_0RB0RF_1LC---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LD_0RC0RB_0LD1RE_0LA1LC_0RB0RF_1LCHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LD_0RC0RB_0LD1RE_0LA1LC_0RB0RF_1LC---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 2, Stmt.write 1 Dir.left)
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
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
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
@[simp] lemma append_assoc (l1 l2 : zF) (s : zB) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append,append_cons,ih]
lemma zSm {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
lemma z01 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
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
lemma zPs {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 : Cfg zG_ zL_} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n,_,hn⟩ := h; exact ⟨n,hn⟩
lemma zPt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,n_pos,hn⟩ := h₁; obtain ⟨m,m_pos,hm⟩ := h₂
  exact ⟨n + m,by omega,zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z02 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,n_pos,hn⟩ := h₁; obtain ⟨m,hm⟩ := h₂
  exact ⟨n + m,lt_of_lt_of_le n_pos (Nat.le_add_right n m),zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z03 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,hn⟩ := h₁; obtain ⟨m,m_pos,hm⟩ := h₂
  exact ⟨n + m,by omega,zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z04 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  z02 (z01 tm c_1 c_2 h₁) h₂
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z04 (by (try simp only [Turing.ListBlank.head_cons,zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,z00,zDh,zDt])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))
abbrev Q_A : Fin 6 := 5
abbrev Q_B : Fin 6 := 2
abbrev Q_C : Fin 6 := 3
abbrev Q_D : Fin 6 := 0
abbrev Q_E : Fin 6 := 1
abbrev Q_F : Fin 6 := 4
def zCR (l : zB) (q : Fin 6) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (l {{q}}> r)
def zCL (l : zB) (q : Fin 6) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (l <{{q}} r)
abbrev Z : zF := [1,1,0,0]
abbrev T : zF := [1,0,1,0]
abbrev lh : zB := (0 : Fin 2) >> (1 : Fin 2) >> default
inductive Call where
  | hb
  | hc
def zCs : Call -> Fin 6
  | .hb => Q_B
  | .hc => Q_C
def z05 (c : Call) (r1 r2 : zB) : Prop :=
  ∀ l,(zCR l Q_B r1) [target_tm]⊢⁺ (zCL l (zCs c) r2)
inductive Side : List Call -> zB -> zB -> Prop where
  | nil (r : zB) : Side [] r r
  | cons {c : Call} {ls : List Call} {r1 r2 r3 : zB} :
      z05 c r1 r2 -> Side ls r2 r3 -> Side (c :: ls) r1 r3
def Seg (ls_in ls_out : List Call) (w1 w2 : zF) : Prop :=
  ∀ r1 r2,Side ls_out r1 r2 -> Side ls_in (w1 +> r1) (w2 +> r2)
@[simp] lemma z06 {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma zLp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] lemma zLp' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] lemma z07 {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l
lemma z08 {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm,zLp,zLp,ih,List.append_assoc]
lemma z09 {α : Type*} (l : List α) (n : Nat) : l ^ n ++ l = l ++ l ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [zLp,List.append_assoc,ih]
lemma z09' {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ^ n ++ l := by
  rw [zLp]
  exact (z09 l n).symm
lemma z0a {ls1 ls2 : List Call} {r1 r2 r3 : zB}
    (h1 : Side ls1 r1 r2) (h2 : Side ls2 r2 r3) : Side (ls1 ++ ls2) r1 r3 := by
  induction h1 with
  | nil _ => exact h2
  | cons hc _ ih => exact Side.cons hc (ih h2)
lemma z0b {ls1 ls2 : List Call} {r1 r3 : zB}
    (h : Side (ls1 ++ ls2) r1 r3) : ∃ r2,Side ls1 r1 r2 /\ Side ls2 r2 r3 := by
  induction ls1 generalizing r1 with
  | nil => exact ⟨r1,Side.nil r1,h⟩
  | cons c ls1 ih =>
    rcases h with _ | ⟨hc,hrest⟩
    rcases ih hrest with ⟨r2,h1,h2⟩
    exact ⟨r2,Side.cons hc h1,h2⟩
lemma z0c {ls : List Call} {r : zB}
    (h : Side ls r r) (k : Nat) : Side (ls ^ k) r r := by
  induction k with
  | zero => exact Side.nil r
  | succ k ih => exact z0a h ih
lemma z0d (w : zF) : Seg [] [] w w := by
  intro r1 r2 h; cases h; exact Side.nil (w +> r1)
lemma z0e (ls : List Call) : Seg ls ls [] [] := by
  intro r1 r2 h; exact h
lemma zS0 {ls1 ls2 ls3 : List Call} {w1 w2 u1 u2 : zF}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls2 ls3 u1 u2) :
    Seg ls1 ls3 (w1 ++ u1) (w2 ++ u2) := by
  intro r1 r2 h
  simp only [append_assoc]
  exact h1 _ _ (h2 r1 r2 h)
lemma zSc {ls1 ls2 : List Call} {w1 w2 : zF} {r1 r2 : zB}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
    Side ls1 (w1 +> r1) (w2 +> r2) :=
  h1 r1 r2 h2
lemma zSg {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : zF}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3 := by
  intro r1 r3 h
  rcases z0b h with ⟨r2,ha,hb⟩
  exact z0a (h1 r1 r2 ha) (h2 r2 r3 hb)
lemma z0f {ls1 ls2 : List Call} {w : zF}
    (h : Seg ls1 ls2 w w) (n : Nat) : Seg (ls1 ^ n) (ls2 ^ n) w w := by
  induction n with
  | zero => exact z0d w
  | succ n ih => exact zSg h ih
lemma zS4 {c : Call} {w1 w2 : zF}
    (h1 : ∀ l r,(zCR l Q_B (w1 +> r)) [target_tm]⊢⁺ (zCL l (zCs c) (w2 +> r))) :
    Seg [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)
lemma zS2 {c_out c_in : Call} {w1 w2 mid : zF}
    (h1 : ∀ l r,(zCR l Q_B (w1 +> r)) [target_tm]⊢⁺ (zCR (mid +> l) Q_B r))
    (h2 : ∀ l r,(zCL (mid +> l) (zCs c_out) r) [target_tm]⊢⁺ (zCL l (zCs c_in) (w2 +> r))) :
    Seg [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1) (zPt (hc1 (mid +> l)) (h2 l r2))
lemma zS5 {c1 c2 c_in : Call} {w1 w2 mid1 mid2 : zF}
    (h1 : ∀ l r,(zCR l Q_B (w1 +> r)) [target_tm]⊢⁺ (zCR (mid1 +> l) Q_B r))
    (h2 : ∀ l r,(zCL (mid1 +> l) (zCs c1) r) [target_tm]⊢⁺ (zCR (mid2 +> l) Q_B r))
    (h3 : ∀ l r,(zCL (mid2 +> l) (zCs c2) r) [target_tm]⊢⁺ (zCL l (zCs c_in) (w2 +> r))) :
    Seg [c_in] [c1,c2] w1 w2 := by
  intro r1 r3 h
  rcases h with _ | ⟨hc1,hrest⟩
  rcases hrest with _ | ⟨hc2,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1)
    (zPt (hc1 (mid1 +> l))
      (zPt (h2 l _)
        (zPt (hc2 (mid2 +> l)) (h3 l r3))))
lemma z0g : Seg [.hb] [] Z T :=
  zS4 (fun l r => by unfold zCR zCL zCs Z T; simp only [append_cons,append_nil]; execute)
lemma z0h : Seg [.hb] [.hb] T Z :=
  zS2 (mid := [0,0,0,1])
    (fun l r => by unfold zCR T; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCs Z; simp only [append_cons,append_nil]; execute)
lemma z0i : Seg [.hb] [.hc,.hb] T T :=
  zS5 (mid1 := [0,0,0,1]) (mid2 := [0,1,0,1])
    (fun l r => by unfold zCR T; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCs T; simp only [append_cons,append_nil]; execute)
lemma z0j : Seg [.hc] [.hc,.hc] T T :=
  zS5 (mid1 := [0,0,0,1]) (mid2 := [0,1,0,1])
    (fun l r => by unfold zCR T; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCs T; simp only [append_cons,append_nil]; execute)
lemma z0k : Seg [.hc] [.hb] [1,0,0] [1,0,0] :=
  zS2 (mid := [0,0,1])
    (fun l r => by unfold zCR; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCs; simp only [append_cons,append_nil]; execute)
lemma z0l : Seg [.hb] [.hc,.hc] [1,0,0] [1,1,0] :=
  zS5 (mid1 := [0,0,1]) (mid2 := [0,1,1])
    (fun l r => by unfold zCR; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCs; simp only [append_cons,append_nil]; execute)
lemma z0m : Seg [.hb] [] [1,1,0] [1,0,1] :=
  zS4 (fun l r => by unfold zCR zCL zCs; simp only [append_cons,append_nil]; execute)
lemma z0n : Seg [.hc] [] [0] [0] :=
  zS4 (fun l r => by unfold zCR zCL zCs; simp only [append_cons,append_nil]; execute)
lemma z0o : Seg [.hc] [.hb] [1,0,1,1,0] [1,0,1,0,0] :=
  zS2 (mid := [0,0,0,0,1])
    (fun l r => by unfold zCR; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCs; simp only [append_cons,append_nil]; execute)
lemma z0p : Seg [.hb,.hb] [.hb] T T :=
  zSg z0h z0g
lemma z0q : Seg [.hb] [.hb] [1,0,1,1,0,0] [1,1,0,1,0,0] :=
  zS2 (mid := [0,0,1,0,1,1])
    (fun l r => by unfold zCR; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCs; simp only [append_cons,append_nil]; execute)
lemma z0r : Seg [.hb] [] [1,1,0,1,0,0] [1,0,1,1,0,0] :=
  zS4 (fun l r => by unfold zCR zCL zCs; simp only [append_cons,append_nil]; execute)
lemma z0s : Seg [.hb,.hb] [.hb] [1,0,1,1,0,0] [1,0,1,1,0,0] :=
  zSg z0q z0r
lemma z0t : Seg [.hb] [.hc,.hc] [1,0,1,1,0,0] [1,0,1,1,1,0] :=
  zS5 (mid1 := [0,0,1,0,1,1]) (mid2 := [0,1,1,0,1,1])
    (fun l r => by unfold zCR; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCs; simp only [append_cons,append_nil]; execute)
lemma z0u : Seg [.hc] [.hb] [1,0,1,1,1,0,0] [1,0,1,0,1,0,0] :=
  zS2 (mid := [0,0,1,0,1,0,1])
    (fun l r => by unfold zCR; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCs; simp only [append_cons,append_nil]; execute)
lemma z0v (r : zB) :
    (zCL lh Q_B r) [target_tm]⊢⁺ (zCR lh Q_B ([0,1,0] +> r)) := by
  unfold zCL zCR lh; simp only [append_cons,append_nil]; execute
lemma z0w (r : zB) :
    (zCL lh Q_C r) [target_tm]⊢⁺ (zCR lh Q_B ([1,0] +> r)) := by
  unfold zCL zCR lh; simp only [append_cons,append_nil]; execute
lemma E10 (l r : zB) :
    (zCR l Q_E ([1,0] +> r)) [target_tm]⊢⁺ (zCR ([0,0] +> l) Q_B r) := by
  unfold zCR; simp only [append_cons,append_nil]; execute
lemma z0x (l r : zB) :
    (zCL ([0,0,0,1,0,1,0,1] +> l) Q_C r) [target_tm]⊢⁺
      (zCR ([0,1,0,1,0,1,0,1] +> l) Q_B r) := by
  unfold zCL zCR; simp only [append_cons,append_nil]; execute
lemma z0y (l r : zB) :
    (zCL ([0,1,0,1,0,1,0,1] +> l) Q_C r) [target_tm]⊢⁺
      (zCL l Q_C (T +> (T +> r))) := by
  unfold zCL T; simp only [append_cons,append_nil]; execute
lemma z0z (l r : zB) :
    (zCL ([0,1,0,1,0,1,0,1] +> l) Q_B r) [target_tm]⊢⁺
      (zCL l Q_B (T +> (T +> r))) := by
  unfold zCL T; simp only [append_cons,append_nil]; execute
lemma z0A (l r : zB) :
    (zCL ([0,0,0,1,0,1,1] +> l) Q_B r) [target_tm]⊢⁺
      (zCL l Q_B ([1,0,1,1,1,0,0] +> r)) := by
  unfold zCL; simp only [append_cons,append_nil]; execute
lemma z0B {r r' : zB} (h : Side [.hc] r r') (l : zB) :
    (zCR l Q_B r) [target_tm]⊢⁺ (zCL l Q_C r') := by
  rcases h with _ | ⟨hc1,hnil⟩; cases hnil; exact hc1 l
lemma z0C {r r' : zB} (h : Side [.hb] r r') (l : zB) :
    (zCR l Q_B r) [target_tm]⊢⁺ (zCL l Q_B r') := by
  rcases h with _ | ⟨hc1,hnil⟩; cases hnil; exact hc1 l
lemma z0D {r : zB} (h : Side [.hc] r r) (l : zB) :
    (zCR l Q_B ([1,0,1,1,1,0] +> r)) [target_tm]⊢⁺
      (zCR ([0,1,0,1,0,1] +> l) Q_E r) := by
  have s1 : (zCR l Q_B ([1,0,1,1,1,0] +> r)) [target_tm]⊢⁺
      (zCR ([0,0,0,0,0,1] +> l) Q_B r) := by
    unfold zCR; simp only [append_cons,append_nil]; execute
  have s2 : (zCL ([0,0,0,0,0,1] +> l) Q_C r) [target_tm]⊢⁺
      (zCR ([0,1,0,0,0,1] +> l) Q_B r) := by
    unfold zCL zCR; simp only [append_cons,append_nil]; execute
  have s3 : (zCL ([0,1,0,0,0,1] +> l) Q_C r) [target_tm]⊢⁺
      (zCR ([0,1,0,1,0,1] +> l) Q_E r) := by
    unfold zCL zCR; simp only [append_cons,append_nil]; execute
  exact zPt s1
    (zPt (z0B h _)
      (zPt s2
        (zPt (z0B h _) s3)))
lemma z0E {r : zB} (h : Side [.hc] r r) (l : zB) :
    (zCR l Q_B ([1,0,1,1,0,1,0,1,0] +> r)) [target_tm]⊢⁺
      (zCR ([0,0,0,1,0,1,1] +> l) Q_B ([1,0] +> r)) := by
  have s1 : (zCR l Q_B ([1,0,1,1,0,1,0,1,0] +> r)) [target_tm]⊢⁺
      (zCR ([0,0,0,1,0,0,0,0,1] +> l) Q_B r) := by
    unfold zCR; simp only [append_cons,append_nil]; execute
  have s2 : (zCL ([0,0,0,1,0,0,0,0,1] +> l) Q_C r) [target_tm]⊢⁺
      (zCR ([0,1,0,1,0,0,0,0,1] +> l) Q_B r) := by
    unfold zCL zCR; simp only [append_cons,append_nil]; execute
  have s3 : (zCL ([0,1,0,1,0,0,0,0,1] +> l) Q_C r) [target_tm]⊢⁺
      (zCR ([0,0,0,1,0,1,0,0,1] +> l) Q_B r) := by
    unfold zCL zCR; simp only [append_cons,append_nil]; execute
  have s4 : (zCL ([0,0,0,1,0,1,0,0,1] +> l) Q_C r) [target_tm]⊢⁺
      (zCR ([0,1,0,1,0,1,0,0,1] +> l) Q_B r) := by
    unfold zCL zCR; simp only [append_cons,append_nil]; execute
  have s5 : (zCL ([0,1,0,1,0,1,0,0,1] +> l) Q_C r) [target_tm]⊢⁺
      (zCR ([0,0,0,1,0,1,1] +> l) Q_B ([1,0] +> r)) := by
    unfold zCL zCR; simp only [append_cons,append_nil]; execute
  exact zPt s1
    (zPt (z0B h _)
      (zPt s2
        (zPt (z0B h _)
          (zPt s3
            (zPt (z0B h _)
              (zPt s4
                (zPt (z0B h _) s5)))))))
inductive Num : Nat -> Nat -> Nat -> zF -> Prop where
  | nil : Num 0 0 0 []
  | Z {d a b w} : Num d a b w -> Num (1 + d) (a * 2) b (Z ++ w)
  | T {d a b w} : Num d a b w -> Num (1 + d) (1 + a * 2) (2 ^ d + b) (T ++ w)
lemma zPp (d : Nat) : 0 < 2 ^ d := by
  induction d with
  | zero => decide
  | succ d ih => rw [Nat.pow_succ]; omega
lemma zP2 (d : Nat) : 2 ^ (1 + d) = 2 ^ d + 2 ^ d := by
  rw [Nat.add_comm,Nat.pow_succ]; omega
lemma z0F (d : Nat) : 2 ^ (2 + d) = 4 * 2 ^ d := by
  have h : 2 + d = 1 + (1 + d) := by omega
  rw [h,zP2 (1 + d),zP2 d]; omega
lemma z0G (d : Nat) : 2 ^ (3 + d) = 8 * 2 ^ d := by
  have h : 3 + d = 1 + (2 + d) := by omega
  rw [h,zP2 (2 + d),z0F d]; omega
lemma z0H {d a b : Nat} {w : zF} (h : Num d a b w) :
    a < 2 ^ d /\ b < 2 ^ d := by
  induction h with
  | nil => simp
  | @Z d a b w _ ih =>
    rw [zP2]
    (try omega)
  | @T d a b w _ ih =>
    rw [zP2]
    (try omega)
lemma z0I (d : Nat) : Num d 0 0 (Z ^ d) := by
  induction d with
  | zero => exact Num.nil
  | succ d ih =>
    have h := Num.Z ih
    rwa [Nat.add_comm 1 d] at h
lemma z0J (d b : Nat) (hb : b < 2 ^ d) : ∃ a w,Num d a b w := by
  induction d generalizing b with
  | zero =>
    have hb0 : b = 0 := by simpa using! hb
    subst hb0
    exact ⟨0,[],Num.nil⟩
  | succ d ih =>
    rw [Nat.add_comm d 1,zP2] at hb
    by_cases hlt : b < 2 ^ d
    · rcases ih b hlt with ⟨a,w,hw⟩
      have h := Num.Z hw
      rw [Nat.add_comm 1 d] at h
      exact ⟨a * 2,Z ++ w,h⟩
    · have hsub : b - 2 ^ d < 2 ^ d := by omega
      rcases ih (b - 2 ^ d) hsub with ⟨a,w,hw⟩
      have h := Num.T hw
      have heq : 2 ^ d + (b - 2 ^ d) = b := by omega
      rw [Nat.add_comm 1 d,heq] at h
      exact ⟨1 + a * 2,T ++ w,h⟩
lemma z0K (n : Nat) :
    Seg ([Call.hb] ^ (n * 2) ++ [Call.hc]) ([Call.hb] ^ n ++ [Call.hc,Call.hc]) T T := by
  induction n with
  | zero => exact z0j
  | succ n ih =>
    have h_eq1 : (n + 1) * 2 = 2 + n * 2 := by omega
    have h_eq2 : ([Call.hb] ^ ((n + 1) * 2) ++ [Call.hc]) =
        [Call.hb,Call.hb] ++ ([Call.hb] ^ (n * 2) ++ [Call.hc]) := by
      rw [h_eq1,z08]; rfl
    have h_eq3 : ([Call.hb] ^ (n + 1) ++ [Call.hc,Call.hc]) =
        [Call.hb] ++ ([Call.hb] ^ n ++ [Call.hc,Call.hc]) := by
      rw [Nat.add_comm n 1,z08]; rfl
    rw [h_eq2,h_eq3]
    exact zSg z0p ih
lemma z0L (n : Nat) :
    Seg ([Call.hb] ^ (1 + n * 2) ++ [Call.hc]) ([Call.hb] ^ n ++ [Call.hc,Call.hc]) Z T := by
  have h_eq1 : ([Call.hb] ^ (1 + n * 2) ++ [Call.hc]) =
      [Call.hb] ++ ([Call.hb] ^ (n * 2) ++ [Call.hc]) := by
    rw [z08]; rfl
  have h_eq2 : ([Call.hb] ^ n ++ [Call.hc,Call.hc]) =
      [] ++ ([Call.hb] ^ n ++ [Call.hc,Call.hc]) := rfl
  rw [h_eq1,h_eq2]
  exact zSg z0g (z0K n)
lemma T_C (d : Nat) : Seg [Call.hc] ([Call.hc] ^ (2 ^ d)) (T ^ d) (T ^ d) := by
  induction d with
  | zero => exact z0e [Call.hc]
  | succ d ih =>
    have h_pow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    rw [h_pow,z08]
    have h_cc : [Call.hc,Call.hc] = [Call.hc] ++ [Call.hc] := rfl
    have h_step := zS0 z0j (by rw [h_cc]; exact zSg ih ih)
    exact h_step
lemma z0M (k : Nat) (r : zB) :
    Side [Call.hc] ((T ^ k) +> ([0] +> r)) ((T ^ k) +> ([0] +> r)) := by
  refine zSc (T_C k) ?_
  refine z0c ?_ (2 ^ k)
  exact zSc z0n (Side.nil r)
def z0N (n k : Nat) (t r : zB) : Prop :=
  Side ([Call.hb] ^ n ++ [Call.hc]) r ((T ^ k) +> ([0] +> t))
lemma z0O {n k : Nat} {t r : zB} (c : Nat) (h : z0N n k t r) :
    Side ([Call.hb] ^ n ++ [Call.hc] ^ (1 + c)) r ((T ^ k) +> ([0] +> t)) := by
  rw [z08,<- List.append_assoc]
  exact z0a h (z0c (z0M k t) c)
lemma z0P {n k : Nat} {t r : zB} (h : z0N n k t r) :
    z0N (1 + n * 2) (1 + k) t (Z +> r) := by
  unfold z0N
  have h_tk : (T ^ (1 + k)) +> ([0] +> t) = T +> ((T ^ k) +> ([0] +> t)) := by
    rw [zLp',append_assoc]
  rw [h_tk]
  exact zSc (z0L n) (z0O 1 h)
lemma z0Q {n k : Nat} {t r : zB} (h : z0N n k t r) :
    z0N (n * 2) (1 + k) t (T +> r) := by
  unfold z0N
  have h_tk : (T ^ (1 + k)) +> ([0] +> t) = T +> ((T ^ k) +> ([0] +> t)) := by
    rw [zLp',append_assoc]
  rw [h_tk]
  exact zSc (z0K n) (z0O 1 h)
lemma z0R {d a b : Nat} {w : zF} (h : Num d a b w) :
    ∀ {n k : Nat} {t r : zB},
      z0N n k t r -> z0N ((n + 1) * 2 ^ d - 1 - a) (d + k) t (w +> r) := by
  induction h with
  | nil =>
    intro n k t r hN
    have heq : (n + 1) * 2 ^ 0 - 1 - 0 = n := by omega
    rw [heq,Nat.zero_add,append_nil]
    exact hN
  | @Z d a b w hNum ih =>
    intro n k t r hN
    have hbnd := z0H hNum
    have hstep := z0P (ih hN)
    rw [append_assoc]
    have hle : 2 ^ d <= (n + 1) * 2 ^ d := by nlinarith
    have heq1 : 1 + (((n + 1) * 2 ^ d - 1 - a) * 2) = (n + 1) * 2 ^ (1 + d) - 1 - a * 2 := by
      rw [zP2,Nat.mul_add]; omega
    have heq2 : 1 + (d + k) = (1 + d) + k := by omega
    rwa [heq1,heq2] at hstep
  | @T d a b w hNum ih =>
    intro n k t r hN
    have hbnd := z0H hNum
    have hstep := z0Q (ih hN)
    rw [append_assoc]
    have hle : 2 ^ d <= (n + 1) * 2 ^ d := by nlinarith
    have heq1 : ((n + 1) * 2 ^ d - 1 - a) * 2 = (n + 1) * 2 ^ (1 + d) - 1 - (1 + a * 2) := by
      rw [zP2,Nat.mul_add]; omega
    have heq2 : 1 + (d + k) = (1 + d) + k := by omega
    rwa [heq1,heq2] at hstep
lemma z0S (d : Nat) :
    Seg [Call.hc] ([Call.hb] ^ (2 ^ d)) (T ^ d ++ [1,0,0]) (T ^ d ++ [1,0,0]) := by
  induction d with
  | zero => exact z0k
  | succ d ih =>
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    rw [hpow,z08]
    have h_eq : T ^ (d + 1) ++ [1,0,0] = T ++ (T ^ d ++ [1,0,0]) := by
      rw [zLp,List.append_assoc]
    rw [h_eq]
    have h_cc : [Call.hc,Call.hc] = [Call.hc] ++ [Call.hc] := rfl
    exact zS0 z0j (by rw [h_cc]; exact zSg ih ih)
lemma z0T {d a b : Nat} {w : zF} (h : Num d a b w) :
    Seg [Call.hb] ([Call.hb] ^ b ++ [Call.hc,Call.hc]) (T ^ d ++ [1,0,0]) (w ++ [1,1,0]) := by
  induction h with
  | nil => exact z0l
  | @Z d a b w hNum ih =>
    have h_eq1 : T ^ (1 + d) ++ [1,0,0] = T ++ (T ^ d ++ [1,0,0]) := by
      rw [zLp',List.append_assoc]
    have h_eq2 : (Z ++ w) ++ [1,1,0] = Z ++ (w ++ [1,1,0]) := List.append_assoc _ _ _
    rw [h_eq1,h_eq2]
    exact zS0 z0h ih
  | @T d a b w hNum ih =>
    have h_eq1 : T ^ (1 + d) ++ [1,0,0] = T ++ (T ^ d ++ [1,0,0]) := by
      rw [zLp',List.append_assoc]
    have h_eq2 : (T ++ w) ++ [1,1,0] = T ++ (w ++ [1,1,0]) := List.append_assoc _ _ _
    have h_eq3 : [Call.hb] ^ (2 ^ d + b) ++ [Call.hc,Call.hc] =
        [Call.hb] ^ (2 ^ d) ++ ([Call.hb] ^ b ++ [Call.hc,Call.hc]) := by
      rw [z08,List.append_assoc]
    rw [h_eq1,h_eq2,h_eq3]
    have h_cb : [Call.hc,Call.hb] = [Call.hc] ++ [Call.hb] := rfl
    exact zS0 z0i (by rw [h_cb]; exact zSg (z0S d) ih)
lemma z0U (n : Nat) : ([1,0] : zF) ++ T ^ n = T ^ n ++ [1,0] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [1,0] ++ ([1,0,1,0] ++ T ^ n) = ([1,0,1,0] ++ T ^ n) ++ [1,0]
    have h1 : ([1,0] : zF) ++ ([1,0,1,0] ++ T ^ n) =
        [1,0,1,0] ++ ([1,0] ++ T ^ n) := rfl
    rw [h1,ih,List.append_assoc]
lemma z0V {d a b n : Nat} {w : zF} {t r : zB}
    (hN : Num d a b w) (hR : z0N b n t r) :
    z0N 1 1 (w +> ([1,1,0] +> ((T ^ n) +> ([0] +> t))))
      ([1,1,0] +> ((T ^ (1 + d)) +> ([0] +> r))) := by
  unfold z0N
  have h_in : [Call.hb] ^ 1 ++ [Call.hc] = [Call.hb] ++ [Call.hc] := rfl
  rw [h_in]
  refine z0a (zSc z0m (Side.nil _)) ?_
  have h_mid : ([1,0,1] : zF) +> ((T ^ (1 + d)) +> ([0] +> r)) =
      [1,0,1,1,0] +> ((T ^ d ++ [1,0,0]) +> r) := by
    have h_rot : ([1,0] : zF) ++ T ^ d = T ^ d ++ [1,0] := z0U d
    calc ([1,0,1] : zF) +> ((T ^ (1 + d)) +> ([0] +> r))
      _ = [1,0,1,1,0] +> (([1,0] ++ T ^ d) +> ([0] +> r)) := by
        rw [zLp']; simp only [T,append_assoc,append_cons,append_nil]
      _ = [1,0,1,1,0] +> ((T ^ d ++ [1,0,0]) +> r) := by
        rw [h_rot]; simp only [append_assoc,append_cons,append_nil]
  rw [h_mid]
  have h_out : (T ^ 1) +> ([0] +> (w +> ([1,1,0] +> ((T ^ n) +> ([0] +> t))))) =
      [1,0,1,0,0] +> ((w ++ [1,1,0]) +> ((T ^ n) +> ([0] +> t))) := by
    simp only [z07,T,append_assoc,append_cons,append_nil]
  rw [h_out]
  exact zSc z0o (zSc (z0T hN) (z0O 1 hR))
lemma z0W {d a b : Nat} {w : zF} (h : Num d a b w) (hb : b = 0) :
    a = 0 /\ w = Z ^ d := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | @Z d a b w hNum ih =>
    rcases ih hb with ⟨rfl,rfl⟩
    exact ⟨rfl,(zLp' Z d).symm⟩
  | @T d a b w hNum _ =>
    have hpos := zPp d
    (try omega)
inductive RC : Nat -> Nat -> zB -> Prop where
  | base (d : Nat) : RC d (2 ^ d - 1) ((Z ^ d) +> default)
  | node {d a b h k q : Nat} {w : zF} {r : zB} :
      Num d a b w -> RC k q r -> k < h -> h <= d ->
      RC (1 + d) (2 ^ (1 + d) - 1 - a) (w +> ([1,1,0] +> ((T ^ h) +> ([0] +> r))))
lemma z0X {k q : Nat} {r : zB} (h : RC k q r) :
    q < 2 ^ k /\ (0 < k -> 2 ^ (k - 1) <= q) := by
  cases h with
  | base =>
    have hpos := zPp k
    refine ⟨by omega,fun hk => ?_⟩
    cases k with
    | zero => omega
    | succ k =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      simp only [Nat.add_sub_cancel]; omega
  | @node d a b h k q w r hNum _ _ _ =>
    have hbnd := z0H hNum
    have hpow := zP2 d
    refine ⟨by omega,fun _ => ?_⟩
    have hsub : 1 + d - 1 = d := by omega
    rw [hsub]; omega
lemma z0Y {q : Nat} {r : zB} (h : RC 0 q r) : q = 0 /\ r = default := by
  generalize hk : (0 : Nat) = k at h
  cases h with
  | base =>
    subst hk
    exact ⟨rfl,rfl⟩
  | node =>
    (try omega)
lemma z0Z {d a q k k' q' : Nat} {w : zF} {r t : zB}
    (hN : Num d a q w) (hR : RC k q r) (hT : RC k' q' t)
    (hk : (k = 0 /\ k' = 0) \/ k' < k) (hd : k <= d) :
    RC (1 + d) (2 ^ (1 + d) - 1 - a) (w +> ([1,1,0] +> ((T ^ k) +> ([0] +> t)))) := by
  cases k with
  | zero =>
    rcases z0Y hR with ⟨rfl,rfl⟩
    have hk'0 : k' = 0 := by omega
    subst hk'0
    rcases z0Y hT with ⟨rfl,rfl⟩
    rcases z0W hN rfl with ⟨rfl,rfl⟩
    have h_z : ([1,1,0] : zF) +> ((T ^ 0) +> ([0] +> default)) = Z +> default := rfl
    rw [h_z,<- append_assoc,<- z09' Z d]
    have h_base := RC.base (1 + d)
    have h_eq1 : 1 + d = d + 1 := by omega
    have h_eq2 : 2 ^ (1 + d) - 1 - 0 = 2 ^ (1 + d) - 1 := by omega
    rw [h_eq2]
    rwa [<- h_eq1]
  | succ k =>
    have hk' : k' < k + 1 := by omega
    exact RC.node hN hT hk' hd
lemma z10 {a b : Nat} (h : a <= b) : 2 ^ a <= 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h
lemma z11 {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b :=
  Nat.pow_lt_pow_right (by decide) h
lemma z12 {k q : Nat} {r : zB} (h : RC k q r) :
    ∃ k' q' t,RC k' q' t /\ ((k = 0 /\ k' = 0) \/ k' < k) /\ z0N q k t r := by
  induction h with
  | base d =>
    refine ⟨0,0,default,RC.base 0,by omega,?_⟩
    have hN := z0R (z0I d) (n := 0) (k := 0) (t := default) (r := default) ?_
    · have heq1 : (0 + 1) * 2 ^ d - 1 - 0 = 2 ^ d - 1 := by omega
      have heq2 : d + 0 = d := by omega
      rwa [heq1,heq2] at hN
    · unfold z0N
      have h_fc := z0M 0 default
      simpa [list_nat_repeat,z00] using! h_fc
  | @node d a b h k q w r hNum hRC hkh hhd ih =>
    rcases ih with ⟨k',q',t,hT,hk,hN⟩
    cases h with
    | zero => omega
    | succ h =>
      have h_rc_bnd := z0X hRC
      have h_pow_le : 2 ^ k <= 2 ^ h := z10 (by omega)
      have hq_lt : q < 2 ^ h := by omega
      rcases z0J h q hq_lt with ⟨a',w',hw'⟩
      refine ⟨1 + h,2 ^ (1 + h) - 1 - a',w' +> ([1,1,0] +> ((T ^ k) +> ([0] +> t))),
        z0Z hw' hRC hT hk (by omega),by omega,?_⟩
      have h_mn := z0V hw' hN
      have h_step := z0R hNum h_mn
      have hbnd := z0H hNum
      have heq1 : (1 + 1) * 2 ^ d - 1 - a = 2 ^ (1 + d) - 1 - a := by
        rw [zP2]; omega
      have heq2 : d + 1 = 1 + d := by omega
      have heq3 : 1 + h = h + 1 := by omega
      rwa [heq1,heq2,heq3] at h_step
def z13 (w : zF) (h : Nat) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  zCR lh Q_B ([0,1,0] +> (w +> ([1,1,0] +> ((T ^ h) +> ([0] +> r)))))
lemma z14 {n m k : Nat} {t r : zB} (h : z0N (n + m) k t r) :
    ∃ r',Side ([Call.hb] ^ n) r r' /\ z0N m k t r' := by
  unfold z0N at h ⊢
  rw [z08,List.append_assoc] at h
  exact z0b h
lemma z15 {i : Nat} {r r' : zB} (h : Side ([Call.hb] ^ (2 ^ i)) r r') :
    (zCR lh Q_B ((T ^ i) +> ([0] +> r))) [target_tm]⊢⁺
      (zCR lh Q_B ((T ^ (1 + i)) +> ([0] +> r'))) := by
  have s1 := z0B (z0M i r) lh
  have s2 := z0w ((T ^ i) +> ([0] +> r))
  have h_mid1 : ([1,0] : zF) +> ((T ^ i) +> ([0] +> r)) = (T ^ i ++ [1,0,0]) +> r := by
    have h_rot := z0U i
    calc ([1,0] : zF) +> ((T ^ i) +> ([0] +> r))
      _ = ([1,0] ++ T ^ i) +> ([0] +> r) := by simp only [append_assoc]
      _ = (T ^ i ++ [1,0,0]) +> r := by rw [h_rot]; simp only [append_assoc,append_cons,append_nil]
  have s3 := z0B (zSc (z0S i) h) lh
  rw [<- h_mid1] at s3
  have s4 := z0w ((T ^ i ++ [1,0,0]) +> r')
  have h_mid2 : ([1,0] : zF) +> ((T ^ i ++ [1,0,0]) +> r') =
      (T ^ (1 + i)) +> ([0] +> r') := by
    have h_rot := z0U i
    have h1 : ([1,0] : zF) +> ((T ^ i ++ [1,0,0]) +> r') =
        (([1,0] ++ T ^ i) ++ [1,0]) +> ([0] +> r') := by
      simp only [append_assoc,append_cons,append_nil]
    have h2 : (T ^ (1 + i)) +> ([0] +> r') =
        (T ^ i ++ ([1,0] ++ [1,0])) +> ([0] +> r') := by
      rw [Nat.add_comm 1 i,z08,z07]
      simp only [T,append_assoc,append_cons,append_nil]
    rw [h1,h2,h_rot,List.append_assoc]
  rw [h_mid2] at s4
  exact zPt s1 (zPt s2 (zPt s3 s4))
lemma z16 {i a b k : Nat} {w : zF} {t r : zB}
    (hN : Num i a b w) (hR : z0N b k t r) :
    (zCR lh Q_B ((T ^ i) +> ([0] +> r))) [target_tm]⊢⁺ z13 w k t := by
  have s1 := z0B (z0M i r) lh
  have s2 := z0w ((T ^ i) +> ([0] +> r))
  have h_mid1 : ([1,0] : zF) +> ((T ^ i) +> ([0] +> r)) = (T ^ i ++ [1,0,0]) +> r := by
    have h_rot := z0U i
    calc ([1,0] : zF) +> ((T ^ i) +> ([0] +> r))
      _ = ([1,0] ++ T ^ i) +> ([0] +> r) := by simp only [append_assoc]
      _ = (T ^ i ++ [1,0,0]) +> r := by rw [h_rot]; simp only [append_assoc,append_cons,append_nil]
  have s3 := z0C (zSc (z0T hN) (z0O 1 hR)) lh
  rw [<- h_mid1] at s3
  have s4 := z0v ((w ++ [1,1,0]) +> ((T ^ k) +> ([0] +> t)))
  have s14 := zPt s1 (zPt s2 (zPt s3 s4))
  simpa only [z13,append_assoc] using! s14
lemma z17 (n : Nat) :
    ∀ {i a b q k : Nat} {w : zF} {t r : zB},
      Num (n + i) a b w -> q + 2 ^ i = 2 ^ (n + i) + b -> z0N q k t r ->
      (zCR lh Q_B ((T ^ i) +> ([0] +> r))) [target_tm]⊢⁺ z13 w k t := by
  induction n with
  | zero =>
    intro i a b q k w t r hN hq hR
    rw [Nat.zero_add] at hN hq
    have hqb : q = b := by omega
    subst hqb
    exact z16 hN hR
  | succ n ih =>
    intro i a b q k w t r hN hq hR
    have hpow : 2 ^ (1 + i) <= 2 ^ (n + 1 + i) := z10 (by omega)
    have hpow_succ := zP2 i
    have hq_split : q = 2 ^ i + (q - 2 ^ i) := by omega
    rw [hq_split] at hR
    rcases z14 hR with ⟨r',h1,h2⟩
    have s1 := z15 h1
    have heq_ni : n + 1 + i = n + (1 + i) := by omega
    rw [heq_ni] at hN hq
    have s2 := ih hN (q := q - 2 ^ i) (by omega) h2
    exact zPt s1 s2
lemma z18 (n : Nat) :
    Seg ([Call.hb] ^ (1 + n * 2)) ([Call.hb] ^ n ++ [Call.hc,Call.hc])
      [1,0,1,1,0,0] [1,0,1,1,1,0] := by
  induction n with
  | zero => exact z0t
  | succ n ih =>
    have heq1 : 1 + (n + 1) * 2 = 2 + (1 + n * 2) := by omega
    have heq2 : [Call.hb] ^ (1 + (n + 1) * 2) = [Call.hb,Call.hb] ++ [Call.hb] ^ (1 + n * 2) := by
      rw [heq1,z08]; rfl
    have heq3 : [Call.hb] ^ (n + 1) ++ [Call.hc,Call.hc] =
        [Call.hb] ++ ([Call.hb] ^ n ++ [Call.hc,Call.hc]) := by
      rw [Nat.add_comm n 1,z08]; rfl
    rw [heq2,heq3]
    exact zSg z0s ih
lemma z19 (s : Nat) (r l : zB) :
    (zCR l Q_B ([1,0,1,1,1,0] +> ((T ^ (1 + s)) +> ([0] +> r)))) [target_tm]⊢⁺
      (zCR ([0,0,0,1,0,1,0,1] +> l) Q_B ((T ^ s ++ [1,0,0]) +> r)) := by
  have s1 := z0D (z0M (1 + s) r) l
  have h_ts : (T ^ (1 + s)) +> ([0] +> r) = [1,0] +> ((T ^ s ++ [1,0,0]) +> r) := by
    have h_rot := z0U s
    calc (T ^ (1 + s)) +> ([0] +> r)
      _ = [1,0] +> (([1,0] ++ T ^ s) +> ([0] +> r)) := by
        rw [zLp']; simp only [T,append_assoc,append_cons,append_nil]
      _ = [1,0] +> ((T ^ s ++ [1,0,0]) +> r) := by
        rw [h_rot]; simp only [append_assoc,append_cons,append_nil]
  have s2 := E10 ([0,1,0,1,0,1] +> l) ((T ^ s ++ [1,0,0]) +> r)
  rw [<- h_ts] at s2
  have s12 := zPt s1 s2
  simpa only [append_assoc,append_cons,append_nil] using! s12
lemma z1a (s : Nat) {r r' : zB}
    (h : Side ([Call.hb] ^ (2 ^ s)) r r') :
    Side [Call.hc] ([1,0,1,1,1,0] +> ((T ^ s) +> ([0] +> r)))
      ((T ^ (1 + s)) +> ([1,0,0] +> r')) := by
  cases s with
  | zero =>
    have h1 := zSc z0u h
    simpa only [z06,z07,T,append_assoc,append_cons,append_nil] using! h1
  | succ s =>
    have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [Nat.pow_succ]; omega
    rw [hpow,z08] at h
    rcases z0b h with ⟨r1,h1,h2⟩
    refine Side.cons (fun l => ?_) (Side.nil _)
    have heq_s : s + 1 = 1 + s := by omega
    rw [heq_s]
    have s1 := z19 s r l
    have s2 := z0B (zSc (z0S s) h1) ([0,0,0,1,0,1,0,1] +> l)
    have s3 := z0x l ((T ^ s ++ [1,0,0]) +> r1)
    have s4 := z0B (zSc (z0S s) h2) ([0,1,0,1,0,1,0,1] +> l)
    have s5 := z0y l ((T ^ s ++ [1,0,0]) +> r')
    have h_end : T +> (T +> ((T ^ s ++ [1,0,0]) +> r')) =
        (T ^ (1 + (1 + s))) +> ([1,0,0] +> r') := by
      simp only [zLp',T,append_assoc,append_cons,append_nil]
    rw [h_end] at s5
    exact zPt s1
      (zPt s2
        (zPt s3
          (zPt s4 s5)))
lemma z1b {n k : Nat} {t r r' : zB}
    (h1 : Side [Call.hb] r r') (h2 : z0N n k t r') : z0N (1 + n) k t r := by
  unfold z0N at h2 ⊢
  rw [z08,List.append_assoc]
  exact z0a h1 h2
lemma z1c {α : Type*} (l : List α) (m n : Nat) : l ^ (m * n) = (l ^ n) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have heq : (m + 1) * n = n + m * n := by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]
    rw [heq,z08,zLp,ih]
lemma z1d (j n : Nat) :
    Seg ([Call.hc] ^ n) ([Call.hb] ^ (n * 2 ^ j)) (T ^ j ++ [1,0,0]) (T ^ j ++ [1,0,0]) := by
  rw [z1c]
  exact z0f (z0S j) n
lemma z1e {j a b k : Nat} {w : zF} {t r u : zB}
    (hN : Num j a b w) (hR : z0N b k t r)
    (hM : z0N 1 1 u ([1,1,0] +> ((T ^ k) +> ([0] +> t)))) :
    z0N (2 ^ (1 + j) - a) (1 + j) u ((T ^ j ++ [1,0,0]) +> r) := by
  have hbnd := z0H hN
  have h1 := zSc (z0T hN) (z0O 1 hR)
  rw [append_assoc w [1,1,0]] at h1
  have h2 := z1b h1 (z0R hN hM)
  have heq1 : 1 + ((1 + 1) * 2 ^ j - 1 - a) = 2 ^ (1 + j) - a := by
    rw [zP2]; omega
  have heq2 : j + 1 = 1 + j := by omega
  rwa [heq1,heq2] at h2
lemma z1f {s m a b k : Nat} {w : zF} {t r u : zB}
    (hN : Num (1 + s) a b w)
    (hR : z0N (2 ^ s + m * 2 ^ (1 + s) + b) k t r)
    (hM : z0N 1 1 u ([1,1,0] +> ((T ^ k) +> ([0] +> t)))) :
    Side ([Call.hc] ^ (1 + m) ++ ([Call.hb] ^ (2 ^ (2 + s) - a) ++ [Call.hc]))
      ([1,0,1,1,1,0] +> ((T ^ s) +> ([0] +> r))) ((T ^ (2 + s)) +> ([0] +> u)) := by
  have heq_split : 2 ^ s + m * 2 ^ (1 + s) + b = 2 ^ s + (m * 2 ^ (1 + s) + b) := by omega
  rw [heq_split] at hR
  rcases z14 hR with ⟨r1,h1,h23⟩
  rcases z14 h23 with ⟨r2,h2,h3⟩
  have heq_hc : [Call.hc] ^ (1 + m) ++ ([Call.hb] ^ (2 ^ (2 + s) - a) ++ [Call.hc]) =
      [Call.hc] ++ ([Call.hc] ^ m ++ ([Call.hb] ^ (2 ^ (2 + s) - a) ++ [Call.hc])) := by
    rw [z08,List.append_assoc]; rfl
  rw [heq_hc]
  refine z0a (z1a s h1) ?_
  rw [<- append_assoc (T ^ (1 + s)) [1,0,0]]
  refine z0a (zSc (z1d (1 + s) m) h2) ?_
  have h_fin := z1e hN h3 hM
  have heq_s : 1 + (1 + s) = 2 + s := by omega
  rwa [heq_s] at h_fin
lemma z1g {s a b k : Nat} {w : zF} {t r : zB}
    (hN : Num s a b w) (hR : z0N (2 ^ s + b) k t r) :
    Side [Call.hb] ([1,0,1,1,1,0] +> ((T ^ (1 + s)) +> ([0] +> r)))
      (T +> (T +> (w +> ([1,1,0] +> ((T ^ k) +> ([0] +> t)))))) := by
  rcases z14 hR with ⟨r1,h1,h2⟩
  refine Side.cons (fun l => ?_) (Side.nil _)
  have s1 := z19 s r l
  have s2 := z0B (zSc (z0S s) h1) ([0,0,0,1,0,1,0,1] +> l)
  have s3 := z0x l ((T ^ s ++ [1,0,0]) +> r1)
  have s4 := z0C (zSc (z0T hN) (z0O 1 h2)) ([0,1,0,1,0,1,0,1] +> l)
  have s5 := z0z l ((w ++ [1,1,0]) +> ((T ^ k) +> ([0] +> t)))
  have s15 := zPt s1
    (zPt s2
      (zPt s3
        (zPt s4 s5)))
  simpa only [zCs,append_assoc] using! s15
lemma z1h {s a b k : Nat} {w : zF} {t r u : zB}
    (hN : Num s a b w) (hR : z0N (2 ^ s + b) k t r)
    (hM : z0N 1 1 u ([1,1,0] +> ((T ^ k) +> ([0] +> t)))) :
    z0N (2 ^ (3 + s) - 3 - a * 4) (3 + s) u
      ([1,0,1,1,1,0] +> ((T ^ (1 + s)) +> ([0] +> r))) := by
  have hbnd := z0H hN
  have hstep := z1b (z1g hN hR) (z0Q (z0Q (z0R hN hM)))
  have hpow3 := z0G s
  have heq1 : 1 + (((1 + 1) * 2 ^ s - 1 - a) * 2 * 2) = 2 ^ (3 + s) - 3 - a * 4 := by
    (try omega)
  have heq2 : 1 + (1 + (s + 1)) = 3 + s := by omega
  rwa [heq1,heq2] at hstep
lemma T_B (n : Nat) : Seg ([Call.hb] ^ (n * 2)) ([Call.hb] ^ n) T T := by
  induction n with
  | zero => exact z0d T
  | succ n ih =>
    have heq1 : (n + 1) * 2 = 2 + n * 2 := by omega
    have heq2 : [Call.hb] ^ ((n + 1) * 2) = [Call.hb,Call.hb] ++ [Call.hb] ^ (n * 2) := by
      rw [heq1,z08]; rfl
    have heq3 : [Call.hb] ^ (n + 1) = [Call.hb] ++ [Call.hb] ^ n := by
      rw [Nat.add_comm n 1,z08]; rfl
    rw [heq2,heq3]
    exact zSg z0p ih
lemma Z_B (n : Nat) : Seg ([Call.hb] ^ (1 + n * 2)) ([Call.hb] ^ n) Z T := by
  have heq1 : [Call.hb] ^ (1 + n * 2) = [Call.hb] ++ [Call.hb] ^ (n * 2) := by
    rw [z08]; rfl
  have heq2 : [Call.hb] ^ n = [] ++ [Call.hb] ^ n := rfl
  rw [heq1,heq2]
  exact zSg z0g (T_B n)
lemma z1i {d a b : Nat} {w : zF} (h : Num d a b w) (n : Nat) :
    Seg ([Call.hb] ^ ((n + 1) * 2 ^ d - 1 - a)) ([Call.hb] ^ n) w (T ^ d) := by
  induction h with
  | nil =>
    have heq : (n + 1) * 2 ^ 0 - 1 - 0 = n := by omega
    rw [heq]
    exact z0e ([Call.hb] ^ n)
  | @Z d a b w hNum ih =>
    have hbnd := z0H hNum
    have hstep := zS0 (Z_B ((n + 1) * 2 ^ d - 1 - a)) ih
    have hle : 2 ^ d <= (n + 1) * 2 ^ d := by nlinarith
    have heq1 : 1 + ((n + 1) * 2 ^ d - 1 - a) * 2 = (n + 1) * 2 ^ (1 + d) - 1 - a * 2 := by
      rw [zP2,Nat.mul_add]; omega
    rw [zLp' T d]
    rwa [heq1] at hstep
  | @T d a b w hNum ih =>
    have hbnd := z0H hNum
    have hstep := zS0 (T_B ((n + 1) * 2 ^ d - 1 - a)) ih
    have hle : 2 ^ d <= (n + 1) * 2 ^ d := by nlinarith
    have heq1 : ((n + 1) * 2 ^ d - 1 - a) * 2 = (n + 1) * 2 ^ (1 + d) - 1 - (1 + a * 2) := by
      rw [zP2,Nat.mul_add]; omega
    rw [zLp' T d]
    rwa [heq1] at hstep
lemma z1j (j n : Nat) : Seg ([Call.hb] ^ (n * 2 ^ j)) ([Call.hb] ^ n) (T ^ j) (T ^ j) := by
  induction j generalizing n with
  | zero =>
    have heq : n * 2 ^ 0 = n := by omega
    rw [heq]
    exact z0e ([Call.hb] ^ n)
  | succ j ih =>
    have hstep := zS0 (T_B (n * 2 ^ j)) (ih n)
    have heq1 : n * 2 ^ j * 2 = n * 2 ^ (j + 1) := by rw [Nat.pow_succ,Nat.mul_assoc]
    have heq2 : T ++ T ^ j = T ^ (j + 1) := rfl
    rwa [heq1,heq2] at hstep
lemma z1k {j a b : Nat} {w : zF} (h : Num j a b w) :
    Seg [Call.hb] ([Call.hc] ^ b ++ [Call.hb]) (T ^ j) w := by
  induction h with
  | nil => exact z0e [Call.hb]
  | @Z d a b w hNum ih =>
    rw [zLp' T d]
    exact zS0 z0h ih
  | @T d a b w hNum ih =>
    rw [zLp' T d]
    have heq : [Call.hc] ^ (2 ^ d + b) ++ [Call.hb] =
        [Call.hc] ^ (2 ^ d) ++ ([Call.hc] ^ b ++ [Call.hb]) := by
      rw [z08,List.append_assoc]
    rw [heq]
    have h_cb : [Call.hc,Call.hb] = [Call.hc] ++ [Call.hb] := rfl
    exact zS0 z0i (by rw [h_cb]; exact zSg (T_C d) ih)
lemma z1l {j a b : Nat} {w : zF} (n : Nat) (h : Num j a b w) :
    Seg ([Call.hb] ^ ((1 + n) * 2 ^ j - a)) ([Call.hc] ^ b ++ [Call.hb] ^ (1 + n)) (T ^ j) (T ^ j) := by
  have hbnd := z0H h
  have hle : 2 ^ j <= (n + 1) * 2 ^ j := by nlinarith
  have heq1 : (1 + n) * 2 ^ j - a = 1 + ((n + 1) * 2 ^ j - 1 - a) := by
    rw [Nat.add_comm 1 n]; omega
  have heq2 : [Call.hb] ^ ((1 + n) * 2 ^ j - a) =
      [Call.hb] ++ [Call.hb] ^ ((n + 1) * 2 ^ j - 1 - a) := by
    rw [heq1,z08]; rfl
  have heq3 : [Call.hc] ^ b ++ [Call.hb] ^ (1 + n) =
      ([Call.hc] ^ b ++ [Call.hb]) ++ [Call.hb] ^ n := by
    rw [z08,List.append_assoc]; rfl
  rw [heq2,heq3]
  exact zSg (z1k h) (z1i h n)
lemma z1m {j a b : Nat} {w : zF} (p n : Nat) (h : Num j a b w) :
    Seg ([Call.hb] ^ ((p + 1 + n) * 2 ^ j - a) ++ [Call.hc])
      ([Call.hb] ^ p ++ [Call.hc] ^ b ++ [Call.hb] ^ (1 + n) ++ [Call.hc] ^ (2 ^ j)) (T ^ j) (T ^ j) := by
  have hbnd := z0H h
  have h1 := zSg (z1j j p) (zSg (z1l n h) (T_C j))
  have heq_in : [Call.hb] ^ (p * 2 ^ j) ++ ([Call.hb] ^ ((1 + n) * 2 ^ j - a) ++ [Call.hc]) =
      [Call.hb] ^ ((p + 1 + n) * 2 ^ j - a) ++ [Call.hc] := by
    rw [<- List.append_assoc,<- z08]
    congr 1; congr 1
    have hle : 2 ^ j <= (1 + n) * 2 ^ j := by nlinarith
    have : (p + 1 + n) * 2 ^ j = p * 2 ^ j + (1 + n) * 2 ^ j := by
      rw [Nat.add_assoc p 1 n,Nat.add_mul]
    (try omega)
  have heq_out : [Call.hb] ^ p ++ (([Call.hc] ^ b ++ [Call.hb] ^ (1 + n)) ++ [Call.hc] ^ (2 ^ j)) =
      [Call.hb] ^ p ++ [Call.hc] ^ b ++ [Call.hb] ^ (1 + n) ++ [Call.hc] ^ (2 ^ j) := by
    simp only [List.append_assoc]
  rwa [heq_in,heq_out] at h1
lemma z1n {d a b : Nat} {w : zF} (h : Num d a b w) :
    Num (1 + d) a (b * 2) (w ++ Z) := by
  induction h with
  | nil => exact Num.Z Num.nil
  | @Z d a b w hNum ih =>
    have h1 := Num.Z ih
    rwa [List.append_assoc]
  | @T d a b w hNum ih =>
    have h1 := Num.T ih
    rw [List.append_assoc]
    have heq : 2 ^ (1 + d) + b * 2 = (2 ^ d + b) * 2 := by rw [zP2]; omega
    rwa [heq] at h1
lemma z1o {d a b : Nat} {w : zF} (h : Num d a b w) :
    Num (1 + d) (2 ^ d + a) (1 + b * 2) (w ++ T) := by
  induction h with
  | nil => exact Num.T Num.nil
  | @Z d a b w hNum ih =>
    have h1 := Num.Z ih
    rw [List.append_assoc]
    have heq : (2 ^ d + a) * 2 = 2 ^ (1 + d) + a * 2 := by rw [zP2]; omega
    rwa [heq] at h1
  | @T d a b w hNum ih =>
    have h1 := Num.T ih
    rw [List.append_assoc]
    have heq1 : 1 + (2 ^ d + a) * 2 = 2 ^ (1 + d) + (1 + a * 2) := by rw [zP2]; omega
    have heq2 : 2 ^ (1 + d) + (1 + b * 2) = 1 + (2 ^ d + b) * 2 := by rw [zP2]; omega
    rwa [heq1,heq2] at h1
lemma z1p {d a b : Nat} {w : zF} (h : Num d a b w) :
    ∃ w',Num d b a w' := by
  induction h with
  | nil => exact ⟨[],Num.nil⟩
  | @Z d a b w _ ih =>
    rcases ih with ⟨w',hw'⟩
    exact ⟨w' ++ Z,z1n hw'⟩
  | @T d a b w _ ih =>
    rcases ih with ⟨w',hw'⟩
    exact ⟨w' ++ T,z1o hw'⟩
lemma z1q {d a b : Nat} {w : zF} (h : Num d a b w) :
    ∃ w',Num d (2 ^ d - 1 - a) (2 ^ d - 1 - b) w' := by
  induction h with
  | nil => exact ⟨[],Num.nil⟩
  | @Z d a b w hNum ih =>
    rcases ih with ⟨w',hw'⟩
    have hbnd := z0H hNum
    have h1 := Num.T hw'
    have heq1 : 1 + (2 ^ d - 1 - a) * 2 = 2 ^ (1 + d) - 1 - a * 2 := by rw [zP2]; omega
    have heq2 : 2 ^ d + (2 ^ d - 1 - b) = 2 ^ (1 + d) - 1 - b := by rw [zP2]; omega
    rw [heq1,heq2] at h1
    exact ⟨T ++ w',h1⟩
  | @T d a b w hNum ih =>
    rcases ih with ⟨w',hw'⟩
    have hbnd := z0H hNum
    have h1 := Num.Z hw'
    have heq1 : (2 ^ d - 1 - a) * 2 = 2 ^ (1 + d) - 1 - (1 + a * 2) := by rw [zP2]; omega
    have heq2 : 2 ^ d - 1 - b = 2 ^ (1 + d) - 1 - (2 ^ d + b) := by rw [zP2]; omega
    rw [heq1,heq2] at h1
    exact ⟨Z ++ w',h1⟩
lemma z1r {p n k : Nat} {t r r' : zB}
    (h1 : Side ([Call.hb] ^ p) r r') (h2 : z0N n k t r') :
    z0N (p + n) k t r := by
  unfold z0N at h2 ⊢
  rw [z08,List.append_assoc]
  exact z0a h1 h2
lemma z1s {s a b q e : Nat} {w we : zF} {r v t u : zB}
    (hN : Num s a b w) (hQ : Num s e q we)
    (hM : z0N 1 1 v ([1,1,0] +> ((T ^ (1 + s)) +> ([0] +> r))))
    (hR : z0N (2 ^ (1 + s) - 1 - e) (1 + s) t v)
    (hM' : z0N 1 1 u ([1,1,0] +> ((T ^ (1 + s)) +> ([0] +> t)))) :
    z0N (2 ^ (3 + s) - a * 2 + q * 4) (3 + s) u
      ([1,0] +> (Z +> (w +> ([1,1,0] +> ((T ^ (1 + s)) +> ([0] +> r)))))) := by
  rcases z1p hQ with ⟨wq,hq⟩
  rcases z1q hq with ⟨wq',hq'⟩
  have hbndN := z0H hN
  have hbndQ := z0H hQ
  have hR' : z0N (2 ^ s + (2 ^ s - 1 - e)) (1 + s) t v := by
    have heq : 2 ^ s + (2 ^ s - 1 - e) = 2 ^ (1 + s) - 1 - e := by rw [zP2]; omega
    rwa [heq]
  have hP := z0O 1 (z0R hN hM)
  have hpre := zSc (z18 ((1 + 1) * 2 ^ s - 1 - a)) hP
  have h_in : ([1,0,1,1,0,0] : zF) +> (w +> ([1,1,0] +> ((T ^ (1 + s)) +> ([0] +> r)))) =
      [1,0] +> (Z +> (w +> ([1,1,0] +> ((T ^ (1 + s)) +> ([0] +> r))))) := rfl
  rw [h_in] at hpre
  have hpost := z1h hq' hR' hM'
  have h_s1 : s + 1 = 1 + s := by omega
  rw [h_s1] at hpre
  have hcomb := z1r hpre hpost
  have hpow3 := z0G s
  have heq : (1 + ((1 + 1) * 2 ^ s - 1 - a) * 2) + (2 ^ (3 + s) - 3 - (2 ^ s - 1 - q) * 4) =
      2 ^ (3 + s) - a * 2 + q * 4 := by
    (try omega)
  rwa [heq] at hcomb
lemma z1t (h : Nat) (r l : zB) :
    (zCR l Q_B ([1,0] +> ([1,1,0] +> ((T ^ (1 + h)) +> ([0] +> r))))) [target_tm]⊢⁺
      (zCR ([0,0,0,1,0,1,1] +> l) Q_B ((T ^ h ++ [1,0,0]) +> r)) := by
  have s1 := z0E (z0M h r) l
  have h_in : ([1,0,1,1,0,1,0,1,0] : zF) +> ((T ^ h) +> ([0] +> r)) =
      [1,0] +> ([1,1,0] +> ((T ^ (1 + h)) +> ([0] +> r))) := by
    rw [zLp']; simp only [T,append_assoc,append_cons,append_nil]
  rw [h_in] at s1
  have h_out : ([1,0] : zF) +> ((T ^ h) +> ([0] +> r)) = (T ^ h ++ [1,0,0]) +> r := by
    have h_rot := z0U h
    calc ([1,0] : zF) +> ((T ^ h) +> ([0] +> r))
      _ = ([1,0] ++ T ^ h) +> ([0] +> r) := by simp only [append_assoc]
      _ = (T ^ h ++ [1,0,0]) +> r := by rw [h_rot]; simp only [append_assoc,append_cons,append_nil]
  rwa [h_out] at s1
lemma z1u {h a q k : Nat} {w : zF} {t r : zB}
    (hN : Num h a q w) (hR : z0N q k t r) :
    Side [Call.hb] ([1,0] +> ([1,1,0] +> ((T ^ (1 + h)) +> ([0] +> r))))
      ([1,0,1,1,1,0,0] +> (w +> ([1,1,0] +> ((T ^ k) +> ([0] +> t))))) := by
  refine Side.cons (fun l => ?_) (Side.nil _)
  have s1 := z1t h r l
  have s2 := z0C (zSc (z0T hN) (z0O 1 hR)) ([0,0,0,1,0,1,1] +> l)
  have s3 := z0A l ((w ++ [1,1,0]) +> ((T ^ k) +> ([0] +> t)))
  have s13 := zPt s1 (zPt s2 s3)
  simpa only [zCs,append_assoc] using! s13
lemma z1v {hs : List Call} {k : Nat} {t r : zB} (c : Nat)
    (h : Side (hs ++ [Call.hc]) r ((T ^ k) +> ([0] +> t))) :
    Side (hs ++ [Call.hc] ^ (1 + c)) r ((T ^ k) +> ([0] +> t)) := by
  rw [z08,<- List.append_assoc]
  exact z0a h (z0c (z0M k t) c)
lemma z1w {j a b p n k : Nat} {w : zF} {t r : zB}
    (hN : Num j a b w)
    (hR : Side ([Call.hb] ^ p ++ [Call.hc] ^ b ++ [Call.hb] ^ (1 + n) ++ [Call.hc]) r ((T ^ k) +> ([0] +> t))) :
    z0N ((p + 1 + n) * 2 ^ j - a) (j + k) t ((T ^ j) +> r) := by
  unfold z0N
  rw [z08,append_assoc]
  refine zSc (z1m p n hN) ?_
  have hpos := zPp j
  have h_more := z1v (2 ^ j - 1) hR
  have heq : 1 + (2 ^ j - 1) = 2 ^ j := by omega
  rwa [heq] at h_more
lemma z1x {d a b d' a' b' : Nat} {w w' : zF}
    (h : Num d a b w) (h' : Num d' a' b' w') (hd : d = d') (ha : a = a') : b = b' /\ w = w' := by
  induction h generalizing d' a' b' w' with
  | nil =>
    cases h' with
    | nil => exact ⟨rfl,rfl⟩
    | Z => omega
    | T => omega
  | @Z d a b w hNum ih =>
    cases h' with
    | nil => omega
    | @Z d1 a1 b0 w0 h0 =>
      rcases ih h0 (by omega) (by omega) with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
    | @T d1 a1 b0 w0 h0 =>
      (try omega)
  | @T d a b w hNum ih =>
    cases h' with
    | nil => omega
    | @Z d1 a1 b0 w0 h0 =>
      (try omega)
    | @T d1 a1 b0 w0 h0 =>
      have hd1 : d1 = d := by omega
      subst d1
      rcases ih h0 rfl (by omega) with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
lemma z1y {d a b b' : Nat} {w w' : zF}
    (h : Num d a b w) (h' : Num d a b' w') : b = b' /\ w = w' :=
  z1x h h' rfl rfl
lemma z1z {d a b : Nat} {w : zF} (h : Num d a b w) (ha : a + 1 < 2 ^ d) :
    ∃ e b' w',e < d /\ Num d (1 + a) b' w' /\
      b' + 2 ^ d = b + 3 * 2 ^ e /\ 2 ^ e <= b' /\ b' < 2 ^ (1 + e) := by
  induction h with
  | nil =>
    simp at ha
  | @Z d a b w hNum _ =>
    have hbnd := z0H hNum
    have hpow := zP2 d
    refine ⟨d,2 ^ d + b,T ++ w,by omega,Num.T hNum,by omega,by omega,by omega⟩
  | @T d a b w hNum ih =>
    have hpow := zP2 d
    rcases ih (by omega) with ⟨e,b',w',he,hN',hsum,hle,hlt⟩
    have hZ := Num.Z hN'
    have heq : (1 + a) * 2 = 1 + (1 + a * 2) := by omega
    rw [heq] at hZ
    refine ⟨e,b',Z ++ w',by omega,hZ,by omega,hle,hlt⟩
lemma z1A {j c z : Nat} {w : zF} (hN : Num j c z w) (hz : 0 < z) :
    ∃ e f wf,0 < e /\ e <= j /\ 2 ^ (e - 1) <= z /\ z < 2 ^ e /\
      Num (1 + j) f (2 ^ (1 + j) - c) wf /\ f + z * 2 + 1 = 3 * 2 ^ e := by
  have hbnd := z0H hN
  have hc_pos : 0 < c := by
    by_contra h0
    have hc0 : c = 0 := by omega
    subst hc0
    rcases z1y (z0I j) hN with ⟨rfl,_⟩
    (try omega)
  rcases z1q (z1n hN) with ⟨w',hcomp⟩
  have hpow_j := zP2 j
  rcases z1z hcomp (by omega) with ⟨e,f,wf,he,hf,hsum,hle,hlt⟩
  rcases z1p hf with ⟨wf',hf'⟩
  have he_pos : 0 < e := by
    cases e with
    | zero =>
      simp only [Nat.pow_zero,Nat.add_zero] at hle hlt hsum
      (try omega)
    | succ e => omega
  have heq_c : 1 + (2 ^ (1 + j) - 1 - c) = 2 ^ (1 + j) - c := by omega
  rw [heq_c] at hf'
  have hpow_e : 2 ^ e = 2 ^ (e - 1) + 2 ^ (e - 1) := by
    cases e with
    | zero => omega
    | succ e =>
      simp only [Nat.add_sub_cancel]
      rw [Nat.add_comm e 1,zP2]
  have hpow_e1 := zP2 e
  refine ⟨e,f,wf',he_pos,by omega,by omega,by omega,hf',by omega⟩
lemma z1B {j c z : Nat} {w : zF} (hN : Num j c z w) :
    ∃ wf,Num (1 + j) (2 ^ (1 + j) - 1 - z * 2) (2 ^ (1 + j) - 1 - c) wf := by
  rcases z1q (z1n hN) with ⟨w',h⟩
  exact z1p h
lemma z1C : z0N 0 0 default default := by
  unfold z0N
  have h := z0M 0 default
  simpa [list_nat_repeat,z00] using! h
lemma z1D {d k q : Nat} {r : zB} (hR : RC k q r) (hd : k <= d) :
    ∃ a w k' q' t,
      Num d a q w /\ RC k' q' t /\ ((k = 0 /\ k' = 0) \/ k' < k) /\
      z0N q k t r /\
      RC (1 + d) (2 ^ (1 + d) - 1 - a) (w +> ([1,1,0] +> ((T ^ k) +> ([0] +> t)))) /\
      z0N 1 1 (w +> ([1,1,0] +> ((T ^ k) +> ([0] +> t)))) ([1,1,0] +> ((T ^ (1 + d)) +> ([0] +> r))) := by
  rcases z12 hR with ⟨k',q',t,hT,hk,hN⟩
  have h_bnd := z0X hR
  have h_pow := z10 hd
  have hq : q < 2 ^ d := by omega
  rcases z0J d q hq with ⟨a,w,hw⟩
  exact ⟨a,w,k',q',t,hw,hT,hk,hN,z0Z hw hR hT hk hd,z0V hw hN⟩
lemma z1E {d a q k k' q' : Nat} {w : zF} {r t : zB}
    (hN : Num d a q w) (hR : RC k q r) (hT : RC k' q' t)
    (hk : (k = 0 /\ k' = 0) \/ k' < k) (hd : k <= d) :
    ∃ q2 u,RC k q2 u /\
      z0N (2 ^ (1 + d) - 1 - a) (1 + d) u (w +> ([1,1,0] +> ((T ^ k) +> ([0] +> t)))) := by
  cases k with
  | zero =>
    have hk'0 : k' = 0 := by omega
    subst hk'0
    rcases z0Y hT with ⟨rfl,rfl⟩
    refine ⟨0,default,RC.base 0,?_⟩
    have h_z : ([1,1,0] : zF) +> ((T ^ 0) +> ([0] +> default)) = Z +> default := rfl
    rw [h_z]
    have hstep := z0R hN (z0P z1C)
    have hbnd := z0H hN
    have heq1 : (1 + 0 * 2 + 1) * 2 ^ d - 1 - a = 2 ^ (1 + d) - 1 - a := by rw [zP2]; omega
    have heq2 : d + (1 + 0) = 1 + d := by omega
    rwa [heq1,heq2] at hstep
  | succ k =>
    have hk' : k' <= k := by omega
    rcases z1D hT hk' with ⟨a2,w2,k2,q2,t2,hN2,hT2,hk2,hchild,hU,hM⟩
    have heq_k : 1 + k = k + 1 := by omega
    rw [heq_k] at hU hM
    refine ⟨2 ^ (k + 1) - 1 - a2,w2 +> ([1,1,0] +> ((T ^ k') +> ([0] +> t2))),hU,?_⟩
    have hstep := z0R hN hM
    have hbnd := z0H hN
    have heq1 : (1 + 1) * 2 ^ d - 1 - a = 2 ^ (1 + d) - 1 - a := by rw [zP2]; omega
    have heq2 : d + 1 = 1 + d := by omega
    rwa [heq1,heq2] at hstep
lemma z1F {d a b : Nat} {w : zF} (hN : Num (1 + d) a b w) (hb : b < 2 ^ d) :
    ∃ n,2 ^ (2 + d) - 1 - a = 1 + n * 2 := by
  generalize hd : 1 + d = d0 at hN
  cases hN with
  | nil => omega
  | @Z d1 a0 b0 w0 h0 =>
    have hd1 : d1 = d := by omega
    subst d1
    have hbnd := z0H h0
    have hpow1 := zP2 d
    have hpow2 := z0F d
    exact ⟨2 ^ (1 + d) - 1 - a0,by omega⟩
  | @T d1 a0 b0 w0 h0 =>
    have hd1 : d1 = d := by omega
    subst d1
    (try omega)
lemma z1G {j a b p n k : Nat} {w : zF} {t r r' : zB}
    (hN : Num j a b w)
    (hP : Side ([Call.hb] ^ p) r r')
    (hR : Side ([Call.hc] ^ b ++ [Call.hb] ^ (1 + n) ++ [Call.hc]) r' ((T ^ k) +> ([0] +> t))) :
    z0N ((p + 1 + n) * 2 ^ j - a) (j + k) t ((T ^ j) +> r) := by
  refine z1w hN ?_
  have h1 := z0a hP hR
  simpa only [List.append_assoc] using! h1
lemma z1H (a b : Nat) : 2 ^ (a + b) = 2 ^ a * 2 ^ b := Nat.pow_add 2 a b
lemma z1I {j s b z e v p k : Nat} {wb we : zF} {t r r0 u : zB}
    (hZ : Num (1 + j) b z wb) (hV : Num s e v we) (hz : 0 < z)
    (hR : z0N (2 ^ (2 + j + s) - 1 - e - 2 ^ s * b) k t r)
    (hM : z0N 1 1 u ([1,1,0] +> ((T ^ k) +> ([0] +> t))))
    (hP : Side ([Call.hb] ^ p) r0 ([1,0,1,1,1,0] +> ((T ^ s) +> ([0] +> r)))) :
    ∃ f Q,0 < f /\ f <= 1 + j /\ 2 ^ (f - 1) <= z /\ z < 2 ^ f /\
      z0N Q (3 + j + s) u ((T ^ (1 + j)) +> r0) /\
      Q + 3 * 2 ^ f = (p + 2 ^ (1 + s) + 2 + v * 2) * 2 ^ (1 + j) + z * 2 + 1 := by
  have hVb := z0H hV
  rcases z1q hV with ⟨wc,hC⟩
  generalize hj : 1 + j = j0 at hZ
  cases hZ with
  | nil => omega
  | @Z j1 a b0 w0 hZ0 =>
    have hj1 : j1 = j := by omega
    subst j1
    have hZb := z0H hZ0
    rcases z1A hZ0 hz with ⟨f,b',wf,hf,hfj,hfz1,hfz2,hF,hE⟩
    rcases z1p (z1n hC) with ⟨wr,hrem⟩
    have hR' : z0N (2 ^ s + (2 ^ (1 + j) - a - 1) * 2 ^ (1 + s) + (2 ^ s - 1 - e)) k t r := by
      have heq : 2 ^ s + (2 ^ (1 + j) - a - 1) * 2 ^ (1 + s) + (2 ^ s - 1 - e) =
          2 ^ (2 + j + s) - 1 - e - 2 ^ s * (a * 2) := by
        have h1 : (2 ^ (1 + j) - a - 1) * 2 ^ (1 + s) + 2 ^ s * (a * 2) + 2 ^ s + 2 ^ s = 2 ^ (2 + j + s) := by
          have h2 : 2 + j + s = (1 + j) + (1 + s) := by omega
          rw [h2,z1H (1 + j) (1 + s),zP2 s]
          have h3 : 2 ^ (1 + j) - a - 1 + a + 1 = 2 ^ (1 + j) := by have := zP2 j; omega
          nlinarith
        (try omega)
      rwa [heq]
    have hD := z1f hrem hR' hM
    have hD' : Side ([Call.hc] ^ (2 ^ (1 + j) - a) ++ [Call.hb] ^ (1 + (2 ^ (1 + s) + 1 + v * 2)) ++ [Call.hc])
        ([1,0,1,1,1,0] +> ((T ^ s) +> ([0] +> r))) ((T ^ (2 + s)) +> ([0] +> u)) := by
      have heq1 : 1 + (2 ^ (1 + j) - a - 1) = 2 ^ (1 + j) - a := by rw [zP2]; omega
      have heq2 : 2 ^ (2 + s) - (2 ^ s - 1 - v) * 2 = 1 + (2 ^ (1 + s) + 1 + v * 2) := by
        have : 2 + s = 1 + (1 + s) := by omega
        rw [this,zP2 (1 + s),zP2 s]; omega
      rw [<- List.append_assoc] at hD
      rwa [heq1,heq2] at hD
    have hH := z1G hF hP hD'
    have hFb := z0H hF
    refine ⟨f,(p + 1 + (2 ^ (1 + s) + 1 + v * 2)) * 2 ^ (1 + j) - b',
      hf,by omega,hfz1,hfz2,?_,?_⟩
    · have heq : (1 + j) + (2 + s) = 3 + j + s := by omega
      rwa [heq] at hH
    · have h1 : (p + 1 + (2 ^ (1 + s) + 1 + v * 2)) * 2 ^ (1 + j) =
          (p + 2 ^ (1 + s) + 1 + v * 2) * 2 ^ (1 + j) + 2 ^ (1 + j) := by nlinarith
      have h2 : (p + 2 ^ (1 + s) + 2 + v * 2) * 2 ^ (1 + j) =
          (p + 2 ^ (1 + s) + 1 + v * 2) * 2 ^ (1 + j) + 2 ^ (1 + j) := by nlinarith
      (try omega)
  | @T j1 a b0 w0 hZ0 =>
    have hj1 : j1 = j := by omega
    subst j1
    have hZb := z0H hZ0
    rcases z1B hZ0 with ⟨wf,hF⟩
    rcases z1p (z1o hC) with ⟨wr,hrem⟩
    have hR' : z0N (2 ^ s + (2 ^ (1 + j) - a - 2) * 2 ^ (1 + s) + (2 ^ s + (2 ^ s - 1 - e))) k t r := by
      have heq : 2 ^ s + (2 ^ (1 + j) - a - 2) * 2 ^ (1 + s) + (2 ^ s + (2 ^ s - 1 - e)) =
          2 ^ (2 + j + s) - 1 - e - 2 ^ s * (1 + a * 2) := by
        have h1 : (2 ^ (1 + j) - a - 2) * 2 ^ (1 + s) + 2 ^ s * (1 + a * 2) + 2 ^ s + 2 ^ s + 2 ^ s = 2 ^ (2 + j + s) := by
          have h2 : 2 + j + s = (1 + j) + (1 + s) := by omega
          rw [h2,z1H (1 + j) (1 + s),zP2 s]
          have h3 : 2 ^ (1 + j) - a - 2 + a + 2 = 2 ^ (1 + j) := by have := zP2 j; omega
          nlinarith
        (try omega)
      rwa [heq]
    have hD := z1f hrem hR' hM
    have hD' : Side ([Call.hc] ^ (2 ^ (1 + j) - 1 - a) ++ [Call.hb] ^ (1 + (2 ^ (1 + s) + v * 2)) ++ [Call.hc])
        ([1,0,1,1,1,0] +> ((T ^ s) +> ([0] +> r))) ((T ^ (2 + s)) +> ([0] +> u)) := by
      have heq1 : 1 + (2 ^ (1 + j) - a - 2) = 2 ^ (1 + j) - 1 - a := by rw [zP2]; omega
      have heq2 : 2 ^ (2 + s) - (1 + (2 ^ s - 1 - v) * 2) = 1 + (2 ^ (1 + s) + v * 2) := by
        have : 2 + s = 1 + (1 + s) := by omega
        rw [this,zP2 (1 + s),zP2 s]; omega
      rw [<- List.append_assoc] at hD
      rwa [heq1,heq2] at hD
    have hH := z1G hF hP hD'
    have hFb := z0H hF
    refine ⟨1 + j,(p + 1 + (2 ^ (1 + s) + v * 2)) * 2 ^ (1 + j) - (2 ^ (1 + j) - 1 - b0 * 2),
      by omega,by omega,?_,?_,?_,?_⟩
    · have heq : 1 + j - 1 = j := by omega
      rw [heq]; omega
    · rw [zP2 j]; omega
    · have heq : (1 + j) + (2 + s) = 3 + j + s := by omega
      rwa [heq] at hH
    · have h1 : (p + 2 ^ (1 + s) + 2 + v * 2) * 2 ^ (1 + j) =
          (p + 1 + (2 ^ (1 + s) + v * 2)) * 2 ^ (1 + j) + 2 ^ (1 + j) := by nlinarith
      have h2 : (p + 1 + (2 ^ (1 + s) + v * 2)) * 2 ^ (1 + j) =
          (p + (2 ^ (1 + s) + v * 2)) * 2 ^ (1 + j) + 2 ^ (1 + j) := by nlinarith
      have h3 := zP2 j
      (try omega)
lemma z1J {d a b : Nat} {w : zF} (h : Num d a b w) :
    ∀ {r v : zB},
      z0N 1 1 v r -> Side [Call.hb] ([1,0] +> r) ([1,0,1,1,1,0,0] +> v) ->
      ∃ j s p r0,d = j + s /\
        ([1,0] : zF) +> (w +> r) = (T ^ j) +> r0 /\
        p * 2 ^ j + a + 1 = 2 ^ (1 + d) /\
        (j < d -> a + 2 ^ j < 2 ^ d) /\
        (a + 1 < 2 ^ d -> j < d) /\
        (j = 0 -> ∃ m,a = m * 2) /\
        Side ([Call.hb] ^ p) r0 ([1,0,1,1,1,0] +> ((T ^ s) +> ([0] +> v))) := by
  induction h with
  | nil =>
    intro r v hM hB
    refine ⟨0,0,1,[1,0] +> r,rfl,rfl,by omega,by omega,by omega,fun _ => ⟨0,rfl⟩,?_⟩
    simpa only [z06,z07,List.append_nil,append_cons,append_nil] using! hB
  | @Z d a b w hNum _ =>
    intro r v hM hB
    have hbnd := z0H hNum
    have hpow1 := zP2 d
    have hpow2 := zP2 (1 + d)
    refine ⟨0,1 + d,1 + ((1 + 1) * 2 ^ d - 1 - a) * 2,[1,0,1,1,0,0] +> (w +> r),
      by omega,rfl,by omega,by omega,by omega,fun _ => ⟨a,rfl⟩,?_⟩
    have hP := zSc (z18 ((1 + 1) * 2 ^ d - 1 - a)) (z0O 1 (z0R hNum hM))
    have heq : d + 1 = 1 + d := by omega
    rwa [heq] at hP
  | @T d a b w hNum ih =>
    intro r v hM hB
    rcases ih hM hB with ⟨j,s,p,r0,hd,hw,hp,ha,hj,hpar,hP⟩
    have hpow_d := zP2 d
    have hpow_1d := zP2 (1 + d)
    have hpow_j := zP2 j
    refine ⟨1 + j,s,p,r0,by omega,?_,?_,?_,?_,by omega,hP⟩
    · calc ([1,0] : zF) +> ((T ++ w) +> r)
        _ = T +> ([1,0] +> (w +> r)) := by simp only [T,append_assoc,append_cons,append_nil]
        _ = (T ^ (1 + j)) +> r0 := by rw [hw,zLp',append_assoc]
    · nlinarith
    · intro hj'
      have h1 := ha (by omega)
      (try omega)
    · omega
lemma z1K {d k q : Nat} {r : zB} (hR : RC k q r) (hd : k <= d) :
    ∃ a w v q2 t qu u,
      Num d a q w /\ RC (1 + d) (2 ^ (1 + d) - 1 - a) v /\
      z0N 1 1 v ([1,1,0] +> ((T ^ (1 + d)) +> ([0] +> r))) /\
      Side [Call.hb] ([1,0] +> ([1,1,0] +> ((T ^ (1 + d)) +> ([0] +> r)))) ([1,0,1,1,1,0,0] +> v) /\
      RC k q2 t /\ z0N (2 ^ (1 + d) - 1 - a) (1 + d) t v /\
      RC (1 + d) qu u /\ z0N 1 1 u ([1,1,0] +> ((T ^ (1 + d)) +> ([0] +> t))) /\
      (k < d -> ∃ m,qu = 1 + m * 2) := by
  rcases z1D hR hd with ⟨a,w,k',q',t',hN,hT,hk,hNR,hV,hM⟩
  rcases z1E hN hR hT hk hd with ⟨q2,t,hT2,hNV⟩
  rcases z1D hT2 hd with ⟨a2,w2,k2,q3,t2,hN2,hT3,hk2,hNT,hU,hM2⟩
  refine ⟨a,w,_,q2,t,_,_,hN,hV,hM,z1u hN hNR,hT2,hNV,hU,hM2,?_⟩
  intro hkd
  cases d with
  | zero => omega
  | succ d =>
    have heq_d : d + 1 = 1 + d := by omega
    rw [heq_d] at hN2
    have h_bnd := z0X hT2
    have h_pow := z10 (a := k) (b := d) (by omega)
    have h_mark := z1F hN2 (by omega)
    have heq_2d : 2 + d = 1 + (d + 1) := by omega
    rwa [<- heq_2d]
lemma z1L (n : Nat) :
    ∀ {d a b : Nat} {w : zF},Num (n + d) a b w ->
      ∃ a1 b1 w1 a2 b2 w2,Num n a1 b1 w1 /\ Num d a2 b2 w2 /\
        a = a1 + 2 ^ n * a2 /\ b = b1 * 2 ^ d + b2 /\ w = w1 ++ w2 := by
  induction n with
  | zero =>
    intro d a b w h
    rw [Nat.zero_add] at h
    exact ⟨0,0,[],a,b,w,Num.nil,h,by omega,by omega,rfl⟩
  | succ n ih =>
    intro d a b w h
    have heq : n + 1 + d = 1 + (n + d) := by omega
    rw [heq] at h
    generalize hnd : 1 + (n + d) = nd at h
    cases h with
    | nil => omega
    | @Z nd0 a0 b0 w0 h0 =>
      have hnd0 : nd0 = n + d := by omega
      subst nd0
      rcases ih h0 with ⟨a1,b1,w1,a2,b2,w2,h1,h2,ha,hb,hw⟩
      have hZ := Num.Z h1
      rw [Nat.add_comm 1 n] at hZ
      have hpow := zP2 n
      rw [Nat.add_comm 1 n] at hpow
      refine ⟨a1 * 2,b1,Z ++ w1,a2,b2,w2,hZ,h2,by nlinarith,hb,by rw [hw,List.append_assoc]⟩
    | @T nd0 a0 b0 w0 h0 =>
      have hnd0 : nd0 = n + d := by omega
      subst nd0
      rcases ih h0 with ⟨a1,b1,w1,a2,b2,w2,h1,h2,ha,hb,hw⟩
      have hT := Num.T h1
      rw [Nat.add_comm 1 n] at hT
      have hpow := zP2 n
      rw [Nat.add_comm 1 n] at hpow
      have hpow_nd := z1H n d
      refine ⟨1 + a1 * 2,2 ^ n + b1,T ++ w1,a2,b2,w2,hT,h2,by nlinarith,by nlinarith,by rw [hw,List.append_assoc]⟩
def z1M (d a q Q : Nat) : Prop :=
  ∃ j f z v,
    j <= d /\ 0 < f /\ f <= j /\ 2 ^ (f - 1) <= z /\ z < 2 ^ f /\
    q = v * 2 ^ j + z /\ Q + a + 3 * 2 ^ f = 2 ^ (2 + d) + q * 2 + 2 ^ (1 + j) /\
    (j < d -> a + 2 ^ j < 2 ^ d) /\ (a + 1 < 2 ^ d -> j < d)
lemma z1N {d a b k q : Nat} {w : zF} {r : zB}
    (hN : Num d (1 + a * 2) b w) (hR : RC k (1 + q * 2) r) (hd : k <= d) :
    ∃ Q qu u,RC (1 + d) qu u /\
      z0N Q (2 + d) u ([1,0] +> (w +> ([1,1,0] +> ((T ^ (1 + d)) +> ([0] +> r))))) /\
      z1M d (1 + a * 2) (1 + q * 2) Q /\ (k < d -> ∃ m,qu = 1 + m * 2) := by
  rcases z1K hR hd with ⟨e,we,v,q2,t,qu,u,hE,hV,hM,hB,hT,hNV,hU,hM2,hpar⟩
  rcases z1J hN hM hB with ⟨j,s,p,r0,hds,hword,hp,ha,hj,hpar',hP⟩
  cases j with
  | zero =>
    rcases hpar' rfl with ⟨m,hm⟩
    (try omega)
  | succ j =>
    have heq_j : j + 1 = 1 + j := by omega
    rw [heq_j] at hds hword hp ha hj
    have hE' : Num (s + (1 + j)) e (1 + q * 2) we := by
      have heq : s + (1 + j) = d := by omega
      rwa [heq]
    rcases z1L s hE' with ⟨e0,v0,w0,b0,z,wz,hE0,hZ,he,hq,hw⟩
    have hz : 0 < z := by
      have hpow : v0 * 2 ^ (1 + j) = (v0 * 2 ^ j) * 2 := by
        rw [zP2 j,Nat.mul_add]; omega
      (try omega)
    have hNV' : z0N (2 ^ (2 + j + s) - 1 - e0 - 2 ^ s * b0) (1 + d) t v := by
      have heq : 2 ^ (2 + j + s) - 1 - e0 - 2 ^ s * b0 = 2 ^ (1 + d) - 1 - e := by
        have h1 : 2 + j + s = 1 + d := by omega
        rw [h1,he]; omega
      rwa [heq]
    rcases z1I hZ hE0 hz hNV' hM2 hP with ⟨f,Q,hf,hfj,hfz1,hfz2,hnormal,hQ⟩
    refine ⟨Q,qu,u,hU,?_,?_,hpar⟩
    · rw [<- hword] at hnormal
      have heq : 3 + j + s = 2 + d := by omega
      rwa [heq] at hnormal
    · refine ⟨1 + j,f,z,v0,by omega,hf,hfj,hfz1,hfz2,hq,?_,ha,hj⟩
      have h1 : 2 + d = (2 + s) + (1 + j) := by omega
      have h2 : 1 + d = (1 + s) + (1 + j) := by omega
      rw [h1,z1H (2 + s) (1 + j)]
      rw [h2,z1H (1 + s) (1 + j)] at hp
      have h3 : 2 ^ (2 + s) = 2 * 2 ^ (1 + s) := by
        have : 2 + s = 1 + (1 + s) := by omega
        rw [this,zP2 (1 + s)]; omega
      have h4 := zP2 (1 + j)
      rw [h3,h4]
      nlinarith
lemma z1O {s a b k q : Nat} {w : zF} {r : zB}
    (hN : Num s a b w) (hR : RC k q r) (hk : k <= s) :
    ∃ qu u,RC (1 + s) qu u /\
      z0N (2 ^ (3 + s) - a * 2 + q * 4) (3 + s) u
        ([1,0] +> (Z +> (w +> ([1,1,0] +> ((T ^ (1 + s)) +> ([0] +> r)))))) /\
      (k < s -> ∃ m,qu = 1 + m * 2) := by
  rcases z1K hR hk with ⟨e,we,v,q2,t,qu,u,hE,hV,hM,hB,hT,hNV,hU,hM2,hpar⟩
  exact ⟨qu,u,hU,z1s hN hE hM hNV hM2,hpar⟩
lemma z1P {d a q Q : Nat} (ha : a < 2 ^ d) (hq : q < 2 ^ d) (hC : z1M d a q Q) :
    3 * 2 ^ d < Q + 1 /\ Q + 1 < 6 * 2 ^ d := by
  rcases hC with ⟨j,f,z,v,hjd,hf,hfj,hz1,hz2,hqv,hQ,ha',hj'⟩
  have hpj : 2 ^ f <= 2 ^ j := z10 hfj
  have hpz : 2 ^ f <= z * 2 := by
    cases f with
    | zero => omega
    | succ f =>
      simp only [Nat.add_sub_cancel] at hz1
      rw [Nat.add_comm f 1,zP2]; omega
  have hdl : d = j + (d - j) := by omega
  have hpow_d : 2 ^ d = 2 ^ j * 2 ^ (d - j) := by rw [<- z1H,<- hdl]
  have hv_lt : v < 2 ^ (d - j) := by nlinarith
  have hcap : q + 2 ^ j <= 2 ^ d + z := by nlinarith
  have hpow2 := z0F d
  have hpow_j := zP2 j
  (try omega)
lemma z1Q {d a q Q : Nat} (hC : z1M d (1 + a * 2) q Q) :
    ∃ m,Q = 1 + m * 2 := by
  rcases hC with ⟨j,f,z,v,hjd,hf,hfj,hz1,hz2,hqv,hQ,ha',hj'⟩
  cases f with
  | zero => omega
  | succ f =>
    have hpow_f : 2 ^ (f + 1) = 2 ^ f * 2 := by rw [Nat.pow_succ]
    have hpow_d := z0F d
    have hpow_j := zP2 j
    exact ⟨Q / 2,by omega⟩
lemma z1R {d a q Q : Nat} (hd : 0 < d) (ha : a + 1 < 2 ^ d) (hq : 2 ^ (d - 1) <= q)
    (hC : z1M d a q Q) : 2 ^ (2 + d) < Q := by
  rcases hC with ⟨j,f,z,v,hjd,hf,hfj,hz1,hz2,hqv,hQ,ha',hj'⟩
  have ha_lt := ha' (hj' ha)
  have hpj : 2 ^ f <= 2 ^ j := z10 hfj
  have hqd : 2 ^ d <= q * 2 := by
    cases d with
    | zero => omega
    | succ d =>
      simp only [Nat.add_sub_cancel] at hq
      rw [Nat.add_comm d 1,zP2]; omega
  have hpow_j := zP2 j
  (try omega)
lemma z1S {d a m : Nat} {w : zF} (hd : 0 < d) (h : Num d a (m * 2) w) :
    a + 1 < 2 ^ d := by
  rcases z1p h with ⟨w',h'⟩
  generalize hm : m * 2 = m2 at h'
  cases h' with
  | nil => omega
  | @Z d0 a0 b0 w0 h0 =>
    have hbnd := z0H h0
    rw [zP2]
    (try omega)
  | @T d0 a0 b0 w0 h0 =>
    (try omega)
inductive Inv : Cfg (Fin 2) (Fin 6) -> Prop where
  | E {s a b k q : Nat} {w : zF} {r : zB} :
      Num s a b w -> RC k q r -> k <= s ->
      Inv (z13 (Z ++ w) (1 + s) r)
  | O {s a b k q : Nat} {w : zF} {r : zB} :
      Num s a b w -> RC k (1 + q * 2) r -> k <= 1 + s ->
      (k = 1 + s -> a + 1 < 2 ^ s) ->
      Inv (z13 (T ++ w) (2 + s) r)
lemma z1T {d Q k q : Nat} {r t : zB}
    (hd : 0 < d) (hN : z0N Q (2 + d) t r) (hR : RC k q t) (hk : k <= 1 + d)
    (hQ1 : 3 * 2 ^ d < Q + 1) (hQ2 : Q + 1 < 6 * 2 ^ d)
    (hlow : Q + 1 < 2 ^ (2 + d) -> (∃ m,q = 1 + m * 2) /\ (k = 1 + d -> ∃ m,Q = 1 + m * 2)) :
    ∃ c,((zCR lh Q_B ([0] +> r)) [target_tm]⊢⁺ c) /\ Inv c := by
  have hpow1 := zP2 d
  have hpow2 := z0F d
  have h_2d : 2 + d = 1 + (1 + d) := by omega
  by_cases hH : 2 ^ (2 + d) <= Q + 1
  · have hb : Q + 1 - 2 ^ (2 + d) < 2 ^ (1 + d) := by omega
    rcases z0J (1 + d) (Q + 1 - 2 ^ (2 + d)) hb with ⟨a,w,hW⟩
    refine ⟨z13 (Z ++ w) (2 + d) t,?_,?_⟩
    · have hZ : Num (2 + d + 0) (a * 2) (Q + 1 - 2 ^ (2 + d)) (Z ++ w) := by
        have hZ0 := Num.Z hW
        have heq_d : 1 + (1 + d) = 2 + d + 0 := by omega
        rwa [heq_d] at hZ0
      have h_ret := z17 (2 + d) (i := 0) hZ (q := Q) (by rw [Nat.add_zero]; omega) hN
      simpa only [z06,append_nil] using! h_ret
    · have h_inv := Inv.E hW hR hk
      rwa [<- h_2d] at h_inv
  · rcases hlow (by omega) with ⟨⟨m,rfl⟩,hodd⟩
    have hb : Q + 1 - 3 * 2 ^ d < 2 ^ d := by omega
    rcases z0J d (Q + 1 - 3 * 2 ^ d) hb with ⟨a,w,hW⟩
    refine ⟨z13 (T ++ w) (2 + d) t,?_,?_⟩
    · have hT : Num (1 + d + 0) (1 + a * 2) (2 ^ d + (Q + 1 - 3 * 2 ^ d)) (T ++ w) := by
        have hT0 := Num.T hW
        have heq_d : 1 + d = 1 + d + 0 := by omega
        rwa [heq_d] at hT0
      have h_ret := z17 (1 + d) (i := 0) hT (q := Q) (by rw [Nat.add_zero]; omega) hN
      simpa only [z06,append_nil] using! h_ret
    · refine Inv.O hW hR hk (fun heq => ?_)
      rcases hodd heq with ⟨v,hv⟩
      have h_even : Q + 1 - 3 * 2 ^ d = (Q + 1 - 3 * 2 ^ d) / 2 * 2 := by
        cases d with
        | zero => omega
        | succ d =>
          have : 2 ^ (d + 1) = 2 ^ d * 2 := Nat.pow_succ 2 d
          (try omega)
      rw [h_even] at hW
      exact z1S hd hW
lemma z1U {d k q : Nat} {r : zB} (h : RC k q r) (hd : k <= d) :
    q < 2 ^ d := by
  have hbnd := z0X h
  have hpow := z10 hd
  (try omega)
lemma z1V (c : Cfg (Fin 2) (Fin 6)) (h : Inv c) :
    ∃ c',(c [target_tm]⊢⁺ c') /\ Inv c' := by
  cases h with
  | @E s a b k q w r hN hR hk =>
    rcases z1O hN hR hk with ⟨qu,u,hU,hM,hpar⟩
    have hNb := z0H hN
    have hRb := z1U hR hk
    have hpow1 := zP2 s
    have hpow2 := z0F s
    have hpow3 := z0G s
    have hpow_21s := z0F (1 + s)
    have hM' : z0N (2 ^ (3 + s) - a * 2 + q * 4) (2 + (1 + s)) u
        ([1,0] +> (Z +> (w +> ([1,1,0] +> ((T ^ (1 + s)) +> ([0] +> r)))))) := by
      have h_3s : 3 + s = 2 + (1 + s) := by omega
      exact Eq.mp (by rw [h_3s]) hM
    have h_next := z1T (d := 1 + s) (by omega) hM' hU (by omega)
      (by omega) (by omega) ?_
    · rcases h_next with ⟨c',hc',hinv'⟩
      refine ⟨c',?_,hinv'⟩
      unfold z13
      simpa only [append_assoc,append_cons,append_nil] using! hc'
    · intro hlow
      have hks : k < s := by
        by_contra hge
        have hkeq : k = s := by omega
        subst k
        have hbnd := z0X hR
        cases s with
        | zero => omega
        | succ s =>
          have hq_ge := hbnd.2 (by omega)
          simp only [Nat.add_sub_cancel] at hq_ge
          have : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [Nat.pow_succ]; omega
          (try omega)
      exact ⟨hpar hks,by omega⟩
  | @O s a b k q w r hN hR hk ha =>
    have hW := Num.T hN
    rcases z1N hW hR hk with ⟨Q,qu,u,hU,hM,hC,hpar⟩
    have hWb := z0H hW
    have hRb := z1U hR hk
    rcases z1P hWb.1 hRb hC with ⟨hQ1,hQ2⟩
    have h_next := z1T (d := 1 + s) (by omega) hM hU (by omega)
      hQ1 hQ2 ?_
    · rcases h_next with ⟨c',hc',hinv'⟩
      refine ⟨c',?_,hinv'⟩
      have h_2s : 2 + s = 1 + (1 + s) := by omega
      unfold z13
      rw [h_2s]
      simpa only [append_assoc,append_cons,append_nil] using! hc'
    · intro hlow
      have hks : k < 1 + s := by
        by_contra hge
        have hkeq : k = 1 + s := by omega
        subst k
        have ha_lt := ha rfl
        have hbnd := z0X hR
        have hpow_s := zP2 s
        have h_large := z1R (d := 1 + s) (by omega) (by omega) (hbnd.2 (by omega)) hC
        (try omega)
      exact ⟨hpar hks,fun _ => z1Q hC⟩
lemma z1W :
    (init []) [target_tm]⊢⁺ (((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (default : zB)) {{0}}> ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (default : zB))) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{0}}> default) := rfl
  rw [h_init]
  execute
lemma z1X :
    (((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (default : zB)) {{0}}> ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (default : zB))) [target_tm]⊢⁺ (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (default : zB)) {{4}}> ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (default : zB))) := by
  execute
lemma z1Y :
    (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (default : zB)) {{4}}> ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (default : zB))) [target_tm]⊢⁺ (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (default : zB)) {{1}}> ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (default : zB))) := by
  execute
lemma z1Z :
    (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (default : zB)) {{1}}> ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (default : zB))) [target_tm]⊢⁺ z13 (Z ++ T) 2 default := by
  unfold z13 zCR lh Z T
  simp only [zLp,z06,List.append_assoc,List.cons_append,List.nil_append,append_cons,append_nil]
  execute
lemma z20 :
    (init []) [target_tm]⊢⁺ z13 (Z ++ T) 2 default :=
  zPt z1W (zPt z1X (zPt z1Y z1Z))
lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
lemma z21 (m : Nat) :
    ∃ N ≥ m,∃ c,multiStep target_tm (init []) N = some c /\ Inv c := by
  induction m with
  | zero =>
    rcases z20 with ⟨k,_,hk⟩
    have hT : Num 1 1 1 T := Num.T Num.nil
    have hRC : RC 0 0 default := RC.base 0
    have h_inv := Inv.E hT hRC (by omega)
    exact ⟨k,Nat.zero_le k,_,hk,h_inv⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,c,h_ms,h_inv⟩
    rcases z1V c h_inv with ⟨c',⟨k,hk_pos,h_step_k⟩,h_inv'⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,c',zMt target_tm _ _ _ N k h_ms h_step_k,h_inv'⟩

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
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases z21 (n + 1) with ⟨N,hN,c',h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

end BusyBeaver.M_1RB1LD_0RC0RB_0LD1RE_0LA1LC_0RB0RF_1LCHHH
