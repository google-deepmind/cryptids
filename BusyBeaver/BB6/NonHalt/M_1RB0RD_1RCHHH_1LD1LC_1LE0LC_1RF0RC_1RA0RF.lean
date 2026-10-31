/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RD_1RC---_1LD1LC_1LE0LC_1RF0RC_1RA0RF` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RD_1RC---_1LD1LC_1LE0LC_1RF0RC_1RA0RF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RD_1RCHHH_1LD1LC_1LE0LC_1RF0RC_1RA0RF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RD_1RC---_1LD1LC_1LE0LC_1RF0RC_1RA0RF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => none
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 5, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open Counter

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
variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000000
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
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  z02 (z01 tm c_1 c_2 h₁) h₂
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [Turing.ListBlank.head_cons,zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,z00,zDh,zDt])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))
abbrev t : zF := [1,1,0,0]
abbrev d0 : zF := [0,0]
abbrev d1 : zF := [1,0]
abbrev one : zF := [1]
abbrev lh : zB := default
abbrev w_word : zF := t ++ t ++ one
abbrev w_pre : zF := w_word
@[simp] lemma zDd : d0 +> (default : zB) = default := by
  simp [d0]
inductive Call where
  | ch
  | cj
  | cp
  | ca
def zCs : Call -> Fin 6
  | .ch => E
  | .cj => D
  | .cp => D
  | .ca => D
def zCw : Call -> zF
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
  | .ca => [1,1,1,0,1,0]
def zCR (l : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (r <{{zCs c}} (l <+ zCw c))
def zCL (l : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> r) {{F}}> l)
def zCf (q : Nat) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  zCL lh ((w_pre ++ (t ^ (2 + q) ++ (d1 ++ one))) +> r)
def z04 (c : Call) (r1 r2 : zB) : Prop :=
  ∀ l,(zCR l c r1) [target_tm]⊢⁺ (zCL l r2)
inductive Side : List Call -> zB -> zB -> Prop where
  | nil (r : zB) : Side [] r r
  | cons {c : Call} {ls : List Call} {r1 r2 r3 : zB} :
      z04 c r1 r2 -> Side ls r2 r3 -> Side (c :: ls) r1 r3
def Seg (ls_in ls_out : List Call) (w1 w2 : zF) : Prop :=
  ∀ r1 r2,Side ls_out r1 r2 -> Side ls_in (w1 +> r1) (w2 +> r2)
@[simp] lemma z05 {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma zLp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] lemma zLp' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] lemma z06 {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l
lemma z07 {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm,zLp,zLp,ih,List.append_assoc]
lemma z08 {ls1 ls2 : List Call} {r1 r2 r3 : zB}
    (h1 : Side ls1 r1 r2) (h2 : Side ls2 r2 r3) : Side (ls1 ++ ls2) r1 r3 := by
  induction h1 with
  | nil _ => exact h2
  | cons hc _ ih => exact Side.cons hc (ih h2)
lemma z09 {ls1 ls2 : List Call} {r1 r3 : zB}
    (h : Side (ls1 ++ ls2) r1 r3) : ∃ r2,Side ls1 r1 r2 /\ Side ls2 r2 r3 := by
  induction ls1 generalizing r1 with
  | nil => exact ⟨r1,Side.nil r1,h⟩
  | cons c ls1 ih =>
    rcases h with _ | ⟨hc,hrest⟩
    rcases ih hrest with ⟨r2,h1,h2⟩
    exact ⟨r2,Side.cons hc h1,h2⟩
lemma z0a (w : zF) : Seg [] [] w w := by
  intro r1 r2 h; cases h; exact Side.nil (w +> r1)
lemma z0b (ls : List Call) : Seg ls ls [] [] := by
  intro r1 r2 h; simpa using! h
lemma zSc {ls1 ls2 : List Call} {w1 w2 : zF} {r1 r2 : zB}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
    Side ls1 (w1 +> r1) (w2 +> r2) :=
  h1 r1 r2 h2
lemma zSg {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : zF}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3 := by
  intro r1 r3 h
  rcases z09 h with ⟨r2,ha,hb⟩
  exact z08 (h1 r1 r2 ha) (h2 r2 r3 hb)
lemma zS0 {ls1 ls2 ls3 : List Call} {u1 u2 v1 v2 : zF}
    (h1 : Seg ls1 ls2 u1 u2) (h2 : Seg ls2 ls3 v1 v2) :
    Seg ls1 ls3 (u1 ++ v1) (u2 ++ v2) := by
  intro r1 r2 h
  rw [append_assoc u1 v1 r1,append_assoc u2 v2 r2]
  exact h1 (v1 +> r1) (v2 +> r2) (h2 r1 r2 h)
lemma zS4 {c : Call} {w1 w2 : zF}
    (h1 : ∀ l r,(zCR l c (w1 +> r)) [target_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)
lemma zS2 {c_in c_out : Call} {w1 w2 mid : zF}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [target_tm]⊢⁺ (zCR (mid +> l) c_out r))
    (h2 : ∀ l r,(zCL (mid +> l) r) [target_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1) (zPt (hc1 (mid +> l)) (h2 l r2))
lemma zS5 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : zF}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [target_tm]⊢⁺ (zCR (mid1 +> l) c1 r))
    (h2 : ∀ l r,(zCL (mid1 +> l) r) [target_tm]⊢⁺ (zCR (mid2 +> l) c2 r))
    (h3 : ∀ l r,(zCL (mid2 +> l) r) [target_tm]⊢⁺ (zCL l (w2 +> r))) :
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
lemma z0c : Seg [.ch] [.ch,.ch] t t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma zH0 : Seg [.ch] [] d0 d1 :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1; simp only [append_cons,append_nil]; execute)
lemma zH4 : Seg [.ch] [.ch] d1 d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
lemma z0d : Seg [.cp] [.ch] t (t ++ [0]) :=
  zS2 (mid := [1,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma z0e : Seg [.ch] [.cj] (t ++ [0]) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0f : Seg [.cj] [.ch] t (t ++ one) :=
  zS2 (mid := [1,1,0,1,1])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma zH2 : Seg [.ch] [.cj,.ch] (t ++ one) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0g : Seg [.cp] [] (d1 ++ d0) (t ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d1 d0 t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma z0h : Seg [.cj] [.cj] (d1 ++ d0) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1 d0; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0i : Seg [.cp] [.cp] (d1 ++ d1) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0j : Seg [.cj] [.cp,.ch] (d1 ++ d1) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0k : Seg [.cj] [] d0 (d0 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma zH1 : Seg [.ch] [] (d0 ++ one) (d1 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma zH3 : Seg [.ch] [.cj] (d1 ++ one) d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
lemma z0l : Seg [.cj] [.cp] d1 d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
lemma z0m : Seg [.ca] [.cj,.ch] w_word (w_word ++ t) :=
  zS5 (mid1 := [1,0,1,1,1,1,0,1,1,1,0,1,0]) (mid2 := [1,0,1,0,1,1,0,1,1,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs w_word t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL w_word t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma z0n (r : zB) :
    (zCL lh r) [target_tm]⊢⁺ (zCR lh .ca r) := by
  unfold zCL zCR lh zCw zCs
  simp only [append_cons,append_nil,z00]
  execute
lemma H_T (n : Nat) : Seg ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t := by
  induction n with
  | zero => exact z0a t
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [zLp,h_eq,z07]
    exact zSg z0c ih
lemma zSa {w2 : zF} (hw : Seg [.ch,.ch] [.ch] w2 w2) (n : Nat) :
    Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) w2 w2 := by
  induction n with
  | zero => exact z0a w2
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq,z07,zLp]
    exact zSg hw ih
lemma z0o : Seg [.ch,.ch] [.ch] d0 d0 :=
  zSg zH0 zH4
lemma z0p : Seg [.ch,.ch] [.ch] d1 d1 :=
  zSg zH4 zH0
lemma z0q (n : Nat) : Seg ([.ch] ^ (n * 2)) ([.ch] ^ n) d0 d0 :=
  zSa z0o n
lemma z0r (n : Nat) : Seg ([.ch] ^ (1 + n * 2)) ([.ch] ^ n) d0 d1 := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg zH0 (zSa z0p n)
lemma z0s (n : Nat) : Seg ([.ch] ^ (n * 2)) ([.ch] ^ n) d1 d1 :=
  zSa z0p n
lemma z0t (n : Nat) : Seg ([.ch] ^ (1 + n * 2)) ([.ch] ^ (1 + n)) d1 d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg zH4 (z0q n)
lemma z0u (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0d z0e) (H_T n)
lemma z0v (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0f zH2) (H_T n)
lemma z0w (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0g zH2) (H_T n)
lemma z0x (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0h (H_T n)
lemma z0y (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0i (H_T n)
lemma z0z (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using! zSg z0j (H_T n)
lemma z0A (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0k (zSg zH1 zH3)
  have h1 := zSg h0 (z0q n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using! h1
lemma z0B (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0l (z0q n)
lemma z0C : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0k zH1
lemma z0D (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0k (zSg zH1 (zSg zH3 zH0))
  have h1 := zSg h0 (z0s n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using! h1
lemma z0E (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1 := zSg z0l zH0
  have h1 := zSg h0 (z0s n)
  simpa only [zLp',List.cons_append,List.nil_append] using! h1
lemma z0F (n : Nat) : Seg ([.ch] ^ n ++ [.cj,.ch]) ([.ch] ^ (1 + n * 2) ++ [.cj,.ch]) t t := by
  have h1 := zSg (H_T n) (z0v 0)
  have heq : 1 + n * 2 = n * 2 + 1 := by omega
  rw [heq,z07]
  simpa only [z06,List.append_assoc,List.cons_append,List.nil_append] using! h1
lemma z0G (n : Nat) : Seg ([.ch] ^ (1 + n * 2)) ([.cj] ++ [.ch] ^ n) (d1 ++ one) d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg zH3 (z0q n)
lemma z0H (n : Nat) : Seg ([.ch] ^ (1 + n * 2) ++ [.cj,.ch]) ([.cj] ++ [.ch] ^ n)
    (d1 ++ one) (d1 ++ one) := by
  simpa only [List.append_nil] using! zSg (z0G n) z0C
lemma z0I (q : Nat) : ∀ n,Seg ([.ch] ^ n ++ [.cj,.ch])
    ([.ch] ^ ((1 + n) * 2 ^ q - 1) ++ [.cj,.ch]) (t ^ q) (t ^ q) := by
  induction q with
  | zero =>
    intro n
    have heq : (1 + n) * 2 ^ 0 - 1 = n := by omega
    rw [heq]; exact z0b _
  | succ q ih =>
    intro n
    have heq : (1 + n) * 2 ^ (q + 1) - 1 = (1 + (1 + n * 2)) * 2 ^ q - 1 := by
      rw [Nat.pow_succ]; ring_nf
    rw [zLp,heq]
    exact zS0 (z0F n) (ih (1 + n * 2))
open WordCalculus Word e_Choice
local notation "zW" => List Word
local notation "zR" => List.replicate
inductive Num : Nat -> zF -> List Call -> Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)
lemma loc_z2t {k : Nat} (hK : 0 < k) : ∃ hs,Num k [] hs := by
  rcases z0U k with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · cases a with
    | zero => omega
    | succ a =>
      have heq : (a + 1) * 2 = 2 + a * 2 := by omega
      rw [heq]; exact ⟨[.cj] ++ [.ch] ^ a,Num.even a⟩
  · exact ⟨[.cp] ++ [.ch] ^ a,Num.odd a⟩
lemma loc_z2u {k : Nat} {hs hs' : List Call} (h1 : Num k [] hs) (h2 : Num k [] hs') :
    hs = hs' := by
  cases h1 with
  | @odd n =>
    generalize hk : 1 + n * 2 = k0 at h2
    cases h2 with
    | @odd m =>
      have hnm : n = m := by omega
      subst hnm; rfl
    | even _ => omega
  | @even n =>
    generalize hk : 2 + n * 2 = k0 at h2
    cases h2 with
    | odd _ => omega
    | @even m =>
      have hnm : n = m := by omega
      subst hnm; rfl
def loc_z2v (k : Nat) (r r' : zB) : Prop :=
  ∀ w hs,Num k w hs -> Side hs (w +> r) r'
lemma loc_z2w {r r' : zB} (h : loc_z2v 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl
lemma loc_z2x {n : Nat} {r r' : zB}
    (hI : loc_z2v (n * 2) r r') : loc_z2v (2 + n * 4) (d0 +> r) (d0 +> r') := by
  intro w hs hN
  generalize hk : 2 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = n * 2 := by omega
    subst hm
    cases n with
    | zero =>
      have hr' := loc_z2w hI
      subst hr'
      rw [<- append_assoc d0 one r]
      exact zSc z0k (Side.nil r)
    | succ n =>
      have heq : (n + 1) * 2 = 2 + n * 2 := by omega
      rw [heq]
      refine zSc (z0A n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        rw [heq]; exact Num.even n
      simpa using! hI [] _ hN2
lemma loc_z2y {n : Nat} {r r' : zB}
    (hI : loc_z2v (n * 2) r r') : loc_z2v (4 + n * 4) (d0 +> r) (d1 +> r') := by
  intro w hs hN
  generalize hk : 4 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = 1 + n * 2 := by omega
    subst hm
    cases n with
    | zero =>
      have hr' := loc_z2w hI
      subst hr'
      rw [<- append_assoc d1 one r]
      exact zSc z0C (Side.nil r)
    | succ n =>
      have heq : 1 + (n + 1) * 2 = 3 + n * 2 := by omega
      rw [heq]
      refine zSc (z0D n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        have heq2 : (n + 1) * 2 = 2 + n * 2 := by omega
        rw [heq2]; exact Num.even n
      simpa using! hI [] _ hN2
lemma loc_z2z {A H : Nat} {da : zW} (hD : zDg A H da) (hZ : A = 0) :
    zTs da default = default := by
  induction hD with
  | nil => rfl
  | @zero A H u _ ih =>
    have hA0 : A = 0 := by omega
    rw [zTs,ih hA0,zDd]
  | one _ => omega
lemma loc_z2A {A H : Nat} {da : zW} (hD : zDg A H da) (hPos : 0 < A) :
    loc_z2v ((A - 1) * 2) default (zTs da default) := by
  induction hD with
  | nil => omega
  | @zero A H u _ ih =>
    have hA_pos : 0 < A := by omega
    have hIH := ih hA_pos
    have hs := loc_z2x hIH
    rw [zDd] at hs
    have heq : (A * 2 - 1) * 2 = 2 + (A - 1) * 4 := by omega
    rw [zTs]
    rwa [heq]
  | @one A H u hDu ih =>
    cases A with
    | zero =>
      have h_side : zTs (Q :: u) default = one +> default := by
        rw [zTs,loc_z2z hDu rfl]
        simp [d1,one]
      rw [h_side]
      intro w hs hN
      have hk0 : (1 + 0 * 2 - 1) * 2 = 0 := rfl
      rw [hk0] at hN
      generalize hk : (0 : Nat) = k0 at hN
      cases hN with
      | zero => exact Side.nil (one +> default)
      | odd _ => omega
      | even _ => omega
    | succ A =>
      have hA_pos : 0 < A + 1 := by omega
      have hIH := ih hA_pos
      have heq_in : (A + 1 - 1) * 2 = A * 2 := by omega
      rw [heq_in] at hIH
      have hs := loc_z2y hIH
      rw [zDd] at hs
      have heq : (1 + (A + 1) * 2 - 1) * 2 = 4 + A * 4 := by omega
      rw [zTs]
      rwa [heq]
lemma zEd {n : Nat} {u : zW} {b : Nat} {v : zW}
    (hI : zEf n u b v) :
    ∀ {A H : Nat},zDg A H v -> Seg ([Call.ch] ^ n) ([Call.ch] ^ b) (zWt u) (zWt v) := by
  induction hI with
  | nil n =>
    intro A H _
    exact z0b _
  | T _ _ =>
    intro A H hD
    exact False.elim (z0X hD)
  | d00 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0q _) (ih hD')
  | d01 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0r _) (ih hD')
  | d10 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0s _) (ih hD')
  | d11 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0t _) (ih hD')
lemma loc_z2B {n : Nat} {hs hs' : List Call}
    (hI : Num (3 + n) [] hs) (hJ : Num (2 + n * 2) [] hs') :
    Seg hs ([Call.ch] ++ hs') t t := by
  generalize hk1 : 3 + n = k1 at hI
  generalize hk2 : 2 + n * 2 = k2 at hJ
  cases hI with
  | @odd m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases m with
      | zero => omega
      | succ m =>
        have h1m : m + 1 = 1 + m := by omega
        have hq : q = m * 2 := by omega
        subst hq
        rw [h1m]
        exact z0u m
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases m with
      | zero => omega
      | succ m =>
        have h1m : m + 1 = 1 + m := by omega
        have hq : q = 1 + m * 2 := by omega
        subst hq
        rw [h1m]
        exact z0v m
lemma loc_z2C {n : Nat} {hs hs' : List Call}
    (hI : Num (1 + n) [] hs) (hJ : Num (n * 2) [] hs') :
    Seg hs hs' (d1 ++ d0) t := by
  generalize hk1 : 1 + n = k1 at hI
  generalize hk2 : n * 2 = k2 at hJ
  cases hI with
  | @odd m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases m with
      | zero => omega
      | succ m =>
        have h1m : m + 1 = 1 + m := by omega
        have hq : q = 1 + m * 2 := by omega
        subst hq
        rw [h1m]
        exact z0w m
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      have hq : q = m * 2 := by omega
      subst hq
      exact z0x m
lemma loc_z2D {n : Nat} {hs hs' : List Call}
    (hI : Num (1 + n) [] hs) (hJ : Num (1 + n * 2) [] hs') :
    Seg hs hs' (d1 ++ d1) t := by
  generalize hk1 : 1 + n = k1 at hI
  generalize hk2 : 1 + n * 2 = k2 at hJ
  cases hI with
  | @odd m =>
    cases hJ with
    | @odd q =>
      have hq : q = m * 2 := by omega
      subst hq
      exact z0y m
    | even _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hq : q = 1 + m * 2 := by omega
      subst hq
      exact z0z m
    | even _ => omega
lemma loc_z2E {n : Nat} {hs hs' : List Call}
    (hI : Num (2 + n * 4) [] hs) (hJ : Num (n * 2) [] hs') :
    Seg hs hs' d0 d0 := by
  generalize hk1 : 2 + n * 4 = k1 at hI
  generalize hk2 : n * 2 = k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases n with
      | zero => omega
      | succ n =>
        have hm : m = 2 + q * 2 := by omega
        subst hm
        exact z0A q
lemma loc_z2F {n : Nat} {hs hs' : List Call}
    (hI : Num (2 + n * 4) [] hs) (hJ : Num (1 + n * 2) [] hs') :
    Seg hs hs' d1 d0 := by
  generalize hk1 : 2 + n * 4 = k1 at hI
  generalize hk2 : 1 + n * 2 = k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hm : m = q * 2 := by omega
      subst hm
      exact z0B q
    | even _ => omega
lemma loc_z2G {n : Nat} {hs hs' : List Call}
    (hI : Num (4 + n * 4) [] hs) (hJ : Num (n * 2) [] hs') :
    Seg hs hs' d0 d1 := by
  generalize hk1 : 4 + n * 4 = k1 at hI
  generalize hk2 : n * 2 = k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases n with
      | zero => omega
      | succ n =>
        have hm : m = 3 + q * 2 := by omega
        subst hm
        exact z0D q
lemma loc_z2H {n : Nat} {hs hs' : List Call}
    (hI : Num (4 + n * 4) [] hs) (hJ : Num (1 + n * 2) [] hs') :
    Seg hs hs' d1 d1 := by
  generalize hk1 : 4 + n * 4 = k1 at hI
  generalize hk2 : 1 + n * 2 = k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hm : m = 1 + q * 2 := by omega
      subst hm
      exact z0E q
    | even _ => omega
lemma loc_z2I {k : Nat} {v : zW} {k' : Nat} {w : zW} {a b : Rat}
    (hI : zPS k v k' w a b) :
    ∀ {u : zW} {n n' : Nat} {hs hs' : List Call},
      zEf n u n' v -> Num k [] hs -> Num k' [] hs' ->
      Seg (([Call.ch] ^ n) ++ hs) (([Call.ch] ^ n') ++ hs') (zWt u) (zWt w) := by
  induction hI with
  | nil k =>
    intro u n n' hs hs' hE hN hN'
    cases hE
    rw [loc_z2u hN hN']
    exact z0b _
  | @T m _ _ _ _ _ _ ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    cases hE with
    | T hSub =>
      rcases loc_z2t (by omega : 0 < 2 + m * 2) with ⟨hs0,hN0⟩
      have hIH := ih hSub hN0 hN'
      have hStep := zSg (H_T n0) (loc_z2B hN hN0)
      have heq : ([Call.ch] ^ (n0 * 2)) ++ ([Call.ch] ++ hs0) = ([Call.ch] ^ (1 + n0 * 2)) ++ hs0 := by
        have h1 : 1 + n0 * 2 = n0 * 2 + 1 := by omega
        rw [h1,z07,z06,List.append_assoc]
      rw [heq] at hStep
      exact zS0 hStep hIH
  | @pair0 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([Q,K] ++ u) at hE
    rcases z1F [Q,K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := z1M hSub (by cases hN' <;> omega)
    rcases loc_z2t hPos with ⟨hs0,hN0⟩
    have hD10 : zDg 1 2 [Q,K] := zDg.one (zDg.zero zDg.nil)
    have hStep := zSg (zEd hL hD10) (loc_z2C hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @pair1 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([Q,Q] ++ u) at hE
    rcases z1F [Q,Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases loc_z2t (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD11 : zDg 3 2 [Q,Q] := zDg.one (zDg.one zDg.nil)
    have hStep := zSg (zEd hL hD11) (loc_z2D hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short00 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([K] ++ u) at hE
    rcases z1F [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := z1M hSub (by cases hN' <;> omega)
    rcases loc_z2t hPos with ⟨hs0,hN0⟩
    have hD0 : zDg 0 1 [K] := zDg.zero zDg.nil
    have hStep := zSg (zEd hL hD0) (loc_z2E hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short01 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([Q] ++ u) at hE
    rcases z1F [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases loc_z2t (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : zDg 1 1 [Q] := zDg.one zDg.nil
    have hStep := zSg (zEd hL hD1) (loc_z2F hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short10 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([K] ++ u) at hE
    rcases z1F [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := z1M hSub (by cases hN' <;> omega)
    rcases loc_z2t hPos with ⟨hs0,hN0⟩
    have hD0 : zDg 0 1 [K] := zDg.zero zDg.nil
    have hStep := zSg (zEd hL hD0) (loc_z2G hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short11 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([Q] ++ u) at hE
    rcases z1F [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases loc_z2t (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : zDg 1 1 [Q] := zDg.one zDg.nil
    have hStep := zSg (zEd hL hD1) (loc_z2H hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
lemma loc_z2J {k : Nat} {v : zW} {k' : Nat} {w : zW} {a b : Rat}
    (hI : zPS k v k' w a b) {u : zW} {r r' : zB}
    (hE : zEf 0 u 0 v) (hK : 0 < k') (hC : loc_z2v k' r r') :
    loc_z2v k (zTs u r) (zTs w r') := by
  intro w0 hs hN
  have hPosK : 0 < k := z1M hI hK
  have hw0 : w0 = [] := by
    cases hN with
    | zero => omega
    | odd _ => rfl
    | even _ => rfl
  subst hw0
  rcases loc_z2t hK with ⟨hs',hN'⟩
  have hSeg := loc_z2I hI hE hN hN'
  dsimp at hSeg
  have hSide := zSc hSeg (hC [] hs' hN')
  rwa [z16,z16] at hSide
lemma loc_z2K {q : Nat} {orig out : zW} (hS : EStep q orig out) :
    loc_z2v (4 * 2 ^ q) (zTs orig default) (zTs out default) := by
  rcases hS with ⟨eff,n,v,a0,b0,J,da,hE,hI,hPos,hDA⟩
  have hBlank : zTs [K] default = default := by simp [zTs,d0]
  have hC : loc_z2v (n * 2) default (zTs da default) := by
    have heq : n * 2 = ((1 + n) - 1) * 2 := by omega
    rw [heq]
    exact loc_z2A hDA (by omega)
  have hRun := loc_z2J hI hE (by omega : 0 < n * 2) hC
  rwa [z15,hBlank,<- z15] at hRun
lemma loc_z2L (q : Nat) :
    Seg [.cj,.ch] ([.cj] ++ [.ch] ^ (2 ^ q - 1)) (t ^ (1 + q) ++ (d1 ++ one)) (t ^ (1 + q) ++ (d1 ++ one)) := by
  have hpos := zPp q
  have hT := z0I (1 + q) 0
  have heq : (1 + 0) * 2 ^ (1 + q) - 1 = 1 + (2 ^ q - 1) * 2 := by
    rw [zP2]; omega
  rw [heq] at hT
  dsimp at hT
  exact zS0 hT (z0H (2 ^ q - 1))
lemma loc_z2M (q : Nat) :
    Seg [.ca] ([.cj] ++ [.ch] ^ (2 ^ (1 + q) - 1))
      (w_pre ++ (t ^ (2 + q) ++ (d1 ++ one)))
      (w_pre ++ (t ^ (2 + (q + 1)) ++ (d1 ++ one))) := by
  have h1 := zS0 z0m (loc_z2L (1 + q))
  have heq1 : 1 + (1 + q) = 2 + q := by omega
  have heq2 : (w_pre ++ t) ++ (t ^ (2 + q) ++ (d1 ++ one)) = w_pre ++ (t ^ (2 + (q + 1)) ++ (d1 ++ one)) := by
    have h3 : 2 + (q + 1) = 1 + (2 + q) := by omega
    rw [h3,zLp']
    simp only [List.append_assoc]
  rw [heq1] at h1
  rwa [heq2] at h1
lemma loc_z2N (q : Nat) {r r' : zB} (hI : loc_z2v (4 * 2 ^ q) r r') :
    (zCf q r) [target_tm]⊢⁺ zCf (q + 1) r' := by
  have hpos := zPp q
  have h_num : Num (4 * 2 ^ q) [] ([.cj] ++ [.ch] ^ (2 ^ (1 + q) - 1)) := by
    have heq : 4 * 2 ^ q = 2 + (2 ^ (1 + q) - 1) * 2 := by rw [zP2]; omega
    rw [heq]; exact Num.even (2 ^ (1 + q) - 1)
  have hC := hI [] ([.cj] ++ [.ch] ^ (2 ^ (1 + q) - 1)) h_num
  have hS := zSc (loc_z2M q) hC
  rcases hS with _ | ⟨hca,hnil⟩
  cases hnil
  exact zPt (z0n _) (hca lh)
lemma loc_z2O {q : Nat} {orig out : zW} (hS : EStep q orig out) :
    (zCf q (zTs orig default)) [target_tm]⊢⁺ zCf (q + 1) (zTs out default) :=
  loc_z2N q (loc_z2K hS)
lemma loc_z2P {h : Nat} {u : zW} {j : Nat} {v : zW} (hR : ERounds h u j v) :
    (zCf h (zTs u default)) [target_tm]⊢* zCf j (zTs v default) := by
  induction hR with
  | refl _ _ => exact ⟨0,rfl⟩
  | next hS _ ih =>
    rcases loc_z2O hS with ⟨n,_,hn⟩
    rcases ih with ⟨m,hm⟩
    exact ⟨n + m,zMt target_tm _ _ _ n m hn hm⟩
def loc_z2Q : zW := [V,V,Q,V,Q,K,V,K,Q,K,Q,Q]
def loc_z2R : zW := [V,V,Q,V,Q,Q,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,Q,V,V,Q,Q,V,V,Q,V,V,V,Q,V,V,V,Q,Q,V,K,Q,V,V,V,Q,Q,V,V,V,V,Q,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,Q,K,Q,Q,V,Q,Q,Q,K,K,V,V,V,V,K,V,V,V,V,V]
def loc_z2S : zW := [Q,K,K,K,Q,K,K,K,Q,Q,K,Q,K,K,K,Q,K,Q,Q,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def loc_z2T : zW := [K,K,K,K,Q,K,K,K,K,Q,Q,K,Q,K,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def loc_z2U : List e_Code := [
  (.More CT 61 (.More CT 121 (.More CS10 60 (.More CT 117 (.More CS10 58 (.More CS11 28 (.More CT 54 (.More CP0 109 (.More CP1 217 (.More CP0 434 (.Stop 434))))))))))),
  (.More CT 125 (.More CT 249 (.More CS10 124 (.More CT 245 (.More CS10 122 (.More CS10 60 (.More CT 117 (.More CT 233 (.More CT 465 (.More CT 929 (.More CS10 464 (.More CP0 927 (.More CS00 463 (.More CS00 231 (.More CS01 115 (.More CP1 230 (.More CP0 460 (.Stop 460)))))))))))))))))),
  (.More CT 253 (.More CT 505 (.More CS10 252 (.More CT 501 (.More CS10 250 (.More CS10 124 (.More CT 245 (.More CT 489 (.More CT 977 (.More CT 1953 (.More CS10 976 (.More CT 1949 (.More CP0 3899 (.More CS00 1949 (.More CT 3895 (.More CT 7789 (.More CS10 3894 (.More CS10 1946 (.More CS10 972 (.More CP0 1943 (.More CS01 971 (.More CP1 1942 (.More CP0 3884 (.Stop 3884)))))))))))))))))))))))),
  (.More CT 509 (.More CT 1017 (.More CS10 508 (.More CT 1013 (.More CS10 506 (.More CS10 252 (.More CT 501 (.More CT 1001 (.More CT 2001 (.More CT 4001 (.More CS10 2000 (.More CT 3997 (.More CT 7993 (.More CS11 3996 (.More CT 7990 (.More CT 15979 (.More CS10 7989 (.More CP1 15977 (.More CT 31952 (.More CS01 15976 (.More CT 31950 (.More CT 63899 (.More CS10 31949 (.More CS00 15974 (.More CP0 31947 (.More CP0 63893 (.More CS00 31946 (.More CP1 63891 (.More CP1 127782 (.More CP0 255564 (.Stop 255564))))))))))))))))))))))))))))))),
  (.More CT 1021 (.More CT 2041 (.More CS10 1020 (.More CT 2037 (.More CS10 1018 (.More CS10 508 (.More CT 1013 (.More CT 2025 (.More CT 4049 (.More CT 8097 (.More CS10 4048 (.More CT 8093 (.More CT 16185 (.More CS10 8092 (.More CT 16181 (.More CT 32361 (.More CS10 16180 (.More CT 32357 (.More CT 64713 (.More CS11 32356 (.More CT 64710 (.More CT 129419 (.More CS10 64709 (.More CS00 32354 (.More CT 64705 (.More CT 129409 (.More CS11 64704 (.More CT 129406 (.More CT 258811 (.More CT 517621 (.More CS10 258810 (.More CS10 129404 (.More CS11 64701 (.More CP1 129402 (.More CP0 258804 (.More CS10 129401 (.More CS01 64700 (.More CP0 129400 (.More CS10 64699 (.More CS01 32349 (.More CP1 64698 (.More CP1 129396 (.More CP0 258792 (.Stop 258792)))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 2045 (.More CT 4089 (.More CS10 2044 (.More CT 4085 (.More CS10 2042 (.More CS10 1020 (.More CT 2037 (.More CT 4073 (.More CT 8145 (.More CT 16289 (.More CS10 8144 (.More CT 16285 (.More CT 32569 (.More CS10 16284 (.More CT 32565 (.More CT 65129 (.More CS10 32564 (.More CT 65125 (.More CT 130249 (.More CS10 65124 (.More CT 130245 (.More CT 260489 (.More CS10 130244 (.More CS10 65121 (.More CT 130239 (.More CT 260477 (.More CS10 130238 (.More CT 260473 (.More CT 520945 (.More CT 1041889 (.More CS10 520944 (.More CP1 1041887 (.More CT 2083772 (.More CT 4167543 (.More CS10 2083771 (.More CS00 1041885 (.More CT 2083767 (.More CS10 1041883 (.More CS01 520941 (.More CT 1041880 (.More CT 2083759 (.More CT 4167517 (.More CS10 2083758 (.More CS10 1041878 (.More CS10 520938 (.More CS11 260468 (.More CP1 520936 (.More CP0 1041872 (.More CP0 2083743 (.More CS00 1041871 (.More CP1 2083741 (.More CP1 4167482 (.More CP1 8334964 (.More CP0 16669928 (.Stop 16669928))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 4093 (.More CT 8185 (.More CS10 4092 (.More CT 8181 (.More CS10 4090 (.More CS10 2044 (.More CT 4085 (.More CT 8169 (.More CT 16337 (.More CT 32673 (.More CS10 16336 (.More CT 32669 (.More CT 65337 (.More CS10 32668 (.More CT 65333 (.More CT 130665 (.More CS10 65332 (.More CT 130661 (.More CT 261321 (.More CS10 130660 (.More CT 261317 (.More CT 522633 (.More CS10 261316 (.More CS11 130657 (.More CT 261312 (.More CT 522623 (.More CS10 261311 (.More CT 522619 (.More CT 1045237 (.More CT 2090473 (.More CS10 1045236 (.More CT 2090469 (.More CT 4180937 (.More CT 8361873 (.More CS10 4180936 (.More CS10 2090467 (.More CT 4180931 (.More CS10 2090465 (.More CS01 1045232 (.More CT 2090462 (.More CT 4180923 (.More CT 8361845 (.More CS10 4180922 (.More CS11 2090460 (.More CP1 4180920 (.More CT 8361838 (.More CT 16723675 (.More CT 33447349 (.More CS11 16723674 (.More CT 33447346 (.More CT 66894691 (.More CT 133789381 (.More CT 267578761 (.More CS10 133789380 (.More CS10 66894689 (.More CS00 33447344 (.More CP0 66894687 (.More CS01 33447343 (.More CP1 66894686 (.More CP0 133789372 (.More CS11 66894685 (.More CP0 133789370 (.More CP0 267578739 (.More CS00 133789369 (.More CS01 66894684 (.More CP1 133789368 (.More CP1 267578736 (.More CP1 535157472 (.More CP0 1070314944 (.Stop 1070314944)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 8189 (.More CT 16377 (.More CS10 8188 (.More CT 16373 (.More CS10 8186 (.More CS10 4092 (.More CT 8181 (.More CT 16361 (.More CT 32721 (.More CT 65441 (.More CS10 32720 (.More CT 65437 (.More CT 130873 (.More CS10 65436 (.More CT 130869 (.More CT 261737 (.More CS10 130868 (.More CT 261733 (.More CT 523465 (.More CS10 261732 (.More CT 523461 (.More CT 1046921 (.More CS10 523460 (.More CS11 261729 (.More CT 523456 (.More CT 1046911 (.More CS10 523455 (.More CT 1046907 (.More CT 2093813 (.More CT 4187625 (.More CS10 2093812 (.More CT 4187621 (.More CT 8375241 (.More CT 16750481 (.More CS10 8375240 (.More CS11 4187619 (.More CT 8375236 (.More CS00 4187618 (.More CS11 2093808 (.More CT 4187614 (.More CT 8375227 (.More CT 16750453 (.More CS10 8375226 (.More CS11 4187612 (.More CT 8375222 (.More CT 16750443 (.More CT 33500885 (.More CT 67001769 (.More CS10 33500884 (.More CT 67001765 (.More CT 134003529 (.More CT 268007057 (.More CT 536014113 (.More CS10 268007056 (.More CP0 536014111 (.More CT 1072028219 (.More CS11 536014109 (.More CT 1072028216 (.More CT 2144056431 (.More CS10 1072028215 (.More CT 2144056427 (.More CT 4288112853 (.More CP1 8576225707 (.More CT 17152451412 (.More CT 34304902823 (.More CT 68609805645 (.More CT 137219611289 (.More CS10 68609805644 (.More CS10 34304902821 (.More CS00 17152451410 (.More CS10 8576225704 (.More CS11 4288112851 (.More CP0 8576225702 (.More CS10 4288112850 (.More CS10 2144056424 (.More CS10 1072028211 (.More CS00 536014105 (.More CS00 268007052 (.More CP0 536014103 (.More CP1 1072028205 (.More CP0 2144056410 (.More CP0 4288112819 (.More CS00 2144056409 (.More CP1 4288112817 (.More CP1 8576225634 (.More CP1 17152451268 (.More CP1 34304902536 (.More CP0 68609805072 (.Stop 68609805072)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
]
lemma loc_z2V :
    ERounds 4 loc_z2Q 12 (loc_z2R ++ loc_z2S) := by
  have h1 : ERounds 4 loc_z2Q (4 + loc_z2U.length) (loc_z2R ++ loc_z2S) := by
    apply e_z2p loc_z2U
    decide
  exact h1
lemma loc_z2W :
    EGood 12 (loc_z2R ++ loc_z2S) := by
  apply e_z2s 12 loc_z2R loc_z2S loc_z2T
  · decide
  · exact EGuard.T 0 _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · norm_num [loc_z2R,loc_z2T,z1e,z1f,z1h]
abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev loc_z2X (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev loc_z34 (c : CCfg) : Option CCfg := Counter.bstep target_tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep target_tm n c
lemma zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (loc_z2X c1) [target_tm]⊢⁺ (loc_z2X c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩
def loc_z37 : CCfg :=
  ⟨A,0,[],[]⟩
def loc_z38 : CCfg :=
  ⟨C,0,[1,0,0,1,0,0,0,1,0,1],[0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def loc_z39 : CCfg :=
  ⟨D,0,[0,0,0,0,0,1],[1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def loc_z3a : CCfg :=
  ⟨D,0,[1,1,0,0,1,0,1,0,1,1,0,0,0,0,1,0,1],[1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def loc_z3b : CCfg :=
  ⟨F,0,[0,0,0,0,1,1,0,0,1,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,1],[1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3c : CCfg :=
  ⟨C,1,[0,0,1,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,0,0,0,1,1,0,0,0,0,0,0,0,0,1,0,1],[0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3d : CCfg :=
  ⟨F,0,[0,1,1,0,0,1,1,0,0,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,0,0,0,1,1,0,0,0,0,1,0,0,0,1,0,1],[]⟩
set_option maxRecDepth 4000000 in
lemma loc_z3e : zCm loc_z37 1000 = some loc_z38 := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3f : zCm loc_z38 1000 = some loc_z39 := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3g : zCm loc_z39 1000 = some loc_z3a := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3h : zCm loc_z3a 1000 = some loc_z3b := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3i : zCm loc_z3b 1000 = some loc_z3c := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3j : zCm loc_z3c 287 = some loc_z3d := by decide
lemma loc_z3k :
    (init []) [target_tm]⊢⁺ zCf 4 (zTs loc_z2Q default) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = loc_z2X loc_z37 := rfl
  have h_end : loc_z2X loc_z3d = zCf 4 (zTs loc_z2Q default) := by
    simp [loc_z2X,loc_z3d,zCf,zCL,lh,w_pre,w_word,t,d0,d1,one,loc_z2Q,zTs]
  rw [h_init,<- h_end]
  exact zPt (zTc (by decide) loc_z3e) (zPt (zTc (by decide) loc_z3f) (zPt (zTc (by decide) loc_z3g) (zPt (zTc (by decide) loc_z3h) (zPt (zTc (by decide) loc_z3i) ((zTc (by decide) loc_z3j))))))
lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
lemma loc_z3l (m : Nat) :
    ∃ N ≥ m,∃ h w,multiStep target_tm (init []) N = some (zCf h (zTs w default)) /\ EGood h w := by
  induction m with
  | zero =>
    rcases loc_z3k with ⟨k1,_,hk1⟩
    rcases loc_z2P loc_z2V with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,12,loc_z2R ++ loc_z2S,
      zMt target_tm _ _ _ k1 k2 hk1 hk2,loc_z2W⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,h,w,h_ms,h_good⟩
    rcases e_z2d h_good with ⟨w',hStep,h_good'⟩
    rcases loc_z2O hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,h + 1,w',
      zMt target_tm _ _ _ N k h_ms h_step_k,h_good'⟩

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
  rcases loc_z3l (n + 1) with ⟨N,hN,_,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

end BusyBeaver.M_1RB0RD_1RCHHH_1LD1LC_1LE0LC_1RF0RC_1RA0RF
