/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LF_1RC0RB_1RD0RF_1RE---_1LF1LE_1LA0LE` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LF_1RC0RB_1RD0RF_1RE---_1LF1LE_1LA0LE`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LF_1RC0RB_1RD0RF_1REHHH_1LF1LE_1LA0LE

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LF_1RC0RB_1RD0RF_1RE---_1LF1LE_1LA0LE`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => none
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 4, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open Counter

variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
@[reducible] private def holdout_0420_tm : Machine (Fin 2) (Fin 6) := target_tm
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000000
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
local macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
local macro "gstep" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [Turing.ListBlank.head_cons,zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,z00,zDh,zDt])
local macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | gstep)))
abbrev t : zF := [1,1,0,0]
abbrev d0 : zF := [0,0]
abbrev d1 : zF := [1,0]
abbrev one : zF := [1]
abbrev lh : zB := [1,0,1] +> default
abbrev w_word : zF := t ++ one
abbrev w_pre : zF := w_word
@[simp] lemma zDd : d0 +> (default : zB) = default := by
  simp [d0]
inductive Call where
  | ch
  | cj
  | cp
  | ca
def zCs : Call -> Fin 6
  | .ch => A
  | .cj => F
  | .cp => F
  | .ca => A
def zCw : Call -> zF
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
  | .ca => [1,1,1,0,1,1]
def zCR (l : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (r <{{zCs c}} (l <+ zCw c))
def zCL (l : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> r) {{B}}> l)
def zCf (q : Nat) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  zCL lh ((w_pre ++ (t ^ (2 + q) ++ (d1 ++ one))) +> r)
def z04 (c : Call) (r1 r2 : zB) : Prop :=
  ∀ l,(zCR l c r1) [holdout_0420_tm]⊢⁺ (zCL l r2)
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
    (h1 : ∀ l r,(zCR l c (w1 +> r)) [holdout_0420_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)
lemma zS2 {c_in c_out : Call} {w1 w2 mid : zF}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [holdout_0420_tm]⊢⁺ (zCR (mid +> l) c_out r))
    (h2 : ∀ l r,(zCL (mid +> l) r) [holdout_0420_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1) (zPt (hc1 (mid +> l)) (h2 l r2))
lemma zS5 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : zF}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [holdout_0420_tm]⊢⁺ (zCR (mid1 +> l) c1 r))
    (h2 : ∀ l r,(zCL (mid1 +> l) r) [holdout_0420_tm]⊢⁺ (zCR (mid2 +> l) c2 r))
    (h3 : ∀ l r,(zCL (mid2 +> l) r) [holdout_0420_tm]⊢⁺ (zCL l (w2 +> r))) :
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
  zS5 (mid1 := [1,0,1,1,1,1,0,1,1]) (mid2 := [1,0,1,0,1,1,0,1,1])
    (fun l r => by unfold zCR zCw zCs w_word t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL w_word t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma z0n (r : zB) :
    (zCL lh r) [holdout_0420_tm]⊢⁺ (zCR lh .ca r) := by
  unfold zCL zCR lh zCw zCs
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
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
    (zCf q r) [holdout_0420_tm]⊢⁺ zCf (q + 1) r' := by
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
    (zCf q (zTs orig default)) [holdout_0420_tm]⊢⁺ zCf (q + 1) (zTs out default) :=
  loc_z2N q (loc_z2K hS)
lemma loc_z2P {h : Nat} {u : zW} {j : Nat} {v : zW} (hR : ERounds h u j v) :
    (zCf h (zTs u default)) [holdout_0420_tm]⊢* zCf j (zTs v default) := by
  induction hR with
  | refl _ _ => exact ⟨0,rfl⟩
  | next hS _ ih =>
    rcases loc_z2O hS with ⟨n,_,hn⟩
    rcases ih with ⟨m,hm⟩
    exact ⟨n + m,zMt holdout_0420_tm _ _ _ n m hn hm⟩
def loc_z2Q : zW := [V,V,V,K,K,K,Q,Q,Q]
abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev CCfg.head (c : CCfg) : Fin 2 := c.cur
abbrev CCfg.left (c : CCfg) : List (Fin 2) := c.l
abbrev CCfg.right (c : CCfg) : List (Fin 2) := c.r
abbrev loc_z2R (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev loc_z2Y (c : CCfg) : Option CCfg := Counter.bstep holdout_0420_tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep holdout_0420_tm n c
lemma zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (loc_z2R c1) [holdout_0420_tm]⊢⁺ (loc_z2R c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩
def loc_z31 : CCfg :=
  ⟨A,0,[],[]⟩
def loc_z32 : CCfg :=
  ⟨B,1,[0,1,1,0,0,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,1,0,1,0,1],[0,1]⟩
def z31_1 : CCfg := ⟨B,1,[1,1,0,0,1,0,1],[1,0,1,1,1,1,0,1,1,1,0,1]⟩
def z31_2 : CCfg := ⟨B,0,[0,0,0,0,1,0,1],[1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def z31_3 : CCfg := ⟨C,1,[1,0,0,0,0,1,0,0,0,0,1],[1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_4 : CCfg := ⟨C,1,[1,0,0,1,0,0,0,1,0,0,1],[0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def z31_5 : CCfg := ⟨E,0,[1,0,0,0,0,0,0,0,0,1,1],[0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_6 : CCfg := ⟨F,0,[0,1,0,0,1,0,1,1,0,0,0,1,1],[1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_7 : CCfg := ⟨B,1,[0,1],[1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def z31_8 : CCfg := ⟨F,0,[0,0,1],[1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def z31_9 : CCfg := ⟨B,1,[1],[1,1,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def z31_10 : CCfg := ⟨B,1,[1,1,0,0,0,0,1,0,0,0,1],[1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def z31_11 : CCfg := ⟨F,1,[0,1,0,0,1,0,1,0,1,0,1],[1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def z31_12 : CCfg := ⟨B,1,[0,0,1,0,0,0,0,0,1],[1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def z31_13 : CCfg := ⟨F,0,[0,0,1,0,1,0,0,0,1],[1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def z31_14 : CCfg := ⟨E,0,[0,1,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,1,0,1],[0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_15 : CCfg := ⟨F,1,[0,0,1,1,0,0,1,1,0,0,0,0,0,0,1,0,1,0,1],[1,0,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_16 : CCfg := ⟨F,1,[0,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1],[1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_17 : CCfg := ⟨B,0,[0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,1],[1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_18 : CCfg := ⟨B,0,[0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,1,0,0,0,1],[1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_19 : CCfg := ⟨F,1,[0,0,1,1,0,0,0,0,1,0,0,0,1,0,0,0,1],[1,0,1,0,1,1,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_20 : CCfg := ⟨F,0,[1,0,1,0,1,0,0,0,1],[1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_21 : CCfg := ⟨F,0,[0,0,0,0,0,0,0,0,1,0,1],[1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_22 : CCfg := ⟨B,0,[0,0,0,0,1,0,1,0,0,0,1,0,1],[1,0,1,0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def z31_23 : CCfg := ⟨E,0,[1,0,0,0,0,1,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,1,0,1,0,1],[0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
lemma z33_0 : (loc_z2R loc_z31) [holdout_0420_tm]⊢⁺ (loc_z2R z31_1) := zTc (by decide : 0 < 100) (by decide : zCm loc_z31 100 = some z31_1)
lemma z33_1 : (loc_z2R z31_1) [holdout_0420_tm]⊢⁺ (loc_z2R z31_2) := zTc (by decide : 0 < 100) (by decide : zCm z31_1 100 = some z31_2)
lemma z33_2 : (loc_z2R z31_2) [holdout_0420_tm]⊢⁺ (loc_z2R z31_3) := zTc (by decide : 0 < 100) (by decide : zCm z31_2 100 = some z31_3)
lemma z33_3 : (loc_z2R z31_3) [holdout_0420_tm]⊢⁺ (loc_z2R z31_4) := zTc (by decide : 0 < 100) (by decide : zCm z31_3 100 = some z31_4)
lemma z33_4 : (loc_z2R z31_4) [holdout_0420_tm]⊢⁺ (loc_z2R z31_5) := zTc (by decide : 0 < 100) (by decide : zCm z31_4 100 = some z31_5)
lemma z33_5 : (loc_z2R z31_5) [holdout_0420_tm]⊢⁺ (loc_z2R z31_6) := zTc (by decide : 0 < 100) (by decide : zCm z31_5 100 = some z31_6)
lemma z33_6 : (loc_z2R z31_6) [holdout_0420_tm]⊢⁺ (loc_z2R z31_7) := zTc (by decide : 0 < 100) (by decide : zCm z31_6 100 = some z31_7)
lemma z33_7 : (loc_z2R z31_7) [holdout_0420_tm]⊢⁺ (loc_z2R z31_8) := zTc (by decide : 0 < 100) (by decide : zCm z31_7 100 = some z31_8)
lemma z33_8 : (loc_z2R z31_8) [holdout_0420_tm]⊢⁺ (loc_z2R z31_9) := zTc (by decide : 0 < 100) (by decide : zCm z31_8 100 = some z31_9)
lemma z33_9 : (loc_z2R z31_9) [holdout_0420_tm]⊢⁺ (loc_z2R z31_10) := zTc (by decide : 0 < 100) (by decide : zCm z31_9 100 = some z31_10)
lemma z33_10 : (loc_z2R z31_10) [holdout_0420_tm]⊢⁺ (loc_z2R z31_11) := zTc (by decide : 0 < 100) (by decide : zCm z31_10 100 = some z31_11)
lemma z33_11 : (loc_z2R z31_11) [holdout_0420_tm]⊢⁺ (loc_z2R z31_12) := zTc (by decide : 0 < 100) (by decide : zCm z31_11 100 = some z31_12)
lemma z33_12 : (loc_z2R z31_12) [holdout_0420_tm]⊢⁺ (loc_z2R z31_13) := zTc (by decide : 0 < 100) (by decide : zCm z31_12 100 = some z31_13)
lemma z33_13 : (loc_z2R z31_13) [holdout_0420_tm]⊢⁺ (loc_z2R z31_14) := zTc (by decide : 0 < 100) (by decide : zCm z31_13 100 = some z31_14)
lemma z33_14 : (loc_z2R z31_14) [holdout_0420_tm]⊢⁺ (loc_z2R z31_15) := zTc (by decide : 0 < 100) (by decide : zCm z31_14 100 = some z31_15)
lemma z33_15 : (loc_z2R z31_15) [holdout_0420_tm]⊢⁺ (loc_z2R z31_16) := zTc (by decide : 0 < 100) (by decide : zCm z31_15 100 = some z31_16)
lemma z33_16 : (loc_z2R z31_16) [holdout_0420_tm]⊢⁺ (loc_z2R z31_17) := zTc (by decide : 0 < 100) (by decide : zCm z31_16 100 = some z31_17)
lemma z33_17 : (loc_z2R z31_17) [holdout_0420_tm]⊢⁺ (loc_z2R z31_18) := zTc (by decide : 0 < 100) (by decide : zCm z31_17 100 = some z31_18)
lemma z33_18 : (loc_z2R z31_18) [holdout_0420_tm]⊢⁺ (loc_z2R z31_19) := zTc (by decide : 0 < 100) (by decide : zCm z31_18 100 = some z31_19)
lemma z33_19 : (loc_z2R z31_19) [holdout_0420_tm]⊢⁺ (loc_z2R z31_20) := zTc (by decide : 0 < 100) (by decide : zCm z31_19 100 = some z31_20)
lemma z33_20 : (loc_z2R z31_20) [holdout_0420_tm]⊢⁺ (loc_z2R z31_21) := zTc (by decide : 0 < 100) (by decide : zCm z31_20 100 = some z31_21)
lemma z33_21 : (loc_z2R z31_21) [holdout_0420_tm]⊢⁺ (loc_z2R z31_22) := zTc (by decide : 0 < 100) (by decide : zCm z31_21 100 = some z31_22)
lemma z33_22 : (loc_z2R z31_22) [holdout_0420_tm]⊢⁺ (loc_z2R z31_23) := zTc (by decide : 0 < 100) (by decide : zCm z31_22 100 = some z31_23)
lemma z33_23 : (loc_z2R z31_23) [holdout_0420_tm]⊢⁺ (loc_z2R loc_z32) := zTc (by decide : 0 < 53) (by decide : zCm z31_23 53 = some loc_z32)
lemma loc_z34 : (loc_z2R loc_z31) [holdout_0420_tm]⊢⁺ (loc_z2R loc_z32) :=
  zPt z33_0 (zPt z33_1 (zPt z33_2 (zPt z33_3 (zPt z33_4 (zPt z33_5
  (zPt z33_6 (zPt z33_7 (zPt z33_8 (zPt z33_9 (zPt z33_10 (zPt z33_11
  (zPt z33_12 (zPt z33_13 (zPt z33_14 (zPt z33_15 (zPt z33_16 (zPt z33_17
  (zPt z33_18 (zPt z33_19 (zPt z33_20 (zPt z33_21 (zPt z33_22 z33_23))))))))))))))))))))))
lemma loc_z35 :
    (init []) [holdout_0420_tm]⊢⁺ zCf 3 (zTs loc_z2Q default) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = loc_z2R loc_z31 := rfl
  have h_end : loc_z2R loc_z32 = zCf 3 (zTs loc_z2Q default) := by
    simp [loc_z2R,loc_z32,zCf,zCL,lh,w_word,t,d0,d1,one,loc_z2Q,zTs]
  rw [h_init,<- h_end]
  exact loc_z34
def loc_z36 : List e_Code := [
  (.More CT 29 (.More CT 57 (.More CT 113 (.More CS11 56 (.More CP1 112 (.More CP1 224 (.More CP0 448 (.Stop 448)))))))),
  (.More CT 61 (.More CT 121 (.More CT 241 (.More CS10 120 (.More CT 237 (.More CT 473 (.More CT 945 (.More CS10 472 (.More CS10 235 (.More CS00 117 (.More CP0 233 (.More CS01 116 (.More CP1 232 (.More CP0 464 (.Stop 464))))))))))))))),
  (.More CT 125 (.More CT 249 (.More CT 497 (.More CS10 248 (.More CT 493 (.More CT 985 (.More CT 1969 (.More CS10 984 (.More CP0 1967 (.More CT 3931 (.More CS11 1965 (.More CT 3928 (.More CT 7855 (.More CS10 3927 (.More CS00 1963 (.More CS00 981 (.More CP0 1961 (.More CS01 980 (.More CP1 1960 (.More CP0 3920 (.Stop 3920))))))))))))))))))))),
  (.More CT 253 (.More CT 505 (.More CT 1009 (.More CS10 504 (.More CT 1005 (.More CT 2009 (.More CT 4017 (.More CS10 2008 (.More CT 4013 (.More CT 8025 (.More CS10 4012 (.More CT 8021 (.More CT 16041 (.More CS10 8020 (.More CS10 4009 (.More CS01 2004 (.More CT 4006 (.More CS01 2003 (.More CT 4004 (.More CT 8007 (.More CS10 4003 (.More CS00 2001 (.More CS00 1000 (.More CP0 1999 (.More CP0 3997 (.More CP1 7993 (.More CP1 15986 (.More CP0 31972 (.Stop 31972))))))))))))))))))))))))))))),
  (.More CT 509 (.More CT 1017 (.More CT 2033 (.More CS10 1016 (.More CT 2029 (.More CT 4057 (.More CT 8113 (.More CS10 4056 (.More CT 8109 (.More CT 16217 (.More CS10 8108 (.More CT 16213 (.More CT 32425 (.More CS10 16212 (.More CP1 32423 (.More CT 64844 (.More CS01 32422 (.More CT 64842 (.More CT 129683 (.More CS10 64841 (.More CS00 32420 (.More CS10 16209 (.More CT 32415 (.More CT 64829 (.More CT 129657 (.More CT 259313 (.More CT 518625 (.More CS10 259312 (.More CS10 129655 (.More CP0 259309 (.More CS00 129654 (.More CS11 64826 (.More CP0 129652 (.More CS10 64825 (.More CS01 32412 (.More CP1 64824 (.More CP1 129648 (.More CP0 259296 (.Stop 259296))))))))))))))))))))))))))))))))))))))),
  (.More CT 1021 (.More CT 2041 (.More CT 4081 (.More CS10 2040 (.More CT 4077 (.More CT 8153 (.More CT 16305 (.More CS10 8152 (.More CT 16301 (.More CT 32601 (.More CS10 16300 (.More CT 32597 (.More CT 65193 (.More CS10 32596 (.More CT 65189 (.More CT 130377 (.More CS11 65188 (.More CT 130374 (.More CT 260747 (.More CS10 130373 (.More CS00 65186 (.More CS11 32592 (.More CT 65182 (.More CT 130363 (.More CT 260725 (.More CT 521449 (.More CT 1042897 (.More CS10 521448 (.More CS11 260723 (.More CT 521444 (.More CP1 1042889 (.More CT 2085776 (.More CS00 1042888 (.More CS11 521443 (.More CT 1042884 (.More CT 2085767 (.More CT 4171533 (.More CS10 2085766 (.More CS10 1042882 (.More CS10 521440 (.More CP0 1042879 (.More CS01 521439 (.More CP0 1042878 (.More CS10 521438 (.More CP0 1042875 (.More CP1 2085749 (.More CP1 4171498 (.More CP1 8342996 (.More CP0 16685992 (.Stop 16685992)))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 2045 (.More CT 4089 (.More CT 8177 (.More CS10 4088 (.More CT 8173 (.More CT 16345 (.More CT 32689 (.More CS10 16344 (.More CT 32685 (.More CT 65369 (.More CS10 32684 (.More CT 65365 (.More CT 130729 (.More CS10 65364 (.More CT 130725 (.More CT 261449 (.More CS10 130724 (.More CT 261445 (.More CT 522889 (.More CS10 261444 (.More CS10 130721 (.More CS00 65360 (.More CT 130717 (.More CT 261433 (.More CT 522865 (.More CT 1045729 (.More CT 2091457 (.More CS10 1045728 (.More CS11 522863 (.More CT 1045724 (.More CT 2091447 (.More CT 4182893 (.More CP0 8365787 (.More CT 16731571 (.More CT 33463141 (.More CT 66926281 (.More CS10 33463140 (.More CP1 66926279 (.More CT 133852556 (.More CS01 66926278 (.More CT 133852554 (.More CS00 66926277 (.More CT 133852551 (.More CT 267705101 (.More CT 535410201 (.More CT 1070820401 (.More CT 2141640801 (.More CS10 1070820400 (.More CS10 535410199 (.More CS00 267705099 (.More CP0 535410197 (.More CS00 267705098 (.More CP0 535410195 (.More CS00 267705097 (.More CP1 535410193 (.More CP0 1070820386 (.More CS10 535410192 (.More CP0 1070820383 (.More CS01 535410191 (.More CP1 1070820382 (.More CP1 2141640764 (.More CP1 4283281528 (.More CP0 8566563056 (.Stop 8566563056)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 4093 (.More CT 8185 (.More CT 16369 (.More CS10 8184 (.More CT 16365 (.More CT 32729 (.More CT 65457 (.More CS10 32728 (.More CT 65453 (.More CT 130905 (.More CS10 65452 (.More CT 130901 (.More CT 261801 (.More CS10 130900 (.More CT 261797 (.More CT 523593 (.More CS10 261796 (.More CT 523589 (.More CT 1047177 (.More CS10 523588 (.More CP1 1047175 (.More CT 2094348 (.More CT 4188695 (.More CT 8377389 (.More CT 16754777 (.More CT 33509553 (.More CS10 16754776 (.More CS11 8377387 (.More CT 16754772 (.More CT 33509543 (.More CT 67019085 (.More CT 134038169 (.More CT 268076337 (.More CT 536152673 (.More CT 1072305345 (.More CS10 536152672 (.More CT 1072305341 (.More CT 2144610681 (.More CS11 1072305340 (.More CT 2144610678 (.More CS01 1072305339 (.More CT 2144610676 (.More CT 4289221351 (.More CT 8578442701 (.More CT 17156885401 (.More CT 34313770801 (.More CS10 17156885400 (.More CP0 34313770799 (.More CT 68627541595 (.More CS11 34313770797 (.More CT 68627541592 (.More CS01 34313770796 (.More CT 68627541590 (.More CT 137255083179 (.More CS10 68627541589 (.More CT 137255083175 (.More CS11 68627541587 (.More CT 137255083172 (.More CT 274510166343 (.More CT 549020332685 (.More CT 1098040665369 (.More CS10 549020332684 (.More CS10 274510166341 (.More CS00 137255083170 (.More CS10 68627541584 (.More CS10 34313770791 (.More CP0 68627541581 (.More CS00 34313770790 (.More CS10 17156885394 (.More CP0 34313770787 (.More CS00 17156885393 (.More CS00 8578442696 (.More CP0 17156885391 (.More CP1 34313770781 (.More CP0 68627541562 (.More CP0 137255083123 (.More CS00 68627541561 (.More CP0 137255083121 (.More CP1 274510166241 (.More CP1 549020332482 (.More CP1 1098040664964 (.More CP1 2196081329928 (.More CP0 4392162659856 (.Stop 4392162659856))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
]
def loc_z37 : zW := [V,V,V,Q,V,V,V,Q,V,V,Q,V,V,Q,V,V,Q,V,V,Q,V,V,V,V,V,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,Q,V,K,V,V,V,V,V,Q,V,V,Q,V,K,V,V,Q,V,Q,V,V,V,V,Q,Q,K,Q,Q,V,K,Q,V,K,K,V,V,V,V,K,V,V,V,V,V,V]
def loc_z38 : zW := [Q,K,K,K,Q,K,K,K,K,Q,Q,Q,K,K,K,Q,Q,Q,K,Q,K,K,Q,K,Q,K,K,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def loc_z39 : zW := [K,K,K,K,Q,K,K,K,K,Q,K,K,K,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,K,K,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
set_option maxRecDepth 500000 in
lemma loc_z3a :
    ERounds 3 loc_z2Q 11 (loc_z37 ++ loc_z38) := by
  have h1 : ERounds 3 loc_z2Q (3 + loc_z36.length) (loc_z37 ++ loc_z38) := by
    apply e_z2p loc_z36
    decide
  simpa using! h1
set_option maxRecDepth 500000 in
lemma loc_z3b :
    EGood 11 (loc_z37 ++ loc_z38) := by
  apply e_z2s 11 loc_z37 loc_z38 loc_z39
  · decide
  · exact EGuard.T 0 _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · norm_num [loc_z37,loc_z39,z1e,z1f,z1h]
lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep holdout_0420_tm c (j + d) = some c') :
    (multiStep holdout_0420_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep holdout_0420_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
lemma loc_z3c (m : Nat) :
    ∃ N ≥ m,∃ h w,multiStep holdout_0420_tm (init []) N = some (zCf h (zTs w default)) /\ EGood h w := by
  induction m with
  | zero =>
    rcases loc_z35 with ⟨k1,_,hk1⟩
    rcases loc_z2P loc_z3a with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,11,loc_z37 ++ loc_z38,
      zMt holdout_0420_tm _ _ _ k1 k2 hk1 hk2,loc_z3b⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,h,w,h_ms,h_good⟩
    rcases e_z2d h_good with ⟨w',hStep,h_good'⟩
    rcases loc_z2O hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,h + 1,w',
      zMt holdout_0420_tm _ _ _ N k h_ms h_step_k,h_good'⟩
lemma holdout_0420_nonhalt :
    IsDoesNotHalt holdout_0420_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases loc_z3c (n + 1) with ⟨N,hN,_,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := holdout_0420_nonhalt

end BusyBeaver.M_1RB1LF_1RC0RB_1RD0RF_1REHHH_1LF1LE_1LA0LE
