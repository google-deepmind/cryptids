/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB---_1LC1LB_1LD0LB_1RE1LC_1RF0RE_0RA0RC` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB---_1LC1LB_1LD0LB_1RE1LC_1RF0RE_0RA0RC`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RBHHH_1LC1LB_1LD0LB_1RE1LC_1RF0RE_0RA0RC

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB---_1LC1LB_1LD0LB_1RE1LC_1RF0RE_0RA0RC`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => none
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 2, Stmt.write 0 Dir.right)

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
abbrev w_pre : zF := t ++ t ++ [0] ++ t ++ t ++ one
abbrev w_word : zF := w_pre
@[simp] lemma zDd : d0 +> (default : zB) = default := by
  simp [d0]
inductive Call where
  | ch
  | cj
  | cp
  | ca
def zCs : Call -> Fin 6
  | .ch => D
  | .cj => C
  | .cp => C
  | .ca => C
def zCw : Call -> zF
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
  | .ca => [1,0,1,0,1,0]
def zCR (l : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (r <{{zCs c}} (l <+ zCw c))
def zCL (l : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> r) {{E}}> l)
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
  intro r1 r2 h; exact h
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
lemma zS0 {ls1 ls2 ls3 : List Call} {w1 w2 v1 v2 : zF}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls2 ls3 v1 v2) :
    Seg ls1 ls3 (w1 ++ v1) (w2 ++ v2) := by
  intro r1 r2 h
  rw [append_assoc,append_assoc]
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
lemma z0c : Seg [.cp] [.ch] t (t ++ [0]) :=
  zS2 (mid := [1,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma z0d : Seg [.cj] [.ch] t (t ++ one) :=
  zS2 (mid := [1,1,0,1,1])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma z0e : Seg [.ch] [.cj] (t ++ [0]) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma zH2 : Seg [.ch] [.cj,.ch] (t ++ one) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0f : Seg [.ch] [.ch,.ch] t t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
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
lemma zH0 : Seg [.ch] [] d0 d1 :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1; simp only [append_cons,append_nil]; execute)
lemma zH4 : Seg [.ch] [.ch] d1 d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
lemma H_T (n : Nat) : Seg ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t := by
  induction n with
  | zero => exact z0a t
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [zLp,h_eq,z07]
    exact zSg z0f ih
lemma zSa {w2 : zF} (hw : Seg [.ch,.ch] [.ch] w2 w2) (n : Nat) :
    Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) w2 w2 := by
  induction n with
  | zero => exact z0a w2
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq,z07,zLp]
    exact zSg hw ih
lemma z0m : Seg [.ch,.ch] [.ch] d0 d0 :=
  zSg zH0 zH4
lemma z0n : Seg [.ch,.ch] [.ch] d1 d1 :=
  zSg zH4 zH0
lemma z0o (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d0 d0 :=
  zSa z0m n
lemma z0p (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ n) d0 d1 := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg zH0 (zSa z0n n)
lemma z0q (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d1 d1 :=
  zSa z0n n
lemma z0r (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ (1 + n)) d1 d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg zH4 (zSa z0m n)
lemma z0s (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0c z0e) (H_T n)
lemma z0t (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0d zH2) (H_T n)
lemma z0u (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0g zH2) (H_T n)
lemma z0v (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0h (H_T n)
lemma z0w (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0i (H_T n)
lemma z0x (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using! zSg z0j (H_T n)
lemma z0y (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0k (zSg zH1 zH3)
  have h1 := zSg h0 (zSa z0m n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using! h1
lemma z0z (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0l (zSa z0m n)
lemma z0A : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0k zH1
lemma z0B (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0k (zSg zH1 (zSg zH3 zH0))
  have h1 := zSg h0 (zSa z0n n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using! h1
lemma z0C (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1 := zSg z0l zH0
  have h1 := zSg h0 (zSa z0n n)
  simpa only [zLp',List.cons_append,List.nil_append] using! h1
lemma z0D (n : Nat) : Seg (([Call.ch] ^ n) ++ [.cj,.ch]) (([Call.ch] ^ (1 + n * 2)) ++ [.cj,.ch]) t t := by
  have h1 : Seg (([Call.ch] ^ n) ++ [.cj,.ch]) (([Call.ch] ^ (n * 2)) ++ [.ch,.cj,.ch]) t t :=
    zSg (H_T n) (z0t 0)
  have heq : (([Call.ch] ^ (n * 2)) ++ [.ch,.cj,.ch]) = (([Call.ch] ^ (1 + n * 2)) ++ [.cj,.ch]) := by
    have h2 : 1 + n * 2 = n * 2 + 1 := by omega
    rw [h2,z07,z06,List.append_assoc]
    rfl
  rwa [heq] at h1
lemma z0E (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([.cj] ++ [.ch] ^ n) (d1 ++ one) d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using! zSg zH3 (z0o n)
lemma z0F (n : Nat) : Seg (([Call.ch] ^ (1 + n * 2)) ++ [.cj,.ch]) ([.cj] ++ [.ch] ^ n) (d1 ++ one) (d1 ++ one) := by
  simpa only [List.append_nil] using! zSg (z0E n) z0A
lemma z0G (q : Nat) :
    ∀ n,Seg (([Call.ch] ^ n) ++ [.cj,.ch]) (([Call.ch] ^ ((1 + n) * 2 ^ q - 1)) ++ [.cj,.ch]) (t ^ q) (t ^ q) := by
  induction q with
  | zero =>
    intro n
    have heq : (1 + n) * 2 ^ 0 - 1 = n := by simp
    rw [heq]
    exact z0b _
  | succ q ih =>
    intro n
    have h1 := zS0 (z0D n) (ih (1 + n * 2))
    have heq : (1 + (1 + n * 2)) * 2 ^ q - 1 = (1 + n) * 2 ^ (q + 1) - 1 := by
      rw [Nat.pow_succ]; ring_nf
    rw [heq] at h1
    exact h1
lemma z0H : Seg [.ca] [.cj,.ch] w_pre (w_pre ++ t) :=
  zS5
    (mid1 := [1,0,1,1,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1,0])
    (mid2 := [1,0,1,0,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs w_pre t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL w_pre t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma z0I (r : zB) :
    (zCL lh r) [target_tm]⊢⁺ (zCR lh .ca r) := by
  unfold zCL zCR lh zCw zCs
  simp only [append_cons,append_nil,z00]
  execute
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
      refine zSc (z0y n) ?_
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
      exact zSc z0A (Side.nil r)
    | succ n =>
      have heq : 1 + (n + 1) * 2 = 3 + n * 2 := by omega
      rw [heq]
      refine zSc (z0B n) ?_
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
    exact zS0 (z0o _) (ih hD')
  | d01 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0p _) (ih hD')
  | d10 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0q _) (ih hD')
  | d11 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0r _) (ih hD')
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
        exact z0s m
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
        exact z0t m
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
        exact z0u m
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      have hq : q = m * 2 := by omega
      subst hq
      exact z0v m
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
      exact z0w m
    | even _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hq : q = 1 + m * 2 := by omega
      subst hq
      exact z0x m
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
        exact z0y q
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
      exact z0z q
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
        exact z0B q
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
      exact z0C q
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
  have hT := z0G (1 + q) 0
  have heq : (1 + 0) * 2 ^ (1 + q) - 1 = 1 + (2 ^ q - 1) * 2 := by
    rw [zP2]; omega
  rw [heq] at hT
  dsimp at hT
  exact zS0 hT (z0F (2 ^ q - 1))
lemma loc_z2M (q : Nat) :
    Seg [.ca] ([.cj] ++ [.ch] ^ (2 ^ (1 + q) - 1))
      (w_pre ++ (t ^ (2 + q) ++ (d1 ++ one)))
      (w_pre ++ (t ^ (2 + (q + 1)) ++ (d1 ++ one))) := by
  have h1 := zS0 z0H (loc_z2L (1 + q))
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
  exact zPt (z0I _) (hca lh)
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
def loc_z2Q : zW := [V,V,V,V,V,V,V,K,Q,K,Q,K,K,K,K,Q]
abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev CCfg.head (c : CCfg) : Fin 2 := c.cur
abbrev CCfg.left (c : CCfg) : List (Fin 2) := c.l
abbrev CCfg.right (c : CCfg) : List (Fin 2) := c.r
abbrev loc_z2R (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev loc_z2Y (c : CCfg) : Option CCfg := Counter.bstep target_tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep target_tm n c
lemma zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (loc_z2R c1) [target_tm]⊢⁺ (loc_z2R c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩
def loc_z31 : CCfg :=
  ⟨A,0,[],[]⟩
def loc_z32 : CCfg :=
  ⟨B,0,[1,0,0,1,0,0,0,0,0,1],[0,1,0,1,0,1,0,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1]⟩
def loc_z33 : CCfg :=
  ⟨C,1,[0,0,0,0,1,0,1,0,0,0,1],[1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1]⟩
def loc_z34 : CCfg :=
  ⟨E,1,[1,0,0,0,0,0,0,0,0,0,0,0,1],[1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1]⟩
def loc_z35 : CCfg :=
  ⟨C,1,[0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,0,0,0,1,0,0,0,1,0,1],[1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1]⟩
def loc_z36 : CCfg :=
  ⟨E,0,[0,0,1,1,0,0,1,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1],[1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1]⟩
def loc_z37 : CCfg :=
  ⟨C,0,[1,1,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,1],[1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1]⟩
def loc_z38 : CCfg :=
  ⟨C,1,[0,0,0,0,1,0,1,0,0,0,0,0,1,0,1,0,1],[1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1]⟩
def loc_z39 : CCfg :=
  ⟨E,0,[0,1,1,0,0,1,1,0,0,0,1,1,0,0,1,1,0,0,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,1],[]⟩
set_option maxRecDepth 4000000 in
lemma loc_z3a : zCm loc_z31 1000 = some loc_z32 := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3b : zCm loc_z32 1000 = some loc_z33 := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3c : zCm loc_z33 1000 = some loc_z34 := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3d : zCm loc_z34 1000 = some loc_z35 := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3e : zCm loc_z35 1000 = some loc_z36 := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3f : zCm loc_z36 1000 = some loc_z37 := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3g : zCm loc_z37 1000 = some loc_z38 := by decide
set_option maxRecDepth 4000000 in
lemma loc_z3h : zCm loc_z38 976 = some loc_z39 := by decide
lemma loc_z3i :
    (init []) [target_tm]⊢⁺ zCf 2 (zTs loc_z2Q default) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = loc_z2R loc_z31 := rfl
  have h_end : loc_z2R loc_z39 = zCf 2 (zTs loc_z2Q default) := by
    simp [loc_z2R,loc_z39,zCf,zCL,lh,w_pre,t,d0,d1,one,loc_z2Q,zTs]
  rw [h_init,<- h_end]
  exact zPt (zTc (by decide) loc_z3a)
    (zPt (zTc (by decide) loc_z3b)
      (zPt (zTc (by decide) loc_z3c)
        (zPt (zTc (by decide) loc_z3d)
          (zPt (zTc (by decide) loc_z3e)
            (zPt (zTc (by decide) loc_z3f)
              (zPt (zTc (by decide) loc_z3g)
                (zTc (by decide) loc_z3h)))))))
def loc_z3j : List e_Code := [
  (.More CT 13 (.More CT 25 (.More CT 49 (.More CT 97 (.More CT 193 (.More CT 385 (.More CT 769 (.More CP0 1539 (.More CS00 769 (.More CP0 1537 (.More CS00 768 (.More CS10 383 (.More CS01 191 (.More CP0 382 (.Stop 382))))))))))))))),
  (.More CT 29 (.More CT 57 (.More CT 113 (.More CT 225 (.More CT 449 (.More CT 897 (.More CT 1793 (.More CT 3585 (.More CS11 1792 (.More CT 3582 (.More CP0 7165 (.More CS00 3582 (.More CT 7161 (.More CS10 3580 (.More CS10 1789 (.More CS00 894 (.More CS10 446 (.More CS10 222 (.More CS10 110 (.More CP1 219 (.More CP0 438 (.Stop 438)))))))))))))))))))))),
  (.More CT 61 (.More CT 121 (.More CT 241 (.More CT 481 (.More CT 961 (.More CT 1921 (.More CT 3841 (.More CT 7681 (.More CS10 3840 (.More CT 7677 (.More CT 15353 (.More CS11 7676 (.More CT 15350 (.More CS00 7675 (.More CS01 3837 (.More CP1 7674 (.More CP1 15348 (.More CT 30694 (.More CT 61387 (.More CS10 30693 (.More CP0 61385 (.More CS01 30692 (.More CP0 61384 (.More CP1 122767 (.More CP0 245534 (.Stop 245534)))))))))))))))))))))))))),
  (.More CT 125 (.More CT 249 (.More CT 497 (.More CT 993 (.More CT 1985 (.More CT 3969 (.More CT 7937 (.More CT 15873 (.More CS10 7936 (.More CT 15869 (.More CT 31737 (.More CS10 15868 (.More CT 31733 (.More CP0 63467 (.More CT 126931 (.More CT 253861 (.More CT 507721 (.More CT 1015441 (.More CS10 507720 (.More CT 1015437 (.More CS11 507718 (.More CT 1015434 (.More CT 2030867 (.More CT 4061733 (.More CS10 2030866 (.More CS11 1015432 (.More CP0 2030864 (.More CS10 1015431 (.More CP0 2030861 (.More CS01 1015430 (.More CP1 2030860 (.More CP1 4061720 (.More CP0 8123440 (.More CS11 4061719 (.More CP1 8123438 (.More CP0 16246876 (.Stop 16246876))))))))))))))))))))))))))))))))))))),
  (.More CT 253 (.More CT 505 (.More CT 1009 (.More CT 2017 (.More CT 4033 (.More CT 8065 (.More CT 16129 (.More CT 32257 (.More CS10 16128 (.More CT 32253 (.More CT 64505 (.More CS10 32252 (.More CT 64501 (.More CT 129001 (.More CT 258001 (.More CT 516001 (.More CT 1032001 (.More CT 2064001 (.More CS10 1032000 (.More CT 2063997 (.More CS10 1031998 (.More CT 2063993 (.More CT 4127985 (.More CT 8255969 (.More CS10 4127984 (.More CS11 2063991 (.More CT 4127980 (.More CS00 2063990 (.More CT 4127977 (.More CS11 2063988 (.More CT 4127974 (.More CT 8255947 (.More CT 16511893 (.More CS10 8255946 (.More CT 16511889 (.More CT 33023777 (.More CS10 16511888 (.More CS10 8255943 (.More CS00 4127971 (.More CS00 2063985 (.More CS00 1031992 (.More CS10 515995 (.More CS01 257997 (.More CP0 515994 (.More CS10 257996 (.More CP0 515991 (.More CS01 257995 (.More CP1 515990 (.More CP1 1031980 (.More CP0 2063960 (.More CP1 4127919 (.More CP1 8255838 (.More CP0 16511676 (.Stop 16511676)))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 509 (.More CT 1017 (.More CT 2033 (.More CT 4065 (.More CT 8129 (.More CT 16257 (.More CT 32513 (.More CT 65025 (.More CS10 32512 (.More CT 65021 (.More CT 130041 (.More CS10 65020 (.More CT 130037 (.More CT 260073 (.More CT 520145 (.More CT 1040289 (.More CT 2080577 (.More CT 4161153 (.More CS10 2080576 (.More CT 4161149 (.More CS10 2080574 (.More CT 4161145 (.More CT 8322289 (.More CT 16644577 (.More CS10 8322288 (.More CS11 4161143 (.More CT 8322284 (.More CS01 4161142 (.More CT 8322282 (.More CS00 4161141 (.More CT 8322279 (.More CT 16644557 (.More CT 33289113 (.More CS10 16644556 (.More CT 33289109 (.More CT 66578217 (.More CS10 33289108 (.More CS11 16644553 (.More CP0 33289106 (.More CS10 16644552 (.More CS10 8322275 (.More CS00 4161137 (.More CT 8322271 (.More CS10 4161135 (.More CT 8322267 (.More CS11 4161133 (.More CT 8322264 (.More CT 16644527 (.More CT 33289053 (.More CT 66578105 (.More CT 133156209 (.More CT 266312417 (.More CS10 133156208 (.More CS10 66578103 (.More CP1 133156205 (.More CP1 266312410 (.More CP0 532624820 (.More CP0 1065249639 (.More CS00 532624819 (.More CS01 266312409 (.More CP1 532624818 (.More CP1 1065249636 (.More CP0 2130499272 (.More CS11 1065249635 (.More CP1 2130499270 (.More CP1 4260998540 (.More CP0 8521997080 (.Stop 8521997080)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 1021 (.More CT 2041 (.More CT 4081 (.More CT 8161 (.More CT 16321 (.More CT 32641 (.More CT 65281 (.More CT 130561 (.More CS10 65280 (.More CT 130557 (.More CT 261113 (.More CS10 130556 (.More CT 261109 (.More CT 522217 (.More CT 1044433 (.More CT 2088865 (.More CT 4177729 (.More CT 8355457 (.More CS10 4177728 (.More CT 8355453 (.More CS10 4177726 (.More CT 8355449 (.More CT 16710897 (.More CT 33421793 (.More CS10 16710896 (.More CS11 8355447 (.More CT 16710892 (.More CS01 8355446 (.More CT 16710890 (.More CS01 8355445 (.More CT 16710888 (.More CT 33421775 (.More CT 66843549 (.More CS10 33421774 (.More CT 66843545 (.More CT 133687089 (.More CS10 66843544 (.More CS11 33421771 (.More CT 66843540 (.More CS00 33421770 (.More CP1 66843539 (.More CT 133687076 (.More CS00 66843538 (.More CT 133687073 (.More CS10 66843536 (.More CT 133687069 (.More CT 267374137 (.More CT 534748273 (.More CT 1069496545 (.More CT 2138993089 (.More CT 4277986177 (.More CS10 2138993088 (.More CS11 1069496543 (.More CT 2138993084 (.More CT 4277986167 (.More CT 8555972333 (.More CT 17111944665 (.More CP1 34223889331 (.More CT 68447778660 (.More CT 136895557319 (.More CT 273791114637 (.More CS10 136895557318 (.More CT 273791114633 (.More CT 547582229265 (.More CT 1095164458529 (.More CS10 547582229264 (.More CS10 273791114631 (.More CS00 136895557315 (.More CS00 68447778657 (.More CS00 34223889328 (.More CP0 68447778655 (.More CP1 136895557309 (.More CP0 273791114618 (.More CS11 136895557308 (.More CP0 273791114616 (.More CS10 136895557307 (.More CS01 68447778653 (.More CP0 136895557306 (.More CS10 68447778652 (.More CS11 34223889325 (.More CP1 68447778650 (.More CP1 136895557300 (.More CP0 273791114600 (.More CP1 547582229199 (.More CP1 1095164458398 (.More CP1 2190328916796 (.More CP0 4380657833592 (.Stop 4380657833592)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 2045 (.More CT 4089 (.More CT 8177 (.More CT 16353 (.More CT 32705 (.More CT 65409 (.More CT 130817 (.More CT 261633 (.More CS10 130816 (.More CT 261629 (.More CT 523257 (.More CS10 261628 (.More CT 523253 (.More CT 1046505 (.More CT 2093009 (.More CT 4186017 (.More CT 8372033 (.More CT 16744065 (.More CS10 8372032 (.More CT 16744061 (.More CS10 8372030 (.More CT 16744057 (.More CT 33488113 (.More CT 66976225 (.More CS10 33488112 (.More CS11 16744055 (.More CT 33488108 (.More CS01 16744054 (.More CT 33488106 (.More CS01 16744053 (.More CT 33488104 (.More CT 66976207 (.More CT 133952413 (.More CS10 66976206 (.More CT 133952409 (.More CT 267904817 (.More CS10 133952408 (.More CS11 66976203 (.More CT 133952404 (.More CS01 66976202 (.More CT 133952402 (.More CT 267904803 (.More CS11 133952401 (.More CT 267904800 (.More CS00 133952400 (.More CT 267904797 (.More CT 535809593 (.More CT 1071619185 (.More CT 2143238369 (.More CT 4286476737 (.More CT 8572953473 (.More CS10 4286476736 (.More CS11 2143238367 (.More CT 4286476732 (.More CT 8572953463 (.More CT 17145906925 (.More CT 34291813849 (.More CT 68583627697 (.More CT 137167255393 (.More CT 274334510785 (.More CT 548669021569 (.More CS10 274334510784 (.More CT 548669021565 (.More CT 1097338043129 (.More CT 2194676086257 (.More CS10 1097338043128 (.More CP0 2194676086255 (.More CP0 4389352172509 (.More CT 8778704345015 (.More CT 17557408690029 (.More CT 35114817380057 (.More CS10 17557408690028 (.More CT 35114817380053 (.More CS10 17557408690026 (.More CS11 8778704345012 (.More CT 17557408690022 (.More CS00 8778704345011 (.More CS00 4389352172505 (.More CT 8778704345007 (.More CT 17557408690013 (.More CT 35114817380025 (.More CT 70229634760049 (.More CT 140459269520097 (.More CT 280918539040193 (.More CT 561837078080385 (.More CS10 280918539040192 (.More CS10 140459269520095 (.More CS00 70229634760047 (.More CS01 35114817380023 (.More CP1 70229634760046 (.More CP1 140459269520092 (.More CP1 280918539040184 (.More CP0 561837078080368 (.More CS10 280918539040183 (.More CP1 561837078080365 (.More CP0 1123674156160730 (.More CP0 2247348312321459 (.More CP1 4494696624642917 (.More CP0 8989393249285834 (.More CS11 4494696624642916 (.More CP0 8989393249285832 (.More CS10 4494696624642915 (.More CS01 2247348312321457 (.More CP1 4494696624642914 (.More CP1 8989393249285828 (.More CP0 17978786498571656 (.More CS11 8989393249285827 (.More CP1 17978786498571654 (.More CP1 35957572997143308 (.More CP1 71915145994286616 (.More CP0 143830291988573232 (.Stop 143830291988573232))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
]
def loc_z3k : zW := [V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,Q,V,K,V,K,V,V,V,Q,V,V,Q,Q,V,K,V,V,Q,V,K,V,V,V,V,V,V,Q,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,Q,V,K,K,V,V,V,V,V,V,V,Q,Q,K,K,V,V,V,V,Q,V,V,V,V,V,Q,V,Q,K,V,V,V,Q,V,V,V,V]
def loc_z3l : zW := [Q,K,K,K,Q,Q,K,K,K,K,Q,Q,K,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,K,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q]
def loc_z3m : zW := [K,K,K,K,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]
set_option maxRecDepth 4000000 in
lemma loc_z3n :
    ERounds 2 loc_z2Q 10 (loc_z3k ++ loc_z3l) := by
  have h1 : ERounds 2 loc_z2Q (2 + loc_z3j.length) (loc_z3k ++ loc_z3l) := by
    apply e_z2p loc_z3j
    decide
  simpa using! h1
set_option maxRecDepth 4000000 in
lemma loc_z3o :
    EGood 10 (loc_z3k ++ loc_z3l) := by
  apply e_z2s 10 loc_z3k loc_z3l loc_z3m
  · decide
  · exact EGuard.T 0 _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · norm_num [loc_z3k,loc_z3m,z1e,z1f,z1h]
lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
lemma z3p (m : Nat) :
    ∃ N ≥ m,∃ h w,multiStep target_tm (init []) N = some (zCf h (zTs w default)) /\ EGood h w := by
  induction m with
  | zero =>
    rcases loc_z3i with ⟨k1,_,hk1⟩
    rcases loc_z2P loc_z3n with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,10,loc_z3k ++ loc_z3l,
      zMt target_tm _ _ _ k1 k2 hk1 hk2,loc_z3o⟩
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
  rcases z3p (n + 1) with ⟨N,hN,_,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

end BusyBeaver.M_1RBHHH_1LC1LB_1LD0LB_1RE1LC_1RF0RE_0RA0RC
