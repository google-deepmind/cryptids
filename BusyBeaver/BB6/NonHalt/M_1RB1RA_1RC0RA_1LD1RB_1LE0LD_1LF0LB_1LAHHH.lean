/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RA_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LA---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RA_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LA---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RA_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LAHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RA_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LA---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option maxRecDepth 2000000
@[simp] lemma _vault_listblank_mk_empty {Γ : Type*} [Inhabited Γ] :
    Turing.ListBlank.mk ([] : List Γ) = default := by
  ext n; cases n <;> rfl
@[simp] lemma _vault_listblank_mk_cons {Γ : Type*} [Inhabited Γ] (x : Γ) (xs : List Γ) :
    Turing.ListBlank.mk (x :: xs) = Turing.ListBlank.cons x (Turing.ListBlank.mk xs) := by
  ext n; cases n <;> rfl


variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
@[reducible] private def holdout_0596_tm : Machine (Fin 2) (Fin 6) := target_tm
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
abbrev w_pre : zF := t ++ one
abbrev lh : zB := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
@[simp] lemma zDd : d0 +> (default : zB) = default := by
  simp [d0]
inductive Call where
  | ch
  | cj
  | cp
  | ca
def zCs : Call -> Fin 6
  | .ch => C
  | .cj => B
  | .cp => B
  | .ca => C
def zCw : Call -> zF
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
  | .ca => [1,1,1,0,1,1]
def zCR (l : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  ((l <+ zCw c) {{zCs c}}> r)
def zCL (l : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (l <{{D}} ([0] +> r))
def zCf (q : Nat) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  zCR lh .ca ((w_pre ++ t ^ (2 + q) ++ (d1 ++ one)) +> r)
def z04 (c : Call) (r1 r2 : zB) : Prop :=
  ∀ l,(zCR l c r1) [holdout_0596_tm]⊢⁺ (zCL l r2)
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
lemma zS0 {ls1 ls2 ls3 : List Call} {w1 w2 u1 u2 : zF}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls2 ls3 u1 u2) :
    Seg ls1 ls3 (w1 ++ u1) (w2 ++ u2) := by
  intro r1 r2 h
  rw [append_assoc w1 u1 r1,append_assoc w2 u2 r2]
  exact h1 (u1 +> r1) (u2 +> r2) (h2 r1 r2 h)
lemma zS4 {c : Call} {w1 w2 : zF}
    (h1 : ∀ l r,(zCR l c (w1 +> r)) [holdout_0596_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)
lemma zS2 {c_in c_out : Call} {w1 w2 mid : zF}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [holdout_0596_tm]⊢⁺ (zCR (mid +> l) c_out r))
    (h2 : ∀ l r,(zCL (mid +> l) r) [holdout_0596_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1) (zPt (hc1 (mid +> l)) (h2 l r2))
lemma zS5 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : zF}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [holdout_0596_tm]⊢⁺ (zCR (mid1 +> l) c1 r))
    (h2 : ∀ l r,(zCL (mid1 +> l) r) [holdout_0596_tm]⊢⁺ (zCR (mid2 +> l) c2 r))
    (h3 : ∀ l r,(zCL (mid2 +> l) r) [holdout_0596_tm]⊢⁺ (zCL l (w2 +> r))) :
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
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
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
lemma zS3 (n : Nat) : Seg ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t := by
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
lemma H_T (n : Nat) : Seg ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t :=
  zS3 n
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
lemma z0s : Side [.ch] default (d1 +> default) := by
  refine Side.cons (fun l => ?_) (Side.nil _)
  unfold zCR zCL zCw zCs d1
  simp only [append_cons,append_nil,z00]
  execute
lemma z0t (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.ch] ++ [.cj] ++ [.ch] ^ (n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0c z0e) (zS3 n)
lemma z0u (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n)) ([.ch] ++ [.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0d zH2) (zS3 n)
lemma z0v (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0g zH2) (zS3 n)
lemma z0w (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0h (zS3 n)
lemma z0x (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0i (zS3 n)
lemma z0y (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using! zSg z0j (zS3 n)
lemma z0z (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0k (zSg zH1 zH3)
  have h1 := zSg h0 (zSa z0m n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using! h1
lemma z0A (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0l (zSa z0m n)
lemma z0B : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0k zH1
lemma z0C (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0k (zSg zH1 (zSg zH3 zH0))
  have h1 := zSg h0 (zSa z0n n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using! h1
lemma z0D (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1 := zSg z0l zH0
  have h1 := zSg h0 (zSa z0n n)
  simpa only [zLp',List.cons_append,List.nil_append] using! h1
lemma z0E (n : Nat) : Seg ([.ch] ^ n ++ [.cj,.ch]) ([.ch] ^ (1 + n * 2) ++ [.cj,.ch]) t t := by
  have h0 := zSg (H_T n) (z0u 0)
  have heq : 1 + n * 2 = n * 2 + 1 := by omega
  rw [heq,z07]
  simpa only [z05,z06,List.append_nil,List.append_assoc,List.cons_append,List.nil_append] using! h0
lemma z0F (n : Nat) : Seg ([.ch] ^ (1 + n * 2)) ([.cj] ++ [.ch] ^ n) (d1 ++ one) d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg zH3 (zSa z0m n)
lemma z0G (n : Nat) : Seg ([.ch] ^ (1 + n * 2) ++ [.cj,.ch]) ([.cj] ++ [.ch] ^ n) (d1 ++ one) (d1 ++ one) := by
  simpa only [List.append_nil] using! zSg (z0F n) z0B
lemma z0H (q : Nat) :
    ∀ n,Seg (([Call.ch] ^ n) ++ [.cj,.ch]) (([Call.ch] ^ ((1 + n) * 2 ^ q - 1)) ++ [.cj,.ch]) (t ^ q) (t ^ q) := by
  induction q with
  | zero =>
    intro n
    have heq : (1 + n) * 2 ^ 0 - 1 = n := by simp
    rw [heq]
    exact z0b _
  | succ q ih =>
    intro n
    have h1 := zS0 (z0E n) (ih (1 + n * 2))
    have heq : (1 + (1 + n * 2)) * 2 ^ q - 1 = (1 + n) * 2 ^ (q + 1) - 1 := by
      rw [Nat.pow_succ]; ring_nf
    rw [heq] at h1
    exact h1
lemma z0I : Seg [.ca] [.cj,.ch] w_pre (w_pre ++ t) :=
  zS5 (mid1 := [1,0,1,1,1,1,0,1,1]) (mid2 := [1,0,1,0,1,1,0,1,1])
    (fun l r => by unfold zCR zCw zCs w_pre t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL w_pre t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma z0J (r : zB) :
    (zCL lh r) [holdout_0596_tm]⊢⁺ (zCR lh .ca r) := by
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
lemma loc_z2u {k : Nat} (hK : 0 < k) : ∃ hs,Num k [] hs := by
  rcases z0U k with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · cases a with
    | zero => omega
    | succ a =>
      have heq : (a + 1) * 2 = 2 + a * 2 := by omega
      rw [heq]; exact ⟨[.cj] ++ [.ch] ^ a,Num.even a⟩
  · exact ⟨[.cp] ++ [.ch] ^ a,Num.odd a⟩
lemma loc_z2v {k : Nat} {hs hs' : List Call} (h1 : Num k [] hs) (h2 : Num k [] hs') :
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
def loc_z2w (k : Nat) (r r' : zB) : Prop :=
  ∀ w hs,Num k w hs -> Side hs (w +> r) r'
lemma loc_z2x {r r' : zB} (h : loc_z2w 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl
lemma loc_z2y {n : Nat} {r r' : zB}
    (hI : loc_z2w (n * 2) r r') : loc_z2w (2 + n * 4) (d0 +> r) (d0 +> r') := by
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
      have hr' := loc_z2x hI
      subst hr'
      rw [<- append_assoc d0 one r]
      exact zSc z0k (Side.nil r)
    | succ n =>
      have heq : (n + 1) * 2 = 2 + n * 2 := by omega
      rw [heq]
      refine zSc (z0z n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        rw [heq]; exact Num.even n
      simpa using! hI [] _ hN2
lemma loc_z2z {n : Nat} {r r' : zB}
    (hI : loc_z2w (n * 2) r r') : loc_z2w (4 + n * 4) (d0 +> r) (d1 +> r') := by
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
      have hr' := loc_z2x hI
      subst hr'
      rw [<- append_assoc d1 one r]
      exact zSc z0B (Side.nil r)
    | succ n =>
      have heq : 1 + (n + 1) * 2 = 3 + n * 2 := by omega
      rw [heq]
      refine zSc (z0C n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        have heq2 : (n + 1) * 2 = 2 + n * 2 := by omega
        rw [heq2]; exact Num.even n
      simpa using! hI [] _ hN2
lemma loc_z2A {A H : Nat} {da : zW} (hD : zDg A H da) (hZ : A = 0) :
    zTs da default = default := by
  induction hD with
  | nil => rfl
  | @zero A H u _ ih =>
    have hA0 : A = 0 := by omega
    rw [zTs,ih hA0,zDd]
  | one _ => omega
lemma loc_z2B {A H : Nat} {da : zW} (hD : zDg A H da) (hPos : 0 < A) :
    loc_z2w ((A - 1) * 2) default (zTs da default) := by
  induction hD with
  | nil => omega
  | @zero A H u _ ih =>
    have hA_pos : 0 < A := by omega
    have hIH := ih hA_pos
    have hs := loc_z2y hIH
    rw [zDd] at hs
    have heq : (A * 2 - 1) * 2 = 2 + (A - 1) * 4 := by omega
    rw [zTs]
    rwa [heq]
  | @one A H u hDu ih =>
    cases A with
    | zero =>
      have h_side : zTs (Q :: u) default = one +> default := by
        rw [zTs,loc_z2A hDu rfl]
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
      have hs := loc_z2z hIH
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
lemma loc_z2C {n : Nat} {hs hs' : List Call}
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
        exact z0t m
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
        exact z0u m
lemma loc_z2D {n : Nat} {hs hs' : List Call}
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
        exact z0v m
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      have hq : q = m * 2 := by omega
      subst hq
      exact z0w m
lemma loc_z2E {n : Nat} {hs hs' : List Call}
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
      exact z0x m
    | even _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hq : q = 1 + m * 2 := by omega
      subst hq
      exact z0y m
    | even _ => omega
lemma loc_z2F {n : Nat} {hs hs' : List Call}
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
        exact z0z q
lemma loc_z2G {n : Nat} {hs hs' : List Call}
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
      exact z0A q
    | even _ => omega
lemma loc_z2H {n : Nat} {hs hs' : List Call}
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
        exact z0C q
lemma loc_z2I {n : Nat} {hs hs' : List Call}
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
      exact z0D q
    | even _ => omega
lemma loc_z2J {k : Nat} {v : zW} {k' : Nat} {w : zW} {a b : Rat}
    (hI : zPS k v k' w a b) :
    ∀ {u : zW} {n n' : Nat} {hs hs' : List Call},
      zEf n u n' v -> Num k [] hs -> Num k' [] hs' ->
      Seg (([Call.ch] ^ n) ++ hs) (([Call.ch] ^ n') ++ hs') (zWt u) (zWt w) := by
  induction hI with
  | nil k =>
    intro u n n' hs hs' hE hN hN'
    cases hE
    rw [loc_z2v hN hN']
    exact z0b _
  | @T m _ _ _ _ _ _ ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    cases hE with
    | T hSub =>
      rcases loc_z2u (by omega : 0 < 2 + m * 2) with ⟨hs0,hN0⟩
      have hIH := ih hSub hN0 hN'
      have hStep := zSg (H_T n0) (loc_z2C hN hN0)
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
    rcases loc_z2u hPos with ⟨hs0,hN0⟩
    have hD10 : zDg 1 2 [Q,K] := zDg.one (zDg.zero zDg.nil)
    have hStep := zSg (zEd hL hD10) (loc_z2D hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @pair1 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([Q,Q] ++ u) at hE
    rcases z1F [Q,Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases loc_z2u (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD11 : zDg 3 2 [Q,Q] := zDg.one (zDg.one zDg.nil)
    have hStep := zSg (zEd hL hD11) (loc_z2E hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short00 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([K] ++ u) at hE
    rcases z1F [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := z1M hSub (by cases hN' <;> omega)
    rcases loc_z2u hPos with ⟨hs0,hN0⟩
    have hD0 : zDg 0 1 [K] := zDg.zero zDg.nil
    have hStep := zSg (zEd hL hD0) (loc_z2F hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short01 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([Q] ++ u) at hE
    rcases z1F [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases loc_z2u (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : zDg 1 1 [Q] := zDg.one zDg.nil
    have hStep := zSg (zEd hL hD1) (loc_z2G hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short10 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([K] ++ u) at hE
    rcases z1F [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := z1M hSub (by cases hN' <;> omega)
    rcases loc_z2u hPos with ⟨hs0,hN0⟩
    have hD0 : zDg 0 1 [K] := zDg.zero zDg.nil
    have hStep := zSg (zEd hL hD0) (loc_z2H hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short11 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([Q] ++ u) at hE
    rcases z1F [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases loc_z2u (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : zDg 1 1 [Q] := zDg.one zDg.nil
    have hStep := zSg (zEd hL hD1) (loc_z2I hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
lemma loc_z2K {k : Nat} {v : zW} {k' : Nat} {w : zW} {a b : Rat}
    (hI : zPS k v k' w a b) {u : zW} {r r' : zB}
    (hE : zEf 0 u 0 v) (hK : 0 < k') (hC : loc_z2w k' r r') :
    loc_z2w k (zTs u r) (zTs w r') := by
  intro w0 hs hN
  have hPosK : 0 < k := z1M hI hK
  have hw0 : w0 = [] := by
    cases hN with
    | zero => omega
    | odd _ => rfl
    | even _ => rfl
  subst hw0
  rcases loc_z2u hK with ⟨hs',hN'⟩
  have hSeg := loc_z2J hI hE hN hN'
  dsimp at hSeg
  have hSide := zSc hSeg (hC [] hs' hN')
  rwa [z16,z16] at hSide
lemma loc_z2L {q : Nat} {orig out : zW} (hS : EStep q orig out) :
    loc_z2w (4 * 2 ^ q) (zTs orig default) (zTs out default) := by
  rcases hS with ⟨eff,n,v,a0,b0,J,da,hE,hI,hPos,hDA⟩
  have hBlank : zTs [K] default = default := by simp [zTs,d0]
  have hC : loc_z2w (n * 2) default (zTs da default) := by
    have heq : n * 2 = ((1 + n) - 1) * 2 := by omega
    rw [heq]
    exact loc_z2B hDA (by omega)
  have hRun := loc_z2K hI hE (by omega : 0 < n * 2) hC
  rwa [z15,hBlank,<- z15] at hRun
lemma loc_z2M (q : Nat) :
    Seg [.cj,.ch] ([.cj] ++ [.ch] ^ (2 ^ q - 1)) (t ^ (1 + q) ++ (d1 ++ one)) (t ^ (1 + q) ++ (d1 ++ one)) := by
  have hpos := zPp q
  have hT := z0H (1 + q) 0
  have heq : (1 + 0) * 2 ^ (1 + q) - 1 = 1 + (2 ^ q - 1) * 2 := by
    rw [zP2]; omega
  rw [heq] at hT
  dsimp at hT
  exact zS0 hT (z0G (2 ^ q - 1))
lemma loc_z2N (q : Nat) :
    Seg [.ca] ([.cj] ++ [.ch] ^ (2 ^ (1 + q) - 1))
      (w_pre ++ (t ^ (2 + q) ++ (d1 ++ one)))
      (w_pre ++ (t ^ (2 + (q + 1)) ++ (d1 ++ one))) := by
  have h1 := zS0 z0I (loc_z2M (1 + q))
  have heq1 : 1 + (1 + q) = 2 + q := by omega
  have heq2 : (w_pre ++ t) ++ (t ^ (2 + q) ++ (d1 ++ one)) = w_pre ++ (t ^ (2 + (q + 1)) ++ (d1 ++ one)) := by
    have h3 : 2 + (q + 1) = 1 + (2 + q) := by omega
    rw [h3,zLp']
    simp only [List.append_assoc]
  rw [heq1] at h1
  rwa [heq2] at h1
lemma loc_z2O (q : Nat) {r r' : zB} (hI : loc_z2w (4 * 2 ^ q) r r') :
    (zCf q r) [holdout_0596_tm]⊢⁺ zCf (q + 1) r' := by
  have hpos := zPp q
  have h_num : Num (4 * 2 ^ q) [] ([.cj] ++ [.ch] ^ (2 ^ (1 + q) - 1)) := by
    have heq : 4 * 2 ^ q = 2 + (2 ^ (1 + q) - 1) * 2 := by rw [zP2]; omega
    rw [heq]; exact Num.even (2 ^ (1 + q) - 1)
  have hC := hI [] ([.cj] ++ [.ch] ^ (2 ^ (1 + q) - 1)) h_num
  have hS := zSc (loc_z2N q) hC
  rcases hS with _ | ⟨hca,hnil⟩
  cases hnil
  have h_step := zPt (hca lh) (z0J _)
  simpa only [zCf,List.append_assoc] using! h_step
lemma loc_z2P {q : Nat} {orig out : zW} (hS : EStep q orig out) :
    (zCf q (zTs orig default)) [holdout_0596_tm]⊢⁺ zCf (q + 1) (zTs out default) :=
  loc_z2O q (loc_z2L hS)
lemma loc_z2Q {h : Nat} {u : zW} {j : Nat} {v : zW} (hR : ERounds h u j v) :
    (zCf h (zTs u default)) [holdout_0596_tm]⊢* zCf j (zTs v default) := by
  induction hR with
  | refl _ _ => exact ⟨0,rfl⟩
  | next hS _ ih =>
    rcases loc_z2P hS with ⟨n,_,hn⟩
    rcases ih with ⟨m,hm⟩
    exact ⟨n + m,zMt holdout_0596_tm _ _ _ n m hn hm⟩
def loc_z2R : zW := [Q,K,K,Q,K,K,K,Q]
def loc_z2S : List e_Code := [
  (.More CP0 63 (.More CS00 31 (.More CP0 61 (.More CS00 30 (.More CS10 14 (.More CP0 27 (.Stop 27))))))),
  (.More CT 125 (.More CS11 62 (.More CT 122 (.More CP1 245 (.More CT 488 (.More CP0 977 (.More CP1 1953 (.More CP0 3906 (.Stop 3906))))))))),
  (.More CT 253 (.More CS10 126 (.More CT 249 (.More CT 497 (.More CT 993 (.More CT 1985 (.More CT 3969 (.More CT 7937 (.More CS10 3968 (.More CP0 7935 (.More CS00 3967 (.More CS00 1983 (.More CS00 991 (.More CS01 495 (.More CP1 990 (.More CP1 1980 (.More CP0 3960 (.Stop 3960)))))))))))))))))),
  (.More CT 509 (.More CS10 254 (.More CT 505 (.More CT 1009 (.More CT 2017 (.More CT 4033 (.More CT 8065 (.More CT 16129 (.More CS10 8064 (.More CT 16125 (.More CP0 32251 (.More CS00 16125 (.More CS00 8062 (.More CT 16121 (.More CT 32241 (.More CT 64481 (.More CS10 32240 (.More CS10 16119 (.More CS00 8059 (.More CS00 4029 (.More CS00 2014 (.More CS10 1006 (.More CS11 502 (.More CP1 1004 (.More CP1 2008 (.More CP0 4016 (.Stop 4016))))))))))))))))))))))))))),
  (.More CT 1021 (.More CS10 510 (.More CT 1017 (.More CT 2033 (.More CT 4065 (.More CT 8129 (.More CT 16257 (.More CT 32513 (.More CS10 16256 (.More CT 32509 (.More CT 65017 (.More CP1 130035 (.More CT 260068 (.More CT 520135 (.More CT 1040269 (.More CS10 520134 (.More CP0 1040267 (.More CP0 2080533 (.More CP1 4161065 (.More CT 8322128 (.More CT 16644255 (.More CT 33288509 (.More CS10 16644254 (.More CS10 8322126 (.More CS10 4161062 (.More CS11 2080530 (.More CP0 4161060 (.More CS11 2080529 (.More CP1 4161058 (.More CP1 8322116 (.More CP0 16644232 (.Stop 16644232)))))))))))))))))))))))))))))))),
  (.More CT 2045 (.More CS10 1022 (.More CT 2041 (.More CT 4081 (.More CT 8161 (.More CT 16321 (.More CT 32641 (.More CT 65281 (.More CS10 32640 (.More CT 65277 (.More CT 130553 (.More CT 261105 (.More CT 522209 (.More CT 1044417 (.More CT 2088833 (.More CS10 1044416 (.More CT 2088829 (.More CT 4177657 (.More CT 8355313 (.More CT 16710625 (.More CT 33421249 (.More CT 66842497 (.More CS10 33421248 (.More CS11 16710623 (.More CP1 33421246 (.More CT 66842490 (.More CS00 33421245 (.More CT 66842487 (.More CT 133684973 (.More CT 267369945 (.More CS10 133684972 (.More CS10 66842485 (.More CS00 33421242 (.More CP1 66842483 (.More CP0 133684966 (.More CP0 267369931 (.More CS00 133684965 (.More CS01 66842482 (.More CP1 133684964 (.More CP1 267369928 (.More CP0 534739856 (.More CP1 1069479711 (.More CP1 2138959422 (.More CP1 4277918844 (.More CP0 8555837688 (.Stop 8555837688)))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 4093 (.More CS10 2046 (.More CT 4089 (.More CT 8177 (.More CT 16353 (.More CT 32705 (.More CT 65409 (.More CT 130817 (.More CS10 65408 (.More CT 130813 (.More CT 261625 (.More CT 523249 (.More CT 1046497 (.More CT 2092993 (.More CT 4185985 (.More CS10 2092992 (.More CT 4185981 (.More CT 8371961 (.More CT 16743921 (.More CT 33487841 (.More CT 66975681 (.More CT 133951361 (.More CS10 66975680 (.More CS11 33487839 (.More CT 66975676 (.More CT 133951351 (.More CS11 66975675 (.More CT 133951348 (.More CT 267902695 (.More CT 535805389 (.More CS10 267902694 (.More CP0 535805387 (.More CT 1071610771 (.More CT 2143221541 (.More CT 4286443081 (.More CP1 8572886163 (.More CT 17145772324 (.More CT 34291544647 (.More CT 68583089293 (.More CT 137166178585 (.More CT 274332357169 (.More CT 548664714337 (.More CT 1097329428673 (.More CS10 548664714336 (.More CS10 274332357167 (.More CS00 137166178583 (.More CP1 274332357165 (.More CP1 548664714330 (.More CP1 1097329428660 (.More CP0 2194658857320 (.More CS11 1097329428659 (.More CP0 2194658857318 (.More CS11 1097329428658 (.More CP1 2194658857316 (.More CP0 4389317714632 (.More CP1 8778635429263 (.More CP1 17557270858526 (.More CP0 35114541717052 (.More CS11 17557270858525 (.More CP1 35114541717050 (.More CP1 70229083434100 (.More CP1 140458166868200 (.More CP0 280916333736400 (.Stop 280916333736400))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
]
def loc_z2T : zW := [V,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,Q,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,Q,K,V,V,V,V,Q,V,Q,V,V,V,V,V,Q,V,V,V,V]
def loc_z2U : zW := [Q,K,K,K,Q,K,Q,Q,Q,K,K,K,Q,Q,K,Q,K,K,K,Q,K,K,Q,K,K,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q]
def loc_z2V : zW := [K,K,K,K,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,K,K,K,Q,Q,K,K,K,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]
set_option maxRecDepth 500000 in
lemma loc_z2W :
    ERounds 4 loc_z2R 11 (loc_z2T ++ loc_z2U) := by
  have h1 : ERounds 4 loc_z2R (4 + loc_z2S.length) (loc_z2T ++ loc_z2U) := by
    apply e_z2p loc_z2S
    decide
  simpa using! h1
set_option maxRecDepth 500000 in
lemma loc_z2X :
    EGood 11 (loc_z2T ++ loc_z2U) := by
  apply e_z2s 11 loc_z2T loc_z2U loc_z2V
  · decide
  · exact EGuard.T 1 _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · norm_num [loc_z2T,loc_z2V,z1e,z1f,z1h]
def loc_z2Y : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1,1,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1] +> default) {{D}}> ([1,1] +> default))
def loc_z2Z : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1] +> default) {{B}}> ([0,0,1,0,0,0,0,1,0,1] +> default))
def loc_z30 : Cfg (Fin 2) (Fin 6) :=
  (([1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1] +> default) {{B}}> ([1,0,1,0,0,1,1,0,0,0,0,0,0,0,0,1] +> default))
def loc_z31 : Cfg (Fin 2) (Fin 6) :=
  (([1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1] +> default) {{D}}> ([1,1,1,0,0,0,0,0,0,1,0,1] +> default))
def loc_z32 : Cfg (Fin 2) (Fin 6) :=
  (([1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1] +> default) {{C}}> ([0,1,0,0,0,0,1,1,0,0,1] +> default))
def loc_z33 : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1] +> default) {{D}}> ([1,1,1,0,0,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1] +> default))
def loc_z34 : Cfg (Fin 2) (Fin 6) :=
  (([0,1,0,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1] +> default) {{A}}> ([0,0,1,1,0,0,0,0,1,1,0,0,1,0,0,0,1] +> default))
def loc_z35 : Cfg (Fin 2) (Fin 6) :=
  (([1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1] +> default) {{D}}> ([1,0,0,0,1] +> default))
def loc_z36 : Cfg (Fin 2) (Fin 6) :=
  (([1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1] +> default) {{E}}> ([1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,0,0,1] +> default))
def loc_z37 : Cfg (Fin 2) (Fin 6) :=
  (([1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1] +> default) {{D}}> ([1,0,1,0,1,0,1] +> default))
def loc_z38 : Cfg (Fin 2) (Fin 6) :=
  (([0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1] +> default) {{D}}> ([1,0,0,0,1,1,0,0,1,0,0,0,0,0,0,0,1] +> default))
def loc_z39 : Cfg (Fin 2) (Fin 6) :=
  (([1,1,1,1,0,1,1,1,0,1] +> default) {{D}}> ([0,0,0,1,1,0,0,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,0,0,0,0,1] +> default))
def loc_z3a : Cfg (Fin 2) (Fin 6) :=
  (([1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1] +> default) {{C}}> ([1,0,1,1,0,0,1,0,0,0,1,0,0,0,1] +> default))
def loc_z3b : Cfg (Fin 2) (Fin 6) :=
  (([0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1] +> default) {{E}}> ([1,1,0,0,1,0,0,0,0,0,1,0,1] +> default))
def loc_z3c : Cfg (Fin 2) (Fin 6) :=
  (([1,1,1,0,1,0,1,1,0,1,1,1,0,1] +> default) {{D}}> ([0,0,0,1,1,0,0,1,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,0,0,1,0,1] +> default))
def loc_z3d : Cfg (Fin 2) (Fin 6) :=
  (([0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1] +> default) {{A}}> ([0,0,1,0,0,0,1,0,1,0,1] +> default))
def loc_z3e : Cfg (Fin 2) (Fin 6) :=
  (([1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1] +> default) {{C}}> ([1] +> default))
def loc_z3f : Cfg (Fin 2) (Fin 6) :=
  (([1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1] +> default) {{B}}> ([1,0,0,1,1,0,1,1,0,0,1,0,0,0,0,0,0,0,0,0,1] +> default))
lemma loc_z3g : (init []) [holdout_0596_tm]⊢⁺ loc_z2Y := by
  unfold init loc_z2Y
  simp only [append_cons,append_nil,z00]
  execute
lemma loc_z3h : (loc_z2Y) [holdout_0596_tm]⊢⁺ loc_z2Z := by
  unfold loc_z2Y loc_z2Z
  simp only [append_cons,append_nil,z00]
  execute
lemma loc_z3i : (loc_z2Z) [holdout_0596_tm]⊢⁺ loc_z30 := by
  unfold loc_z2Z loc_z30
  simp only [append_cons,append_nil,z00]
  execute
lemma loc_z3j : (loc_z30) [holdout_0596_tm]⊢⁺ loc_z31 := by
  unfold loc_z30 loc_z31
  simp only [append_cons,append_nil,z00]
  execute
lemma loc_z3k : (loc_z31) [holdout_0596_tm]⊢⁺ loc_z32 := by
  unfold loc_z31 loc_z32
  simp only [append_cons,append_nil,z00]
  execute
lemma loc_z3l : (loc_z32) [holdout_0596_tm]⊢⁺ loc_z33 := by
  unfold loc_z32 loc_z33
  simp only [append_cons,append_nil,z00]
  execute
lemma loc_z3m : (loc_z33) [holdout_0596_tm]⊢⁺ loc_z34 := by
  unfold loc_z33 loc_z34
  simp only [append_cons,append_nil,z00]
  execute
lemma loc_z3n : (loc_z34) [holdout_0596_tm]⊢⁺ loc_z35 := by
  unfold loc_z34 loc_z35
  simp only [append_cons,append_nil,z00]
  execute
lemma loc_z3o : (loc_z35) [holdout_0596_tm]⊢⁺ loc_z36 := by
  unfold loc_z35 loc_z36
  simp only [append_cons,append_nil,z00]
  execute
lemma z3p : (loc_z36) [holdout_0596_tm]⊢⁺ loc_z37 := by
  unfold loc_z36 loc_z37
  simp only [append_cons,append_nil,z00]
  execute
lemma z3q : (loc_z37) [holdout_0596_tm]⊢⁺ loc_z38 := by
  unfold loc_z37 loc_z38
  simp only [append_cons,append_nil,z00]
  execute
lemma z3r : (loc_z38) [holdout_0596_tm]⊢⁺ loc_z39 := by
  unfold loc_z38 loc_z39
  simp only [append_cons,append_nil,z00]
  execute
lemma z3s : (loc_z39) [holdout_0596_tm]⊢⁺ loc_z3a := by
  unfold loc_z39 loc_z3a
  simp only [append_cons,append_nil,z00]
  execute
lemma z3t : (loc_z3a) [holdout_0596_tm]⊢⁺ loc_z3b := by
  unfold loc_z3a loc_z3b
  simp only [append_cons,append_nil,z00]
  execute
lemma z3u : (loc_z3b) [holdout_0596_tm]⊢⁺ loc_z3c := by
  unfold loc_z3b loc_z3c
  simp only [append_cons,append_nil,z00]
  execute
lemma z3v : (loc_z3c) [holdout_0596_tm]⊢⁺ loc_z3d := by
  unfold loc_z3c loc_z3d
  simp only [append_cons,append_nil,z00]
  execute
lemma z3w : (loc_z3d) [holdout_0596_tm]⊢⁺ loc_z3e := by
  unfold loc_z3d loc_z3e
  simp only [append_cons,append_nil,z00]
  execute
lemma z3x : (loc_z3e) [holdout_0596_tm]⊢⁺ loc_z3f := by
  unfold loc_z3e loc_z3f
  simp only [append_cons,append_nil,z00]
  execute
lemma z3y : loc_z3f [holdout_0596_tm]⊢⁺ zCf 4 (zTs loc_z2R default) := by
  have h_target : zCf 4 (zTs loc_z2R default) = (([1,1,1,0,1,1,1,0,1] +> default) {{C}}> ([1,1,0,0,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,0,0,0,1,0,0,0,0,0,0,0,1] +> default)) := by
    unfold zCf zCR lh zCw zCs w_pre t d1 one loc_z2R
    simp only [zTs,d0,d1,t,one,zLp,z05,List.cons_append,List.nil_append,append_cons,append_nil,z00]
  rw [h_target]
  unfold loc_z3f
  simp only [append_cons,append_nil,z00]
  execute
lemma loc_z3z : (init []) [holdout_0596_tm]⊢⁺ zCf 4 (zTs loc_z2R default) :=
  (zPt loc_z3g (zPt loc_z3h (zPt loc_z3i (zPt loc_z3j (zPt loc_z3k (zPt loc_z3l (zPt loc_z3m (zPt loc_z3n (zPt loc_z3o (zPt z3p (zPt z3q (zPt z3r (zPt z3s (zPt z3t (zPt z3u (zPt z3v (zPt z3w (zPt z3x z3y))))))))))))))))))
lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep holdout_0596_tm c (j + d) = some c') :
    (multiStep holdout_0596_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep holdout_0596_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
lemma loc_z3A (m : Nat) :
    ∃ N ≥ m,∃ q w,multiStep holdout_0596_tm (init []) N = some (zCf q (zTs w default)) /\ EGood q w := by
  induction m with
  | zero =>
    rcases loc_z3z with ⟨k1,_,hk1⟩
    rcases loc_z2Q loc_z2W with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,11,loc_z2T ++ loc_z2U,
      zMt holdout_0596_tm _ _ _ k1 k2 hk1 hk2,loc_z2X⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,q,w,h_ms,h_good⟩
    rcases e_z2d h_good with ⟨w',hStep,h_good'⟩
    rcases loc_z2P hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,q + 1,w',
      zMt holdout_0596_tm _ _ _ N k h_ms h_step_k,h_good'⟩
lemma holdout_0596_nonhalt :
    IsDoesNotHalt holdout_0596_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases loc_z3A (n + 1) with ⟨N,hN,_,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := holdout_0596_nonhalt

end BusyBeaver.M_1RB1RA_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LAHHH
