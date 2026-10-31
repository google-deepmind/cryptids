/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RA_1RC0RE_1RD---_1LE1LD_1LF0LD_1RA1LE` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RA_1RC0RE_1RD---_1LE1LD_1LF0LD_1RA1LE`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RA_1RC0RE_1RDHHH_1LE1LD_1LF0LD_1RA1LE

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RA_1RC0RE_1RD---_1LE1LD_1LF0LD_1RA1LE`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => none
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 4, Stmt.write 1 Dir.left)

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open Counter

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
@[reducible] private def holdout_0549_tm : Machine (Fin 2) (Fin 6) := target_tm
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
  | .ch => F
  | .cj => E
  | .cp => E
  | .ca => F
def zCw : Call -> zF
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
  | .ca => [1,1,1,0,1,1]
def zCR (l : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (r <{{zCs c}} (l <+ zCw c))
def zCL (l : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> r) {{A}}> l)
def zCf (q : Nat) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  zCL lh ((w_pre ++ (t ^ (2 + q) ++ (d1 ++ one))) +> r)
def z04 (c : Call) (r1 r2 : zB) : Prop :=
  ∀ l,(zCR l c r1) [holdout_0549_tm]⊢⁺ (zCL l r2)
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
    (h1 : ∀ l r,(zCR l c (w1 +> r)) [holdout_0549_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)
lemma zS2 {c_in c_out : Call} {w1 w2 mid : zF}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [holdout_0549_tm]⊢⁺ (zCR (mid +> l) c_out r))
    (h2 : ∀ l r,(zCL (mid +> l) r) [holdout_0549_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1) (zPt (hc1 (mid +> l)) (h2 l r2))
lemma zS5 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : zF}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [holdout_0549_tm]⊢⁺ (zCR (mid1 +> l) c1 r))
    (h2 : ∀ l r,(zCL (mid1 +> l) r) [holdout_0549_tm]⊢⁺ (zCR (mid2 +> l) c2 r))
    (h3 : ∀ l r,(zCL (mid2 +> l) r) [holdout_0549_tm]⊢⁺ (zCL l (w2 +> r))) :
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
    (zCL lh r) [holdout_0549_tm]⊢⁺ (zCR lh .ca r) := by
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
    (zCf q r) [holdout_0549_tm]⊢⁺ zCf (q + 1) r' := by
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
    (zCf q (zTs orig default)) [holdout_0549_tm]⊢⁺ zCf (q + 1) (zTs out default) :=
  loc_z2N q (loc_z2K hS)
lemma loc_z2P {h : Nat} {u : zW} {j : Nat} {v : zW} (hR : ERounds h u j v) :
    (zCf h (zTs u default)) [holdout_0549_tm]⊢* zCf j (zTs v default) := by
  induction hR with
  | refl _ _ => exact ⟨0,rfl⟩
  | next hS _ ih =>
    rcases loc_z2O hS with ⟨n,_,hn⟩
    rcases ih with ⟨m,hm⟩
    exact ⟨n + m,zMt holdout_0549_tm _ _ _ n m hn hm⟩
def loc_z2Q : zW := [V,Q,Q,V,V,Q,V,Q,V,V,V,K,V,V,K,K,Q,K,K,K,Q,K,Q]
abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev CCfg.head (c : CCfg) : Fin 2 := c.cur
abbrev CCfg.left (c : CCfg) : List (Fin 2) := c.l
abbrev CCfg.right (c : CCfg) : List (Fin 2) := c.r
abbrev loc_z2R (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev loc_z2Y (c : CCfg) : Option CCfg := Counter.bstep holdout_0549_tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep holdout_0549_tm n c
lemma zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (loc_z2R c1) [holdout_0549_tm]⊢⁺ (loc_z2R c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩
def loc_z31 : CCfg :=
  ⟨A,0,[],[]⟩
def loc_z32 : CCfg :=
  ⟨E,0,[0,0,0,1,1,0,0,1,1],[1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def loc_z33 : CCfg :=
  ⟨F,1,[1,0,0,1,0,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,0,0,0,1],[1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def loc_z34 : CCfg :=
  ⟨B,1,[1,0,0,1,0,1],[1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z35 : CCfg :=
  ⟨A,0,[0,0,1,1,1,0,0,1,0,1,1,0,0,1,0,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,1,0,1,0,0,0,1],[1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z36 : CCfg :=
  ⟨A,1,[1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,0,1,0,1,1,0,0,1,1,1,0,0,1,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,1,0,0,0,0,0,0,0,1],[1,0,1,1,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def loc_z37 : CCfg :=
  ⟨E,0,[0,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,1],[1,1,1,0,1,1,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def loc_z38 : CCfg :=
  ⟨E,0,[1,0,1,0,1],[1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def loc_z39 : CCfg :=
  ⟨A,1,[1,0,0,0,0,0,1,0,1,0,1],[1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1]⟩
def loc_z3a : CCfg :=
  ⟨A,1,[0,0,1,1,0,0,1,1,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1],[1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3b : CCfg :=
  ⟨E,0,[0,1,0,0,0,0,1,0,1,0,1,0,0,0,1,0,1],[1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3c : CCfg :=
  ⟨A,0,[0,0,1,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1],[1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3d : CCfg :=
  ⟨A,1,[0,0,1,1,0,0,1,0,1,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,1],[1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3e : CCfg :=
  ⟨E,1,[0,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,1],[1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3f : CCfg :=
  ⟨E,0,[0,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,1,0,1,0,1,0,0,0,1,0,1],[1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3g : CCfg :=
  ⟨E,0,[0,1,0,0,0,0,1,0,1,0,0,0,1,0,1,0,1,0,1],[1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3h : CCfg :=
  ⟨E,1,[0,0,1,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1],[1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3i : CCfg :=
  ⟨E,0,[0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,1],[1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3j : CCfg :=
  ⟨A,1,[0,1,1,0,0,1,0,1,1,1,0,0,1,0,1,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1],[0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1]⟩
def loc_z3k : CCfg :=
  ⟨A,1,[0,1,1,0,0,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,1,0,0,1,0,1,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1],[0,1]⟩
set_option maxRecDepth 500000 in
lemma loc_z3l : zCm loc_z31 1000 = some loc_z32 := by decide
set_option maxRecDepth 500000 in
lemma loc_z3m : zCm loc_z32 1000 = some loc_z33 := by decide
set_option maxRecDepth 500000 in
lemma loc_z3n : zCm loc_z33 1000 = some loc_z34 := by decide
set_option maxRecDepth 500000 in
lemma loc_z3o : zCm loc_z34 1000 = some loc_z35 := by decide
set_option maxRecDepth 500000 in
lemma z3p : zCm loc_z35 1000 = some loc_z36 := by decide
set_option maxRecDepth 500000 in
lemma z3q : zCm loc_z36 1000 = some loc_z37 := by decide
set_option maxRecDepth 500000 in
lemma z3r : zCm loc_z37 1000 = some loc_z38 := by decide
set_option maxRecDepth 500000 in
lemma z3s : zCm loc_z38 1000 = some loc_z39 := by decide
set_option maxRecDepth 500000 in
lemma z3t : zCm loc_z39 1000 = some loc_z3a := by decide
set_option maxRecDepth 500000 in
lemma z3u : zCm loc_z3a 1000 = some loc_z3b := by decide
set_option maxRecDepth 500000 in
lemma z3v : zCm loc_z3b 1000 = some loc_z3c := by decide
set_option maxRecDepth 500000 in
lemma z3w : zCm loc_z3c 1000 = some loc_z3d := by decide
set_option maxRecDepth 500000 in
lemma z3x : zCm loc_z3d 1000 = some loc_z3e := by decide
set_option maxRecDepth 500000 in
lemma z3y : zCm loc_z3e 1000 = some loc_z3f := by decide
set_option maxRecDepth 500000 in
lemma loc_z3z : zCm loc_z3f 1000 = some loc_z3g := by decide
set_option maxRecDepth 500000 in
lemma loc_z3A : zCm loc_z3g 1000 = some loc_z3h := by decide
set_option maxRecDepth 500000 in
lemma loc_z3B : zCm loc_z3h 1000 = some loc_z3i := by decide
set_option maxRecDepth 500000 in
lemma loc_z3C : zCm loc_z3i 1000 = some loc_z3j := by decide
set_option maxRecDepth 500000 in
lemma loc_z3D : zCm loc_z3j 53 = some loc_z3k := by decide
lemma loc_z3E :
    (init []) [holdout_0549_tm]⊢⁺ zCf 5 (zTs loc_z2Q default) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = loc_z2R loc_z31 := rfl
  have h_end : loc_z2R loc_z3k = zCf 5 (zTs loc_z2Q default) := by
    simp [loc_z2R,loc_z3k,zCf,zCL,lh,w_pre,w_word,t,d0,d1,one,loc_z2Q,zTs]
  rw [h_init,<- h_end]
  exact zPt (zTc (by decide) loc_z3l) (zPt (zTc (by decide) loc_z3m) (zPt (zTc (by decide) loc_z3n) (zPt (zTc (by decide) loc_z3o) (zPt (zTc (by decide) z3p) (zPt (zTc (by decide) z3q) (zPt (zTc (by decide) z3r) (zPt (zTc (by decide) z3s) (zPt (zTc (by decide) z3t) (zPt (zTc (by decide) z3u) (zPt (zTc (by decide) z3v) (zPt (zTc (by decide) z3w) (zPt (zTc (by decide) z3x) (zPt (zTc (by decide) z3y) (zPt (zTc (by decide) loc_z3z) (zPt (zTc (by decide) loc_z3A) (zPt (zTc (by decide) loc_z3B) (zPt (zTc (by decide) loc_z3C) ((zTc (by decide) loc_z3D)))))))))))))))))))
def loc_z3F : List e_Code := [
  (.More CT 125 (.More CS10 62 (.More CS10 30 (.More CT 57 (.More CT 113 (.More CS10 56 (.More CT 109 (.More CS10 54 (.More CT 105 (.More CT 209 (.More CT 417 (.More CS11 208 (.More CT 414 (.More CT 827 (.More CS11 413 (.More CP0 826 (.More CS10 412 (.More CS10 205 (.More CP0 409 (.More CS01 204 (.More CP0 408 (.Stop 408)))))))))))))))))))))),
  (.More CT 253 (.More CS10 126 (.More CS10 62 (.More CT 121 (.More CT 241 (.More CS10 120 (.More CT 237 (.More CS10 118 (.More CT 233 (.More CT 465 (.More CT 929 (.More CS10 464 (.More CT 925 (.More CT 1849 (.More CS10 924 (.More CT 1845 (.More CS10 922 (.More CS10 460 (.More CT 917 (.More CS11 458 (.More CT 914 (.More CS00 457 (.More CP1 913 (.More CP0 1826 (.More CS10 912 (.More CP1 1823 (.More CP0 3646 (.Stop 3646)))))))))))))))))))))))))))),
  (.More CT 509 (.More CS10 254 (.More CS10 126 (.More CT 249 (.More CT 497 (.More CS10 248 (.More CT 493 (.More CS10 246 (.More CT 489 (.More CT 977 (.More CT 1953 (.More CS10 976 (.More CT 1949 (.More CT 3897 (.More CS10 1948 (.More CT 3893 (.More CS10 1946 (.More CS10 972 (.More CT 1941 (.More CS10 970 (.More CT 1937 (.More CS11 968 (.More CT 1934 (.More CT 3867 (.More CS10 1933 (.More CT 3863 (.More CT 7725 (.More CS10 3862 (.More CP0 7723 (.More CS00 3861 (.More CS00 1930 (.More CP0 3859 (.More CS00 1929 (.More CS01 964 (.More CP1 1928 (.More CP0 3856 (.Stop 3856))))))))))))))))))))))))))))))))))))),
  (.More CT 1021 (.More CS10 510 (.More CS10 254 (.More CT 505 (.More CT 1009 (.More CS10 504 (.More CT 1005 (.More CS10 502 (.More CT 1001 (.More CT 2001 (.More CT 4001 (.More CS10 2000 (.More CT 3997 (.More CT 7993 (.More CS10 3996 (.More CT 7989 (.More CS10 3994 (.More CS10 1996 (.More CT 3989 (.More CS10 1994 (.More CT 3985 (.More CS10 1992 (.More CT 3981 (.More CT 7961 (.More CS10 3980 (.More CT 7957 (.More CT 15913 (.More CS10 7956 (.More CT 15909 (.More CP0 31819 (.More CT 63635 (.More CP1 127271 (.More CT 254540 (.More CT 509079 (.More CS10 254539 (.More CS00 127269 (.More CS00 63634 (.More CP0 127267 (.More CS00 63633 (.More CS00 31816 (.More CP1 63631 (.More CP1 127262 (.More CP0 254524 (.Stop 254524)))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 2045 (.More CS10 1022 (.More CS10 510 (.More CT 1017 (.More CT 2033 (.More CS10 1016 (.More CT 2029 (.More CS10 1014 (.More CT 2025 (.More CT 4049 (.More CT 8097 (.More CS10 4048 (.More CT 8093 (.More CT 16185 (.More CS10 8092 (.More CT 16181 (.More CS10 8090 (.More CS10 4044 (.More CT 8085 (.More CS10 4042 (.More CT 8081 (.More CS10 4040 (.More CT 8077 (.More CT 16153 (.More CS10 8076 (.More CT 16149 (.More CT 32297 (.More CS10 16148 (.More CT 32293 (.More CT 64585 (.More CT 129169 (.More CT 258337 (.More CT 516673 (.More CT 1033345 (.More CS10 516672 (.More CS10 258335 (.More CS00 129167 (.More CT 258331 (.More CP0 516663 (.More CT 1033323 (.More CT 2066645 (.More CT 4133289 (.More CS10 2066644 (.More CS10 1033321 (.More CP0 2066641 (.More CS00 1033320 (.More CP0 2066639 (.More CS00 1033319 (.More CP0 2066637 (.More CS00 1033318 (.More CS10 516658 (.More CS11 258328 (.More CP1 516656 (.More CP1 1033312 (.More CP0 2066624 (.Stop 2066624)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 4093 (.More CS10 2046 (.More CS10 1022 (.More CT 2041 (.More CT 4081 (.More CS10 2040 (.More CT 4077 (.More CS10 2038 (.More CT 4073 (.More CT 8145 (.More CT 16289 (.More CS10 8144 (.More CT 16285 (.More CT 32569 (.More CS10 16284 (.More CT 32565 (.More CS10 16282 (.More CS10 8140 (.More CT 16277 (.More CS10 8138 (.More CT 16273 (.More CS10 8136 (.More CT 16269 (.More CT 32537 (.More CS10 16268 (.More CT 32533 (.More CT 65065 (.More CS10 32532 (.More CT 65061 (.More CT 130121 (.More CT 260241 (.More CT 520481 (.More CT 1040961 (.More CT 2081921 (.More CS10 1040960 (.More CP0 2081919 (.More CT 4163835 (.More CT 8327669 (.More CT 16655337 (.More CT 33310673 (.More CT 66621345 (.More CS10 33310672 (.More CS11 16655335 (.More CT 33310668 (.More CS01 16655334 (.More CT 33310666 (.More CS01 16655333 (.More CT 33310664 (.More CS01 16655332 (.More CP1 33310664 (.More CT 66621326 (.More CT 133242651 (.More CT 266485301 (.More CS10 133242650 (.More CS10 66621324 (.More CS10 33310661 (.More CS01 16655330 (.More CP0 33310660 (.More CP0 66621319 (.More CS00 33310659 (.More CS00 16655329 (.More CP0 33310657 (.More CS00 16655328 (.More CS10 8327663 (.More CP1 16655325 (.More CP1 33310650 (.More CP1 66621300 (.More CP0 133242600 (.Stop 133242600))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 8189 (.More CS10 4094 (.More CS10 2046 (.More CT 4089 (.More CT 8177 (.More CS10 4088 (.More CT 8173 (.More CS10 4086 (.More CT 8169 (.More CT 16337 (.More CT 32673 (.More CS10 16336 (.More CT 32669 (.More CT 65337 (.More CS10 32668 (.More CT 65333 (.More CS10 32666 (.More CS10 16332 (.More CT 32661 (.More CS10 16330 (.More CT 32657 (.More CS10 16328 (.More CT 32653 (.More CT 65305 (.More CS10 32652 (.More CT 65301 (.More CT 130601 (.More CS10 65300 (.More CT 130597 (.More CT 261193 (.More CT 522385 (.More CT 1044769 (.More CT 2089537 (.More CT 4179073 (.More CS10 2089536 (.More CT 4179069 (.More CT 8358137 (.More CT 16716273 (.More CT 33432545 (.More CT 66865089 (.More CT 133730177 (.More CS10 66865088 (.More CS11 33432543 (.More CT 66865084 (.More CS01 33432542 (.More CT 66865082 (.More CS01 33432541 (.More CT 66865080 (.More CS01 33432540 (.More CT 66865078 (.More CT 133730155 (.More CT 267460309 (.More CT 534920617 (.More CS10 267460308 (.More CS11 133730153 (.More CP0 267460306 (.More CT 534920609 (.More CT 1069841217 (.More CP1 2139682435 (.More CT 4279364868 (.More CP0 8558729737 (.More CT 17117459471 (.More CT 34234918941 (.More CT 68469837881 (.More CT 136939675761 (.More CS10 68469837880 (.More CS10 34234918939 (.More CS00 17117459469 (.More CP0 34234918937 (.More CS00 17117459468 (.More CS10 8558729733 (.More CP1 17117459465 (.More CP1 34234918930 (.More CP0 68469837860 (.More CS10 34234918929 (.More CS00 17117459464 (.More CP0 34234918927 (.More CS00 17117459463 (.More CS00 8558729731 (.More CS01 4279364865 (.More CP1 8558729730 (.More CP1 17117459460 (.More CP1 34234918920 (.More CP0 68469837840 (.Stop 68469837840))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 16381 (.More CS10 8190 (.More CS10 4094 (.More CT 8185 (.More CT 16369 (.More CS10 8184 (.More CT 16365 (.More CS10 8182 (.More CT 16361 (.More CT 32721 (.More CT 65441 (.More CS10 32720 (.More CT 65437 (.More CT 130873 (.More CS10 65436 (.More CT 130869 (.More CS10 65434 (.More CS10 32716 (.More CT 65429 (.More CS10 32714 (.More CT 65425 (.More CS10 32712 (.More CT 65421 (.More CT 130841 (.More CS10 65420 (.More CT 130837 (.More CT 261673 (.More CS10 130836 (.More CT 261669 (.More CT 523337 (.More CT 1046673 (.More CT 2093345 (.More CT 4186689 (.More CT 8373377 (.More CS10 4186688 (.More CT 8373373 (.More CT 16746745 (.More CT 33493489 (.More CT 66986977 (.More CT 133973953 (.More CT 267947905 (.More CS10 133973952 (.More CS11 66986975 (.More CT 133973948 (.More CS01 66986974 (.More CT 133973946 (.More CS01 66986973 (.More CT 133973944 (.More CS01 66986972 (.More CT 133973942 (.More CT 267947883 (.More CT 535895765 (.More CT 1071791529 (.More CS10 535895764 (.More CS11 267947881 (.More CT 535895760 (.More CT 1071791519 (.More CT 2143583037 (.More CT 4287166073 (.More CT 8574332145 (.More CT 17148664289 (.More CT 34297328577 (.More CT 68594657153 (.More CT 137189314305 (.More CT 274378628609 (.More CS10 137189314304 (.More CP0 274378628607 (.More CT 548757257211 (.More CP1 1097514514423 (.More CT 2195029028844 (.More CT 4390058057687 (.More CT 8780116115373 (.More CS10 4390058057686 (.More CS10 2195029028842 (.More CT 4390058057681 (.More CP0 8780116115363 (.More CS01 4390058057681 (.More CT 8780116115360 (.More CT 17560232230719 (.More CT 35120464461437 (.More CT 70240928922873 (.More CS10 35120464461436 (.More CS10 17560232230717 (.More CS00 8780116115358 (.More CS10 4390058057678 (.More CS10 2195029028838 (.More CP0 4390058057675 (.More CS00 2195029028837 (.More CS00 1097514514418 (.More CP0 2195029028835 (.More CS01 1097514514417 (.More CP0 2195029028834 (.More CP0 4390058057667 (.More CS01 2195029028833 (.More CP1 4390058057666 (.More CP0 8780116115332 (.More CS10 4390058057665 (.More CS00 2195029028832 (.More CP0 4390058057663 (.More CS00 2195029028831 (.More CS00 1097514514415 (.More CP1 2195029028829 (.More CP1 4390058057658 (.More CP1 8780116115316 (.More CP1 17560232230632 (.More CP0 35120464461264 (.Stop 35120464461264)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
]
def loc_z3G : zW := [V,Q,Q,V,V,Q,V,Q,V,V,V,Q,V,V,Q,V,Q,Q,V,Q,V,Q,V,V,Q,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,Q,Q,V,K,V,K,V,K,V,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,Q,Q,V,V,K,V,V,V,V,Q,Q,K,Q,Q,V,K,K,V,K,V,V,K,V,V,Q,K,V,K,K,V,V,V,V,V]
def loc_z3H : zW := [Q,K,K,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,K,K,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def loc_z3I : zW := [K,K,K,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,K,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
set_option maxRecDepth 500000 in
lemma loc_z3J :
    ERounds 5 loc_z2Q 13 (loc_z3G ++ loc_z3H) := by
  have h1 : ERounds 5 loc_z2Q (5 + loc_z3F.length) (loc_z3G ++ loc_z3H) := by
    apply e_z2p loc_z3F
    decide
  simpa using! h1
set_option maxRecDepth 500000 in
lemma z3K :
    EGood 13 (loc_z3G ++ loc_z3H) := by
  apply e_z2s 13 loc_z3G loc_z3H loc_z3I
  · decide
  · exact EGuard.T 2 _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · norm_num [loc_z3G,loc_z3I,z1e,z1f,z1h]
lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep holdout_0549_tm c (j + d) = some c') :
    (multiStep holdout_0549_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep holdout_0549_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
lemma z3L (m : Nat) :
    ∃ N ≥ m,∃ h w,multiStep holdout_0549_tm (init []) N = some (zCf h (zTs w default)) /\ EGood h w := by
  induction m with
  | zero =>
    rcases loc_z3E with ⟨k1,_,hk1⟩
    rcases loc_z2P loc_z3J with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,13,loc_z3G ++ loc_z3H,
      zMt holdout_0549_tm _ _ _ k1 k2 hk1 hk2,z3K⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,h,w,h_ms,h_good⟩
    rcases e_z2d h_good with ⟨w',hStep,h_good'⟩
    rcases loc_z2O hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,h + 1,w',
      zMt holdout_0549_tm _ _ _ N k h_ms h_step_k,h_good'⟩
lemma holdout_0549_nonhalt :
    IsDoesNotHalt holdout_0549_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases z3L (n + 1) with ⟨N,hN,_,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := holdout_0549_nonhalt

end BusyBeaver.M_1RB0RA_1RC0RE_1RDHHH_1LE1LD_1LF0LD_1RA1LE
