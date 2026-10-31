/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LA---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LA---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LAHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LA---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
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
abbrev lh : zB := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
@[simp] lemma zDd : d0 +> (default : zB) = default := by
  simp [d0]
inductive Call where
  | ch
  | cj
  | cp
  | ca
def zCs : Call -> Fin 6
  | .ch => A
  | .cj => D
  | .cp => D
  | .ca => D
def zCw : Call -> zF
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
  | .ca => [1,1,1,0,1,1]
def zCR (l : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (r <{{zCs c}} (zCw c +> l))
def zCL (l : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  ((r <+ [0]) {{B}}> l)
def zCf (r : zB) : Cfg (Fin 2) (Fin 6) :=
  zCR lh .ca r
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
lemma z0b : Seg [.cp] [] t (t ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma z0c : Seg [.cj] [.cj] t t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0d : Seg [.ch] [.ch,.ch] t t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0e : Seg [.cp] [] (d1 ++ d0) (t ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d1 d0 t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma zH2 : Seg [.ch] [.cj,.ch] (t ++ one) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0f : Seg [.cj] [.cj] (d1 ++ d0) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1 d0; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0g : Seg [.cp] [.cp] (d1 ++ d1) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0h : Seg [.cj] [.cp,.ch] (d1 ++ d1) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0i : Seg [.cj] [] d0 (d0 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma zH1 : Seg [.ch] [] (d0 ++ one) (d1 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma zH3 : Seg [.ch] [.cj] (d1 ++ one) d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
lemma z0j : Seg [.cj] [.cp] d1 d0 :=
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
    exact zSg z0d ih
lemma zSa {w2 : zF} (hw : Seg [.ch,.ch] [.ch] w2 w2) (n : Nat) :
    Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) w2 w2 := by
  induction n with
  | zero => exact z0a w2
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq,z07,zLp]
    exact zSg hw ih
lemma z0k : Seg [.ch,.ch] [.ch] d0 d0 :=
  zSg zH0 zH4
lemma z0l : Seg [.ch,.ch] [.ch] d1 d1 :=
  zSg zH4 zH0
lemma z0m (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0b zH2) (zS3 n)
lemma z0n (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) t t :=
  zSg z0c (zS3 n)
lemma z0o (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0e zH2) (zS3 n)
lemma z0p (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0f (zS3 n)
lemma z0q (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0g (zS3 n)
lemma z0r (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using zSg z0h (zS3 n)
lemma z0s (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0i (zSg zH1 zH3)
  have h1 := zSg h0 (zSa z0k n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
lemma z0t (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0j (zSa z0k n)
lemma z0u : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0i zH1
lemma z0v (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0i (zSg zH1 (zSg zH3 zH0))
  have h1 := zSg h0 (zSa z0l n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
lemma z0w (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1 := zSg z0j zH0
  have h1 := zSg h0 (zSa z0l n)
  simpa only [zLp',List.cons_append,List.nil_append] using h1
lemma z0x : Seg [.ca] [.cj,.ch] [] t := by
  intro r1 r3 h
  rcases h with _ | ⟨hc1,hrest⟩
  rcases hrest with _ | ⟨hc2,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  have h1 : zCR l .ca ([] +> r1) = zCR ([1,0,1,1] +> l) .cj r1 := by
    unfold zCR zCw zCs; simp only [append_cons,append_nil]
  have h2 : ∀ r_mid,(zCL ([1,0,1,1] +> l) r_mid) [target_tm]⊢⁺ (zCR ([1,0,1,0] +> l) .ch r_mid) := by
    intro r_mid; unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute
  have h3 : (zCL ([1,0,1,0] +> l) r3) [target_tm]⊢⁺ (zCL l (t +> r3)) := by
    unfold zCL t; simp only [append_cons,append_nil]; execute
  rw [h1]
  exact zPt (hc1 ([1,0,1,1] +> l))
    (zPt (h2 _)
      (zPt (hc2 ([1,0,1,0] +> l)) h3))
lemma z0y (r : zB) :
    (zCL lh r) [target_tm]⊢⁺ (zCf r) := by
  unfold zCf zCL zCR lh zCw zCs
  simp only [append_cons,append_nil]
  execute
def z0z : zB :=
  t +> (t +> (t +> (d0 +> (d1 +> (t +> default)))))
lemma z0A :
    (init []) [target_tm]⊢⁺ (([0,0,1,0,1] +> default) {{B}}> ([0,1,1,1,0,1,0,1,0,1] +> default)) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]; simp only [append_cons,append_nil]; execute
lemma z0B :
    (([0,0,1,0,1] +> default) {{B}}> ([0,1,1,1,0,1,0,1,0,1] +> default)) [target_tm]⊢⁺
    (([0,1,0,0,0,0,1] +> default) {{B}}> ([1,0,1,1,1,0,1,0,1,0,1,1,1,0,1] +> default)) := by
  simp only [append_cons,append_nil]; execute
lemma z0C :
    (([0,1,0,0,0,0,1] +> default) {{B}}> ([1,0,1,1,1,0,1,0,1,0,1,1,1,0,1] +> default)) [target_tm]⊢⁺
    (([0,0,0,1,1] +> default) {{A}}> ([0,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1] +> default)) := by
  simp only [append_cons,append_nil]; execute
lemma z0D :
    (([0,0,0,1,1] +> default) {{A}}> ([0,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1] +> default)) [target_tm]⊢⁺
    zCf z0z := by
  unfold zCf zCR z0z lh zCw zCs t d0 d1
  simp only [append_cons,append_nil]
  execute
lemma z0E :
    (init []) [target_tm]⊢⁺ zCf z0z :=
  zPt z0A (zPt z0B (zPt z0C z0D))
inductive BRIncs : Nat -> zB -> zB -> Prop where
  | zero (r : zB) : BRIncs 0 r (one +> r)
  | T {n : Nat} {r r' : zB} :
      BRIncs (n * 2) r r' -> BRIncs (1 + n) (t +> r) (t +> r')
  | pair0 {n : Nat} {r r' : zB} :
      BRIncs (n * 2) r r' -> BRIncs (1 + n) (d1 +> (d0 +> r)) (t +> r')
  | pair1 {n : Nat} {r r' : zB} :
      BRIncs (1 + n * 2) r r' -> BRIncs (1 + n) (d1 +> (d1 +> r)) (t +> r')
  | short00 {n : Nat} {r r' : zB} :
      BRIncs (n * 2) r r' -> BRIncs (2 + n * 4) (d0 +> r) (d0 +> r')
  | short01 {n : Nat} {r r' : zB} :
      BRIncs (1 + n * 2) r r' -> BRIncs (2 + n * 4) (d1 +> r) (d0 +> r')
  | short10 {n : Nat} {r r' : zB} :
      BRIncs (n * 2) r r' -> BRIncs (4 + n * 4) (d0 +> r) (d1 +> r')
  | short11 {n : Nat} {r r' : zB} :
      BRIncs (1 + n * 2) r r' -> BRIncs (4 + n * 4) (d1 +> r) (d1 +> r')
inductive Binary : Nat -> Nat -> zB -> Prop where
  | one : Binary 1 1 (d1 +> default)
  | zero {n H : Nat} {r : zB} :
      Binary (1 + n) H r -> Binary (2 + n * 2) (1 + H) (d0 +> r)
  | two {n H : Nat} {r : zB} :
      Binary (1 + n) H r -> Binary (3 + n * 2) (1 + H) (d1 +> r)

open WordCalculus Word
local notation "zW" => List Word
local notation "zR" => List.replicate

lemma z0G {A H : Nat} {r : zB} (h : Binary A H r) :
    0 < A /\ 0 < H /\ 2 ^ H <= A * 2 /\ A < 2 ^ H := by
  induction h with
  | one => decide
  | @zero n H r _ ih =>
    rw [zP2 H]; omega
  | @two n H r _ ih =>
    rw [zP2 H]; omega

lemma z0H {A H : Nat} {r : zB} (h : Binary A H r) :
    BRIncs ((A - 1) * 2) default r := by
  induction h with
  | one =>
    have h0 := BRIncs.zero (default : zB)
    have hd : d1 +> (default : zB) = one +> default := by simp [d1,one]
    rw [hd]; exact h0
  | @zero n H r _ ih =>
    have ih' : BRIncs (n * 2) default r := by
      have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
      rwa [heq] at ih
    have hs := BRIncs.short00 ih'
    rw [zDd] at hs
    have heq : ((2 + n * 2) - 1) * 2 = 2 + n * 4 := by omega
    rwa [heq]
  | @two n H r _ ih =>
    have ih' : BRIncs (n * 2) default r := by
      have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
      rwa [heq] at ih
    have hs := BRIncs.short10 ih'
    rw [zDd] at hs
    have heq : ((3 + n * 2) - 1) * 2 = 4 + n * 4 := by omega
    rwa [heq]

lemma loc_z0X {A H : Nat} {u : zW} (h1 : zDg A H u) :
    ∀ {v : zW},zDg A H v -> u = v := by
  induction h1 with
  | nil =>
    intro v h2
    cases v with
    | nil => rfl
    | cons w v' =>
      cases w with
      | V => exact False.elim (z0X h2)
      | K =>
        rcases zD0 h2 with ⟨_,_,_,_,h⟩
        (try omega)
      | Q =>
        rcases zD1 h2 with ⟨_,_,_,_,h⟩
        (try omega)
  | @zero A H u _ ih =>
    intro v h2
    generalize hA_eq : A * 2 = A0 at h2
    generalize hH_eq : 1 + H = H0 at h2
    cases h2 with
    | nil => omega
    | @zero A' H' v' hD =>
      have hA : A = A' := by omega
      have hH : H = H' := by omega
      subst hA hH
      rw [ih hD]
    | one _ => omega
  | @one A H u _ ih =>
    intro v h2
    generalize hA_eq : 1 + A * 2 = A0 at h2
    generalize hH_eq : 1 + H = H0 at h2
    cases h2 with
    | nil => omega
    | zero _ => omega
    | @one A' H' v' hD =>
      have hA : A = A' := by omega
      have hH : H = H' := by omega
      subst hA hH
      rw [ih hD]

lemma loc_z1b {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (hI : Scan a (Q :: K :: u) b v l) :
    ∃ n w s,a = 1 + n /\ Scan (n * 2) u b w s /\ v = V :: w /\ l = (1 + s) * (1 / 2) := by
  cases hI with
  | @pair0 n _ _ w s hJ =>
    exact ⟨n,w,s,rfl,hJ,rfl,rfl⟩
  | @short01 n _ _ _ _ hJ =>
    exact False.elim (zSz n u b _ _ hJ)
  | @short11 n _ _ _ _ hJ =>
    exact False.elim (zSz n u b _ _ hJ)

inductive BScan : Nat -> zW -> Nat -> zW -> Rat -> Rat -> Prop where
  | nil (k : Nat) : BScan k [] k [] 0 0
  | T {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan (n * 2) u k v a b -> BScan (1 + n) (V :: u) k (V :: v) (a * (1 / 2)) (b * (1 / 2))
  | pair0 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan (n * 2) u k v a b -> BScan (1 + n) (Q :: K :: u) k (V :: v) (a * (1 / 2)) (b * (1 / 2))
  | pair1 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan (1 + n * 2) u k v a b -> BScan (1 + n) (Q :: Q :: u) k (V :: v) (a * (1 / 2)) ((1 / 4) + b * (1 / 2))
  | short00 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan (n * 2) u k v a b -> BScan (2 + n * 4) (K :: u) k (K :: v) (2 + a * 2) (b * 2)
  | short01 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan (1 + n * 2) u k v a b -> BScan (2 + n * 4) (Q :: u) k (K :: v) (1 + a * 2) (b * 2)
  | short10 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan (n * 2) u k v a b -> BScan (4 + n * 4) (K :: u) k (Q :: v) (3 + a * 2) (b * 2)
  | short11 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan (1 + n * 2) u k v a b -> BScan (4 + n * 4) (Q :: u) k (Q :: v) (2 + a * 2) (b * 2)

lemma loc_z1i {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : BScan k u k' v a b) :
    (k : Rat) - 2 = ((k' : Rat) - 2) * z1h v + 2 * (a - b) := by
  induction h with
  | nil k => simp [z1h]
  | T _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | pair0 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | pair1 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short00 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short01 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short10 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short11 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith

lemma loc_z1j {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : BScan k u k' v a b) :
    z1e v <= z1e u /\ 0 <= a /\ a <= 2 * z1e u + z1f u /\ 0 <= b /\
    z1e v + a - b - z1g v <= 2 * z1e u + z1f u := by
  induction h with
  | nil _ => simp [z1e,z1f,z1g]
  | @T n u k v a b _ ih =>
    have hw := zWn u; have hm := z1i u
    dsimp [z1e,z1f,z1g]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @pair0 n u k v a b _ ih =>
    have hw := zWn u; have hm := z1i u
    dsimp [z1e,z1f,z1g]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @pair1 n u k v a b _ ih =>
    have hw := zWn u; have hm := z1i u
    dsimp [z1e,z1f,z1g]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @short00 n u k v a b _ ih =>
    have hw := zWn u; have hm := z1i u
    dsimp [z1e,z1f,z1g]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @short01 n u k v a b _ ih =>
    have hw := zWn u; have hm := z1i u
    dsimp [z1e,z1f,z1g]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @short10 n u k v a b _ ih =>
    have hw := zWn u; have hm := z1i u
    dsimp [z1e,z1f,z1g]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @short11 n u k v a b _ ih =>
    have hw := zWn u; have hm := z1i u
    dsimp [z1e,z1f,z1g]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma loc_z1k {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h1 : BScan k u k' v a b) :
    ∀ {w : zW} {k'' : Nat} {x : zW} {c d : Rat},
      BScan k' w k'' x c d ->
      ∃ a' b',BScan k (u ++ w) k'' (v ++ x) a' b' /\
        a' = a + z1h v * c /\ b' = b + z1h v * d := by
  induction h1 with
  | nil _ =>
    intro w k'' x c d h2
    exact ⟨c,d,h2,by simp [z1h],by simp [z1h]⟩
  | T _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨a' * (1 / 2),b' * (1 / 2),BScan.T hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | pair0 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨a' * (1 / 2),b' * (1 / 2),BScan.pair0 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | pair1 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨a' * (1 / 2),(1 / 4) + b' * (1 / 2),BScan.pair1 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short00 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨2 + a' * 2,b' * 2,BScan.short00 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short01 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨1 + a' * 2,b' * 2,BScan.short01 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short10 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨3 + a' * 2,b' * 2,BScan.short10 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short11 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨2 + a' * 2,b' * 2,BScan.short11 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩

lemma loc_z1l {e : Bool} {u : zW} (hI : zPr e u) :
    ∀ (k : Nat),(e = true -> ∃ n,k = n * 2) ->
      6 * z1e u < (k : Rat) - 2 ->
      ∃ b v lp lm,BScan k u b v lp lm /\ 2 < b := by
  induction hI with
  | nil e =>
    intro k _ hk
    dsimp [z1e] at hk
    have hk_gt : (2 : Rat) < (k : Rat) := by linarith
    have hk_nat : 2 < k := by exact_mod_cast hk_gt
    exact ⟨k,[],0,0,BScan.nil k,hk_nat⟩
  | @T e u _ ih =>
    intro k _ hk
    have hw := zWn u
    dsimp [z1e] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (k * 2) (fun _ => ⟨k,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      exact ⟨b,V :: v,lp * (1 / 2),lm * (1 / 2),BScan.T hS,hB⟩
  | @short0 u _ ih =>
    intro k hEk hk
    have hw := zWn u
    dsimp [z1e] at hk
    rcases hEk rfl with ⟨n,rfl⟩
    rcases z0U n with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (a * 2) (fun _ => ⟨a,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
        refine ⟨b,Q :: v,3 + lp * 2,lm * 2,?_,hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact BScan.short10 hS
    · rcases ih (a * 2) (fun _ => ⟨a,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      refine ⟨b,K :: v,2 + lp * 2,lm * 2,?_,hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact BScan.short00 hS
  | @short1 u _ ih =>
    intro k hEk hk
    have hw := zWn u
    dsimp [z1e] at hk
    rcases hEk rfl with ⟨n,rfl⟩
    rcases z0U n with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (1 + a * 2) (fun h => by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
        refine ⟨b,Q :: v,2 + lp * 2,lm * 2,?_,hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact BScan.short11 hS
    · rcases ih (1 + a * 2) (fun h => by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      refine ⟨b,K :: v,1 + lp * 2,lm * 2,?_,hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact BScan.short01 hS
  | @pair0 e u _ ih =>
    intro k _ hk
    have hw := zWn u
    dsimp [z1e] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (k * 2) (fun _ => ⟨k,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      exact ⟨b,V :: v,lp * (1 / 2),lm * (1 / 2),BScan.pair0 hS,hB⟩
  | @pair1 e u _ ih =>
    intro k _ hk
    have hw := zWn u
    dsimp [z1e] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (1 + k * 2) (fun h => by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      exact ⟨b,V :: v,lp * (1 / 2),(1 / 4) + lm * (1 / 2),BScan.pair1 hS,hB⟩

lemma loc_z1m (u : zW) (k : Nat) (h : 6 * z1e u < ((k * 2 : Nat) : Rat) - 2) :
    ∃ b v lp lm,BScan (k * 2) u b v lp lm /\ 2 < b :=
  loc_z1l (z0W u).1 (k * 2) (fun _ => ⟨k,rfl⟩) h

lemma loc_z1n {k : Nat} {u : zW} {k' : Nat} {v : zW} {l : Rat}
    (hI : Scan k u k' v l) :
    ∀ {A H : Nat},zDg A H u ->
      ∃ a b,BScan k u k' v a b /\ a <= 2 * z1e v + l /\ b <= l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0,0,BScan.nil k,by simp [z1e],by linarith⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (z0X hD)
  | pair0 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD0 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨a * (1 / 2),b * (1 / 2),BScan.pair0 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD1 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨a * (1 / 2),(1 / 4) + b * (1 / 2),BScan.pair1 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨2 + a * 2,b * 2,BScan.short00 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨1 + a * 2,b * 2,BScan.short01 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨3 + a * 2,b * 2,BScan.short10 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨2 + a * 2,b * 2,BScan.short11 hJ,by dsimp [z1e]; linarith,by linarith⟩

lemma loc_z1o {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : BScan k u k' v a b) :
    ∀ {A H : Nat},zDg A H u ->
      ∃ l,Scan k u k' v l /\ a <= 2 * z1e v + l /\ b <= l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0,Scan.nil k,by simp [z1e],by linarith⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (z0X hD)
  | pair0 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD0 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hP,hM⟩
    exact ⟨(1 + l) * (1 / 2),Scan.pair0 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD1 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hP,hM⟩
    exact ⟨(1 / 4) + l * (1 / 2),Scan.pair1 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨1 + l * 2,Scan.short00 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨l * 2,Scan.short01 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨1 + l * 2,Scan.short10 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨l * 2,Scan.short11 hJ,by dsimp [z1e]; linarith,by linarith⟩

lemma loc_z1p {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : BScan k u k' v a b) : z1h v <= z1h u := by
  induction h with
  | nil _ => simp [z1h]
  | T _ ih => dsimp [z1h]; linarith
  | @pair0 _ u _ _ _ _ _ _ => have hp := zSp u; dsimp [z1h]; linarith
  | @pair1 _ u _ _ _ _ _ _ => have hp := zSp u; dsimp [z1h]; linarith
  | short00 _ ih => dsimp [z1h]; linarith
  | short01 _ ih => dsimp [z1h]; linarith
  | short10 _ ih => dsimp [z1h]; linarith
  | short11 _ ih => dsimp [z1h]; linarith

lemma loc_z1q {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : BScan k u k' v a b) :
    ∀ (p q : zW),u = p ++ q -> z10 p q ->
      ∃ m x y a1 b1 a2 b2,BScan k p m x a1 b1 /\ BScan m q k' y a2 b2 /\
        v = x ++ y /\ a = a1 + z1h x * a2 /\ b = b1 + z1h x * b2 := by
  induction h with
  | nil k =>
    intro p q hE _
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨k,[],[],0,0,0,0,BScan.nil k,BScan.nil k,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p => simp at hE
  | T hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.T hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt V p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,V :: x,y,a1 * (1 / 2),b1 * (1 / 2),a2,b2,BScan.T hJ,hK,rfl,
        by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | pair0 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.pair0 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := zCt K p q (zCt Q (K :: p) q hP)
        rcases ih p q hE hP' with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
        exact ⟨m,V :: x,y,a1 * (1 / 2),b1 * (1 / 2),a2,b2,BScan.pair0 hJ,hK,rfl,
          by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | pair1 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.pair1 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := zCt Q p q (zCt Q (Q :: p) q hP)
        rcases ih p q hE hP' with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
        exact ⟨m,V :: x,y,a1 * (1 / 2),(1 / 4) + b1 * (1 / 2),a2,b2,BScan.pair1 hJ,hK,rfl,
          by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | short00 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.short00 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt K p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,K :: x,y,2 + a1 * 2,b1 * 2,a2,b2,BScan.short00 hJ,hK,rfl,
        by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | short01 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.short01 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt Q p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,K :: x,y,1 + a1 * 2,b1 * 2,a2,b2,BScan.short01 hJ,hK,rfl,
        by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | short10 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.short10 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt K p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,Q :: x,y,3 + a1 * 2,b1 * 2,a2,b2,BScan.short10 hJ,hK,rfl,
        by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | short11 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.short11 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt Q p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,Q :: x,y,2 + a1 * 2,b1 * 2,a2,b2,BScan.short11 hJ,hK,rfl,
        by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩

lemma loc_z1r (r k : Nat) (u : zW) (k' : Nat) (v : zW) (a b : Rat)
    (hI : BScan k (u ++ zR (1 + r * 2) Q ++ [K]) k' v a b) :
    ∃ w n,v = w ++ zR (1 + r) V /\ k' = n * 2 ^ (1 + r) := by
  rcases z14 u with ⟨p,n,rfl,hP⟩
  have hE : (p ++ zR n Q) ++ zR (1 + r * 2) Q ++ [K] =
      p ++ (zR (1 + r * 2 + n) Q ++ [K]) := by
    have heq : 1 + r * 2 + n = n + (1 + r * 2) := by omega
    rw [heq,List.replicate_add n (1 + r * 2)]; simp only [List.append_assoc]
  rw [hE] at hI
  rcases loc_z1q hI p (zR (1 + r * 2 + n) Q ++ [K]) rfl (Or.inl hP)
    with ⟨m,x,y,_,_,_,_,_,hK,rfl,_,_⟩
  have hD : zDg ((2 ^ (1 + r * 2 + n) - 1) + 0 * 2 ^ (1 + r * 2 + n)) ((1 + r * 2 + n) + 1)
      (zR (1 + r * 2 + n) Q ++ [K]) :=
    z19 (z1a (1 + r * 2 + n)) (zDg.zero zDg.nil)
  rcases loc_z1o hK hD with ⟨l,hL,_,_⟩
  rcases z1s n r m k' y l hL with ⟨w,q,rfl,rfl⟩
  exact ⟨x ++ w,q,by rw [List.append_assoc],rfl⟩

lemma loc_z1s {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : BScan k u k' v a b) :
    ∀ {A H : Nat},zDg A H u ->
      ∃ l,Scan k u k' v l /\ a - b - z1g v <= z1e v + l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0,Scan.nil k,by simp [z1e,z1g]⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (z0X hD)
  | pair0 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD0 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hL⟩
    exact ⟨(1 + l) * (1 / 2),Scan.pair0 hJ,by dsimp [z1e,z1g]; linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD1 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hL⟩
    exact ⟨(1 / 4) + l * (1 / 2),Scan.pair1 hJ,by dsimp [z1e,z1g]; linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨1 + l * 2,Scan.short00 hJ,by dsimp [z1e,z1g]; linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨l * 2,Scan.short01 hJ,by dsimp [z1e,z1g]; linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨1 + l * 2,Scan.short10 hJ,by dsimp [z1e,z1g]; linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨l * 2,Scan.short11 hJ,by dsimp [z1e,z1g]; linarith⟩

lemma loc_z1t {k : Nat} {ds : zW} {k' : Nat} {v : zW} {l : Rat}
    (hI : Scan k (ds ++ [K]) k' v l)
    (hLow : ∃ w,ds = Q :: K :: w)
    (hDig : ∃ A H,zDg A H ds) :
    z1e v <= z1f ds * (1 / 4) /\ z1e v + l <= z1f ds * (1 / 2) + (1 / 2) := by
  rcases hLow with ⟨w,rfl⟩
  rcases hDig with ⟨A,H,hD⟩
  rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
  rcases zD0 hD1 with ⟨A2,H2,hK,_,_⟩
  change Scan k (Q :: K :: (w ++ [K])) k' v l at hI
  rcases loc_z1b hI with ⟨n,x,s,_,hJ,rfl,hL⟩
  rcases z1x hJ (z1v hK) with ⟨hM,hS,_⟩
  dsimp [z1f,z1e]
  constructor <;> linarith

lemma loc_z1u {k : Nat} {ds : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : BScan k (ds ++ [K]) k' v a b)
    (hLow : ∃ w,ds = Q :: K :: w)
    (hDig : ∃ A H,zDg A H ds) :
    z1e v <= z1f ds * (1 / 4) /\ a <= z1f ds /\
    z1e v + a - b - z1g v <= z1f ds := by
  rcases hDig with ⟨A,H,hD⟩
  have hFull := z19 hD (zDg.zero zDg.nil)
  rcases loc_z1o hI hFull with ⟨l,hJ,hP,_⟩
  rcases loc_z1s hI hFull with ⟨l',hJ',hE⟩
  rcases loc_z1t hJ hLow ⟨A,H,hD⟩ with ⟨hM1,hL1⟩
  rcases loc_z1t hJ' hLow ⟨A,H,hD⟩ with ⟨_,hL2⟩
  rcases hLow with ⟨w,rfl⟩
  have hw := zWn w
  dsimp [z1f] at hM1 hL1 hL2 ⊢
  refine ⟨by linarith,by linarith,by linarith⟩

lemma loc_z1v {u : zW} {A H : Nat} {ds : zW} (hDig : zDg A H ds)
    (hHeight : z1h u * ((2 ^ H : Nat) : Rat) = 1 / 2)
    (hPhi : 3 * z1e u + z1f u + z1h u * z1f ds <= 1 / 64)
    (hLow : ∃ w,ds = Q :: K :: w) :
    ∃ k v a b,BScan 4 (u ++ ds ++ [K]) k v a b /\ 2 < k /\
      a <= 2 * z1e u + z1f u + z1h u * z1f ds /\
      z1e v <= z1e u + z1h u * z1f ds * (1 / 4) /\
      z1e v + a - b - z1g v <= 2 * z1e u + z1f u + z1h u * z1f ds := by
  have hWu := zWn u
  have hWd := zWn ds
  have hSu := zSp u
  have hSmall : 6 * z1e u < ((2 * 2 : Nat) : Rat) - 2 := by
    push_cast; nlinarith
  rcases loc_z1m u 2 hSmall with ⟨m,x,a1,b1,hI,hPos⟩
  have hBudget := loc_z1i hI
  have hBounds := loc_z1j hI
  have hGain := loc_z1p hI
  have hSx := zSp x
  have hCarry : 1 < (m : Rat) * z1h x := by
    push_cast at hBudget; nlinarith
  rcases hLow with ⟨w,hEq⟩
  have hRest : (z1e (w ++ [K]) + z1f (w ++ [K]) + 2) * z1h x <= 1 := by
    have hDs := (zDw hDig).1
    rw [<- hDs] at hHeight
    rw [hEq] at hDig hHeight
    dsimp [z1h] at hHeight
    rcases zD1 hDig with ⟨A1,H1,hD1,_,_⟩
    rcases zD0 hD1 with ⟨A2,H2,hJw,_,_⟩
    rcases zDw hJw with ⟨hDw,hMw,_⟩
    have hWw := zWn w
    have hMsw := z1i w
    have hSw := zSp w
    rw [z1j,z1k]
    dsimp [z1e,z1f]
    nlinarith
  cases m with
  | zero => omega
  | succ m =>
    have hEx_w : (z1e (w ++ [K]) + z1f (w ++ [K])) * 2 < ((m * 2 : Nat) : Rat) := by
      push_cast at hCarry ⊢; nlinarith
    rcases z1q (w ++ [K]) m hEx_w with ⟨k,y,l,hJ,_⟩
    have hCore : Scan (m + 1) (ds ++ [K]) k (V :: y) ((1 + l) * (1 / 2)) := by
      rw [hEq]
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      exact Scan.pair0 hJ
    have hFull := z19 hDig (zDg.zero zDg.nil)
    rcases loc_z1n hCore hFull with ⟨a2,b2,hJ',_,_⟩
    rcases loc_z1k hI hJ' with ⟨a,b,hIJ,hAp,hBp⟩
    rcases loc_z1u hJ' ⟨w,hEq⟩ ⟨A,H,hDig⟩ with ⟨hMt,hAt,hEt⟩
    have hIJ' : BScan 4 (u ++ ds ++ [K]) k (x ++ V :: y) a b := by
      simpa [List.append_assoc] using hIJ
    have hAfull : a <= 2 * z1e u + z1f u + z1h u * z1f ds := by
      nlinarith
    have hPositive : 2 < k := by
      have hB := loc_z1i hIJ
      have hF := loc_z1j hIJ
      have hS := zSp (x ++ V :: y)
      have hk_gt : (2 : Rat) < (k : Rat) := by
        push_cast at hB; nlinarith
      exact_mod_cast hk_gt
    refine ⟨k,x ++ V :: y,a,b,hIJ',hPositive,hAfull,?_,?_⟩
    · rw [z1j]; nlinarith
    · rw [z1j,z1l]; nlinarith

lemma loc_z1w (p : Nat) :
    ∀ (k k' : Nat) (v : zW) (a b : Rat),
      BScan k (zR p V) k' v a b ->
      v = zR p V /\ k' + 2 * 2 ^ p = k * 2 ^ p + 2 /\ a = 0 /\ b = 0 := by
  induction p with
  | zero =>
    intro k k' v a b hI
    cases hI
    exact ⟨rfl,by simp,rfl,rfl⟩
  | succ p ih =>
    intro k k' v a b hI
    cases hI with
    | @T n _ _ v0 a0 b0 hJ =>
      rcases ih (n * 2) k' v0 a0 b0 hJ with ⟨rfl,hEq,rfl,rfl⟩
      refine ⟨rfl,?_,by ring,by ring⟩
      calc k' + 2 * 2 ^ (p + 1)
        _ = (k' + 2 * 2 ^ p) + 2 * 2 ^ p := by rw [Nat.pow_succ]; ring
        _ = (n * 2 * 2 ^ p + 2) + 2 * 2 ^ p := by rw [hEq]
        _ = (1 + n) * 2 ^ (p + 1) + 2 := by rw [Nat.pow_succ]; ring

lemma loc_z1y (u : zW) :
    ∀ (v : zW) (h H : Nat),zHn (u ++ v) h = some H ->
      ∃ j,zHn u h = some j /\ zHn v j = some H := by
  induction u with
  | nil =>
    intro v h H hE
    exact ⟨h,rfl,hE⟩
  | cons w u ih =>
    intro v h H hE
    cases w with
    | V => exact ih v (h + 1) H hE
    | K =>
      cases h with
      | zero => contradiction
      | succ h => exact ih v h H hE
    | Q =>
      cases h with
      | zero => contradiction
      | succ h => exact ih v h H hE

lemma loc_z1z (n : Nat) :
    ∀ (h : Nat),zHn (zR n V) h = some (h + n) := by
  induction n with
  | zero => intro h; simp [zHn]
  | succ n ih =>
    intro h
    dsimp [List.replicate,zHn]
    rw [ih (h + 1)]
    congr 1; omega

lemma loc_z1A (u : zW) (n h H : Nat)
    (hE : zHn (u ++ zR n V) h = some H) : n <= H := by
  rcases loc_z1y u (zR n V) h H hE with ⟨j,_,hJ⟩
  rw [loc_z1z] at hJ
  injection hJ with hJ
  (try omega)

lemma loc_z1B (u : zW) :
    ∀ (h : Nat),z1e u < ((2 ^ h : Nat) : Rat) -> ∃ H,zHn u h = some H := by
  induction u with
  | nil => intro h _; exact ⟨h,rfl⟩
  | cons w u ih =>
    intro h hM
    cases w with
    | V =>
      dsimp [z1e,zHn] at hM ⊢
      apply ih (h + 1)
      rw [Nat.pow_succ]; push_cast at hM ⊢; linarith
    | K =>
      cases h with
      | zero =>
        have hw := (zWn u).1
        dsimp [z1e] at hM; linarith
      | succ h =>
        dsimp [z1e,zHn] at hM ⊢
        apply ih h
        rw [Nat.pow_succ] at hM; push_cast at hM ⊢; linarith
    | Q =>
      cases h with
      | zero =>
        have hw := (zWn u).1
        dsimp [z1e] at hM; linarith
      | succ h =>
        dsimp [z1e,zHn] at hM ⊢
        apply ih h
        rw [Nat.pow_succ] at hM; push_cast at hM ⊢; linarith

lemma loc_z1C {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : BScan k u k' v a b) :
    ∀ (h H : Nat),zHn v h = some H -> k < 2 ^ (1 + h) -> k' < 2 ^ (1 + H) := by
  induction hI with
  | nil k =>
    intro h H hHeight hBound
    injection hHeight with hEq; subst hEq; exact hBound
  | T _ ih =>
    intro h H hHeight hBound
    apply ih (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,zP2 (1 + h)]; omega
  | pair0 _ ih =>
    intro h H hHeight hBound
    apply ih (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,zP2 (1 + h)]; omega
  | pair1 _ ih =>
    intro h H hHeight hBound
    apply ih (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,zP2 (1 + h)]; omega
  | short00 _ ih =>
    intro h H hHeight hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply ih h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,zP2 (1 + h),zP2 h] at hBound
      rw [zP2 h]; omega
  | short01 _ ih =>
    intro h H hHeight hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply ih h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,zP2 (1 + h),zP2 h] at hBound
      rw [zP2 h]; omega
  | short10 _ ih =>
    intro h H hHeight hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply ih h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,zP2 (1 + h),zP2 h] at hBound
      rw [zP2 h]; omega
  | short11 _ ih =>
    intro h H hHeight hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply ih h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,zP2 (1 + h),zP2 h] at hBound
      rw [zP2 h]; omega

lemma loc_z1D {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : BScan k u k' v a b) :
    ∀ (h H : Nat),zHn v h = some H -> u ≠ [] -> k <= 2 ^ (1 + h) -> k' < 2 ^ (1 + H) := by
  cases hI with
  | nil _ => intro _ _ _ hNe _; exact False.elim (hNe rfl)
  | T hSub =>
    intro h H hHeight _ hBound
    apply loc_z1C hSub (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,zP2 (1 + h)]; omega
  | pair0 hSub =>
    intro h H hHeight _ hBound
    apply loc_z1C hSub (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,zP2 (1 + h)]; omega
  | pair1 hSub =>
    intro h H hHeight _ hBound
    apply loc_z1C hSub (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,zP2 (1 + h)]; omega
  | short00 hSub =>
    intro h H hHeight _ hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply loc_z1C hSub h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,zP2 (1 + h),zP2 h] at hBound
      rw [zP2 h]; omega
  | short01 hSub =>
    intro h H hHeight _ hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply loc_z1C hSub h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,zP2 (1 + h),zP2 h] at hBound
      rw [zP2 h]; omega
  | short10 hSub =>
    intro h H hHeight _ hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply loc_z1C hSub h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,zP2 (1 + h),zP2 h] at hBound
      rw [zP2 h]; omega
  | short11 hSub =>
    intro h H hHeight _ hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply loc_z1C hSub h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,zP2 (1 + h),zP2 h] at hBound
      rw [zP2 h]; omega

def loc_z1E (u : zW) : Prop :=
  ∃ p w,u = zR (1 + p) V ++ K :: w

lemma loc_z1F (u v : zW) (h : loc_z1E u) : loc_z1E (u ++ v) := by
  rcases h with ⟨p,w,rfl⟩
  exact ⟨p,w ++ v,by simp [List.append_assoc]⟩

lemma loc_z1G (p : Nat) (u : zW) (k : Nat) (v : zW) (a b : Rat)
    (hI : BScan 4 (zR (1 + p) V ++ K :: u) k v a b) :
    ∃ w a' b',v = zR (1 + p) V ++ K :: w /\ BScan (2 ^ (1 + p)) u k w a' b' := by
  rcases loc_z1q hI (zR (1 + p) V) (K :: u) rfl (Or.inl (z12 (1 + p)))
    with ⟨m,x,y,_,_,_,_,hJ,hK,rfl,_,_⟩
  rcases loc_z1w (1 + p) 4 m x _ _ hJ with ⟨rfl,hEq,_,_⟩
  have hm : m = 2 + 2 ^ (1 + p) * 2 := by
    rw [zP2 p] at hEq ⊢; omega
  cases hK with
  | @short00 n _ _ w0 a0 b0 hSub =>
    have hn : n * 2 = 2 ^ (1 + p) := by
      rw [zP2 p] at hm ⊢; omega
    rw [hn] at hSub
    exact ⟨w0,a0,b0,rfl,hSub⟩
  | @short10 n _ _ _ _ _ _ =>
    rw [zP2 p] at hm; omega

lemma loc_z1H (p : Nat) (u : zW) : z0Y (zR p V ++ u) = z0Y u := by
  induction p with
  | zero => rfl
  | succ p ih => exact ih

lemma loc_z1J {orig : zW} {k : Nat} {v : zW} {a b : Rat} {J : Nat}
    (hI : BScan 4 orig k v a b) (hGu : loc_z1E orig) (hPair : z0Y orig = true)
    (hHeight : zHn v 0 = some J) :
    loc_z1E (V :: v) /\ k < 2 ^ (1 + J) := by
  rcases hGu with ⟨p,u,rfl⟩
  rcases loc_z1G p u k v a b hI with ⟨w,a',b',rfl,hS⟩
  refine ⟨⟨1 + p,w,?_⟩,?_⟩
  · have hrep : zR (1 + (1 + p)) V = V :: zR (1 + p) V := by
      rw [Nat.add_comm 1 (1 + p),List.replicate_succ]
    rw [hrep,List.cons_append]
  · have hH : zHn w p = some J := by
      rcases loc_z1y (zR (1 + p) V) (K :: w) 0 J hHeight with ⟨j,h1,h2⟩
      rw [loc_z1z] at h1
      injection h1 with h1; subst h1
      have hp : 0 + (1 + p) = p + 1 := by omega
      rw [hp] at h2
      exact h2
    have hNe : u ≠ [] := by
      intro hEmpty
      subst hEmpty
      rw [loc_z1H] at hPair
      contradiction
    exact loc_z1D hS p J hH hNe (by omega)

lemma loc_z1K {n H : Nat} {ds : zW} (hD : zDg (1 + n * 4) H ds) (hH : 2 <= H) :
    ∃ w,ds = Q :: K :: w := by
  generalize hA_eq : 1 + n * 4 = A at hD
  cases hD with
  | nil => omega
  | zero _ => omega
  | @one A1 H1 u1 hD1 =>
    have hA1 : A1 = n * 2 := by omega
    subst hA1
    generalize hA1_eq : n * 2 = A1' at hD1
    cases hD1 with
    | nil => omega
    | @zero A2 H2 w _ => exact ⟨w,rfl⟩
    | one _ => omega

lemma loc_z1M {B H : Nat} {ds : zW} {unit : Rat}
    (hD : zDg B H ds) (hU : 0 < unit)
    (hHeight : unit * ((2 ^ H : Nat) : Rat) = 1)
    (hZ : 2 <= z1f ds)
    (hSmall : unit * (1 + z1f ds) <= 1 / 64) :
    ∃ rest,ds = rest ++ zR 6 Q := by
  have hH6 : 6 <= H := by
    by_contra hlt
    have hle : H <= 5 := by omega
    have hpow_le : 2 ^ H <= 32 := by
      calc 2 ^ H <= 2 ^ 5 := Nat.pow_le_pow_right (by decide) hle
      _ = 32 := by decide
    have hpow_q : ((2 ^ H : Nat) : Rat) <= 32 := by exact_mod_cast hpow_le
    nlinarith
  have hShift : unit * ((2 ^ (H - 6) : Nat) : Rat) = 1 / 64 := by
    have heq : H = (H - 6) + 6 := by omega
    have hpow : 2 ^ H = 2 ^ (H - 6) * 64 := by
      rw [heq,Nat.pow_add]; rfl
    have hpow_q : ((2 ^ H : Nat) : Rat) = ((2 ^ (H - 6) : Nat) : Rat) * 64 := by
      exact_mod_cast hpow
    rw [hpow_q] at hHeight
    linarith
  have hEq := z1n hD
  have hH_split : (H - 6) + 6 = H := by omega
  have hD' : zDg B ((H - 6) + 6) ds := by rwa [hH_split]
  apply z21 (H - 6) 6 B ds hD'
  have hL_q : ((2 ^ ((H - 6) + 6) : Nat) : Rat) <= ((B + 2 ^ (H - 6) : Nat) : Rat) := by
    rw [hH_split]
    push_cast at hEq hShift ⊢
    nlinarith
  exact_mod_cast hL_q

inductive BGood : zW -> Prop where
  | intro (H : Nat) (u : zW) (A : Nat) (ds : zW) :
      zDg A H ds ->
      z1h u * ((2 ^ H : Nat) : Rat) = 1 / 2 ->
      loc_z1E u ->
      (∃ w,u = w ++ [V]) ->
      (∃ w,ds = Q :: K :: w) ->
      (∃ w,ds = w ++ zR 6 Q) ->
      3 * z1e u + z1f u + z1h u * z1f ds <= 1 / 64 ->
      BGood (u ++ ds)

inductive BStep : zW -> zW -> Prop where
  | intro (orig : zW) (n : Nat) (v : zW) (a b : Rat) (J : Nat) (ds : zW) :
      BScan 4 (orig ++ [K]) (n * 2) v a b ->
      zDg (1 + n) J ds ->
      BStep orig (V :: (v ++ ds))

lemma loc_z1N {orig : zW} (hG : BGood orig) :
    ∃ out,BStep orig out /\ BGood out := by
  rcases hG with ⟨H,u,A,ds,hDig,hHeight,hGu,_,hLow,hHigh,hPhi⟩
  have hWu := zWn u
  have hWd := zWn ds
  have hSu := zSp u
  rcases loc_z1v hDig hHeight hPhi hLow with ⟨k,v,a,b,hI,_,hAp,hMass,hEnergy⟩
  have hMassSmall : z1e v < 1 := by nlinarith
  have hMassSmall0 : z1e v < ((2 ^ 0 : Nat) : Rat) := by push_cast; exact hMassSmall
  rcases loc_z1B v 0 hMassSmall0 with ⟨J,hHv⟩
  have hUnit := z2e v 0 J hHv
  have hUnit1 : z1h v * ((2 ^ J : Nat) : Rat) = 1 := by
    have h20 : ((2 ^ 0 : Nat) : Rat) = 1 := rfl
    rwa [h20] at hUnit
  rcases hHigh with ⟨hi,hHi⟩
  have hIH : BScan 4 ((u ++ hi ++ [Q]) ++ zR (1 + 2 * 2) Q ++ [K]) k v a b := by
    have h6 : zR 6 Q = [Q] ++ zR (1 + 2 * 2) Q := rfl
    rw [hHi,h6] at hI
    simpa [List.append_assoc] using hI
  rcases loc_z1r 2 4 (u ++ hi ++ [Q]) k v a b hIH with ⟨last,n,hV,rfl⟩
  have hJ3 : 3 <= J := by
    apply loc_z1A last 3 0 J
    rw [<- hV]; exact hHv
  have hPair : z0Y (u ++ ds ++ [K]) = true := by
    rcases hLow with ⟨w,rfl⟩
    have h10 : z0Y (Q :: K :: w ++ [K]) = true := rfl
    have heq : u ++ (Q :: K :: w) ++ [K] = u ++ (Q :: K :: w ++ [K]) := by simp [List.append_assoc]
    rw [heq]
    exact e_z27 u _ h10
  rcases loc_z1J hI (loc_z1F (u ++ ds) [K] (loc_z1F u ds hGu)) hPair hHv with ⟨hGuardV,hUpper⟩
  have hPow : 2 ^ J = 8 * 2 ^ (J - 3) := by
    have heq : J = 3 + (J - 3) := by omega
    conv_lhs => rw [heq,Nat.pow_add]
  have hPow1 : 2 ^ (1 + J) = 16 * 2 ^ (J - 3) := by
    have heq : 1 + J = 4 + (J - 3) := by omega
    conv_lhs => rw [heq,Nat.pow_add]
  have hBound : 1 + n * 4 < 2 ^ J := by
    rw [hPow1] at hUpper
    rw [hPow]
    have : n * (2 ^ (1 + 2)) = n * 8 := rfl
    (try omega)
  rcases z18 J (1 + n * 4) hBound with ⟨ds',hD'⟩
  have hLow' : ∃ w,ds' = Q :: K :: w := loc_z1K hD' (by omega)
  have hDef := z1n hD'
  have hBudget := loc_z1i hI
  have hDeficit : z1h v * z1f ds' = a - b - 3 * z1h v := by
    have h1n4 : ((1 + n * 4 : Nat) : Rat) = 1 + (n : Rat) * 4 := by push_cast; ring
    have hn8 : ((n * 2 ^ (1 + 2) : Nat) : Rat) = (n : Rat) * 8 := by push_cast; ring
    have h4 : ((4 : Nat) : Rat) = 4 := rfl
    rw [h1n4] at hDef
    rw [hn8,h4] at hBudget
    have hSv_def : z1h v * (z1f ds' + (1 + (n : Rat) * 4) + 1) = 1 := by
      rw [hDef]; exact hUnit1
    nlinarith
  have hPhiNew : 3 * z1e (V :: v) + z1f (V :: v) + z1h (V :: v) * z1f ds' <=
      (7 / 8) * (3 * z1e u + z1f u + z1h u * z1f ds) := by
    have hSv := zSp v
    have hSplit := z1i v
    dsimp [z1e,z1f,z1h]
    nlinarith
  have hHigh' : ∃ w,ds' = w ++ zR 6 Q := by
    refine loc_z1M hD' (zSp v) hUnit1 ?_ ?_
    · rcases hLow' with ⟨w,rfl⟩
      have hw := zWn w
      dsimp [z1f]; linarith
    · have hBnd := loc_z1j hI
      have hSv := zSp v
      nlinarith
  refine ⟨V :: (v ++ ds'),?_,?_⟩
  · refine BStep.intro (u ++ ds) (n * 4) v a b J ds' ?_ hD'
    have heq : (n * 4) * 2 = n * 2 ^ (1 + 2) := by ring
    rw [heq]
    simpa [List.append_assoc] using hI
  · have hOut_eq : V :: (v ++ ds') = (V :: v) ++ ds' := rfl
    rw [hOut_eq]
    refine BGood.intro J (V :: v) (1 + n * 4) ds' hD' ?_ hGuardV ?_ hLow' hHigh' (by linarith)
    · dsimp [z1h]; linarith
    · refine ⟨V :: (last ++ [V,V]),?_⟩
      rw [hV]; simp [List.replicate,List.append_assoc]

lemma loc_z1O {a : Nat} {u : zW} {b : Nat} {v : zW} {lp lm : Rat}
    (h : BScan a u b v lp lm) :
    ∀ {r r' : zB},BRIncs b r r' -> BRIncs a (zTs u r) (zTs v r') := by
  induction h with
  | nil _ => intro r r' hR; exact hR
  | T _ ih => intro r r' hR; exact BRIncs.T (ih hR)
  | pair0 _ ih => intro r r' hR; exact BRIncs.pair0 (ih hR)
  | pair1 _ ih => intro r r' hR; exact BRIncs.pair1 (ih hR)
  | short00 _ ih => intro r r' hR; exact BRIncs.short00 (ih hR)
  | short01 _ ih => intro r r' hR; exact BRIncs.short01 (ih hR)
  | short10 _ ih => intro r r' hR; exact BRIncs.short10 (ih hR)
  | short11 _ ih => intro r r' hR; exact BRIncs.short11 (ih hR)

lemma loc_z1P {A H : Nat} {da : zW} (hD : zDg A H da) (hZ : A = 0) :
    zTs da default = default := by
  induction hD with
  | nil => rfl
  | @zero A H u _ ih =>
    have hA0 : A = 0 := by omega
    change d0 +> zTs u default = default
    rw [ih hA0,zDd]
  | one _ => omega

lemma loc_z1Q {A H : Nat} {da : zW} (hD : zDg A H da) (hPos : 0 < A) :
    BRIncs ((A - 1) * 2) default (zTs da default) := by
  induction hD with
  | nil => omega
  | @zero A H u _ ih =>
    have hA_pos : 0 < A := by omega
    have hIH := ih hA_pos
    have hs := BRIncs.short00 hIH
    rw [zDd] at hs
    have heq : (A * 2 - 1) * 2 = 2 + (A - 1) * 4 := by omega
    dsimp [zTs]
    rwa [heq]
  | @one A H u hDu ih =>
    cases A with
    | zero =>
      change BRIncs 0 default (d1 +> zTs u default)
      rw [loc_z1P hDu rfl]
      have h0 := BRIncs.zero (default : zB)
      have hd : d1 +> (default : zB) = one +> default := by simp [d1,one]
      rw [hd]; exact h0
    | succ A =>
      have hA_pos : 0 < A + 1 := by omega
      have hIH := ih hA_pos
      have heq_in : (A + 1 - 1) * 2 = A * 2 := by omega
      rw [heq_in] at hIH
      have hs := BRIncs.short10 hIH
      rw [zDd] at hs
      have heq : (1 + (A + 1) * 2 - 1) * 2 = 4 + A * 4 := by omega
      dsimp [zTs]
      rwa [heq]

lemma loc_z1R {orig out : zW} (hS : BStep orig out) :
    ∃ r,BRIncs 4 (zTs orig default) r /\ zTs out default = t +> r := by
  rcases hS with ⟨n,v,a,b,J,ds,hI,hD⟩
  refine ⟨zTs v (zTs ds default),?_,?_⟩
  · have hB : BRIncs (n * 2) default (zTs ds default) := by
      have heq : n * 2 = ((1 + n) - 1) * 2 := by omega
      rw [heq]
      exact loc_z1Q hD (by omega)
    have hR := loc_z1O hI hB
    simpa [z15,zTs] using hR
  · simp [z15,zTs]

def loc_zPf : Nat -> Nat -> Option (zW)
  | 0,_ => none
  | _ + 1,0 => none
  | _ + 1,1 => some [Q]
  | fuel + 1,m + 2 =>
    match loc_zPf fuel ((m + 2) / 2) with
    | none => none
    | some ws => some ((if (m + 2) % 2 == 0 then K else Q) :: ws)

lemma loc_z1S (fuel : Nat) :
    ∀ (m : Nat) (ws : zW),loc_zPf fuel m = some ws ->
      ∃ H,Binary m H (zTs ws default) := by
  induction fuel with
  | zero => intro m ws h; contradiction
  | succ fuel ih =>
    intro m ws h
    rcases m with _ | _ | m
    · contradiction
    · injection h with h; subst h
      exact ⟨1,Binary.one⟩
    · dsimp [loc_zPf] at h
      cases hrec : loc_zPf fuel ((m + 2) / 2) with
      | none => rw [hrec] at h; contradiction
      | some ws' =>
        rw [hrec] at h
        injection h with h; subst h
        rcases ih ((m + 2) / 2) ws' hrec with ⟨H,hB⟩
        have hq : (m + 2) / 2 = 1 + ((m + 2) / 2 - 1) := by omega
        rw [hq] at hB
        rcases Nat.mod_two_eq_zero_or_one (m + 2) with hmod | hmod
        · have hcond : ((m + 2) % 2 == 0) = true := beq_iff_eq.mpr hmod
          rw [hcond]; dsimp [zTs]
          refine ⟨1 + H,?_⟩
          have heq : m + 2 = 2 + ((m + 2) / 2 - 1) * 2 := by omega
          rw [heq]; exact Binary.zero hB
        · have hcond : ((m + 2) % 2 == 0) = false := beq_false_of_ne (by omega)
          rw [hcond]; dsimp [zTs]
          refine ⟨1 + H,?_⟩
          have heq : m + 2 = 3 + ((m + 2) / 2 - 1) * 2 := by omega
          rw [heq]; exact Binary.two hB

open e_Choice
def loc_z1W : e_Choice -> Nat -> Nat
  | CT,n | CP0,n | CP1,n => 1 + n
  | CS00,n | CS01,n => 2 + n * 4
  | CS10,n | CS11,n => 4 + n * 4

def loc_z1X : e_Choice -> Nat -> Nat
  | CT,n | CP0,n | CS00,n | CS10,n => n * 2
  | CP1,n | CS01,n | CS11,n => 1 + n * 2

def loc_z20 : e_Code -> Nat -> zW -> Option (zW)
  | .Stop n,k,u =>
    if k == n * 2 then
      if u.all z23 then loc_zPf 64 (1 + n) else none
    else none
  | .More ch n c,k,u =>
    if k == loc_z1W ch n then
      match zSw (e_z2i ch) u with
      | none => none
      | some w =>
        match loc_z20 c (loc_z1X ch n) w with
        | none => none
        | some v => some (e_z2j ch :: v)
    else none

lemma loc_z21 (c : e_Code) :
    ∀ (k : Nat) (u v : zW),loc_z20 c k u = some v ->
      BRIncs k (zTs u default) (zTs v default) := by
  induction c with
  | Stop n =>
    intro k u v hE
    dsimp [loc_z20] at hE
    cases hk : (k == n * 2) with
    | false => rw [hk] at hE; contradiction
    | true =>
      rw [hk] at hE
      have rfl_k : k = n * 2 := beq_iff_eq.mp hk
      subst rfl_k
      cases hu : u.all z23 with
      | false => rw [hu] at hE; contradiction
      | true =>
        rw [hu] at hE
        dsimp at hE
        rw [z24 u hu]
        rcases loc_z1S 64 (1 + n) v hE with ⟨H,hB⟩
        have hR := z0H hB
        have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
        rwa [heq] at hR
  | More ch n c ih =>
    intro k u v hE
    dsimp [loc_z20] at hE
    cases hk : (k == loc_z1W ch n) with
    | false => rw [hk] at hE; contradiction
    | true =>
      rw [hk] at hE
      dsimp at hE
      have rfl_k : k = loc_z1W ch n := beq_iff_eq.mp hk
      subst rfl_k
      cases hU : zSw (e_z2i ch) u with
      | none => rw [hU] at hE; contradiction
      | some w =>
        rw [hU] at hE
        dsimp at hE
        cases hC : loc_z20 c (loc_z1X ch n) w with
        | none => rw [hC] at hE; contradiction
        | some x =>
          rw [hC] at hE
          injection hE with hE; subst hE
          have rfl_u := z22 (e_z2i ch) u w hU
          subst rfl_u
          have hIH := ih (loc_z1X ch n) w x hC
          cases ch
          · exact BRIncs.T hIH
          · exact BRIncs.pair0 hIH
          · exact BRIncs.pair1 hIH
          · exact BRIncs.short00 hIH
          · exact BRIncs.short01 hIH
          · exact BRIncs.short10 hIH
          · exact BRIncs.short11 hIH

def loc_z22 (c : e_Code) (u : zW) : Option (zW) :=
  match loc_z20 c 4 (u ++ [K]) with
  | some v => some (V :: v)
  | none => none

lemma loc_z23 (c : e_Code) (u v : zW) (h : loc_z22 c u = some v) :
    ∃ r,BRIncs 4 (zTs u default) r /\ zTs v default = t +> r := by
  dsimp [loc_z22] at h
  cases hE : loc_z20 c 4 (u ++ [K]) with
  | none => rw [hE] at h; contradiction
  | some w =>
    rw [hE] at h
    injection h with h; subst h
    refine ⟨zTs w default,?_,rfl⟩
    have hR := loc_z21 c 4 (u ++ [K]) w hE
    simpa [z15,zTs] using hR

inductive loc_Rounds : zB -> zB -> Prop where
  | refl (r : zB) : loc_Rounds r r
  | next {r s t0 : zB} :
      BRIncs 4 r s -> loc_Rounds (t +> s) t0 -> loc_Rounds r t0

def loc_z24 : List e_Code -> zW -> Option (zW)
  | [],u => some u
  | c :: cs,u =>
    match loc_z22 c u with
    | none => none
    | some v => loc_z24 cs v

lemma loc_z25 (cs : List e_Code) :
    ∀ (u v : zW),loc_z24 cs u = some v ->
      loc_Rounds (zTs u default) (zTs v default) := by
  induction cs with
  | nil =>
    intro u v h
    injection h with h; subst h
    exact loc_Rounds.refl _
  | cons c cs ih =>
    intro u v h
    dsimp [loc_z24] at h
    cases hW : loc_z22 c u with
    | none => rw [hW] at h; contradiction
    | some w =>
      rw [hW] at h
      rcases loc_z23 c u w hW with ⟨r,hR,hEq⟩
      refine loc_Rounds.next hR ?_
      rw [<- hEq]
      exact ih w v h

lemma loc_z28 (u ds : zW) (p : Nat)
    (hD : ds.all z25 = true)
    (hS : z1h u * z1h ds = 1 / 2)
    (hGu : u = zR (1 + p) V ++ K :: u.drop (2 + p))
    (hEnd : u = u.take (u.length - 1) ++ [V])
    (hLo : ds = Q :: K :: ds.drop 2)
    (hHi : ds = ds.take (ds.length - 6) ++ zR 6 Q)
    (hF : 3 * z1e u + z1f u + z1h u * z1f ds <= 1 / 64) :
    BGood (u ++ ds) := by
  rcases z26 ds hD with ⟨A,hI⟩
  refine BGood.intro ds.length u A ds hI ?_ ⟨p,u.drop (2 + p),hGu⟩
    ⟨u.take (u.length - 1),hEnd⟩ ⟨ds.drop 2,hLo⟩ ⟨ds.take (ds.length - 6),hHi⟩ hF
  rw [<- (zDw hI).1]
  exact hS

def loc_z29 : zW := [V,V,V,K,Q,V]

def loc_z2a : List e_Code := [
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CS00 4 (.More CS11 1 (.More CT 2 (.More CS10 0 (.Stop 0)))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CS00 8 (.More CS11 3 (.More CT 6 (.More CS11 2 (.More CP0 4 (.Stop 4)))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CS00 16 (.More CS11 7 (.More CT 14 (.More CS11 6 (.More CT 12 (.More CP0 23 (.More CP0 45 (.Stop 45))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CS00 32 (.More CS11 15 (.More CT 30 (.More CS11 14 (.More CT 28 (.More CT 55 (.More CT 109 (.More CS00 54 (.More CP1 107 (.More CP0 214 (.More CP0 427 (.Stop 427)))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More CS00 64 (.More CS11 31 (.More CT 62 (.More CS11 30 (.More CT 60 (.More CT 119 (.More CT 237 (.More CS00 118 (.More CT 235 (.More CT 469 (.More CT 937 (.More CS00 468 (.More CS10 233 (.More CS01 116 (.More CP0 232 (.More CP0 463 (.More CS01 231 (.More CP0 462 (.Stop 462)))))))))))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More CT 257 (.More CS00 128 (.More CS11 63 (.More CT 126 (.More CS11 62 (.More CT 124 (.More CT 247 (.More CT 493 (.More CS00 246 (.More CT 491 (.More CT 981 (.More CT 1961 (.More CS00 980 (.More CP0 1959 (.More CT 3917 (.More CT 7833 (.More CS00 3916 (.More CT 7831 (.More CS01 3915 (.More CP1 7830 (.More CP0 15660 (.More CS10 7829 (.More CP1 15657 (.More CP0 31314 (.Stop 31314)))))))))))))))))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More CT 257 (.More CT 513 (.More CS00 256 (.More CS11 127 (.More CT 254 (.More CS11 126 (.More CT 252 (.More CT 503 (.More CT 1005 (.More CS00 502 (.More CT 1003 (.More CT 2005 (.More CT 4009 (.More CS00 2004 (.More CT 4007 (.More CT 8013 (.More CT 16025 (.More CS00 8012 (.More CT 16023 (.More CS00 8011 (.More CT 16021 (.More CT 32041 (.More CS01 16020 (.More CT 32040 (.More CT 64079 (.More CS01 32039 (.More CP0 64078 (.More CS10 32038 (.More CP0 64075 (.More CP0 128149 (.More CS00 64074 (.More CP0 128147 (.More CS01 64073 (.More CP1 128146 (.More CP0 256292 (.Stop 256292))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More CT 257 (.More CT 513 (.More CT 1025 (.More CS00 512 (.More CS11 255 (.More CT 510 (.More CS11 254 (.More CT 508 (.More CT 1015 (.More CT 2029 (.More CS00 1014 (.More CT 2027 (.More CT 4053 (.More CT 8105 (.More CS00 4052 (.More CT 8103 (.More CT 16205 (.More CT 32409 (.More CS00 16204 (.More CT 32407 (.More CS00 16203 (.More CT 32405 (.More CT 64809 (.More CS00 32404 (.More CT 64807 (.More CT 129613 (.More CS00 64806 (.More CT 129611 (.More CS01 64805 (.More CT 129610 (.More CT 259219 (.More CS00 129609 (.More CT 259217 (.More CS00 129608 (.More CT 259215 (.More CT 518429 (.More CP0 1036857 (.More CP0 2073713 (.More CS00 1036856 (.More CP0 2073711 (.More CS00 1036855 (.More CP0 2073709 (.More CS00 1036854 (.More CP0 2073707 (.More CP1 4147413 (.More CP1 8294826 (.More CP0 16589652 (.Stop 16589652)))))))))))))))))))))))))))))))))))))))))))))))))))))))
]

def loc_z2b : zW := [V,V,V,V,V,V,V,V,V,V,V,K,Q,V,Q,V,V,V,K,V,V,V,K,V,V,V,K,V,K,V,V,K,V,V,K,V,K,V,V,K,V,K,V,V,V,V,K,V,K,V,K,V,V,V,V]

def loc_z2c : zW := [Q,K,Q,K,Q,K,Q,K,Q,Q,K,K,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q]

lemma loc_z2d :
    loc_Rounds z0z (zTs (loc_z2b ++ loc_z2c) default) := by
  have h1 : loc_Rounds (zTs loc_z29 default) (zTs (loc_z2b ++ loc_z2c) default) := by
    apply loc_z25 loc_z2a
    decide
  simpa [loc_z29,z0z,zTs] using h1

lemma loc_z2e :
    BGood (loc_z2b ++ loc_z2c) := by
  apply loc_z28 loc_z2b loc_z2c 10
  · decide
  · norm_num [loc_z2b,loc_z2c,z1h]
  · decide
  · decide
  · decide
  · decide
  · norm_num [loc_z2b,loc_z2c,z1e,z1f,z1h]

inductive Num : Nat -> zF -> List Call -> Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)

def loc_z2f (k : Nat) (r r' : zB) : Prop :=
  ∀ w hs,Num k w hs -> Side hs (w +> r) r'

lemma loc_z2g {r r' : zB} (h : loc_z2f 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl

lemma loc_z2h {n : Nat} {r r' : zB}
    (hI : loc_z2f (n * 2) r r') : loc_z2f (1 + n) (t +> r) (t +> r') := by
  intro w hs hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil]
    cases m with
    | zero =>
      have hn0 : n * 2 = 0 := by omega
      rw [hn0] at hI
      have hr' := loc_z2g hI
      subst hr'
      rw [<- append_assoc t one r]
      exact zSc z0b (Side.nil r)
    | succ m =>
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      refine zSc (z0m m) ?_
      have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : n * 2 = 2 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil]
    refine zSc (z0n m) ?_
    have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : n * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2

lemma loc_z2i {n : Nat} {r r' : zB}
    (hI : loc_z2f (n * 2) r r') : loc_z2f (1 + n) (d1 +> (d0 +> r)) (t +> r') := by
  intro w hs hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil,<- append_assoc d1 d0 r]
    cases m with
    | zero =>
      have hn0 : n * 2 = 0 := by omega
      rw [hn0] at hI
      have hr' := loc_z2g hI
      subst hr'
      rw [<- append_assoc t one r]
      exact zSc z0e (Side.nil r)
    | succ m =>
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      refine zSc (z0o m) ?_
      have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : n * 2 = 2 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil,<- append_assoc d1 d0 r]
    refine zSc (z0p m) ?_
    have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : n * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2

lemma loc_z2j {n : Nat} {r r' : zB}
    (hI : loc_z2f (1 + n * 2) r r') : loc_z2f (1 + n) (d1 +> (d1 +> r)) (t +> r') := by
  intro w hs hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil,<- append_assoc d1 d1 r]
    refine zSc (z0q m) ?_
    have hN1 : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ (m * 2)) := by
      have hm : 1 + n * 2 = 1 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (m * 2)
    simpa using hI [] _ hN1
  | @even m =>
    simp only [append_nil,<- append_assoc d1 d1 r]
    refine zSc (z0r m) ?_
    have hN1 : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ (1 + m * 2)) := by
      have hm : 1 + n * 2 = 1 + (1 + m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (1 + m * 2)
    simpa using hI [] _ hN1

lemma loc_z2k {n : Nat} {r r' : zB}
    (hI : loc_z2f (n * 2) r r') : loc_z2f (2 + n * 4) (d0 +> r) (d0 +> r') := by
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
      have hr' := loc_z2g hI
      subst hr'
      rw [<- append_assoc d0 one r]
      exact zSc z0i (Side.nil r)
    | succ n =>
      have heq : (n + 1) * 2 = 2 + n * 2 := by omega
      rw [heq]
      refine zSc (z0s n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        rw [heq]; exact Num.even n
      simpa using hI [] _ hN2

lemma loc_z2l {n : Nat} {r r' : zB}
    (hI : loc_z2f (1 + n * 2) r r') : loc_z2f (2 + n * 4) (d1 +> r) (d0 +> r') := by
  intro w hs hN
  generalize hk : 2 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = n * 2 := by omega
    subst hm
    refine zSc (z0t n) ?_
    simpa using hI [] _ (Num.odd n)

lemma loc_z2m {n : Nat} {r r' : zB}
    (hI : loc_z2f (n * 2) r r') : loc_z2f (4 + n * 4) (d0 +> r) (d1 +> r') := by
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
      have hr' := loc_z2g hI
      subst hr'
      rw [<- append_assoc d1 one r]
      exact zSc z0u (Side.nil r)
    | succ n =>
      have heq : 1 + (n + 1) * 2 = 3 + n * 2 := by omega
      rw [heq]
      refine zSc (z0v n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        have heq2 : (n + 1) * 2 = 2 + n * 2 := by omega
        rw [heq2]; exact Num.even n
      simpa using hI [] _ hN2

lemma loc_z2n {n : Nat} {r r' : zB}
    (hI : loc_z2f (1 + n * 2) r r') : loc_z2f (4 + n * 4) (d1 +> r) (d1 +> r') := by
  intro w hs hN
  generalize hk : 4 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = 1 + n * 2 := by omega
    subst hm
    refine zSc (z0w n) ?_
    simpa using hI [] _ (Num.odd n)

lemma loc_z2o {k : Nat} {r r' : zB} (hI : BRIncs k r r') :
    loc_z2f k r r' := by
  induction hI with
  | zero r =>
    intro w hs hN
    generalize hk : 0 = k0 at hN
    cases hN with
    | zero => exact Side.nil (one +> r)
    | odd _ => omega
    | even _ => omega
  | T _ ih => exact loc_z2h ih
  | pair0 _ ih => exact loc_z2i ih
  | pair1 _ ih => exact loc_z2j ih
  | short00 _ ih => exact loc_z2k ih
  | short01 _ ih => exact loc_z2l ih
  | short10 _ ih => exact loc_z2m ih
  | short11 _ ih => exact loc_z2n ih

lemma loc_z2p {r r' : zB} (hI : BRIncs 4 r r') :
    (zCf r) [target_tm]⊢⁺ zCf (t +> r') := by
  have hC := loc_z2o hI [] ([.cj] ++ [.ch] ^ 1) (Num.even 1)
  have hS := zSc z0x hC
  dsimp at hS
  rcases hS with _ | ⟨hca,hnil⟩
  cases hnil
  exact zPt (hca lh) (z0y (t +> r'))

lemma loc_z2q {orig out : zW} (hS : BStep orig out) :
    (zCf (zTs orig default)) [target_tm]⊢⁺ zCf (zTs out default) := by
  rcases loc_z1R hS with ⟨r,hI,hEq⟩
  rw [hEq]
  exact loc_z2p hI

lemma loc_z2r {r r' : zB} (h : loc_Rounds r r') :
    (zCf r) [target_tm]⊢* zCf r' := by
  induction h with
  | refl _ => exact ⟨0,rfl⟩
  | next hR _ ih =>
    rcases loc_z2p hR with ⟨n,_,hn⟩
    rcases ih with ⟨m,hm⟩
    exact ⟨n + m,zMt target_tm _ _ _ n m hn hm⟩

lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl

lemma loc_z2s (m : Nat) :
    ∃ N ≥ m,∃ w,multiStep target_tm (init []) N = some (zCf (zTs w default)) /\ BGood w := by
  induction m with
  | zero =>
    rcases z0E with ⟨k1,_,hk1⟩
    rcases loc_z2r loc_z2d with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,loc_z2b ++ loc_z2c,
      zMt target_tm _ _ _ k1 k2 hk1 hk2,loc_z2e⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,w,h_ms,h_good⟩
    rcases loc_z1N h_good with ⟨w',hStep,h_good'⟩
    rcases loc_z2q hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,w',
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
  rcases loc_z2s (n + 1) with ⟨N,hN,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

end BusyBeaver.M_1RB1LD_1RC0RB_1LD0RD_1LA0LE_1LD1LF_1LAHHH
