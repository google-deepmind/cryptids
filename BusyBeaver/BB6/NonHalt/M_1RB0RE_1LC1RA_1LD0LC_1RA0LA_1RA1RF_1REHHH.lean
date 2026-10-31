/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RE---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RE---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1REHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RE---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 4, Stmt.write 1 Dir.right)
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
  | .ch => B
  | .cj => A
  | .cp => A
  | .ca => A
def zCw : Call -> zF
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
  | .ca => [1,1,1,0,1,0]
def zCR (l : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  ((l <+ zCw c) {{zCs c}}> r)
def zCL (l : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (l <{{C}} ([0] +> r))
def zCf (r : zB) : Cfg (Fin 2) (Fin 6) :=
  zCL lh r
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
lemma z0b : Seg [.cp] [.cj] t t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0c : Seg [.cj] [.cj,.ch] t t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
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
lemma z0k : Seg [.ca] [.cj] [] t := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  have h1 : zCR l .ca ([] +> r1) = zCR ([1,0,1,0] +> l) .cj r1 := by
    unfold zCR zCw zCs; simp only [append_cons,append_nil]
  have h2 : (zCL ([1,0,1,0] +> l) r2) [target_tm]⊢⁺ (zCL l (t +> r2)) := by
    unfold zCL t; simp only [append_cons,append_nil]; execute
  rw [h1]
  exact zPt (hc1 ([1,0,1,0] +> l)) h2
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
lemma z0l : Seg [.ch,.ch] [.ch] d0 d0 :=
  zSg zH0 zH4
lemma z0m : Seg [.ch,.ch] [.ch] d1 d1 :=
  zSg zH4 zH0
lemma z0n (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) t t :=
  zSg z0b (zS3 n)
lemma z0o (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using zSg z0c (zS3 n)
lemma z0p (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0e zH2) (zS3 n)
lemma z0q (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0f (zS3 n)
lemma z0r (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0g (zS3 n)
lemma z0s (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using zSg z0h (zS3 n)
lemma z0t (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0i (zSg zH1 zH3)
  have h1 := zSg h0 (zSa z0l n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
lemma z0u (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0j (zSa z0l n)
lemma z0v : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0i zH1
lemma z0w (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0i (zSg zH1 (zSg zH3 zH0))
  have h1 := zSg h0 (zSa z0m n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
lemma z0x (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1 := zSg z0j zH0
  have h1 := zSg h0 (zSa z0m n)
  simpa only [zLp',List.cons_append,List.nil_append] using h1
lemma z0y : Seg [.ca,.ch] ([.cj] ++ [.ch] ^ 2) [] t :=
  zSg z0k z0d
lemma z0z (r : zB) :
    (zCf r) [target_tm]⊢⁺ (zCR ([1] +> default) .ca r) := by
  unfold zCf zCL zCR lh zCw zCs
  simp only [append_cons,append_nil]
  execute
lemma z0A (r : zB) :
    (zCL ([1] +> default) r) [target_tm]⊢⁺ (zCR lh .ch r) := by
  unfold zCL zCR lh zCw zCs
  simp only [append_cons,append_nil]
  execute
lemma z0B :
    (init []) [target_tm]⊢⁺ zCf (t +> (d1 +> (d1 +> default))) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold zCf zCL lh t d1
  simp only [append_cons,append_nil]
  execute
inductive RIncs : Nat -> zB -> zB -> Prop where
  | zero (r : zB) : RIncs 0 r (one +> r)
  | T {n : Nat} {r r' : zB} :
      RIncs ((1 + n) * 2) r r' -> RIncs (1 + n) (t +> r) (t +> r')
  | pair0 {n : Nat} {r r' : zB} :
      RIncs (n * 2) r r' -> RIncs (1 + n) (d1 +> (d0 +> r)) (t +> r')
  | pair1 {n : Nat} {r r' : zB} :
      RIncs (1 + n * 2) r r' -> RIncs (1 + n) (d1 +> (d1 +> r)) (t +> r')
  | short00 {n : Nat} {r r' : zB} :
      RIncs (n * 2) r r' -> RIncs (2 + n * 4) (d0 +> r) (d0 +> r')
  | short01 {n : Nat} {r r' : zB} :
      RIncs (1 + n * 2) r r' -> RIncs (2 + n * 4) (d1 +> r) (d0 +> r')
  | short10 {n : Nat} {r r' : zB} :
      RIncs (n * 2) r r' -> RIncs (4 + n * 4) (d0 +> r) (d1 +> r')
  | short11 {n : Nat} {r r' : zB} :
      RIncs (1 + n * 2) r r' -> RIncs (4 + n * 4) (d1 +> r) (d1 +> r')
inductive Binary : Nat -> Nat -> zB -> Prop where
  | one : Binary 1 1 (d1 +> default)
  | zero {n H : Nat} {r : zB} :
      Binary (1 + n) H r -> Binary (2 + n * 2) (1 + H) (d0 +> r)
  | two {n H : Nat} {r : zB} :
      Binary (1 + n) H r -> Binary (3 + n * 2) (1 + H) (d1 +> r)

open WordCalculus Word
local notation "zW" => List Word
local notation "zR" => List.replicate

lemma z0C (n : Nat) : 0 < 8 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

lemma z0E {A H : Nat} {r : zB} (h : Binary A H r) :
    0 < A /\ 0 < H /\ 2 ^ H <= A * 2 /\ A < 2 ^ H := by
  induction h with
  | one => decide
  | @zero n H r _ ih =>
    rw [zP2 H]; omega
  | @two n H r _ ih =>
    rw [zP2 H]; omega

lemma z0F (n : Nat) : ∃ H r,Binary (1 + n) H r := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨1,d1 +> default,Binary.one⟩
    | succ m =>
      rcases z0U m with ⟨a,rfl⟩ | ⟨a,rfl⟩
      · rcases ih a (by omega) with ⟨H0,r,hI⟩
        refine ⟨1 + H0,d0 +> r,?_⟩
        have heq : 1 + (a * 2 + 1) = 2 + a * 2 := by omega
        rw [heq]; exact Binary.zero hI
      · rcases ih a (by omega) with ⟨H0,r,hI⟩
        refine ⟨1 + H0,d1 +> r,?_⟩
        have heq : 1 + ((1 + a * 2) + 1) = 3 + a * 2 := by omega
        rw [heq]; exact Binary.two hI

lemma z0G {A H : Nat} {r : zB} (h : Binary A H r) :
    RIncs ((A - 1) * 2) default r := by
  induction h with
  | one =>
    have h0 := RIncs.zero (default : zB)
    have hd : d1 +> (default : zB) = one +> default := by simp [d1,one]
    rw [hd]; exact h0
  | @zero n H r _ ih =>
    have ih' : RIncs (n * 2) default r := by
      have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
      rwa [heq] at ih
    have hs := RIncs.short00 ih'
    rw [zDd] at hs
    have heq : ((2 + n * 2) - 1) * 2 = 2 + n * 4 := by omega
    rwa [heq]
  | @two n H r _ ih =>
    have ih' : RIncs (n * 2) default r := by
      have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
      rwa [heq] at ih
    have hs := RIncs.short10 ih'
    rw [zDd] at hs
    have heq : ((3 + n * 2) - 1) * 2 = 4 + n * 4 := by omega
    rwa [heq]

lemma z0S {A H : Nat} {u : zW} (h1 : zDg A H u) :
    ∀ {B J : Nat} {r : zB},Binary B J r -> Binary (A + B * 2 ^ H) (H + J) (zTs u r) := by
  induction h1 with
  | nil =>
    intro B J r h2
    simpa [zTs] using h2
  | @zero A H u _ ih =>
    intro B J r h2
    have hI := ih h2
    have hB := z0E hI
    have hI' : Binary (1 + (A + B * 2 ^ H - 1)) (H + J) (zTs u r) := by
      have heq : 1 + (A + B * 2 ^ H - 1) = A + B * 2 ^ H := by omega
      rwa [heq]
    have h3 := Binary.zero hI'
    have heq1 : 2 + (A + B * 2 ^ H - 1) * 2 = A * 2 + B * 2 ^ (1 + H) := by
      rw [zP2 H,Nat.mul_add]; omega
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    simpa [zTs,heq1,heq2] using h3
  | @one A H u _ ih =>
    intro B J r h2
    have hI := ih h2
    have hB := z0E hI
    have hI' : Binary (1 + (A + B * 2 ^ H - 1)) (H + J) (zTs u r) := by
      have heq : 1 + (A + B * 2 ^ H - 1) = A + B * 2 ^ H := by omega
      rwa [heq]
    have h3 := Binary.two hI'
    have heq1 : 3 + (A + B * 2 ^ H - 1) * 2 = (1 + A * 2) + B * 2 ^ (1 + H) := by
      rw [zP2 H,Nat.mul_add]; omega
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    simpa [zTs,heq1,heq2] using h3

lemma z0T : Binary 191 8 (zTs (zR 6 Q ++ [K,Q]) default) := by
  dsimp [List.replicate,zTs]
  exact Binary.two (n := 94) (Binary.two (n := 46) (Binary.two (n := 22)
    (Binary.two (n := 10) (Binary.two (n := 4) (Binary.two (n := 1)
      (Binary.zero (n := 0) Binary.one))))))

def loc_z0V (ds : zW) : Prop := ∃ v,ds = K :: K :: v

def loc_z0W (ds : zW) : Prop := ∃ v,ds = v ++ zR 6 Q

lemma loc_z0X (r k : Nat) (hL : 191 * 2 ^ r <= k * 2) (hU : k * 2 < 192 * 2 ^ r) :
    ∃ ds,zDg (k * 8 - 512 * 2 ^ r) (8 + r) ds /\ loc_z0V ds /\ loc_z0W ds /\
      Binary (k * 8) (10 + r) (zTs ds (d0 +> (d1 +> default))) := by
  let a := k * 2 - 191 * 2 ^ r
  have hA : a + 191 * 2 ^ r = k * 2 := by omega
  have ha_lt : a < 2 ^ r := by omega
  rcases z18 r a ha_lt with ⟨v,hD⟩
  refine ⟨K :: K :: (v ++ zR 6 Q),?_,⟨_,rfl⟩,⟨K :: K :: v,rfl⟩,?_⟩
  · have hApp := z19 hD (z1a 6)
    have hZ1 := zDg.zero hApp
    have hZ2 := zDg.zero hZ1
    have hpos := zPp r
    have heq1 : ((a + (2 ^ 6 - 1) * 2 ^ r) * 2) * 2 = k * 8 - 512 * 2 ^ r := by
      change ((a + 63 * 2 ^ r) * 2) * 2 = k * 8 - 512 * 2 ^ r
      (try omega)
    have heq2 : 1 + (1 + (r + 6)) = 8 + r := by omega
    rwa [heq1,heq2] at hZ2
  · have hB := z0S hD z0T
    rw [z15] at hB
    dsimp [zTs] at hB ⊢
    rw [z15]
    have hpos := zPp r
    have hB' : Binary (1 + (a + 191 * 2 ^ r - 1)) (r + 8)
        (zTs v (zTs (zR 6 Q) (d0 +> (d1 +> default)))) := by
      have heq : 1 + (a + 191 * 2 ^ r - 1) = a + 191 * 2 ^ r := by omega
      rwa [heq]
    have hB1 := Binary.zero hB'
    have hB1' : Binary (1 + (2 * (a + 191 * 2 ^ r) - 1)) (1 + (r + 8))
        (d0 +> zTs v (zTs (zR 6 Q) (d0 +> (d1 +> default)))) := by
      have heq : 1 + (2 * (a + 191 * 2 ^ r) - 1) = 2 + (a + 191 * 2 ^ r - 1) * 2 := by omega
      rwa [heq]
    have hB2 := Binary.zero hB1'
    have heq1 : 2 + (2 * (a + 191 * 2 ^ r) - 1) * 2 = k * 8 := by omega
    have heq2 : 1 + (1 + (r + 8)) = 10 + r := by omega
    rwa [heq1,heq2] at hB2

lemma loc_z0Y (n : Nat) : 2 ^ (3 * n) = 8 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq : 3 * (n + 1) = 3 * n + 3 := by omega
    rw [heq,Nat.pow_add,ih,Nat.pow_succ]; ring

lemma loc_z0Z (n : Nat) :
    2 ^ (10 + 3 * n) = 256 * 2 ^ (2 + 3 * n) /\ 8 ^ (3 + n) = 128 * 2 ^ (2 + 3 * n) := by
  constructor
  · have heq : 10 + 3 * n = (2 + 3 * n) + 8 := by omega
    rw [heq,Nat.pow_add]; ring
  · rw [Nat.pow_add 8 3 n,Nat.pow_add 2 2 (3 * n),loc_z0Y]; ring

lemma loc_z18 {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) :
    ∀ {r r' : zB},RIncs b r r' -> RIncs a (zTs u r) (zTs v r') := by
  induction h with
  | nil _ => intro r r' hR; exact hR
  | T _ ih => intro r r' hR; exact RIncs.T (ih hR)
  | pair0 _ ih => intro r r' hR; exact RIncs.pair0 (ih hR)
  | pair1 _ ih => intro r r' hR; exact RIncs.pair1 (ih hR)
  | short00 _ ih => intro r r' hR; exact RIncs.short00 (ih hR)
  | short01 _ ih => intro r r' hR; exact RIncs.short01 (ih hR)
  | short10 _ ih => intro r r' hR; exact RIncs.short10 (ih hR)
  | short11 _ ih => intro r r' hR; exact RIncs.short11 (ih hR)

lemma loc_z1a {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) :
    (a : Rat) = (b : Rat) * z1h v + (z1g v + l) * 2 := by
  induction h with
  | nil k => simp [z1g,z1h]
  | T _ ih => dsimp [z1g,z1h]; push_cast at ih ⊢; linarith
  | pair0 _ ih => dsimp [z1g,z1h]; push_cast at ih ⊢; linarith
  | pair1 _ ih => dsimp [z1g,z1h]; push_cast at ih ⊢; linarith
  | short00 _ ih => dsimp [z1g,z1h]; push_cast at ih ⊢; linarith
  | short01 _ ih => dsimp [z1g,z1h]; push_cast at ih ⊢; linarith
  | short10 _ ih => dsimp [z1g,z1h]; push_cast at ih ⊢; linarith
  | short11 _ ih => dsimp [z1g,z1h]; push_cast at ih ⊢; linarith

lemma loc_z1e {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) : z1h v <= z1h u := by
  induction h with
  | nil _ => simp [z1h]
  | T _ ih => dsimp [z1h]; linarith
  | @pair0 _ u _ _ _ _ _ => have hp := zSp u; dsimp [z1h]; linarith
  | @pair1 _ u _ _ _ _ _ => have hp := zSp u; dsimp [z1h]; linarith
  | short00 _ ih => dsimp [z1h]; linarith
  | short01 _ ih => dsimp [z1h]; linarith
  | short10 _ ih => dsimp [z1h]; linarith
  | short11 _ ih => dsimp [z1h]; linarith

lemma loc_z1f {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) (he : z0Y u = true) : z1h v * 8 <= z1h u := by
  induction h with
  | nil _ => contradiction
  | T _ ih => dsimp [z0Y,z1h] at he ⊢; have := ih he; linarith
  | pair0 hS _ => have := loc_z1e hS; dsimp [z1h]; linarith
  | pair1 hS _ => have := loc_z1e hS; dsimp [z1h]; linarith
  | short00 _ ih => dsimp [z0Y,z1h] at he ⊢; have := ih he; linarith
  | @short01 n u k v l hS ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [z0Y,z1h] at he ih ⊢; have := ih he; linarith
      | K => exact False.elim (zSz n u' k v l hS)
      | Q => dsimp [z0Y,z1h] at he ih ⊢; have := ih he; linarith
  | short10 _ ih => dsimp [z0Y,z1h] at he ⊢; have := ih he; linarith
  | @short11 n u k v l hS ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [z0Y,z1h] at he ih ⊢; have := ih he; linarith
      | K => exact False.elim (zSz n u' k v l hS)
      | Q => dsimp [z0Y,z1h] at he ih ⊢; have := ih he; linarith

lemma loc_z1i {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) (he : z0Y u = true) : 0 < l := by
  induction h with
  | nil _ => contradiction
  | T _ ih => dsimp [z0Y] at he; have := ih he; linarith
  | pair0 hI _ => have := z1o hI; linarith
  | pair1 hI _ => have := z1o hI; linarith
  | short00 hI _ => have := z1o hI; linarith
  | @short01 n u k v l hI ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [z0Y] at he; have := ih he; linarith
      | K => exact False.elim (zSz n u' k v l hI)
      | Q => dsimp [z0Y] at he; have := ih he; linarith
  | short10 hI _ => have := z1o hI; linarith
  | @short11 n u k v l hI ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [z0Y] at he; have := ih he; linarith
      | K => exact False.elim (zSz n u' k v l hI)
      | Q => dsimp [z0Y] at he; have := ih he; linarith

lemma loc_z1k (r : Nat) :
    zR (3 + r) V = zR r V ++ [V,V,V] := by
  have heq : 3 + r = r + 3 := by omega
  rw [heq,List.replicate_add]; rfl

lemma loc_z1l (n a b : Nat) (v : zW) (l : Rat)
    (hI : Scan a (zR (6 + n) Q ++ [K]) b v l) :
    ∃ w k,v = w ++ [V,V,V] /\ b = k * 8 := by
  rcases z0U n with ⟨a0,rfl⟩ | ⟨a0,rfl⟩
  · have heq : 6 + a0 * 2 = 2 + (2 + a0) * 2 := by omega
    rw [heq] at hI
    rcases z1r (2 + a0) a b v l hI with ⟨d,k,rfl,rfl,_⟩
    refine ⟨d :: zR a0 V,k * 2 ^ (1 + a0),?_,?_⟩
    · have heq2 : 1 + (2 + a0) = 3 + a0 := by omega
      rw [heq2,loc_z1k]; rfl
    · have heq2 : 2 + (2 + a0) = (1 + a0) + 3 := by omega
      rw [heq2,Nat.pow_add]; ring
  · have heq : 6 + (1 + a0 * 2) = 1 + (3 + a0) * 2 := by omega
    rw [heq] at hI
    rcases zS1 (3 + a0) a b v l hI with ⟨rfl,rfl,_⟩
    refine ⟨zR (1 + a0) V,(a - 1) * 2 ^ (1 + a0),?_,?_⟩
    · have heq2 : 1 + (3 + a0) = 3 + (1 + a0) := by omega
      rw [heq2,loc_z1k]
    · have heq2 : 1 + (3 + a0) = (1 + a0) + 3 := by omega
      rw [heq2,Nat.pow_add]; ring

lemma loc_z1m (n : Nat) :
    ∀ (a b : Nat) (v : zW) (l : Rat),
      Scan a (zR n V) b v l ->
      v = zR n V /\ b = a * 2 ^ n /\ l = 0 := by
  induction n with
  | zero =>
    intro a b v l hI
    cases hI
    exact ⟨rfl,by simp,rfl⟩
  | succ n ih =>
    intro a b v l hI
    cases hI with
    | @T m _ _ v0 l0 hJ =>
      rcases ih ((1 + m) * 2) b v0 l0 hJ with ⟨rfl,rfl,rfl⟩
      refine ⟨rfl,?_,by ring⟩
      rw [Nat.pow_succ]; ring

lemma loc_z1n {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (hI : Scan a (u ++ [V,V,V]) b v l) :
    ∃ w k,v = w ++ [V,V,V] /\ b = k * 8 := by
  rcases z1z hI u [V,V,V] rfl (Or.inr ⟨[V,V],rfl⟩) with ⟨c,x,y,s,t0,_,hK,rfl,_⟩
  rcases loc_z1m 3 c b y t0 hK with ⟨rfl,rfl,_⟩
  exact ⟨x,c,rfl,rfl⟩

lemma loc_z1o {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (hI : Scan a (u ++ zR 6 Q ++ [K]) b v l) :
    ∃ w k,v = w ++ [V,V,V] /\ b = k * 8 := by
  rcases z14 u with ⟨p,n,rfl,hP⟩
  have hE : (p ++ zR n Q) ++ zR 6 Q ++ [K] =
      p ++ (zR (6 + n) Q ++ [K]) := by
    have heq : 6 + n = n + 6 := by omega
    rw [heq,List.replicate_add]; simp [List.append_assoc]
  rw [hE] at hI
  rcases z1z hI p (zR (6 + n) Q ++ [K]) rfl (Or.inl hP) with ⟨c,x,y,s,t0,_,hK,rfl,_⟩
  rcases loc_z1l n c b y t0 hK with ⟨w,k,rfl,rfl⟩
  exact ⟨x ++ w,k,by rw [List.append_assoc],rfl⟩

lemma loc_z1q {n : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (hI : Scan (n * 8) (K :: K :: u) b v l) : z0Y v = true := by
  generalize ha : n * 8 = a at hI
  cases hI with
  | short00 hJ => omega
  | @short10 m _ _ _ _ hJ =>
    generalize hb : m * 2 = a2 at hJ
    cases hJ with
    | short00 _ => rfl
    | short10 _ => omega

lemma loc_z1v {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    {c : Nat} {ds w : zW} {m z : Rat}
    (hI : Scan a u b v l) (hE : z0Y u = true)
    (hJ : Scan b ds c w m) (hD : zTd ds z) (hZ : 3 <= z) :
    z1h v * z1e w <= (7 / 24) * (z1h u * z) /\
    z1h v * m <= (7 / 24) * (z1h u * z) := by
  have hg := loc_z1f hI hE
  rcases z1x hJ hD with ⟨hM,hL,_⟩
  have hp := zSp v
  have h1 : z1h v * (1 + z * 2) <= (7 / 24) * (z1h u * z) := by nlinarith
  constructor <;> nlinarith

lemma loc_z1w {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    {c : Nat} {ds w : zW} {m z : Rat}
    (hI : Scan a u b v l) (hE : z0Y u = true)
    (hJ : Scan b ds c w m) (hD : zTd ds z) (hZ : 3 <= z) :
    z1e (v ++ w) <= z1e u + (7 / 24) * (z1h u * z) /\
    z1e (v ++ w) + l + z1h v * m <= z1e u + z1f u + (7 / 12) * (z1h u * z) := by
  have hb := z1o hI
  have hd := loc_z1v hI hE hJ hD hZ
  rw [z1j]
  constructor <;> linarith

lemma loc_z1x {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (hI : Scan a u b v l) (hB : 0 < b) :
    ∃ H r,Binary b H r /\ RIncs a (zTs u (d1 +> default)) (zTs v (t +> r)) := by
  cases b with
  | zero => omega
  | succ n =>
    have h1n : n + 1 = 1 + n := by omega
    rw [h1n] at hI ⊢
    rcases z0F n with ⟨H,r,hD⟩
    refine ⟨H,r,hD,?_⟩
    refine loc_z18 hI ?_
    have hR := z0G hD
    have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
    rw [heq] at hR
    have hp := RIncs.pair0 hR
    rwa [zDd] at hp

lemma loc_z1y {u : zW} {A H : Nat} {ds : zW} (hD : zDg A H ds)
    (hE : z1h u * ((2 ^ H : Nat) : Rat) = 1 / 2)
    (hF : z1e u * 2 + z1f u + z1h u * z1f ds <= 1 / 64) :
    ∃ b v l J r,
      Scan 6 (u ++ ds ++ [K]) b v l /\ Binary b J r /\
      RIncs 6 (zTs (u ++ ds) (d0 +> (d1 +> default))) (zTs v (t +> r)) := by
  rcases zDw hD with ⟨hS,hM,_⟩
  have hU := (zWn u).1
  have hP := zSp u
  have hEx : (z1e (u ++ ds ++ [K]) + z1f (u ++ ds ++ [K])) * 2 < ((3 * 2 : Nat) : Rat) := by
    rw [z1j,z1j,z1k,z1k,z1m]
    dsimp [z1e,z1f,z1h]
    rw [hS]
    have hM' : z1e ds = ((2 ^ H : Nat) : Rat) - 1 := by linarith
    rw [hM']
    nlinarith
  rcases z1q (u ++ ds ++ [K]) 3 hEx with ⟨b,v,l,hI,hB⟩
  rcases loc_z1x hI hB with ⟨J,r,hR,hK⟩
  refine ⟨b,v,l,J,r,hI,hR,?_⟩
  simpa [z15,zTs] using hK

def loc_z1z (u : zW) : Prop := ∃ p,u = p ++ [V,V,V]

lemma loc_z1A (u v : zW) (h : z0Y u = true) : z0Y (u ++ v) = true := by
  induction u with
  | nil => contradiction
  | cons w u ih =>
    cases w with
    | V => exact ih h
    | K => exact ih h
    | Q =>
      cases u with
      | nil => contradiction
      | cons w2 u' =>
        cases w2 with
        | V => exact ih h
        | K => rfl
        | Q => exact ih h

lemma loc_z1B {u : zW} {A H : Nat} {ds : zW} (hD : zDg A H ds)
    (hHs : z1h u * ((2 ^ H : Nat) : Rat) = 1 / 2)
    (hF : z1e u * 2 + z1f u + z1h u * z1f ds <= 1 / 64)
    (hU : loc_z1z u) (hW : z0Y u = true) (hLo : loc_z0V ds) (hHi : loc_z0W ds) :
    ∃ k v l g,
      Scan 6 (u ++ ds ++ [K]) (k * 8) v l /\
      loc_z1z v /\ z0Y v = true /\
      z1h v * ((8 ^ g : Nat) : Rat) = 1 /\
      z1e v <= z1e u + (7 / 24) * (z1h u * z1f ds) /\
      z1e v + l <= z1e u + z1f u + (7 / 12) * (z1h u * z1f ds) /\
      0 < z1g v + l /\ z1g v + l <= 1 / 64 := by
  rcases hU with ⟨p,hU⟩
  rcases loc_z1y hD hHs hF with ⟨b,v,l,_,_,hI,_,_⟩
  have hCu : z10 u (ds ++ [K]) := by
    left
    rw [hU]
    have heq : p ++ [V,V,V] = (p ++ [V,V]) ++ [V] := by simp [List.append_assoc]
    rw [heq,z11]; rfl
  have hI_assoc : Scan 6 (u ++ (ds ++ [K])) b v l := by
    simpa [List.append_assoc] using hI
  rcases z1z hI_assoc u (ds ++ [K]) rfl hCu with ⟨c,x,y,s,t0,hI1,hI2,hV,hL⟩
  have hHv : z0Y v = true := by
    have hJ1 := hI1
    rw [hU] at hJ1
    rcases loc_z1n hJ1 with ⟨z,k,_,rfl⟩
    rcases hLo with ⟨w,rfl⟩
    have hLow := loc_z1q hI2
    rw [hV]
    exact e_z27 x y hLow
  have hBv : ∃ p' k,v = p' ++ [V,V,V] /\ b = k * 8 := by
    rcases hHi with ⟨w,rfl⟩
    have hI' : Scan 6 ((u ++ w) ++ zR 6 Q ++ [K]) b v l := by
      simpa [List.append_assoc] using hI
    exact loc_z1o hI'
  rcases hBv with ⟨z,k,hZ,rfl⟩
  rcases z1A hI with ⟨g,hG⟩
  have hS : z1h v * ((8 ^ g : Nat) : Rat) = 1 := by
    have hDs := (zDw hD).1
    rw [z1m,z1m] at hG
    dsimp [z1h] at hG
    rw [hDs] at hG
    nlinarith
  have hZd : 3 <= z1f ds := by
    rcases hLo with ⟨w,rfl⟩
    have hw := (zWn w).2.1
    dsimp [z1f]; linarith
  rcases loc_z1w hI1 hW hI2 (z1v hD) hZd with ⟨hM,hB⟩
  rw [<- hV] at hM hB
  have hB' : z1e v + l <= z1e u + z1f u + (7 / 12) * (z1h u * z1f ds) := by linarith
  refine ⟨k,v,l,g,hI,⟨z,hZ⟩,hHv,hS,hM,hB',?_,?_⟩
  · have hwv := zWn v
    have hloss := loc_z1i hI (loc_z1A (u ++ ds) [K] (loc_z1A u ds hW))
    linarith
  · have hwv := zWn v
    have hwu := zWn u
    have hwds := zWn ds
    have hsu := zSp u
    have hms := z1i v
    nlinarith

lemma loc_z1C {g k : Nat} {s delta : Rat}
    (hS : s * ((8 ^ g : Nat) : Rat) = 1)
    (hB : (6 : Rat) = ((k * 8 : Nat) : Rat) * s + delta * 2)
    (hD : 0 < delta) (hU : delta <= 1 / 64) :
    ∃ n,g = 3 + n /\ 191 * 2 ^ (2 + 3 * n) <= k * 2 /\ k * 2 < 192 * 2 ^ (2 + 3 * n) := by
  have hP_nat := z0C g
  have hP : (0 : Rat) < ((8 ^ g : Nat) : Rat) := Nat.cast_pos.mpr hP_nat
  have hE : ((k * 8 : Nat) : Rat) = (6 - delta * 2) * ((8 ^ g : Nat) : Rat) := by
    have hT : ((k * 8 : Nat) : Rat) * s = 6 - delta * 2 := by linarith
    calc ((k * 8 : Nat) : Rat)
      _ = (((k * 8 : Nat) : Rat) * s) * ((8 ^ g : Nat) : Rat) := by
          rw [mul_assoc,hS,mul_one]
      _ = (6 - delta * 2) * ((8 ^ g : Nat) : Rat) := by rw [hT]
  have hL_q : ((191 * 8 ^ g : Nat) : Rat) <= ((256 * k : Nat) : Rat) := by
    push_cast at hP hE ⊢; nlinarith
  have hL : 191 * 8 ^ g <= 256 * k := Nat.cast_le.mp hL_q
  have hR_q : ((k * 8 : Nat) : Rat) < ((6 * 8 ^ g : Nat) : Rat) := by
    push_cast at hP hE ⊢; nlinarith
  have hR : k * 8 < 6 * 8 ^ g := Nat.cast_lt.mp hR_q
  rcases g with _ | _ | _ | n
  · omega
  · omega
  · omega
  · have hp := (loc_z0Z n).2
    have h3n : n + 1 + 1 + 1 = 3 + n := by omega
    rw [h3n,hp] at hL hR
    exact ⟨n,by omega,by omega,by omega⟩

lemma loc_z1D {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    {H : Nat} {r : zB}
    (hI : Scan a u b v l) (hB : Binary b H r) :
    RIncs a (zTs u (d1 +> default)) (zTs v (t +> r)) := by
  have hb := (z0E hB).1
  cases b with
  | zero => omega
  | succ b =>
    have h1b : b + 1 = 1 + b := by omega
    rw [h1b] at hI hB
    refine loc_z18 hI ?_
    have hR := z0G hB
    have heq : ((1 + b) - 1) * 2 = b * 2 := by omega
    rw [heq] at hR
    have hp := RIncs.pair0 hR
    rwa [zDd] at hp

inductive Good : zB -> Prop where
  | intro (u : zW) (A H : Nat) (ds : zW) :
      zDg A H ds ->
      z1h u * ((2 ^ H : Nat) : Rat) = 1 / 2 ->
      z1e u * 2 + z1f u + z1h u * z1f ds <= 1 / 64 ->
      loc_z1z u -> z0Y u = true -> loc_z0V ds -> loc_z0W ds ->
      Good (zTs (u ++ ds) (d0 +> (d1 +> default)))

lemma loc_z1E {r : zB} (hG : Good r) :
    ∃ r',RIncs 6 r r' /\ Good (t +> r') := by
  rcases hG with ⟨u,A,H,ds,hD,hHs,hF,hU,hW,hLo,hHi⟩
  rcases loc_z1B hD hHs hF hU hW hLo hHi with
    ⟨k,v,l,g,hI,hTv,hV,hS,hM,hL,hPos,hBound⟩
  have hB := loc_z1a hI
  rcases loc_z1C hS hB hPos hBound with ⟨n,rfl,hKl,hKu⟩
  rcases loc_z0X (2 + 3 * n) k hKl hKu with ⟨ds',hD',hLo',hHi',hBin⟩
  refine ⟨zTs v (t +> zTs ds' (d0 +> (d1 +> default))),?_,?_⟩
  · have hR := loc_z1D hI hBin
    simpa [z15,zTs] using hR
  · have hOut : t +> zTs v (t +> zTs ds' (d0 +> (d1 +> default))) =
        zTs ((V :: (v ++ [V])) ++ ds') (d0 +> (d1 +> default)) := by
      simp [z15,zTs]
    rw [hOut]
    have hp1 := (loc_z0Z n).1
    have hp2 := (loc_z0Z n).2
    have h82 : 8 + (2 + 3 * n) = 10 + 3 * n := by omega
    refine Good.intro (V :: (v ++ [V])) _ (8 + (2 + 3 * n)) ds' hD' ?_ ?_ ?_ ?_ hLo' hHi'
    · rw [hp2] at hS
      rw [h82,hp1]
      dsimp [z1h]; rw [z1m]; dsimp [z1h]
      push_cast at hS ⊢
      nlinarith
    · have hZ := z1n hD'
      rw [h82,hp1] at hZ
      have hAeq : (k * 8 - 512 * 2 ^ (2 + 3 * n)) + 512 * 2 ^ (2 + 3 * n) = k * 8 := by omega
      have hAE : (((k * 8 - 512 * 2 ^ (2 + 3 * n) : Nat) : Rat)) + ((512 * 2 ^ (2 + 3 * n) : Nat) : Rat) = ((k * 8 : Nat) : Rat) := by
        exact_mod_cast hAeq
      rw [hp2] at hS
      push_cast at hZ hAE hS hB
      dsimp [z1e,z1f,z1h]
      rw [z1j,z1k,z1m]
      dsimp [z1e,z1f,z1h]
      have hms := z1i v
      have hwu := zWn u
      have hwds := zWn ds
      have hsu := zSp u
      have hsv := zSp v
      nlinarith
    · rcases hTv with ⟨w,rfl⟩
      refine ⟨V :: (w ++ [V]),?_⟩
      simp [List.append_assoc]
    · dsimp [z0Y]
      exact loc_z1A v [V] hV

def loc_zPf : Nat -> Nat -> Option (zW)
  | 0,_ => none
  | _ + 1,0 => none
  | _ + 1,1 => some [Q]
  | fuel + 1,m + 2 =>
    match loc_zPf fuel ((m + 2) / 2) with
    | none => none
    | some ws => some ((if (m + 2) % 2 == 0 then K else Q) :: ws)

lemma loc_z1F (fuel : Nat) :
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
def loc_z1J : e_Choice -> Nat -> Nat
  | CT,n | CP0,n | CP1,n => 1 + n
  | CS00,n | CS01,n => 2 + n * 4
  | CS10,n | CS11,n => 4 + n * 4

def loc_z1K : e_Choice -> Nat -> Nat
  | CT,n => (1 + n) * 2
  | CP0,n | CS00,n | CS10,n => n * 2
  | CP1,n | CS01,n | CS11,n => 1 + n * 2

def loc_z1N : e_Code -> Nat -> zW -> Option (zW)
  | .Stop n,k,u =>
    if k == n * 2 then
      if u.all z23 then loc_zPf 64 (1 + n) else none
    else none
  | .More ch n c,k,u =>
    if k == loc_z1J ch n then
      match zSw (e_z2i ch) u with
      | none => none
      | some w =>
        match loc_z1N c (loc_z1K ch n) w with
        | none => none
        | some v => some (e_z2j ch :: v)
    else none

lemma loc_z1O (c : e_Code) :
    ∀ (k : Nat) (u v : zW),loc_z1N c k u = some v ->
      RIncs k (zTs u default) (zTs v default) := by
  induction c with
  | Stop n =>
    intro k u v hE
    dsimp [loc_z1N] at hE
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
        rcases loc_z1F 64 (1 + n) v hE with ⟨H,hB⟩
        have hR := z0G hB
        have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
        rwa [heq] at hR
  | More ch n c ih =>
    intro k u v hE
    dsimp [loc_z1N] at hE
    cases hk : (k == loc_z1J ch n) with
    | false => rw [hk] at hE; contradiction
    | true =>
      rw [hk] at hE
      dsimp at hE
      have rfl_k : k = loc_z1J ch n := beq_iff_eq.mp hk
      subst rfl_k
      cases hU : zSw (e_z2i ch) u with
      | none => rw [hU] at hE; contradiction
      | some w =>
        rw [hU] at hE
        dsimp at hE
        cases hC : loc_z1N c (loc_z1K ch n) w with
        | none => rw [hC] at hE; contradiction
        | some x =>
          rw [hC] at hE
          injection hE with hE; subst hE
          have rfl_u := z22 (e_z2i ch) u w hU
          subst rfl_u
          have hIH := ih (loc_z1K ch n) w x hC
          cases ch
          · exact RIncs.T hIH
          · exact RIncs.pair0 hIH
          · exact RIncs.pair1 hIH
          · exact RIncs.short00 hIH
          · exact RIncs.short01 hIH
          · exact RIncs.short10 hIH
          · exact RIncs.short11 hIH

def loc_z1P (c : e_Code) (u : zW) : Option (zW) :=
  match loc_z1N c 6 (u ++ [K]) with
  | some v => some (V :: v)
  | none => none

lemma loc_z1Q (c : e_Code) (u v : zW) (h : loc_z1P c u = some v) :
    ∃ r,RIncs 6 (zTs u default) r /\ zTs v default = t +> r := by
  dsimp [loc_z1P] at h
  cases hE : loc_z1N c 6 (u ++ [K]) with
  | none => rw [hE] at h; contradiction
  | some w =>
    rw [hE] at h
    injection h with h; subst h
    refine ⟨zTs w default,?_,rfl⟩
    have hR := loc_z1O c 6 (u ++ [K]) w hE
    simpa [z15,zTs] using hR

inductive loc_Rounds : zB -> zB -> Prop where
  | refl (r : zB) : loc_Rounds r r
  | next {r s t0 : zB} :
      RIncs 6 r s -> loc_Rounds (t +> s) t0 -> loc_Rounds r t0

def loc_z1R : List e_Code -> zW -> Option (zW)
  | [],u => some u
  | c :: cs,u =>
    match loc_z1P c u with
    | none => none
    | some v => loc_z1R cs v

lemma loc_z1S (cs : List e_Code) :
    ∀ (u v : zW),loc_z1R cs u = some v ->
      loc_Rounds (zTs u default) (zTs v default) := by
  induction cs with
  | nil =>
    intro u v h
    injection h with h; subst h
    exact loc_Rounds.refl _
  | cons c cs ih =>
    intro u v h
    dsimp [loc_z1R] at h
    cases hW : loc_z1P c u with
    | none => rw [hW] at h; contradiction
    | some w =>
      rw [hW] at h
      rcases loc_z1Q c u w hW with ⟨r,hR,hEq⟩
      refine loc_Rounds.next hR ?_
      rw [<- hEq]
      exact ih w v h

lemma loc_z1V (u ds : zW)
    (hD : ds.all z25 = true)
    (hS : z1h u * z1h ds = 1 / 2)
    (hF : z1e u * 2 + z1f u + z1h u * z1f ds <= 1 / 64)
    (hU : loc_z1z u) (hW : z0Y u = true) (hLo : loc_z0V ds) (hHi : loc_z0W ds) :
    Good (zTs (u ++ ds) (d0 +> (d1 +> default))) := by
  rcases z26 ds hD with ⟨A,hI⟩
  refine Good.intro u A ds.length ds hI ?_ hF hU hW hLo hHi
  rw [<- (zDw hI).1]
  exact hS

def loc_z1W : zW := [V,Q,Q]

def loc_z1X : List e_Code := [
  (.More CT 5 (.More CS11 2 (.More CP0 4 (.Stop 4)))),
  (.More CT 5 (.More CT 11 (.More CS11 5 (.More CT 10 (.More CP0 21 (.More CP0 41 (.Stop 41))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CS11 11 (.More CT 22 (.More CT 45 (.More CT 91 (.More CS10 45 (.More CP0 89 (.More CP0 177 (.More CP0 353 (.Stop 353)))))))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CS11 23 (.More CT 46 (.More CT 93 (.More CT 187 (.More CS11 93 (.More CT 186 (.More CT 373 (.More CT 747 (.More CS10 373 (.More CP0 745 (.More CS00 372 (.More CS10 185 (.More CS01 92 (.More CP0 184 (.More CP0 367 (.Stop 367)))))))))))))))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CS11 47 (.More CT 94 (.More CT 189 (.More CT 379 (.More CS11 189 (.More CT 378 (.More CT 757 (.More CT 1515 (.More CS11 757 (.More CT 1514 (.More CS00 757 (.More CP0 1513 (.More CT 3025 (.More CT 6051 (.More CS10 3025 (.More CS00 1512 (.More CS10 755 (.More CS00 377 (.More CP1 753 (.More CP0 1506 (.More CP0 3011 (.Stop 3011))))))))))))))))))))))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CS11 95 (.More CT 190 (.More CT 381 (.More CT 763 (.More CS11 381 (.More CT 762 (.More CT 1525 (.More CT 3051 (.More CS11 1525 (.More CT 3050 (.More CS00 1525 (.More CT 3049 (.More CT 6099 (.More CT 12199 (.More CP0 24399 (.More CP0 48797 (.More CT 97593 (.More CT 195187 (.More CT 390375 (.More CS10 195187 (.More CS00 97593 (.More CP0 195185 (.More CS00 97592 (.More CS10 48795 (.More CS01 24397 (.More CP1 48794 (.More CP0 97588 (.More CP0 195175 (.Stop 195175))))))))))))))))))))))))))))))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CT 383 (.More CS11 191 (.More CT 382 (.More CT 765 (.More CT 1531 (.More CS11 765 (.More CT 1530 (.More CT 3061 (.More CT 6123 (.More CS11 3061 (.More CT 6122 (.More CS00 3061 (.More CT 6121 (.More CT 12243 (.More CT 24487 (.More CT 48975 (.More CT 97951 (.More CT 195903 (.More CT 391807 (.More CT 783615 (.More CP0 1567231 (.More CT 3134461 (.More CS10 1567230 (.More CP0 3134459 (.More CT 6268917 (.More CT 12537835 (.More CT 25075671 (.More CS10 12537835 (.More CS00 6268917 (.More CS00 3134458 (.More CP0 6268915 (.More CS01 3134457 (.More CP0 6268914 (.More CS10 3134456 (.More CP0 6268911 (.More CP1 12537821 (.More CP1 25075642 (.More CP0 50151284 (.More CP0 100302567 (.Stop 100302567)))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CT 383 (.More CT 767 (.More CS11 383 (.More CT 766 (.More CT 1533 (.More CT 3067 (.More CS11 1533 (.More CT 3066 (.More CT 6133 (.More CT 12267 (.More CS11 6133 (.More CT 12266 (.More CS00 6133 (.More CT 12265 (.More CT 24531 (.More CT 49063 (.More CT 98127 (.More CT 196255 (.More CT 392511 (.More CT 785023 (.More CT 1570047 (.More CT 3140095 (.More CT 6280191 (.More CS11 3140095 (.More CT 6280190 (.More CT 12560381 (.More CT 25120763 (.More CT 50241527 (.More CP0 100483055 (.More CS00 50241527 (.More CT 100483053 (.More CS10 50241526 (.More CT 100483051 (.More CS11 50241525 (.More CT 100483050 (.More CT 200966101 (.More CT 401932203 (.More CT 803864407 (.More CT 1607728815 (.More CS10 803864407 (.More CS00 401932203 (.More CS00 200966101 (.More CP0 401932201 (.More CP1 803864401 (.More CP0 1607728802 (.More CS11 803864400 (.More CP1 1607728800 (.More CP1 3215457600 (.More CP0 6430915200 (.More CS10 3215457599 (.More CP0 6430915197 (.More CS01 3215457598 (.More CP1 6430915196 (.More CP1 12861830392 (.More CP0 25723660784 (.More CP0 51447321567 (.Stop 51447321567)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
]

def loc_z1Y : zW := [V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,K,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,K,V,Q,V,Q,V,V,V,V,V,Q,K,K,V,V,V,Q,V,V,V,Q,V,K,V,V,V,V]

def loc_z1Z : zW := [K,K,K,K,K,Q,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q]

lemma loc_z20 :
    loc_Rounds (zTs loc_z1W default) (zTs (loc_z1Y ++ loc_z1Z) (d0 +> (d1 +> default))) := by
  have h1 : loc_Rounds (zTs loc_z1W default) (zTs (loc_z1Y ++ loc_z1Z ++ [K,Q]) default) := by
    apply loc_z1S loc_z1X
    decide
  simpa [z15,zTs] using h1

lemma loc_z21 :
    Good (zTs (loc_z1Y ++ loc_z1Z) (d0 +> (d1 +> default))) := by
  apply loc_z1V
  · decide
  · norm_num [loc_z1Y,loc_z1Z,z1h]
  · norm_num [loc_z1Y,loc_z1Z,z1e,z1f,z1h]
  · exact ⟨loc_z1Y.take (loc_z1Y.length - 3),by decide⟩
  · decide
  · exact ⟨loc_z1Z.drop 2,by decide⟩
  · exact ⟨loc_z1Z.take (loc_z1Z.length - 6),by decide⟩

inductive Num : Nat -> zF -> List Call -> Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)

def loc_z22 (k : Nat) (r r' : zB) : Prop :=
  ∀ w hs,Num k w hs -> Side hs (w +> r) r'

lemma loc_z23 {r r' : zB} (h : loc_z22 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl

lemma loc_z24 {n : Nat} {r r' : zB}
    (hI : loc_z22 ((1 + n) * 2) r r') : loc_z22 (1 + n) (t +> r) (t +> r') := by
  intro w hs hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil]
    refine zSc (z0n m) ?_
    have hN2 : Num ((1 + n) * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : (1 + n) * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil]
    refine zSc (z0o m) ?_
    have hN2 : Num ((1 + n) * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
      have hm : (1 + n) * 2 = 2 + (1 + m * 2) * 2 := by omega
      rw [hm]; exact Num.even (1 + m * 2)
    simpa using hI [] _ hN2

lemma loc_z25 {n : Nat} {r r' : zB}
    (hI : loc_z22 (n * 2) r r') : loc_z22 (1 + n) (d1 +> (d0 +> r)) (t +> r') := by
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
      have hr' := loc_z23 hI
      subst hr'
      rw [<- append_assoc t one r]
      exact zSc z0e (Side.nil r)
    | succ m =>
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      refine zSc (z0p m) ?_
      have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : n * 2 = 2 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil,<- append_assoc d1 d0 r]
    refine zSc (z0q m) ?_
    have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : n * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2

lemma loc_z26 {n : Nat} {r r' : zB}
    (hI : loc_z22 (1 + n * 2) r r') : loc_z22 (1 + n) (d1 +> (d1 +> r)) (t +> r') := by
  intro w hs hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil,<- append_assoc d1 d1 r]
    refine zSc (z0r m) ?_
    have hN1 : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ (m * 2)) := by
      have hm : 1 + n * 2 = 1 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (m * 2)
    simpa using hI [] _ hN1
  | @even m =>
    simp only [append_nil,<- append_assoc d1 d1 r]
    refine zSc (z0s m) ?_
    have hN1 : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ (1 + m * 2)) := by
      have hm : 1 + n * 2 = 1 + (1 + m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (1 + m * 2)
    simpa using hI [] _ hN1

lemma loc_z27 {n : Nat} {r r' : zB}
    (hI : loc_z22 (n * 2) r r') : loc_z22 (2 + n * 4) (d0 +> r) (d0 +> r') := by
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
      have hr' := loc_z23 hI
      subst hr'
      rw [<- append_assoc d0 one r]
      exact zSc z0i (Side.nil r)
    | succ n =>
      have heq : (n + 1) * 2 = 2 + n * 2 := by omega
      rw [heq]
      refine zSc (z0t n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        rw [heq]; exact Num.even n
      simpa using hI [] _ hN2

lemma loc_z28 {n : Nat} {r r' : zB}
    (hI : loc_z22 (1 + n * 2) r r') : loc_z22 (2 + n * 4) (d1 +> r) (d0 +> r') := by
  intro w hs hN
  generalize hk : 2 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = n * 2 := by omega
    subst hm
    refine zSc (z0u n) ?_
    simpa using hI [] _ (Num.odd n)

lemma loc_z29 {n : Nat} {r r' : zB}
    (hI : loc_z22 (n * 2) r r') : loc_z22 (4 + n * 4) (d0 +> r) (d1 +> r') := by
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
      have hr' := loc_z23 hI
      subst hr'
      rw [<- append_assoc d1 one r]
      exact zSc z0v (Side.nil r)
    | succ n =>
      have heq : 1 + (n + 1) * 2 = 3 + n * 2 := by omega
      rw [heq]
      refine zSc (z0w n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        have heq2 : (n + 1) * 2 = 2 + n * 2 := by omega
        rw [heq2]; exact Num.even n
      simpa using hI [] _ hN2

lemma loc_z2a {n : Nat} {r r' : zB}
    (hI : loc_z22 (1 + n * 2) r r') : loc_z22 (4 + n * 4) (d1 +> r) (d1 +> r') := by
  intro w hs hN
  generalize hk : 4 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = 1 + n * 2 := by omega
    subst hm
    refine zSc (z0x n) ?_
    simpa using hI [] _ (Num.odd n)

lemma loc_z2b {k : Nat} {r r' : zB} (hI : RIncs k r r') :
    loc_z22 k r r' := by
  induction hI with
  | zero r =>
    intro w hs hN
    generalize hk : 0 = k0 at hN
    cases hN with
    | zero => exact Side.nil (one +> r)
    | odd _ => omega
    | even _ => omega
  | T _ ih => exact loc_z24 ih
  | pair0 _ ih => exact loc_z25 ih
  | pair1 _ ih => exact loc_z26 ih
  | short00 _ ih => exact loc_z27 ih
  | short01 _ ih => exact loc_z28 ih
  | short10 _ ih => exact loc_z29 ih
  | short11 _ ih => exact loc_z2a ih

lemma loc_z2c {r r' : zB} (hI : RIncs 6 r r') :
    (zCf r) [target_tm]⊢⁺ zCf (t +> r') := by
  have hC := loc_z2b hI [] ([.cj] ++ [.ch] ^ 2) (Num.even 2)
  have hS := zSc z0y hC
  dsimp at hS
  rcases hS with _ | ⟨hca,hrest⟩
  rcases hrest with _ | ⟨hch,hnil⟩
  cases hnil
  exact zPt (z0z r)
    (zPt (hca ([1] +> default))
      (zPt (z0A _) (hch lh)))

lemma loc_z2d {r r' : zB} (h : loc_Rounds r r') :
    (zCf r) [target_tm]⊢* zCf r' := by
  induction h with
  | refl _ => exact ⟨0,rfl⟩
  | next hR _ ih =>
    rcases loc_z2c hR with ⟨n,_,hn⟩
    rcases ih with ⟨m,hm⟩
    exact ⟨n + m,zMt target_tm _ _ _ n m hn hm⟩

lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl

lemma loc_z2e (m : Nat) :
    ∃ N ≥ m,∃ r,multiStep target_tm (init []) N = some (zCf r) /\ Good r := by
  induction m with
  | zero =>
    rcases z0B with ⟨k1,_,hk1⟩
    rcases loc_z2d loc_z20 with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,_,zMt target_tm _ _ _ k1 k2 hk1 hk2,loc_z21⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,r,h_ms,h_good⟩
    rcases loc_z1E h_good with ⟨r',hR,h_good'⟩
    rcases loc_z2c hR with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,t +> r',zMt target_tm _ _ _ N k h_ms h_step_k,h_good'⟩

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
  rcases loc_z2e (n + 1) with ⟨N,hN,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

end BusyBeaver.M_1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1REHHH
