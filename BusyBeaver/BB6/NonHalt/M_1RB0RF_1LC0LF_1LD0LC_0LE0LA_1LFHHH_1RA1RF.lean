/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter
public import BusyBeaver.Calculi.WordCalculusA
public import BusyBeaver.Calculi.WordCalculusB
public import BusyBeaver.Calculi.WordCalculusC
public import BusyBeaver.Calculi.WordCalculusD
public import BusyBeaver.Calculi.WordCalculusE

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RF_1LC0LF_1LD0LC_0LE0LA_1LFHHH_1RA1RF

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_1LC0LF_1LD0LC_0LE0LA_1LFHHH_1RA1RF"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
open Counter

namespace Solution

set_option linter.deprecated false
set_option linter.dupNamespace false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {Γ₀ Λ₀ α β γ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
variable {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000000
@[simp] theorem zMz (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) : multiStep M config 0 = some config := rfl
@[simp] theorem zMo (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) : multiStep M config 1 = step M config := rfl
@[simp] theorem zMs (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep,Function.iterate_succ',Function.comp_apply,multiStep]
@[simp] theorem z00 : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] theorem zDh : (default : HalfTape).head = 0 := rfl
@[simp] theorem zDt : (default : HalfTape).tail = default := rfl
@[simp] theorem append_nil (s : HalfTape) : ([] : BitWord) +> s = s := rfl
@[simp] theorem append_cons (a : Fin 2) (l : BitWord) (s : HalfTape) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[simp] theorem append_assoc (l1 l2 : BitWord) (s : HalfTape) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append,append_cons,ih]
theorem zSm {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 c_2 : Cfg Γ₀ Λ₀) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
theorem z01 {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 c_2 : Cfg Γ₀ Λ₀) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1,by decide,zSm tm c_1 c_2 h⟩
theorem zMa {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 : Cfg Γ₀ Λ₀) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ,zMs,ih,Option.bind_assoc]
    simp_rw [zMs]
theorem zMt {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 c_2 c_3 : Cfg Γ₀ Λ₀) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa,h₁]; simp [h₂]
theorem zPs {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 : Cfg Γ₀ Λ₀} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n,_,hn⟩ := h; exact ⟨n,hn⟩
theorem zPt {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,n_pos,hn⟩ := h₁; obtain ⟨m,m_pos,hm⟩ := h₂
  exact ⟨n + m,by omega,zMt tm c_1 c_2 c_3 n m hn hm⟩
theorem z02 {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,n_pos,hn⟩ := h₁; obtain ⟨m,hm⟩ := h₂
  exact ⟨n + m,lt_of_lt_of_le n_pos (Nat.le_add_right n m),zMt tm c_1 c_2 c_3 n m hn hm⟩
theorem z03 {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  z02 (z01 tm c_1 c_2 h₁) h₂
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.ListBlank.head_cons,zDh]); rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,z00,zDh,zDt])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))
abbrev t : BitWord := [1,1,0,0]
abbrev d0 : BitWord := [0,0]
abbrev d1 : BitWord := [1,0]
abbrev one : BitWord := [1]
abbrev lh : HalfTape := default
abbrev w_pre : BitWord := t ++ t ++ [0] ++ t ++ t ++ one
abbrev w_word : BitWord := w_pre
@[simp] theorem zDd : d0 +> (default : HalfTape) = default := by
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
def zCw : Call -> BitWord
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
  | .ca => [1,0,1,0,1,0]
def zCR (l : HalfTape) (c : Call) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  ((l <+ zCw c) {{zCs c}}> r)
def zCL (l : HalfTape) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (l <{{C}} ([0] +> r))
def zCf (q : Nat) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  zCL lh ((w_pre ++ (t ^ (2 + q) ++ (d1 ++ one))) +> r)
def z04 (c : Call) (r1 r2 : HalfTape) : Prop :=
  ∀ l,(zCR l c r1) [target_tm]⊢⁺ (zCL l r2)
inductive Side : List Call -> HalfTape -> HalfTape -> Prop where
  | nil (r : HalfTape) : Side [] r r
  | cons {c : Call} {ls : List Call} {r1 r2 r3 : HalfTape} :
      z04 c r1 r2 -> Side ls r2 r3 -> Side (c :: ls) r1 r3
def Seg (ls_in ls_out : List Call) (w1 w2 : BitWord) : Prop :=
  ∀ r1 r2,Side ls_out r1 r2 -> Side ls_in (w1 +> r1) (w2 +> r2)
@[simp] theorem z05 {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] theorem zLp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] theorem zLp' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] theorem z06 {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l
theorem z07 {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm,zLp,zLp,ih,List.append_assoc]
theorem z08 {ls1 ls2 : List Call} {r1 r2 r3 : HalfTape}
    (h1 : Side ls1 r1 r2) (h2 : Side ls2 r2 r3) : Side (ls1 ++ ls2) r1 r3 := by
  induction h1 with
  | nil _ => exact h2
  | cons hc _ ih => exact Side.cons hc (ih h2)
theorem z09 {ls1 ls2 : List Call} {r1 r3 : HalfTape}
    (h : Side (ls1 ++ ls2) r1 r3) : ∃ r2,Side ls1 r1 r2 /\ Side ls2 r2 r3 := by
  induction ls1 generalizing r1 with
  | nil => exact ⟨r1,Side.nil r1,h⟩
  | cons c ls1 ih =>
    rcases h with _ | ⟨hc,hrest⟩
    rcases ih hrest with ⟨r2,h1,h2⟩
    exact ⟨r2,Side.cons hc h1,h2⟩
theorem z0a (w : BitWord) : Seg [] [] w w := by
  intro r1 r2 h; cases h; exact Side.nil (w +> r1)
theorem z0b (ls : List Call) : Seg ls ls [] [] := by
  intro r1 r2 h; exact h
theorem zSc {ls1 ls2 : List Call} {w1 w2 : BitWord} {r1 r2 : HalfTape}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
    Side ls1 (w1 +> r1) (w2 +> r2) :=
  h1 r1 r2 h2
theorem zSg {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : BitWord}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3 := by
  intro r1 r3 h
  rcases z09 h with ⟨r2,ha,hb⟩
  exact z08 (h1 r1 r2 ha) (h2 r2 r3 hb)
theorem zS0 {ls1 ls2 ls3 : List Call} {w1 w2 v1 v2 : BitWord}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls2 ls3 v1 v2) :
    Seg ls1 ls3 (w1 ++ v1) (w2 ++ v2) := by
  intro r1 r2 h
  rw [append_assoc,append_assoc]
  exact h1 (v1 +> r1) (v2 +> r2) (h2 r1 r2 h)
theorem zS4 {c : Call} {w1 w2 : BitWord}
    (h1 : ∀ l r,(zCR l c (w1 +> r)) [target_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)
theorem zS2 {c_in c_out : Call} {w1 w2 mid : BitWord}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [target_tm]⊢⁺ (zCR (mid +> l) c_out r))
    (h2 : ∀ l r,(zCL (mid +> l) r) [target_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1) (zPt (hc1 (mid +> l)) (h2 l r2))
theorem zS5 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : BitWord}
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
theorem z0c : Seg [.cp] [.ch] t (t ++ [0]) :=
  zS2 (mid := [1,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0d : Seg [.cj] [.ch] t (t ++ one) :=
  zS2 (mid := [1,1,0,1,1])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0e : Seg [.ch] [.cj] (t ++ [0]) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH2 : Seg [.ch] [.cj,.ch] (t ++ one) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0f : Seg [.ch] [.ch,.ch] t t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0g : Seg [.cp] [] (d1 ++ d0) (t ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d1 d0 t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0h : Seg [.cj] [.cj] (d1 ++ d0) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1 d0; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0i : Seg [.cp] [.cp] (d1 ++ d1) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0j : Seg [.cj] [.cp,.ch] (d1 ++ d1) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0k : Seg [.cj] [] d0 (d0 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH1 : Seg [.ch] [] (d0 ++ one) (d1 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH3 : Seg [.ch] [.cj] (d1 ++ one) d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
theorem z0l : Seg [.cj] [.cp] d1 d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
theorem zH0 : Seg [.ch] [] d0 d1 :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1; simp only [append_cons,append_nil]; execute)
theorem zH4 : Seg [.ch] [.ch] d1 d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
theorem H_T (n : Nat) : Seg ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t := by
  induction n with
  | zero => exact z0a t
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [zLp,h_eq,z07]
    exact zSg z0f ih
theorem zSa {w2 : BitWord} (hw : Seg [.ch,.ch] [.ch] w2 w2) (n : Nat) :
    Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) w2 w2 := by
  induction n with
  | zero => exact z0a w2
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq,z07,zLp]
    exact zSg hw ih
theorem z0m : Seg [.ch,.ch] [.ch] d0 d0 :=
  zSg zH0 zH4
theorem z0n : Seg [.ch,.ch] [.ch] d1 d1 :=
  zSg zH4 zH0
theorem z0o (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d0 d0 :=
  zSa z0m n
theorem z0p (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ n) d0 d1 := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg zH0 (zSa z0n n)
theorem z0q (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d1 d1 :=
  zSa z0n n
theorem z0r (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ (1 + n)) d1 d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg zH4 (zSa z0m n)
theorem z0s (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0c z0e) (H_T n)
theorem z0t (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0d zH2) (H_T n)
theorem z0u (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0g zH2) (H_T n)
theorem z0v (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0h (H_T n)
theorem z0w (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0i (H_T n)
theorem z0x (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using zSg z0j (H_T n)
theorem z0y (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0k (zSg zH1 zH3)
  have h1 := zSg h0 (zSa z0m n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
theorem z0z (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0l (zSa z0m n)
theorem z0A : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0k zH1
theorem z0B (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0k (zSg zH1 (zSg zH3 zH0))
  have h1 := zSg h0 (zSa z0n n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
theorem z0C (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1 := zSg z0l zH0
  have h1 := zSg h0 (zSa z0n n)
  simpa only [zLp',List.cons_append,List.nil_append] using h1
theorem z0D (n : Nat) : Seg (([Call.ch] ^ n) ++ [.cj,.ch]) (([Call.ch] ^ (1 + n * 2)) ++ [.cj,.ch]) t t := by
  have h1 : Seg (([Call.ch] ^ n) ++ [.cj,.ch]) (([Call.ch] ^ (n * 2)) ++ [.ch,.cj,.ch]) t t :=
    zSg (H_T n) (z0t 0)
  have heq : (([Call.ch] ^ (n * 2)) ++ [.ch,.cj,.ch]) = (([Call.ch] ^ (1 + n * 2)) ++ [.cj,.ch]) := by
    have h2 : 1 + n * 2 = n * 2 + 1 := by omega
    rw [h2,z07,z06,List.append_assoc]
    rfl
  rwa [heq] at h1
theorem z0E (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([.cj] ++ [.ch] ^ n) (d1 ++ one) d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using zSg zH3 (z0o n)
theorem z0F (n : Nat) : Seg (([Call.ch] ^ (1 + n * 2)) ++ [.cj,.ch]) ([.cj] ++ [.ch] ^ n) (d1 ++ one) (d1 ++ one) := by
  simpa only [List.append_nil] using zSg (z0E n) z0A
theorem z0G (q : Nat) :
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
theorem z0H : Seg [.ca] [.cj,.ch] w_pre (w_pre ++ t) :=
  zS5
    (mid1 := [1,0,1,1,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1,0])
    (mid2 := [1,0,1,0,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs w_pre t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL w_pre t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0I (r : HalfTape) :
    (zCL lh r) [target_tm]⊢⁺ (zCR lh .ca r) := by
  unfold zCL zCR lh zCw zCs
  simp only [append_cons,append_nil,z00]
  execute
open WordCalculus Word ChoiceE
local notation "WordList" => List Word
inductive Num : Nat -> BitWord -> List Call -> Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)
theorem loc_z2t {k : Nat} (hK : 0 < k) : ∃ hs,Num k [] hs := by
  rcases even_or_odd_mul_two k with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · cases a with
    | zero => omega
    | succ a =>
      have heq : (a + 1) * 2 = 2 + a * 2 := by omega
      rw [heq]; exact ⟨[.cj] ++ [.ch] ^ a,Num.even a⟩
  · exact ⟨[.cp] ++ [.ch] ^ a,Num.odd a⟩
theorem loc_z2u {k : Nat} {hs hs' : List Call} (h1 : Num k [] hs) (h2 : Num k [] hs') :
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
def loc_z2v (k : Nat) (r r' : HalfTape) : Prop :=
  ∀ w hs,Num k w hs -> Side hs (w +> r) r'
theorem loc_z2w {r r' : HalfTape} (h : loc_z2v 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl
theorem loc_z2x {n : Nat} {r r' : HalfTape}
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
      simpa using hI [] _ hN2
theorem loc_z2y {n : Nat} {r r' : HalfTape}
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
      simpa using hI [] _ hN2
theorem loc_z2z {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hZ : A = 0) :
    evalWords da default = default := by
  induction hD with
  | nil => rfl
  | @zero A H u _ ih =>
    have hA0 : A = 0 := by omega
    rw [evalWords,ih hA0,zDd]
  | one _ => omega
theorem loc_z2A {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hPos : 0 < A) :
    loc_z2v ((A - 1) * 2) default (evalWords da default) := by
  induction hD with
  | nil => omega
  | @zero A H u _ ih =>
    have hA_pos : 0 < A := by omega
    have hIH := ih hA_pos
    have hs := loc_z2x hIH
    rw [zDd] at hs
    have heq : (A * 2 - 1) * 2 = 2 + (A - 1) * 4 := by omega
    rw [evalWords]
    rwa [heq]
  | @one A H u hDu ih =>
    cases A with
    | zero =>
      have h_side : evalWords (Q :: u) default = one +> default := by
        rw [evalWords,loc_z2z hDu rfl]
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
      rw [evalWords]
      rwa [heq]
theorem zEd {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (hI : WordEffect n u b v) :
    ∀ {A H : Nat},DigitVal A H v -> Seg ([Call.ch] ^ n) ([Call.ch] ^ b) (wordsToBits u) (wordsToBits v) := by
  induction hI with
  | nil n =>
    intro A H _
    exact z0b _
  | T _ _ =>
    intro A H hD
    exact False.elim (digitVal_not_cons_V hD)
  | d00 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0o _) (ih hD')
  | d01 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0p _) (ih hD')
  | d10 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0q _) (ih hD')
  | d11 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0r _) (ih hD')
theorem loc_z2B {n : Nat} {hs hs' : List Call}
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
theorem loc_z2C {n : Nat} {hs hs' : List Call}
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
theorem loc_z2D {n : Nat} {hs hs' : List Call}
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
theorem loc_z2E {n : Nat} {hs hs' : List Call}
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
theorem loc_z2F {n : Nat} {hs hs' : List Call}
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
theorem loc_z2G {n : Nat} {hs hs' : List Call}
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
theorem loc_z2H {n : Nat} {hs hs' : List Call}
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
theorem loc_z2I {k : Nat} {v : WordList} {k' : Nat} {w : WordList} {a b : Rat}
    (hI : PhaseScan k v k' w a b) :
    ∀ {u : WordList} {n n' : Nat} {hs hs' : List Call},
      WordEffect n u n' v -> Num k [] hs -> Num k' [] hs' ->
      Seg (([Call.ch] ^ n) ++ hs) (([Call.ch] ^ n') ++ hs') (wordsToBits u) (wordsToBits w) := by
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
    change WordEffect n0 u0 n1 ([Q,K] ++ u) at hE
    rcases wordEffect_split_output [Q,K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases loc_z2t hPos with ⟨hs0,hN0⟩
    have hD10 : DigitVal 1 2 [Q,K] := DigitVal.one (DigitVal.zero DigitVal.nil)
    have hStep := zSg (zEd hL hD10) (loc_z2C hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @pair1 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q,Q] ++ u) at hE
    rcases wordEffect_split_output [Q,Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases loc_z2t (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD11 : DigitVal 3 2 [Q,Q] := DigitVal.one (DigitVal.one DigitVal.nil)
    have hStep := zSg (zEd hL hD11) (loc_z2D hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short00 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([K] ++ u) at hE
    rcases wordEffect_split_output [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases loc_z2t hPos with ⟨hs0,hN0⟩
    have hD0 : DigitVal 0 1 [K] := DigitVal.zero DigitVal.nil
    have hStep := zSg (zEd hL hD0) (loc_z2E hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short01 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q] ++ u) at hE
    rcases wordEffect_split_output [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases loc_z2t (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : DigitVal 1 1 [Q] := DigitVal.one DigitVal.nil
    have hStep := zSg (zEd hL hD1) (loc_z2F hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short10 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([K] ++ u) at hE
    rcases wordEffect_split_output [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases loc_z2t hPos with ⟨hs0,hN0⟩
    have hD0 : DigitVal 0 1 [K] := DigitVal.zero DigitVal.nil
    have hStep := zSg (zEd hL hD0) (loc_z2G hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short11 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q] ++ u) at hE
    rcases wordEffect_split_output [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases loc_z2t (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : DigitVal 1 1 [Q] := DigitVal.one DigitVal.nil
    have hStep := zSg (zEd hL hD1) (loc_z2H hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
theorem loc_z2J {k : Nat} {v : WordList} {k' : Nat} {w : WordList} {a b : Rat}
    (hI : PhaseScan k v k' w a b) {u : WordList} {r r' : HalfTape}
    (hE : WordEffect 0 u 0 v) (hK : 0 < k') (hC : loc_z2v k' r r') :
    loc_z2v k (evalWords u r) (evalWords w r') := by
  intro w0 hs hN
  have hPosK : 0 < k := phaseScan_pos_of_out_pos hI hK
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
  rwa [wordsToBits_append_tape,wordsToBits_append_tape] at hSide
theorem loc_z2K {q : Nat} {orig out : WordList} (hS : EStep q orig out) :
    loc_z2v (4 * 2 ^ q) (evalWords orig default) (evalWords out default) := by
  rcases hS with ⟨eff,n,v,a0,b0,J,da,hE,hI,hPos,hDA⟩
  have hBlank : evalWords [K] default = default := by simp [evalWords,d0]
  have hC : loc_z2v (n * 2) default (evalWords da default) := by
    have heq : n * 2 = ((1 + n) - 1) * 2 := by omega
    rw [heq]
    exact loc_z2A hDA (by omega)
  have hRun := loc_z2J hI hE (by omega : 0 < n * 2) hC
  rwa [evalWords_append,hBlank,<- evalWords_append] at hRun
theorem loc_z2L (q : Nat) :
    Seg [.cj,.ch] ([.cj] ++ [.ch] ^ (2 ^ q - 1)) (t ^ (1 + q) ++ (d1 ++ one)) (t ^ (1 + q) ++ (d1 ++ one)) := by
  have hpos := pow_two_pos q
  have hT := z0G (1 + q) 0
  have heq : (1 + 0) * 2 ^ (1 + q) - 1 = 1 + (2 ^ q - 1) * 2 := by
    rw [pow_two_one_add]; omega
  rw [heq] at hT
  dsimp at hT
  exact zS0 hT (z0F (2 ^ q - 1))
theorem loc_z2M (q : Nat) :
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
theorem loc_z2N (q : Nat) {r r' : HalfTape} (hI : loc_z2v (4 * 2 ^ q) r r') :
    (zCf q r) [target_tm]⊢⁺ zCf (q + 1) r' := by
  have hpos := pow_two_pos q
  have h_num : Num (4 * 2 ^ q) [] ([.cj] ++ [.ch] ^ (2 ^ (1 + q) - 1)) := by
    have heq : 4 * 2 ^ q = 2 + (2 ^ (1 + q) - 1) * 2 := by rw [pow_two_one_add]; omega
    rw [heq]; exact Num.even (2 ^ (1 + q) - 1)
  have hC := hI [] ([.cj] ++ [.ch] ^ (2 ^ (1 + q) - 1)) h_num
  have hS := zSc (loc_z2M q) hC
  rcases hS with _ | ⟨hca,hnil⟩
  cases hnil
  exact zPt (z0I _) (hca lh)
theorem loc_z2O {q : Nat} {orig out : WordList} (hS : EStep q orig out) :
    (zCf q (evalWords orig default)) [target_tm]⊢⁺ zCf (q + 1) (evalWords out default) :=
  loc_z2N q (loc_z2K hS)
theorem loc_z2P {h : Nat} {u : WordList} {j : Nat} {v : WordList} (hR : ERounds h u j v) :
    (zCf h (evalWords u default)) [target_tm]⊢* zCf j (evalWords v default) := by
  induction hR with
  | refl _ _ => exact ⟨0,rfl⟩
  | next hS _ ih =>
    rcases loc_z2O hS with ⟨n,_,hn⟩
    rcases ih with ⟨m,hm⟩
    exact ⟨n + m,zMt target_tm _ _ _ n m hn hm⟩
def loc_z2Q : WordList := [Q,V,K,K,Q]
abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev CCfg.head (c : CCfg) : Fin 2 := c.cur
abbrev CCfg.left (c : CCfg) : List (Fin 2) := c.l
abbrev CCfg.right (c : CCfg) : List (Fin 2) := c.r
abbrev loc_z2R (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev loc_z2Y (c : CCfg) : Option CCfg := Counter.bstep target_tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep target_tm n c
theorem zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (loc_z2R c1) [target_tm]⊢⁺ (loc_z2R c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩
def loc_z31 : CCfg :=
  ⟨A,0,[],[]⟩
def loc_z32 : CCfg :=
  ⟨C,1,[1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1,0,1],[0,1,1,0,1,1,0,0,0,0,0,0,1]⟩
def loc_z33 : CCfg :=
  ⟨C,0,[],[0,1,1,0,0,1,1,0,0,0,1,1,0,0,1,1,0,0,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,1,1,0,0,0,0,0,0,1]⟩
set_option maxRecDepth 4000000 in
theorem loc_z34 : zCm loc_z31 1000 = some loc_z32 := by decide
set_option maxRecDepth 4000000 in
theorem loc_z35 : zCm loc_z32 72 = some loc_z33 := by decide
theorem loc_z36 :
    (init []) [target_tm]⊢⁺ zCf 2 (evalWords loc_z2Q default) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = loc_z2R loc_z31 := rfl
  have h_end : loc_z2R loc_z33 = zCf 2 (evalWords loc_z2Q default) := by
    unfold loc_z2R zCf zCL lh
    rw [<- wordsToBits_append_tape,<- append_assoc,<- append_assoc]
    have h_list : ([0] ++ (w_pre ++ (t ^ (2 + 2) ++ (d1 ++ one)))) ++ wordsToBits loc_z2Q = loc_z33.right ++ [0] := by decide
    rw [h_list,append_assoc]
    simp only [append_cons,append_nil,z00]
    rfl
  rw [h_init,<- h_end]
  exact zPt (zTc (by decide) loc_z34) (zTc (by decide) loc_z35)
def loc_z37 : List CodeE := [
  (.More CS11 3 (.More CT 4 (.More CP0 9 (.More CP0 17 (.Stop 17))))),
  (.More CS11 7 (.More CT 12 (.More CT 23 (.More CT 45 (.More CP0 91 (.More CS00 45 (.More CS01 22 (.More CP0 44 (.Stop 44))))))))),
  (.More CS11 15 (.More CT 28 (.More CT 55 (.More CT 109 (.More CT 217 (.More CP1 435 (.More CT 868 (.More CS00 434 (.More CS10 216 (.More CP0 431 (.More CS01 215 (.More CP0 430 (.Stop 430))))))))))))),
  (.More CS11 31 (.More CT 60 (.More CT 119 (.More CT 237 (.More CT 473 (.More CT 945 (.More CT 1889 (.More CP0 3779 (.More CT 7555 (.More CS11 3777 (.More CT 7552 (.More CS00 3776 (.More CS10 1887 (.More CS00 943 (.More CS00 471 (.More CP0 941 (.More CP1 1881 (.More CP0 3762 (.Stop 3762))))))))))))))))))),
  (.More CS11 63 (.More CT 124 (.More CT 247 (.More CT 493 (.More CT 985 (.More CT 1969 (.More CT 3937 (.More CT 7873 (.More CT 15745 (.More CS10 7872 (.More CT 15741 (.More CS11 7870 (.More CP0 15740 (.More CS10 7869 (.More CT 15735 (.More CT 31469 (.More CT 62937 (.More CS10 31468 (.More CP0 62935 (.More CP1 125869 (.More CP0 251738 (.More CS10 125868 (.More CS11 62933 (.More CP1 125866 (.More CP0 251732 (.Stop 251732)))))))))))))))))))))))))),
  (.More CS11 127 (.More CT 252 (.More CT 503 (.More CT 1005 (.More CT 2009 (.More CT 4017 (.More CT 8033 (.More CT 16065 (.More CT 32129 (.More CS10 16064 (.More CT 32125 (.More CS10 16062 (.More CT 32121 (.More CS10 16060 (.More CT 32117 (.More CT 64233 (.More CT 128465 (.More CS10 64232 (.More CT 128461 (.More CT 256921 (.More CT 513841 (.More CS10 256920 (.More CS11 128459 (.More CT 256916 (.More CT 513831 (.More CS10 256915 (.More CS00 128457 (.More CS00 64228 (.More CS10 32113 (.More CS00 16056 (.More CS10 8027 (.More CP1 16053 (.More CP1 32106 (.More CP0 64212 (.More CS10 32105 (.More CP1 64209 (.More CP1 128418 (.More CP0 256836 (.Stop 256836))))))))))))))))))))))))))))))))))))))),
  (.More CS11 255 (.More CT 508 (.More CT 1015 (.More CT 2029 (.More CT 4057 (.More CT 8113 (.More CT 16225 (.More CT 32449 (.More CT 64897 (.More CS10 32448 (.More CT 64893 (.More CS10 32446 (.More CT 64889 (.More CS10 32444 (.More CT 64885 (.More CT 129769 (.More CT 259537 (.More CS10 129768 (.More CT 259533 (.More CT 519065 (.More CT 1038129 (.More CS10 519064 (.More CS11 259531 (.More CT 519060 (.More CT 1038119 (.More CS10 519059 (.More CS00 259529 (.More CP0 519057 (.More CP0 1038113 (.More CT 2076223 (.More CT 4152445 (.More CT 8304889 (.More CS10 4152444 (.More CT 8304885 (.More CT 16609769 (.More CT 33219537 (.More CS10 16609768 (.More CS10 8304883 (.More CS01 4152441 (.More CP0 8304882 (.More CP0 16609763 (.More CP1 33219525 (.More CP0 66439050 (.More CS10 33219524 (.More CS11 16609761 (.More CP1 33219522 (.More CP1 66439044 (.More CP0 132878088 (.Stop 132878088))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CS11 511 (.More CT 1020 (.More CT 2039 (.More CT 4077 (.More CT 8153 (.More CT 16305 (.More CT 32609 (.More CT 65217 (.More CT 130433 (.More CS10 65216 (.More CT 130429 (.More CS10 65214 (.More CT 130425 (.More CS10 65212 (.More CT 130421 (.More CT 260841 (.More CT 521681 (.More CS10 260840 (.More CT 521677 (.More CT 1043353 (.More CT 2086705 (.More CS10 1043352 (.More CS11 521675 (.More CT 1043348 (.More CT 2086695 (.More CS10 1043347 (.More CS00 521673 (.More CT 1043343 (.More CT 2086685 (.More CT 4173369 (.More CT 8346737 (.More CT 16693473 (.More CS10 8346736 (.More CT 16693469 (.More CT 33386937 (.More CT 66773873 (.More CS10 33386936 (.More CP0 66773871 (.More CT 133547739 (.More CT 267095477 (.More CT 534190953 (.More CT 1068381905 (.More CS10 534190952 (.More CS11 267095475 (.More CT 534190948 (.More CT 1068381895 (.More CT 2136763789 (.More CS10 1068381894 (.More CS10 534190946 (.More CS10 267095472 (.More CS10 133547735 (.More CP0 267095469 (.More CP0 534190937 (.More CP1 1068381873 (.More CP0 2136763746 (.More CS10 1068381872 (.More CS10 534190935 (.More CS01 267095467 (.More CP1 534190934 (.More CP0 1068381868 (.More CS10 534190933 (.More CP1 1068381865 (.More CP1 2136763730 (.More CP1 4273527460 (.More CP0 8547054920 (.Stop 8547054920)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CS11 1023 (.More CT 2044 (.More CT 4087 (.More CT 8173 (.More CT 16345 (.More CT 32689 (.More CT 65377 (.More CT 130753 (.More CT 261505 (.More CS10 130752 (.More CT 261501 (.More CS10 130750 (.More CT 261497 (.More CS10 130748 (.More CT 261493 (.More CT 522985 (.More CT 1045969 (.More CS10 522984 (.More CT 1045965 (.More CT 2091929 (.More CT 4183857 (.More CS10 2091928 (.More CS11 1045963 (.More CT 2091924 (.More CT 4183847 (.More CS10 2091923 (.More CS00 1045961 (.More CT 2091919 (.More CT 4183837 (.More CT 8367673 (.More CT 16735345 (.More CT 33470689 (.More CS10 16735344 (.More CT 33470685 (.More CT 66941369 (.More CT 133882737 (.More CS10 66941368 (.More CT 133882733 (.More CT 267765465 (.More CT 535530929 (.More CT 1071061857 (.More CT 2142123713 (.More CS10 1071061856 (.More CS11 535530927 (.More CT 1071061852 (.More CT 2142123703 (.More CT 4284247405 (.More CS10 2142123702 (.More CS11 1071061850 (.More CP0 2142123700 (.More CT 4284247397 (.More CT 8568494793 (.More CT 17136989585 (.More CT 34273979169 (.More CS10 17136989584 (.More CP0 34273979167 (.More CT 68547958331 (.More CT 137095916661 (.More CS10 68547958330 (.More CT 137095916657 (.More CT 274191833313 (.More CT 548383666625 (.More CT 1096767333249 (.More CS10 548383666624 (.More CS10 274191833311 (.More CS00 137095916655 (.More CP1 274191833309 (.More CP1 548383666618 (.More CP0 1096767333236 (.More CP0 2193534666471 (.More CP1 4387069332941 (.More CP0 8774138665882 (.More CP0 17548277331763 (.More CS00 8774138665881 (.More CS00 4387069332940 (.More CS11 2193534666469 (.More CP1 4387069332938 (.More CP0 8774138665876 (.More CS10 4387069332937 (.More CS01 2193534666468 (.More CP1 4387069332936 (.More CP1 8774138665872 (.More CP1 17548277331744 (.More CP0 35096554663488 (.Stop 35096554663488))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CS11 2047 (.More CT 4092 (.More CT 8183 (.More CT 16365 (.More CT 32729 (.More CT 65457 (.More CT 130913 (.More CT 261825 (.More CT 523649 (.More CS10 261824 (.More CT 523645 (.More CS10 261822 (.More CT 523641 (.More CS10 261820 (.More CT 523637 (.More CT 1047273 (.More CT 2094545 (.More CS10 1047272 (.More CT 2094541 (.More CT 4189081 (.More CT 8378161 (.More CS10 4189080 (.More CS11 2094539 (.More CT 4189076 (.More CT 8378151 (.More CS10 4189075 (.More CS00 2094537 (.More CT 4189071 (.More CT 8378141 (.More CT 16756281 (.More CT 33512561 (.More CT 67025121 (.More CS10 33512560 (.More CT 67025117 (.More CT 134050233 (.More CT 268100465 (.More CS10 134050232 (.More CT 268100461 (.More CT 536200921 (.More CT 1072401841 (.More CT 2144803681 (.More CT 4289607361 (.More CS10 2144803680 (.More CS11 1072401839 (.More CT 2144803676 (.More CT 4289607351 (.More CT 8579214701 (.More CS10 4289607350 (.More CS11 2144803674 (.More CT 4289607346 (.More CT 8579214691 (.More CT 17158429381 (.More CT 34316858761 (.More CT 68633717521 (.More CS10 34316858760 (.More CT 68633717517 (.More CT 137267435033 (.More CT 274534870065 (.More CS10 137267435032 (.More CT 274534870061 (.More CT 549069740121 (.More CT 1098139480241 (.More CT 2196278960481 (.More CS10 1098139480240 (.More CP0 2196278960479 (.More CT 4392557920955 (.More CT 8785115841909 (.More CT 17570231683817 (.More CT 35140463367633 (.More CT 70280926735265 (.More CT 140561853470529 (.More CT 281123706941057 (.More CS11 140561853470528 (.More CP0 281123706941056 (.More CT 562247413882109 (.More CT 1124494827764217 (.More CS10 562247413882108 (.More CS10 281123706941053 (.More CT 562247413882103 (.More CT 1124494827764205 (.More CT 2248989655528409 (.More CT 4497979311056817 (.More CS10 2248989655528408 (.More CS10 1124494827764203 (.More CS00 562247413882101 (.More CS00 281123706941050 (.More CS10 140561853470524 (.More CS11 70280926735261 (.More CP0 140561853470522 (.More CP0 281123706941043 (.More CS00 140561853470521 (.More CS01 70280926735260 (.More CP1 140561853470520 (.More CP1 281123706941040 (.More CP0 562247413882080 (.More CP0 1124494827764159 (.More CP0 2248989655528317 (.More CP1 4497979311056633 (.More CP0 8995958622113266 (.More CP0 17991917244226531 (.More CS00 8995958622113265 (.More CS00 4497979311056632 (.More CS11 2248989655528315 (.More CP1 4497979311056630 (.More CP0 8995958622113260 (.More CS10 4497979311056629 (.More CP1 8995958622113257 (.More CP1 17991917244226514 (.More CP1 35983834488453028 (.More CP1 71967668976906056 (.More CP0 143935337953812112 (.Stop 143935337953812112))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
]
def loc_z38 : WordList := [Q,V,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,V,V,Q,Q,V,V,Q,K,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,V,V,V,Q,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,Q,K,K,Q,Q,V,V,K,K,V,V,V,V,V,V,V,V,K,K,Q,V,V,Q,V,V,V,V,V]
def loc_z39 : WordList := [Q,K,K,K,Q,K,K,Q,K,Q,Q,Q,Q,K,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,K,K,K,K,Q,Q,K,Q,K,Q,Q,K,Q,Q,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def loc_z3a : WordList := [K,K,K,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,Q,Q,K,Q,K,K,K,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
set_option maxRecDepth 4000000 in
theorem loc_z3b :
    ERounds 2 loc_z2Q 12 (loc_z38 ++ loc_z39) := by
  have h1 : ERounds 2 loc_z2Q (2 + loc_z37.length) (loc_z38 ++ loc_z39) := by
    apply evalERounds_sound loc_z37
    decide
  exact h1
set_option maxRecDepth 4000000 in
theorem loc_z3c :
    EGood 12 (loc_z38 ++ loc_z39) := by
  apply eGood_of_check 12 loc_z38 loc_z39 loc_z3a
  · decide
  · exact EGuard.D _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · norm_num [loc_z38,loc_z3a,wordMass,wordMassK,wordScale]
theorem zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
theorem loc_z3d (m : Nat) :
    ∃ N ≥ m,∃ h w,multiStep target_tm (init []) N = some (zCf h (evalWords w default)) /\ EGood h w := by
  induction m with
  | zero =>
    rcases loc_z36 with ⟨k1,_,hk1⟩
    rcases loc_z2P loc_z3b with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,12,loc_z38 ++ loc_z39,
      zMt target_tm _ _ _ k1 k2 hk1 hk2,loc_z3c⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,h,w,h_ms,h_good⟩
    rcases eGood_progress h_good with ⟨w',hStep,h_good'⟩
    rcases loc_z2O hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,h + 1,w',
      zMt target_tm _ _ _ N k h_ms h_step_k,h_good'⟩

end Solution



set_option linter.deprecated false
set_option linter.dupNamespace false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000
open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases loc_z3d (n + 1) with ⟨N,hN,_,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end BusyBeaver.M_1RB0RF_1LC0LF_1LD0LC_0LE0LA_1LFHHH_1RA1RF
