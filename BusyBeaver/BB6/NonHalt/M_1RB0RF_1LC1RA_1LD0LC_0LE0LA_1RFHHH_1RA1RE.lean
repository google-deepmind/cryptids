/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.WordCalculusA
public import BusyBeaver.Calculi.WordCalculusB
public import BusyBeaver.Calculi.WordCalculusC
public import BusyBeaver.Calculi.WordCalculusD
public import BusyBeaver.Calculi.WordCalculusE

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RF_1LC1RA_1LD0LC_0LE0LA_1RFHHH_1RA1RE

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_1LC1RA_1LD0LC_0LE0LA_1RFHHH_1RA1RE"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
namespace Solution

set_option linter.deprecated false
set_option linter.dupNamespace false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {Γ₀ Λ₀ α β γ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
variable {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
set_option maxHeartbeats 8000000
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
abbrev lh : HalfTape := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
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
  | .ca => [1,1,1,0,1,0]
def zCR (l : HalfTape) (c : Call) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  ((l <+ zCw c) {{zCs c}}> r)
def zCL (l : HalfTape) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (l <{{C}} ([0] +> r))
def zCf (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  zCL lh r
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
theorem z0b : Seg [.cp] [.cj] t t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0c : Seg [.cj] [.cj,.ch] t t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0d : Seg [.ch] [.ch,.ch] t t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0e : Seg [.cp] [] (d1 ++ d0) (t ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d1 d0 t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH2 : Seg [.ch] [.cj,.ch] (t ++ one) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0f : Seg [.cj] [.cj] (d1 ++ d0) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1 d0; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0g : Seg [.cp] [.cp] (d1 ++ d1) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0h : Seg [.cj] [.cp,.ch] (d1 ++ d1) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0i : Seg [.cj] [] d0 (d0 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH1 : Seg [.ch] [] (d0 ++ one) (d1 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH3 : Seg [.ch] [.cj] (d1 ++ one) d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
theorem z0j : Seg [.cj] [.cp] d1 d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
theorem zH0 : Seg [.ch] [] d0 d1 :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1; simp only [append_cons,append_nil]; execute)
theorem zH4 : Seg [.ch] [.ch] d1 d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
theorem z0k : Seg [.ca] [.cj] [] t := by
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
theorem zS3 (n : Nat) : Seg ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t := by
  induction n with
  | zero => exact z0a t
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [zLp,h_eq,z07]
    exact zSg z0d ih
theorem zSa {w2 : BitWord} (hw : Seg [.ch,.ch] [.ch] w2 w2) (n : Nat) :
    Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) w2 w2 := by
  induction n with
  | zero => exact z0a w2
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq,z07,zLp]
    exact zSg hw ih
theorem z0l : Seg [.ch,.ch] [.ch] d0 d0 :=
  zSg zH0 zH4
theorem z0m : Seg [.ch,.ch] [.ch] d1 d1 :=
  zSg zH4 zH0
theorem z0n (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) t t :=
  zSg z0b (zS3 n)
theorem z0o (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using zSg z0c (zS3 n)
theorem z0p (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0e zH2) (zS3 n)
theorem z0q (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0f (zS3 n)
theorem z0r (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0g (zS3 n)
theorem z0s (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using zSg z0h (zS3 n)
theorem z0t (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0i (zSg zH1 zH3)
  have h1 := zSg h0 (zSa z0l n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
theorem z0u (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0j (zSa z0l n)
theorem z0v : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0i zH1
theorem z0w (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0i (zSg zH1 (zSg zH3 zH0))
  have h1 := zSg h0 (zSa z0m n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
theorem z0x (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1 := zSg z0j zH0
  have h1 := zSg h0 (zSa z0m n)
  simpa only [zLp',List.cons_append,List.nil_append] using h1
theorem z0y : Seg [.ca] [.cj] [] t :=
  z0k
theorem z0z (r : HalfTape) :
    (zCf r) [target_tm]⊢⁺ (zCR ([1,1] +> default) .ca r) := by
  unfold zCf zCL zCR lh zCw zCs
  simp only [append_cons,append_nil]
  execute
theorem z0A (r : HalfTape) :
    (zCL ([1,1] +> default) r) [target_tm]⊢⁺ (zCR lh .cj r) := by
  unfold zCL zCR lh zCw zCs
  simp only [append_cons,append_nil]
  execute
def z0B : Cfg (Fin 2) (Fin 6) :=
  (([1,1,1,0,1,0,1,0,1,1,1,0,1] +> default) {{C}}> ([1,1] +> default))
def z0C : Cfg (Fin 2) (Fin 6) :=
  (([] +> default) {{D}}> ([0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,0,0,1] +> default))
def z0D : Cfg (Fin 2) (Fin 6) :=
  (([0,1,1,1,0,1,0,1,0,1,0,1,1] +> default) {{C}}> ([1,0,0,0,0,0,1,1] +> default))
def z0E : Cfg (Fin 2) (Fin 6) :=
  (([1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1] +> default) {{A}}> ([1,0,0,0,1,1] +> default))
def z0F : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1] +> default) {{A}}> ([0,1,0,1] +> default))
def z0G : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1] +> default) {{C}}> ([1,1,1,0,0,1,0,1,0,1] +> default))
def z0H : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1] +> default) {{A}}> ([0,0,1,0,0,1,0,0,0,0,0,1] +> default))
def z0I : Cfg (Fin 2) (Fin 6) :=
  (([1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1] +> default) {{A}}> ([0,1,0,0,0,1] +> default))
def z0J : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1] +> default) {{C}}> ([0,0,0,1,1,0,0,1,0,1,0,1,0,1] +> default))
def z0K : Cfg (Fin 2) (Fin 6) :=
  (([1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1] +> default) {{C}}> ([0,0,0,0,0,0,0,0,0,0,0,1] +> default))
def z0L : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1,0,1,1,1,0,1,0,1,0,1] +> default) {{A}}> ([1,0,0,1,1,0,0,1,1,0,0,1,0,1,0,0,0,0,0,1] +> default))
def z0M : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1] +> default) {{A}}> ([1,0,0,0,0,1,0,1,0,0,0,1] +> default))
def z0N : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1] +> default) {{A}}> ([1,0,1,0,0,0,0,0,0,0,0,1,0,1] +> default))
def z0O : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1,0,1,0,1,0,1,0,1,0,1,0,1] +> default) {{A}}> ([0,1,1,0,0,1,1,0,0,1,0,1,0,0,0,1,0,1] +> default))
def z0P : Cfg (Fin 2) (Fin 6) :=
  (([1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1] +> default) {{A}}> ([0,0,0,1,0,1,0,1,0,1] +> default))
theorem z0Q : (init []) [target_tm]⊢⁺ z0B := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]; unfold z0B; simp only [append_cons,append_nil]; execute
theorem z0R : z0B [target_tm]⊢⁺ z0C := by
  unfold z0B z0C; simp only [append_cons,append_nil]; execute
theorem z0S : z0C [target_tm]⊢⁺ z0D := by
  unfold z0C z0D; simp only [append_cons,append_nil]; execute
theorem z0T : z0D [target_tm]⊢⁺ z0E := by
  unfold z0D z0E; simp only [append_cons,append_nil]; execute
theorem pre_z0U : z0E [target_tm]⊢⁺ z0F := by
  unfold z0E z0F; simp only [append_cons,append_nil]; execute
theorem pre_z0V : z0F [target_tm]⊢⁺ z0G := by
  unfold z0F z0G; simp only [append_cons,append_nil]; execute
theorem pre_z0W : z0G [target_tm]⊢⁺ z0H := by
  unfold z0G z0H; simp only [append_cons,append_nil]; execute
theorem pre_z0X : z0H [target_tm]⊢⁺ z0I := by
  unfold z0H z0I; simp only [append_cons,append_nil]; execute
theorem pre_z0Y : z0I [target_tm]⊢⁺ z0J := by
  unfold z0I z0J; simp only [append_cons,append_nil]; execute
theorem pre_z0Z : z0J [target_tm]⊢⁺ z0K := by
  unfold z0J z0K; simp only [append_cons,append_nil]; execute
theorem pre_z10 : z0K [target_tm]⊢⁺ z0L := by
  unfold z0K z0L; simp only [append_cons,append_nil]; execute
theorem pre_z11 : z0L [target_tm]⊢⁺ z0M := by
  unfold z0L z0M; simp only [append_cons,append_nil]; execute
theorem pre_z12 : z0M [target_tm]⊢⁺ z0N := by
  unfold z0M z0N; simp only [append_cons,append_nil]; execute
theorem pre_z13 : z0N [target_tm]⊢⁺ z0O := by
  unfold z0N z0O; simp only [append_cons,append_nil]; execute
theorem pre_z14 : z0O [target_tm]⊢⁺ z0P := by
  unfold z0O z0P; simp only [append_cons,append_nil]; execute
theorem pre_z15 : z0P [target_tm]⊢⁺
    zCf (([1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,0,1,0,1,0,1,0] : BitWord) +> default) := by
  unfold z0P zCf zCL lh
  simp only [append_cons,append_nil,z00]
  execute
theorem pre_z16 :
    (init []) [target_tm]⊢⁺
      zCf (([1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,0,1,0,1,0,1,0] : BitWord) +> default) :=
  zPt z0Q
    (zPt z0R
      (zPt z0S
        (zPt z0T
          (zPt pre_z0U
            (zPt pre_z0V
              (zPt pre_z0W
                (zPt pre_z0X
                  (zPt pre_z0Y
                    (zPt pre_z0Z
                      (zPt pre_z10
                        (zPt pre_z11
                          (zPt pre_z12
                            (zPt pre_z13
                              (zPt pre_z14 pre_z15))))))))))))))
inductive RIncs : Nat -> HalfTape -> HalfTape -> Prop where
  | zero (r : HalfTape) : RIncs 0 r (one +> r)
  | T {n : Nat} {r r' : HalfTape} :
      RIncs ((1 + n) * 2) r r' -> RIncs (1 + n) (t +> r) (t +> r')
  | pair0 {n : Nat} {r r' : HalfTape} :
      RIncs (n * 2) r r' -> RIncs (1 + n) (d1 +> (d0 +> r)) (t +> r')
  | pair1 {n : Nat} {r r' : HalfTape} :
      RIncs (1 + n * 2) r r' -> RIncs (1 + n) (d1 +> (d1 +> r)) (t +> r')
  | short00 {n : Nat} {r r' : HalfTape} :
      RIncs (n * 2) r r' -> RIncs (2 + n * 4) (d0 +> r) (d0 +> r')
  | short01 {n : Nat} {r r' : HalfTape} :
      RIncs (1 + n * 2) r r' -> RIncs (2 + n * 4) (d1 +> r) (d0 +> r')
  | short10 {n : Nat} {r r' : HalfTape} :
      RIncs (n * 2) r r' -> RIncs (4 + n * 4) (d0 +> r) (d1 +> r')
  | short11 {n : Nat} {r r' : HalfTape} :
      RIncs (1 + n * 2) r r' -> RIncs (4 + n * 4) (d1 +> r) (d1 +> r')
inductive Binary : Nat -> Nat -> HalfTape -> Prop where
  | one : Binary 1 1 (d1 +> default)
  | zero {n H : Nat} {r : HalfTape} :
      Binary (1 + n) H r -> Binary (2 + n * 2) (1 + H) (d0 +> r)
  | two {n H : Nat} {r : HalfTape} :
      Binary (1 + n) H r -> Binary (3 + n * 2) (1 + H) (d1 +> r)

open WordCalculus Word
local notation "WordList" => List Word

theorem loc_z17 (n : Nat) : 0 < 8 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem loc_z19 {A H : Nat} {r : HalfTape} (h : Binary A H r) :
    0 < A /\ 0 < H /\ 2 ^ H <= A * 2 /\ A < 2 ^ H := by
  induction h with
  | one => decide
  | @zero n H r _ ih =>
    rw [pow_two_one_add H]; omega
  | @two n H r _ ih =>
    rw [pow_two_one_add H]; omega

theorem loc_z1a (n : Nat) : ∃ H r,Binary (1 + n) H r := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨1,d1 +> default,Binary.one⟩
    | succ m =>
      rcases even_or_odd_mul_two m with ⟨a,rfl⟩ | ⟨a,rfl⟩
      · rcases ih a (by omega) with ⟨H0,r,hI⟩
        refine ⟨1 + H0,d0 +> r,?_⟩
        have heq : 1 + (a * 2 + 1) = 2 + a * 2 := by omega
        rw [heq]; exact Binary.zero hI
      · rcases ih a (by omega) with ⟨H0,r,hI⟩
        refine ⟨1 + H0,d1 +> r,?_⟩
        have heq : 1 + ((1 + a * 2) + 1) = 3 + a * 2 := by omega
        rw [heq]; exact Binary.two hI

theorem loc_z1b {A H : Nat} {r : HalfTape} (h : Binary A H r) :
    RIncs ((A - 1) * 2) default r := by
  induction h with
  | one =>
    have h0 := RIncs.zero (default : HalfTape)
    have hd : d1 +> (default : HalfTape) = one +> default := by simp [d1,one]
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

theorem loc_z1n {A H : Nat} {u : WordList} (h1 : DigitVal A H u) :
    ∀ {B J : Nat} {r : HalfTape},Binary B J r -> Binary (A + B * 2 ^ H) (H + J) (evalWords u r) := by
  induction h1 with
  | nil =>
    intro B J r h2
    simpa [evalWords] using h2
  | @zero A H u _ ih =>
    intro B J r h2
    have hI := ih h2
    have hB := loc_z19 hI
    have hI' : Binary (1 + (A + B * 2 ^ H - 1)) (H + J) (evalWords u r) := by
      have heq : 1 + (A + B * 2 ^ H - 1) = A + B * 2 ^ H := by omega
      rwa [heq]
    have h3 := Binary.zero hI'
    have heq1 : 2 + (A + B * 2 ^ H - 1) * 2 = A * 2 + B * 2 ^ (1 + H) := by
      rw [pow_two_one_add H,Nat.mul_add]; omega
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    simpa [evalWords,heq1,heq2] using h3
  | @one A H u _ ih =>
    intro B J r h2
    have hI := ih h2
    have hB := loc_z19 hI
    have hI' : Binary (1 + (A + B * 2 ^ H - 1)) (H + J) (evalWords u r) := by
      have heq : 1 + (A + B * 2 ^ H - 1) = A + B * 2 ^ H := by omega
      rwa [heq]
    have h3 := Binary.two hI'
    have heq1 : 3 + (A + B * 2 ^ H - 1) * 2 = (1 + A * 2) + B * 2 ^ (1 + H) := by
      rw [pow_two_one_add H,Nat.mul_add]; omega
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    simpa [evalWords,heq1,heq2] using h3

def loc_z1p (ds : WordList) : Prop := ∃ w,ds = Q :: (List.replicate 1 K ++ w)

def loc_z1q (ds : WordList) : Prop := ∃ w,ds = w ++ List.replicate 5 Q

theorem loc_z1r (n : Nat) : DigitVal 0 n (List.replicate n K) := by
  induction n with
  | zero => exact DigitVal.nil
  | succ n ih =>
    have h0 := DigitVal.zero ih
    have heq : 1 + n = n + 1 := by omega
    simpa [List.replicate,heq] using h0

theorem loc_z1s (n : Nat) :
    Binary (2 ^ (n + 1) - 1) (n + 1) (evalWords (List.replicate (n + 1) Q) default) := by
  rw [replicate_succ_append,evalWords_append]
  dsimp [evalWords]
  have hpos := pow_two_pos n
  have hB := loc_z1n (digitVal_replicate_Q n) Binary.one
  have heq : (2 ^ n - 1) + 1 * 2 ^ n = 2 ^ (n + 1) - 1 := by
    rw [Nat.pow_succ]; omega
  rwa [heq] at hB

theorem loc_z1t (r k : Nat) (hL : 31 * 2 ^ r <= k) (hU : k < 32 * 2 ^ r) :
    ∃ ds,DigitVal (1 + k * 4) (7 + r) ds /\ loc_z1p ds /\ loc_z1q ds /\
      Binary (1 + k * 4) (7 + r) (evalWords ds default) := by
  let a := k - 31 * 2 ^ r
  have hA : a + 31 * 2 ^ r = k := by omega
  have ha_lt : a < 2 ^ r := by omega
  rcases exists_digitVal_of_lt_pow r a ha_lt with ⟨v,hD⟩
  have hLow : DigitVal 1 2 (Q :: List.replicate 1 K) := by
    have h1 := DigitVal.one (loc_z1r 1)
    simpa using h1
  have hHigh : DigitVal k (r + 5) (v ++ List.replicate 5 Q) := by
    have hApp := digitVal_append hD (digitVal_replicate_Q 5)
    have heq : a + (2 ^ 5 - 1) * 2 ^ r = k := by
      change a + 31 * 2 ^ r = k
      exact hA
    rwa [heq] at hApp
  have hHighB : Binary k (r + 5) (evalWords (v ++ List.replicate 5 Q) default) := by
    rw [evalWords_append]
    have hB := loc_z1n hD (loc_z1s 4)
    have heq : a + (2 ^ 5 - 1) * 2 ^ r = k := by
      change a + 31 * 2 ^ r = k
      exact hA
    rwa [heq] at hB
  refine ⟨(Q :: List.replicate 1 K) ++ (v ++ List.replicate 5 Q),?_,⟨v ++ List.replicate 5 Q,rfl⟩,
    ⟨(Q :: List.replicate 1 K) ++ v,by rw [List.append_assoc]⟩,?_⟩
  · have hApp := digitVal_append hLow hHigh
    have heq1 : 1 + k * 2 ^ 2 = 1 + k * 4 := by ring
    have heq2 : 2 + (r + 5) = 7 + r := by omega
    rwa [heq1,heq2] at hApp
  · rw [evalWords_append]
    have hB := loc_z1n hLow hHighB
    have heq1 : 1 + k * 2 ^ 2 = 1 + k * 4 := by ring
    have heq2 : 2 + (r + 5) = 7 + r := by omega
    rwa [heq1,heq2] at hB

theorem loc_z1u (n : Nat) : 2 ^ (3 * n) = 8 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq : 3 * (n + 1) = 3 * n + 3 := by omega
    rw [heq,Nat.pow_add,ih,Nat.pow_succ]; ring

theorem loc_z1D {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) :
    ∀ {r r' : HalfTape},RIncs b r r' -> RIncs a (evalWords u r) (evalWords v r') := by
  induction h with
  | nil _ => intro r r' hR; exact hR
  | T _ ih => intro r r' hR; exact RIncs.T (ih hR)
  | pair0 _ ih => intro r r' hR; exact RIncs.pair0 (ih hR)
  | pair1 _ ih => intro r r' hR; exact RIncs.pair1 (ih hR)
  | short00 _ ih => intro r r' hR; exact RIncs.short00 (ih hR)
  | short01 _ ih => intro r r' hR; exact RIncs.short01 (ih hR)
  | short10 _ ih => intro r r' hR; exact RIncs.short10 (ih hR)
  | short11 _ ih => intro r r' hR; exact RIncs.short11 (ih hR)

theorem loc_z1F {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) :
    (a : Rat) = (b : Rat) * wordScale v + (wordMassQ v + l) * 2 := by
  induction h with
  | nil k => simp [wordMassQ,wordScale]
  | T _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | pair0 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | pair1 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | short00 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | short01 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | short10 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | short11 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith

theorem loc_z1J {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) : wordScale v <= wordScale u := by
  induction h with
  | nil _ => simp [wordScale]
  | T _ ih => dsimp [wordScale]; linarith
  | @pair0 _ u _ _ _ _ _ => have hp := wordScale_pos u; dsimp [wordScale]; linarith
  | @pair1 _ u _ _ _ _ _ => have hp := wordScale_pos u; dsimp [wordScale]; linarith
  | short00 _ ih => dsimp [wordScale]; linarith
  | short01 _ ih => dsimp [wordScale]; linarith
  | short10 _ ih => dsimp [wordScale]; linarith
  | short11 _ ih => dsimp [wordScale]; linarith

theorem loc_z1K {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) (he : hasQKSubword u = true) : wordScale v * 8 <= wordScale u := by
  induction h with
  | nil _ => contradiction
  | T _ ih => dsimp [hasQKSubword,wordScale] at he ⊢; have := ih he; linarith
  | pair0 hS _ => have := loc_z1J hS; dsimp [wordScale]; linarith
  | pair1 hS _ => have := loc_z1J hS; dsimp [wordScale]; linarith
  | short00 _ ih => dsimp [hasQKSubword,wordScale] at he ⊢; have := ih he; linarith
  | @short01 n u k v l hS ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [hasQKSubword,wordScale] at he ih ⊢; have := ih he; linarith
      | K => exact False.elim (not_scan_odd_cons_K n u' k v l hS)
      | Q => dsimp [hasQKSubword,wordScale] at he ih ⊢; have := ih he; linarith
  | short10 _ ih => dsimp [hasQKSubword,wordScale] at he ⊢; have := ih he; linarith
  | @short11 n u k v l hS ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [hasQKSubword,wordScale] at he ih ⊢; have := ih he; linarith
      | K => exact False.elim (not_scan_odd_cons_K n u' k v l hS)
      | Q => dsimp [hasQKSubword,wordScale] at he ih ⊢; have := ih he; linarith

theorem loc_z1O {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) (he : hasQKSubword u = true) : 0 < l := by
  induction h with
  | nil _ => contradiction
  | T _ ih => dsimp [hasQKSubword] at he; have := ih he; linarith
  | pair0 hI _ => have := scan_mass_bounds hI; linarith
  | pair1 hI _ => have := scan_mass_bounds hI; linarith
  | short00 hI _ => have := scan_mass_bounds hI; linarith
  | @short01 n u k v l hI ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [hasQKSubword] at he; have := ih he; linarith
      | K => exact False.elim (not_scan_odd_cons_K n u' k v l hI)
      | Q => dsimp [hasQKSubword] at he; have := ih he; linarith
  | short10 hI _ => have := scan_mass_bounds hI; linarith
  | @short11 n u k v l hI ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [hasQKSubword] at he; have := ih he; linarith
      | K => exact False.elim (not_scan_odd_cons_K n u' k v l hI)
      | Q => dsimp [hasQKSubword] at he; have := ih he; linarith

theorem loc_z1Q (n : Nat) :
    ∀ (a b : Nat) (v : WordList) (l : Rat),
      Scan a (List.replicate n V) b v l ->
      v = List.replicate n V /\ b = a * 2 ^ n /\ l = 0 := by
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

theorem loc_z1W {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (hI : Scan a (Q :: K :: u) b v l) :
    ∃ n w s,a = 1 + n /\ Scan (n * 2) u b w s /\ v = V :: w /\ l = (1 + s) * (1 / 2) := by
  cases hI with
  | @pair0 n _ _ w s hJ =>
    exact ⟨n,w,s,rfl,hJ,rfl,rfl⟩
  | @short01 n _ _ _ _ hJ =>
    exact False.elim (not_scan_odd_cons_K n u b _ _ hJ)
  | @short11 n _ _ _ _ hJ =>
    exact False.elim (not_scan_odd_cons_K n u b _ _ hJ)

theorem loc_z1X {a : Nat} {ds : WordList} {b : Nat} {v : WordList} {l : Rat}
    (hI : Scan a (ds ++ [K]) b v l)
    (hw : ∃ w,ds = Q :: K :: w)
    (hD : ∃ A H,DigitVal A H ds)
    (hZ : 2 <= wordMassK ds) :
    wordMass v <= wordMassK ds * (1 / 4) /\ wordMass v + l <= wordMassK ds * (3 / 4) := by
  rcases hw with ⟨w,rfl⟩
  rcases hD with ⟨A,H,hD⟩
  cases hD with
  | one hJ =>
    cases hJ with
    | zero hK =>
      rcases loc_z1W hI with ⟨n,x,s,_,hJ',rfl,rfl⟩
      have hB := scan_tailDefect_bound hJ' (tailDefect_append_K_of_digitVal hK)
      rcases hB with ⟨hM,hL,_⟩
      have hZw := (wordMass_nonneg w).2.1
      dsimp [wordMassK,wordMass] at hZ ⊢
      constructor <;> linarith

theorem loc_z1Y {m : Nat} {u : WordList} {A H : Nat} {ds : WordList}
    (hD : DigitVal A H ds)
    (hS : wordScale u * ((2 ^ H : Nat) : Rat) = 1)
    (hM : 1 <= m)
    (hF : wordMass u + wordMassK u < 1 / 2)
    (hW : ∃ w,ds = Q :: K :: w) :
    ∃ b x l c y s,
      Scan (m * 2) u b x l /\ Scan b (ds ++ [K]) c y s /\ 0 < c := by
  rcases hW with ⟨w,rfl⟩
  have hm_q : (1 : Rat) <= (m : Rat) := by exact_mod_cast hM
  have hEx1 : (wordMass u + wordMassK u) * 2 < ((m * 2 : Nat) : Rat) := by
    push_cast; linarith
  rcases exists_scan_of_mass_lt u m hEx1 with ⟨b,x,l,hI,hB_pos⟩
  have hBounds := scan_mass_bounds hI
  have hSplit_x := wordMass_eq_add x
  have hPos_x := wordMass_nonneg x
  have hDelt : wordMassQ x + l < 1 / 2 := by linarith
  have hBudget_eq := loc_z1F hI
  have hBudget : 1 < (b : Rat) * wordScale x := by
    push_cast at hBudget_eq; linarith
  have hRest : (wordMass (w ++ [K]) + wordMassK (w ++ [K]) + 2) * wordScale x <= 1 := by
    rw [<- (digitVal_scale_and_mass hD).1] at hS
    cases hD with
    | one hJ =>
      cases hJ with
      | zero hK =>
        have hDw := digitVal_scale_and_mass hK
        have hSc := loc_z1J hI
        have hPos_w := wordMass_nonneg w
        have hSplit_w := wordMass_eq_add w
        have hSc_x := wordScale_pos x
        have hSc_u := wordScale_pos u
        have hSc_w := wordScale_pos w
        dsimp [wordScale] at hS
        rw [wordMass_append,wordMassK_append]
        dsimp [wordMass,wordMassK]
        nlinarith
  cases b with
  | zero => omega
  | succ b =>
    have hSc_x := wordScale_pos x
    have hEx2 : (wordMass (w ++ [K]) + wordMassK (w ++ [K])) * 2 < ((b * 2 : Nat) : Rat) := by
      push_cast at hBudget ⊢
      nlinarith
    rcases exists_scan_of_mass_lt (w ++ [K]) b hEx2 with ⟨c,y,s,hJ,hC_pos⟩
    refine ⟨1 + b,x,l,c,V :: y,(1 + s) * (1 / 2),?_,?_,hC_pos⟩
    · have heq : 1 + b = b + 1 := by omega
      rwa [heq]
    · exact Scan.pair0 hJ

theorem loc_z20 (r a : Nat) (u : WordList) (b : Nat) (v : WordList) (l : Rat)
    (hI : Scan a (u ++ List.replicate (1 + r * 2) Q ++ [K]) b v l) :
    ∃ w k,v = w ++ List.replicate (1 + r) V /\ b = k * 2 ^ (1 + r) := by
  rcases split_trailing_Q u with ⟨p,n,rfl,hP⟩
  have hE : (p ++ List.replicate n Q) ++ List.replicate (1 + r * 2) Q ++ [K] =
      p ++ (List.replicate (1 + r * 2 + n) Q ++ [K]) := by
    have heq : 1 + r * 2 + n = n + (1 + r * 2) := by omega
    rw [heq,List.replicate_add n (1 + r * 2)]
    simp only [List.append_assoc]
  rw [hE] at hI
  rcases scan_split_of_splitCond hI p (List.replicate (1 + r * 2 + n) Q ++ [K]) rfl (Or.inl hP) with ⟨c,x,y,s,t0,_,hK,rfl,_⟩
  rcases scan_add_Q_K_inv n r c b y t0 hK with ⟨w,k,rfl,rfl⟩
  exact ⟨x ++ w,k,by rw [List.append_assoc],rfl⟩

theorem loc_z21 {ds : WordList} (h : loc_z1p ds) : ∃ w,ds = Q :: K :: w := by
  rcases h with ⟨w,rfl⟩
  exact ⟨w,rfl⟩

theorem loc_z22 {ds : WordList} (h : loc_z1p ds) : 2 <= wordMassK ds := by
  rcases h with ⟨w,rfl⟩
  have hw := (wordMass_nonneg w).2.1
  dsimp [List.replicate,wordMassK]
  linarith

theorem loc_z23 {m : Nat} {u : WordList} {A H : Nat} {ds : WordList}
    (hD : DigitVal A H ds)
    (hS : wordScale u * ((2 ^ H : Nat) : Rat) = 1)
    (hM : 1 <= m)
    (hF : (5 / 2) * wordMass u + wordMassK u + wordScale u * wordMassK ds <= 1 / 32)
    (hLo : loc_z1p ds)
    (hHi : loc_z1q ds) :
    ∃ k v l g,
      Scan (m * 2) (u ++ ds ++ [K]) (k * 8) v l /\
      (∃ w,v = w ++ List.replicate 3 V) /\
      wordScale v * ((8 ^ g : Nat) : Rat) = 2 /\
      wordMass v <= wordMass u + (1 / 4) * (wordScale u * wordMassK ds) /\
      wordMass v + l <= wordMass u + wordMassK u + (3 / 4) * (wordScale u * wordMassK ds) /\
      0 < wordMassQ v + l /\ wordMassQ v + l <= 1 / 32 := by
  rcases hHi with ⟨w,hHi_eq⟩
  have hU := wordMass_nonneg u
  have hDs := wordMass_nonneg ds
  have hSu := wordScale_pos u
  have hSmall : wordMass u + wordMassK u < 1 / 2 := by nlinarith
  rcases loc_z1Y hD hS hM hSmall (loc_z21 hLo) with ⟨b,x,s,c,y,t0,hI1,hI2,_⟩
  rcases scan_append hI1 hI2 with ⟨l,hI,rfl⟩
  have hI_assoc : Scan (m * 2) (u ++ ds ++ [K]) c (x ++ y) (s + wordScale x * t0) := by
    simpa [List.append_assoc] using hI
  have hEnd : ∃ p k,x ++ y = p ++ List.replicate 3 V /\ c = k * 8 := by
    have hI_hi : Scan (m * 2) ((u ++ w) ++ List.replicate (1 + 2 * 2) Q ++ [K]) c (x ++ y) (s + wordScale x * t0) := by
      have heq_list : u ++ ds ++ [K] = (u ++ w) ++ List.replicate (1 + 2 * 2) Q ++ [K] := by
        rw [hHi_eq]; simp [List.append_assoc]
      rwa [<- heq_list]
    rcases loc_z20 2 (m * 2) (u ++ w) c (x ++ y) (s + wordScale x * t0) hI_hi with ⟨p,k,hE,hC⟩
    exact ⟨p,k,hE,hC⟩
  rcases hEnd with ⟨p,k,hE,rfl⟩
  rcases scan_scale_pow_eight hI_assoc with ⟨g,hG⟩
  refine ⟨k,x ++ y,s + wordScale x * t0,g,hI_assoc,⟨p,hE⟩,?_,?_,?_,?_⟩
  · rw [wordScale_append,wordScale_append] at hG
    dsimp [wordScale] at hG
    rw [(digitVal_scale_and_mass hD).1] at hG
    nlinarith
  · have hB1 := scan_mass_bounds hI1
    have hS1 := loc_z1J hI1
    have hB2 := loc_z1X hI2 (loc_z21 hLo) ⟨A,H,hD⟩ (loc_z22 hLo)
    have hSx := wordScale_pos x
    rw [wordMass_append]; nlinarith
  · have hB1 := scan_mass_bounds hI1
    have hS1 := loc_z1J hI1
    have hB2 := loc_z1X hI2 (loc_z21 hLo) ⟨A,H,hD⟩ (loc_z22 hLo)
    have hSx := wordScale_pos x
    rw [wordMass_append]; nlinarith
  · have hW : hasQKSubword (u ++ ds ++ [K]) = true := by
      rw [List.append_assoc]
      apply hasQKSubword_append_right
      rcases loc_z21 hLo with ⟨z,rfl⟩
      rfl
    have hLoss := loc_z1O hI_assoc hW
    have hB1 := scan_mass_bounds hI1
    have hS1 := loc_z1J hI1
    have hB2 := loc_z1X hI2 (loc_z21 hLo) ⟨A,H,hD⟩ (loc_z22 hLo)
    have hSx := wordScale_pos x
    have hMv : wordMass (x ++ y) + (s + wordScale x * t0) <= wordMass u + wordMassK u + (3 / 4) * (wordScale u * wordMassK ds) := by
      rw [wordMass_append]; nlinarith
    have hSuz : 0 <= wordScale u * wordMassK ds := by nlinarith
    have hPos_xy := wordMass_nonneg (x ++ y)
    have hSplit_xy := wordMass_eq_add (x ++ y)
    constructor <;> linarith

theorem loc_z24 {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat} {H : Nat} {r : HalfTape}
    (hI : Scan a u (b * 2) v l) (hB : Binary (1 + b) H r) :
    RIncs a (evalWords u default) (evalWords v r) := by
  apply loc_z1D hI
  have hR := loc_z1b hB
  have heq : ((1 + b) - 1) * 2 = b * 2 := by omega
  rwa [heq] at hR

theorem loc_z25 (m g k : Nat) (s delta : Rat)
    (hM : m = 1 \/ m = 2)
    (hS : s * ((8 ^ g : Nat) : Rat) = 2)
    (hB : ((m * 2 : Nat) : Rat) = ((k * 8 : Nat) : Rat) * s + delta * 2)
    (hPos : 0 < delta)
    (hSmall : delta <= 1 / 32) :
    ∃ n,g = 3 + n /\ 31 * 2 ^ (m + 3 * n) <= k /\ k < 32 * 2 ^ (m + 3 * n) := by
  have hMq : (1 : Rat) <= (m : Rat) /\ (m : Rat) <= 2 := by
    rcases hM with rfl | rfl <;> norm_num
  have hPow : (0 : Rat) < ((8 ^ g : Nat) : Rat) := by exact_mod_cast loc_z17 g
  have hEq : ((k * 8 : Nat) : Rat) = ((m : Rat) - delta) * ((8 ^ g : Nat) : Rat) := by
    push_cast at hB ⊢
    have hE : (k : Rat) * 8 * s = ((m : Rat) - delta) * 2 := by linarith
    have hE' : (k : Rat) * 8 * (s * ((8 ^ g : Nat) : Rat)) = ((m : Rat) - delta) * 2 * ((8 ^ g : Nat) : Rat) := by
      calc (k : Rat) * 8 * (s * ((8 ^ g : Nat) : Rat))
        _ = ((k : Rat) * 8 * s) * ((8 ^ g : Nat) : Rat) := by ring
        _ = ((m : Rat) - delta) * 2 * ((8 ^ g : Nat) : Rat) := by rw [hE]
    rw [hS] at hE'
    push_cast at hE'
    linarith
  have hK : 0 < k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    subst hk_eq
    push_cast at hPow hEq
    nlinarith
  have hR_q : ((k * 8 : Nat) : Rat) < ((m * 8 ^ g : Nat) : Rat) := by
    push_cast at hPow hEq ⊢
    nlinarith
  have hR : k * 8 < m * 8 ^ g := by exact_mod_cast hR_q
  have hg1 : 1 <= g := by
    by_contra hg_lt
    have hg_eq : g = 0 := by omega
    subst hg_eq
    rcases hM with rfl | rfl <;> omega
  let n1 := g - 1
  have hg_eq : g = 1 + n1 := by omega
  rw [hg_eq] at hR hEq
  have hpow_1n : 8 ^ (1 + n1) = 8 * 8 ^ n1 := by
    rw [Nat.pow_add]
  rw [hpow_1n] at hR hEq
  have hRn : k + 1 <= m * 8 ^ n1 := by
    rcases hM with rfl | rfl <;> omega
  have hRn_q : ((k + 1 : Nat) : Rat) <= ((m * 8 ^ n1 : Nat) : Rat) := by exact_mod_cast hRn
  have hPow_n1 : (0 : Rat) <= ((8 ^ n1 : Nat) : Rat) := by positivity
  have hP : (32 : Rat) <= ((8 ^ n1 : Nat) : Rat) := by
    rcases hM with rfl | rfl <;> (push_cast at hEq hRn_q ⊢; nlinarith)
  have hP_nat : 32 <= 8 ^ n1 := by exact_mod_cast hP
  have hN : 2 <= n1 := by
    by_contra hn2
    have hn1 : n1 <= 1 := by omega
    have hle1 : 8 ^ n1 <= 8 ^ 1 := Nat.pow_le_pow_right (by decide) hn1
    (try omega)
  let j := n1 - 2
  have hNJ : n1 = 2 + j := by omega
  refine ⟨j,by omega,?_,?_⟩
  · rw [hNJ,Nat.pow_add 8 2 j] at hEq
    have hPow_j : (0 : Rat) < ((8 ^ j : Nat) : Rat) := by exact_mod_cast loc_z17 j
    have h_le_q : ((31 * 2 ^ (m + 3 * j) : Nat) : Rat) <= (k : Rat) := by
      rw [Nat.pow_add 2 m (3 * j),loc_z1u]
      rcases hM with rfl | rfl <;> (push_cast at hPow_j hEq ⊢; nlinarith)
    exact_mod_cast h_le_q
  · rw [hNJ,Nat.pow_add 8 2 j] at hEq
    have hPow_j : (0 : Rat) < ((8 ^ j : Nat) : Rat) := by exact_mod_cast loc_z17 j
    have h_lt_q : (k : Rat) < ((32 * 2 ^ (m + 3 * j) : Nat) : Rat) := by
      rw [Nat.pow_add 2 m (3 * j),loc_z1u]
      rcases hM with rfl | rfl <;> (push_cast at hPow_j hEq ⊢; nlinarith)
    exact_mod_cast h_lt_q

theorem loc_z26 {m : Nat} {a : WordList} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    {H : Nat} {ds : WordList} {z : Rat}
    (hI : Scan (m * 2) a (b * 2) v l)
    (hD : DigitVal (1 + b) H ds)
    (hS : wordScale v * wordScale ds = (m : Rat))
    (hM : wordMass v <= wordMass u + (1 / 4) * z)
    (hB : wordMass v + l <= wordMass u + wordMassK u + (3 / 4) * z)
    (hZ : 0 <= z) :
    (5 / 2) * wordMass v + wordMassK (v ++ ds) <=
      (7 / 5) * ((5 / 2) * wordMass u + wordMassK u + z) := by
  have hE := loc_z1F hI
  have hDt := digitVal_wordMassK_eq hD
  have hDs := (digitVal_scale_and_mass hD).1
  have hSplit_v := wordMass_eq_add v
  have hPos_u := wordMass_nonneg u
  have hSv := wordScale_pos v
  push_cast at hE hDt hDs
  rw [wordMassK_append]
  nlinarith

theorem loc_z27 (m n : Nat) (s : Rat)
    (hM : m = 1 \/ m = 2)
    (hS : s * ((8 ^ (3 + n) : Nat) : Rat) = 2) :
    s * ((2 ^ (7 + (m + 3 * n)) : Nat) : Rat) = (m : Rat) := by
  have h8 : 8 ^ (3 + n) = 512 * 8 ^ n := by
    rw [Nat.pow_add 8 3 n]
  rw [h8] at hS
  have h2 : 2 ^ (7 + (m + 3 * n)) = 128 * 2 ^ m * 8 ^ n := by
    rw [Nat.pow_add 2 7 _,Nat.pow_add 2 m (3 * n),loc_z1u]; ring
  rw [h2]
  rcases hM with rfl | rfl <;> (push_cast at hS ⊢; linarith)

inductive C24Good (bound : Rat) : HalfTape -> Prop where
  | intro (u : WordList) (A H : Nat) (ds : WordList) :
      DigitVal A H ds ->
      wordScale u * ((2 ^ H : Nat) : Rat) = 1 ->
      (5 / 2) * wordMass u + wordMassK u + wordScale u * wordMassK ds <= bound ->
      loc_z1p ds ->
      loc_z1q ds ->
      C24Good bound (evalWords (u ++ ds) default)

theorem loc_z28 (m : Nat) (bound bound' : Rat) (r : HalfTape)
    (hM : m = 1 \/ m = 2)
    (hLimit : bound <= 1 / 32)
    (hG : C24Good bound r)
    (hRate : (7 / 5) * bound <= (m : Rat) * bound') :
    ∃ r',RIncs (m * 2) r r' /\ C24Good bound' (evalWords (List.replicate (m - 1) V) r') := by
  rcases hG with ⟨u,A,H,ds,hD,hS,hF,hLo,hHi⟩
  have hPos_m : 1 <= m := by rcases hM with rfl | rfl <;> omega
  have hSmall : (5 / 2) * wordMass u + wordMassK u + wordScale u * wordMassK ds <= 1 / 32 := by linarith
  rcases loc_z23 hD hS hPos_m hSmall hLo hHi with ⟨k,v,l,g,hI,hEnd,hScale,hMv,hBv,hPos,hUpper⟩
  have hBudget := loc_z1F hI
  rcases loc_z25 m g k (wordScale v) (wordMassQ v + l) hM hScale hBudget hPos hUpper with ⟨n,rfl,hKl,hKu⟩
  rcases loc_z1t (m + 3 * n) k hKl hKu with ⟨ds',hD',hLo',hHi',hBin⟩
  have hScale' : wordScale v * wordScale ds' = (m : Rat) := by
    rw [(digitVal_scale_and_mass hD').1]
    exact loc_z27 m n (wordScale v) hM hScale
  have hI' : Scan (m * 2) (u ++ ds ++ [K]) ((k * 4) * 2) v l := by
    have heq : k * 8 = (k * 4) * 2 := by omega
    rwa [<- heq]
  have hR := loc_z24 hI' hBin
  have hd0_side : evalWords [K] default = default := zDd
  have hR' : RIncs (m * 2) (evalWords (u ++ ds) default) (evalWords (v ++ ds') default) := by
    rw [evalWords_append (u ++ ds) [K],hd0_side,<- evalWords_append v ds'] at hR
    exact hR
  have hZ : 0 <= wordScale u * wordMassK ds := by
    have hSu := wordScale_pos u
    have hPos_ds := (wordMass_nonneg ds).2.1
    nlinarith
  have hWeight := loc_z26 hI' hD' hScale' hMv hBv hZ
  refine ⟨evalWords (v ++ ds') default,hR',?_⟩
  rw [<- evalWords_append,<- List.append_assoc]
  refine C24Good.intro (List.replicate (m - 1) V ++ v) (1 + k * 4) (7 + (m + 3 * n)) ds' hD' ?_ ?_ hLo' hHi'
  · rw [<- (digitVal_scale_and_mass hD').1,wordScale_append]
    rcases hM with rfl | rfl <;> (dsimp [List.replicate,wordScale]; push_cast at hScale'; nlinarith)
  · rw [wordMass_append,wordMassK_append,wordScale_append]
    rw [wordMassK_append] at hWeight
    rcases hM with rfl | rfl <;> (dsimp [List.replicate,wordMass,wordMassK,wordScale]; push_cast at hRate; nlinarith)

theorem loc_z29 {r : HalfTape} (hG : C24Good (1 / 64) r) :
    ∃ s r',RIncs 2 r s /\ RIncs 4 s r' /\ C24Good (1 / 64) (t +> r') := by
  rcases loc_z28 1 (1 / 64) ((7 / 5) * (1 / 64)) r (Or.inl rfl) (by norm_num) hG (by norm_num) with ⟨s,hR,hH⟩
  dsimp [List.replicate,evalWords] at hH
  rcases loc_z28 2 ((7 / 5) * (1 / 64)) (1 / 64) s (Or.inr rfl) (by norm_num) hH (by norm_num) with ⟨r',hS,hI⟩
  dsimp [List.replicate,evalWords] at hI
  exact ⟨s,r',hR,hS,hI⟩

theorem ne_of_beq_eq_false {a b : Nat} (h : (a == b) = false) : a ≠ b := by
  intro heq; subst heq; rw [beq_self_eq_true] at h; contradiction

def loc_zPf : Nat -> Nat -> Option (WordList)
  | 0,_ => none
  | fuel + 1,k =>
    if k == 0 then none
    else if k == 1 then some [Q]
    else match loc_zPf fuel (k / 2) with
      | none => none
      | some ws => some ((if k % 2 == 0 then K else Q) :: ws)

theorem loc_z2a (fuel : Nat) :
    ∀ (k : Nat) (ws : WordList),loc_zPf fuel k = some ws ->
      ∃ H,Binary k H (evalWords ws default) := by
  induction fuel with
  | zero => intro k ws h; contradiction
  | succ fuel ih =>
    intro k ws h
    dsimp [loc_zPf] at h
    cases hk0 : (k == 0) with
    | true => rw [hk0] at h; contradiction
    | false =>
      rw [hk0] at h; dsimp at h
      have hk0' : k ≠ 0 := ne_of_beq_eq_false hk0
      cases hk1 : (k == 1) with
      | true =>
        rw [hk1] at h; dsimp at h
        injection h with h; subst h
        have rfl_k : k = 1 := beq_iff_eq.mp hk1
        subst rfl_k
        exact ⟨1,Binary.one⟩
      | false =>
        rw [hk1] at h; dsimp at h
        have hk1' : k ≠ 1 := ne_of_beq_eq_false hk1
        cases hrec : loc_zPf fuel (k / 2) with
        | none => rw [hrec] at h; contradiction
        | some ws' =>
          rw [hrec] at h; dsimp at h
          injection h with h; subst h
          rcases ih (k / 2) ws' hrec with ⟨H,hB⟩
          have hq : k / 2 = 1 + (k / 2 - 1) := by omega
          rw [hq] at hB
          rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
          · have hcond : (k % 2 == 0) = true := beq_iff_eq.mpr hmod
            rw [hcond]; dsimp [evalWords]
            refine ⟨1 + H,?_⟩
            have heq : k = 2 + (k / 2 - 1) * 2 := by omega
            rw [heq]; exact Binary.zero hB
          · have hcond : (k % 2 == 0) = false := beq_false_of_ne (by omega)
            rw [hcond]; dsimp [evalWords]
            refine ⟨1 + H,?_⟩
            have heq : k = 3 + (k / 2 - 1) * 2 := by omega
            rw [heq]; exact Binary.two hB

def loc_z2h (e : Bool) : Word := if e then Q else K

def loc_z2i (e : Bool) (k : Nat) : Option (Word × Nat) :=
  if k == 0 then none
  else if k % 2 == 0 then
    if k % 4 == 2 then
      some (K,bitStepNat e (k / 4))
    else
      some (Q,bitStepNat e (k / 4 - 1))
  else none

theorem loc_z2j (e : Bool) (k : Nat) (d : Word) (k' : Nat) (r r' : HalfTape)
    (hS : loc_z2i e k = some (d,k')) (hI : RIncs k' r r') :
    RIncs k (evalWords [loc_z2h e] r) (evalWords [d] r') := by
  dsimp [loc_z2i] at hS
  cases hk0 : (k == 0) with
  | true => rw [hk0] at hS; contradiction
  | false =>
    rw [hk0] at hS; dsimp at hS
    have hk0' : k ≠ 0 := ne_of_beq_eq_false hk0
    cases hk2 : (k % 2 == 0) with
    | false => rw [hk2] at hS; contradiction
    | true =>
      rw [hk2] at hS; dsimp at hS
      have hk2' : k % 2 = 0 := beq_iff_eq.mp hk2
      cases hk4 : (k % 4 == 2) with
      | true =>
        rw [hk4] at hS; dsimp at hS
        injection hS with hS1; injection hS1 with hS1 hS2; subst hS1; subst hS2
        have hk4' : k % 4 = 2 := beq_iff_eq.mp hk4
        have hk_eq : k = 2 + (k / 4) * 4 := by omega
        rw [hk_eq]
        cases e
        · exact RIncs.short00 hI
        · exact RIncs.short01 hI
      | false =>
        rw [hk4] at hS; dsimp at hS
        injection hS with hS1; injection hS1 with hS1 hS2; subst hS1; subst hS2
        have hk4' : k % 4 ≠ 2 := ne_of_beq_eq_false hk4
        have hk_eq : k = 4 + (k / 4 - 1) * 4 := by omega
        rw [hk_eq]
        cases e
        · exact RIncs.short10 hI
        · exact RIncs.short11 hI

def loc_z2l : Nat -> WordList -> Nat -> WordList -> Option (WordList)
  | 0,_,_,_ => none
  | fuel + 1,u,k,acc =>
    if k == 0 then
      if u.all isWordK then some (acc.reverseAux [Q]) else none
    else
      match u with
      | [] =>
        if k % 2 == 0 then
          match loc_zPf 64 (1 + k / 2) with
          | some ws => some (acc.reverseAux ws)
          | none => none
        else none
      | V :: u' => loc_z2l fuel u' (k * 2) (V :: acc)
      | K :: u' =>
        match loc_z2i false k with
        | some (d,k') => loc_z2l fuel u' k' (d :: acc)
        | none => none
      | Q :: u' =>
        if (k % 2 == 0) && startsWithKOrNil (Q :: u') then
          match loc_z2i true k with
          | some (d,k') => loc_z2l fuel u' k' (d :: acc)
          | none => none
        else
          match u' with
          | K :: v => loc_z2l fuel v ((k - 1) * 2) (V :: acc)
          | Q :: v => loc_z2l fuel v (1 + (k - 1) * 2) (V :: acc)
          | _ => none

theorem loc_z2m (fuel : Nat) :
    ∀ (u : WordList) (k : Nat) (acc v : WordList),loc_z2l fuel u k acc = some v ->
      ∃ w,v = acc.reverseAux w /\ RIncs k (evalWords u default) (evalWords w default) := by
  induction fuel with
  | zero => intro u k acc v hE; contradiction
  | succ fuel ih =>
    intro u k acc v hE
    dsimp [loc_z2l] at hE
    cases hk0 : (k == 0) with
    | true =>
      rw [hk0] at hE; dsimp at hE
      have rfl_k : k = 0 := beq_iff_eq.mp hk0; subst rfl_k
      cases hu : u.all isWordK with
      | false => rw [hu] at hE; contradiction
      | true =>
        rw [hu] at hE; dsimp at hE
        injection hE with hE; subst hE
        refine ⟨[Q],rfl,?_⟩
        rw [evalWords_default_of_all_K u hu]
        have h0 := RIncs.zero (default : HalfTape)
        simpa [evalWords,d1,one] using h0
    | false =>
      rw [hk0] at hE; dsimp at hE
      have hk0' : k ≠ 0 := ne_of_beq_eq_false hk0
      cases u with
      | nil =>
        cases hk2 : (k % 2 == 0) with
        | false => rw [hk2] at hE; contradiction
        | true =>
          rw [hk2] at hE; dsimp at hE
          have hk2' : k % 2 = 0 := beq_iff_eq.mp hk2
          cases hp : loc_zPf 64 (1 + k / 2) with
          | none => rw [hp] at hE; contradiction
          | some ws =>
            rw [hp] at hE; dsimp at hE
            injection hE with hE; subst hE
            rcases loc_z2a 64 (1 + k / 2) ws hp with ⟨H,hB⟩
            have hR := loc_z1b hB
            have heq : ((1 + k / 2) - 1) * 2 = k := by omega
            rw [heq] at hR
            exact ⟨ws,rfl,hR⟩
      | cons x u' =>
        cases x
        · dsimp at hE
          rcases ih u' (k * 2) (V :: acc) v hE with ⟨w,rfl,hR⟩
          refine ⟨V :: w,rfl,?_⟩
          have hk_eq : k = 1 + (k - 1) := by omega
          have hk2_eq : k * 2 = (1 + (k - 1)) * 2 := by omega
          rw [hk2_eq] at hR
          rw [hk_eq]
          exact RIncs.T hR
        · dsimp at hE
          cases hS : loc_z2i false k with
          | none => rw [hS] at hE; contradiction
          | some dk =>
            rcases dk with ⟨d,k'⟩
            rw [hS] at hE; dsimp at hE
            rcases ih u' k' (d :: acc) v hE with ⟨w,rfl,hR⟩
            have h_sn := loc_z2j false k d k' (evalWords u' default) (evalWords w default) hS hR
            rw [<- evalWords_append [d] w default] at h_sn
            exact ⟨d :: w,rfl,h_sn⟩
        · dsimp at hE
          cases hcond : ((k % 2 == 0) && startsWithKOrNil (Q :: u')) with
          | true =>
            rw [hcond] at hE; dsimp at hE
            cases hS : loc_z2i true k with
            | none => rw [hS] at hE; contradiction
            | some dk =>
              rcases dk with ⟨d,k'⟩
              rw [hS] at hE; dsimp at hE
              rcases ih u' k' (d :: acc) v hE with ⟨w,rfl,hR⟩
              have h_sn := loc_z2j true k d k' (evalWords u' default) (evalWords w default) hS hR
              rw [<- evalWords_append [d] w default] at h_sn
              exact ⟨d :: w,rfl,h_sn⟩
          | false =>
            rw [hcond] at hE; dsimp at hE
            cases u' with
            | nil => contradiction
            | cons x2 u'' =>
              cases x2
              · contradiction
              · dsimp at hE
                rcases ih u'' ((k - 1) * 2) (V :: acc) v hE with ⟨w,rfl,hR⟩
                refine ⟨V :: w,rfl,?_⟩
                have hk_eq : k = 1 + (k - 1) := by omega
                rw [hk_eq]
                exact RIncs.pair0 hR
              · dsimp at hE
                rcases ih u'' (1 + (k - 1) * 2) (V :: acc) v hE with ⟨w,rfl,hR⟩
                refine ⟨V :: w,rfl,?_⟩
                have hk_eq : k = 1 + (k - 1) := by omega
                rw [hk_eq]
                exact RIncs.pair1 hR

def loc_z2n (k : Nat) (u : WordList) : Option (WordList) :=
  loc_z2l 64 (u ++ [K]) k []

theorem loc_z2o (k : Nat) (u v : WordList) (hE : loc_z2n k u = some v) :
    RIncs k (evalWords u default) (evalWords v default) := by
  rcases loc_z2m 64 (u ++ [K]) k [] v hE with ⟨w,rfl,hR⟩
  have hd0_side : evalWords [K] default = default := zDd
  rw [evalWords_append u [K],hd0_side] at hR
  exact hR

def loc_z2s (c0 c1 : Nat) : WordList -> Nat -> Nat
  | [],n => n
  | V :: u,n => loc_z2s c0 c1 u (halfCeil n)
  | K :: u,n => loc_z2s c0 c1 u (n * 2 + c0)
  | Q :: u,n => loc_z2s c0 c1 u (n * 2 + c1)

theorem loc_z2u (c0 c1 : Nat) (u : WordList) :
    ∀ (n : Nat),
      (c0 : Rat) * wordMassK u.reverse + (c1 : Rat) * wordMassQ u.reverse + wordScale u.reverse * (n : Rat) <=
        ((loc_z2s c0 c1 u n : Nat) : Rat) := by
  induction u with
  | nil =>
    intro n
    simp [wordMassK,wordMassQ,wordScale,loc_z2s]
  | cons w u ih =>
    intro n
    have hsp := wordScale_pos u.reverse
    cases w
    · dsimp [loc_z2s]
      rw [List.reverse_cons,wordMassK_append,wordMassQ_append,wordScale_append]
      dsimp [wordMassK,wordMassQ,wordScale]
      have hhu := rat_le_two_mul_halfCeil n
      have hih := ih (halfCeil n)
      nlinarith
    · dsimp [loc_z2s]
      rw [List.reverse_cons,wordMassK_append,wordMassQ_append,wordScale_append]
      dsimp [wordMassK,wordMassQ,wordScale]
      have hih := ih (n * 2 + c0)
      push_cast at hih
      nlinarith
    · dsimp [loc_z2s]
      rw [List.reverse_cons,wordMassK_append,wordMassQ_append,wordScale_append]
      dsimp [wordMassK,wordMassQ,wordScale]
      have hih := ih (n * 2 + c1)
      push_cast at hih
      nlinarith

theorem loc_z2v (c0 c1 : Nat) (u : WordList) (n : Nat) :
    (c0 : Rat) * wordMassK u + (c1 : Rat) * wordMassQ u + wordScale u * (n : Rat) <=
      ((loc_z2s c0 c1 u.reverse n : Nat) : Rat) := by
  have h := loc_z2u c0 c1 u.reverse n
  simpa [List.reverse_reverse] using h

def loc_z2B (u ds : WordList) : Bool :=
  decide (loc_z2s (7 * 65536) (5 * 65536) u.reverse
    (loc_z2s (2 * 65536) 0 ds.reverse 0) <= 2048)

theorem loc_z2C (u ds : WordList) (hE : loc_z2B u ds = true) :
    (5 / 2) * wordMass u + wordMassK u + wordScale u * wordMassK ds <= 1 / 64 := by
  unfold loc_z2B at hE
  have hle : loc_z2s (7 * 65536) (5 * 65536) u.reverse (loc_z2s (2 * 65536) 0 ds.reverse 0) <= 2048 :=
    of_decide_eq_true hE
  have hle_q : ((loc_z2s (7 * 65536) (5 * 65536) u.reverse (loc_z2s (2 * 65536) 0 ds.reverse 0) : Nat) : Rat) <= 2048 := by
    exact_mod_cast hle
  have hD := loc_z2v (2 * 65536) 0 ds 0
  have hU := loc_z2v (7 * 65536) (5 * 65536) u (loc_z2s (2 * 65536) 0 ds.reverse 0)
  have hSu := wordScale_pos u
  have hSplit := wordMass_eq_add u
  push_cast at hD hU
  nlinarith

def loc_z2E : WordList := Q :: List.replicate 1 K

def loc_z2F : WordList := List.replicate 5 Q

def loc_z2G (u : WordList) : Bool :=
  match splitPrefixDigits u with
  | none => false
  | some (p,ds) =>
    match heightShift p 0 with
    | none => false
    | some H =>
      if H == ds.length then
        match stripWordPrefix loc_z2E ds,
              stripWordPrefix loc_z2F ds.reverse with
        | some _,some _ => loc_z2B p ds
        | _,_ => false
      else false

theorem loc_z2H (u : WordList) (hE : loc_z2G u = true) :
    C24Good (1 / 64) (evalWords u default) := by
  unfold loc_z2G at hE
  cases hC : splitPrefixDigits u with
  | none => rw [hC] at hE; contradiction
  | some pds =>
    rcases pds with ⟨p,ds⟩
    rw [hC] at hE; dsimp only [] at hE
    cases hU : heightShift p 0 with
    | none => rw [hU] at hE; contradiction
    | some H =>
      rw [hU] at hE; dsimp only [] at hE
      cases hL : (H == ds.length) with
      | false => rw [hL] at hE; contradiction
      | true =>
        rw [hL] at hE; rw [if_pos rfl] at hE
        have rfl_H : H = ds.length := beq_iff_eq.mp hL
        subst rfl_H
        cases hLo : stripWordPrefix loc_z2E ds with
        | none => rw [hLo] at hE; contradiction
        | some lo =>
          rw [hLo] at hE
          cases hHi : stripWordPrefix loc_z2F ds.reverse with
          | none => rw [hHi] at hE; contradiction
          | some hi =>
            rw [hHi] at hE; dsimp only [] at hE
            rcases splitPrefixDigits_sound u p ds hC with ⟨rfl,hD⟩
            rcases exists_digitVal_of_all_isDigitWord ds hD with ⟨A,hDA⟩
            refine C24Good.intro p A ds.length ds hDA ?_ ?_ ?_ ?_
            · have hsp := heightShift_sound p 0 ds.length hU
              simpa using hsp
            · exact loc_z2C p ds hE
            · exact ⟨lo,stripWordPrefix_sound loc_z2E ds lo hLo⟩
            · have hHi_eq := stripWordPrefix_sound loc_z2F ds.reverse hi hHi
              have hRev := congrArg List.reverse hHi_eq
              rw [List.reverse_reverse,List.reverse_append] at hRev
              change ds = hi.reverse ++ (List.replicate 5 Q).reverse at hRev
              rw [replicate_reverse] at hRev
              exact ⟨hi.reverse,hRev⟩

def loc_z2I (u : WordList) : Option (WordList) :=
  match loc_z2n 2 u with
  | none => none
  | some v =>
    match loc_z2n 4 v with
    | none => none
    | some w => some (V :: w)

inductive C24Rounds : HalfTape -> HalfTape -> Prop where
  | refl (r : HalfTape) : C24Rounds r r
  | next {r s v w : HalfTape} :
      RIncs 2 r s -> RIncs 4 s v -> C24Rounds (t +> v) w -> C24Rounds r w

def loc_z2J : Nat -> WordList -> Bool
  | 0,u => loc_z2G u
  | n + 1,u =>
    match loc_z2I u with
    | none => false
    | some v => loc_z2J n v

theorem loc_z2K (n : Nat) :
    ∀ (u : WordList),loc_z2J n u = true ->
      ∃ r,C24Rounds (evalWords u default) r /\ C24Good (1 / 64) r := by
  induction n with
  | zero =>
    intro u hE
    exact ⟨evalWords u default,C24Rounds.refl _,loc_z2H u hE⟩
  | succ n ih =>
    intro u hE
    dsimp [loc_z2J,loc_z2I] at hE
    cases hV : loc_z2n 2 u with
    | none => rw [hV] at hE; contradiction
    | some v =>
      rw [hV] at hE; dsimp at hE
      cases hW : loc_z2n 4 v with
      | none => rw [hW] at hE; contradiction
      | some w =>
        rw [hW] at hE; dsimp at hE
        rcases ih (V :: w) hE with ⟨r,hR,hG⟩
        exact ⟨r,C24Rounds.next (loc_z2o 2 u v hV) (loc_z2o 4 v w hW) hR,hG⟩

def loc_z2L : WordList :=
  List.replicate 5 V ++ List.replicate 5 Q

theorem loc_z2M : loc_z2J 1 loc_z2L = true := by
  decide

inductive Num : Nat -> BitWord -> List Call -> Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)

def loc_z2N (k : Nat) (r r' : HalfTape) : Prop :=
  ∀ w hs,Num k w hs -> Side hs (w +> r) r'

theorem loc_z2O {r r' : HalfTape} (h : loc_z2N 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl

theorem loc_z2P {n : Nat} {r r' : HalfTape}
    (hI : loc_z2N ((1 + n) * 2) r r') : loc_z2N (1 + n) (t +> r) (t +> r') := by
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

theorem loc_z2Q {n : Nat} {r r' : HalfTape}
    (hI : loc_z2N (n * 2) r r') : loc_z2N (1 + n) (d1 +> (d0 +> r)) (t +> r') := by
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
      have hr' := loc_z2O hI
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

theorem loc_z2R {n : Nat} {r r' : HalfTape}
    (hI : loc_z2N (1 + n * 2) r r') : loc_z2N (1 + n) (d1 +> (d1 +> r)) (t +> r') := by
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

theorem loc_z2S {n : Nat} {r r' : HalfTape}
    (hI : loc_z2N (n * 2) r r') : loc_z2N (2 + n * 4) (d0 +> r) (d0 +> r') := by
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
      have hr' := loc_z2O hI
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

theorem loc_z2T {n : Nat} {r r' : HalfTape}
    (hI : loc_z2N (1 + n * 2) r r') : loc_z2N (2 + n * 4) (d1 +> r) (d0 +> r') := by
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

theorem loc_z2U {n : Nat} {r r' : HalfTape}
    (hI : loc_z2N (n * 2) r r') : loc_z2N (4 + n * 4) (d0 +> r) (d1 +> r') := by
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
      have hr' := loc_z2O hI
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

theorem loc_z2V {n : Nat} {r r' : HalfTape}
    (hI : loc_z2N (1 + n * 2) r r') : loc_z2N (4 + n * 4) (d1 +> r) (d1 +> r') := by
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

theorem loc_z2W {k : Nat} {r r' : HalfTape} (hI : RIncs k r r') :
    loc_z2N k r r' := by
  induction hI with
  | zero r =>
    intro w hs hN
    generalize hk : 0 = k0 at hN
    cases hN with
    | zero => exact Side.nil (one +> r)
    | odd _ => omega
    | even _ => omega
  | T _ ih => exact loc_z2P ih
  | pair0 _ ih => exact loc_z2Q ih
  | pair1 _ ih => exact loc_z2R ih
  | short00 _ ih => exact loc_z2S ih
  | short01 _ ih => exact loc_z2T ih
  | short10 _ ih => exact loc_z2U ih
  | short11 _ ih => exact loc_z2V ih

theorem loc_z2X {r s r' : HalfTape} (hI : RIncs 2 r s) (hJ : RIncs 4 s r') :
    (zCf r) [target_tm]⊢⁺ zCf (t +> r') := by
  have hC1 := loc_z2W hI [] ([.cj] ++ [.ch] ^ 0) (Num.even 0)
  have hS1 := zSc z0y hC1
  dsimp at hS1
  rcases hS1 with _ | ⟨hca,hnil1⟩
  cases hnil1
  have hC2 := loc_z2W hJ [] ([.cj] ++ [.ch] ^ 1) (Num.even 1)
  have hS2 := zSc (z0o 0) hC2
  dsimp at hS2
  rcases hS2 with _ | ⟨hcj,hnil2⟩
  cases hnil2
  exact zPt (z0z r)
    (zPt (hca ([1,1] +> default))
      (zPt (z0A (t +> s)) (hcj lh)))

theorem loc_z2Y {r r' : HalfTape} (h : C24Rounds r r') :
    (zCf r) [target_tm]⊢* zCf r' := by
  induction h with
  | refl _ => exact ⟨0,rfl⟩
  | next hR1 hR2 _ ih =>
    rcases loc_z2X hR1 hR2 with ⟨n,_,hn⟩
    rcases ih with ⟨m,hm⟩
    exact ⟨n + m,zMt target_tm _ _ _ n m hn hm⟩

theorem zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl

theorem loc_z2Z :
    (init []) [target_tm]⊢⁺ zCf (evalWords loc_z2L default) := by
  have h := pre_z16
  have heq : evalWords loc_z2L default =
      (([1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,0,1,0,1,0,1,0] : BitWord) +> default) := by
    simp [loc_z2L,List.replicate,evalWords,t,d1,append_cons,append_nil]
  rwa [heq]

theorem loc_z30 (m : Nat) :
    ∃ N ≥ m,∃ r,multiStep target_tm (init []) N = some (zCf r) /\ C24Good (1 / 64) r := by
  induction m with
  | zero =>
    rcases loc_z2Z with ⟨k1,_,hk1⟩
    rcases loc_z2K 1 loc_z2L loc_z2M with ⟨r0,hR0,hG0⟩
    rcases loc_z2Y hR0 with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,r0,zMt target_tm _ _ _ k1 k2 hk1 hk2,hG0⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,r,h_ms,h_good⟩
    rcases loc_z29 h_good with ⟨s,r',hR1,hR2,h_good'⟩
    rcases loc_z2X hR1 hR2 with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,t +> r',zMt target_tm _ _ _ N k h_ms h_step_k,h_good'⟩

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
  rcases loc_z30 (n + 1) with ⟨N,hN,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end BusyBeaver.M_1RB0RF_1LC1RA_1LD0LC_0LE0LA_1RFHHH_1RA1RE
