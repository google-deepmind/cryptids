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


open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LFHHH_1RA1RF


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LFHHH_1RA1RF"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

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
abbrev lh : HalfTape := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
abbrev w_pre : BitWord := t ++ one
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
  | .ca => B
def zCw : Call -> BitWord
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
  | .ca => [1,1,1,0,1,1]
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
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg zH0 (zSa z0n n)
theorem z0q (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d1 d1 :=
  zSa z0n n
theorem z0r (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ (1 + n)) d1 d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg zH4 (zSa z0m n)
theorem z0s (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0c z0e) (H_T n)
theorem z0t (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0d zH2) (H_T n)
theorem z0u (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0g zH2) (H_T n)
theorem z0v (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0h (H_T n)
theorem z0w (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0i (H_T n)
theorem z0x (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using! zSg z0j (H_T n)
theorem z0y (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0k (zSg zH1 zH3)
  have h1 := zSg h0 (zSa z0m n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using! h1
theorem z0z (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0l (zSa z0m n)
theorem z0A : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0k zH1
theorem z0B (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0k (zSg zH1 (zSg zH3 zH0))
  have h1 := zSg h0 (zSa z0n n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using! h1
theorem z0C (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1 := zSg z0l zH0
  have h1 := zSg h0 (zSa z0n n)
  simpa only [zLp',List.cons_append,List.nil_append] using! h1
theorem z0D (n : Nat) : Seg (([Call.ch] ^ n) ++ [.cj,.ch]) (([Call.ch] ^ (1 + n * 2)) ++ [.cj,.ch]) t t := by
  have h1 : Seg (([Call.ch] ^ n) ++ [.cj,.ch]) (([Call.ch] ^ (n * 2)) ++ [.ch,.cj,.ch]) t t :=
    zSg (H_T n) (z0t 0)
  have heq : (([Call.ch] ^ (n * 2)) ++ [.ch,.cj,.ch]) = (([Call.ch] ^ (1 + n * 2)) ++ [.cj,.ch]) := by
    have h2 : 1 + n * 2 = n * 2 + 1 := by omega
    rw [h2,z07,z06,List.append_assoc]
    rfl
  rwa [heq] at h1
theorem z0E (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([.cj] ++ [.ch] ^ n) (d1 ++ one) d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using! zSg zH3 (z0o n)
theorem z0F (n : Nat) : Seg (([Call.ch] ^ (1 + n * 2)) ++ [.cj,.ch]) ([.cj] ++ [.ch] ^ n) (d1 ++ one) (d1 ++ one) := by
  simpa only [List.append_nil] using! zSg (z0E n) z0A
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
    (mid1 := [1,0,1,1,1,1,0,1,1])
    (mid2 := [1,0,1,0,1,1,0,1,1])
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
      simpa using! hI [] _ hN2
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
      simpa using! hI [] _ hN2
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
def loc_z2Q : WordList := [Q,K,Q,K,K,V,K,Q,Q,Q,Q,Q,Q,Q]
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
  ⟨B,0,[1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1],[1,0,0,1,1,0,0,1,1,0,0,0,0,1,0,0,0,1]⟩
def loc_z33 : CCfg :=
  ⟨C,1,[0,1],[0,1,1,0,0,1,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,0,0,0,1]⟩
set_option maxRecDepth 4000000 in
theorem loc_z34 : zCm loc_z31 1000 = some loc_z32 := by decide
set_option maxRecDepth 4000000 in
theorem loc_z35 : zCm loc_z32 49 = some loc_z33 := by decide
theorem loc_z36 :
    (init []) [target_tm]⊢⁺
    (zCL lh ((w_pre ++ (t ^ 8 ++ [0,0,1,0,0,0,1])) +> default)) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = loc_z2R loc_z31 := rfl
  have h_end : loc_z2R loc_z33 = zCL lh ((w_pre ++ (t ^ 8 ++ [0,0,1,0,0,0,1])) +> default) := by
    unfold loc_z2R zCL lh
    rw [<- append_assoc]
    have h_list : [0] ++ (w_pre ++ (t ^ 8 ++ [0,0,1,0,0,0,1])) = loc_z33.right := by decide
    rw [h_list]
    simp only [Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,append_cons,append_nil,z00]
    rfl
  rw [h_init,<- h_end]
  exact zPt (zTc (by decide) loc_z34) (zTc (by decide) loc_z35)
def loc_z37 : WordList := [K,Q,K,Q,K,K,K,K,K]
def loc_z38 : WordList := [Q,K,K,Q,K,K,K,K,Q]
theorem loc_z39 :
    Side [.cj,.ch] (wordsToBits loc_z38 +> default) ((t ++ [0,0,1,1,0,0,0,0,1,0,0,0,0,1]) +> default) := by
  refine Side.cons (r2 := [1,1,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,1] +> default) ?_ (Side.cons ?_ (Side.nil _))
  · intro l
    unfold zCR zCL zCw zCs
    simp only [loc_z38,wordsToBits,d1,d0,List.cons_append,List.nil_append,append_cons,append_nil,z00]
    execute
  · intro l
    unfold zCR zCL zCw zCs t
    simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
    execute
theorem loc_z3a :
    (zCL lh ((w_pre ++ (t ^ 8 ++ [0,0,1,0,0,0,1])) +> default))
    [target_tm]⊢⁺
    (zCL lh ((w_pre ++ (t ^ 10 ++ [0,0,1,1,0,0,0,0,1,0,0,0,0,1])) +> default)) := by
  have hE : WordEffect 255 loc_z37 0 loc_z38 := by
    have h1 := evalEffect_sound loc_z37 255
    have h2 : evalEffect 255 loc_z37 = (0,loc_z38) := by decide
    rwa [h2] at h1
  rcases exists_digitVal_of_all_isDigitWordE loc_z38 (by decide) with ⟨A,hD⟩
  have hSeg_ch := zEd hE hD
  have hSide_ch := zSc hSeg_ch (Side.nil default)
  have hSide_255 := z08 hSide_ch loc_z39
  have hCarry : Seg [.cj,.ch] (([Call.ch] ^ 255) ++ [.cj,.ch]) (t ^ 8) (t ^ 8) := z0G 8 0
  have hSide_t8 := zSc hCarry hSide_255
  have hSide_ca := zSc z0H hSide_t8
  rcases hSide_ca with _ | ⟨hca,hnil⟩
  cases hnil
  have h_in : (w_pre +> ((t ^ 8) +> (wordsToBits loc_z37 +> default))) =
      ((w_pre ++ (t ^ 8 ++ [0,0,1,0,0,0,1])) +> default) := by
    simp only [loc_z37,wordsToBits,d0,d1,List.cons_append,List.nil_append,append_cons,append_nil,z00,append_assoc]
  have h_out : ((w_pre ++ t) +> ((t ^ 8) +> ((t ++ [0,0,1,1,0,0,0,0,1,0,0,0,0,1]) +> default))) =
      ((w_pre ++ (t ^ 10 ++ [0,0,1,1,0,0,0,0,1,0,0,0,0,1])) +> default) := by
    simp only [zLp,z05,List.cons_append,List.nil_append,append_cons,append_nil,append_assoc]
  rw [h_in,h_out] at hca
  exact zPt (z0I _) (hca lh)
theorem loc_z3b : Seg [.ch] [] [0,1,0,0] t :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
def loc_z3c : WordList := [K,K,K,K,K,K,K,K]
def loc_z3d : WordList := [K,Q,Q,Q,Q,Q,Q,Q]
theorem loc_z3e :
    Seg ([Call.ch] ^ 1023) ([Call.ch] ^ 254)
      (d0 ++ (t ++ (d0 ++ (d1 ++ (d0 ++ [0,1,0,0])))))
      (d1 ++ (t ++ (d0 ++ (d0 ++ (d0 ++ t))))) := by
  have h6 : Seg ([Call.ch] ^ 128) ([Call.ch] ^ 254) [0,1,0,0] t := by
    simpa only [zLp',List.cons_append,List.nil_append] using! zSg loc_z3b (H_T 127)
  exact zS0 (z0p 511)
    (zS0 (H_T 511)
      (zS0 (z0o 511)
        (zS0 (z0r 255)
          (zS0 (z0o 128) h6))))
theorem loc_z3f :
    Side [.cj,.ch]
      (((d1 ++ (t ++ (d0 ++ (d0 ++ (d0 ++ t))))) ++ wordsToBits loc_z3d) +> default)
      ((d1 ++ one) +> evalWords loc_z2Q default) := by
  refine Side.cons (r2 := ([0,0,1,1,0,0,0,1,0] ++ ((d0 ++ (d0 ++ t)) ++ wordsToBits loc_z3d)) +> default) ?_ (Side.cons ?_ (Side.nil _))
  · intro l
    unfold zCR zCL zCw zCs
    simp only [loc_z3d,wordsToBits,d1,d0,t,List.cons_append,List.nil_append,append_cons,append_nil,z00]
    execute
  · intro l
    unfold zCR zCL zCw zCs
    simp only [loc_z3d,wordsToBits,loc_z2Q,evalWords,d1,d0,t,one,List.cons_append,List.nil_append,append_cons,append_nil,z00]
    execute
theorem loc_z3g :
    (zCL lh ((w_pre ++ (t ^ 10 ++ [0,0,1,1,0,0,0,0,1,0,0,0,0,1])) +> default))
    [target_tm]⊢⁺
    (zCf 9 (evalWords loc_z2Q default)) := by
  have hE : WordEffect 254 loc_z3c 0 loc_z3d := by
    have h1 := evalEffect_sound loc_z3c 254
    have h2 : evalEffect 254 loc_z3c = (0,loc_z3d) := by decide
    rwa [h2] at h1
  rcases exists_digitVal_of_all_isDigitWordE loc_z3d (by decide) with ⟨A,hD⟩
  have hSeg_b := zEd hE hD
  have hSeg_all := zS0 loc_z3e hSeg_b
  have hSide_ch := zSc hSeg_all (Side.nil default)
  have hSide_1023 := z08 hSide_ch loc_z3f
  have hCarry : Seg [.cj,.ch] (([Call.ch] ^ 1023) ++ [.cj,.ch]) (t ^ 10) (t ^ 10) := z0G 10 0
  have hSide_t10 := zSc hCarry hSide_1023
  have hSide_ca := zSc z0H hSide_t10
  rcases hSide_ca with _ | ⟨hca,hnil⟩
  cases hnil
  have h_in : (w_pre +> ((t ^ 10) +> (((d0 ++ (t ++ (d0 ++ (d1 ++ (d0 ++ [0,1,0,0]))))) ++ wordsToBits loc_z3c) +> default))) =
      ((w_pre ++ (t ^ 10 ++ [0,0,1,1,0,0,0,0,1,0,0,0,0,1])) +> default) := by
    simp only [loc_z3c,wordsToBits,d0,d1,t,List.cons_append,List.nil_append,append_cons,append_nil,z00,append_assoc]
  have h_out : zCL lh (((w_pre ++ t) +> ((t ^ 10) +> ((d1 ++ one) +> evalWords loc_z2Q default)))) =
      zCf 9 (evalWords loc_z2Q default) := by
    unfold zCf
    simp only [zLp,z05,List.cons_append,List.nil_append,append_cons,append_nil,append_assoc]
  rw [h_in] at hca
  have hStep := zPt (z0I _) (hca lh)
  rwa [h_out] at hStep
theorem loc_z3h :
    (init []) [target_tm]⊢⁺ zCf 9 (evalWords loc_z2Q default) :=
  zPt loc_z36 (zPt loc_z3a loc_z3g)
def loc_z3i : List CodeE := [
  (.More CP0 2047 (.More CP0 4093 (.More CS00 2046 (.More CT 4089 (.More CS11 2044 (.More CP1 4088 (.More CP1 8176 (.More CP1 16352 (.More CP0 32704 (.Stop 32704)))))))))),
  (.More CT 4093 (.More CT 8185 (.More CS11 4092 (.More CT 8182 (.More CS00 4091 (.More CT 8179 (.More CT 16357 (.More CT 32713 (.More CT 65425 (.More CS10 32712 (.More CS10 16355 (.More CS00 8177 (.More CS00 4088 (.More CP1 8175 (.More CP1 16350 (.More CP1 32700 (.More CP1 65400 (.More CP1 130800 (.More CP0 261600 (.Stop 261600)))))))))))))))))))),
  (.More CT 8189 (.More CT 16377 (.More CS10 8188 (.More CT 16373 (.More CS11 8186 (.More CT 16370 (.More CT 32739 (.More CT 65477 (.More CT 130953 (.More CS10 65476 (.More CP0 130951 (.More CS00 65475 (.More CT 130947 (.More CT 261893 (.More CT 523785 (.More CT 1047569 (.More CT 2095137 (.More CT 4190273 (.More CS10 2095136 (.More CS10 1047567 (.More CS00 523783 (.More CS00 261891 (.More CS00 130945 (.More CP1 261889 (.More CP0 523778 (.More CP1 1047555 (.More CP1 2095110 (.More CP1 4190220 (.More CP1 8380440 (.More CP0 16760880 (.Stop 16760880)))))))))))))))))))))))))))))))
]
def loc_z3j : WordList := [V,V,Q,V,Q,V,V,V,V,Q,V,K,V,V,V,V,V,V,Q,Q,K,K,K,V,V,V,V,V,V,V]
def loc_z3k : WordList := [Q,K,K,K,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def loc_z3l : WordList := [K,K,K,K,Q,Q,K,Q,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
set_option maxRecDepth 4000000 in
theorem loc_z3m :
    ERounds 9 loc_z2Q 12 (loc_z3j ++ loc_z3k) := by
  have h1 : ERounds 9 loc_z2Q (9 + loc_z3i.length) (loc_z3j ++ loc_z3k) := by
    apply evalERounds_sound loc_z3i
    decide
  exact h1
set_option maxRecDepth 4000000 in
theorem loc_z3n :
    EGood 12 (loc_z3j ++ loc_z3k) := by
  apply eGood_of_check 12 loc_z3j loc_z3k loc_z3l
  · decide
  · exact EGuard.T 0 _
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · norm_num [loc_z3j,loc_z3l,wordMass,wordMassK,wordScale]
theorem zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
theorem loc_z3o (m : Nat) :
    ∃ N ≥ m,∃ h w,multiStep target_tm (init []) N = some (zCf h (evalWords w default)) /\ EGood h w := by
  induction m with
  | zero =>
    rcases loc_z3h with ⟨k1,_,hk1⟩
    rcases loc_z2P loc_z3m with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,12,loc_z3j ++ loc_z3k,
      zMt target_tm _ _ _ k1 k2 hk1 hk2,loc_z3n⟩
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
  rcases loc_z3o (n + 1) with ⟨N,hN,_,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LFHHH_1RA1RF
