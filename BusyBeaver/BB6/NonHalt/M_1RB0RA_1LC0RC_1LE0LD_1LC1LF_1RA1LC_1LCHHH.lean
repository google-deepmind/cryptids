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

namespace BusyBeaver.M_1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LCHHH


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LCHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
open Counter

variable {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
@[reducible] def holdout_0001_tm : Machine (Fin 2) (Fin 6) := target_tm
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
set_option maxHeartbeats 2000000
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
local macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
local macro "gstep" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.ListBlank.head_cons,zDh]); rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,z00,zDh,zDt])
local macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | gstep)))
abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev z04 (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev z0b (c : CCfg) : Option CCfg := Counter.bstep holdout_0001_tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep holdout_0001_tm n c
theorem zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (z04 c1) [holdout_0001_tm]⊢⁺ (z04 c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩
abbrev t : BitWord := [1,1,0,0]
abbrev d0 : BitWord := [0,0]
abbrev d1 : BitWord := [1,0]
abbrev one : BitWord := [1]
abbrev lh : HalfTape := [1,0,1] +> default
abbrev w_pre : BitWord := t ++ t ++ one
@[simp] theorem zDd : d0 +> (default : HalfTape) = default := by
  simp [d0]
inductive Call where
  | ch
  | cj
  | cp
  | ca
def zCs : Call -> Fin 6
  | .ch => E
  | .cj => C
  | .cp => C
  | .ca => E
def zCw : Call -> BitWord
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
  | .ca => [1,1,1,0,1,0]
def zCR (l : HalfTape) (c : Call) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (r <{{zCs c}} (l <+ zCw c))
def zCL (l : HalfTape) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> r) {{A}}> l)
def zCf (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  zCL lh (w_pre +> r)
def z0f (c : Call) (r1 r2 : HalfTape) : Prop :=
  ∀ l,(zCR l c r1) [holdout_0001_tm]⊢⁺ (zCL l r2)
inductive Side : List Call -> HalfTape -> HalfTape -> Prop where
  | nil (r : HalfTape) : Side [] r r
  | cons {c : Call} {ls : List Call} {r1 r2 r3 : HalfTape} :
      z0f c r1 r2 -> Side ls r2 r3 -> Side (c :: ls) r1 r3
def Seg (ls_in ls_out : List Call) (w1 w2 : BitWord) : Prop :=
  ∀ r1 r2,Side ls_out r1 r2 -> Side ls_in (w1 +> r1) (w2 +> r2)
@[simp] theorem z0g {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] theorem zLp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] theorem zLp' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] theorem z0h {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l
theorem z0i {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm,zLp,zLp,ih,List.append_assoc]
theorem z0j {ls1 ls2 : List Call} {r1 r2 r3 : HalfTape}
    (h1 : Side ls1 r1 r2) (h2 : Side ls2 r2 r3) : Side (ls1 ++ ls2) r1 r3 := by
  induction h1 with
  | nil _ => exact h2
  | cons hc _ ih => exact Side.cons hc (ih h2)
theorem z0k {ls1 ls2 : List Call} {r1 r3 : HalfTape}
    (h : Side (ls1 ++ ls2) r1 r3) : ∃ r2,Side ls1 r1 r2 /\ Side ls2 r2 r3 := by
  induction ls1 generalizing r1 with
  | nil => exact ⟨r1,Side.nil r1,h⟩
  | cons c ls1 ih =>
    rcases h with _ | ⟨hc,hrest⟩
    rcases ih hrest with ⟨r2,h1,h2⟩
    exact ⟨r2,Side.cons hc h1,h2⟩
theorem z0l (w : BitWord) : Seg [] [] w w := by
  intro r1 r2 h; cases h; exact Side.nil (w +> r1)
theorem z0m (ls : List Call) : Seg ls ls [] [] := by
  intro r1 r2 h; exact h
theorem zSc {ls1 ls2 : List Call} {w1 w2 : BitWord} {r1 r2 : HalfTape}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
    Side ls1 (w1 +> r1) (w2 +> r2) :=
  h1 r1 r2 h2
theorem zSg {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : BitWord}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3 := by
  intro r1 r3 h
  rcases z0k h with ⟨r2,ha,hb⟩
  exact z0j (h1 r1 r2 ha) (h2 r2 r3 hb)
theorem zS0 {ls1 ls2 ls3 : List Call} {w1 w2 v1 v2 : BitWord}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls2 ls3 v1 v2) :
    Seg ls1 ls3 (w1 ++ v1) (w2 ++ v2) := by
  intro r1 r2 h
  rw [append_assoc,append_assoc]
  exact h1 (v1 +> r1) (v2 +> r2) (h2 r1 r2 h)
theorem zS4 {c : Call} {w1 w2 : BitWord}
    (h1 : ∀ l r,(zCR l c (w1 +> r)) [holdout_0001_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)
theorem zS2 {c_in c_out : Call} {w1 w2 mid : BitWord}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [holdout_0001_tm]⊢⁺ (zCR (mid +> l) c_out r))
    (h2 : ∀ l r,(zCL (mid +> l) r) [holdout_0001_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1) (zPt (hc1 (mid +> l)) (h2 l r2))
theorem zS5 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : BitWord}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [holdout_0001_tm]⊢⁺ (zCR (mid1 +> l) c1 r))
    (h2 : ∀ l r,(zCL (mid1 +> l) r) [holdout_0001_tm]⊢⁺ (zCR (mid2 +> l) c2 r))
    (h3 : ∀ l r,(zCL (mid2 +> l) r) [holdout_0001_tm]⊢⁺ (zCL l (w2 +> r))) :
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
theorem z0n : Seg [.cp] [.ch] t (t ++ [0]) :=
  zS2 (mid := [1,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0o : Seg [.cj] [.ch] t (t ++ one) :=
  zS2 (mid := [1,1,0,1,1])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0p : Seg [.ch] [.cj] (t ++ [0]) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH2 : Seg [.ch] [.cj,.ch] (t ++ one) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0q : Seg [.ch] [.ch,.ch] t t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0r : Seg [.cp] [] (d1 ++ d0) (t ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d1 d0 t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0s : Seg [.cj] [.cj] (d1 ++ d0) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1 d0; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0t : Seg [.cp] [.cp] (d1 ++ d1) t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0u : Seg [.cj] [.cp,.ch] (d1 ++ d1) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0v : Seg [.cj] [] d0 (d0 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH1 : Seg [.ch] [] (d0 ++ one) (d1 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH3 : Seg [.ch] [.cj] (d1 ++ one) d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
theorem z0w : Seg [.cj] [.cp] d1 d0 :=
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
  | zero => exact z0l t
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [zLp,h_eq,z0i]
    exact zSg z0q ih
theorem zSa {w2 : BitWord} (hw : Seg [.ch,.ch] [.ch] w2 w2) (n : Nat) :
    Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) w2 w2 := by
  induction n with
  | zero => exact z0l w2
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq,z0i,zLp]
    exact zSg hw ih
theorem z0x : Seg [.ch,.ch] [.ch] d0 d0 :=
  zSg zH0 zH4
theorem z0y : Seg [.ch,.ch] [.ch] d1 d1 :=
  zSg zH4 zH0
theorem z0z (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d0 d0 :=
  zSa z0x n
theorem z0A (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ n) d0 d1 := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg zH0 (zSa z0y n)
theorem z0B (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d1 d1 :=
  zSa z0y n
theorem z0C (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ (1 + n)) d1 d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg zH4 (zSa z0x n)
theorem z0D (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0n z0p) (H_T n)
theorem z0E (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0o zH2) (H_T n)
theorem z0F (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0r zH2) (H_T n)
theorem z0G (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0s (H_T n)
theorem z0H (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0t (H_T n)
theorem z0I (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using zSg z0u (H_T n)
theorem z0J (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0v (zSg zH1 zH3)
  have h1 := zSg h0 (zSa z0x n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
theorem z0K (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0w (zSa z0x n)
theorem z0L : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0v zH1
theorem z0M (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0v (zSg zH1 (zSg zH3 zH0))
  have h1 := zSg h0 (zSa z0y n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
theorem z0N (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1 := zSg z0w zH0
  have h1 := zSg h0 (zSa z0y n)
  simpa only [zLp',List.cons_append,List.nil_append] using h1
theorem z0O : Side [.ch] default (d1 +> default) := by
  refine Side.cons (fun l => ?_) (Side.nil _)
  unfold zCR zCL zCw zCs d1
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
theorem z0P : Seg [.ca] [.ch,.ch] t [1,1,0,0,0,1,1,0,0] :=
  zS5
    (mid1 := [1,0,1,1,1,1,0,1,0])
    (mid2 := [1,0,1,0,1,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0Q : Seg [.ch] [.ch] [1,1,0,0,0,1,1,0,0] (t ++ t ++ one) :=
  zS2
    (mid := [1,1,0,1,1,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0R : Seg [.ca,.ch] ([.cj] ++ [.ch] ^ 5) w_pre (w_pre ++ t) := by
  have h1 : Seg [.ca,.ch] [.ch,.ch,.ch] t (t ++ t ++ one) :=
    zSg z0P z0Q
  have h2 : Seg [.ch,.ch,.ch] ([.cj] ++ [.ch] ^ 5) (t ++ one) t :=
    zSg zH2 (H_T 2)
  have h3 := zS0 h1 h2
  simpa only [w_pre,List.append_assoc,List.cons_append,List.nil_append] using h3
theorem z0S (r : HalfTape) :
    (zCL lh r) [holdout_0001_tm]⊢⁺ (zCR ([1] +> default) .ca r) := by
  unfold zCL zCR lh zCw zCs
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
theorem z0T (r : HalfTape) :
    (zCL ([1] +> default) r) [holdout_0001_tm]⊢⁺ (zCR lh .ch r) := by
  unfold zCL zCR lh zCw zCs
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
open WordCalculus
open WordCalculus.Word
local notation "WordList" => List Word
def z3p : WordList :=
  [Q,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V]
def z3q : WordList :=
  [K,V,K,V,V,V,V,V,V,K,V,V,V,K,V]
theorem z3w (n : Nat) :
    Copy (31 + 32 * n) (260 + 256 * n) z3p z3q (4617 + 4096 * n) (30684 + 32768 * n) := by
  unfold z3p z3q
  refine copy_step_d11 (n' := 16 + 16 * n) (k' := 128 + 128 * n) (m := 64 + 64 * n) (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 33 + 32 * n) (k' := 252 + 256 * n) (m := 125 + 128 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 17 + 16 * n) (k' := 124 + 128 * n) (m := 62 + 64 * n) (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 35 + 32 * n) (k' := 244 + 256 * n) (m := 121 + 128 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 71 + 64 * n) (k' := 484 + 512 * n) (m := 241 + 256 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 143 + 128 * n) (k' := 964 + 1024 * n) (m := 481 + 512 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 287 + 256 * n) (k' := 1924 + 2048 * n) (m := 961 + 1024 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 575 + 512 * n) (k' := 3844 + 4096 * n) (m := 1921 + 2048 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 1151 + 1024 * n) (k' := 7684 + 8192 * n) (m := 3841 + 4096 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 576 + 512 * n) (k' := 3840 + 4096 * n) (m := 1920 + 2048 * n) (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 1153 + 1024 * n) (k' := 7676 + 8192 * n) (m := 3837 + 4096 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 2307 + 2048 * n) (k' := 15348 + 16384 * n) (m := 7673 + 8192 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 4615 + 4096 * n) (k' := 30692 + 32768 * n) (m := 15345 + 16384 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 2308 + 2048 * n) (k' := 15344 + 16384 * n) (m := 7672 + 8192 * n) (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 4617 + 4096 * n) (k' := 30684 + 32768 * n) (m := 15341 + 16384 * n) (by omega) (by omega) (by omega) ?_
  exact Copy.nil _ _
theorem z3x (q : Nat) (hQ : 5 <= q) :
    CopyTwelve (List.replicate q V ++ z3p) (List.replicate q V ++ z3q) := by
  have hPow : 2 ^ q = 32 * 2 ^ (q - 5) := by
    have heq : q = 5 + (q - 5) := by omega
    conv_lhs => rw [heq,Nat.pow_add]
  have hPos := pow_two_pos (q - 5)
  have hTs := copy_replicate_V q 0 8
  have hBase := z3w (2 ^ (q - 5) - 1)
  have h1 : (1 + 0) * 2 ^ q - 1 = 31 + 32 * (2 ^ (q - 5) - 1) := by omega
  have h2 : 4 + 8 * 2 ^ q = 260 + 256 * (2 ^ (q - 5) - 1) := by omega
  rw [h1,h2] at hTs
  exact ⟨_,_,copy_append hTs hBase⟩
theorem z3y : isSafePrefix z3q = true := by decide +kernel
def z3K : WordList :=
  [K,Q,K,Q,Q,Q,Q,Q,K] ++ List.replicate 15 Q
def z3L : WordList :=
  [V,V,Q,V,Q,V,K,K,V,Q,K]
def u_5 : WordList := [V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,K,K,Q,Q,Q,K,Q,Q,Q,Q,K,Q,K,K,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q]
def z3M : WordList := [V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,K,V,Q,Q,V,V,Q,V,K,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,Q,V,K,V,V,Q,V,V,V,V,Q,K,V,V,V,V,V,Q,V,Q,V,K,V,V,Q,K,Q,V,V,V,V,V,V,K,V,V,V,V,V,Q,V,V,V,V,V,K,K,K,K,K,Q,K,K,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,K,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def z3N : WordList := [V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,Q,V,Q,V,V,Q,V,V,V,V,Q,Q,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,Q,K,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,Q,V,Q,V,Q,V,V,K,K,Q,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,Q,V,Q,V,V,Q,K,K,V,V,V,V,V,V,Q,V,V,V,V,V,V,V]
def z3O : WordList := [V,V,V,V,V,V,V,Q,V,Q,V,K,V,V,Q,V,Q,V,Q,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,K,V,Q,V,K,V,V,Q,K,Q,V,V,V,V,V,V,K,V,V,V,V,V,Q,V,V,V,V,V,V,K,K,K,K,K,K,Q,K,K,Q,K,Q,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,K,Q,K,Q,Q,Q,K,K,K,Q,K,Q,K,K,K,K,K,K,K,K,K,K,K,K,K,Q,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,Q,K,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def z3P : WordList := [V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,Q,V,Q,V,V,Q,V,V,V,V,Q,Q,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,Q,V,Q,V,Q,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,K,V,K,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,Q,V,Q,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,K,V,Q,V,V,Q,Q,K,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,Q,V,Q,V,Q,K,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,K,V,V,V,Q,V,Q,V,V,Q,V,K,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,Q,V,Q,V,V,Q,K,K,V,V]
def z3Q : WordList := [V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,K,V,V,Q,V,Q,V,Q,K,K,V,V,V,V,Q,Q,V,V,K,K,V,Q,V,Q,V,V,Q,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,Q,V,K,V,V,V,V,K,K,V,K,Q,V,V,V,V,V,V,Q,V,Q,V,K,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,K,V,Q,V,K,V,V,Q,K,Q,V,V,V,V,V,V,K,V,V,V,V,V,Q,V,V,V,V,V,V,V,K,K,K,K,K,K,K,Q,K,K,Q,K,Q,Q,Q,Q,K,Q,K,Q,K,Q,K,K,K,K,Q,Q,Q,K,Q,Q,Q,K,K,K,Q,Q,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,K,K,Q,Q,K,K,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,K,K,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,K,K,K,Q,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def z3R : WordList := [V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,Q,V,Q,V,V,Q,V,V,V,V,Q,Q,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,Q,V,Q,V,Q,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,K,V,K,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,Q,V,Q,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,K,V,K,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,Q,V,Q,V,Q,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,Q,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,K,V,Q,V,V,Q,Q,K,V,V]
def z3S : WordList := [V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,Q,V,V,Q,V,Q,V,Q,K,Q,V,V,V,V,Q,Q,V,V,V,V,K,V,Q,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,Q,V,Q,V,V,Q,K,K,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,K,V,V,Q,V,Q,V,Q,K,Q,V,V,V,V,Q,Q,Q,K,V,V,K,Q,V,V,V,V,V,V,K,V,K,Q,K,Q,Q,Q,K,K,K,Q,Q,V,V,V,Q,V,K,Q,V,V,V,V,V,V,V,V,Q,V,K,V,K,V,Q,V,K,V,Q,V,V,V,V,V,V,V,Q,V,K,V,V,Q,V,V,V,V,V,V,V,K,Q,V,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,V,V,Q,Q,Q,Q,V,V,V,V,V,V,V,Q,K,V,K,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,K,V,Q,V,K,V,V,Q,K,Q,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V]
def z3T : WordList := [K,K,K,K,K,K,K,Q,Q,Q,K,K,Q,K,Q,Q,Q,Q,K,Q,K,Q,K,Q,K,K,K,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,K,K,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,K,K,K,Q,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,K,Q,Q,K,K,K,Q,K,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,K,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,K,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,K,K,Q,K,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,K,K,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,K,K,K,Q,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def z3U : WordList := [V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,Q,V,Q,V,V,Q,V,V,V,V,Q,Q,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,Q,V,Q,V,Q,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,K,V,K,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,Q,V,Q,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,K,V,K,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,Q,V,Q,V,Q,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,Q,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,K,V,K,V,V,Q,V,V,V]
def z3V : WordList := [V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,Q,V,V,Q,V,Q,V,Q,Q,K,V,V,V,V,Q,Q,V,V,V,V,Q,V,K,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,K,V,Q,V,V,Q,Q,K,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,Q,V,Q,V,Q,K,Q,V,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,K,V,V,Q,Q,Q,K,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,K,V,K,V,Q,V,K,V,V,V,V,V,V,V,Q,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,V,V,V,Q,Q,V,Q,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,Q,V,Q,V,V,Q,K,K,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V]
def z3W : WordList := [V,V,V,V,Q,V,Q,V,K,V,V,Q,V,Q,V,Q,K,K,V,V,V,V,Q,Q,Q,K,V,V,V,V,V,Q,V,V,V,K,V,V,Q,Q,V,V,V,Q,V,Q,V,Q,V,V,Q,V,K,Q,V,V,V,V,V,V,V,Q,K,V,V,Q,V,Q,K,V,K,V,V,Q,V,V,V,V,Q,K,V,K,Q,Q,V,V,V,V,V,V,V,V,Q,V,K,K,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,Q,Q,V,K,V,V,V,V,V,Q,V,V,Q,V,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,Q,Q,Q,Q,V,V,V,V,V,V,V,Q,K,V,K,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,K,V,Q,V,K,V,V,Q,K,Q,V,V,V,V,V,V,K,V,V,V,V,V,Q,V,V,V,V,V,V,V]
def z3X : WordList := [K,K,K,K,K,K,K,K,Q,K,K,Q,K,Q,Q,Q,Q,K,Q,K,Q,K,Q,K,K,K,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,K,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,K,Q,Q,Q,Q,Q,K,Q,Q,K,K,K,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,K,K,K,Q,Q,Q,K,K,K,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,K,K,Q,Q,Q,K,Q,K,K,K,K,K,K,K,Q,K,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,Q,K,Q]
def z3Y : WordList := [Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,K,K,Q,K,Q,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,K,K,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,K,K,K,Q,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
theorem z45 : EntrySpec 18 z3p z3K 11000 := entrySpec_of_checkEntrySpec (by decide +kernel)
set_option maxRecDepth 500000 in
theorem z46 : evalRounds 5 z3L = some u_5 := by decide +kernel
set_option maxRecDepth 500000 in
theorem z47 : evalRounds 5 u_5 = some z3M := by decide +kernel
set_option maxRecDepth 500000 in
theorem z48 : evalRounds 2 z3M = some (z3N ++ z3O) := by decide +kernel
set_option maxRecDepth 500000 in
theorem z49 : evalRounds 2 (z3N ++ z3O) = some (z3P ++ z3Q) := by decide +kernel
set_option maxRecDepth 500000 in
theorem z4a :
    checkStepTwoPieces z3P z3Q 110434817290149211768284085870454066060546939462225549259006050933145647 7067168235385531200914694256602959202955917586119058258266247915060068152 1260824944739856172946394001775484681970160284962916614243143022817523291247800206387780525642753349635545663353377664 z3R z3S z3T = true := by decide +kernel
set_option maxRecDepth 500000 in
theorem z4b :
    checkStepThreePieces (V :: z3R) (z3S ++ [V]) (z3T ++ [Q])
      1766902070710385858937921437335091786398117464135613873040684957281812527 630451725914695248319732282316851358108579217770468995664483969260760571151030486379468182403867732674229876057702399 113076451955992548153983074076597066130126825388972272726165497219966302796 676910774998025375822660775135045812617818152164822448708937095293664528614370053480259847094293709720004454266978684988792836 1675949902787505483440020087106021837049676974903580799208465931217206203605325682553129796896712940054963540497648261454412042999479128922952102697101568 z3U z3V z3W z3X z3Y = true := by decide +kernel
set_option maxRecDepth 500000 in
theorem z4c :
    checkEntryThreePieces 18 z3p z3K 11000
      (V :: z3U) z3V (z3W ++ [V]) z3X z3Y
      244 416 508 28269993083910161508169751504624082417804810888089862649298329268595458391 169232962271100938707715443929017058497083679336597570160963934441725064445424265138458712223603740228005634717572939333509119 838001039849071895726743081222718556285143149697103330185313006108943225172823266912222700929127475495397164689088385716467769609144035444689331281199359 28948472917924005384365825540735060395832126349404019352881489171041749393536 47079 4103 = true := by decide +kernel
theorem z4d : ∃ v,Rounds z3L v /\ AggState z3p 16 18 v := by
  have h0_5 := evalRounds_sound 5 z3L u_5 z46
  have h5_10 := evalRounds_sound 5 u_5 z3M z47
  have h10_12 := evalRounds_sound 2 z3M (z3N ++ z3O) z48
  have h12_14 := evalRounds_sound 2 (z3N ++ z3O) (z3P ++ z3Q) z49
  have h14_15 := step_of_checkStepTwoPieces z3P z3Q 110434817290149211768284085870454066060546939462225549259006050933145647 7067168235385531200914694256602959202955917586119058258266247915060068152 1260824944739856172946394001775484681970160284962916614243143022817523291247800206387780525642753349635545663353377664 z3R z3S z3T z4a
  have h15_16 := step_of_checkStepThreePieces (V :: z3R) (z3S ++ [V]) (z3T ++ [Q])
    1766902070710385858937921437335091786398117464135613873040684957281812527 630451725914695248319732282316851358108579217770468995664483969260760571151030486379468182403867732674229876057702399 113076451955992548153983074076597066130126825388972272726165497219966302796 676910774998025375822660775135045812617818152164822448708937095293664528614370053480259847094293709720004454266978684988792836 1675949902787505483440020087106021837049676974903580799208465931217206203605325682553129796896712940054963540497648261454412042999479128922952102697101568 z3U z3V z3W z3X z3Y z4b
  have hEq15 : V :: ((z3R ++ z3S) ++ V :: (z3T ++ [Q])) =
      (V :: z3R) ++ (z3S ++ [V]) ++ (z3T ++ [Q]) := by
    simp [List.append_assoc]
  rw [hEq15] at h14_15
  have hEq16 : V :: ((z3U ++ z3V ++ z3W) ++ V :: ((z3X ++ z3Y) ++ [Q])) =
      ((V :: z3U) ++ z3V ++ (z3W ++ [V])) ++ (z3X ++ z3Y) ++ [Q] := by
    simp [List.append_assoc]
  rw [hEq16] at h15_16
  have hGood := good_of_checkEntryThreePieces 18 z3p z3K 11000
    (V :: z3U) z3V (z3W ++ [V]) z3X z3Y
    244 416 508 28269993083910161508169751504624082417804810888089862649298329268595458391 169232962271100938707715443929017058497083679336597570160963934441725064445424265138458712223603740228005634717572939333509119 838001039849071895726743081222718556285143149697103330185313006108943225172823266912222700929127475495397164689088385716467769609144035444689331281199359 28948472917924005384365825540735060395832126349404019352881489171041749393536 47079 4103
    z45 z4c
  refine ⟨_,?_,hGood⟩
  exact rounds_trans h0_5 (rounds_trans h5_10 (rounds_trans h10_12 (rounds_trans h12_14
    (Rounds.next h14_15 (Rounds.next h15_16 (Rounds.refl _))))))
inductive Num : Nat -> BitWord -> List Call -> Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)
theorem z4e {k : Nat} (hK : 0 < k) : ∃ hs,Num k [] hs := by
  rcases even_or_odd_mul_two k with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · cases a with
    | zero => omega
    | succ a =>
      have heq : (a + 1) * 2 = 2 + a * 2 := by omega
      rw [heq]; exact ⟨[.cj] ++ [.ch] ^ a,Num.even a⟩
  · exact ⟨[.cp] ++ [.ch] ^ a,Num.odd a⟩
theorem z4f {k : Nat} {hs hs' : List Call} (h1 : Num k [] hs) (h2 : Num k [] hs') :
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
def z4g (k : Nat) (r r' : HalfTape) : Prop :=
  ∀ w hs,Num k w hs -> Side hs (w +> r) r'
theorem z4h {r r' : HalfTape} (h : z4g 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl
theorem z4i {n : Nat} {r r' : HalfTape}
    (hI : z4g (n * 2) r r') : z4g (2 + n * 4) (d0 +> r) (d0 +> r') := by
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
      have hr' := z4h hI
      subst hr'
      rw [<- append_assoc d0 one r]
      exact zSc z0v (Side.nil r)
    | succ n =>
      have heq : (n + 1) * 2 = 2 + n * 2 := by omega
      rw [heq]
      refine zSc (z0J n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        rw [heq]; exact Num.even n
      simpa using hI [] _ hN2
theorem z4j {n : Nat} {r r' : HalfTape}
    (hI : z4g (n * 2) r r') : z4g (4 + n * 4) (d0 +> r) (d1 +> r') := by
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
      have hr' := z4h hI
      subst hr'
      rw [<- append_assoc d1 one r]
      exact zSc z0L (Side.nil r)
    | succ n =>
      have heq : 1 + (n + 1) * 2 = 3 + n * 2 := by omega
      rw [heq]
      refine zSc (z0M n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        have heq2 : (n + 1) * 2 = 2 + n * 2 := by omega
        rw [heq2]; exact Num.even n
      simpa using hI [] _ hN2
theorem z4k {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hZ : A = 0) :
    evalWords da default = default := by
  induction hD with
  | nil => rfl
  | @zero A H u _ ih =>
    have hA0 : A = 0 := by omega
    dsimp only [evalWords]
    rw [ih hA0,zDd]
  | one _ => omega
theorem z4l {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hPos : 0 < A) :
    z4g ((A - 1) * 2) default (evalWords da default) := by
  induction hD with
  | nil => omega
  | @zero A H u _ ih =>
    have hA_pos : 0 < A := by omega
    have hIH := ih hA_pos
    have hs := z4i hIH
    rw [zDd] at hs
    have heq : (A * 2 - 1) * 2 = 2 + (A - 1) * 4 := by omega
    dsimp [evalWords]
    rwa [heq]
  | @one A H u hDu ih =>
    cases A with
    | zero =>
      change z4g 0 default (d1 +> evalWords u default)
      rw [z4k hDu rfl]
      intro w hs hN
      generalize hk : 0 = k0 at hN
      cases hN with
      | zero =>
        have hd : d1 +> (default : HalfTape) = one +> default := by simp [d1,one]
        rw [hd]; exact Side.nil (one +> default)
      | odd _ => omega
      | even _ => omega
    | succ A =>
      have hA_pos : 0 < A + 1 := by omega
      have hIH := ih hA_pos
      have heq_in : (A + 1 - 1) * 2 = A * 2 := by omega
      rw [heq_in] at hIH
      have hs := z4j hIH
      rw [zDd] at hs
      have heq : (1 + (A + 1) * 2 - 1) * 2 = 4 + A * 4 := by omega
      dsimp [evalWords]
      rwa [heq]
theorem zEd {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (hI : WordEffect n u b v) :
    ∀ {A H : Nat},DigitVal A H v -> Seg ([Call.ch] ^ n) ([Call.ch] ^ b) (wordsToBits u) (wordsToBits v) := by
  induction hI with
  | nil n =>
    intro A H _
    exact z0m ([Call.ch] ^ n)
  | T _ _ =>
    intro A H hD
    exact False.elim (digitVal_not_cons_V hD)
  | d00 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0z _) (ih hD')
  | d01 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0A _) (ih hD')
  | d10 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0B _) (ih hD')
  | d11 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A',H',hD',_,_⟩
    exact zS0 (z0C _) (ih hD')
theorem z4m {n : Nat} {hs hs' : List Call}
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
        exact z0D m
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
        exact z0E m
theorem z4n {n : Nat} {hs hs' : List Call}
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
        exact z0F m
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      have hq : q = m * 2 := by omega
      subst hq
      exact z0G m
theorem z4o {n : Nat} {hs hs' : List Call}
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
      exact z0H m
    | even _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hq : q = 1 + m * 2 := by omega
      subst hq
      exact z0I m
    | even _ => omega
theorem z4p {n : Nat} {hs hs' : List Call}
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
        exact z0J q
theorem z4q {n : Nat} {hs hs' : List Call}
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
      exact z0K q
    | even _ => omega
theorem z4r {n : Nat} {hs hs' : List Call}
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
        exact z0M q
theorem z4s {n : Nat} {hs hs' : List Call}
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
      exact z0N q
    | even _ => omega
theorem z4t {k : Nat} {v : WordList} {k' : Nat} {w : WordList} {a b : Rat}
    (hI : PhaseScan k v k' w a b) :
    ∀ {u : WordList} {n n' : Nat} {hs hs' : List Call},
      WordEffect n u n' v -> Num k [] hs -> Num k' [] hs' ->
      Seg (([Call.ch] ^ n) ++ hs) (([Call.ch] ^ n') ++ hs') (wordsToBits u) (wordsToBits w) := by
  induction hI with
  | nil k =>
    intro u n n' hs hs' hE hN hN'
    cases hE
    rw [z4f hN hN']
    exact z0m (([Call.ch] ^ n) ++ hs')
  | @T m _ _ _ _ _ _ ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    cases hE with
    | T hSub =>
      rcases z4e (by omega : 0 < 2 + m * 2) with ⟨hs0,hN0⟩
      have hIH := ih hSub hN0 hN'
      have hStep := zSg (H_T n0) (z4m hN hN0)
      have heq : ([Call.ch] ^ (n0 * 2)) ++ ([Call.ch] ++ hs0) = ([Call.ch] ^ (1 + n0 * 2)) ++ hs0 := by
        have h1 : 1 + n0 * 2 = n0 * 2 + 1 := by omega
        rw [h1,z0i,z0h,List.append_assoc]
      rw [heq] at hStep
      exact zS0 hStep hIH
  | @pair0 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q,K] ++ u) at hE
    rcases wordEffect_split_output [Q,K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases z4e hPos with ⟨hs0,hN0⟩
    have hD10 : DigitVal 1 2 [Q,K] := DigitVal.one (DigitVal.zero DigitVal.nil)
    have hStep := zSg (zEd hL hD10) (z4n hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @pair1 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q,Q] ++ u) at hE
    rcases wordEffect_split_output [Q,Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z4e (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD11 : DigitVal 3 2 [Q,Q] := DigitVal.one (DigitVal.one DigitVal.nil)
    have hStep := zSg (zEd hL hD11) (z4o hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short00 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([K] ++ u) at hE
    rcases wordEffect_split_output [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases z4e hPos with ⟨hs0,hN0⟩
    have hD0 : DigitVal 0 1 [K] := DigitVal.zero DigitVal.nil
    have hStep := zSg (zEd hL hD0) (z4p hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short01 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q] ++ u) at hE
    rcases wordEffect_split_output [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z4e (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : DigitVal 1 1 [Q] := DigitVal.one DigitVal.nil
    have hStep := zSg (zEd hL hD1) (z4q hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short10 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([K] ++ u) at hE
    rcases wordEffect_split_output [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases z4e hPos with ⟨hs0,hN0⟩
    have hD0 : DigitVal 0 1 [K] := DigitVal.zero DigitVal.nil
    have hStep := zSg (zEd hL hD0) (z4r hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short11 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q] ++ u) at hE
    rcases wordEffect_split_output [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z4e (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : DigitVal 1 1 [Q] := DigitVal.one DigitVal.nil
    have hStep := zSg (zEd hL hD1) (z4s hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
theorem z4u {n : Nat} {r r' : HalfTape}
    (hI : z4g (n * 2) r r') : z4g (1 + n) (d1 +> (d0 +> r)) (t +> r') := by
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
      have hr' := z4h hI
      subst hr'
      rw [<- append_assoc t one r]
      exact zSc z0r (Side.nil r)
    | succ m =>
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      refine zSc (z0F m) ?_
      have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : n * 2 = 2 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil,<- append_assoc d1 d0 r]
    refine zSc (z0G m) ?_
    have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : n * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2
theorem z4v {k : Nat} {v : WordList} {k' : Nat} {w : WordList} {a b : Rat}
    (hI : PhaseScan k v k' w a b) {u : WordList} {r' : HalfTape}
    (hE : WordEffect 0 u 1 v) (hK : 0 < k') (hC : z4g k' (d1 +> default) r') :
    z4g k (evalWords u default) (evalWords w r') := by
  intro w0 hs hN
  have hPosK : 0 < k := phaseScan_pos_of_out_pos hI hK
  have hw0 : w0 = [] := by cases hN <;> first | rfl | omega
  subst hw0
  rcases z4e hK with ⟨hs',hN'⟩
  have hSeg := z4t hI hE hN hN'
  dsimp at hSeg
  have hSide := zSc hSeg (z0j z0O (hC [] hs' hN'))
  rwa [wordsToBits_append_tape,wordsToBits_append_tape] at hSide
theorem z4w {orig out : WordList} (hS : Step orig out) :
    ∃ r,z4g 12 (evalWords orig default) r /\ evalWords out default = t +> r := by
  cases hS with
  | intro eff k v a b J A da hE hI hDA hSum =>
    have hposJ := pow_two_pos J
    have hPosK : 0 < k := by omega
    have hDFull : DigitVal k (J + 1) (da ++ [Q]) := by
      have h := digitVal_append hDA (DigitVal.one DigitVal.nil)
      have heq : A + 1 * 2 ^ J = k := by omega
      rwa [heq] at h
    have hC0 : z4g ((k - 1) * 2) default (evalWords (da ++ [Q]) default) :=
      z4l hDFull hPosK
    have hC1 : z4g k (d1 +> default) (evalWords (V :: (da ++ [Q])) default) := by
      have h := z4u hC0
      have hk : 1 + (k - 1) = k := by omega
      rwa [hk,zDd] at h
    have hRun := z4v hI hE hPosK hC1
    rw [<- evalWords_append] at hRun
    exact ⟨evalWords (v ++ V :: (da ++ [Q])) default,hRun,rfl⟩
theorem z4x {r r' : HalfTape} (hI : z4g 12 r r') :
    (zCf r) [holdout_0001_tm]⊢⁺ zCf (t +> r') := by
  have h_num : Num 12 [] ([.cj] ++ [.ch] ^ 5) := Num.even 5
  have hC := hI [] ([.cj] ++ [.ch] ^ 5) h_num
  have hS := zSc z0R hC
  rcases hS with _ | ⟨hca,hrest⟩
  rcases hrest with _ | ⟨hch,hnil⟩
  cases hnil
  have h1 := zPt (z0S (w_pre +> r)) (hca ([1] +> default))
  have h2 := zPt (z0T _) (hch lh)
  have h3 := zPt h1 h2
  rwa [append_assoc] at h3
theorem z4y {orig out : WordList} (hS : Step orig out) :
    (zCf (evalWords orig default)) [holdout_0001_tm]⊢⁺ zCf (evalWords out default) := by
  rcases z4w hS with ⟨r,hC,hEq⟩
  rw [hEq]
  exact z4x hC
theorem z4z {u v : WordList} (hR : Rounds u v) :
    (zCf (evalWords u default)) [holdout_0001_tm]⊢* zCf (evalWords v default) := by
  induction hR with
  | refl u => exact ⟨0,rfl⟩
  | next hS _ ih =>
    rcases z4y hS with ⟨n1,_,hn1⟩
    rcases ih with ⟨n2,hn2⟩
    exact ⟨n1 + n2,zMt holdout_0001_tm _ _ _ n1 n2 hn1 hn2⟩
def z4A : CCfg := ⟨0,0,[],[]⟩
def z4B : CCfg := ⟨0,1,[0,1,1,0,0,1,1,0,0,1,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,0,1,1,0,0,0,0,0,0,1,1,0,0,1],[0,1]⟩
set_option maxRecDepth 500000 in
theorem z4C : zCm z4A 969 = some z4B := by decide
theorem z4D :
    (init []) [holdout_0001_tm]⊢* zCf (evalWords z3L default) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = z04 z4A := rfl
  have h2 : z04 z4B = zCf (evalWords z3L default) := by
    unfold z04 z4B zCf zCL lh w_pre z3L
    simp only [List.replicate,List.cons_append,List.nil_append,evalWords,wordsToBits,t,d1,d0,one,append_cons,append_nil,z00]
    rfl
  have hPlus : (z04 z4A) [holdout_0001_tm]⊢⁺ (z04 z4B) :=
    zTc (by decide) z4C
  rw [<- h0,h2] at hPlus
  rcases hPlus with ⟨n,_,hn⟩
  exact ⟨n,hn⟩
theorem zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep holdout_0001_tm c (j + d) = some c') :
    (multiStep holdout_0001_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep holdout_0001_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
theorem z4E (m : Nat) :
    ∃ N ≥ m,∃ p q w,
      multiStep holdout_0001_tm (init []) N = some (zCf (evalWords w default)) /\
      AggState z3p p q w := by
  induction m with
  | zero =>
    rcases z4d with ⟨v0,hRounds,hGood0⟩
    rcases z4D with ⟨k1,hk1⟩
    rcases z4z hRounds with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,16,18,v0,
      zMt holdout_0001_tm _ _ _ k1 k2 hk1 hk2,hGood0⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,p,q,w,h_ms,h_good⟩
    rcases aggState_step_of_copyTwelve z3p z3q z3y z3x p q w h_good
      with ⟨w',hStep,h_good'⟩
    rcases z4y hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,1 + p,1 + q,w',
      zMt holdout_0001_tm _ _ _ N k h_ms h_step_k,h_good'⟩
theorem holdout_0001_nonhalt :
    IsDoesNotHalt holdout_0001_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases z4E (n + 1) with ⟨N,hN,_,_,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs,hn] at h_some
  exact h_some



theorem is_does_not_halt : IsNotHalt target_tm := holdout_0001_nonhalt

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LCHHH
