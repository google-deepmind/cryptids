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

namespace BusyBeaver.M_1RBHHH_1LC0LF_1RD1LB_1RE0RD_1LB0RB_1LB0LA


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RBHHH_1LC0LF_1RD1LB_1RE0RD_1LB0RB_1LB0LA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
open Counter
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000
variable {α β γ : Type*} [Inhabited α] [Inhabited β] [Inhabited γ]

namespace Solution
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

set_option linter.deprecated false
set_option linter.dupNamespace false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

variable {Γ₀ Λ₀ α β γ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
set_option maxHeartbeats 2000000
@[simp] theorem zMz (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0=some config:=rfl
@[simp] theorem zMo (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1=step M config:=rfl
@[simp] theorem zMs (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : Nat) :
    multiStep M config (n + 1)=Option.bind (multiStep M config n) (step M):= by
  rw [multiStep,Function.iterate_succ',Function.comp_apply,multiStep]
@[simp] theorem z00 : (0 : Fin 2) >> default=default:= by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] theorem zDh : (default : HalfTape).head=0:=rfl
@[simp] theorem zDt : (default : HalfTape).tail=default:=rfl
@[simp] theorem append_nil (s : HalfTape) : ([] : BitWord) +> s=s:=rfl
@[simp] theorem append_cons (a : Fin 2) (l : BitWord) (s : HalfTape) :
    (a :: l) +> s=a >> (l +> s):=rfl
@[simp] theorem append_assoc (l1 l2 : BitWord) (s : HalfTape) :
    (l1 ++ l2) +> s=l1 +> (l2 +> s):= by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append,append_cons,ih]
theorem zSm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂:= by simp [h]
theorem z01 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂:=⟨1,by decide,zSm tm c₁ c₂ h⟩
theorem zMa {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m)=(multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m):= by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ,zMs,ih,Option.bind_assoc]
    simp_rw [zMs]
theorem zMt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c3 : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c3) :
    c₁ [tm]⊢^{n+m} c3:= by
  rw [zMa,h₁]; simp [h₂]
theorem zPs {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂:= by obtain ⟨n,_,hn⟩:=h; exact ⟨n,hn⟩
theorem zPt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c3) : c₁ [tm]⊢⁺ c3:= by
  obtain ⟨n,n_pos,hn⟩:=h₁; obtain ⟨m,m_pos,hm⟩:=h₂
  exact ⟨n + m,by omega,zMt tm c₁ c₂ c3 n m hn hm⟩
theorem z02 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3:= by
  obtain ⟨n,n_pos,hn⟩:=h₁; obtain ⟨m,hm⟩:=h₂
  exact ⟨n + m,lt_of_lt_of_le n_pos (Nat.le_add_right n m),zMt tm c₁ c₂ c3 n m hn hm⟩
theorem z03 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3 :=
  z02 (z01 tm c₁ c₂ h₁) h₂
macro "finish" : tactic =>
  `(tactic| exists 0 <;> rfl)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.ListBlank.head_cons,zDh]); rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,z00,zDh,zDt])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))
abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev z04 (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev z0b (c : CCfg) : Option CCfg := Counter.bstep target_tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep target_tm n c
theorem zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (z04 c1) [target_tm]⊢⁺ (z04 c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩
abbrev t : BitWord:=[1,1,0,0]
abbrev d0 : BitWord:=[0,0]
abbrev d1 : BitWord:=[1,0]
abbrev one : BitWord:=[1]
abbrev lh : HalfTape:=[1,1,0,1,0,1] +> default
abbrev w_pre : BitWord:=t
@[simp] theorem zDd : d0 +> (default : HalfTape)=default:= by
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
def zCw : Call -> BitWord
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
  | .ca => [1,1,0,1,1]
def zCR (l : HalfTape) (c : Call) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (r <{{zCs c}} (l <+ zCw c))
def zCL (l : HalfTape) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> r) {{D}}> l)
def zCf (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  zCL lh (w_pre +> r)
def z0f (c : Call) (r1 r2 : HalfTape) : Prop :=
  ∀ l,(zCR l c r1) [target_tm]⊢⁺ (zCL l r2)
inductive Side : List Call -> HalfTape -> HalfTape -> Prop where
  | nil (r : HalfTape) : Side [] r r
  | cons {c : Call} {ls : List Call} {r1 r2 r3 : HalfTape} :
      z0f c r1 r2 -> Side ls r2 r3 -> Side (c :: ls) r1 r3
def Seg (ls_in ls_out : List Call) (w1 w2 : BitWord) : Prop :=
  ∀ r1 r2,Side ls_out r1 r2 -> Side ls_in (w1 +> r1) (w2 +> r2)
@[simp] theorem z0g {α : Type*} (l : List α) : l ^ (0 : Nat)=[]:=rfl
@[simp] theorem zLp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1)=l ++ l ^ n:=rfl
@[simp] theorem zLp' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n)=l ++ l ^ n:= by
  rw [Nat.add_comm 1 n]; rfl
@[simp] theorem z0h {α : Type*} (l : List α) : l ^ (1 : Nat)=l:= by
  change l ++ []=l; exact List.append_nil l
theorem z0i {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n)=l ^ m ++ l ^ n:= by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm,zLp,zLp,ih,List.append_assoc]
theorem z0j {ls1 ls2 : List Call} {r1 r2 r3 : HalfTape}
    (h1 : Side ls1 r1 r2) (h2 : Side ls2 r2 r3) : Side (ls1 ++ ls2) r1 r3:= by
  induction h1 with
  | nil _ => exact h2
  | cons hc _ ih => exact Side.cons hc (ih h2)
theorem z0k {ls1 ls2 : List Call} {r1 r3 : HalfTape}
    (h : Side (ls1 ++ ls2) r1 r3) : ∃ r2,Side ls1 r1 r2 /\ Side ls2 r2 r3:= by
  induction ls1 generalizing r1 with
  | nil => exact ⟨r1,Side.nil r1,h⟩
  | cons c ls1 ih =>
    rcases h with _ | ⟨hc,hrest⟩
    rcases ih hrest with ⟨r2,h1,h2⟩
    exact ⟨r2,Side.cons hc h1,h2⟩
theorem z0l (w : BitWord) : Seg [] [] w w:= by
  intro r1 r2 h; cases h; exact Side.nil (w +> r1)
theorem z0m (ls : List Call) : Seg ls ls [] []:= by
  intro r1 r2 h; exact h
theorem zSc {ls1 ls2 : List Call} {w1 w2 : BitWord} {r1 r2 : HalfTape}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
    Side ls1 (w1 +> r1) (w2 +> r2) :=
  h1 r1 r2 h2
theorem zSg {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : BitWord}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3:= by
  intro r1 r3 h
  rcases z0k h with ⟨r2,ha,hb⟩
  exact z0j (h1 r1 r2 ha) (h2 r2 r3 hb)
theorem zS0 {ls1 ls2 ls3 : List Call} {w1 w2 v1 v2 : BitWord}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls2 ls3 v1 v2) :
    Seg ls1 ls3 (w1 ++ v1) (w2 ++ v2):= by
  intro r1 r2 h
  rw [append_assoc,append_assoc]
  exact h1 (v1 +> r1) (v2 +> r2) (h2 r1 r2 h)
theorem zS4 {c : Call} {w1 w2 : BitWord}
    (h1 : ∀ l r,(zCR l c (w1 +> r)) [target_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c] [] w1 w2:= by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)
theorem zS2 {c_in c_out : Call} {w1 w2 mid : BitWord}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [target_tm]⊢⁺ (zCR (mid +> l) c_out r))
    (h2 : ∀ l r,(zCL (mid +> l) r) [target_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c_out] w1 w2:= by
  intro r1 r2 h
  rcases h with _ | ⟨hc1,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1) (zPt (hc1 (mid +> l)) (h2 l r2))
theorem zS5 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : BitWord}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [target_tm]⊢⁺ (zCR (mid1 +> l) c1 r))
    (h2 : ∀ l r,(zCL (mid1 +> l) r) [target_tm]⊢⁺ (zCR (mid2 +> l) c2 r))
    (h3 : ∀ l r,(zCL (mid2 +> l) r) [target_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c1,c2] w1 w2:= by
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
  zS2 (mid:=[1,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0o : Seg [.cj] [.ch] t (t ++ one) :=
  zS2 (mid:=[1,1,0,1,1])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0p : Seg [.ch] [.cj] (t ++ [0]) t :=
  zS2 (mid:=[1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH2 : Seg [.ch] [.cj,.ch] (t ++ one) t :=
  zS5 (mid1:=[1,0,1,1]) (mid2:=[1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0q : Seg [.ch] [.ch,.ch] t t :=
  zS5 (mid1:=[1,0,1,1]) (mid2:=[1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0r : Seg [.cp] [] (d1 ++ d0) (t ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d1 d0 t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0s : Seg [.cj] [.cj] (d1 ++ d0) t :=
  zS2 (mid:=[1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1 d0; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0t : Seg [.cp] [.cp] (d1 ++ d1) t :=
  zS2 (mid:=[1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0u : Seg [.cj] [.cp,.ch] (d1 ++ d1) t :=
  zS5 (mid1:=[1,0,1,1]) (mid2:=[1,0,1,0])
    (fun l r => by unfold zCR zCw zCs d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
theorem z0v : Seg [.cj] [] d0 (d0 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH1 : Seg [.ch] [] (d0 ++ one) (d1 ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem zH3 : Seg [.ch] [.cj] (d1 ++ one) d0 :=
  zS2 (mid:=[1,1])
    (fun l r => by unfold zCR zCw zCs d1 one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
theorem z0w : Seg [.cj] [.cp] d1 d0 :=
  zS2 (mid:=[1,1])
    (fun l r => by unfold zCR zCw zCs d1; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
theorem zH0 : Seg [.ch] [] d0 d1 :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 d1; simp only [append_cons,append_nil]; execute)
theorem zH4 : Seg [.ch] [.ch] d1 d0 :=
  zS2 (mid:=[1,1])
    (fun l r => by unfold zCR zCw zCs d1; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
theorem H_T (n : Nat) : Seg ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t:= by
  induction n with
  | zero => exact z0l t
  | succ n ih =>
    have h_eq : (n + 1) * 2=2 + n * 2:= by omega
    rw [zLp,h_eq,z0i]
    exact zSg z0q ih
theorem zSa {w2 : BitWord} (hw : Seg [.ch,.ch] [.ch] w2 w2) (n : Nat) :
    Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) w2 w2:= by
  induction n with
  | zero => exact z0l w2
  | succ n ih =>
    have h_eq : (n + 1) * 2=2 + n * 2:= by omega
    rw [h_eq,z0i,zLp]
    exact zSg hw ih
theorem z0x : Seg [.ch,.ch] [.ch] d0 d0 :=
  zSg zH0 zH4
theorem z0y : Seg [.ch,.ch] [.ch] d1 d1 :=
  zSg zH4 zH0
theorem z0z (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d0 d0 :=
  zSa z0x n
theorem z0A (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ n) d0 d1:= by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg zH0 (zSa z0y n)
theorem z0B (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d1 d1 :=
  zSa z0y n
theorem z0C (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ (1 + n)) d1 d0:= by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg zH4 (zSa z0x n)
theorem z0D (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (n * 2)) t t:= by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0n z0p) (H_T n)
theorem z0E (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (1 + n * 2)) t t:= by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0o zH2) (H_T n)
theorem z0F (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t:= by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0r zH2) (H_T n)
theorem z0G (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0s (H_T n)
theorem z0H (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0t (H_T n)
theorem z0I (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t:= by
  simpa only [zLp',List.cons_append,List.nil_append] using zSg z0u (H_T n)
theorem z0J (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0:= by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0v (zSg zH1 zH3)
  have h1:=zSg h0 (zSa z0x n)
  have heq : (2 + n * 2)=1 + (1 + n * 2):= by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
theorem z0K (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0w (zSa z0x n)
theorem z0L : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0v zH1
theorem z0M (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1:= by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0v (zSg zH1 (zSg zH3 zH0))
  have h1:=zSg h0 (zSa z0y n)
  have heq : (3 + n * 2)=1 + (1 + (1 + n * 2)):= by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
theorem z0N (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1:= by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1:=zSg z0w zH0
  have h1:=zSg h0 (zSa z0y n)
  simpa only [zLp',List.cons_append,List.nil_append] using h1
theorem z0O : Side [.ch] default (d1 +> default):= by
  refine Side.cons (fun l => ?_) (Side.nil _)
  unfold zCR zCL zCw zCs d1
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
theorem z0P {r1 r3 : HalfTape} (h : Side [.ch,.ch] r1 r3) :
    Side [.ca] r1 (t +> r3):= by
  rcases h with _ | ⟨hc1,hrest⟩
  rcases hrest with _ | ⟨hc2,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  have h0 : zCR l .ca r1=zCR ([1,0,1,1] +> l) .ch r1:= by
    unfold zCR zCw zCs
    simp only [List.cons_append,List.nil_append,append_cons,append_nil]
  have h2 : ∀ r,(zCL ([1,0,1,1] +> l) r) [target_tm]⊢⁺ (zCR ([1,0,1,0] +> l) .ch r):= by
    intro r; unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute
  have h3 : (zCL ([1,0,1,0] +> l) r3) [target_tm]⊢⁺ (zCL l (t +> r3)):= by
    unfold zCL t; simp only [append_cons,append_nil]; execute
  rw [h0]
  exact zPt (hc1 ([1,0,1,1] +> l))
    (zPt (h2 _) (zPt (hc2 ([1,0,1,0] +> l)) h3))
theorem z0Q : Seg [.cj,.ca] ([.ch,.cj] ++ [.ch] ^ 3) w_pre (w_pre ++ t):= by
  intro r1 r3 h
  rcases h with _ | ⟨hch,hrest⟩
  have h1:=z0o r1 _ (Side.cons hch (Side.nil _))
  rcases h1 with _ | ⟨hcj,hnil⟩
  cases hnil
  have h2:=(zSg zH2 z0q) _ r3 hrest
  have h3:=z0P h2
  rw [<- append_assoc t t r3] at h3
  exact Side.cons hcj h3
theorem z0R (r : HalfTape) :
    (zCL lh r) [target_tm]⊢⁺ (zCR ([1,0,1,0,1,0,1] +> default) .cj r):= by
  unfold zCL zCR lh zCw zCs
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
theorem z0S (r : HalfTape) :
    (zCL ([1,0,1,0,1,0,1] +> default) r) [target_tm]⊢⁺ (zCR lh .ca r):= by
  unfold zCL zCR lh zCw zCs
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
open WordCalculus
open WordCalculus.Word
local notation "WordList" => List Word
def z3t : WordList :=
  [Q,V,Q,Q,Q,V,V,V,Q,V,V,V,Q,V,V,V,Q,V]
def z3u : WordList :=
  [K,V,K,K,K,V,V,V,K,V,V,V,K,V,V,V,K,V]
theorem z3w (n : Nat) :
    Copy (31 + 32 * n) (260 + 256 * n) z3t z3u (809 + 512 * n) (2908 + 4096 * n):= by
  unfold z3t z3u
  refine copy_step_d11 (n':=16 + 16 * n) (k':=128 + 128 * n) (m:=64 + 64 * n) (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n':=33 + 32 * n) (k':=252 + 256 * n) (m:=125 + 128 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n':=17 + 16 * n) (k':=124 + 128 * n) (m:=62 + 64 * n) (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n':=9 + 8 * n) (k':=60 + 64 * n) (m:=30 + 32 * n) (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n':=5 + 4 * n) (k':=28 + 32 * n) (m:=14 + 16 * n) (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n':=11 + 8 * n) (k':=52 + 64 * n) (m:=25 + 32 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n':=23 + 16 * n) (k':=100 + 128 * n) (m:=49 + 64 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n':=47 + 32 * n) (k':=196 + 256 * n) (m:=97 + 128 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n':=24 + 16 * n) (k':=96 + 128 * n) (m:=48 + 64 * n) (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n':=49 + 32 * n) (k':=188 + 256 * n) (m:=93 + 128 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n':=99 + 64 * n) (k':=372 + 512 * n) (m:=185 + 256 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n':=199 + 128 * n) (k':=740 + 1024 * n) (m:=369 + 512 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n':=100 + 64 * n) (k':=368 + 512 * n) (m:=184 + 256 * n) (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n':=201 + 128 * n) (k':=732 + 1024 * n) (m:=365 + 512 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n':=403 + 256 * n) (k':=1460 + 2048 * n) (m:=729 + 1024 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n':=807 + 512 * n) (k':=2916 + 4096 * n) (m:=1457 + 2048 * n) (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n':=404 + 256 * n) (k':=1456 + 2048 * n) (m:=728 + 1024 * n) (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n':=809 + 512 * n) (k':=2908 + 4096 * n) (m:=1453 + 2048 * n) (by omega) (by omega) (by omega) ?_
  exact Copy.nil _ _
theorem z3x (q : Nat) (hQ : 5 <= q) :
    CopyTwelve (List.replicate q V ++ z3t) (List.replicate q V ++ z3u):= by
  have hPow : 2 ^ q=32 * 2 ^ (q - 5):= by
    have heq : q=5 + (q - 5):= by omega
    conv_lhs => rw [heq,Nat.pow_add]
  have hPos:=pow_two_pos (q - 5)
  have hTs:=copy_replicate_V q 0 8
  have hBase:=z3w (2 ^ (q - 5) - 1)
  have h1 : (1 + 0) * 2 ^ q - 1=31 + 32 * (2 ^ (q - 5) - 1):= by omega
  have h2 : 4 + 8 * 2 ^ q=260 + 256 * (2 ^ (q - 5) - 1):= by omega
  rw [h1,h2] at hTs
  exact ⟨_,_,copy_append hTs hBase⟩
theorem z3y : isSafePrefix z3u=true:= by decide +kernel
def z3Q : WordList :=
  [Q,K,Q,K,Q,K,Q,Q,K] ++ List.replicate 15 Q
def z3R : WordList :=
  List.replicate 6 V ++ [Q,V] ++ List.replicate 3 Q ++ List.replicate 3 V ++ [Q] ++
  List.replicate 3 V ++ [K] ++ List.replicate 3 V ++ [Q,V,K,K] ++ List.replicate 4 Q ++ [K,Q,Q]
def u_5 : WordList:=[V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,Q,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,Q,Q,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,Q,V,V,Q,V,V,V,Q,V,K,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,K,V,V,V,V,V,K,K,K,Q,Q,Q,K,Q,K,K,K,Q,Q,Q,K,K,K,Q,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q]
def z3S : WordList:=[V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,Q,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,Q,Q,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,Q,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,V,Q,Q,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,Q,Q,Q,V,V,V,Q,Q,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,Q,V,V,V,Q,Q,K,V,Q,V,V,Q,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,V,V,Q,V,K,Q,V,K,Q,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,K,V,V,K,K,V,V,K,K,Q,Q,V,V,V,K,Q,K,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,K,V,V,K,V,Q,Q,V,Q,Q,V,V,V,V,Q,V,V,V,K,V,Q,V,V,V,V,V,V,K,K,K,K,K,K,Q,K,Q,Q,K,Q,Q,K,K,K,Q,K,Q,K,K,K,Q,K,K,Q,K,K,Q,Q,K,Q,K,Q,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,Q,K,K,Q,K,K,K,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def z3T : WordList:=[V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,Q,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,Q,Q,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,Q,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,V,Q,Q,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,Q,Q,Q,V,V,V,Q,Q,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,Q,Q,K,V,V,Q,V,V,Q,K,V,Q,V,K,V,Q,V,Q,K,V,V,V,Q,V,K,K,V,Q,V,K,V,V,V,V,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,Q,Q,V,Q,V,V,V,V,Q,V,V,Q,V,K,Q,V,K,Q,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,Q,Q,V,V,V,V,V,K,Q,K,K,Q,Q,K,V,K,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,K,V,V,V,V,K,V,Q,V,V,V,V,V,Q,V,V,V,K,V,V,Q,K,V,V,V,Q,V,V,K,Q,V,V,K,V,V,V,V,Q,Q,V,V,V,Q,V,V,V,V,V,V,K,V,V,K,V,Q,Q,V,Q,Q,V,V,V,V,Q,V,V,V,K,V,Q,V,V,V,V,V,V,V,K,K,K,K,K,K,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,K,K,K,Q,Q,Q,Q,K,Q,K,Q,K,K,Q,Q,K,K,Q,K,K,Q,K,K,Q,Q,K,Q,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,K,K,K,Q,K,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,K,K,K,K,K,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,K,Q,K,K,K,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,K,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def z3U : WordList:=[V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,Q,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,Q,Q,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,Q,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,V,Q,Q,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,Q,Q,Q,V,V,V,Q,Q,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,Q,V,Q,V,Q,V,K,V,Q,Q,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,Q,Q,V,K,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,Q,Q,V,V,V,V,V,V,K,K,V,K,V,Q,V,K,Q,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,K,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,K,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,K,Q,V,K,Q,V,V,V,V,Q,V,V,V,Q,V,K,V,V,V,V,V,V,V,Q,V,V,V,V,Q,K,K,V,Q,Q,Q,V,V,K,V,V,Q,Q,V,K,V,V,V,Q,V,K,V,Q,V,Q,V,Q,V,V,K,Q,Q,K,K,Q,Q,K,Q,V,V,Q,V,K,V,Q,V,V,K,V,V,V,K,V,V,V,K,K,K,Q,Q,K,Q,Q,K,Q,K,K,V,V,V,V,K,V,V,V,Q,V,V,V,Q,V,K,Q,V,K,V,V,Q,K,V,V,V,Q,V,V,K,Q,V,V,K,V,V,V,V,Q,Q,V,V,V,Q,V,V,V,V,V,V,K,V,V,K,V,Q,Q,V,Q,Q,V,V,V,V,Q,V,V,V,K,V,V,V,V,V,V,V,V,V,K,K,K,K,K,K,K,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,Q,Q,K,K,K,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,K,K,Q,K,Q,K,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,K,Q,K,K,K,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,K,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def z3V : WordList:=[V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,Q,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,Q,Q,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,Q,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,Q,V,Q,V,Q,V,V,Q,V,V,Q,Q,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,Q,Q,Q,V,V,V,Q,Q,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,V,V,Q,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,Q,V,K,V,Q,V,Q,V,K,K,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,Q,Q,V,K,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,Q,Q,V,V,V,V,V,V,V,V,K,V,K,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,Q,Q,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,Q,Q,K,V,Q,K,Q,V,V,Q,V,V,Q,K,V,K,V,V,V,Q,V,Q,V,K,V,Q,V,Q,V,V,V,V,K,Q,Q,V,V,V,Q,V,Q,V,K,V,V,Q,V,V,V,Q,V,V,V,V,V,V,K,V,Q,Q,K,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,K,V,V,Q,K,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,K,Q,V,K,Q,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,Q,Q,V,Q,Q,K,V,V,K,V,K,V,K,V,Q,Q,Q,V,Q,Q,K,V,K,K,V,V,Q,Q,V,V,Q,V,K,V,V,Q,K,V,K,V,V,V,V,K,V,Q,V,V,V,V,Q,Q,K,V,V,Q,V,Q,V,Q,K,V,V,V,V,Q,K,V,V,V,Q,K,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,Q,V,V,V,Q,V,K,Q,V,K,V,V,Q,K,V,V,V,Q,V,V,K,Q,V,V,K,V,V,V,V,Q,Q,V,V,V,Q,V,V,V,V,V,V,K,V,V,K,V,Q,Q,V,Q,Q,V,V,V,V,Q,V,V,V,K,V,Q,V,V,V,V,V,V,V,V,K,K,K,K,K,K,K,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,K,K,K,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,K,K,K,Q,Q,K,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,Q,K,K,K,Q,K,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,K,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,Q,K,K,Q,K,K,K,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,K,Q,K,K,K,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,K,K,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
theorem z3W : EntrySpec 20 z3t z3Q 9000 := entrySpec_of_checkEntrySpec (by decide +kernel)
set_option maxRecDepth 4000000 in
theorem z3X : evalLowerRounds 5 z3R=some u_5:= by decide +kernel
set_option maxRecDepth 4000000 in
theorem z3Y : evalLowerRounds 5 u_5=some z3S:= by decide +kernel
set_option maxRecDepth 4000000 in
theorem z3Z : evalLowerRounds 2 z3S=some z3T:= by decide +kernel
set_option maxRecDepth 4000000 in
theorem z40 : evalLowerRounds 1 z3T=some z3U:= by decide +kernel
set_option maxRecDepth 4000000 in
theorem z41 : evalLowerRounds 1 z3U=some z3V:= by decide +kernel
set_option maxRecDepth 4000000 in
theorem z42 : checkEntryTwo 20 z3t z3Q 9000 (z3V ++ [Q]) 1852706365173628188237142867651181648556690957234892077209186308856837946639875 587146083964752735467109177766019616504586562932017459858360926881414728156959077196424392135657539255289087=true:= by decide +kernel
theorem z43 : ∃ v,LowerRounds z3R v /\ AggState z3t 16 20 (v ++ [Q]):= by
  refine ⟨z3V,?_,good_of_checkEntryTwo 20 z3t z3Q 9000 (z3V ++ [Q]) 1852706365173628188237142867651181648556690957234892077209186308856837946639875 587146083964752735467109177766019616504586562932017459858360926881414728156959077196424392135657539255289087 z3W z42⟩
  exact lowerRounds_trans (evalLowerRounds_sound 5 z3R u_5 z3X)
    (lowerRounds_trans (evalLowerRounds_sound 5 u_5 z3S z3Y)
      (lowerRounds_trans (evalLowerRounds_sound 2 z3S z3T z3Z)
        (lowerRounds_trans (evalLowerRounds_sound 1 z3T z3U z40)
          (evalLowerRounds_sound 1 z3U z3V z41))))
inductive Num : Nat -> BitWord -> List Call -> Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)
theorem z44 {k : Nat} (hK : 0 < k) : ∃ hs,Num k [] hs:= by
  rcases even_or_odd_mul_two k with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · cases a with
    | zero => omega
    | succ a =>
      have heq : (a + 1) * 2=2 + a * 2:= by omega
      rw [heq]; exact ⟨[.cj] ++ [.ch] ^ a,Num.even a⟩
  · exact ⟨[.cp] ++ [.ch] ^ a,Num.odd a⟩
theorem z45 {k : Nat} {hs hs' : List Call} (h1 : Num k [] hs) (h2 : Num k [] hs') :
    hs=hs':= by
  cases h1 with
  | @odd n =>
    generalize hk : 1 + n * 2=k0 at h2
    cases h2 with
    | @odd m =>
      have hnm : n=m:= by omega
      subst hnm; rfl
    | even _ => omega
  | @even n =>
    generalize hk : 2 + n * 2=k0 at h2
    cases h2 with
    | odd _ => omega
    | @even m =>
      have hnm : n=m:= by omega
      subst hnm; rfl
def z46 (k : Nat) (r r' : HalfTape) : Prop :=
  ∀ w hs,Num k w hs -> Side hs (w +> r) r'
theorem z47 {r r' : HalfTape} (h : z46 0 r r') :
    r'=one +> r:= by
  have h0:=h one [] Num.zero
  cases h0
  rfl
theorem z48 {n : Nat} {r r' : HalfTape}
    (hI : z46 (n * 2) r r') : z46 (2 + n * 4) (d0 +> r) (d0 +> r'):= by
  intro w hs hN
  generalize hk : 2 + n * 4=k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m=n * 2:= by omega
    subst hm
    cases n with
    | zero =>
      have hr':=z47 hI
      subst hr'
      rw [<- append_assoc d0 one r]
      exact zSc z0v (Side.nil r)
    | succ n =>
      have heq : (n + 1) * 2=2 + n * 2:= by omega
      rw [heq]
      refine zSc (z0J n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n):= by
        rw [heq]; exact Num.even n
      simpa using hI [] _ hN2
theorem z49 {n : Nat} {r r' : HalfTape}
    (hI : z46 (n * 2) r r') : z46 (4 + n * 4) (d0 +> r) (d1 +> r'):= by
  intro w hs hN
  generalize hk : 4 + n * 4=k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m=1 + n * 2:= by omega
    subst hm
    cases n with
    | zero =>
      have hr':=z47 hI
      subst hr'
      rw [<- append_assoc d1 one r]
      exact zSc z0L (Side.nil r)
    | succ n =>
      have heq : 1 + (n + 1) * 2=3 + n * 2:= by omega
      rw [heq]
      refine zSc (z0M n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n):= by
        have heq2 : (n + 1) * 2=2 + n * 2:= by omega
        rw [heq2]; exact Num.even n
      simpa using hI [] _ hN2
theorem z4a {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hZ : A=0) :
    evalWords da default=default:= by
  induction hD with
  | nil => rfl
  | @zero A H u _ ih =>
    have hA0 : A=0:= by omega
    dsimp only [evalWords]
    rw [ih hA0,zDd]
  | one _ => omega
theorem z4b {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hPos : 0 < A) :
    z46 ((A - 1) * 2) default (evalWords da default):= by
  induction hD with
  | nil => omega
  | @zero A H u _ ih =>
    have hA_pos : 0 < A:= by omega
    have hIH:=ih hA_pos
    have hs:=z48 hIH
    rw [zDd] at hs
    have heq : (A * 2 - 1) * 2=2 + (A - 1) * 4:= by omega
    dsimp [evalWords]
    rwa [heq]
  | @one A H u hDu ih =>
    cases A with
    | zero =>
      change z46 0 default (d1 +> evalWords u default)
      rw [z4a hDu rfl]
      intro w hs hN
      generalize hk : 0=k0 at hN
      cases hN with
      | zero =>
        have hd : d1 +> (default : HalfTape)=one +> default:= by simp [d1,one]
        rw [hd]; exact Side.nil (one +> default)
      | odd _ => omega
      | even _ => omega
    | succ A =>
      have hA_pos : 0 < A + 1:= by omega
      have hIH:=ih hA_pos
      have heq_in : (A + 1 - 1) * 2=A * 2:= by omega
      rw [heq_in] at hIH
      have hs:=z49 hIH
      rw [zDd] at hs
      have heq : (1 + (A + 1) * 2 - 1) * 2=4 + A * 4:= by omega
      dsimp [evalWords]
      rwa [heq]
theorem zEd {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (hI : WordEffect n u b v) :
    ∀ {A H : Nat},DigitVal A H v -> Seg ([Call.ch] ^ n) ([Call.ch] ^ b) (wordsToBits u) (wordsToBits v):= by
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
theorem z4c {n : Nat} {hs hs' : List Call}
    (hI : Num (3 + n) [] hs) (hJ : Num (2 + n * 2) [] hs') :
    Seg hs ([Call.ch] ++ hs') t t:= by
  generalize hk1 : 3 + n=k1 at hI
  generalize hk2 : 2 + n * 2=k2 at hJ
  cases hI with
  | @odd m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases m with
      | zero => omega
      | succ m =>
        have h1m : m + 1=1 + m:= by omega
        have hq : q=m * 2:= by omega
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
        have h1m : m + 1=1 + m:= by omega
        have hq : q=1 + m * 2:= by omega
        subst hq
        rw [h1m]
        exact z0E m
theorem z4d {n : Nat} {hs hs' : List Call}
    (hI : Num (1 + n) [] hs) (hJ : Num (n * 2) [] hs') :
    Seg hs hs' (d1 ++ d0) t:= by
  generalize hk1 : 1 + n=k1 at hI
  generalize hk2 : n * 2=k2 at hJ
  cases hI with
  | @odd m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases m with
      | zero => omega
      | succ m =>
        have h1m : m + 1=1 + m:= by omega
        have hq : q=1 + m * 2:= by omega
        subst hq
        rw [h1m]
        exact z0F m
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      have hq : q=m * 2:= by omega
      subst hq
      exact z0G m
theorem z4e {n : Nat} {hs hs' : List Call}
    (hI : Num (1 + n) [] hs) (hJ : Num (1 + n * 2) [] hs') :
    Seg hs hs' (d1 ++ d1) t:= by
  generalize hk1 : 1 + n=k1 at hI
  generalize hk2 : 1 + n * 2=k2 at hJ
  cases hI with
  | @odd m =>
    cases hJ with
    | @odd q =>
      have hq : q=m * 2:= by omega
      subst hq
      exact z0H m
    | even _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hq : q=1 + m * 2:= by omega
      subst hq
      exact z0I m
    | even _ => omega
theorem z4f {n : Nat} {hs hs' : List Call}
    (hI : Num (2 + n * 4) [] hs) (hJ : Num (n * 2) [] hs') :
    Seg hs hs' d0 d0:= by
  generalize hk1 : 2 + n * 4=k1 at hI
  generalize hk2 : n * 2=k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases n with
      | zero => omega
      | succ n =>
        have hm : m=2 + q * 2:= by omega
        subst hm
        exact z0J q
theorem z4g {n : Nat} {hs hs' : List Call}
    (hI : Num (2 + n * 4) [] hs) (hJ : Num (1 + n * 2) [] hs') :
    Seg hs hs' d1 d0:= by
  generalize hk1 : 2 + n * 4=k1 at hI
  generalize hk2 : 1 + n * 2=k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hm : m=q * 2:= by omega
      subst hm
      exact z0K q
    | even _ => omega
theorem z4h {n : Nat} {hs hs' : List Call}
    (hI : Num (4 + n * 4) [] hs) (hJ : Num (n * 2) [] hs') :
    Seg hs hs' d0 d1:= by
  generalize hk1 : 4 + n * 4=k1 at hI
  generalize hk2 : n * 2=k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases n with
      | zero => omega
      | succ n =>
        have hm : m=3 + q * 2:= by omega
        subst hm
        exact z0M q
theorem z4i {n : Nat} {hs hs' : List Call}
    (hI : Num (4 + n * 4) [] hs) (hJ : Num (1 + n * 2) [] hs') :
    Seg hs hs' d1 d1:= by
  generalize hk1 : 4 + n * 4=k1 at hI
  generalize hk2 : 1 + n * 2=k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hm : m=1 + q * 2:= by omega
      subst hm
      exact z0N q
    | even _ => omega
theorem z4j {k : Nat} {v : WordList} {k' : Nat} {w : WordList} {a b : ℚ}
    (hI : PhaseScan k v k' w a b) :
    ∀ {u : WordList} {n n' : Nat} {hs hs' : List Call},
      WordEffect n u n' v -> Num k [] hs -> Num k' [] hs' ->
      Seg (([Call.ch] ^ n) ++ hs) (([Call.ch] ^ n') ++ hs') (wordsToBits u) (wordsToBits w):= by
  induction hI with
  | nil k =>
    intro u n n' hs hs' hE hN hN'
    cases hE
    rw [z45 hN hN']
    exact z0m (([Call.ch] ^ n) ++ hs')
  | @T m _ _ _ _ _ _ ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    cases hE with
    | T hSub =>
      rcases z44 (by omega : 0 < 2 + m * 2) with ⟨hs0,hN0⟩
      have hIH:=ih hSub hN0 hN'
      have hStep:=zSg (H_T n0) (z4c hN hN0)
      have heq : ([Call.ch] ^ (n0 * 2)) ++ ([Call.ch] ++ hs0)=([Call.ch] ^ (1 + n0 * 2)) ++ hs0:= by
        have h1 : 1 + n0 * 2=n0 * 2 + 1:= by omega
        rw [h1,z0i,z0h,List.append_assoc]
      rw [heq] at hStep
      exact zS0 hStep hIH
  | @pair0 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q,K] ++ u) at hE
    rcases wordEffect_split_output [Q,K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2:=phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases z44 hPos with ⟨hs0,hN0⟩
    have hD10 : DigitVal 1 2 [Q,K]:=DigitVal.one (DigitVal.zero DigitVal.nil)
    have hStep:=zSg (zEd hL hD10) (z4d hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @pair1 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q,Q] ++ u) at hE
    rcases wordEffect_split_output [Q,Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z44 (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD11 : DigitVal 3 2 [Q,Q]:=DigitVal.one (DigitVal.one DigitVal.nil)
    have hStep:=zSg (zEd hL hD11) (z4e hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short00 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([K] ++ u) at hE
    rcases wordEffect_split_output [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2:=phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases z44 hPos with ⟨hs0,hN0⟩
    have hD0 : DigitVal 0 1 [K]:=DigitVal.zero DigitVal.nil
    have hStep:=zSg (zEd hL hD0) (z4f hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short01 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q] ++ u) at hE
    rcases wordEffect_split_output [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z44 (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : DigitVal 1 1 [Q]:=DigitVal.one DigitVal.nil
    have hStep:=zSg (zEd hL hD1) (z4g hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short10 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([K] ++ u) at hE
    rcases wordEffect_split_output [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2:=phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases z44 hPos with ⟨hs0,hN0⟩
    have hD0 : DigitVal 0 1 [K]:=DigitVal.zero DigitVal.nil
    have hStep:=zSg (zEd hL hD0) (z4h hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short11 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q] ++ u) at hE
    rcases wordEffect_split_output [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z44 (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : DigitVal 1 1 [Q]:=DigitVal.one DigitVal.nil
    have hStep:=zSg (zEd hL hD1) (z4i hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
theorem z4k {n : Nat} {r r' : HalfTape}
    (hI : z46 (n * 2) r r') : z46 (1 + n) (d1 +> (d0 +> r)) (t +> r'):= by
  intro w hs hN
  generalize hk : 1 + n=k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil,<- append_assoc d1 d0 r]
    cases m with
    | zero =>
      have hn0 : n * 2=0:= by omega
      rw [hn0] at hI
      have hr':=z47 hI
      subst hr'
      rw [<- append_assoc t one r]
      exact zSc z0r (Side.nil r)
    | succ m =>
      have h1m : m + 1=1 + m:= by omega
      rw [h1m]
      refine zSc (z0F m) ?_
      have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)):= by
        have hm : n * 2=2 + (1 + m * 2) * 2:= by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil,<- append_assoc d1 d0 r]
    refine zSc (z0G m) ?_
    have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (m * 2)):= by
      have hm : n * 2=2 + (m * 2) * 2:= by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2
theorem z4l (padding : Nat) :
    evalWords (List.replicate padding K) default=default:= by
  induction padding with
  | zero => rfl
  | succ p ih =>
    change d0 +> evalWords (List.replicate p K) default=default
    rw [ih,zDd]
theorem z4m {orig out : WordList} (hS : LowerStep orig out) :
    ∃ r,Side ([.ch,.cj] ++ [.ch] ^ 3) (evalWords orig default) r /\
      evalWords out default=t +> r:= by
  cases hS with
  | intro padding eff k v a b J da hE hI hPosK hDA =>
    have hC0 : z46 ((k - 1) * 2) default (evalWords da default) :=
      z4b hDA hPosK
    have hC1 : z46 k (d1 +> default) (evalWords (V :: da) default):= by
      have h:=z4k hC0
      have hk : 1 + (k - 1)=k:= by omega
      rwa [hk,zDd] at h
    have hN8 : Num 8 [] ([.cj] ++ [.ch] ^ 3):=Num.even 3
    rcases z44 hPosK with ⟨hs',hN'⟩
    have hSeg:=z4j hI hE hN8 hN'
    dsimp at hSeg
    have hSide:=zSc hSeg (z0j z0O (hC1 [] hs' hN'))
    rw [wordsToBits_append_tape,wordsToBits_append_tape,evalWords_append,z4l] at hSide
    refine ⟨evalWords (v ++ V :: da) default,?_,rfl⟩
    rwa [evalWords_append]
theorem z4n {r r' : HalfTape} (hI : Side ([.ch,.cj] ++ [.ch] ^ 3) r r') :
    (zCf r) [target_tm]⊢⁺ zCf (t +> r'):= by
  have hS:=zSc z0Q hI
  rcases hS with _ | ⟨hcj,hrest⟩
  rcases hrest with _ | ⟨hca,hnil⟩
  cases hnil
  have h1:=zPt (z0R (w_pre +> r)) (hcj ([1,0,1,0,1,0,1] +> default))
  have h2:=zPt (z0S _) (hca lh)
  have h3:=zPt h1 h2
  rwa [append_assoc] at h3
theorem z4o {orig out : WordList} (hS : LowerStep orig out) :
    (zCf (evalWords orig default)) [target_tm]⊢⁺ zCf (evalWords out default):= by
  rcases z4m hS with ⟨r,hSide,hEq⟩
  rw [hEq]
  exact z4n hSide
theorem z4p {u v : WordList} (hR : LowerRounds u v) :
    (zCf (evalWords u default)) [target_tm]⊢* zCf (evalWords v default):= by
  induction hR with
  | refl u => exact ⟨0,rfl⟩
  | next hS _ ih =>
    rcases z4o hS with ⟨n1,_,hn1⟩
    rcases ih with ⟨n2,hn2⟩
    exact ⟨n1 + n2,zMt target_tm _ _ _ n1 n2 hn1 hn2⟩
def z4q : CCfg:=⟨0,0,[],[]⟩
def z4r : CCfg:=⟨3,1,[0,1,1,0,0,1,1,0,0,1,0,1,1,1,0,0,1,0,1,0,0,0,1,1],[0,1,0,1,0,1,1,1,1,0,1,0,1]⟩
def z4s : CCfg:=⟨1,1,[0,1,0,0,1,1,0,0,1,0,0,1,1,0,0,1,0,1,0,1,0,1,1,0,0,1,1,0,0,0,0,1],[1,0,1,0,1,0,1,0,1,0,1,1,1,1,0,1,0,1]⟩
def z4t : CCfg:=⟨3,1,[1,0,1,0,1,1,0,0,1,1,1,0,0,0,0,0,0,0,0,1],[1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,0,1,0,1]⟩
def z4u : CCfg:=⟨3,1,[1,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,0,0,1,0,0,0,1],[1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,0,1,0,1]⟩
def z4v : CCfg:=⟨3,1,[0,0,1,1,0,0,0,0,1,0,0,0,1,0,1],[1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1]⟩
def z4w : CCfg:=⟨5,1,[0,0,1,1,0,0,0,0,1,1,0,0,0,0,1,0,1,0,1,0,1],[0,1,1,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4x : CCfg:=⟨5,0,[1,0,0,0,0,1,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,1,0,1,0,1,1],[0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,0,1,0,1]⟩
def z4y : CCfg:=⟨2,1,[1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,1,0,1,0,1,1,0,0,0,0,0,0,1],[1,1,0,1,1,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,0,1,0,1]⟩
def z4z : CCfg:=⟨4,1,[1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,1,0,1,0,1,1,0,0,0,0,1,0,0,0,1],[1,1,0,1,0,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,1,1,0,1,0,1,0,1]⟩
def z4A : CCfg:=⟨5,0,[0,0,0,1,1,0,0,1,1,0,0,0,0,1,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,1],[0,1,0,1,0,1,1,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,0,1,0,1]⟩
def z4B : CCfg:=⟨4,1,[1,0,0,1,0,1,1,0,0,1,0,1,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,1,0,1,0,1,1,0,0,0,0,0,0,1,0,0,0,1],[0,1,0,1,0,1,0,1,1,1,0,1,0,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,0,1,0,1]⟩
def z4C : CCfg:=⟨5,0,[0,1,1,0,0,1,0,1,1,0,0,1,0,1,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,1,0,1,0,1,1,0,0,0,0,0,0,0,0,1,0,1],[0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,0,1,0,1]⟩
def z4D : CCfg:=⟨2,0,[0,0,0,0,0,1,1,0,0,0,0,1,0,1,0,1,0,1],[1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,0,1,0,1]⟩
def z4E : CCfg:=⟨5,0,[0,1,0,1,1,0,0,1,1,0,0,0,0,1,0,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1],[0,1,1,1,0,1,1,1,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,1,0,1,0,1]⟩
def z4F : CCfg:=⟨1,1,[0,1,0,0,0,0,1,1,0,0,1,0,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,1,0,0,1,1,0,0,0,0,1,0,1,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,1],[1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,1,0,1,0,1]⟩
def z4G : CCfg:=⟨1,0,[1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,0,0,0,0,1,0,1],[1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4H : CCfg:=⟨1,1,[0,0,0,0,1,1,0,0,0,0,1,0,1,0,0,0,0,0,1],[1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4I : CCfg:=⟨1,0,[1,1,0,0,1,0,1,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,0,0,0,0,1,0,1,0,1,0,1],[1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4J : CCfg:=⟨1,0,[0,1,0,0,1,0,1,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,1],[1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4K : CCfg:=⟨1,1,[0,0,0,0,1,1,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1],[1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4L : CCfg:=⟨3,1,[1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1],[1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4M : CCfg:=⟨1,1,[0,0,0,0,0,0,1,0,1,0,1,0,0,0,0,0,1],[1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4N : CCfg:=⟨3,1,[0,0,0,0,0,0,1,0,1,0,1,0,0,0,1],[1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4O : CCfg:=⟨3,1,[1,0,0,0,0,0,1,0,0,0,0,0,1,0,1],[1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4P : CCfg:=⟨3,0,[0,0,1,1,0,0,1,0,1,1,0,0,0,0,1,0,0,0,0,0,0,0,1,0,1,0,1],[1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4Q : CCfg:=⟨3,1,[1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1],[1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4R : CCfg:=⟨1,1,[0,0,1,1,0,0,1,0,1,1,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1],[1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4S : CCfg:=⟨1,0,[0,0,1,1,0,0,0,0,1,0,1,0,1,0,0,0,1,0,0,0,0,0,1],[1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4T : CCfg:=⟨3,0,[0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1],[1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4U : CCfg:=⟨1,1,[0,0,1,0,1,1,0,0,0,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,1],[1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4V : CCfg:=⟨1,1,[0,1,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,1,0,1,0,1,0,0,0,1],[1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4W : CCfg:=⟨1,0,[0,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,1,0,1],[1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4X : CCfg:=⟨3,1,[1,0,0,0,1,0,0,0,0,0,1,0,0,0,1,0,1],[1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4Y : CCfg:=⟨3,0,[0,0,1,0,1,1,0,0,1,0,1,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,1,0,1],[1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,0,1,0,1]⟩
def z4Z : CCfg:=⟨3,1,[0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,0,1,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,1,0,1],[1,0,1,0,1]⟩
set_option maxRecDepth 4000000 in
theorem z50 : zCm z4q 1000=some z4r:= by decide
set_option maxRecDepth 4000000 in
theorem z51 : zCm z4r 1000=some z4s:= by decide
set_option maxRecDepth 4000000 in
theorem z52 : zCm z4s 1000=some z4t:= by decide
set_option maxRecDepth 4000000 in
theorem z53 : zCm z4t 1000=some z4u:= by decide
set_option maxRecDepth 4000000 in
theorem z54 : zCm z4u 1000=some z4v:= by decide
set_option maxRecDepth 4000000 in
theorem z55 : zCm z4v 1000=some z4w:= by decide
set_option maxRecDepth 4000000 in
theorem z56 : zCm z4w 1000=some z4x:= by decide
set_option maxRecDepth 4000000 in
theorem z57 : zCm z4x 1000=some z4y:= by decide
set_option maxRecDepth 4000000 in
theorem z58 : zCm z4y 1000=some z4z:= by decide
set_option maxRecDepth 4000000 in
theorem z59 : zCm z4z 1000=some z4A:= by decide
set_option maxRecDepth 4000000 in
theorem z5a : zCm z4A 1000=some z4B:= by decide
set_option maxRecDepth 4000000 in
theorem z5b : zCm z4B 1000=some z4C:= by decide
set_option maxRecDepth 4000000 in
theorem z5c : zCm z4C 1000=some z4D:= by decide
set_option maxRecDepth 4000000 in
theorem z5d : zCm z4D 1000=some z4E:= by decide
set_option maxRecDepth 4000000 in
theorem z5e : zCm z4E 1000=some z4F:= by decide
set_option maxRecDepth 4000000 in
theorem z5f : zCm z4F 1000=some z4G:= by decide
set_option maxRecDepth 4000000 in
theorem z5g : zCm z4G 1000=some z4H:= by decide
set_option maxRecDepth 4000000 in
theorem z5h : zCm z4H 1000=some z4I:= by decide
set_option maxRecDepth 4000000 in
theorem z5i : zCm z4I 1000=some z4J:= by decide
set_option maxRecDepth 4000000 in
theorem z5j : zCm z4J 1000=some z4K:= by decide
set_option maxRecDepth 4000000 in
theorem z5k : zCm z4K 1000=some z4L:= by decide
set_option maxRecDepth 4000000 in
theorem z5l : zCm z4L 1000=some z4M:= by decide
set_option maxRecDepth 4000000 in
theorem z5m : zCm z4M 1000=some z4N:= by decide
set_option maxRecDepth 4000000 in
theorem z5n : zCm z4N 1000=some z4O:= by decide
set_option maxRecDepth 4000000 in
theorem z5o : zCm z4O 1000=some z4P:= by decide
set_option maxRecDepth 4000000 in
theorem z5p : zCm z4P 1000=some z4Q:= by decide
set_option maxRecDepth 4000000 in
theorem z5q : zCm z4Q 1000=some z4R:= by decide
set_option maxRecDepth 4000000 in
theorem z5r : zCm z4R 1000=some z4S:= by decide
set_option maxRecDepth 4000000 in
theorem z5s : zCm z4S 1000=some z4T:= by decide
set_option maxRecDepth 4000000 in
theorem z5t : zCm z4T 1000=some z4U:= by decide
set_option maxRecDepth 4000000 in
theorem z5u : zCm z4U 1000=some z4V:= by decide
set_option maxRecDepth 4000000 in
theorem z5v : zCm z4V 1000=some z4W:= by decide
set_option maxRecDepth 4000000 in
theorem z5w : zCm z4W 1000=some z4X:= by decide
set_option maxRecDepth 4000000 in
theorem z5x : zCm z4X 1000=some z4Y:= by decide
set_option maxRecDepth 4000000 in
theorem z5y : zCm z4Y 171=some z4Z:= by decide
theorem z5z :
    (init []) [target_tm]⊢* zCf (evalWords z3R default):= by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6))=z04 z4q:=rfl
  have h2 : z04 z4Z=zCf (evalWords z3R default):= by
    unfold z04 z4Z zCf zCL lh w_pre z3R
    simp only [List.replicate,List.cons_append,List.nil_append,evalWords,wordsToBits,t,d1,d0,one,append_cons,append_nil,z00]
    rfl
  have hPlus : (z04 z4q) [target_tm]⊢⁺ (z04 z4Z) :=
    zPt (zTc (by decide) z50)
      (zPt (zTc (by decide) z51)
        (zPt (zTc (by decide) z52)
          (zPt (zTc (by decide) z53)
            (zPt (zTc (by decide) z54)
              (zPt (zTc (by decide) z55)
                (zPt (zTc (by decide) z56)
                  (zPt (zTc (by decide) z57)
                    (zPt (zTc (by decide) z58)
                      (zPt (zTc (by decide) z59)
                        (zPt (zTc (by decide) z5a)
                          (zPt (zTc (by decide) z5b)
                            (zPt (zTc (by decide) z5c)
                              (zPt (zTc (by decide) z5d)
                                (zPt (zTc (by decide) z5e)
                                  (zPt (zTc (by decide) z5f)
                                    (zPt (zTc (by decide) z5g)
                                      (zPt (zTc (by decide) z5h)
                                        (zPt (zTc (by decide) z5i)
                                          (zPt (zTc (by decide) z5j)
                                            (zPt (zTc (by decide) z5k)
                                              (zPt (zTc (by decide) z5l)
                                                (zPt (zTc (by decide) z5m)
                                                  (zPt (zTc (by decide) z5n)
                                                    (zPt (zTc (by decide) z5o)
                                                      (zPt (zTc (by decide) z5p)
                                                        (zPt (zTc (by decide) z5q)
                                                          (zPt (zTc (by decide) z5r)
                                                            (zPt (zTc (by decide) z5s)
                                                              (zPt (zTc (by decide) z5t)
                                                                (zPt (zTc (by decide) z5u)
                                                                  (zPt (zTc (by decide) z5v)
                                                                    (zPt (zTc (by decide) z5w)
                                                                      (zPt (zTc (by decide) z5x)
                                                                        (zTc (by decide) z5y))))))))))))))))))))))))))))))))))
  rw [<- h0,h2] at hPlus
  rcases hPlus with ⟨n,_,hn⟩
  exact ⟨n,hn⟩
theorem zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d)=some c') :
    (multiStep target_tm c j).isSome:= by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
theorem z5A (m : Nat) :
    ∃ N ≥ m,∃ p q w,
      multiStep target_tm (init []) N=some (zCf (evalWords w default)) /\
      AggState z3t p q (w ++ [Q]):= by
  induction m with
  | zero =>
    rcases z43 with ⟨v0,hRounds,hGood0⟩
    rcases z5z with ⟨k1,hk1⟩
    rcases z4p hRounds with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,16,20,v0,
      zMt target_tm _ _ _ k1 k2 hk1 hk2,hGood0⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,p,q,w,h_ms,h_good⟩
    rcases aggState_lowerStep_of_copyTwelve z3t z3u z3y z3x p q w h_good
      with ⟨w',hStep,h_good'⟩
    rcases z4o hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,1 + p,1 + q,w',
      zMt target_tm _ _ _ N k h_ms h_step_k,h_good'⟩

end Solution


set_option linter.deprecated false
set_option linter.dupNamespace false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000



open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases z5A (n + 1) with ⟨N,hN,_,_,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1))=N:=Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some:=zIm h_N
  rw [zMs,hn] at h_some
  exact h_some

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RBHHH_1LC0LF_1RD1LB_1RE0RD_1LB0RB_1LB0LA
