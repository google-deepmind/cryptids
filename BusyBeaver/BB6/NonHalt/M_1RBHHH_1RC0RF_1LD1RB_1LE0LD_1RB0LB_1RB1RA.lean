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

namespace BusyBeaver.M_1RBHHH_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RBHHH_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA"

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
set_option linter.dupNamespace false
set_option linter.deprecated false
set_option maxHeartbeats 2000000

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
variable {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]

abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000000
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
theorem refl_star (c : Cfg (Fin 2) (Fin 6)) : c [target_tm]⊢* c := ⟨0, rfl⟩
theorem step_L_p {q q' : Fin 6} {s a b : Fin 2} {l r : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨b, l, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, b >> l, r⟩⟩ [target_tm]⊢⁺ ce := by
  refine z03 ?_ h; simp only [step, ht, Option.map, Tape.write, Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
theorem step_L0_p {q q' : Fin 6} {s a : Fin 2} {r : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨0, default, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, default, r⟩⟩ [target_tm]⊢⁺ ce := by
  rw [← z00]; exact step_L_p ht h
theorem step_R_p {q0 q1 : Fin 6} {s a b : Fin 2} {l r : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q0 s = some (some q1, Stmt.write a Dir.right))
    (h : ⟨some q1, ⟨b, a >> l, r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q0, ⟨s, l, b >> r⟩⟩ [target_tm]⊢⁺ ce := by
  refine z03 ?_ h; simp only [step, ht, Option.map, Tape.write, Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
theorem step_R0_p {q0 q1 : Fin 6} {s a : Fin 2} {l : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q0 s = some (some q1, Stmt.write a Dir.right))
    (h : ⟨some q1, ⟨0, a >> l, default⟩⟩ [target_tm]⊢* ce) :
    ⟨some q0, ⟨s, l, default⟩⟩ [target_tm]⊢⁺ ce := by
  rw [← z00]; exact step_R_p ht h
theorem step_L_s {q q' : Fin 6} {s a b : Fin 2} {l r : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨b, l, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, b >> l, r⟩⟩ [target_tm]⊢* ce := zPs (step_L_p ht h)
theorem step_L0_s {q q' : Fin 6} {s a : Fin 2} {r : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨0, default, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, default, r⟩⟩ [target_tm]⊢* ce := zPs (step_L0_p ht h)
theorem step_R_s {q0 q1 : Fin 6} {s a b : Fin 2} {l r : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q0 s = some (some q1, Stmt.write a Dir.right))
    (h : ⟨some q1, ⟨b, a >> l, r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q0, ⟨s, l, b >> r⟩⟩ [target_tm]⊢* ce := zPs (step_R_p ht h)
theorem step_R0_s {q0 q1 : Fin 6} {s a : Fin 2} {l : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q0 s = some (some q1, Stmt.write a Dir.right))
    (h : ⟨some q1, ⟨0, a >> l, default⟩⟩ [target_tm]⊢* ce) :
    ⟨some q0, ⟨s, l, default⟩⟩ [target_tm]⊢* ce := zPs (step_R0_p ht h)
local macro "finish" : tactic =>
  `(tactic| exact refl_star _)
local macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.ListBlank.head_cons,zDh]); rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,z00,zDh,zDt])
theorem step_Lg_p {q q' : Fin 6} {s a : Fin 2} {l r : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨l.head, l.tail, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, l, r⟩⟩ [target_tm]⊢⁺ ce := z03 (by rw [step, ht]; rfl) h
theorem step_Rg_p {q0 q1 : Fin 6} {s a : Fin 2} {l r : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q0 s = some (some q1, Stmt.write a Dir.right))
    (h : ⟨some q1, ⟨r.head, a >> l, r.tail⟩⟩ [target_tm]⊢* ce) :
    ⟨some q0, ⟨s, l, r⟩⟩ [target_tm]⊢⁺ ce := z03 (by rw [step, ht]; rfl) h
theorem step_Lg_s {q q' : Fin 6} {s a : Fin 2} {l r : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨l.head, l.tail, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, l, r⟩⟩ [target_tm]⊢* ce := zPs (step_Lg_p ht h)
theorem step_Rg_s {q0 q1 : Fin 6} {s a : Fin 2} {l r : HalfTape} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q0 s = some (some q1, Stmt.write a Dir.right))
    (h : ⟨some q1, ⟨r.head, a >> l, r.tail⟩⟩ [target_tm]⊢* ce) :
    ⟨some q0, ⟨s, l, r⟩⟩ [target_tm]⊢* ce := zPs (step_Rg_p ht h)
local macro "fast_step" : tactic =>
  `(tactic| (
      first
      | refine step_R_s rfl ?_
      | refine step_L_s rfl ?_
      | refine step_R0_s rfl ?_
      | refine step_L0_s rfl ?_
      | refine step_Rg_s rfl ?_
      | refine step_Lg_s rfl ?_
      | refine step_R_p rfl ?_
      | refine step_L_p rfl ?_
      | refine step_R0_p rfl ?_
      | refine step_L0_p rfl ?_
      | refine step_Rg_p rfl ?_
      | refine step_Lg_p rfl ?_
      | step) <;> try rw [z00])
local macro "execute" : tactic =>
  `(tactic| (
      simp only [Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zDh, zDt, z00];
      repeat (first | finish | fast_step)))
abbrev t : BitWord := [1,1,0,0]
abbrev d0 : BitWord := [0,0]
abbrev d1 : BitWord := [1,0]
abbrev one : BitWord := [1]
abbrev lh : HalfTape := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
abbrev w_pre : BitWord := t ++ one
@[simp] theorem zDd : d0 +> (default : HalfTape) = default := by
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
  | .ca => [1,1,1,0,1,0]
def zCR (l : HalfTape) (c : Call) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  ((l <+ zCw c) {{zCs c}}> r)
def zCL (l : HalfTape) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (l <{{D}} ([0] +> r))
abbrev w_init : BitWord := t ++ (t ++ one)
def zCf (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  zCL lh (w_init +> r)
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
theorem z0D : Side [.ch] default (d1 +> default) := by
  refine Side.cons (fun l => ?_) (Side.nil _)
  unfold zCR zCL zCw zCs d1
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
theorem z0E : Seg [.ca] [.ch,.ch] t ((t ++ [0]) ++ t) :=
  zS5
    (mid1 := [1,0,1,1,1,1,0,1,0])
    (mid2 := [1,0,1,0,1,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
theorem z0F : Seg [.ca,.ch] ([.cj] ++ [.ch] ^ 5) w_init (w_init ++ t) := by
  have h1a : Seg [.ch,.ch] [.cj,.ch,.ch,.ch] (t ++ one) t :=
    zSg zH2 z0f
  have h1 : Seg [.ca] [.cj,.ch,.ch,.ch] (t ++ (t ++ one)) (((t ++ [0]) ++ t) ++ t) :=
    zS0 z0E h1a
  have h2 : Seg [.ch] [.ch,.ch] (((t ++ [0]) ++ t) ++ t) ((t ++ (t ++ one)) ++ t) :=
    zS0 (zS0 z0e z0d) z0f
  exact zSg h1 h2
theorem z0G (r : HalfTape) :
    (zCL lh r) [target_tm]⊢⁺ (zCR ([1] +> default) .ca r) := by
  unfold zCL zCR lh zCw zCs
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
theorem z0H (r : HalfTape) :
    (zCL ([1] +> default) r) [target_tm]⊢⁺ (zCR lh .ch r) := by
  unfold zCL zCR lh zCw zCs
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
open WordCalculus Word
local notation "WordList" => List Word
theorem loc_z1L {n : Nat} {ds : WordList} {A H B : Nat}
    (hD : DigitVal A H ds) (hSum : A + n = B + 2 ^ H) (hBound : B < 2 ^ H) :
    ∃ v,DigitVal B H v /\ WordEffect n (ds ++ [Q]) 1 (v ++ [K]) := by
  rcases exists_wordEffect ds n with ⟨b,v,hE⟩
  rcases wordEffect_digitVal hE hD with ⟨C,hV,hEq⟩
  have hCb := lt_pow_of_digitVal hV
  have hb1 : b = 1 := by
    rcases b with _ | _ | b'
    · omega
    · rfl
    · rw [Nat.add_mul,Nat.add_mul,Nat.one_mul] at hEq
      omega
  subst hb1
  have hCB : C = B := by omega
  subst hCB
  exact ⟨v,hV,wordEffect_append hE (@WordEffect.d11 0 [] 1 [] (WordEffect.nil 1))⟩
theorem loc_z1M {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (hI : WordEffect n u b v) :
    ((1 + n : Nat) : Rat) <= ((1 + b : Nat) : Rat) * wordScale u /\
    ((1 + b : Nat) : Rat) * wordScale u <= ((1 + n : Nat) : Rat) + 2 * wordMass u := by
  have hBud := wordEffect_budget_eq hI
  have hW := wordEffect_preserves_scale_and_mass hI
  have hSu := wordMass_eq_add u
  have hSv := wordMass_eq_add v
  have hNu := wordMass_nonneg u
  have hNv := wordMass_nonneg v
  refine ⟨by linarith,by linarith⟩
theorem loc_z1N (u : WordList) (A H : Nat) (ds : WordList)
    (hD : DigitVal A H ds)
    (hHeight : wordScale u * ((2 ^ H : Nat) : Rat) = 1)
    (hCut : notEndsWithQ u = true)
    (hNe : u ≠ [])
    (hBound : wordMass u + wordScale u * (1 + wordMassK ds) <= 1 / 128) :
    ∃ k v a b,PhaseScan 12 (u ++ ds ++ [K]) k v a b /\ 4 < k := by
  have hWu := wordMass_nonneg u
  have hWd := wordMass_nonneg ds
  have hSu := wordScale_pos u
  have hEx_in : 8 * wordMass u < ((6 * 2 : Nat) : Rat) - 4 := by
    push_cast; nlinarith
  rcases exists_phaseScan_of_mass_lt u 6 hEx_in with ⟨k,v,a,b,hI,hK⟩
  rcases phaseScan_even_out_of_notEndsWithQ hI hCut hNe with ⟨n,rfl⟩
  have hBudget := phaseScan_budget_eq hI
  have hLoss := phaseScan_loss_bounds hI
  have hSv := phaseScan_scale_le hI
  have hPv := wordScale_pos v
  have hCarry : 7 < (((n * 2 : Nat) : Rat) - 4) * wordScale v := by
    push_cast at hBudget ⊢; nlinarith
  rcases digitVal_scale_and_mass hD with ⟨hSd,hMd,_⟩
  have hRest : 2 * (wordMass (ds ++ [K]) + wordMassK (ds ++ [K])) * wordScale v < 7 := by
    rw [wordMass_append,wordMassK_append]
    dsimp [wordMass,wordMassK]
    have h1 : wordScale u * wordMassK ds <= 1 / 128 := by nlinarith
    have h2 : wordScale u * wordScale ds = 1 := by rwa [hSd]
    have h3 : wordScale v * wordScale ds <= 1 := by nlinarith
    have h4 : wordScale v * wordMass ds <= 1 := by nlinarith
    have h5 : wordScale v * wordMassK ds <= 1 / 128 := by nlinarith
    nlinarith
  have hTail1 : 2 * (wordMass (ds ++ [K]) + wordMassK (ds ++ [K])) < ((n * 2 : Nat) : Rat) := by
    nlinarith
  have hTail2 : 8 * (1 + 2 * wordMassK ds) < ((n * 2 : Nat) : Rat) - 4 := by
    have h1 : wordScale v * wordMassK ds <= 1 / 128 := by nlinarith
    have h2 : 8 * (1 + 2 * wordMassK ds) * wordScale v < 1 := by nlinarith
    nlinarith
  rcases scan_tailDefect_step_bound (ds ++ [K]) (wordMassK ds) n (tailDefect_append_K_of_digitVal hD) hTail1 hTail2
    with ⟨k',w,c,d,hJ,hK'⟩
  rcases phaseScan_append hI hJ with ⟨a',b',hIJ,_,_⟩
  refine ⟨k',v ++ w,a',b',?_,hK'⟩
  simpa [List.append_assoc] using hIJ
theorem loc_z1O (n : Nat) : (0 : Rat) < ((2 ^ n : Nat) : Rat) := by
  exact_mod_cast pow_two_pos n
theorem loc_z1P (n : Nat) :
    wordMass (List.replicate n V) = 0 /\
    wordScale (List.replicate n V) * ((2 ^ n : Nat) : Rat) = 1 := by
  induction n with
  | zero => simp [wordMass,wordScale]
  | succ n ih =>
    dsimp [List.replicate,wordMass,wordScale]
    refine ⟨by linarith [ih.1],?_⟩
    have hpow : ((2 ^ (n + 1) : Nat) : Rat) = ((2 ^ n : Nat) : Rat) * 2 := by
      rw [Nat.pow_succ]; push_cast; ring
    rw [hpow]
    linarith [ih.2]
theorem loc_z1Q (n : Nat) (x : Rat) :
    wordScale (List.replicate n V) * x * ((2 ^ n : Nat) : Rat) = x := by
  have h := (loc_z1P n).2
  calc wordScale (List.replicate n V) * x * ((2 ^ n : Nat) : Rat)
    _ = x * (wordScale (List.replicate n V) * ((2 ^ n : Nat) : Rat)) := by ring
    _ = x * 1 := by rw [h]
    _ = x := by ring
theorem loc_z1R {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) :
    ∀ (p q : WordList),u = p ++ q -> SplitCond p q ->
      ∃ c x y s t0,Scan a p c x s /\ Scan c q b y t0 /\
        v = x ++ y /\ l = s + wordScale x * t0 := by
  induction h with
  | nil k =>
    intro p q hE _
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨k,[],[],0,0,Scan.nil k,Scan.nil k,rfl,by simp [wordScale]⟩
    | cons _ _ => simp at hE
  | T hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.T hI,rfl,by simp [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (splitCond_of_cons V p q hP) with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
      exact ⟨c,V :: x,y,s1 * (1 / 2),t1,Scan.T hJ,hK,rfl,by dsimp [wordScale]; rw [hL]; ring⟩
  | pair0 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.pair0 hI,rfl,by simp [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := splitCond_of_cons K p q (splitCond_of_cons Q (K :: p) q hP)
        rcases ih p q hE hP' with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
        exact ⟨c,V :: x,y,(1 + s1) * (1 / 2),t1,Scan.pair0 hJ,hK,rfl,by dsimp [wordScale]; rw [hL]; ring⟩
  | pair1 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.pair1 hI,rfl,by simp [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := splitCond_of_cons Q p q (splitCond_of_cons Q (Q :: p) q hP)
        rcases ih p q hE hP' with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
        exact ⟨c,V :: x,y,(1 / 4) + s1 * (1 / 2),t1,Scan.pair1 hJ,hK,rfl,by dsimp [wordScale]; rw [hL]; ring⟩
  | short00 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short00 hI,rfl,by simp [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (splitCond_of_cons K p q hP) with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
      exact ⟨c,K :: x,y,1 + s1 * 2,t1,Scan.short00 hJ,hK,rfl,by dsimp [wordScale]; rw [hL]; ring⟩
  | short01 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short01 hI,rfl,by simp [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (splitCond_of_cons Q p q hP) with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
      exact ⟨c,K :: x,y,s1 * 2,t1,Scan.short01 hJ,hK,rfl,by dsimp [wordScale]; rw [hL]; ring⟩
  | short10 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short10 hI,rfl,by simp [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (splitCond_of_cons K p q hP) with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
      exact ⟨c,Q :: x,y,1 + s1 * 2,t1,Scan.short10 hJ,hK,rfl,by dsimp [wordScale]; rw [hL]; ring⟩
  | short11 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short11 hI,rfl,by simp [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (splitCond_of_cons Q p q hP) with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
      exact ⟨c,Q :: x,y,s1 * 2,t1,Scan.short11 hJ,hK,rfl,by dsimp [wordScale]; rw [hL]; ring⟩
theorem loc_z1S (r a b : Nat) (v : WordList) (l : Rat) (u : WordList) (z : Rat)
    (hI : Scan a ((List.replicate (1 + r * 2) Q ++ [K]) ++ u) b v l)
    (hZ : TailDefect u z) :
    wordMass v * ((2 ^ (1 + r) : Nat) : Rat) <= 1 + 2 * z /\
    (l - 1 / 2) * ((2 ^ (1 + r) : Nat) : Rat) <= 1 + 2 * z := by
  have hCut : SplitCond (List.replicate (1 + r * 2) Q ++ [K]) u := by
    left; rw [notEndsWithQ_append_singleton]; rfl
  rcases loc_z1R hI (List.replicate (1 + r * 2) Q ++ [K]) u rfl hCut
    with ⟨c,x,y,s,t0,hJ,hK,rfl,hL⟩
  rcases scan_odd_Q_K_inv r a c x s hJ with ⟨rfl,_,rfl⟩
  rcases scan_tailDefect_bound hK hZ with ⟨hMy,hLy,_⟩
  rcases loc_z1P (1 + r) with ⟨hMx,hSx⟩
  have hF1 := loc_z1Q (1 + r) (wordMass y)
  have hF2 := loc_z1Q (1 + r) t0
  have hPos := loc_z1O (1 + r)
  rw [wordMass_append]
  refine ⟨by nlinarith,by nlinarith⟩
theorem loc_z1T (r a b : Nat) (v : WordList) (l : Rat) (u : WordList) (z : Rat)
    (hI : Scan a ((List.replicate (2 + r * 2) Q ++ [K]) ++ u) b v l)
    (hZ : TailDefect u z) :
    (wordMass v - 1) * ((2 ^ r : Nat) : Rat) <= 1 + 2 * z /\
    (l - 1) * ((2 ^ r : Nat) : Rat) <= 1 + 2 * z := by
  have hCut : SplitCond (List.replicate (2 + r * 2) Q ++ [K]) u := by
    left; rw [notEndsWithQ_append_singleton]; rfl
  rcases loc_z1R hI (List.replicate (2 + r * 2) Q ++ [K]) u rfl hCut
    with ⟨c,x,y,s,t0,hJ,hK,rfl,hL⟩
  rcases scan_even_Q_K_inv r a c x s hJ with ⟨d,n,rfl,_,rfl⟩
  rcases scan_tailDefect_bound hK hZ with ⟨hMy,hLy,_⟩
  rcases loc_z1P (1 + r) with ⟨hMx,hSx⟩
  have hF1 := loc_z1Q (1 + r) (wordMass y)
  have hF2 := loc_z1Q (1 + r) t0
  have hPos := loc_z1O r
  have hWy := wordMass_nonneg y
  have hPow1 : ((2 ^ (1 + r) : Nat) : Rat) = 2 * ((2 ^ r : Nat) : Rat) := by
    rw [pow_two_one_add]; push_cast; ring
  cases d <;> (
    dsimp [List.cons_append,wordMass,wordScale] at hL ⊢
    rw [wordMass_append]
    rw [hPow1] at hF1 hF2
    refine ⟨by nlinarith,by nlinarith⟩
  )
theorem loc_z1U (c a b : Nat) (v : WordList) (l : Rat) (u : WordList) (z : Rat)
    (hI : Scan a ((List.replicate c Q ++ [K]) ++ u) b v l)
    (hZ : TailDefect u z) (hC : 0 < c) :
    wordMass v * ((2 ^ (c + c / 2) : Nat) : Rat) <= ((2 ^ (c + c / 2) : Nat) : Rat) + 2 * ((2 ^ c : Nat) : Rat) * (1 + 2 * z) /\
    l * ((2 ^ (c + c / 2) : Nat) : Rat) <= ((2 ^ (c + c / 2) : Nat) : Rat) + 2 * ((2 ^ c : Nat) : Rat) * (1 + 2 * z) := by
  have hZn := tailDefect_nonneg hZ
  rcases even_or_odd_mul_two c with ⟨a0,rfl⟩ | ⟨a0,rfl⟩
  · cases a0 with
    | zero => omega
    | succ r =>
      have heq : (r + 1) * 2 = 2 + r * 2 := by omega
      rw [heq] at hI ⊢
      rcases loc_z1T r a b v l u z hI hZ with ⟨hM,hL⟩
      have hP : 2 + r * 2 + (2 + r * 2) / 2 = (2 + r * 2) + r + 1 := by omega
      have hPow : ((2 ^ (2 + r * 2 + (2 + r * 2) / 2) : Nat) : Rat) =
          ((2 ^ (2 + r * 2) : Nat) : Rat) * ((2 ^ r : Nat) : Rat) * 2 := by
        rw [hP,Nat.pow_add,Nat.pow_add]
        push_cast; ring
      have hp1 := loc_z1O (2 + r * 2)
      have hp2 := loc_z1O r
      rw [hPow]
      refine ⟨by nlinarith,by nlinarith⟩
  · rcases loc_z1S a0 a b v l u z hI hZ with ⟨hM,hL⟩
    have hP : 1 + a0 * 2 + (1 + a0 * 2) / 2 = (1 + a0 * 2) + a0 := by omega
    have hPow : ((2 ^ (1 + a0 * 2 + (1 + a0 * 2) / 2) : Nat) : Rat) =
        ((2 ^ (1 + a0 * 2) : Nat) : Rat) * ((2 ^ a0 : Nat) : Rat) := by
      rw [hP,Nat.pow_add]; push_cast; ring
    have hPow1 : ((2 ^ (1 + a0) : Nat) : Rat) = 2 * ((2 ^ a0 : Nat) : Rat) := by
      rw [pow_two_one_add]; push_cast; ring
    rw [hPow1] at hM hL
    have hp1 := loc_z1O (1 + a0 * 2)
    have hp2 := loc_z1O a0
    rw [hPow]
    refine ⟨by nlinarith,by nlinarith⟩
theorem loc_z1V (c : Nat) :
    ∀ (u : WordList) (z : Rat),TailDefect (List.replicate c Q ++ u) z ->
      ∃ z',TailDefect u z' /\ z = ((2 ^ c : Nat) : Rat) * z' := by
  induction c with
  | zero =>
    intro u z hI
    exact ⟨z,hI,by simp⟩
  | succ c ih =>
    intro u z hI
    dsimp [List.replicate] at hI
    rcases tailDefect_cons_Q_inv hI with ⟨y,hJ,rfl⟩
    rcases ih u y hJ with ⟨x,hK,rfl⟩
    refine ⟨x,hK,?_⟩
    rw [Nat.pow_succ]; push_cast; ring
theorem loc_z1W (x z p q : Rat) (hp : 0 < p) (hpq : p <= q) (hz : 0 <= z)
    (h : x * q <= q + 2 * z) : x * p <= p + 2 * z := by
  rcases le_or_gt x 1 with hle | hgt
  · nlinarith
  · nlinarith
theorem loc_z1X (s c : Nat) (u : WordList) (A H a b : Nat) (v : WordList) (l : Rat)
    (hD : DigitVal A H (List.replicate c Q ++ K :: u))
    (hI : Scan a ((List.replicate c Q ++ K :: u) ++ [K]) b v l)
    (hC : 0 < c) (hSC : s <= c) :
    wordMass v * ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK (List.replicate c Q ++ K :: u) /\
    l * ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK (List.replicate c Q ++ K :: u) := by
  have hZ := tailDefect_append_K_of_digitVal hD
  rw [List.append_assoc] at hZ
  rcases loc_z1V c (K :: u ++ [K]) (wordMassK (List.replicate c Q ++ K :: u)) hZ with ⟨x,hU,hX⟩
  rcases tailDefect_cons_K_inv hU with ⟨hNil,_⟩ | ⟨z,hV,rfl⟩
  · simp at hNil
  · have hE : (List.replicate c Q ++ K :: u) ++ [K] =
        (List.replicate c Q ++ [K]) ++ (u ++ [K]) := by
      simp [List.append_assoc]
    rw [hE] at hI
    rcases loc_z1U c a b v l (u ++ [K]) z hI hV hC with ⟨hM,hL⟩
    have hPos := loc_z1O (s + s / 2)
    have hMono_nat : 2 ^ (s + s / 2) <= 2 ^ (c + c / 2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hMono : ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (c + c / 2) : Nat) : Rat) := by
      exact_mod_cast hMono_nat
    have hW := (wordMass_nonneg (List.replicate c Q ++ K :: u)).2.1
    refine ⟨loc_z1W (wordMass v) (wordMassK (List.replicate c Q ++ K :: u)) _ _ hPos hMono hW (by linarith),
            loc_z1W l (wordMassK (List.replicate c Q ++ K :: u)) _ _ hPos hMono hW (by linarith)⟩
theorem loc_z1Y (s : Nat) (ds : WordList) (A H k k' : Nat) (v : WordList) (a b : Rat)
    (hD : DigitVal A H ds)
    (hI : PhaseScan k (ds ++ [K]) k' v a b)
    (hLow : ∃ c u,(0 < c /\ s <= c) /\ ds = List.replicate c Q ++ K :: u) :
    wordMass v * ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds /\
    a * ((2 ^ (s + s / 2) : Nat) : Rat) <= 4 * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds) /\
    b * ((2 ^ (s + s / 2) : Nat) : Rat) <= 3 * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds) := by
  rcases hLow with ⟨c,u,⟨hC,hSC⟩,rfl⟩
  have hFull := digitVal_append hD (DigitVal.zero DigitVal.nil)
  rcases phaseScan_digitVal_loss_bound hI hFull with ⟨l,hJ,hP,hN⟩
  rcases loc_z1X s c u A H k k' v l hD hJ hC hSC with ⟨hM,hL⟩
  have hPos := loc_z1O (s + s / 2)
  refine ⟨hM,by nlinarith,by nlinarith⟩
theorem loc_z1Z (r J k b A B : Nat)
    (hR : r <= J)
    (hK : ∃ n,k = n * 2 ^ r)
    (hB : ∃ n,1 + b = n * 2 ^ r)
    (hAsum : A + 2 ^ J = k)
    (hBsum : B + 2 ^ J = A + b) :
    ∃ n,1 + B = n * 2 ^ r := by
  rcases hK with ⟨n,rfl⟩
  rcases hB with ⟨m,hM⟩
  have hP : 2 ^ J = 2 ^ (J - r) * 2 ^ r := by
    rw [<- Nat.pow_add,Nat.sub_add_cancel hR]
  refine ⟨n + m - 2 * 2 ^ (J - r),?_⟩
  rw [Nat.sub_mul,Nat.add_mul]
  have h2 : 2 * 2 ^ (J - r) * 2 ^ r = 2 ^ J + 2 ^ J := by
    calc 2 * 2 ^ (J - r) * 2 ^ r
      _ = 2 * (2 ^ (J - r) * 2 ^ r) := by ring
      _ = 2 * 2 ^ J := by rw [<- hP]
      _ = 2 ^ J + 2 ^ J := by ring
  omega
theorem loc_z20 (s : Nat) :
    ∀ (B H : Nat) (ds : WordList),
      DigitVal B H ds -> s <= H -> (∃ n,1 + B = n * 2 ^ s) ->
      ∃ u,ds = List.replicate s Q ++ u := by
  induction s with
  | zero =>
    intro B H ds _ _ _
    exact ⟨ds,rfl⟩
  | succ s ih =>
    intro B H ds hD hSH ⟨n,hN⟩
    have hN2 : 1 + B = (n * 2 ^ s) * 2 := by rw [Nat.pow_succ] at hN; linarith
    cases hD with
    | nil => omega
    | zero _ => omega
    | @one A' H' u' hSub =>
      rcases ih A' H' u' hSub (by omega) ⟨n,by omega⟩ with ⟨w,rfl⟩
      exact ⟨w,rfl⟩
theorem loc_z21 (p : Nat) :
    ∀ (n : Nat) (u : WordList) (b : Nat) (v : WordList),
      WordEffect n (List.replicate p V ++ u) b v ->
      ∃ q w,v = List.replicate p V ++ w /\ 1 + q = (1 + n) * 2 ^ p /\ WordEffect q u b w := by
  induction p with
  | zero =>
    intro n u b v hI
    exact ⟨n,v,rfl,by simp,hI⟩
  | succ p ih =>
    intro n u b v hI
    dsimp [List.replicate] at hI
    cases hI with
    | T hSub =>
      rcases ih (1 + n * 2) u b _ hSub with ⟨q,w,rfl,hEq,hJ⟩
      refine ⟨q,w,rfl,?_,hJ⟩
      rw [Nat.pow_succ]; ring_nf at hEq ⊢; omega
theorem loc_z22 (n : Nat) (w : Word) :
    List.replicate (1 + n) w = w :: List.replicate n w := by
  rw [Nat.add_comm 1 n,List.replicate_succ]
theorem loc_z23 (p : Nat) (u : WordList) (b : Nat) (v : WordList)
    (hI : WordEffect 0 (List.replicate (1 + p) V ++ Q :: u) b v) :
    ∃ w,v = List.replicate (1 + p) V ++ K :: w /\ WordEffect (2 ^ p) u b w := by
  rcases loc_z21 (1 + p) 0 (Q :: u) b v hI with ⟨q,w0,rfl,hEq,hJ⟩
  have hp := pow_two_pos p
  have hpow : 2 ^ (1 + p) = 2 ^ p + 2 ^ p := pow_two_one_add p
  generalize hq0 : q = q0 at hJ
  generalize hu0 : Q :: u = u0 at hJ
  cases hJ with
  | nil _ => nomatch hu0
  | T _ => nomatch hu0
  | d00 _ => nomatch hu0
  | d01 _ => nomatch hu0
  | d10 _ => omega
  | @d11 m u' _ w hSub =>
    injection hu0 with _ hu'; subst hu'
    have hm : 1 + m = 2 ^ p := by omega
    rw [hm] at hSub
    exact ⟨w,rfl,hSub⟩
theorem loc_z24 (p : Nat) (u : WordList) (k : Nat) (v : WordList) (a b : Rat)
    (hI : PhaseScan 12 (List.replicate p V ++ K :: u) k v a b) :
    ∃ w a' b',v = List.replicate p V ++ Q :: w /\
      PhaseScan (4 * 2 ^ p) u k w a' b' /\
      a = wordScale (List.replicate p V) * (4 + 2 * a') /\
      b = wordScale (List.replicate p V) * (2 * b') := by
  rcases phaseScan_split_of_splitCond hI (List.replicate p V) (K :: u) rfl (Or.inl (notEndsWithQ_replicate_V p))
    with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
  rcases phaseScan_replicate_V_inv p 12 m x a1 b1 hJ with ⟨rfl,hEq,rfl,rfl⟩
  have hp := pow_two_pos p
  generalize hm0 : m = m0 at hK
  generalize hu0 : K :: u = u0 at hK
  cases hK with
  | nil _ => nomatch hu0
  | T _ => nomatch hu0
  | pair0 _ => nomatch hu0
  | pair1 _ => nomatch hu0
  | short01 _ => nomatch hu0
  | short11 _ => nomatch hu0
  | short00 _ => omega
  | @short10 n u' _ w a' b' hSub =>
    injection hu0 with _ hu'; subst hu'
    have hn : n * 2 = 4 * 2 ^ p := by omega
    rw [hn] at hSub
    refine ⟨w,a',b',rfl,hSub,by linarith,by linarith⟩
theorem loc_z25 (r k : Nat) (u : WordList) (k' : Nat) (v : WordList) (a b : Rat)
    (carry : Nat) (eff : WordList) (A B J : Nat) (ds : WordList)
    (hI : PhaseScan k (u ++ List.replicate (1 + r * 2) Q ++ [K]) k' v a b)
    (hE : WordEffect 0 (V :: (v ++ [V])) carry eff)
    (hD : DigitVal B J ds) (hR : 1 + r <= J)
    (hAsum : A + 2 ^ J = k') (hBsum : B + 2 ^ J = A + carry) :
    ∃ w,ds = List.replicate (1 + r) Q ++ w := by
  rcases phaseScan_append_odd_Q_K_inv r k u k' v a b hI with ⟨w,n,rfl,hK⟩
  have hEq : V :: ((w ++ List.replicate (1 + r) V) ++ [V]) =
      (V :: w) ++ List.replicate (2 + r) V := by
    have h1 : 2 + r = (1 + r) + 1 := by omega
    rw [h1,replicate_succ_append]; simp [List.append_assoc]
  rw [hEq] at hE
  rcases wordEffect_append_replicate_V_inv (V :: w) (2 + r) 0 carry eff hE with ⟨x,m,_,hC⟩
  apply loc_z20 (1 + r) B J ds hD hR
  refine loc_z1Z (1 + r) J k' carry A B hR ⟨n,hK⟩ ⟨m * 2,?_⟩ hAsum hBsum
  have h2 : 2 + r = (1 + r) + 1 := by omega
  rw [h2,Nat.pow_succ] at hC
  linarith
theorem loc_z26 (x p q s f : Rat) (hp : 0 < p) (hs : 0 <= s)
    (h1 : x * p <= q) (h2 : s * q <= f * p) : s * x <= f := by
  nlinarith
theorem loc_z27 (s : Nat) (ds : WordList) (A H k k' : Nat) (v : WordList) (a b sigma f : Rat)
    (hD : DigitVal A H ds) (hI : PhaseScan k (ds ++ [K]) k' v a b)
    (hLow : ∃ c u,(0 < c /\ s <= c) /\ ds = List.replicate c Q ++ K :: u)
    (hSig : 0 <= sigma)
    (hBound : sigma * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds) <= f * ((2 ^ (s + s / 2) : Nat) : Rat)) :
    sigma * wordMass v <= f /\ sigma * a <= 4 * f /\ sigma * b <= 3 * f := by
  rcases loc_z1Y s ds A H k k' v a b hD hI hLow with ⟨hM,hP,hN⟩
  have hPos := loc_z1O (s + s / 2)
  refine ⟨loc_z26 (wordMass v) _ _ sigma f hPos hSig hM hBound,
          loc_z26 a _ _ sigma (4 * f) hPos hSig hP (by linarith),
          loc_z26 b _ _ sigma (3 * f) hPos hSig hN (by linarith)⟩
theorem le_of_mul_le_mul_pos_right {a b u : Rat} (hu : 0 < u) (h : a * u <= b * u) : a <= b := by
  by_contra hlt
  have : b < a := not_le.mp hlt
  nlinarith
theorem lt_of_mul_lt_mul_pos_right {a b u : Rat} (hu : 0 < u) (h : a * u < b * u) : a < b := by
  by_contra hle
  have : b <= a := not_lt.mp hle
  nlinarith
theorem loc_z28 (a b : Nat) : ((2 ^ (a + b) : Nat) : Rat) = ((2 ^ a : Nat) : Rat) * ((2 ^ b : Nat) : Rat) := by
  rw [Nat.pow_add,Nat.cast_mul]
theorem loc_z29 : ((2 ^ 2 : Nat) : Rat) = 4 := by norm_num
theorem loc_z2a : ((2 ^ 10 : Nat) : Rat) = 1024 := by norm_num
theorem loc_z2b (p : Nat) (u ds : WordList) (A H k : Nat) (v : WordList) (a b : Rat) (s : Nat) (e f : Rat)
    (hI : PhaseScan 12 (List.replicate p V ++ K :: (u ++ ds ++ [K])) k v a b)
    (hD : DigitVal A H ds) (hCut : notEndsWithQ u = true)
    (hLow : ∃ c w,(0 < c /\ s <= c) /\ ds = List.replicate c Q ++ K :: w)
    (hError : e = 2 * wordScale (List.replicate p V) * wordMass u)
    (hBound : (2 * wordScale (List.replicate p V) * wordScale u) * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds) <= f * ((2 ^ (s + s / 2) : Nat) : Rat)) :
    ∃ w,v = List.replicate p V ++ Q :: w /\
      wordMass (V :: (v ++ [V])) <= wordScale (List.replicate p V) * (1 / 2) + (e + f) * (1 / 2) /\
      4 * wordScale (List.replicate p V) - e * (1 / 4) - 3 * f <= a - b /\
      a - b <= 4 * wordScale (List.replicate p V) + 4 * e + 4 * f := by
  rcases loc_z24 p (u ++ ds ++ [K]) k v a b hI with ⟨w,c,d,rfl,hJ,hPos,hNeg⟩
  have hEq_u : u ++ ds ++ [K] = u ++ (ds ++ [K]) := by simp [List.append_assoc]
  rw [hEq_u] at hJ
  rcases phaseScan_split_of_splitCond hJ u (ds ++ [K]) rfl (Or.inl hCut)
    with ⟨m,x,y,a1,b1,a2,b2,hK,hL,rfl,hC,hDlt⟩
  have hBounds := phaseScan_loss_bounds hK
  have hTailBounds := phaseScan_loss_bounds hL
  have hScale := phaseScan_scale_le hK
  have hSu := wordScale_pos u
  have hSx := wordScale_pos x
  have hSp := wordScale_pos (List.replicate p V)
  have hWds := wordMass_nonneg ds
  have hPow := loc_z1O (s + s / 2)
  have h1 : 2 * wordScale (List.replicate p V) * wordScale x <= 2 * wordScale (List.replicate p V) * wordScale u := by nlinarith
  have h2 : 0 <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds := by linarith
  have hF : (2 * wordScale (List.replicate p V) * wordScale x) * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds) <=
      f * ((2 ^ (s + s / 2) : Nat) : Rat) := by
    nlinarith
  rcases loc_z27 s ds A H m k y a2 b2 (2 * wordScale (List.replicate p V) * wordScale x) f hD hL hLow (by positivity) hF
    with ⟨hMt,hPt,hNt⟩
  have hPa : 0 <= (2 * wordScale (List.replicate p V) * wordScale x) * a2 := by
    have : 0 <= a2 := hTailBounds.2.1
    positivity
  have hPb : 0 <= (2 * wordScale (List.replicate p V) * wordScale x) * b2 := by
    have : 0 <= b2 := hTailBounds.2.2.2.1
    positivity
  have hA1 : 0 <= 2 * wordScale (List.replicate p V) * a1 := by
    have : 0 <= a1 := hBounds.2.1
    positivity
  have hA1u : 2 * wordScale (List.replicate p V) * a1 <= 4 * e := by
    have : a1 <= 4 * wordMass u := hBounds.2.2.1
    nlinarith
  have hB1 : 0 <= 2 * wordScale (List.replicate p V) * b1 := by
    have : 0 <= b1 := hBounds.2.2.2.1
    positivity
  have hB1u : 2 * wordScale (List.replicate p V) * b1 <= e * (1 / 4) := by
    have : b1 <= wordMass u * (1 / 4) := hBounds.2.2.2.2
    nlinarith
  have hMx : 2 * wordScale (List.replicate p V) * wordMass x <= e := by
    have : wordMass x <= wordMass u := hBounds.1
    nlinarith
  have hMassP := (loc_z1P p).1
  have hAb_eq : a - b = 4 * wordScale (List.replicate p V) +
      2 * wordScale (List.replicate p V) * a1 +
      (2 * wordScale (List.replicate p V) * wordScale x) * a2 -
      2 * wordScale (List.replicate p V) * b1 -
      (2 * wordScale (List.replicate p V) * wordScale x) * b2 := by
    rw [hPos,hNeg,hC,hDlt]; ring
  refine ⟨x ++ y,rfl,?_,?_,?_⟩
  · have hE1 : wordMass (V :: ((List.replicate p V ++ Q :: (x ++ y)) ++ [V])) =
        wordScale (List.replicate p V) * (1 / 2) +
        (2 * wordScale (List.replicate p V) * wordMass x + (2 * wordScale (List.replicate p V) * wordScale x) * wordMass y) * (1 / 2) := by
      simp only [List.cons_append,List.append_assoc,wordMass,wordMass_append,wordScale,hMassP]
      ring
    rw [hE1]
    linarith
  · rw [hAb_eq]; linarith
  · rw [hAb_eq]; linarith
theorem loc_z2c (p : Nat) (u : WordList) (b : Nat) (v : WordList)
    (hI : WordEffect 0 (List.replicate (1 + p) V ++ Q :: u) b v) :
    2 * wordScale (List.replicate (1 + p) V) <=
      ((1 + b : Nat) : Rat) * wordScale (List.replicate (1 + p) V ++ Q :: u) - 1 /\
    ((1 + b : Nat) : Rat) * wordScale (List.replicate (1 + p) V ++ Q :: u) - 1 <=
      2 * wordMass (List.replicate (1 + p) V ++ Q :: u) := by
  rcases loc_z23 p u b v hI with ⟨w,rfl,hE⟩
  rcases loc_z1M hE with ⟨hLo,hHi⟩
  have hSp := wordScale_pos (List.replicate (1 + p) V)
  rcases loc_z1P (1 + p) with ⟨hM,hS⟩
  have hS' : wordScale (List.replicate (1 + p) V) * (2 * ((2 ^ p : Nat) : Rat)) = 1 := by
    rw [pow_two_one_add,Nat.cast_add] at hS
    linarith
  have htmp : ((1 + 2 ^ p : Nat) : Rat) = 1 + ((2 ^ p : Nat) : Rat) := by
    rw [Nat.cast_add,Nat.cast_one]
  rw [htmp] at hLo hHi
  have h1 : ((1 + b : Nat) : Rat) * wordScale (List.replicate (1 + p) V ++ Q :: u) =
      2 * wordScale (List.replicate (1 + p) V) * (((1 + b : Nat) : Rat) * wordScale u) := by
    rw [wordScale_append]; dsimp [wordScale]; ring
  have h2 : 2 * wordMass (List.replicate (1 + p) V ++ Q :: u) =
      2 * wordScale (List.replicate (1 + p) V) * (1 + 2 * wordMass u) := by
    rw [wordMass_append,hM]; dsimp [wordMass]; ring
  rw [h1,h2]
  refine ⟨by nlinarith,by nlinarith⟩
theorem loc_z2d (alpha e f unit delta R e' : Rat)
    (_ : 0 < alpha) (_ : 0 <= e) (_ : 0 <= f) (_ : 0 <= unit)
    (_ : e <= alpha * (3 / 64)) (_ : f <= alpha * (1 / 128)) (_ : unit <= alpha * (1 / 1024))
    (_ : 0 <= e') (_ : e' <= (e + f) * (1 / 2)) (_ : alpha <= R) (_ : R <= alpha + 2 * e')
    (_ : 4 * alpha - e * (1 / 4) - 3 * f <= delta) (_ : delta <= 4 * alpha + 4 * e + 4 * f) :
    (3 / 4) * alpha <= delta * (1 / 2) - 4 * unit - R /\
    delta * (1 / 2) - 4 * unit - R <= (5 / 4) * alpha := by
  exact ⟨by linarith,by linarith⟩
theorem loc_z2e {u : WordList} {k : Nat} {v : WordList} {a b : Rat}
    (hI : PhaseScan 12 u k v a b) :
    (k : Rat) * wordScale (V :: (v ++ [V])) =
      2 + 4 * wordScale (V :: (v ++ [V])) - (a - b) * (1 / 2) := by
  have hEq := phaseScan_budget_eq hI
  push_cast at hEq
  dsimp [wordScale]
  rw [wordScale_append]
  dsimp [wordScale]
  linarith
theorem loc_z2f {u : WordList} {k : Nat} {v : WordList} {a b : Rat} {J A B carry : Nat}
    (hI : PhaseScan 12 u k v a b)
    (hHeight : wordScale (V :: (v ++ [V])) * ((2 ^ J : Nat) : Rat) = 1)
    (hAsum : A + 2 ^ J = k)
    (hBsum : B + 2 ^ J = A + carry) :
    1 - ((1 + B : Nat) : Rat) * wordScale (V :: (v ++ [V])) =
      (a - b) * (1 / 2) - 4 * wordScale (V :: (v ++ [V])) -
      (((1 + carry : Nat) : Rat) * wordScale (V :: (v ++ [V])) - 1) := by
  have hBudget := loc_z2e hI
  have hSum : B + 2 ^ J + 2 ^ J = k + carry := by omega
  have hQsum : ((B + 2 ^ J + 2 ^ J : Nat) : Rat) = ((k + carry : Nat) : Rat) := by exact_mod_cast hSum
  rw [Nat.cast_add,Nat.cast_add,Nat.cast_add] at hQsum
  have hQ_u : ((B : Rat) + ((2 ^ J : Nat) : Rat) + ((2 ^ J : Nat) : Rat)) * wordScale (V :: (v ++ [V])) =
      ((k : Rat) + (carry : Rat)) * wordScale (V :: (v ++ [V])) := by rw [hQsum]
  rw [Nat.cast_add,Nat.cast_one,Nat.cast_add,Nat.cast_one]
  linarith
theorem loc_z2g (J k carry : Nat) (alpha unit delta R : Rat)
    (hPos : 0 < alpha) (hSmall : alpha <= 1 / 32) (hUnit : 0 < unit) (hTiny : unit <= alpha * (1 / 1024))
    (hHeight : unit * ((2 ^ J : Nat) : Rat) = 1)
    (hDl : (15 / 4) * alpha <= delta) (hDu : delta <= (17 / 4) * alpha)
    (hRl : alpha <= R) (hRu : R <= (5 / 4) * alpha)
    (hK : (k : Rat) * unit = 2 + 4 * unit - delta * (1 / 2))
    (hC : ((1 + carry : Nat) : Rat) * unit = 1 + R) :
    ∃ A B,A + 2 ^ J = k /\ B + 2 ^ J = A + carry /\
      2 ^ J <= A * 2 /\ A < 2 ^ J /\ 2 ^ J <= B * 2 /\ B < 2 ^ J := by
  rw [Nat.cast_add,Nat.cast_one] at hC
  have hH' : ((2 ^ J : Nat) : Rat) * unit = 1 := by linarith
  have hK_u : ((2 ^ J : Nat) : Rat) * unit <= (k : Rat) * unit := by linarith
  have hK_q : ((2 ^ J : Nat) : Rat) <= (k : Rat) := le_of_mul_le_mul_pos_right hUnit hK_u
  have hKnat : 2 ^ J <= k := by exact_mod_cast hK_q
  have hB_u : (((2 ^ J + 2 ^ J : Nat) : Rat)) * unit <= ((k + carry : Nat) : Rat) * unit := by
    rw [Nat.cast_add,Nat.cast_add]; linarith
  have hB_q : ((2 ^ J + 2 ^ J : Nat) : Rat) <= ((k + carry : Nat) : Rat) := le_of_mul_le_mul_pos_right hUnit hB_u
  have hBnat : 2 ^ J + 2 ^ J <= k + carry := by exact_mod_cast hB_q
  refine ⟨k - 2 ^ J,k + carry - (2 ^ J + 2 ^ J),by omega,by omega,?_,?_,?_,?_⟩
  · have hq_u : ((2 ^ J : Nat) : Rat) * unit <= (((k - 2 ^ J) * 2 : Nat) : Rat) * unit := by
      rw [Nat.cast_mul,Nat.cast_sub hKnat,Nat.cast_ofNat]; linarith
    have hq := le_of_mul_le_mul_pos_right hUnit hq_u
    exact_mod_cast hq
  · have hq_u : ((k - 2 ^ J : Nat) : Rat) * unit < ((2 ^ J : Nat) : Rat) * unit := by
      rw [Nat.cast_sub hKnat]; linarith
    have hq := lt_of_mul_lt_mul_pos_right hUnit hq_u
    exact_mod_cast hq
  · have hq_u : ((2 ^ J : Nat) : Rat) * unit <= (((k + carry - (2 ^ J + 2 ^ J)) * 2 : Nat) : Rat) * unit := by
      rw [Nat.cast_mul,Nat.cast_sub hBnat,Nat.cast_add,Nat.cast_add,Nat.cast_ofNat]; linarith
    have hq := le_of_mul_le_mul_pos_right hUnit hq_u
    exact_mod_cast hq
  · have hq_u : ((k + carry - (2 ^ J + 2 ^ J) : Nat) : Rat) * unit < ((2 ^ J : Nat) : Rat) * unit := by
      rw [Nat.cast_sub hBnat,Nat.cast_add,Nat.cast_add]; linarith
    have hq := lt_of_mul_lt_mul_pos_right hUnit hq_u
    exact_mod_cast hq
inductive loc_Reserve : Nat -> Rat -> Prop where
  | even (n : Nat) (tau : Rat) : tau * ((2 ^ n : Nat) : Rat) = 8 -> loc_Reserve (n * 2) tau
  | odd (n : Nat) (tau : Rat) : tau * ((2 ^ n : Nat) : Rat) = 6 -> loc_Reserve (1 + n * 2) tau
theorem loc_z2h {p : Nat} {tau : Rat} (hI : loc_Reserve p tau) :
    ∃ tau',loc_Reserve (1 + p) tau' /\ tau' <= (3 / 4) * tau := by
  cases hI with
  | @even n tau hEq =>
    exact ⟨(3 / 4) * tau,loc_Reserve.odd n ((3 / 4) * tau) (by linarith),by linarith⟩
  | @odd n tau hEq =>
    have hpos := loc_z1O n
    have htau : 0 <= tau := by nlinarith
    refine ⟨(2 / 3) * tau,?_,by linarith⟩
    have heq : 1 + (1 + n * 2) = (1 + n) * 2 := by omega
    rw [heq]
    refine loc_Reserve.even (1 + n) ((2 / 3) * tau) ?_
    rw [pow_two_one_add,Nat.cast_add]; linarith
theorem loc_z2i {p : Nat} {tau : Rat} (hI : loc_Reserve p tau) (hP : 16 <= p) :
    0 < tau /\ tau <= 1 / 32 := by
  cases hI with
  | @even n tau hEq =>
    have hpos := loc_z1O n
    have hBound_nat : 2 ^ 8 <= 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    have hBound : (256 : Rat) <= ((2 ^ n : Nat) : Rat) := by exact_mod_cast hBound_nat
    exact ⟨by nlinarith,by nlinarith⟩
  | @odd n tau hEq =>
    have hpos := loc_z1O n
    have hBound_nat : 2 ^ 8 <= 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    have hBound : (256 : Rat) <= ((2 ^ n : Nat) : Rat) := by exact_mod_cast hBound_nat
    exact ⟨by nlinarith,by nlinarith⟩
theorem loc_z2j (p n H s : Nat)
    (hN : 8 <= n) (hP : p = n * 2 \/ p = 1 + n * 2)
    (hS : s = (p - 2) / 2) (hH : p + p / 2 + 9 <= H) :
    4 * ((2 ^ n : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) /\
    4 * ((2 ^ p : Nat) : Rat) * ((2 ^ n : Nat) : Rat) <= ((2 ^ H : Nat) : Rat) := by
  refine ⟨?_,?_⟩
  · have hle : 2 ^ (2 + n) <= 2 ^ (s + s / 2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hq : ((2 ^ (2 + n) : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) := by exact_mod_cast hle
    rw [loc_z28 2 n,loc_z29] at hq
    linarith
  · have hle : 2 ^ (2 + p + n) <= 2 ^ H :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hq : ((2 ^ (2 + p + n) : Nat) : Rat) <= ((2 ^ H : Nat) : Rat) := by exact_mod_cast hle
    rw [loc_z28 (2 + p) n,loc_z28 2 p,loc_z29] at hq
    linarith
theorem loc_z2k (alpha unit f t0 q tau : Rat)
    (ht0 : 0 < t0) (_ : 0 <= alpha) (_ : 0 <= unit)
    (hGap : 4 * t0 * unit <= alpha) (hLow : 4 * t0 <= q)
    (hF : f * q <= unit * q + 5 * alpha) (hTau : 6 <= tau * t0) :
    f <= alpha * tau * (1 / 4) := by
  rcases le_or_gt f unit with hle | hgt
  · have h1 : alpha * 6 <= alpha * (tau * t0) := by nlinarith
    have h2 : unit * (4 * t0) <= (alpha * tau * (1 / 4)) * (4 * t0) := by linarith
    have h3 : unit <= alpha * tau * (1 / 4) := le_of_mul_le_mul_pos_right (by linarith) h2
    linarith
  · have h1 : (f - unit) * (4 * t0) <= (f - unit) * q := by nlinarith
    have h2 : alpha * 6 <= alpha * (tau * t0) := by nlinarith
    have h3 : f * (4 * t0) <= (alpha * tau * (1 / 4)) * (4 * t0) := by linarith
    exact le_of_mul_le_mul_pos_right (by linarith) h3
theorem loc_z2l (t0 q h alpha unit : Rat)
    (hQ : 0 < q) (_ : 0 <= unit)
    (hAq : alpha * q = 1) (hUh : unit * h = 1)
    (hLe : 4 * q * t0 <= h) :
    4 * t0 * unit <= alpha := by
  have h1 : (4 * q * t0) * unit <= h * unit := by nlinarith
  have h2 : (4 * t0 * unit) * q <= alpha * q := by linarith
  exact le_of_mul_le_mul_pos_right hQ h2
theorem loc_z2m (p H s : Nat) (alpha unit tau f : Rat)
    (hI : loc_Reserve p tau) (hP : 16 <= p) (hH : p + p / 2 + 9 <= H) (hS : s = (p - 2) / 2)
    (hA : 0 < alpha) (hU : 0 < unit)
    (hAp : alpha * ((2 ^ p : Nat) : Rat) = 1) (hUh : unit * ((2 ^ H : Nat) : Rat) = 1)
    (hF : f * ((2 ^ (s + s / 2) : Nat) : Rat) <= unit * ((2 ^ (s + s / 2) : Nat) : Rat) + 5 * alpha) :
    f <= alpha * tau * (1 / 4) := by
  cases hI with
  | @even n tau hTau =>
    rcases loc_z2j (n * 2) n H s (by omega) (Or.inl rfl) hS hH with ⟨hLow,hHigh⟩
    have hpos := loc_z1O n
    have hposP := loc_z1O (n * 2)
    have hGap := loc_z2l ((2 ^ n : Nat) : Rat) ((2 ^ (n * 2) : Nat) : Rat) ((2 ^ H : Nat) : Rat)
      alpha unit hposP (by linarith) hAp hUh (by linarith)
    exact loc_z2k alpha unit f ((2 ^ n : Nat) : Rat) ((2 ^ (s + s / 2) : Nat) : Rat) tau
      hpos (by linarith) (by linarith) hGap hLow hF (by linarith)
  | @odd n tau hTau =>
    rcases loc_z2j (1 + n * 2) n H s (by omega) (Or.inr rfl) hS hH with ⟨hLow,hHigh⟩
    have hpos := loc_z1O n
    have hposP := loc_z1O (1 + n * 2)
    have hGap := loc_z2l ((2 ^ n : Nat) : Rat) ((2 ^ (1 + n * 2) : Nat) : Rat) ((2 ^ H : Nat) : Rat)
      alpha unit hposP (by linarith) hAp hUh (by linarith)
    exact loc_z2k alpha unit f ((2 ^ n : Nat) : Rat) ((2 ^ (s + s / 2) : Nat) : Rat) tau
      hpos (by linarith) (by linarith) hGap hLow hF (by linarith)
theorem loc_z2n (p : Nat) (hP : 16 <= p) :
    (p + 1) + (p + 1) / 2 + 9 <= 1 + 3 * (((p - 2) / 2 + 1) / 2) + 3 * ((p - 1) / 2) := by
  omega
theorem loc_z2o (alpha tau tau' e f e' : Rat)
    (_ : 0 <= alpha) (_ : tau' <= (3 / 4) * tau)
    (_ : e <= alpha * ((3 / 64) - tau)) (_ : f <= alpha * tau * (1 / 4))
    (_ : e' <= (e + f) * (1 / 2)) :
    e' <= (alpha * (1 / 2)) * ((3 / 64) - tau') := by
  nlinarith
theorem loc_z2p {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : PhaseScan k u k' v a b) :
    ∃ g,wordScale u = wordScale v * ((8 ^ g : Nat) : Rat) /\ u.length = v.length + g := by
  induction hI with
  | nil _ => exact ⟨0,by simp [wordScale],rfl⟩
  | T _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [wordScale]; rw [hE]; ring,by dsimp; omega⟩
  | pair0 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    refine ⟨1 + g,?_,by dsimp; omega⟩
    have h8 : ((8 ^ (1 + g) : Nat) : Rat) = 8 * ((8 ^ g : Nat) : Rat) := by
      rw [Nat.add_comm 1 g,Nat.pow_succ]; push_cast; ring
    dsimp [wordScale]; rw [h8,hE]; ring
  | pair1 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    refine ⟨1 + g,?_,by dsimp; omega⟩
    have h8 : ((8 ^ (1 + g) : Nat) : Rat) = 8 * ((8 ^ g : Nat) : Rat) := by
      rw [Nat.add_comm 1 g,Nat.pow_succ]; push_cast; ring
    dsimp [wordScale]; rw [h8,hE]; ring
  | short00 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [wordScale]; rw [hE]; ring,by dsimp; omega⟩
  | short01 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [wordScale]; rw [hE]; ring,by dsimp; omega⟩
  | short10 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [wordScale]; rw [hE]; ring,by dsimp; omega⟩
  | short11 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [wordScale]; rw [hE]; ring,by dsimp; omega⟩
theorem loc_z2q {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : PhaseScan k u k' v a b) : v.length <= u.length := by
  rcases loc_z2p hI with ⟨g,_,hL⟩
  omega
theorem loc_z2r (c k k' : Nat) (v : WordList) (l : Rat)
    (hC : 0 < c) (hI : Scan k (List.replicate c Q ++ [K]) k' v l) :
    v.length + (c + 1) / 2 = c + 1 := by
  rcases even_or_odd_mul_two c with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · cases r with
    | zero => omega
    | succ r =>
      have heq : (r + 1) * 2 = 2 + r * 2 := by omega
      rw [heq] at hI
      rcases scan_even_Q_K_inv r k k' v l hI with ⟨d,n,rfl,_,_⟩
      simp; try omega
  · rcases scan_odd_Q_K_inv r k k' v l hI with ⟨rfl,_,_⟩
    simp; try omega
theorem loc_z2s (c k k' : Nat) (v : WordList) (a b : Rat)
    (hC : 0 < c) (hI : PhaseScan k (List.replicate c Q ++ [K]) k' v a b) :
    v.length + (c + 1) / 2 = c + 1 := by
  have hD := digitVal_append (digitVal_replicate_Q c) (DigitVal.zero DigitVal.nil)
  rcases phaseScan_digitVal_loss_bound hI hD with ⟨l,hJ,_,_⟩
  exact loc_z2r c k k' v l hC hJ
theorem loc_z2t (k : Nat) (u : WordList) (c : Nat) (mid : WordList) (t0 k' : Nat) (v : WordList) (a b : Rat)
    (hC : 0 < c) (hT : 0 < t0) (hU : notEndsWithQ u = true) (hM : notEndsWithQ mid = true)
    (hI : PhaseScan k (u ++ List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K])) k' v a b) :
    ∃ g,wordScale (u ++ List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K])) =
      wordScale v * ((8 ^ g : Nat) : Rat) /\ (c + 1) / 2 + (t0 + 1) / 2 <= g := by
  rcases loc_z2p hI with ⟨g,hG,hL⟩
  refine ⟨g,hG,?_⟩
  have hE0 : u ++ List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K]) =
      u ++ (List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K])) := by
    simp [List.append_assoc]
  rw [hE0] at hI
  rcases phaseScan_split_of_splitCond hI u _ rfl (Or.inl hU) with ⟨m,x,y,_,_,_,_,hJ,hK,hV,_,_⟩
  have hSplit : List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K]) =
      (List.replicate c Q ++ [K]) ++ (mid ++ (List.replicate t0 Q ++ [K])) := by
    simp [List.append_assoc]
  have hCut1 : SplitCond (List.replicate c Q ++ [K]) (mid ++ (List.replicate t0 Q ++ [K])) := by
    left; rw [notEndsWithQ_append_singleton]; rfl
  rcases phaseScan_split_of_splitCond hK _ _ hSplit hCut1 with ⟨m1,x1,y1,_,_,_,_,hJ1,hK1,hV1,_,_⟩
  rcases phaseScan_split_of_splitCond hK1 mid (List.replicate t0 Q ++ [K]) rfl (Or.inl hM)
    with ⟨m2,x2,y2,_,_,_,_,hJ2,hK2,hV2,_,_⟩
  have hL_x := loc_z2q hJ
  have hL_x2 := loc_z2q hJ2
  have hL_x1 := loc_z2s c m m1 x1 _ _ hC hJ1
  have hL_y2 := loc_z2s t0 m2 k' y2 _ _ hT hK2
  rw [hV,hV1,hV2] at hL
  simp only [List.length_append,List.length_cons,List.length_replicate,List.length_nil] at hL hL_x1 hL_y2
  omega
theorem loc_z2u (n : Nat) : 8 ^ n = 2 ^ (3 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq : 3 * (n + 1) = 3 * n + 3 := by omega
    rw [Nat.pow_succ,heq,Nat.pow_add,ih]
theorem loc_z2v (u ds : WordList) (A H k k' : Nat) (v : WordList) (a b : Rat)
    (p c : Nat) (mid : WordList) (t0 : Nat)
    (hD : DigitVal A H ds) (hHeight : wordScale u * ((2 ^ H : Nat) : Rat) = 1)
    (hI : PhaseScan k (u ++ ds ++ [K]) k' v a b)
    (hU : notEndsWithQ u = true) (hM : notEndsWithQ mid = true)
    (hDs : ds = List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q))
    (hP : 16 <= p) (hC : (p - 2) / 2 <= c) (hT : p - 2 <= t0) :
    ∃ J,(p + 1) + (p + 1) / 2 + 9 <= J /\ wordScale (V :: (v ++ [V])) * ((2 ^ J : Nat) : Rat) = 1 := by
  have hEq : u ++ ds ++ [K] = u ++ List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K]) := by
    rw [hDs]; simp [List.append_assoc]
  have hI' : PhaseScan k (u ++ List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K])) k' v a b := by
    rwa [<- hEq]
  rcases loc_z2t k u c mid t0 k' v a b (by omega) (by omega) hU hM hI' with ⟨g,hGain,hCount⟩
  rw [<- hEq] at hGain
  refine ⟨1 + 3 * g,?_,?_⟩
  · have hArith := loc_z2n p hP
    omega
  · have hWidth := (digitVal_scale_and_mass hD).1
    have hG1 : wordScale (u ++ ds ++ [K]) = wordScale u * wordScale ds * 2 := by
      rw [wordScale_append,wordScale_append]; dsimp [wordScale]; ring
    rw [hG1] at hGain
    have hG2 : wordScale (V :: (v ++ [V])) = wordScale v * (1 / 4) := by
      dsimp [wordScale]; rw [wordScale_append]; dsimp [wordScale]; ring
    rw [hG2,pow_two_one_add,<- loc_z2u,Nat.cast_add]
    calc wordScale v * (1 / 4) * (((8 ^ g : Nat) : Rat) + ((8 ^ g : Nat) : Rat))
      _ = (wordScale v * ((8 ^ g : Nat) : Rat)) * (1 / 2) := by ring
      _ = (wordScale u * wordScale ds * 2) * (1 / 2) := by rw [<- hGain]
      _ = wordScale u * wordScale ds := by ring
      _ = wordScale u * ((2 ^ H : Nat) : Rat) := by rw [hWidth]
      _ = 1 := hHeight
theorem loc_z2w (p H : Nat) (alpha unit : Rat)
    (hPH : p + 10 <= H) (hA : 0 < alpha) (hU : 0 < unit)
    (hAp : alpha * ((2 ^ p : Nat) : Rat) = 1) (hUh : unit * ((2 ^ H : Nat) : Rat) = 1) :
    unit <= alpha * (1 / 1024) := by
  have hHigh_nat : 2 ^ (p + 10) <= 2 ^ H := Nat.pow_le_pow_right (by decide) hPH
  have hHigh_q : ((2 ^ (p + 10) : Nat) : Rat) <= ((2 ^ H : Nat) : Rat) := by exact_mod_cast hHigh_nat
  rw [loc_z28 p 10,loc_z2a] at hHigh_q
  have h1 : unit * (((2 ^ p : Nat) : Rat) * 1024) <= unit * ((2 ^ H : Nat) : Rat) := by nlinarith
  have h2 : unit * ((2 ^ p : Nat) : Rat) <= (alpha * (1 / 1024)) * ((2 ^ p : Nat) : Rat) := by linarith
  exact le_of_mul_le_mul_pos_right (loc_z1O p) h2
theorem loc_z2x (p J : Nat) (alpha unit : Rat)
    (hP : 16 <= p) (hJ : (p + 1) + (p + 1) / 2 + 9 <= J)
    (hA : 0 < alpha) (hU : 0 < unit)
    (hAp : alpha * ((2 ^ p : Nat) : Rat) = 1) (hUj : unit * ((2 ^ J : Nat) : Rat) = 1) :
    unit <= alpha * (1 / 1024) :=
  loc_z2w p J alpha unit (by omega) hA hU hAp hUj
theorem loc_z2y (p H : Nat) (alpha unit : Rat)
    (hPH : p <= H) (hA : alpha * ((2 ^ p : Nat) : Rat) = 1) (hU : unit * ((2 ^ H : Nat) : Rat) = 1) :
    unit * ((2 ^ (H - p) : Nat) : Rat) = alpha := by
  have hPos := loc_z1O p
  have hEq : 2 ^ H = 2 ^ (H - p) * 2 ^ p := by rw [<- Nat.pow_add,Nat.sub_add_cancel hPH]
  have hEq_q : ((2 ^ H : Nat) : Rat) = ((2 ^ (H - p) : Nat) : Rat) * ((2 ^ p : Nat) : Rat) := by
    rw [hEq,Nat.cast_mul]
  rw [hEq_q] at hU
  have hle1 := le_of_mul_le_mul_pos_right hPos (show (unit * ((2 ^ (H - p) : Nat) : Rat)) * ((2 ^ p : Nat) : Rat) <= alpha * ((2 ^ p : Nat) : Rat) by linarith)
  have hle2 := le_of_mul_le_mul_pos_right hPos (show alpha * ((2 ^ p : Nat) : Rat) <= (unit * ((2 ^ (H - p) : Nat) : Rat)) * ((2 ^ p : Nat) : Rat) by linarith)
  linarith
theorem loc_z2z (n t0 B : Nat) (ds : WordList)
    (hD : DigitVal B (n + t0) ds) (hL : 2 ^ (n + t0) <= B + 2 ^ n) :
    ∃ u,ds = u ++ List.replicate t0 Q := by
  have hBound := lt_pow_of_digitVal hD
  have hPos := pow_two_pos t0
  rw [Nat.pow_add] at hL hBound
  let a := B - (2 ^ t0 - 1) * 2 ^ n
  have hSum : a + (2 ^ t0 - 1) * 2 ^ n = B := by
    have : (2 ^ t0 - 1) * 2 ^ n + 2 ^ n = 2 ^ n * 2 ^ t0 := by
      have h1 : (2 ^ t0 - 1) + 1 = 2 ^ t0 := by omega
      calc (2 ^ t0 - 1) * 2 ^ n + 2 ^ n
        _ = ((2 ^ t0 - 1) + 1) * 2 ^ n := by ring
        _ = 2 ^ t0 * 2 ^ n := by rw [h1]
        _ = 2 ^ n * 2 ^ t0 := by ring
    omega
  have ha_lt : a < 2 ^ n := by
    have : (2 ^ t0 - 1) * 2 ^ n + 2 ^ n = 2 ^ n * 2 ^ t0 := by
      have h1 : (2 ^ t0 - 1) + 1 = 2 ^ t0 := by omega
      calc (2 ^ t0 - 1) * 2 ^ n + 2 ^ n
        _ = ((2 ^ t0 - 1) + 1) * 2 ^ n := by ring
        _ = 2 ^ t0 * 2 ^ n := by rw [h1]
        _ = 2 ^ n * 2 ^ t0 := by ring
    omega
  rcases exists_digitVal_of_lt_pow n a ha_lt with ⟨u,hU⟩
  refine ⟨u,digitVal_unique hD ?_⟩
  rw [<- hSum]
  exact digitVal_append hU (digitVal_replicate_Q t0)
theorem loc_z2A (p H B : Nat) (ds : WordList) (alpha unit : Rat)
    (hD : DigitVal B H ds) (hP : 2 <= p) (hPH : p <= H)
    (_ : 0 < alpha) (hU : 0 < unit) (_ : unit <= alpha)
    (hAp : alpha * ((2 ^ p : Nat) : Rat) = 1) (hUh : unit * ((2 ^ H : Nat) : Rat) = 1)
    (hDeficit : unit * wordMassK ds <= (5 / 2) * alpha) :
    ∃ u,ds = u ++ List.replicate (p - 2) Q := by
  have hShift : unit * ((2 ^ (H - (p - 2)) : Nat) : Rat) = 4 * alpha := by
    have heq : H - (p - 2) = (H - p) + 2 := by omega
    rw [heq,loc_z28 (H - p) 2,loc_z29]
    have hd := loc_z2y p H alpha unit hPH hAp hUh
    linarith
  have hZ := digitVal_wordMassK_eq hD
  have hH_split : (H - (p - 2)) + (p - 2) = H := by omega
  have hD' : DigitVal B ((H - (p - 2)) + (p - 2)) ds := by rwa [hH_split]
  apply loc_z2z (H - (p - 2)) (p - 2) B ds hD'
  have hZ_u : (B : Rat) * unit + unit + unit * wordMassK ds = 1 := by
    calc (B : Rat) * unit + unit + unit * wordMassK ds
      _ = unit * (wordMassK ds + (B : Rat) + 1) := by ring
      _ = unit * ((2 ^ H : Nat) : Rat) := by rw [hZ]
      _ = 1 := hUh
  have hL_u : ((2 ^ H : Nat) : Rat) * unit <= ((B + 2 ^ (H - (p - 2)) : Nat) : Rat) * unit := by
    rw [Nat.cast_add]; linarith
  have hL_q : ((2 ^ ((H - (p - 2)) + (p - 2)) : Nat) : Rat) <= ((B + 2 ^ (H - (p - 2)) : Nat) : Rat) := by
    rw [hH_split]
    exact le_of_mul_le_mul_pos_right hU hL_u
  exact_mod_cast hL_q
theorem loc_z2B {B H : Nat} {ds : WordList} (hI : DigitVal B H ds) (hZ : 0 < wordMassK ds) :
    ∃ c w,ds = List.replicate c Q ++ K :: w := by
  induction hI with
  | nil => dsimp [wordMassK] at hZ; linarith
  | @zero A H u _ _ => exact ⟨0,u,rfl⟩
  | @one A H u _ ih =>
    dsimp [wordMassK] at hZ
    rcases ih (by linarith) with ⟨c,w,rfl⟩
    exact ⟨c + 1,w,rfl⟩
theorem loc_z2C (c : Nat) :
    ∀ (s : Nat) (u v : WordList),
      List.replicate s Q ++ u = List.replicate c Q ++ K :: v -> s <= c := by
  induction c with
  | zero =>
    intro s u v hE
    cases s with
    | zero => omega
    | succ s => nomatch hE
  | succ c ih =>
    intro s u v hE
    cases s with
    | zero => omega
    | succ s =>
      dsimp [List.replicate] at hE
      injection hE with _ hE'
      have h := ih s u v hE'
      omega
theorem loc_z2D (u v : WordList) (c s : Nat)
    (hC : notEndsWithQ u = true)
    (hE : u ++ List.replicate c Q = v ++ List.replicate s Q) : s <= c := by
  by_contra hGt
  have hlt : c < s := by omega
  have h_eq : s = (s - c) + c := by omega
  rw [h_eq,List.replicate_add,<- List.append_assoc] at hE
  have hU := List.append_inj_left' hE rfl
  subst hU
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : s - c ≠ 0) with ⟨n,hn⟩
  rw [hn,replicate_succ_append,<- List.append_assoc,notEndsWithQ_append_singleton] at hC
  contradiction
theorem loc_z2E (u v : WordList) (h : notEndsWithQ (u ++ v) = true) : notEndsWithQ v = true := by
  induction u with
  | nil => exact h
  | cons w u ih => exact ih (notEndsWithQ_of_cons w (u ++ v) h)
theorem loc_z2F {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (hI : WordEffect n u b v) (hEnd : ∃ w,u = w ++ [V]) :
    ∃ w,v = w ++ [V] := by
  rcases hEnd with ⟨w,rfl⟩
  rcases wordEffect_append_replicate_V_inv w 1 n b v hI with ⟨x,m,hE,_⟩
  exact ⟨x,hE⟩
theorem loc_z2G (p : Nat) (u : WordList) :
    wordMass (List.replicate p V ++ Q :: u) = wordScale (List.replicate p V) * (1 + 2 * wordMass u) := by
  rw [wordMass_append]
  dsimp [wordMass]
  have h := (loc_z1P p).1
  linarith
theorem loc_z2H (p : Nat) (hP : 16 <= p) :
    wordScale (List.replicate p V) <= 1 / 65536 := by
  have h1 := (loc_z1P p).2
  have h2 := wordScale_pos (List.replicate p V)
  have hle : 2 ^ 16 <= 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
  have hq : (65536 : Rat) <= ((2 ^ p : Nat) : Rat) := by exact_mod_cast hle
  nlinarith
inductive Good : Nat -> WordList -> Prop where
  | intro (p H : Nat) (u : WordList) (A : Nat) (da : WordList) (carry : Nat) (eff : WordList)
      (B : Nat) (db : WordList) (tau : Rat) :
      16 <= p -> p + p / 2 + 9 <= H ->
      (∃ rest,u = List.replicate p V ++ Q :: rest) ->
      (∃ rest,u = rest ++ [V]) ->
      wordScale u * ((2 ^ H : Nat) : Rat) = 1 ->
      DigitVal A H da ->
      WordEffect 0 u carry eff ->
      A + carry = B + 2 ^ H ->
      DigitVal B H db ->
      loc_Reserve p tau ->
      wordMass u <= wordScale (List.replicate p V) * (1 + (3 / 64) - tau) ->
      (3 / 2) * wordScale (List.replicate p V) <= wordScale u * wordMassK db ->
      wordScale u * wordMassK db <= (5 / 2) * wordScale (List.replicate p V) ->
      (∃ rest,db = List.replicate ((p - 2) / 2) Q ++ rest) ->
      Good p (u ++ da ++ [Q])
inductive loc_Step : WordList -> WordList -> Prop where
  | intro (orig eff : WordList) (k : Nat) (v : WordList) (a b : Rat) (J A : Nat) (da : WordList) :
      WordEffect 0 orig 1 eff ->
      PhaseScan 12 eff k v a b ->
      DigitVal A J da ->
      A + 2 ^ J = k ->
      loc_Step orig (V :: (v ++ V :: (da ++ [Q])))
theorem loc_z2I (c : Nat) (mid : WordList) (hM : notEndsWithQ mid = true) :
    notEndsWithQ (List.replicate c Q ++ K :: mid) = true := by
  cases mid with
  | nil => rw [notEndsWithQ_append_singleton]; rfl
  | cons x xs =>
    induction c with
    | zero => exact hM
    | succ c ih =>
      cases c with
      | zero => exact hM
      | succ c' => exact ih
theorem loc_z2J {B H : Nat} {ds : WordList} {s t0 : Nat}
    (hD : DigitVal B H ds) (hZ : 0 < wordMassK ds)
    (hLo : ∃ u,ds = List.replicate s Q ++ u)
    (hHi : ∃ u,ds = u ++ List.replicate t0 Q) :
    ∃ c mid n,ds = List.replicate c Q ++ K :: (mid ++ List.replicate n Q) /\
      notEndsWithQ mid = true /\ s <= c /\ t0 <= n := by
  rcases hLo with ⟨lo,hLo_eq⟩
  rcases hHi with ⟨hi,hHi_eq⟩
  rcases loc_z2B hD hZ with ⟨c,w,hE⟩
  rcases split_trailing_Q w with ⟨mid,n,rfl,hM⟩
  refine ⟨c,mid,n,hE,hM,?_,?_⟩
  · apply loc_z2C c s lo (mid ++ List.replicate n Q)
    rw [<- hLo_eq,hE]
  · apply loc_z2D (List.replicate c Q ++ K :: mid) hi n t0 (loc_z2I c mid hM)
    have h1 : (List.replicate c Q ++ K :: mid) ++ List.replicate n Q =
        List.replicate c Q ++ K :: (mid ++ List.replicate n Q) := by
      simp [List.append_assoc]
    rw [h1,<- hE,hHi_eq]
theorem loc_z2K (p : Nat) (u : WordList) (carry : Nat) (eff : WordList)
    (hP : 0 < p) (hE : WordEffect 0 (List.replicate p V ++ Q :: u) carry eff) :
    ∃ v,eff = List.replicate p V ++ K :: v := by
  cases p with
  | zero => omega
  | succ p =>
    have heq : p + 1 = 1 + p := by omega
    rw [heq] at hE ⊢
    rcases loc_z23 p u carry eff hE with ⟨v,hV,_⟩
    exact ⟨v,hV⟩
theorem loc_z2L {p : Nat} {orig : WordList} (hI : Good p orig) :
    ∃ out,loc_Step orig out /\ Good (1 + p) out := by
  rcases hI with ⟨H,u,A,da,carry,eff,B,db,tau,
    hP,hHbound,⟨rest,hStart⟩,hEnd,hHeight,hDA,hEff,hSum,hDB,hRes,hM,hDlo,hDhi,hLow⟩
  let alpha := wordScale (List.replicate p V)
  let unit := wordScale u
  have hAlpha : 0 < alpha := wordScale_pos (List.replicate p V)
  have hUnit : 0 < unit := wordScale_pos u
  have hAp : alpha * ((2 ^ p : Nat) : Rat) = 1 := (loc_z1P p).2
  have hAsmall : alpha <= 1 / 65536 := loc_z2H p hP
  rcases loc_z2i hRes hP with ⟨hTau,hTauSmall⟩
  have hUsmall : unit <= alpha * (1 / 1024) :=
    loc_z2w p H alpha unit (by omega) hAlpha hUnit hAp hHeight
  rcases wordEffect_preserves_scale_and_mass hEff with ⟨hEffScale,hEffMass⟩
  rcases loc_z2F hEff hEnd with ⟨last,hElast⟩
  have hCut : notEndsWithQ eff = true := by rw [hElast,notEndsWithQ_append_singleton]; rfl
  have hNe : eff ≠ [] := by rw [hElast]; simp
  have hEffHeight : wordScale eff * ((2 ^ H : Nat) : Rat) = 1 := by rw [hEffScale]; exact hHeight
  have hEffBound : wordMass eff + wordScale eff * (1 + wordMassK db) <= 1 / 128 := by
    rw [hEffScale,hEffMass]
    change wordMass u + unit * (1 + wordMassK db) <= 1 / 128
    have : unit * wordMassK db <= (5 / 2) * alpha := hDhi
    have : wordMass u <= alpha * (1 + (3 / 64) - tau) := hM
    nlinarith
  rcases loc_z1N eff B H db hDB hEffHeight hCut hNe hEffBound with ⟨k,v,a,b,hIscan,hK⟩
  have hZ : 0 < wordMassK db := by
    have : (3 / 2) * alpha <= unit * wordMassK db := hDlo
    nlinarith
  rcases loc_z2A p H B db alpha unit hDB (by omega) (by omega)
    hAlpha hUnit (by linarith) hAp hHeight hDhi with ⟨hi,hHi⟩
  rcases loc_z2J hDB hZ hLow ⟨hi,hHi⟩ with ⟨c,mid,t0,hSplit,hMidCut,hC,hT⟩
  rcases loc_z2v eff db B H 12 k v a b p c mid t0 hDB hEffHeight hIscan
    hCut hMidCut hSplit hP hC hT with ⟨J,hJbound,hJheight⟩
  let new := V :: (v ++ [V])
  let nu := wordScale new
  have hNu : 0 < nu := wordScale_pos new
  have hNuSmall : nu <= alpha * (1 / 1024) :=
    loc_z2x p J alpha nu hP hJbound hAlpha hNu hAp hJheight
  have hEffStart : ∃ w,eff = List.replicate p V ++ K :: w := by
    rw [hStart] at hEff
    exact loc_z2K p rest carry eff (by omega) hEff
  rcases hEffStart with ⟨w,hEstart⟩
  have hWcut : notEndsWithQ w = true := by
    rw [hEstart] at hCut
    exact notEndsWithQ_of_cons K w (loc_z2E (List.replicate p V) (K :: w) hCut)
  let e := wordMass u - alpha
  have hEeq : e = 2 * alpha * wordMass w := by
    have h1 : wordMass eff = wordMass u := hEffMass
    rw [hEstart,wordMass_append] at h1
    dsimp [wordMass] at h1
    have h2 := (loc_z1P p).1
    change wordMass u - alpha = 2 * alpha * wordMass w
    linarith
  have hWw := wordMass_nonneg w
  have hMw : 0 <= wordMass w := hWw.1
  have hEpos : 0 <= e := by rw [hEeq]; positivity
  have hEbound : e <= alpha * ((3 / 64) - tau) := by
    change wordMass u - alpha <= alpha * ((3 / 64) - tau)
    linarith
  let s := (p - 2) / 2
  let pow := ((2 ^ (s + s / 2) : Nat) : Rat)
  have hPow : 0 < pow := loc_z1O (s + s / 2)
  let f := unit + 2 * unit * wordMassK db / pow
  have hFeq : f * pow = unit * pow + 2 * unit * wordMassK db := by
    change (unit + 2 * unit * wordMassK db / pow) * pow = unit * pow + 2 * unit * wordMassK db
    have hne : pow ≠ 0 := ne_of_gt hPow
    rw [add_mul,div_mul_cancel₀ _ hne]
  have hWdb := wordMass_nonneg db
  have hZdb : 0 <= wordMassK db := hWdb.2.1
  have hFpos : 0 <= f :=
    le_of_mul_le_mul_pos_right hPow (by nlinarith [hFeq,hPow,hUnit,hZdb])
  have hFbound : f <= alpha * tau * (1 / 4) := by
    apply loc_z2m p H s alpha unit tau f hRes hP hHbound rfl hAlpha hUnit hAp hHeight
    change f * pow <= unit * pow + 5 * alpha
    have : unit * wordMassK db <= (5 / 2) * alpha := hDhi
    linarith
  have hLow' : ∃ c w0,(0 < c /\ s <= c) /\ db = List.replicate c Q ++ K :: w0 :=
    ⟨c,mid ++ List.replicate t0 Q,⟨by omega,hC⟩,hSplit⟩
  have hFactor : 2 * alpha * wordScale w = unit := by
    have h1 : wordScale eff = unit := hEffScale
    rw [hEstart,wordScale_append] at h1
    dsimp [wordScale] at h1
    change 2 * alpha * wordScale w = unit
    have : wordScale (List.replicate p V) = alpha := rfl
    linarith
  have hScanStart : PhaseScan 12 (List.replicate p V ++ K :: (w ++ db ++ [K])) k v a b := by
    rw [hEstart] at hIscan
    simpa [List.append_assoc] using hIscan
  have hStageBound : (2 * alpha * wordScale w) * (pow + 2 * wordMassK db) <= f * pow := by
    rw [hFactor]; linarith
  rcases loc_z2b p w db B H k v a b s e f hScanStart hDB hWcut hLow' hEeq hStageBound
    with ⟨tail,hVstart,hMnext,hDl,hDu⟩
  rcases exists_wordEffect new 0 with ⟨carry',eff',hEff'⟩
  have hNewStart : new = List.replicate (1 + p) V ++ Q :: (tail ++ [V]) := by
    change V :: (v ++ [V]) = List.replicate (1 + p) V ++ Q :: (tail ++ [V])
    rw [hVstart,loc_z22]; simp [List.append_assoc]
  have hEff'_start : WordEffect 0 (List.replicate (1 + p) V ++ Q :: (tail ++ [V])) carry' eff' := by
    rwa [<- hNewStart]
  rcases loc_z2c p (tail ++ [V]) carry' eff' hEff'_start with ⟨hRlo0,hRhi0⟩
  rw [<- hNewStart] at hRlo0 hRhi0
  let R := ((1 + carry' : Nat) : Rat) * nu - 1
  have hScale1p : wordScale (List.replicate (1 + p) V) = alpha * (1 / 2) := by
    rw [loc_z22]; rfl
  have hRlo : alpha <= R := by
    rw [hScale1p] at hRlo0
    change 2 * (alpha * (1 / 2)) <= R at hRlo0
    linarith
  have hRhi : R <= 2 * wordMass new := hRhi0
  have hEnew : 0 <= wordMass new - alpha * (1 / 2) := by
    rw [hNewStart,loc_z2G,hScale1p]
    have hWt := wordMass_nonneg (tail ++ [V])
    nlinarith
  have hFtiny : f <= alpha * (1 / 128) := by nlinarith
  have hEtiny : e <= alpha * (3 / 64) := by nlinarith
  have hBudget := loc_z2e hIscan
  have hMnext' : wordMass new <= alpha * (1 / 2) + (e + f) * (1 / 2) := hMnext
  rcases loc_z2g J k carry' alpha nu (a - b) R hAlpha (by linarith)
    hNu hNuSmall hJheight (by linarith) (by linarith) hRlo (by linarith) hBudget (by change ((1 + carry' : Nat) : Rat) * nu = 1 + (((1 + carry' : Nat) : Rat) * nu - 1); ring)
    with ⟨A',B',hAsum,hBsum,hAl,hAu,hBl,hBu⟩
  rcases exists_digitVal_of_lt_pow J A' hAu with ⟨da',hDA'⟩
  rcases exists_digitVal_of_lt_pow J B' hBu with ⟨db',hDB'⟩
  rcases loc_z2h hRes with ⟨tau',hRes',hTauStep⟩
  have hMkeep := loc_z2o alpha tau tau' e f (wordMass new - alpha * (1 / 2))
    (by linarith) hTauStep hEbound hFbound (by linarith)
  rcases loc_z2d alpha e f nu (a - b) R (wordMass new - alpha * (1 / 2))
    hAlpha hEpos hFpos (by linarith) hEtiny hFtiny hNuSmall hEnew (by linarith)
    hRlo (by linarith) hDl hDu with ⟨hDkeepL,hDkeepU⟩
  have hDef := loc_z2f hIscan hJheight hAsum hBsum
  have hZnew := digitVal_wordMassK_eq hDB'
  have hDnew : nu * wordMassK db' = (a - b) * (1 / 2) - 4 * nu - R := by
    have h1 : 1 - ((1 + B' : Nat) : Rat) * nu = (a - b) * (1 / 2) - 4 * nu - R := hDef
    rw [Nat.cast_add,Nat.cast_one] at h1
    have h2 : nu * (wordMassK db' + (B' : Rat) + 1) = 1 := by
      rw [hZnew]; exact hJheight
    linarith
  have hLowNew : ∃ rest',db' = List.replicate (((1 + p) - 2) / 2) Q ++ rest' := by
    let r := ((1 + p) - 2) / 2 - 1
    have hHr1 : 1 + r = ((1 + p) - 2) / 2 := by omega
    have hHr2 : 1 + r * 2 <= p - 2 := by omega
    have hHighEnd : ∃ z,db = z ++ List.replicate (1 + r * 2) Q := by
      refine ⟨hi ++ List.replicate ((p - 2) - (1 + r * 2)) Q,?_⟩
      have heq_p : (p - 2) - (1 + r * 2) + (1 + r * 2) = p - 2 := by omega
      rw [hHi,List.append_assoc,<- List.replicate_add,heq_p]
    rcases hHighEnd with ⟨z,hHZ⟩
    have hSC : PhaseScan 12 ((eff ++ z) ++ List.replicate (1 + r * 2) Q ++ [K]) k v a b := by
      rw [hHZ] at hIscan
      simpa [List.append_assoc] using hIscan
    rcases loc_z25 r 12 (eff ++ z) k v a b carry' eff' A' B' J db'
      hSC hEff' hDB' (by omega) hAsum hBsum with ⟨z',hL⟩
    rw [hHr1] at hL
    exact ⟨z',hL⟩
  refine ⟨new ++ da' ++ [Q],?_,?_⟩
  · have hOut_eq : new ++ da' ++ [Q] = V :: (v ++ V :: (da' ++ [Q])) := by
      change V :: (v ++ [V]) ++ da' ++ [Q] = V :: (v ++ V :: (da' ++ [Q]))
      simp [List.append_assoc]
    rw [hOut_eq]
    rcases loc_z1L hDA hSum (lt_pow_of_digitVal hDB) with ⟨d,hDD,hEE⟩
    have hd_eq : d = db := digitVal_unique hDD hDB
    subst d
    have hFull : WordEffect 0 (u ++ da ++ [Q]) 1 (eff ++ db ++ [K]) := by
      simpa only [List.append_assoc] using wordEffect_append hEff hEE
    exact loc_Step.intro (u ++ da ++ [Q]) (eff ++ db ++ [K]) k v a b J A' da' hFull hIscan hDA' hAsum
  · refine Good.intro (1 + p) J new A' da' carry' eff' B' db' tau'
      (by omega) (by omega) ⟨tail ++ [V],hNewStart⟩ ⟨V :: v,rfl⟩ hJheight hDA' hEff'
      (by omega) hDB' hRes' ?_ ?_ ?_ hLowNew
    · rw [hScale1p]
      linarith
    · rw [hScale1p]
      change (3 / 2) * (alpha * (1 / 2)) <= nu * wordMassK db'
      linarith
    · rw [hScale1p]
      change nu * wordMassK db' <= (5 / 2) * (alpha * (1 / 2))
      linarith
theorem ne_of_beq_eq_false {a b : Nat} (h : (a == b) = false) : a ≠ b := by
  intro heq; subst heq; rw [beq_self_eq_true] at h; contradiction
def loc_z2M : Word -> Bool
  | V => false
  | _ => true
theorem loc_z2N (ds : WordList) (h : ds.all loc_z2M = true) :
    ∃ A,DigitVal A ds.length ds := by
  induction ds with
  | nil => exact ⟨0,DigitVal.nil⟩
  | cons w ds ih =>
    cases w
    · contradiction
    · dsimp [List.all,loc_z2M] at h
      rcases ih h with ⟨A,hI⟩
      have heq : (K :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨A * 2,DigitVal.zero hI⟩
    · dsimp [List.all,loc_z2M] at h
      rcases ih h with ⟨A,hI⟩
      have heq : (Q :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨1 + A * 2,DigitVal.one hI⟩
theorem loc_z2O {A H : Nat} {u : WordList} (hI : DigitVal A H u) :
    u.all loc_z2M = true := by
  induction hI with
  | nil => rfl
  | zero _ ih => exact ih
  | one _ ih => exact ih
def loc_z2P (e : Bool) (n : Nat) : Nat := if e then 1 + n * 2 else n * 2
def loc_z2Q (e : Bool) : Word := if e then Q else K
def loc_z2R (w : Word) (n : Nat) : Word × Nat :=
  match w with
  | V => (V,1 + n * 2)
  | K => (if n % 2 == 0 then K else Q,n / 2)
  | Q =>
    let m := n + 1
    (if m % 2 == 0 then K else Q,m / 2)
theorem loc_z2S (w : Word) (n : Nat) (d : Word) (m : Nat)
    (hE : loc_z2R w n = (d,m)) :
    ∀ {u : WordList} {b : Nat} {v : WordList},
      WordEffect m u b v -> WordEffect n (w :: u) b (d :: v) := by
  intro u b v hI
  cases w with
  | V =>
    dsimp [loc_z2R] at hE
    injection hE with hd hm; subst hd hm
    exact WordEffect.T hI
  | K =>
    dsimp [loc_z2R] at hE
    injection hE with hd hm; subst hd hm
    rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
    · have hcond : (n % 2 == 0) = true := beq_iff_eq.mpr hmod
      rw [hcond]
      have h1 := WordEffect.d00 hI
      have heq : (n / 2) * 2 = n := by omega
      rwa [heq] at h1
    · have hcond : (n % 2 == 0) = false := beq_false_of_ne (by omega)
      rw [hcond]
      have h1 := WordEffect.d01 hI
      have heq : 1 + (n / 2) * 2 = n := by omega
      rwa [heq] at h1
  | Q =>
    dsimp [loc_z2R] at hE
    injection hE with hd hm; subst hd hm
    rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
    · have hcond : ((n + 1) % 2 == 0) = false := beq_false_of_ne (by omega)
      rw [hcond]
      have hm_eq : (n + 1) / 2 = n / 2 := by omega
      rw [hm_eq] at hI
      have h1 := WordEffect.d10 hI
      have heq : (n / 2) * 2 = n := by omega
      rwa [heq] at h1
    · have hcond : ((n + 1) % 2 == 0) = true := beq_iff_eq.mpr (by omega)
      rw [hcond]
      have hm_eq : (n + 1) / 2 = 1 + n / 2 := by omega
      rw [hm_eq] at hI
      have h1 := WordEffect.d11 hI
      have heq : 1 + (n / 2) * 2 = n := by omega
      rwa [heq] at h1
def forceLit {α : Type} (n : Nat) (k : Nat -> α) : α :=
  Nat.casesOn n (k 0) (fun m => k (Nat.succ m))
@[simp] theorem forceLit_eq {α : Type} (n : Nat) (k : Nat -> α) : forceLit n k = k n := by
  cases n <;> rfl
def strictWord {α : Type} (w : Word) (k : Word -> α) : α :=
  Word.casesOn w (k V) (k K) (k Q)
@[simp] theorem strictWord_eq {α : Type} (w : Word) (k : Word -> α) : strictWord w k = k w := by
  cases w <;> rfl
def loc_z2T : WordList -> Nat -> WordList -> Nat × WordList
  | [],n,acc => (n,acc.reverseAux [])
  | w :: u,n,acc =>
    let (d,m) := loc_z2R w n
    strictWord d (fun d' => forceLit m (fun m' => loc_z2T u m' (d' :: acc)))
theorem loc_z2U (u : WordList) :
    ∀ (n : Nat) (acc : WordList) (b : Nat) (out : WordList),
      loc_z2T u n acc = (b,out) ->
      ∃ v,out = acc.reverseAux v /\ WordEffect n u b v := by
  induction u with
  | nil =>
    intro n acc b out hE
    dsimp [loc_z2T] at hE
    injection hE with hb hout; subst hb hout
    exact ⟨[],rfl,WordEffect.nil n⟩
  | cons w u ih =>
    intro n acc b out hE
    dsimp [loc_z2T] at hE
    generalize hC : loc_z2R w n = dm at hE
    rcases dm with ⟨d,m⟩
    simp only [strictWord_eq, forceLit_eq] at hE
    rcases ih m (d :: acc) b out hE with ⟨v,rfl,hI⟩
    exact ⟨d :: v,rfl,loc_z2S w n d m hC hI⟩
def loc_z2V (e : Bool) (k : Nat) : Option (Word × Nat) :=
  if k == 0 then none
  else if k % 2 == 0 then
    if k % 4 == 2 then
      some (K,loc_z2P e (k / 4))
    else
      some (Q,loc_z2P e (k / 4 - 1))
  else none
theorem loc_z2W (e : Bool) (k : Nat) (d : Word) (k' : Nat) (u : WordList) (c : Nat) (v : WordList) (a b : Rat)
    (hS : loc_z2V e k = some (d,k')) (hI : PhaseScan k' u c v a b) :
    ∃ x y,PhaseScan k (loc_z2Q e :: u) c (d :: v) x y := by
  dsimp [loc_z2V] at hS
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
        injection hS with hS1; injection hS1 with hS1 hS2; subst hS1 hS2
        have hk4' : k % 4 = 2 := beq_iff_eq.mp hk4
        have hk_eq : k = 2 + (k / 4) * 4 := by omega
        rw [hk_eq]
        cases e
        · exact ⟨3 + a * 2,b * 2,PhaseScan.short00 hI⟩
        · exact ⟨2 + a * 2,b * 2,PhaseScan.short01 hI⟩
      | false =>
        rw [hk4] at hS; dsimp at hS
        injection hS with hS1; injection hS1 with hS1 hS2; subst hS1 hS2
        have hk4' : k % 4 ≠ 2 := ne_of_beq_eq_false hk4
        have hk_eq : k = 4 + (k / 4 - 1) * 4 := by omega
        rw [hk_eq]
        cases e
        · exact ⟨4 + a * 2,b * 2,PhaseScan.short10 hI⟩
        · exact ⟨3 + a * 2,b * 2,PhaseScan.short11 hI⟩
def loc_z2X : WordList -> Bool
  | [] => true
  | K :: _ => true
  | V :: _ => false
  | Q :: u => !loc_z2X u
def loc_z2Y : WordList -> WordList -> Nat -> WordList -> Option (Nat × WordList)
  | [],_,_,_ => none
  | _ :: fuel,[],k,acc => some (k,acc.reverseAux [])
  | _ :: fuel,w :: u,k,acc =>
    if k == 0 then none
    else match w with
      | V =>
        if 3 <= k then forceLit (2 + (k - 3) * 2) (fun m' => loc_z2Y fuel u m' (V :: acc))
        else none
      | K =>
        match loc_z2V false k with
        | some (d,k') => strictWord d (fun d' => forceLit k' (fun m' => loc_z2Y fuel u m' (d' :: acc)))
        | none => none
      | Q =>
        if (k % 2 == 0) && loc_z2X (Q :: u) then
          match loc_z2V true k with
          | some (d,k') => strictWord d (fun d' => forceLit k' (fun m' => loc_z2Y fuel u m' (d' :: acc)))
          | none => none
        else
          match u with
          | K :: v => forceLit ((k - 1) * 2) (fun m' => loc_z2Y fuel v m' (V :: acc))
          | Q :: v => forceLit (1 + (k - 1) * 2) (fun m' => loc_z2Y fuel v m' (V :: acc))
          | _ => none
theorem loc_z2Z (fuel : WordList) :
    ∀ (u : WordList) (k : Nat) (acc : WordList) (k' : Nat) (out : WordList),
      loc_z2Y fuel u k acc = some (k',out) ->
      ∃ v a b,out = acc.reverseAux v /\ PhaseScan k u k' v a b := by
  induction fuel with
  | nil => intro u k acc k' out hE; contradiction
  | cons _ fuel ih =>
    intro u k acc k' out hE
    cases u with
    | nil =>
      dsimp [loc_z2Y] at hE
      injection hE with hE1; injection hE1 with hk hout; subst hk hout
      exact ⟨[],0,0,rfl,PhaseScan.nil k⟩
    | cons w u =>
      dsimp [loc_z2Y] at hE
      cases hk0 : (k == 0) with
      | true => rw [hk0] at hE; contradiction
      | false =>
        rw [hk0] at hE; dsimp at hE
        have hk0' : k ≠ 0 := ne_of_beq_eq_false hk0
        cases w with
        | V =>
          dsimp at hE
          by_cases h3 : 3 <= k
          · rw [if_pos h3] at hE; simp only [strictWord_eq, forceLit_eq] at hE
            rcases ih u (2 + (k - 3) * 2) (V :: acc) k' out hE with ⟨v,a,b,rfl,hI⟩
            have hk_eq : k = 3 + (k - 3) := by omega
            rw [hk_eq]
            exact ⟨V :: v,a * (1 / 2),b * (1 / 2),rfl,PhaseScan.T hI⟩
          · rw [if_neg h3] at hE; contradiction
        | K =>
          dsimp at hE
          cases hS : loc_z2V false k with
          | none => rw [hS] at hE; contradiction
          | some dk =>
            rcases dk with ⟨d,m⟩
            rw [hS] at hE; dsimp at hE; simp only [strictWord_eq, forceLit_eq] at hE
            rcases ih u m (d :: acc) k' out hE with ⟨v,a,b,rfl,hI⟩
            rcases loc_z2W false k d m u k' v a b hS hI with ⟨x,y,hSub⟩
            exact ⟨d :: v,x,y,rfl,hSub⟩
        | Q =>
          dsimp at hE
          cases hcond : ((k % 2 == 0) && loc_z2X (Q :: u)) with
          | true =>
            rw [hcond] at hE; dsimp at hE
            cases hS : loc_z2V true k with
            | none => rw [hS] at hE; contradiction
            | some dk =>
              rcases dk with ⟨d,m⟩
              rw [hS] at hE; dsimp at hE; simp only [strictWord_eq, forceLit_eq] at hE
              rcases ih u m (d :: acc) k' out hE with ⟨v,a,b,rfl,hI⟩
              rcases loc_z2W true k d m u k' v a b hS hI with ⟨x,y,hSub⟩
              exact ⟨d :: v,x,y,rfl,hSub⟩
          | false =>
            rw [hcond] at hE; dsimp at hE
            cases u with
            | nil => contradiction
            | cons w2 v0 =>
              cases w2 with
              | V => contradiction
              | K =>
                dsimp at hE; simp only [strictWord_eq, forceLit_eq] at hE
                rcases ih v0 ((k - 1) * 2) (V :: acc) k' out hE with ⟨v,a,b,rfl,hI⟩
                have hk_eq : k = 1 + (k - 1) := by omega
                rw [hk_eq]
                exact ⟨V :: v,a * (1 / 2),(1 + b) * (1 / 2),rfl,PhaseScan.pair0 hI⟩
              | Q =>
                dsimp at hE; simp only [strictWord_eq, forceLit_eq] at hE
                rcases ih v0 (1 + (k - 1) * 2) (V :: acc) k' out hE with ⟨v,a,b,rfl,hI⟩
                have hk_eq : k = 1 + (k - 1) := by omega
                rw [hk_eq]
                exact ⟨V :: v,a * (1 / 2),(3 / 4) + b * (1 / 2),rfl,PhaseScan.pair1 hI⟩
def loc_zPf : WordList -> Nat -> Option (WordList)
  | [],_ => none
  | _ :: fuel,k =>
    if k == 0 then none
    else if k == 1 then some [Q]
    else match loc_zPf fuel (k / 2) with
      | none => none
      | some ws => strictWord (if k % 2 == 0 then K else Q) (fun d' => some (d' :: ws))
theorem loc_z30 (fuel : WordList) :
    ∀ (k : Nat) (ws : WordList),loc_zPf fuel k = some ws ->
      ∃ A H da,ws = da ++ [Q] /\ DigitVal A H da /\ A + 2 ^ H = k := by
  induction fuel with
  | nil => intro k ws h; contradiction
  | cons _ fuel ih =>
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
        exact ⟨0,0,[],rfl,DigitVal.nil,rfl⟩
      | false =>
        rw [hk1] at h; dsimp at h
        have hk1' : k ≠ 1 := ne_of_beq_eq_false hk1
        cases hrec : loc_zPf fuel (k / 2) with
        | none => rw [hrec] at h; contradiction
        | some ws' =>
          rw [hrec] at h; dsimp at h; simp only [strictWord_eq] at h
          injection h with h; subst h
          rcases ih (k / 2) ws' hrec with ⟨A,H,da,rfl,hD,hSum⟩
          rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
          · have hcond : (k % 2 == 0) = true := beq_iff_eq.mpr hmod
            rw [hcond]
            refine ⟨A * 2,1 + H,K :: da,rfl,DigitVal.zero hD,?_⟩
            rw [pow_two_one_add]; omega
          · have hcond : (k % 2 == 0) = false := beq_false_of_ne (by omega)
            rw [hcond]
            refine ⟨1 + A * 2,1 + H,Q :: da,rfl,DigitVal.one hD,?_⟩
            rw [pow_two_one_add]; omega
def loc_z31 (u : WordList) : Option (WordList) :=
  let (carry,eff) := loc_z2T u 0 []
  if carry == 1 then
    let fuel := V :: V :: V :: V :: eff
    match loc_z2Y fuel eff 12 [] with
    | some (k,v) =>
      match loc_zPf fuel k with
      | some ws => some (V :: (v ++ V :: ws))
      | none => none
    | none => none
  else none
theorem loc_z32 (u out : WordList) (hR : loc_z31 u = some out) : loc_Step u out := by
  dsimp [loc_z31] at hR
  generalize hE : loc_z2T u 0 [] = ce at hR
  rcases ce with ⟨carry,eff⟩
  dsimp at hR
  cases hC : (carry == 1) with
  | false => rw [hC] at hR; contradiction
  | true =>
    rw [hC] at hR; dsimp at hR
    have rfl_c : carry = 1 := beq_iff_eq.mp hC
    subst rfl_c
    cases hS : loc_z2Y (V :: V :: V :: V :: eff) eff 12 [] with
    | none => rw [hS] at hR; contradiction
    | some kv =>
      rcases kv with ⟨k,v⟩
      rw [hS] at hR; dsimp at hR
      cases hP : loc_zPf (V :: V :: V :: V :: eff) k with
      | none => rw [hP] at hR; contradiction
      | some ws =>
        rw [hP] at hR; dsimp at hR
        injection hR with hR; subst hR
        rcases loc_z2U u 0 [] 1 eff hE with ⟨w1,rfl,hEff⟩
        rcases loc_z2Z (V :: V :: V :: V :: eff) eff 12 [] k v hS with ⟨w2,a,b,rfl,hScan⟩
        rcases loc_z30 (V :: V :: V :: V :: eff) k ws hP with ⟨A,J,da,rfl,hDA,hSum⟩
        exact loc_Step.intro u eff k v a b J A da hEff hScan hDA hSum
def loc_zSw : WordList -> WordList -> Option (WordList)
  | [],u => some u
  | V :: p,V :: u => loc_zSw p u
  | K :: p,K :: u => loc_zSw p u
  | Q :: p,Q :: u => loc_zSw p u
  | _,_ => none
theorem loc_z33 (p : WordList) :
    ∀ (u v : WordList),loc_zSw p u = some v -> u = p ++ v := by
  induction p with
  | nil => intro u v h; injection h
  | cons w p ih =>
    intro u v h
    cases u with
    | nil => cases w <;> contradiction
    | cons x u =>
      cases w <;> cases x <;> try contradiction
      all_goals
        dsimp [loc_zSw] at h
        rw [ih u v h]; rfl
theorem loc_z34 (u pre rest : WordList)
    (hE : loc_zSw pre (u.reverseAux []) = some rest) :
    u = rest.reverseAux pre.reverse := by
  have h1 := loc_z33 pre u.reverse rest hE
  have h2 := congrArg List.reverse h1
  simp [List.reverseAux_eq] at h2 ⊢
  exact h2
def loc_zHn : WordList -> Nat -> Option Nat
  | [],h => some h
  | V :: u,h => loc_zHn u (h + 1)
  | _ :: _,0 => none
  | _ :: u,h + 1 => loc_zHn u h
theorem loc_z35 (u : WordList) :
    ∀ (h H : Nat),loc_zHn u h = some H ->
      wordScale u * ((2 ^ H : Nat) : Rat) = ((2 ^ h : Nat) : Rat) := by
  induction u with
  | nil =>
    intro h H hE
    injection hE with hE; subst hE
    simp [wordScale]
  | cons w u ih =>
    intro h H hE
    cases w
    · dsimp [loc_zHn,wordScale] at hE ⊢
      have hih := ih (h + 1) H hE
      rw [Nat.pow_succ] at hih
      push_cast at hih ⊢; linarith
    · cases h with
      | zero => contradiction
      | succ h =>
        dsimp [loc_zHn,wordScale] at hE ⊢
        have hih := ih h H hE
        rw [Nat.pow_succ]
        push_cast at hih ⊢; linarith
    · cases h with
      | zero => contradiction
      | succ h =>
        dsimp [loc_zHn,wordScale] at hE ⊢
        have hih := ih h H hE
        rw [Nat.pow_succ]
        push_cast at hih ⊢; linarith
def loc_z36 : WordList -> WordList -> Option (WordList × WordList)
  | [],_ => none
  | V :: u,ds => some (u.reverseAux [V],ds)
  | w :: u,ds => loc_z36 u (w :: ds)
theorem loc_z37 (u : WordList) :
    ∀ (ds p tail : WordList),loc_z36 u ds = some (p,tail) ->
      ds.all loc_z2M = true ->
      u.reverseAux ds = p ++ tail /\ tail.all loc_z2M = true /\ (∃ v,p = v ++ [V]) := by
  induction u with
  | nil => intro ds p tail hE _; contradiction
  | cons w u ih =>
    intro ds p tail hE hD
    cases w
    · dsimp [loc_z36] at hE
      injection hE with h1; injection h1 with h1 h2; subst h1 h2
      refine ⟨by simp [List.reverseAux_eq],hD,u.reverse,by simp [List.reverseAux_eq]⟩
    · dsimp [loc_z36] at hE
      have hD' : (K :: ds).all loc_z2M = true := by simp [loc_z2M,hD]
      exact ih (K :: ds) p tail hE hD'
    · dsimp [loc_z36] at hE
      have hD' : (Q :: ds).all loc_z2M = true := by simp [loc_z2M,hD]
      exact ih (Q :: ds) p tail hE hD'
def loc_z38 (u : WordList) : Option (WordList × WordList) :=
  loc_z36 (u.reverseAux []) []
theorem loc_z39 (u p ds : WordList) (hE : loc_z38 u = some (p,ds)) :
    u = p ++ ds /\ ds.all loc_z2M = true /\ (∃ v,p = v ++ [V]) := by
  rcases loc_z37 (u.reverseAux []) [] p ds hE rfl with ⟨hU,hD,hEnd⟩
  simp [List.reverseAux_eq] at hU
  exact ⟨hU,hD,hEnd⟩
def loc_z3a (n : Nat) : Nat := (n + 1) / 2
theorem loc_z3b (n : Nat) : (n : Rat) <= 2 * ((loc_z3a n : Nat) : Rat) := by
  have h : n <= (loc_z3a n) * 2 := by unfold loc_z3a; omega
  have hq : (n : Rat) <= (((loc_z3a n) * 2 : Nat) : Rat) := by exact_mod_cast h
  push_cast at hq
  linarith
def loc_z3c (c0 c1 : Nat) : WordList -> Nat -> Nat
  | [],n => n
  | V :: u,n => loc_z3c c0 c1 u (loc_z3a n)
  | K :: u,n => loc_z3c c0 c1 u (n * 2 + c0)
  | Q :: u,n => loc_z3c c0 c1 u (n * 2 + c1)
theorem loc_z3d (c0 c1 : Nat) (u : WordList) :
    ∀ (n : Nat),
      (c0 : Rat) * wordMassK u.reverse + (c1 : Rat) * wordMassQ u.reverse + wordScale u.reverse * (n : Rat) <=
        ((loc_z3c c0 c1 u n : Nat) : Rat) := by
  induction u with
  | nil =>
    intro n
    simp [wordMassK,wordMassQ,wordScale,loc_z3c]
  | cons w u ih =>
    intro n
    have hsp := wordScale_pos u.reverse
    cases w
    · dsimp [loc_z3c]
      rw [List.reverse_cons,wordMassK_append,wordMassQ_append,wordScale_append]
      dsimp [wordMassK,wordMassQ,wordScale]
      have hhu := loc_z3b n
      have hih := ih (loc_z3a n)
      nlinarith
    · dsimp [loc_z3c]
      rw [List.reverse_cons,wordMassK_append,wordMassQ_append,wordScale_append]
      dsimp [wordMassK,wordMassQ,wordScale]
      have hih := ih (n * 2 + c0)
      push_cast at hih
      nlinarith
    · dsimp [loc_z3c]
      rw [List.reverse_cons,wordMassK_append,wordMassQ_append,wordScale_append]
      dsimp [wordMassK,wordMassQ,wordScale]
      have hih := ih (n * 2 + c1)
      push_cast at hih
      nlinarith
theorem loc_z3e (c0 c1 : Nat) (u : WordList) (n : Nat) :
    (c0 : Rat) * wordMassK u + (c1 : Rat) * wordMassQ u + wordScale u * (n : Rat) <=
      ((loc_z3c c0 c1 (u.reverseAux []) n : Nat) : Rat) := by
  have h := loc_z3d c0 c1 u.reverse n
  simpa [List.reverseAux_eq,List.reverse_reverse] using h
def loc_z3f : WordList := [Q,Q,K] ++ List.replicate 14 Q
theorem loc_z3g :
    wordMassK loc_z3f = 4 /\ wordScale loc_z3f * wordScale (List.replicate 16 V) = 2 := by
  constructor
  · norm_num [loc_z3f,List.replicate,wordMassK]
  · norm_num [loc_z3f,List.replicate,wordScale]
theorem loc_z3h {B H : Nat} {db u : WordList}
    (hD : DigitVal B H db)
    (hHeight : wordScale u * ((2 ^ H : Nat) : Rat) = 1)
    (hHi : ∃ lo,db = lo ++ loc_z3f) :
    (3 / 2) * wordScale (List.replicate 16 V) <= wordScale u * wordMassK db /\
    wordScale u * wordMassK db <= (5 / 2) * wordScale (List.replicate 16 V) := by
  rcases hHi with ⟨lo,rfl⟩
  have hDig := loc_z2O hD
  rw [List.all_append] at hDig
  rcases Bool.and_eq_true_iff.mp hDig with ⟨hDigLo,_⟩
  rcases loc_z2N lo hDigLo with ⟨A,hDA⟩
  rcases digitVal_scale_and_mass hDA with ⟨hLs,hLm,_⟩
  rcases digitVal_scale_and_mass hD with ⟨hDs,_,_⟩
  have hSplitLo := wordMass_eq_add lo
  have hWlo := wordMass_nonneg lo
  have hSu := wordScale_pos u
  have hSlo := wordScale_pos lo
  have hSh := wordScale_pos loc_z3f
  have hS16 := wordScale_pos (List.replicate 16 V)
  rcases loc_z3g with ⟨hZ,hS⟩
  rw [wordScale_append] at hDs
  let x := wordScale u * wordScale lo
  have hX : x * wordScale loc_z3f = 1 := by
    change (wordScale u * wordScale lo) * wordScale loc_z3f = 1
    nlinarith
  have hXa : 2 * x = wordScale (List.replicate 16 V) := by nlinarith
  rw [wordMassK_append,hZ]
  have hZlo_le : wordMassK lo <= wordScale lo - 1 := by linarith
  refine ⟨by nlinarith,by nlinarith⟩
def loc_z3i (rest : WordList) : Bool :=
  decide (loc_z3c 65536 65536 (rest.reverseAux []) 0 <= 16)
theorem loc_z3j (rest : WordList) (hE : loc_z3i rest = true) :
    wordMass rest <= 1 / 4096 := by
  have hle : loc_z3c 65536 65536 (rest.reverseAux []) 0 <= 16 := of_decide_eq_true hE
  have hle_q : ((loc_z3c 65536 65536 (rest.reverseAux []) 0 : Nat) : Rat) <= 16 := by exact_mod_cast hle
  have hR := loc_z3e 65536 65536 rest 0
  have hSplit := wordMass_eq_add rest
  push_cast at hR
  linarith
def loc_z3k (orig : WordList) : Bool :=
  match loc_z38 orig with
  | none => false
  | some (u,tail) =>
    match loc_zSw [Q] (tail.reverseAux []) with
    | none => false
    | some rd =>
      let da := rd.reverseAux []
      match loc_zSw (List.replicate 16 V ++ [Q]) u,loc_zHn u 0 with
      | some rest,some H =>
        if 33 <= H && H == da.length then
          let (carry,_) := loc_z2T u 0 []
          let (last,db) := loc_z2T da carry []
          if last == 1 then
            match loc_zSw (List.replicate 7 Q) db,
                  loc_zSw loc_z3f.reverse (db.reverseAux []) with
            | some _,some _ => loc_z3i rest
            | _,_ => false
          else false
        else false
      | _,_ => false
theorem loc_z3l (orig : WordList) (hCheck : loc_z3k orig = true) :
    Good 16 orig := by
  unfold loc_z3k at hCheck
  cases hC : loc_z38 orig with
  | none => rw [hC] at hCheck; contradiction
  | some utail =>
    rcases utail with ⟨u,tail⟩
    rw [hC] at hCheck; dsimp only [] at hCheck
    cases hTop : loc_zSw [Q] (tail.reverseAux []) with
    | none => rw [hTop] at hCheck; contradiction
    | some rd =>
      rw [hTop] at hCheck; dsimp only [] at hCheck
      cases hStart : loc_zSw (List.replicate 16 V ++ [Q]) u with
      | none => rw [hStart] at hCheck; contradiction
      | some rest =>
        rw [hStart] at hCheck
        cases hHeight : loc_zHn u 0 with
        | none => rw [hHeight] at hCheck; contradiction
        | some H =>
          rw [hHeight] at hCheck; dsimp only [] at hCheck
          cases hCondH : (decide (33 <= H) && (H == (rd.reverseAux []).length)) with
          | false => rw [hCondH] at hCheck; contradiction
          | true =>
            rw [hCondH] at hCheck
            rcases Bool.and_eq_true_iff.mp hCondH with ⟨hH33,hWidth⟩
            have hHbound : 33 <= H := of_decide_eq_true hH33
            have hWidth_eq : H = (rd.reverseAux []).length := beq_iff_eq.mp hWidth
            generalize hE : loc_z2T u 0 [] = ce at hCheck
            rcases ce with ⟨carry,eff⟩
            generalize hF : loc_z2T (rd.reverseAux []) carry [] = ldb at hCheck
            rcases ldb with ⟨last,db⟩
            cases hLast : (last == 1) with
            | false => rw [hLast] at hCheck; contradiction
            | true =>
              rw [hLast] at hCheck
              have rfl_last : last = 1 := beq_iff_eq.mp hLast
              subst rfl_last
              cases hLow : loc_zSw (List.replicate 7 Q) db with
              | none => rw [hLow] at hCheck; contradiction
              | some lo =>
                rw [hLow] at hCheck
                cases hHigh : loc_zSw loc_z3f.reverse (db.reverseAux []) with
                | none => rw [hHigh] at hCheck; contradiction
                | some hi =>
                  rw [hHigh] at hCheck
                  have hMass := loc_z3j rest hCheck
                  rcases loc_z39 orig u tail hC with ⟨hOrig,hDig,hEnd⟩
                  have hTail : tail = rd.reverseAux [] ++ [Q] := by
                    have h1 := loc_z34 tail [Q] rd hTop
                    simpa [List.reverseAux_eq] using h1
                  rw [hTail,List.all_append] at hDig
                  rcases Bool.and_eq_true_iff.mp hDig with ⟨hDigDa,_⟩
                  rcases loc_z2N (rd.reverseAux []) hDigDa with ⟨A,hDA⟩
                  rw [<- hWidth_eq] at hDA
                  rcases loc_z2U u 0 [] carry eff hE with ⟨v1,rfl,hEff⟩
                  rcases loc_z2U (rd.reverseAux []) carry [] 1 db hF with ⟨v2,rfl,hEffD⟩
                  rcases wordEffect_digitVal hEffD hDA with ⟨B,hDB,hSum⟩
                  have hStart_eq := loc_z33 (List.replicate 16 V ++ [Q]) u rest hStart
                  simp only [List.append_assoc,List.singleton_append] at hStart_eq
                  have hHeight_eq := loc_z35 u 0 H hHeight
                  have hHigh' : ∃ x,db = x ++ loc_z3f := by
                    have h1 := loc_z34 db loc_z3f.reverse hi hHigh
                    refine ⟨hi.reverse,?_⟩
                    simpa [List.reverseAux_eq] using h1
                  rcases loc_z3h hDB hHeight_eq hHigh' with ⟨hDlo,hDhi⟩
                  rw [hOrig,hTail,<- List.append_assoc]
                  refine Good.intro 16 H u A (rd.reverseAux []) carry eff B db (1 / 32)
                    (by decide) hHbound ⟨rest,hStart_eq⟩ hEnd hHeight_eq hDA hEff (by omega) hDB
                    (loc_Reserve.even 8 (1 / 32) (by norm_num)) ?_ hDlo hDhi
                    ⟨lo,loc_z33 (List.replicate 7 Q) db lo hLow⟩
                  rw [hStart_eq,loc_z2G]
                  have hSp := wordScale_pos (List.replicate 16 V)
                  nlinarith
inductive loc_Rounds : WordList -> WordList -> Prop where
  | refl (u : WordList) : loc_Rounds u u
  | next {u v w : WordList} : loc_Step u v -> loc_Rounds v w -> loc_Rounds u w
def loc_z3m : Nat -> WordList -> Bool
  | 0,u => loc_z3k u
  | n + 1,u =>
    match loc_z31 u with
    | none => false
    | some v => loc_z3m n v
theorem loc_z3n (n : Nat) :
    ∀ (u : WordList),loc_z3m n u = true ->
      ∃ v,loc_Rounds u v /\ Good 16 v := by
  induction n with
  | zero =>
    intro u hE
    exact ⟨u,loc_Rounds.refl u,loc_z3l u hE⟩
  | succ n ih =>
    intro u hE
    dsimp [loc_z3m] at hE
    cases hV : loc_z31 u with
    | none => rw [hV] at hE; contradiction
    | some v =>
      rw [hV] at hE
      rcases ih v hE with ⟨w,hR,hG⟩
      exact ⟨w,loc_Rounds.next (loc_z32 u v hV) hR,hG⟩
def loc_z3o : WordList := [V,V,Q,V,V,V,V,K,Q,K,Q,K,Q]
def u_0 : WordList := loc_z3o
def u_1 : WordList := [V,V,V,Q,V,V,V,V,V,K,K,V,V,K,K,K,K,K,K,Q,Q]
def u_2 : WordList := [V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,K,Q,Q,Q,K,Q,Q,Q,K,K,K,K,K,K,Q,Q,Q]
def u_3 : WordList := [V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,Q,Q,Q,K,V,V,V,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q]
def u_4 : WordList := [V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q]
def u_5 : WordList := [V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,K,K,V,V,V,V,V,V,V,Q,V,V,V,K,K,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q]
def u_6 : WordList := [V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,Q,K,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,K,K,K,K,K,K,Q,Q,V,K,K,Q,V,V,V,V,V,V,V,V,V,V,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q]
def u_7 : WordList := [V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,K,K,V,K,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,K,K,K,V,V,V,V,V,V,Q,V,V,V,V,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,K,K,K,K,K,K,K,K,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q]
def u_8 : WordList := [V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,K,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,Q,K,K,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,K,K,K,K,K,K,K,V,K,V,K,V,V,V,V,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,V,V,V,V,V,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q]
def u_9 : WordList := [V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,K,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,K,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,K,V,V,V,V,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,K,V,V,K,K,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,Q,V,V,V,V,V,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def u_10 : WordList := [V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,K,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,K,Q,Q,K,Q,Q,K,Q,V,V,V,Q,Q,V,K,Q,K,K,V,V,V,V,V,V,K,K,V,V,V,V,V,V,K,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,K,Q,K,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,K,K,Q,Q,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,K,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def u_11 : WordList := [V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,K,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,K,V,K,Q,K,Q,V,V,Q,K,Q,K,V,V,V,V,V,K,Q,Q,Q,Q,V,V,V,V,V,V,V,V,Q,K,V,Q,V,V,Q,V,V,V,Q,Q,V,Q,K,V,V,V,V,V,Q,V,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,K,K,K,K,K,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,K,K,K,K,K,K,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def u_12 : WordList := [V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,K,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,K,V,Q,V,V,Q,K,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,Q,Q,V,Q,V,V,Q,V,V,V,Q,Q,V,K,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,Q,K,K,Q,Q,K,Q,K,Q,Q,V,K,K,K,Q,V,V,V,K,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,K,K,V,V,V,V,V,Q,V,V,K,V,V,V,V,V,Q,Q,Q,Q,V,V,V,V,Q,K,V,V,V,V,V,K,V,V,Q,V,V,V,V,V,K,K,V,V,V,V,V,V,K,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,Q,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,K,K,K,K,K,Q,Q,K,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def u_13 : WordList := [V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,K,V,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,Q,Q,V,K,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,K,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,Q,Q,K,V,K,V,V,V,V,K,Q,V,V,V,Q,V,V,V,V,V,V,Q,Q,Q,Q,V,Q,V,Q,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,V,Q,V,K,V,V,K,V,Q,Q,Q,Q,K,Q,V,Q,V,V,K,V,V,V,V,V,V,V,Q,V,V,K,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,K,V,V,V,V,V,Q,Q,Q,Q,V,V,V,V,V,V,V,V,V,V,K,V,V,Q,V,V,V,V,V,K,K,V,V,V,V,V,V,K,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,K,Q,K,K,K,K,K,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q,Q,Q,K,K,K,K,K,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def u_14 : WordList := [V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,Q,V,V,Q,K,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,Q,Q,V,K,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,Q,Q,V,V,K,V,Q,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,Q,V,K,V,K,V,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,Q,V,Q,V,V,V,V,Q,K,Q,V,V,V,V,Q,V,V,V,Q,K,V,V,V,V,V,V,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,V,K,Q,K,Q,V,V,V,K,K,K,K,K,V,V,V,V,V,V,V,V,Q,Q,K,V,Q,Q,K,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,K,V,Q,V,Q,Q,K,K,V,V,V,V,V,V,Q,K,V,K,V,V,V,V,V,V,Q,V,V,V,K,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,K,V,V,V,V,V,Q,Q,Q,Q,V,V,V,V,V,V,V,V,V,V,K,V,V,Q,V,V,V,V,V,K,K,V,V,V,V,V,V,K,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,K,Q,K,K,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,Q,Q,K,K,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,K,K,Q,K,Q,Q,K,K,Q,Q,K,K,K,Q,Q,Q,K,K,K,K,K,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,K,Q,Q,Q,K,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
theorem step_0 : loc_z31 u_0 = some u_1 := by decide
theorem step_1 : loc_z31 u_1 = some u_2 := by decide
theorem step_2 : loc_z31 u_2 = some u_3 := by decide
theorem step_3 : loc_z31 u_3 = some u_4 := by decide
theorem step_4 : loc_z31 u_4 = some u_5 := by decide
theorem step_5 : loc_z31 u_5 = some u_6 := by decide
theorem step_6 : loc_z31 u_6 = some u_7 := by decide
theorem step_7 : loc_z31 u_7 = some u_8 := by decide
theorem step_8 : loc_z31 u_8 = some u_9 := by decide
theorem step_9 : loc_z31 u_9 = some u_10 := by decide
theorem step_10 : loc_z31 u_10 = some u_11 := by decide
theorem step_11 : loc_z31 u_11 = some u_12 := by decide
theorem step_12 : loc_z31 u_12 = some u_13 := by decide
theorem step_13 : loc_z31 u_13 = some u_14 := by decide
theorem good_14 : loc_z3k u_14 = true := by decide
theorem z3p_rounds : loc_Rounds loc_z3o u_14 := by
  exact loc_Rounds.next (loc_z32 u_0 u_1 step_0) (loc_Rounds.next (loc_z32 u_1 u_2 step_1) (loc_Rounds.next (loc_z32 u_2 u_3 step_2) (loc_Rounds.next (loc_z32 u_3 u_4 step_3) (loc_Rounds.next (loc_z32 u_4 u_5 step_4) (loc_Rounds.next (loc_z32 u_5 u_6 step_5) (loc_Rounds.next (loc_z32 u_6 u_7 step_6) (loc_Rounds.next (loc_z32 u_7 u_8 step_7) (loc_Rounds.next (loc_z32 u_8 u_9 step_8) (loc_Rounds.next (loc_z32 u_9 u_10 step_9) (loc_Rounds.next (loc_z32 u_10 u_11 step_10) (loc_Rounds.next (loc_z32 u_11 u_12 step_11) (loc_Rounds.next (loc_z32 u_12 u_13 step_12) (loc_Rounds.next (loc_z32 u_13 u_14 step_13) (loc_Rounds.refl u_14))))))))))))))
theorem z3p : ∃ v, loc_Rounds loc_z3o v /\ Good 16 v := ⟨u_14, z3p_rounds, loc_z3l u_14 good_14⟩
inductive Num : Nat -> BitWord -> List Call -> Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)
theorem z3q {k : Nat} (hK : 0 < k) : ∃ hs,Num k [] hs := by
  rcases even_or_odd_mul_two k with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · cases a with
    | zero => omega
    | succ a =>
      have heq : (a + 1) * 2 = 2 + a * 2 := by omega
      rw [heq]; exact ⟨[.cj] ++ [.ch] ^ a,Num.even a⟩
  · exact ⟨[.cp] ++ [.ch] ^ a,Num.odd a⟩
theorem z3r {k : Nat} {hs hs' : List Call} (h1 : Num k [] hs) (h2 : Num k [] hs') :
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
def z3s (k : Nat) (r r' : HalfTape) : Prop :=
  ∀ w hs,Num k w hs -> Side hs (w +> r) r'
theorem z3t {r r' : HalfTape} (h : z3s 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl
theorem z3u {n : Nat} {r r' : HalfTape}
    (hI : z3s (n * 2) r r') : z3s (2 + n * 4) (d0 +> r) (d0 +> r') := by
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
      have hr' := z3t hI
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
theorem z3v {n : Nat} {r r' : HalfTape}
    (hI : z3s (n * 2) r r') : z3s (4 + n * 4) (d0 +> r) (d1 +> r') := by
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
      have hr' := z3t hI
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
theorem z3w {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hZ : A = 0) :
    evalWords da default = default := by
  induction hD with
  | nil => rfl
  | @zero A H u _ ih =>
    have hA0 : A = 0 := by omega
    dsimp only [evalWords]
    rw [ih hA0,zDd]
  | one _ => omega
theorem z3x {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hPos : 0 < A) :
    z3s ((A - 1) * 2) default (evalWords da default) := by
  induction hD with
  | nil => omega
  | @zero A H u _ ih =>
    have hA_pos : 0 < A := by omega
    have hIH := ih hA_pos
    have hs := z3u hIH
    rw [zDd] at hs
    have heq : (A * 2 - 1) * 2 = 2 + (A - 1) * 4 := by omega
    dsimp [evalWords]
    rwa [heq]
  | @one A H u hDu ih =>
    cases A with
    | zero =>
      change z3s 0 default (d1 +> evalWords u default)
      rw [z3w hDu rfl]
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
      have hs := z3v hIH
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
    exact z0b ([Call.ch] ^ n)
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
theorem z3y {n : Nat} {hs hs' : List Call}
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
theorem loc_z3z {n : Nat} {hs hs' : List Call}
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
theorem loc_z3A {n : Nat} {hs hs' : List Call}
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
theorem loc_z3B {n : Nat} {hs hs' : List Call}
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
theorem loc_z3C {n : Nat} {hs hs' : List Call}
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
theorem loc_z3D {n : Nat} {hs hs' : List Call}
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
theorem loc_z3E {n : Nat} {hs hs' : List Call}
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
theorem loc_z3F {k : Nat} {v : WordList} {k' : Nat} {w : WordList} {a b : Rat}
    (hI : PhaseScan k v k' w a b) :
    ∀ {u : WordList} {n n' : Nat} {hs hs' : List Call},
      WordEffect n u n' v -> Num k [] hs -> Num k' [] hs' ->
      Seg (([Call.ch] ^ n) ++ hs) (([Call.ch] ^ n') ++ hs') (wordsToBits u) (wordsToBits w) := by
  induction hI with
  | nil k =>
    intro u n n' hs hs' hE hN hN'
    cases hE
    rw [z3r hN hN']
    exact z0b (([Call.ch] ^ n) ++ hs')
  | @T m _ _ _ _ _ _ ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    cases hE with
    | T hSub =>
      rcases z3q (by omega : 0 < 2 + m * 2) with ⟨hs0,hN0⟩
      have hIH := ih hSub hN0 hN'
      have hStep := zSg (H_T n0) (z3y hN hN0)
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
    rcases z3q hPos with ⟨hs0,hN0⟩
    have hD10 : DigitVal 1 2 [Q,K] := DigitVal.one (DigitVal.zero DigitVal.nil)
    have hStep := zSg (zEd hL hD10) (loc_z3z hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @pair1 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q,Q] ++ u) at hE
    rcases wordEffect_split_output [Q,Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z3q (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD11 : DigitVal 3 2 [Q,Q] := DigitVal.one (DigitVal.one DigitVal.nil)
    have hStep := zSg (zEd hL hD11) (loc_z3A hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short00 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([K] ++ u) at hE
    rcases wordEffect_split_output [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases z3q hPos with ⟨hs0,hN0⟩
    have hD0 : DigitVal 0 1 [K] := DigitVal.zero DigitVal.nil
    have hStep := zSg (zEd hL hD0) (loc_z3B hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short01 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q] ++ u) at hE
    rcases wordEffect_split_output [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z3q (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : DigitVal 1 1 [Q] := DigitVal.one DigitVal.nil
    have hStep := zSg (zEd hL hD1) (loc_z3C hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short10 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([K] ++ u) at hE
    rcases wordEffect_split_output [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases z3q hPos with ⟨hs0,hN0⟩
    have hD0 : DigitVal 0 1 [K] := DigitVal.zero DigitVal.nil
    have hStep := zSg (zEd hL hD0) (loc_z3D hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
  | @short11 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q] ++ u) at hE
    rcases wordEffect_split_output [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z3q (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : DigitVal 1 1 [Q] := DigitVal.one DigitVal.nil
    have hStep := zSg (zEd hL hD1) (loc_z3E hN hN0)
    rw [wordsToBits_append]
    exact zS0 hStep (ih hR hN0 hN')
theorem loc_z3G {n : Nat} {r r' : HalfTape}
    (hI : z3s (n * 2) r r') : z3s (1 + n) (d1 +> (d0 +> r)) (t +> r') := by
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
      have hr' := z3t hI
      subst hr'
      rw [<- append_assoc t one r]
      exact zSc z0g (Side.nil r)
    | succ m =>
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      refine zSc (z0u m) ?_
      have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : n * 2 = 2 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil,<- append_assoc d1 d0 r]
    refine zSc (z0v m) ?_
    have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : n * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2
theorem loc_z3H {k : Nat} {v : WordList} {k' : Nat} {w : WordList} {a b : Rat}
    (hI : PhaseScan k v k' w a b) {u : WordList} {r' : HalfTape}
    (hE : WordEffect 0 u 1 v) (hK : 0 < k') (hC : z3s k' (d1 +> default) r') :
    z3s k (evalWords u default) (evalWords w r') := by
  intro w0 hs hN
  have hPosK : 0 < k := phaseScan_pos_of_out_pos hI hK
  have hw0 : w0 = [] := by
    cases hN with
    | zero => omega
    | odd _ => rfl
    | even _ => rfl
  subst hw0
  rcases z3q hK with ⟨hs',hN'⟩
  have hSeg := loc_z3F hI hE hN hN'
  dsimp at hSeg
  have hSide_out : Side ([Call.ch] ++ hs') (d0 +> default) r' := by
    rw [zDd]
    exact z08 z0D (hC [] hs' hN')
  have hSide := zSc hSeg hSide_out
  rw [zDd] at hSide
  rwa [wordsToBits_append_tape,wordsToBits_append_tape] at hSide
theorem loc_z3I {orig out : WordList} (hS : loc_Step orig out) :
    ∃ r,z3s 12 (evalWords orig default) r /\ evalWords out default = t +> r := by
  rcases hS with ⟨eff,k,v,a,b,J,A,da,hE,hI,hDA,hSum⟩
  have hDA1 : DigitVal (A + 2 ^ J) (J + 1) (da ++ [Q]) := by
    have h1 := digitVal_append hDA (DigitVal.one DigitVal.nil)
    simpa using h1
  rw [hSum] at hDA1
  have hK_pos : 0 < k := by
    have hp := pow_two_pos J
    omega
  have hC0 : z3s ((k - 1) * 2) default (evalWords (da ++ [Q]) default) :=
    z3x hDA1 hK_pos
  have hC1 : z3s (1 + (k - 1)) (d1 +> (d0 +> default)) (t +> evalWords (da ++ [Q]) default) :=
    loc_z3G hC0
  have hk_eq : 1 + (k - 1) = k := by omega
  rw [hk_eq,zDd] at hC1
  have hRun := loc_z3H hI hE hK_pos hC1
  refine ⟨evalWords v (t +> evalWords (da ++ [Q]) default),hRun,?_⟩
  simp [evalWords,evalWords_append]
theorem loc_z3J {r r' : HalfTape} (hI : z3s 12 r r') :
    (zCf r) [target_tm]⊢⁺ zCf (t +> r') := by
  have h_num : Num 12 [] ([.cj] ++ [.ch] ^ 5) := Num.even 5
  have hC := hI [] ([.cj] ++ [.ch] ^ 5) h_num
  have hS := zSc z0F hC
  rcases hS with _ | ⟨hca,hrest⟩
  rcases hrest with _ | ⟨hch,hnil⟩
  cases hnil
  have h1 := zPt (z0G (w_init +> r)) (hca ([1] +> default))
  have h2 := zPt (z0H _) (hch lh)
  have h3 := zPt h1 h2
  have heq : (w_init ++ t) +> r' = w_init +> (t +> r') := append_assoc w_init t r'
  unfold zCf
  rwa [heq] at h3
theorem z3K {orig out : WordList} (hS : loc_Step orig out) :
    (zCf (evalWords orig default)) [target_tm]⊢⁺ zCf (evalWords out default) := by
  rcases loc_z3I hS with ⟨r,hC,hOut⟩
  rw [hOut]
  exact loc_z3J hC
theorem z3L {u v : WordList} (hR : loc_Rounds u v) :
    (zCf (evalWords u default)) [target_tm]⊢* zCf (evalWords v default) := by
  induction hR with
  | refl _ => exact ⟨0,rfl⟩
  | next hS _ ih =>
    rcases z3K hS with ⟨n,_,hn⟩
    rcases ih with ⟨m,hm⟩
    exact ⟨n + m,zMt target_tm _ _ _ n m hn hm⟩
abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev z3M (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev z3T (c : CCfg) : Option CCfg := Counter.bstep target_tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep target_tm n c
def z3X : CCfg :=
  ⟨A,0,[],[]⟩
def z3Y : CCfg :=
  ⟨D,1,[0,1],[0,1,1,0,0,1,1,0,0,1,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,0,0,0,1,0,0,0,1]⟩
def z3X_1 : CCfg := ⟨D,1,[0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],[0, 0, 0, 1, 0, 0, 1]⟩
def z3X_2 : CCfg := ⟨B,1,[1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],[0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1]⟩
def z3X_3 : CCfg := ⟨B,1,[1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],[0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1]⟩
def z3X_4 : CCfg := ⟨B,0,[1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1],[0, 0, 0, 0, 1, 0, 0, 0, 1]⟩
def z3X_5 : CCfg := ⟨B,1,[1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1],[0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩
theorem z3Z_1 : zCm z3X 300 = some z3X_1 := by decide
theorem z40_1 : (z3M z3X) [target_tm]⊢^{300} (z3M z3X_1) :=
  Counter.bmultiStep_sound 300 z3X z3X_1 z3Z_1
theorem z3Z_2 : zCm z3X_1 300 = some z3X_2 := by decide
theorem z40_2 : (z3M z3X_1) [target_tm]⊢^{300} (z3M z3X_2) :=
  Counter.bmultiStep_sound 300 z3X_1 z3X_2 z3Z_2
theorem loc_z3Z_3 : zCm z3X_2 300 = some z3X_3 := by decide
theorem loc_z40_3 : (z3M z3X_2) [target_tm]⊢^{300} (z3M z3X_3) :=
  Counter.bmultiStep_sound 300 z3X_2 z3X_3 loc_z3Z_3
theorem z3Z_4 : zCm z3X_3 300 = some z3X_4 := by decide
theorem z40_4 : (z3M z3X_3) [target_tm]⊢^{300} (z3M z3X_4) :=
  Counter.bmultiStep_sound 300 z3X_3 z3X_4 z3Z_4
theorem z3Z_5 : zCm z3X_4 300 = some z3X_5 := by decide
theorem z40_5 : (z3M z3X_4) [target_tm]⊢^{300} (z3M z3X_5) :=
  Counter.bmultiStep_sound 300 z3X_4 z3X_5 z3Z_5
theorem z3Z_6 : zCm z3X_5 272 = some z3Y := by decide
theorem z40_6 : (z3M z3X_5) [target_tm]⊢^{272} (z3M z3Y) :=
  Counter.bmultiStep_sound 272 z3X_5 z3Y z3Z_6
theorem z40 : (z3M z3X) [target_tm]⊢^{1772} (z3M z3Y) := by
  have h1 := zMt target_tm _ _ _ 300 300 z40_1 z40_2
  have h2 := zMt target_tm _ _ _ 600 300 h1 loc_z40_3
  have h3 := zMt target_tm _ _ _ 900 300 h2 z40_4
  have h4 := zMt target_tm _ _ _ 1200 300 h3 z40_5
  exact zMt target_tm _ _ _ 1500 272 h4 z40_6
theorem z41 :
    (init []) [target_tm]⊢* zCf (evalWords loc_z3o default) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = z3M z3X := rfl
  have h_end : z3M z3Y = zCf (evalWords loc_z3o default) := by
    simp [z3M,z3Y,zCf,zCL,lh,w_init,t,d0,d1,one,loc_z3o,evalWords]
  refine ⟨1772,?_⟩
  rw [h_init,<- h_end]
  exact z40
theorem zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
theorem z42 (m : Nat) :
    ∃ N ≥ m,∃ p w,multiStep target_tm (init []) N = some (zCf (evalWords w default)) /\ Good p w := by
  induction m with
  | zero =>
    rcases z41 with ⟨k1,hk1⟩
    rcases z3p with ⟨v,hR,hG⟩
    rcases z3L hR with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,16,v,
      zMt target_tm _ _ _ k1 k2 hk1 hk2,hG⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,p,w,h_ms,h_good⟩
    rcases loc_z2L h_good with ⟨w',hStep,h_good'⟩
    rcases z3K hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,1 + p,w',
      zMt target_tm _ _ _ N k h_ms h_step_k,h_good'⟩

end Solution


set_option linter.deprecated false
set_option linter.dupNamespace false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000



theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases Solution.z42 (n + 1) with ⟨N,hN,_,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := Solution.zIm h_N
  rw [Solution.zMs,hn] at h_some
  exact h_some

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RBHHH_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA
