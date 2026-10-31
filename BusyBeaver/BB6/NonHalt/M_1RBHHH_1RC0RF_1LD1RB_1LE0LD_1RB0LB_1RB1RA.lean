/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB---_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB---_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RBHHH_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB---_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => none
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 0, Stmt.write 1 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open Counter
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000
variable {α β γ : Type*} [Inhabited α] [Inhabited β] [Inhabited γ]

namespace Solution
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.deprecated false
set_option maxHeartbeats 2000000

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]

abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
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
lemma refl_star (c : Cfg (Fin 2) (Fin 6)) : c [target_tm]⊢* c := ⟨0, rfl⟩
lemma step_L_p {q q' : Fin 6} {s a b : Fin 2} {l r : zB} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨b, l, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, b >> l, r⟩⟩ [target_tm]⊢⁺ ce := by
  refine z03 ?_ h; simp only [step, ht, Option.map, Tape.write, Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
lemma step_L0_p {q q' : Fin 6} {s a : Fin 2} {r : zB} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨0, default, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, default, r⟩⟩ [target_tm]⊢⁺ ce := by
  rw [← z00]; exact step_L_p ht h
lemma step_R_p {q0 q1 : Fin 6} {s a b : Fin 2} {l r : zB} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q0 s = some (some q1, Stmt.write a Dir.right))
    (h : ⟨some q1, ⟨b, a >> l, r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q0, ⟨s, l, b >> r⟩⟩ [target_tm]⊢⁺ ce := by
  refine z03 ?_ h; simp only [step, ht, Option.map, Tape.write, Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
lemma step_R0_p {q0 q1 : Fin 6} {s a : Fin 2} {l : zB} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q0 s = some (some q1, Stmt.write a Dir.right))
    (h : ⟨some q1, ⟨0, a >> l, default⟩⟩ [target_tm]⊢* ce) :
    ⟨some q0, ⟨s, l, default⟩⟩ [target_tm]⊢⁺ ce := by
  rw [← z00]; exact step_R_p ht h
lemma step_L_s {q q' : Fin 6} {s a b : Fin 2} {l r : zB} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨b, l, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, b >> l, r⟩⟩ [target_tm]⊢* ce := zPs (step_L_p ht h)
lemma step_L0_s {q q' : Fin 6} {s a : Fin 2} {r : zB} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨0, default, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, default, r⟩⟩ [target_tm]⊢* ce := zPs (step_L0_p ht h)
lemma step_R_s {q0 q1 : Fin 6} {s a b : Fin 2} {l r : zB} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q0 s = some (some q1, Stmt.write a Dir.right))
    (h : ⟨some q1, ⟨b, a >> l, r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q0, ⟨s, l, b >> r⟩⟩ [target_tm]⊢* ce := zPs (step_R_p ht h)
lemma step_R0_s {q0 q1 : Fin 6} {s a : Fin 2} {l : zB} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q0 s = some (some q1, Stmt.write a Dir.right))
    (h : ⟨some q1, ⟨0, a >> l, default⟩⟩ [target_tm]⊢* ce) :
    ⟨some q0, ⟨s, l, default⟩⟩ [target_tm]⊢* ce := zPs (step_R0_p ht h)
local macro "finish" : tactic =>
  `(tactic| exact refl_star _)
local macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [Turing.ListBlank.head_cons,zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,z00,zDh,zDt])
lemma step_Lg_p {q q' : Fin 6} {s a : Fin 2} {l r : zB} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨l.head, l.tail, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, l, r⟩⟩ [target_tm]⊢⁺ ce := z03 (by rw [step, ht]; rfl) h
lemma step_Rg_p {q0 q1 : Fin 6} {s a : Fin 2} {l r : zB} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q0 s = some (some q1, Stmt.write a Dir.right))
    (h : ⟨some q1, ⟨r.head, a >> l, r.tail⟩⟩ [target_tm]⊢* ce) :
    ⟨some q0, ⟨s, l, r⟩⟩ [target_tm]⊢⁺ ce := z03 (by rw [step, ht]; rfl) h
lemma step_Lg_s {q q' : Fin 6} {s a : Fin 2} {l r : zB} {ce : Cfg (Fin 2) (Fin 6)}
    (ht : target_tm q s = some (some q', Stmt.write a Dir.left))
    (h : ⟨some q', ⟨l.head, l.tail, a >> r⟩⟩ [target_tm]⊢* ce) :
    ⟨some q, ⟨s, l, r⟩⟩ [target_tm]⊢* ce := zPs (step_Lg_p ht h)
lemma step_Rg_s {q0 q1 : Fin 6} {s a : Fin 2} {l r : zB} {ce : Cfg (Fin 2) (Fin 6)}
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
abbrev t : zF := [1,1,0,0]
abbrev d0 : zF := [0,0]
abbrev d1 : zF := [1,0]
abbrev one : zF := [1]
abbrev lh : zB := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
abbrev w_pre : zF := t ++ one
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
  | .ca => [1,1,1,0,1,0]
def zCR (l : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  ((l <+ zCw c) {{zCs c}}> r)
def zCL (l : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (l <{{D}} ([0] +> r))
abbrev w_init : zF := t ++ (t ++ one)
def zCf (r : zB) : Cfg (Fin 2) (Fin 6) :=
  zCL lh (w_init +> r)
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
lemma zS0 {ls1 ls2 ls3 : List Call} {w1 w2 v1 v2 : zF}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls2 ls3 v1 v2) :
    Seg ls1 ls3 (w1 ++ v1) (w2 ++ v2) := by
  intro r1 r2 h
  rw [append_assoc,append_assoc]
  exact h1 (v1 +> r1) (v2 +> r2) (h2 r1 r2 h)
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
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
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
lemma H_T (n : Nat) : Seg ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t := by
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
lemma z0o (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d0 d0 :=
  zSa z0m n
lemma z0p (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ n) d0 d1 := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg zH0 (zSa z0n n)
lemma z0q (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d1 d1 :=
  zSa z0n n
lemma z0r (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ (1 + n)) d1 d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg zH4 (zSa z0m n)
lemma z0s (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0c z0e) (H_T n)
lemma z0t (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n)) ([.ch,.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0d zH2) (H_T n)
lemma z0u (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using
    zSg (zSg z0g zH2) (H_T n)
lemma z0v (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0h (H_T n)
lemma z0w (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0i (H_T n)
lemma z0x (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using zSg z0j (H_T n)
lemma z0y (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0k (zSg zH1 zH3)
  have h1 := zSg h0 (zSa z0m n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
lemma z0z (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0l (zSa z0m n)
lemma z0A : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0k zH1
lemma z0B (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0k (zSg zH1 (zSg zH3 zH0))
  have h1 := zSg h0 (zSa z0n n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using h1
lemma z0C (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1 := zSg z0l zH0
  have h1 := zSg h0 (zSa z0n n)
  simpa only [zLp',List.cons_append,List.nil_append] using h1
lemma z0D : Side [.ch] default (d1 +> default) := by
  refine Side.cons (fun l => ?_) (Side.nil _)
  unfold zCR zCL zCw zCs d1
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
lemma z0E : Seg [.ca] [.ch,.ch] t ((t ++ [0]) ++ t) :=
  zS5
    (mid1 := [1,0,1,1,1,1,0,1,0])
    (mid2 := [1,0,1,0,1,1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma z0F : Seg [.ca,.ch] ([.cj] ++ [.ch] ^ 5) w_init (w_init ++ t) := by
  have h1a : Seg [.ch,.ch] [.cj,.ch,.ch,.ch] (t ++ one) t :=
    zSg zH2 z0f
  have h1 : Seg [.ca] [.cj,.ch,.ch,.ch] (t ++ (t ++ one)) (((t ++ [0]) ++ t) ++ t) :=
    zS0 z0E h1a
  have h2 : Seg [.ch] [.ch,.ch] (((t ++ [0]) ++ t) ++ t) ((t ++ (t ++ one)) ++ t) :=
    zS0 (zS0 z0e z0d) z0f
  exact zSg h1 h2
lemma z0G (r : zB) :
    (zCL lh r) [target_tm]⊢⁺ (zCR ([1] +> default) .ca r) := by
  unfold zCL zCR lh zCw zCs
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
lemma z0H (r : zB) :
    (zCL ([1] +> default) r) [target_tm]⊢⁺ (zCR lh .ch r) := by
  unfold zCL zCR lh zCw zCs
  simp only [List.cons_append,List.nil_append,append_cons,append_nil,z00]
  execute
open WordCalculus Word
local notation "zW" => List Word
local notation "zR" => List.replicate
lemma loc_z1L {n : Nat} {ds : zW} {A H B : Nat}
    (hD : zDg A H ds) (hSum : A + n = B + 2 ^ H) (hBound : B < 2 ^ H) :
    ∃ v,zDg B H v /\ zEf n (ds ++ [Q]) 1 (v ++ [K]) := by
  rcases z1B ds n with ⟨b,v,hE⟩
  rcases z1G hE hD with ⟨C,hV,hEq⟩
  have hCb := z1b hV
  have hb1 : b = 1 := by
    rcases b with _ | _ | b'
    · omega
    · rfl
    · rw [Nat.add_mul,Nat.add_mul,Nat.one_mul] at hEq
      omega
  subst hb1
  have hCB : C = B := by omega
  subst hCB
  exact ⟨v,hV,z1D hE (@zEf.d11 0 [] 1 [] (zEf.nil 1))⟩
lemma loc_z1M {n : Nat} {u : zW} {b : Nat} {v : zW}
    (hI : zEf n u b v) :
    ((1 + n : Nat) : Rat) <= ((1 + b : Nat) : Rat) * z1h u /\
    ((1 + b : Nat) : Rat) * z1h u <= ((1 + n : Nat) : Rat) + 2 * z1e u := by
  have hBud := z1J hI
  have hW := z1I hI
  have hSu := z1i u
  have hSv := z1i v
  have hNu := zWn u
  have hNv := zWn v
  refine ⟨by linarith,by linarith⟩
lemma loc_z1N (u : zW) (A H : Nat) (ds : zW)
    (hD : zDg A H ds)
    (hHeight : z1h u * ((2 ^ H : Nat) : Rat) = 1)
    (hCut : z0Z u = true)
    (hNe : u ≠ [])
    (hBound : z1e u + z1h u * (1 + z1f ds) <= 1 / 128) :
    ∃ k v a b,zPS 12 (u ++ ds ++ [K]) k v a b /\ 4 < k := by
  have hWu := zWn u
  have hWd := zWn ds
  have hSu := zSp u
  have hEx_in : 8 * z1e u < ((6 * 2 : Nat) : Rat) - 4 := by
    push_cast; nlinarith
  rcases z1R u 6 hEx_in with ⟨k,v,a,b,hI,hK⟩
  rcases z1X hI hCut hNe with ⟨n,rfl⟩
  have hBudget := z1N hI
  have hLoss := z1O hI
  have hSv := z1V hI
  have hPv := zSp v
  have hCarry : 7 < (((n * 2 : Nat) : Rat) - 4) * z1h v := by
    push_cast at hBudget ⊢; nlinarith
  rcases zDw hD with ⟨hSd,hMd,_⟩
  have hRest : 2 * (z1e (ds ++ [K]) + z1f (ds ++ [K])) * z1h v < 7 := by
    rw [z1j,z1k]
    dsimp [z1e,z1f]
    have h1 : z1h u * z1f ds <= 1 / 128 := by nlinarith
    have h2 : z1h u * z1h ds = 1 := by rwa [hSd]
    have h3 : z1h v * z1h ds <= 1 := by nlinarith
    have h4 : z1h v * z1e ds <= 1 := by nlinarith
    have h5 : z1h v * z1f ds <= 1 / 128 := by nlinarith
    nlinarith
  have hTail1 : 2 * (z1e (ds ++ [K]) + z1f (ds ++ [K])) < ((n * 2 : Nat) : Rat) := by
    nlinarith
  have hTail2 : 8 * (1 + 2 * z1f ds) < ((n * 2 : Nat) : Rat) - 4 := by
    have h1 : z1h v * z1f ds <= 1 / 128 := by nlinarith
    have h2 : 8 * (1 + 2 * z1f ds) * z1h v < 1 := by nlinarith
    nlinarith
  rcases z1W (ds ++ [K]) (z1f ds) n (z1v hD) hTail1 hTail2
    with ⟨k',w,c,d,hJ,hK'⟩
  rcases z1P hI hJ with ⟨a',b',hIJ,_,_⟩
  refine ⟨k',v ++ w,a',b',?_,hK'⟩
  simpa [List.append_assoc] using hIJ
lemma loc_z1O (n : Nat) : (0 : Rat) < ((2 ^ n : Nat) : Rat) := by
  exact_mod_cast zPp n
lemma loc_z1P (n : Nat) :
    z1e (zR n V) = 0 /\
    z1h (zR n V) * ((2 ^ n : Nat) : Rat) = 1 := by
  induction n with
  | zero => simp [z1e,z1h]
  | succ n ih =>
    dsimp [List.replicate,z1e,z1h]
    refine ⟨by linarith [ih.1],?_⟩
    have hpow : ((2 ^ (n + 1) : Nat) : Rat) = ((2 ^ n : Nat) : Rat) * 2 := by
      rw [Nat.pow_succ]; push_cast; ring
    rw [hpow]
    linarith [ih.2]
lemma loc_z1Q (n : Nat) (x : Rat) :
    z1h (zR n V) * x * ((2 ^ n : Nat) : Rat) = x := by
  have h := (loc_z1P n).2
  calc z1h (zR n V) * x * ((2 ^ n : Nat) : Rat)
    _ = x * (z1h (zR n V) * ((2 ^ n : Nat) : Rat)) := by ring
    _ = x * 1 := by rw [h]
    _ = x := by ring
lemma loc_z1R {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) :
    ∀ (p q : zW),u = p ++ q -> z10 p q ->
      ∃ c x y s t0,Scan a p c x s /\ Scan c q b y t0 /\
        v = x ++ y /\ l = s + z1h x * t0 := by
  induction h with
  | nil k =>
    intro p q hE _
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨k,[],[],0,0,Scan.nil k,Scan.nil k,rfl,by simp [z1h]⟩
    | cons _ _ => simp at hE
  | T hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.T hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt V p q hP) with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
      exact ⟨c,V :: x,y,s1 * (1 / 2),t1,Scan.T hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | pair0 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.pair0 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := zCt K p q (zCt Q (K :: p) q hP)
        rcases ih p q hE hP' with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
        exact ⟨c,V :: x,y,(1 + s1) * (1 / 2),t1,Scan.pair0 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | pair1 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.pair1 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := zCt Q p q (zCt Q (Q :: p) q hP)
        rcases ih p q hE hP' with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
        exact ⟨c,V :: x,y,(1 / 4) + s1 * (1 / 2),t1,Scan.pair1 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | short00 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short00 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt K p q hP) with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
      exact ⟨c,K :: x,y,1 + s1 * 2,t1,Scan.short00 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | short01 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short01 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt Q p q hP) with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
      exact ⟨c,K :: x,y,s1 * 2,t1,Scan.short01 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | short10 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short10 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt K p q hP) with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
      exact ⟨c,Q :: x,y,1 + s1 * 2,t1,Scan.short10 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | short11 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short11 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt Q p q hP) with ⟨c,x,y,s1,t1,hJ,hK,rfl,hL⟩
      exact ⟨c,Q :: x,y,s1 * 2,t1,Scan.short11 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
lemma loc_z1S (r a b : Nat) (v : zW) (l : Rat) (u : zW) (z : Rat)
    (hI : Scan a ((zR (1 + r * 2) Q ++ [K]) ++ u) b v l)
    (hZ : zTd u z) :
    z1e v * ((2 ^ (1 + r) : Nat) : Rat) <= 1 + 2 * z /\
    (l - 1 / 2) * ((2 ^ (1 + r) : Nat) : Rat) <= 1 + 2 * z := by
  have hCut : z10 (zR (1 + r * 2) Q ++ [K]) u := by
    left; rw [z11]; rfl
  rcases loc_z1R hI (zR (1 + r * 2) Q ++ [K]) u rfl hCut
    with ⟨c,x,y,s,t0,hJ,hK,rfl,hL⟩
  rcases zS1 r a c x s hJ with ⟨rfl,_,rfl⟩
  rcases z1x hK hZ with ⟨hMy,hLy,_⟩
  rcases loc_z1P (1 + r) with ⟨hMx,hSx⟩
  have hF1 := loc_z1Q (1 + r) (z1e y)
  have hF2 := loc_z1Q (1 + r) t0
  have hPos := loc_z1O (1 + r)
  rw [z1j]
  refine ⟨by nlinarith,by nlinarith⟩
lemma loc_z1T (r a b : Nat) (v : zW) (l : Rat) (u : zW) (z : Rat)
    (hI : Scan a ((zR (2 + r * 2) Q ++ [K]) ++ u) b v l)
    (hZ : zTd u z) :
    (z1e v - 1) * ((2 ^ r : Nat) : Rat) <= 1 + 2 * z /\
    (l - 1) * ((2 ^ r : Nat) : Rat) <= 1 + 2 * z := by
  have hCut : z10 (zR (2 + r * 2) Q ++ [K]) u := by
    left; rw [z11]; rfl
  rcases loc_z1R hI (zR (2 + r * 2) Q ++ [K]) u rfl hCut
    with ⟨c,x,y,s,t0,hJ,hK,rfl,hL⟩
  rcases z1r r a c x s hJ with ⟨d,n,rfl,_,rfl⟩
  rcases z1x hK hZ with ⟨hMy,hLy,_⟩
  rcases loc_z1P (1 + r) with ⟨hMx,hSx⟩
  have hF1 := loc_z1Q (1 + r) (z1e y)
  have hF2 := loc_z1Q (1 + r) t0
  have hPos := loc_z1O r
  have hWy := zWn y
  have hPow1 : ((2 ^ (1 + r) : Nat) : Rat) = 2 * ((2 ^ r : Nat) : Rat) := by
    rw [zP2]; push_cast; ring
  cases d <;> (
    dsimp [List.cons_append,z1e,z1h] at hL ⊢
    rw [z1j]
    rw [hPow1] at hF1 hF2
    refine ⟨by nlinarith,by nlinarith⟩
  )
lemma loc_z1U (c a b : Nat) (v : zW) (l : Rat) (u : zW) (z : Rat)
    (hI : Scan a ((zR c Q ++ [K]) ++ u) b v l)
    (hZ : zTd u z) (hC : 0 < c) :
    z1e v * ((2 ^ (c + c / 2) : Nat) : Rat) <= ((2 ^ (c + c / 2) : Nat) : Rat) + 2 * ((2 ^ c : Nat) : Rat) * (1 + 2 * z) /\
    l * ((2 ^ (c + c / 2) : Nat) : Rat) <= ((2 ^ (c + c / 2) : Nat) : Rat) + 2 * ((2 ^ c : Nat) : Rat) * (1 + 2 * z) := by
  have hZn := z1t hZ
  rcases z0U c with ⟨a0,rfl⟩ | ⟨a0,rfl⟩
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
      rw [zP2]; push_cast; ring
    rw [hPow1] at hM hL
    have hp1 := loc_z1O (1 + a0 * 2)
    have hp2 := loc_z1O a0
    rw [hPow]
    refine ⟨by nlinarith,by nlinarith⟩
lemma loc_z1V (c : Nat) :
    ∀ (u : zW) (z : Rat),zTd (zR c Q ++ u) z ->
      ∃ z',zTd u z' /\ z = ((2 ^ c : Nat) : Rat) * z' := by
  induction c with
  | zero =>
    intro u z hI
    exact ⟨z,hI,by simp⟩
  | succ c ih =>
    intro u z hI
    dsimp [List.replicate] at hI
    rcases zTo hI with ⟨y,hJ,rfl⟩
    rcases ih u y hJ with ⟨x,hK,rfl⟩
    refine ⟨x,hK,?_⟩
    rw [Nat.pow_succ]; push_cast; ring
lemma loc_z1W (x z p q : Rat) (hp : 0 < p) (hpq : p <= q) (hz : 0 <= z)
    (h : x * q <= q + 2 * z) : x * p <= p + 2 * z := by
  rcases le_or_gt x 1 with hle | hgt
  · nlinarith
  · nlinarith
lemma loc_z1X (s c : Nat) (u : zW) (A H a b : Nat) (v : zW) (l : Rat)
    (hD : zDg A H (zR c Q ++ K :: u))
    (hI : Scan a ((zR c Q ++ K :: u) ++ [K]) b v l)
    (hC : 0 < c) (hSC : s <= c) :
    z1e v * ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f (zR c Q ++ K :: u) /\
    l * ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f (zR c Q ++ K :: u) := by
  have hZ := z1v hD
  rw [List.append_assoc] at hZ
  rcases loc_z1V c (K :: u ++ [K]) (z1f (zR c Q ++ K :: u)) hZ with ⟨x,hU,hX⟩
  rcases z1u hU with ⟨hNil,_⟩ | ⟨z,hV,rfl⟩
  · simp at hNil
  · have hE : (zR c Q ++ K :: u) ++ [K] =
        (zR c Q ++ [K]) ++ (u ++ [K]) := by
      simp [List.append_assoc]
    rw [hE] at hI
    rcases loc_z1U c a b v l (u ++ [K]) z hI hV hC with ⟨hM,hL⟩
    have hPos := loc_z1O (s + s / 2)
    have hMono_nat : 2 ^ (s + s / 2) <= 2 ^ (c + c / 2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hMono : ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (c + c / 2) : Nat) : Rat) := by
      exact_mod_cast hMono_nat
    have hW := (zWn (zR c Q ++ K :: u)).2.1
    refine ⟨loc_z1W (z1e v) (z1f (zR c Q ++ K :: u)) _ _ hPos hMono hW (by linarith),
            loc_z1W l (z1f (zR c Q ++ K :: u)) _ _ hPos hMono hW (by linarith)⟩
lemma loc_z1Y (s : Nat) (ds : zW) (A H k k' : Nat) (v : zW) (a b : Rat)
    (hD : zDg A H ds)
    (hI : zPS k (ds ++ [K]) k' v a b)
    (hLow : ∃ c u,(0 < c /\ s <= c) /\ ds = zR c Q ++ K :: u) :
    z1e v * ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds /\
    a * ((2 ^ (s + s / 2) : Nat) : Rat) <= 4 * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds) /\
    b * ((2 ^ (s + s / 2) : Nat) : Rat) <= 3 * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds) := by
  rcases hLow with ⟨c,u,⟨hC,hSC⟩,rfl⟩
  have hFull := z19 hD (zDg.zero zDg.nil)
  rcases z1T hI hFull with ⟨l,hJ,hP,hN⟩
  rcases loc_z1X s c u A H k k' v l hD hJ hC hSC with ⟨hM,hL⟩
  have hPos := loc_z1O (s + s / 2)
  refine ⟨hM,by nlinarith,by nlinarith⟩
lemma loc_z1Z (r J k b A B : Nat)
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
lemma loc_z20 (s : Nat) :
    ∀ (B H : Nat) (ds : zW),
      zDg B H ds -> s <= H -> (∃ n,1 + B = n * 2 ^ s) ->
      ∃ u,ds = zR s Q ++ u := by
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
lemma loc_z21 (p : Nat) :
    ∀ (n : Nat) (u : zW) (b : Nat) (v : zW),
      zEf n (zR p V ++ u) b v ->
      ∃ q w,v = zR p V ++ w /\ 1 + q = (1 + n) * 2 ^ p /\ zEf q u b w := by
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
lemma loc_z22 (n : Nat) (w : Word) :
    zR (1 + n) w = w :: zR n w := by
  rw [Nat.add_comm 1 n,List.replicate_succ]
lemma loc_z23 (p : Nat) (u : zW) (b : Nat) (v : zW)
    (hI : zEf 0 (zR (1 + p) V ++ Q :: u) b v) :
    ∃ w,v = zR (1 + p) V ++ K :: w /\ zEf (2 ^ p) u b w := by
  rcases loc_z21 (1 + p) 0 (Q :: u) b v hI with ⟨q,w0,rfl,hEq,hJ⟩
  have hp := zPp p
  have hpow : 2 ^ (1 + p) = 2 ^ p + 2 ^ p := zP2 p
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
lemma loc_z24 (p : Nat) (u : zW) (k : Nat) (v : zW) (a b : Rat)
    (hI : zPS 12 (zR p V ++ K :: u) k v a b) :
    ∃ w a' b',v = zR p V ++ Q :: w /\
      zPS (4 * 2 ^ p) u k w a' b' /\
      a = z1h (zR p V) * (4 + 2 * a') /\
      b = z1h (zR p V) * (2 * b') := by
  rcases z1Y hI (zR p V) (K :: u) rfl (Or.inl (z12 p))
    with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
  rcases z20 p 12 m x a1 b1 hJ with ⟨rfl,hEq,rfl,rfl⟩
  have hp := zPp p
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
lemma loc_z25 (r k : Nat) (u : zW) (k' : Nat) (v : zW) (a b : Rat)
    (carry : Nat) (eff : zW) (A B J : Nat) (ds : zW)
    (hI : zPS k (u ++ zR (1 + r * 2) Q ++ [K]) k' v a b)
    (hE : zEf 0 (V :: (v ++ [V])) carry eff)
    (hD : zDg B J ds) (hR : 1 + r <= J)
    (hAsum : A + 2 ^ J = k') (hBsum : B + 2 ^ J = A + carry) :
    ∃ w,ds = zR (1 + r) Q ++ w := by
  rcases z1Z r k u k' v a b hI with ⟨w,n,rfl,hK⟩
  have hEq : V :: ((w ++ zR (1 + r) V) ++ [V]) =
      (V :: w) ++ zR (2 + r) V := by
    have h1 : 2 + r = (1 + r) + 1 := by omega
    rw [h1,z13]; simp [List.append_assoc]
  rw [hEq] at hE
  rcases z1L (V :: w) (2 + r) 0 carry eff hE with ⟨x,m,_,hC⟩
  apply loc_z20 (1 + r) B J ds hD hR
  refine loc_z1Z (1 + r) J k' carry A B hR ⟨n,hK⟩ ⟨m * 2,?_⟩ hAsum hBsum
  have h2 : 2 + r = (1 + r) + 1 := by omega
  rw [h2,Nat.pow_succ] at hC
  linarith
lemma loc_z26 (x p q s f : Rat) (hp : 0 < p) (hs : 0 <= s)
    (h1 : x * p <= q) (h2 : s * q <= f * p) : s * x <= f := by
  nlinarith
lemma loc_z27 (s : Nat) (ds : zW) (A H k k' : Nat) (v : zW) (a b sigma f : Rat)
    (hD : zDg A H ds) (hI : zPS k (ds ++ [K]) k' v a b)
    (hLow : ∃ c u,(0 < c /\ s <= c) /\ ds = zR c Q ++ K :: u)
    (hSig : 0 <= sigma)
    (hBound : sigma * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds) <= f * ((2 ^ (s + s / 2) : Nat) : Rat)) :
    sigma * z1e v <= f /\ sigma * a <= 4 * f /\ sigma * b <= 3 * f := by
  rcases loc_z1Y s ds A H k k' v a b hD hI hLow with ⟨hM,hP,hN⟩
  have hPos := loc_z1O (s + s / 2)
  refine ⟨loc_z26 (z1e v) _ _ sigma f hPos hSig hM hBound,
          loc_z26 a _ _ sigma (4 * f) hPos hSig hP (by linarith),
          loc_z26 b _ _ sigma (3 * f) hPos hSig hN (by linarith)⟩
lemma le_of_mul_le_mul_pos_right {a b u : Rat} (hu : 0 < u) (h : a * u <= b * u) : a <= b := by
  by_contra hlt
  have : b < a := not_le.mp hlt
  nlinarith
lemma lt_of_mul_lt_mul_pos_right {a b u : Rat} (hu : 0 < u) (h : a * u < b * u) : a < b := by
  by_contra hle
  have : b <= a := not_lt.mp hle
  nlinarith
lemma loc_z28 (a b : Nat) : ((2 ^ (a + b) : Nat) : Rat) = ((2 ^ a : Nat) : Rat) * ((2 ^ b : Nat) : Rat) := by
  rw [Nat.pow_add,Nat.cast_mul]
lemma loc_z29 : ((2 ^ 2 : Nat) : Rat) = 4 := by norm_num
lemma loc_z2a : ((2 ^ 10 : Nat) : Rat) = 1024 := by norm_num
lemma loc_z2b (p : Nat) (u ds : zW) (A H k : Nat) (v : zW) (a b : Rat) (s : Nat) (e f : Rat)
    (hI : zPS 12 (zR p V ++ K :: (u ++ ds ++ [K])) k v a b)
    (hD : zDg A H ds) (hCut : z0Z u = true)
    (hLow : ∃ c w,(0 < c /\ s <= c) /\ ds = zR c Q ++ K :: w)
    (hError : e = 2 * z1h (zR p V) * z1e u)
    (hBound : (2 * z1h (zR p V) * z1h u) * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds) <= f * ((2 ^ (s + s / 2) : Nat) : Rat)) :
    ∃ w,v = zR p V ++ Q :: w /\
      z1e (V :: (v ++ [V])) <= z1h (zR p V) * (1 / 2) + (e + f) * (1 / 2) /\
      4 * z1h (zR p V) - e * (1 / 4) - 3 * f <= a - b /\
      a - b <= 4 * z1h (zR p V) + 4 * e + 4 * f := by
  rcases loc_z24 p (u ++ ds ++ [K]) k v a b hI with ⟨w,c,d,rfl,hJ,hPos,hNeg⟩
  have hEq_u : u ++ ds ++ [K] = u ++ (ds ++ [K]) := by simp [List.append_assoc]
  rw [hEq_u] at hJ
  rcases z1Y hJ u (ds ++ [K]) rfl (Or.inl hCut)
    with ⟨m,x,y,a1,b1,a2,b2,hK,hL,rfl,hC,hDlt⟩
  have hBounds := z1O hK
  have hTailBounds := z1O hL
  have hScale := z1V hK
  have hSu := zSp u
  have hSx := zSp x
  have hSp := zSp (zR p V)
  have hWds := zWn ds
  have hPow := loc_z1O (s + s / 2)
  have h1 : 2 * z1h (zR p V) * z1h x <= 2 * z1h (zR p V) * z1h u := by nlinarith
  have h2 : 0 <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds := by linarith
  have hF : (2 * z1h (zR p V) * z1h x) * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds) <=
      f * ((2 ^ (s + s / 2) : Nat) : Rat) := by
    nlinarith
  rcases loc_z27 s ds A H m k y a2 b2 (2 * z1h (zR p V) * z1h x) f hD hL hLow (by positivity) hF
    with ⟨hMt,hPt,hNt⟩
  have hPa : 0 <= (2 * z1h (zR p V) * z1h x) * a2 := by
    have : 0 <= a2 := hTailBounds.2.1
    positivity
  have hPb : 0 <= (2 * z1h (zR p V) * z1h x) * b2 := by
    have : 0 <= b2 := hTailBounds.2.2.2.1
    positivity
  have hA1 : 0 <= 2 * z1h (zR p V) * a1 := by
    have : 0 <= a1 := hBounds.2.1
    positivity
  have hA1u : 2 * z1h (zR p V) * a1 <= 4 * e := by
    have : a1 <= 4 * z1e u := hBounds.2.2.1
    nlinarith
  have hB1 : 0 <= 2 * z1h (zR p V) * b1 := by
    have : 0 <= b1 := hBounds.2.2.2.1
    positivity
  have hB1u : 2 * z1h (zR p V) * b1 <= e * (1 / 4) := by
    have : b1 <= z1e u * (1 / 4) := hBounds.2.2.2.2
    nlinarith
  have hMx : 2 * z1h (zR p V) * z1e x <= e := by
    have : z1e x <= z1e u := hBounds.1
    nlinarith
  have hMassP := (loc_z1P p).1
  have hAb_eq : a - b = 4 * z1h (zR p V) +
      2 * z1h (zR p V) * a1 +
      (2 * z1h (zR p V) * z1h x) * a2 -
      2 * z1h (zR p V) * b1 -
      (2 * z1h (zR p V) * z1h x) * b2 := by
    rw [hPos,hNeg,hC,hDlt]; ring
  refine ⟨x ++ y,rfl,?_,?_,?_⟩
  · have hE1 : z1e (V :: ((zR p V ++ Q :: (x ++ y)) ++ [V])) =
        z1h (zR p V) * (1 / 2) +
        (2 * z1h (zR p V) * z1e x + (2 * z1h (zR p V) * z1h x) * z1e y) * (1 / 2) := by
      simp only [List.cons_append,List.append_assoc,z1e,z1j,z1h,hMassP]
      ring
    rw [hE1]
    linarith
  · rw [hAb_eq]; linarith
  · rw [hAb_eq]; linarith
lemma loc_z2c (p : Nat) (u : zW) (b : Nat) (v : zW)
    (hI : zEf 0 (zR (1 + p) V ++ Q :: u) b v) :
    2 * z1h (zR (1 + p) V) <=
      ((1 + b : Nat) : Rat) * z1h (zR (1 + p) V ++ Q :: u) - 1 /\
    ((1 + b : Nat) : Rat) * z1h (zR (1 + p) V ++ Q :: u) - 1 <=
      2 * z1e (zR (1 + p) V ++ Q :: u) := by
  rcases loc_z23 p u b v hI with ⟨w,rfl,hE⟩
  rcases loc_z1M hE with ⟨hLo,hHi⟩
  have hSp := zSp (zR (1 + p) V)
  rcases loc_z1P (1 + p) with ⟨hM,hS⟩
  have hS' : z1h (zR (1 + p) V) * (2 * ((2 ^ p : Nat) : Rat)) = 1 := by
    rw [zP2,Nat.cast_add] at hS
    linarith
  have htmp : ((1 + 2 ^ p : Nat) : Rat) = 1 + ((2 ^ p : Nat) : Rat) := by
    rw [Nat.cast_add,Nat.cast_one]
  rw [htmp] at hLo hHi
  have h1 : ((1 + b : Nat) : Rat) * z1h (zR (1 + p) V ++ Q :: u) =
      2 * z1h (zR (1 + p) V) * (((1 + b : Nat) : Rat) * z1h u) := by
    rw [z1m]; dsimp [z1h]; ring
  have h2 : 2 * z1e (zR (1 + p) V ++ Q :: u) =
      2 * z1h (zR (1 + p) V) * (1 + 2 * z1e u) := by
    rw [z1j,hM]; dsimp [z1e]; ring
  rw [h1,h2]
  refine ⟨by nlinarith,by nlinarith⟩
lemma loc_z2d (alpha e f unit delta R e' : Rat)
    (_ : 0 < alpha) (_ : 0 <= e) (_ : 0 <= f) (_ : 0 <= unit)
    (_ : e <= alpha * (3 / 64)) (_ : f <= alpha * (1 / 128)) (_ : unit <= alpha * (1 / 1024))
    (_ : 0 <= e') (_ : e' <= (e + f) * (1 / 2)) (_ : alpha <= R) (_ : R <= alpha + 2 * e')
    (_ : 4 * alpha - e * (1 / 4) - 3 * f <= delta) (_ : delta <= 4 * alpha + 4 * e + 4 * f) :
    (3 / 4) * alpha <= delta * (1 / 2) - 4 * unit - R /\
    delta * (1 / 2) - 4 * unit - R <= (5 / 4) * alpha := by
  exact ⟨by linarith,by linarith⟩
lemma loc_z2e {u : zW} {k : Nat} {v : zW} {a b : Rat}
    (hI : zPS 12 u k v a b) :
    (k : Rat) * z1h (V :: (v ++ [V])) =
      2 + 4 * z1h (V :: (v ++ [V])) - (a - b) * (1 / 2) := by
  have hEq := z1N hI
  push_cast at hEq
  dsimp [z1h]
  rw [z1m]
  dsimp [z1h]
  linarith
lemma loc_z2f {u : zW} {k : Nat} {v : zW} {a b : Rat} {J A B carry : Nat}
    (hI : zPS 12 u k v a b)
    (hHeight : z1h (V :: (v ++ [V])) * ((2 ^ J : Nat) : Rat) = 1)
    (hAsum : A + 2 ^ J = k)
    (hBsum : B + 2 ^ J = A + carry) :
    1 - ((1 + B : Nat) : Rat) * z1h (V :: (v ++ [V])) =
      (a - b) * (1 / 2) - 4 * z1h (V :: (v ++ [V])) -
      (((1 + carry : Nat) : Rat) * z1h (V :: (v ++ [V])) - 1) := by
  have hBudget := loc_z2e hI
  have hSum : B + 2 ^ J + 2 ^ J = k + carry := by omega
  have hQsum : ((B + 2 ^ J + 2 ^ J : Nat) : Rat) = ((k + carry : Nat) : Rat) := by exact_mod_cast hSum
  rw [Nat.cast_add,Nat.cast_add,Nat.cast_add] at hQsum
  have hQ_u : ((B : Rat) + ((2 ^ J : Nat) : Rat) + ((2 ^ J : Nat) : Rat)) * z1h (V :: (v ++ [V])) =
      ((k : Rat) + (carry : Rat)) * z1h (V :: (v ++ [V])) := by rw [hQsum]
  rw [Nat.cast_add,Nat.cast_one,Nat.cast_add,Nat.cast_one]
  linarith
lemma loc_z2g (J k carry : Nat) (alpha unit delta R : Rat)
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
lemma loc_z2h {p : Nat} {tau : Rat} (hI : loc_Reserve p tau) :
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
    rw [zP2,Nat.cast_add]; linarith
lemma loc_z2i {p : Nat} {tau : Rat} (hI : loc_Reserve p tau) (hP : 16 <= p) :
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
lemma loc_z2j (p n H s : Nat)
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
lemma loc_z2k (alpha unit f t0 q tau : Rat)
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
lemma loc_z2l (t0 q h alpha unit : Rat)
    (hQ : 0 < q) (_ : 0 <= unit)
    (hAq : alpha * q = 1) (hUh : unit * h = 1)
    (hLe : 4 * q * t0 <= h) :
    4 * t0 * unit <= alpha := by
  have h1 : (4 * q * t0) * unit <= h * unit := by nlinarith
  have h2 : (4 * t0 * unit) * q <= alpha * q := by linarith
  exact le_of_mul_le_mul_pos_right hQ h2
lemma loc_z2m (p H s : Nat) (alpha unit tau f : Rat)
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
lemma loc_z2n (p : Nat) (hP : 16 <= p) :
    (p + 1) + (p + 1) / 2 + 9 <= 1 + 3 * (((p - 2) / 2 + 1) / 2) + 3 * ((p - 1) / 2) := by
  omega
lemma loc_z2o (alpha tau tau' e f e' : Rat)
    (_ : 0 <= alpha) (_ : tau' <= (3 / 4) * tau)
    (_ : e <= alpha * ((3 / 64) - tau)) (_ : f <= alpha * tau * (1 / 4))
    (_ : e' <= (e + f) * (1 / 2)) :
    e' <= (alpha * (1 / 2)) * ((3 / 64) - tau') := by
  nlinarith
lemma loc_z2p {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k u k' v a b) :
    ∃ g,z1h u = z1h v * ((8 ^ g : Nat) : Rat) /\ u.length = v.length + g := by
  induction hI with
  | nil _ => exact ⟨0,by simp [z1h],rfl⟩
  | T _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring,by dsimp; omega⟩
  | pair0 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    refine ⟨1 + g,?_,by dsimp; omega⟩
    have h8 : ((8 ^ (1 + g) : Nat) : Rat) = 8 * ((8 ^ g : Nat) : Rat) := by
      rw [Nat.add_comm 1 g,Nat.pow_succ]; push_cast; ring
    dsimp [z1h]; rw [h8,hE]; ring
  | pair1 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    refine ⟨1 + g,?_,by dsimp; omega⟩
    have h8 : ((8 ^ (1 + g) : Nat) : Rat) = 8 * ((8 ^ g : Nat) : Rat) := by
      rw [Nat.add_comm 1 g,Nat.pow_succ]; push_cast; ring
    dsimp [z1h]; rw [h8,hE]; ring
  | short00 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring,by dsimp; omega⟩
  | short01 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring,by dsimp; omega⟩
  | short10 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring,by dsimp; omega⟩
  | short11 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring,by dsimp; omega⟩
lemma loc_z2q {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k u k' v a b) : v.length <= u.length := by
  rcases loc_z2p hI with ⟨g,_,hL⟩
  omega
lemma loc_z2r (c k k' : Nat) (v : zW) (l : Rat)
    (hC : 0 < c) (hI : Scan k (zR c Q ++ [K]) k' v l) :
    v.length + (c + 1) / 2 = c + 1 := by
  rcases z0U c with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · cases r with
    | zero => omega
    | succ r =>
      have heq : (r + 1) * 2 = 2 + r * 2 := by omega
      rw [heq] at hI
      rcases z1r r k k' v l hI with ⟨d,n,rfl,_,_⟩
      simp; try omega
  · rcases zS1 r k k' v l hI with ⟨rfl,_,_⟩
    simp; try omega
lemma loc_z2s (c k k' : Nat) (v : zW) (a b : Rat)
    (hC : 0 < c) (hI : zPS k (zR c Q ++ [K]) k' v a b) :
    v.length + (c + 1) / 2 = c + 1 := by
  have hD := z19 (z1a c) (zDg.zero zDg.nil)
  rcases z1T hI hD with ⟨l,hJ,_,_⟩
  exact loc_z2r c k k' v l hC hJ
lemma loc_z2t (k : Nat) (u : zW) (c : Nat) (mid : zW) (t0 k' : Nat) (v : zW) (a b : Rat)
    (hC : 0 < c) (hT : 0 < t0) (hU : z0Z u = true) (hM : z0Z mid = true)
    (hI : zPS k (u ++ zR c Q ++ K :: (mid ++ zR t0 Q ++ [K])) k' v a b) :
    ∃ g,z1h (u ++ zR c Q ++ K :: (mid ++ zR t0 Q ++ [K])) =
      z1h v * ((8 ^ g : Nat) : Rat) /\ (c + 1) / 2 + (t0 + 1) / 2 <= g := by
  rcases loc_z2p hI with ⟨g,hG,hL⟩
  refine ⟨g,hG,?_⟩
  have hE0 : u ++ zR c Q ++ K :: (mid ++ zR t0 Q ++ [K]) =
      u ++ (zR c Q ++ K :: (mid ++ zR t0 Q ++ [K])) := by
    simp [List.append_assoc]
  rw [hE0] at hI
  rcases z1Y hI u _ rfl (Or.inl hU) with ⟨m,x,y,_,_,_,_,hJ,hK,hV,_,_⟩
  have hSplit : zR c Q ++ K :: (mid ++ zR t0 Q ++ [K]) =
      (zR c Q ++ [K]) ++ (mid ++ (zR t0 Q ++ [K])) := by
    simp [List.append_assoc]
  have hCut1 : z10 (zR c Q ++ [K]) (mid ++ (zR t0 Q ++ [K])) := by
    left; rw [z11]; rfl
  rcases z1Y hK _ _ hSplit hCut1 with ⟨m1,x1,y1,_,_,_,_,hJ1,hK1,hV1,_,_⟩
  rcases z1Y hK1 mid (zR t0 Q ++ [K]) rfl (Or.inl hM)
    with ⟨m2,x2,y2,_,_,_,_,hJ2,hK2,hV2,_,_⟩
  have hL_x := loc_z2q hJ
  have hL_x2 := loc_z2q hJ2
  have hL_x1 := loc_z2s c m m1 x1 _ _ hC hJ1
  have hL_y2 := loc_z2s t0 m2 k' y2 _ _ hT hK2
  rw [hV,hV1,hV2] at hL
  simp only [List.length_append,List.length_cons,List.length_replicate,List.length_nil] at hL hL_x1 hL_y2
  omega
lemma loc_z2u (n : Nat) : 8 ^ n = 2 ^ (3 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq : 3 * (n + 1) = 3 * n + 3 := by omega
    rw [Nat.pow_succ,heq,Nat.pow_add,ih]
lemma loc_z2v (u ds : zW) (A H k k' : Nat) (v : zW) (a b : Rat)
    (p c : Nat) (mid : zW) (t0 : Nat)
    (hD : zDg A H ds) (hHeight : z1h u * ((2 ^ H : Nat) : Rat) = 1)
    (hI : zPS k (u ++ ds ++ [K]) k' v a b)
    (hU : z0Z u = true) (hM : z0Z mid = true)
    (hDs : ds = zR c Q ++ K :: (mid ++ zR t0 Q))
    (hP : 16 <= p) (hC : (p - 2) / 2 <= c) (hT : p - 2 <= t0) :
    ∃ J,(p + 1) + (p + 1) / 2 + 9 <= J /\ z1h (V :: (v ++ [V])) * ((2 ^ J : Nat) : Rat) = 1 := by
  have hEq : u ++ ds ++ [K] = u ++ zR c Q ++ K :: (mid ++ zR t0 Q ++ [K]) := by
    rw [hDs]; simp [List.append_assoc]
  have hI' : zPS k (u ++ zR c Q ++ K :: (mid ++ zR t0 Q ++ [K])) k' v a b := by
    rwa [<- hEq]
  rcases loc_z2t k u c mid t0 k' v a b (by omega) (by omega) hU hM hI' with ⟨g,hGain,hCount⟩
  rw [<- hEq] at hGain
  refine ⟨1 + 3 * g,?_,?_⟩
  · have hArith := loc_z2n p hP
    omega
  · have hWidth := (zDw hD).1
    have hG1 : z1h (u ++ ds ++ [K]) = z1h u * z1h ds * 2 := by
      rw [z1m,z1m]; dsimp [z1h]; ring
    rw [hG1] at hGain
    have hG2 : z1h (V :: (v ++ [V])) = z1h v * (1 / 4) := by
      dsimp [z1h]; rw [z1m]; dsimp [z1h]; ring
    rw [hG2,zP2,<- loc_z2u,Nat.cast_add]
    calc z1h v * (1 / 4) * (((8 ^ g : Nat) : Rat) + ((8 ^ g : Nat) : Rat))
      _ = (z1h v * ((8 ^ g : Nat) : Rat)) * (1 / 2) := by ring
      _ = (z1h u * z1h ds * 2) * (1 / 2) := by rw [<- hGain]
      _ = z1h u * z1h ds := by ring
      _ = z1h u * ((2 ^ H : Nat) : Rat) := by rw [hWidth]
      _ = 1 := hHeight
lemma loc_z2w (p H : Nat) (alpha unit : Rat)
    (hPH : p + 10 <= H) (hA : 0 < alpha) (hU : 0 < unit)
    (hAp : alpha * ((2 ^ p : Nat) : Rat) = 1) (hUh : unit * ((2 ^ H : Nat) : Rat) = 1) :
    unit <= alpha * (1 / 1024) := by
  have hHigh_nat : 2 ^ (p + 10) <= 2 ^ H := Nat.pow_le_pow_right (by decide) hPH
  have hHigh_q : ((2 ^ (p + 10) : Nat) : Rat) <= ((2 ^ H : Nat) : Rat) := by exact_mod_cast hHigh_nat
  rw [loc_z28 p 10,loc_z2a] at hHigh_q
  have h1 : unit * (((2 ^ p : Nat) : Rat) * 1024) <= unit * ((2 ^ H : Nat) : Rat) := by nlinarith
  have h2 : unit * ((2 ^ p : Nat) : Rat) <= (alpha * (1 / 1024)) * ((2 ^ p : Nat) : Rat) := by linarith
  exact le_of_mul_le_mul_pos_right (loc_z1O p) h2
lemma loc_z2x (p J : Nat) (alpha unit : Rat)
    (hP : 16 <= p) (hJ : (p + 1) + (p + 1) / 2 + 9 <= J)
    (hA : 0 < alpha) (hU : 0 < unit)
    (hAp : alpha * ((2 ^ p : Nat) : Rat) = 1) (hUj : unit * ((2 ^ J : Nat) : Rat) = 1) :
    unit <= alpha * (1 / 1024) :=
  loc_z2w p J alpha unit (by omega) hA hU hAp hUj
lemma loc_z2y (p H : Nat) (alpha unit : Rat)
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
lemma loc_z2z (n t0 B : Nat) (ds : zW)
    (hD : zDg B (n + t0) ds) (hL : 2 ^ (n + t0) <= B + 2 ^ n) :
    ∃ u,ds = u ++ zR t0 Q := by
  have hBound := z1b hD
  have hPos := zPp t0
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
  rcases z18 n a ha_lt with ⟨u,hU⟩
  refine ⟨u,z1d hD ?_⟩
  rw [<- hSum]
  exact z19 hU (z1a t0)
lemma loc_z2A (p H B : Nat) (ds : zW) (alpha unit : Rat)
    (hD : zDg B H ds) (hP : 2 <= p) (hPH : p <= H)
    (_ : 0 < alpha) (hU : 0 < unit) (_ : unit <= alpha)
    (hAp : alpha * ((2 ^ p : Nat) : Rat) = 1) (hUh : unit * ((2 ^ H : Nat) : Rat) = 1)
    (hDeficit : unit * z1f ds <= (5 / 2) * alpha) :
    ∃ u,ds = u ++ zR (p - 2) Q := by
  have hShift : unit * ((2 ^ (H - (p - 2)) : Nat) : Rat) = 4 * alpha := by
    have heq : H - (p - 2) = (H - p) + 2 := by omega
    rw [heq,loc_z28 (H - p) 2,loc_z29]
    have hd := loc_z2y p H alpha unit hPH hAp hUh
    linarith
  have hZ := z1n hD
  have hH_split : (H - (p - 2)) + (p - 2) = H := by omega
  have hD' : zDg B ((H - (p - 2)) + (p - 2)) ds := by rwa [hH_split]
  apply loc_z2z (H - (p - 2)) (p - 2) B ds hD'
  have hZ_u : (B : Rat) * unit + unit + unit * z1f ds = 1 := by
    calc (B : Rat) * unit + unit + unit * z1f ds
      _ = unit * (z1f ds + (B : Rat) + 1) := by ring
      _ = unit * ((2 ^ H : Nat) : Rat) := by rw [hZ]
      _ = 1 := hUh
  have hL_u : ((2 ^ H : Nat) : Rat) * unit <= ((B + 2 ^ (H - (p - 2)) : Nat) : Rat) * unit := by
    rw [Nat.cast_add]; linarith
  have hL_q : ((2 ^ ((H - (p - 2)) + (p - 2)) : Nat) : Rat) <= ((B + 2 ^ (H - (p - 2)) : Nat) : Rat) := by
    rw [hH_split]
    exact le_of_mul_le_mul_pos_right hU hL_u
  exact_mod_cast hL_q
lemma loc_z2B {B H : Nat} {ds : zW} (hI : zDg B H ds) (hZ : 0 < z1f ds) :
    ∃ c w,ds = zR c Q ++ K :: w := by
  induction hI with
  | nil => dsimp [z1f] at hZ; linarith
  | @zero A H u _ _ => exact ⟨0,u,rfl⟩
  | @one A H u _ ih =>
    dsimp [z1f] at hZ
    rcases ih (by linarith) with ⟨c,w,rfl⟩
    exact ⟨c + 1,w,rfl⟩
lemma loc_z2C (c : Nat) :
    ∀ (s : Nat) (u v : zW),
      zR s Q ++ u = zR c Q ++ K :: v -> s <= c := by
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
lemma loc_z2D (u v : zW) (c s : Nat)
    (hC : z0Z u = true)
    (hE : u ++ zR c Q = v ++ zR s Q) : s <= c := by
  by_contra hGt
  have hlt : c < s := by omega
  have h_eq : s = (s - c) + c := by omega
  rw [h_eq,List.replicate_add,<- List.append_assoc] at hE
  have hU := List.append_inj_left' hE rfl
  subst hU
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : s - c ≠ 0) with ⟨n,hn⟩
  rw [hn,z13,<- List.append_assoc,z11] at hC
  contradiction
lemma loc_z2E (u v : zW) (h : z0Z (u ++ v) = true) : z0Z v = true := by
  induction u with
  | nil => exact h
  | cons w u ih => exact ih (zCo w (u ++ v) h)
lemma loc_z2F {n : Nat} {u : zW} {b : Nat} {v : zW}
    (hI : zEf n u b v) (hEnd : ∃ w,u = w ++ [V]) :
    ∃ w,v = w ++ [V] := by
  rcases hEnd with ⟨w,rfl⟩
  rcases z1L w 1 n b v hI with ⟨x,m,hE,_⟩
  exact ⟨x,hE⟩
lemma loc_z2G (p : Nat) (u : zW) :
    z1e (zR p V ++ Q :: u) = z1h (zR p V) * (1 + 2 * z1e u) := by
  rw [z1j]
  dsimp [z1e]
  have h := (loc_z1P p).1
  linarith
lemma loc_z2H (p : Nat) (hP : 16 <= p) :
    z1h (zR p V) <= 1 / 65536 := by
  have h1 := (loc_z1P p).2
  have h2 := zSp (zR p V)
  have hle : 2 ^ 16 <= 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
  have hq : (65536 : Rat) <= ((2 ^ p : Nat) : Rat) := by exact_mod_cast hle
  nlinarith
inductive Good : Nat -> zW -> Prop where
  | intro (p H : Nat) (u : zW) (A : Nat) (da : zW) (carry : Nat) (eff : zW)
      (B : Nat) (db : zW) (tau : Rat) :
      16 <= p -> p + p / 2 + 9 <= H ->
      (∃ rest,u = zR p V ++ Q :: rest) ->
      (∃ rest,u = rest ++ [V]) ->
      z1h u * ((2 ^ H : Nat) : Rat) = 1 ->
      zDg A H da ->
      zEf 0 u carry eff ->
      A + carry = B + 2 ^ H ->
      zDg B H db ->
      loc_Reserve p tau ->
      z1e u <= z1h (zR p V) * (1 + (3 / 64) - tau) ->
      (3 / 2) * z1h (zR p V) <= z1h u * z1f db ->
      z1h u * z1f db <= (5 / 2) * z1h (zR p V) ->
      (∃ rest,db = zR ((p - 2) / 2) Q ++ rest) ->
      Good p (u ++ da ++ [Q])
inductive loc_Step : zW -> zW -> Prop where
  | intro (orig eff : zW) (k : Nat) (v : zW) (a b : Rat) (J A : Nat) (da : zW) :
      zEf 0 orig 1 eff ->
      zPS 12 eff k v a b ->
      zDg A J da ->
      A + 2 ^ J = k ->
      loc_Step orig (V :: (v ++ V :: (da ++ [Q])))
lemma loc_z2I (c : Nat) (mid : zW) (hM : z0Z mid = true) :
    z0Z (zR c Q ++ K :: mid) = true := by
  cases mid with
  | nil => rw [z11]; rfl
  | cons x xs =>
    induction c with
    | zero => exact hM
    | succ c ih =>
      cases c with
      | zero => exact hM
      | succ c' => exact ih
lemma loc_z2J {B H : Nat} {ds : zW} {s t0 : Nat}
    (hD : zDg B H ds) (hZ : 0 < z1f ds)
    (hLo : ∃ u,ds = zR s Q ++ u)
    (hHi : ∃ u,ds = u ++ zR t0 Q) :
    ∃ c mid n,ds = zR c Q ++ K :: (mid ++ zR n Q) /\
      z0Z mid = true /\ s <= c /\ t0 <= n := by
  rcases hLo with ⟨lo,hLo_eq⟩
  rcases hHi with ⟨hi,hHi_eq⟩
  rcases loc_z2B hD hZ with ⟨c,w,hE⟩
  rcases z14 w with ⟨mid,n,rfl,hM⟩
  refine ⟨c,mid,n,hE,hM,?_,?_⟩
  · apply loc_z2C c s lo (mid ++ zR n Q)
    rw [<- hLo_eq,hE]
  · apply loc_z2D (zR c Q ++ K :: mid) hi n t0 (loc_z2I c mid hM)
    have h1 : (zR c Q ++ K :: mid) ++ zR n Q =
        zR c Q ++ K :: (mid ++ zR n Q) := by
      simp [List.append_assoc]
    rw [h1,<- hE,hHi_eq]
lemma loc_z2K (p : Nat) (u : zW) (carry : Nat) (eff : zW)
    (hP : 0 < p) (hE : zEf 0 (zR p V ++ Q :: u) carry eff) :
    ∃ v,eff = zR p V ++ K :: v := by
  cases p with
  | zero => omega
  | succ p =>
    have heq : p + 1 = 1 + p := by omega
    rw [heq] at hE ⊢
    rcases loc_z23 p u carry eff hE with ⟨v,hV,_⟩
    exact ⟨v,hV⟩
lemma loc_z2L {p : Nat} {orig : zW} (hI : Good p orig) :
    ∃ out,loc_Step orig out /\ Good (1 + p) out := by
  rcases hI with ⟨H,u,A,da,carry,eff,B,db,tau,
    hP,hHbound,⟨rest,hStart⟩,hEnd,hHeight,hDA,hEff,hSum,hDB,hRes,hM,hDlo,hDhi,hLow⟩
  let alpha := z1h (zR p V)
  let unit := z1h u
  have hAlpha : 0 < alpha := zSp (zR p V)
  have hUnit : 0 < unit := zSp u
  have hAp : alpha * ((2 ^ p : Nat) : Rat) = 1 := (loc_z1P p).2
  have hAsmall : alpha <= 1 / 65536 := loc_z2H p hP
  rcases loc_z2i hRes hP with ⟨hTau,hTauSmall⟩
  have hUsmall : unit <= alpha * (1 / 1024) :=
    loc_z2w p H alpha unit (by omega) hAlpha hUnit hAp hHeight
  rcases z1I hEff with ⟨hEffScale,hEffMass⟩
  rcases loc_z2F hEff hEnd with ⟨last,hElast⟩
  have hCut : z0Z eff = true := by rw [hElast,z11]; rfl
  have hNe : eff ≠ [] := by rw [hElast]; simp
  have hEffHeight : z1h eff * ((2 ^ H : Nat) : Rat) = 1 := by rw [hEffScale]; exact hHeight
  have hEffBound : z1e eff + z1h eff * (1 + z1f db) <= 1 / 128 := by
    rw [hEffScale,hEffMass]
    change z1e u + unit * (1 + z1f db) <= 1 / 128
    have : unit * z1f db <= (5 / 2) * alpha := hDhi
    have : z1e u <= alpha * (1 + (3 / 64) - tau) := hM
    nlinarith
  rcases loc_z1N eff B H db hDB hEffHeight hCut hNe hEffBound with ⟨k,v,a,b,hIscan,hK⟩
  have hZ : 0 < z1f db := by
    have : (3 / 2) * alpha <= unit * z1f db := hDlo
    nlinarith
  rcases loc_z2A p H B db alpha unit hDB (by omega) (by omega)
    hAlpha hUnit (by linarith) hAp hHeight hDhi with ⟨hi,hHi⟩
  rcases loc_z2J hDB hZ hLow ⟨hi,hHi⟩ with ⟨c,mid,t0,hSplit,hMidCut,hC,hT⟩
  rcases loc_z2v eff db B H 12 k v a b p c mid t0 hDB hEffHeight hIscan
    hCut hMidCut hSplit hP hC hT with ⟨J,hJbound,hJheight⟩
  let new := V :: (v ++ [V])
  let nu := z1h new
  have hNu : 0 < nu := zSp new
  have hNuSmall : nu <= alpha * (1 / 1024) :=
    loc_z2x p J alpha nu hP hJbound hAlpha hNu hAp hJheight
  have hEffStart : ∃ w,eff = zR p V ++ K :: w := by
    rw [hStart] at hEff
    exact loc_z2K p rest carry eff (by omega) hEff
  rcases hEffStart with ⟨w,hEstart⟩
  have hWcut : z0Z w = true := by
    rw [hEstart] at hCut
    exact zCo K w (loc_z2E (zR p V) (K :: w) hCut)
  let e := z1e u - alpha
  have hEeq : e = 2 * alpha * z1e w := by
    have h1 : z1e eff = z1e u := hEffMass
    rw [hEstart,z1j] at h1
    dsimp [z1e] at h1
    have h2 := (loc_z1P p).1
    change z1e u - alpha = 2 * alpha * z1e w
    linarith
  have hWw := zWn w
  have hMw : 0 <= z1e w := hWw.1
  have hEpos : 0 <= e := by rw [hEeq]; positivity
  have hEbound : e <= alpha * ((3 / 64) - tau) := by
    change z1e u - alpha <= alpha * ((3 / 64) - tau)
    linarith
  let s := (p - 2) / 2
  let pow := ((2 ^ (s + s / 2) : Nat) : Rat)
  have hPow : 0 < pow := loc_z1O (s + s / 2)
  let f := unit + 2 * unit * z1f db / pow
  have hFeq : f * pow = unit * pow + 2 * unit * z1f db := by
    change (unit + 2 * unit * z1f db / pow) * pow = unit * pow + 2 * unit * z1f db
    have hne : pow ≠ 0 := ne_of_gt hPow
    rw [add_mul,div_mul_cancel₀ _ hne]
  have hWdb := zWn db
  have hZdb : 0 <= z1f db := hWdb.2.1
  have hFpos : 0 <= f :=
    le_of_mul_le_mul_pos_right hPow (by nlinarith [hFeq,hPow,hUnit,hZdb])
  have hFbound : f <= alpha * tau * (1 / 4) := by
    apply loc_z2m p H s alpha unit tau f hRes hP hHbound rfl hAlpha hUnit hAp hHeight
    change f * pow <= unit * pow + 5 * alpha
    have : unit * z1f db <= (5 / 2) * alpha := hDhi
    linarith
  have hLow' : ∃ c w0,(0 < c /\ s <= c) /\ db = zR c Q ++ K :: w0 :=
    ⟨c,mid ++ zR t0 Q,⟨by omega,hC⟩,hSplit⟩
  have hFactor : 2 * alpha * z1h w = unit := by
    have h1 : z1h eff = unit := hEffScale
    rw [hEstart,z1m] at h1
    dsimp [z1h] at h1
    change 2 * alpha * z1h w = unit
    have : z1h (zR p V) = alpha := rfl
    linarith
  have hScanStart : zPS 12 (zR p V ++ K :: (w ++ db ++ [K])) k v a b := by
    rw [hEstart] at hIscan
    simpa [List.append_assoc] using hIscan
  have hStageBound : (2 * alpha * z1h w) * (pow + 2 * z1f db) <= f * pow := by
    rw [hFactor]; linarith
  rcases loc_z2b p w db B H k v a b s e f hScanStart hDB hWcut hLow' hEeq hStageBound
    with ⟨tail,hVstart,hMnext,hDl,hDu⟩
  rcases z1B new 0 with ⟨carry',eff',hEff'⟩
  have hNewStart : new = zR (1 + p) V ++ Q :: (tail ++ [V]) := by
    change V :: (v ++ [V]) = zR (1 + p) V ++ Q :: (tail ++ [V])
    rw [hVstart,loc_z22]; simp [List.append_assoc]
  have hEff'_start : zEf 0 (zR (1 + p) V ++ Q :: (tail ++ [V])) carry' eff' := by
    rwa [<- hNewStart]
  rcases loc_z2c p (tail ++ [V]) carry' eff' hEff'_start with ⟨hRlo0,hRhi0⟩
  rw [<- hNewStart] at hRlo0 hRhi0
  let R := ((1 + carry' : Nat) : Rat) * nu - 1
  have hScale1p : z1h (zR (1 + p) V) = alpha * (1 / 2) := by
    rw [loc_z22]; rfl
  have hRlo : alpha <= R := by
    rw [hScale1p] at hRlo0
    change 2 * (alpha * (1 / 2)) <= R at hRlo0
    linarith
  have hRhi : R <= 2 * z1e new := hRhi0
  have hEnew : 0 <= z1e new - alpha * (1 / 2) := by
    rw [hNewStart,loc_z2G,hScale1p]
    have hWt := zWn (tail ++ [V])
    nlinarith
  have hFtiny : f <= alpha * (1 / 128) := by nlinarith
  have hEtiny : e <= alpha * (3 / 64) := by nlinarith
  have hBudget := loc_z2e hIscan
  have hMnext' : z1e new <= alpha * (1 / 2) + (e + f) * (1 / 2) := hMnext
  rcases loc_z2g J k carry' alpha nu (a - b) R hAlpha (by linarith)
    hNu hNuSmall hJheight (by linarith) (by linarith) hRlo (by linarith) hBudget (by change ((1 + carry' : Nat) : Rat) * nu = 1 + (((1 + carry' : Nat) : Rat) * nu - 1); ring)
    with ⟨A',B',hAsum,hBsum,hAl,hAu,hBl,hBu⟩
  rcases z18 J A' hAu with ⟨da',hDA'⟩
  rcases z18 J B' hBu with ⟨db',hDB'⟩
  rcases loc_z2h hRes with ⟨tau',hRes',hTauStep⟩
  have hMkeep := loc_z2o alpha tau tau' e f (z1e new - alpha * (1 / 2))
    (by linarith) hTauStep hEbound hFbound (by linarith)
  rcases loc_z2d alpha e f nu (a - b) R (z1e new - alpha * (1 / 2))
    hAlpha hEpos hFpos (by linarith) hEtiny hFtiny hNuSmall hEnew (by linarith)
    hRlo (by linarith) hDl hDu with ⟨hDkeepL,hDkeepU⟩
  have hDef := loc_z2f hIscan hJheight hAsum hBsum
  have hZnew := z1n hDB'
  have hDnew : nu * z1f db' = (a - b) * (1 / 2) - 4 * nu - R := by
    have h1 : 1 - ((1 + B' : Nat) : Rat) * nu = (a - b) * (1 / 2) - 4 * nu - R := hDef
    rw [Nat.cast_add,Nat.cast_one] at h1
    have h2 : nu * (z1f db' + (B' : Rat) + 1) = 1 := by
      rw [hZnew]; exact hJheight
    linarith
  have hLowNew : ∃ rest',db' = zR (((1 + p) - 2) / 2) Q ++ rest' := by
    let r := ((1 + p) - 2) / 2 - 1
    have hHr1 : 1 + r = ((1 + p) - 2) / 2 := by omega
    have hHr2 : 1 + r * 2 <= p - 2 := by omega
    have hHighEnd : ∃ z,db = z ++ zR (1 + r * 2) Q := by
      refine ⟨hi ++ zR ((p - 2) - (1 + r * 2)) Q,?_⟩
      have heq_p : (p - 2) - (1 + r * 2) + (1 + r * 2) = p - 2 := by omega
      rw [hHi,List.append_assoc,<- List.replicate_add,heq_p]
    rcases hHighEnd with ⟨z,hHZ⟩
    have hSC : zPS 12 ((eff ++ z) ++ zR (1 + r * 2) Q ++ [K]) k v a b := by
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
    rcases loc_z1L hDA hSum (z1b hDB) with ⟨d,hDD,hEE⟩
    have hd_eq : d = db := z1d hDD hDB
    subst d
    have hFull : zEf 0 (u ++ da ++ [Q]) 1 (eff ++ db ++ [K]) := by
      simpa only [List.append_assoc] using z1D hEff hEE
    exact loc_Step.intro (u ++ da ++ [Q]) (eff ++ db ++ [K]) k v a b J A' da' hFull hIscan hDA' hAsum
  · refine Good.intro (1 + p) J new A' da' carry' eff' B' db' tau'
      (by omega) (by omega) ⟨tail ++ [V],hNewStart⟩ ⟨V :: v,rfl⟩ hJheight hDA' hEff'
      (by omega) hDB' hRes' ?_ ?_ ?_ hLowNew
    · rw [hScale1p]
      linarith
    · rw [hScale1p]
      change (3 / 2) * (alpha * (1 / 2)) <= nu * z1f db'
      linarith
    · rw [hScale1p]
      change nu * z1f db' <= (5 / 2) * (alpha * (1 / 2))
      linarith
lemma ne_of_beq_eq_false {a b : Nat} (h : (a == b) = false) : a ≠ b := by
  intro heq; subst heq; rw [beq_self_eq_true] at h; contradiction
def loc_z2M : Word -> Bool
  | V => false
  | _ => true
lemma loc_z2N (ds : zW) (h : ds.all loc_z2M = true) :
    ∃ A,zDg A ds.length ds := by
  induction ds with
  | nil => exact ⟨0,zDg.nil⟩
  | cons w ds ih =>
    cases w
    · contradiction
    · dsimp [List.all,loc_z2M] at h
      rcases ih h with ⟨A,hI⟩
      have heq : (K :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨A * 2,zDg.zero hI⟩
    · dsimp [List.all,loc_z2M] at h
      rcases ih h with ⟨A,hI⟩
      have heq : (Q :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨1 + A * 2,zDg.one hI⟩
lemma loc_z2O {A H : Nat} {u : zW} (hI : zDg A H u) :
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
lemma loc_z2S (w : Word) (n : Nat) (d : Word) (m : Nat)
    (hE : loc_z2R w n = (d,m)) :
    ∀ {u : zW} {b : Nat} {v : zW},
      zEf m u b v -> zEf n (w :: u) b (d :: v) := by
  intro u b v hI
  cases w with
  | V =>
    dsimp [loc_z2R] at hE
    injection hE with hd hm; subst hd hm
    exact zEf.T hI
  | K =>
    dsimp [loc_z2R] at hE
    injection hE with hd hm; subst hd hm
    rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
    · have hcond : (n % 2 == 0) = true := beq_iff_eq.mpr hmod
      rw [hcond]
      have h1 := zEf.d00 hI
      have heq : (n / 2) * 2 = n := by omega
      rwa [heq] at h1
    · have hcond : (n % 2 == 0) = false := beq_false_of_ne (by omega)
      rw [hcond]
      have h1 := zEf.d01 hI
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
      have h1 := zEf.d10 hI
      have heq : (n / 2) * 2 = n := by omega
      rwa [heq] at h1
    · have hcond : ((n + 1) % 2 == 0) = true := beq_iff_eq.mpr (by omega)
      rw [hcond]
      have hm_eq : (n + 1) / 2 = 1 + n / 2 := by omega
      rw [hm_eq] at hI
      have h1 := zEf.d11 hI
      have heq : 1 + (n / 2) * 2 = n := by omega
      rwa [heq] at h1
def forceLit {α : Type} (n : Nat) (k : Nat -> α) : α :=
  Nat.casesOn n (k 0) (fun m => k (Nat.succ m))
@[simp] lemma forceLit_eq {α : Type} (n : Nat) (k : Nat -> α) : forceLit n k = k n := by
  cases n <;> rfl
def strictWord {α : Type} (w : Word) (k : Word -> α) : α :=
  Word.casesOn w (k V) (k K) (k Q)
@[simp] lemma strictWord_eq {α : Type} (w : Word) (k : Word -> α) : strictWord w k = k w := by
  cases w <;> rfl
def loc_z2T : zW -> Nat -> zW -> Nat × zW
  | [],n,acc => (n,acc.reverseAux [])
  | w :: u,n,acc =>
    let (d,m) := loc_z2R w n
    strictWord d (fun d' => forceLit m (fun m' => loc_z2T u m' (d' :: acc)))
lemma loc_z2U (u : zW) :
    ∀ (n : Nat) (acc : zW) (b : Nat) (out : zW),
      loc_z2T u n acc = (b,out) ->
      ∃ v,out = acc.reverseAux v /\ zEf n u b v := by
  induction u with
  | nil =>
    intro n acc b out hE
    dsimp [loc_z2T] at hE
    injection hE with hb hout; subst hb hout
    exact ⟨[],rfl,zEf.nil n⟩
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
lemma loc_z2W (e : Bool) (k : Nat) (d : Word) (k' : Nat) (u : zW) (c : Nat) (v : zW) (a b : Rat)
    (hS : loc_z2V e k = some (d,k')) (hI : zPS k' u c v a b) :
    ∃ x y,zPS k (loc_z2Q e :: u) c (d :: v) x y := by
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
        · exact ⟨3 + a * 2,b * 2,zPS.short00 hI⟩
        · exact ⟨2 + a * 2,b * 2,zPS.short01 hI⟩
      | false =>
        rw [hk4] at hS; dsimp at hS
        injection hS with hS1; injection hS1 with hS1 hS2; subst hS1 hS2
        have hk4' : k % 4 ≠ 2 := ne_of_beq_eq_false hk4
        have hk_eq : k = 4 + (k / 4 - 1) * 4 := by omega
        rw [hk_eq]
        cases e
        · exact ⟨4 + a * 2,b * 2,zPS.short10 hI⟩
        · exact ⟨3 + a * 2,b * 2,zPS.short11 hI⟩
def loc_z2X : zW -> Bool
  | [] => true
  | K :: _ => true
  | V :: _ => false
  | Q :: u => !loc_z2X u
def loc_z2Y : zW -> zW -> Nat -> zW -> Option (Nat × zW)
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
lemma loc_z2Z (fuel : zW) :
    ∀ (u : zW) (k : Nat) (acc : zW) (k' : Nat) (out : zW),
      loc_z2Y fuel u k acc = some (k',out) ->
      ∃ v a b,out = acc.reverseAux v /\ zPS k u k' v a b := by
  induction fuel with
  | nil => intro u k acc k' out hE; contradiction
  | cons _ fuel ih =>
    intro u k acc k' out hE
    cases u with
    | nil =>
      dsimp [loc_z2Y] at hE
      injection hE with hE1; injection hE1 with hk hout; subst hk hout
      exact ⟨[],0,0,rfl,zPS.nil k⟩
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
            exact ⟨V :: v,a * (1 / 2),b * (1 / 2),rfl,zPS.T hI⟩
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
                exact ⟨V :: v,a * (1 / 2),(1 + b) * (1 / 2),rfl,zPS.pair0 hI⟩
              | Q =>
                dsimp at hE; simp only [strictWord_eq, forceLit_eq] at hE
                rcases ih v0 (1 + (k - 1) * 2) (V :: acc) k' out hE with ⟨v,a,b,rfl,hI⟩
                have hk_eq : k = 1 + (k - 1) := by omega
                rw [hk_eq]
                exact ⟨V :: v,a * (1 / 2),(3 / 4) + b * (1 / 2),rfl,zPS.pair1 hI⟩
def loc_zPf : zW -> Nat -> Option (zW)
  | [],_ => none
  | _ :: fuel,k =>
    if k == 0 then none
    else if k == 1 then some [Q]
    else match loc_zPf fuel (k / 2) with
      | none => none
      | some ws => strictWord (if k % 2 == 0 then K else Q) (fun d' => some (d' :: ws))
lemma loc_z30 (fuel : zW) :
    ∀ (k : Nat) (ws : zW),loc_zPf fuel k = some ws ->
      ∃ A H da,ws = da ++ [Q] /\ zDg A H da /\ A + 2 ^ H = k := by
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
        exact ⟨0,0,[],rfl,zDg.nil,rfl⟩
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
            refine ⟨A * 2,1 + H,K :: da,rfl,zDg.zero hD,?_⟩
            rw [zP2]; omega
          · have hcond : (k % 2 == 0) = false := beq_false_of_ne (by omega)
            rw [hcond]
            refine ⟨1 + A * 2,1 + H,Q :: da,rfl,zDg.one hD,?_⟩
            rw [zP2]; omega
def loc_z31 (u : zW) : Option (zW) :=
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
lemma loc_z32 (u out : zW) (hR : loc_z31 u = some out) : loc_Step u out := by
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
def loc_zSw : zW -> zW -> Option (zW)
  | [],u => some u
  | V :: p,V :: u => loc_zSw p u
  | K :: p,K :: u => loc_zSw p u
  | Q :: p,Q :: u => loc_zSw p u
  | _,_ => none
lemma loc_z33 (p : zW) :
    ∀ (u v : zW),loc_zSw p u = some v -> u = p ++ v := by
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
lemma loc_z34 (u pre rest : zW)
    (hE : loc_zSw pre (u.reverseAux []) = some rest) :
    u = rest.reverseAux pre.reverse := by
  have h1 := loc_z33 pre u.reverse rest hE
  have h2 := congrArg List.reverse h1
  simp [List.reverseAux_eq] at h2 ⊢
  exact h2
def loc_zHn : zW -> Nat -> Option Nat
  | [],h => some h
  | V :: u,h => loc_zHn u (h + 1)
  | _ :: _,0 => none
  | _ :: u,h + 1 => loc_zHn u h
lemma loc_z35 (u : zW) :
    ∀ (h H : Nat),loc_zHn u h = some H ->
      z1h u * ((2 ^ H : Nat) : Rat) = ((2 ^ h : Nat) : Rat) := by
  induction u with
  | nil =>
    intro h H hE
    injection hE with hE; subst hE
    simp [z1h]
  | cons w u ih =>
    intro h H hE
    cases w
    · dsimp [loc_zHn,z1h] at hE ⊢
      have hih := ih (h + 1) H hE
      rw [Nat.pow_succ] at hih
      push_cast at hih ⊢; linarith
    · cases h with
      | zero => contradiction
      | succ h =>
        dsimp [loc_zHn,z1h] at hE ⊢
        have hih := ih h H hE
        rw [Nat.pow_succ]
        push_cast at hih ⊢; linarith
    · cases h with
      | zero => contradiction
      | succ h =>
        dsimp [loc_zHn,z1h] at hE ⊢
        have hih := ih h H hE
        rw [Nat.pow_succ]
        push_cast at hih ⊢; linarith
def loc_z36 : zW -> zW -> Option (zW × zW)
  | [],_ => none
  | V :: u,ds => some (u.reverseAux [V],ds)
  | w :: u,ds => loc_z36 u (w :: ds)
lemma loc_z37 (u : zW) :
    ∀ (ds p tail : zW),loc_z36 u ds = some (p,tail) ->
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
def loc_z38 (u : zW) : Option (zW × zW) :=
  loc_z36 (u.reverseAux []) []
lemma loc_z39 (u p ds : zW) (hE : loc_z38 u = some (p,ds)) :
    u = p ++ ds /\ ds.all loc_z2M = true /\ (∃ v,p = v ++ [V]) := by
  rcases loc_z37 (u.reverseAux []) [] p ds hE rfl with ⟨hU,hD,hEnd⟩
  simp [List.reverseAux_eq] at hU
  exact ⟨hU,hD,hEnd⟩
def loc_z3a (n : Nat) : Nat := (n + 1) / 2
lemma loc_z3b (n : Nat) : (n : Rat) <= 2 * ((loc_z3a n : Nat) : Rat) := by
  have h : n <= (loc_z3a n) * 2 := by unfold loc_z3a; omega
  have hq : (n : Rat) <= (((loc_z3a n) * 2 : Nat) : Rat) := by exact_mod_cast h
  push_cast at hq
  linarith
def loc_z3c (c0 c1 : Nat) : zW -> Nat -> Nat
  | [],n => n
  | V :: u,n => loc_z3c c0 c1 u (loc_z3a n)
  | K :: u,n => loc_z3c c0 c1 u (n * 2 + c0)
  | Q :: u,n => loc_z3c c0 c1 u (n * 2 + c1)
lemma loc_z3d (c0 c1 : Nat) (u : zW) :
    ∀ (n : Nat),
      (c0 : Rat) * z1f u.reverse + (c1 : Rat) * z1g u.reverse + z1h u.reverse * (n : Rat) <=
        ((loc_z3c c0 c1 u n : Nat) : Rat) := by
  induction u with
  | nil =>
    intro n
    simp [z1f,z1g,z1h,loc_z3c]
  | cons w u ih =>
    intro n
    have hsp := zSp u.reverse
    cases w
    · dsimp [loc_z3c]
      rw [List.reverse_cons,z1k,z1l,z1m]
      dsimp [z1f,z1g,z1h]
      have hhu := loc_z3b n
      have hih := ih (loc_z3a n)
      nlinarith
    · dsimp [loc_z3c]
      rw [List.reverse_cons,z1k,z1l,z1m]
      dsimp [z1f,z1g,z1h]
      have hih := ih (n * 2 + c0)
      push_cast at hih
      nlinarith
    · dsimp [loc_z3c]
      rw [List.reverse_cons,z1k,z1l,z1m]
      dsimp [z1f,z1g,z1h]
      have hih := ih (n * 2 + c1)
      push_cast at hih
      nlinarith
lemma loc_z3e (c0 c1 : Nat) (u : zW) (n : Nat) :
    (c0 : Rat) * z1f u + (c1 : Rat) * z1g u + z1h u * (n : Rat) <=
      ((loc_z3c c0 c1 (u.reverseAux []) n : Nat) : Rat) := by
  have h := loc_z3d c0 c1 u.reverse n
  simpa [List.reverseAux_eq,List.reverse_reverse] using h
def loc_z3f : zW := [Q,Q,K] ++ zR 14 Q
lemma loc_z3g :
    z1f loc_z3f = 4 /\ z1h loc_z3f * z1h (zR 16 V) = 2 := by
  constructor
  · norm_num [loc_z3f,List.replicate,z1f]
  · norm_num [loc_z3f,List.replicate,z1h]
lemma loc_z3h {B H : Nat} {db u : zW}
    (hD : zDg B H db)
    (hHeight : z1h u * ((2 ^ H : Nat) : Rat) = 1)
    (hHi : ∃ lo,db = lo ++ loc_z3f) :
    (3 / 2) * z1h (zR 16 V) <= z1h u * z1f db /\
    z1h u * z1f db <= (5 / 2) * z1h (zR 16 V) := by
  rcases hHi with ⟨lo,rfl⟩
  have hDig := loc_z2O hD
  rw [List.all_append] at hDig
  rcases Bool.and_eq_true_iff.mp hDig with ⟨hDigLo,_⟩
  rcases loc_z2N lo hDigLo with ⟨A,hDA⟩
  rcases zDw hDA with ⟨hLs,hLm,_⟩
  rcases zDw hD with ⟨hDs,_,_⟩
  have hSplitLo := z1i lo
  have hWlo := zWn lo
  have hSu := zSp u
  have hSlo := zSp lo
  have hSh := zSp loc_z3f
  have hS16 := zSp (zR 16 V)
  rcases loc_z3g with ⟨hZ,hS⟩
  rw [z1m] at hDs
  let x := z1h u * z1h lo
  have hX : x * z1h loc_z3f = 1 := by
    change (z1h u * z1h lo) * z1h loc_z3f = 1
    nlinarith
  have hXa : 2 * x = z1h (zR 16 V) := by nlinarith
  rw [z1k,hZ]
  have hZlo_le : z1f lo <= z1h lo - 1 := by linarith
  refine ⟨by nlinarith,by nlinarith⟩
def loc_z3i (rest : zW) : Bool :=
  decide (loc_z3c 65536 65536 (rest.reverseAux []) 0 <= 16)
lemma loc_z3j (rest : zW) (hE : loc_z3i rest = true) :
    z1e rest <= 1 / 4096 := by
  have hle : loc_z3c 65536 65536 (rest.reverseAux []) 0 <= 16 := of_decide_eq_true hE
  have hle_q : ((loc_z3c 65536 65536 (rest.reverseAux []) 0 : Nat) : Rat) <= 16 := by exact_mod_cast hle
  have hR := loc_z3e 65536 65536 rest 0
  have hSplit := z1i rest
  push_cast at hR
  linarith
def loc_z3k (orig : zW) : Bool :=
  match loc_z38 orig with
  | none => false
  | some (u,tail) =>
    match loc_zSw [Q] (tail.reverseAux []) with
    | none => false
    | some rd =>
      let da := rd.reverseAux []
      match loc_zSw (zR 16 V ++ [Q]) u,loc_zHn u 0 with
      | some rest,some H =>
        if 33 <= H && H == da.length then
          let (carry,_) := loc_z2T u 0 []
          let (last,db) := loc_z2T da carry []
          if last == 1 then
            match loc_zSw (zR 7 Q) db,
                  loc_zSw loc_z3f.reverse (db.reverseAux []) with
            | some _,some _ => loc_z3i rest
            | _,_ => false
          else false
        else false
      | _,_ => false
lemma loc_z3l (orig : zW) (hCheck : loc_z3k orig = true) :
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
      cases hStart : loc_zSw (zR 16 V ++ [Q]) u with
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
              cases hLow : loc_zSw (zR 7 Q) db with
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
                  rcases z1G hEffD hDA with ⟨B,hDB,hSum⟩
                  have hStart_eq := loc_z33 (zR 16 V ++ [Q]) u rest hStart
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
                    ⟨lo,loc_z33 (zR 7 Q) db lo hLow⟩
                  rw [hStart_eq,loc_z2G]
                  have hSp := zSp (zR 16 V)
                  nlinarith
inductive loc_Rounds : zW -> zW -> Prop where
  | refl (u : zW) : loc_Rounds u u
  | next {u v w : zW} : loc_Step u v -> loc_Rounds v w -> loc_Rounds u w
def loc_z3m : Nat -> zW -> Bool
  | 0,u => loc_z3k u
  | n + 1,u =>
    match loc_z31 u with
    | none => false
    | some v => loc_z3m n v
lemma loc_z3n (n : Nat) :
    ∀ (u : zW),loc_z3m n u = true ->
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
def loc_z3o : zW := [V,V,Q,V,V,V,V,K,Q,K,Q,K,Q]
def u_0 : zW := loc_z3o
def u_1 : zW := [V,V,V,Q,V,V,V,V,V,K,K,V,V,K,K,K,K,K,K,Q,Q]
def u_2 : zW := [V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,K,Q,Q,Q,K,Q,Q,Q,K,K,K,K,K,K,Q,Q,Q]
def u_3 : zW := [V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,Q,Q,Q,K,V,V,V,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q]
def u_4 : zW := [V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q]
def u_5 : zW := [V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,K,K,V,V,V,V,V,V,V,Q,V,V,V,K,K,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q]
def u_6 : zW := [V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,Q,K,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,K,K,K,K,K,K,Q,Q,V,K,K,Q,V,V,V,V,V,V,V,V,V,V,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q]
def u_7 : zW := [V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,K,K,V,K,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,K,K,K,V,V,V,V,V,V,Q,V,V,V,V,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,K,K,K,K,K,K,K,K,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q]
def u_8 : zW := [V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,K,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,Q,K,K,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,K,K,K,K,K,K,K,V,K,V,K,V,V,V,V,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,V,V,V,V,V,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q]
def u_9 : zW := [V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,K,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,K,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,K,V,V,V,V,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,K,V,V,K,K,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,Q,V,V,V,V,V,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def u_10 : zW := [V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,K,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,K,Q,Q,K,Q,Q,K,Q,V,V,V,Q,Q,V,K,Q,K,K,V,V,V,V,V,V,K,K,V,V,V,V,V,V,K,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,K,Q,K,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,K,K,Q,Q,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,K,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def u_11 : zW := [V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,K,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,K,V,K,Q,K,Q,V,V,Q,K,Q,K,V,V,V,V,V,K,Q,Q,Q,Q,V,V,V,V,V,V,V,V,Q,K,V,Q,V,V,Q,V,V,V,Q,Q,V,Q,K,V,V,V,V,V,Q,V,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,K,K,K,K,K,Q,Q,K,Q,K,Q,K,Q,Q,K,Q,K,K,K,K,K,K,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def u_12 : zW := [V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,K,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,K,V,Q,V,V,Q,K,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,Q,Q,V,Q,V,V,Q,V,V,V,Q,Q,V,K,Q,V,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,Q,K,K,Q,Q,K,Q,K,Q,Q,V,K,K,K,Q,V,V,V,K,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,K,Q,K,Q,K,K,V,V,V,V,V,Q,V,V,K,V,V,V,V,V,Q,Q,Q,Q,V,V,V,V,Q,K,V,V,V,V,V,K,V,V,Q,V,V,V,V,V,K,K,V,V,V,V,V,V,K,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,Q,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,Q,K,K,K,K,K,K,Q,Q,K,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def u_13 : zW := [V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,K,V,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,Q,Q,V,K,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,K,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,Q,Q,K,V,K,V,V,V,V,K,Q,V,V,V,Q,V,V,V,V,V,V,Q,Q,Q,Q,V,Q,V,Q,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,V,Q,V,K,V,V,K,V,Q,Q,Q,Q,K,Q,V,Q,V,V,K,V,V,V,V,V,V,V,Q,V,V,K,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,K,V,V,V,V,V,Q,Q,Q,Q,V,V,V,V,V,V,V,V,V,V,K,V,V,Q,V,V,V,V,V,K,K,V,V,V,V,V,V,K,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,K,Q,K,K,K,K,K,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q,Q,Q,K,K,K,K,K,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
def u_14 : zW := [V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,V,Q,V,Q,V,Q,V,V,Q,K,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,Q,Q,V,K,V,V,Q,V,V,V,Q,Q,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,Q,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,Q,Q,V,V,K,V,Q,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,V,V,V,V,Q,Q,V,V,V,V,Q,V,Q,V,V,Q,V,K,V,K,V,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,Q,V,V,V,V,V,Q,Q,K,K,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,Q,V,Q,V,V,V,V,Q,K,Q,V,V,V,V,Q,V,V,V,Q,K,V,V,V,V,V,V,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,V,K,Q,K,Q,V,V,V,K,K,K,K,K,V,V,V,V,V,V,V,V,Q,Q,K,V,Q,Q,K,V,Q,V,V,V,V,V,V,V,V,Q,V,V,V,K,V,Q,V,Q,Q,K,K,V,V,V,V,V,V,Q,K,V,K,V,V,V,V,V,V,Q,V,V,V,K,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,K,V,V,V,V,V,Q,Q,Q,Q,V,V,V,V,V,V,V,V,V,V,K,V,V,Q,V,V,V,V,V,K,K,V,V,V,V,V,V,K,V,V,K,V,V,V,Q,V,V,V,V,V,Q,K,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,K,Q,K,K,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,Q,Q,K,K,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,K,K,Q,K,Q,Q,K,K,Q,Q,K,K,K,Q,Q,Q,K,K,K,K,K,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,K,Q,Q,Q,K,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]
lemma step_0 : loc_z31 u_0 = some u_1 := by decide
lemma step_1 : loc_z31 u_1 = some u_2 := by decide
lemma step_2 : loc_z31 u_2 = some u_3 := by decide
lemma step_3 : loc_z31 u_3 = some u_4 := by decide
lemma step_4 : loc_z31 u_4 = some u_5 := by decide
lemma step_5 : loc_z31 u_5 = some u_6 := by decide
lemma step_6 : loc_z31 u_6 = some u_7 := by decide
lemma step_7 : loc_z31 u_7 = some u_8 := by decide
lemma step_8 : loc_z31 u_8 = some u_9 := by decide
lemma step_9 : loc_z31 u_9 = some u_10 := by decide
lemma step_10 : loc_z31 u_10 = some u_11 := by decide
lemma step_11 : loc_z31 u_11 = some u_12 := by decide
lemma step_12 : loc_z31 u_12 = some u_13 := by decide
lemma step_13 : loc_z31 u_13 = some u_14 := by decide
lemma good_14 : loc_z3k u_14 = true := by decide
lemma z3p_rounds : loc_Rounds loc_z3o u_14 := by
  exact loc_Rounds.next (loc_z32 u_0 u_1 step_0) (loc_Rounds.next (loc_z32 u_1 u_2 step_1) (loc_Rounds.next (loc_z32 u_2 u_3 step_2) (loc_Rounds.next (loc_z32 u_3 u_4 step_3) (loc_Rounds.next (loc_z32 u_4 u_5 step_4) (loc_Rounds.next (loc_z32 u_5 u_6 step_5) (loc_Rounds.next (loc_z32 u_6 u_7 step_6) (loc_Rounds.next (loc_z32 u_7 u_8 step_7) (loc_Rounds.next (loc_z32 u_8 u_9 step_8) (loc_Rounds.next (loc_z32 u_9 u_10 step_9) (loc_Rounds.next (loc_z32 u_10 u_11 step_10) (loc_Rounds.next (loc_z32 u_11 u_12 step_11) (loc_Rounds.next (loc_z32 u_12 u_13 step_12) (loc_Rounds.next (loc_z32 u_13 u_14 step_13) (loc_Rounds.refl u_14))))))))))))))
lemma z3p : ∃ v, loc_Rounds loc_z3o v /\ Good 16 v := ⟨u_14, z3p_rounds, loc_z3l u_14 good_14⟩
inductive Num : Nat -> zF -> List Call -> Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)
lemma z3q {k : Nat} (hK : 0 < k) : ∃ hs,Num k [] hs := by
  rcases z0U k with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · cases a with
    | zero => omega
    | succ a =>
      have heq : (a + 1) * 2 = 2 + a * 2 := by omega
      rw [heq]; exact ⟨[.cj] ++ [.ch] ^ a,Num.even a⟩
  · exact ⟨[.cp] ++ [.ch] ^ a,Num.odd a⟩
lemma z3r {k : Nat} {hs hs' : List Call} (h1 : Num k [] hs) (h2 : Num k [] hs') :
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
def z3s (k : Nat) (r r' : zB) : Prop :=
  ∀ w hs,Num k w hs -> Side hs (w +> r) r'
lemma z3t {r r' : zB} (h : z3s 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl
lemma z3u {n : Nat} {r r' : zB}
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
lemma z3v {n : Nat} {r r' : zB}
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
lemma z3w {A H : Nat} {da : zW} (hD : zDg A H da) (hZ : A = 0) :
    zTs da default = default := by
  induction hD with
  | nil => rfl
  | @zero A H u _ ih =>
    have hA0 : A = 0 := by omega
    dsimp only [zTs]
    rw [ih hA0,zDd]
  | one _ => omega
lemma z3x {A H : Nat} {da : zW} (hD : zDg A H da) (hPos : 0 < A) :
    z3s ((A - 1) * 2) default (zTs da default) := by
  induction hD with
  | nil => omega
  | @zero A H u _ ih =>
    have hA_pos : 0 < A := by omega
    have hIH := ih hA_pos
    have hs := z3u hIH
    rw [zDd] at hs
    have heq : (A * 2 - 1) * 2 = 2 + (A - 1) * 4 := by omega
    dsimp [zTs]
    rwa [heq]
  | @one A H u hDu ih =>
    cases A with
    | zero =>
      change z3s 0 default (d1 +> zTs u default)
      rw [z3w hDu rfl]
      intro w hs hN
      generalize hk : 0 = k0 at hN
      cases hN with
      | zero =>
        have hd : d1 +> (default : zB) = one +> default := by simp [d1,one]
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
      dsimp [zTs]
      rwa [heq]
lemma zEd {n : Nat} {u : zW} {b : Nat} {v : zW}
    (hI : zEf n u b v) :
    ∀ {A H : Nat},zDg A H v -> Seg ([Call.ch] ^ n) ([Call.ch] ^ b) (zWt u) (zWt v) := by
  induction hI with
  | nil n =>
    intro A H _
    exact z0b ([Call.ch] ^ n)
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
lemma z3y {n : Nat} {hs hs' : List Call}
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
lemma loc_z3z {n : Nat} {hs hs' : List Call}
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
lemma loc_z3A {n : Nat} {hs hs' : List Call}
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
lemma loc_z3B {n : Nat} {hs hs' : List Call}
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
lemma loc_z3C {n : Nat} {hs hs' : List Call}
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
lemma loc_z3D {n : Nat} {hs hs' : List Call}
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
lemma loc_z3E {n : Nat} {hs hs' : List Call}
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
lemma loc_z3F {k : Nat} {v : zW} {k' : Nat} {w : zW} {a b : Rat}
    (hI : zPS k v k' w a b) :
    ∀ {u : zW} {n n' : Nat} {hs hs' : List Call},
      zEf n u n' v -> Num k [] hs -> Num k' [] hs' ->
      Seg (([Call.ch] ^ n) ++ hs) (([Call.ch] ^ n') ++ hs') (zWt u) (zWt w) := by
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
    change zEf n0 u0 n1 ([Q,K] ++ u) at hE
    rcases z1F [Q,K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := z1M hSub (by cases hN' <;> omega)
    rcases z3q hPos with ⟨hs0,hN0⟩
    have hD10 : zDg 1 2 [Q,K] := zDg.one (zDg.zero zDg.nil)
    have hStep := zSg (zEd hL hD10) (loc_z3z hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @pair1 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([Q,Q] ++ u) at hE
    rcases z1F [Q,Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z3q (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD11 : zDg 3 2 [Q,Q] := zDg.one (zDg.one zDg.nil)
    have hStep := zSg (zEd hL hD11) (loc_z3A hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short00 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([K] ++ u) at hE
    rcases z1F [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := z1M hSub (by cases hN' <;> omega)
    rcases z3q hPos with ⟨hs0,hN0⟩
    have hD0 : zDg 0 1 [K] := zDg.zero zDg.nil
    have hStep := zSg (zEd hL hD0) (loc_z3B hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short01 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([Q] ++ u) at hE
    rcases z1F [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z3q (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : zDg 1 1 [Q] := zDg.one zDg.nil
    have hStep := zSg (zEd hL hD1) (loc_z3C hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short10 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([K] ++ u) at hE
    rcases z1F [K] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    have hPos : 0 < m * 2 := z1M hSub (by cases hN' <;> omega)
    rcases z3q hPos with ⟨hs0,hN0⟩
    have hD0 : zDg 0 1 [K] := zDg.zero zDg.nil
    have hStep := zSg (zEd hL hD0) (loc_z3D hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
  | @short11 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change zEf n0 u0 n1 ([Q] ++ u) at hE
    rcases z1F [Q] hE with ⟨u1,u2,q,rfl,hL,hR⟩
    rcases z3q (by omega : 0 < 1 + m * 2) with ⟨hs0,hN0⟩
    have hD1 : zDg 1 1 [Q] := zDg.one zDg.nil
    have hStep := zSg (zEd hL hD1) (loc_z3E hN hN0)
    rw [z17]
    exact zS0 hStep (ih hR hN0 hN')
lemma loc_z3G {n : Nat} {r r' : zB}
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
lemma loc_z3H {k : Nat} {v : zW} {k' : Nat} {w : zW} {a b : Rat}
    (hI : zPS k v k' w a b) {u : zW} {r' : zB}
    (hE : zEf 0 u 1 v) (hK : 0 < k') (hC : z3s k' (d1 +> default) r') :
    z3s k (zTs u default) (zTs w r') := by
  intro w0 hs hN
  have hPosK : 0 < k := z1M hI hK
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
  rwa [z16,z16] at hSide
lemma loc_z3I {orig out : zW} (hS : loc_Step orig out) :
    ∃ r,z3s 12 (zTs orig default) r /\ zTs out default = t +> r := by
  rcases hS with ⟨eff,k,v,a,b,J,A,da,hE,hI,hDA,hSum⟩
  have hDA1 : zDg (A + 2 ^ J) (J + 1) (da ++ [Q]) := by
    have h1 := z19 hDA (zDg.one zDg.nil)
    simpa using h1
  rw [hSum] at hDA1
  have hK_pos : 0 < k := by
    have hp := zPp J
    omega
  have hC0 : z3s ((k - 1) * 2) default (zTs (da ++ [Q]) default) :=
    z3x hDA1 hK_pos
  have hC1 : z3s (1 + (k - 1)) (d1 +> (d0 +> default)) (t +> zTs (da ++ [Q]) default) :=
    loc_z3G hC0
  have hk_eq : 1 + (k - 1) = k := by omega
  rw [hk_eq,zDd] at hC1
  have hRun := loc_z3H hI hE hK_pos hC1
  refine ⟨zTs v (t +> zTs (da ++ [Q]) default),hRun,?_⟩
  simp [zTs,z15]
lemma loc_z3J {r r' : zB} (hI : z3s 12 r r') :
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
lemma z3K {orig out : zW} (hS : loc_Step orig out) :
    (zCf (zTs orig default)) [target_tm]⊢⁺ zCf (zTs out default) := by
  rcases loc_z3I hS with ⟨r,hC,hOut⟩
  rw [hOut]
  exact loc_z3J hC
lemma z3L {u v : zW} (hR : loc_Rounds u v) :
    (zCf (zTs u default)) [target_tm]⊢* zCf (zTs v default) := by
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
lemma z3Z_1 : zCm z3X 300 = some z3X_1 := by decide
lemma z40_1 : (z3M z3X) [target_tm]⊢^{300} (z3M z3X_1) :=
  Counter.bmultiStep_sound 300 z3X z3X_1 z3Z_1
lemma z3Z_2 : zCm z3X_1 300 = some z3X_2 := by decide
lemma z40_2 : (z3M z3X_1) [target_tm]⊢^{300} (z3M z3X_2) :=
  Counter.bmultiStep_sound 300 z3X_1 z3X_2 z3Z_2
lemma loc_z3Z_3 : zCm z3X_2 300 = some z3X_3 := by decide
lemma loc_z40_3 : (z3M z3X_2) [target_tm]⊢^{300} (z3M z3X_3) :=
  Counter.bmultiStep_sound 300 z3X_2 z3X_3 loc_z3Z_3
lemma z3Z_4 : zCm z3X_3 300 = some z3X_4 := by decide
lemma z40_4 : (z3M z3X_3) [target_tm]⊢^{300} (z3M z3X_4) :=
  Counter.bmultiStep_sound 300 z3X_3 z3X_4 z3Z_4
lemma z3Z_5 : zCm z3X_4 300 = some z3X_5 := by decide
lemma z40_5 : (z3M z3X_4) [target_tm]⊢^{300} (z3M z3X_5) :=
  Counter.bmultiStep_sound 300 z3X_4 z3X_5 z3Z_5
lemma z3Z_6 : zCm z3X_5 272 = some z3Y := by decide
lemma z40_6 : (z3M z3X_5) [target_tm]⊢^{272} (z3M z3Y) :=
  Counter.bmultiStep_sound 272 z3X_5 z3Y z3Z_6
lemma z40 : (z3M z3X) [target_tm]⊢^{1772} (z3M z3Y) := by
  have h1 := zMt target_tm _ _ _ 300 300 z40_1 z40_2
  have h2 := zMt target_tm _ _ _ 600 300 h1 loc_z40_3
  have h3 := zMt target_tm _ _ _ 900 300 h2 z40_4
  have h4 := zMt target_tm _ _ _ 1200 300 h3 z40_5
  exact zMt target_tm _ _ _ 1500 272 h4 z40_6
lemma z41 :
    (init []) [target_tm]⊢* zCf (zTs loc_z3o default) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = z3M z3X := rfl
  have h_end : z3M z3Y = zCf (zTs loc_z3o default) := by
    simp [z3M,z3Y,zCf,zCL,lh,w_init,t,d0,d1,one,loc_z3o,zTs]
  refine ⟨1772,?_⟩
  rw [h_init,<- h_end]
  exact z40
lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
lemma z42 (m : Nat) :
    ∃ N ≥ m,∃ p w,multiStep target_tm (init []) N = some (zCf (zTs w default)) /\ Good p w := by
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


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases Solution.z42 (n + 1) with ⟨N,hN,_,_,h_N,_⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := Solution.zIm h_N
  rw [Solution.zMs,hn] at h_some
  exact h_some

end BusyBeaver.M_1RBHHH_1RC0RF_1LD1RB_1LE0LD_1RB0LB_1RB1RA
