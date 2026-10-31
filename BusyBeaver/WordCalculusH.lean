module

public import BusyBeaver.Counter
public import BusyBeaver.WordCalculusA
public import BusyBeaver.WordCalculusB

import BusyBeaver.WordCalculusD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver Counter

namespace BusyBeaver.WordCanonBR

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
def canon_tm : Machine (Fin 2) (Fin 6)
  | 0,0 => some (some 1,Stmt.write 1 Dir.right)
  | 0,1 => some (some 4,Stmt.write 0 Dir.right)
  | 1,0 => some (some 2,Stmt.write 1 Dir.left)
  | 1,1 => some (some 0,Stmt.write 1 Dir.right)
  | 2,0 => some (some 3,Stmt.write 1 Dir.left)
  | 2,1 => some (some 2,Stmt.write 0 Dir.left)
  | 3,0 => some (some 5,Stmt.write 1 Dir.left)
  | 3,1 => some (some 0,Stmt.write 0 Dir.left)
  | 4,0 => some (some 0,Stmt.write 1 Dir.right)
  | 4,1 => some (some 1,Stmt.write 1 Dir.right)
  | 5,0 => some (some 4,Stmt.write 1 Dir.left)
  | 5,1 => none
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000000
@[scoped simp] lemma zMz (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 0 = some config := rfl
@[scoped simp] lemma zMo (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 1 = step M config := rfl
@[scoped simp] lemma zMs (M : Machine zG_ zL_) (config : Cfg zG_ zL_) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep,Function.iterate_succ',Function.comp_apply,multiStep]
@[scoped simp] lemma z00 : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[scoped simp] lemma zDh : (default : zB).head = 0 := rfl
@[scoped simp] lemma zDt : (default : zB).tail = default := rfl
@[scoped simp] lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[scoped simp] lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[scoped simp] lemma append_assoc (l1 l2 : zF) (s : zB) :
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
  `(tactic| (try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft]) <;> exact ⟨0,rfl⟩)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, z00, zDh, zDt, append_cons, append_nil])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev c_to_cfg (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩
abbrev c_step (c : CCfg) : Option CCfg := Counter.bstep canon_tm c
abbrev zCm (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep canon_tm n c
lemma zTc {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCm c1 n = some c2) :
    (c_to_cfg c1) [canon_tm]⊢⁺ (c_to_cfg c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩

abbrev t : zF := [1,1,0,0]
abbrev d0 : zF := [0,0]
abbrev d1 : zF := [1,0]
abbrev one : zF := [1]
abbrev lh : zB := [1,0,1] +> default
abbrev w_word : zF := [0,0,0,1,1,0,1,0]
abbrev w_rest : zF := t ++ t ++ (t ++ d1) ++ t ++ (t ++ d0) ++ t ++ (t ++ d0) ++ t ++ t ++ d1 ++ (t ++ one)
abbrev w_base : zF := w_word ++ w_rest
@[scoped simp] lemma zDd : d0 +> (default : zB) = default := by
  simp [d0]
inductive Call where
  | ch
  | cj
  | cp
def zCs : Call -> Fin 6
  | .ch => B
  | .cj => A
  | .cp => A
def zCw : Call -> zF
  | .ch => [1]
  | .cj => [1,1]
  | .cp => [1,0]
def zCR (l : zB) (c : Call) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  ((zCw c +> l) {{zCs c}}> r)
def zCL (l : zB) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  (l <{{C}} ([0] +> r))
def zCf (r : zB) : Cfg (Fin 2) (Fin 6) :=
  zCL lh (w_base +> r)
def z04 (c : Call) (r1 r2 : zB) : Prop :=
  ∀ l,(zCR l c r1) [canon_tm]⊢⁺ (zCL l r2)
inductive Side : List Call -> zB -> zB -> Prop where
  | nil (r : zB) : Side [] r r
  | cons {c : Call} {ls : List Call} {r1 r2 r3 : zB} :
      z04 c r1 r2 -> Side ls r2 r3 -> Side (c :: ls) r1 r3
def Seg (ls_in ls_out : List Call) (w1 w2 : zF) : Prop :=
  ∀ r1 r2,Side ls_out r1 r2 -> Side ls_in (w1 +> r1) (w2 +> r2)
@[scoped simp] lemma z05 {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[scoped simp] lemma zLp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[scoped simp] lemma zLp' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[scoped simp] lemma z06 {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
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
lemma z0m_id (ls : List Call) : Seg ls ls [] [] := by
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
    (h1 : ∀ l r,(zCR l c (w1 +> r)) [canon_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)
lemma zS2 {c_in c_out : Call} {w1 w2 mid : zF}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [canon_tm]⊢⁺ (zCR (mid +> l) c_out r))
    (h2 : ∀ l r,(zCL (mid +> l) r) [canon_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1) (zPt (hc (mid +> l)) (h2 l r2))
lemma zS5 {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : zF}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [canon_tm]⊢⁺ (zCR (mid1 +> l) c1 r))
    (h2 : ∀ l r,(zCL (mid1 +> l) r) [canon_tm]⊢⁺ (zCR (mid2 +> l) c2 r))
    (h3 : ∀ l r,(zCL (mid2 +> l) r) [canon_tm]⊢⁺ (zCL l (w2 +> r))) :
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
lemma zS6 {c_in c1 c2 c3 : Call} {w1 w2 mid1 mid2 mid3 : zF}
    (h1 : ∀ l r,(zCR l c_in (w1 +> r)) [canon_tm]⊢⁺ (zCR (mid1 +> l) c1 r))
    (h2 : ∀ l r,(zCL (mid1 +> l) r) [canon_tm]⊢⁺ (zCR (mid2 +> l) c2 r))
    (h3 : ∀ l r,(zCL (mid2 +> l) r) [canon_tm]⊢⁺ (zCR (mid3 +> l) c3 r))
    (h4 : ∀ l r,(zCL (mid3 +> l) r) [canon_tm]⊢⁺ (zCL l (w2 +> r))) :
    Seg [c_in] [c1,c2,c3] w1 w2 := by
  intro r1 r4 h
  rcases h with _ | ⟨hc1,hrest⟩
  rcases hrest with _ | ⟨hc2,hrest2⟩
  rcases hrest2 with _ | ⟨hc3,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact zPt (h1 l r1)
    (zPt (hc1 (mid1 +> l))
      (zPt (h2 l _)
        (zPt (hc2 (mid2 +> l))
          (zPt (h3 l _)
            (zPt (hc3 (mid3 +> l)) (h4 l r4))))))

-- Atomic Segs:
lemma z0b : Seg [.cp] [] t [1,1,0,1,0] :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma z0c_p : Seg [.ch] [.cp,.ch] [1,1,0,1,0] t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0c : Seg [.cj] [.cp] t t :=
  zS2 (mid := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma zH2 : Seg [.ch] [.cj,.ch] (t ++ one) t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0d : Seg [.ch] [.ch,.ch] t t :=
  zS5 (mid1 := [1,0,1,1]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs t; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma z0e : Seg [.cp] [] (d1 ++ d0) (t ++ one) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d1 d0 t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
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

-- Additional atomic Segs for chains and w_base:
lemma zC_base : Seg [.cp] [.ch,.cp] [0,1,1,1] t :=
  zS5 (mid1 := [0,1,1,1,0]) (mid2 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma zO_head : Seg [.cp] [] [1,0,0,0] [1,1,0,0,1] :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs; simp only [append_cons,append_nil]; execute)
lemma zO_mid : Seg [.ch] [.ch,.cp,.ch] [1,0,1,1,1] t :=
  zS6 (mid1 := [0,1,1,1,1]) (mid2 := [1,0,1,1]) (mid3 := [1,0,1,0])
    (fun l r => by unfold zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL t; simp only [append_cons,append_nil]; execute)
lemma zO_b0 : Seg [.cp] [.ch] [1,1] [1,1,0] :=
  zS2 (mid := [0,1,0])
    (fun l r => by unfold zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL; simp only [append_cons,append_nil]; execute)
lemma zO_b2 : Seg [.ch] [.cp] [1,1,0] d0 :=
  zS2 (mid := [1,1])
    (fun l r => by unfold zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0; simp only [append_cons,append_nil]; execute)
lemma zE_head : Seg [.cj] [] [0,0,1,0,0,0] [0,0,1,1,0,0,0] :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs; simp only [append_cons,append_nil]; execute)
lemma zE_b0 : Seg [.cj] [] [0,0,1,1] [0,0,1,1,1] :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs; simp only [append_cons,append_nil]; execute)
lemma zW_td1a : Seg [.cp] [] (t ++ d1) [1,1,0,1,0,1,0] :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs t d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma zW_td1b : Seg [.ch] [.cp] [1,1,0,1,0,1,0] (d0 ++ t) :=
  zS2 (mid := [1,0,1,0,1,1])
    (fun l r => by unfold zCR zCw zCs; simp only [append_cons,append_nil]; execute)
    (fun l r => by unfold zCL d0 t; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma zW_td0a : Seg [.cp] [] (t ++ d0) [1,1,0,1,0,0,0] :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs t d0; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)
lemma zW_td0b : Seg [.ch] [] [1,1,0,1,0,0,0] (d0 ++ (t ++ one)) :=
  zS4 (fun l r => by unfold zCR zCL zCw zCs d0 t one; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute)

lemma zS3 (n : Nat) : Seg ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t := by
  induction n with
  | zero => exact z0a t
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [zLp,h_eq,z07]
    exact zSg z0d ih
lemma zT_pow (r : Nat) : ∀ n,Seg ([Call.ch] ^ n) ([Call.ch] ^ (n * 2 ^ r)) (t ^ r) (t ^ r) := by
  induction r with
  | zero =>
    intro n
    have h1 : n * 2 ^ 0 = n := by simp
    rw [h1]
    exact z0m_id _
  | succ r ih =>
    intro n
    have h_eq : n * 2 ^ (r + 1) = (n * 2) * 2 ^ r := by rw [Nat.pow_succ]; ring
    rw [zLp,h_eq]
    exact zS0 (zS3 n) (ih (n * 2))
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
lemma zH_d0_even (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d0 d0 :=
  zSa z0k n
lemma zH_d0_odd (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ n) d0 d1 := by
  simpa only [zLp',List.cons_append,List.nil_append] using! zSg zH0 (zSa z0l n)
lemma zH_d1_even (n : Nat) : Seg ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d1 d1 :=
  zSa z0l n

-- Standard composite Segs:
lemma z0m (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cp] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0b z0c_p) (zS3 n)
lemma z0n (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) t t :=
  zSg z0c (zS3 n)
lemma z0o (n : Nat) : Seg ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using!
    zSg (zSg z0e zH2) (zS3 n)
lemma z0p (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  zSg z0f (zS3 n)
lemma z0q (n : Nat) : Seg ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  zSg z0g (zS3 n)
lemma z0r (n : Nat) : Seg ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [zLp',List.cons_append,List.nil_append] using! zSg z0h (zS3 n)
lemma z0s (n : Nat) : Seg ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg [.cj,.ch,.ch] [.cj] d0 d0 :=
    zSg z0i (zSg zH1 zH3)
  have h1 := zSg h0 (zSa z0k n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using! h1
lemma z0t (n : Nat) : Seg ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  zSg z0j (zSa z0k n)
lemma z0u : Seg [.cj,.ch] [] d0 (d1 ++ one) :=
  zSg z0i zH1
lemma z0v (n : Nat) : Seg ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg [.cj,.ch,.ch,.ch] [.cj] d0 d1 :=
    zSg z0i (zSg zH1 (zSg zH3 zH0))
  have h1 := zSg h0 (zSa z0l n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq,zLp',List.cons_append,List.nil_append] using! h1
lemma z0w (n : Nat) : Seg ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg [.cj,.ch] [.cp] d1 d1 := zSg z0j zH0
  have h1 := zSg h0 (zSa z0l n)
  simpa only [zLp',List.cons_append,List.nil_append] using! h1

-- Chain combinators: zCp_chain, zOdd_base, zEven_base
lemma zCp_step {r r_out : zB} (h : Side [.cp] ([0,1] +> r) r_out) :
    Side [.cp] ([0,1,1,0,0,0] +> r) (t +> r_out) := by
  rcases h with _ | ⟨hcp,hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  have h1 : (zCR l .cp ([0,1,1,0,0,0] +> r)) [canon_tm]⊢⁺ (zCR ([1,0,1,0] +> l) .cp ([0,1] +> r)) := by
    unfold zCR zCw zCs; simp only [append_cons,append_nil]; execute
  have h2 : (zCL ([1,0,1,0] +> l) r_out) [canon_tm]⊢⁺ (zCL l (t +> r_out)) := by
    unfold zCL t; simp only [append_cons,append_nil]; execute
  exact zPt h1 (zPt (hcp ([1,0,1,0] +> l)) h2)

lemma zCp_chain (m : Nat) :
    Seg [.cp] [.ch,.cp] ([0,1] ++ (d1 ++ d0) ^ m ++ [1,1]) (t ^ (1 + m)) := by
  induction m with
  | zero =>
    simpa [z05,z06] using! zC_base
  | succ m ih =>
    intro r1 r2 h
    have h_sub := ih r1 r2 h
    have h_in : ([0,1] ++ (d1 ++ d0) ^ (m + 1) ++ [1,1]) +> r1 =
        [0,1,1,0,0,0] +> (((d1 ++ d0) ^ m ++ [1,1]) +> r1) := by
      rw [zLp (d1 ++ d0) m]
      simp only [d1,d0,List.cons_append,List.nil_append,append_cons,append_nil]
    have h_mid : ([0,1] ++ (d1 ++ d0) ^ m ++ [1,1]) +> r1 =
        [0,1] +> (((d1 ++ d0) ^ m ++ [1,1]) +> r1) := by
      simp only [List.cons_append,List.nil_append,append_cons,append_nil]
    rw [h_mid] at h_sub
    have h_step := zCp_step h_sub
    rw [<- h_in] at h_step
    have h_out : t +> (t ^ (1 + m) +> r2) = t ^ (1 + (m + 1)) +> r2 := by
      rw [zLp' t (m + 1),Nat.add_comm m 1,append_assoc]
    rwa [<- h_out]

lemma zOdd_base (r : Nat) :
    Seg [.cp,.ch] [.ch,.cp] ((d1 ++ d0) ^ r ++ [1,1]) (d0 ++ t ^ r) := by
  cases r with
  | zero =>
    simpa [z05,List.append_nil] using! zSg zO_b0 zO_b2
  | succ m =>
    have h1 : Seg [.cp] [] ([1,0,0,0] ++ ((d1 ++ d0) ^ m ++ [1,1])) ([1,1,0,0,1] ++ ((d1 ++ d0) ^ m ++ [1,1])) :=
      zS0 zO_head (z0a _)
    have h2 : Seg [.ch] [.ch,.cp] ([1,1,0] ++ ([0,1] ++ (d1 ++ d0) ^ m ++ [1,1])) (d0 ++ t ^ (1 + m)) :=
      zS0 zO_b2 (zCp_chain m)
    have h_in : (d1 ++ d0) ^ (m + 1) ++ [1,1] = [1,0,0,0] ++ ((d1 ++ d0) ^ m ++ [1,1]) := by
      rw [zLp (d1 ++ d0) m]; rfl
    have h_mid : [1,1,0,0,1] ++ ((d1 ++ d0) ^ m ++ [1,1]) = [1,1,0] ++ ([0,1] ++ (d1 ++ d0) ^ m ++ [1,1]) := rfl
    have h_out : m + 1 = 1 + m := by omega
    rw [h_in,h_out]
    rw [h_mid] at h1
    exact zSg h1 h2

lemma zEven_ch_step {r r_mid r_out : zB}
    (h1 : Side [.cp] ([0,1] +> r) r_mid)
    (h2 : Side [.ch] r_mid r_out) :
    Side [.ch] ([1,0,1,1,0,0,0] +> r) (t +> r_out) := by
  rcases h1 with _ | ⟨hcp,hnil1⟩; cases hnil1
  rcases h2 with _ | ⟨hch,hnil2⟩; cases hnil2
  refine Side.cons (fun l => ?_) (Side.nil _)
  have hs1 : (zCR l .ch ([1,0,1,1,0,0,0] +> r)) [canon_tm]⊢⁺ (zCR ([1,0,1,1] +> l) .cp ([0,1] +> r)) := by
    unfold zCR zCw zCs; simp only [append_cons,append_nil]; execute
  have hs2 : (zCL ([1,0,1,1] +> l) r_mid) [canon_tm]⊢⁺ (zCR ([1,0,1,0] +> l) .ch r_mid) := by
    unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute
  have hs3 : (zCL ([1,0,1,0] +> l) r_out) [canon_tm]⊢⁺ (zCL l (t +> r_out)) := by
    unfold zCL t; simp only [append_cons,append_nil]; execute
  exact zPt hs1 (zPt (hcp ([1,0,1,1] +> l)) (zPt hs2 (zPt (hch ([1,0,1,0] +> l)) hs3)))

lemma zEven_base (r : Nat) :
    Seg [.cj,.ch,.ch] ([.ch,.cp] ++ [.ch] ^ (2 ^ r)) (d0 ++ (d1 ++ d0) ^ r ++ [1,1]) (t ^ (1 + r)) := by
  cases r with
  | zero =>
    have h1 : Seg [.cj] [] [0,0,1,1] [0,0,1,1,1] := zE_b0
    have h2 : Seg [.ch] [] ([0,0] ++ [1,1,1]) ([1,0] ++ [1,1,1]) := zS0 zH0 (z0a [1,1,1])
    have h3 : Seg [.ch] [.ch,.cp,.ch] [1,0,1,1,1] t := zO_mid
    simpa [z05,z06] using! zSg h1 (zSg h2 h3)
  | succ m =>
    intro r1 r2 h
    have h_split : ([Call.ch,Call.cp] ++ [Call.ch] ^ (2 ^ (m + 1))) = ([Call.ch,Call.cp] ++ ([Call.ch] ^ (1 * 2 ^ (1 + m)))) := by
      rw [Nat.one_mul,Nat.add_comm 1 m]
    rw [h_split] at h
    rcases z09 h with ⟨r_mid,h_cp,h_ch_pow⟩
    have h_cp_seg := zCp_chain m r1 r_mid h_cp
    have h_ch_seg := zT_pow (1 + m) 1 r_mid r2 (by simpa [z06] using! h_ch_pow)
    simp only [z06] at h_ch_seg
    have h_mid_eq : ([0,1] ++ (d1 ++ d0) ^ m ++ [1,1]) +> r1 = [0,1] +> (((d1 ++ d0) ^ m ++ [1,1]) +> r1) := by
      simp only [List.cons_append,List.nil_append,append_cons,append_nil]
    rw [h_mid_eq] at h_cp_seg
    have h_step3 := zEven_ch_step h_cp_seg h_ch_seg
    have h_step2 : Side [.ch,.ch] ([0,0,1,1,0,0,0] +> (((d1 ++ d0) ^ m ++ [1,1]) +> r1)) (t +> (t ^ (1 + m) +> r2)) := by
      have h_s2 := (zS0 zH0 (z0a [1,1,0,0,0])) (((d1 ++ d0) ^ m ++ [1,1]) +> r1) _ (Side.nil _)
      exact z08 h_s2 h_step3
    have h_step1 : Side [.cj,.ch,.ch] ([0,0,1,0,0,0] +> (((d1 ++ d0) ^ m ++ [1,1]) +> r1)) (t +> (t ^ (1 + m) +> r2)) := by
      have h_s1 := zE_head (((d1 ++ d0) ^ m ++ [1,1]) +> r1) _ (Side.nil _)
      exact z08 h_s1 h_step2
    have h_in : (d0 ++ (d1 ++ d0) ^ (m + 1) ++ [1,1]) +> r1 = [0,0,1,0,0,0] +> (((d1 ++ d0) ^ m ++ [1,1]) +> r1) := by
      rw [zLp (d1 ++ d0) m]
      simp only [d0,d1,List.cons_append,List.nil_append,append_cons,append_nil]
    have h_out : t ^ (1 + (m + 1)) +> r2 = t +> (t ^ (1 + m) +> r2) := by
      rw [zLp' t (m + 1),Nat.add_comm m 1,append_assoc]
    rw [h_in,h_out]
    exact h_step1

-- Turnaround at w_word and w_rest:
lemma zW_turn {r r' : zB} (h : Side [.ch,.cj,.ch] r r') :
    (zCL lh (w_word +> r)) [canon_tm]⊢⁺ (zCL lh ((w_word ++ t ++ t ++ (t ++ d1)) +> r')) := by
  rcases h with _ | ⟨hc1,hrest1⟩
  rcases hrest1 with _ | ⟨hc2,hrest2⟩
  rcases hrest2 with _ | ⟨hc3,hnil⟩
  cases hnil
  have h1a : (zCL lh (w_word +> r)) [canon_tm]⊢⁺
      (([1,1,0,1,1,1,1,0,1] +> default) <{{C}} ([1,1,1,0,0,0,0,1,1,1,0,1,0] +> r)) := by
    unfold zCL lh w_word; simp only [append_cons,append_nil]; execute
  have h1b : (([1,1,0,1,1,1,1,0,1] +> default) <{{C}} ([1,1,1,0,0,0,0,1,1,1,0,1,0] +> r)) [canon_tm]⊢⁺
      (zCR ([1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1] +> default) .ch r) := by
    unfold zCR zCw zCs; simp only [append_cons,append_nil]; execute
  have h2a : ∀ s1,(zCL ([1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1] +> default) s1) [canon_tm]⊢⁺
      (([1,0,1,0,1,0,1,1,1,0,1,0,0,1] +> default) {{A}}> ([1,0,1,0,0,0,0,1] +> s1)) := by
    intro s1; unfold zCL; simp only [append_cons,append_nil]; execute
  have h2b : ∀ s1,(([1,0,1,0,1,0,1,1,1,0,1,0,0,1] +> default) {{A}}> ([1,0,1,0,0,0,0,1] +> s1)) [canon_tm]⊢⁺
      (zCR ([1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,0,1] +> default) .cj s1) := by
    intro s1; unfold zCR zCw zCs; simp only [append_cons,append_nil]; execute
  have h3 : ∀ s2,(zCL ([1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,0,1] +> default) s2) [canon_tm]⊢⁺
      (zCR ([1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1] +> default) .ch s2) := by
    intro s2; unfold zCL zCR zCw zCs; simp only [append_cons,append_nil]; execute
  have h4a : (zCL ([1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1] +> default) r') [canon_tm]⊢⁺
      (([1,0,0,1] +> default) <{{D}} ([1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0] +> r')) := by
    unfold zCL; simp only [append_cons,append_nil]; execute
  have h4b : (([1,0,0,1] +> default) <{{D}} ([1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0] +> r')) [canon_tm]⊢⁺
      (zCL lh ((w_word ++ t ++ t ++ (t ++ d1)) +> r')) := by
    unfold zCL lh w_word t d1; simp only [List.cons_append,List.nil_append,append_cons,append_nil]; execute
  exact zPt (zPt h1a h1b)
    (zPt (hc1 _)
      (zPt (zPt (h2a _) (h2b _))
        (zPt (hc2 _)
          (zPt (h3 _)
            (zPt (hc3 _) (zPt h4a h4b))))))

lemma zW_s1 : Seg [.ch,.cj,.ch] ([.ch] ^ 2 ++ [.cp] ++ [.ch] ^ 2) t t := by
  simpa only [zLp,z05,z06,List.cons_append,List.nil_append] using! zSg z0d (zSg z0c z0d)
lemma zW_s2 : Seg ([.ch] ^ 2 ++ [.cp] ++ [.ch] ^ 2) ([.ch] ^ 4 ++ [.cp] ++ [.ch] ^ 3) t t := by
  simpa only [List.append_assoc] using! zSg (zS3 2) (z0m 1)
lemma zW_s3 : Seg ([.ch] ^ 4 ++ [.cp] ++ [.ch] ^ 3) ([.ch] ^ 4 ++ [.cp] ++ [.ch] ^ 2) (t ++ d1) (d0 ++ t) := by
  have ha : Seg ([.ch] ^ 4) ([.ch] ^ 4) (t ++ d1) (t ++ d1) := zS0 (zS3 4) (zH_d1_even 4)
  have hb1 : Seg [.cp,.ch] [.cp] (t ++ d1) (d0 ++ t) := zSg zW_td1a zW_td1b
  have hb2 : Seg ([.ch] ^ 2) ([.ch] ^ 2) (d0 ++ t) (d0 ++ t) := zS0 (zH_d0_even 1) (zS3 1)
  have hb : Seg ([.cp] ++ [.ch] ^ 3) ([.cp] ++ [.ch] ^ 2) (t ++ d1) (d0 ++ t) := by
    simpa only [zLp,z05,z06,List.cons_append,List.nil_append] using! zSg hb1 hb2
  simpa only [List.append_assoc] using! zSg ha hb
lemma zW_s4 : Seg ([.ch] ^ 4 ++ [.cp] ++ [.ch] ^ 2) ([.ch] ^ 8 ++ [.cp] ++ [.ch] ^ 3) t t := by
  simpa only [List.append_assoc] using! zSg (zS3 4) (z0m 1)
lemma zW_s5 : Seg ([.ch] ^ 8 ++ [.cp] ++ [.ch] ^ 3) ([.ch] ^ 8 ++ [.cj,.ch]) (t ++ d0) (d0 ++ t) := by
  have ha : Seg ([.ch] ^ 8) ([.ch] ^ 8) (t ++ d0) (t ++ d0) := zS0 (zS3 8) (zH_d0_even 8)
  have hb1 : Seg [.cp,.ch] [] (t ++ d0) (d0 ++ (t ++ one)) := zSg zW_td0a zW_td0b
  have hb2 : Seg [.ch] [] (d0 ++ (t ++ one)) (d1 ++ (t ++ one)) := zS0 zH0 (z0a (t ++ one))
  have hb3 : Seg [.ch] [.cj,.ch] (d1 ++ (t ++ one)) (d0 ++ t) := zS0 zH4 zH2
  have hb : Seg ([.cp] ++ [.ch] ^ 3) [.cj,.ch] (t ++ d0) (d0 ++ t) := by
    simpa only [zLp,z05,z06,List.cons_append,List.nil_append] using! zSg hb1 (zSg hb2 hb3)
  simpa only [List.append_assoc] using! zSg ha hb
lemma zW_s6 : Seg ([.ch] ^ 8 ++ [.cj,.ch]) ([.ch] ^ 16 ++ [.cp] ++ [.ch] ^ 2) t t := by
  have h1 : Seg ([.cj] ++ [.ch] ^ 1) ([.cp] ++ [.ch] ^ 2) t t := z0n 1
  simpa only [z06,List.cons_append,List.nil_append,List.append_assoc] using! zSg (zS3 8) h1
lemma zW_s7 : Seg ([.ch] ^ 16 ++ [.cp] ++ [.ch] ^ 2) ([.ch] ^ 16) (t ++ d0) (d1 ++ (t ++ one)) := by
  have ha : Seg ([.ch] ^ 16) ([.ch] ^ 16) (t ++ d0) (t ++ d0) := zS0 (zS3 16) (zH_d0_even 16)
  have hb1 : Seg [.cp,.ch] [] (t ++ d0) (d0 ++ (t ++ one)) := zSg zW_td0a zW_td0b
  have hb2 : Seg [.ch] [] (d0 ++ (t ++ one)) (d1 ++ (t ++ one)) := zS0 zH0 (z0a (t ++ one))
  have hb : Seg ([.cp] ++ [.ch] ^ 2) [] (t ++ d0) (d1 ++ (t ++ one)) := by
    simpa only [zLp,z05,z06,List.cons_append,List.nil_append] using! zSg hb1 hb2
  simpa only [List.append_assoc,List.append_nil] using! zSg ha hb
lemma zW_s8 : Seg ([.ch] ^ 16) ([.ch] ^ 32) t t := zS3 16
lemma zW_s9 : Seg ([.ch] ^ 32) ([.ch] ^ 64) t t := zS3 32
lemma zW_s10 : Seg ([.ch] ^ 64) ([.ch] ^ 32) d1 d1 := zH_d1_even 32
lemma zW_s11 : Seg ([.ch] ^ 32) ([.cj] ++ [.ch] ^ 63) (t ++ one) t := by
  have h1 := zSg zH2 (zS3 31)
  have heq_in : ([Call.ch] : List Call) ++ [Call.ch] ^ 31 = [Call.ch] ^ 32 := rfl
  have heq_out : ([Call.cj,Call.ch] : List Call) ++ [Call.ch] ^ (31 * 2) = [Call.cj] ++ [Call.ch] ^ 63 := rfl
  rwa [heq_in,heq_out] at h1

lemma zW_rest_seg :
    Seg [.ch,.cj,.ch] ([.cj] ++ [.ch] ^ 63) w_rest
      (t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one)) ++ t ++ t ++ d1 ++ t) := by
  unfold w_rest
  exact zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 (zS0 zW_s1 zW_s2) zW_s3) zW_s4) zW_s5) zW_s6) zW_s7) zW_s8) zW_s9) zW_s10) zW_s11

lemma zW_full {r r' : zB} (h : Side ([.cj] ++ [.ch] ^ 63) r r') :
    (zCf r) [canon_tm]⊢⁺ (zCf ((t ++ t ++ d1 ++ t) +> r')) := by
  have h_side := zW_rest_seg r r' h
  have h_turn := zW_turn h_side
  have h_in : w_word +> (w_rest +> r) = w_base +> r := by
    unfold w_base w_rest; simp only [List.append_assoc,append_assoc]
  have h_out : (w_word ++ t ++ t ++ (t ++ d1)) +>
      ((t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one)) ++ t ++ t ++ d1 ++ t) +> r') =
      w_base +> ((t ++ t ++ d1 ++ t) +> r') := by
    unfold w_base w_word w_rest t d0 d1 one
    simp only [List.cons_append,List.nil_append,append_cons,append_nil]
  unfold zCf
  rwa [h_in,h_out] at h_turn

-- Words, zQK, zTs, BRIncs, Num, z2f:

open WordCalculus Word
local notation "zW" => List Word
local notation "zR" => List.replicate

def zQK : Nat -> zW -> zW
  | 0,u => u
  | r + 1,u => Q :: K :: zQK r u

lemma zQK_append (r : Nat) (u v : zW) :
    zQK r (u ++ v) = zQK r u ++ v := by
  induction r with
  | zero => rfl
  | succ r ih => simp [zQK,ih]

lemma zTs_R (r_ch : Nat) (r : zB) :
    zTs (zR r_ch V) r = (t ^ r_ch) +> r := by
  induction r_ch with
  | zero => rfl
  | succ r_ch ih =>
    simp only [List.replicate,zTs,ih,zLp,append_assoc]

lemma zTs_QK (r_ch : Nat) (r : zB) :
    zTs (zQK r_ch [V]) r = ((d1 ++ d0) ^ r_ch ++ [1,1]) +> (d0 +> r) := by
  induction r_ch with
  | zero =>
    simp only [zQK,zTs,z05,t,d0,List.nil_append,List.cons_append,append_cons,append_nil]
  | succ r_ch ih =>
    rw [zLp (d1 ++ d0) r_ch]
    simp only [zQK,zTs,ih,d1,d0,List.cons_append,List.nil_append,append_cons,append_nil]

inductive BRIncs : Bool -> Nat -> zB -> zB -> Prop where
  | zero (r : zB) : BRIncs false 0 r (one +> r)
  | T {n : Nat} {r r' : zB} :
      BRIncs false (1 + n * 2) r r' -> BRIncs false (2 + n) (t +> r) (t +> r')
  | pair0 {n : Nat} {r r' : zB} :
      BRIncs false (n * 2) r r' -> BRIncs false (1 + n) (d1 +> (d0 +> r)) (t +> r')
  | pair1 {n : Nat} {r r' : zB} :
      BRIncs false (1 + n * 2) r r' -> BRIncs false (1 + n) (d1 +> (d1 +> r)) (t +> r')
  | short00 {n : Nat} {r r' : zB} :
      BRIncs false (n * 2) r r' -> BRIncs false (2 + n * 4) (d0 +> r) (d0 +> r')
  | short01 {n : Nat} {r r' : zB} :
      BRIncs false (1 + n * 2) r r' -> BRIncs false (2 + n * 4) (d1 +> r) (d0 +> r')
  | short10 {n : Nat} {r r' : zB} :
      BRIncs false (n * 2) r r' -> BRIncs false (4 + n * 4) (d0 +> r) (d1 +> r')
  | short11 {n : Nat} {r r' : zB} :
      BRIncs false (1 + n * 2) r r' -> BRIncs false (4 + n * 4) (d1 +> r) (d1 +> r')
  | odd_chain0 (r_ch : Nat) {m : Nat} {r r' : zB} :
      BRIncs true (1 + m * 2 ^ (1 + r_ch)) r r' ->
      BRIncs false (3 + m * 4) (zTs (zQK r_ch [V]) r) (d0 +> zTs (zR r_ch V) r')
  | odd_chain1 (r_ch : Nat) {m : Nat} {r r' : zB} :
      BRIncs true (1 + m * 2 ^ (1 + r_ch)) r r' ->
      BRIncs false (5 + m * 4) (zTs (zQK r_ch [V]) r) (d1 +> zTs (zR r_ch V) r')
  | even_chain (r_ch : Nat) {m : Nat} {r r' : zB} :
      BRIncs true (1 + (1 + m * 2) * 2 ^ (1 + r_ch)) r r' ->
      BRIncs false (6 + m * 2) (d0 +> zTs (zQK r_ch [V]) r) (zTs (zR (1 + r_ch) V) r')
  | shift_pair0 {n : Nat} {r r' : zB} :
      BRIncs false (n * 2) r r' -> BRIncs true (1 + n) (d0 +> r) (t +> r')
  | shift_pair1 {n : Nat} {r r' : zB} :
      BRIncs false (1 + n * 2) r r' -> BRIncs true (1 + n) (d1 +> r) (t +> r')
  | shift_chain0 (r_ch : Nat) {m : Nat} {r r' : zB} :
      BRIncs true (1 + m * 2 ^ (2 + r_ch)) r r' ->
      BRIncs true (3 + m * 4) (d0 +> zTs (zQK r_ch [V]) r) (d0 +> zTs (zR (1 + r_ch) V) r')
  | shift_chain1 (r_ch : Nat) {m : Nat} {r r' : zB} :
      BRIncs true (1 + m * 2 ^ (2 + r_ch)) r r' ->
      BRIncs true (5 + m * 4) (d0 +> zTs (zQK r_ch [V]) r) (d1 +> zTs (zR (1 + r_ch) V) r')

inductive Num : Bool -> Nat -> zF -> List Call -> Prop where
  | zero : Num false 0 one []
  | odd (n : Nat) : Num false (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num false (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)
  | shift (n : Nat) : Num true (1 + n * 2) d0 ([.ch,.cp] ++ [.ch] ^ n)

def loc_z2f (s : Bool) (k : Nat) (r r' : zB) : Prop :=
  ∀ w hs,Num s k w hs -> Side hs (w +> r) r'

lemma loc_z2g {r r' : zB} (h : loc_z2f false 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl

lemma loc_z2h {n : Nat} {r r' : zB}
    (hI : loc_z2f false (1 + n * 2) r r') : loc_z2f false (2 + n) (t +> r) (t +> r') := by
  intro w hs hN
  generalize hs_eq : false = s0 at hN
  generalize hk : 2 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil]
    cases m with
    | zero => omega
    | succ m =>
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      refine zSc (z0m m) ?_
      have hN1 : Num false (1 + n * 2) [] ([.cp] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : 1 + n * 2 = 1 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.odd (1 + m * 2)
      simpa using! hI [] _ hN1
  | @even m =>
    simp only [append_nil]
    refine zSc (z0n m) ?_
    have hN1 : Num false (1 + n * 2) [] ([.cp] ++ [.ch] ^ (m * 2)) := by
      have hm : 1 + n * 2 = 1 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (m * 2)
    simpa using! hI [] _ hN1
  | shift _ => contradiction

lemma z2i_p0 {n : Nat} {r r' : zB}
    (hI : loc_z2f false (n * 2) r r') : loc_z2f false (1 + n) (d1 +> (d0 +> r)) (t +> r') := by
  intro w hs hN
  generalize hs_eq : false = s0 at hN
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
      have hN2 : Num false (n * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : n * 2 = 2 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using! hI [] _ hN2
  | @even m =>
    simp only [append_nil,<- append_assoc d1 d0 r]
    refine zSc (z0p m) ?_
    have hN2 : Num false (n * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : n * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using! hI [] _ hN2
  | shift _ => contradiction

lemma loc_z2j {n : Nat} {r r' : zB}
    (hI : loc_z2f false (1 + n * 2) r r') : loc_z2f false (1 + n) (d1 +> (d1 +> r)) (t +> r') := by
  intro w hs hN
  generalize hs_eq : false = s0 at hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil,<- append_assoc d1 d1 r]
    refine zSc (z0q m) ?_
    have hN1 : Num false (1 + n * 2) [] ([.cp] ++ [.ch] ^ (m * 2)) := by
      have hm : 1 + n * 2 = 1 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (m * 2)
    simpa using! hI [] _ hN1
  | @even m =>
    simp only [append_nil,<- append_assoc d1 d1 r]
    refine zSc (z0r m) ?_
    have hN1 : Num false (1 + n * 2) [] ([.cp] ++ [.ch] ^ (1 + m * 2)) := by
      have hm : 1 + n * 2 = 1 + (1 + m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (1 + m * 2)
    simpa using! hI [] _ hN1
  | shift _ => contradiction

lemma loc_z2k {n : Nat} {r r' : zB}
    (hI : loc_z2f false (n * 2) r r') : loc_z2f false (2 + n * 4) (d0 +> r) (d0 +> r') := by
  intro w hs hN
  generalize hs_eq : false = s0 at hN
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
      have hN2 : Num false ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        rw [heq]; exact Num.even n
      simpa using! hI [] _ hN2
  | shift _ => contradiction

lemma loc_z2l {n : Nat} {r r' : zB}
    (hI : loc_z2f false (1 + n * 2) r r') : loc_z2f false (2 + n * 4) (d1 +> r) (d0 +> r') := by
  intro w hs hN
  generalize hs_eq : false = s0 at hN
  generalize hk : 2 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = n * 2 := by omega
    subst hm
    refine zSc (z0t n) ?_
    simpa using! hI [] _ (Num.odd n)
  | shift _ => contradiction

lemma loc_z2m {n : Nat} {r r' : zB}
    (hI : loc_z2f false (n * 2) r r') : loc_z2f false (4 + n * 4) (d0 +> r) (d1 +> r') := by
  intro w hs hN
  generalize hs_eq : false = s0 at hN
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
      have hN2 : Num false ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        have heq2 : (n + 1) * 2 = 2 + n * 2 := by omega
        rw [heq2]; exact Num.even n
      simpa using! hI [] _ hN2
  | shift _ => contradiction

lemma loc_z2n {n : Nat} {r r' : zB}
    (hI : loc_z2f false (1 + n * 2) r r') : loc_z2f false (4 + n * 4) (d1 +> r) (d1 +> r') := by
  intro w hs hN
  generalize hs_eq : false = s0 at hN
  generalize hk : 4 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = 1 + n * 2 := by omega
    subst hm
    refine zSc (z0w n) ?_
    simpa using! hI [] _ (Num.odd n)
  | shift _ => contradiction

lemma z2_oc0 (r_ch : Nat) {m : Nat} {r r' : zB}
    (hI : loc_z2f true (1 + m * 2 ^ (1 + r_ch)) r r') :
    loc_z2f false (3 + m * 4) (zTs (zQK r_ch [V]) r) (d0 +> zTs (zR r_ch V) r') := by
  intro w hs hN
  generalize hs_eq : false = s0 at hN
  generalize hk : 3 + m * 4 = k at hN
  cases hN with
  | zero => omega
  | @odd n =>
    simp only [append_nil]
    have hn : n = 1 + m * 2 := by omega
    subst hn
    rw [zTs_QK,zTs_R,<- append_assoc d0 (t ^ r_ch) r']
    have h_seg : Seg ([.cp] ++ [.ch] ^ (1 + m * 2)) ([.ch,.cp] ++ [.ch] ^ (m * 2 ^ r_ch))
        ((d1 ++ d0) ^ r_ch ++ [1,1]) (d0 ++ t ^ r_ch) := by
      have h1 := zOdd_base r_ch
      have h2 := zS0 (zH_d0_even m) (zT_pow r_ch m)
      simpa only [zLp',List.cons_append,List.nil_append,List.append_assoc] using! zSg h1 h2
    refine zSc h_seg ?_
    have h_num : Num true (1 + m * 2 ^ (1 + r_ch)) d0 ([.ch,.cp] ++ [.ch] ^ (m * 2 ^ r_ch)) := by
      have heq : 1 + m * 2 ^ (1 + r_ch) = 1 + (m * 2 ^ r_ch) * 2 := by
        rw [Nat.add_comm 1 r_ch,Nat.pow_succ]; ring
      rw [heq]; exact Num.shift (m * 2 ^ r_ch)
    exact hI d0 _ h_num
  | even _ => omega
  | shift _ => contradiction

lemma z2_oc1 (r_ch : Nat) {m : Nat} {r r' : zB}
    (hI : loc_z2f true (1 + m * 2 ^ (1 + r_ch)) r r') :
    loc_z2f false (5 + m * 4) (zTs (zQK r_ch [V]) r) (d1 +> zTs (zR r_ch V) r') := by
  intro w hs hN
  generalize hs_eq : false = s0 at hN
  generalize hk : 5 + m * 4 = k at hN
  cases hN with
  | zero => omega
  | @odd n =>
    simp only [append_nil]
    have hn : n = 1 + (1 + m * 2) := by omega
    subst hn
    rw [zTs_QK,zTs_R,<- append_assoc d1 (t ^ r_ch) r']
    have h_seg : Seg ([.cp] ++ [.ch] ^ (1 + (1 + m * 2))) ([.ch,.cp] ++ [.ch] ^ (m * 2 ^ r_ch))
        ((d1 ++ d0) ^ r_ch ++ [1,1]) (d1 ++ t ^ r_ch) := by
      have h1 := zOdd_base r_ch
      have h2 := zS0 (zH_d0_odd m) (zT_pow r_ch m)
      simpa only [zLp',List.cons_append,List.nil_append,List.append_assoc] using! zSg h1 h2
    refine zSc h_seg ?_
    have h_num : Num true (1 + m * 2 ^ (1 + r_ch)) d0 ([.ch,.cp] ++ [.ch] ^ (m * 2 ^ r_ch)) := by
      have heq : 1 + m * 2 ^ (1 + r_ch) = 1 + (m * 2 ^ r_ch) * 2 := by
        rw [Nat.add_comm 1 r_ch,Nat.pow_succ]; ring
      rw [heq]; exact Num.shift (m * 2 ^ r_ch)
    exact hI d0 _ h_num
  | even _ => omega
  | shift _ => contradiction

lemma z2_ec (r_ch : Nat) {m : Nat} {r r' : zB}
    (hI : loc_z2f true (1 + (1 + m * 2) * 2 ^ (1 + r_ch)) r r') :
    loc_z2f false (6 + m * 2) (d0 +> zTs (zQK r_ch [V]) r) (zTs (zR (1 + r_ch) V) r') := by
  intro w hs hN
  generalize hs_eq : false = s0 at hN
  generalize hk : 6 + m * 2 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even n =>
    simp only [append_nil]
    have hn : n = 1 + (1 + m) := by omega
    subst hn
    rw [zTs_QK,zTs_R,<- append_assoc d0 ((d1 ++ d0) ^ r_ch ++ [1,1]) (d0 +> r)]
    have h_seg : Seg ([.cj] ++ [.ch] ^ (1 + (1 + m))) ([.ch,.cp] ++ [.ch] ^ ((1 + m * 2) * 2 ^ r_ch))
        (d0 ++ ((d1 ++ d0) ^ r_ch ++ [1,1])) (t ^ (1 + r_ch)) := by
      have h1 : Seg [.cj,.ch,.ch] ([.ch,.cp] ++ [.ch] ^ (2 ^ r_ch)) (d0 ++ ((d1 ++ d0) ^ r_ch ++ [1,1])) (t ^ (1 + r_ch)) := by
        simpa only [List.append_assoc] using! zEven_base r_ch
      have h2 := zT_pow (1 + r_ch) m
      have h3 := zSg h1 h2
      have heq_in : ([Call.cj,Call.ch,Call.ch] : List Call) ++ [Call.ch] ^ m = [Call.cj] ++ [Call.ch] ^ (1 + (1 + m)) := by
        simp only [zLp',List.cons_append,List.nil_append]
      have heq_out : ([Call.ch,Call.cp] ++ [Call.ch] ^ (2 ^ r_ch)) ++ [Call.ch] ^ (m * 2 ^ (1 + r_ch)) =
          [Call.ch,Call.cp] ++ [Call.ch] ^ ((1 + m * 2) * 2 ^ r_ch) := by
        rw [List.append_assoc,<- z07]
        congr 2
        rw [Nat.add_comm 1 r_ch,Nat.pow_succ]; ring
      rwa [heq_in,heq_out] at h3
    refine zSc h_seg ?_
    have h_num : Num true (1 + (1 + m * 2) * 2 ^ (1 + r_ch)) d0 ([.ch,.cp] ++ [.ch] ^ ((1 + m * 2) * 2 ^ r_ch)) := by
      have heq : 1 + (1 + m * 2) * 2 ^ (1 + r_ch) = 1 + ((1 + m * 2) * 2 ^ r_ch) * 2 := by
        rw [Nat.add_comm 1 r_ch,Nat.pow_succ]; ring
      rw [heq]; exact Num.shift ((1 + m * 2) * 2 ^ r_ch)
    exact hI d0 _ h_num
  | shift _ => contradiction

lemma z2_sp0 {n : Nat} {r r' : zB}
    (hI : loc_z2f false (n * 2) r r') : loc_z2f true (1 + n) (d0 +> r) (t +> r') := by
  intro w hs hN
  generalize hs_eq : true = s0 at hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => contradiction
  | odd _ => contradiction
  | even _ => contradiction
  | @shift m =>
    have hn : n = m * 2 := by omega
    subst hn
    rw [<- append_assoc d0 d0 r]
    cases m with
    | zero =>
      have hn0 : 0 * 2 * 2 = 0 := rfl
      rw [hn0] at hI
      have hr' := loc_z2g hI
      subst hr'
      rw [<- append_assoc t one r]
      have h_seg : Seg ([.ch,.cp] ++ [.ch] ^ 0) [] (d0 ++ d0) (t ++ one) := by
        simpa only [z05,List.append_nil] using! zSg (zS0 zH0 (z0a d0)) z0e
      exact zSc h_seg (Side.nil r)
    | succ m =>
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m] at hI ⊢
      have h_seg : Seg ([.ch,.cp] ++ [.ch] ^ (1 + m)) ([.cj] ++ [.ch] ^ (1 + m * 2)) (d0 ++ d0) t := by
        simpa only [List.cons_append,List.nil_append] using! zSg (zS0 zH0 (z0a d0)) (z0o m)
      refine zSc h_seg ?_
      have hN2 : Num false ((1 + m) * 2 * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : (1 + m) * 2 * 2 = 2 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using! hI [] _ hN2

lemma z2_sp1 {n : Nat} {r r' : zB}
    (hI : loc_z2f false (1 + n * 2) r r') : loc_z2f true (1 + n) (d1 +> r) (t +> r') := by
  intro w hs hN
  generalize hs_eq : true = s0 at hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => contradiction
  | odd _ => contradiction
  | even _ => contradiction
  | @shift m =>
    have hn : n = m * 2 := by omega
    subst hn
    rw [<- append_assoc d0 d1 r]
    have h_seg : Seg ([.ch,.cp] ++ [.ch] ^ m) ([.cp] ++ [.ch] ^ (m * 2)) (d0 ++ d1) t := by
      simpa only [List.cons_append,List.nil_append] using! zSg (zS0 zH0 (z0a d1)) (z0q m)
    refine zSc h_seg ?_
    have hN1 : Num false (1 + m * 2 * 2) [] ([.cp] ++ [.ch] ^ (m * 2)) := by
      have hm : 1 + m * 2 * 2 = 1 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (m * 2)
    simpa using! hI [] _ hN1

lemma z2_sc0 (r_ch : Nat) {m : Nat} {r r' : zB}
    (hI : loc_z2f true (1 + m * 2 ^ (2 + r_ch)) r r') :
    loc_z2f true (3 + m * 4) (d0 +> zTs (zQK r_ch [V]) r) (d0 +> zTs (zR (1 + r_ch) V) r') := by
  intro w hs hN
  generalize hs_eq : true = s0 at hN
  generalize hk : 3 + m * 4 = k at hN
  cases hN with
  | zero => contradiction
  | odd _ => contradiction
  | even _ => contradiction
  | @shift n =>
    have hn : n = 1 + m * 2 := by omega
    subst hn
    rw [zTs_QK,zTs_R,<- append_assoc d0 (t ^ (1 + r_ch)) r']
    have h_in : d0 +> (d0 +> (((d1 ++ d0) ^ r_ch ++ [1,1]) +> (d0 +> r))) =
        (d0 ++ ((d0 ++ (d1 ++ d0) ^ r_ch ++ [1,1]))) +> (d0 +> r) := by
      simp only [List.append_assoc,append_assoc]
    rw [h_in]
    have h_seg : Seg ([.ch,.cp] ++ [.ch] ^ (1 + m * 2)) ([.ch,.cp] ++ [.ch] ^ (m * 2 ^ (1 + r_ch)))
        (d0 ++ (d0 ++ (d1 ++ d0) ^ r_ch ++ [1,1])) (d0 ++ t ^ (1 + r_ch)) := by
      have h0 : Seg [.ch] [] (d0 ++ (d0 ++ (d1 ++ d0) ^ r_ch ++ [1,1])) ((d1 ++ d0) ^ (1 + r_ch) ++ [1,1]) := by
        rw [zLp']
        simpa only [List.append_assoc] using! zS0 zH0 (z0a (d0 ++ (d1 ++ d0) ^ r_ch ++ [1,1]))
      have h1 := zOdd_base (1 + r_ch)
      have h2 := zS0 (zH_d0_even m) (zT_pow (1 + r_ch) m)
      simpa only [zLp',List.cons_append,List.nil_append,List.append_assoc] using! zSg h0 (zSg h1 h2)
    refine zSc h_seg ?_
    have h_num : Num true (1 + m * 2 ^ (2 + r_ch)) d0 ([.ch,.cp] ++ [.ch] ^ (m * 2 ^ (1 + r_ch))) := by
      have heq : 1 + m * 2 ^ (2 + r_ch) = 1 + (m * 2 ^ (1 + r_ch)) * 2 := by
        have h2r : 2 + r_ch = (1 + r_ch) + 1 := by omega
        rw [h2r,Nat.pow_succ]; ring
      rw [heq]; exact Num.shift (m * 2 ^ (1 + r_ch))
    exact hI d0 _ h_num

lemma z2_sc1 (r_ch : Nat) {m : Nat} {r r' : zB}
    (hI : loc_z2f true (1 + m * 2 ^ (2 + r_ch)) r r') :
    loc_z2f true (5 + m * 4) (d0 +> zTs (zQK r_ch [V]) r) (d1 +> zTs (zR (1 + r_ch) V) r') := by
  intro w hs hN
  generalize hs_eq : true = s0 at hN
  generalize hk : 5 + m * 4 = k at hN
  cases hN with
  | zero => contradiction
  | odd _ => contradiction
  | even _ => contradiction
  | @shift n =>
    have hn : n = 1 + (1 + m * 2) := by omega
    subst hn
    rw [zTs_QK,zTs_R,<- append_assoc d1 (t ^ (1 + r_ch)) r']
    have h_in : d0 +> (d0 +> (((d1 ++ d0) ^ r_ch ++ [1,1]) +> (d0 +> r))) =
        (d0 ++ ((d0 ++ (d1 ++ d0) ^ r_ch ++ [1,1]))) +> (d0 +> r) := by
      simp only [List.append_assoc,append_assoc]
    rw [h_in]
    have h_seg : Seg ([.ch,.cp] ++ [.ch] ^ (1 + (1 + m * 2))) ([.ch,.cp] ++ [.ch] ^ (m * 2 ^ (1 + r_ch)))
        (d0 ++ (d0 ++ (d1 ++ d0) ^ r_ch ++ [1,1])) (d1 ++ t ^ (1 + r_ch)) := by
      have h0 : Seg [.ch] [] (d0 ++ (d0 ++ (d1 ++ d0) ^ r_ch ++ [1,1])) ((d1 ++ d0) ^ (1 + r_ch) ++ [1,1]) := by
        rw [zLp']
        simpa only [List.append_assoc] using! zS0 zH0 (z0a (d0 ++ (d1 ++ d0) ^ r_ch ++ [1,1]))
      have h1 := zOdd_base (1 + r_ch)
      have h2 := zS0 (zH_d0_odd m) (zT_pow (1 + r_ch) m)
      simpa only [zLp',List.cons_append,List.nil_append,List.append_assoc] using! zSg h0 (zSg h1 h2)
    refine zSc h_seg ?_
    have h_num : Num true (1 + m * 2 ^ (2 + r_ch)) d0 ([.ch,.cp] ++ [.ch] ^ (m * 2 ^ (1 + r_ch))) := by
      have heq : 1 + m * 2 ^ (2 + r_ch) = 1 + (m * 2 ^ (1 + r_ch)) * 2 := by
        have h2r : 2 + r_ch = (1 + r_ch) + 1 := by omega
        rw [h2r,Nat.pow_succ]; ring
      rw [heq]; exact Num.shift (m * 2 ^ (1 + r_ch))
    exact hI d0 _ h_num

lemma loc_z2o {s : Bool} {k : Nat} {r r' : zB} (hI : BRIncs s k r r') :
    loc_z2f s k r r' := by
  induction hI with
  | zero r =>
    intro w hs hN
    generalize hs_eq : false = s0 at hN
    generalize hk : 0 = k0 at hN
    cases hN with
    | zero => exact Side.nil (one +> r)
    | odd _ => omega
    | even _ => omega
    | shift _ => contradiction
  | T _ ih => exact loc_z2h ih
  | pair0 _ ih => exact z2i_p0 ih
  | pair1 _ ih => exact loc_z2j ih
  | short00 _ ih => exact loc_z2k ih
  | short01 _ ih => exact loc_z2l ih
  | short10 _ ih => exact loc_z2m ih
  | short11 _ ih => exact loc_z2n ih
  | odd_chain0 r_ch _ ih => exact z2_oc0 r_ch ih
  | odd_chain1 r_ch _ ih => exact z2_oc1 r_ch ih
  | even_chain r_ch _ ih => exact z2_ec r_ch ih
  | shift_pair0 _ ih => exact z2_sp0 ih
  | shift_pair1 _ ih => exact z2_sp1 ih
  | shift_chain0 r_ch _ ih => exact z2_sc0 r_ch ih
  | shift_chain1 r_ch _ ih => exact z2_sc1 r_ch ih

lemma loc_z2p {r r' : zB} (hI : BRIncs false 128 r r') :
    (zCf r) [canon_tm]⊢⁺ (zCf (zTs [V,V,Q,V] r')) := by
  have hC := loc_z2o hI [] ([.cj] ++ [.ch] ^ 63) (Num.even 63)
  simp only [append_nil] at hC
  have hW := zW_full hC
  have heq : (t ++ t ++ d1 ++ t) +> r' = zTs [V,V,Q,V] r' := by
    simp only [zTs,t,d1,List.cons_append,List.nil_append,append_cons,append_nil]
  rwa [heq] at hW

-- Section 7A: Binary, Digits (zDg), Weights (z0Y..z11, z0W), z0L, zHn
inductive Binary : Nat -> Nat -> zB -> Prop where
  | one : Binary 1 1 (d1 +> default)
  | zero {n H : Nat} {r : zB} : Binary (1 + n) H r -> Binary (2 + n * 2) (1 + H) (d0 +> r)
  | two {n H : Nat} {r : zB} : Binary (1 + n) H r -> Binary (3 + n * 2) (1 + H) (d1 +> r)

lemma z0H {A H : Nat} {r : zB} (h : Binary A H r) :
    BRIncs false ((A - 1) * 2) default r := by
  induction h with
  | one =>
    have h0 := BRIncs.zero (default : zB)
    have hd : d1 +> (default : zB) = one +> default := by simp [d1,one]
    rw [hd]; exact h0
  | @zero n H r _ ih =>
    have ih' : BRIncs false (n * 2) default r := by
      have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
      rwa [heq] at ih
    have hs := BRIncs.short00 ih'
    rw [zDd] at hs
    have heq : ((2 + n * 2) - 1) * 2 = 2 + n * 4 := by omega
    rwa [heq]
  | @two n H r _ ih =>
    have ih' : BRIncs false (n * 2) default r := by
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
      | K => rcases zD0 h2 with ⟨_,_,_,_,h⟩; omega
      | Q => rcases zD1 h2 with ⟨_,_,_,_,h⟩; omega
  | @zero A H u _ ih =>
    intro v h2
    generalize hA_eq : A * 2 = A0 at h2
    generalize hH_eq : 1 + H = H0 at h2
    cases h2 with
    | nil => omega
    | @zero A' H' v' hD =>
      have hA : A = A' := by omega
      have hH : H = H' := by omega
      subst hA hH; rw [ih hD]
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
      subst hA hH; rw [ih hD]

def z0L : zW -> Bool
  | Q :: K :: _ => true
  | Q :: Q :: _ => true
  | _ :: v => z0L v
  | [] => false

lemma loc_z1I (u v : zW) (h : z0L v = true) : z0L (u ++ v) = true := by
  induction u with
  | nil => exact h
  | cons w u ih =>
    cases w with
    | V => exact ih
    | K => exact ih
    | Q =>
      cases u with
      | nil =>
        cases v with
        | nil => contradiction
        | cons w2 v' => (cases w2 <;> simp [z0L] at h ⊢); exact h
      | cons w2 u' =>
        cases w2 with
        | V => exact ih
        | K => rfl
        | Q => rfl

lemma zDg_pos_z0L {A H : Nat} {w : zW} (hD : zDg A H w) (hPos : 0 < A) :
    z0L (w ++ [K]) = true := by
  induction hD with
  | nil => omega
  | @zero A1 H1 u1 _ ih =>
    exact ih (by omega)
  | @one A1 H1 u1 hDu _ =>
    cases hDu with
    | nil => rfl
    | zero _ => rfl
    | one _ => rfl

def loc_z0W : zW -> Rat
  | [] => 0
  | V :: v => loc_z0W v * (1 / 2)
  | K :: v => (11 / 8) + loc_z0W v * 2
  | Q :: v => 1 + loc_z0W v * 2

lemma loc_zWn (u : zW) : 0 <= z1e u /\ 0 <= z1f u /\ 0 <= z1g u /\ 0 <= loc_z0W u := by
  induction u with
  | nil => simp [z1e,z1f,z1g,loc_z0W]
  | cons a u ih =>
    cases a <;> (dsimp [z1e,z1f,z1g,loc_z0W]; refine ⟨by linarith,by linarith,by linarith,by linarith⟩)

lemma zWY (u : zW) : z1e u <= loc_z0W u /\ loc_z0W u <= (11 / 8) * z1e u := by
  induction u with
  | nil => simp [z1e,loc_z0W]
  | cons a u ih =>
    cases a <;> (dsimp [z1e,loc_z0W]; constructor <;> linarith)

lemma z13W (u v : zW) : loc_z0W (u ++ v) = loc_z0W u + z1h u * loc_z0W v := by
  induction u with
  | nil => simp [loc_z0W,z1h]
  | cons a u ih => cases a <;> (dsimp [loc_z0W,z1h]; rw [ih]; ring)

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
        have hw := (loc_zWn u).1
        dsimp [z1e] at hM; linarith
      | succ h =>
        dsimp [z1e,zHn] at hM ⊢
        apply ih h
        rw [Nat.pow_succ] at hM; push_cast at hM ⊢; linarith
    | Q =>
      cases h with
      | zero =>
        have hw := (loc_zWn u).1
        dsimp [z1e] at hM; linarith
      | succ h =>
        dsimp [z1e,zHn] at hM ⊢
        apply ih h
        rw [Nat.pow_succ] at hM; push_cast at hM ⊢; linarith

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

-- Section 7B: Scan on digit words

lemma z0L_odd_scan {n : Nat} {w : zW} {b : Nat} {v : zW} {l : Rat}
    (h : Scan (1 + n * 2) (w ++ [Q,Q,K]) b v l)
    (hL : z0L (Q :: w ++ [K]) = true) :
    z0L (w ++ [K]) = true := by
  cases w with
  | nil =>
    exact False.elim (zSo 1 n b v l h)
  | cons t0 w' =>
    cases t0 with
    | V => exact hL
    | K => exact False.elim (zSz n (w' ++ [Q,Q,K]) b v l h)
    | Q =>
      cases w' with
      | nil => rfl
      | cons t1 w'' =>
        cases t1 with
        | K => rfl
        | Q => rfl
        | V =>
          change Scan (1 + n * 2) (Q :: V :: (w'' ++ [Q,Q,K])) b v l at h
          generalize ha : 1 + n * 2 = a at h
          cases h <;> omega

lemma zScan_qqk {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) :
    ∀ (w0 : zW),u = w0 ++ [Q,Q,K] ->
      z1h v <= (1 / 8) * z1h u /\
      (z0L (w0 ++ [K]) = true -> z1h v <= (1 / 64) * z1h u) /\
      (∃ n,b = n * 4) /\
      (∃ v0,v = v0 ++ [V]) := by
  induction h with
  | nil _ =>
    intro w0 hu
    cases w0 <;> simp at hu
  | @T n u0 k v0 l0 _ ih =>
    intro w0 hu
    cases w0 with
    | nil => simp at hu
    | cons t0 w' =>
      injection hu with ht0 hu0; subst ht0
      rcases ih w' hu0 with ⟨h1,h2,⟨m,hm⟩,⟨vp,hvp⟩⟩
      refine ⟨by dsimp [z1h]; linarith,fun hL => ?_,⟨m,hm⟩,⟨V :: vp,by simp [hvp]⟩⟩
      have h2' := h2 hL
      dsimp [z1h]; linarith
  | @pair0 n u0 k v0 l0 _ ih =>
    intro w0 hu
    cases w0 with
    | nil => simp at hu
    | cons t0 w1 =>
      cases w1 with
      | nil => cases t0 <;> simp at hu
      | cons t1 w' =>
        injection hu with ht0 hu1
        injection hu1 with ht1 hu0
        subst ht0 ht1
        rcases ih w' hu0 with ⟨h1,_,⟨m,hm⟩,⟨vp,hvp⟩⟩
        have hp := zSp u0
        refine ⟨by dsimp [z1h]; linarith,fun _ => by dsimp [z1h]; linarith,⟨m,hm⟩,⟨V :: vp,by simp [hvp]⟩⟩
  | @pair1 n u0 k v0 l0 hSub ih =>
    intro w0 hu
    cases w0 with
    | nil =>
      injection hu with _ hu1
      injection hu1 with _ hu0
      subst hu0
      exact False.elim (zSz n [] k v0 l0 hSub)
    | cons t0 w1 =>
      cases w1 with
      | nil =>
        injection hu with ht0 hu1
        injection hu1 with _ hu0
        subst ht0 hu0
        rcases zS1 0 (1 + n * 2) k v0 l0 hSub with ⟨rfl,hk,_⟩
        refine ⟨by norm_num [z1h],fun _ => by norm_num [z1h],⟨n,by omega⟩,⟨[V],rfl⟩⟩
      | cons t1 w' =>
        injection hu with ht0 hu1
        injection hu1 with ht1 hu0
        subst ht0 ht1
        rcases ih w' hu0 with ⟨h1,_,⟨m,hm⟩,⟨vp,hvp⟩⟩
        have hp := zSp u0
        refine ⟨by dsimp [z1h]; linarith,fun _ => by dsimp [z1h]; linarith,⟨m,hm⟩,⟨V :: vp,by simp [hvp]⟩⟩
  | @short00 n u0 k v0 l0 _ ih =>
    intro w0 hu
    cases w0 with
    | nil => simp at hu
    | cons t0 w' =>
      injection hu with ht0 hu0; subst ht0
      rcases ih w' hu0 with ⟨h1,h2,⟨m,hm⟩,⟨vp,hvp⟩⟩
      refine ⟨by dsimp [z1h]; linarith,fun hL => ?_,⟨m,hm⟩,⟨K :: vp,by simp [hvp]⟩⟩
      have h2' := h2 hL
      dsimp [z1h]; linarith
  | @short10 n u0 k v0 l0 _ ih =>
    intro w0 hu
    cases w0 with
    | nil => simp at hu
    | cons t0 w' =>
      injection hu with ht0 hu0; subst ht0
      rcases ih w' hu0 with ⟨h1,h2,⟨m,hm⟩,⟨vp,hvp⟩⟩
      refine ⟨by dsimp [z1h]; linarith,fun hL => ?_,⟨m,hm⟩,⟨Q :: vp,by simp [hvp]⟩⟩
      have h2' := h2 hL
      dsimp [z1h]; linarith
  | @short01 n u0 k v0 l0 hSub ih =>
    intro w0 hu
    cases w0 with
    | nil =>
      injection hu with _ hu0; subst hu0
      rcases zS1 0 (1 + n * 2) k v0 l0 hSub with ⟨rfl,hk,_⟩
      refine ⟨by norm_num [z1h],fun hL => by contradiction,⟨n,by omega⟩,⟨[K],rfl⟩⟩
    | cons t0 w' =>
      injection hu with ht0 hu0; subst ht0
      rcases ih w' hu0 with ⟨h1,h2,⟨m,hm⟩,⟨vp,hvp⟩⟩
      refine ⟨by dsimp [z1h]; linarith,fun hL => ?_,⟨m,hm⟩,⟨K :: vp,by simp [hvp]⟩⟩
      rw [hu0] at hSub
      have h2' := h2 (z0L_odd_scan hSub hL)
      dsimp [z1h]; linarith
  | @short11 n u0 k v0 l0 hSub ih =>
    intro w0 hu
    cases w0 with
    | nil =>
      injection hu with _ hu0; subst hu0
      rcases zS1 0 (1 + n * 2) k v0 l0 hSub with ⟨rfl,hk,_⟩
      refine ⟨by norm_num [z1h],fun hL => by contradiction,⟨n,by omega⟩,⟨[Q],rfl⟩⟩
    | cons t0 w' =>
      injection hu with ht0 hu0; subst ht0
      rcases ih w' hu0 with ⟨h1,h2,⟨m,hm⟩,⟨vp,hvp⟩⟩
      refine ⟨by dsimp [z1h]; linarith,fun hL => ?_,⟨m,hm⟩,⟨Q :: vp,by simp [hvp]⟩⟩
      rw [hu0] at hSub
      have h2' := h2 (z0L_odd_scan hSub hL)
      dsimp [z1h]; linarith

-- Section 7C: BScan (15 constructors) and its lemmas
def zIv : Nat -> Rat
  | 0 => 1
  | r + 1 => zIv r * (1 / 2)

def zP4 : Nat -> Rat
  | 0 => 1
  | r + 1 => zP4 r * 4

lemma zIv_P4 (r : Nat) :
    0 < zIv r /\ zIv r <= 1 /\ 1 <= zP4 r /\ (1 <= r -> 4 <= zP4 r /\ 8 * zIv r <= zP4 r) := by
  induction r with
  | zero =>
    dsimp [zIv,zP4]
    refine ⟨by linarith,by linarith,by linarith,fun h => by omega⟩
  | succ r ih =>
    rcases ih with ⟨h1,h2,h3,h4⟩
    dsimp [zIv,zP4]
    cases r with
    | zero =>
      dsimp [zIv,zP4]
      refine ⟨by linarith,by linarith,by linarith,fun _ => ⟨by linarith,by linarith⟩⟩
    | succ r' =>
      rcases h4 (by omega) with ⟨h4a,h4b⟩
      refine ⟨by linarith,by linarith,by linarith,fun _ => ⟨by linarith,by linarith⟩⟩

lemma z11_R (r : Nat) (u : zW) :
    z1h (zR r V ++ u) = zIv r * z1h u := by
  induction r with
  | zero => simp [zIv]
  | succ r ih =>
    dsimp [List.replicate,z1h,zIv]
    rw [ih]; ring

lemma z11_QK (r : Nat) (u : zW) :
    z1h (zQK r u) = zP4 r * z1h u := by
  induction r with
  | zero => simp [zQK,zP4]
  | succ r ih =>
    dsimp [zQK,z1h,zP4]
    rw [ih]; ring

lemma z0W_R (r : Nat) (u : zW) :
    loc_z0W (zR r V ++ u) = zIv r * loc_z0W u := by
  induction r with
  | zero => simp [zIv]
  | succ r ih =>
    dsimp [List.replicate,loc_z0W,zIv]
    rw [ih]; ring

lemma z0W_QK (r : Nat) (u : zW) :
    loc_z0W (zQK r u) = (5 / 4) * (zP4 r - 1) + zP4 r * loc_z0W u := by
  induction r with
  | zero => simp [zQK,zP4]
  | succ r ih =>
    dsimp [zQK,loc_z0W,zP4]
    rw [ih]; ring

inductive BScan : Bool -> Nat -> zW -> Nat -> zW -> Rat -> Rat -> Prop where
  | nil (k : Nat) : BScan false k [] k [] 0 0
  | T {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2) u k v a b ->
      BScan false (2 + n) (V :: u) k (V :: v) (a * (1 / 2)) (b * (1 / 2))
  | pair0 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan false (n * 2) u k v a b ->
      BScan false (1 + n) (Q :: K :: u) k (V :: v) (a * (1 / 2)) ((1 / 4) + b * (1 / 2))
  | pair1 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2) u k v a b ->
      BScan false (1 + n) (Q :: Q :: u) k (V :: v) (a * (1 / 2)) ((1 / 2) + b * (1 / 2))
  | short00 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan false (n * 2) u k v a b ->
      BScan false (2 + n * 4) (K :: u) k (K :: v) ((5 / 2) + a * 2) (b * 2)
  | short01 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2) u k v a b ->
      BScan false (2 + n * 4) (Q :: u) k (K :: v) ((3 / 2) + a * 2) (b * 2)
  | short10 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan false (n * 2) u k v a b ->
      BScan false (4 + n * 4) (K :: u) k (Q :: v) ((7 / 2) + a * 2) (b * 2)
  | short11 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2) u k v a b ->
      BScan false (4 + n * 4) (Q :: u) k (Q :: v) ((5 / 2) + a * 2) (b * 2)
  | odd_chain0 (r : Nat) {m : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (1 + r)) u k v a b ->
      BScan false (3 + m * 4) (zQK r (V :: u)) k (K :: (zR r V ++ v))
        ((2 + a * 2) * zIv r) (b * 2 * zIv r)
  | odd_chain1 (r : Nat) {m : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (1 + r)) u k v a b ->
      BScan false (5 + m * 4) (zQK r (V :: u)) k (Q :: (zR r V ++ v))
        (1 + (2 + a * 2) * zIv r) (b * 2 * zIv r)
  | even_chain (r : Nat) {m : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan true (1 + (1 + m * 2) * 2 ^ (1 + r)) u k v a b ->
      BScan false (6 + m * 2) (K :: zQK r (V :: u)) k (zR (1 + r) V ++ v)
        (1 + (1 + a) * (1 / 2) * zIv r) (b * (1 / 2) * zIv r)
  | shift_pair0 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan false (n * 2) u k v a b ->
      BScan true (1 + n) (K :: u) k (V :: v) (a * (1 / 2)) ((1 / 4) + b * (1 / 2))
  | shift_pair1 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan false (1 + n * 2) u k v a b ->
      BScan true (1 + n) (Q :: u) k (V :: v) (a * (1 / 2)) ((1 / 2) + b * (1 / 2))
  | shift_chain0 (r : Nat) {m : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (2 + r)) u k v a b ->
      BScan true (3 + m * 4) (K :: zQK r (V :: u)) k (K :: (zR (1 + r) V ++ v))
        ((1 + a) * zIv r) (b * zIv r)
  | shift_chain1 (r : Nat) {m : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      BScan true (1 + m * 2 ^ (2 + r)) u k v a b ->
      BScan true (5 + m * 4) (K :: zQK r (V :: u)) k (Q :: (zR (1 + r) V ++ v))
        (1 + (1 + a) * zIv r) (b * zIv r)

lemma zIv_pow2 (r : Nat) :
    ((2 ^ r : Nat) : Rat) * zIv r = 1 := by
  induction r with
  | zero => simp [zIv]
  | succ r ih =>
    rw [Nat.pow_succ]; dsimp [zIv]; push_cast at ih ⊢; linarith

lemma loc_z1i {s : Bool} {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : BScan s k u k' v a b) :
    (k : Rat) - 3 = ((k' : Rat) - 3) * z1h v + 2 * (a - b) := by
  induction h with
  | nil k => simp [z1h]
  | T _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | pair0 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | pair1 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short00 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short01 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short10 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short11 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | @odd_chain0 r m u k v a b _ ih =>
    dsimp [z1h]; rw [z11_R]
    have hp : ((2 ^ (1 + r) : Nat) : Rat) * zIv r = 2 := by
      have hp0 := zIv_pow2 r; rw [zP2 r]; push_cast at hp0 ⊢; linarith
    calc ((3 + m * 4 : Nat) : Rat) - 3
      _ = (m : Rat) * 2 * (((2 ^ (1 + r) : Nat) : Rat) * zIv r) := by rw [hp]; push_cast; ring
      _ = (((1 + m * 2 ^ (1 + r) : Nat) : Rat) - 3) * (2 * zIv r) + 4 * zIv r := by push_cast; ring
      _ = (((k : Rat) - 3) * z1h v + 2 * (a - b)) * (2 * zIv r) + 4 * zIv r := by rw [ih]
      _ = ((k : Rat) - 3) * (zIv r * z1h v * 2) + 2 * ((2 + a * 2) * zIv r - b * 2 * zIv r) := by ring
  | @odd_chain1 r m u k v a b _ ih =>
    dsimp [z1h]; rw [z11_R]
    have hp : ((2 ^ (1 + r) : Nat) : Rat) * zIv r = 2 := by
      have hp0 := zIv_pow2 r; rw [zP2 r]; push_cast at hp0 ⊢; linarith
    calc ((5 + m * 4 : Nat) : Rat) - 3
      _ = 2 + (m : Rat) * 2 * (((2 ^ (1 + r) : Nat) : Rat) * zIv r) := by rw [hp]; push_cast; ring
      _ = (((1 + m * 2 ^ (1 + r) : Nat) : Rat) - 3) * (2 * zIv r) + 4 * zIv r + 2 := by push_cast; ring
      _ = (((k : Rat) - 3) * z1h v + 2 * (a - b)) * (2 * zIv r) + 4 * zIv r + 2 := by rw [ih]
      _ = ((k : Rat) - 3) * (zIv r * z1h v * 2) + 2 * (1 + (2 + a * 2) * zIv r - b * 2 * zIv r) := by ring
  | @even_chain r m u k v a b _ ih =>
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    rw [h1r]; dsimp [z1h]; rw [z11_R]
    have hp : ((2 ^ (1 + r) : Nat) : Rat) * zIv r = 2 := by
      have hp0 := zIv_pow2 r; rw [zP2 r]; push_cast at hp0 ⊢; linarith
    calc ((6 + m * 2 : Nat) : Rat) - 3
      _ = 2 + (1 + (m : Rat) * 2) * (1 / 2) * (((2 ^ (1 + r) : Nat) : Rat) * zIv r) := by rw [hp]; push_cast; ring
      _ = (((1 + (1 + m * 2) * 2 ^ (1 + r) : Nat) : Rat) - 3) * ((1 / 2) * zIv r) + zIv r + 2 := by push_cast; ring
      _ = (((k : Rat) - 3) * z1h v + 2 * (a - b)) * ((1 / 2) * zIv r) + zIv r + 2 := by rw [ih]
      _ = ((k : Rat) - 3) * (zIv r * z1h v * (1 / 2)) + 2 * (1 + (1 + a) * (1 / 2) * zIv r - b * (1 / 2) * zIv r) := by ring
  | shift_pair0 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | shift_pair1 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | @shift_chain0 r m u k v a b _ ih =>
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    rw [h1r]; dsimp [z1h]; rw [z11_R]
    have hp : ((2 ^ (2 + r) : Nat) : Rat) * zIv r = 4 := by
      have hp0 := zIv_pow2 r
      have h2r : 2 + r = 1 + (1 + r) := by omega
      rw [h2r,zP2 (1 + r),zP2 r]; push_cast at hp0 ⊢; linarith
    calc ((3 + m * 4 : Nat) : Rat) - 3
      _ = (m : Rat) * (((2 ^ (2 + r) : Nat) : Rat) * zIv r) := by rw [hp]; push_cast; ring
      _ = (((1 + m * 2 ^ (2 + r) : Nat) : Rat) - 3) * zIv r + 2 * zIv r := by push_cast; ring
      _ = (((k : Rat) - 3) * z1h v + 2 * (a - b)) * zIv r + 2 * zIv r := by rw [ih]
      _ = ((k : Rat) - 3) * (zIv r * z1h v * (1 / 2) * 2) + 2 * ((1 + a) * zIv r - b * zIv r) := by ring
  | @shift_chain1 r m u k v a b _ ih =>
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    rw [h1r]; dsimp [z1h]; rw [z11_R]
    have hp : ((2 ^ (2 + r) : Nat) : Rat) * zIv r = 4 := by
      have hp0 := zIv_pow2 r
      have h2r : 2 + r = 1 + (1 + r) := by omega
      rw [h2r,zP2 (1 + r),zP2 r]; push_cast at hp0 ⊢; linarith
    calc ((5 + m * 4 : Nat) : Rat) - 3
      _ = 2 + (m : Rat) * (((2 ^ (2 + r) : Nat) : Rat) * zIv r) := by rw [hp]; push_cast; ring
      _ = (((1 + m * 2 ^ (2 + r) : Nat) : Rat) - 3) * zIv r + 2 * zIv r + 2 := by push_cast; ring
      _ = (((k : Rat) - 3) * z1h v + 2 * (a - b)) * zIv r + 2 * zIv r + 2 := by rw [ih]
      _ = ((k : Rat) - 3) * (zIv r * z1h v * (1 / 2) * 2) + 2 * (1 + (1 + a) * zIv r - b * zIv r) := by ring

lemma loc_z1j {s : Bool} {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : BScan s k u k' v a b) :
    (s = false ->
      loc_z0W v <= (66 / 19) * loc_z0W u /\
      a - b <= (64 / 11) * loc_z0W u /\
      b - a <= (1 / 2) * loc_z0W u) /\
    (s = true ->
      loc_z0W v <= (33 / 38) * loc_z0W u - (11 / 16) /\
      a - b <= (16 / 11) * loc_z0W u - (3 / 2) /\
      b - a <= (1 / 8) * loc_z0W u + (3 / 8)) /\
    (s = true -> (∃ m,k = 1 + m * 4) ->
      loc_z0W v <= (33 / 38) * loc_z0W u - (33 / 38)) := by
  induction h with
  | nil _ =>
    refine ⟨fun _ => by simp [loc_z0W],fun h => by contradiction,fun h _ => by contradiction⟩
  | @T n u k v a b _ ih =>
    rcases ih.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun _ => ?_,fun h => by contradiction,fun h _ => by contradiction⟩
    dsimp [loc_z0W]; refine ⟨by linarith,by linarith,by linarith⟩
  | @pair0 n u k v a b _ ih =>
    rcases ih.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun _ => ?_,fun h => by contradiction,fun h _ => by contradiction⟩
    dsimp [loc_z0W]; refine ⟨by linarith,by linarith,by linarith⟩
  | @pair1 n u k v a b _ ih =>
    rcases ih.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun _ => ?_,fun h => by contradiction,fun h _ => by contradiction⟩
    dsimp [loc_z0W]; refine ⟨by linarith,by linarith,by linarith⟩
  | @short00 n u k v a b _ ih =>
    rcases ih.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun _ => ?_,fun h => by contradiction,fun h _ => by contradiction⟩
    dsimp [loc_z0W]; refine ⟨by linarith,by linarith,by linarith⟩
  | @short01 n u k v a b _ ih =>
    rcases ih.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun _ => ?_,fun h => by contradiction,fun h _ => by contradiction⟩
    dsimp [loc_z0W]; refine ⟨by linarith,by linarith,by linarith⟩
  | @short10 n u k v a b _ ih =>
    rcases ih.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun _ => ?_,fun h => by contradiction,fun h _ => by contradiction⟩
    dsimp [loc_z0W]; refine ⟨by linarith,by linarith,by linarith⟩
  | @short11 n u k v a b _ ih =>
    rcases ih.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun _ => ?_,fun h => by contradiction,fun h _ => by contradiction⟩
    dsimp [loc_z0W]; refine ⟨by linarith,by linarith,by linarith⟩
  | @odd_chain0 r m u k v a b _ ih =>
    rcases ih.2.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun _ => ?_,fun h => by contradiction,fun h _ => by contradiction⟩
    dsimp [loc_z0W]; rw [z0W_R,z0W_QK]; dsimp [loc_z0W]
    cases r with
    | zero =>
      dsimp [zIv,zP4]; refine ⟨by linarith,by linarith,by linarith⟩
    | succ r' =>
      rcases zIv_P4 (r' + 1) with ⟨hiv1,hiv2,hp4,hge1⟩
      rcases hge1 (by omega) with ⟨hp4_4,_⟩
      refine ⟨by nlinarith,by nlinarith,by nlinarith⟩
  | @odd_chain1 r m u k v a b _ ih =>
    rcases ih.2.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun _ => ?_,fun h => by contradiction,fun h _ => by contradiction⟩
    dsimp [loc_z0W]; rw [z0W_R,z0W_QK]; dsimp [loc_z0W]
    cases r with
    | zero =>
      dsimp [zIv,zP4]; refine ⟨by linarith,by linarith,by linarith⟩
    | succ r' =>
      rcases zIv_P4 (r' + 1) with ⟨hiv1,hiv2,hp4,hge1⟩
      rcases hge1 (by omega) with ⟨hp4_4,_⟩
      refine ⟨by nlinarith,by nlinarith,by nlinarith⟩
  | @even_chain r m u k v a b _ ih =>
    rcases ih.2.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun _ => ?_,fun h => by contradiction,fun h _ => by contradiction⟩
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    rw [h1r]; dsimp [loc_z0W]; rw [z0W_R,z0W_QK]; dsimp [loc_z0W]
    rcases zIv_P4 r with ⟨hiv1,hiv2,hp4,_⟩
    refine ⟨by nlinarith,by nlinarith,by nlinarith⟩
  | @shift_pair0 n u k v a b _ ih =>
    rcases ih.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun h => by contradiction,fun _ => ?_,fun _ _ => ?_⟩
    · dsimp [loc_z0W]; refine ⟨by linarith,by linarith,by linarith⟩
    · dsimp [loc_z0W]; linarith
  | @shift_pair1 n u k v a b _ ih =>
    rcases ih.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun h => by contradiction,fun _ => ?_,fun _ _ => ?_⟩
    · dsimp [loc_z0W]; refine ⟨by linarith,by linarith,by linarith⟩
    · dsimp [loc_z0W]; linarith
  | @shift_chain0 r m u k v a b _ ih =>
    have hdiv : ∃ m',1 + m * 2 ^ (2 + r) = 1 + m' * 4 := by
      refine ⟨m * 2 ^ r,?_⟩
      have h2r : 2 + r = r + 2 := by omega
      rw [h2r,Nat.pow_add]; ring
    rcases ih.2.1 rfl with ⟨_,h2,h3⟩
    have h1 := ih.2.2 rfl hdiv
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun h => by contradiction,fun _ => ?_,fun _ ⟨q,hq⟩ => by omega⟩
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    rw [h1r]; dsimp [loc_z0W]; rw [z0W_R,z0W_QK]; dsimp [loc_z0W]
    cases r with
    | zero =>
      dsimp [zIv,zP4]; refine ⟨by linarith,by linarith,by linarith⟩
    | succ r' =>
      rcases zIv_P4 (r' + 1) with ⟨hiv1,hiv2,hp4,hge1⟩
      rcases hge1 (by omega) with ⟨hp4_4,_⟩
      refine ⟨by nlinarith,by nlinarith,by nlinarith⟩
  | @shift_chain1 r m u k v a b _ ih =>
    rcases ih.2.1 rfl with ⟨h1,h2,h3⟩
    have hw := (loc_zWn u).2.2.2
    refine ⟨fun h => by contradiction,fun _ => ?_,fun _ _ => ?_⟩
    · have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
        rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
      rw [h1r]; dsimp [loc_z0W]; rw [z0W_R,z0W_QK]; dsimp [loc_z0W]
      cases r with
      | zero =>
        dsimp [zIv,zP4]; refine ⟨by linarith,by linarith,by linarith⟩
      | succ r' =>
        rcases zIv_P4 (r' + 1) with ⟨hiv1,hiv2,hp4,hge1⟩
        rcases hge1 (by omega) with ⟨hp4_4,_⟩
        refine ⟨by nlinarith,by nlinarith,by nlinarith⟩
    · have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
        rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
      rw [h1r]; dsimp [loc_z0W]; rw [z0W_R,z0W_QK]; dsimp [loc_z0W]
      cases r with
      | zero =>
        dsimp [zIv,zP4]; linarith
      | succ r' =>
        rcases zIv_P4 (r' + 1) with ⟨hiv1,hiv2,hp4,hge1⟩
        rcases hge1 (by omega) with ⟨hp4_4,_⟩
        nlinarith

lemma loc_z1k {s : Bool} {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h1 : BScan s k u k' v a b) :
    ∀ {w : zW} {k'' : Nat} {x : zW} {c d : Rat},
      BScan false k' w k'' x c d ->
      ∃ a' b',BScan s k (u ++ w) k'' (v ++ x) a' b' /\
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
    exact ⟨a' * (1 / 2),(1 / 4) + b' * (1 / 2),BScan.pair0 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | pair1 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨a' * (1 / 2),(1 / 2) + b' * (1 / 2),BScan.pair1 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short00 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨(5 / 2) + a' * 2,b' * 2,BScan.short00 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short01 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨(3 / 2) + a' * 2,b' * 2,BScan.short01 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short10 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨(7 / 2) + a' * 2,b' * 2,BScan.short10 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short11 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨(5 / 2) + a' * 2,b' * 2,BScan.short11 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | @odd_chain0 r m u k v a b _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    have h_in : zQK r (V :: u) ++ w = zQK r (V :: (u ++ w)) := by
      rw [<- zQK_append]; rfl
    have h_out : K :: (zR r V ++ (v ++ x)) = (K :: (zR r V ++ v)) ++ x := by
      simp [List.append_assoc]
    refine ⟨(2 + a' * 2) * zIv r,b' * 2 * zIv r,?_ ,?_,?_⟩
    · rw [h_in,<- h_out]; exact BScan.odd_chain0 r hK
    · dsimp [z1h]; rw [z11_R,hA]; ring
    · dsimp [z1h]; rw [z11_R,hB]; ring
  | @odd_chain1 r m u k v a b _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    have h_in : zQK r (V :: u) ++ w = zQK r (V :: (u ++ w)) := by
      rw [<- zQK_append]; rfl
    have h_out : Q :: (zR r V ++ (v ++ x)) = (Q :: (zR r V ++ v)) ++ x := by
      simp [List.append_assoc]
    refine ⟨1 + (2 + a' * 2) * zIv r,b' * 2 * zIv r,?_ ,?_,?_⟩
    · rw [h_in,<- h_out]; exact BScan.odd_chain1 r hK
    · dsimp [z1h]; rw [z11_R,hA]; ring
    · dsimp [z1h]; rw [z11_R,hB]; ring
  | @even_chain r m u k v a b _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    have h_in : (K :: zQK r (V :: u)) ++ w = K :: zQK r (V :: (u ++ w)) := by
      simp [<- zQK_append]
    have h_out : zR (1 + r) V ++ (v ++ x) = (zR (1 + r) V ++ v) ++ x := by
      simp [List.append_assoc]
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    refine ⟨1 + (1 + a') * (1 / 2) * zIv r,b' * (1 / 2) * zIv r,?_ ,?_,?_⟩
    · rw [h_in,<- h_out]; exact BScan.even_chain r hK
    · rw [h1r]; dsimp [z1h]; rw [z11_R,hA]; ring
    · rw [h1r]; dsimp [z1h]; rw [z11_R,hB]; ring
  | shift_pair0 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨a' * (1 / 2),(1 / 4) + b' * (1 / 2),BScan.shift_pair0 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | shift_pair1 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨a' * (1 / 2),(1 / 2) + b' * (1 / 2),BScan.shift_pair1 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | @shift_chain0 r m u k v a b _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    have h_in : (K :: zQK r (V :: u)) ++ w = K :: zQK r (V :: (u ++ w)) := by
      simp [<- zQK_append]
    have h_out : K :: (zR (1 + r) V ++ (v ++ x)) = (K :: (zR (1 + r) V ++ v)) ++ x := by
      simp [List.append_assoc]
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    refine ⟨(1 + a') * zIv r,b' * zIv r,?_ ,?_,?_⟩
    · rw [h_in,<- h_out]; exact BScan.shift_chain0 r hK
    · dsimp [z1h]; rw [h1r]; dsimp [z1h]; rw [z11_R,hA]; ring
    · dsimp [z1h]; rw [h1r]; dsimp [z1h]; rw [z11_R,hB]; ring
  | @shift_chain1 r m u k v a b _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    have h_in : (K :: zQK r (V :: u)) ++ w = K :: zQK r (V :: (u ++ w)) := by
      simp [<- zQK_append]
    have h_out : Q :: (zR (1 + r) V ++ (v ++ x)) = (Q :: (zR (1 + r) V ++ v)) ++ x := by
      simp [List.append_assoc]
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    refine ⟨1 + (1 + a') * zIv r,b' * zIv r,?_ ,?_,?_⟩
    · rw [h_in,<- h_out]; exact BScan.shift_chain1 r hK
    · dsimp [z1h]; rw [h1r]; dsimp [z1h]; rw [z11_R,hA]; ring
    · dsimp [z1h]; rw [h1r]; dsimp [z1h]; rw [z11_R,hB]; ring

lemma loc_z1n {k : Nat} {u : zW} {k' : Nat} {v : zW} {l : Rat}
    (hI : Scan k u k' v l) :
    ∀ {A H : Nat},zDg A H u ->
      ∃ a b,BScan false k u k' v a b /\ a - b <= (5 / 2) * z1e v + l /\ b - a <= 1 := by
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
    exact ⟨a * (1 / 2),(1 / 4) + b * (1 / 2),BScan.pair0 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD1 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨a * (1 / 2),(1 / 2) + b * (1 / 2),BScan.pair1 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨(5 / 2) + a * 2,b * 2,BScan.short00 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨(3 / 2) + a * 2,b * 2,BScan.short01 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨(7 / 2) + a * 2,b * 2,BScan.short10 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨(5 / 2) + a * 2,b * 2,BScan.short11 hJ,by dsimp [z1e]; linarith,by linarith⟩

lemma zHi_bscan {m k' : Nat} {w0 y : zW} {l : Rat} {A0 H0 : Nat}
    (hS : Scan (m * 2) (w0 ++ [Q,Q,K]) k' y l)
    (hD0 : zDg A0 H0 w0) :
    ∃ a b,BScan false (1 + m) ((Q :: K :: w0) ++ [Q,Q,K]) k' (V :: y) a b /\
      z1e (V :: y) <= (1 / 4) * z1f (Q :: K :: w0) /\
      a - b <= (7 / 8) * z1f (Q :: K :: w0) /\
      b - a <= 1 := by
  have hD_qq : zDg 3 2 [Q,Q] := zDg.one (zDg.one zDg.nil)
  have hD_w : zDg (A0 + 3 * 2 ^ H0) (H0 + 2) (w0 ++ [Q,Q]) := z19 hD0 hD_qq
  have hS' : Scan (m * 2) ((w0 ++ [Q,Q]) ++ [K]) k' y l := by
    simpa [List.append_assoc] using! hS
  rcases z1x hS' (z1v hD_w) with ⟨hY,hL,_⟩
  have hZ_eq : z1f (w0 ++ [Q,Q]) = z1f w0 := by
    rw [z1k]; simp [z1f]
  rw [hZ_eq] at hY hL
  have hD_wk : zDg ((A0 + 3 * 2 ^ H0) + 0 * 2 ^ (H0 + 2)) ((H0 + 2) + 1) ((w0 ++ [Q,Q]) ++ [K]) :=
    z19 hD_w (zDg.zero zDg.nil)
  rcases loc_z1n hS' hD_wk with ⟨a0,b0,hB0,hAB0,hBA0⟩
  have hB0' : BScan false (m * 2) (w0 ++ [Q,Q,K]) k' y a0 b0 := by
    simpa [List.append_assoc] using! hB0
  refine ⟨a0 * (1 / 2),(1 / 4) + b0 * (1 / 2),BScan.pair0 hB0',?_,?_,?_⟩
  · dsimp [z1e,z1f]; linarith
  · dsimp [z1f]; linarith
  · linarith


end BusyBeaver.WordCanonBR
