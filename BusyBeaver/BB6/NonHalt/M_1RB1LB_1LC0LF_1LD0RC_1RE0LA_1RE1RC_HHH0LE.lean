/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LB_1LC0LF_1LD0RC_1RE0LA_1RE1RC_---0LE` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LB_1LC0LF_1LD0RC_1RE0LA_1RE1RC_---0LE`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LB_1LC0LF_1LD0RC_1RE0LA_1RE1RC_HHH0LE

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LB_1LC0LF_1LD0RC_1RE0LA_1RE1RC_---0LE`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 4, Stmt.write 0 Dir.left)

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
-- ============================================================================
-- Section 2: Turing Machine Infrastructure & Notations
-- ============================================================================


/- A Turing machine statement writing a symbol and moving in direction `dir`. -/
-- ============================================================================
-- Section 5: Specific Turing Machine: holdout_0203
-- ============================================================================
/- Transition function for holdout_0203: `1RB1LB_1LC0LF_1LD0RC_1RE0LA_1RE1RC_---0LE` -/

-- ============================================================================
-- Section 6: Proof of holdout_0203_nonhalt
-- ============================================================================

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

@[simp] lemma zMz (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] lemma tape_mk1_nil : Tape.mk₁ ([] : List (Fin 2)) = ⟨0, default, default⟩ := rfl
@[simp] lemma zPz (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma zPsl (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma zCal (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma zLan (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma zLac (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zZcd : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma zDt : (default : ListBlank (Fin 2)).tail = default := rfl
@[simp] lemma zAnl (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma zNal (l : List (Fin 2)) : [] ++ l = l := rfl

omit [Inhabited Γ] in
@[simp]
theorem zLpa (l : List Γ) (n m : Nat) : l^(n + m) = l^n ++ l^m := match m with
  | 0 => by simp_rw [HPow.hPow, add_zero, list_nat_repeat, List.append_nil]
  | m + 1 => by
    rw [add_comm m 1, <- add_assoc, add_comm 1 m, zLpa]
    simp only [HPow.hPow, list_nat_repeat, List.append_eq, List.append_assoc]
    rw [<- List.append_assoc, <- List.append_assoc, List.append_cancel_right_eq]
    induction n with
    | zero => simp
    | succ n ih => simpa

omit [Inhabited Γ] in
@[simp]
theorem zLpc (l : List Γ) (n m : Nat) : l^n ++ l^m = l^m ++ l^n := by
  rw [<- zLpa, add_comm, zLpa]

lemma zLaa (s : ListBlank Γ) (l₁ l₂ : List Γ) :
    (s <+ l₁) <+ l₂ = s <+ (l₂ ++ l₁) := by
  unfold ListBlank.append
  split
  · split
    · next h => simp_all
    · simp_all
  · rename_i _ l₂ l₁
    refine (congr_arg _ ?_).symm
    exact ListBlank.append_assoc l₁ _ s

lemma zLp1 (u : List (Fin 2)) (k : Nat) :
    u^k ++ u = u^(k + 1) := by
  have h := zLpc u k 1
  dsimp [HPow.hPow, list_nat_repeat] at h ⊢
  rw [List.append_nil] at h
  exact h

lemma zSm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂ := by simp [h]

lemma zSp2 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ := ⟨1, by decide, zSm tm c₁ c₂ h⟩

lemma zMa {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]

lemma zMt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rw [zMa, h₁]; simp [h₂]

lemma zPs {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

lemma zMst {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, zMt tm c₁ c₂ c₃ n m hn hm⟩

lemma zPsp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c₁ c₂ c₃ n m hn hm⟩

lemma zSsp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  zPsp (zSp2 tm c₁ c₂ h₁) h₂

lemma zSpp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), zMt tm c₁ c₂ c₃ n m hn hm⟩

lemma zPpp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  zPsp h₁ (zPs h₂)

macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine zSsp (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zZcd, zDh, zDt])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

-- Non-halting from an arbitrary configuration
def NonHaltFrom (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∀ n : Nat, (multiStep target_tm c n).isSome

lemma zIm_some {c : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : (multiStep target_tm c (j + d)).isSome) :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl

lemma multistep_nonhalt {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target_tm]⊢* c₂) (h₂ : NonHaltFrom c₂) :
    NonHaltFrom c₁ := by
  rcases h₁ with ⟨k, hk⟩
  intro n
  have h_some : (multiStep target_tm c₁ (k + n)).isSome := by
    rw [zMa, hk]
    exact h₂ n
  rw [Nat.add_comm k n] at h_some
  exact zIm_some h_some

-- Head configurations (L-R mirror of SBCv12.v TM1)
structure Head0 where
  q : Fin 6
  u : List (Fin 2)

def hf : Head0 := ⟨A, [0]⟩
def hh : Head0 := ⟨B, [1, 0]⟩
def ht : Head0 := ⟨E, [0, 0, 1, 0]⟩

def cfgL (h : Head0) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  l <{{h.q}} (h.u +> r)

def cfgR (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  l {{C}}> r

def sideLR (h : Head0) (l l' : ListBlank (Fin 2)) : Prop :=
  ∀ r : ListBlank (Fin 2), (cfgL h l r) [target_tm]⊢⁺ (cfgR l' r)

def segLR (h : Head0) (w w' : List (Fin 2)) : Prop :=
  ∀ l r : ListBlank (Fin 2), (cfgL h (w +> l) r) [target_tm]⊢⁺ (cfgR (w' +> l) r)

def segLL (h h' : Head0) (w v : List (Fin 2)) : Prop :=
  ∀ l r : ListBlank (Fin 2), (cfgL h (w +> l) r) [target_tm]⊢* (cfgL h' l (v +> r))

def segRR (v w' : List (Fin 2)) : Prop :=
  ∀ l r : ListBlank (Fin 2), (cfgR l (v +> r)) [target_tm]⊢* (cfgR (w' +> l) r)

def Result (h : Head0) (l : ListBlank (Fin 2)) (P : ListBlank (Fin 2) → Prop) : Prop :=
  (∃ l', sideLR h l l' ∧ P l') ∨ (∀ r, NonHaltFrom (cfgL h l r))

lemma result_mono {h : Head0} {l : ListBlank (Fin 2)} {P Q : ListBlank (Fin 2) → Prop}
    (hr : Result h l P) (hPQ : ∀ l', P l' → Q l') : Result h l Q := by
  rcases hr with ⟨l', hstep, hP⟩ | hnh
  · exact Or.inl ⟨l', hstep, hPQ l' hP⟩
  · exact Or.inr hnh

lemma result_return {h : Head0} {w w' : List (Fin 2)} {l : ListBlank (Fin 2)}
    {P : ListBlank (Fin 2) → Prop}
    (hseg : segLR h w w') (hP : P (w' +> l)) : Result h (w +> l) P :=
  Or.inl ⟨w' +> l, fun r => hseg l r, hP⟩

def Calls (h h' : Head0) (w w' : List (Fin 2)) : Prop :=
  ∃ v, segLL h h' w v ∧ segRR v w'

lemma result_call {h h' : Head0} {w w' : List (Fin 2)} {l : ListBlank (Fin 2)}
    {P Q : ListBlank (Fin 2) → Prop}
    (hc : Calls h h' w w') (hr : Result h' l P)
    (hPQ : ∀ l', P l' → Q (w' +> l')) : Result h (w +> l) Q := by
  rcases hc with ⟨v, hLL, hRR⟩
  rcases hr with ⟨l', hstep, hP⟩ | hnh
  · refine Or.inl ⟨w' +> l', fun r => ?_, hPQ l' hP⟩
    exact zPsp (zSpp (hLL l r) (hstep (v +> r))) (hRR l' r)
  · refine Or.inr (fun r => ?_)
    exact multistep_nonhalt (hLL l r) (hnh (v +> r))

lemma calls_app {h1 h2 h3 : Head0} {w1 w2 w3 w4 : List (Fin 2)}
    (hc1 : Calls h1 h2 w1 w2) (hc2 : Calls h2 h3 w3 w4) :
    Calls h1 h3 (w1 ++ w3) (w2 ++ w4) := by
  rcases hc1 with ⟨v1, h1, h2⟩
  rcases hc2 with ⟨v2, h3, h4⟩
  refine ⟨v2 ++ v1, fun l r => ?_, fun l r => ?_⟩
  · rw [<- zLaa]
    have step1 := h1 (w3 +> l) r
    have step2 := h3 l (v1 +> r)
    rw [zLaa] at step2
    exact zMst step1 step2
  · rw [<- zLaa]
    have step1 := h4 l (v1 +> r)
    have step2 := h2 (w4 +> l) r
    rw [zLaa] at step2
    exact zMst step1 step2

-- Base return segments
lemma f_zero : segLR hf [0] [0, 0] := by
  intro l r; unfold cfgL cfgR hf; simp only [zCal, zLac, zLan]; execute

lemma h_zero : segLR hh [0, 0, 0] [1, 1, 0, 1, 1] := by
  intro l r; unfold cfgL cfgR hh; simp only [zCal, zLac, zLan]; execute

lemma h_one : segLR hh [0, 1] [1, 1, 0, 0] := by
  intro l r; unfold cfgL cfgR hh; simp only [zCal, zLac, zLan]; execute

-- Base and inductive call segments
lemma t_zeros_step : Calls ht ht [0] [0] := by
  refine ⟨[1], fun l r => ?_, fun l r => ?_⟩
  · refine zPs ?_; unfold cfgL ht; simp only [zCal, zLac, zLan]; execute
  · refine zPs ?_; unfold cfgR; simp only [zCal, zLac, zLan]; execute

lemma t_zeros (n : Nat) : Calls ht ht (([0] : List (Fin 2))^n) (([0] : List (Fin 2))^n) := by
  induction n with
  | zero =>
    refine ⟨[], fun l r => ⟨0, by simp⟩, fun l r => ⟨0, by simp⟩⟩
  | succ n ih =>
    simpa only [zPsl] using calls_app t_zeros_step ih

lemma t_four_step : Calls ht ht [1, 1, 1, 1] [1, 1, 1, 1] := by
  refine ⟨[1, 0, 1, 0], fun l r => ?_, fun l r => ?_⟩
  · refine zPs ?_; unfold cfgL ht; simp only [zCal, zLac, zLan]; execute
  · refine zPs ?_; unfold cfgR; simp only [zCal, zLac, zLan]; execute

lemma t_four_pow (q : Nat) : Calls ht ht (([1] : List (Fin 2))^(q * 4)) (([1] : List (Fin 2))^(q * 4)) := by
  induction q with
  | zero =>
    refine ⟨[], fun l r => ⟨0, by simp⟩, fun l r => ⟨0, by simp⟩⟩
  | succ q ih =>
    have h_eq : ([1] : List (Fin 2))^((q + 1) * 4) = ([1] : List (Fin 2))^(q * 4) ++ [1, 1, 1, 1] := by
      have h_add : (q + 1) * 4 = q * 4 + 4 := by omega
      rw [h_add, zLpa]; rfl
    rw [h_eq]
    exact calls_app ih t_four_step

lemma t_four (q : Nat) : Calls ht ht (([1] : List (Fin 2))^(4 + q * 4)) (([1] : List (Fin 2))^(4 + q * 4)) := by
  have h_eq : ([1] : List (Fin 2))^(4 + q * 4) = [1, 1, 1, 1] ++ ([1] : List (Fin 2))^(q * 4) := by
    rw [zLpa]; rfl
  rw [h_eq]
  exact calls_app t_four_step (t_four_pow q)

lemma t_one_base : Calls ht hf [1] [1, 1, 1, 1] := by
  refine ⟨[1, 0, 1, 0], fun l r => ?_, ?_⟩
  · refine zPs ?_; unfold cfgL ht hf; simp only [zCal, zLac, zLan]; execute
  · intro l r; unfold cfgR; refine zPs ?_; simp only [zCal, zLac, zLan]; execute

lemma t_one (q : Nat) : Calls ht hf (([1] : List (Fin 2))^(1 + q * 4)) (([1] : List (Fin 2))^(4 + q * 4)) := by
  have h1 : ([1] : List (Fin 2))^(1 + q * 4) = ([1] : List (Fin 2))^(q * 4) ++ [1] := by
    have h_add : 1 + q * 4 = q * 4 + 1 := by omega
    rw [h_add, zLpa]; rfl
  have h2 : ([1] : List (Fin 2))^(4 + q * 4) = ([1] : List (Fin 2))^(q * 4) ++ [1, 1, 1, 1] := by
    have h_add : 4 + q * 4 = q * 4 + 4 := by omega
    rw [h_add, zLpa]; rfl
  rw [h1, h2]
  exact calls_app (t_four_pow q) t_one_base

lemma t_two_base : Calls ht hh [1, 1] [1, 1, 1, 1] := by
  refine ⟨[1, 0, 1, 0], fun l r => ?_, ?_⟩
  · refine zPs ?_; unfold cfgL ht hh; simp only [zCal, zLac, zLan]; execute
  · intro l r; unfold cfgR; refine zPs ?_; simp only [zCal, zLac, zLan]; execute

lemma t_two (q : Nat) : Calls ht hh (([1] : List (Fin 2))^(2 + q * 4)) (([1] : List (Fin 2))^(4 + q * 4)) := by
  have h1 : ([1] : List (Fin 2))^(2 + q * 4) = ([1] : List (Fin 2))^(q * 4) ++ [1, 1] := by
    have h_add : 2 + q * 4 = q * 4 + 2 := by omega
    rw [h_add, zLpa]; rfl
  have h2 : ([1] : List (Fin 2))^(4 + q * 4) = ([1] : List (Fin 2))^(q * 4) ++ [1, 1, 1, 1] := by
    have h_add : 4 + q * 4 = q * 4 + 4 := by omega
    rw [h_add, zLpa]; rfl
  rw [h1, h2]
  exact calls_app (t_four_pow q) t_two_base

lemma h_two_four_base : Calls hh ht [0, 0, 1, 1, 1, 1] [1, 1, 0, 0] := by
  refine ⟨[1, 1, 1, 0], fun l r => ?_, fun l r => ?_⟩
  · refine zPs ?_; unfold cfgL hh ht; simp only [zCal, zLac, zLan]; execute
  · refine zPs ?_; unfold cfgR; simp only [zCal, zLac, zLan]; execute

lemma h_two_four (q : Nat) : Calls hh ht ([0, 0] ++ ([1] : List (Fin 2))^(4 + q * 4)) ([1, 1, 0, 0] ++ ([1] : List (Fin 2))^(q * 4)) := by
  have h1 : ([0, 0] ++ ([1] : List (Fin 2))^(4 + q * 4)) = [0, 0, 1, 1, 1, 1] ++ ([1] : List (Fin 2))^(q * 4) := by
    rw [zLpa]; rfl
  rw [h1]
  exact calls_app h_two_four_base (t_four_pow q)

lemma h_two_one_base : Calls hh hf [0, 0, 1] [1, 1, 0, 0] := by
  refine ⟨[1, 1, 1, 0], fun l r => ?_, fun l r => ?_⟩
  · refine zPs ?_; unfold cfgL hh hf; simp only [zCal, zLac, zLan]; execute
  · refine zPs ?_; unfold cfgR; simp only [zCal, zLac, zLan]; execute

lemma h_two_one (q : Nat) : Calls hh hf ([0, 0] ++ ([1] : List (Fin 2))^(1 + q * 4)) ([1, 1, 0, 0] ++ ([1] : List (Fin 2))^(q * 4)) := by
  cases q with
  | zero =>
    exact h_two_one_base
  | succ q' =>
    have h1 : ([0, 0] ++ ([1] : List (Fin 2))^(1 + (q' + 1) * 4)) =
        [0, 0, 1, 1, 1, 1] ++ ([1] : List (Fin 2))^(1 + q' * 4) := by
      have h_add : 1 + (q' + 1) * 4 = 4 + (1 + q' * 4) := by omega
      rw [h_add, zLpa]; rfl
    have h2 : ([1, 1, 0, 0] ++ ([1] : List (Fin 2))^((q' + 1) * 4)) =
        [1, 1, 0, 0] ++ ([1] : List (Fin 2))^(4 + q' * 4) := by
      have h_add : (q' + 1) * 4 = 4 + q' * 4 := by omega
      rw [h_add]
    rw [h1, h2]
    exact calls_app h_two_four_base (t_one q')

lemma h_two : Calls hh ht [1, 1] [] := by
  refine ⟨[], fun l r => ?_, fun l r => ⟨0, by simp⟩⟩
  refine zPs ?_; unfold cfgL hh ht; simp only [zCal, zLac, zLan]; execute

-- Blank divergence for ht
lemma t_blank_step (r : ListBlank (Fin 2)) :
    (cfgL ht default r) [target_tm]⊢⁺ (cfgL ht default ((1 : Fin 2) >> r)) := by
  unfold cfgL ht; simp only [zCal, zLac, zLan]; execute

lemma t_blank_reach (n : Nat) (r : ListBlank (Fin 2)) :
    ∃ N ≥ n, (multiStep target_tm (cfgL ht default r) N).isSome := by
  induction n generalizing r with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ n ih =>
    rcases t_blank_step r with ⟨k, hk_pos, hk⟩
    rcases ih ((1 : Fin 2) >> r) with ⟨N', hN', hsome⟩
    refine ⟨k + N', by omega, ?_⟩
    rw [zMa, hk]
    exact hsome

lemma t_blank (r : ListBlank (Fin 2)) : NonHaltFrom (cfgL ht default r) := by
  intro n
  rcases t_blank_reach n r with ⟨N, hN, hsome⟩
  have h_eq : n + (N - n) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at hsome
  exact zIm_some hsome

-- Inductive grammar G on the active left half-tape
inductive G : Bool → ListBlank (Fin 2) → Prop where
  | blank (p : Bool) : G p default
  | four (p : Bool) (n q : Nat) (l : ListBlank (Fin 2)) :
      G false l →
      G p ((([0] : List (Fin 2))^((if p then 2 else 3) + n * 3)) +>
           ((([1] : List (Fin 2))^(4 + q * 4)) +> l))
  | one (p : Bool) (n q : Nat) (l : ListBlank (Fin 2)) :
      G true l →
      G p ((([0] : List (Fin 2))^((if p then 2 else 3) + n * 3)) +>
           ((([1] : List (Fin 2))^(1 + q * 4)) +> l))
  | two (p : Bool) (n q : Nat) (l : ListBlank (Fin 2)) :
      G true l →
      G p ((([0] : List (Fin 2))^((if p then 1 else 2) + n * 3)) +>
           ((([1] : List (Fin 2))^(2 + q * 4)) +> l))

lemma zero_cons_pow (k : Nat) (s : ListBlank (Fin 2)) :
    (0 : Fin 2) >> ((([0] : List (Fin 2))^k) +> s) = (([0] : List (Fin 2))^(1 + k)) +> s := by
  have h : ([0] : List (Fin 2))^(1 + k) = [0] ++ ([0] : List (Fin 2))^k := by
    rw [zLpa]; rfl
  rw [h, <- zLaa]; rfl

lemma twozeros_append_pow (k : Nat) (s : ListBlank (Fin 2)) :
    ([0, 0] : List (Fin 2)) +> ((([0] : List (Fin 2))^k) +> s) = (([0] : List (Fin 2))^(2 + k)) +> s := by
  have h : ([0] : List (Fin 2))^(2 + k) = [0, 0] ++ ([0] : List (Fin 2))^k := by
    rw [zLpa]; rfl
  rw [h, <- zLaa]

lemma G_zero (l : ListBlank (Fin 2)) (h : G true l) : G false ((0 : Fin 2) >> l) := by
  cases h with
  | blank =>
    rw [zZcd]; exact G.blank false
  | four _ n q l₀ h₀ =>
    rw [zero_cons_pow]
    have h_exp : 1 + ((if true then 2 else 3) + n * 3) = (if false then 2 else 3) + n * 3 := by (try dsimp); omega
    rw [h_exp]
    exact G.four false n q l₀ h₀
  | one _ n q l₀ h₀ =>
    rw [zero_cons_pow]
    have h_exp : 1 + ((if true then 2 else 3) + n * 3) = (if false then 2 else 3) + n * 3 := by (try dsimp); omega
    rw [h_exp]
    exact G.one false n q l₀ h₀
  | two _ n q l₀ h₀ =>
    rw [zero_cons_pow]
    have h_exp : 1 + ((if true then 1 else 2) + n * 3) = (if false then 1 else 2) + n * 3 := by (try dsimp); omega
    rw [h_exp]
    exact G.two false n q l₀ h₀

lemma G_twozeros (l : ListBlank (Fin 2)) (h : G false l) : G true (([0, 0] : List (Fin 2)) +> l) := by
  cases h with
  | blank =>
    have h_def : ([0, 0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default := by
      simp [zLac, zLan, zZcd]
    rw [h_def]; exact G.blank true
  | four _ n q l₀ h₀ =>
    rw [twozeros_append_pow]
    have h_exp : 2 + ((if false then 2 else 3) + n * 3) = (if true then 2 else 3) + (1 + n) * 3 := by (try dsimp); omega
    rw [h_exp]
    exact G.four true (1 + n) q l₀ h₀
  | one _ n q l₀ h₀ =>
    rw [twozeros_append_pow]
    have h_exp : 2 + ((if false then 2 else 3) + n * 3) = (if true then 2 else 3) + (1 + n) * 3 := by (try dsimp); omega
    rw [h_exp]
    exact G.one true (1 + n) q l₀ h₀
  | two _ n q l₀ h₀ =>
    rw [twozeros_append_pow]
    have h_exp : 2 + ((if false then 1 else 2) + n * 3) = (if true then 1 else 2) + (1 + n) * 3 := by (try dsimp); omega
    rw [h_exp]
    exact G.two true (1 + n) q l₀ h₀

lemma G_twoblocks (q : Nat) (l : ListBlank (Fin 2)) (h : G false l) :
    G true (([0, 0] : List (Fin 2)) +> ((([1] : List (Fin 2))^(q * 4)) +> l)) := by
  cases q with
  | zero =>
    simpa using G_twozeros l h
  | succ q' =>
    have h_0 : ([0, 0] : List (Fin 2)) = ([0] : List (Fin 2))^((if true then 2 else 3) + 0 * 3) := rfl
    have h_1 : (q' + 1) * 4 = 4 + q' * 4 := by (try dsimp); omega
    rw [h_0, h_1]
    exact G.four true 0 q' l h

lemma G_mark (l : ListBlank (Fin 2)) (h : G true l) :
    G true (([0, 1, 1] : List (Fin 2)) +> l) := by
  have h_eq : ([0, 1, 1] : List (Fin 2)) +> l =
      (([0] : List (Fin 2))^((if true then 1 else 2) + 0 * 3)) +>
      ((([1] : List (Fin 2))^(2 + 0 * 4)) +> l) := rfl
  rw [h_eq]
  exact G.two true 0 0 l h

lemma G_true_has_zero (l : ListBlank (Fin 2)) (h : G true l) :
    ∃ u, l = ([0] : List (Fin 2)) +> u := by
  cases h with
  | blank =>
    refine ⟨default, ?_⟩
    simp [zLac, zLan, zZcd]
  | four _ n q l₀ _ =>
    refine ⟨(([0] : List (Fin 2))^(1 + n * 3)) +> ((([1] : List (Fin 2))^(4 + q * 4)) +> l₀), ?_⟩
    have h_exp : ([0] : List (Fin 2))^((if true then 2 else 3) + n * 3) =
        [0] ++ ([0] : List (Fin 2))^(1 + n * 3) := by
      have h_add : (if true then 2 else 3) + n * 3 = 1 + (1 + n * 3) := by (try dsimp); omega
      rw [h_add, zLpa]; rfl
    rw [h_exp, <- zLaa]
  | one _ n q l₀ _ =>
    refine ⟨(([0] : List (Fin 2))^(1 + n * 3)) +> ((([1] : List (Fin 2))^(1 + q * 4)) +> l₀), ?_⟩
    have h_exp : ([0] : List (Fin 2))^((if true then 2 else 3) + n * 3) =
        [0] ++ ([0] : List (Fin 2))^(1 + n * 3) := by
      have h_add : (if true then 2 else 3) + n * 3 = 1 + (1 + n * 3) := by (try dsimp); omega
      rw [h_add, zLpa]; rfl
    rw [h_exp, <- zLaa]
  | two _ n q l₀ _ =>
    refine ⟨(([0] : List (Fin 2))^(n * 3)) +> ((([1] : List (Fin 2))^(2 + q * 4)) +> l₀), ?_⟩
    have h_exp : ([0] : List (Fin 2))^((if true then 1 else 2) + n * 3) =
        [0] ++ ([0] : List (Fin 2))^(n * 3) := by
      have h_add : (if true then 1 else 2) + n * 3 = 1 + n * 3 := rfl
      rw [h_add, zLpa]; rfl
    rw [h_exp, <- zLaa]

lemma f_G (l : ListBlank (Fin 2)) (h : G true l) : Result hf l (G false) := by
  rcases G_true_has_zero l h with ⟨u, hlu⟩
  rw [hlu]
  refine result_return f_zero ?_
  have h_eq : ([0, 0] : List (Fin 2)) +> u = (0 : Fin 2) >> (([0] : List (Fin 2)) +> u) := rfl
  rw [h_eq, <- hlu]
  exact G_zero l h

def Mark (l : ListBlank (Fin 2)) : Prop :=
  ∃ u, G true u ∧ l = ([1, 1] : List (Fin 2)) +> u

lemma h_big (l : ListBlank (Fin 2)) (h : G true l) :
    Result hh (([0, 0, 0] : List (Fin 2)) +> l) Mark := by
  refine result_return h_zero ?_
  exact ⟨([0, 1, 1] : List (Fin 2)) +> l, G_mark l h, rfl⟩

lemma G_calls (p : Bool) (l : ListBlank (Fin 2)) (h : G p l) :
    Result ht l (G p) ∧ (p = true → Result hh l Mark) := by
  induction h with
  | blank p =>
    refine ⟨Or.inr t_blank, fun hp => ?_⟩
    have h_def : (default : ListBlank (Fin 2)) = ([0, 0, 0] : List (Fin 2)) +> default := by
      simp [zLac, zLan, zZcd]
    rw [h_def]
    exact h_big default (G.blank true)
  | four p n q l₀ h₀ ih =>
    rcases ih with ⟨IT, _⟩
    refine ⟨?_, fun hp => ?_⟩
    · rw [zLaa]
      refine result_call (calls_app (t_zeros ((if p then 2 else 3) + n * 3)) (t_four q)) IT ?_
      intro u hu
      rw [<- zLaa]
      exact G.four p n q u hu
    · subst hp
      cases n with
      | zero =>
        have h_eq : ((([0] : List (Fin 2))^((if true then 2 else 3) + 0 * 3)) +>
            ((([1] : List (Fin 2))^(4 + q * 4)) +> l₀)) =
            (([0, 0] ++ ([1] : List (Fin 2))^(4 + q * 4)) +> l₀) := by
          rw [<- zLaa]; rfl
        rw [h_eq]
        refine result_call (h_two_four q) IT ?_
        intro u hu
        refine ⟨([0, 0] : List (Fin 2)) +> ((([1] : List (Fin 2))^(q * 4)) +> u),
          G_twoblocks q u hu, ?_⟩
        rw [<- zLaa]; rfl
      | succ n' =>
        have h_eq : ((([0] : List (Fin 2))^((if true then 2 else 3) + (n' + 1) * 3)) +>
            ((([1] : List (Fin 2))^(4 + q * 4)) +> l₀)) =
            ([0, 0, 0] : List (Fin 2)) +>
            ((([0] : List (Fin 2))^((if true then 2 else 3) + n' * 3)) +>
             ((([1] : List (Fin 2))^(4 + q * 4)) +> l₀)) := by
          have h_exp : ([0] : List (Fin 2))^((if true then 2 else 3) + (n' + 1) * 3) =
              [0, 0, 0] ++ ([0] : List (Fin 2))^((if true then 2 else 3) + n' * 3) := by
            have h_add : (if true then 2 else 3) + (n' + 1) * 3 = 3 + ((if true then 2 else 3) + n' * 3) := by omega
            rw [h_add, zLpa]; rfl
          rw [h_exp, <- zLaa]
        rw [h_eq]
        exact h_big _ (G.four true n' q l₀ h₀)
  | one p n q l₀ h₀ ih =>
    refine ⟨?_, fun hp => ?_⟩
    · rw [zLaa]
      refine result_call (calls_app (t_zeros ((if p then 2 else 3) + n * 3)) (t_one q)) (f_G l₀ h₀) ?_
      intro u hu
      rw [<- zLaa]
      exact G.four p n q u hu
    · subst hp
      cases n with
      | zero =>
        have h_eq : ((([0] : List (Fin 2))^((if true then 2 else 3) + 0 * 3)) +>
            ((([1] : List (Fin 2))^(1 + q * 4)) +> l₀)) =
            (([0, 0] ++ ([1] : List (Fin 2))^(1 + q * 4)) +> l₀) := by
          rw [<- zLaa]; rfl
        rw [h_eq]
        refine result_call (h_two_one q) (f_G l₀ h₀) ?_
        intro u hu
        refine ⟨([0, 0] : List (Fin 2)) +> ((([1] : List (Fin 2))^(q * 4)) +> u),
          G_twoblocks q u hu, ?_⟩
        rw [<- zLaa]; rfl
      | succ n' =>
        have h_eq : ((([0] : List (Fin 2))^((if true then 2 else 3) + (n' + 1) * 3)) +>
            ((([1] : List (Fin 2))^(1 + q * 4)) +> l₀)) =
            ([0, 0, 0] : List (Fin 2)) +>
            ((([0] : List (Fin 2))^((if true then 2 else 3) + n' * 3)) +>
             ((([1] : List (Fin 2))^(1 + q * 4)) +> l₀)) := by
          have h_exp : ([0] : List (Fin 2))^((if true then 2 else 3) + (n' + 1) * 3) =
              [0, 0, 0] ++ ([0] : List (Fin 2))^((if true then 2 else 3) + n' * 3) := by
            have h_add : (if true then 2 else 3) + (n' + 1) * 3 = 3 + ((if true then 2 else 3) + n' * 3) := by omega
            rw [h_add, zLpa]; rfl
          rw [h_exp, <- zLaa]
        rw [h_eq]
        exact h_big _ (G.one true n' q l₀ h₀)
  | two p n q l₀ h₀ ih =>
    rcases ih with ⟨_, IH⟩
    refine ⟨?_, fun hp => ?_⟩
    · rw [zLaa]
      refine result_call (calls_app (t_zeros ((if p then 1 else 2) + n * 3)) (t_two q)) (IH rfl) ?_
      rintro v ⟨u, hu, rfl⟩
      rw [<- zLaa]
      have h_ones : (([1] : List (Fin 2))^(4 + q * 4)) +> (([1, 1] : List (Fin 2)) +> u) =
          (([1] : List (Fin 2))^(2 + (1 + q) * 4)) +> u := by
        have h_eq1 : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2))^2 := rfl
        have h_add : (4 + q * 4) + 2 = 2 + (1 + q) * 4 := by omega
        rw [h_eq1, zLaa, <- zLpa, h_add]
      rw [h_ones]
      exact G.two p n (1 + q) u hu
    · subst hp
      cases n with
      | zero =>
        have h_eq : ((([0] : List (Fin 2))^((if true then 1 else 2) + 0 * 3)) +>
            ((([1] : List (Fin 2))^(2 + q * 4)) +> l₀)) =
            ([0, 1] : List (Fin 2)) +> ((([1] : List (Fin 2))^(1 + q * 4)) +> l₀) := by
          have h_1 : ([1] : List (Fin 2))^(2 + q * 4) = [1] ++ ([1] : List (Fin 2))^(1 + q * 4) := by
            have h_add : 2 + q * 4 = 1 + (1 + q * 4) := by omega
            rw [h_add, zLpa]; rfl
          rw [h_1, <- zLaa]; rfl
        rw [h_eq]
        refine result_return h_one ?_
        refine ⟨(([0] : List (Fin 2))^((if true then 2 else 3) + 0 * 3)) +>
            ((([1] : List (Fin 2))^(1 + q * 4)) +> l₀),
          G.one true 0 q l₀ h₀, rfl⟩
      | succ n' =>
        have h_eq : ((([0] : List (Fin 2))^((if true then 1 else 2) + (n' + 1) * 3)) +>
            ((([1] : List (Fin 2))^(2 + q * 4)) +> l₀)) =
            ([0, 0, 0] : List (Fin 2)) +>
            ((([0] : List (Fin 2))^((if true then 1 else 2) + n' * 3)) +>
             ((([1] : List (Fin 2))^(2 + q * 4)) +> l₀)) := by
          have h_exp : ([0] : List (Fin 2))^((if true then 1 else 2) + (n' + 1) * 3) =
              [0, 0, 0] ++ ([0] : List (Fin 2))^((if true then 1 else 2) + n' * 3) := by
            have h_add : (if true then 1 else 2) + (n' + 1) * 3 = 3 + ((if true then 1 else 2) + n' * 3) := by omega
            rw [h_add, zLpa]; rfl
          rw [h_exp, <- zLaa]
        rw [h_eq]
        exact h_big _ (G.two true n' q l₀ h₀)

def Safe (l : ListBlank (Fin 2)) : Prop :=
  G true l ∨ Mark l

lemma safe_step (l : ListBlank (Fin 2)) (hs : Safe l) : Result hh l Safe := by
  rcases hs with hG | ⟨u, hG, rfl⟩
  · exact result_mono ((G_calls true l hG).2 rfl) (fun u hu => Or.inr hu)
  · refine result_call h_two (G_calls true u hG).1 ?_
    intro v hv
    exact Or.inl hv

def cfg (l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  cfgL hh l ((1 : Fin 2) >> default)

lemma left_return (l : ListBlank (Fin 2)) :
    (cfgR l ((1 : Fin 2) >> default)) [target_tm]⊢⁺ (cfg l) := by
  unfold cfg cfgL cfgR hh; simp only [zCal, zLac, zLan]; execute

lemma safe_reach (m : Nat) (l : ListBlank (Fin 2)) (hs : Safe l) :
    ∃ N ≥ m, (multiStep target_tm (cfg l) N).isSome := by
  induction m generalizing l with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ m ih =>
    rcases safe_step l hs with ⟨l', hstep, hs'⟩ | hnh
    · have hrun : (cfg l) [target_tm]⊢⁺ (cfg l') :=
        zPpp (hstep ((1 : Fin 2) >> default)) (left_return l')
      rcases hrun with ⟨k, hk_pos, hk⟩
      rcases ih l' hs' with ⟨N', hN', hsome⟩
      refine ⟨k + N', by omega, ?_⟩
      rw [zMa, hk]
      exact hsome
    · exact ⟨m + 1, Nat.le_refl (m + 1), hnh ((1 : Fin 2) >> default) (m + 1)⟩

lemma safe_nonhalt (l : ListBlank (Fin 2)) (hs : Safe l) : NonHaltFrom (cfg l) := by
  intro m
  rcases safe_reach m l hs with ⟨N, hN, hsome⟩
  have h_eq : m + (N - m) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at hsome
  exact zIm_some hsome

lemma init_to_cfg : (init []) [target_tm]⊢* (cfg default) := by
  refine zPs ?_
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold cfg cfgL hh
  simp only [zCal, zLac, zLan]
  execute

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
  have h_nh : NonHaltFrom (init []) :=
    multistep_nonhalt init_to_cfg (safe_nonhalt default (Or.inl (G.blank true)))
  intro c hc
  rcases hc with ⟨n, hn⟩
  have h_some := h_nh (n + 1)
  rw [zMs, hn] at h_some
  exact h_some

end BusyBeaver.M_1RB1LB_1LC0LF_1LD0RC_1RE0LA_1RE1RC_HHH0LE
