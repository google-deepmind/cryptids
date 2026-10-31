/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LF_0RC---_1RD0RA_1LE0RC_0LA0LE_1LE1LB` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LF_0RC---_1RD0RA_1LE0RC_0LA0LE_1LE1LB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LF_0RCHHH_1RD0RA_1LE0RC_0LA0LE_1LE1LB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LF_0RC---_1RD0RA_1LE0RC_0LA0LE_1LE1LB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => none
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 1, Stmt.write 1 Dir.left)

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

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

@[simp] lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] lemma pow_zero_list (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma pow_succ_list (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := ListBlank.cons_zero_default
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl
@[simp] lemma init_nil : (init ([] : List (Fin 2))) = (default {{A}}> default) := rfl

lemma str_app_assoc (xs ys : List (Fin 2)) (s : ListBlank (Fin 2)) :
    (xs ++ ys) +> s = xs +> (ys +> s) :=
  ListBlank.append_assoc xs ys s

lemma lpow_add {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n :=
  list_pow_add l m n

lemma lpow_shift {α : Type*} (l : List α) (n : Nat) : l ^ n ++ l = l ^ (n + 1) :=
  (list_pow_succ' l n).symm

lemma step_multiStep (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂ := by simp [h]

lemma step_stepStar (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢* c₂ := ⟨1, step_multiStep tm c₁ c₂ h⟩

lemma step_stepPlus (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ := ⟨1, by decide, step_multiStep tm c₁ c₂ h⟩

lemma multiStep_add (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]

lemma multiStep_trans (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rw [multiStep_add, h₁]; simp [h₂]

lemma stepStar_trans {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_stepStar {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

lemma stepPlus_stepStar_stepPlus {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepStar_stepPlus_stepPlus {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_trans {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus h₁ (stepPlus_stepStar h₂)

lemma step_stepStar_stepPlus {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂

macro "finish" : tactic =>
  `(tactic| (refine ⟨0, ?_⟩; simp only [init_nil, multiStep_zero, pow_zero_list, pow_succ_list, cons_append_list, append_nil_list, listblank_append_nil, listblank_append_cons, zero_cons_default]; rfl))
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by (try simp only [init_nil, pow_zero_list, pow_succ_list, cons_append_list, append_nil_list, listblank_append_nil, listblank_append_cons, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail]); rfl) ?_ <;>
    simp only [init_nil, pow_zero_list, pow_succ_list, cons_append_list, append_nil_list, listblank_append_nil, listblank_append_cons, Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default, default_head, default_tail])
macro "execute" : tactic =>
  `(tactic| (repeat' (first | finish | step)))

-- ============================================================================
-- Token and Processed-Token Encodings (`PR_SBC.v`)
-- ============================================================================

inductive tok where
  | T0 | T1 | TZ
  deriving DecidableEq, Repr

@[simp] def tokw : tok → List (Fin 2)
  | .T0 => [0, 0]
  | .T1 => [0, 1]
  | .TZ => [1, 0, 0]

@[simp] def tw : List tok → List (Fin 2)
  | [] => []
  | t :: ts => tokw t ++ tw ts

inductive ptok where
  | P | PZ
  deriving DecidableEq, Repr

@[simp] def pw : ptok → List (Fin 2)
  | .P => [0, 1]
  | .PZ => [0, 1, 0]

@[simp] def pl : List ptok → List (Fin 2)
  | [] => []
  | p :: ps => pw p ++ pl ps

@[simp] def proc : tok → ptok
  | .TZ => .PZ
  | _ => .P

@[simp] def rep {α : Type*} (x : α) : Nat → List α
  | 0 => []
  | n + 1 => x :: rep x n

@[simp] lemma rep_add_two {α : Type*} (x : α) (n : Nat) : rep x (n + 2) = x :: x :: rep x n := rfl

lemma rep_length {α : Type*} (x : α) (n : Nat) : (rep x n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep, ih]

lemma repeat_snoc {α : Type*} (x : α) (n : Nat) : rep x n ++ [x] = x :: rep x n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep, ih]

lemma tw_app (xs ys : List tok) : tw (xs ++ ys) = tw xs ++ tw ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [tw, ih, List.append_assoc]

lemma tw_cons (x : tok) (xs : List tok) : tw (x :: xs) = tokw x ++ tw xs := rfl

lemma pl_app (xs ys : List ptok) : pl (xs ++ ys) = pl xs ++ pl ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pl, ih, List.append_assoc]

-- ============================================================================
-- Elementary Finite-Step Rules (`es`)
-- ============================================================================

lemma AT0 (l r : ListBlank (Fin 2)) :
    (l {{A}}> (([0, 0] : List (Fin 2)) +> r)) [target_tm]⊢*
    ((([0, 1] : List (Fin 2)) +> l) {{C}}> r) := by execute

lemma AT0p (l r : ListBlank (Fin 2)) :
    (l {{A}}> (([0, 0] : List (Fin 2)) +> r)) [target_tm]⊢⁺
    ((([0, 1] : List (Fin 2)) +> l) {{C}}> r) := by execute

lemma CT1 (l r : ListBlank (Fin 2)) :
    (l {{C}}> (([0, 1] : List (Fin 2)) +> r)) [target_tm]⊢*
    ((([0, 1] : List (Fin 2)) +> l) {{C}}> r) := by execute

lemma CTZ (l r : ListBlank (Fin 2)) :
    (l {{C}}> (([1, 0, 0] : List (Fin 2)) +> r)) [target_tm]⊢*
    ((([0, 1, 0] : List (Fin 2)) +> l) {{C}}> r) := by execute

lemma CT0 (l r : ListBlank (Fin 2)) :
    (l {{C}}> (([0, 0] : List (Fin 2)) +> r)) [target_tm]⊢*
    (l <{{E}} (([0, 1] : List (Fin 2)) +> r)) := by execute

lemma EPZ (l r : ListBlank (Fin 2)) :
    ((([0, 1, 0] : List (Fin 2)) +> l) <{{E}} r) [target_tm]⊢*
    (l <{{E}} (([1, 0, 0] : List (Fin 2)) +> r)) := by execute

lemma EP (l r : ListBlank (Fin 2)) :
    ((([0, 1] : List (Fin 2)) +> l) <{{E}} r) [target_tm]⊢*
    (l <{{F}} (([0, 0] : List (Fin 2)) +> r)) := by execute

lemma FP (l r : ListBlank (Fin 2)) :
    ((([0, 1] : List (Fin 2)) +> l) <{{F}} r) [target_tm]⊢*
    (l <{{E}} (([0, 1] : List (Fin 2)) +> r)) := by execute

lemma FPZP (l r : ListBlank (Fin 2)) :
    ((([0, 1, 0] : List (Fin 2)) +> (([0, 1] : List (Fin 2)) +> l)) <{{F}} (([0, 0] : List (Fin 2)) +> r)) [target_tm]⊢*
    (l <{{E}} (([0, 0] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> (([0, 1] : List (Fin 2)) +> r)))) := by execute

lemma ENDl (l r : ListBlank (Fin 2)) :
    ((([0, 0] : List (Fin 2)) +> l) <{{F}} r) [target_tm]⊢*
    (l <{{A}} (([0, 1] : List (Fin 2)) +> r)) := by execute

lemma B1 (l r : ListBlank (Fin 2)) :
    ((([1, 0] : List (Fin 2)) +> l) <{{F}} r) [target_tm]⊢*
    ((([0, 0] : List (Fin 2)) +> l) {{A}}> r) := by execute

lemma BN (l r : ListBlank (Fin 2)) :
    ((([0, 1, 0, 0, 1, 0] : List (Fin 2)) +> l) <{{F}} (([0, 0] : List (Fin 2)) +> r)) [target_tm]⊢*
    (l <{{A}} (([0, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) +> r)) := by execute

lemma ENDZX (l r : ListBlank (Fin 2)) :
    ((([0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0] : List (Fin 2)) +> l) <{{F}} r) [target_tm]⊢*
    (l <{{A}} (([0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> r)) := by execute

lemma Bnc (X : ListBlank (Fin 2)) :
    (default <{{F}} (([0, 0] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> X))) [target_tm]⊢*
    (default {{A}}> (([0, 0] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> X)))) := by
  execute

-- ============================================================================
-- Sweeps & Return Transducer (`Csweep`, `retf`, `CTZs`, `EPZs`)
-- ============================================================================

@[simp] def noT0 : List tok → Prop
  | [] => True
  | .T0 :: _ => False
  | _ :: ts => noT0 ts

def prc (ts : List tok) : List ptok := (ts.map proc).reverse

lemma prc_app (xs ys : List tok) : prc (xs ++ ys) = prc ys ++ prc xs := by
  simp [prc, List.map_append, List.reverse_append]

lemma Csweep (ts : List tok) (h : noT0 ts) (l r : ListBlank (Fin 2)) :
    (l {{C}}> (tw ts +> r)) [target_tm]⊢* ((pl (prc ts) +> l) {{C}}> r) := by
  induction ts generalizing l with
  | nil => exact ⟨0, rfl⟩
  | cons t ts ih =>
    have hprc : pl (prc (t :: ts)) +> l = pl (prc ts) +> (pw (proc t) +> l) := by
      simp [prc, pl_app, str_app_assoc]
    rw [hprc]
    cases t with
    | T0 => exact False.elim h
    | T1 =>
      simp only [tw, tokw, str_app_assoc]
      exact stepStar_trans (CT1 l (tw ts +> r)) (ih h (([0, 1] : List (Fin 2)) +> l))
    | TZ =>
      simp only [tw, tokw, str_app_assoc]
      exact stepStar_trans (CTZ l (tw ts +> r)) (ih h (([0, 1, 0] : List (Fin 2)) +> l))

def retf (m : Fin 6) : List ptok → List tok → Fin 6 × List ptok × List tok
  | [], rs => (m, [], rs)
  | .PZ :: ps', rs =>
    if m = E then retf E ps' (.TZ :: rs)
    else if m = F then
      match ps' with
      | .P :: ps'' =>
        match rs with
        | .T0 :: rs' => retf E ps'' (.T0 :: .TZ :: .T1 :: rs')
        | _ => (m, .PZ :: ps', rs)
      | _ => (m, .PZ :: ps', rs)
    else (m, .PZ :: ps', rs)
  | .P :: ps', rs =>
    if m = E then retf F ps' (.T0 :: rs)
    else if m = F then retf E ps' (.T1 :: rs)
    else (m, .P :: ps', rs)

@[simp] lemma retf_E_P (ps : List ptok) (rs : List tok) :
    retf E (.P :: ps) rs = retf F ps (.T0 :: rs) := rfl

@[simp] lemma retf_F_P (ps : List ptok) (rs : List tok) :
    retf F (.P :: ps) rs = retf E ps (.T1 :: rs) := rfl

@[simp] lemma retf_E_PZ (ps : List ptok) (rs : List tok) :
    retf E (.PZ :: ps) rs = retf E ps (.TZ :: rs) := by
  cases ps with
  | nil => rfl
  | cons p ps' =>
    cases p <;> (try rfl) <;> cases rs <;> (try rfl) <;> rename_i r0 _ <;> cases r0 <;> rfl

@[simp] lemma retf_F_PZ_P (ps : List ptok) (rs : List tok) :
    retf F (.PZ :: .P :: ps) (.T0 :: rs) = retf E ps (.T0 :: .TZ :: .T1 :: rs) := rfl

lemma retf_spec_n : ∀ (n : Nat) (ps : List ptok), ps.length ≤ n →
    ∀ (m : Fin 6) (rs : List tok) (m' : Fin 6) (ps' : List ptok) (rs' : List tok),
    retf m ps rs = (m', ps', rs') →
    ∀ (l r : ListBlank (Fin 2)),
    ((pl ps +> l) <{{m}} (tw rs +> r)) [target_tm]⊢* ((pl ps' +> l) <{{m'}} (tw rs' +> r))
  | 0, ps, hn, m, rs, m', ps', rs', hr, l, r => by
    cases ps with
    | nil =>
      rcases hr with ⟨rfl, rfl, rfl⟩
      exact ⟨0, rfl⟩
    | cons _ _ => simp at hn
  | n + 1, [], _, m, rs, m', ps', rs', hr, l, r => by
    rcases hr with ⟨rfl, rfl, rfl⟩
    exact ⟨0, rfl⟩
  | n + 1, .P :: ps, hn, m, rs, m', ps', rs', hr, l, r => by
    by_cases hmE : m = E
    · subst hmE
      have hr' : retf F ps (.T0 :: rs) = (m', ps', rs') := hr
      have h1 : ((pl (.P :: ps) +> l) <{{E}} (tw rs +> r)) [target_tm]⊢*
          ((pl ps +> l) <{{F}} (tw (.T0 :: rs) +> r)) := by
        simpa [pl, pw, tw, tokw, str_app_assoc] using EP (pl ps +> l) (tw rs +> r)
      exact stepStar_trans h1 (retf_spec_n n ps (by simpa using hn) F (.T0 :: rs) m' ps' rs' hr' l r)
    · by_cases hmF : m = F
      · subst hmF
        have hr' : retf E ps (.T1 :: rs) = (m', ps', rs') := hr
        have h1 : ((pl (.P :: ps) +> l) <{{F}} (tw rs +> r)) [target_tm]⊢*
            ((pl ps +> l) <{{E}} (tw (.T1 :: rs) +> r)) := by
          simpa [pl, pw, tw, tokw, str_app_assoc] using FP (pl ps +> l) (tw rs +> r)
        exact stepStar_trans h1 (retf_spec_n n ps (by simpa using hn) E (.T1 :: rs) m' ps' rs' hr' l r)
      · unfold retf at hr
        simp only [hmE, hmF, ite_false] at hr
        rcases hr with ⟨rfl, rfl, rfl⟩
        exact ⟨0, rfl⟩
  | n + 1, .PZ :: ps, hn, m, rs, m', ps', rs', hr, l, r => by
    by_cases hmE : m = E
    · subst hmE
      have hr' : retf E ps (.TZ :: rs) = (m', ps', rs') := by unfold retf at hr; exact hr
      have h1 : ((pl (.PZ :: ps) +> l) <{{E}} (tw rs +> r)) [target_tm]⊢*
          ((pl ps +> l) <{{E}} (tw (.TZ :: rs) +> r)) := by
        simpa [pl, pw, tw, tokw, str_app_assoc] using EPZ (pl ps +> l) (tw rs +> r)
      exact stepStar_trans h1 (retf_spec_n n ps (by simpa using hn) E (.TZ :: rs) m' ps' rs' hr' l r)
    · by_cases hmF : m = F
      · subst hmF
        cases ps with
        | nil =>
          rcases hr with ⟨rfl, rfl, rfl⟩
          exact ⟨0, rfl⟩
        | cons p2 ps'' =>
          cases p2 with
          | PZ =>
            rcases hr with ⟨rfl, rfl, rfl⟩
            exact ⟨0, rfl⟩
          | P =>
            cases rs with
            | nil =>
              rcases hr with ⟨rfl, rfl, rfl⟩
              exact ⟨0, rfl⟩
            | cons r0 rs0 =>
              cases r0 with
              | T1 =>
                rcases hr with ⟨rfl, rfl, rfl⟩
                exact ⟨0, rfl⟩
              | TZ =>
                rcases hr with ⟨rfl, rfl, rfl⟩
                exact ⟨0, rfl⟩
              | T0 =>
                have hr' : retf E ps'' (.T0 :: .TZ :: .T1 :: rs0) = (m', ps', rs') := hr
                have h1 : ((pl (.PZ :: .P :: ps'') +> l) <{{F}} (tw (.T0 :: rs0) +> r)) [target_tm]⊢*
                    ((pl ps'' +> l) <{{E}} (tw (.T0 :: .TZ :: .T1 :: rs0) +> r)) := by
                  simpa [pl, pw, tw, tokw, str_app_assoc] using FPZP (pl ps'' +> l) (tw rs0 +> r)
                have hlen : ps''.length ≤ n := by simp at hn; omega
                exact stepStar_trans h1 (retf_spec_n n ps'' hlen E (.T0 :: .TZ :: .T1 :: rs0) m' ps' rs' hr' l r)
      · unfold retf at hr
        simp only [hmE, hmF, ite_false] at hr
        rcases hr with ⟨rfl, rfl, rfl⟩
        exact ⟨0, rfl⟩

lemma retf_spec (ps : List ptok) (m : Fin 6) (rs : List tok) (m' : Fin 6) (ps' : List ptok) (rs' : List tok)
    (hr : retf m ps rs = (m', ps', rs')) (l r : ListBlank (Fin 2)) :
    ((pl ps +> l) <{{m}} (tw rs +> r)) [target_tm]⊢* ((pl ps' +> l) <{{m'}} (tw rs' +> r)) :=
  retf_spec_n ps.length ps (Nat.le_refl _) m rs m' ps' rs' hr l r

lemma CTZs (g : Nat) (l r : ListBlank (Fin 2)) :
    (l {{C}}> ((([1, 0, 0] : List (Fin 2)) ^ g) +> r)) [target_tm]⊢*
    ((((([0, 1, 0] : List (Fin 2)) ^ g) +> l)) {{C}}> r) := by
  induction g generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ g ih =>
    rw [pow_succ_list, str_app_assoc]
    have h1 := CTZ l ((([1, 0, 0] : List (Fin 2)) ^ g) +> r)
    have h2 := ih (([0, 1, 0] : List (Fin 2)) +> l)
    have hrew : (([0, 1, 0] : List (Fin 2)) ^ g) +> (([0, 1, 0] : List (Fin 2)) +> l) =
        (([0, 1, 0] : List (Fin 2)) ^ (g + 1)) +> l := by
      rw [← str_app_assoc, lpow_shift]
    rw [hrew] at h2
    exact stepStar_trans h1 h2

lemma EPZs (g : Nat) (l r : ListBlank (Fin 2)) :
    ((((([0, 1, 0] : List (Fin 2)) ^ g) +> l)) <{{E}} r) [target_tm]⊢*
    (l <{{E}} ((([1, 0, 0] : List (Fin 2)) ^ g) +> r)) := by
  induction g generalizing r with
  | zero => exact ⟨0, rfl⟩
  | succ g ih =>
    rw [pow_succ_list, str_app_assoc]
    have h1 := EPZ ((([0, 1, 0] : List (Fin 2)) ^ g) +> l) r
    have h2 := ih (([1, 0, 0] : List (Fin 2)) +> r)
    have hrew : (([1, 0, 0] : List (Fin 2)) ^ g) +> (([1, 0, 0] : List (Fin 2)) +> r) =
        (([1, 0, 0] : List (Fin 2)) ^ (g + 1)) +> r := by
      rw [← str_app_assoc, lpow_shift]
    rw [hrew] at h2
    exact stepStar_trans h1 h2

lemma tw_Z (g : Nat) : tw (rep .TZ g) = ([1, 0, 0] : List (Fin 2)) ^ g := by
  induction g with
  | zero => rfl
  | succ g ih => simp [rep, tw, tokw, ih]

lemma tw_T0_cons' (xs : List tok) (r : ListBlank (Fin 2)) :
    tw (.T0 :: xs) +> r = ([0, 0] : List (Fin 2)) +> (tw xs +> r) := by
  rw [tw_cons, str_app_assoc]; rfl

lemma tw_T1_cons' (xs : List tok) (r : ListBlank (Fin 2)) :
    tw (.T1 :: xs) +> r = ([0, 1] : List (Fin 2)) +> (tw xs +> r) := by
  rw [tw_cons, str_app_assoc]; rfl

lemma tw_TZ_cons' (xs : List tok) (r : ListBlank (Fin 2)) :
    tw (.TZ :: xs) +> r = ([1, 0, 0] : List (Fin 2)) +> (tw xs +> r) := by
  rw [tw_cons, str_app_assoc]; rfl

lemma tw_rep_TZ_app (g : Nat) (xs : List tok) (r : ListBlank (Fin 2)) :
    tw (rep .TZ g ++ xs) +> r = ((([1, 0, 0] : List (Fin 2)) ^ g) +> (tw xs +> r)) := by
  rw [tw_app, tw_Z, str_app_assoc]

def bit (v : Nat) : tok := if v % 2 = 1 then .T1 else .T0

def ctr : List Nat → Nat → List tok
  | [], v => [bit v]
  | g :: gs', v => bit v :: .TZ :: .T1 :: (rep .TZ g ++ ctr gs' (v / 2))

lemma bit_even (w : Nat) : bit (2 * w) = .T0 := by
  unfold bit
  have : (2 * w) % 2 = 0 := by omega
  simp [this]

lemma bit_odd (w : Nat) : bit (2 * w + 1) = .T1 := by
  unfold bit
  have : (2 * w + 1) % 2 = 1 := by omega
  simp [this]

lemma ctr_even (g : Nat) (gs : List Nat) (w : Nat) :
    ctr (g :: gs) (2 * w) = .T0 :: .TZ :: .T1 :: (rep .TZ g ++ ctr gs w) := by
  have hd : (2 * w) / 2 = w := by omega
  simp [ctr, bit_even, hd]

lemma ctr_odd (g : Nat) (gs : List Nat) (w : Nat) :
    ctr (g :: gs) (2 * w + 1) = .T1 :: .TZ :: .T1 :: (rep .TZ g ++ ctr gs w) := by
  have hd : (2 * w + 1) / 2 = w := by omega
  simp [ctr, bit_odd, hd]

lemma ctr_hd_even (gs : List Nat) (w : Nat) :
    ∃ rest, ctr gs (2 * w) = .T0 :: rest ∧ ctr gs (2 * w + 1) = .T1 :: rest := by
  cases gs with
  | nil => exact ⟨[], by simp [ctr, bit_even], by simp [ctr, bit_odd]⟩
  | cons g gs' => exact ⟨.TZ :: .T1 :: (rep .TZ g ++ ctr gs' w), ctr_even g gs' w, ctr_odd g gs' w⟩

lemma pow2S (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by ring

lemma IncC (gs : List Nat) : ∀ (v : Nat), v + 1 < 2 ^ (gs.length + 1) →
    ∀ (l r : ListBlank (Fin 2)) (t : List tok),
    (l {{C}}> (tw (ctr gs v ++ t) +> r)) [target_tm]⊢*
    (l <{{E}} (tw (ctr gs (v + 1) ++ t) +> r)) := by
  induction gs with
  | nil =>
    intro v hv l r t
    rcases BusyBeaver.nat_even_or_odd_two_mul v with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · simp only [ctr, bit_even, bit_odd, List.singleton_append, tw, tokw, str_app_assoc]
      exact CT0 l (tw t +> r)
    · simp at hv
  | cons g gs ih =>
    intro v hv l r t
    rcases BusyBeaver.nat_even_or_odd_two_mul v with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rcases ctr_hd_even (g :: gs) w with ⟨rest, h0, h1⟩
      rw [h0, h1]
      simp only [List.cons_append, tw, tokw, str_app_assoc]
      exact CT0 l (tw (rest ++ t) +> r)
    · have hsucc : 2 * w + 1 + 1 = 2 * (w + 1) := by omega
      rw [ctr_odd, hsucc, ctr_even]
      have hvw : w + 1 < 2 ^ (gs.length + 1) := by
        simp only [List.length_cons] at hv
        rw [pow2S (gs.length + 1)] at hv
        omega
      simp only [List.cons_append, List.append_assoc, tw_T0_cons', tw_T1_cons', tw_TZ_cons', tw_rep_TZ_app]
      have s1 := CT1 l (([1, 0, 0] : List (Fin 2)) +> (([0, 1] : List (Fin 2)) +> ((([1, 0, 0] : List (Fin 2)) ^ g) +> (tw (ctr gs w ++ t) +> r))))
      have s2 := CTZ (([0, 1] : List (Fin 2)) +> l) (([0, 1] : List (Fin 2)) +> ((([1, 0, 0] : List (Fin 2)) ^ g) +> (tw (ctr gs w ++ t) +> r)))
      have s3 := CT1 (([0, 1, 0] : List (Fin 2)) +> (([0, 1] : List (Fin 2)) +> l)) ((([1, 0, 0] : List (Fin 2)) ^ g) +> (tw (ctr gs w ++ t) +> r))
      have s4 := CTZs g (([0, 1] : List (Fin 2)) +> (([0, 1, 0] : List (Fin 2)) +> (([0, 1] : List (Fin 2)) +> l))) (tw (ctr gs w ++ t) +> r)
      have s5 := ih w hvw ((([0, 1, 0] : List (Fin 2)) ^ g) +> (([0, 1] : List (Fin 2)) +> (([0, 1, 0] : List (Fin 2)) +> (([0, 1] : List (Fin 2)) +> l)))) r t
      have s6 := EPZs g (([0, 1] : List (Fin 2)) +> (([0, 1, 0] : List (Fin 2)) +> (([0, 1] : List (Fin 2)) +> l))) (tw (ctr gs (w + 1) ++ t) +> r)
      have s7 := EP (([0, 1, 0] : List (Fin 2)) +> (([0, 1] : List (Fin 2)) +> l)) ((([1, 0, 0] : List (Fin 2)) ^ g) +> (tw (ctr gs (w + 1) ++ t) +> r))
      have s8 := FPZP l ((([1, 0, 0] : List (Fin 2)) ^ g) +> (tw (ctr gs (w + 1) ++ t) +> r))
      exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4 (stepStar_trans s5 (stepStar_trans s6 (stepStar_trans s7 s8))))))

lemma IncL (gs : List Nat) (v a : Nat) (hv : v + 1 < 2 ^ (gs.length + 1))
    (l r : ListBlank (Fin 2)) (t : List tok) :
    (l {{A}}> (tw (.T0 :: (rep .TZ a ++ (ctr gs v ++ t))) +> r)) [target_tm]⊢*
    (l <{{F}} (tw (.T0 :: (rep .TZ a ++ (ctr gs (v + 1) ++ t))) +> r)) := by
  simp only [tw_T0_cons', tw_rep_TZ_app]
  have s1 := AT0 l ((([1, 0, 0] : List (Fin 2)) ^ a) +> (tw (ctr gs v ++ t) +> r))
  have s2 := CTZs a (([0, 1] : List (Fin 2)) +> l) (tw (ctr gs v ++ t) +> r)
  have s3 := IncC gs v hv ((([0, 1, 0] : List (Fin 2)) ^ a) +> (([0, 1] : List (Fin 2)) +> l)) r t
  have s4 := EPZs a (([0, 1] : List (Fin 2)) +> l) (tw (ctr gs (v + 1) ++ t) +> r)
  have s5 := EP l ((([1, 0, 0] : List (Fin 2)) ^ a) +> (tw (ctr gs (v + 1) ++ t) +> r))
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 (stepStar_trans s4 s5)))

lemma TwoInc (gs : List Nat) (v p : Nat) (t : List tok) (L r : ListBlank (Fin 2))
    (hv : v + 2 < 2 ^ (gs.length + 1)) :
    ((([1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L)) {{A}}> (tw (.T0 :: (rep .TZ p ++ (ctr gs v ++ t))) +> r)) [target_tm]⊢*
    (L {{A}}> (tw (.T0 :: (rep .TZ (p + 1) ++ (ctr gs (v + 2) ++ t))) +> r)) := by
  have s1 := IncL gs v p (by omega) (([1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L)) r t
  have s2 := B1 (([0] : List (Fin 2)) +> L) (tw (.T0 :: (rep .TZ p ++ (ctr gs (v + 1) ++ t))) +> r)
  have s3 := IncL gs (v + 1) p hv (([0, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L)) r t
  have s4 := ENDl (([0] : List (Fin 2)) +> L) (tw (.T0 :: (rep .TZ p ++ (ctr gs (v + 2) ++ t))) +> r)
  have h_rhs : ((([0] : List (Fin 2)) +> L) <{{A}} (([0, 1] : List (Fin 2)) +> (tw (.T0 :: (rep .TZ p ++ (ctr gs (v + 2) ++ t))) +> r))) =
      (L {{A}}> (tw (.T0 :: (rep .TZ (p + 1) ++ (ctr gs (v + 2) ++ t))) +> r)) := by
    simp [rep, tw, tokw, str_app_assoc]
  rw [h_rhs] at s4
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 s4))

lemma ZXg (gs : List Nat) (v p : Nat) (t : List tok) (L r : ListBlank (Fin 2))
    (hv : v + 2 < 2 ^ (gs.length + 1)) :
    ((([1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L)) {{A}}>
      (tw (.T0 :: (rep .TZ p ++ (ctr gs v ++ t))) +> r)) [target_tm]⊢*
    (L {{A}}> (tw (.T0 :: (ctr ((p + 2) :: gs) (2 * (v + 2)) ++ t)) +> r)) := by
  have hsplit : (([1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L)) =
      (([1, 0] : List (Fin 2)) +> (([1, 0, 0, 1, 0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L))) := by simp
  rw [hsplit]
  have s1 := IncL gs v p (by omega) (([1, 0] : List (Fin 2)) +> (([1, 0, 0, 1, 0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L))) r t
  have s2 := B1 (([1, 0, 0, 1, 0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L)) (tw (.T0 :: (rep .TZ p ++ (ctr gs (v + 1) ++ t))) +> r)
  have s3 := IncL gs (v + 1) p hv (([0, 0] : List (Fin 2)) +> (([1, 0, 0, 1, 0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L))) r t
  have hmerge : (([0, 0] : List (Fin 2)) +> (([1, 0, 0, 1, 0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L))) =
      (([0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L)) := by simp
  rw [hmerge] at s3
  have s4 := ENDZX (([0] : List (Fin 2)) +> L) (tw (.T0 :: (rep .TZ p ++ (ctr gs (v + 2) ++ t))) +> r)
  have h_rhs : ((([0] : List (Fin 2)) +> L) <{{A}} (([0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1] : List (Fin 2)) +> (tw (.T0 :: (rep .TZ p ++ (ctr gs (v + 2) ++ t))) +> r))) =
      (L {{A}}> (tw (.T0 :: (ctr ((p + 2) :: gs) (2 * (v + 2)) ++ t)) +> r)) := by
    rw [ctr_even]
    simp [rep, tw, tokw, tw_app, tw_Z, str_app_assoc]
  rw [h_rhs] at s4
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 s4))

lemma ZXP2g (gs : List Nat) (v p : Nat) (t : List tok) (L r : ListBlank (Fin 2))
    (hv : v + 1 < 2 ^ (gs.length + 1)) :
    ((([0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L)) {{A}}>
      (tw (.T0 :: (rep .TZ p ++ (ctr gs v ++ t))) +> r)) [target_tm]⊢*
    (L {{A}}> (tw (.T0 :: (ctr (p :: gs) (2 * (v + 1)) ++ t)) +> r)) := by
  have s1 := IncL gs v p hv (([0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> L)) r t
  rw [tw_T0_cons'] at s1
  have s2 := BN (([0] : List (Fin 2)) +> L) (tw (rep .TZ p ++ (ctr gs (v + 1) ++ t)) +> r)
  have h_rhs : ((([0] : List (Fin 2)) +> L) <{{A}} (([0, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) +> (tw (rep .TZ p ++ (ctr gs (v + 1) ++ t)) +> r))) =
      (L {{A}}> (tw (.T0 :: (ctr (p :: gs) (2 * (v + 1)) ++ t)) +> r)) := by
    rw [ctr_even]
    simp [tw, tokw, tw_app, tw_Z, str_app_assoc]
  rw [h_rhs] at s2
  exact stepStar_trans s1 s2

-- ============================================================================
-- Right-Tail Grammar (`tailx`, `tailw`, `Lst`, `Tail10`, `Tail0z`, `Tail11`)
-- ============================================================================

@[simp] def bt (b : Bool) : tok := if b then .T1 else .T0

def tailx (y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) (e : List Bool) : List tok :=
  bt y :: bt z :: .TZ :: .T1 :: bt b4 :: bt b5 :: .TZ :: .T1 :: bt b6 :: .TZ :: bt b7 :: .TZ :: .T1 ::
  bt b8 :: bt b9 :: .TZ :: bt b10 :: .TZ :: .T1 :: bt b11 :: .TZ :: bt b12 :: .TZ :: bt b13 :: .TZ ::
  bt b14 :: .TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1])

def tailw (x y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) (e : List Bool) : List tok :=
  bt x :: tailx y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e

def Lst (y z : Bool) (S : ListBlank (Fin 2)) : Prop :=
  ∃ b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e,
    S = tw (tailw true y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default

lemma tw_T0_cons (xs : List tok) (r : ListBlank (Fin 2)) :
    tw (.T0 :: xs) +> r = ([0, 0] : List (Fin 2)) +> (tw xs +> r) := by
  rw [tw_cons, str_app_assoc]; rfl

lemma tw_T1_cons (xs : List tok) (r : ListBlank (Fin 2)) :
    ([0, 1] : List (Fin 2)) +> (tw xs +> r) = tw (.T1 :: xs) +> r := by
  rw [tw_cons, str_app_assoc]; rfl

lemma TailRet (pre rest : List tok) (m : Fin 6) (out : List tok)
    (hn : noT0 pre) (hr : retf E (prc pre) [.T1] = (m, [], out))
    (l R : ListBlank (Fin 2)) :
    (l {{C}}> (tw (pre ++ (.T0 :: rest)) +> R)) [target_tm]⊢*
    (l <{{m}} (tw (out ++ rest) +> R)) := by
  rw [tw_app, str_app_assoc, tw_T0_cons']
  have s1 := Csweep pre hn l (([0, 0] : List (Fin 2)) +> (tw rest +> R))
  have s2 := CT0 (pl (prc pre) +> l) (tw rest +> R)
  have s3 := retf_spec (prc pre) E [.T1] m [] out hr l (tw rest +> R)
  rw [← tw_T1_cons'] at s2
  have s123 := stepStar_trans s1 (stepStar_trans s2 s3)
  simp only [pl, listblank_append_nil] at s123
  rw [tw_app, str_app_assoc]
  exact s123

lemma TailRet' (w pre rest : List tok) (m : Fin 6) (out w' : List tok)
    (hw : w = pre ++ (.T0 :: rest))
    (hn : noT0 pre) (hr : retf E (prc pre) [.T1] = (m, [], out))
    (hw' : out ++ rest = w')
    (l R : ListBlank (Fin 2)) :
    (l {{C}}> (tw w +> R)) [target_tm]⊢*
    (l <{{m}} (tw w' +> R)) := by
  subst hw; subst hw'
  exact TailRet pre rest m out hn hr l R

lemma TailRetF' (w pre rest : List tok) (out w' : List tok)
    (hw : w = pre ++ (.T0 :: rest))
    (hn : noT0 pre) (hr : retf E (prc pre) [.T1] = (F, [], .T0 :: out))
    (hw' : out ++ rest = w')
    (l R : ListBlank (Fin 2)) :
    (l {{C}}> (tw w +> R)) [target_tm]⊢*
    (l <{{F}} (([0, 0] : List (Fin 2)) +> (tw w' +> R))) := by
  subst hw; subst hw'
  have h := TailRet pre rest F (.T0 :: out) hn hr l R
  have hcons : (.T0 :: out) ++ rest = .T0 :: (out ++ rest) := rfl
  rw [hcons, tw_T0_cons] at h
  exact h

lemma Tail10 (l : ListBlank (Fin 2)) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) (e : List Bool) :
    (l {{C}}> (tw (tailw true true false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default)) [target_tm]⊢*
    (l <{{E}} (tw (tailw true false true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default)) :=
  TailRet' _ [.T1, .T1] ((tailx true true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e).tail.tail)
    E [.T1, .T0, .T1] _ rfl trivial rfl rfl l default

lemma Tail0z (l : ListBlank (Fin 2)) (z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) (e : List Bool) :
    (l {{C}}> (tw (tailw true false z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default)) [target_tm]⊢*
    (l <{{F}} (([0, 0] : List (Fin 2)) +> (tw (tailx true z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default))) :=
  TailRetF' _ [.T1] ((tailx true z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e).tail)
    [.T1] _ rfl trivial rfl rfl l default

@[irreducible] def F1 : List tok :=
  [.T1, .T1, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1, .T1,
   .TZ, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1, .TZ, .T1, .TZ, .T1, .TZ, .T1]

@[irreducible] def F1E : List tok :=
  [.T1, .T0, .T0, .TZ, .T1, .T1, .T0, .TZ, .T1, .T0, .TZ, .T0, .TZ, .T1, .T1, .T0,
   .TZ, .T0, .TZ, .T1, .T0, .TZ, .T1, .TZ, .T0, .TZ, .T1, .TZ, .T0, .TZ, .T1]

@[irreducible] def F1F_tail : List tok :=
  [.T1, .T0, .TZ, .T1, .T0, .T0, .TZ, .T1, .T0, .TZ, .T1, .TZ, .T1, .T0, .T0,
   .TZ, .T1, .TZ, .T1, .T0, .TZ, .T0, .TZ, .T1, .TZ, .T0, .TZ, .T1, .TZ, .T1]

lemma noT0_F1 : noT0 F1 := by unfold F1; trivial
lemma F1E_ret (X : List tok) : retf E (prc F1) X = (E, [], F1E ++ X) := by unfold F1 F1E; rfl
lemma F1F_ret (X : List tok) : retf F (prc F1) X = (F, [], .T0 :: (F1F_tail ++ X)) := by unfold F1 F1F_tail; rfl

lemma tailw_ones (e : List Bool) :
    tailw true true true true true true true true true true true true true true true e =
    F1 ++ (e.map bt ++ [.T1]) := by unfold F1; rfl

lemma tailw_F1E (X : List Bool) :
    tailw true false false true false false false true false false false true false true false X =
    F1E ++ (X.map bt ++ [.T1]) := by unfold F1E; rfl

lemma tailw_F1F (X : List Bool) :
    tailw true true false false false false true false false true false false true false true (false :: X) =
    .T1 :: (F1F_tail ++ (.T0 :: (X.map bt ++ [.T1]))) := by unfold F1F_tail; rfl


lemma prc_T1s (j : Nat) : prc (rep .T1 j) = rep .P j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hcons : prc (.T1 :: rep .T1 j) = prc (rep .T1 j) ++ [.P] := by
      simp only [prc, List.map_cons, proc, List.reverse_cons]
    rw [rep, hcons, ih, repeat_snoc]; rfl

lemma noT0_app (xs ys : List tok) (hx : noT0 xs) (hy : noT0 ys) : noT0 (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons x xs ih =>
    cases x with
    | T0 => exact False.elim hx
    | T1 => exact ih hx
    | TZ => exact ih hx

lemma noT0_T1s (j : Nat) : noT0 (rep .T1 j) := by
  induction j with
  | zero => trivial
  | succ j ih => exact ih

lemma noT0_F1_T1s (j : Nat) : noT0 (F1 ++ rep .T1 j) :=
  noT0_app F1 (rep .T1 j) noT0_F1 (noT0_T1s j)

lemma map_bt_true (j : Nat) : (rep true j).map bt = rep .T1 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [rep, List.map_cons, ih]
    rfl

lemma map_bt_alt (i : Nat) : (([true, false] : List Bool) ^ i).map bt = ([tok.T1, tok.T0] : List tok) ^ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [list_pow_succ, list_pow_succ, List.map_append, ih]
    rfl

lemma retf_PP (i : Nat) (ps : List ptok) (rs : List tok) :
    retf E (rep .P (2 * i) ++ ps) rs = retf E ps ((([tok.T1, tok.T0] : List tok) ^ i) ++ rs) := by
  induction i generalizing rs with
  | zero => rfl
  | succ i ih =>
    have h2 : 2 * (i + 1) = (2 * i) + 1 + 1 := by omega
    rw [h2, rep, rep, List.cons_append, List.cons_append, retf_E_P, retf_F_P]
    rw [ih (.T1 :: .T0 :: rs)]
    have hshift : (([tok.T1, tok.T0] : List tok) ^ i) ++ (.T1 :: .T0 :: rs) =
        (([tok.T1, tok.T0] : List tok) ^ (i + 1)) ++ rs := by
      change (([tok.T1, tok.T0] : List tok) ^ i) ++ ([tok.T1, tok.T0] ++ rs) = _
      rw [← List.append_assoc, lpow_shift]
    rw [hshift]

lemma retf_PPP (i : Nat) (ps : List ptok) (rs : List tok) :
    retf E (rep .P (2 * i + 1) ++ ps) rs = retf F ps (.T0 :: ((([tok.T1, tok.T0] : List tok) ^ i) ++ rs)) := by
  have hrep : rep ptok.P (2 * i + 1) ++ ps = rep ptok.P (2 * i) ++ (.P :: ps) := by
    rw [rep, ← repeat_snoc, List.append_assoc]; rfl
  rw [hrep, retf_PP, retf_E_P]

lemma e_split (e : List Bool) :
    (∃ j e', e = rep true j ++ (false :: e')) ∨ (∃ m, e = rep true m) := by
  induction e with
  | nil => exact Or.inr ⟨0, rfl⟩
  | cons b e ih =>
    cases b with
    | false => exact Or.inl ⟨0, e, rfl⟩
    | true =>
      rcases ih with ⟨j, e', rfl⟩ | ⟨m, rfl⟩
      · exact Or.inl ⟨j + 1, e', rfl⟩
      · exact Or.inr ⟨m + 1, rfl⟩

@[simp] lemma bt_true : bt true = .T1 := rfl
@[simp] lemma bt_false : bt false = .T0 := rfl

lemma tw_T1_end (xs : List tok) :
    tw (xs ++ [.T1]) +> (default : ListBlank (Fin 2)) =
    tw (xs ++ [.T1, .T0]) +> default := by
  rw [tw_app, tw_app, str_app_assoc, str_app_assoc]
  apply congrArg (fun r => tw xs +> r)
  simp only [tw, tokw, List.cons_append, List.nil_append, listblank_append_cons, listblank_append_nil, zero_cons_default]

lemma tw_T1_cons_eq (xs ys : List tok) (r : ListBlank (Fin 2)) (h : .T1 :: xs = ys) :
    ([0, 1] : List (Fin 2)) +> (tw xs +> r) = tw ys +> r := by
  subst h; exact tw_T1_cons xs r

lemma TailRet_eq (w1 w2 : List tok) (m : Fin 6) (S' : ListBlank (Fin 2)) (l : ListBlank (Fin 2))
    (hw : tw w1 +> default = tw w2 +> default)
    (hstep : (l {{C}}> (tw w2 +> default)) [target_tm]⊢* (l <{{m}} S')) :
    (l {{C}}> (tw w1 +> default)) [target_tm]⊢* (l <{{m}} S') := by
  rw [hw]; exact hstep

lemma list_hs1_aux (xs : List tok) (j : Nat) (e' : List Bool) :
    xs ++ ((rep true j ++ (false :: e')).map bt ++ [.T1]) =
    (xs ++ rep .T1 j) ++ (.T0 :: (e'.map bt ++ [.T1])) := by
  simp only [List.map_append, map_bt_true, List.map_cons, bt_false, List.cons_append, List.nil_append, List.append_assoc]

lemma Tail11_end_hs1 (j : Nat) (e' : List Bool) :
    tailw true true true true true true true true true true true true true true true (rep true j ++ (false :: e')) =
    (F1 ++ rep .T1 j) ++ (.T0 :: (e'.map bt ++ [.T1])) :=
  (tailw_ones _).trans (list_hs1_aux F1 j e')

lemma Tail11_end_ret_even (i : Nat) :
    retf E (prc (F1 ++ rep .T1 (2 * i))) [.T1] =
    (E, [], F1E ++ ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1])) := by
  rw [prc_app, prc_T1s, retf_PP, F1E_ret]

lemma Tail11_end_ret_odd (i : Nat) :
    retf E (prc (F1 ++ rep .T1 (2 * i + 1))) [.T1] =
    (F, [], .T0 :: (F1F_tail ++ (.T0 :: ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1])))) := by
  rw [prc_app, prc_T1s, retf_PPP, F1F_ret]

lemma list_lst_even1_aux (xs : List tok) (i : Nat) (e' : List Bool) :
    (xs ++ ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1])) ++ (e'.map bt ++ [.T1]) =
    xs ++ (((([true, false] : List Bool) ^ i) ++ (true :: e')).map bt ++ [.T1]) := by
  simp only [List.map_append, map_bt_alt, List.map_cons, bt_true, List.cons_append, List.nil_append, List.append_assoc]

lemma Tail11_end_lst_even1 (i : Nat) (e' : List Bool) :
    (F1E ++ ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1])) ++ (e'.map bt ++ [.T1]) =
    tailw true false false true false false false true false false false true false true false ((([true, false] : List Bool) ^ i) ++ (true :: e')) :=
  (list_lst_even1_aux F1E i e').trans (tailw_F1E _).symm

lemma list_lst_odd1_aux (xs : List tok) (i : Nat) (e' : List Bool) :
    .T1 :: ((xs ++ (.T0 :: ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1]))) ++ (e'.map bt ++ [.T1])) =
    .T1 :: (xs ++ (.T0 :: (((([true, false] : List Bool) ^ i) ++ (true :: e')).map bt ++ [.T1]))) := by
  simp only [List.map_append, map_bt_alt, List.map_cons, bt_true, List.cons_append, List.nil_append, List.append_assoc]

lemma Tail11_end_lst_odd1 (i : Nat) (e' : List Bool) :
    .T1 :: ((F1F_tail ++ (.T0 :: ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1]))) ++ (e'.map bt ++ [.T1])) =
    tailw true true false false false false true false false true false false true false true (false :: ((([true, false] : List Bool) ^ i) ++ (true :: e'))) :=
  (list_lst_odd1_aux F1F_tail i e').trans (tailw_F1F _).symm

lemma rep_snoc {α : Type*} (x : α) (n : Nat) : rep x (n + 1) = rep x n ++ [x] :=
  (repeat_snoc x n).symm

lemma list_hs2_aux1 (xs : List tok) (m : Nat) :
    xs ++ ((rep true m).map bt ++ [.T1]) = (xs ++ rep .T1 m) ++ [.T1] := by
  rw [map_bt_true, List.append_assoc]

lemma list_hs2_aux2 (xs : List tok) (m : Nat) :
    (xs ++ rep .T1 m) ++ [.T1, .T0] = (xs ++ rep .T1 (m + 1)) ++ [.T0] := by
  rw [rep_snoc]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

lemma Tail11_end_hs2 (m k : Nat) (hk : m + 1 = k) :
    tw (tailw true true true true true true true true true true true true true true true (rep true m)) +> (default : ListBlank (Fin 2)) =
    tw ((F1 ++ rep .T1 k) ++ [.T0]) +> default := by
  subst hk
  rw [tailw_ones, list_hs2_aux1, tw_T1_end, list_hs2_aux2]

lemma Tail11_end_lst_even2 (i : Nat) :
    (F1E ++ ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1])) ++ [] =
    tailw true false false true false false false true false false false true false true false (([true, false] : List Bool) ^ i) := by
  rw [tailw_F1E, map_bt_alt, List.append_nil]

lemma Tail11_end_lst_odd2 (i : Nat) :
    .T1 :: ((F1F_tail ++ (.T0 :: ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1]))) ++ []) =
    tailw true true false false false false true false false true false false true false true (false :: (([true, false] : List Bool) ^ i)) := by
  rw [tailw_F1F, map_bt_alt, List.append_nil]

lemma Lst_intro (y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) (e : List Bool)
    (S : ListBlank (Fin 2))
    (h : S = tw (tailw true y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default) :
    Lst y z S :=
  ⟨b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, e, h⟩

lemma Tail11_inl (w pre rest out : List tok)
    (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) (e : List Bool)
    (hw : w = pre ++ (.T0 :: rest))
    (hn : noT0 pre)
    (hr : retf E (prc pre) [.T1] = (E, [], out))
    (hw' : out ++ rest = tailw true false false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) :
    (∃ S', (∀ l, (l {{C}}> (tw w +> default)) [target_tm]⊢* (l <{{E}} S')) ∧ Lst false false S') ∨
    (∃ S', (∀ l, (l {{C}}> (tw w +> default)) [target_tm]⊢* (l <{{F}} (([0, 0] : List (Fin 2)) +> S'))) ∧ Lst true false (([0, 1] : List (Fin 2)) +> S')) :=
  Or.inl ⟨tw (tailw true false false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default,
    fun l => TailRet' w pre rest E out _ hw hn hr hw' l default,
    Lst_intro false false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e _ rfl⟩

lemma Tail11_inr (w pre rest out : List tok)
    (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) (e : List Bool)
    (hw : w = pre ++ (.T0 :: rest))
    (hn : noT0 pre)
    (hr : retf E (prc pre) [.T1] = (F, [], .T0 :: out))
    (hw' : .T1 :: (out ++ rest) = tailw true true false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) :
    (∃ S', (∀ l, (l {{C}}> (tw w +> default)) [target_tm]⊢* (l <{{E}} S')) ∧ Lst false false S') ∨
    (∃ S', (∀ l, (l {{C}}> (tw w +> default)) [target_tm]⊢* (l <{{F}} (([0, 0] : List (Fin 2)) +> S'))) ∧ Lst true false (([0, 1] : List (Fin 2)) +> S')) :=
  Or.inr ⟨tw (out ++ rest) +> default,
    fun l => TailRetF' w pre rest out (out ++ rest) hw hn hr rfl l default,
    Lst_intro true false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e _ (tw_T1_cons_eq (out ++ rest) _ default hw')⟩

lemma Tail11_inl_eq (w pre rest out : List tok)
    (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) (e : List Bool)
    (hw : tw w +> default = tw (pre ++ (.T0 :: rest)) +> default)
    (hn : noT0 pre)
    (hr : retf E (prc pre) [.T1] = (E, [], out))
    (hw' : out ++ rest = tailw true false false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) :
    (∃ S', (∀ l, (l {{C}}> (tw w +> default)) [target_tm]⊢* (l <{{E}} S')) ∧ Lst false false S') ∨
    (∃ S', (∀ l, (l {{C}}> (tw w +> default)) [target_tm]⊢* (l <{{F}} (([0, 0] : List (Fin 2)) +> S'))) ∧ Lst true false (([0, 1] : List (Fin 2)) +> S')) :=
  Or.inl ⟨tw (tailw true false false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default,
    fun l => TailRet_eq w (pre ++ (.T0 :: rest)) E _ l hw (TailRet' _ pre rest E out _ rfl hn hr hw' l default),
    Lst_intro false false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e _ rfl⟩

lemma Tail11_inr_eq (w pre rest out : List tok)
    (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) (e : List Bool)
    (hw : tw w +> default = tw (pre ++ (.T0 :: rest)) +> default)
    (hn : noT0 pre)
    (hr : retf E (prc pre) [.T1] = (F, [], .T0 :: out))
    (hw' : .T1 :: (out ++ rest) = tailw true true false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) :
    (∃ S', (∀ l, (l {{C}}> (tw w +> default)) [target_tm]⊢* (l <{{E}} S')) ∧ Lst false false S') ∨
    (∃ S', (∀ l, (l {{C}}> (tw w +> default)) [target_tm]⊢* (l <{{F}} (([0, 0] : List (Fin 2)) +> S'))) ∧ Lst true false (([0, 1] : List (Fin 2)) +> S')) :=
  Or.inr ⟨tw (out ++ rest) +> default,
    fun l => TailRet_eq w (pre ++ (.T0 :: rest)) F _ l hw (TailRetF' _ pre rest out (out ++ rest) rfl hn hr rfl l default),
    Lst_intro true false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e _ (tw_T1_cons_eq (out ++ rest) _ default hw')⟩

lemma Tail11_end (e : List Bool) :
    (∃ S', (∀ l, (l {{C}}> (tw (tailw true true true true true true true true true true true true true true true e) +> default)) [target_tm]⊢*
              (l <{{E}} S')) ∧ Lst false false S') ∨
    (∃ S', (∀ l, (l {{C}}> (tw (tailw true true true true true true true true true true true true true true true e) +> default)) [target_tm]⊢*
              (l <{{F}} (([0, 0] : List (Fin 2)) +> S'))) ∧ Lst true false (([0, 1] : List (Fin 2)) +> S')) := by
  rcases e_split e with ⟨j, e', rfl⟩ | ⟨m, rfl⟩
  · rcases BusyBeaver.nat_even_or_odd_two_mul j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Tail11_inl _ (F1 ++ rep .T1 (2 * i)) (e'.map bt ++ [.T1])
        (F1E ++ ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1]))
        true false false false true false false false true false true false
        ((([true, false] : List Bool) ^ i) ++ (true :: e'))
        (Tail11_end_hs1 (2 * i) e') (noT0_F1_T1s (2 * i)) (Tail11_end_ret_even i) (Tail11_end_lst_even1 i e')
    · exact Tail11_inr _ (F1 ++ rep .T1 (2 * i + 1)) (e'.map bt ++ [.T1])
        (F1F_tail ++ (.T0 :: ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1])))
        false false false true false false true false false true false true
        (false :: ((([true, false] : List Bool) ^ i) ++ (true :: e')))
        (Tail11_end_hs1 (2 * i + 1) e') (noT0_F1_T1s (2 * i + 1)) (Tail11_end_ret_odd i) (Tail11_end_lst_odd1 i e')
  · rcases BusyBeaver.nat_even_or_odd_two_mul (m + 1) with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Tail11_inl_eq _ (F1 ++ rep .T1 (2 * i)) []
        (F1E ++ ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1]))
        true false false false true false false false true false true false
        (([true, false] : List Bool) ^ i)
        (Tail11_end_hs2 m (2 * i) hi) (noT0_F1_T1s (2 * i)) (Tail11_end_ret_even i) (Tail11_end_lst_even2 i)
    · exact Tail11_inr_eq _ (F1 ++ rep .T1 (2 * i + 1)) []
        (F1F_tail ++ (.T0 :: ((([tok.T1, tok.T0] : List tok) ^ i) ++ [.T1])))
        false false false true false false true false false true false true
        (false :: (([true, false] : List Bool) ^ i))
        (Tail11_end_hs2 m (2 * i + 1) hi) (noT0_F1_T1s (2 * i + 1)) (Tail11_end_ret_odd i) (Tail11_end_lst_odd2 i)

lemma Tail11 (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) (e : List Bool) :
    (∃ S', (∀ l, (l {{C}}> (tw (tailw true true true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default)) [target_tm]⊢*
              (l <{{E}} S')) ∧ Lst false false S') ∨
    (∃ S', (∀ l, (l {{C}}> (tw (tailw true true true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default)) [target_tm]⊢*
              (l <{{F}} (([0, 0] : List (Fin 2)) +> S'))) ∧ Lst true false (([0, 1] : List (Fin 2)) +> S')) := by
  cases b4
  · exact Tail11_inl _ [.T1, .T1, .T1, .TZ, .T1]
      (bt b5 :: .TZ :: .T1 :: bt b6 :: .TZ :: bt b7 :: .TZ :: .T1 :: bt b8 :: bt b9 :: .TZ :: bt b10 :: .TZ :: .T1 :: bt b11 :: .TZ :: bt b12 :: .TZ :: bt b13 :: .TZ :: bt b14 :: .TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .T0, .TZ, .T1, .T1]
      true b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e rfl trivial rfl rfl
  cases b5
  · exact Tail11_inr _ [.T1, .T1, .T1, .TZ, .T1, .T1]
      (.TZ :: .T1 :: bt b6 :: .TZ :: bt b7 :: .TZ :: .T1 :: bt b8 :: bt b9 :: .TZ :: bt b10 :: .TZ :: .T1 :: bt b11 :: .TZ :: bt b12 :: .TZ :: bt b13 :: .TZ :: bt b14 :: .TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .TZ, .T1, .T0, .T1]
      false true b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e rfl trivial rfl rfl
  cases b6
  · exact Tail11_inr _ [.T1, .T1, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1]
      (.TZ :: bt b7 :: .TZ :: .T1 :: bt b8 :: bt b9 :: .TZ :: bt b10 :: .TZ :: .T1 :: bt b11 :: .TZ :: bt b12 :: .TZ :: bt b13 :: .TZ :: bt b14 :: .TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .TZ, .T1, .T0, .T0, .TZ, .T1, .T1]
      false false true b7 b8 b9 b10 b11 b12 b13 b14 b15 e rfl trivial rfl rfl
  cases b7
  · exact Tail11_inl _ [.T1, .T1, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .T1, .TZ]
      (.TZ :: .T1 :: bt b8 :: bt b9 :: .TZ :: bt b10 :: .TZ :: .T1 :: bt b11 :: .TZ :: bt b12 :: .TZ :: bt b13 :: .TZ :: bt b14 :: .TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .T0, .TZ, .T1, .T1, .T0, .TZ, .T1, .T0, .TZ, .T1]
      true false false true b8 b9 b10 b11 b12 b13 b14 b15 e rfl trivial rfl rfl
  cases b8
  · exact Tail11_inl _ [.T1, .T1, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1]
      (bt b9 :: .TZ :: bt b10 :: .TZ :: .T1 :: bt b11 :: .TZ :: bt b12 :: .TZ :: bt b13 :: .TZ :: bt b14 :: .TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .T0, .TZ, .T1, .T1, .T0, .TZ, .T1, .T0, .TZ, .T0, .TZ, .T1, .T1]
      true false false false true b9 b10 b11 b12 b13 b14 b15 e rfl trivial rfl rfl
  cases b9
  · exact Tail11_inr _ [.T1, .T1, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1]
      (.TZ :: bt b10 :: .TZ :: .T1 :: bt b11 :: .TZ :: bt b12 :: .TZ :: bt b13 :: .TZ :: bt b14 :: .TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .TZ, .T1, .T0, .T0, .TZ, .T1, .T0, .TZ, .T1, .TZ, .T1, .T0, .T1]
      false false false true false true b10 b11 b12 b13 b14 b15 e rfl trivial rfl rfl
  cases b10
  · exact Tail11_inl _ [.T1, .T1, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1, .T1, .TZ]
      (.TZ :: .T1 :: bt b11 :: .TZ :: bt b12 :: .TZ :: bt b13 :: .TZ :: bt b14 :: .TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .T0, .TZ, .T1, .T1, .T0, .TZ, .T1, .T0, .TZ, .T0, .TZ, .T1, .T1, .T0, .TZ, .T1]
      true false false false true false true b11 b12 b13 b14 b15 e rfl trivial rfl rfl
  cases b11
  · exact Tail11_inl _ [.T1, .T1, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .TZ, .T1]
      (.TZ :: bt b12 :: .TZ :: bt b13 :: .TZ :: bt b14 :: .TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .T0, .TZ, .T1, .T1, .T0, .TZ, .T1, .T0, .TZ, .T0, .TZ, .T1, .T1, .T0, .TZ, .T0, .TZ, .T1, .T1]
      true false false false true false false true b12 b13 b14 b15 e rfl trivial rfl rfl
  cases b12
  · exact Tail11_inr _ [.T1, .T1, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1, .TZ]
      (.TZ :: bt b13 :: .TZ :: bt b14 :: .TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .TZ, .T1, .T0, .T0, .TZ, .T1, .T0, .TZ, .T1, .TZ, .T1, .T0, .T0, .TZ, .T1, .TZ, .T1, .T0, .TZ, .T1]
      false false false true false false true false true b13 b14 b15 e rfl trivial rfl rfl
  cases b13
  · exact Tail11_inl _ [.T1, .T1, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ]
      (.TZ :: bt b14 :: .TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .T0, .TZ, .T1, .T1, .T0, .TZ, .T1, .T0, .TZ, .T0, .TZ, .T1, .T1, .T0, .TZ, .T0, .TZ, .T1, .T0, .TZ, .T1, .TZ, .T1]
      true false false false true false false false true true b14 b15 e rfl trivial rfl rfl
  cases b14
  · exact Tail11_inr _ [.T1, .T1, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1, .TZ]
      (.TZ :: bt b15 :: .TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .TZ, .T1, .T0, .T0, .TZ, .T1, .T0, .TZ, .T1, .TZ, .T1, .T0, .T0, .TZ, .T1, .TZ, .T1, .T0, .TZ, .T0, .TZ, .T1, .TZ, .T1]
      false false false true false false true false false true true b15 e rfl trivial rfl rfl
  cases b15
  · exact Tail11_inl _ [.T1, .T1, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1, .T1, .TZ, .T1, .TZ, .T1, .T1, .TZ, .T1, .TZ, .T1, .TZ, .T1, .TZ]
      (.TZ :: .T1 :: (e.map bt ++ [.T1]))
      [.T1, .T0, .T0, .TZ, .T1, .T1, .T0, .TZ, .T1, .T0, .TZ, .T0, .TZ, .T1, .T1, .T0, .TZ, .T0, .TZ, .T1, .T0, .TZ, .T1, .TZ, .T0, .TZ, .T1, .TZ, .T1]
      true false false false true false false false true false true true e rfl trivial rfl rfl
  exact Tail11_end e

-- ============================================================================
-- Overflow & Digit-Block Return Algebra (`retf_app`, `RB_*`, `LD`, `OvN1`, `OvN0`, `OvS1`)
-- ============================================================================

lemma retf_app_n : ∀ (n : Nat) (ps1 : List ptok), ps1.length ≤ n →
    ∀ (m : Fin 6) (ps2 : List ptok) (rs : List tok) (m1 : Fin 6) (rs1 : List tok),
    retf m ps1 rs = (m1, [], rs1) →
    retf m (ps1 ++ ps2) rs = retf m1 ps2 rs1
  | 0, ps1, hn, m, ps2, rs, m1, rs1, hr => by
    cases ps1 with
    | nil =>
      rcases hr with ⟨rfl, _, rfl⟩
      rfl
    | cons _ _ => simp at hn
  | n + 1, [], _, m, ps2, rs, m1, rs1, hr => by
    rcases hr with ⟨rfl, _, rfl⟩
    rfl
  | n + 1, .P :: ps1, hn, m, ps2, rs, m1, rs1, hr => by
    by_cases hmE : m = E
    · subst hmE
      have hr' : retf F ps1 (.T0 :: rs) = (m1, [], rs1) := by unfold retf at hr; exact hr
      rw [List.cons_append, retf_E_P]
      exact retf_app_n n ps1 (by simpa using hn) F ps2 (.T0 :: rs) m1 rs1 hr'
    · by_cases hmF : m = F
      · subst hmF
        have hr' : retf E ps1 (.T1 :: rs) = (m1, [], rs1) := by unfold retf at hr; exact hr
        rw [List.cons_append, retf_F_P]
        exact retf_app_n n ps1 (by simpa using hn) E ps2 (.T1 :: rs) m1 rs1 hr'
      · unfold retf at hr
        simp only [hmE, hmF, ite_false] at hr
        nomatch hr
  | n + 1, .PZ :: ps1, hn, m, ps2, rs, m1, rs1, hr => by
    by_cases hmE : m = E
    · subst hmE
      have hr' : retf E ps1 (.TZ :: rs) = (m1, [], rs1) := by unfold retf at hr; exact hr
      rw [List.cons_append, retf_E_PZ]
      exact retf_app_n n ps1 (by simpa using hn) E ps2 (.TZ :: rs) m1 rs1 hr'
    · by_cases hmF : m = F
      · subst hmF
        cases ps1 with
        | nil => nomatch hr
        | cons p2 ps'' =>
          cases p2 with
          | PZ => nomatch hr
          | P =>
            cases rs with
            | nil => nomatch hr
            | cons r0 rs0 =>
              cases r0 with
              | T1 => nomatch hr
              | TZ => nomatch hr
              | T0 =>
                have hr' : retf E ps'' (.T0 :: .TZ :: .T1 :: rs0) = (m1, [], rs1) := by unfold retf at hr; exact hr
                have hlen : ps''.length ≤ n := by simp at hn; omega
                rw [List.cons_append, List.cons_append, retf_F_PZ_P]
                exact retf_app_n n ps'' hlen E ps2 (.T0 :: .TZ :: .T1 :: rs0) m1 rs1 hr'
      · unfold retf at hr
        simp only [hmE, hmF, ite_false] at hr
        nomatch hr

lemma retf_app (m : Fin 6) (ps1 ps2 : List ptok) (rs : List tok) (m1 : Fin 6) (rs1 : List tok)
    (hr : retf m ps1 rs = (m1, [], rs1)) :
    retf m (ps1 ++ ps2) rs = retf m1 ps2 rs1 :=
  retf_app_n ps1.length ps1 (Nat.le_refl _) m ps2 rs m1 rs1 hr

lemma RB_E2 (n : Nat) (rs : List tok) :
    retf E (([ptok.PZ, ptok.P] : List ptok) ^ (2 * n)) rs =
    (E, [], (([tok.T0, tok.TZ, tok.T1, tok.TZ] : List tok) ^ n) ++ rs) := by
  induction n generalizing rs with
  | zero => rfl
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n) + 1 + 1 := by omega
    rw [h2, list_pow_succ, list_pow_succ]
    simp only [List.cons_append, List.nil_append, retf_E_PZ, retf_E_P, retf_F_PZ_P]
    rw [ih (.T0 :: .TZ :: .T1 :: .TZ :: rs)]
    have hshift : (([tok.T0, tok.TZ, tok.T1, tok.TZ] : List tok) ^ n) ++ (.T0 :: .TZ :: .T1 :: .TZ :: rs) =
        (([tok.T0, tok.TZ, tok.T1, tok.TZ] : List tok) ^ (n + 1)) ++ rs := by
      change (([tok.T0, tok.TZ, tok.T1, tok.TZ] : List tok) ^ n) ++ ([tok.T0, tok.TZ, tok.T1, tok.TZ] ++ rs) = _
      rw [← List.append_assoc, lpow_shift]
    rw [hshift]

lemma RB_F2 (n : Nat) (rs : List tok) :
    retf F (([ptok.PZ, ptok.P] : List ptok) ^ (2 * n)) (.T0 :: rs) =
    (F, [], .T0 :: ((([tok.TZ, tok.T0, tok.TZ, tok.T1] : List tok) ^ n) ++ rs)) := by
  induction n generalizing rs with
  | zero => rfl
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n) + 1 + 1 := by omega
    rw [h2, list_pow_succ, list_pow_succ]
    simp only [List.cons_append, List.nil_append, retf_F_PZ_P, retf_E_PZ, retf_E_P]
    rw [ih (.TZ :: .T0 :: .TZ :: .T1 :: rs)]
    have hshift : (([tok.TZ, tok.T0, tok.TZ, tok.T1] : List tok) ^ n) ++ (.TZ :: .T0 :: .TZ :: .T1 :: rs) =
        (([tok.TZ, tok.T0, tok.TZ, tok.T1] : List tok) ^ (n + 1)) ++ rs := by
      change (([tok.TZ, tok.T0, tok.TZ, tok.T1] : List tok) ^ n) ++ ([tok.TZ, tok.T0, tok.TZ, tok.T1] ++ rs) = _
      rw [← List.append_assoc, lpow_shift]
    rw [hshift]

lemma RB_E1 (n : Nat) (rs : List tok) :
    retf E (([ptok.PZ, ptok.P] : List ptok) ^ (2 * n + 1)) rs =
    (F, [], .T0 :: ((([tok.TZ, tok.T0, tok.TZ, tok.T1] : List tok) ^ n) ++ (.TZ :: rs))) := by
  rw [list_pow_succ]
  simp only [List.cons_append, List.nil_append, retf_E_PZ, retf_E_P]
  exact RB_F2 n (.TZ :: rs)

lemma RB_F1 (n : Nat) (rs : List tok) :
    retf F (([ptok.PZ, ptok.P] : List ptok) ^ (2 * n + 1)) (.T0 :: rs) =
    (E, [], (([tok.T0, tok.TZ, tok.T1, tok.TZ] : List tok) ^ n) ++ (.T0 :: .TZ :: .T1 :: rs)) := by
  rw [list_pow_succ]
  simp only [List.cons_append, List.nil_append, retf_F_PZ_P]
  exact RB_E2 n (.T0 :: .TZ :: .T1 :: rs)

lemma shift4 (n : Nat) :
    [.T0, .TZ, .T1] ++ (([tok.TZ, tok.T0, tok.TZ, tok.T1] : List tok) ^ n) =
    (([tok.T0, tok.TZ, tok.T1, tok.TZ] : List tok) ^ n) ++ [.T0, .TZ, .T1] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [list_pow_succ, list_pow_succ]
    have h1 : ([tok.T0, tok.TZ, tok.T1] : List tok) ++ ([.TZ, .T0, .TZ, .T1] ++ (([tok.TZ, tok.T0, tok.TZ, tok.T1] : List tok) ^ n)) =
        [.T0, .TZ, .T1, .TZ] ++ ([.T0, .TZ, .T1] ++ (([tok.TZ, tok.T0, tok.TZ, tok.T1] : List tok) ^ n)) := rfl
    rw [h1, ih, List.append_assoc]

def dig (b : tok) (g : Nat) : List tok := b :: .TZ :: .T1 :: rep .TZ g

@[simp] def LD (b : tok) : List Nat → List tok
  | [] => []
  | g :: G' => dig b g ++ LD b G'

lemma LD_app (b : tok) (G1 G2 : List Nat) : LD b (G1 ++ G2) = LD b G1 ++ LD b G2 := by
  induction G1 with
  | nil => rfl
  | cons g G1 ih => simp only [List.cons_append, LD, ih, List.append_assoc]

lemma LD_ones (b : tok) (r : Nat) : LD b (rep 1 r) = ([b, .TZ, .T1, .TZ] : List tok) ^ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [rep, LD, ih, list_pow_succ]
    rfl

lemma ctr_zero (gs : List Nat) : ctr gs 0 = LD .T0 gs ++ [.T0] := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [ctr, bit, LD, dig, ih, List.cons_append, List.nil_append, List.append_assoc]; rfl

lemma pow_pos (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n

lemma ctr_ones (gs : List Nat) : ctr gs (2 ^ (gs.length + 1) - 1) = LD .T1 gs ++ [.T1] := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hp := pow_pos (gs.length + 1)
    have hlen : 2 ^ ((g :: gs).length + 1) - 1 = 2 * (2 ^ (gs.length + 1) - 1) + 1 := by
      simp only [List.length_cons]
      rw [pow2S (gs.length + 1)]
      omega
    rw [hlen, ctr_odd, ih]
    simp only [LD, dig, List.cons_append, List.append_assoc]

lemma noT0_TZ (a : Nat) : noT0 (rep .TZ a) := by
  induction a with
  | zero => trivial
  | succ a ih => exact ih

lemma noT0_LD1 (G : List Nat) : noT0 (LD .T1 G) := by
  induction G with
  | nil => trivial
  | cons g G ih =>
    simp only [LD, dig]
    exact noT0_app _ _ (noT0_TZ g) ih

lemma noT0_U (q : Nat) : noT0 (([tok.T1, tok.TZ] : List tok) ^ q) := by
  induction q with
  | zero => trivial
  | succ q ih =>
    rw [list_pow_succ]
    exact ih

lemma prc_TZ (a : Nat) : prc (rep .TZ a) = rep .PZ a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    have hcons : prc (.TZ :: rep .TZ a) = prc (rep .TZ a) ++ [.PZ] := by
      simp only [prc, List.map_cons, proc, List.reverse_cons]
    rw [rep, hcons, ih, repeat_snoc]; rfl

lemma prc_U (q : Nat) : prc (([tok.T1, tok.TZ] : List tok) ^ q) = ([ptok.PZ, ptok.P] : List ptok) ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [list_pow_succ, prc_app, ih]
    exact lpow_shift [ptok.PZ, ptok.P] q

lemma prc_dig (g : Nat) : prc (dig .T1 g) = rep .PZ g ++ [.P, .PZ, .P] := by
  change prc ([.T1, .TZ, .T1] ++ rep .TZ g) = _
  rw [prc_app, prc_TZ]; rfl

@[simp] def flatMapDig : List Nat → List ptok
  | [] => []
  | g :: gs => (rep .PZ g ++ [.P, .PZ, .P]) ++ flatMapDig gs

lemma flatMapDig_app (xs ys : List Nat) : flatMapDig (xs ++ ys) = flatMapDig xs ++ flatMapDig ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, flatMapDig, ih, List.append_assoc]

lemma prc_LD (G : List Nat) : prc (LD .T1 G) = flatMapDig G.reverse := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    simp only [LD, prc_app, ih, prc_dig, List.reverse_cons, flatMapDig_app, flatMapDig, List.append_nil]

lemma retf_dig (g : Nat) (ps : List ptok) (rs : List tok) :
    retf E (rep .PZ g ++ ([.P, .PZ, .P] ++ ps)) rs = retf E ps (dig .T0 g ++ rs) := by
  induction g generalizing rs with
  | zero =>
    simp only [rep, List.nil_append, List.cons_append, retf_E_P, retf_F_PZ_P]
    rfl
  | succ g ih =>
    rw [rep, List.cons_append, retf_E_PZ, ih (.TZ :: rs)]
    have hdig : dig .T0 g ++ (.TZ :: rs) = dig .T0 (g + 1) ++ rs := by
      simp only [dig, List.cons_append, List.append_assoc]
      congr 3
      change rep tok.TZ g ++ ([.TZ] ++ rs) = _
      rw [← List.append_assoc, repeat_snoc]; rfl
    rw [hdig]

lemma retf_LD (G : List Nat) (ps : List ptok) (rs : List tok) :
    retf E (prc (LD .T1 G) ++ ps) rs = retf E ps (LD .T0 G ++ rs) := by
  induction G generalizing ps rs with
  | nil => rfl
  | cons g G ih =>
    simp only [LD, prc_app, List.append_assoc]
    rw [ih, prc_dig, List.append_assoc, retf_dig]

lemma retf_lead (a : Nat) (rs : List tok) :
    retf E (rep .PZ a ++ [.P]) rs = (F, [], .T0 :: (rep .TZ a ++ rs)) := by
  induction a generalizing rs with
  | zero => rfl
  | succ a ih =>
    rw [rep, List.cons_append, retf_E_PZ, ih (.TZ :: rs)]
    have hrep : rep tok.TZ a ++ (.TZ :: rs) = rep tok.TZ (a + 1) ++ rs := by
      change rep tok.TZ a ++ ([.TZ] ++ rs) = _
      rw [← List.append_assoc, repeat_snoc]; rfl
    rw [hrep]

lemma OvSweep (w : List tok) (hw : noT0 w) (l S : ListBlank (Fin 2)) :
    (l {{A}}> (tw (.T0 :: w) +> S)) [target_tm]⊢⁺ ((pl (prc w ++ [.P]) +> l) {{C}}> S) := by
  rw [tw_cons, str_app_assoc]
  have s1 := AT0p l (tw w +> S)
  have s2 := Csweep w hw (([0, 1] : List (Fin 2)) +> l) S
  rw [pl_app, str_app_assoc]
  exact stepPlus_stepStar_stepPlus s1 s2

def sfx (H : Bool) : List tok := if H then [.TZ] else [.TZ, .T1, .TZ]
def gsof (G : List Nat) (r1 : Nat) : List Nat := G ++ (2 :: rep 1 r1)
def qof (H : Bool) (r1 : Nat) : Nat := if H then 2 * r1 + 1 else 2 * (r1 + 1)
def ones (gs : List Nat) : Nat := 2 ^ (gs.length + 1) - 1

@[simp] lemma sfx_true : sfx true = [.TZ] := rfl
@[simp] lemma sfx_false : sfx false = [.TZ, .T1, .TZ] := rfl
@[simp] lemma qof_true (r1 : Nat) : qof true r1 = 2 * r1 + 1 := rfl
@[simp] lemma qof_false (r1 : Nat) : qof false r1 = 2 * (r1 + 1) := rfl

lemma U2 (r : Nat) : ([tok.T1, .TZ, .T1, .TZ] : List tok) ^ r = ([tok.T1, .TZ] : List tok) ^ (2 * r) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have h2 : 2 * (r + 1) = (2 * r) + 1 + 1 := by omega
    rw [h2, list_pow_succ, list_pow_succ, list_pow_succ, ih]
    rfl

lemma body_ones (G : List Nat) (r1 : Nat) (H : Bool) :
    ctr (gsof G r1) (ones (gsof G r1)) ++ sfx H =
    LD .T1 G ++ (dig .T1 2 ++ (([tok.T1, .TZ] : List tok) ^ (qof H r1))) := by
  unfold ones gsof
  rw [ctr_ones, LD_app]
  simp only [LD, LD_ones, U2, List.append_assoc]
  congr 2
  cases H
  · change ([tok.T1, tok.TZ] : List tok) ^ (2 * r1) ++ ([tok.T1, tok.TZ] ++ [tok.T1, tok.TZ]) =
      ([tok.T1, tok.TZ] : List tok) ^ ((2 * r1 + 1) + 1)
    rw [← List.append_assoc, lpow_shift, lpow_shift]
  · exact lpow_shift ([tok.T1, tok.TZ] : List tok) (2 * r1)

lemma body_zero (G : List Nat) (r1 : Nat) :
    ctr (gsof G r1) 0 = LD .T0 G ++ (dig .T0 2 ++ ((([tok.T0, .TZ, .T1, .TZ] : List tok) ^ r1) ++ [.T0])) := by
  unfold gsof
  rw [ctr_zero, LD_app]
  simp only [LD, LD_ones, List.append_assoc]

lemma noT0_w (a : Nat) (G : List Nat) (q : Nat) :
    noT0 (rep .TZ a ++ (LD .T1 G ++ (dig .T1 2 ++ (([tok.T1, .TZ] : List tok) ^ q)))) :=
  noT0_app _ _ (noT0_TZ a) (noT0_app _ _ (noT0_LD1 G) (noT0_app _ _ trivial (noT0_U q)))

lemma prc_w (a : Nat) (G : List Nat) (q : Nat) :
    prc (rep .TZ a ++ (LD .T1 G ++ (dig .T1 2 ++ (([tok.T1, .TZ] : List tok) ^ q)))) ++ [.P] =
    (([ptok.PZ, ptok.P] : List ptok) ^ q) ++ ([.PZ, .PZ, .P, .PZ, .P] ++ (prc (LD .T1 G) ++ (rep .PZ a ++ [.P]))) := by
  simp only [prc_app, prc_U, prc_TZ, prc_dig, List.append_assoc, List.cons_append, List.nil_append]
  rfl

lemma BNp (ps : List ptok) (l r : ListBlank (Fin 2)) :
    ((pl ([.PZ, .PZ, .P, .PZ, .P] ++ ps) +> l) <{{F}} (([0, 0] : List (Fin 2)) +> r)) [target_tm]⊢*
    ((([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> (pl ps +> l)) {{A}}> (([0, 0, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) +> r)) := by
  rw [pl_app, str_app_assoc]
  simp only [pl, pw, List.cons_append, List.nil_append]
  execute

lemma tw_T00Z1 : tw [.T0, .T0, .TZ, .T1] = ([0, 0, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) := rfl

lemma OvN1 (G : List Nat) (r1 a : Nat) (l St St' : ListBlank (Fin 2))
    (ht : ∀ l', (l' {{C}}> St) [target_tm]⊢* (l' <{{E}} St')) :
    (l {{A}}> (tw (.T0 :: (rep .TZ a ++ (ctr (gsof G r1) (ones (gsof G r1)) ++ sfx true))) +> St)) [target_tm]⊢⁺
    ((([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> (pl (prc (LD .T1 G) ++ (rep .PZ a ++ [.P])) +> l)) {{A}}>
      (tw (.T0 :: (ctr (rep 1 r1) 0 ++ sfx false)) +> St')) := by
  rw [body_ones]
  have s1 := OvSweep (rep .TZ a ++ (LD .T1 G ++ (dig .T1 2 ++ (([tok.T1, .TZ] : List tok) ^ (qof true r1)))))
    (noT0_w a G (qof true r1)) l St
  rw [prc_w] at s1
  let X := prc (LD .T1 G) ++ (rep .PZ a ++ [.P])
  have s2 := ht (pl ((([ptok.PZ, ptok.P] : List ptok) ^ (qof true r1)) ++ ([.PZ, .PZ, .P, .PZ, .P] ++ X)) +> l)
  have hr : retf E ((([ptok.PZ, ptok.P] : List ptok) ^ (qof true r1)) ++ ([.PZ, .PZ, .P, .PZ, .P] ++ X)) [] =
      (F, [.PZ, .PZ, .P, .PZ, .P] ++ X, .T0 :: ((([tok.TZ, .T0, .TZ, .T1] : List tok) ^ r1) ++ [.TZ])) := by
    exact retf_app E (([ptok.PZ, ptok.P] : List ptok) ^ (2 * r1 + 1)) ([.PZ, .PZ, .P, .PZ, .P] ++ X) [] F
      (.T0 :: ((([tok.TZ, .T0, .TZ, .T1] : List tok) ^ r1) ++ [.TZ])) (RB_E1 r1 [])
  have s3 := retf_spec ((([ptok.PZ, ptok.P] : List ptok) ^ (qof true r1)) ++ ([.PZ, .PZ, .P, .PZ, .P] ++ X))
    E [] F ([.PZ, .PZ, .P, .PZ, .P] ++ X) (.T0 :: ((([tok.TZ, .T0, .TZ, .T1] : List tok) ^ r1) ++ [.TZ])) hr l St'
  rw [tw_T0_cons'] at s3
  have s4 := BNp X l (tw ((([tok.TZ, .T0, .TZ, .T1] : List tok) ^ r1) ++ [.TZ]) +> St')
  have heq : tw (.T0 :: (ctr (rep 1 r1) 0 ++ sfx false)) +> St' =
      (([0, 0, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) +> (tw ((([tok.TZ, .T0, .TZ, .T1] : List tok) ^ r1) ++ [.TZ]) +> St')) := by
    rw [ctr_zero, LD_ones]
    have htok : (.T0 :: (((([tok.T0, .TZ, .T1, .TZ] : List tok) ^ r1) ++ [.T0]) ++ sfx false)) =
        ([.T0, .T0, .TZ, .T1] ++ ((([tok.TZ, .T0, .TZ, .T1] : List tok) ^ r1) ++ [.TZ])) := by
      simp only [sfx_false, List.cons_append, List.nil_append, List.append_assoc]
      have hsh := (shift4 r1).symm
      have hsh' := congrArg (fun u => tok.T0 :: (u ++ [.TZ])) hsh
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using hsh'
    rw [htok, tw_app, str_app_assoc, tw_T00Z1]
  rw [← heq] at s4
  exact stepPlus_stepStar_stepPlus s1 (stepStar_trans s2 (stepStar_trans s3 s4))

lemma OvN0 (G : List Nat) (r1 a : Nat) (l St S0 : ListBlank (Fin 2))
    (ht : ∀ l', (l' {{C}}> St) [target_tm]⊢* (l' <{{F}} (([0, 0] : List (Fin 2)) +> S0))) :
    (l {{A}}> (tw (.T0 :: (rep .TZ a ++ (ctr (gsof G r1) (ones (gsof G r1)) ++ sfx false))) +> St)) [target_tm]⊢⁺
    ((([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> (pl (prc (LD .T1 G) ++ (rep .PZ a ++ [.P])) +> l)) {{A}}>
      (tw (.T0 :: (ctr (rep 1 (r1 + 1)) 0 ++ sfx true)) +> (([0, 1] : List (Fin 2)) +> S0))) := by
  rw [body_ones]
  have s1 := OvSweep (rep .TZ a ++ (LD .T1 G ++ (dig .T1 2 ++ (([tok.T1, .TZ] : List tok) ^ (qof false r1)))))
    (noT0_w a G (qof false r1)) l St
  rw [prc_w] at s1
  let X := prc (LD .T1 G) ++ (rep .PZ a ++ [.P])
  have s2 := ht (pl ((([ptok.PZ, ptok.P] : List ptok) ^ (qof false r1)) ++ ([.PZ, .PZ, .P, .PZ, .P] ++ X)) +> l)
  have hr : retf F ((([ptok.PZ, ptok.P] : List ptok) ^ (qof false r1)) ++ ([.PZ, .PZ, .P, .PZ, .P] ++ X)) [.T0] =
      (F, [.PZ, .PZ, .P, .PZ, .P] ++ X, .T0 :: ((([tok.TZ, .T0, .TZ, .T1] : List tok) ^ (r1 + 1)) ++ [])) := by
    exact retf_app F (([ptok.PZ, ptok.P] : List ptok) ^ (2 * (r1 + 1))) ([.PZ, .PZ, .P, .PZ, .P] ++ X) [.T0] F
      (.T0 :: ((([tok.TZ, .T0, .TZ, .T1] : List tok) ^ (r1 + 1)) ++ [])) (RB_F2 (r1 + 1) [])
  have s3 := retf_spec ((([ptok.PZ, ptok.P] : List ptok) ^ (qof false r1)) ++ ([.PZ, .PZ, .P, .PZ, .P] ++ X))
    F [.T0] F ([.PZ, .PZ, .P, .PZ, .P] ++ X) (.T0 :: ((([tok.TZ, .T0, .TZ, .T1] : List tok) ^ (r1 + 1)) ++ [])) hr l S0
  rw [tw_T0_cons', List.append_nil, tw_T0_cons'] at s3
  have s4 := BNp X l (tw (([tok.TZ, .T0, .TZ, .T1] : List tok) ^ (r1 + 1)) +> S0)
  have heq : tw (.T0 :: (ctr (rep 1 (r1 + 1)) 0 ++ sfx true)) +> (([0, 1] : List (Fin 2)) +> S0) =
      (([0, 0, 0, 0, 1, 0, 0, 0, 1] : List (Fin 2)) +> (tw (([tok.TZ, .T0, .TZ, .T1] : List tok) ^ (r1 + 1)) +> S0)) := by
    have h01 : (([0, 1] : List (Fin 2)) +> S0) = tw [.T1] +> S0 := rfl
    rw [h01, ← str_app_assoc, ← tw_app, ctr_zero, LD_ones]
    have htok : (.T0 :: (((([tok.T0, .TZ, .T1, .TZ] : List tok) ^ (r1 + 1)) ++ [.T0]) ++ sfx true)) ++ [.T1] =
        [.T0, .T0, .TZ, .T1] ++ (([tok.TZ, .T0, .TZ, .T1] : List tok) ^ (r1 + 1)) := by
      simp only [sfx_true, List.cons_append, List.nil_append, List.append_assoc]
      have hsh := (shift4 (r1 + 1)).symm
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using congrArg (fun u => tok.T0 :: u) hsh
    rw [htok, tw_app, str_app_assoc, tw_T00Z1]
  rw [← heq] at s4
  exact stepPlus_stepStar_stepPlus s1 (stepStar_trans s2 (stepStar_trans s3 s4))

lemma OvS1 (G : List Nat) (r1 a : Nat) (l St S0 : ListBlank (Fin 2))
    (ht : ∀ l', (l' {{C}}> St) [target_tm]⊢* (l' <{{F}} (([0, 0] : List (Fin 2)) +> S0))) :
    (l {{A}}> (tw (.T0 :: (rep .TZ a ++ (ctr (gsof G r1) (ones (gsof G r1)) ++ sfx true))) +> St)) [target_tm]⊢⁺
    (l <{{F}} (tw (.T0 :: (rep .TZ a ++ (ctr (gsof G r1) 0 ++ sfx true))) +> (([0, 1] : List (Fin 2)) +> S0))) := by
  rw [body_ones]
  have s1 := OvSweep (rep .TZ a ++ (LD .T1 G ++ (dig .T1 2 ++ (([tok.T1, .TZ] : List tok) ^ (qof true r1)))))
    (noT0_w a G (qof true r1)) l St
  rw [prc_w] at s1
  have s2 := ht (pl ((([ptok.PZ, ptok.P] : List ptok) ^ (qof true r1)) ++ ([.PZ, .PZ, .P, .PZ, .P] ++ (prc (LD .T1 G) ++ (rep .PZ a ++ [.P])))) +> l)
  have hr : retf F ((([ptok.PZ, ptok.P] : List ptok) ^ (qof true r1)) ++ ([.PZ, .PZ, .P, .PZ, .P] ++ (prc (LD .T1 G) ++ (rep .PZ a ++ [.P])))) [.T0] =
      (F, [], .T0 :: (rep .TZ a ++ (LD .T0 G ++ (dig .T0 2 ++ ((([tok.T0, .TZ, .T1, .TZ] : List tok) ^ r1) ++ [.T0, .TZ, .T1]))))) := by
    have h1 := retf_app F (([ptok.PZ, ptok.P] : List ptok) ^ (2 * r1 + 1))
      ([.PZ, .PZ, .P, .PZ, .P] ++ (prc (LD .T1 G) ++ (rep .PZ a ++ [.P]))) [.T0] E
      ((([tok.T0, .TZ, .T1, .TZ] : List tok) ^ r1) ++ [.T0, .TZ, .T1]) (RB_F1 r1 [])
    simp only [qof_true]
    rw [h1]
    change retf E (rep .PZ 2 ++ ([.P, .PZ, .P] ++ (prc (LD .T1 G) ++ (rep .PZ a ++ [.P]))))
      ((([tok.T0, .TZ, .T1, .TZ] : List tok) ^ r1) ++ [.T0, .TZ, .T1]) = _
    rw [retf_dig, retf_LD, retf_lead]
  have s3 := retf_spec ((([ptok.PZ, ptok.P] : List ptok) ^ (qof true r1)) ++ ([.PZ, .PZ, .P, .PZ, .P] ++ (prc (LD .T1 G) ++ (rep .PZ a ++ [.P]))))
    F [.T0] F [] (.T0 :: (rep .TZ a ++ (LD .T0 G ++ (dig .T0 2 ++ ((([tok.T0, .TZ, .T1, .TZ] : List tok) ^ r1) ++ [.T0, .TZ, .T1]))))) hr l S0
  rw [tw_T0_cons'] at s3
  simp only [pl, listblank_append_nil] at s3
  have heq : tw (.T0 :: (rep .TZ a ++ (ctr (gsof G r1) 0 ++ sfx true))) +> (([0, 1] : List (Fin 2)) +> S0) =
      tw (.T0 :: (rep .TZ a ++ (LD .T0 G ++ (dig .T0 2 ++ ((([tok.T0, .TZ, .T1, .TZ] : List tok) ^ r1) ++ [.T0, .TZ, .T1]))))) +> S0 := by
    have h01 : (([0, 1] : List (Fin 2)) +> S0) = tw [.T1] +> S0 := rfl
    rw [h01, ← str_app_assoc, ← tw_app, body_zero]
    simp only [sfx_true, List.cons_append, List.nil_append, List.append_assoc]
  rw [← heq] at s3
  exact stepPlus_stepStar_stepPlus s1 (stepStar_trans s2 s3)

-- High-Level Configurations & Zone / Orbit Lemmas (`KP`, `KX`, `Zones`, `NOrb`, `POrb`)
-- ============================================================================

def KP (W : ListBlank (Fin 2)) (p : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  W {{A}}> (tw (.T0 :: (rep .TZ p ++ (ctr gs v ++ sfx H))) +> St)

def NN (gs : List Nat) : Nat := 2 ^ (gs.length + 1)

lemma wall0 : (([1] : List (Fin 2)) +> (default : ListBlank (Fin 2))) =
    (([1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> default)) := by
  simp

lemma P100 (n : Nat) (l : ListBlank (Fin 2)) (p : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2))
    (hv : v + 2 < NN gs) :
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 1))) +> l)) p gs v H St) [target_tm]⊢*
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l)) (p + 1) gs (v + 2) H St) := by
  have hL : (([1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 1))) +> l) =
      (([1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l)))) := by
    rw [list_pow_succ]; simp only [List.cons_append, List.nil_append, listblank_append_cons, listblank_append_nil]
  unfold KP
  rw [hL]
  exact TwoInc gs v p (sfx H) ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l)) St hv

lemma P100s (m : Nat) : ∀ (n : Nat) (l : ListBlank (Fin 2)) (p : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2)),
    2 * m + v < NN gs →
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ (m + n))) +> l)) p gs v H St) [target_tm]⊢*
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l)) (m + p) gs (2 * m + v) H St) := by
  induction m with
  | zero =>
    intro n l p gs v H St _
    simp
    exact ⟨0, rfl⟩
  | succ m ih =>
    intro n l p gs v H St hv
    have hm : m + 1 + n = (m + n) + 1 := by omega
    rw [hm]
    have s1 := P100 (m + n) l p gs v H St (by omega)
    have s2 := ih n l (p + 1) gs (v + 2) H St (by omega)
    have hp : m + (p + 1) = (m + 1) + p := by omega
    have hv' : 2 * m + (v + 2) = 2 * (m + 1) + v := by omega
    rw [hp, hv'] at s2
    exact stepStar_trans s1 s2

lemma WX (p : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2))
    (hv : v + 2 < NN gs) :
    (KP (([1] : List (Fin 2)) +> default) p gs v H St) [target_tm]⊢*
    (KP default (p + 1) gs (v + 2) H St) := by
  unfold KP
  rw [wall0]
  exact TwoInc gs v p (sfx H) default St hv

lemma stepStar_F_A_of_eq {R₁ R₂ R₁' R₂' : ListBlank (Fin 2)}
    (h₁ : R₁' = R₁) (h₂ : R₂' = R₂)
    (h : (default <{{F}} R₁) [target_tm]⊢* (default {{A}}> R₂)) :
    (default <{{F}} R₁') [target_tm]⊢* (default {{A}}> R₂') := by
  subst h₁; subst h₂; exact h

lemma tw_bnc1 (a : Nat) (xs : List tok) :
    tw (.T0 :: (rep .TZ (a + 1) ++ xs)) = [0, 0] ++ ([1, 0, 0] ++ tw (rep .TZ a ++ xs)) := rfl

lemma tw_bnc2 (a : Nat) (xs : List tok) :
    tw (.T0 :: (rep .TZ (a + 2) ++ xs)) = [0, 0] ++ ([1, 0, 0] ++ ([1, 0, 0] ++ tw (rep .TZ a ++ xs))) := rfl

lemma Bnc_h1_a (a : Nat) (xs : List tok) (St : ListBlank (Fin 2)) :
    tw (.T0 :: (rep .TZ (a + 1) ++ xs)) +> St =
    ([0, 0] ++ ([1, 0, 0] ++ tw (rep .TZ a ++ xs))) +> St :=
  congrArg (fun l => l +> St) (tw_bnc1 a xs)

lemma Bnc_h1_b (ys : List (Fin 2)) (St : ListBlank (Fin 2)) :
    ([0, 0] ++ ([1, 0, 0] ++ ys)) +> St =
    ([0, 0] : List (Fin 2)) +> (([1, 0, 0] ++ ys) +> St) :=
  str_app_assoc [0, 0] ([1, 0, 0] ++ ys) St

lemma Bnc_h1_c (ys : List (Fin 2)) (St : ListBlank (Fin 2)) :
    ([0, 0] : List (Fin 2)) +> (([1, 0, 0] ++ ys) +> St) =
    ([0, 0] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> (ys +> St)) :=
  congrArg (fun r => ([0, 0] : List (Fin 2)) +> r) (str_app_assoc [1, 0, 0] ys St)

lemma Bnc_h1 (a : Nat) (xs : List tok) (St : ListBlank (Fin 2)) :
    tw (.T0 :: (rep .TZ (a + 1) ++ xs)) +> St =
    ([0, 0] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> (tw (rep .TZ a ++ xs) +> St)) := by
  have ha := Bnc_h1_a a xs St
  have hb := Bnc_h1_b (tw (rep .TZ a ++ xs)) St
  have hc := Bnc_h1_c (tw (rep .TZ a ++ xs)) St
  exact Eq.trans ha (Eq.trans hb hc)

lemma Bnc_h2_a (a : Nat) (xs : List tok) (St : ListBlank (Fin 2)) :
    tw (.T0 :: (rep .TZ (a + 2) ++ xs)) +> St =
    ([0, 0] ++ ([1, 0, 0] ++ ([1, 0, 0] ++ tw (rep .TZ a ++ xs)))) +> St :=
  congrArg (fun l => l +> St) (tw_bnc2 a xs)

lemma Bnc_h2_b (ys : List (Fin 2)) (St : ListBlank (Fin 2)) :
    ([0, 0] ++ ([1, 0, 0] ++ ([1, 0, 0] ++ ys))) +> St =
    ([0, 0] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> (ys +> St))) := by
  have h1 := str_app_assoc [0, 0] ([1, 0, 0] ++ ([1, 0, 0] ++ ys)) St
  have h2 := Bnc_h1_c ([1, 0, 0] ++ ys) St
  have h3 := congrArg (fun r => ([0, 0] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> r)) (str_app_assoc [1, 0, 0] ys St)
  exact Eq.trans h1 (Eq.trans h2 h3)

lemma Bnc_h2 (a : Nat) (xs : List tok) (St : ListBlank (Fin 2)) :
    tw (.T0 :: (rep .TZ (a + 2) ++ xs)) +> St =
    ([0, 0] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> (([1, 0, 0] : List (Fin 2)) +> (tw (rep .TZ a ++ xs) +> St))) := by
  have ha := Bnc_h2_a a xs St
  have hb := Bnc_h2_b (tw (rep .TZ a ++ xs)) St
  exact Eq.trans ha hb

lemma Bnc_TZ (a : Nat) (xs : List tok) (St : ListBlank (Fin 2)) :
    (default <{{F}} (tw (.T0 :: (rep .TZ (a + 1) ++ xs)) +> St)) [target_tm]⊢*
    (default {{A}}> (tw (.T0 :: (rep .TZ (a + 2) ++ xs)) +> St)) := by
  have h1 := Bnc_h1 a xs St
  have h2 := Bnc_h2 a xs St
  have hb := Bnc (tw (rep .TZ a ++ xs) +> St)
  exact stepStar_F_A_of_eq h1 h2 hb

lemma Inc1 (a : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2))
    (hv : v + 1 < NN gs) :
    (KP default (a + 1) gs v H St) [target_tm]⊢*
    (KP default (a + 2) gs (v + 1) H St) := by
  have s1 := IncL gs v (a + 1) hv default St (sfx H)
  have s2 := Bnc_TZ a (ctr gs (v + 1) ++ sfx H) St
  exact stepStar_trans s1 s2

lemma Incs (m : Nat) : ∀ (a : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2)),
    m + v < NN gs →
    (KP default (a + 1) gs v H St) [target_tm]⊢*
    (KP default (m + (a + 1)) gs (m + v) H St) := by
  induction m with
  | zero =>
    intro a gs v H St _
    simp
    exact ⟨0, rfl⟩
  | succ m ih =>
    intro a gs v H St hv
    have s1 := Inc1 a gs v H St (by omega)
    have s2 := ih (a + 1) gs (v + 1) H St (by omega)
    have ha : m + (a + 2) = (m + 1) + (a + 1) := by omega
    have hv' : m + (v + 1) = (m + 1) + v := by omega
    rw [ha, hv'] at s2
    exact stepStar_trans s1 s2

@[simp] def zw : List Nat → List (Fin 2)
  | [] => []
  | g :: L' => [1, 0, 0, 1] ++ ((([0, 1, 0] : List (Fin 2)) ^ (g + 1)) ++ zw L')

@[simp] def zv : List Nat → Nat → Nat
  | [], v => v
  | g :: L', v => zv L' (2 * v + 2 * g)

@[simp] def zg : List Nat → Nat → List Nat → List Nat
  | [], _, gs => gs
  | g :: L', p, gs => zg L' (g - 2) ((p + 2) :: gs)

@[simp] def zp : List Nat → Nat → Nat
  | [], p => p
  | g :: L', _ => zp L' (g - 2)

lemma P010s (m : Nat) : ∀ (X : List (Fin 2)) (Y : ListBlank (Fin 2)) (p : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2)),
    2 * m + v < NN gs →
    (KP ((([1, 0] ++ ((([0, 1, 0] : List (Fin 2)) ^ m) ++ X)) +> Y)) p gs v H St) [target_tm]⊢*
    (KP ((([1, 0] ++ X) +> Y)) (m + p) gs (2 * m + v) H St) := by
  induction m with
  | zero =>
    intro X Y p gs v H St _
    simp
    exact ⟨0, rfl⟩
  | succ m ih =>
    intro X Y p gs v H St hv
    have hL : (([1, 0] ++ ((([0, 1, 0] : List (Fin 2)) ^ (m + 1)) ++ X)) +> Y) =
        (([1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> ((([1, 0] ++ ((([0, 1, 0] : List (Fin 2)) ^ m) ++ X)) +> Y)))) := by
      rw [list_pow_succ]; simp only [List.cons_append, List.nil_append, listblank_append_cons, listblank_append_nil]
    have s1 : (KP ((([1, 0] ++ ((([0, 1, 0] : List (Fin 2)) ^ (m + 1)) ++ X)) +> Y)) p gs v H St) [target_tm]⊢*
        (KP ((([1, 0] ++ ((([0, 1, 0] : List (Fin 2)) ^ m) ++ X)) +> Y)) (p + 1) gs (v + 2) H St) := by
      unfold KP
      rw [hL]
      exact TwoInc gs v p (sfx H) ((([1, 0] ++ ((([0, 1, 0] : List (Fin 2)) ^ m) ++ X)) +> Y)) St (by unfold NN at hv; omega)
    have s2 := ih X Y (p + 1) gs (v + 2) H St (by omega)
    have hp : m + (p + 1) = (m + 1) + p := by omega
    have hv' : 2 * m + (v + 2) = 2 * (m + 1) + v := by omega
    rw [hp, hv'] at s2
    exact stepStar_trans s1 s2

lemma Zone (g : Nat) (L : List Nat) (X : List (Fin 2)) (Y : ListBlank (Fin 2))
    (p : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2))
    (hg : 2 ≤ g) (hv : v + g < NN gs) :
    (KP ((([1, 0] ++ (zw (g :: L) ++ X)) +> Y)) p gs v H St) [target_tm]⊢*
    (KP ((([1, 0] ++ (zw L ++ X)) +> Y)) (g - 2) ((p + 2) :: gs) (2 * v + 2 * g) H St) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 2 := ⟨g - 2, by omega⟩
  have hsub : g' + 2 - 2 = g' := by omega
  rw [hsub]
  have hL : (([1, 0] ++ (zw ((g' + 2) :: L) ++ X)) +> Y) =
      (([1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0] : List (Fin 2)) +>
        (([0] : List (Fin 2)) +> ((([1, 0] ++ ((([0, 1, 0] : List (Fin 2)) ^ g') ++ (zw L ++ X))) +> Y)))) := by
    simp only [zw, pow_succ_list, List.cons_append, List.nil_append, List.append_assoc, listblank_append_cons, listblank_append_nil]
  have s1 : (KP ((([1, 0] ++ (zw ((g' + 2) :: L) ++ X)) +> Y)) p gs v H St) [target_tm]⊢*
      (KP ((([1, 0] ++ ((([0, 1, 0] : List (Fin 2)) ^ g') ++ (zw L ++ X))) +> Y)) 0 ((p + 2) :: gs) (2 * (v + 2)) H St) := by
    unfold KP
    rw [hL]
    exact ZXg gs v p (sfx H) ((([1, 0] ++ ((([0, 1, 0] : List (Fin 2)) ^ g') ++ (zw L ++ X))) +> Y)) St (by unfold NN at hv; omega)
  have hbound : 2 * g' + 2 * (v + 2) < NN ((p + 2) :: gs) := by
    unfold NN at hv ⊢
    simp only [List.length_cons]
    rw [pow2S (gs.length + 1)]
    omega
  have s2 := P010s g' (zw L ++ X) Y 0 ((p + 2) :: gs) (2 * (v + 2)) H St hbound
  have hp : g' + 0 = g' := by omega
  have hv' : 2 * g' + 2 * (v + 2) = 2 * v + 2 * (g' + 2) := by omega
  rw [hp, hv'] at s2
  exact stepStar_trans s1 s2

lemma zv_ge (L : List Nat) : ∀ v, 2 ^ L.length * v ≤ zv L v := by
  induction L with
  | nil => intro v; simp
  | cons g L ih =>
    intro v
    have h := ih (2 * v + 2 * g)
    simp only [zv, List.length_cons, pow2S]
    have hle : 2 * 2 ^ L.length * v ≤ 2 ^ L.length * (2 * v + 2 * g) := by
      have h1 : 2 * 2 ^ L.length * v = 2 ^ L.length * (2 * v) := by ring
      rw [h1]
      exact Nat.mul_le_mul_left (2 ^ L.length) (by omega)
    exact Nat.le_trans hle h

lemma zg_len (L : List Nat) : ∀ p gs, (zg L p gs).length = L.length + gs.length := by
  induction L with
  | nil => intro p gs; simp
  | cons g L ih => intro p gs; simp [zg, ih]; omega

@[simp] def AllGe2 : List Nat → Prop
  | [] => True
  | g :: L => 2 ≤ g ∧ AllGe2 L

lemma AllGe2_app (L1 L2 : List Nat) (h1 : AllGe2 L1) (h2 : AllGe2 L2) : AllGe2 (L1 ++ L2) := by
  induction L1 with
  | nil => exact h2
  | cons g L1 ih => exact ⟨h1.1, ih h1.2⟩

lemma AllGe2_rev (L : List Nat) (h : AllGe2 L) : AllGe2 L.reverse := by
  induction L with
  | nil => trivial
  | cons g L ih =>
    simp only [List.reverse_cons]
    exact AllGe2_app L.reverse [g] (ih h.2) ⟨h.1, trivial⟩

lemma Zones (L : List Nat) (hL : AllGe2 L) :
    ∀ (X : List (Fin 2)) (Y : ListBlank (Fin 2)) (p : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2)),
    zv L v < 2 ^ ((gs.length + 1) + L.length) →
    (KP ((([1, 0] ++ (zw L ++ X)) +> Y)) p gs v H St) [target_tm]⊢*
    (KP ((([1, 0] ++ X) +> Y)) (zp L p) (zg L p gs) (zv L v) H St) := by
  induction L with
  | nil =>
    intro X Y p gs v H St _
    simp [zw, zp, zg, zv]
    exact ⟨0, rfl⟩
  | cons g L ih =>
    intro X Y p gs v H St hv
    rcases hL with ⟨hg, hL'⟩
    simp only [zv, zp, zg, List.length_cons] at hv ⊢
    have hz := zv_ge L (2 * v + 2 * g)
    have hn : v + g < NN gs := by
      unfold NN
      have he : 2 ^ ((gs.length + 1) + (L.length + 1)) = 2 ^ L.length * (2 * 2 ^ (gs.length + 1)) := by
        rw [← Nat.add_assoc, pow2S, Nat.pow_add]; ring
      rw [he] at hv
      have hp := pow_pos L.length
      nlinarith
    have s1 := Zone g L X Y p gs v H St hg hn
    have heq : (((p + 2) :: gs).length + 1) + L.length = (gs.length + 1) + (L.length + 1) := by
      simp; omega
    have s2 := ih hL' X Y (g - 2) ((p + 2) :: gs) (2 * v + 2 * g) H St (by rw [heq]; exact hv)
    exact stepStar_trans s1 s2

@[simp] def gval : List Nat → Nat
  | [] => 0
  | g :: G' => 2 * (g + gval G')

lemma zv_app (L1 L2 : List Nat) : ∀ v, zv (L1 ++ L2) v = zv L2 (zv L1 v) := by
  induction L1 with
  | nil => intro v; rfl
  | cons g L1 ih => intro v; exact ih (2 * v + 2 * g)

lemma zp_app (L1 L2 : List Nat) : ∀ p, zp (L1 ++ L2) p = zp L2 (zp L1 p) := by
  induction L1 with
  | nil => intro p; rfl
  | cons g L1 ih => intro p; exact ih (g - 2)

lemma zg_app (L1 L2 : List Nat) : ∀ p gs, zg (L1 ++ L2) p gs = zg L2 (zp L1 p) (zg L1 p gs) := by
  induction L1 with
  | nil => intro p gs; rfl
  | cons g L1 ih => intro p gs; exact ih (g - 2) ((p + 2) :: gs)

lemma zw_app (L1 L2 : List Nat) : zw (L1 ++ L2) = zw L1 ++ zw L2 := by
  induction L1 with
  | nil => rfl
  | cons g L1 ih => simp [zw, ih, List.append_assoc]

lemma zv_rev (G : List Nat) : zv G.reverse 0 = gval G := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    simp [List.reverse_cons, zv_app, ih, gval]
    omega

lemma zg_rev (G gs0 : List Nat) (hG : AllGe2 G) :
    (zp G.reverse 0 + 2) :: zg G.reverse 0 gs0 = G ++ (2 :: gs0) := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    rcases hG with ⟨hg, hG'⟩
    simp only [List.reverse_cons, zp_app, zg_app, zp, zg]
    rw [ih hG']
    have hsub : g - 2 + 2 = g := by omega
    simp [hsub]

lemma zp_rev_last (G : List Nat) (p : Nat) : zp (G.reverse ++ [p]) 0 = p - 2 := by
  rw [zp_app]; rfl

lemma zv_rev_last (G : List Nat) (p : Nat) : zv (G.reverse ++ [p]) 0 = 2 * gval G + 2 * p := by
  rw [zv_app, zv_rev]; rfl

lemma zg_rev_last (G : List Nat) (p : Nat) (gs0 : List Nat) (hG : AllGe2 G) :
    zg (G.reverse ++ [p]) 0 gs0 = G ++ (2 :: gs0) := by
  rw [zg_app]; exact zg_rev G gs0 hG

lemma pl_lead (a : Nat) : pl (rep .PZ a ++ [.P]) = [0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ a) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [rep, List.cons_append, pl, pw, ih, list_pow_succ]; rfl

lemma pl_PZ (g : Nat) : pl (rep .PZ g) = ([0, 1, 0] : List (Fin 2)) ^ g := by
  induction g with
  | zero => rfl
  | succ g ih =>
    rw [rep, pl, pw, ih, list_pow_succ]

lemma zw_LD_gen (L : List Nat) :
    ([1, 0, 0, 1] : List (Fin 2)) ++ pl (flatMapDig L) = zw L ++ [1, 0, 0, 1] := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    simp only [flatMapDig, zw, pl_app, pl_PZ, pl, pw, List.cons_append, List.nil_append, List.append_assoc]
    have ih' : (1 :: 0 :: 0 :: 1 :: pl (flatMapDig L)) = zw L ++ [1, 0, 0, 1] := ih
    rw [ih']
    change (1 : Fin 2) :: 0 :: 0 :: 1 :: ((([0, 1, 0] : List (Fin 2)) ^ g) ++ ([0, 1, 0] ++ (zw L ++ [1, 0, 0, 1]))) = _
    rw [← List.append_assoc ((([0, 1, 0] : List (Fin 2)) ^ g)), lpow_shift]

lemma wallOv (G : List Nat) (W : List ptok) (l : ListBlank (Fin 2)) :
    (([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> (pl (prc (LD .T1 G) ++ W) +> l)) =
    (([1, 0] ++ (zw G.reverse ++ ([1, 0, 0, 1] ++ pl W))) +> l) := by
  rw [← str_app_assoc, pl_app, prc_LD]
  congr 1
  change ([1, 0] ++ [1, 0, 0, 1]) ++ (pl (flatMapDig G.reverse) ++ pl W) = _
  rw [List.append_assoc [1, 0], ← List.append_assoc [1, 0, 0, 1], zw_LD_gen]
  simp [List.append_assoc]

lemma wallPO (G : List Nat) (p n : Nat) (l : ListBlank (Fin 2)) :
    (([1, 0] ++ (zw G.reverse ++ ([1, 0, 0, 1] ++ pl (rep .PZ p ++ [.P])))) +>
      ((([0, 0, 0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l))) =
    (([1, 0] ++ (zw (G.reverse ++ [p]) ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 1)))) +> l) := by
  rw [← str_app_assoc, zw_app, pl_app, pl_PZ]
  congr 1
  simp only [zw, List.append_nil, List.append_assoc]
  congr 3
  change (([0, 1, 0] : List (Fin 2)) ^ p) ++ ([0, 1, 0] ++ ([0, 0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ n))) =
    (([0, 1, 0] : List (Fin 2)) ^ (p + 1)) ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 1))
  rw [← List.append_assoc ((([0, 1, 0] : List (Fin 2)) ^ p)), lpow_shift]
  rfl

lemma ZXN (a : Nat) (l : ListBlank (Fin 2)) (p : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2))
    (hv : v + 2 < NN gs) :
    (KP ((([1, 0] ++ ([1, 0, 0, 1] ++ pl (rep .PZ (a + 2) ++ [.P]))) +> l)) p gs v H St) [target_tm]⊢*
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ a)) +> l)) 0 ((p + 2) :: gs) (2 * (v + 2)) H St) := by
  unfold KP
  rw [pl_lead]
  have hL : (([1, 0] ++ ([1, 0, 0, 1] ++ ([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ (a + 2))))) +> l) =
      (([1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ a)) +> l)))) := by
    rw [list_pow_succ, list_pow_succ]; simp only [List.cons_append, List.nil_append, listblank_append_cons, listblank_append_nil]
  rw [hL]
  exact ZXg gs v p (sfx H) ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ a)) +> l)) St hv

lemma ZXP (n : Nat) (l : ListBlank (Fin 2)) (p : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2))
    (hv : v + 3 < NN gs) :
    (KP ((([1, 0] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 3))) +> l)) p gs v H St) [target_tm]⊢*
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l)) 0 ((p + 1) :: gs) (2 * (v + 3)) H St) := by
  have hL1 : (([1, 0] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 3))) +> l) =
      (([1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 2))) +> l)))) := by
    rw [list_pow_succ]; simp only [List.cons_append, List.nil_append, listblank_append_cons, listblank_append_nil]
  have s1 : (KP ((([1, 0] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 3))) +> l)) p gs v H St) [target_tm]⊢*
      (KP ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 2))) +> l)) (p + 1) gs (v + 2) H St) := by
    unfold KP
    rw [hL1]
    exact TwoInc gs v p (sfx H) ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 2))) +> l)) St (by unfold NN at hv; omega)
  have hL2 : (([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 2))) +> l) =
      (([0, 1, 0, 0, 1, 0] : List (Fin 2)) +> (([0] : List (Fin 2)) +> ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l)))) := by
    rw [list_pow_succ, list_pow_succ]; simp only [List.cons_append, List.nil_append, listblank_append_cons, listblank_append_nil]
  have s2 : (KP ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 2))) +> l)) (p + 1) gs (v + 2) H St) [target_tm]⊢*
      (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l)) 0 ((p + 1) :: gs) (2 * (v + 3)) H St) := by
    unfold KP
    rw [hL2]
    exact ZXP2g gs (v + 2) (p + 1) (sfx H) ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l)) St hv
  exact stepStar_trans s1 s2

def OvNp (H : Bool) (r1 : Nat) (St : ListBlank (Fin 2)) (H' : Bool) (r1' : Nat) (St' : ListBlank (Fin 2)) : Prop :=
  ∀ G a l,
    (l {{A}}> (tw (.T0 :: (rep .TZ a ++ (ctr (gsof G r1) (ones (gsof G r1)) ++ sfx H))) +> St)) [target_tm]⊢⁺
    ((([1, 0, 1, 0, 0, 1] : List (Fin 2)) +> (pl (prc (LD .T1 G) ++ (rep .PZ a ++ [.P])) +> l)) {{A}}>
      (tw (.T0 :: (ctr (rep 1 r1') 0 ++ sfx H')) +> St'))

def OvSp (r1 : Nat) (St St' : ListBlank (Fin 2)) : Prop :=
  ∀ G a l,
    (l {{A}}> (tw (.T0 :: (rep .TZ a ++ (ctr (gsof G r1) (ones (gsof G r1)) ++ sfx true))) +> St)) [target_tm]⊢⁺
    (l <{{F}} (tw (.T0 :: (rep .TZ a ++ (ctr (gsof G r1) 0 ++ sfx true))) +> St'))

lemma OvNp1 (r1 : Nat) (St St' : ListBlank (Fin 2))
    (ht : ∀ l', (l' {{C}}> St) [target_tm]⊢* (l' <{{E}} St')) :
    OvNp true r1 St false r1 St' :=
  fun G a l => OvN1 G r1 a l St St' ht

lemma OvNp0 (r1 : Nat) (St S0 : ListBlank (Fin 2))
    (ht : ∀ l', (l' {{C}}> St) [target_tm]⊢* (l' <{{F}} (([0, 0] : List (Fin 2)) +> S0))) :
    OvNp false r1 St true (r1 + 1) (([0, 1] : List (Fin 2)) +> S0) :=
  fun G a l => OvN0 G r1 a l St S0 ht

lemma OvSp1 (r1 : Nat) (St S0 : ListBlank (Fin 2))
    (ht : ∀ l', (l' {{C}}> St) [target_tm]⊢* (l' <{{F}} (([0, 0] : List (Fin 2)) +> S0))) :
    OvSp r1 St (([0, 1] : List (Fin 2)) +> S0) :=
  fun G a l => OvS1 G r1 a l St S0 ht

lemma len_gsof (G : List Nat) (r1 : Nat) : (gsof G r1).length = G.length + (r1 + 1) := by
  simp [gsof, rep_length]

lemma pS (k r : Nat) : 2 ^ (k + (r + 1)) = 2 * 2 ^ (k + r) := by
  rw [← Nat.add_assoc, pow2S]

lemma NN_gsof (G : List Nat) (r1 : Nat) : NN (gsof G r1) = 4 * 2 ^ (G.length + r1) := by
  unfold NN
  rw [len_gsof]
  have h1 : G.length + (r1 + 1) + 1 = (G.length + r1) + 1 + 1 := by omega
  rw [h1, pow2S, pow2S]; ring

lemma ones_gsof (G : List Nat) (r1 : Nat) : ones (gsof G r1) = 4 * 2 ^ (G.length + r1) - 1 := by
  unfold ones
  have h := NN_gsof G r1
  unfold NN at h
  omega

lemma Q_cons (g : Nat) (G : List Nat) (r1 : Nat) :
    2 ^ ((g :: G).length + (r1 + 1)) = 4 * 2 ^ (G.length + r1) := by
  simp only [List.length_cons]
  have h1 : G.length + 1 + (r1 + 1) = (G.length + r1) + 1 + 1 := by omega
  rw [h1, pow2S, pow2S]; ring

lemma KP_eq (W : ListBlank (Fin 2)) (p p' : Nat) (gs : List Nat) (v v' : Nat) (H : Bool) (St : ListBlank (Fin 2))
    (hp : p = p') (hv : v = v') : KP W p gs v H St = KP W p' gs v' H St := by
  subst hp; subst hv; rfl

lemma stepStar_KP_r {c₁ : Cfg (Fin 2) (Fin 6)} {W : ListBlank (Fin 2)} {p p' : Nat} {gs gs' : List Nat} {v v' : Nat} {H : Bool} {St : ListBlank (Fin 2)}
    (h : c₁ [target_tm]⊢* KP W p gs v H St) (hp : p = p') (hgs : gs = gs') (hv : v = v') :
    c₁ [target_tm]⊢* KP W p' gs' v' H St := by
  subst hp; subst hgs; subst hv; exact h

lemma stepPlus_KP_pow_r {c₁ : Cfg (Fin 2) (Fin 6)} {e e' : Nat} {l : ListBlank (Fin 2)} {p : Nat} {gs : List Nat} {v : Nat} {H : Bool} {St : ListBlank (Fin 2)}
    (h : c₁ [target_tm]⊢⁺ KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ e)) +> l)) p gs v H St) (he : e = e') :
    c₁ [target_tm]⊢⁺ KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ e')) +> l)) p gs v H St := by
  subst he; exact h

lemma stepStar_KP_pow_r {c₁ : Cfg (Fin 2) (Fin 6)} {e e' : Nat} {l : ListBlank (Fin 2)} {p : Nat} {gs : List Nat} {v : Nat} {H : Bool} {St : ListBlank (Fin 2)}
    (h : c₁ [target_tm]⊢* KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ e)) +> l)) p gs v H St) (he : e = e') :
    c₁ [target_tm]⊢* KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ e')) +> l)) p gs v H St := by
  subst he; exact h

lemma stepStar_KP_pow0_r {c₁ : Cfg (Fin 2) (Fin 6)} {l : ListBlank (Fin 2)} {p : Nat} {gs : List Nat} {v : Nat} {H : Bool} {St : ListBlank (Fin 2)}
    (h : c₁ [target_tm]⊢* KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ 0)) +> l)) p gs v H St) :
    c₁ [target_tm]⊢* KP (([1] : List (Fin 2)) +> l) p gs v H St := h

lemma ones_S (gs : List Nat) : (ones gs - 1) + 1 = ones gs := by
  unfold ones
  have hp := pow_pos gs.length
  rw [pow2S]
  omega

lemma ones_lt (gs : List Nat) : ones gs < NN gs := by
  unfold ones NN
  have hp := pow_pos (gs.length + 1)
  omega

lemma NOrb (H : Bool) (r1 : Nat) (St : ListBlank (Fin 2)) (H' : Bool) (r1' : Nat) (St' : ListBlank (Fin 2))
    (G : List Nat) (a : Nat)
    (hov : OvNp H r1 St H' r1' St') (hG : AllGe2 G)
    (hv : gval G + 2 < 2 ^ (G.length + (r1' + 1))) :
    (KP default (a + 2) (gsof G r1) (ones (gsof G r1)) H St) [target_tm]⊢⁺
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ a)) +> default)) 0 (gsof G r1') (2 * gval G + 4) H' St') := by
  have s1 := hov G (a + 2) default
  rw [wallOv] at s1
  have hGr : AllGe2 G.reverse := AllGe2_rev G hG
  have hz : zv G.reverse 0 < 2 ^ (((rep 1 r1').length + 1) + G.reverse.length) := by
    rw [zv_rev, rep_length, List.length_reverse]
    have heq : (r1' + 1) + G.length = G.length + (r1' + 1) := by omega
    rw [heq]; omega
  have s2 := Zones G.reverse hGr ([1, 0, 0, 1] ++ pl (rep .PZ (a + 2) ++ [.P])) default 0 (rep 1 r1') 0 H' St' hz
  have hx : zv G.reverse 0 + 2 < NN (zg G.reverse 0 (rep 1 r1')) := by
    unfold NN
    rw [zg_len, zv_rev, rep_length, List.length_reverse]
    have heq : (G.length + r1') + 1 = G.length + (r1' + 1) := by omega
    rw [heq]; exact hv
  have s3 := ZXN a default (zp G.reverse 0) (zg G.reverse 0 (rep 1 r1')) (zv G.reverse 0) H' St' hx
  have s23 := stepStar_trans s2 s3
  have s23' := stepStar_KP_r s23 rfl (zg_rev G (rep 1 r1') hG)
    (by rw [zv_rev]; omega : 2 * (zv G.reverse 0 + 2) = 2 * gval G + 4)
  exact stepPlus_stepStar_stepPlus s1 s23'

lemma POrb (H : Bool) (r1 : Nat) (St : ListBlank (Fin 2)) (H' : Bool) (r1' : Nat) (St' : ListBlank (Fin 2))
    (G : List Nat) (p n : Nat) (l0 : ListBlank (Fin 2))
    (hov : OvNp H r1 St H' r1' St') (hG : AllGe2 G) (hp : 2 ≤ p)
    (hv : 2 * gval G + 2 * p + 3 < 2 ^ (G.length + (r1' + 2))) :
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 3))) +> l0)) p (gsof G r1) (ones (gsof G r1) - 1) H St) [target_tm]⊢*
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l0)) 0 (gsof (((p - 2) + 1) :: G) r1') (2 * (2 * gval G + 2 * p + 3)) H' St') := by
  have hI : (ones (gsof G r1) - 1) + 1 < 2 ^ ((gsof G r1).length + 1) := by
    rw [ones_S]; exact ones_lt (gsof G r1)
  have s1 := IncL (gsof G r1) (ones (gsof G r1) - 1) p hI ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 3))) +> l0)) St (sfx H)
  rw [ones_S] at s1
  have hL1 : (([1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 3))) +> l0) =
      (([1, 0] : List (Fin 2)) +> ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 2))) +> l0))) := by
    rw [list_pow_succ]; simp only [List.cons_append, List.nil_append, listblank_append_cons, listblank_append_nil]
  rw [hL1] at s1
  have s2 := B1 ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 2))) +> l0))
    (tw (.T0 :: (rep .TZ p ++ (ctr (gsof G r1) (ones (gsof G r1)) ++ sfx H))) +> St)
  have s3 := stepPlus_stepStar (hov G p (([0, 0] : List (Fin 2)) +> ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 2))) +> l0))))
  rw [wallOv] at s3
  have hL2 : (([0, 0] : List (Fin 2)) +> ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 2))) +> l0))) =
      ((([0, 0, 0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 2))) +> l0)) := by
    simp only [List.cons_append, List.nil_append, listblank_append_cons, listblank_append_nil]
  rw [hL2, wallPO] at s3
  have hGr : AllGe2 (G.reverse ++ [p]) := AllGe2_app G.reverse [p] (AllGe2_rev G hG) ⟨hp, trivial⟩
  have hz : zv (G.reverse ++ [p]) 0 < 2 ^ (((rep 1 r1').length + 1) + (G.reverse ++ [p]).length) := by
    rw [zv_rev_last, rep_length, List.length_append, List.length_reverse]
    simp only [List.length_singleton]
    have heq : (r1' + 1) + (G.length + 1) = G.length + (r1' + 2) := by omega
    rw [heq]; omega
  have s4 := Zones (G.reverse ++ [p]) hGr (([0, 0, 1] : List (Fin 2)) ^ (n + 3)) l0 0 (rep 1 r1') 0 H' St' hz
  have hx : zv (G.reverse ++ [p]) 0 + 3 < NN (zg (G.reverse ++ [p]) 0 (rep 1 r1')) := by
    unfold NN
    rw [zg_len, zv_rev_last, rep_length, List.length_append, List.length_reverse]
    simp only [List.length_singleton]
    have heq : ((G.length + 1) + r1') + 1 = G.length + (r1' + 2) := by omega
    rw [heq]; exact hv
  have s5 := ZXP n l0 (zp (G.reverse ++ [p]) 0) (zg (G.reverse ++ [p]) 0 (rep 1 r1')) (zv (G.reverse ++ [p]) 0) H' St' hx
  have s45 := stepStar_trans s4 s5
  have hgs : (zp (G.reverse ++ [p]) 0 + 1) :: zg (G.reverse ++ [p]) 0 (rep 1 r1') = gsof (((p - 2) + 1) :: G) r1' := by
    rw [zp_rev_last, zg_rev_last G p (rep 1 r1') hG]; rfl
  have s45' := stepStar_KP_r s45 rfl hgs (by rw [zv_rev_last])
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 s45'))

lemma SILENTP (r1 : Nat) (St St' : ListBlank (Fin 2)) (G : List Nat) (p n : Nat) (l0 : ListBlank (Fin 2))
    (hov : OvSp r1 St St') :
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 1))) +> l0)) p (gsof G r1) (ones (gsof G r1) - 1) true St) [target_tm]⊢*
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l0)) (p + 1) (gsof G r1) 0 true St') := by
  have hI : (ones (gsof G r1) - 1) + 1 < 2 ^ ((gsof G r1).length + 1) := by
    rw [ones_S]; exact ones_lt (gsof G r1)
  have s1 := IncL (gsof G r1) (ones (gsof G r1) - 1) p hI ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 1))) +> l0)) St (sfx true)
  rw [ones_S] at s1
  have hL1 : (([1] ++ (([0, 0, 1] : List (Fin 2)) ^ (n + 1))) +> l0) =
      (([1, 0] : List (Fin 2)) +> ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l0))) := by
    rw [list_pow_succ]; simp only [List.cons_append, List.nil_append, listblank_append_cons, listblank_append_nil]
  rw [hL1] at s1
  have s2 := B1 ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l0))
    (tw (.T0 :: (rep .TZ p ++ (ctr (gsof G r1) (ones (gsof G r1)) ++ sfx true))) +> St)
  have s3 := stepPlus_stepStar (hov G p (([0, 0] : List (Fin 2)) +> ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l0))))
  have s4 := ENDl ((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l0)) (tw (.T0 :: (rep .TZ p ++ (ctr (gsof G r1) 0 ++ sfx true))) +> St')
  have h_s4 : (((([0, 1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l0)) <{{A}} (([0, 1] : List (Fin 2)) +> (tw (.T0 :: (rep .TZ p ++ (ctr (gsof G r1) 0 ++ sfx true))) +> St'))) =
      (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ n)) +> l0)) (p + 1) (gsof G r1) 0 true St') := by
    unfold KP
    simp only [rep, List.cons_append, tw_T0_cons', tw_TZ_cons', listblank_append_cons, listblank_append_nil, ListBlank.head_cons, ListBlank.tail_cons]
  rw [h_s4] at s4
  exact stepStar_trans s1 (stepStar_trans s2 (stepStar_trans s3 s4))

lemma SILENT (r1 : Nat) (St St' : ListBlank (Fin 2)) (G : List Nat) (a : Nat)
    (hov : OvSp r1 St St') :
    (KP default (a + 1) (gsof G r1) (ones (gsof G r1)) true St) [target_tm]⊢⁺
    (KP default (a + 2) (gsof G r1) 0 true St') := by
  have s1 := hov G (a + 1) default
  have s2 := Bnc_TZ a (ctr (gsof G r1) 0 ++ sfx true) St'
  exact stepPlus_stepStar_stepPlus s1 s2

def KX (a : Nat) (G : List Nat) (r1 : Nat) (St : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  KP default a (gsof G r1) (ones (gsof G r1)) true St

-- ============================================================================
-- Macro-Step Paths (`pathS`, `pre1`, `pathP1`, `pathP1S`, `pathP3`)
-- ============================================================================

lemma pathS (a : Nat) (G : List Nat) (r1 : Nat) (St St' : ListBlank (Fin 2))
    (hov : OvSp r1 St St') (ha : 1 ≤ a) :
    (KX a G r1 St) [target_tm]⊢⁺ (KX (a + 4 * 2 ^ (G.length + r1)) G r1 St') := by
  unfold KX
  have hO := ones_gsof G r1
  have hN := NN_gsof G r1
  have hP := pow_pos (G.length + r1)
  have ha1 : a = (a - 1) + 1 := by omega
  rw [ha1]
  have s1 := SILENT r1 St St' G (a - 1) hov
  have s2 := Incs (ones (gsof G r1)) (a - 1 + 1) (gsof G r1) 0 true St' (by omega)
  have s2' := stepStar_KP_r s2
    (by omega : ones (gsof G r1) + (a - 1 + 1 + 1) = a - 1 + 1 + 4 * 2 ^ (G.length + r1))
    rfl
    (by omega : ones (gsof G r1) + 0 = ones (gsof G r1))
  exact stepPlus_stepStar_stepPlus s1 s2'

def TailF (St S0 : ListBlank (Fin 2)) : Prop :=
  ∀ l', (l' {{C}}> St) [target_tm]⊢* (l' <{{F}} (([0, 0] : List (Fin 2)) +> S0))

lemma pre1 (a : Nat) (G : List Nat) (r1 : Nat) (St St1 S0 : ListBlank (Fin 2)) (kap s : Nat)
    (hov1 : OvNp true r1 St false r1 St1) (ht2 : TailF St1 S0)
    (hG : AllGe2 G) (hV : gval G + 6 + kap = 2 ^ (G.length + r1))
    (ha : a = s + 2 ^ (G.length + r1) + kap) (hs : 8 ≤ s) :
    (KX a G r1 St) [target_tm]⊢⁺
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ (s - 8))) +> default)) 0
      (gsof ((2 ^ (G.length + r1) + 2 + kap) :: G) (r1 + 1))
      (8 * 2 ^ (G.length + r1) - 6) true (([0, 1] : List (Fin 2)) +> S0)) := by
  unfold KX
  let Q := 2 ^ (G.length + r1)
  have hO : ones (gsof G r1) = 4 * Q - 1 := ones_gsof G r1
  have hN : NN (gsof G r1) = 4 * Q := NN_gsof G r1
  have hP : 0 < Q := pow_pos (G.length + r1)
  have ha2 : a = (a - 2) + 2 := by omega
  rw [ha2]
  have hNOrb_cond : gval G + 2 < 2 ^ (G.length + (r1 + 1)) := by
    rw [pS]; change gval G + 2 < 2 * Q; omega
  have s1 := NOrb true r1 St false r1 St1 G (a - 2) hov1 hG hNOrb_cond
  have ha_split : a - 2 = (Q + 3 + kap) + ((s - 8) + 3) := by omega
  have s1' := stepPlus_KP_pow_r s1 ha_split
  have s2 := P100s (Q + 3 + kap) ((s - 8) + 3) default 0 (gsof G r1) (2 * gval G + 4) false St1 (by omega)
  have s2' := stepStar_KP_r s2
    (by omega : (Q + 3 + kap) + 0 = Q + 3 + kap)
    rfl
    (by omega : 2 * (Q + 3 + kap) + (2 * gval G + 4) = ones (gsof G r1) - 1)
  have hPOrb_cond : 2 * gval G + 2 * (Q + 3 + kap) + 3 < 2 ^ (G.length + (r1 + 1 + 2)) := by
    have hpow : 2 ^ (G.length + (r1 + 1 + 2)) = 8 * Q := by
      have : G.length + (r1 + 1 + 2) = ((G.length + r1) + 1) + 1 + 1 := by omega
      rw [this, pow2S, pow2S, pow2S]; ring
    rw [hpow]; omega
  have hov0 := OvNp0 r1 St1 S0 ht2
  have hp_cond : 2 ≤ Q + 3 + kap := by omega
  have s3 := POrb false r1 St1 true (r1 + 1) (([0, 1] : List (Fin 2)) +> S0) G (Q + 3 + kap) (s - 8) default
    hov0 hG hp_cond hPOrb_cond
  have hsub : (Q + 3 + kap - 2) + 1 = Q + 2 + kap := by omega
  have s3' := stepStar_KP_r s3 rfl (by rw [hsub])
    (by omega : 2 * (2 * gval G + 2 * (Q + 3 + kap) + 3) = 8 * Q - 6)
  have s23 := stepStar_trans s2' s3'
  exact stepPlus_stepStar_stepPlus s1' s23

lemma pathP1 (a : Nat) (G : List Nat) (r1 : Nat) (St St1 S0 : ListBlank (Fin 2)) (kap s : Nat)
    (hov1 : OvNp true r1 St false r1 St1) (ht2 : TailF St1 S0)
    (hG : AllGe2 G) (hV : gval G + 6 + kap = 2 ^ (G.length + r1))
    (ha : a = s + 2 ^ (G.length + r1) + kap) (hs1 : 8 ≤ s) (hs2 : s ≤ 4 * 2 ^ (G.length + r1) + 9) :
    (KX a G r1 St) [target_tm]⊢⁺
    (KX (8 * 2 ^ (G.length + r1) + 12 - s) ((2 ^ (G.length + r1) + 2 + kap) :: G) (r1 + 1) (([0, 1] : List (Fin 2)) +> S0)) := by
  let Q := 2 ^ (G.length + r1)
  let G' := (Q + 2 + kap) :: G
  have hP : 0 < Q := pow_pos (G.length + r1)
  have hN : NN (gsof G' (r1 + 1)) = 16 * Q := by
    rw [NN_gsof]; unfold G'; rw [Q_cons]; change 4 * (4 * Q) = 16 * Q; omega
  have hO : ones (gsof G' (r1 + 1)) = 16 * Q - 1 := by
    rw [ones_gsof]; unfold G'; rw [Q_cons]; change 4 * (4 * Q) - 1 = 16 * Q - 1; omega
  have s1 := pre1 a G r1 St St1 S0 kap s hov1 ht2 hG hV ha hs1
  have s1' := stepPlus_KP_pow_r s1 (by omega : s - 8 = (s - 8) + 0)
  have s2 := P100s (s - 8) 0 default 0 (gsof G' (r1 + 1)) (8 * Q - 6) true (([0, 1] : List (Fin 2)) +> S0) (by omega)
  have s2' := stepStar_KP_r (stepStar_KP_pow0_r s2) (by omega : (s - 8) + 0 = s - 8) rfl rfl
  have s3 := WX (s - 8) (gsof G' (r1 + 1)) (2 * (s - 8) + (8 * Q - 6)) true (([0, 1] : List (Fin 2)) +> S0) (by omega)
  have s4 := Incs (8 * Q + 19 - 2 * s) (s - 8) (gsof G' (r1 + 1)) (2 * (s - 8) + (8 * Q - 6) + 2) true (([0, 1] : List (Fin 2)) +> S0) (by omega)
  unfold KX
  have s4' := stepStar_KP_r s4
    (by omega : (8 * Q + 19 - 2 * s) + (s - 8 + 1) = 8 * Q + 12 - s)
    rfl
    (by omega : (8 * Q + 19 - 2 * s) + (2 * (s - 8) + (8 * Q - 6) + 2) = ones (gsof G' (r1 + 1)))
  have s34 := stepStar_trans s3 s4'
  have s234 := stepStar_trans s2' s34
  exact stepPlus_stepStar_stepPlus s1' s234

lemma pathP1S (a : Nat) (G : List Nat) (r1 : Nat) (St St1 S0 St3 : ListBlank (Fin 2)) (kap s : Nat)
    (hov1 : OvNp true r1 St false r1 St1) (ht2 : TailF St1 S0) (hov3 : OvSp (r1 + 1) (([0, 1] : List (Fin 2)) +> S0) St3)
    (hG : AllGe2 G) (hV : gval G + 6 + kap = 2 ^ (G.length + r1))
    (ha : a = s + 2 ^ (G.length + r1) + kap) (hs1 : 4 * 2 ^ (G.length + r1) + 11 ≤ s) (hs2 : s ≤ 12 * 2 ^ (G.length + r1) + 9) :
    (KX a G r1 St) [target_tm]⊢⁺
    (KX (24 * 2 ^ (G.length + r1) + 12 - s) ((2 ^ (G.length + r1) + 2 + kap) :: G) (r1 + 1) St3) := by
  let Q := 2 ^ (G.length + r1)
  let G' := (Q + 2 + kap) :: G
  have hP : 0 < Q := pow_pos (G.length + r1)
  have hN : NN (gsof G' (r1 + 1)) = 16 * Q := by
    rw [NN_gsof]; unfold G'; rw [Q_cons]; change 4 * (4 * Q) = 16 * Q; omega
  have hO : ones (gsof G' (r1 + 1)) = 16 * Q - 1 := by
    rw [ones_gsof]; unfold G'; rw [Q_cons]; change 4 * (4 * Q) - 1 = 16 * Q - 1; omega
  have s1 := pre1 a G r1 St St1 S0 kap s hov1 ht2 hG hV ha (by omega)
  have hs_split : s - 8 = (4 * Q + 2) + ((s - 4 * Q - 11) + 1) := by omega
  have s1' := stepPlus_KP_pow_r s1 hs_split
  have s2 := P100s (4 * Q + 2) ((s - 4 * Q - 11) + 1) default 0 (gsof G' (r1 + 1)) (8 * Q - 6) true (([0, 1] : List (Fin 2)) +> S0) (by omega)
  have s2' := stepStar_KP_r s2
    (by omega : (4 * Q + 2) + 0 = 4 * Q + 2)
    rfl
    (by omega : 2 * (4 * Q + 2) + (8 * Q - 6) = ones (gsof G' (r1 + 1)) - 1)
  have s3 := SILENTP (r1 + 1) (([0, 1] : List (Fin 2)) +> S0) St3 G' (4 * Q + 2) (s - 4 * Q - 11) default hov3
  have s3' := stepStar_KP_pow_r s3 (by omega : s - 4 * Q - 11 = (s - 4 * Q - 11) + 0)
  have s4 := P100s (s - 4 * Q - 11) 0 default (4 * Q + 2 + 1) (gsof G' (r1 + 1)) 0 true St3 (by omega)
  have s4' := stepStar_KP_r (stepStar_KP_pow0_r s4) rfl rfl
    (by omega : 2 * (s - 4 * Q - 11) + 0 = 2 * (s - 4 * Q - 11))
  have s5 := WX ((s - 4 * Q - 11) + (4 * Q + 2 + 1)) (gsof G' (r1 + 1)) (2 * (s - 4 * Q - 11)) true St3 (by omega)
  have s6 := Incs (24 * Q + 19 - 2 * s) ((s - 4 * Q - 11) + (4 * Q + 2 + 1)) (gsof G' (r1 + 1)) (2 * (s - 4 * Q - 11) + 2) true St3 (by omega)
  unfold KX
  have s6' := stepStar_KP_r s6
    (by omega : (24 * Q + 19 - 2 * s) + ((s - 4 * Q - 11) + (4 * Q + 2 + 1) + 1) = 24 * Q + 12 - s)
    rfl
    (by omega : (24 * Q + 19 - 2 * s) + (2 * (s - 4 * Q - 11) + 2) = ones (gsof G' (r1 + 1)))
  have s56 := stepStar_trans s5 s6'
  have s456 := stepStar_trans s4' s56
  have s3456 := stepStar_trans s3' s456
  have s23456 := stepStar_trans s2' s3456
  exact stepPlus_stepStar_stepPlus s1' s23456

lemma pathP3 (a : Nat) (G : List Nat) (r1 : Nat) (St St1 S0 St3 S4 : ListBlank (Fin 2)) (kap s : Nat)
    (hov1 : OvNp true r1 St false r1 St1) (ht2 : TailF St1 S0)
    (hov3 : OvNp true (r1 + 1) (([0, 1] : List (Fin 2)) +> S0) false (r1 + 1) St3) (ht4 : TailF St3 S4)
    (hG : AllGe2 G) (hV : gval G + 6 + kap = 2 ^ (G.length + r1))
    (ha : a = s + 2 ^ (G.length + r1) + kap) (hs1 : 4 * 2 ^ (G.length + r1) + 24 ≤ s) (hs2 : s ≤ 36 * 2 ^ (G.length + r1) + 31) :
    (KX a G r1 St) [target_tm]⊢⁺
    (KX (68 * 2 ^ (G.length + r1) + 40 - s) (7 :: (4 * 2 ^ (G.length + r1) + 1) :: (2 ^ (G.length + r1) + 2 + kap) :: G)
      (r1 + 2) (([0, 1] : List (Fin 2)) +> S4)) := by
  let Q := 2 ^ (G.length + r1)
  let G' := (Q + 2 + kap) :: G
  let G'' := (4 * Q + 1) :: G'
  let G3 := 7 :: G''
  have hP : 0 < Q := pow_pos (G.length + r1)
  have hN : NN (gsof G' (r1 + 1)) = 16 * Q := by
    rw [NN_gsof]; unfold G'; rw [Q_cons]; change 4 * (4 * Q) = 16 * Q; omega
  have hO : ones (gsof G' (r1 + 1)) = 16 * Q - 1 := by
    rw [ones_gsof]; unfold G'; rw [Q_cons]; change 4 * (4 * Q) - 1 = 16 * Q - 1; omega
  have hG' : AllGe2 G' := ⟨by omega, hG⟩
  have hV' : gval G' = 4 * Q - 8 := by simp [G', gval]; omega
  have s1 := pre1 a G r1 St St1 S0 kap s hov1 ht2 hG hV ha (by omega)
  have hs_split1 : s - 8 = (4 * Q + 2) + ((s - 4 * Q - 13) + 3) := by omega
  have s1' := stepPlus_KP_pow_r s1 hs_split1
  have s2 := P100s (4 * Q + 2) ((s - 4 * Q - 13) + 3) default 0 (gsof G' (r1 + 1)) (8 * Q - 6) true (([0, 1] : List (Fin 2)) +> S0) (by omega)
  have s2' := stepStar_KP_r s2
    (by omega : (4 * Q + 2) + 0 = 4 * Q + 2)
    rfl
    (by omega : 2 * (4 * Q + 2) + (8 * Q - 6) = ones (gsof G' (r1 + 1)) - 1)
  have hPOrb1 : 2 * gval G' + 2 * (4 * Q + 2) + 3 < 2 ^ (G'.length + (r1 + 1 + 2)) := by
    have hpow : 2 ^ (G'.length + (r1 + 1 + 2)) = 16 * Q := by
      simp only [G', List.length_cons]
      have : (G.length + 1) + (r1 + 1 + 2) = (((G.length + r1) + 1) + 1) + 1 + 1 := by omega
      rw [this, pow2S, pow2S, pow2S, pow2S]; ring
    rw [hpow]; omega
  have hp1 : 2 ≤ 4 * Q + 2 := by omega
  have s3 := POrb true (r1 + 1) (([0, 1] : List (Fin 2)) +> S0) false (r1 + 1) St3 G' (4 * Q + 2) (s - 4 * Q - 13) default
    hov3 hG' hp1 hPOrb1
  have hsub1 : (4 * Q + 2 - 2) + 1 = 4 * Q + 1 := by omega
  have hs_split2 : s - 4 * Q - 13 = 8 + ((s - 4 * Q - 24) + 3) := by omega
  have s3' := stepStar_KP_pow_r (stepStar_KP_r s3 rfl (by rw [hsub1]) rfl) hs_split2
  have hN2 : NN (gsof G'' (r1 + 1)) = 32 * Q := by
    rw [NN_gsof]; simp only [G'', G', List.length_cons]
    have : ((G.length + 1) + 1) + (r1 + 1) = (((G.length + r1) + 1) + 1) + 1 := by omega
    rw [this, pow2S, pow2S, pow2S]; ring
  have hO2 : ones (gsof G'' (r1 + 1)) = 32 * Q - 1 := by unfold ones NN at *; omega
  have hG'' : AllGe2 G'' := ⟨by omega, hG'⟩
  have hV'' : gval G'' = 16 * Q - 14 := by simp [G'', gval, hV']; omega
  have s4 := P100s 8 ((s - 4 * Q - 24) + 3) default 0 (gsof G'' (r1 + 1))
    (2 * (2 * gval G' + 2 * (4 * Q + 2) + 3)) false St3 (by omega)
  have s4' := stepStar_KP_r s4
    (by omega : 8 + 0 = 8)
    rfl
    (by omega : 2 * 8 + 2 * (2 * gval G' + 2 * (4 * Q + 2) + 3) = ones (gsof G'' (r1 + 1)) - 1)
  have hPOrb2 : 2 * gval G'' + 2 * 8 + 3 < 2 ^ (G''.length + (r1 + 1 + 1 + 2)) := by
    have hpow : 2 ^ (G''.length + (r1 + 1 + 1 + 2)) = 64 * Q := by
      simp only [G'', G', List.length_cons]
      have : ((G.length + 1) + 1) + (r1 + 1 + 1 + 2) = (((((G.length + r1) + 1) + 1) + 1) + 1) + 1 + 1 := by omega
      rw [this, pow2S, pow2S, pow2S, pow2S, pow2S, pow2S]; ring
    rw [hpow]; omega
  have hov0 := OvNp0 (r1 + 1) St3 S4 ht4
  have hp2 : 2 ≤ 8 := by omega
  have s5 := POrb false (r1 + 1) St3 true (r1 + 2) (([0, 1] : List (Fin 2)) +> S4) G'' 8 (s - 4 * Q - 24) default
    hov0 hG'' hp2 hPOrb2
  have hsub2 : (8 - 2) + 1 = 7 := rfl
  have s5' := stepStar_KP_pow_r (stepStar_KP_r s5 rfl (by rw [hsub2]) rfl) (by omega : s - 4 * Q - 24 = (s - 4 * Q - 24) + 0)
  have hN3 : NN (gsof G3 (r1 + 2)) = 128 * Q := by
    rw [NN_gsof]; simp only [G3, G'', G', List.length_cons]
    have : (((G.length + 1) + 1) + 1) + (r1 + 2) = ((((G.length + r1) + 1) + 1) + 1) + 1 + 1 := by omega
    rw [this, pow2S, pow2S, pow2S, pow2S, pow2S]; ring
  have hO3 : ones (gsof G3 (r1 + 2)) = 128 * Q - 1 := by unfold ones NN at *; omega
  have s6 := P100s (s - 4 * Q - 24) 0 default 0 (gsof G3 (r1 + 2)) (2 * (2 * gval G'' + 2 * 8 + 3)) true (([0, 1] : List (Fin 2)) +> S4) (by omega)
  have s6' := stepStar_KP_r (stepStar_KP_pow0_r s6) (by omega : (s - 4 * Q - 24) + 0 = s - 4 * Q - 24) rfl rfl
  have s7 := WX (s - 4 * Q - 24) (gsof G3 (r1 + 2)) (2 * (s - 4 * Q - 24) + 2 * (2 * gval G'' + 2 * 8 + 3)) true (([0, 1] : List (Fin 2)) +> S4) (by omega)
  have s8 := Incs (72 * Q + 63 - 2 * s) (s - 4 * Q - 24) (gsof G3 (r1 + 2))
    (2 * (s - 4 * Q - 24) + 2 * (2 * gval G'' + 2 * 8 + 3) + 2) true (([0, 1] : List (Fin 2)) +> S4) (by omega)
  unfold KX
  have s8' := stepStar_KP_r s8
    (by omega : (72 * Q + 63 - 2 * s) + (s - 4 * Q - 24 + 1) = 68 * Q + 40 - s)
    rfl
    (by omega : (72 * Q + 63 - 2 * s) + (2 * (s - 4 * Q - 24) + 2 * (2 * gval G'' + 2 * 8 + 3) + 2) = ones (gsof G3 (r1 + 2)))
  have s78 := stepStar_trans s7 s8'
  have s678 := stepStar_trans s6' s78
  have s5678 := stepStar_trans s5' s678
  have s45678 := stepStar_trans s4' s5678
  have s345678 := stepStar_trans s3' s45678
  have s2345678 := stepStar_trans s2' s345678
  exact stepPlus_stepStar_stepPlus s1' s2345678

-- ============================================================================
-- Global Invariant (`INV`), Step Closure (`step`), and Non-Halting (`nonhalt`)
-- ============================================================================

def INV (a : Nat) (G : List Nat) (r1 : Nat) (St : ListBlank (Fin 2)) : Prop :=
  AllGe2 G ∧ 64 ≤ 2 ^ (G.length + r1) ∧
  ∃ kap s, (kap = 2 ∨ kap = 8) ∧ gval G + 6 + kap = 2 ^ (G.length + r1) ∧
    a = s + 2 ^ (G.length + r1) + kap ∧
    ((Lst true true St ∧ 24 ≤ s ∧ s ≤ 2 ^ (G.length + r1) + 2) ∨
     (Lst true false St ∧ ((8 ≤ s ∧ s ≤ 4 * 2 ^ (G.length + r1) - 14) ∨
                           (4 * 2 ^ (G.length + r1) + 24 ≤ s ∧ s ≤ 8 * 2 ^ (G.length + r1)))))

lemma Lst_tailx (y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) (e : List Bool) :
    Lst y z (([0, 1] : List (Fin 2)) +> (tw (tailx y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default)) :=
  Lst_intro y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e _ (tw_T1_cons _ default)

lemma Q1 (g : Nat) (G : List Nat) (r1 : Nat) : 2 ^ ((g :: G).length + (r1 + 1)) = 4 * 2 ^ (G.length + r1) :=
  Q_cons g G r1

lemma Q3 (g1 g2 g3 : Nat) (G : List Nat) (r1 : Nat) :
    2 ^ ((g1 :: g2 :: g3 :: G).length + (r1 + 2)) = 32 * 2 ^ (G.length + r1) := by
  simp only [List.length_cons]
  have : (((G.length + 1) + 1) + 1) + (r1 + 2) = ((((G.length + r1) + 1) + 1) + 1) + 1 + 1 := by omega
  rw [this, pow2S, pow2S, pow2S, pow2S, pow2S]; ring

lemma step_inv (a : Nat) (G : List Nat) (r1 : Nat) (St : ListBlank (Fin 2)) (hinv : INV a G r1 St) :
    ∃ a' G' r1' St', ((KX a G r1 St) [target_tm]⊢⁺ (KX a' G' r1' St')) ∧ INV a' G' r1' St' := by
  rcases hinv with ⟨hG, hQ, kap, s, hk, hV, ha, ht⟩
  let Q := 2 ^ (G.length + r1)
  have hQ_def : 2 ^ (G.length + r1) = Q := rfl
  rcases ht with ⟨hL, hs1, hs2⟩ | ⟨hL, hs⟩
  · rcases hL with ⟨b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, e, rfl⟩
    rcases Tail11 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e with ⟨S', hE, hL'⟩ | ⟨S0, hF, hL'⟩
    · rcases hL' with ⟨c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, e', rfl⟩
      let S0 := tw (tailx true false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e') +> default
      have ht2 : TailF (tw (tailw true false false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e') +> default) S0 :=
        fun l => Tail0z l false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e'
      refine ⟨8 * Q + 12 - s, (Q + 2 + kap) :: G, r1 + 1, ([0, 1] : List (Fin 2)) +> S0, ?_, ?_⟩
      · exact pathP1 a G r1 _ _ S0 kap s (OvNp1 r1 _ _ hE) ht2 hG hV ha (by omega) (by omega)
      · refine ⟨⟨by omega, hG⟩, ?_, 2, 4 * Q + 10 - s, Or.inl rfl, ?_, ?_, Or.inr ⟨Lst_tailx true false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e', Or.inl ⟨?_, ?_⟩⟩⟩
        · rw [Q1, hQ_def]; omega
        · rw [Q1, hQ_def]; simp [gval]; omega
        · rw [Q1, hQ_def]; omega
        · omega
        · rw [Q1, hQ_def]; omega
    · refine ⟨a + 4 * Q, G, r1, ([0, 1] : List (Fin 2)) +> S0, ?_, ?_⟩
      · exact pathS a G r1 _ _ (OvSp1 r1 _ S0 hF) (by omega)
      · refine ⟨hG, hQ, kap, s + 4 * Q, hk, hV, by omega, Or.inr ⟨hL', Or.inr ⟨by omega, by omega⟩⟩⟩
  · rcases hL with ⟨b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, e, rfl⟩
    let St1 := tw (tailw true false true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default
    have hE : ∀ l, (l {{C}}> (tw (tailw true true false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default)) [target_tm]⊢*
        (l <{{E}} St1) := fun l => Tail10 l b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e
    let S0 := tw (tailx true true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) +> default
    have ht2 : TailF St1 S0 := fun l => Tail0z l true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e
    rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
    · refine ⟨8 * Q + 12 - s, (Q + 2 + kap) :: G, r1 + 1, ([0, 1] : List (Fin 2)) +> S0, ?_, ?_⟩
      · exact pathP1 a G r1 _ St1 S0 kap s (OvNp1 r1 _ _ hE) ht2 hG hV ha (by omega) (by omega)
      · refine ⟨⟨by omega, hG⟩, ?_, 2, 4 * Q + 10 - s, Or.inl rfl, ?_, ?_, Or.inl ⟨Lst_tailx true true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e, ?_, ?_⟩⟩
        · rw [Q1, hQ_def]; omega
        · rw [Q1, hQ_def]; simp [gval]; omega
        · rw [Q1, hQ_def]; omega
        · omega
        · rw [Q1, hQ_def]; omega
    · rcases Tail11 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e with ⟨S3, hE3, hL3⟩ | ⟨S3, hF3, hL3⟩
      · rcases hL3 with ⟨c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, e', rfl⟩
        let S4 := tw (tailx true false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e') +> default
        have ht4 : TailF (tw (tailw true false false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e') +> default) S4 :=
          fun l => Tail0z l false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e'
        refine ⟨68 * Q + 40 - s, 7 :: (4 * Q + 1) :: (Q + 2 + kap) :: G, r1 + 2, ([0, 1] : List (Fin 2)) +> S4, ?_, ?_⟩
        · exact pathP3 a G r1 _ St1 S0 _ S4 kap s (OvNp1 r1 _ _ hE) ht2 (OvNp1 (r1 + 1) _ _ hE3) ht4 hG hV ha (by omega) (by omega)
        · refine ⟨⟨by omega, ⟨by omega, ⟨by omega, hG⟩⟩⟩, ?_, 8, 36 * Q + 32 - s, Or.inr rfl, ?_, ?_, Or.inr ⟨Lst_tailx true false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e', Or.inl ⟨?_, ?_⟩⟩⟩
          · rw [Q3, hQ_def]; omega
          · rw [Q3, hQ_def]; simp [gval]; omega
          · rw [Q3, hQ_def]; omega
          · omega
          · rw [Q3, hQ_def]; omega
      · refine ⟨24 * Q + 12 - s, (Q + 2 + kap) :: G, r1 + 1, ([0, 1] : List (Fin 2)) +> S3, ?_, ?_⟩
        · exact pathP1S a G r1 _ St1 S0 _ kap s (OvNp1 r1 _ _ hE) ht2 (OvSp1 (r1 + 1) _ S3 hF3) hG hV ha (by omega) (by omega)
        · refine ⟨⟨by omega, hG⟩, ?_, 2, 20 * Q + 10 - s, Or.inl rfl, ?_, ?_, Or.inr ⟨hL3, Or.inl ⟨?_, ?_⟩⟩⟩
          · rw [Q1, hQ_def]; omega
          · rw [Q1, hQ_def]; simp [gval]; omega
          · rw [Q1, hQ_def]; omega
          · omega
          · rw [Q1, hQ_def]; omega

def St0 : ListBlank (Fin 2) :=
  tw (tailw true true true true true true false true true true true false true false true [false, true, false]) +> default

lemma W1 (p : Nat) (gs : List Nat) (v : Nat) (H : Bool) (St : ListBlank (Fin 2))
    (hv : v + 1 < NN gs) :
    (KP (([1] : List (Fin 2)) +> default) p gs v H St) [target_tm]⊢*
    (KP default p gs (v + 1) H St) := by
  unfold KP
  have h1 : (([1] : List (Fin 2)) +> (default : ListBlank (Fin 2))) = (([1, 0] : List (Fin 2)) +> default) := by
    simp only [listblank_append_cons, listblank_append_nil, zero_cons_default]
  have h2 : (([0, 0] : List (Fin 2)) +> (default : ListBlank (Fin 2))) = default := by
    simp only [listblank_append_cons, listblank_append_nil, zero_cons_default]
  rw [h1]
  have s1 := IncL gs v p hv (([1, 0] : List (Fin 2)) +> default) St (sfx H)
  have s2 := B1 default (tw (.T0 :: (rep .TZ p ++ (ctr gs (v + 1) ++ sfx H))) +> St)
  rw [h2] at s2
  exact stepStar_trans s1 s2


-- ============================================================================
-- Bignum-Accelerated NatCfg Simulator (`NatSim`)
-- ============================================================================

open BusyBeaver.Longitudinal

def St_5786 : ListBlank (Fin 2) :=
  tw (tailw true true true false true true false true true true true false true false true [false, true, false]) +> default

def St_6060 : ListBlank (Fin 2) :=
  tw (tailw true false false true true true false true true true true false true false true [false, true, false]) +> default

def S0_6060 : ListBlank (Fin 2) :=
  tw (tailx true false true true true false true true true true false true false true [false, true, false]) +> default

def St_17206 : ListBlank (Fin 2) :=
  tw (tailw true true false true true true false true true true true false true false true [false, true, false]) +> default

def St_17206_1 : ListBlank (Fin 2) :=
  tw (tailw true false true true true true false true true true true false true false true [false, true, false]) +> default

def S0_17206 : ListBlank (Fin 2) :=
  tw (tailx true true true true true false true true true true false true false true [false, true, false]) +> default

theorem init_4353 :
    multiStep target_tm (init []) 4353 =
      some (NatCfg.toCfg ⟨0, 0, 2396745, 726013156963562508614058902102144551304⟩) := by
  rw [← toCfg_zero]
  exact stepsNat_sound target_tm 4353 ⟨0, 0, 0, 0⟩ _ (by decide +kernel) (by decide)

lemma init_to_4353_cfg_eq :
    NatCfg.toCfg (K := 6) ⟨0, 0, 2396745, 726013156963562508614058902102144551304⟩ =
      KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ 7)) +> default)) 0 (gsof [] 3) 10 true St_5786 := by
  have hcfg := toCfg_headRight A 2396745 1452026313927125017228117804204289102608
  have hl : (([1] ++ (([0, 0, 1] : List (Fin 2)) ^ 7)) +> default) = decodeHalf 2396745 := by
    rw [← decodeHalf_zero, decodeHalf_encodeList]
    rfl
  have hr : tw (.T0 :: (rep .TZ 0 ++ (ctr (gsof [] 3) 10 ++ sfx true))) +> St_5786 =
      decodeHalf 1452026313927125017228117804204289102608 := by
    unfold St_5786
    rw [← str_app_assoc, ← decodeHalf_zero, decodeHalf_encodeList]
    rfl
  unfold KP
  rw [hl, hr]
  exact hcfg

lemma init_to_4353 : (init []) [target_tm]⊢*
    (KP ((([1] ++ (([0, 0, 1] : List (Fin 2)) ^ 7)) +> default)) 0 (gsof [] 3) 10 true St_5786) := by
  refine ⟨4353, ?_⟩
  rw [← init_to_4353_cfg_eq]
  exact init_4353

lemma init_reaches : (init []) [target_tm]⊢* (KX 121 [28] 5 St0) := by
  have s0 := init_to_4353
  have s1_raw := P100s 7 0 default 0 (gsof [] 3) 10 true St_5786 (by decide)
  have s1 := stepStar_KP_r (stepStar_KP_pow0_r s1_raw) rfl rfl rfl
  have s01 := stepStar_trans s0 s1
  have s2 := W1 7 (gsof [] 3) 24 true St_5786 (by decide)
  have s02 := stepStar_trans s01 s2
  have s3_raw := Incs 6 6 (gsof [] 3) 25 true St_5786 (by decide)
  have s3 := stepStar_KP_r s3_raw rfl rfl rfl
  have s03 := stepStar_trans s02 s3
  have ht_5786 : ∀ l, (l {{C}}> St_5786) [target_tm]⊢* (l <{{E}} St_6060) := fun l =>
    TailRet'
      (tailw true true true false true true false true true true true false true false true [false, true, false])
      [.T1, .T1, .T1, .TZ, .T1]
      (bt true :: .TZ :: .T1 :: bt true :: .TZ :: bt false :: .TZ :: .T1 :: bt true :: bt true :: .TZ :: bt true :: .TZ :: .T1 :: bt true :: .TZ :: bt false :: .TZ :: bt true :: .TZ :: bt false :: .TZ :: bt true :: .TZ :: .T1 :: ([false, true, false].map bt ++ [.T1]))
      E [.T1, .T0, .T0, .TZ, .T1, .T1]
      (tailw true false false true true true false true true true true false true false true [false, true, false])
      rfl trivial rfl rfl l default
  have s4_raw := stepPlus_stepStar (NOrb true 3 St_5786 false 3 St_6060 [] 11 (OvNp1 3 St_5786 St_6060 ht_5786) trivial (by decide))
  have s4 := stepStar_KP_r s4_raw rfl rfl rfl
  have s04 := stepStar_trans s03 s4
  have s5_raw := P100s 11 0 default 0 (gsof [] 3) 4 false St_6060 (by decide)
  have s5 := stepStar_KP_r (stepStar_KP_pow0_r s5_raw) rfl rfl rfl
  have s05 := stepStar_trans s04 s5
  have s6 := W1 11 (gsof [] 3) 26 false St_6060 (by decide)
  have s06 := stepStar_trans s05 s6
  have s7_raw := Incs 4 10 (gsof [] 3) 27 false St_6060 (by decide)
  have s7 := stepStar_KP_r s7_raw rfl rfl rfl
  have s07 := stepStar_trans s06 s7
  have ht_6060 : ∀ l, (l {{C}}> St_6060) [target_tm]⊢* (l <{{F}} (([0, 0] : List (Fin 2)) +> S0_6060)) := fun l =>
    Tail0z l false true true true false true true true true false true false true [false, true, false]
  have s8_raw := stepPlus_stepStar (NOrb false 3 St_6060 true 4 (([0, 1] : List (Fin 2)) +> S0_6060) [] 13 (OvNp0 3 St_6060 S0_6060 ht_6060) trivial (by decide))
  have hSt : (([0, 1] : List (Fin 2)) +> S0_6060) = St_17206 := tw_T1_cons_eq _ _ default rfl
  have s8 := s8_raw
  rw [hSt] at s8
  have s08 := stepStar_trans s07 s8
  have s9_raw := P100s 13 0 default 0 (gsof [] 4) 4 true St_17206 (by decide)
  have s9 := stepStar_KP_r (stepStar_KP_pow0_r s9_raw) rfl rfl rfl
  have s09 := stepStar_trans s08 s9
  have s10 := W1 13 (gsof [] 4) 30 true St_17206 (by decide)
  have s010 := stepStar_trans s09 s10
  have s11_raw := Incs 32 12 (gsof [] 4) 31 true St_17206 (by decide)
  have s11 : (KP default 13 (gsof [] 4) 31 true St_17206) [target_tm]⊢* (KX 45 [] 4 St_17206) := s11_raw
  have s011 := stepStar_trans s010 s11
  have ht_17206 : ∀ l, (l {{C}}> St_17206) [target_tm]⊢* (l <{{E}} St_17206_1) := fun l =>
    Tail10 l true true true false true true true true false true false true [false, true, false]
  have ht2_17206 : TailF St_17206_1 S0_17206 := fun l =>
    Tail0z l true true true true false true true true true false true false true [false, true, false]
  have s12 := stepPlus_stepStar (pathP1 45 [] 4 St_17206 St_17206_1 S0_17206 10 19
    (OvNp1 4 St_17206 St_17206_1 ht_17206) ht2_17206 trivial rfl rfl (by decide) (by decide))
  have hSt0 : (([0, 1] : List (Fin 2)) +> S0_17206) = St0 := tw_T1_cons_eq _ _ default rfl
  rw [hSt0] at s12
  exact stepStar_trans s011 s12

lemma INV0 : INV 121 [28] 5 St0 := by
  refine ⟨⟨by decide, trivial⟩, by decide, 2, 55, Or.inl rfl, by decide, by decide,
    Or.inl ⟨Lst_intro true true true true true false true true true true false true false true [false, true, false] _ rfl, by decide, by decide⟩⟩

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
  refine BusyBeaver.Counter.does_not_halt_of_invariant
    (fun cfg => ∃ a G r1 St, cfg = KX a G r1 St ∧ INV a G r1 St) ?_ ?_
  · exact ⟨KX 121 [28] 5 St0, init_reaches, 121, [28], 5, St0, rfl, INV0⟩
  · rintro _ ⟨a, G, r1, St, rfl, hinv⟩
    rcases step_inv a G r1 St hinv with ⟨a', G', r1', St', hstep, hinv'⟩
    exact ⟨KX a' G' r1' St', hstep, a', G', r1', St', rfl, hinv'⟩

end BusyBeaver.M_1RB0LF_0RCHHH_1RD0RA_1LE0RC_0LA0LE_1LE1LB
