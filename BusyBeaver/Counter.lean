module

public import BusyBeaver.Defs
import Mathlib.Tactic.Ring

/-!
# Shared Counter Infrastructure (`BusyBeaver.Counter`)

Reusable symbolic execution, finite-window stepping, digit-stack carry cascade,
run-compressed counter increment, and machine-conjugation infrastructure for
Busy Beaver counter / odometer machines (`#166`, `#128`, `#737`, etc.).

All declarations live in `namespace BusyBeaver.Counter` with `@[scoped simp]`
attributes so that importing `BusyBeaver.Basic` (which re-exports
`BusyBeaver.Counter`) does not alter the default `simp` set of non-counter
proofs; counter proofs activate these definitions and simp rules via
`open Counter`.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.Counter

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- ============================================================================
-- 1. Multi-Step & Tape / List-Repeat Algebra
-- ============================================================================

section MultiStepAlgebra

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[scoped simp] private lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) :
    multiStep M config 0 = some config := rfl

@[scoped simp] private lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) :
    multiStep M config 1 = step M config := rfl

@[scoped simp] private lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

lemma step_multiStep (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂ := by simp [h]

lemma step_stepPlus (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ := ⟨1, by decide, step_multiStep tm c₁ c₂ h⟩

private lemma multiStep_add (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
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

lemma multiStep_step {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {n : Nat}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢^{n} c₃) : c₁ [tm]⊢^{n + 1} c₃ := by
  have := multiStep_trans tm c₁ c₂ c₃ 1 n h₁ h₂
  rwa [Nat.add_comm 1 n] at this

lemma stepStar_refl (tm : Machine Γ Λ) (c : Cfg Γ Λ) : c [tm]⊢* c :=
  ⟨0, rfl⟩

lemma stepStar_of_multiStep {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {n : Nat}
    (h : c₁ [tm]⊢^{n} c₂) : c₁ [tm]⊢* c₂ := ⟨n, h⟩

lemma stepStar_trans {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  rcases h₁ with ⟨n, hn⟩; rcases h₂ with ⟨m, hm⟩
  exact ⟨n + m, multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_stepStar {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : c₁ [tm]⊢⁺ c₂) : c₁ [tm]⊢* c₂ := by
  rcases h with ⟨n, _, hn⟩; exact ⟨n, hn⟩

lemma stepPlus_stepPlus_stepPlus {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  rcases h₁ with ⟨n, n_pos, hn⟩; rcases h₂ with ⟨m, _, hm⟩
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_trans {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepPlus_stepPlus h₁ h₂

lemma stepPlus_to_stepStar {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ :=
  stepPlus_stepStar h

lemma stepPlus_stepStar_stepPlus {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  rcases h₁ with ⟨n, n_pos, hn⟩; rcases h₂ with ⟨m, hm⟩
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepStar_stepPlus_stepPlus {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  rcases h₁ with ⟨n, hn⟩; rcases h₂ with ⟨m, m_pos, hm⟩
  exact ⟨n + m, Nat.lt_add_left n m_pos, multiStep_trans tm c₁ c₂ c₃ n m hn hm⟩

lemma stepPlus_stepStar_trans {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus h₁ h₂

lemma stepStar_stepPlus_trans {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepStar_stepPlus_stepPlus h₁ h₂

lemma step_stepStar_stepPlus {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus tm c₁ c₂ h₁) h₂

omit [Inhabited Γ] in
@[scoped simp] lemma pow_zero_list (l : List Γ) : l ^ (0 : Nat) = [] := rfl

omit [Inhabited Γ] in
lemma pow_succ_list (l : List Γ) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl

omit [Inhabited Γ] in
@[scoped simp] private theorem list_pow_add (l : List Γ) (n m : Nat) : l ^ (n + m) = l ^ n ++ l ^ m := by
  induction n with
  | zero => simp [pow_zero_list]
  | succ n ih =>
    rw [Nat.succ_add, pow_succ_list, pow_succ_list, ih, List.append_assoc]

omit [Inhabited Γ] in
lemma pow_succ_right (l : List Γ) (n : Nat) : l ^ (n + 1) = l ^ n ++ l := by
  rw [list_pow_add]; simp [pow_succ_list, pow_zero_list]

omit [Inhabited Γ] in
@[scoped simp] lemma nil_pow_list : ∀ (n : Nat), ([] : List Γ) ^ n = []
  | 0 => rfl
  | n + 1 => by simp [pow_succ_list, nil_pow_list n]

@[scoped simp] lemma listblank_append_nil (s : ListBlank Γ) : ([] : List Γ) +> s = s := rfl

@[scoped simp] lemma listblank_append_cons (a : Γ) (l : List Γ) (s : ListBlank Γ) :
    (a :: l) +> s = a >> (l +> s) := rfl

@[scoped simp] lemma listblank_append_assoc (l₁ l₂ : List Γ) (s : ListBlank Γ) :
    (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s) :=
  Turing.ListBlank.append_assoc l₁ l₂ s

@[scoped simp] lemma default_head_gen : (default : ListBlank Γ).head = default := rfl
@[scoped simp] lemma default_tail_gen : (default : ListBlank Γ).tail = default := rfl

@[scoped simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[scoped simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

@[scoped simp] lemma zero_cons_default : (0 : Fin 2) >> (default : ListBlank (Fin 2)) = default := by
  change ListBlank.cons default default = default
  exact ListBlank.cons_head_tail default

@[scoped simp] lemma zeros_append_default :
    ∀ (k : ℕ), (([0] : List (Fin 2)) ^ k) +> (default : ListBlank (Fin 2)) = default
  | 0 => rfl
  | k + 1 => by simp [pow_succ_list, zeros_append_default k]

lemma right_pow_succ (u : List Γ) (n : Nat) (r : ListBlank Γ) :
    u ^ (n + 1) +> r = u +> (u ^ n +> r) := by
  rw [pow_succ_list, listblank_append_assoc]

lemma right_pow_succ_right (u : List Γ) (n : Nat) (r : ListBlank Γ) :
    u ^ (n + 1) +> r = u ^ n +> (u +> r) := by
  rw [pow_succ_right, listblank_append_assoc]

end MultiStepAlgebra

-- ============================================================================
-- 2. Symbolic Window Steppers (`CCfg` & `LocalState`)
-- ============================================================================

section WindowSteppers

/-- Head-centered finite-window configuration over symbol type `Γ` and state type `Λ`. -/
structure CCfg (Γ Λ : Type*) where
  q   : Λ
  cur : Γ
  l   : List Γ
  r   : List Γ
  deriving DecidableEq

abbrev CCfg.head {Γ Λ : Type*} (c : CCfg Γ Λ) : Γ := c.cur
abbrev CCfg.left {Γ Λ : Type*} (c : CCfg Γ Λ) : List Γ := c.l
abbrev CCfg.right {Γ Λ : Type*} (c : CCfg Γ Λ) : List Γ := c.r

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Evaluates a `CCfg` with arbitrary left and right `ListBlank` tails. -/
@[reducible] def evalWindow (l_tail r_tail : ListBlank Γ) (c : CCfg Γ Λ) : Cfg Γ Λ :=
  ⟨some c.q, ⟨c.cur, c.l +> l_tail, c.r +> r_tail⟩⟩

/-- Evaluates a `CCfg` with a blank (`default`) left tail and symbolic right tail `r_tail`. -/
@[reducible] def evalCCfg (r_tail : ListBlank Γ) (c : CCfg Γ Λ) : Cfg Γ Λ :=
  evalWindow default r_tail c

/-- Evaluates a `CCfg` with a symbolic left tail `l_tail` and blank (`default`) right tail. -/
@[reducible] def evalRCCfg (l_tail : ListBlank Γ) (c : CCfg Γ Λ) : Cfg Γ Λ :=
  evalWindow l_tail default c

/-- Evaluates a `CCfg` with blank (`default`) tails on both sides. -/
@[reducible] def evalBCfg (c : CCfg Γ Λ) : Cfg Γ Λ :=
  evalWindow default default c

/-- Pushes symbol `w` onto window list `xs`; when `blank = true`, `xs = []`, and `w = default`,
    keeps the window list empty `[]` since `[default] +> default = default`. -/
def pushWindow [DecidableEq Γ] (blank : Bool) (w : Γ) (xs : List Γ) : List Γ :=
  if blank && xs.isEmpty && w == default then [] else w :: xs

lemma pushWindow_append [DecidableEq Γ] {blank : Bool} (w : Γ) (xs : List Γ)
    (tail : ListBlank Γ) (h_blank : blank = true → tail = default) :
    pushWindow blank w xs +> tail = w >> (xs +> tail) := by
  unfold pushWindow
  cases blank with
  | false => simp
  | true =>
    have ht := h_blank rfl
    subst ht
    cases xs with
    | nil =>
      by_cases hw : w = default
      · subst hw
        simp only [List.isEmpty_nil, Bool.true_and, beq_self_eq_true, ↓reduceIte,
          listblank_append_nil]
        exact (Turing.ListBlank.cons_head_tail default).symm
      · simp [hw]
    | cons _ _ => simp

/-- Unified finite-window step function parameterized by `(blankL, blankR)`:
    when `blankL = true` (resp. `blankR = true`), stepping off the empty left (resp. right)
    window pops `default : Γ` from the blank tail and pushing `default` onto an empty window
    keeps it empty; when `false`, stepping off `[]` returns `none`. -/
def stepWindow [DecidableEq Γ] (blankL blankR : Bool) (tm : Machine Γ Λ) (c : CCfg Γ Λ) :
    Option (CCfg Γ Λ) :=
  match tm c.q c.cur with
  | none => none
  | some (none, _) => none
  | some (some q', Stmt.write w Dir.left) =>
    let r' := pushWindow blankR w c.r
    match c.l with
    | [] => if blankL then some ⟨q', default, [], r'⟩ else none
    | b :: ls => some ⟨q', b, ls, r'⟩
  | some (some q', Stmt.write w Dir.right) =>
    let l' := pushWindow blankL w c.l
    match c.r with
    | [] => if blankR then some ⟨q', default, l', []⟩ else none
    | b :: rs => some ⟨q', b, l', rs⟩

theorem stepWindow_sound [DecidableEq Γ] {blankL blankR : Bool} {tm : Machine Γ Λ} {c c' : CCfg Γ Λ}
    (l_tail r_tail : ListBlank Γ)
    (hL : blankL = true → l_tail = default)
    (hR : blankR = true → r_tail = default)
    (h : stepWindow blankL blankR tm c = some c') :
    (evalWindow l_tail r_tail c) [tm]⊢ (evalWindow l_tail r_tail c') := by
  unfold stepWindow at h
  revert h
  cases h_tm : tm c.q c.cur with
  | none => intro h; nomatch h
  | some val =>
    rcases val with ⟨q_opt, stmt⟩
    cases q_opt with
    | none => intro h; nomatch h
    | some q' =>
      rcases stmt with ⟨w, dir⟩
      cases dir with
      | left =>
        cases hl : c.l with
        | nil =>
          cases h_bl : blankL with
          | false => intro h; nomatch h
          | true =>
            intro h; injection h with h'; subst h'
            have hlt := hL h_bl; subst hlt
            simp [step, evalWindow, h_tm, hl, Turing.Tape.write, Turing.Tape.move,
              pushWindow_append w c.r r_tail hR]
        | cons b ls =>
          intro h; injection h with h'; subst h'
          simp [step, evalWindow, h_tm, hl, Turing.Tape.write, Turing.Tape.move,
            pushWindow_append w c.r r_tail hR]
      | right =>
        cases hr : c.r with
        | nil =>
          cases h_br : blankR with
          | false => intro h; nomatch h
          | true =>
            intro h; injection h with h'; subst h'
            have hrt := hR h_br; subst hrt
            simp [step, evalWindow, h_tm, hr, Turing.Tape.write, Turing.Tape.move,
              pushWindow_append w c.l l_tail hL]
        | cons b rs =>
          intro h; injection h with h'; subst h'
          simp [step, evalWindow, h_tm, hr, Turing.Tape.write, Turing.Tape.move,
            pushWindow_append w c.l l_tail hL]

def multiStepWindow [DecidableEq Γ] (blankL blankR : Bool) (tm : Machine Γ Λ) :
    ℕ → CCfg Γ Λ → Option (CCfg Γ Λ)
  | 0, c => some c
  | n + 1, c => (stepWindow blankL blankR tm c).bind (multiStepWindow blankL blankR tm n)

theorem multiStepWindow_sound [DecidableEq Γ] {blankL blankR : Bool} {tm : Machine Γ Λ}
    (l_tail r_tail : ListBlank Γ)
    (hL : blankL = true → l_tail = default)
    (hR : blankR = true → r_tail = default) :
    ∀ (n : ℕ) (c c' : CCfg Γ Λ),
      multiStepWindow blankL blankR tm n c = some c' →
      (evalWindow l_tail r_tail c) [tm]⊢^{n} (evalWindow l_tail r_tail c')
  | 0, c, c', h => by
    injection h with h'; subst h'; rfl
  | n + 1, c, c', h => by
    simp only [multiStepWindow, Option.bind_eq_some_iff] at h
    rcases h with ⟨c₁, h₁, h₂⟩
    exact multiStep_step (stepWindow_sound l_tail r_tail hL hR h₁)
      (multiStepWindow_sound l_tail r_tail hL hR n c₁ c' h₂)

/-- Strict window stepper (neither side blank-extended). -/
def wstep [DecidableEq Γ] (tm : Machine Γ Λ) : CCfg Γ Λ → Option (CCfg Γ Λ) :=
  stepWindow false false tm
def wmultiStep [DecidableEq Γ] (tm : Machine Γ Λ) : ℕ → CCfg Γ Λ → Option (CCfg Γ Λ) :=
  multiStepWindow false false tm

theorem wstep_sound [DecidableEq Γ] {tm : Machine Γ Λ} (c c' : CCfg Γ Λ)
    (l_tail r_tail : ListBlank Γ) (h : wstep tm c = some c') :
    (evalWindow l_tail r_tail c) [tm]⊢ (evalWindow l_tail r_tail c') :=
  stepWindow_sound l_tail r_tail (by intro hc; nomatch hc) (by intro hc; nomatch hc) h

theorem wmultiStep_sound [DecidableEq Γ] {tm : Machine Γ Λ} (n : ℕ) (c c' : CCfg Γ Λ)
    (l_tail r_tail : ListBlank Γ) (h : wmultiStep tm n c = some c') :
    (evalWindow l_tail r_tail c) [tm]⊢^{n} (evalWindow l_tail r_tail c') :=
  multiStepWindow_sound l_tail r_tail (by intro hc; nomatch hc) (by intro hc; nomatch hc) n c c' h

/-- Left-blank-extended window stepper (`evalCCfg`). -/
def cstep [DecidableEq Γ] (tm : Machine Γ Λ) : CCfg Γ Λ → Option (CCfg Γ Λ) :=
  stepWindow true false tm
def cmultiStep [DecidableEq Γ] (tm : Machine Γ Λ) : ℕ → CCfg Γ Λ → Option (CCfg Γ Λ) :=
  multiStepWindow true false tm

theorem cstep_sound [DecidableEq Γ] {tm : Machine Γ Λ} (c c' : CCfg Γ Λ) (r_tail : ListBlank Γ)
    (h : cstep tm c = some c') :
    (evalCCfg r_tail c) [tm]⊢ (evalCCfg r_tail c') :=
  stepWindow_sound default r_tail (fun _ => rfl) (by intro hc; nomatch hc) h

theorem cmultiStep_sound [DecidableEq Γ] {tm : Machine Γ Λ} (n : ℕ) (c c' : CCfg Γ Λ)
    (r_tail : ListBlank Γ) (h : cmultiStep tm n c = some c') :
    (evalCCfg r_tail c) [tm]⊢^{n} (evalCCfg r_tail c') :=
  multiStepWindow_sound default r_tail (fun _ => rfl) (by intro hc; nomatch hc) n c c' h

/-- Right-blank-extended window stepper (`evalRCCfg`). -/
def rcstep [DecidableEq Γ] (tm : Machine Γ Λ) : CCfg Γ Λ → Option (CCfg Γ Λ) :=
  stepWindow false true tm
def rcmultiStep [DecidableEq Γ] (tm : Machine Γ Λ) : ℕ → CCfg Γ Λ → Option (CCfg Γ Λ) :=
  multiStepWindow false true tm

theorem rcstep_sound [DecidableEq Γ] {tm : Machine Γ Λ} (c c' : CCfg Γ Λ) (l_tail : ListBlank Γ)
    (h : rcstep tm c = some c') :
    (evalRCCfg l_tail c) [tm]⊢ (evalRCCfg l_tail c') :=
  stepWindow_sound l_tail default (by intro hc; nomatch hc) (fun _ => rfl) h

theorem rcmultiStep_sound [DecidableEq Γ] {tm : Machine Γ Λ} (n : ℕ) (c c' : CCfg Γ Λ)
    (l_tail : ListBlank Γ) (h : rcmultiStep tm n c = some c') :
    (evalRCCfg l_tail c) [tm]⊢^{n} (evalRCCfg l_tail c') :=
  multiStepWindow_sound l_tail default (by intro hc; nomatch hc) (fun _ => rfl) n c c' h

/-- Both-sides-blank-extended window stepper (`evalBCfg`). -/
def bstep [DecidableEq Γ] (tm : Machine Γ Λ) : CCfg Γ Λ → Option (CCfg Γ Λ) :=
  stepWindow true true tm
def bmultiStep [DecidableEq Γ] (tm : Machine Γ Λ) : ℕ → CCfg Γ Λ → Option (CCfg Γ Λ) :=
  multiStepWindow true true tm

theorem bstep_sound [DecidableEq Γ] {tm : Machine Γ Λ} (c c' : CCfg Γ Λ) (h : bstep tm c = some c') :
    (evalBCfg c) [tm]⊢ (evalBCfg c') :=
  stepWindow_sound default default (fun _ => rfl) (fun _ => rfl) h

theorem bmultiStep_sound [DecidableEq Γ] {tm : Machine Γ Λ} (n : ℕ) (c c' : CCfg Γ Λ)
    (h : bmultiStep tm n c = some c') :
    (evalBCfg c) [tm]⊢^{n} (evalBCfg c') :=
  multiStepWindow_sound default default (fun _ => rfl) (fun _ => rfl) n c c' h

/-- Directional half-tape configuration constructor (`l <{{q}} r` vs `l {{q}}> r`). -/
def cfg_of (q : Λ) (d : Dir) (l r : ListBlank Γ) : Cfg Γ Λ :=
  match d with
  | .left => ⟨some q, ⟨ListBlank.head l, ListBlank.tail l, r⟩⟩
  | .right => ⟨some q, ⟨ListBlank.head r, l, ListBlank.tail r⟩⟩

/-- Directional finite-window state (`l`, `r`, state `q`, head direction `d`). -/
structure LocalState (Γ Λ : Type*) where
  l : List Γ
  r : List Γ
  q : Λ
  d : Dir
  deriving DecidableEq

def step_local (tm : Machine Γ Λ) (s : LocalState Γ Λ) : Option (LocalState Γ Λ) :=
  match s.d with
  | .left =>
    match s.l with
    | [] => none
    | b :: l =>
      match tm s.q b with
      | some (some q', Stmt.write b' .left) => some ⟨l, b' :: s.r, q', .left⟩
      | some (some q', Stmt.write b' .right) => some ⟨b' :: l, s.r, q', .right⟩
      | _ => none
  | .right =>
    match s.r with
    | [] => none
    | b :: r =>
      match tm s.q b with
      | some (some q', Stmt.write b' .left) => some ⟨s.l, b' :: r, q', .left⟩
      | some (some q', Stmt.write b' .right) => some ⟨b' :: s.l, r, q', .right⟩
      | _ => none

lemma step_local_spec {tm : Machine Γ Λ} {s1 s2 : LocalState Γ Λ}
    (h : step_local tm s1 = some s2) (L R : ListBlank Γ) :
    (cfg_of s1.q s1.d (s1.l +> L) (s1.r +> R)) [tm]⊢
    (cfg_of s2.q s2.d (s2.l +> L) (s2.r +> R)) := by
  rcases s1 with ⟨l1, r1, q1, d1⟩
  rcases s2 with ⟨l2, r2, q2, d2⟩
  unfold step_local at h
  cases d1
  · cases l1 with
    | nil => contradiction
    | cons b l =>
      dsimp only at h
      cases htm : tm q1 b with
      | none => rw [htm] at h; contradiction
      | some qa =>
        rcases qa with ⟨_ | q', ⟨b', _ | _⟩⟩
        · rw [htm] at h; contradiction
        · rw [htm] at h; contradiction
        · rw [htm] at h
          injection h with hs; cases hs
          unfold cfg_of step; dsimp only
          rw [listblank_append_cons, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, htm]
          simp only [listblank_append_cons]; rfl
        · rw [htm] at h
          injection h with hs; cases hs
          unfold cfg_of step; dsimp only
          rw [listblank_append_cons, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, htm]
          simp only [listblank_append_cons]; rfl
  · cases r1 with
    | nil => contradiction
    | cons b r =>
      dsimp only at h
      cases htm : tm q1 b with
      | none => rw [htm] at h; contradiction
      | some qa =>
        rcases qa with ⟨_ | q', ⟨b', _ | _⟩⟩
        · rw [htm] at h; contradiction
        · rw [htm] at h; contradiction
        · rw [htm] at h
          injection h with hs; cases hs
          unfold cfg_of step; dsimp only
          rw [listblank_append_cons, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, htm]
          simp only [listblank_append_cons]; rfl
        · rw [htm] at h
          injection h with hs; cases hs
          unfold cfg_of step; dsimp only
          rw [listblank_append_cons, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, htm]
          simp only [listblank_append_cons]; rfl

def run_local (tm : Machine Γ Λ) : Nat → LocalState Γ Λ → Option (LocalState Γ Λ)
  | 0, s => some s
  | n + 1, s =>
    match step_local tm s with
    | some s' => run_local tm n s'
    | none => none

lemma run_local_spec {tm : Machine Γ Λ} {n : Nat} {s1 s2 : LocalState Γ Λ}
    (h : run_local tm n s1 = some s2) (L R : ListBlank Γ) :
    (cfg_of s1.q s1.d (s1.l +> L) (s1.r +> R)) [tm]⊢*
    (cfg_of s2.q s2.d (s2.l +> L) (s2.r +> R)) := by
  induction n generalizing s1 with
  | zero =>
    unfold run_local at h
    injection h with hs; subst hs
    exact ⟨0, rfl⟩
  | succ n ih =>
    unfold run_local at h
    cases hs : step_local tm s1 with
    | none => rw [hs] at h; contradiction
    | some sm =>
      rw [hs] at h
      exact stepPlus_stepStar (step_stepStar_stepPlus (step_local_spec hs L R) (ih h))

lemma run_local_plus_eq {tm : Machine Γ Λ} {n : Nat} {s1 s2 : LocalState Γ Λ}
    {c1 c2 : Cfg Γ Λ} (L R : ListBlank Γ)
    (h : run_local tm (n + 1) s1 = some s2)
    (h1 : cfg_of s1.q s1.d (s1.l +> L) (s1.r +> R) = c1)
    (h2 : cfg_of s2.q s2.d (s2.l +> L) (s2.r +> R) = c2) :
    c1 [tm]⊢⁺ c2 := by
  rw [← h1, ← h2]
  unfold run_local at h
  cases hs : step_local tm s1 with
  | none => rw [hs] at h; contradiction
  | some sm =>
    rw [hs] at h
    exact step_stepStar_stepPlus (step_local_spec hs L R) (run_local_spec h L R)

end WindowSteppers

-- ============================================================================
-- 3. Fixed-Block Token Tape Codec (`encWords`, `encTape`)
-- ============================================================================

section WordCodec

variable {Tok Γ : Type*} [Inhabited Γ]

/-- Concatenates the word encodings of a token list `List Tok`. -/
def encWords (w : Tok → List Γ) : List Tok → List Γ
  | [] => []
  | d :: xs => w d ++ encWords w xs

omit [Inhabited Γ] in
@[scoped simp] lemma encWords_nil (w : Tok → List Γ) : encWords w [] = [] := rfl

omit [Inhabited Γ] in
@[scoped simp] lemma encWords_cons (w : Tok → List Γ) (d : Tok) (xs : List Tok) :
    encWords w (d :: xs) = w d ++ encWords w xs := rfl

omit [Inhabited Γ] in
@[scoped simp] lemma encWords_append (w : Tok → List Γ) (x y : List Tok) :
    encWords w (x ++ y) = encWords w x ++ encWords w y := by
  induction x with
  | nil => rfl
  | cons d xs ih => simp [ih, List.append_assoc]

/-- Encodes a token list `List Tok` onto a half-tape ending in `sentinel : ListBlank Γ`. -/
def encTape (w : Tok → List Γ) (sentinel : ListBlank Γ) (x : List Tok) : ListBlank Γ :=
  encWords w x +> sentinel

@[scoped simp] lemma encTape_nil (w : Tok → List Γ) (sentinel : ListBlank Γ) :
    encTape w sentinel [] = sentinel := rfl

lemma encTape_cons (w : Tok → List Γ) (sentinel : ListBlank Γ) (d : Tok) (xs : List Tok) :
    encTape w sentinel (d :: xs) = w d +> encTape w sentinel xs := by
  simp only [encTape, encWords_cons, listblank_append_assoc]

@[scoped simp] lemma encTape_append (w : Tok → List Γ) (sentinel : ListBlank Γ) (x y : List Tok) :
    encTape w sentinel (x ++ y) = encWords w x +> encTape w sentinel y := by
  simp only [encTape, encWords_append, listblank_append_assoc]

end WordCodec

-- ============================================================================
-- 4A. Binary & Shift-Overflow Counter Algebra (`IterRel`, `BinDigit`, `BinSweep`, `DigitVal`)
-- ============================================================================

section BinaryCounterAlgebra

/-- `n`-fold relational composition of a single-step counter increment relation `Inc`. -/
inductive IterRel {α : Type*} (Inc : α → α → Prop) : ℕ → α → α → Prop
  | zero (x : α) : IterRel Inc 0 x x
  | succ {n : ℕ} {x y z : α} : Inc x y → IterRel Inc n y z → IterRel Inc (n + 1) x z

/-- Composition of iterated relation steps: `IterRel Inc m x y → IterRel Inc n y z → IterRel Inc (m + n) x z`. -/
theorem IterRel_trans {α : Type*} {Inc : α → α → Prop} {m n : ℕ} {x y z : α}
    (h₁ : IterRel Inc m x y) (h₂ : IterRel Inc n y z) : IterRel Inc (m + n) x z := by
  induction h₁ with
  | zero => simpa only [Nat.zero_add] using h₂
  | succ hstep _ ih =>
    rw [Nat.succ_add]
    exact IterRel.succ hstep (ih h₂)

/-- Lifts a single-step counter increment `cfg (x, m) ⊢* cfg (x', m + 1)` to `n` increments. -/
theorem IterRel_lift_rc {α Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {Inc : α → α → Prop}
    (evalCfg : α → ℕ → Cfg Γ Λ)
    (h_step : ∀ {x x'}, Inc x x' → ∀ m, (evalCfg x m) [tm]⊢* (evalCfg x' (m + 1)))
    {n : ℕ} {x x' : α} (h : IterRel Inc n x x') :
    ∀ (m : ℕ), (evalCfg x m) [tm]⊢* (evalCfg x' (m + n)) := by
  induction h with
  | zero x =>
    intro m; rw [Nat.add_zero]; exact stepStar_refl _ _
  | @succ n x y z h1 _ ih =>
    intro m
    rw [← Nat.add_assoc, Nat.add_right_comm m n 1]
    exact stepStar_trans (h_step h1 m) (ih (m + 1))

/-- Canonical 2-word digit alphabet (`W0`, `W1`) for shift-overflow binary counters (`SOBC`). -/
inductive LD
  | W0 : LD
  | W1 : LD
  deriving DecidableEq, Repr

lemma pow_W1_odd : ∀ (m : ℕ) (s : List LD),
    ((([.W1] : List LD) ^ (2 * m + 1)) ++ s) =
      ((([.W1, .W1] : List LD) ^ m) ++ (.W1 :: s))
  | 0, s => rfl
  | m + 1, s => by
    have h2 : 2 * (m + 1) + 1 = 2 + (2 * m + 1) := by omega
    rw [h2, list_pow_add, List.append_assoc, pow_W1_odd m s]; rfl

/-- Single-step carry increment relation on `List LD` (`SOBC` word algebra). -/
inductive LInc : List LD → List LD → Prop
  | w0 {xs xs' : List LD} : LInc xs xs' → LInc (.W0 :: xs) (.W0 :: xs')
  | w10 (xs : List LD) : LInc (.W1 :: .W0 :: xs) (.W1 :: .W1 :: xs)
  | w11 {xs xs' : List LD} : LInc xs xs' → LInc (.W1 :: .W1 :: xs) (.W1 :: .W0 :: xs')

lemma LInc_append {a a' : List LD} (h : LInc a a') (b : List LD) :
    LInc (a ++ b) (a' ++ b) := by
  induction h with
  | w0 _ ih => exact .w0 ih
  | w10 xs => exact .w10 (xs ++ b)
  | w11 _ ih => exact .w11 ih

lemma LInc_pow_11_10 : ∀ (k : ℕ) (s : List LD),
    LInc ((([.W1, .W1] : List LD) ^ k) ++ (.W1 :: .W0 :: s))
      ((([.W1, .W0] : List LD) ^ k) ++ (.W1 :: .W1 :: s))
  | 0, s => .w10 s
  | k + 1, s => .w11 (LInc_pow_11_10 k s)

abbrev LIncs : ℕ → List LD → List LD → Prop := IterRel LInc

lemma LIncs_w0 {n : ℕ} {xs xs' : List LD} (h : LIncs n xs xs') :
    LIncs n (.W0 :: xs) (.W0 :: xs') := by
  induction h with
  | zero xs => exact .zero (.W0 :: xs)
  | succ h1 _ ih => exact .succ (.w0 h1) ih

lemma LIncs_w11 {n : ℕ} {xs xs' : List LD} (h : LIncs n xs xs') :
    LIncs (2 * n) (.W1 :: .W1 :: xs) (.W1 :: .W1 :: xs') := by
  induction h with
  | zero xs => exact .zero (.W1 :: .W1 :: xs)
  | @succ n x y z h1 _ ih =>
    rw [Nat.mul_succ]
    exact .succ (.w11 h1) (.succ (.w10 y) ih)

lemma LIncs_w10 {n : ℕ} {xs xs' : List LD} (h : LIncs n xs xs') :
    LIncs (2 * n + 1) (.W1 :: .W0 :: xs) (.W1 :: .W1 :: xs') :=
  .succ (.w10 xs) (LIncs_w11 h)

/-- Full-saturation binary counter sweep relation (`LIncsP`):
    saturates every `(.W1, .W0)` pair to `(.W1, .W1)` in `n` increments. -/
inductive LIncsP : ℕ → List LD → List LD → Prop
  | nil : LIncsP 0 [] []
  | w0 {n : ℕ} {xs xs' : List LD} : LIncsP n xs xs' → LIncsP n (.W0 :: xs) (.W0 :: xs')
  | w10 {n : ℕ} {xs xs' : List LD} : LIncsP n xs xs' → LIncsP (2 * n + 1) (.W1 :: .W0 :: xs) (.W1 :: .W1 :: xs')
  | w11 {n : ℕ} {xs xs' : List LD} : LIncsP n xs xs' → LIncsP (2 * n) (.W1 :: .W1 :: xs) (.W1 :: .W1 :: xs')

theorem LIncsP_to_LIncs {n : ℕ} {x x' : List LD} (h : LIncsP n x x') : LIncs n x x' := by
  induction h with
  | nil => exact .zero []
  | w0 _ ih => exact LIncs_w0 ih
  | w10 _ ih => exact LIncs_w10 ih
  | w11 _ ih => exact LIncs_w11 ih

lemma LIncsP_append {m : ℕ} {a a' : List LD} (ha : LIncsP m a a') :
    ∀ {n : ℕ} {b b' : List LD}, LIncsP n b b' → ∃ k, LIncsP k (a ++ b) (a' ++ b') := by
  induction ha with
  | nil => intro n b b' hb; exact ⟨n, hb⟩
  | w0 _ ih =>
    intro n b b' hb
    rcases ih hb with ⟨k, hk⟩
    exact ⟨k, .w0 hk⟩
  | w10 _ ih =>
    intro n b b' hb
    rcases ih hb with ⟨k, hk⟩
    exact ⟨2 * k + 1, .w10 hk⟩
  | w11 _ ih =>
    intro n b b' hb
    rcases ih hb with ⟨k, hk⟩
    exact ⟨2 * k, .w11 hk⟩

lemma LIncsP_pow_10 : ∀ (k : ℕ) {n : ℕ} {xs xs' : List LD},
    LIncsP n xs xs' →
    ∃ m, LIncsP m ((([.W1, .W0] : List LD) ^ k) ++ xs) ((([.W1, .W1] : List LD) ^ k) ++ xs')
  | 0, _, _, _, h => ⟨_, h⟩
  | k + 1, _, _, _, h => by
    rcases LIncsP_pow_10 k h with ⟨m, hm⟩
    exact ⟨2 * m + 1, .w10 hm⟩

lemma LIncsP_pow10_bound {n : ℕ} {xs xs' : List LD} (h : LIncsP n xs xs') :
    LIncsP (2 * (512 * n + 511) + 1)
      ((([.W1, .W0] : List LD) ^ 10) ++ xs)
      ((([.W1, .W1] : List LD) ^ 10) ++ xs') := by
  have h1 := LIncsP.w10 h
  have h2 := LIncsP.w10 h1
  have h3 := LIncsP.w10 h2
  have h4 := LIncsP.w10 h3
  have h5 := LIncsP.w10 h4
  have h6 := LIncsP.w10 h5
  have h7 := LIncsP.w10 h6
  have h8 := LIncsP.w10 h7
  have h9 := LIncsP.w10 h8
  have h10 := LIncsP.w10 h9
  have heq : 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * n + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 =
      2 * (512 * n + 511) + 1 := by omega
  rwa [heq] at h10

/-- Shift-overflow transducer relation (`LOv2`) on `List LD`. -/
inductive LOv2 : List LD → List LD → List LD → Prop
  | nil (u : List LD) : LOv2 [] u u
  | w0 {xs u u' : List LD} :
      LOv2 xs u u' → LOv2 (.W0 :: xs) u (.W1 :: u')
  | w11_0 {xs u x : List LD} :
      LOv2 xs u (.W0 :: x) →
      LOv2 (.W1 :: .W1 :: xs) u (.W0 :: .W0 :: .W1 :: x)
  | w11_1 {xs u z z' : List LD} :
      LOv2 xs u (.W1 :: z) → LInc z z' →
      LOv2 (.W1 :: .W1 :: xs) u (.W0 :: .W0 :: .W0 :: z')

lemma LOv2_append {a b u v w : List LD} (ha : LOv2 a v w) (hb : LOv2 b u v) :
    LOv2 (a ++ b) u w := by
  induction ha with
  | nil => exact hb
  | w0 _ ih => exact .w0 (ih hb)
  | w11_0 _ ih => exact .w11_0 (ih hb)
  | w11_1 _ hz ih => exact .w11_1 (ih hb) hz

lemma LOv2_suffix {w u y : List LD} (h : LOv2 w u y) (s : List LD) :
    LOv2 w (u ++ s) (y ++ s) := by
  induction h with
  | nil _ => exact .nil _
  | w0 _ ih => exact .w0 ih
  | w11_0 _ ih => exact .w11_0 ih
  | w11_1 _ hz ih => exact .w11_1 ih (LInc_append hz s)

lemma LOv2_pow_11 : ∀ (k : ℕ) (s : List LD),
    LOv2 ((([.W1, .W1] : List LD) ^ k))
      ([.W0, .W0, .W1, .W0] ++ s)
      ([.W0, .W0, .W1, .W0] ++ ((([.W1, .W0] : List LD) ^ k) ++ s))
  | 0, _ => .nil _
  | k + 1, s => .w11_0 (LOv2_pow_11 k s)

def lincFinite : List LD → Option (List LD)
  | [] => none
  | [.W1] => none
  | .W0 :: xs => (lincFinite xs).map (.W0 :: ·)
  | .W1 :: .W0 :: xs => some (.W1 :: .W1 :: xs)
  | .W1 :: .W1 :: xs => (lincFinite xs).map (.W1 :: .W0 :: ·)

theorem lincFinite_sound : ∀ {x x' : List LD}, lincFinite x = some x' → LInc x x'
  | [], _, h => by nomatch h
  | [.W1], _, h => by nomatch h
  | .W0 :: xs, _, h => by
    simp only [lincFinite, Option.map_eq_some_iff] at h
    rcases h with ⟨xs', hxs, rfl⟩
    exact .w0 (lincFinite_sound hxs)
  | .W1 :: .W0 :: xs, _, h => by
    injection h with h'; subst h'
    exact .w10 xs
  | .W1 :: .W1 :: xs, _, h => by
    simp only [lincFinite, Option.map_eq_some_iff] at h
    rcases h with ⟨xs', hxs, rfl⟩
    exact .w11 (lincFinite_sound hxs)

def lincspFinite : List LD → Option (List LD)
  | [] => some []
  | [.W1] => none
  | .W0 :: xs => (lincspFinite xs).map (.W0 :: ·)
  | .W1 :: .W0 :: xs => (lincspFinite xs).map (.W1 :: .W1 :: ·)
  | .W1 :: .W1 :: xs => (lincspFinite xs).map (.W1 :: .W1 :: ·)

def lincspCount : List LD → ℕ
  | [] => 0
  | [.W1] => 0
  | .W0 :: xs => lincspCount xs
  | .W1 :: .W0 :: xs => 2 * lincspCount xs + 1
  | .W1 :: .W1 :: xs => 2 * lincspCount xs

theorem lincspFinite_sound : ∀ {x x' : List LD},
    lincspFinite x = some x' → LIncsP (lincspCount x) x x'
  | [], _, h => by
    injection h with h'; subst h'; exact .nil
  | [.W1], _, h => by nomatch h
  | .W0 :: xs, _, h => by
    simp only [lincspFinite, Option.map_eq_some_iff] at h
    rcases h with ⟨xs', hxs, rfl⟩
    exact .w0 (lincspFinite_sound hxs)
  | .W1 :: .W0 :: xs, _, h => by
    simp only [lincspFinite, Option.map_eq_some_iff] at h
    rcases h with ⟨xs', hxs, rfl⟩
    exact .w10 (lincspFinite_sound hxs)
  | .W1 :: .W1 :: xs, _, h => by
    simp only [lincspFinite, Option.map_eq_some_iff] at h
    rcases h with ⟨xs', hxs, rfl⟩
    exact .w11 (lincspFinite_sound hxs)

def lov2Finite : List LD → List LD → Option (List LD)
  | [], u => some u
  | .W0 :: xs, u => (lov2Finite xs u).map (.W1 :: ·)
  | .W1 :: .W1 :: xs, u =>
    match lov2Finite xs u with
    | some (.W0 :: x) => some (.W0 :: .W0 :: .W1 :: x)
    | some (.W1 :: z) => (lincFinite z).map (.W0 :: .W0 :: .W0 :: ·)
    | _ => none
  | _, _ => none

theorem lov2Finite_sound : ∀ {w u y : List LD},
    lov2Finite w u = some y → LOv2 w u y
  | [], u, _, h => by
    injection h with h'; subst h'; exact .nil u
  | .W0 :: xs, u, _, h => by
    simp only [lov2Finite, Option.map_eq_some_iff] at h
    rcases h with ⟨u', hu, rfl⟩
    exact .w0 (lov2Finite_sound hu)
  | .W1 :: .W0 :: _, _, _, h => by nomatch h
  | [.W1], _, _, h => by nomatch h
  | .W1 :: .W1 :: xs, u, _, h => by
    unfold lov2Finite at h
    revert h
    cases hov : lov2Finite xs u with
    | none => intro h; nomatch h
    | some r =>
      cases r with
      | nil => intro h; nomatch h
      | cons d tail =>
        cases d with
        | W0 =>
          intro h; injection h with h'; subst h'
          exact .w11_0 (lov2Finite_sound hov)
        | W1 =>
          simp only [Option.map_eq_some_iff]
          rintro ⟨z', hz, rfl⟩
          exact .w11_1 (lov2Finite_sound hov) (lincFinite_sound hz)

def stepBuffer (b : List LD) : Option (List LD) :=
  match (lincspFinite b).bind (fun bp => lov2Finite bp [.W0, .W0, .W1, .W0]) with
  | some (.W0 :: x) => some (.W1 :: x)
  | some (.W1 :: z) => (lincFinite z).map (.W0 :: ·)
  | _ => none

def checkBuffer : ℕ → List LD → Bool
  | 0, b => (lincspFinite b).isSome
  | r + 1, b =>
    match stepBuffer b with
    | some b' => checkBuffer r b'
    | none => false

abbrev IsBuffer (r : ℕ) (b : List LD) : Prop := checkBuffer r b = true

lemma checkBuffer_mono : ∀ {r : ℕ} {b : List LD},
    checkBuffer (r + 1) b = true → checkBuffer r b = true
  | 0, b, h => by
    unfold checkBuffer stepBuffer at h
    cases h1 : lincspFinite b with
    | none => simp [h1] at h
    | some bp => simp [checkBuffer, h1]
  | r + 1, b, h => by
    unfold checkBuffer at h ⊢
    cases hs : stepBuffer b with
    | none => simp [hs] at h
    | some b' =>
      rw [hs] at h
      exact checkBuffer_mono h

lemma isBuffer_le {k r : ℕ} (hkr : k ≤ r) {b : List LD} (hb : IsBuffer r b) :
    IsBuffer k b := by
  induction r generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst this; exact hb
  | succ r' ih =>
    rcases Nat.of_le_succ hkr with hlt | rfl
    · exact ih hlt (checkBuffer_mono hb)
    · exact hb

theorem stepBuffer_spec {r : ℕ} {b : List LD} (hb : IsBuffer (r + 1) b) :
    ∃ (n : ℕ) (bp b' : List LD),
      LIncsP n b bp ∧
      IsBuffer r b' ∧
      ∀ (s : List LD),
        LOv2 ([.W1, .W1, .W1, .W1] ++ bp)
          ([.W0, .W0, .W1, .W0] ++ s)
          ([.W0, .W0, .W1, .W0] ++ (b' ++ s)) := by
  unfold IsBuffer checkBuffer at hb
  cases hs : stepBuffer b with
  | none => rw [hs] at hb; nomatch hb
  | some b' =>
    rw [hs] at hb
    unfold stepBuffer at hs
    revert hs
    cases h_lp : lincspFinite b with
    | none => intro hs; nomatch hs
    | some bp =>
      simp only [Option.bind_some]
      cases h_ov : lov2Finite bp [.W0, .W0, .W1, .W0] with
      | none => intro hs; nomatch hs
      | some ov =>
        cases ov with
        | nil => intro hs; nomatch hs
        | cons d tail =>
          cases d with
          | W0 =>
            intro hs; injection hs with hs'; subst hs'
            refine ⟨lincspCount b, bp, .W1 :: tail, lincspFinite_sound h_lp, hb, ?_⟩
            intro s
            have hov_s := LOv2_suffix (lov2Finite_sound h_ov) s
            exact .w11_0 (.w11_0 hov_s)
          | W1 =>
            simp only [Option.map_eq_some_iff]
            rintro ⟨z', hz, rfl⟩
            refine ⟨lincspCount b, bp, .W0 :: z', lincspFinite_sound h_lp, hb, ?_⟩
            intro s
            have hov_s := LOv2_suffix (lov2Finite_sound h_ov) s
            have hz_s := LInc_append (lincFinite_sound hz) s
            exact .w11_0 (.w11_1 hov_s hz_s)

def macroStepFinite (u : List LD) : Option (List LD) :=
  match (lincspFinite u).bind (fun up => lov2Finite up [.W0, .W0]) with
  | some (.W0 :: x) => some (.W1 :: x)
  | some (.W1 :: z) => (lincFinite z).map (.W0 :: ·)
  | _ => none

theorem macroStepFinite_spec {u u' : List LD} (h : macroStepFinite u = some u') :
    ∃ (n : ℕ) (up : List LD),
      LIncsP n u up ∧
      LOv2 ([.W1, .W1, .W1, .W1] ++ up) [.W0, .W0] ([.W0, .W0, .W1, .W0] ++ u') := by
  unfold macroStepFinite at h
  revert h
  cases h_lp : lincspFinite u with
  | none => intro h; nomatch h
  | some up =>
    simp only [Option.bind_some]
    cases h_ov : lov2Finite up [.W0, .W0] with
    | none => intro h; nomatch h
    | some ov =>
      cases ov with
      | nil => intro h; nomatch h
      | cons d tail =>
        cases d with
        | W0 =>
          intro h; injection h with h'; subst h'
          exact ⟨lincspCount u, up, lincspFinite_sound h_lp, .w11_0 (.w11_0 (lov2Finite_sound h_ov))⟩
        | W1 =>
          simp only [Option.map_eq_some_iff]
          rintro ⟨z', hz, rfl⟩
          exact ⟨lincspCount u, up, lincspFinite_sound h_lp,
            .w11_0 (.w11_1 (lov2Finite_sound h_ov) (lincFinite_sound hz))⟩

def runU : ℕ → List LD → Option (List LD)
  | 0, u => some u
  | k + 1, u => (macroStepFinite u).bind (runU k)

inductive ChainTail (r : ℕ) : List LD → Prop
  | nil : ChainTail r (([.W1, .W0] : List LD) ^ (2 * r))
  | pair {T : List LD} : ChainTail r T → ChainTail r (.W1 :: .W0 :: T)
  | buf {B T : List LD} :
      IsBuffer r B → ChainTail r T →
      ChainTail r ((([.W1, .W0] : List LD) ^ (2 * r)) ++ (B ++ T))

lemma ChainTail_pow_pair : ∀ (k : ℕ) {r : ℕ} {T : List LD},
    ChainTail r T → ChainTail r ((([.W1, .W0] : List LD) ^ k) ++ T)
  | 0, _, _, h => h
  | k + 1, _, _, h => ChainTail.pair (ChainTail_pow_pair k h)

theorem ChainTail_step {r : ℕ} {T : List LD} (hT : ChainTail (r + 1) T)
    {u u' : List LD} (hu : macroStepFinite u = some u') :
    ∃ (n : ℕ) (W' T' : List LD),
      LIncsP n (T ++ u) W' ∧
      LOv2 W' [.W0, .W0] ([.W0, .W0, .W1, .W0] ++ (T' ++ u')) ∧
      ChainTail r T' := by
  induction hT with
  | nil =>
    rcases macroStepFinite_spec hu with ⟨nu, up, h_up, h_ovu⟩
    have h_2 : ((([.W1, .W0] : List LD) ^ (2 * (r + 1))) ++ u) =
        ((([.W1, .W0] : List LD) ^ (2 * r)) ++ ([.W1, .W0, .W1, .W0] ++ u)) := by
      have : 2 * (r + 1) = 2 * r + 2 := by omega
      rw [this, list_pow_add, List.append_assoc]; rfl
    rw [h_2]
    have h_lp2 : LIncsP (2 * (2 * nu + 1) + 1) ([.W1, .W0, .W1, .W0] ++ u) ([.W1, .W1, .W1, .W1] ++ up) :=
      .w10 (.w10 h_up)
    rcases LIncsP_pow_10 (2 * r) h_lp2 with ⟨n_all, h_all⟩
    refine ⟨n_all, _, ([.W1, .W0] : List LD) ^ (2 * r), h_all, ?_, .nil⟩
    exact LOv2_append (LOv2_pow_11 (2 * r) u') h_ovu
  | @pair T₀ _ ih =>
    rcases ih with ⟨n₀, W₀', T₀', h_lp0, h_ov0, h_ct0⟩
    refine ⟨2 * n₀ + 1, .W1 :: .W1 :: W₀', .W1 :: .W0 :: T₀', .w10 h_lp0, ?_, .pair h_ct0⟩
    exact .w11_0 h_ov0
  | @buf B T₀ hB _ ih =>
    rcases ih with ⟨n₀, W₀', T₀', h_lp0, h_ov0, h_ct0⟩
    rcases stepBuffer_spec hB with ⟨nB, bp, B', h_lpB, hB', h_ovB⟩
    have h_2 : ((([.W1, .W0] : List LD) ^ (2 * (r + 1))) ++ (B ++ T₀) ++ u) =
        ((([.W1, .W0] : List LD) ^ (2 * r)) ++ ([.W1, .W0, .W1, .W0] ++ B ++ (T₀ ++ u))) := by
      have : 2 * (r + 1) = 2 * r + 2 := by omega
      rw [this, list_pow_add]
      simp only [List.append_assoc]; rfl
    rw [h_2]
    rcases LIncsP_append (.w10 (.w10 h_lpB)) h_lp0 with ⟨n_mid, h_mid⟩
    rcases LIncsP_pow_10 (2 * r) h_mid with ⟨n_all, h_all⟩
    refine ⟨n_all, _, ((([.W1, .W0] : List LD) ^ (2 * r)) ++ (B' ++ T₀')), h_all, ?_, .buf hB' h_ct0⟩
    have h_ov_mid : LOv2 (([.W1, .W1, .W1, .W1] ++ bp) ++ W₀') [.W0, .W0]
        ([.W0, .W0, .W1, .W0] ++ (B' ++ (T₀' ++ u'))) :=
      LOv2_append (h_ovB (T₀' ++ u')) h_ov0
    have h_ov_top := LOv2_append (LOv2_pow_11 (2 * r) (B' ++ (T₀' ++ u'))) h_ov_mid
    simpa only [List.append_assoc] using! h_ov_top

lemma ChainTail_zero_lincsp {T : List LD} (hT : ChainTail 0 T) :
    ∃ n T', LIncsP n T T' := by
  induction hT with
  | nil => exact ⟨0, [], .nil⟩
  | pair _ ih =>
    rcases ih with ⟨n, T', h⟩
    exact ⟨2 * n + 1, .W1 :: .W1 :: T', .w10 h⟩
  | @buf B T₀ hB _ ih =>
    rcases ih with ⟨n, T', h⟩
    unfold IsBuffer checkBuffer at hB
    cases h_lp : lincspFinite B with
    | none => rw [h_lp] at hB; nomatch hB
    | some bp =>
      rcases LIncsP_append (lincspFinite_sound h_lp) h with ⟨k, hk⟩
      exact ⟨k, bp ++ T', hk⟩

inductive Only011 : List LD → Prop
  | nil : Only011 []
  | w0 {xs : List LD} : Only011 xs → Only011 (.W0 :: xs)
  | w11 {xs : List LD} : Only011 xs → Only011 (.W1 :: .W1 :: xs)

lemma Only011_append {a b : List LD} (ha : Only011 a) (hb : Only011 b) :
    Only011 (a ++ b) := by
  induction ha with
  | nil => exact hb
  | w0 _ ih => exact .w0 ih
  | w11 _ ih => exact .w11 ih

lemma LIncsP_only011 {n : ℕ} {x x' : List LD} (h : LIncsP n x x') : Only011 x' := by
  induction h with
  | nil => exact .nil
  | w0 _ ih => exact .w0 ih
  | w10 _ ih => exact .w11 ih
  | w11 _ ih => exact .w11 ih

def checkOnly011 : List LD → Bool
  | [] => true
  | .W0 :: xs => checkOnly011 xs
  | .W1 :: .W1 :: xs => checkOnly011 xs
  | _ => false

theorem checkOnly011_sound : ∀ {w : List LD}, checkOnly011 w = true → Only011 w
  | [], _ => .nil
  | .W0 :: xs, h => .w0 (checkOnly011_sound h)
  | .W1 :: .W1 :: xs, h => .w11 (checkOnly011_sound h)
  | [.W1], h => by nomatch h
  | .W1 :: .W0 :: _, h => by nomatch h

/-- LSB-first positional binary value relation over two chosen digit tokens `d0, d1 : Tok`. -/
inductive DigitVal {Tok : Type*} (d0 d1 : Tok) : Nat → Nat → List Tok → Prop where
  | nil : DigitVal d0 d1 0 0 []
  | zero {A H : Nat} {u : List Tok} : DigitVal d0 d1 A H u → DigitVal d0 d1 (A * 2) (1 + H) (d0 :: u)
  | one {A H : Nat} {u : List Tok} : DigitVal d0 d1 A H u → DigitVal d0 d1 (1 + A * 2) (1 + H) (d1 :: u)

lemma digitVal_exists {Tok : Type*} (d0 d1 : Tok) (H : Nat) :
    ∀ A, A < 2 ^ H → ∃ u, DigitVal d0 d1 A H u := by
  induction H with
  | zero =>
    intro A hA
    have h0 : A = 0 := by omega
    subst h0; exact ⟨[], DigitVal.nil⟩
  | succ H ih =>
    intro A hA
    have hpow : 2 ^ (H + 1) = 2 ^ H * 2 := Nat.pow_succ 2 H
    have h1H : H + 1 = 1 + H := by omega
    rcases Nat.even_or_odd' A with ⟨a, rfl | rfl⟩
    · rcases ih a (by omega) with ⟨u, hI⟩
      have ha2 : 2 * a = a * 2 := Nat.mul_comm 2 a
      rw [h1H, ha2]; exact ⟨d0 :: u, DigitVal.zero hI⟩
    · rcases ih a (by omega) with ⟨u, hI⟩
      have ha2 : 2 * a + 1 = 1 + a * 2 := by omega
      rw [h1H, ha2]; exact ⟨d1 :: u, DigitVal.one hI⟩

lemma digitVal_append {Tok : Type*} {d0 d1 : Tok} {A H : Nat} {u : List Tok}
    (h1 : DigitVal d0 d1 A H u) :
    ∀ {B J : Nat} {v : List Tok},
      DigitVal d0 d1 B J v → DigitVal d0 d1 (A + B * 2 ^ H) (H + J) (u ++ v) := by
  induction h1 with
  | nil =>
    intro B J v h2
    simpa using h2
  | @zero A H u _ ih =>
    intro B J v h2
    have h3 := DigitVal.zero (ih h2)
    have heq1 : (A + B * 2 ^ H) * 2 = A * 2 + B * 2 ^ (1 + H) := by
      rw [Nat.add_comm 1 H, Nat.pow_succ]; ring
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    rwa [heq1, heq2] at h3
  | @one A H u _ ih =>
    intro B J v h2
    have h3 := DigitVal.one (ih h2)
    have heq1 : 1 + (A + B * 2 ^ H) * 2 = (1 + A * 2) + B * 2 ^ (1 + H) := by
      rw [Nat.add_comm 1 H, Nat.pow_succ]; ring
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    rwa [heq1, heq2] at h3

end BinaryCounterAlgebra

-- ============================================================================
-- 4B. Recursive Capacity Counter (`LTok`, `cap`, `dec_l`)
-- ============================================================================

section CapacityCounter

/-- Canonical 3-token alphabet for 1-mode capacity counters:
    `L0` (odd capacity `2c + 1`), `L1` (even capacity `2c`), `L2` (halving frame `c / 2`). -/
inductive LTok where
  | L0
  | L1
  | L2
  deriving DecidableEq, Repr

@[simp]
def cap : List LTok → Nat
  | [] => 0
  | .L0 :: l => 2 * cap l + 1
  | .L1 :: l => 2 * cap l
  | .L2 :: l => cap l / 2

@[simp]
def dec_l_fuel : Nat → List LTok → List LTok
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, .L0 :: l => .L1 :: l
  | n + 1, .L1 :: l => .L0 :: dec_l_fuel n l
  | n + 1, .L2 :: l => .L2 :: dec_l_fuel n (dec_l_fuel n l)

def dec_l (l : List LTok) : List LTok := dec_l_fuel l.length l

@[scoped simp]
lemma length_dec_l_fuel (n : Nat) (l : List LTok) : (dec_l_fuel n l).length = l.length := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons t tl => cases t <;> simp [dec_l_fuel, ih]

@[scoped simp]
lemma length_dec_l (l : List LTok) : (dec_l l).length = l.length :=
  length_dec_l_fuel l.length l

@[scoped simp] lemma dec_l_nil : dec_l [] = [] := rfl
@[scoped simp] lemma dec_l_L0 (l : List LTok) : dec_l (.L0 :: l) = .L1 :: l := rfl
@[scoped simp] lemma dec_l_L1 (l : List LTok) : dec_l (.L1 :: l) = .L0 :: dec_l l := rfl
@[scoped simp] lemma dec_l_L2 (l : List LTok) : dec_l (.L2 :: l) = .L2 :: dec_l (dec_l l) := by
  simp only [dec_l, List.length_cons, dec_l_fuel, length_dec_l_fuel]

lemma cap_dec_l_aux (n : Nat) :
    ∀ l : List LTok, l.length ≤ n → cap l ≥ 1 → cap (dec_l l) = cap l - 1 := by
  induction n with
  | zero =>
    intro l hlen h
    cases l <;> simp at hlen h
  | succ n ih =>
    intro l hlen h
    cases l with
    | nil => simp at h
    | cons t l =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      cases t with
      | L0 => simp
      | L1 =>
        simp only [cap, dec_l_L1] at h ⊢
        have h1 : cap l ≥ 1 := by omega
        rw [ih l hlen h1]; omega
      | L2 =>
        simp only [cap, dec_l_L2] at h ⊢
        have h2 : cap l ≥ 1 := by omega
        have ih1 := ih l hlen h2
        have h3 : cap (dec_l l) ≥ 1 := by omega
        have ih2 := ih (dec_l l) (by rw [length_dec_l]; exact hlen) h3
        rw [ih2, ih1]; omega

lemma cap_dec_l (l : List LTok) (h : cap l ≥ 1) : cap (dec_l l) = cap l - 1 :=
  cap_dec_l_aux l.length l (Nat.le_refl _) h

end CapacityCounter

-- ============================================================================
-- 4C. Multi-Stage Counter (`add_last`, `bump_enc`, `ValidKS`, `GoodKS`)
-- ============================================================================

section MultiStageCounter

def add_last : List ℕ → ℕ → List ℕ
  | [], _ => []
  | [x], c => [x + c]
  | x :: y :: rest, c => x :: add_last (y :: rest) c

lemma add_last_cons (x : ℕ) {ks : List ℕ} (hne : ks ≠ []) (c : ℕ) :
    add_last (x :: ks) c = x :: add_last ks c := by
  cases ks with
  | nil => contradiction
  | cons _ _ => rfl

@[scoped simp] lemma add_last_length : ∀ (ks : List ℕ) (c : ℕ), (add_last ks c).length = ks.length
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, _ => by simp [add_last, add_last_length]

@[scoped simp] lemma add_last_ne_nil : ∀ (ks : List ℕ) (c : ℕ), ks ≠ [] → add_last ks c ≠ []
  | [], _, h => absurd rfl h
  | [_], _, _ => by simp [add_last]
  | _ :: _ :: _, _, _ => by simp [add_last]

@[scoped simp] lemma add_last_zero : ∀ (ks : List ℕ), add_last ks 0 = ks
  | [] => rfl
  | [x] => by simp [add_last]
  | x :: y :: rest => by simp [add_last, add_last_zero]

lemma add_last_add : ∀ (ks : List ℕ) (a b : ℕ),
    add_last (add_last ks a) b = add_last ks (a + b)
  | [], _, _ => rfl
  | [x], a, b => by simp [add_last, Nat.add_assoc]
  | x :: y :: rest, a, b => by
    have hne : add_last (y :: rest) a ≠ [] := add_last_ne_nil (y :: rest) a (by simp)
    rw [add_last_cons x (by simp), add_last_cons x hne, add_last_cons x (by simp), add_last_add]

def bump_enc (k₀ : ℕ) : List ℕ → ℕ × List ℕ
  | [] => (k₀ + 3, [])
  | k₁ :: ks => (k₀, add_last (k₁ :: ks) 3)

def bump_enc_twice (m₀ : ℕ) (ms : List ℕ) : ℕ × List ℕ :=
  let p := bump_enc m₀ ms
  bump_enc p.1 p.2

lemma bump_enc_nonempty (k₀ : ℕ) {ks : List ℕ} (hne : ks ≠ []) :
    bump_enc k₀ ks = (k₀, add_last ks 3) := by
  cases ks with
  | nil => contradiction
  | cons _ _ => rfl

lemma bump_enc_twice_nonempty (m₀ : ℕ) {ms : List ℕ} (hne : ms ≠ []) :
    bump_enc_twice m₀ ms = (m₀, add_last ms 6) := by
  unfold bump_enc_twice
  rw [bump_enc_nonempty m₀ hne, bump_enc_nonempty m₀ (add_last_ne_nil ms 3 hne), add_last_add]

def ValidKS : List ℕ → Prop
  | [] => True
  | [_] => True
  | k :: k' :: rest => k ≥ 1 ∧ ValidKS (k' :: rest)

lemma ValidKS_add_last : ∀ (ks : List ℕ) (c : ℕ), ValidKS ks → ValidKS (add_last ks c)
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | k :: y :: rest, c, ⟨hk, hrest⟩ => by
    have hne : add_last (y :: rest) c ≠ [] := add_last_ne_nil (y :: rest) c (by simp)
    cases h_al : add_last (y :: rest) c with
    | nil => exact absurd h_al hne
    | cons z zs =>
      simp only [add_last, h_al, ValidKS]
      have h_ih := ValidKS_add_last (y :: rest) c hrest
      rw [h_al] at h_ih
      exact ⟨hk, h_ih⟩

lemma ValidKS_bump_enc (k₀ : ℕ) (ks : List ℕ) (h : ValidKS ks) : ValidKS (bump_enc k₀ ks).2 := by
  cases ks with
  | nil => trivial
  | cons k₁ rest => exact ValidKS_add_last (k₁ :: rest) 3 h

def GoodKS (s : ℕ) : List ℕ → Prop
  | [] => True
  | k :: rest => s ≤ 35 * (k + 2) ∧ GoodKS (s + 63 * (k + 2)) rest

lemma GoodKS_mono : ∀ (ks : List ℕ) (s₁ s₂ : ℕ), s₁ ≤ s₂ → GoodKS s₂ ks → GoodKS s₁ ks
  | [], _, _, _, _ => trivial
  | k :: rest, s₁, s₂, hle, ⟨h1, h2⟩ =>
    ⟨by omega, GoodKS_mono rest (s₁ + 63 * (k + 2)) (s₂ + 63 * (k + 2)) (by omega) h2⟩

lemma GoodKS_add_last : ∀ (ks : List ℕ) (s c : ℕ), GoodKS s ks → GoodKS s (add_last ks c)
  | [], _, _, _ => trivial
  | [k], s, c, ⟨h1, _⟩ => ⟨by omega, trivial⟩
  | k :: y :: rest, s, c, ⟨h1, h2⟩ =>
    ⟨h1, GoodKS_add_last (y :: rest) (s + 63 * (k + 2)) c h2⟩

lemma GoodKS_valid : ∀ (ks : List ℕ) (s : ℕ), s ≥ 71 → GoodKS s ks → ValidKS ks
  | [], _, _, _ => trivial
  | [_], _, _, _ => trivial
  | k :: y :: rest, s, hs, ⟨h1, h2⟩ =>
    ⟨by omega, GoodKS_valid (y :: rest) (s + 63 * (k + 2)) (by omega) h2⟩

lemma GoodKS_succ_valid (s w : ℕ) (ws : List ℕ) (h : GoodKS s ((w + 1) :: ws)) :
    ValidKS ((w + 1) :: ws) := by
  cases ws with
  | nil => trivial
  | cons y rest =>
    exact ⟨by omega, GoodKS_valid (y :: rest) (s + 63 * (w + 1 + 2)) (by omega) h.2⟩

def InvNil (k₀ : ℕ) (ks : List ℕ) : Prop :=
  (ks = [] ∧ k₀ ≥ 5) ∨
  (ks ≠ [] ∧ GoodKS (if k₀ = 1 then 81 else 36 * (k₀ + 2)) ks)

end MultiStageCounter

-- ============================================================================
-- 4D. Call-Stack Segment Counter (`Side`, `Seg`)
-- ============================================================================

section CallCounter

variable {Call Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Multi-call right-half-tape transduction relation parameterized by `CallStep`. -/
inductive Side (CallStep : Call → ListBlank Γ → ListBlank Γ → Prop) :
    List Call → ListBlank Γ → ListBlank Γ → Prop where
  | nil (r : ListBlank Γ) : Side CallStep [] r r
  | cons {c : Call} {ls : List Call} {r1 r2 r3 : ListBlank Γ} :
      CallStep c r1 r2 → Side CallStep ls r2 r3 → Side CallStep (c :: ls) r1 r3

/-- Segment transformer lifting `Side CallStep ls_out` to `Side CallStep ls_in` across finite words `w1 ↦ w2`. -/
def Seg (CallStep : Call → ListBlank Γ → ListBlank Γ → Prop)
    (ls_in ls_out : List Call) (w1 w2 : List Γ) : Prop :=
  ∀ r1 r2, Side CallStep ls_out r1 r2 → Side CallStep ls_in (w1 +> r1) (w2 +> r2)

lemma Side_append {CallStep : Call → ListBlank Γ → ListBlank Γ → Prop}
    {ls1 ls2 : List Call} {r1 r2 r3 : ListBlank Γ}
    (h1 : Side CallStep ls1 r1 r2) (h2 : Side CallStep ls2 r2 r3) :
    Side CallStep (ls1 ++ ls2) r1 r3 := by
  induction h1 with
  | nil _ => exact h2
  | cons hc _ ih => exact Side.cons hc (ih h2)

lemma Side_split {CallStep : Call → ListBlank Γ → ListBlank Γ → Prop}
    {ls1 ls2 : List Call} {r1 r3 : ListBlank Γ}
    (h : Side CallStep (ls1 ++ ls2) r1 r3) :
    ∃ r2, Side CallStep ls1 r1 r2 ∧ Side CallStep ls2 r2 r3 := by
  induction ls1 generalizing r1 with
  | nil => exact ⟨r1, Side.nil r1, h⟩
  | cons c ls1 ih =>
    rcases h with _ | ⟨hc, hrest⟩
    rcases ih hrest with ⟨r2, h1, h2⟩
    exact ⟨r2, Side.cons hc h1, h2⟩

lemma Seg_nil {CallStep : Call → ListBlank Γ → ListBlank Γ → Prop} (w : List Γ) :
    Seg CallStep [] [] w w := by
  intro r1 r2 h; cases h; exact Side.nil (w +> r1)

lemma Seg_refl {CallStep : Call → ListBlank Γ → ListBlank Γ → Prop} (ls : List Call) :
    Seg CallStep ls ls [] [] := by
  intro r1 r2 h; exact h

lemma Seg_apply {CallStep : Call → ListBlank Γ → ListBlank Γ → Prop}
    {ls1 ls2 : List Call} {w1 w2 : List Γ} {r1 r2 : ListBlank Γ}
    (h1 : Seg CallStep ls1 ls2 w1 w2) (h2 : Side CallStep ls2 r1 r2) :
    Side CallStep ls1 (w1 +> r1) (w2 +> r2) :=
  h1 r1 r2 h2

lemma Seg_par {CallStep : Call → ListBlank Γ → ListBlank Γ → Prop}
    {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : List Γ}
    (h1 : Seg CallStep ls1 ls2 w1 w2) (h2 : Seg CallStep ls3 ls4 w2 w3) :
    Seg CallStep (ls1 ++ ls3) (ls2 ++ ls4) w1 w3 := by
  intro r1 r3 h
  rcases Side_split h with ⟨r2, ha, hb⟩
  exact Side_append (h1 r1 r2 ha) (h2 r2 r3 hb)

lemma Seg_seq {CallStep : Call → ListBlank Γ → ListBlank Γ → Prop}
    {ls1 ls2 ls3 : List Call} {w1 w2 v1 v2 : List Γ}
    (h1 : Seg CallStep ls1 ls2 w1 w2) (h2 : Seg CallStep ls2 ls3 v1 v2) :
    Seg CallStep ls1 ls3 (w1 ++ v1) (w2 ++ v2) := by
  intro r1 r2 h
  rw [listblank_append_assoc, listblank_append_assoc]
  exact h1 (v1 +> r1) (v2 +> r2) (h2 r1 r2 h)

end CallCounter

-- ============================================================================
-- 5. General Non-Halting & Halting Era Closure Combinators
-- ============================================================================

section EraClosure

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

lemma isSome_step_of_multiStep_gt {M : Machine Γ Λ} {c₀ c c' : Cfg Γ Λ} {n M_steps : ℕ}
    (hn : multiStep M c₀ n = some c)
    (hM : multiStep M c₀ M_steps = some c')
    (h_lt : n < M_steps) :
    (step M c).isSome := by
  obtain ⟨d, hd⟩ : ∃ d, M_steps = (n + 1) + d := ⟨M_steps - (n + 1), by omega⟩
  rw [hd] at hM
  cases h_step : step M c with
  | some c₁ => simp
  | none =>
    have h_n1 : multiStep M c₀ (n + 1) = none := by
      rw [multiStep_succ, hn, Option.bind, h_step]
    have h_none : ∀ k, multiStep M c₀ ((n + 1) + k) = none := by
      intro k
      induction k with
      | zero => exact h_n1
      | succ k ih =>
        rw [Nat.add_succ, multiStep_succ, ih, Option.bind]
    rw [h_none d] at hM
    cases hM

theorem does_not_halt_of_arbitrarily_long {M : Machine Γ Λ}
    (h_long : ∀ N : ℕ, ∃ k ≥ N, ∃ c', (init []) [M]⊢^{k} c') :
    ∀ (cfg : Cfg Γ Λ), ((init []) [M]⊢* cfg) → (step M cfg).isSome := by
  intro cfg ⟨n, hn⟩
  obtain ⟨k, hk, c', hc'⟩ := h_long (n + 1)
  exact isSome_step_of_multiStep_gt hn hc' (by omega)

theorem does_not_halt_of_invariant {M : Machine Γ Λ} (Inv : Cfg Γ Λ → Prop)
    (h_init : ∃ c₀, ((init []) [M]⊢* c₀) ∧ Inv c₀)
    (h_step : ∀ c, Inv c → ∃ c', (c [M]⊢⁺ c') ∧ Inv c') :
    ∀ (cfg : Cfg Γ Λ), ((init []) [M]⊢* cfg) → (step M cfg).isSome := by
  rcases h_init with ⟨c₀, ⟨n₀, hn₀⟩, h_inv₀⟩
  have h_chain : ∀ m : ℕ, ∃ k ≥ m, ∃ c, (c₀ [M]⊢^{k} c) ∧ Inv c := by
    intro m
    induction m with
    | zero => exact ⟨0, by omega, c₀, rfl, h_inv₀⟩
    | succ m ih =>
      rcases ih with ⟨k, hk, c, hc, h_inv⟩
      rcases h_step c h_inv with ⟨c', ⟨d, hd, hc'⟩, h_inv'⟩
      exact ⟨k + d, by omega, c', multiStep_trans M c₀ c c' k d hc hc', h_inv'⟩
  apply does_not_halt_of_arbitrarily_long
  intro N
  rcases h_chain N with ⟨k, hk, c, hc, _⟩
  exact ⟨n₀ + k, by omega, c, multiStep_trans M (init []) c₀ c n₀ k hn₀ hc⟩

theorem does_not_halt_of_stepPlus_chain {M : Machine Γ Λ}
    (C : ℕ → Cfg Γ Λ) (i₀ : ℕ)
    (h_init : (init []) [M]⊢* C i₀)
    (h_chain : ∀ i ≥ i₀, (C i) [M]⊢⁺ (C (i + 1))) :
    ∀ (cfg : Cfg Γ Λ), ((init []) [M]⊢* cfg) → (step M cfg).isSome := by
  refine does_not_halt_of_invariant (fun cfg => ∃ i ≥ i₀, cfg = C i) ?_ ?_
  · exact ⟨C i₀, h_init, i₀, le_rfl, rfl⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨C (i + 1), h_chain i hi, i + 1, by omega, rfl⟩

def flipDir : Dir → Dir
  | Dir.left => Dir.right
  | Dir.right => Dir.left

def conjStmt (f : Bool) : Stmt Γ → Stmt Γ
  | ⟨w, d⟩ => ⟨w, if f then flipDir d else d⟩

def conjOut (σ : Λ → Λ) (f : Bool) :
    Option Λ × Stmt Γ → Option Λ × Stmt Γ
  | (q', st) => (q'.map σ, conjStmt f st)

def mirrorTape (f : Bool) (T : Tape Γ) : Tape Γ :=
  if f then ⟨T.head, T.right, T.left⟩ else T

def conjCfg (σ : Λ → Λ) (f : Bool) (c : Cfg Γ Λ) : Cfg Γ Λ :=
  ⟨c.q.map σ, mirrorTape f c.tape⟩

theorem head_mirrorTape (f : Bool) (T : Tape Γ) : (mirrorTape f T).head = T.head := by
  cases f <;> rfl

theorem mirrorTape_write (f : Bool) (T : Tape Γ) (w : Γ) :
    mirrorTape f (T.write w) = (mirrorTape f T).write w := by
  cases f <;> rfl

theorem mirrorTape_move (f : Bool) (T : Tape Γ) (d : Dir) :
    mirrorTape f (T.move d) = (mirrorTape f T).move (if f then flipDir d else d) := by
  cases f <;> cases d <;> rfl

theorem step_conj_of_tableIso {M_tgt M_src : Machine Γ Λ} {σ : Λ → Λ} {f : Bool}
    (h_iso : ∀ (q : Λ) (a : Γ), M_tgt (σ q) a = (M_src q a).map (conjOut σ f))
    (c : Cfg Γ Λ) :
    step M_tgt (conjCfg σ f c) = (step M_src c).map (conjCfg σ f) := by
  rcases c with ⟨_ | q, T⟩
  · rfl
  · simp only [conjCfg, step, Option.map_some, head_mirrorTape, h_iso q T.head, Option.map_map]
    congr 1
    funext ⟨q', w, d⟩
    simp only [Function.comp_apply, conjOut, conjStmt, conjCfg, mirrorTape_write, mirrorTape_move]

theorem multiStep_conj_of_tableIso {M_tgt M_src : Machine Γ Λ} {σ : Λ → Λ} {f : Bool}
    (h_iso : ∀ (q : Λ) (a : Γ), M_tgt (σ q) a = (M_src q a).map (conjOut σ f))
    (c : Cfg Γ Λ) (k : ℕ) :
    multiStep M_tgt (conjCfg σ f c) k = (multiStep M_src c k).map (conjCfg σ f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [multiStep_succ, multiStep_succ, ih]
    cases multiStep M_src c k with
    | none => rfl
    | some W => simp [step_conj_of_tableIso h_iso]

theorem does_not_halt_of_conj_invariant {M_tgt M_src : Machine Γ Λ} {σ : Λ → Λ} {f : Bool}
    (h_iso : ∀ (q : Λ) (a : Γ), M_tgt (σ q) a = (M_src q a).map (conjOut σ f))
    (Inv : Cfg Γ Λ → Prop)
    (h_init : ∃ c₀, ((init []) [M_tgt]⊢* conjCfg σ f c₀) ∧ Inv c₀)
    (h_step : ∀ c, Inv c → ∃ c', (c [M_src]⊢⁺ c') ∧ Inv c') :
    ∀ (cfg : Cfg Γ Λ), ((init []) [M_tgt]⊢* cfg) → (step M_tgt cfg).isSome := by
  refine does_not_halt_of_invariant (fun cfg => ∃ c, cfg = conjCfg σ f c ∧ Inv c) ?_ ?_
  · rcases h_init with ⟨c₀, h_reach, h_inv₀⟩
    exact ⟨conjCfg σ f c₀, h_reach, c₀, rfl, h_inv₀⟩
  · rintro _ ⟨c, rfl, h_inv⟩
    rcases h_step c h_inv with ⟨c', ⟨k, hk_pos, h_ms⟩, h_inv'⟩
    refine ⟨conjCfg σ f c', ⟨k, hk_pos, ?_⟩, c', rfl, h_inv'⟩
    rw [multiStep_conj_of_tableIso h_iso c k, h_ms, Option.map_some]

end EraClosure

-- ============================================================================
-- 9. Inductive Tape Binary Counter (RC and FC)
-- ============================================================================

section InductiveTapeCounter

def rd0 : List (Fin 2) := [0, 0, 0, 0]

@[scoped simp] lemma rd0_append_default : rd0 +> (default : ListBlank (Fin 2)) = default := by
  simp [rd0]

@[scoped simp] lemma three_zeros_append_default :
    ([0, 0, 0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default := by
  simp

inductive RC (d : List (Fin 2)) : Nat → ListBlank (Fin 2) → Prop
  | zero : RC d 0 default
  | d0 (n : Nat) (r : ListBlank (Fin 2)) : RC d n r → RC d (n * 2) (rd0 +> r)
  | d1 (n : Nat) (r : ListBlank (Fin 2)) : RC d n r → RC d (1 + n * 2) (d +> r)

inductive FC (d : List (Fin 2)) (tail : ListBlank (Fin 2)) : Nat → Nat → ListBlank (Fin 2) → Prop
  | nil : FC d tail 0 0 tail
  | d0 (k n : Nat) (r : ListBlank (Fin 2)) : FC d tail k n r → FC d tail (k + 1) (n * 2) (rd0 +> r)
  | d1 (k n : Nat) (r : ListBlank (Fin 2)) : FC d tail k n r → FC d tail (k + 1) (1 + n * 2) (d +> r)

lemma RC_eq {d : List (Fin 2)} {n m : Nat} {r s : ListBlank (Fin 2)}
    (h : RC d n r) (hn : n = m) (hr : r = s) : RC d m s := by
  subst hn; subst hr; exact h

lemma FC_eq {d : List (Fin 2)} {tail : ListBlank (Fin 2)} {k k' n n' : Nat} {r r' : ListBlank (Fin 2)}
    (h : FC d tail k n r) (hk : k = k') (hn : n = n') (hr : r = r') :
    FC d tail k' n' r' := by
  subst hk; subst hn; subst hr; exact h

lemma RC_zero_unique {d : List (Fin 2)} {r : ListBlank (Fin 2)} (h : RC d 0 r) : r = default := by
  generalize hn : (0 : Nat) = n at h
  induction h with
  | zero => rfl
  | d0 n r _ ih =>
    have hn0 : n = 0 := by omega
    rw [ih hn0.symm, rd0_append_default]
  | d1 _ _ _ _ => omega

lemma RC_inv_d0 {d : List (Fin 2)} {n : Nat} {s : ListBlank (Fin 2)} (hs : RC d (n * 2) s) :
    (n = 0 ∧ s = default) ∨ ∃ s0, s = rd0 +> s0 ∧ RC d n s0 := by
  generalize hm : n * 2 = m at hs
  cases hs with
  | zero => exact Or.inl ⟨by omega, rfl⟩
  | d0 n0 s0 hs0 =>
    have hn : n0 = n := by omega
    subst hn
    exact Or.inr ⟨s0, rfl, hs0⟩
  | d1 _ _ _ => omega

lemma RC_inv_d1 {d : List (Fin 2)} {n : Nat} {s : ListBlank (Fin 2)} (hs : RC d (1 + n * 2) s) :
    ∃ s0, s = d +> s0 ∧ RC d n s0 := by
  generalize hm : 1 + n * 2 = m at hs
  cases hs with
  | zero => omega
  | d0 _ _ _ => omega
  | d1 n0 s0 hs0 =>
    have hn : n0 = n := by omega
    subst hn
    exact ⟨s0, rfl, hs0⟩

lemma FC_inv_nil {d : List (Fin 2)} {tail : ListBlank (Fin 2)} {n : Nat} {s : ListBlank (Fin 2)}
    (hs : FC d tail 0 n s) : s = tail := by
  generalize hk : (0 : Nat) = k at hs
  cases hs with
  | nil => rfl
  | d0 _ _ _ _ => omega
  | d1 _ _ _ _ => omega

lemma FC_inv_d0 {d : List (Fin 2)} {tail : ListBlank (Fin 2)} {k n : Nat} {s : ListBlank (Fin 2)}
    (hs : FC d tail (k + 1) (n * 2) s) : ∃ s0, s = rd0 +> s0 ∧ FC d tail k n s0 := by
  generalize hk : k + 1 = K, hm : n * 2 = m at hs
  cases hs with
  | nil => omega
  | d0 k0 n0 s0 hs0 =>
    have hk0 : k0 = k := by omega
    have hn0 : n0 = n := by omega
    subst hk0; subst hn0
    exact ⟨s0, rfl, hs0⟩
  | d1 _ _ _ _ => omega

lemma FC_inv_d1 {d : List (Fin 2)} {tail : ListBlank (Fin 2)} {k n : Nat} {s : ListBlank (Fin 2)}
    (hs : FC d tail (k + 1) (1 + n * 2) s) : ∃ s0, s = d +> s0 ∧ FC d tail k n s0 := by
  generalize hk : k + 1 = K, hm : 1 + n * 2 = m at hs
  cases hs with
  | nil => omega
  | d0 _ _ _ _ => omega
  | d1 k0 n0 s0 hs0 =>
    have hk0 : k0 = k := by omega
    have hn0 : n0 = n := by omega
    subst hk0; subst hn0
    exact ⟨s0, rfl, hs0⟩

lemma RC_unique {d : List (Fin 2)} {n : Nat} {r s : ListBlank (Fin 2)}
    (hr : RC d n r) (hs : RC d n s) : r = s := by
  induction hr generalizing s with
  | zero => exact (RC_zero_unique hs).symm
  | d0 n r hr ih =>
    rcases RC_inv_d0 hs with ⟨rfl, rfl⟩ | ⟨s0, rfl, hs0⟩
    · rw [RC_zero_unique hr, rd0_append_default]
    · rw [ih hs0]
  | d1 n r _ ih =>
    rcases RC_inv_d1 hs with ⟨s0, rfl, hs0⟩
    rw [ih hs0]

lemma FC_unique {d : List (Fin 2)} {tail : ListBlank (Fin 2)} {k n : Nat} {r s : ListBlank (Fin 2)}
    (hr : FC d tail k n r) (hs : FC d tail k n s) : r = s := by
  induction hr generalizing s with
  | nil => exact (FC_inv_nil hs).symm
  | d0 k n r _ ih =>
    rcases FC_inv_d0 hs with ⟨s0, rfl, hs0⟩
    rw [ih hs0]
  | d1 k n r _ ih =>
    rcases FC_inv_d1 hs with ⟨s0, rfl, hs0⟩
    rw [ih hs0]

lemma pow2_pos (k : Nat) : 0 < 2 ^ k := Nat.two_pow_pos k

lemma FC_zero (d : List (Fin 2)) (tail : ListBlank (Fin 2)) (k : Nat) :
    FC d tail k 0 (rd0 ^ k +> tail) := by
  induction k with
  | zero => exact FC.nil
  | succ k ih =>
    rw [right_pow_succ rd0 k tail]
    exact FC_eq (FC.d0 k 0 (rd0 ^ k +> tail) ih) rfl (by omega) rfl

lemma FC_full (d : List (Fin 2)) (tail : ListBlank (Fin 2)) (k : Nat) :
    FC d tail k (2 ^ k - 1) (d ^ k +> tail) := by
  induction k with
  | zero => exact FC.nil
  | succ k ih =>
    have hp := pow2_pos k
    rw [right_pow_succ d k tail]
    exact FC_eq (FC.d1 k (2 ^ k - 1) (d ^ k +> tail) ih) rfl (by rw [Nat.pow_succ]; omega) rfl

lemma FC_full_unique {d : List (Fin 2)} {tail : ListBlank (Fin 2)} {k : Nat} {r : ListBlank (Fin 2)}
    (h : FC d tail k (2 ^ k - 1) r) : r = d ^ k +> tail :=
  FC_unique h (FC_full d tail k)

lemma FC_RC {d : List (Fin 2)} {tail : ListBlank (Fin 2)} {k n : Nat} {r : ListBlank (Fin 2)} {m : Nat}
    (hf : FC d tail k n r) (hr : RC d m tail) : RC d (n + 2 ^ k * m) r := by
  induction hf with
  | nil => exact RC_eq hr (by omega) rfl
  | d0 k n r _ ih => exact RC_eq (RC.d0 (n + 2 ^ k * m) r ih) (by rw [Nat.pow_succ]; ring) rfl
  | d1 k n r _ ih => exact RC_eq (RC.d1 (n + 2 ^ k * m) r ih) (by rw [Nat.pow_succ]; ring) rfl

lemma RC_zeros {d : List (Fin 2)} {n : Nat} {r : ListBlank (Fin 2)} (k : Nat) (hr : RC d n r) :
    RC d (2 ^ k * n) (rd0 ^ k +> r) := by
  simpa using FC_RC (FC_zero d r k) hr

lemma RC_carry {d : List (Fin 2)} {n : Nat} {r : ListBlank (Fin 2)} (h : RC d n r) :
    ∃ (k : Nat) (s : ListBlank (Fin 2)),
      r = d ^ k +> (rd0 +> s) ∧ RC d (n + 1) (rd0 ^ k +> (d +> s)) := by
  induction h with
  | zero =>
    refine ⟨(0 : Nat), default, ?_, ?_⟩
    · simp
    · exact RC_eq (RC.d1 0 default RC.zero) (by omega) rfl
  | d0 n r hr _ =>
    exact ⟨(0 : Nat), r, rfl, RC_eq (RC.d1 n r hr) (by omega) rfl⟩
  | d1 n r _ ih =>
    rcases ih with ⟨k, s, rfl, hs⟩
    refine ⟨k + 1, s, ?_, ?_⟩
    · rw [right_pow_succ d k (rd0 +> s)]
    · rw [right_pow_succ rd0 k (d +> s)]
      exact RC_eq (RC.d0 (n + 1) (rd0 ^ k +> (d +> s)) hs) (by omega) rfl

lemma RC_positive_split {d : List (Fin 2)} {n : Nat} {r : ListBlank (Fin 2)}
    (h : RC d n r) (hn : 0 < n) :
    ∃ t q s, r = rd0 ^ t +> (d +> s) ∧ RC d q s ∧ n = 2 ^ t * (1 + q * 2) ∧ q < n := by
  induction h with
  | zero => omega
  | d0 n r _ ih =>
    rcases ih (by omega) with ⟨t, q, s, rfl, hs, heq, hlt⟩
    refine ⟨t + 1, q, s, ?_, hs, ?_, by omega⟩
    · rw [right_pow_succ rd0 t (d +> s)]
    · rw [Nat.pow_succ, heq]; ring
  | d1 n r hr _ =>
    exact ⟨0, n, r, rfl, hr, by omega, by omega⟩

lemma FC_carry {d : List (Fin 2)} {tail : ListBlank (Fin 2)} {k n : Nat} {r : ListBlank (Fin 2)}
    (h : FC d tail k n r) (hb : n + 1 < 2 ^ k) :
    ∃ j s, j < k ∧ r = d ^ j +> (rd0 +> s) ∧ FC d tail k (n + 1) (rd0 ^ j +> (d +> s)) := by
  induction h with
  | nil => simp at hb
  | d0 k n r hr _ =>
    exact ⟨0, r, by omega, rfl, FC_eq (FC.d1 k n r hr) rfl (by omega) rfl⟩
  | d1 k n r _ ih =>
    have hb' : n + 1 < 2 ^ k := by rw [Nat.pow_succ] at hb; omega
    rcases ih hb' with ⟨j, s, hj, rfl, hs⟩
    refine ⟨j + 1, s, by omega, ?_, ?_⟩
    · rw [right_pow_succ d j (rd0 +> s)]
    · rw [right_pow_succ rd0 j (d +> s)]
      exact FC_eq (FC.d0 k (n + 1) (rd0 ^ j +> (d +> s)) hs) rfl (by omega) rfl

lemma zero3_rd0 (n : Nat) (r : ListBlank (Fin 2)) :
    ([0, 0, 0] : List (Fin 2)) +> (rd0 ^ n +> r) = rd0 ^ n +> ([0, 0, 0] +> r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [right_pow_succ rd0 n r, right_pow_succ rd0 n ([0, 0, 0] +> r), ← ih]
    rfl

lemma one_zero_comm_rd0_pow (t : Nat) (s : ListBlank (Fin 2)) :
    ([0] : List (Fin 2)) +> (rd0 ^ t +> s) = rd0 ^ t +> ([0] +> s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [right_pow_succ rd0 t s, right_pow_succ rd0 t ([0] +> s), ← ih]
    rfl

end InductiveTapeCounter

-- ============================================================================
-- 10. Base-4 Separator Odometer
-- ============================================================================

section Base4SeparatorOdometer

/-- 3-Step Composition helper for stepPlus transitions. -/
lemma stepPlus_trans3 {α : Type*} {stepPlus : α → α → Prop}
    (htrans : ∀ {a b c : α}, stepPlus a b → stepPlus b c → stepPlus a c)
    {a b c d : α} (h1 : stepPlus a b) (h2 : stepPlus b c) (h3 : stepPlus c d) :
    stepPlus a d :=
  htrans h1 (htrans h2 h3)

/-- Abstract 4-Phase Base-4 Separator Odometer Cycle (`[0] ↦ [2] ↦ [0, 2] ↦ [3] ↦ carry`):
    Chains the 4 odometer phase transitions into a single multi-step transition:
    - Phase 1: `(0 :: 1 :: R) ↦ (2 :: R)` with `m ↦ m + 1`
    - Phase 2: `(2 :: 1 :: R) ↦ (0 :: 2 :: R)` with `m ↦ m + 1`
    - Phase 3: `(0 :: 2 :: R) ↦ (3 :: R)` with `m ↦ m + 1`
    - Phase 4: `(3 :: R) ↦ carry` with `m ↦ m + 1`
    yielding `(0 :: 1 :: 1 :: R) ↦ carry` with `m ↦ m + 4`. -/
theorem odom_full_cycle_stepPlus
    {α : Type*} {stepPlus : α → α → Prop}
    (htrans : ∀ {a b c : α}, stepPlus a b → stepPlus b c → stepPlus a c)
    (cfgB : ℕ → List ℕ → α) (carryCfg : ℕ → List ℕ → α)
    (h02 : ∀ m R, stepPlus (cfgB m (0 :: 1 :: R)) (cfgB (m + 1) (2 :: R)))
    (h2_02 : ∀ m R, stepPlus (cfgB m (2 :: 1 :: R)) (cfgB (m + 1) (0 :: 2 :: R)))
    (h02_3 : ∀ m R, stepPlus (cfgB m (0 :: 2 :: R)) (cfgB (m + 1) (3 :: R)))
    (h3_carry : ∀ m R, stepPlus (cfgB m (3 :: R)) (carryCfg (m + 1) R))
    (m : ℕ) (R : List ℕ) :
    stepPlus (cfgB m (0 :: 1 :: 1 :: R)) (carryCfg (m + 4) R) := by
  have s1 := h02 m (1 :: R)
  have s2 := h2_02 (m + 1) R
  have s3 := h02_3 (m + 2) R
  have s4 := h3_carry (m + 3) R
  exact htrans s1 (htrans s2 (htrans s3 s4))

/-- Concrete 4-Phase Base-4 Separator Odometer Cycle for Turing Machine configurations. -/
theorem odom_full_cycle_compose
    {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (tm : Machine Γ Λ)
    (cfgB : ℕ → List ℕ → Cfg Γ Λ) (carryCfg : ℕ → List ℕ → Cfg Γ Λ)
    (h02 : ∀ m R, (cfgB m (0 :: 1 :: R)) [tm]⊢⁺ (cfgB (m + 1) (2 :: R)))
    (h2_02 : ∀ m R, (cfgB m (2 :: 1 :: R)) [tm]⊢⁺ (cfgB (m + 1) (0 :: 2 :: R)))
    (h02_3 : ∀ m R, (cfgB m (0 :: 2 :: R)) [tm]⊢⁺ (cfgB (m + 1) (3 :: R)))
    (h3_carry : ∀ m R, (cfgB m (3 :: R)) [tm]⊢⁺ (carryCfg (m + 1) R))
    (m : ℕ) (R : List ℕ) :
    (cfgB m (0 :: 1 :: 1 :: R)) [tm]⊢⁺ (carryCfg (m + 4) R) := by
  have s1 := h02 m (1 :: R)
  have s2 := h2_02 (m + 1) R
  have s3 := h02_3 (m + 2) R
  have s4 := h3_carry (m + 3) R
  exact stepPlus_trans s1 (stepPlus_trans s2 (stepPlus_trans s3 s4))

/-- Inductive right-stack grammar `ValidOdomR` for Base-4 Separator Odometer sweeps. -/
inductive ValidOdomR : List ℕ → Prop
  | end_nil : ValidOdomR []
  | end_one : ValidOdomR [1]
  | cons_one (d : ℕ) (R : List ℕ) : ValidOdomR (d :: R) → ValidOdomR (1 :: d :: R)
  | cons_three (R : List ℕ) : ValidOdomR R → ValidOdomR (3 :: R)
  | cons_five (R : List ℕ) : ValidOdomR (1 :: R) → ValidOdomR (5 :: 1 :: 1 :: R)

/-- Complete Phase-2 right-stack grammar `ValidPhase2R` covering all 5 Phase-2 blocks
    and terminal/separator suffixes (`[]`, `[1]`, `[2]`, `0 :: R`, including
    `[0]`, `[1, 0]`, and `[1, 1, 0]`). -/
inductive ValidPhase2R : List ℕ → Prop
  | end_nil : ValidPhase2R []
  | end_one : ValidPhase2R [1]
  | end_two : ValidPhase2R [2]
  | end_zero (R : List ℕ) : ValidPhase2R (0 :: R)
  | end_two_cons (d : ℕ) (R : List ℕ) : ValidPhase2R (2 :: d :: R)
  | end_four_one (R : List ℕ) : ValidPhase2R (4 :: 1 :: R)
  | cons_one (d : ℕ) (R : List ℕ) : ValidPhase2R (d :: R) → ValidPhase2R (1 :: d :: R)
  | cons_three (R : List ℕ) : ValidPhase2R R → ValidPhase2R (3 :: R)
  | cons_five (R : List ℕ) : ValidPhase2R (1 :: R) → ValidPhase2R (5 :: 1 :: 1 :: R)

theorem validOdomR_imp_validPhase2R (R : List ℕ) (hR : ValidOdomR R) : ValidPhase2R R := by
  induction hR with
  | end_nil => exact .end_nil
  | end_one => exact .end_one
  | cons_one d R' _ ih => exact .cons_one d R' ih
  | cons_three R' _ ih => exact .cons_three R' ih
  | cons_five R' _ ih => exact .cons_five R' ih

theorem validPhase2R_zero : ValidPhase2R [0] := .end_zero []

theorem validPhase2R_one_zero : ValidPhase2R [1, 0] := .cons_one 0 [] (.end_zero [])

theorem validPhase2R_one_one_zero : ValidPhase2R [1, 1, 0] :=
  .cons_one 1 [0] (.cons_one 0 [] (.end_zero []))

/-- Any run of `1`s followed by `0 :: R` satisfies `ValidPhase2R`. -/
theorem replicate_one_zero_validPhase2R (k : ℕ) (R : List ℕ) :
    ValidPhase2R (List.replicate k 1 ++ (0 :: R)) := by
  induction k with
  | zero => exact .end_zero R
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    cases hrep : List.replicate k 1 ++ (0 :: R) with
    | nil =>
      have hlen := congrArg List.length hrep
      simp at hlen
    | cons d R' =>
      rw [hrep] at ih
      exact .cons_one d R' ih

end Base4SeparatorOdometer

end BusyBeaver.Counter
