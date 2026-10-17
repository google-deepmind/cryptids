/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`.

## Collatz-like Acceleration Rules
P1(a, 0) -> P1(2, a + 1)
P1(a, 1) -> P1(a + 2, 0)
P1(2m, d + 2) -> P1(2m + 3, d)
P1(2m + 1, 2) -> Halt
P1(2m + 1, 3) -> P2(m, 1, 0)
P1(2m + 1, d + 4) -> P2(m, 2, d)
P2(0, m, 0) -> P1(0, 2m + 3)
P2(k + 1, m, 0) -> P2(k, 0, 2m + 3)
P2(k, m, 1) -> P2(k, m + 1, 0)
P2(0, m, d + 2) -> P1(2m + 4, d)
P2(k + 1, m, d + 2) -> P2(k, m + 2, d)
-/


@[expose] public section

namespace BusyBeaver.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE

open SixState Turing Relation

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

local notation c₁ " [" M "]⊢ " c₂ => step M c₁ = some c₂
local notation c₁ " [" M "]⊢^{" n "} " c₂ => multiStep M c₁ n = some c₂
local notation c₁ " [" M "]⊢* " c₂ => ∃ n, multiStep M c₁ n = some c₂
local notation c₁ " [" M "]⊢⁺ " c₂ => ∃ n > 0, multiStep M c₁ n = some c₂

local notation l " {{" s "}} " r => (⟨s, l, r⟩ : Tape _)
local notation:67 s:67 " << " a:68 => ListBlank.cons a s
local infixr:67 " >> " => ListBlank.cons
local notation:67 s:67 " <+ " l:68 => ListBlank.append l s
local infixr:67 " +> " => ListBlank.append
macro l:term " {{" q:term "}}> " r:term : term => `(Cfg.headRight $q $l $r)
macro l:term " <{{" q:term "}} " r:term : term => `(Cfg.headLeft $q $l $r)

@[simp] lemma pow_zero_list (l : List (Fin 2)) : l ^ (0 : Nat) = [] := list_pow_zero l
@[simp] lemma pow_succ_list (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l
  ++ (l ^ n) := list_pow_succ l n
@[simp] lemma cons_append_list (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs)
  ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma append_nil_list (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x ::
  xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

abbrev stepPlus_stepStar {c₁ c₂ : Cfg (Fin 2) (Fin 6)} (h₁ : c₁ [target]⊢⁺ c₂) : c₁ [target]⊢* c₂ :=
  ReachesPlus.to_star h₁

abbrev step_stepStar_stepPlus {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target]⊢ c₂) (h₂ : c₂ [target]⊢* c₃) : c₁ [target]⊢⁺ c₃ :=
  ReachesPlus.head h₁ h₂

abbrev stepPlus_stepStar_stepPlus {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target]⊢⁺ c₂) (h₂ : c₂ [target]⊢* c₃) : c₁ [target]⊢⁺ c₃ :=
  ReachesPlus.trans_star h₁ h₂

abbrev stepStar_stepPlus_stepPlus {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target]⊢* c₂) (h₂ : c₂ [target]⊢⁺ c₃) : c₁ [target]⊢⁺ c₃ :=
  ReachesStar.trans_plus h₁ h₂

abbrev stepPlus_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target]⊢⁺ c₂) (h₂ : c₂ [target]⊢⁺ c₃) : c₁ [target]⊢⁺ c₃ :=
  ReachesPlus.trans h₁ h₂

abbrev stepStar_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target]⊢* c₂) (h₂ : c₂ [target]⊢* c₃) : c₁ [target]⊢* c₃ :=
  ReachesStar.trans h₁ h₂

lemma listblank_append_append (s : ListBlank Γ) (l₁ l₂ : List Γ) :
    (s <+ l₁) <+ l₂ = s <+ (l₂ ++ l₁) := by
  unfold ListBlank.append
  split
  · split
    · next h => simp_all
    · simp_all
  · rename_i _ l₂ l₁
    refine (congr_arg _ ?_).symm
    exact ListBlank.append_assoc l₁ _ s

lemma pow_add_append_right (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add, ← listblank_append_append]

lemma pow_succ_append_right (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [pow_succ_list, ← listblank_append_append]

lemma pow_add_append_left (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [listblank_append_append, ← list_pow_add, add_comm]

lemma pow_one_two_mul_left (m : Nat) (l : ListBlank (Fin 2)) :
    (l <+ ([1] : List (Fin 2))^(2 * m)) = (l <+ ([1, 1] : List (Fin 2))^m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h_eq : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [h_eq, pow_add_append_left l ([1] : List (Fin 2)) (2 * m) 2, ih]
    rw [pow_add_append_left l ([1, 1] : List (Fin 2)) m 1]
    rfl

lemma pow_one_two_mul_right (m : Nat) (r : ListBlank (Fin 2)) :
    (([1] : List (Fin 2))^(2 * m) +> r) = (([1, 1] : List (Fin 2))^m +> r) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h_eq : 2 * (m + 1) = 2 + 2 * m := by omega
    rw [h_eq, pow_add_append_right ([1] : List (Fin 2)) 2 (2 * m) r, ih]
    have h_eq2 : m + 1 = 1 + m := by omega
    rw [h_eq2, pow_add_append_right ([1, 1] : List (Fin 2)) 1 m r]
    rfl

lemma zero_cons_10_pow_one (m : Nat) (r : ListBlank (Fin 2)) :
    (([0] : List (Fin 2)) +> (([1, 0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> r))) =
    (([0, 1] : List (Fin 2))^(m + 1) +> r) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ_append_right ([1, 0] : List (Fin 2)) m (([1] : List (Fin 2)) +> r)]
    have h_head : (([0] : List (Fin 2)) +> (([1, 0] : List (Fin 2)) +> (([1,
      0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> r)))) =
        (([0, 1] : List (Fin 2)) +> (([0] : List (Fin 2)) +> (([1,
          0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> r)))) := rfl
    rw [h_head, ih, ← pow_succ_append_right ([0, 1] : List (Fin 2)) (m + 1) r]

lemma one_append_10_pow (k : Nat) :
    (((default : ListBlank (Fin 2)) << (1 : Fin 2)) <+ ([1, 0] : List (Fin 2))^k) =
    (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2))^k) << (1 : Fin 2)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_add_append_left ((default : ListBlank (Fin 2)) << (1 : Fin 2)) ([1,
      0] : List (Fin 2)) k 1, ih]
    rw [pow_add_append_left (default : ListBlank (Fin 2)) ([0, 1] : List (Fin 2)) k 1]
    rfl

macro "finish" : tactic =>
  `(tactic| (
    try simp only [Cfg.headRight, Cfg.headLeft, init, ListBlank.head_cons, ListBlank.tail_cons,
      zero_cons_default, default_head, default_tail, ListBlank.head_default,
      ListBlank.tail_default, ListBlank.cons_default_default, ListBlank.cons_zero_default]
    exact ⟨0, rfl⟩))
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus (by
      try simp only [Cfg.headRight, Cfg.headLeft, init, ListBlank.head_cons, default_head]
      rfl) ?_ <;>
    simp only [Tape.move, Tape.write, ListBlank.head_cons, ListBlank.tail_cons,
      zero_cons_default, default_head, default_tail, ListBlank.head_default,
      ListBlank.tail_default, ListBlank.cons_default_default, ListBlank.cons_zero_default])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

-- ============================================================================
-- Inductive Shift Lemmas for Suspect 55
-- ============================================================================

/-- `C>` scanning `1` shifts leftward over `1^k`, preserving `1^k` on the right. -/
lemma shift_C_left (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1] : List (Fin 2))^k) {{C}}> (([1] : List (Fin 2)) +> r)) [target]⊢*
    (l {{C}}> (([1] : List (Fin 2))^k +> (([1] : List (Fin 2)) +> r))) := by
  induction k generalizing l r with
  | zero =>
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : (l <+ ([1] : List (Fin 2))^(k + 1)) =
        ((l <+ ([1] : List (Fin 2))^k) <+ ([1] : List (Fin 2))) := by
      rw [pow_add_append_left l ([1] : List (Fin 2)) k 1]; rfl
    rw [h_split]
    have h1 : (((l <+ ([1] : List (Fin 2))^k)
      <+ ([1] : List (Fin 2))) {{C}}> (([1] : List (Fin 2)) +> r))
        [target]⊢⁺
        ((l <+ ([1] : List (Fin 2))^k) {{C}}> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))
          +> r))) := by
      simp only [listblank_append_cons, listblank_append_nil]
      execute
    have h2 := ih l (([1] : List (Fin 2)) +> r)
    have h12 := stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)
    have h_comb : (([1] : List (Fin 2))^k +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))
      +> r))) =
        (([1] : List (Fin 2))^(k + 1) +> (([1] : List (Fin 2)) +> r)) := by
      have h_eq : k + 1 = k + 1 := rfl
      rw [pow_add_append_right ([1] : List (Fin 2)) k 1 (([1] : List (Fin 2)) +> r)]
      rfl
    rwa [h_comb] at h12

/-- `E>` scanning `1` shifts leftward over `(11)^k`,
  turning each `(11)` into `(10)` on the right. -/
lemma shift_ED_left (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 1] : List (Fin 2))^k) {{E}}> (([1] : List (Fin 2)) +> r)) [target]⊢*
    (l {{E}}> (([1] : List (Fin 2)) +> (([1, 0] : List (Fin 2))^k +> r))) := by
  induction k generalizing l r with
  | zero =>
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : (l <+ ([1, 1] : List (Fin 2))^(k + 1)) =
        ((l <+ ([1, 1] : List (Fin 2))^k) <+ ([1, 1] : List (Fin 2))) := by
      rw [pow_add_append_left l ([1, 1] : List (Fin 2)) k 1]; rfl
    rw [h_split]
    have h1 : (((l <+ ([1, 1] : List (Fin 2))^k) <+ ([1,
      1] : List (Fin 2))) {{E}}> (([1] : List (Fin 2)) +> r))
        [target]⊢⁺
        ((l <+ ([1, 1] : List (Fin 2))^k) {{E}}> (([1] : List (Fin 2)) +> (([1,
          0] : List (Fin 2)) +> r))) := by
      simp only [listblank_append_cons, listblank_append_nil]
      execute
    have h2 := ih l (([1, 0] : List (Fin 2)) +> r)
    have h12 := stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)
    have h_comb : (([1, 0] : List (Fin 2))^k +> (([1, 0] : List (Fin 2)) +> r)) =
        (([1, 0] : List (Fin 2))^(k + 1) +> r) := by
      rw [pow_add_append_right ([1, 0] : List (Fin 2)) k 1 r]; rfl
    rwa [h_comb] at h12

/-- `A>` shifts rightward over `(01)^k`, writing `(11)^k` on the left. -/
lemma shift_AB_right (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{A}}> (([0, 1] : List (Fin 2))^k +> r)) [target]⊢*
    ((l <+ ([1, 1] : List (Fin 2))^k) {{A}}> r) := by
  induction k generalizing l r with
  | zero =>
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split := pow_succ_append_right ([0, 1] : List (Fin 2)) k r
    rw [h_split]
    have h1 : (l {{A}}> (([0, 1] : List (Fin 2)) +> (([0, 1] : List (Fin 2))^k +> r)))
        [target]⊢⁺
        ((l <+ ([1, 1] : List (Fin 2))) {{A}}> (([0, 1] : List (Fin 2))^k +> r)) := by
      simp only [listblank_append_cons, listblank_append_nil]
      execute
    have h2 := ih (l <+ ([1, 1] : List (Fin 2))) r
    have h12 := stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)
    have h_comb : ((l <+ ([1, 1] : List (Fin 2))) <+ ([1, 1] : List (Fin 2))^k) =
        (l <+ ([1, 1] : List (Fin 2))^(k + 1)) := by
      have h_eq : k + 1 = 1 + k := by omega
      rw [h_eq, pow_add_append_left l ([1, 1] : List (Fin 2)) 1 k]; rfl
    rwa [h_comb] at h12

/-- `F>` shifts rightward over `(10)^k`, writing `(01)^k` (`[1, 0]^k` on the left stack). -/
lemma shift_FE_right (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{F}}> (([1, 0] : List (Fin 2))^k +> r)) [target]⊢*
    ((l <+ ([1, 0] : List (Fin 2))^k) {{F}}> r) := by
  induction k generalizing l r with
  | zero =>
    exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split := pow_succ_append_right ([1, 0] : List (Fin 2)) k r
    rw [h_split]
    have h1 : (l {{F}}> (([1, 0] : List (Fin 2)) +> (([1, 0] : List (Fin 2))^k +> r)))
        [target]⊢⁺
        ((l <+ ([1, 0] : List (Fin 2))) {{F}}> (([1, 0] : List (Fin 2))^k +> r)) := by
      simp only [listblank_append_cons, listblank_append_nil]
      execute
    have h2 := ih (l <+ ([1, 0] : List (Fin 2))) r
    have h12 := stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)
    have h_comb : ((l <+ ([1, 0] : List (Fin 2))) <+ ([1, 0] : List (Fin 2))^k) =
        (l <+ ([1, 0] : List (Fin 2))^(k + 1)) := by
      have h_eq : k + 1 = 1 + k := by omega
      rw [h_eq, pow_add_append_left l ([1, 0] : List (Fin 2)) 1 k]; rfl
    rwa [h_comb] at h12

-- ============================================================================
-- Section 7: Canonical 2-Hub Pattern Set (`P1`, `P2`) & 11 Macro-Rules
-- ============================================================================

/-- Hub Pattern 1: `P1(a, c) := 0^∞ 1^a A> 1^c 0^∞` (`a, c ∈ ℕ`). -/
def pat_P1 : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1] 0 .default
    head  := some A
    right := .rep [1] 1 .default }

/-- Hub Pattern 2: `P2(k, m, c) := 0^∞ (10)^(k+1) (11)^m A> 1^c 0^∞` (`k, m, c ∈ ℕ`). -/
def pat_P2 : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1, 1] 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head  := some A
    right := .rep [1] 2 .default }

/-- The closed 2-hub pattern set `ps`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P1, .true), (pat_P2, .true)]

def cfg_P1 (a c : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((default <+ ([1] : List (Fin 2))^a) {{A}}> (([1] : List (Fin 2))^c +> default))

def cfg_P2 (k m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((((default <+ ([0, 1] : List (Fin 2))^k) << 1) << 0) <+ ([1, 1] : List (Fin 2))^m) {{A}}>
   (([1] : List (Fin 2))^c +> default))

lemma eval_pat_P1 (vars : Nat → Nat) :
    evalTapePattern pat_P1 vars = cfg_P1 (vars 0) (vars 1) := rfl

lemma eval_pat_P2 (vars : Nat → Nat) :
    evalTapePattern pat_P2 vars = cfg_P2 (vars 0) (vars 1) (vars 2) := rfl

lemma in_ps_P1 (a c : Nat) : IsInPatternSet ps (cfg_P1 a c) := by
  refine ⟨(pat_P1, .true), List.Mem.head _, (fun i => match i with | 0 => a | _ => c), rfl, trivial⟩

lemma in_ps_P2 (k m c : Nat) : IsInPatternSet ps (cfg_P2 k m c) := by
  refine ⟨(pat_P2, .true), List.Mem.tail _ (List.Mem.head _),
    (fun i => match i with | 0 => k | 1 => m | _ => c), rfl, trivial⟩

/-- Rule 1 (`P1, c = 0`): `P1(a, 0) -> P1(2, a + 1)` in `a + 6` steps. -/
theorem rule_1 (a : Nat) :
    (cfg_P1 a 0) [target]⊢⁺ (cfg_P1 2 (a + 1)) := by
  have h1 : (cfg_P1 a 0) [target]⊢⁺
      ((default <+ ([1] : List (Fin 2))^a) {{C}}> (([1] : List (Fin 2)) +> default)) := by
    unfold cfg_P1
    simp only [pow_zero_list, listblank_append_cons, listblank_append_nil]
    execute
  have h2 := shift_C_left a default default
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 : (default {{C}}> (([1] : List (Fin 2))^a +> (([1] : List (Fin 2)) +> default)))
      [target]⊢⁺ (cfg_P1 2 (a + 1)) := by
    unfold cfg_P1
    have h_r : (([1] : List (Fin 2))^a +> (([1] : List (Fin 2)) +> (default : ListBlank (Fin 2)))) =
        (([1] : List (Fin 2))^(a + 1) +> default) := by
      rw [pow_add_append_right ([1] : List (Fin 2)) a 1 default]; rfl
    rw [h_r]
    simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
      listblank_append_cons, listblank_append_nil]
    execute
  exact stepPlus_trans h12 h3

/-- Rule 2 (`P1, c = 1`): `P1(a, 1) -> P1(a + 2, 0)` in `2` steps. -/
theorem rule_2 (a : Nat) :
    (cfg_P1 a 1) [target]⊢⁺ (cfg_P1 (a + 2) 0) := by
  unfold cfg_P1
  rw [pow_add_append_left default ([1] : List (Fin 2)) a 2]
  simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
    listblank_append_cons, listblank_append_nil]
  execute

/-- Rule 3 (`P1, a = 2m, c = d + 2`): `P1(2m, d + 2) -> P1(2m + 3, d)` in `4m + 6` steps. -/
theorem rule_3 (m d : Nat) :
    (cfg_P1 (2 * m) (d + 2)) [target]⊢⁺ (cfg_P1 (2 * m + 3) d) := by
  have h1 : (cfg_P1 (2 * m) (d + 2)) [target]⊢⁺
      ((default <+ ([1,
        1] : List (Fin 2))^m) {{E}}> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))
        +> (([1] : List (Fin 2))^d +> default)))) := by
    unfold cfg_P1
    rw [pow_one_two_mul_left m default]
    have h_eq : d + 2 = 2 + d := by omega
    rw [h_eq, pow_add_append_right ([1] : List (Fin 2)) 2 d default]
    simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
      listblank_append_cons, listblank_append_nil]
    execute
  have h2 := shift_ED_left m default (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default))
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 : (default {{E}}> (([1] : List (Fin 2)) +> (([1,
    0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default)))))
      [target]⊢⁺
      ((default << 1) {{A}}> (([0] : List (Fin 2)) +> (([1,
        0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d
        +> default))))) := by
    simp only [listblank_append_cons, listblank_append_nil]
    execute
  have h123 := stepPlus_trans h12 h3
  rw [zero_cons_10_pow_one m (([1] : List (Fin 2))^d +> default)] at h123
  have h4 := shift_AB_right (m + 1) (default << 1) (([1] : List (Fin 2))^d +> default)
  have h1234 := stepPlus_stepStar_stepPlus h123 h4
  have h_l : ((default << 1) <+ ([1, 1] : List (Fin 2))^(m + 1)) =
      (default <+ ([1] : List (Fin 2))^(2 * m + 3)) := by
    rw [← pow_one_two_mul_left (m + 1) (default << 1)]
    have h_d : ((default : ListBlank (Fin 2)) << (1 : Fin 2)) = default
      <+ ([1] : List (Fin 2))^1 := rfl
    rw [h_d, ← pow_add_append_left default ([1] : List (Fin 2)) 1 (2 * (m + 1))]
    have h_eq : 1 + 2 * (m + 1) = 2 * m + 3 := by omega
    rw [h_eq]
  unfold cfg_P1
  rwa [h_l] at h1234

/-- Common prefix for Rules 4, 5, 6 (`a = 2m + 1, c = d + 2`): reaches `E>` in `4m + 8` steps. -/
lemma odd_P1_to_E (m d : Nat) :
    (cfg_P1 (2 * m + 1) (d + 2)) [target]⊢⁺
    ((default <+ ([0, 1] : List (Fin 2))^(m + 2)) {{E}}> (([1] : List (Fin 2))^d +> default)) := by
  have h_l0 : (default <+ ([1] : List (Fin 2))^(2 * m + 1)) =
      ((default << 1) <+ ([1, 1] : List (Fin 2))^m) := by
    have h_eq : 2 * m + 1 = 1 + 2 * m := by omega
    rw [h_eq, pow_add_append_left default ([1] : List (Fin 2)) 1 (2 * m)]
    rw [pow_one_two_mul_left m (default <+ ([1] : List (Fin 2))^1)]
    rfl
  have h1 : (cfg_P1 (2 * m + 1) (d + 2)) [target]⊢⁺
      (((default << 1) <+ ([1,
        1] : List (Fin 2))^m) {{E}}> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))
        +> (([1] : List (Fin 2))^d +> default)))) := by
    unfold cfg_P1
    rw [h_l0]
    have h_eq : d + 2 = 2 + d := by omega
    rw [h_eq, pow_add_append_right ([1] : List (Fin 2)) 2 d default]
    simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
      listblank_append_cons, listblank_append_nil]
    execute
  have h2 := shift_ED_left m (default << 1) (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d
    +> default))
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 : ((default << 1) {{E}}> (([1] : List (Fin 2)) +> (([1,
    0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default)))))
      [target]⊢⁺
      ((default << 1) {{F}}> (([1,
        0] : List (Fin 2))^(m + 1) +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d
        +> default)))) := by
    rw [pow_succ_append_right ([1,
      0] : List (Fin 2)) m (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default))]
    simp only [listblank_append_cons, listblank_append_nil]
    execute
  have h123 := stepPlus_trans h12 h3
  have h4 := shift_FE_right (m + 1) (default << 1) (([1] : List (Fin 2))
    +> (([1] : List (Fin 2))^d +> default))
  have h1234 := stepPlus_stepStar_stepPlus h123 h4
  rw [one_append_10_pow (m + 1)] at h1234
  have h5 : (((default <+ ([0,
    1] : List (Fin 2))^(m + 1)) << 1) {{F}}> (([1] : List (Fin 2))
    +> (([1] : List (Fin 2))^d +> default)))
      [target]⊢⁺
      ((default <+ ([0,
        1] : List (Fin 2))^(m + 2)) {{E}}> (([1] : List (Fin 2))^d +> default)) := by
    rw [pow_add_append_left default ([0, 1] : List (Fin 2)) (m + 1) 1]
    simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
      listblank_append_cons, listblank_append_nil]
    execute
  exact stepPlus_trans h1234 h5

/-- Rule 4 (`P1, a = 2m + 1, c = 2`): `P1(2m + 1, 2)` halts in `4m + 9` steps. -/
theorem rule_4_halt (m : Nat) :
    ∃ cfg', ((cfg_P1 (2 * m + 1) 2) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  refine ⟨(((default <+ ([0, 1] : List (Fin 2))^(m + 2)) << 1) {{F}}> default), ?_, rfl⟩
  have h1 := odd_P1_to_E m 0
  have h2 : ((default <+ ([0,
    1] : List (Fin 2))^(m + 2)) {{E}}> (([1] : List (Fin 2))^0 +> default))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^(m + 2)) << 1) {{F}}> default) := by
    simp only [pow_zero_list, listblank_append_nil]
    execute
  exact stepPlus_trans h1 h2

/-- Rule 5 (`P1, a = 2m + 1, c = 3`): `P1(2m + 1, 3) -> P2(m, 1, 0)` in `4m + 10` steps. -/
theorem rule_5 (m : Nat) :
    (cfg_P1 (2 * m + 1) 3) [target]⊢⁺ (cfg_P2 m 1 0) := by
  have h1 := odd_P1_to_E m 1
  have h2 : ((default <+ ([0,
    1] : List (Fin 2))^(m + 2)) {{E}}> (([1] : List (Fin 2))^1 +> default))
      [target]⊢⁺ (cfg_P2 m 1 0) := by
    unfold cfg_P2
    rw [pow_add_append_left default ([0, 1] : List (Fin 2)) (m + 1) 1]
    rw [pow_add_append_left default ([0, 1] : List (Fin 2)) m 1]
    simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
      listblank_append_cons, listblank_append_nil]
    execute
  exact stepPlus_trans h1 h2

/-- Rule 6 (`P1, a = 2m + 1, c = d + 4`): `P1(2m + 1, d + 4) -> P2(m, 2, d)` in `4m + 12` steps. -/
theorem rule_6 (m d : Nat) :
    (cfg_P1 (2 * m + 1) (d + 4)) [target]⊢⁺ (cfg_P2 m 2 d) := by
  have h1 := odd_P1_to_E m (d + 2)
  have h2 : ((default <+ ([0,
    1] : List (Fin 2))^(m + 2)) {{E}}> (([1] : List (Fin 2))^(d + 2) +> default))
      [target]⊢⁺ (cfg_P2 m 2 d) := by
    unfold cfg_P2
    rw [pow_add_append_left default ([0, 1] : List (Fin 2)) (m + 1) 1]
    rw [pow_add_append_left default ([0, 1] : List (Fin 2)) m 1]
    have h_eq : d + 2 = 2 + d := by omega
    rw [h_eq, pow_add_append_right ([1] : List (Fin 2)) 2 d default]
    simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
      listblank_append_cons, listblank_append_nil]
    execute
  exact stepPlus_trans h1 h2

/-- Common lemma for Rules 7 and 8 (`P2, c = 0`): `(((l << 1) << 0) <+ [1,
  1]^m) A> default -> l A> ([1]^(2m + 3) +> default)`. -/
lemma rule_P2_c0 (l : ListBlank (Fin 2)) (m : Nat) :
    (((((l << 1) << 0) <+ ([1, 1] : List (Fin 2))^m) {{A}}> default)) [target]⊢⁺
    (l {{A}}> (([1] : List (Fin 2))^(2 * m + 3) +> default)) := by
  have h1 : (((((l << 1) << 0) <+ ([1, 1] : List (Fin 2))^m) {{A}}> default)) [target]⊢⁺
      ((((l << 1) << 0) <+ ([1] : List (Fin 2))^(2 * m)) {{C}}> (([1] : List (Fin 2))
        +> default)) := by
    rw [pow_one_two_mul_left m ((l << 1) << 0)]
    simp only [listblank_append_cons, listblank_append_nil]
    execute
  have h2 := shift_C_left (2 * m) ((l << 1) << 0) default
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 : (((l << 1) << 0) {{C}}> (([1] : List (Fin 2))^(2 * m) +> (([1] : List (Fin 2))
    +> default)))
      [target]⊢⁺
      (l {{A}}> (([1] : List (Fin 2))^(2 * m + 3) +> default)) := by
    have h_r1 : (([1] : List (Fin 2))^(2 * m) +> (([1] : List (Fin 2))
      +> (default : ListBlank (Fin 2)))) =
        (([1] : List (Fin 2))^(2 * m + 1) +> default) := by
      rw [pow_add_append_right ([1] : List (Fin 2)) (2 * m) 1 default]; rfl
    have h_r2 : (([1] : List (Fin 2))^(2 * m + 3) +> (default : ListBlank (Fin 2))) =
        (([1] : List (Fin 2))^2 +> (([1] : List (Fin 2))^(2 * m + 1) +> default)) := by
      have h_eq : 2 * m + 3 = 2 + (2 * m + 1) := by omega
      rw [h_eq, pow_add_append_right ([1] : List (Fin 2)) 2 (2 * m + 1) default]
    rw [h_r1, h_r2]
    simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
      listblank_append_cons, listblank_append_nil]
    execute
  exact stepPlus_trans h12 h3

/-- Rule 7 (`P2, k = 0, c = 0`): `P2(0, m, 0) -> P1(0, 2m + 3)` in `2m + 4` steps. -/
theorem rule_7 (m : Nat) :
    (cfg_P2 0 m 0) [target]⊢⁺ (cfg_P1 0 (2 * m + 3)) := by
  unfold cfg_P2 cfg_P1
  simp only [pow_zero_list, listblank_append_nil]
  exact rule_P2_c0 default m

/-- Rule 8 (`P2, k = k' + 1, c = 0`): `P2(k' + 1, m, 0) -> P2(k', 0, 2m + 3)` in `2m + 4` steps. -/
theorem rule_8 (k' m : Nat) :
    (cfg_P2 (k' + 1) m 0) [target]⊢⁺ (cfg_P2 k' 0 (2 * m + 3)) := by
  unfold cfg_P2
  rw [pow_add_append_left default ([0, 1] : List (Fin 2)) k' 1]
  simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
    listblank_append_cons, listblank_append_nil]
  exact rule_P2_c0 (((default <+ ([0, 1] : List (Fin 2))^k') << 1) << 0) m

/-- Rule 9 (`P2, c = 1`): `P2(k, m, 1) -> P2(k, m + 1, 0)` in `2` steps. -/
theorem rule_9 (k m : Nat) :
    (cfg_P2 k m 1) [target]⊢⁺ (cfg_P2 k (m + 1) 0) := by
  unfold cfg_P2
  rw [pow_add_append_left (((default <+ ([0, 1] : List (Fin 2))^k) << 1) << 0) ([1,
    1] : List (Fin 2)) m 1]
  simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
    listblank_append_cons, listblank_append_nil]
  execute

/-- Common lemma for Rules 10 and 11 (`P2, c = d + 2`): `(((l << 1) << 0) <+ [1,
  1]^m) A> ([1]^(d + 2) +> default) -> (l <+ [1, 1]^(m + 2)) A> ([1]^d +> default)`. -/
lemma rule_P2_c2 (l : ListBlank (Fin 2)) (m d : Nat) :
    (((((l << 1) << 0) <+ ([1,
      1] : List (Fin 2))^m) {{A}}> (([1] : List (Fin 2))^(d + 2) +> default))) [target]⊢⁺
    ((l <+ ([1, 1] : List (Fin 2))^(m + 2)) {{A}}> (([1] : List (Fin 2))^d +> default)) := by
  have h1 : (((((l << 1) << 0) <+ ([1,
    1] : List (Fin 2))^m) {{A}}> (([1] : List (Fin 2))^(d + 2) +> default))) [target]⊢⁺
      ((((l << 1) << 0) <+ ([1,
        1] : List (Fin 2))^m) {{E}}> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))
        +> (([1] : List (Fin 2))^d +> default)))) := by
    have h_eq : d + 2 = 2 + d := by omega
    rw [h_eq, pow_add_append_right ([1] : List (Fin 2)) 2 d default]
    simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
      listblank_append_cons, listblank_append_nil]
    execute
  have h2 := shift_ED_left m ((l << 1) << 0) (([1] : List (Fin 2))
    +> (([1] : List (Fin 2))^d +> default))
  have h12 := stepPlus_stepStar_stepPlus h1 h2
  have h3 : (((l << 1) << 0) {{E}}> (([1] : List (Fin 2)) +> (([1,
    0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default)))))
      [target]⊢⁺
      ((l <+ ([1, 1] : List (Fin 2))) {{A}}> (([0] : List (Fin 2)) +> (([1,
        0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d
        +> default))))) := by
    simp only [listblank_append_cons, listblank_append_nil]
    execute
  have h123 := stepPlus_trans h12 h3
  rw [zero_cons_10_pow_one m (([1] : List (Fin 2))^d +> default)] at h123
  have h4 := shift_AB_right (m + 1) (l <+ ([1,
    1] : List (Fin 2))) (([1] : List (Fin 2))^d +> default)
  have h1234 := stepPlus_stepStar_stepPlus h123 h4
  have h_l : ((l <+ ([1, 1] : List (Fin 2))) <+ ([1, 1] : List (Fin 2))^(m + 1)) =
      (l <+ ([1, 1] : List (Fin 2))^(m + 2)) := by
    have h_eq : m + 2 = 1 + (m + 1) := by omega
    rw [h_eq, pow_add_append_left l ([1, 1] : List (Fin 2)) 1 (m + 1)]; rfl
  rwa [h_l] at h1234

/-- Rule 10 (`P2, k = 0, c = d + 2`): `P2(0, m, d + 2) -> P1(2m + 4, d)` in `4m + 6` steps. -/
theorem rule_10 (m d : Nat) :
    (cfg_P2 0 m (d + 2)) [target]⊢⁺ (cfg_P1 (2 * m + 4) d) := by
  unfold cfg_P2 cfg_P1
  simp only [pow_zero_list, listblank_append_nil]
  have h := rule_P2_c2 default m d
  have h_eq : 2 * m + 4 = 2 * (m + 2) := by omega
  rw [h_eq, pow_one_two_mul_left (m + 2) default]
  exact h

/-- Rule 11 (`P2, k = k' + 1, c = d + 2`): `P2(k' + 1, m, d + 2) -> P2(k', m + 2,
  d)` in `4m + 6` steps. -/
theorem rule_11 (k' m d : Nat) :
    (cfg_P2 (k' + 1) m (d + 2)) [target]⊢⁺ (cfg_P2 k' (m + 2) d) := by
  unfold cfg_P2
  rw [pow_add_append_left default ([0, 1] : List (Fin 2)) k' 1]
  simp only [pow_zero_list, pow_succ_list, cons_append_list, List.nil_append,
    listblank_append_cons, listblank_append_nil]
  exact rule_P2_c2 (((default <+ ([0, 1] : List (Fin 2))^k') << 1) << 0) m d

-- ============================================================================
-- Section 8: Blank-Tape Entry & Complete Closure Proof (`IsCryptid`)
-- ============================================================================

/-- Blank initial tape `init []` is `cfg_P1 0 0` and reaches `cfg_P1 2 1` in 6 steps. -/
theorem init_reaches_P1 : (init []) [target]⊢* (cfg_P1 2 1) := by
  have h : (init [] : Cfg (Fin 2) (Fin 6)) = cfg_P1 0 0 := by
    unfold init cfg_P1
    simp only [pow_zero_list, listblank_append_nil]
    rfl
  rw [h]
  exact stepPlus_stepStar (rule_1 0)

theorem audit_ps_nonempty : ∃ cfg, IsInPatternSet ps cfg :=
  ⟨cfg_P1 2 1, in_ps_P1 2 1⟩

theorem audit_init_neq_cfg0 :
    (init [] : Cfg (Fin 2) (Fin 6)) ≠ cfg_P1 2 1 := by
  intro h
  have h_r : (init [] : Cfg (Fin 2) (Fin 6)).tape.head = (cfg_P1 2 1).tape.head :=
    congr_arg (fun c => c.tape.head) h
  revert h_r
  decide

/-- Parity partition of `a ∈ ℕ` into `2 * m` or `2 * m + 1`. -/
lemma nat_even_or_odd_two_mul (a : Nat) : (∃ m, a = 2 * m) ∨ (∃ m, a = 2 * m + 1) := by
  induction a with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ a ih =>
    rcases ih with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact Or.inr ⟨m, rfl⟩
    · exact Or.inl ⟨m + 1, by omega⟩

/-- Complete closure of Hub 1 (`cfg_P1 a c`) across all `(a, c) ∈ ℕ²` (Rules 1–6). -/
theorem step_P1_all (a c : Nat) :
    ∃ cfg', ((cfg_P1 a c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases c with _ | c1
  · -- c = 0: Rule 1
    exact ⟨cfg_P1 2 (a + 1), rule_1 a, Or.inl (in_ps_P1 2 (a + 1))⟩
  · rcases c1 with _ | d
    · -- c = 1: Rule 2
      exact ⟨cfg_P1 (a + 2) 0, rule_2 a, Or.inl (in_ps_P1 (a + 2) 0)⟩
    · -- c = d + 2
      rcases nat_even_or_odd_two_mul a with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · -- a = 2 * m, c = d + 2: Rule 3
        exact ⟨cfg_P1 (2 * m + 3) d, rule_3 m d, Or.inl (in_ps_P1 (2 * m + 3) d)⟩
      · -- a = 2 * m + 1, c = d + 2
        rcases d with _ | d1
        · -- c = 2: Rule 4 (Halt)
          obtain ⟨cfg', h_plus, h_halt⟩ := rule_4_halt m
          exact ⟨cfg', h_plus, Or.inr h_halt⟩
        · rcases d1 with _ | d2
          · -- c = 3: Rule 5
            exact ⟨cfg_P2 m 1 0, rule_5 m, Or.inl (in_ps_P2 m 1 0)⟩
          · -- c = d2 + 4: Rule 6
            exact ⟨cfg_P2 m 2 d2, rule_6 m d2, Or.inl (in_ps_P2 m 2 d2)⟩

/-- Complete closure of Hub 2 (`cfg_P2 k m c`) across all `(k, m, c) ∈ ℕ³` (Rules 7–11). -/
theorem step_P2_all (k m c : Nat) :
    ∃ cfg', ((cfg_P2 k m c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases c with _ | c1
  · -- c = 0
    rcases k with _ | k'
    · -- k = 0, c = 0: Rule 7
      exact ⟨cfg_P1 0 (2 * m + 3), rule_7 m, Or.inl (in_ps_P1 0 (2 * m + 3))⟩
    · -- k = k' + 1, c = 0: Rule 8
      exact ⟨cfg_P2 k' 0 (2 * m + 3), rule_8 k' m, Or.inl (in_ps_P2 k' 0 (2 * m + 3))⟩
  · rcases c1 with _ | d
    · -- c = 1: Rule 9
      exact ⟨cfg_P2 k (m + 1) 0, rule_9 k m, Or.inl (in_ps_P2 k (m + 1) 0)⟩
    · -- c = d + 2
      rcases k with _ | k'
      · -- k = 0, c = d + 2: Rule 10
        exact ⟨cfg_P1 (2 * m + 4) d, rule_10 m d, Or.inl (in_ps_P1 (2 * m + 4) d)⟩
      · -- k = k' + 1, c = d + 2: Rule 11
        exact ⟨cfg_P2 k' (m + 2) d, rule_11 k' m d, Or.inl (in_ps_P2 k' (m + 2) d)⟩

-- ============================================================================
-- Section 9: Countdown Acceleration & Base-2 (2^n) Exponential Macro-Transitions
-- ============================================================================

/-- Countdown acceleration of Rule 11:
    `P₂(k + j, m, d + 2j) ⊢* P₂(k, m + 2j, d)` in `j` sweeps. -/
theorem countdown_P2 : ∀ (j k m d : Nat),
    (cfg_P2 (k + j) m (d + 2 * j)) [target]⊢* (cfg_P2 k (m + 2 * j) d)
  | 0, k, m, d => ⟨0, rfl⟩
  | j + 1, k, m, d => by
    have h1 : k + (j + 1) = (k + j) + 1 := by omega
    have h2 : d + 2 * (j + 1) = (d + 2 * j) + 2 := by omega
    have h3 : (m + 2) + 2 * j = m + 2 * (j + 1) := by omega
    rw [h1, h2, ← h3]
    exact stepStar_trans (stepPlus_stepStar (rule_11 (k + j) m (d + 2 * j)))
      (countdown_P2 j k (m + 2) d)

/-- 1-cycle doubling step on `P₂(k, 2, d)`:
    `P₂(k, 2, d + 2k + 8) ⊢⁺ P₂(2k + 5, 2,
      d)` via `countdown_P2` + `rule_10` + `rule_3` + `rule_6`. -/
theorem double_P2 (k d : Nat) :
    (cfg_P2 k 2 (d + 2 * k + 8)) [target]⊢⁺ (cfg_P2 (2 * k + 5) 2 d) := by
  have h1 := countdown_P2 k 0 2 (d + 8)
  simp only [Nat.zero_add] at h1
  have h_in : d + 2 * k + 8 = d + 8 + 2 * k := by omega
  have h_m : 2 + 2 * k = 2 * k + 2 := by omega
  rw [← h_in, h_m] at h1
  have h2 := rule_10 (2 * k + 2) (d + 6)
  have h_d8 : (d + 6) + 2 = d + 8 := by omega
  have h_p1 : 2 * (2 * k + 2) + 4 = 2 * (2 * k + 4) := by omega
  rw [h_d8, h_p1] at h2
  have h3 := rule_3 (2 * k + 4) (d + 4)
  have h_d6 : (d + 4) + 2 = d + 6 := by omega
  have h_p1_odd : 2 * (2 * k + 4) + 3 = 2 * (2 * k + 5) + 1 := by omega
  rw [h_d6, h_p1_odd] at h3
  have h4 := rule_6 (2 * k + 5) d
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_trans h2 (stepPlus_trans h3 h4))

/-- Relational predicate for Base-2 (`2^n`) exponential doubling on `P₂(k, 2, d)`. -/
def ExpRelP2 (k d_cost k_out : Nat) : Prop :=
  ∀ d : Nat, (cfg_P2 k 2 (d + d_cost)) [target]⊢* (cfg_P2 k_out 2 d)

theorem ExpRelP2_zero (k : Nat) : ExpRelP2 k 0 k := by
  intro d; rw [Nat.add_zero]; exact ⟨0, rfl⟩

theorem ExpRelP2_succ {k d_cost k_out : Nat} (h : ExpRelP2 k d_cost k_out) :
    ExpRelP2 k (d_cost + 2 * k_out + 8) (2 * k_out + 5) := by
  intro d
  have h_eq : d + (d_cost + 2 * k_out + 8) = (d + 2 * k_out + 8) + d_cost := by omega
  rw [h_eq]
  exact stepStar_trans (h (d + 2 * k_out + 8)) (stepPlus_stepStar (double_P2 k_out d))

theorem mul_pow2_ge (k n : Nat) : (k + 5) * 2 ^ n ≥ k + n + 5 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    omega

theorem ExpRelP2_pow2 (n k : Nat) :
    ExpRelP2 k (2 * ((k + 5) * 2 ^ n) - 2 * k - 2 * n - 10) ((k + 5) * 2 ^ n - 5) := by
  induction n with
  | zero =>
    have h1 : 2 * ((k + 5) * 2 ^ 0) - 2 * k - 2 * 0 - 10 = 0 := by omega
    have h2 : (k + 5) * 2 ^ 0 - 5 = k := by omega
    rw [h1, h2]
    exact ExpRelP2_zero k
  | succ n ih =>
    have h_ge := mul_pow2_ge k n
    have h_pow : (k + 5) * 2 ^ (n + 1) = ((k + 5) * 2 ^ n) * 2 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
    have h_step := ExpRelP2_succ ih
    have h1 : 2 * ((k + 5) * 2 ^ n) - 2 * k - 2 * n - 10 + 2 * ((k + 5) * 2 ^ n - 5) + 8 =
              2 * ((k + 5) * 2 ^ (n + 1)) - 2 * k - 2 * (n + 1) - 10 := by
      rw [h_pow]; omega
    have h2 : 2 * ((k + 5) * 2 ^ n - 5) + 5 = (k + 5) * 2 ^ (n + 1) - 5 := by
      rw [h_pow]; omega
    rw [h1, h2] at h_step
    exact h_step

/-- Base-2 (`2^n`) Exponential Macro-Transition on `P₂` for `suspect_55`:
    `P₂(k, 2, d + (2(k + 5) * 2^n - 2k - 2n - 10)) ⊢* P₂((k + 5) * 2^n - 5, 2, d)`. -/
theorem exp_step_P2 (n k d : Nat) :
    (cfg_P2 k 2 (d + (2 * ((k + 5) * 2 ^ n) - 2 * k - 2 * n - 10))) [target]⊢*
    (cfg_P2 ((k + 5) * 2 ^ n - 5) 2 d) :=
  ExpRelP2_pow2 n k d

/-- Base-2 (`2^n`) Exponential Macro-Transition from `P₁` to `P₂` for `suspect_55`:
    `P₁(2k + 1, d + (2(k + 5) * 2^n - 2k - 2n - 10) + 4) ⊢⁺ P₂((k + 5) * 2^n - 5, 2, d)`. -/
theorem exp_step_P1_to_P2 (n k d : Nat) :
    (cfg_P1 (2 * k + 1) (d + (2 * ((k + 5) * 2 ^ n) - 2 * k - 2 * n - 10) + 4)) [target]⊢⁺
    (cfg_P2 ((k + 5) * 2 ^ n - 5) 2 d) :=
  stepPlus_stepStar_stepPlus
    (rule_6 k (d + (2 * ((k + 5) * 2 ^ n) - 2 * k - 2 * n - 10)))
    (exp_step_P2 n k d)

-- END EXPLORATORY DEFINITIONS AND LEMMAS


theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_P1 2 1, init_reaches_P1, in_ps_P1 2 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  rcases h_mem with ⟨⟩ | ⟨_, ⟨⟩ | ⟨_, h_mem⟩⟩
  · rw [eval_pat_P1]
    exact step_P1_all (vars 0) (vars 1)
  · rw [eval_pat_P2]
    exact step_P2_all (vars 0) (vars 1) (vars 2)
  · nomatch h_mem

theorem has_collatz_reduction : HasCollatzReduction target := ⟨ps, is_closed_pattern_set⟩

inductive State
  | P_1 (a c : Nat)
  | P_2 (k m c : Nat)

def start : State := .P_1 2 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 a c => evalTapePattern pat_P1 (fun | 0 => a | 1 => c | _ => 0)
  | .P_2 k m c => evalTapePattern pat_P2 (fun | 0 => k | 1 => m | 2 => c | _ => 0)

def next : State → Option State
  | .P_1 a 0 => some (.P_1 2 (a + 1))
  | .P_1 a 1 => some (.P_1 (a + 2) 0)
  | .P_1 a (c + 2) =>
    match a % 2 with
    | 0 => some (.P_1 (a + 3) c)
    | _ => match c with
      | 0 => none
      | 1 => some (.P_2 (a / 2) 1 0)
      | d + 2 => some (.P_2 (a / 2) 2 d)
  | .P_2 k m 1 => some (.P_2 k (m + 1) 0)
  | .P_2 0 m 0 => some (.P_1 0 (2 * m + 3))
  | .P_2 (k + 1) m 0 => some (.P_2 k 0 (2 * m + 3))
  | .P_2 0 m (d + 2) => some (.P_1 (2 * m + 4) d)
  | .P_2 (k + 1) m (d + 2) => some (.P_2 k (m + 2) d)

private theorem step_state : ∀ s : State,
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone = true
  | .P_1 a 0 => rule_1 a
  | .P_1 a 1 => rule_2 a
  | .P_1 a (c + 2) => by
    have ha : (∃ m, a = 2 * m) ∨ (∃ m, a = 2 * m + 1) := nat_even_or_odd_two_mul a
    cases ha with
    | inl h =>
      rcases h with ⟨m, rfl⟩
      have h1 : (2 * m) % 2 = 0 := by omega
      simp only [next, h1]
      exact rule_3 m c
    | inr h =>
      rcases h with ⟨m, rfl⟩
      have h1 : (2 * m + 1) % 2 = 1 := by omega
      have h2 : (2 * m + 1) / 2 = m := by omega
      simp only [next, h1, h2]
      cases c with
      | zero =>
        have hh := rule_4_halt m
        rcases hh with ⟨cfg', hp, hd⟩
        exact ⟨cfg', stepPlus_stepStar hp, hd⟩
      | succ c =>
        cases c with
        | zero => exact rule_5 m
        | succ d => exact rule_6 m d
  | .P_2 k m 1 => rule_9 k m
  | .P_2 0 m 0 => rule_7 m
  | .P_2 (k + 1) m 0 => rule_8 k m
  | .P_2 0 m (d + 2) => rule_10 m d
  | .P_2 (k + 1) m (d + 2) => rule_11 k m d

theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_P1
  step_some := fun s s' hnext => by
    have h := step_state s
    rw [hnext] at h
    exact h
  step_none := fun s hnext => by
    have h := step_state s
    rw [hnext] at h
    exact h

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE
