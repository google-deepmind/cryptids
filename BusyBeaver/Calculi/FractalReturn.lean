/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Calculi.Longitudinal
import Mathlib.Tactic.Ring

/-!
# Symbolic Executor with Shift-Rule Acceleration (`BusyBeaver.FractalReturn`)

Reusable infrastructure extracted from BusyCoq's `ES_v3.v` verification library:

1. **Block-Power & Half-Tape Algebraic Helpers**:
   - `lpow_shift`, `lpow_all0`, and half-tape normalization lemmas over `Longitudinal`.

2. **Reflective Symbolic Executor with Shift-Rule Acceleration (`ES`)**:
   - Port of BusyCoq's `ES_v3.v` (`VSide`, `VConfig`, `vconfigEs`, `vconfigEs_spec`,
     `checkEs_spec_star`, `checkEs_spec_plus`) with $O(1)$ accumulator-based block rotation
     (`vsideRwLpowRotateAux`), enabling `by decide` discharge of symbolic execution lemmas without
     `native_decide`.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.Longitudinal

namespace BusyBeaver.FractalReturn


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

-- 2. Block-Power & Half-Tape Algebraic Helpers
-- ============================================================================

private theorem lb_head_default : (default : ListBlank Γ).head = default := rfl

private theorem lb_tail_default : (default : ListBlank Γ).tail = default := rfl

private theorem lb_cons_default :
    ListBlank.cons (default : Γ) (default : ListBlank Γ) = default :=
  ListBlank.cons_head_tail (default : ListBlank Γ)

omit [Inhabited Γ] [Inhabited Λ] in
theorem lpow_shift {α : Type*} (w : List α) (n : ℕ) :
    (w ^ n) ++ w = w ++ (w ^ n) := by
  rw [← pow_succ_list', ← pow_succ_list]

omit [Inhabited Λ] in
theorem lpow_add' (a : Γ) (m n : ℕ) (s : ListBlank Γ) :
    ([a] ^ m) +> (([a] ^ n) +> s) = ([a] ^ (m + n)) +> s := by
  rw [pow_add_list, append_assoc]

omit [Inhabited Γ] [Inhabited Λ] in
theorem lpow_rotate_list (h : Γ) (t : List Γ) (n : ℕ) :
    ((h :: t) ^ n) ++ [h] = h :: ((t ++ [h]) ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list, List.append_assoc, ih, pow_succ_list]
    simp

omit [Inhabited Λ] in
theorem lpow_rotate (h : Γ) (t : List Γ) (n : ℕ) (x : ListBlank Γ) :
    ((h :: t) ^ n) +> (h >> x) = h >> (((t ++ [h]) ^ n) +> x) := by
  have h1 : (h >> x) = [h] +> x := rfl
  rw [h1, ← append_assoc, lpow_rotate_list]
  rfl

omit [Inhabited Λ] in
theorem lpow_shift1 (h : Γ) (n : ℕ) (x : ListBlank Γ) :
    ([h] ^ n) +> (h >> x) = ([h] ^ (n + 1)) +> x := by
  rw [lpow_rotate]
  rfl

theorem lpow_all0 (h : List Γ) (n : ℕ)
    (hh : h +> (default : ListBlank Γ) = default) :
    (h ^ n) +> (default : ListBlank Γ) = default := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list, append_assoc, ih, hh]

omit [Inhabited Γ] [Inhabited Λ] in
theorem rev_ones (a : Γ) (n : ℕ) :
    (([a] : List Γ) ^ n).reverse = ([a] : List Γ) ^ n := by
  have hrep : ∀ k : ℕ, ([a] : List Γ) ^ k = List.replicate k a := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ_list, List.singleton_append, ih, List.replicate_succ]
  rw [hrep, List.reverse_replicate]

omit [Inhabited Γ] [Inhabited Λ] in
theorem rev_power {α : Type*} (w : List α) (n : ℕ) :
    (w ^ n).reverse = (w.reverse) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list, List.reverse_append, ih, ← pow_succ_list']

-- ============================================================================
-- 3. Reflective Symbolic-Execution Engine (`ES` from `ES_v3.v`)
-- ============================================================================

/--
Boolean-indexed reachability (`multistep'` in `ES_v3.v`): `⊢⁺` when `b = true`, `⊢*` when `b =
false`. -/
def Multistep' (M : Machine Γ Λ) (b : Bool) (c₁ c₂ : Cfg Γ Λ) : Prop :=
  if b then c₁ [M]⊢⁺ c₂ else c₁ [M]⊢* c₂

theorem Multistep'.trans {M : Machine Γ Λ} {b₁ b₂ b₃ : Bool} {c₁ c₂ c₃ : Cfg Γ Λ}
    (hb : (!b₃ || (b₁ || b₂)) = true)
    (h₁ : Multistep' M b₁ c₁ c₂)
    (h₂ : Multistep' M b₂ c₂ c₃) :
    Multistep' M b₃ c₁ c₃ := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> dsimp [Multistep'] at h₁ h₂ ⊢
  · exact stepStar_trans h₁ h₂
  · cases hb
  · exact stepStar_trans h₁ (stepPlus_to_stepStar h₂)
  · exact stepStar_stepPlus_trans h₁ h₂
  · exact stepStar_trans (stepPlus_to_stepStar h₁) h₂
  · exact stepPlus_stepStar_trans h₁ h₂
  · exact stepStar_trans (stepPlus_to_stepStar h₁) (stepPlus_to_stepStar h₂)
  · exact stepPlus_trans h₁ h₂

/-- Symbolic half-tape expression (`vside` in `ES_v3.v`). -/
inductive VSide (Γ : Type*) where
  | cons (h : Γ) (t : VSide Γ)
  | app (h : List Γ) (n : ℕ) (t : VSide Γ)
  | inf
  | var (i : ℕ)
deriving DecidableEq

/-- Symbolic full-tape configuration (`vconfig` in `ES_v3.v`). -/
inductive VConfig (Γ Λ : Type*) where
  | L (l r : VSide Γ) (q : Λ)
  | R (l r : VSide Γ) (q : Λ)
  | mid (l r : VSide Γ) (m : Γ) (q : Λ)
deriving DecidableEq

/-- Prepend a finite symbol list onto a `VSide` (`vside_app_seg` in `ES_v3.v`). -/
def vsideAppSeg : List Γ → VSide Γ → VSide Γ
  | [], x₀ => x₀
  | h :: t, x₀ => .cons h (vsideAppSeg t x₀)

/-- Evaluate a `VSide` under natural-number assignment `fN` and half-tape assignment `fS`. -/
def VSide.toSide (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ) : VSide Γ → ListBlank Γ
  | .cons h t => h >> t.toSide fN fS
  | .app h n t => (h ^ fN n) +> t.toSide fN fS
  | .inf => default
  | .var i => fS i

/-- Evaluate a `VConfig` under natural-number assignment `fN` and half-tape assignment `fS`. -/
def VConfig.toCfg (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ) : VConfig Γ Λ → Cfg Γ Λ
  | .L l r q => (l.toSide fN fS) <{{q}} (r.toSide fN fS)
  | .R l r q => (l.toSide fN fS) {{q}}> (r.toSide fN fS)
  | .mid l r m q => ⟨some q, ⟨m, l.toSide fN fS, r.toSide fN fS⟩⟩

theorem vsideAppSeg_spec (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ) (x : List Γ) (x₀ : VSide Γ) :
    (vsideAppSeg x x₀).toSide fN fS = x +> x₀.toSide fN fS := by
  induction x with
  | nil => rfl
  | cons h t ih => simp only [vsideAppSeg, VSide.toSide, append_cons, ih]

/--
Expose the scanned symbol under `.L` or `.R` when the leading constructor is `.cons` or `.inf`. -/
def rwVConfigLR : VConfig Γ Λ → VConfig Γ Λ
  | .L (.cons m l) r q => .mid l r m q
  | .L .inf r q => .mid .inf r default q
  | .R l (.cons m r) q => .mid l r m q
  | .R l .inf q => .mid l .inf default q
  | x => x

theorem rwVConfigLR_spec (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ) (x : VConfig Γ Λ) :
    (rwVConfigLR x).toCfg fN fS = x.toCfg fN fS := by
  rcases x with ⟨l, r, q⟩ | ⟨l, r, q⟩ | ⟨l, r, m, q⟩
  · rcases l with ⟨h, t⟩ | ⟨h, n, t⟩ | _ | i <;>
      simp [rwVConfigLR, VConfig.toCfg, VSide.toSide]
  · rcases r with ⟨h, t⟩ | ⟨h, n, t⟩ | _ | i <;>
      simp [rwVConfigLR, VConfig.toCfg, VSide.toSide]
  · rfl

section DecidableES

variable [DecidableEq Γ] [DecidableEq Λ]

/-- Collapse `.cons default .inf` to `.inf`. -/
def vsideConsRw0inf (h : Γ) (t : VSide Γ) : VSide Γ :=
  match t with
  | .inf => if h == default then .inf else .cons h .inf
  | _ => .cons h t

theorem vsideConsRw0inf_spec (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ) (h : Γ) (x : VSide Γ) :
    (vsideConsRw0inf h x).toSide fN fS = h >> x.toSide fN fS := by
  rcases x with ⟨h', t⟩ | ⟨h', n, t⟩ | _ | i <;> dsimp [vsideConsRw0inf]
  · rfl
  · rfl
  · split_ifs with heq
    · have heq' : h = default := beq_iff_eq.mp heq
      subst heq'
      dsimp [VSide.toSide]
      exact lb_cons_default.symm
    · rfl
  · rfl

/-- Rotate leading blank symbols out of `.app x n .inf`. -/
def vsideRwLpowRotateAll0 : List Γ → List Γ → ℕ → VSide Γ
  | [], x₀, n => .app ([] ++ x₀.reverse) n .inf
  | h :: t, x₀, n =>
    if h == default then
      .cons h (vsideRwLpowRotateAll0 t (h :: x₀) n)
    else
      .app ((h :: t) ++ x₀.reverse) n .inf

theorem vsideRwLpowRotateAll0_spec (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    (x x₀ : List Γ) (n : ℕ) :
    (vsideRwLpowRotateAll0 x x₀ n).toSide fN fS =
      (VSide.app (x ++ x₀.reverse) n .inf).toSide fN fS := by
  induction x generalizing x₀ with
  | nil => rfl
  | cons a x ih =>
    dsimp [vsideRwLpowRotateAll0]
    split_ifs with ha
    · have ha' : a = default := beq_iff_eq.mp ha
      subst ha'
      dsimp [VSide.toSide]
      rw [ih (default :: x₀)]
      dsimp [VSide.toSide]
      have hrot := lpow_rotate (default : Γ) (x ++ x₀.reverse) (fN n) default
      rw [lb_cons_default] at hrot
      rw [List.reverse_cons, ← List.append_assoc]
      exact hrot.symm
    · rfl

/-- $O(1)$ accumulator-based block rotation across matching symbols (`vside_rw_lpow_rotate'`). -/
def vsideRwLpowRotateAux : List Γ → List Γ → ℕ → VSide Γ → VSide Γ
  | cur, acc, n, .cons h' t =>
    match cur with
    | h₀ :: h₁ =>
      if h₀ == h' then
        .cons h₀ (vsideRwLpowRotateAux h₁ (h₀ :: acc) n t)
      else
        .app (cur ++ acc.reverse) n (.cons h' t)
    | [] =>
      match acc.reverse with
      | [] => .app [] n (.cons h' t)
      | h₀ :: h₁ =>
        if h₀ == h' then
          .cons h₀ (vsideRwLpowRotateAux h₁ [h₀] n t)
        else
          .app (h₀ :: h₁) n (.cons h' t)
  | cur, acc, n, .inf =>
    let h := cur ++ acc.reverse
    match h with
    | [] => .app [] n .inf
    | h₀ :: h₁ =>
      if BoundedConfig.all0 (h₀ :: h₁) then
        .inf
      else
        vsideRwLpowRotateAll0 (h₀ :: h₁) [] n
  | cur, acc, n, x =>
    .app (cur ++ acc.reverse) n x

theorem vsideRwLpowRotateAux_spec (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    (cur acc : List Γ) (n : ℕ) (x : VSide Γ) :
    (vsideRwLpowRotateAux cur acc n x).toSide fN fS =
      (VSide.app (cur ++ acc.reverse) n x).toSide fN fS := by
  induction x generalizing cur acc with
  | cons h' t ih =>
    rcases cur with _ | ⟨h₀, h₁⟩
    · dsimp [vsideRwLpowRotateAux]
      rcases hrev : acc.reverse with _ | ⟨h₀, h₁⟩
      · rfl
      · dsimp only
        split_ifs with heq
        · have heq' : h₀ = h' := beq_iff_eq.mp heq
          subst heq'
          dsimp [VSide.toSide]
          rw [ih h₁ [h₀]]
          dsimp [VSide.toSide]
          exact (lpow_rotate h₀ h₁ (fN n) (t.toSide fN fS)).symm
        · rfl
    · dsimp [vsideRwLpowRotateAux]
      split_ifs with heq
      · have heq' : h₀ = h' := beq_iff_eq.mp heq
        subst heq'
        dsimp [VSide.toSide]
        rw [ih h₁ (h₀ :: acc)]
        dsimp [VSide.toSide]
        rw [List.reverse_cons, ← List.append_assoc]
        exact (lpow_rotate h₀ (h₁ ++ acc.reverse) (fN n) (t.toSide fN fS)).symm
      · rfl
  | app h' n' t _ => rfl
  | inf =>
    dsimp [vsideRwLpowRotateAux]
    rcases hcur : cur ++ acc.reverse with _ | ⟨h₀, h₁⟩
    · rfl
    · dsimp only
      split_ifs with hall
      · dsimp [VSide.toSide]
        exact (lpow_all0 (h₀ :: h₁) (fN n) (BoundedConfig.all0_spec hall)).symm
      · rw [vsideRwLpowRotateAll0_spec]
        simp [VSide.toSide]
  | var i => rfl

/-- Normalize a `VSide` by rotating matching symbols and collapsing trailing blanks. -/
def vsideRwLpowRotate : VSide Γ → VSide Γ
  | .cons h t => vsideConsRw0inf h (vsideRwLpowRotate t)
  | .app h n t => vsideRwLpowRotateAux h [] n (vsideRwLpowRotate t)
  | x => x

theorem vsideRwLpowRotate_spec (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ) (x : VSide Γ) :
    (vsideRwLpowRotate x).toSide fN fS = x.toSide fN fS := by
  induction x with
  | cons h t ih =>
    dsimp [vsideRwLpowRotate]
    rw [vsideConsRw0inf_spec, ih]
    rfl
  | app h n t ih =>
    dsimp [vsideRwLpowRotate]
    rw [vsideRwLpowRotateAux_spec]
    simp [VSide.toSide, ih]
  | inf => rfl
  | var i => rfl

/-- Normalize both half-tapes of a `VConfig`. -/
def rwLpowRotate : VConfig Γ Λ → VConfig Γ Λ
  | .L l r q => .L (vsideRwLpowRotate l) (vsideRwLpowRotate r) q
  | .R l r q => .R (vsideRwLpowRotate l) (vsideRwLpowRotate r) q
  | .mid l r m q => .mid (vsideRwLpowRotate l) (vsideRwLpowRotate r) m q

theorem rwLpowRotate_spec (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ) (x : VConfig Γ Λ) :
    (rwLpowRotate x).toCfg fN fS = x.toCfg fN fS := by
  rcases x with ⟨l, r, q⟩ | ⟨l, r, q⟩ | ⟨l, r, m, q⟩ <;>
    simp [rwLpowRotate, VConfig.toCfg, vsideRwLpowRotate_spec]

/-- Execute one concrete TM step on a `.mid` symbolic configuration (`vconfig_step1`). -/
def vconfigStep1 (M : Machine Γ Λ) : VConfig Γ Λ → Option (VConfig Γ Λ)
  | .mid l r m q =>
    match M q m with
    | none => none
    | some (none, _) => none
    | some (some q', Stmt.write m' .left) => some (.L l (.cons m' r) q')
    | some (some q', Stmt.write m' .right) => some (.R (.cons m' l) r q')
  | _ => none

theorem vconfigStep1_spec (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {x x₀ : VConfig Γ Λ} (h : vconfigStep1 M x = some x₀) :
    Multistep' M true (x.toCfg fN fS) (x₀.toCfg fN fS) := by
  rcases x with ⟨l, r, q⟩ | ⟨l, r, q⟩ | ⟨l, r, m, q⟩
  · cases h
  · cases h
  · dsimp [vconfigStep1] at h
    rcases hM : M q m with _ | ⟨_ | q', ⟨m', _ | _⟩⟩ <;> rw [hM] at h <;> cases h
    · refine ⟨1, by decide, ?_⟩
      simp [VConfig.toCfg, VSide.toSide, step, hM, Tape.write, Tape.move]
    · refine ⟨1, by decide, ?_⟩
      simp [VConfig.toCfg, VSide.toSide, step, hM, Tape.write, Tape.move]

/-- Step `x` up to `T` concrete steps, stopping early if `x₀ == y && !b` (`none`) or if `.mid` is
  not
available (`some (x₀, y, b)`). -/
def vconfigStep1s (M : Machine Γ Λ) (x y : VConfig Γ Λ) (b : Bool) :
    ℕ → Option (VConfig Γ Λ × VConfig Γ Λ × Bool)
  | 0 => some (x, y, b)
  | T + 1 =>
    let x₀ := rwVConfigLR x
    if (x₀ == y) && !b then
      none
    else
      match vconfigStep1 M x₀ with
      | some x₁ => vconfigStep1s M x₁ y false T
      | none => some (x₀, y, b)

theorem vconfigStep1s_spec (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    (x y : VConfig Γ Λ) (b : Bool) (T : ℕ) :
    match vconfigStep1s M x y b T with
    | some (x', y', b') =>
      Multistep' M b' (x'.toCfg fN fS) (y'.toCfg fN fS) →
      Multistep' M b (x.toCfg fN fS) (y.toCfg fN fS)
    | none => Multistep' M b (x.toCfg fN fS) (y.toCfg fN fS) := by
  induction T generalizing x y b with
  | zero => exact id
  | succ T ih =>
    dsimp [vconfigStep1s]
    split_ifs with heq
    · rw [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at heq
      rcases heq with ⟨hxy, rfl⟩
      rw [← hxy, rwVConfigLR_spec]
      exact stepStar_refl M _
    · rcases hstep : vconfigStep1 M (rwVConfigLR x) with _ | x₁ <;> dsimp only
      · intro hrest
        rwa [← rwVConfigLR_spec fN fS x]
      · have h1 := vconfigStep1_spec M fN fS hstep
        rw [rwVConfigLR_spec] at h1
        have ih' := ih x₁ y false
        rcases hres : vconfigStep1s M x₁ y false T with _ | ⟨x', y', b'⟩ <;>
          rw [hres] at ih' <;> dsimp only at ih' ⊢
        · exact Multistep'.trans (b₃ := b) (by cases b <;> rfl) h1 ih'
        · intro hrest
          exact Multistep'.trans (b₃ := b) (by cases b <;> rfl) h1 (ih' hrest)

/-- Normalize and run `vconfigStep1s` (`vconfig_er` in `ES_v3.v`). -/
def vconfigEr (M : Machine Γ Λ) (x y : VConfig Γ Λ) (b : Bool) (T : ℕ) :
    Option (VConfig Γ Λ × VConfig Γ Λ × Bool) :=
  vconfigStep1s M (rwLpowRotate x) y b T

theorem vconfigEr_spec (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    (x y : VConfig Γ Λ) (b : Bool) (T : ℕ) :
    match vconfigEr M x y b T with
    | none => Multistep' M b (x.toCfg fN fS) (y.toCfg fN fS)
    | some (x₀, y₀, b₀) =>
      Multistep' M b₀ (x₀.toCfg fN fS) (y₀.toCfg fN fS) →
      Multistep' M b (x.toCfg fN fS) (y.toCfg fN fS) := by
  dsimp [vconfigEr]
  have h := vconfigStep1s_spec M fN fS (rwLpowRotate x) y b T
  rcases hres : vconfigStep1s M (rwLpowRotate x) y b T with _ | ⟨x₀, y₀, b₀⟩ <;> rw [hres] at h
  · rwa [rwLpowRotate_spec] at h
  · intro hrest
    have h' := h hrest
    rwa [rwLpowRotate_spec] at h'

/-- Peel `n` symbols off the front of a `VSide` (`vside_split` in `ES_v3.v`). -/
def vsideSplit (x : VSide Γ) : ℕ → Option (VSide Γ × List Γ)
  | 0 => some (x, [])
  | n + 1 =>
    match x with
    | .cons h t =>
      match vsideSplit t n with
      | some (x₀, x₁) => some (x₀, h :: x₁)
      | none => none
    | .inf => some (.inf, ([default] : List Γ) ^ (n + 1))
    | _ => none

theorem vsideSplit_spec (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {x x₁ : VSide Γ} {n : ℕ} {x₀ : List Γ}
    (h : vsideSplit x n = some (x₁, x₀)) :
    x.toSide fN fS = x₀ +> x₁.toSide fN fS := by
  induction n generalizing x x₁ x₀ with
  | zero =>
    unfold vsideSplit at h
    injection h with h
    injection h with h1 h2
    subst h1 h2
    rfl
  | succ n ih =>
    rcases x with ⟨h₀, t⟩ | ⟨h₀, m, t⟩ | _ | i
    · dsimp [vsideSplit] at h
      rcases hsp : vsideSplit t n with _ | ⟨x₁', x₀'⟩ <;> rw [hsp] at h
      · cases h
      · dsimp only at h
        injection h with h
        injection h with h1 h2
        subst h1 h2
        dsimp [VSide.toSide]
        rw [ih hsp]
    · cases h
    · dsimp [vsideSplit] at h
      injection h with h
      injection h with h1 h2
      subst h1 h2
      dsimp [VSide.toSide]
      exact (lpow_all0 [default] (n + 1) lb_cons_default).symm
    · cases h

/-- Left-moving shift-rule induction (`shift_rule_L` in `Individual.v`). -/
theorem shift_rule_L {M : Machine Γ Λ} {q : Λ} {l₀ r₀ w : List Γ}
    (hstep : ∀ l r : ListBlank Γ,
      ((r₀ +> l) <{{q}} (l₀ +> r)) [M]⊢* (l <{{q}} (l₀ +> (w +> r))))
    (n : ℕ) (l r : ListBlank Γ) :
    (((r₀ ^ n) +> l) <{{q}} (l₀ +> r)) [M]⊢* (l <{{q}} (l₀ +> ((w ^ n) +> r))) := by
  induction n generalizing l r with
  | zero => exact stepStar_refl M _
  | succ n ih =>
    rw [pow_succ_list', append_assoc]
    refine stepStar_trans (ih (r₀ +> l) r) ?_
    have h1 := hstep l ((w ^ n) +> r)
    rwa [← append_assoc w (w ^ n) r, ← pow_succ_list w n] at h1

/-- Right-moving shift-rule induction (`shift_rule_R` in `Individual.v`). -/
theorem shift_rule_R {M : Machine Γ Λ} {q : Λ} {l₀ r₀ w : List Γ}
    (hstep : ∀ l r : ListBlank Γ,
      ((l₀ +> l) {{q}}> (r₀ +> r)) [M]⊢* ((l₀ +> (w +> l)) {{q}}> r))
    (n : ℕ) (l r : ListBlank Γ) :
    ((l₀ +> l) {{q}}> ((r₀ ^ n) +> r)) [M]⊢* ((l₀ +> ((w ^ n) +> l)) {{q}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl M _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (hstep l ((r₀ ^ n) +> r)) ?_
    have h1 := ih (w +> l)
    rwa [← append_assoc (w ^ n) w l, ← pow_succ_list' w n] at h1

/--
Check whether `BoundedConfig.steps` certifies a shift rule across `r = .app r₀ i r₁` (`chk_sr`). -/
def chkSr (M : Machine Γ Λ) (l₀ : List Γ) (l₁ r : VSide Γ) (q : Λ) (d : Dir) (T : ℕ) :
    Option (VConfig Γ Λ) :=
  match r with
  | .app r₀ i r₁ =>
    let c₁ : BoundedConfig.BCfg Γ Λ := ⟨l₀, r₀, q, d⟩
    match BoundedConfig.steps M T c₁ with
    | some ⟨l₀', r₀', q', d'⟩ =>
      if (d == d') && (q == q') && (r₀' == []) && (l₀'.take l₀.length == l₀) then
        let l' := vsideAppSeg l₀ (.app (l₀'.drop l₀.length) i l₁)
        match d with
        | .left => some (.L r₁ l' q)
        | .right => some (.R l' r₁ q)
      else
        none
    | none => none
  | _ => none

theorem chkSr_spec (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {l₀ : List Γ} {l₁ r : VSide Γ} {q : Λ} {d : Dir} {T : ℕ} {x : VConfig Γ Λ}
    (h : chkSr M l₀ l₁ r q d T = some x) :
    ((match d with
      | .left => VConfig.L r (vsideAppSeg l₀ l₁) q
      | .right => VConfig.R (vsideAppSeg l₀ l₁) r q).toCfg fN fS) [M]⊢* (x.toCfg fN fS) := by
  rcases r with ⟨h₀, t⟩ | ⟨r₀, i, r₁⟩ | _ | j
  · cases h
  · dsimp [chkSr] at h
    rcases hsteps : BoundedConfig.steps M T ⟨l₀, r₀, q, d⟩ with _ | ⟨l₀', r₀', q', d'⟩ <;>
      rw [hsteps] at h
    · cases h
    · dsimp only at h
      split_ifs at h with hcond
      · simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        rcases hcond with ⟨⟨⟨rfl, rfl⟩, rfl⟩, htake⟩
        have hl₀' : l₀' = l₀ ++ l₀'.drop l₀.length := by
          have htd := List.take_append_drop l₀.length l₀'
          rw [htake] at htd
          exact htd.symm
        rcases d with _ | _ <;> dsimp only at h <;> injection h with h <;> subst h
        · dsimp [VConfig.toCfg, VSide.toSide]
          rw [vsideAppSeg_spec, vsideAppSeg_spec]
          dsimp [VSide.toSide]
          refine shift_rule_L (fun l r => ?_) (fN i) (r₁.toSide fN fS) (l₁.toSide fN fS)
          have hspec := BoundedConfig.steps_spec M T ⟨l₀, r₀, q, .left⟩ hsteps l r
          dsimp [BoundedConfig.toCfg] at hspec
          rw [hl₀', append_assoc] at hspec
          exact hspec
        · dsimp [VConfig.toCfg, VSide.toSide]
          rw [vsideAppSeg_spec, vsideAppSeg_spec]
          dsimp [VSide.toSide]
          refine shift_rule_R (fun l r => ?_) (fN i) (l₁.toSide fN fS) (r₁.toSide fN fS)
          have hspec := BoundedConfig.steps_spec M T ⟨l₀, r₀, q, .right⟩ hsteps l r
          dsimp [BoundedConfig.toCfg] at hspec
          rw [hl₀', append_assoc] at hspec
          exact hspec
  · cases h
  · cases h

/-- Try lookback contexts `l₀` of length `n' .. n' + n - 1` (`try_sr` in `ES_v3.v`). -/
def trySr (M : Machine Γ Λ) (l r : VSide Γ) (q : Λ) (d : Dir) :
    ℕ → ℕ → ℕ → Option (VConfig Γ Λ)
  | 0, _, _ => none
  | n + 1, n', T =>
    match vsideSplit l n' with
    | some (l₁, l₀) =>
      match chkSr M l₀ l₁ r q d T with
      | some res => some res
      | none => trySr M l r q d n (n' + 1) T
    | none => none

theorem trySr_spec (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {l r : VSide Γ} {q : Λ} {d : Dir} {n n' T : ℕ} {x : VConfig Γ Λ}
    (h : trySr M l r q d n n' T = some x) :
    ((match d with
      | .left => VConfig.L r l q
      | .right => VConfig.R l r q).toCfg fN fS) [M]⊢* (x.toCfg fN fS) := by
  induction n generalizing n' with
  | zero => cases h
  | succ n ih =>
    dsimp [trySr] at h
    rcases hsp : vsideSplit l n' with _ | ⟨l₁, l₀⟩ <;> rw [hsp] at h
    · cases h
    · dsimp only at h
      rcases hchk : chkSr M l₀ l₁ r q d T with _ | res <;> rw [hchk] at h
      · dsimp only at h
        exact ih h
      · dsimp only at h
        injection h with h
        subst h
        have hspec := chkSr_spec M fN fS hchk
        have hsplit := vsideSplit_spec fN fS hsp
        rcases d with _ | _ <;>
          dsimp [VConfig.toCfg] at hspec ⊢ <;>
          rw [vsideAppSeg_spec] at hspec <;>
          rwa [hsplit]

/-- Attempt a shift-rule step when the scanned half-tape starts with `.app` (`vconfig_sr`). -/
def vconfigSr (M : Machine Γ Λ) (x : VConfig Γ Λ) (maxLookback T : ℕ) :
    Option (VConfig Γ Λ) :=
  match x with
  | .L (.app r₀ i r₁) r q => trySr M r (.app r₀ i r₁) q .left maxLookback 0 T
  | .R l (.app r₀ i r₁) q => trySr M l (.app r₀ i r₁) q .right maxLookback 0 T
  | _ => none

theorem vconfigSr_spec (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {x x₀ : VConfig Γ Λ} {maxLookback T : ℕ}
    (h : vconfigSr M x maxLookback T = some x₀) :
    Multistep' M false (x.toCfg fN fS) (x₀.toCfg fN fS) := by
  rcases x with ⟨_ | ⟨r₀, i, r₁⟩ | _ | _, r, q⟩ | ⟨l, _ | ⟨r₀, i, r₁⟩ | _ | _, q⟩ | _
  · cases h
  · exact trySr_spec M fN fS h
  · cases h
  · cases h
  · cases h
  · exact trySr_spec M fN fS h
  · cases h
  · cases h
  · cases h

/-- Alternate concrete execution (`vconfigEr`) and shift-rule acceleration (`vconfigSr`). -/
def vconfigErSr (M : Machine Γ Λ) (x y : VConfig Γ Λ) (b : Bool)
    (maxLookback stepFuel : ℕ) : ℕ → Option (VConfig Γ Λ × VConfig Γ Λ × Bool)
  | 0 => some (x, y, b)
  | outerFuel + 1 =>
    match vconfigEr M x y b stepFuel with
    | none => none
    | some (x₀, y₀, b₀) =>
      match vconfigSr M x₀ maxLookback stepFuel with
      | none => some (x₀, y₀, b₀)
      | some x₁ => vconfigErSr M x₁ y₀ b₀ maxLookback stepFuel outerFuel

theorem vconfigErSr_spec (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {x y : VConfig Γ Λ} {b : Bool} {maxLookback stepFuel outerFuel : ℕ}
    (h : vconfigErSr M x y b maxLookback stepFuel outerFuel = none) :
    Multistep' M b (x.toCfg fN fS) (y.toCfg fN fS) := by
  induction outerFuel generalizing x y b with
  | zero => cases h
  | succ outerFuel ih =>
    dsimp [vconfigErSr] at h
    have her := vconfigEr_spec M fN fS x y b stepFuel
    rcases hres : vconfigEr M x y b stepFuel with _ | ⟨x₀, y₀, b₀⟩ <;> rw [hres] at her h
    · exact her
    · dsimp only at h
      rcases hsr : vconfigSr M x₀ maxLookback stepFuel with _ | x₁ <;> rw [hsr] at h
      · cases h
      · dsimp only at h
        refine her ?_
        have hsr_spec := vconfigSr_spec M fN fS hsr
        have ih_spec := ih h
        exact Multistep'.trans (by cases b₀ <;> rfl) hsr_spec ih_spec

/-- Full `ES` symbolic execution engine (`vconfig_es` in `ES_v3.v`). -/
def vconfigEs (M : Machine Γ Λ) (x y : VConfig Γ Λ) (b : Bool)
    (outerFuel : ℕ := 64) (maxLookback : ℕ := 12) (stepFuel : ℕ := 8000) :
    Option (VConfig Γ Λ × VConfig Γ Λ × Bool) :=
  let y₀ := rwLpowRotate y
  let y₁ := rwVConfigLR y₀
  vconfigErSr M x y₁ b maxLookback stepFuel outerFuel

theorem vconfigEs_spec (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {x y : VConfig Γ Λ} {b : Bool} {outerFuel maxLookback stepFuel : ℕ}
    (h : vconfigEs M x y b outerFuel maxLookback stepFuel = none) :
    Multistep' M b (x.toCfg fN fS) (y.toCfg fN fS) := by
  have h' := vconfigErSr_spec M fN fS h
  rwa [rwVConfigLR_spec, rwLpowRotate_spec] at h'

/-- Boolean decision wrapper for `vconfigEs`. -/
def checkEs (M : Machine Γ Λ) (x y : VConfig Γ Λ) (b : Bool)
    (outerFuel : ℕ := 64) (maxLookback : ℕ := 12) (stepFuel : ℕ := 8000) : Bool :=
  (vconfigEs M x y b outerFuel maxLookback stepFuel).isNone

theorem checkEs_spec_star (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {x y : VConfig Γ Λ} {outerFuel maxLookback stepFuel : ℕ}
    (h : checkEs M x y false outerFuel maxLookback stepFuel = true) :
    (x.toCfg fN fS) [M]⊢* (y.toCfg fN fS) := by
  dsimp [checkEs] at h
  rw [Option.isNone_iff_eq_none] at h
  exact vconfigEs_spec M fN fS h

theorem checkEs_spec_plus (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {x y : VConfig Γ Λ} {outerFuel maxLookback stepFuel : ℕ}
    (h : checkEs M x y true outerFuel maxLookback stepFuel = true) :
    (x.toCfg fN fS) [M]⊢⁺ (y.toCfg fN fS) := by
  dsimp [checkEs] at h
  rw [Option.isNone_iff_eq_none] at h
  exact vconfigEs_spec M fN fS h

end DecidableES

end BusyBeaver.FractalReturn
