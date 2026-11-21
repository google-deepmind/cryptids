module

public import BusyBeaver.Calculi.Longitudinal
import Mathlib.Tactic.Ring

/-!
# Fractal-in-Bouncer Return Combinators & Symbolic Executor (`BusyBeaver.FractalReturn`)

Reusable infrastructure extracted from the BusyCoq `FIBv7.v` ("fractal-in-bouncer", holdout `#234`)
and `ES_v3.v` verification libraries:

1. **Return-Closure Non-Halting & 3-Adic Factorization**:
   - `isNotHalt_of_return`: if `init [] [M]⊢* S a₀` and `∀ a, ∃ b, S a [M]⊢⁺ S b`, then `IsNotHalt
     M`.
   - `isNotHalt_of_odd_return`: specialization to odd index families `∀ a, ∃ b, S (1 + a * 2)
     [M]⊢⁺ S (1 + b * 2)`.
   - `factor_three`: every positive `x > 0` factors as `x = 3 ^ e * u` with `u % 3 ≠ 0`.

2. **Reflective Symbolic Executor with Shift-Rule Acceleration (`ES`)**:
   - Port of BusyCoq's `ES_v3.v` (`VSide`, `VConfig`, `vconfigEs`, `vconfigEs_spec`,
     `checkEs_spec_star`,
     `checkEs_spec_plus`, `vsideRL_es_spec`) with $O(1)$ accumulator-based block rotation
     (`vsideRwLpowRotateAux`), enabling `by decide` discharge of symbolic execution lemmas without
     `native_decide`.

3. **Half-Run List Combinators**:
   - `Post`, `mass`, `Pairs`, `Field`, `Fields`, `TripleWord`, `triple_mass`, `M9`, `TripleFields`,
     `EWord`, `Spaced`, `Raised`, `Block`, `Chain`, `CPeriod`, and their append/power/reverse/mass
     algebraic lemmas.

4. **Variable-Arity `Sweep` Tile Schema over `Longitudinal.SegRLs` / `SideRLs`**:
   - `Sweep`, `sweep_step`, `sweep_step_spec`, `sweep_iter`, `Sweep_spec`, `sweep_power`,
     `sweep_iter_spec`, `blank_sweeps`, `right_sweeps`.

5. **Machine-Generic List-Induction Combinators**:
   - `even_absorb_list`, `even_absorb_power`, `A_return_list`, `A_return_power`, `C_recover_list`,
     `odd_recover_list`, `C_recover_period`, `D_sweep`, `D_block`, `D_block_power`, `C_absorb_alt`,
     `C_block`, `C_block_power`, `CPeriod_collapse`, `B_batch`, `B_complete`, `tagged_even`,
     `tagged_odd`, `B_half_power`, `caller_list`, `Chain_even`.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.Longitudinal

namespace BusyBeaver.FractalReturn


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

-- ============================================================================
-- 1. Return-Closure Non-Halting & 3-Adic Factorization
-- ============================================================================

@[scoped simp] private theorem multiStep_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    multiStep M c 0 = some c := rfl

@[scoped simp] private theorem multiStep_one (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    multiStep M c 1 = step M c := rfl

private theorem multiStep_succ (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = (multiStep M c n).bind (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

private theorem multiStep_succ' (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = (step M c).bind (fun c' => multiStep M c' n) := by
  induction n generalizing c with
  | zero =>
    rw [multiStep_one]
    rcases step M c with _ | c' <;> rfl
  | succ n ih =>
    rw [multiStep_succ, ih]
    rcases step M c with _ | c'
    · rfl
    · simp only [Option.bind_some, ← multiStep_succ]

private theorem multiStep_add (M : Machine Γ Λ) (c : Cfg Γ Λ) (m n : ℕ) :
    multiStep M c (m + n) = (multiStep M c m).bind (fun c' => multiStep M c' n) := by
  induction n with
  | zero => simp [multiStep_zero]
  | succ n ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    congr 1
    funext c'
    exact (multiStep_succ M c' n).symm

private theorem multiStep_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {m n : ℕ}
    (h₁ : multiStep M c₁ m = some c₂) (h₂ : multiStep M c₂ n = some c₃) :
    multiStep M c₁ (m + n) = some c₃ := by
  rw [multiStep_add, h₁, Option.bind_some, h₂]

private theorem multiStep_eq_none_of_gt_halted {M : Machine Γ Λ} {c cfg : Cfg Γ Λ} {k m : ℕ}
    (hk : multiStep M c k = some cfg) (h_halt : (step M cfg).isNone) (hgt : k < m) :
    multiStep M c m = none := by
  obtain ⟨d, hd⟩ : ∃ d, m = k + (d + 1) := ⟨m - k - 1, by omega⟩
  rw [hd, multiStep_add, hk, Option.bind_some, multiStep_succ']
  rcases hst : step M cfg with _ | cfg'
  · rfl
  · rw [hst] at h_halt
    cases h_halt

/-- If `init []` reaches `S a₀` in `⊢*` and every `S a` advances in `⊢⁺` (`≥ 1` steps) to some
`S b`, then `M` never halts (`progress_nonhalt_simple` / `isNotHalt_of_return`). -/
theorem isNotHalt_of_return {M : Machine Γ Λ} (S : ℕ → Cfg Γ Λ) (a₀ : ℕ)
    (hinit : (init []) [M]⊢* S a₀)
    (hret : ∀ a, ∃ b, (S a) [M]⊢⁺ S b) :
    IsNotHalt M := by
  obtain ⟨k₀, hk₀⟩ := hinit
  have h_unbounded : ∀ j : ℕ, ∃ N ≥ k₀ + j, ∃ a, multiStep M (init []) N = some (S a) := by
    intro j
    induction j with
    | zero => exact ⟨k₀, Nat.le_refl k₀, a₀, hk₀⟩
    | succ j ih =>
      obtain ⟨N, hN, a, hms₁⟩ := ih
      obtain ⟨b, m, hm_pos, hms₂⟩ := hret a
      refine ⟨N + m, by omega, b, multiStep_trans hms₁ hms₂⟩
  intro cfg ⟨k, hk⟩
  rcases hstep_cfg : step M cfg with _ | _
  · obtain ⟨N, hN, a, hmsN⟩ := h_unbounded (k + 1)
    have hnone : (step M cfg).isNone := by simp [hstep_cfg]
    have hnoneN : multiStep M (init []) N = none :=
      multiStep_eq_none_of_gt_halted hk hnone (by omega)
    rw [hnoneN] at hmsN
    cases hmsN
  · rfl

/--
Odd-indexed specialization of `isNotHalt_of_return` (`S_return a : ∃ b, S (1 + a * 2) ⊢⁺ S (1 + b *
2)`). -/
theorem isNotHalt_of_odd_return {M : Machine Γ Λ} (S : ℕ → Cfg Γ Λ) (a₀ : ℕ)
    (hinit : (init []) [M]⊢* S (1 + a₀ * 2))
    (hret : ∀ a, ∃ b, (S (1 + a * 2)) [M]⊢⁺ S (1 + b * 2)) :
    IsNotHalt M :=
  isNotHalt_of_return (fun a => S (1 + a * 2)) a₀ hinit hret

/-- Every positive natural number `x > 0` factors into a power of `3` times a 3-coprime cofactor
(`factor_three` in `FIBv7.v`). -/
theorem factor_three (x : ℕ) (hx : 0 < x) :
    ∃ e u : ℕ, x = 3 ^ e * u ∧ u % 3 ≠ 0 := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases hmod : x % 3 = 0
    · have hdiv_pos : 0 < x / 3 := by omega
      have hdiv_lt : x / 3 < x := by omega
      obtain ⟨e, u, heq, hu⟩ := ih (x / 3) hdiv_lt hdiv_pos
      refine ⟨e + 1, u, ?_, hu⟩
      have hx3 : x = 3 * (x / 3) := by omega
      rw [hx3, heq, Nat.pow_succ']
      ring
    · exact ⟨0, x, by omega, hmod⟩

-- ============================================================================
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
      simp [rwVConfigLR, VConfig.toCfg, VSide.toSide, lb_head_default, lb_tail_default]
  · rcases r with ⟨h, t⟩ | ⟨h, n, t⟩ | _ | i <;>
      simp [rwVConfigLR, VConfig.toCfg, VSide.toSide, lb_head_default, lb_tail_default]
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

/-- Check that variable `v` does not occur in `x` (`vside_no_occur` in `ES_v3.v`). -/
def vsideNoOccur (v : ℕ) : VSide Γ → Bool
  | .cons _ t => vsideNoOccur v t
  | .app _ _ t => vsideNoOccur v t
  | .inf => true
  | .var i => !(i == v)

theorem vsideNoOccur_spec (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {v : ℕ} {x : VSide Γ} (v' : ListBlank Γ)
    (h : vsideNoOccur v x = true) :
    x.toSide fN (fun i => if i == v then v' else fS i) = x.toSide fN fS := by
  induction x with
  | cons h₀ t ih =>
    dsimp [vsideNoOccur] at h
    dsimp [VSide.toSide]
    rw [ih h]
  | app h₀ n t ih =>
    dsimp [vsideNoOccur] at h
    dsimp [VSide.toSide]
    rw [ih h]
  | inf => rfl
  | var i =>
    dsimp [vsideNoOccur] at h
    rw [Bool.not_eq_true'] at h
    dsimp [VSide.toSide]
    rw [h]
    rfl

/-- Reflective `SideRL` checker via `vconfigEs` (`vsideRL_es` in `ES_v3.v`). -/
def vsideRL_es (M : Machine Γ Λ) (hR hL : DH0 Γ Λ) (x y : VSide Γ) (v : ℕ)
    (outerFuel : ℕ := 64) (maxLookback : ℕ := 12) (stepFuel : ℕ := 8000) : Bool :=
  checkEs M
    (.R (vsideAppSeg hR.2 (.var v)) x hR.1)
    (.L (.var v) (vsideAppSeg hL.2 y) hL.1)
    true outerFuel maxLookback stepFuel &&
  vsideNoOccur v x && vsideNoOccur v y

theorem vsideRL_es_spec (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {hR hL : DH0 Γ Λ} {x y : VSide Γ} {v outerFuel maxLookback stepFuel : ℕ}
    (h : vsideRL_es M hR hL x y v outerFuel maxLookback stepFuel = true) :
    SideRL M hR hL (x.toSide fN fS) (y.toSide fN fS) := by
  dsimp [vsideRL_es] at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨hes, hx⟩, hy⟩
  intro l
  let fS' : ℕ → ListBlank Γ := fun i => if i == v then l else fS i
  have hstep := checkEs_spec_plus M fN fS' hes
  dsimp [VConfig.toCfg] at hstep
  rw [vsideAppSeg_spec, vsideAppSeg_spec] at hstep
  dsimp [VSide.toSide, fS'] at hstep
  rw [beq_self_eq_true, (ite_eq_left_of_eq_true _ _ (eq_true rfl))] at hstep
  rw [vsideNoOccur_spec fN fS l hx, vsideNoOccur_spec fN fS l hy] at hstep
  exact hstep

theorem vsideRLs_es_single_spec (M : Machine Γ Λ) (fN : ℕ → ℕ) (fS : ℕ → ListBlank Γ)
    {hR hL : DH0 Γ Λ} {x y : VSide Γ} {v outerFuel maxLookback stepFuel : ℕ}
    (h : vsideRL_es M hR hL x y v outerFuel maxLookback stepFuel = true) :
    SideRLs M [(hR, hL)] (x.toSide fN fS) (y.toSide fN fS) :=
  SideRLs.single (vsideRL_es_spec M fN fS h)

end DecidableES

-- ============================================================================
-- 4. Half-Run List Combinators (`Post`, `Pairs`, `Fields`, `TripleWord`, `Block`, `Chain`)
-- ============================================================================

/--
Encode a list of half-runs `x` as odd unary runs `[1] ^ (1 + x * 2) ++ [0]` (`Post` in `FIBv7.v`).
-/
def Post : List ℕ → List (Fin 2)
  | [] => []
  | x :: xs => ([1] : List (Fin 2)) ^ (1 + x * 2) ++ [0] ++ Post xs

/-- Total half-run mass of `xs` (`mass` in `FIBv7.v`). -/
def mass : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 2 + mass xs

theorem Post_app (xs ys : List ℕ) :
    Post (xs ++ ys) = Post xs ++ Post ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, Post, ih, List.append_assoc]

theorem mass_app (xs ys : List ℕ) :
    mass (xs ++ ys) = mass xs + mass ys := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih =>
    dsimp [mass]
    rw [ih]
    omega

theorem mass_power (xs : List ℕ) (n : ℕ) :
    mass (xs ^ n) = n * mass xs := by
  induction n with
  | zero => simp [mass]
  | succ n ih =>
    rw [pow_succ_list, mass_app, ih]
    ring

/-- Left-bridge pair encoding (`Pairs` in `FIBv7.v`). -/
def Pairs : List ℕ → List (Fin 2)
  | [] => []
  | x :: xs => [0] ++ ([1] : List (Fin 2)) ^ (1 + x * 2) ++ [0, 1] ++ Pairs xs

theorem Pairs_cons (x : ℕ) (xs : List ℕ) :
    (Pairs (x :: xs)).reverse =
      (Pairs xs).reverse ++ ([1, 0] : List (Fin 2)) ++ ([1] : List (Fin 2)) ^ (1 + x * 2) ++ [0]
        := by
  dsimp [Pairs]
  simp only [List.append_assoc, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, rev_ones]

theorem Pairs_repeat (x n : ℕ) :
    (Pairs (List.replicate n x)).reverse =
      (([1, 0] : List (Fin 2)) ++ ([1] : List (Fin 2)) ^ (1 + x * 2) ++ [0]) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Pairs_cons, ih]
    simp only [List.append_assoc]
    exact lpow_shift _ n

/-- Single 0-prefixed odd run `[0] ++ [1] ^ (1 + x * 2)` (`Field` in `FIBv7.v`). -/
def Field (x : ℕ) : List (Fin 2) :=
  [0] ++ ([1] : List (Fin 2)) ^ (1 + x * 2)

/-- Concatenation of `Field`s across `xs` (`Fields` in `FIBv7.v`). -/
def Fields (xs : List ℕ) : List (Fin 2) :=
  xs.flatMap Field

theorem Fields_app (xs ys : List ℕ) :
    Fields (xs ++ ys) = Fields xs ++ Fields ys :=
  List.flatMap_append

theorem Fields_repeat (x n : ℕ) :
    Fields (List.replicate n x) = (Field x) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Fields, List.flatMap_cons, ← Fields, ih, pow_succ_list]

theorem Post_Fields (xs : List ℕ) (r : ListBlank (Fin 2)) :
    ([0] : List (Fin 2)) +> (Post xs +> r) = Fields xs +> (([0] : List (Fin 2)) +> r) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ([0] : List (Fin 2)) +> ((([1] : List (Fin 2)) ^ (1 + x * 2) ++ [0] ++ Post xs) +> r) =
      (Field x ++ Fields xs) +> (([0] : List (Fin 2)) +> r)
    rw [append_assoc, append_assoc, ih]
    dsimp [Field]
    simp only [append_assoc, append_cons]

theorem Post_Fields_power (n : ℕ) (xs : List ℕ) (r : ListBlank (Fin 2)) :
    ([0] : List (Fin 2)) +> ((Post xs) ^ n +> r) =
      (Fields xs) ^ n +> (([0] : List (Fin 2)) +> r) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list, pow_succ_list, append_assoc, append_assoc, Post_Fields, ih]

/-- Concatenation of half-run triples (`TripleWord` in `FIBv7.v`). -/
def TripleWord : List (ℕ × ℕ × ℕ) → List (Fin 2)
  | [] => []
  | (a, b, c) :: ts => Field a ++ Field b ++ Field c ++ TripleWord ts

/-- Total mass of a list of half-run triples (`triple_mass` in `FIBv7.v`). -/
def triple_mass : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | (a, b, c) :: ts => 4 + a * 2 + b + c + triple_mass ts

theorem triple_mass_app (xs ys : List (ℕ × ℕ × ℕ)) :
    triple_mass (xs ++ ys) = triple_mass xs + triple_mass ys := by
  induction xs with
  | nil => simp [triple_mass]
  | cons x xs ih =>
    rcases x with ⟨a, b, c⟩
    dsimp [triple_mass]
    rw [ih]
    omega

theorem triple_mass_power (xs : List (ℕ × ℕ × ℕ)) (n : ℕ) :
    triple_mass (xs ^ n) = n * triple_mass xs := by
  induction n with
  | zero => simp [triple_mass]
  | succ n ih =>
    rw [pow_succ_list, triple_mass_app, ih]
    ring

theorem TripleWord_app (xs ys : List (ℕ × ℕ × ℕ)) :
    TripleWord (xs ++ ys) = TripleWord xs ++ TripleWord ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a, b, c⟩
    simp only [List.cons_append, TripleWord, ih, List.append_assoc]

theorem TripleWord_power (xs : List (ℕ × ℕ × ℕ)) (n : ℕ) :
    TripleWord (xs ^ n) = (TripleWord xs) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list, TripleWord_app, ih, pow_succ_list]

/-- Period-12 left block `M9 := [1] ^ 9 ++ [0, 1, 0]` (`M9` in `FIBv7.v`). -/
def M9 : List (Fin 2) := ([1] : List (Fin 2)) ^ 9 ++ [0, 1, 0]

theorem M9_pairs (n : ℕ) (l : ListBlank (Fin 2)) :
    l <+ [0] <+ (M9.reverse) ^ n = l <+ (Pairs (List.replicate n 4)).reverse <+ [0] := by
  rw [Pairs_repeat]
  have hM9 : M9.reverse = (0 : Fin 2) :: (([1, 0] : List (Fin 2)) ++ ([1] : List (Fin 2)) ^ 9) := by
    decide
  rw [hM9, ← append_assoc, lpow_rotate_list]
  rfl

/-- Flatten triples into a flat list of half-runs (`TripleFields` in `FIBv7.v`). -/
def TripleFields : List (ℕ × ℕ × ℕ) → List ℕ
  | [] => []
  | (a, b, c) :: ts => a :: b :: c :: TripleFields ts

/--
Left word left behind after state `E` sweeps across `Post (TripleFields ts)` (`EWord` in
  `FIBv7.v`). -/
def EWord : List (ℕ × ℕ × ℕ) → List (Fin 2)
  | [] => []
  | (a, b, c) :: ts =>
    ([0, 1] : List (Fin 2)) ^ (1 + a) ++ ([1] : List (Fin 2)) ^ (4 + (b + c) * 2) ++ EWord ts

/-- Spaced half-run list `xs.flatMap (fun x => [0, 0, x])` (`Spaced` in `FIBv7.v`). -/
def Spaced (xs : List ℕ) : List ℕ :=
  xs.flatMap (fun x => [0, 0, x])

/-- Raised half-run list `xs.flatMap (fun x => [1, 1, 1 + x])` (`Raised` in `FIBv7.v`). -/
def Raised (xs : List ℕ) : List ℕ :=
  xs.flatMap (fun x => [1, 1, 1 + x])

theorem Spaced_map (xs : List ℕ) :
    List.map (fun x => 1 + x) (Spaced xs ++ [0, 0]) = Raised xs ++ [1, 1] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change [1, 1, 1 + x] ++ List.map (fun x => 1 + x) (Spaced xs ++ [0, 0]) =
      [1, 1, 1 + x] ++ (Raised xs ++ [1, 1])
    rw [ih]

/-- Parametric bouncer block `[1] ^ b ++ [0, 1] ^ r ++ [0] ++ [1] ^ c` (`Block` in `FIBv7.v`). -/
def Block (b r c : ℕ) : List (Fin 2) :=
  ([1] : List (Fin 2)) ^ b ++ ([0, 1] : List (Fin 2)) ^ r ++ [0] ++ ([1] : List (Fin 2)) ^ c

theorem Block_reverse (b r c : ℕ) :
    (Block b r c).reverse =
      ([1] : List (Fin 2)) ^ c ++ [0] ++ ([1, 0] : List (Fin 2)) ^ r ++ ([1] : List (Fin 2)) ^ b
        := by
  dsimp [Block]
  simp only [List.append_assoc, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, rev_power, rev_ones]

/-- Parametric `C`-state block chain (`Chain` in `FIBv7.v`). -/
def Chain (C : Λ) (r c n a : ℕ) (l : ListBlank (Fin 2)) : Cfg (Fin 2) Λ :=
  (l <+ (Block 0 r c).reverse ^ n <+ ([1, 0] : List (Fin 2)) ^ r <+ [0] <+ ([1] : List (Fin 2)) ^ a)
    {{C}}> default

/-- Periodic `C`-state half-run configuration (`CPeriod` in `FIBv7.v`). -/
def CPeriod (C : Λ) (n : ℕ) (p : List ℕ) (e : ℕ) (q w t : List ℕ) (a : ℕ) : Cfg (Fin 2) Λ :=
  ((default : ListBlank (Fin 2)) <+ (Post p).reverse <+ ([1] : List (Fin 2)) ^ e <+ [0]
    <+ (Post q).reverse <+ (Post w).reverse ^ n <+ (Post t).reverse
    <+ ([1] : List (Fin 2)) ^ (a * 2)) {{C}}> default

-- ============================================================================
-- 5. Variable-Arity `Sweep` Tile Schema over `Longitudinal.SegRLs` / `SideRLs`
-- ============================================================================

/-- Relational specification of one longitudinal fractal sweep (`Sweep` in `FIBv7.v`):
each triple `(1 + a * 2, b, c)` of half-runs explodes into `a` unit fields `1` followed by a merged
field `3 + b + c`. -/
inductive Sweep : List ℕ → List ℕ → Prop where
  | nil : Sweep [] []
  | cons (a b c : ℕ) (xs ys : List ℕ) :
      Sweep xs ys →
      Sweep ((1 + a * 2) :: b :: c :: xs) (List.replicate a 1 ++ (3 + b + c) :: ys)

/-- Computable partial function executing one `Sweep` pass (`sweep_step` in `FIBv7.v`). -/
def sweep_step : List ℕ → Option (List ℕ)
  | [] => some []
  | [x] => none
  | [x, y] => none
  | x :: b :: c :: xs =>
    if x % 2 == 1 then
      match sweep_step xs with
      | some ys => some (List.replicate (x / 2) 1 ++ (3 + b + c) :: ys)
      | none => none
    else
      none

theorem sweep_step_spec : ∀ {xs ys : List ℕ}, sweep_step xs = some ys → Sweep xs ys
  | [], _, h => by
    cases h
    exact .nil
  | [_], _, h => by cases h
  | [_, _], _, h => by cases h
  | x :: b :: c :: xs, ys, h => by
    dsimp [sweep_step] at h
    split_ifs at h with hodd
    rcases hrec : sweep_step xs with _ | zs <;> rw [hrec] at h
    · cases h
    · dsimp only at h
      injection h with h
      subst h
      rw [beq_iff_eq] at hodd
      have hx : x = 1 + (x / 2) * 2 := by omega
      have hcon := Sweep.cons (x / 2) b c xs zs (sweep_step_spec hrec)
      rwa [← hx] at hcon

/-- Iterate `sweep_step` `k` times (`sweep_iter` in `FIBv7.v`). -/
def sweep_iter : ℕ → List ℕ → Option (List ℕ)
  | 0, xs => some xs
  | k + 1, xs =>
    match sweep_step xs with
    | some ys => sweep_iter k ys
    | none => none

/-- Any boundary signal list `ls` passes unmodified through the empty segment `[]` (`segRLs_nil` in
`Individual62.v`). -/
theorem segRLs_empty {M : Machine Γ Λ} (ls : List (DH0 Γ Λ × DH0 Γ Λ)) :
    SegRLs M ls ls [] [] := by
  induction ls with
  | nil => exact .nil []
  | cons hh ls ih =>
    rcases hh with ⟨h₁, h₂⟩
    exact .lrcons (fun _ _ => stepStar_refl M _) (fun _ _ => stepStar_refl M _) (.nil []) ih

/-- Lift `Sweep xs ys` to a 2D longitudinal tile `SegRLs M [sweep_h] [sweep_h] (Fields xs) (Fields
  ys)`
given the single-triple tile `sweep_triple` (`Sweep_spec` in `FIBv7.v`). -/
theorem Sweep_spec {M : Machine (Fin 2) Λ} {sweep_h : DH0 (Fin 2) Λ × DH0 (Fin 2) Λ}
    (htriple : ∀ a b c : ℕ,
      SegRLs M [sweep_h] [sweep_h]
        (Field (1 + a * 2) ++ Field b ++ Field c)
        ((Field 1) ^ a ++ Field (3 + b + c)))
    {xs ys : List ℕ} (h : Sweep xs ys) :
    SegRLs M [sweep_h] [sweep_h] (Fields xs) (Fields ys) := by
  induction h with
  | nil => exact segRLs_empty [sweep_h]
  | cons a b c xs ys _ ih =>
    have h1 : Fields ((1 + a * 2) :: b :: c :: xs) =
        (Field (1 + a * 2) ++ Field b ++ Field c) ++ Fields xs := by
      simp [Fields, List.append_assoc]
    have h2 : Fields (List.replicate a 1 ++ (3 + b + c) :: ys) =
        ((Field 1) ^ a ++ Field (3 + b + c)) ++ Fields ys := by
      rw [Fields_app, Fields_repeat]
      simp [Fields, List.append_assoc]
    rw [h1, h2]
    exact (htriple a b c).concat ih

/-- Horizontal repetition of a longitudinal tile (`sweep_power` in `FIBv7.v`). -/
theorem sweep_power {M : Machine Γ Λ} {hs : List (DH0 Γ Λ × DH0 Γ Λ)} {xs ys : List Γ}
    (n : ℕ) (h : SegRLs M hs hs xs ys) :
    SegRLs M hs hs (xs ^ n) (ys ^ n) := by
  induction n with
  | zero => exact segRLs_empty hs
  | succ n ih => exact h.concat ih

/-- Lift `k` iterated sweeps `sweep_iter k xs = some ys` to `SegRLs M ([sweep_h] ^ k) ([sweep_h] ^
  k)`
(`sweep_iter_spec` in `FIBv7.v`). -/
theorem sweep_iter_spec {M : Machine (Fin 2) Λ} {sweep_h : DH0 (Fin 2) Λ × DH0 (Fin 2) Λ}
    (htriple : ∀ a b c : ℕ,
      SegRLs M [sweep_h] [sweep_h]
        (Field (1 + a * 2) ++ Field b ++ Field c)
        ((Field 1) ^ a ++ Field (3 + b + c)))
    (k : ℕ) {xs ys : List ℕ} (hs : sweep_iter k xs = some ys) :
    SegRLs M ([sweep_h] ^ k) ([sweep_h] ^ k) (Fields xs) (Fields ys) := by
  induction k generalizing xs ys with
  | zero =>
    cases hs
    exact .nil (Fields xs)
  | succ k ih =>
    dsimp [sweep_iter] at hs
    rcases hstep : sweep_step xs with _ | zs <;> rw [hstep] at hs
    · cases hs
    · rw [pow_succ_list]
      exact (Sweep_spec htriple (sweep_step_spec hstep)).trans (ih hs)

/-- Combine `k` sweeps over a periodic prefix `(Fields xs) ^ n`, a tail `Fields xt`, and a blank
right wall (`right_sweeps` in `FIBv7.v`). -/
theorem right_sweeps {M : Machine (Fin 2) Λ} {sweep_h : DH0 (Fin 2) Λ × DH0 (Fin 2) Λ}
    (htriple : ∀ a b c : ℕ,
      SegRLs M [sweep_h] [sweep_h]
        (Field (1 + a * 2) ++ Field b ++ Field c)
        ((Field 1) ^ a ++ Field (3 + b + c)))
    (hwall : ∀ k : ℕ, SideRLs M ([sweep_h] ^ k) default default)
    (k n : ℕ) {xs ys xt yt : List ℕ}
    (hx : sweep_iter k xs = some ys)
    (ht : sweep_iter k xt = some yt) :
    SideRLs M ([sweep_h] ^ k)
      ((Fields xs) ^ n +> (Fields xt +> default))
      ((Fields ys) ^ n +> (Fields yt +> default)) :=
  (sweep_power n (sweep_iter_spec htriple k hx)).sideRLs_concat
    ((sweep_iter_spec htriple k ht).sideRLs_concat (hwall k))

-- ============================================================================
-- 6. Machine-Generic List-Induction Combinators
-- ============================================================================

/-- Absorb a reversed `Post xs` list into an even run `[1] ^ (a * 2)` in state `C`
(`even_absorb_list` in `FIBv7.v`). -/
theorem even_absorb_list {M : Machine (Fin 2) Λ} {C : Λ}
    (heven_pair : ∀ a x : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ ([1] : List (Fin 2)) ^ (1 + x * 2) <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2))
        {{C}}> default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ ((a + x + 2) * 2)) {{C}}> default))
    (xs : List ℕ) (a : ℕ) (l : ListBlank (Fin 2)) :
    ((l <+ (Post xs).reverse <+ ([1] : List (Fin 2)) ^ (a * 2)) {{C}}> default) [M]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ ((a + mass xs) * 2)) {{C}}> default) := by
  induction xs generalizing a l with
  | nil =>
    change ((l <+ [] <+ ([1] : List (Fin 2)) ^ (a * 2)) {{C}}> default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ ((a + 0) * 2)) {{C}}> default)
    exact stepStar_refl M _
  | cons x xs ih =>
    dsimp [Post, mass]
    simp only [List.append_assoc, List.reverse_append, rev_ones, append_assoc]
    refine stepStar_trans (ih a (l <+ ([1] : List (Fin 2)) ^ (1 + x * 2) <+ [0])) ?_
    have h := heven_pair (a + mass xs) x l
    have heq : (a + mass xs + x + 2) * 2 = (a + (x + 2 + mass xs)) * 2 := by ring
    rwa [heq] at h

/-- Absorb `n` copies of `(Post xs).reverse` into an even run `[1] ^ (a * 2)` in state `C`
(`even_absorb_power` in `FIBv7.v`). -/
theorem even_absorb_power {M : Machine (Fin 2) Λ} {C : Λ}
    (heven_pair : ∀ a x : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ ([1] : List (Fin 2)) ^ (1 + x * 2) <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2))
        {{C}}> default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ ((a + x + 2) * 2)) {{C}}> default))
    (n : ℕ) (xs : List ℕ) (a : ℕ) (l : ListBlank (Fin 2)) :
    ((l <+ (Post xs).reverse ^ n <+ ([1] : List (Fin 2)) ^ (a * 2)) {{C}}> default) [M]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ ((a + n * mass xs) * 2)) {{C}}> default) := by
  induction n generalizing a l with
  | zero =>
    simp only [pow_zero_list, Nat.zero_mul, Nat.add_zero]
    exact stepStar_refl M _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (even_absorb_list heven_pair xs a (l <+ (Post xs).reverse ^ n)) ?_
    have h := ih (a + mass xs) l
    have heq : (a + mass xs + n * mass xs) * 2 = (a + (n + 1) * mass xs) * 2 := by ring
    rwa [heq] at h

/-- Left-moving `A` return across `(Pairs xs).reverse` (`A_return_list` in `FIBv7.v`). -/
theorem A_return_list {M : Machine (Fin 2) Λ} {A : Λ}
    (hret_pair : ∀ n : ℕ, ∀ l r : ListBlank (Fin 2),
      ((l <+ [0] <+ ([1] : List (Fin 2)) ^ (1 + n * 2) <+ [1, 0]) <{{A}} r) [M]⊢*
      (l <{{A}} (([1] : List (Fin 2)) ^ (3 + n * 2) +> ([0] +> r))))
    (xs : List ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (Pairs xs).reverse) <{{A}} r) [M]⊢*
    (l <{{A}} (Post (xs.map (fun x => 1 + x)) +> r)) := by
  induction xs generalizing l r with
  | nil => exact stepStar_refl M _
  | cons x xs ih =>
    rw [Pairs_cons]
    simp only [append_assoc]
    refine stepStar_trans (ih (l <+ [0] <+ ([1] : List (Fin 2)) ^ (1 + x * 2) <+ [1, 0]) r) ?_
    have h := hret_pair x l (Post (xs.map (fun x => 1 + x)) +> r)
    change ((l <+ [0] <+ ([1] : List (Fin 2)) ^ (1 + x * 2) <+ [1, 0]) <{{A}}
        (Post (xs.map (fun x => 1 + x)) +> r)) [M]⊢*
      (l <{{A}} ((([1] : List (Fin 2)) ^ (1 + (1 + x) * 2) ++ [0] ++ Post (xs.map (fun x => 1 +
        x))) +> r))
    rw [append_assoc, append_assoc]
    have heq : 3 + x * 2 = 1 + (1 + x) * 2 := by omega
    rwa [heq] at h

/--
Left-moving `A` return across `n` copies of `(Pairs xs).reverse` (`A_return_power` in `FIBv7.v`). -/
theorem A_return_power {M : Machine (Fin 2) Λ} {A : Λ}
    (hret_pair : ∀ n : ℕ, ∀ l r : ListBlank (Fin 2),
      ((l <+ [0] <+ ([1] : List (Fin 2)) ^ (1 + n * 2) <+ [1, 0]) <{{A}} r) [M]⊢*
      (l <{{A}} (([1] : List (Fin 2)) ^ (3 + n * 2) +> ([0] +> r))))
    (n : ℕ) (xs : List ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (Pairs xs).reverse ^ n) <{{A}} r) [M]⊢*
    (l <{{A}} ((Post (xs.map (fun x => 1 + x))) ^ n +> r)) := by
  induction n generalizing l r with
  | zero => exact stepStar_refl M _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (A_return_list hret_pair xs (l <+ (Pairs xs).reverse ^ n) r) ?_
    have h := ih l (Post (xs.map (fun x => 1 + x)) +> r)
    rwa [← append_assoc, ← pow_succ_list' (Post (xs.map (fun x => 1 + x))) n] at h

/-- Recover a non-empty `(Pairs (x :: xs)).reverse` from an odd run in state `C`
(`C_recover_list` in `FIBv7.v`). -/
theorem C_recover_list {M : Machine (Fin 2) Λ} {A C : Λ}
    (hret_pair : ∀ n : ℕ, ∀ l r : ListBlank (Fin 2),
      ((l <+ [0] <+ ([1] : List (Fin 2)) ^ (1 + n * 2) <+ [1, 0]) <{{A}} r) [M]⊢*
      (l <{{A}} (([1] : List (Fin 2)) ^ (3 + n * 2) +> ([0] +> r))))
    (hrec_one : ∀ x a : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ [0] <+ ([1] : List (Fin 2)) ^ (1 + x * 2) <+ [0, 1, 0]
        <+ ([1] : List (Fin 2)) ^ (1 + a * 2)) {{C}}> default) [M]⊢*
      (l <{{A}} (([1] : List (Fin 2)) ^ (3 + x * 2) +> ([0] +> (([1] : List (Fin 2)) ^ (5 + a * 2)
        +> default)))))
    (x : ℕ) (xs : List ℕ) (a : ℕ) (l : ListBlank (Fin 2)) :
    ((l <+ (Pairs (x :: xs)).reverse <+ [0] <+ ([1] : List (Fin 2)) ^ (1 + a * 2)) {{C}}> default)
      [M]⊢*
    (l <{{A}} (Post ((x :: xs).map (fun x => 1 + x)) +> (([1] : List (Fin 2)) ^ (5 + a * 2) +>
      default))) := by
  induction xs generalizing x l with
  | nil =>
    rw [Pairs_cons]
    dsimp [Pairs, Post, List.map]
    simp only [List.append_nil, append_assoc, append_cons, append_nil]
    have h := hrec_one x a l
    simp only [append_assoc, append_cons, append_nil] at h
    have heq : 3 + x * 2 = 1 + (1 + x) * 2 := by omega
    rwa [heq] at h
  | cons y xs ih =>
    rw [Pairs_cons x (y :: xs)]
    simp only [append_assoc]
    refine stepStar_trans (ih y (l <+ [0] <+ ([1] : List (Fin 2)) ^ (1 + x * 2) <+ [1, 0])) ?_
    have h := hret_pair x l
      (Post ((y :: xs).map (fun x => 1 + x)) +> (([1] : List (Fin 2)) ^ (5 + a * 2) +> default))
    change ((l <+ [0] <+ ([1] : List (Fin 2)) ^ (1 + x * 2) <+ [1, 0]) <{{A}}
        (Post ((y :: xs).map (fun x => 1 + x)) +> (([1] : List (Fin 2)) ^ (5 + a * 2) +>
          default))) [M]⊢*
      (l <{{A}} ((([1] : List (Fin 2)) ^ (1 + (1 + x) * 2) ++ [0] ++
        Post ((y :: xs).map (fun x => 1 + x))) +> (([1] : List (Fin 2)) ^ (5 + a * 2) +> default)))
    rw [append_assoc, append_assoc]
    have heq : 3 + x * 2 = 1 + (1 + x) * 2 := by omega
    rwa [heq] at h

/--
Sweep state `D` across `TripleWord ts *> Field u *> Field v *> 0inf` (`D_sweep` in `FIBv7.v`). -/
theorem D_sweep {M : Machine (Fin 2) Λ} {C D : Λ}
    (heven_pair : ∀ a x : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ ([1] : List (Fin 2)) ^ (1 + x * 2) <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2))
        {{C}}> default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ ((a + x + 2) * 2)) {{C}}> default))
    (hD_pair : ∀ u v : ℕ, ∀ l r : ListBlank (Fin 2),
      ((l <+ [0]) {{D}}> (Field u +> (Field v +> r))) [M]⊢*
      ((l <+ [1] <+ (Post [0]).reverse ^ (1 + u) <+ ([1] : List (Fin 2)) ^ (2 + v * 2)) {{C}}> r))
    (hD_triple : ∀ a b c : ℕ, ∀ l r : ListBlank (Fin 2),
      ((l <+ [0]) {{D}}> (Field a +> (Field b +> (Field c +> r)))) [M]⊢*
      ((l <+ [1] <+ (Post [0]).reverse ^ (1 + a) <+ ([1] : List (Fin 2)) ^ (3 + (b + c) * 2) <+
        [0]) {{D}}> r))
    (ts : List (ℕ × ℕ × ℕ)) (u v : ℕ) (l : ListBlank (Fin 2)) :
    ((l <+ [0]) {{D}}> (TripleWord ts +> (Field u +> (Field v +> default)))) [M]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ (7 + (u * 2 + v + triple_mass ts) * 2)) {{C}}> default) := by
  induction ts generalizing l with
  | nil =>
    dsimp [TripleWord, triple_mass]
    refine stepStar_trans (hD_pair u v l default) ?_
    have h := even_absorb_power heven_pair (1 + u) [0] (1 + v) (l <+ [1])
    have hm : mass [0] = 2 := rfl
    have h0 : (1 + v) * 2 = 2 + v * 2 := by omega
    rw [hm, h0] at h
    have h1 : (l <+ [1]) <+ ([1] : List (Fin 2)) ^ ((1 + v + (1 + u) * 2) * 2) =
        l <+ ([1] : List (Fin 2)) ^ (7 + (u * 2 + v + 0) * 2) := by
      change (([1] : List (Fin 2)) ^ ((1 + v + (1 + u) * 2) * 2)) +> (([1] : List (Fin 2)) ^ 1 +>
        l) = _
      rw [lpow_add']
      congr 2
      omega
    rwa [h1] at h
  | cons t ts ih =>
    rcases t with ⟨a, b, c⟩
    dsimp [TripleWord, triple_mass]
    simp only [append_assoc]
    refine stepStar_trans (hD_triple a b c l (TripleWord ts +> (Field u +> (Field v +> default))))
      ?_
    refine stepStar_trans (ih (l <+ [1] <+ (Post [0]).reverse ^ (1 + a) <+ ([1] : List (Fin 2)) ^
      (3 + (b + c) * 2))) ?_
    have hjoin :
        (l <+ [1] <+ (Post [0]).reverse ^ (1 + a) <+ ([1] : List (Fin 2)) ^ (3 + (b + c) * 2)
          <+ ([1] : List (Fin 2)) ^ (7 + (u * 2 + v + triple_mass ts) * 2)) =
        (l <+ [1] <+ (Post [0]).reverse ^ (1 + a)
          <+ ([1] : List (Fin 2)) ^ ((5 + b + c + u * 2 + v + triple_mass ts) * 2)) := by
      rw [lpow_add']
      congr 2
      omega
    rw [hjoin]
    have h := even_absorb_power heven_pair (1 + a) [0] (5 + b + c + u * 2 + v + triple_mass ts) (l
      <+ [1])
    have hm : mass [0] = 2 := rfl
    rw [hm] at h
    have h2 : (l <+ [1]) <+ ([1] : List (Fin 2)) ^ ((5 + b + c + u * 2 + v + triple_mass ts + (1 +
      a) * 2) * 2) =
        l <+ ([1] : List (Fin 2)) ^ (7 + (u * 2 + v + (4 + a * 2 + b + c + triple_mass ts)) * 2)
          := by
      change (([1] : List (Fin 2)) ^ ((5 + b + c + u * 2 + v + triple_mass ts + (1 + a) * 2) * 2))
        +>
        (([1] : List (Fin 2)) ^ 1 +> l) = _
      rw [lpow_add']
      congr 2
      omega
    rwa [h2] at h

/-- Sweep state `E` across `Post (TripleFields ts)` (`E_sweep` in `FIBv7.v`). -/
theorem E_sweep {M : Machine (Fin 2) Λ} {E : Λ}
    (hE_triple : ∀ a b c : ℕ, ∀ l r : ListBlank (Fin 2),
      (l {{E}}> (Post [a, b, c] +> r)) [M]⊢*
      ((l <+ ([1, 0] : List (Fin 2)) ^ (1 + a) <+ ([1] : List (Fin 2)) ^ (4 + (b + c) * 2)) {{E}}>
        r))
    (ts : List (ℕ × ℕ × ℕ)) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (Post (TripleFields ts) +> r)) [M]⊢*
    ((l <+ (EWord ts).reverse) {{E}}> r) := by
  induction ts generalizing l with
  | nil => exact stepStar_refl M _
  | cons t ts ih =>
    rcases t with ⟨a, b, c⟩
    change (l {{E}}> (Post ([a, b, c] ++ TripleFields ts) +> r)) [M]⊢* _
    rw [Post_app, append_assoc]
    refine stepStar_trans (hE_triple a b c l (Post (TripleFields ts) +> r)) ?_
    have h := ih (l <+ ([1, 0] : List (Fin 2)) ^ (1 + a) <+ ([1] : List (Fin 2)) ^ (4 + (b + c) *
      2))
    dsimp [EWord]
    simp only [List.append_assoc, List.reverse_append, rev_power, rev_ones, append_assoc]
    exact h

/-- Absorb `n` alternating pairs `[1, 0] ^ n` in state `D` (`D_absorb_alt` in `FIBv7.v`). -/
theorem D_absorb_alt {M : Machine (Fin 2) Λ} {D : Λ}
    (hD01 : ∀ a : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ [1, 0]) <{{D}} (([1] : List (Fin 2)) ^ (a * 2) +> default)) [M]⊢*
      (l <{{D}} (([1] : List (Fin 2)) ^ (4 + a * 2) +> default)))
    (n a : ℕ) (l : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ n) <{{D}} (([1] : List (Fin 2)) ^ (a * 2) +> default)) [M]⊢*
    (l <{{D}} (([1] : List (Fin 2)) ^ ((a + n * 2) * 2) +> default)) := by
  induction n generalizing a l with
  | zero =>
    simp only [pow_zero_list, Nat.zero_mul, Nat.add_zero]
    exact stepStar_refl M _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (hD01 a (l <+ ([1, 0] : List (Fin 2)) ^ n)) ?_
    have h := ih (a + 2) l
    have heq1 : 4 + a * 2 = (a + 2) * 2 := by omega
    have heq2 : (a + 2 + n * 2) * 2 = (a + (n + 1) * 2) * 2 := by omega
    rw [← heq1, heq2] at h
    exact h

/--
Absorb `n` reversed `Block (b * 2) r (1 + c * 2)` blocks in state `D` (`D_block_power` in
`FIBv7.v`). -/
theorem D_block_power {M : Machine (Fin 2) Λ} {D : Λ}
    (hD_block : ∀ b r c a : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ (Block (b * 2) r (1 + c * 2)).reverse) <{{D}} (([1] : List (Fin 2)) ^ (a * 2) +>
        default)) [M]⊢*
      (l <{{D}} (([1] : List (Fin 2)) ^ ((a + b + c + r * 2 + 2) * 2) +> default)))
    (n b r c a : ℕ) (l : ListBlank (Fin 2)) :
    ((l <+ (Block (b * 2) r (1 + c * 2)).reverse ^ n) <{{D}} (([1] : List (Fin 2)) ^ (a * 2) +>
      default)) [M]⊢*
    (l <{{D}} (([1] : List (Fin 2)) ^ ((a + n * (b + c + r * 2 + 2)) * 2) +> default)) := by
  induction n generalizing a l with
  | zero =>
    simp only [pow_zero_list, Nat.zero_mul, Nat.add_zero]
    exact stepStar_refl M _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (hD_block b r c a (l <+ (Block (b * 2) r (1 + c * 2)).reverse ^ n)) ?_
    have h := ih (a + b + c + r * 2 + 2) l
    have heq : (a + b + c + r * 2 + 2 + n * (b + c + r * 2 + 2)) * 2 =
        (a + (n + 1) * (b + c + r * 2 + 2)) * 2 := by ring
    rwa [heq] at h

/-- Absorb `[1] ^ (1 + b) <+ [1, 0] ^ n <+ [0] <+ [1] ^ (a * 2)` in state `C`
(`C_absorb_alt` in `FIBv7.v`). -/
theorem C_absorb_alt {M : Machine (Fin 2) Λ} {C : Λ}
    (habsorb_zero : ∀ n : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ [0, 1] <+ ([1] : List (Fin 2)) ^ (n * 2)) {{C}}> default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ (4 + n * 2)) {{C}}> default))
    (habsorb_run : ∀ a b : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2)) {{C}}>
        default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ (4 + b + a * 2)) {{C}}> default))
    (n a b : ℕ) (l : ListBlank (Fin 2)) :
    ((l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ ([1, 0] : List (Fin 2)) ^ n <+ [0]
       <+ ([1] : List (Fin 2)) ^ (a * 2)) {{C}}> default) [M]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ (4 + b + (a + n * 2) * 2)) {{C}}> default) := by
  induction n generalizing a l with
  | zero =>
    dsimp [pow_zero_list]
    have h := habsorb_run a b l
    have heq : 4 + b + a * 2 = 4 + b + (a + 0 * 2) * 2 := by omega
    rwa [heq] at h
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    have h0 :
        (l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ ([1, 0] : List (Fin 2)) ^ n) <+ ([1, 0] : List
          (Fin 2)) <+ [0] =
        (l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ ([1, 0] : List (Fin 2)) ^ n <+ [0]) <+ [0, 1] := rfl
    rw [h0]
    refine stepStar_trans
      (habsorb_zero a (l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ ([1, 0] : List (Fin 2)) ^ n <+ [0]))
        ?_
    have h := ih (a + 2) l
    have heq1 : 4 + a * 2 = (a + 2) * 2 := by omega
    have heq2 : 4 + b + (a + 2 + n * 2) * 2 = 4 + b + (a + (n + 1) * 2) * 2 := by omega
    rw [← heq1, heq2] at h
    exact h

/--
Absorb one reversed `Block (1 + b) r c` into `[1] ^ a` when `a + c = k * 2` (`C_block` in
`FIBv7.v`). -/
theorem C_block {M : Machine (Fin 2) Λ} {C : Λ}
    (habsorb_zero : ∀ n : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ [0, 1] <+ ([1] : List (Fin 2)) ^ (n * 2)) {{C}}> default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ (4 + n * 2)) {{C}}> default))
    (habsorb_run : ∀ a b : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2)) {{C}}>
        default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ (4 + b + a * 2)) {{C}}> default))
    (k b r c a : ℕ) (l : ListBlank (Fin 2)) (hk : a + c = k * 2) :
    ((l <+ (Block (1 + b) r c).reverse <+ ([1] : List (Fin 2)) ^ a) {{C}}> default) [M]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ (a + 4 + b + c + r * 4)) {{C}}> default) := by
  rw [Block_reverse]
  rw [append_assoc, append_assoc, append_assoc, lpow_add', hk]
  have h := C_absorb_alt habsorb_zero habsorb_run r k b l
  have heq : 4 + b + (k + r * 2) * 2 = a + 4 + b + c + r * 4 := by omega
  rwa [heq] at h

/-- Absorb `n` reversed `Block (1 + b) r c` blocks in state `C` (`C_block_power` in `FIBv7.v`). -/
theorem C_block_power {M : Machine (Fin 2) Λ} {C : Λ}
    (habsorb_zero : ∀ n : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ [0, 1] <+ ([1] : List (Fin 2)) ^ (n * 2)) {{C}}> default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ (4 + n * 2)) {{C}}> default))
    (habsorb_run : ∀ a b : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2)) {{C}}>
        default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ (4 + b + a * 2)) {{C}}> default))
    (n b r c a d k : ℕ) (l : ListBlank (Fin 2))
    (hd : b + c = d * 2) (ha : a + c = k * 2) :
    ((l <+ (Block (1 + b) r c).reverse ^ n <+ ([1] : List (Fin 2)) ^ a) {{C}}> default) [M]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ (a + n * (4 + b + c + r * 4))) {{C}}> default) := by
  induction n generalizing a k l with
  | zero =>
    simp only [pow_zero_list, Nat.zero_mul, Nat.add_zero]
    exact stepStar_refl M _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans
      (C_block habsorb_zero habsorb_run k b r c a (l <+ (Block (1 + b) r c).reverse ^ n) ha) ?_
    have h := ih (a + 4 + b + c + r * 4) (k + 2 + d + r * 2) l (by omega)
    have heq : a + 4 + b + c + r * 4 + n * (4 + b + c + r * 4) =
        a + (n + 1) * (4 + b + c + r * 4) := by ring
    rwa [heq] at h

/--
Collapse a `CPeriod` configuration into a single run `[1] ^ (5 + e * 2 + ...)` (`CPeriod_collapse`
in `FIBv7.v`). -/
theorem CPeriod_collapse {M : Machine (Fin 2) Λ} {C : Λ}
    (heven_pair : ∀ a x : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ ([1] : List (Fin 2)) ^ (1 + x * 2) <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2))
        {{C}}> default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ ((a + x + 2) * 2)) {{C}}> default))
    (habsorb_run : ∀ a b : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2)) {{C}}>
        default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ (4 + b + a * 2)) {{C}}> default))
    (n : ℕ) (p : List ℕ) (e : ℕ) (q w t : List ℕ) (a : ℕ) :
    (CPeriod C n p (2 + e * 2) q w t a) [M]⊢*
    (((default : ListBlank (Fin 2)) <+ (Post p).reverse
      <+ ([1] : List (Fin 2)) ^ (5 + e * 2 + (a + mass t + n * mass w + mass q) * 2))
      {{C}}> default) := by
  dsimp [CPeriod]
  refine stepStar_trans
    (even_absorb_list heven_pair t a
      ((default : ListBlank (Fin 2)) <+ (Post p).reverse <+ ([1] : List (Fin 2)) ^ (2 + e * 2)
        <+ [0] <+ (Post q).reverse <+ (Post w).reverse ^ n)) ?_
  refine stepStar_trans
    (even_absorb_power heven_pair n w (a + mass t)
      ((default : ListBlank (Fin 2)) <+ (Post p).reverse <+ ([1] : List (Fin 2)) ^ (2 + e * 2)
        <+ [0] <+ (Post q).reverse)) ?_
  refine stepStar_trans
    (even_absorb_list heven_pair q (a + mass t + n * mass w)
      ((default : ListBlank (Fin 2)) <+ (Post p).reverse <+ ([1] : List (Fin 2)) ^ (2 + e * 2) <+
        [0])) ?_
  have h := habsorb_run (a + mass t + n * mass w + mass q) (1 + e * 2)
    ((default : ListBlank (Fin 2)) <+ (Post p).reverse)
  have heq1 : 1 + (1 + e * 2) = 2 + e * 2 := by omega
  have heq2 : 4 + (1 + e * 2) + (a + mass t + n * mass w + mass q) * 2 =
      5 + e * 2 + (a + mass t + n * mass w + mass q) * 2 := by omega
  rw [heq1, heq2] at h
  exact h

/-- Batch `n * 3` copies of `[0] ++ [1] ^ (1 + p * 2)` in state `B` (`B_batch` in `FIBv7.v`). -/
theorem B_batch {M : Machine (Fin 2) Λ} {B : Λ}
    (hB_triple : ∀ p : ℕ, ∀ l r : ListBlank (Fin 2),
      (l {{B}}> ((([0] ++ ([1] : List (Fin 2)) ^ (1 + p * 2)) ^ 3) +> r)) [M]⊢*
      ((l <+ (Block (5 + p * 4) p 0).reverse) {{B}}> r))
    (p n : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{B}}> ((([0] ++ ([1] : List (Fin 2)) ^ (1 + p * 2)) ^ (n * 3)) +> r)) [M]⊢*
    ((l <+ (Block (5 + p * 4) p 0).reverse ^ n) {{B}}> r) := by
  induction n generalizing l with
  | zero => exact stepStar_refl M _
  | succ n ih =>
    have hmul : (n + 1) * 3 = 3 + n * 3 := by omega
    rw [hmul, pow_add_list, append_assoc]
    refine stepStar_trans (hB_triple p l ((([0] ++ ([1] : List (Fin 2)) ^ (1 + p * 2)) ^ (n * 3))
      +> r)) ?_
    have h := ih (l <+ (Block (5 + p * 4) p 0).reverse)
    rwa [← append_assoc, ← pow_succ_list' (Block (5 + p * 4) p 0).reverse n] at h

/-- Left-moving `B_half` across `n` copies of `(Block 2 (1 + a * 2) (1 + c * 2)).reverse`
(`B_half_power` in `FIBv7.v`). -/
theorem B_half_power {M : Machine (Fin 2) Λ} {B : Λ}
    (hB_half : ∀ a c : ℕ, ∀ l r : ListBlank (Fin 2),
      ((l <+ (Block 2 (1 + a * 2) (1 + c * 2)).reverse) <{{B}} ([0] +> r)) [M]⊢*
      (l <{{B}} ([0, 1, 1] +> (([0, 1, 1, 1] : List (Fin 2)) ^ a +> ([0] +> (([1] : List (Fin 2))
        ^ (3 + c * 2) +> r))))))
    (n a c : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (Block 2 (1 + a * 2) (1 + c * 2)).reverse ^ n) <{{B}} ([0] +> ([1, 1] +> r))) [M]⊢*
    (l <{{B}} ([0, 1, 1] +> ((([0, 1, 1, 1] : List (Fin 2)) ^ a ++ [0] ++ ([1] : List (Fin 2)) ^
      (5 + c * 2)) ^ n +> r))) := by
  induction n generalizing l r with
  | zero => exact stepStar_refl M _
  | succ n ih =>
    rw [pow_succ_list, append_assoc]
    refine stepStar_trans (hB_half a c (l <+ (Block 2 (1 + a * 2) (1 + c * 2)).reverse ^ n) ([1,
      1] +> r)) ?_
    let blk : List (Fin 2) := ([0, 1, 1, 1] : List (Fin 2)) ^ a ++ [0] ++ ([1] : List (Fin 2)) ^
      (5 + c * 2)
    have h1 :
        ([0, 1, 1] +> (([0, 1, 1, 1] : List (Fin 2)) ^ a +> ([0] +> (([1] : List (Fin 2)) ^ (3 + c
          * 2) +> ([1, 1] +> r))))) =
        ([0] +> ([1, 1] +> (blk +> r))) := by
      have h11 : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
      rw [h11, lpow_add']
      have heq : 3 + c * 2 + 2 = 5 + c * 2 := by omega
      rw [heq]
      dsimp [blk]
      simp only [append_assoc, append_cons, append_nil]
    rw [h1]
    refine stepStar_trans (ih l (blk +> r)) ?_
    rw [← append_assoc (blk ^ n) blk r, ← pow_succ_list' blk n]

/-- Left-caller `SideRLs` induction across `(Post xs).reverse` (`caller_list` in `FIBv7.v`). -/
theorem caller_list {M : Machine (Fin 2) Λ} {h_call : DH0 (Fin 2) Λ × DH0 (Fin 2) Λ}
    (hcall_one : ∀ a : ℕ, ∀ l : ListBlank (Fin 2),
      SideRLs (flipTM M) [h_call]
        (l <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2))
        (l <+ ([1] : List (Fin 2)) ^ (3 + a * 2)))
    (xs : List ℕ) (a : ℕ) (l : ListBlank (Fin 2)) :
    SideRLs (flipTM M) ([h_call] ^ xs.length)
      (l <+ (Post xs).reverse <+ ([1] : List (Fin 2)) ^ (a * 2))
      (l <+ ([1] : List (Fin 2)) ^ ((a + mass xs) * 2)) := by
  induction xs generalizing a l with
  | nil =>
    change SideRLs (flipTM M) []
      (l <+ [] <+ ([1] : List (Fin 2)) ^ (a * 2))
      (l <+ ([1] : List (Fin 2)) ^ ((a + 0) * 2))
    exact .nil _
  | cons x xs ih =>
    rw [List.length_cons, pow_succ_list']
    dsimp [Post, mass]
    simp only [List.append_assoc, List.reverse_append, rev_ones, append_assoc]
    refine (ih a (l <+ ([1] : List (Fin 2)) ^ (1 + x * 2) <+ [0])).trans ?_
    have h1 := hcall_one (a + mass xs) (l <+ ([1] : List (Fin 2)) ^ (1 + x * 2))
    have heq : (l <+ ([1] : List (Fin 2)) ^ (1 + x * 2)) <+ ([1] : List (Fin 2)) ^ (3 + (a + mass
      xs) * 2) =
        l <+ ([1] : List (Fin 2)) ^ ((a + (x + 2 + mass xs)) * 2) := by
      rw [lpow_add']
      congr 2
      omega
    rwa [heq] at h1

/-- Collapse a `Chain` with an even leading run `[1] ^ (a * 2)` (`Chain_even` in `FIBv7.v`). -/
theorem Chain_even {M : Machine (Fin 2) Λ} {C : Λ}
    (habsorb_zero : ∀ n : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ [0, 1] <+ ([1] : List (Fin 2)) ^ (n * 2)) {{C}}> default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ (4 + n * 2)) {{C}}> default))
    (habsorb_run : ∀ a b : ℕ, ∀ l : ListBlank (Fin 2),
      ((l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2)) {{C}}>
        default) [M]⊢*
      ((l <+ ([1] : List (Fin 2)) ^ (4 + b + a * 2)) {{C}}> default))
    (r c n a b : ℕ) (l : ListBlank (Fin 2)) :
    (Chain C r (1 + c * 2) n (a * 2) (l <+ ([1] : List (Fin 2)) ^ (1 + b))) [M]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ (4 + b + a * 2 + r * 4 + n * (4 + c * 2 + r * 4))) {{C}}>
      default) := by
  induction n generalizing a b l with
  | zero =>
    dsimp [Chain, pow_zero_list]
    have h := C_absorb_alt habsorb_zero habsorb_run r a b l
    have heq : 4 + b + (a + r * 2) * 2 = 4 + b + a * 2 + r * 4 + 0 * (4 + c * 2 + r * 4) := by omega
    rwa [heq] at h
  | succ n ih =>
    unfold Chain at ih ⊢
    have hblk : (Block 0 r (1 + c * 2)).reverse =
        ([1] : List (Fin 2)) ^ (1 + c * 2) ++ [0] ++ ([1, 0] : List (Fin 2)) ^ r := by
      rw [Block_reverse, pow_zero_list, List.append_nil]
    have hstep1 := ih a (c * 2) (l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ ([1, 0] : List (Fin 2)) ^
      r <+ [0])
    have hlhs :
        (l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ (Block 0 r (1 + c * 2)).reverse ^ (n + 1)
          <+ ([1, 0] : List (Fin 2)) ^ r <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2)) =
        (l <+ ([1] : List (Fin 2)) ^ (1 + b) <+ ([1, 0] : List (Fin 2)) ^ r <+ [0]
          <+ ([1] : List (Fin 2)) ^ (1 + c * 2) <+ (Block 0 r (1 + c * 2)).reverse ^ n
          <+ ([1, 0] : List (Fin 2)) ^ r <+ [0] <+ ([1] : List (Fin 2)) ^ (a * 2)) := by
      rw [pow_succ_list', append_assoc, hblk]
      simp only [append_assoc]
    rw [hlhs]
    refine stepStar_trans hstep1 ?_
    have hrhs :
        4 + c * 2 + a * 2 + r * 4 + n * (4 + c * 2 + r * 4) =
        (2 + c + a + r * 2 + n * (2 + c + r * 2)) * 2 := by ring
    rw [hrhs]
    have h2 := C_absorb_alt habsorb_zero habsorb_run r (2 + c + a + r * 2 + n * (2 + c + r * 2)) b l
    have heq2 : 4 + b + (2 + c + a + r * 2 + n * (2 + c + r * 2) + r * 2) * 2 =
        4 + b + a * 2 + r * 4 + (n + 1) * (4 + c * 2 + r * 4) := by ring
    rwa [heq2] at h2

end BusyBeaver.FractalReturn
