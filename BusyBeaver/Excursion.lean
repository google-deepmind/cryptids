module

public import BusyBeaver.Counter

/-!
# Decreasing Halt-Budget Calculus, Conjugate-Shift Excursion Algebra & Arithmetic Views (`BusyBeaver.Excursion`)

Ported from the Coq BB(6) verification suite (`ccz181078/busycoq`, branch `BB6`):
- `Queue_v1.v`: Decreasing halt-budget non-halting calculus (`HaltsIn`, `Leads`, `Advances`,
  `haltsIn_reduce_multiStep`, `haltsIn_reduce_stepStar`, `haltsIn_reduce_stepPlus`,
  `not_haltsIn_of_advances`, `does_not_halt_of_advances`).
- `ChaoticFractalOthers_v1.v` & `ChaoticBell1Halt.v`: Conjugate-shift excursion word algebra
  (`ConjWord`, `ConjWord.nil`, `ConjWord.append`, `ConjWord.pow`, `ConjWord.excursion`,
  `ConjWord.excursion_plus`) and periodic RLE word commutation (`commute_pow`,
  `commute_pow_left`, `commute_pow_single`, `append_commute_pow`, `append_commute_pow_single`).
- `DivModCases.v`: Dependent Euclidean division-modulo views (`DivMod2`..`DivMod6`, `mod2`..`mod6`)
  and dependent subtraction view (`SubView`, `subView`).
- `Eqv_WordPairs.v` & `Eqv_v2.v`: Constructive (excluded-middle-free) halting and non-halting
  equivalence via common abstract transition models (`IsValidAcceleration.collatzHalts_of_haltsIn`,
  `IsValidAcceleration.isHalt_iff_constructive`, `IsValidAcceleration.isDoesNotHalt_iff`,
  `IsValidAcceleration.equiv_halt`, `IsValidAcceleration.equiv_doesNotHalt`).

All declarations live in `namespace BusyBeaver.Excursion` with `@[scoped simp]` attributes so that
importing `BusyBeaver.Basic` does not alter the default `simp` set of existing proofs.
-/

public section

open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.Counter

namespace BusyBeaver.Excursion

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- ============================================================================
-- 1. Decreasing Halt-Budget Calculus (`HaltsIn`, `Leads`, `Advances`)
-- ============================================================================

section HaltBudgetCalculus

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- `M` reaches a halting configuration from `c` in exactly `n` steps (`halts_in` in `Queue_v1.v`). -/
@[expose] def HaltsIn (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) : Prop :=
  ∃ cfg : Cfg Γ Λ, (c [M]⊢^{n} cfg) ∧ (step M cfg).isNone

theorem haltsIn_zero_iff {M : Machine Γ Λ} {c : Cfg Γ Λ} :
    HaltsIn M c 0 ↔ (step M c).isNone := by
  constructor
  · rintro ⟨cfg, hms, hnone⟩
    change some c = some cfg at hms
    injection hms with h_eq
    subst h_eq
    exact hnone
  · intro hnone
    exact ⟨c, rfl, hnone⟩

theorem haltsIn_iff_reachesStar_isNone {M : Machine Γ Λ} {c : Cfg Γ Λ} :
    (∃ n, HaltsIn M c n) ↔ ∃ cfg, (c [M]⊢* cfg) ∧ (step M cfg).isNone := by
  constructor
  · rintro ⟨n, cfg, hms, hnone⟩
    exact ⟨cfg, ⟨n, hms⟩, hnone⟩
  · rintro ⟨cfg, ⟨n, hms⟩, hnone⟩
    exact ⟨n, cfg, hms, hnone⟩

theorem isHalt_iff_exists_haltsIn (M : Machine Γ Λ) :
    IsHalt M ↔ ∃ n, HaltsIn M (init []) n :=
  haltsIn_iff_reachesStar_isNone.symm

private theorem multiStep_succ_local (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = Option.bind (multiStep M c n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

private theorem multiStep_add_local (M : Machine Γ Λ) (c : Cfg Γ Λ) (m n : ℕ) :
    multiStep M c (m + n) = (multiStep M c m).bind (fun c' => multiStep M c' n) := by
  induction n with
  | zero => simp [multiStep]
  | succ n ih =>
    rw [Nat.add_succ, multiStep_succ_local, ih, Option.bind_assoc]
    simp_rw [multiStep_succ_local]

private theorem multiStep_eq_none_of_halt {M : Machine Γ Λ} {c cfg : Cfg Γ Λ} {n : ℕ}
    (hn : c [M]⊢^{n} cfg) (hnone : (step M cfg).isNone) :
    ∀ d : ℕ, multiStep M c (n + 1 + d) = none
  | 0 => by
    have hstep : step M cfg = none := Option.isNone_iff_eq_none.mp hnone
    rw [Nat.add_zero, multiStep_succ_local, hn, Option.bind_some, hstep]
  | d + 1 => by
    have ih := multiStep_eq_none_of_halt hn hnone d
    have h1 : n + 1 + (d + 1) = (n + 1 + d) + 1 := by omega
    rw [h1, multiStep_succ_local, ih, Option.bind_none]

/-- Deterministic step-budget subtraction: if `c₁` reaches `c₂` in `k` steps and halts in `n`
    steps, then `k ≤ n` and `c₂` halts in `n - k` steps. -/
theorem haltsIn_reduce_multiStep {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {k n : ℕ}
    (h_reach : c₁ [M]⊢^{k} c₂) (h_halt : HaltsIn M c₁ n) :
    k ≤ n ∧ HaltsIn M c₂ (n - k) := by
  rcases h_halt with ⟨cfg, hn, hnone⟩
  rcases Nat.lt_or_ge n k with hlt | hge
  · have hk : k = n + 1 + (k - (n + 1)) := by omega
    have h_absurd : multiStep M c₁ k = none := by
      rw [hk]
      exact multiStep_eq_none_of_halt hn hnone (k - (n + 1))
    rw [h_reach] at h_absurd
    nomatch h_absurd
  · refine ⟨hge, cfg, ?_, hnone⟩
    have hn_eq : n = k + (n - k) := by omega
    rw [hn_eq, multiStep_add_local, h_reach, Option.bind_some] at hn
    exact hn

theorem haltsIn_of_multiStep {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {k m : ℕ}
    (h_reach : c₁ [M]⊢^{k} c₂) (h_halt : HaltsIn M c₂ m) :
    HaltsIn M c₁ (k + m) := by
  rcases h_halt with ⟨cfg, hm, hnone⟩
  refine ⟨cfg, ?_, hnone⟩
  rw [multiStep_add_local, h_reach, Option.bind_some]
  exact hm

/-- If `c₁ [M]⊢* c₂` and `c₁` halts in `n` steps, then `c₂` halts in `m ≤ n` steps. -/
theorem haltsIn_reduce_stepStar {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {n : ℕ}
    (h_reach : c₁ [M]⊢* c₂) (h_halt : HaltsIn M c₁ n) :
    ∃ m, m ≤ n ∧ HaltsIn M c₂ m := by
  rcases h_reach with ⟨k, hk⟩
  rcases haltsIn_reduce_multiStep hk h_halt with ⟨hkn, h_sub⟩
  exact ⟨n - k, by omega, h_sub⟩

/-- If `c₁ [M]⊢⁺ c₂` and `c₁` halts in `n` steps, then `c₂` halts in `m < n` steps. -/
theorem haltsIn_reduce_stepPlus {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {n : ℕ}
    (h_reach : c₁ [M]⊢⁺ c₂) (h_halt : HaltsIn M c₁ n) :
    ∃ m, m < n ∧ HaltsIn M c₂ m := by
  rcases h_reach with ⟨k, hk_pos, hk⟩
  rcases haltsIn_reduce_multiStep hk h_halt with ⟨hkn, h_sub⟩
  exact ⟨n - k, by omega, h_sub⟩

/-- `Leads M c P` (`leads` in `Queue_v1.v`): if `M` halts from `c` in `n` steps, then `M`
    reaches some configuration `d` satisfying `P d` that halts in `m ≤ n` steps.
    Crucially, if a branch never halts (`¬ HaltsIn M c n`), `Leads M c P` holds vacuously! -/
@[expose] def Leads (M : Machine Γ Λ) (c : Cfg Γ Λ) (P : Cfg Γ Λ → Prop) : Prop :=
  ∀ n, HaltsIn M c n → ∃ m d, m ≤ n ∧ P d ∧ HaltsIn M d m

/-- `Advances M c P` (`advances` in `Queue_v1.v`): if `M` halts from `c` in `n` steps, then `M`
    reaches some configuration `d` satisfying `P d` that halts in strictly fewer (`m < n`) steps. -/
@[expose] def Advances (M : Machine Γ Λ) (c : Cfg Γ Λ) (P : Cfg Γ Λ → Prop) : Prop :=
  ∀ n, HaltsIn M c n → ∃ m d, m < n ∧ P d ∧ HaltsIn M d m

theorem Leads.here {M : Machine Γ Λ} {c : Cfg Γ Λ} {P : Cfg Γ Λ → Prop}
    (hc : P c) : Leads M c P :=
  fun n hn => ⟨n, c, Nat.le_refl n, hc, hn⟩

theorem Leads.of_not_halts {M : Machine Γ Λ} {c : Cfg Γ Λ} (P : Cfg Γ Λ → Prop)
    (h_nonhalt : ∀ n, ¬ HaltsIn M c n) : Leads M c P :=
  fun n hn => False.elim (h_nonhalt n hn)

theorem Advances.of_not_halts {M : Machine Γ Λ} {c : Cfg Γ Λ} (P : Cfg Γ Λ → Prop)
    (h_nonhalt : ∀ n, ¬ HaltsIn M c n) : Advances M c P :=
  fun n hn => False.elim (h_nonhalt n hn)

theorem Leads.of_stepStar {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {P : Cfg Γ Λ → Prop}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : P c₂) : Leads M c₁ P := by
  intro n hn
  rcases haltsIn_reduce_stepStar h₁ hn with ⟨m, hmn, hm⟩
  exact ⟨m, c₂, hmn, h₂, hm⟩

theorem Advances.of_stepPlus {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {P : Cfg Γ Λ → Prop}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : P c₂) : Advances M c₁ P := by
  intro n hn
  rcases haltsIn_reduce_stepPlus h₁ hn with ⟨m, hmn, hm⟩
  exact ⟨m, c₂, hmn, h₂, hm⟩

theorem Leads.mono {M : Machine Γ Λ} {c : Cfg Γ Λ} {P Q : Cfg Γ Λ → Prop}
    (h₁ : Leads M c P) (h₂ : ∀ d, P d → Q d) : Leads M c Q := by
  intro n hn
  rcases h₁ n hn with ⟨m, d, hmn, hP, hm⟩
  exact ⟨m, d, hmn, h₂ d hP, hm⟩

theorem Advances.mono {M : Machine Γ Λ} {c : Cfg Γ Λ} {P Q : Cfg Γ Λ → Prop}
    (h₁ : Advances M c P) (h₂ : ∀ d, P d → Q d) : Advances M c Q := by
  intro n hn
  rcases h₁ n hn with ⟨m, d, hmn, hP, hm⟩
  exact ⟨m, d, hmn, h₂ d hP, hm⟩

theorem Advances.to_leads {M : Machine Γ Λ} {c : Cfg Γ Λ} {P : Cfg Γ Λ → Prop}
    (h : Advances M c P) : Leads M c P := by
  intro n hn
  rcases h n hn with ⟨m, d, hmn, hP, hm⟩
  exact ⟨m, d, Nat.le_of_lt hmn, hP, hm⟩

theorem Leads.trans {M : Machine Γ Λ} {c : Cfg Γ Λ} {P Q : Cfg Γ Λ → Prop}
    (h₁ : Leads M c P) (h₂ : ∀ d, P d → Leads M d Q) : Leads M c Q := by
  intro n hn
  rcases h₁ n hn with ⟨m, d, hmn, hP, hm⟩
  rcases h₂ d hP m hm with ⟨k, e, hkm, hQ, hk⟩
  exact ⟨k, e, Nat.le_trans hkm hmn, hQ, hk⟩

theorem Advances.trans {M : Machine Γ Λ} {c : Cfg Γ Λ} {P Q : Cfg Γ Λ → Prop}
    (h₁ : Advances M c P) (h₂ : ∀ d, P d → Leads M d Q) : Advances M c Q := by
  intro n hn
  rcases h₁ n hn with ⟨m, d, hmn, hP, hm⟩
  rcases h₂ d hP m hm with ⟨k, e, hkm, hQ, hk⟩
  exact ⟨k, e, Nat.lt_of_le_of_lt hkm hmn, hQ, hk⟩

theorem Leads.trans_advances {M : Machine Γ Λ} {c : Cfg Γ Λ} {P Q : Cfg Γ Λ → Prop}
    (h₁ : Leads M c P) (h₂ : ∀ d, P d → Advances M d Q) : Advances M c Q := by
  intro n hn
  rcases h₁ n hn with ⟨m, d, hmn, hP, hm⟩
  rcases h₂ d hP m hm with ⟨k, e, hkm, hQ, hk⟩
  exact ⟨k, e, Nat.lt_of_lt_of_le hkm hmn, hQ, hk⟩

theorem Leads.of_stepStar_leads {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {P : Cfg Γ Λ → Prop}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : Leads M c₂ P) : Leads M c₁ P :=
  (Leads.of_stepStar h₁ rfl).trans (fun _ h_eq => h_eq ▸ h₂)

theorem Advances.of_stepPlus_leads {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {P : Cfg Γ Λ → Prop}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : Leads M c₂ P) : Advances M c₁ P :=
  (Advances.of_stepPlus h₁ rfl).trans (fun _ h_eq => h_eq ▸ h₂)

theorem Leads.of_stepPlus_leads {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {P : Cfg Γ Λ → Prop}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : Leads M c₂ P) : Leads M c₁ P :=
  (Advances.of_stepPlus_leads h₁ h₂).to_leads

theorem Advances.of_stepStar_advances {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {P : Cfg Γ Λ → Prop}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : Advances M c₂ P) : Advances M c₁ P :=
  (Leads.of_stepStar h₁ rfl).trans_advances (fun _ h_eq => h_eq ▸ h₂)

theorem Leads.or_left {M : Machine Γ Λ} {c : Cfg Γ Λ} {P Q : Cfg Γ Λ → Prop}
    (h : Leads M c P) : Leads M c (fun d => P d ∨ Q d) :=
  h.mono (fun _ hP => Or.inl hP)

theorem Leads.or_right {M : Machine Γ Λ} {c : Cfg Γ Λ} {P Q : Cfg Γ Λ → Prop}
    (h : Leads M c Q) : Leads M c (fun d => P d ∨ Q d) :=
  h.mono (fun _ hQ => Or.inr hQ)

theorem Leads.or_elim {M : Machine Γ Λ} {c : Cfg Γ Λ} {P Q R : Cfg Γ Λ → Prop}
    (h : Leads M c (fun d => P d ∨ Q d))
    (hP : ∀ d, P d → Leads M d R)
    (hQ : ∀ d, Q d → Leads M d R) : Leads M c R :=
  h.trans (fun d hd => hd.elim (hP d) (hQ d))

theorem Advances.or_elim {M : Machine Γ Λ} {c : Cfg Γ Λ} {P Q R : Cfg Γ Λ → Prop}
    (h : Advances M c (fun d => P d ∨ Q d))
    (hP : ∀ d, P d → Leads M d R)
    (hQ : ∀ d, Q d → Leads M d R) : Advances M c R :=
  h.trans (fun d hd => hd.elim (hP d) (hQ d))

/-- Well-foundedness of halt-budget descent: if every configuration satisfying `P` advances to
    `P` with strictly smaller remaining halt budget, then no `P`-configuration can halt in `n` steps. -/
theorem not_haltsIn_of_advances {M : Machine Γ Λ} {P : Cfg Γ Λ → Prop}
    (h_adv : ∀ c, P c → Advances M c P) :
    ∀ (n : ℕ) (c : Cfg Γ Λ), P c → ¬ HaltsIn M c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro c hc hn
    rcases h_adv c hc n hn with ⟨m, d, hmn, hd, hm⟩
    exact ih m hmn d hd hm

/-- Constructive (excluded-middle-free) non-halting theorem from decreasing halt budget
    (`decreasing_halt_budget` in `Queue_v1.v`): if `Leads M (init []) P` and every `P`
    configuration `Advances` to `P`, then `IsDoesNotHalt M`. -/
theorem does_not_halt_of_leads_advances {M : Machine Γ Λ} {P : Cfg Γ Λ → Prop}
    (h_init : Leads M (init []) P)
    (h_adv : ∀ c, P c → Advances M c P) :
    IsDoesNotHalt M := by
  intro cfg ⟨n, hn⟩
  cases h_step : step M cfg with
  | some _ => rfl
  | none =>
    have h_halt_init : HaltsIn M (init []) n := ⟨cfg, hn, by simp [h_step]⟩
    rcases h_init n h_halt_init with ⟨m, d, _, hPd, h_halt_d⟩
    exact False.elim (not_haltsIn_of_advances h_adv m d hPd h_halt_d)

/-- Specialization of `does_not_halt_of_leads_advances` when `(init []) [M]⊢* c₀` and `P c₀`. -/
theorem does_not_halt_of_advances {M : Machine Γ Λ} {P : Cfg Γ Λ → Prop} {c₀ : Cfg Γ Λ}
    (h_init : (init []) [M]⊢* c₀) (h₀ : P c₀)
    (h_adv : ∀ c, P c → Advances M c P) :
    IsDoesNotHalt M :=
  does_not_halt_of_leads_advances (Leads.of_stepStar h_init h₀) h_adv

end HaltBudgetCalculus

-- ============================================================================
-- 2. Conjugate-Shift Excursion Word Algebra (`ConjWord`, `commute_pow`)
-- ============================================================================

section ConjugateShiftAlgebra

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Conjugate-shift excursion triple (`conj_word` in `ChaoticFractalOthers_v1.v`):
    1. `word_conj`: `w ++ u = u ++ x` (pushing `w` on the left of `u` equals shifting `u` past `x`),
    2. `scan_fwd`: scanning right in state `qF` across `x` leaves `y.reverse` on the left tape, and
    3. `scan_bwd`: scanning left in state `qB` across `y.reverse` leaves `w` on the right tape. -/
structure ConjWord (M : Machine Γ Λ) (qF qB : Λ) (u w x y : List Γ) : Prop where
  word_conj : w ++ u = u ++ x
  scan_fwd : ∀ (l r : ListBlank Γ),
    (l {{qF}}> (x +> r)) [M]⊢* ((y.reverse +> l) {{qF}}> r)
  scan_bwd : ∀ (l r : ListBlank Γ),
    ((y.reverse +> l) <{{qB}} r) [M]⊢* (l <{{qB}} (w +> r))

theorem ConjWord.nil (M : Machine Γ Λ) (qF qB : Λ) (u : List Γ) :
    ConjWord M qF qB u [] [] [] where
  word_conj := by simp
  scan_fwd _ _ := stepStar_refl M _
  scan_bwd _ _ := stepStar_refl M _

theorem ConjWord.append {M : Machine Γ Λ} {qF qB : Λ} {u w₁ x₁ y₁ w₂ x₂ y₂ : List Γ}
    (h₁ : ConjWord M qF qB u w₁ x₁ y₁) (h₂ : ConjWord M qF qB u w₂ x₂ y₂) :
    ConjWord M qF qB u (w₁ ++ w₂) (x₁ ++ x₂) (y₁ ++ y₂) where
  word_conj := by
    rw [List.append_assoc, h₂.word_conj, ← List.append_assoc, h₁.word_conj, List.append_assoc]
  scan_fwd l r := by
    rw [listblank_append_assoc, List.reverse_append, listblank_append_assoc]
    exact stepStar_trans (h₁.scan_fwd l (x₂ +> r)) (h₂.scan_fwd (y₁.reverse +> l) r)
  scan_bwd l r := by
    rw [List.reverse_append, listblank_append_assoc, listblank_append_assoc]
    exact stepStar_trans (h₂.scan_bwd (y₁.reverse +> l) r) (h₁.scan_bwd l (w₂ +> r))

theorem ConjWord.pow {M : Machine Γ Λ} {qF qB : Λ} {u w x y : List Γ}
    (h : ConjWord M qF qB u w x y) :
    ∀ (n : ℕ), ConjWord M qF qB u (w ^ n) (x ^ n) (y ^ n)
  | 0 => ConjWord.nil M qF qB u
  | n + 1 => h.append (h.pow n)

/-- Full right-scan + turnaround + left-scan excursion across `x` followed by `u`:
    if `(l {{qF}}> (u +> r₀)) [M]⊢* (l <{{qB}} (u +> r₁))`, then
    `(l {{qF}}> (x +> (u +> r₀))) [M]⊢* (l <{{qB}} (u +> (x +> r₁)))`. -/
theorem ConjWord.excursion {M : Machine Γ Λ} {qF qB : Λ} {u w x y : List Γ}
    (h : ConjWord M qF qB u w x y)
    {r₀ r₁ : ListBlank Γ}
    (h_turn : ∀ l : ListBlank Γ, (l {{qF}}> (u +> r₀)) [M]⊢* (l <{{qB}} (u +> r₁)))
    (l : ListBlank Γ) :
    (l {{qF}}> (x +> (u +> r₀))) [M]⊢* (l <{{qB}} (u +> (x +> r₁))) := by
  have h₁ := h.scan_fwd l (u +> r₀)
  have h₂ := h_turn (y.reverse +> l)
  have h₃ := h.scan_bwd l (u +> r₁)
  have h_eq : w +> (u +> r₁) = u +> (x +> r₁) := by
    rw [← listblank_append_assoc, h.word_conj, listblank_append_assoc]
  rw [h_eq] at h₃
  exact stepStar_trans h₁ (stepStar_trans h₂ h₃)

/-- `ReachesPlus` version of `ConjWord.excursion` when the turnaround takes at least 1 step. -/
theorem ConjWord.excursion_plus {M : Machine Γ Λ} {qF qB : Λ} {u w x y : List Γ}
    (h : ConjWord M qF qB u w x y)
    {r₀ r₁ : ListBlank Γ}
    (h_turn : ∀ l : ListBlank Γ, (l {{qF}}> (u +> r₀)) [M]⊢⁺ (l <{{qB}} (u +> r₁)))
    (l : ListBlank Γ) :
    (l {{qF}}> (x +> (u +> r₀))) [M]⊢⁺ (l <{{qB}} (u +> (x +> r₁))) := by
  have h₁ := h.scan_fwd l (u +> r₀)
  have h₂ := h_turn (y.reverse +> l)
  have h₃ := h.scan_bwd l (u +> r₁)
  have h_eq : w +> (u +> r₁) = u +> (x +> r₁) := by
    rw [← listblank_append_assoc, h.word_conj, listblank_append_assoc]
  rw [h_eq] at h₃
  exact stepPlus_stepStar_stepPlus (stepStar_stepPlus_stepPlus h₁ h₂) h₃

omit [Inhabited Γ] in
private theorem list_pow_add_local (l : List Γ) (m n : ℕ) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp [pow_zero_list]
  | succ m ih =>
    rw [Nat.succ_add, pow_succ_list, pow_succ_list, ih, List.append_assoc]

omit [Inhabited Γ] in
/-- Periodic RLE commutation lemma (`commute_pow` in `ChaoticBell1Halt.v`):
    if `x ++ v ^ a = w ^ b ++ x`, then `x ++ v ^ (a * k) = w ^ (b * k) ++ x` for all `k`. -/
theorem commute_pow {x v w : List Γ} {a b : ℕ}
    (h : x ++ v ^ a = w ^ b ++ x) :
    ∀ (k : ℕ), x ++ v ^ (a * k) = w ^ (b * k) ++ x
  | 0 => by simp [pow_zero_list]
  | k + 1 => by
    rw [Nat.mul_succ, Nat.mul_succ, list_pow_add_local, list_pow_add_local,
      ← List.append_assoc, commute_pow h k, List.append_assoc, h, ← List.append_assoc]

omit [Inhabited Γ] in
theorem commute_pow_left {x v w : List Γ} {a b : ℕ}
    (h : x ++ v ^ a = w ^ b ++ x) (k : ℕ) :
    x ++ v ^ (k * a) = w ^ (k * b) ++ x := by
  rw [Nat.mul_comm k a, Nat.mul_comm k b]
  exact commute_pow h k

omit [Inhabited Γ] in
theorem commute_pow_single {x v w : List Γ}
    (h : x ++ v = w ++ x) :
    ∀ (k : ℕ), x ++ v ^ k = w ^ k ++ x
  | 0 => by simp [pow_zero_list]
  | k + 1 => by
    rw [pow_succ_list, pow_succ_list, ← List.append_assoc, h, List.append_assoc,
      commute_pow_single h k, ← List.append_assoc]

/-- Half-tape (`ListBlank`) corollary of `commute_pow`. -/
theorem append_commute_pow {x v w : List Γ} {a b : ℕ}
    (h : x ++ v ^ a = w ^ b ++ x) (k : ℕ) (s : ListBlank Γ) :
    x +> (v ^ (a * k) +> s) = w ^ (b * k) +> (x +> s) := by
  rw [← listblank_append_assoc, commute_pow h k, listblank_append_assoc]

/-- Half-tape (`ListBlank`) corollary of `commute_pow_single`. -/
theorem append_commute_pow_single {x v w : List Γ}
    (h : x ++ v = w ++ x) (k : ℕ) (s : ListBlank Γ) :
    x +> (v ^ k +> s) = w ^ k +> (x +> s) := by
  rw [← listblank_append_assoc, commute_pow_single h k, listblank_append_assoc]

end ConjugateShiftAlgebra

-- ============================================================================
-- 3. Dependent Division-Modulo & Subtraction Views (`DivMod2`..`DivMod6`, `SubView`)
-- ============================================================================

section DependentArithmeticViews

/-- Dependent modulo-2 view (`DivMod2` in `DivModCases.v`). -/
inductive DivMod2 (n : ℕ) : Type where
  | eq0 (a : ℕ) (h : n = a * 2) : DivMod2 n
  | eq1 (a : ℕ) (h : n = 1 + a * 2) : DivMod2 n

def mod2 (n : ℕ) : DivMod2 n :=
  if h0 : n % 2 = 0 then
    .eq0 (n / 2) (by omega)
  else
    .eq1 (n / 2) (by omega)

/-- Dependent modulo-3 view (`DivMod3` in `DivModCases.v`). -/
inductive DivMod3 (n : ℕ) : Type where
  | eq0 (a : ℕ) (h : n = a * 3) : DivMod3 n
  | eq1 (a : ℕ) (h : n = 1 + a * 3) : DivMod3 n
  | eq2 (a : ℕ) (h : n = 2 + a * 3) : DivMod3 n

def mod3 (n : ℕ) : DivMod3 n :=
  if h0 : n % 3 = 0 then
    .eq0 (n / 3) (by omega)
  else if h1 : n % 3 = 1 then
    .eq1 (n / 3) (by omega)
  else
    .eq2 (n / 3) (by omega)

/-- Dependent modulo-4 view (`DivMod4` in `DivModCases.v`). -/
inductive DivMod4 (n : ℕ) : Type where
  | eq0 (a : ℕ) (h : n = a * 4) : DivMod4 n
  | eq1 (a : ℕ) (h : n = 1 + a * 4) : DivMod4 n
  | eq2 (a : ℕ) (h : n = 2 + a * 4) : DivMod4 n
  | eq3 (a : ℕ) (h : n = 3 + a * 4) : DivMod4 n

def mod4 (n : ℕ) : DivMod4 n :=
  if h0 : n % 4 = 0 then
    .eq0 (n / 4) (by omega)
  else if h1 : n % 4 = 1 then
    .eq1 (n / 4) (by omega)
  else if h2 : n % 4 = 2 then
    .eq2 (n / 4) (by omega)
  else
    .eq3 (n / 4) (by omega)

/-- Dependent modulo-5 view (`DivMod5` in `DivModCases.v`). -/
inductive DivMod5 (n : ℕ) : Type where
  | eq0 (a : ℕ) (h : n = a * 5) : DivMod5 n
  | eq1 (a : ℕ) (h : n = 1 + a * 5) : DivMod5 n
  | eq2 (a : ℕ) (h : n = 2 + a * 5) : DivMod5 n
  | eq3 (a : ℕ) (h : n = 3 + a * 5) : DivMod5 n
  | eq4 (a : ℕ) (h : n = 4 + a * 5) : DivMod5 n

def mod5 (n : ℕ) : DivMod5 n :=
  if h0 : n % 5 = 0 then
    .eq0 (n / 5) (by omega)
  else if h1 : n % 5 = 1 then
    .eq1 (n / 5) (by omega)
  else if h2 : n % 5 = 2 then
    .eq2 (n / 5) (by omega)
  else if h3 : n % 5 = 3 then
    .eq3 (n / 5) (by omega)
  else
    .eq4 (n / 5) (by omega)

/-- Dependent modulo-6 view (`DivMod6` in `DivModCases.v`). -/
inductive DivMod6 (n : ℕ) : Type where
  | eq0 (a : ℕ) (h : n = a * 6) : DivMod6 n
  | eq1 (a : ℕ) (h : n = 1 + a * 6) : DivMod6 n
  | eq2 (a : ℕ) (h : n = 2 + a * 6) : DivMod6 n
  | eq3 (a : ℕ) (h : n = 3 + a * 6) : DivMod6 n
  | eq4 (a : ℕ) (h : n = 4 + a * 6) : DivMod6 n
  | eq5 (a : ℕ) (h : n = 5 + a * 6) : DivMod6 n

def mod6 (n : ℕ) : DivMod6 n :=
  if h0 : n % 6 = 0 then
    .eq0 (n / 6) (by omega)
  else if h1 : n % 6 = 1 then
    .eq1 (n / 6) (by omega)
  else if h2 : n % 6 = 2 then
    .eq2 (n / 6) (by omega)
  else if h3 : n % 6 = 3 then
    .eq3 (n / 6) (by omega)
  else if h4 : n % 6 = 4 then
    .eq4 (n / 6) (by omega)
  else
    .eq5 (n / 6) (by omega)

/-- Dependent subtraction view (`Sub` in `DivModCases.v`): splits `(a, b)` into `a = b + c` vs `a < b`. -/
inductive SubView (a b : ℕ) : Type where
  | ge (c : ℕ) (h : a = b + c) : SubView a b
  | lt (h : a < b) : SubView a b

def subView (a b : ℕ) : SubView a b :=
  if h : a < b then
    .lt h
  else
    .ge (a - b) (by omega)

end DependentArithmeticViews

-- ============================================================================
-- 4. Constructive Halting & Non-Halting Equivalence via Abstract Models
-- ============================================================================

section ConstructiveModelEquivalence

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

private theorem collatzHalts_of_next_none {S : Type*} {next : S → Option S} {s : S}
    (h : next s = none) : CollatzHalts next s :=
  ⟨1, by simp [h]⟩

private theorem collatzHalts_of_next_some {S : Type*} {next : S → Option S} {s s' : S}
    (h : next s = some s') (h' : CollatzHalts next s') : CollatzHalts next s := by
  rcases h' with ⟨n, hn⟩
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply]
  simpa [h] using hn

/-- Constructive (excluded-middle-free) proof that if `encode s` halts in `n` steps under a valid
    acceleration `h`, then the abstract model `next` halts from `s`. -/
theorem IsValidAcceleration.collatzHalts_of_haltsIn {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    (h : IsValidAcceleration M start encode next) :
    ∀ (n : ℕ) (s : S), HaltsIn M (encode s) n → CollatzHalts next s := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hn
    rcases hnext : next s with _ | s'
    · exact collatzHalts_of_next_none hnext
    · rcases haltsIn_reduce_stepPlus (h.step_some s s' hnext) hn with ⟨m, hmn, hm⟩
      exact collatzHalts_of_next_some hnext (ih m hmn s' hm)

private theorem haltsIn_of_collatzHalts {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    (h : IsValidAcceleration M start encode next) {s : S}
    (hs : CollatzHalts next s) : ∃ n, HaltsIn M (encode s) n := by
  rcases hs with ⟨k, hk⟩
  induction k generalizing s with
  | zero => simp at hk
  | succ k ih =>
    rw [Function.iterate_succ_apply] at hk
    rcases hnext : next s with _ | s'
    · rcases h.step_none s hnext with ⟨cfg', ⟨m, hm⟩, hnone⟩
      exact ⟨m, cfg', hm, hnone⟩
    · have hk' : ((Option.bind · next)^[k] (some s')).isNone := by
        simpa [hnext] using hk
      rcases ih hk' with ⟨m, hm⟩
      rcases h.step_some s s' hnext with ⟨d, _, hd⟩
      exact ⟨d + m, haltsIn_of_multiStep hd hm⟩

/-- Constructive (excluded-middle-free) characterization of `IsHalt M` via `CollatzHalts next start`. -/
theorem IsValidAcceleration.isHalt_iff_constructive {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    (h : IsValidAcceleration M start encode next) :
    IsHalt M ↔ CollatzHalts next start := by
  rw [isHalt_iff_exists_haltsIn]
  constructor
  · rintro ⟨n, hn⟩
    rcases haltsIn_reduce_stepStar h.init_reaches hn with ⟨m, _, hm⟩
    exact IsValidAcceleration.collatzHalts_of_haltsIn h m start hm
  · intro hs
    rcases h.init_reaches with ⟨k, hk⟩
    rcases haltsIn_of_collatzHalts h hs with ⟨m, hm⟩
    exact ⟨k + m, haltsIn_of_multiStep hk hm⟩

/-- Constructive (excluded-middle-free) characterization of `IsDoesNotHalt M` via `¬ CollatzHalts next start`. -/
theorem IsValidAcceleration.isDoesNotHalt_iff {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    (h : IsValidAcceleration M start encode next) :
    IsDoesNotHalt M ↔ ¬ CollatzHalts next start := by
  constructor
  · intro h_dnh h_collatz
    rcases (IsValidAcceleration.isHalt_iff_constructive h).mpr h_collatz with ⟨cfg, hreach, hnone⟩
    have hsome := h_dnh cfg hreach
    rw [Option.isNone_iff_eq_none] at hnone
    simp [hnone] at hsome
  · intro h_not_collatz
    refine does_not_halt_of_advances
      (P := fun cfg => ∃ s, cfg = encode s ∧ ¬ CollatzHalts next s)
      h.init_reaches
      ⟨start, rfl, h_not_collatz⟩
      ?_
    rintro _ ⟨s, rfl, hns⟩
    rcases hnext : next s with _ | s'
    · exact False.elim (hns (collatzHalts_of_next_none hnext))
    · refine Advances.of_stepPlus (h.step_some s s' hnext) ⟨s', rfl, ?_⟩
      intro hs'
      exact hns (collatzHalts_of_next_some hnext hs')

/-- Two machines `M₁` and `M₂` (possibly over different tape/state alphabets) that simulate the
    same abstract transition system `(start, next)` have equivalent `IsHalt` behavior
    (`Eqv_WordPairs.v` / `Eqv_v2.v`). -/
theorem IsValidAcceleration.equiv_halt
    {Γ₁ Λ₁ Γ₂ Λ₂ S : Type*} [Inhabited Γ₁] [Inhabited Λ₁] [Inhabited Γ₂] [Inhabited Λ₂]
    {M₁ : Machine Γ₁ Λ₁} {M₂ : Machine Γ₂ Λ₂}
    {start : S} {encode₁ : S → Cfg Γ₁ Λ₁} {encode₂ : S → Cfg Γ₂ Λ₂} {next : S → Option S}
    (h₁ : IsValidAcceleration M₁ start encode₁ next)
    (h₂ : IsValidAcceleration M₂ start encode₂ next) :
    IsHalt M₁ ↔ IsHalt M₂ :=
  (IsValidAcceleration.isHalt_iff_constructive h₁).trans
    (IsValidAcceleration.isHalt_iff_constructive h₂).symm

/-- Two machines `M₁` and `M₂` that simulate the same abstract transition system `(start, next)`
    have equivalent `IsDoesNotHalt` behavior (`Eqv_WordPairs.v` / `Eqv_v2.v`). -/
theorem IsValidAcceleration.equiv_doesNotHalt
    {Γ₁ Λ₁ Γ₂ Λ₂ S : Type*} [Inhabited Γ₁] [Inhabited Λ₁] [Inhabited Γ₂] [Inhabited Λ₂]
    {M₁ : Machine Γ₁ Λ₁} {M₂ : Machine Γ₂ Λ₂}
    {start : S} {encode₁ : S → Cfg Γ₁ Λ₁} {encode₂ : S → Cfg Γ₂ Λ₂} {next : S → Option S}
    (h₁ : IsValidAcceleration M₁ start encode₁ next)
    (h₂ : IsValidAcceleration M₂ start encode₂ next) :
    IsDoesNotHalt M₁ ↔ IsDoesNotHalt M₂ :=
  (IsValidAcceleration.isDoesNotHalt_iff h₁).trans
    (IsValidAcceleration.isDoesNotHalt_iff h₂).symm

end ConstructiveModelEquivalence

end BusyBeaver.Excursion
