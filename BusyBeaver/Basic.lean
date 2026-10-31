/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs
public import BusyBeaver.Counter
import BusyBeaver.CarryCounter
import BusyBeaver.CtlCertificate
import BusyBeaver.Excursion
import BusyBeaver.Longitudinal
import BusyBeaver.WordCalculusD
import BusyBeaver.WordCalculusE
import BusyBeaver.WordCalculusG
import BusyBeaver.WordCalculusI


/-!
# Basic Lemmas for `BusyBeaver` Turing Machines (`BusyBeaver.Basic`)

Foundational lemmas for reasoning about `BusyBeaver.Machine` execution, multi-step reachability
(`multiStep`, `ReachesIn`, `ReachesStar`, `ReachesPlus`), halting/non-halting invariants
(`HaltsFrom`, `NeverHaltsFrom`), finite block repetition (`l ^ n`), and directed-head tape
configurations (`Cfg.headRight`, `Cfg.headLeft`).
-/

@[expose] public section

namespace BusyBeaver

open Turing

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-! ## Multi-Step Execution (`multiStep`) -/

@[simp]
theorem step_none (M : Machine Γ Λ) (T : Tape Γ) :
    step M ⟨none, T⟩ = none :=
  rfl

@[simp]
theorem multiStep_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    multiStep M c 0 = some c :=
  rfl

@[simp]
theorem multiStep_one (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    multiStep M c 1 = step M c :=
  rfl

private theorem iterate_bind_step_none (M : Machine Γ Λ) (n : ℕ) :
    (Option.bind · (step M))^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Option.bind_none, ih]

/-- Split `multiStep` at the first step: `n + 1` steps from `c` is one step from `c` followed by
`n` steps. -/
theorem multiStep_succ (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = (step M c).bind (fun c' => multiStep M c' n) := by
  unfold multiStep
  rw [Function.iterate_succ_apply]
  rcases h : step M c with _ | c'
  · change (Option.bind · (step M))^[n] (step M c) = _
    rw [h, iterate_bind_step_none, Option.bind_none]
  · change (Option.bind · (step M))^[n] (step M c) = _
    rw [h]
    rfl

/-- Split `multiStep` at the last step: `n + 1` steps from `c` is `n` steps from `c` followed by
one step. -/
theorem multiStep_succ' (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = (multiStep M c n).bind (step M) := by
  unfold multiStep
  rw [Function.iterate_succ_apply']

theorem multiStep_of_step {M : Machine Γ Λ} {c c' : Cfg Γ Λ}
    (h : step M c = some c') (n : ℕ) :
    multiStep M c (n + 1) = multiStep M c' n := by
  rw [multiStep_succ, h, Option.bind_some]

theorem multiStep_of_step_eq_none {M : Machine Γ Λ} {c : Cfg Γ Λ}
    (h : step M c = none) (n : ℕ) :
    multiStep M c (n + 1) = none := by
  rw [multiStep_succ, h, Option.bind_none]

/-- Addition law for `multiStep`: `m + n` steps is `m` steps followed by `n` steps. -/
theorem multiStep_add (M : Machine Γ Λ) (c : Cfg Γ Λ) (m n : ℕ) :
    multiStep M c (m + n) = (multiStep M c m).bind (fun c' => multiStep M c' n) := by
  unfold multiStep
  rw [Nat.add_comm m n, Function.iterate_add_apply]
  rcases h : (Option.bind · (step M))^[m] (some c) with _ | c'
  · rw [iterate_bind_step_none, Option.bind_none]
  · rfl

theorem multiStep_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {m n : ℕ}
    (h₁ : multiStep M c₁ m = some c₂) (h₂ : multiStep M c₂ n = some c₃) :
    multiStep M c₁ (m + n) = some c₃ := by
  rw [multiStep_add, h₁, Option.bind_some, h₂]

/-! ## Exact, Reflexive-Transitive, and Positive Reachability -/

@[simp]
theorem ReachesIn.zero (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    ReachesIn M 0 c c :=
  rfl

theorem ReachesIn.single {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : step M c₁ = some c₂) :
    ReachesIn M 1 c₁ c₂ :=
  h

theorem ReachesIn.step_left {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {n : ℕ}
    (h₁ : step M c₁ = some c₂) (h₂ : ReachesIn M n c₂ c₃) :
    ReachesIn M (n + 1) c₁ c₃ := by
  unfold ReachesIn at *
  rw [multiStep_of_step h₁, h₂]

theorem ReachesIn.step_right {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {n : ℕ}
    (h₁ : ReachesIn M n c₁ c₂) (h₂ : step M c₂ = some c₃) :
    ReachesIn M (n + 1) c₁ c₃ := by
  unfold ReachesIn at *
  rw [multiStep_succ', h₁, Option.bind_some, h₂]

theorem ReachesIn.trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {m n : ℕ}
    (h₁ : ReachesIn M m c₁ c₂) (h₂ : ReachesIn M n c₂ c₃) :
    ReachesIn M (m + n) c₁ c₃ :=
  multiStep_trans h₁ h₂

theorem ReachesIn.to_star {M : Machine Γ Λ} {n : ℕ} {c₁ c₂ : Cfg Γ Λ}
    (h : ReachesIn M n c₁ c₂) :
    ReachesStar M c₁ c₂ :=
  ⟨n, h⟩

theorem ReachesIn.to_plus {M : Machine Γ Λ} {n : ℕ} {c₁ c₂ : Cfg Γ Λ}
    (hn : n > 0) (h : ReachesIn M n c₁ c₂) :
    ReachesPlus M c₁ c₂ :=
  ⟨n, hn, h⟩

@[refl, simp]
theorem ReachesStar.refl (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    ReachesStar M c c :=
  ⟨0, rfl⟩

theorem ReachesStar.single {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : step M c₁ = some c₂) :
    ReachesStar M c₁ c₂ :=
  ⟨1, h⟩

theorem ReachesStar.head {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : step M c₁ = some c₂) (h₂ : ReachesStar M c₂ c₃) :
    ReachesStar M c₁ c₃ := by
  obtain ⟨n, hn⟩ := h₂
  exact ⟨n + 1, ReachesIn.step_left h₁ hn⟩

theorem ReachesStar.tail {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : ReachesStar M c₁ c₂) (h₂ : step M c₂ = some c₃) :
    ReachesStar M c₁ c₃ := by
  obtain ⟨n, hn⟩ := h₁
  exact ⟨n + 1, ReachesIn.step_right hn h₂⟩

theorem ReachesStar.trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : ReachesStar M c₁ c₂) (h₂ : ReachesStar M c₂ c₃) :
    ReachesStar M c₁ c₃ := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  exact ⟨m + n, multiStep_trans hm hn⟩

theorem ReachesPlus.single {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : step M c₁ = some c₂) :
    ReachesPlus M c₁ c₂ :=
  ⟨1, Nat.one_pos, h⟩

theorem ReachesPlus.to_star {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : ReachesPlus M c₁ c₂) :
    ReachesStar M c₁ c₂ := by
  obtain ⟨n, _, hn⟩ := h
  exact ⟨n, hn⟩

theorem ReachesPlus.head {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : step M c₁ = some c₂) (h₂ : ReachesStar M c₂ c₃) :
    ReachesPlus M c₁ c₃ := by
  obtain ⟨n, hn⟩ := h₂
  exact ⟨n + 1, Nat.succ_pos n, ReachesIn.step_left h₁ hn⟩

theorem ReachesPlus.tail {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : ReachesStar M c₁ c₂) (h₂ : step M c₂ = some c₃) :
    ReachesPlus M c₁ c₃ := by
  obtain ⟨n, hn⟩ := h₁
  exact ⟨n + 1, Nat.succ_pos n, ReachesIn.step_right hn h₂⟩

theorem ReachesPlus.trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : ReachesPlus M c₁ c₂) (h₂ : ReachesPlus M c₂ c₃) :
    ReachesPlus M c₁ c₃ := by
  obtain ⟨m, hm_pos, hm⟩ := h₁
  obtain ⟨n, hn_pos, hn⟩ := h₂
  exact ⟨m + n, Nat.add_pos_left hm_pos n, multiStep_trans hm hn⟩

theorem ReachesPlus.trans_star {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : ReachesPlus M c₁ c₂) (h₂ : ReachesStar M c₂ c₃) :
    ReachesPlus M c₁ c₃ := by
  obtain ⟨m, hm_pos, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  exact ⟨m + n, Nat.add_pos_left hm_pos n, multiStep_trans hm hn⟩

theorem ReachesStar.trans_plus {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : ReachesStar M c₁ c₂) (h₂ : ReachesPlus M c₂ c₃) :
    ReachesPlus M c₁ c₃ := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn_pos, hn⟩ := h₂
  exact ⟨m + n, Nat.add_pos_right m hn_pos, multiStep_trans hm hn⟩

theorem ReachesPlus.of_star_ne {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : ReachesStar M c₁ c₂) (hne : c₁ ≠ c₂) :
    ReachesPlus M c₁ c₂ := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | n
  · simp only [multiStep_zero, Option.some.injEq] at hn
    exact absurd hn hne
  · exact ⟨n + 1, Nat.succ_pos n, hn⟩

instance (M : Machine Γ Λ) : Trans (ReachesStar M) (ReachesStar M) (ReachesStar M) :=
  ⟨ReachesStar.trans⟩

instance (M : Machine Γ Λ) : Trans (ReachesPlus M) (ReachesPlus M) (ReachesPlus M) :=
  ⟨ReachesPlus.trans⟩

instance (M : Machine Γ Λ) : Trans (ReachesPlus M) (ReachesStar M) (ReachesPlus M) :=
  ⟨ReachesPlus.trans_star⟩

instance (M : Machine Γ Λ) : Trans (ReachesStar M) (ReachesPlus M) (ReachesPlus M) :=
  ⟨ReachesStar.trans_plus⟩

/-! ## Halting and Non-Halting Invariants -/

/-- `M` eventually reaches a halting configuration starting from `c`. -/
def HaltsFrom (M : Machine Γ Λ) (c : Cfg Γ Λ) : Prop :=
  ∃ cfg : Cfg Γ Λ, ReachesStar M c cfg ∧ (step M cfg).isNone

/-- Every configuration reachable by `M` from `c` has a well-defined successor. -/
def NeverHaltsFrom (M : Machine Γ Λ) (c : Cfg Γ Λ) : Prop :=
  ∀ cfg : Cfg Γ Λ, ReachesStar M c cfg → (step M cfg).isSome

@[simp]
theorem isHalt_iff_haltsFrom_init (M : Machine Γ Λ) :
    IsHalt M ↔ HaltsFrom M (init []) :=
  Iff.rfl

@[simp]
theorem isNotHalt_iff_neverHaltsFrom_init (M : Machine Γ Λ) :
    IsNotHalt M ↔ NeverHaltsFrom M (init []) :=
  Iff.rfl

theorem HaltsFrom.of_reachesStar {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h₁ : ReachesStar M c₁ c₂) (h₂ : HaltsFrom M c₂) :
    HaltsFrom M c₁ := by
  obtain ⟨cfg, hreach, hnone⟩ := h₂
  exact ⟨cfg, h₁.trans hreach, hnone⟩

theorem NeverHaltsFrom.of_reachesStar {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h₁ : ReachesStar M c₁ c₂) (h₂ : NeverHaltsFrom M c₁) :
    NeverHaltsFrom M c₂ := by
  intro cfg hreach
  exact h₂ cfg (h₁.trans hreach)

theorem multiStep_eq_none_of_isNone {M : Machine Γ Λ} {c cfg : Cfg Γ Λ} {k d : ℕ}
    (hk : multiStep M c k = some cfg) (hnone : (step M cfg).isNone) (hd : d > 0) :
    multiStep M c (k + d) = none := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hd
  rw [multiStep_add, hk, Option.bind_some, multiStep_of_step_eq_none]
  exact Option.isNone_iff_eq_none.mp hnone

/-- If `P` is a configuration invariant starting at `c₀` such that every `P`-configuration steps
in `ReachesPlus` (`n > 0` steps) to another `P`-configuration, then `M` never halts from `c₀`. -/
theorem NeverHaltsFrom.of_reachesPlus_invariant {M : Machine Γ Λ} {P : Cfg Γ Λ → Prop}
    (hstep : ∀ c, P c → ∃ c', ReachesPlus M c c' ∧ P c') {c₀ : Cfg Γ Λ} (h₀ : P c₀) :
    NeverHaltsFrom M c₀ := by
  have h_unbounded : ∀ k : ℕ, ∃ N ≥ k, ∃ c', multiStep M c₀ N = some c' ∧ P c' := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.le_refl 0, c₀, rfl, h₀⟩
    | succ k ih =>
      obtain ⟨N, hNk, c₁, hms₁, hP₁⟩ := ih
      obtain ⟨c₂, ⟨m, hm_pos, hms₂⟩, hP₂⟩ := hstep c₁ hP₁
      refine ⟨N + m, by omega, c₂, multiStep_trans hms₁ hms₂, hP₂⟩
  intro cfg ⟨k, hk⟩
  rcases hstep_cfg : step M cfg with _ | _
  · obtain ⟨N, hNk, c', hmsN, _⟩ := h_unbounded (k + 1)
    have hnone : (step M cfg).isNone := by simp [hstep_cfg]
    have hnoneN : multiStep M c₀ N = none := by
      have hsplit : N = k + (N - k) := by omega
      rw [hsplit]
      exact multiStep_eq_none_of_isNone hk hnone (by omega)
    rw [hnoneN] at hmsN
    cases hmsN
  · rfl

/-- If `M` reaches an invariant `P` from `init []` that is closed under `ReachesPlus`, then
`IsNotHalt M`. -/
theorem IsNotHalt.of_reachesPlus_invariant {M : Machine Γ Λ} {P : Cfg Γ Λ → Prop}
    {c₀ : Cfg Γ Λ} (hinit : ReachesStar M (init []) c₀) (h₀ : P c₀)
    (hstep : ∀ c, P c → ∃ c', ReachesPlus M c c' ∧ P c') :
    IsNotHalt M := by
  have h_never_c₀ := NeverHaltsFrom.of_reachesPlus_invariant hstep h₀
  obtain ⟨k₀, hk₀⟩ := hinit
  intro cfg ⟨k, hk⟩
  rcases Nat.lt_or_ge k k₀ with hlt | hge
  · rcases hstep_cfg : step M cfg with _ | _
    · have hnone : (step M cfg).isNone := by simp [hstep_cfg]
      have hnone_k₀ : multiStep M (init []) k₀ = none := by
        have hsplit : k₀ = k + (k₀ - k) := by omega
        rw [hsplit]
        exact multiStep_eq_none_of_isNone hk hnone (by omega)
      rw [hnone_k₀] at hk₀
      cases hk₀
    · rfl
  · have hsplit : k = k₀ + (k - k₀) := by omega
    rw [hsplit, multiStep_add, hk₀, Option.bind_some] at hk
    exact h_never_c₀ cfg ⟨k - k₀, hk⟩

/-! ## Finite Block Repetition (`l ^ n`) -/

section ListPow

omit [Inhabited Γ]

@[simp]
theorem list_pow_zero (l : List Γ) : l ^ (0 : ℕ) = [] :=
  rfl

@[simp]
theorem list_pow_one (l : List Γ) : l ^ (1 : ℕ) = l := by
  simp [HPow.hPow]

theorem list_pow_succ (l : List Γ) (n : ℕ) : l ^ (n + 1) = l ++ l ^ n :=
  rfl

theorem list_pow_add (l : List Γ) (m n : ℕ) : l ^ (m + n) = l ^ m ++ l ^ n := by
  change (List.replicate (m + n) l).flatten =
    (List.replicate m l).flatten ++ (List.replicate n l).flatten
  rw [List.replicate_add, List.flatten_append]

theorem list_pow_succ' (l : List Γ) (n : ℕ) : l ^ (n + 1) = l ^ n ++ l := by
  rw [list_pow_add, list_pow_one]

theorem list_pow_add_comm (l : List Γ) (m n : ℕ) : l ^ m ++ l ^ n = l ^ n ++ l ^ m := by
  rw [← list_pow_add, ← list_pow_add, Nat.add_comm]

@[simp]
theorem nil_pow (n : ℕ) : ([] : List Γ) ^ n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [list_pow_succ, List.nil_append, ih]

theorem singleton_pow (a : Γ) (n : ℕ) : ([a] : List Γ) ^ n = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [list_pow_succ, List.singleton_append, ih, List.replicate_succ]

theorem list_pow_mul (l : List Γ) (m n : ℕ) : l ^ (m * n) = (l ^ m) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, list_pow_add, ih, list_pow_succ']

theorem pair_pow_eq_singleton_pow_two_mul (a : Γ) (k : ℕ) :
    ([a, a] : List Γ) ^ k = ([a] : List Γ) ^ (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, list_pow_add, ih, list_pow_add]
    rfl

theorem one_pow_two_mul (k : ℕ) :
    ([1, 1] : List (Fin 2)) ^ k = ([1] : List (Fin 2)) ^ (2 * k) :=
  pair_pow_eq_singleton_pow_two_mul 1 k

theorem nat_even_or_odd_two_mul (n : ℕ) :
    (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ n ih =>
    rcases ih with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
    · exact Or.inl ⟨k + 1, by omega⟩

end ListPow

/-! ## Half-Tape (`ListBlank`) & Directed-Head (`Cfg.headRight` / `Cfg.headLeft`) Lemmas -/

@[simp]
theorem ListBlank.mk_nil : ListBlank.mk ([] : List Γ) = default :=
  rfl

@[simp]
theorem ListBlank.head_default : (default : ListBlank Γ).head = default :=
  rfl

@[simp]
theorem ListBlank.head_default_fin {n : ℕ} [NeZero n] :
    (default : ListBlank (Fin n)).head = 0 :=
  rfl

@[simp]
theorem ListBlank.tail_default : (default : ListBlank Γ).tail = default :=
  Quotient.sound' (Or.inl ⟨0, rfl⟩)

@[simp]
theorem ListBlank.cons_default_default :
    ListBlank.cons (default : Γ) (default : ListBlank Γ) = default := by
  simpa using ListBlank.cons_head_tail (default : ListBlank Γ)

@[simp]
theorem ListBlank.cons_zero_default {n : ℕ} [NeZero n] :
    ListBlank.cons (0 : Fin n) (default : ListBlank (Fin n)) = default :=
  ListBlank.cons_default_default

theorem ListBlank.default_eq_append_default :
    (default : ListBlank Γ) = ListBlank.append [default] default := by
  simp

theorem ListBlank.default_eq_append_zero {n : ℕ} [NeZero n] :
    (default : ListBlank (Fin n)) = ListBlank.append [0] default := by
  simp

@[simp]
theorem ListBlank.append_nil (L : ListBlank Γ) :
    ListBlank.append ([] : List Γ) L = L :=
  rfl

@[simp]
theorem ListBlank.append_cons (a : Γ) (l : List Γ) (L : ListBlank Γ) :
    ListBlank.append (a :: l) L = ListBlank.cons a (ListBlank.append l L) :=
  rfl

theorem ListBlank.append_append (s : ListBlank Γ) (l₁ l₂ : List Γ) :
    ListBlank.append l₂ (ListBlank.append l₁ s) = ListBlank.append (l₂ ++ l₁) s :=
  (ListBlank.append_assoc l₂ l₁ s).symm

theorem ListBlank.append_comm_of_comm {l₁ l₂ : List Γ} (h : l₁ ++ l₂ = l₂ ++ l₁)
    (s : ListBlank Γ) :
    ListBlank.append l₂ (ListBlank.append l₁ s) = ListBlank.append l₁ (ListBlank.append l₂ s) := by
  rw [ListBlank.append_append, ← h, ← ListBlank.append_append]

theorem ListBlank.append_pow_comm (u : List Γ) (k : ℕ) (s : ListBlank Γ) :
    ListBlank.append (u ^ k) (ListBlank.append u s) =
      ListBlank.append u (ListBlank.append (u ^ k) s) := by
  apply ListBlank.append_comm_of_comm
  rw [← list_pow_succ, ← list_pow_succ']

theorem swap_single_pair_pow (a : Γ) (k : ℕ) (s : ListBlank Γ) :
    ListBlank.append (([a, a] : List Γ) ^ k) (ListBlank.append [a] s) =
      ListBlank.append [a] (ListBlank.append (([a, a] : List Γ) ^ k) s) := by
  rw [pair_pow_eq_singleton_pow_two_mul, ListBlank.append_pow_comm]

theorem swap_1_11_pow (k : ℕ) (s : ListBlank (Fin 2)) :
    ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] s) =
      ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) s) :=
  swap_single_pair_pow 1 k s

theorem ListBlank.append_pow_succ (l : List Γ) (n : ℕ) (L : ListBlank Γ) :
    ListBlank.append (l ^ (n + 1)) L = ListBlank.append l (ListBlank.append (l ^ n) L) := by
  rw [list_pow_succ, ListBlank.append_assoc]

theorem ListBlank.append_pow_add (l : List Γ) (m n : ℕ) (L : ListBlank Γ) :
    ListBlank.append (l ^ (m + n)) L = ListBlank.append (l ^ m) (ListBlank.append (l ^ n) L) := by
  rw [list_pow_add, ListBlank.append_assoc]

theorem append_10_pow_one (k : ℕ) (s : ListBlank (Fin 2)) :
    ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] s) =
      ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [ListBlank.append_pow_succ, ListBlank.append_pow_succ, ih]
    rfl

theorem append_01_pow_zero (k : ℕ) (s : ListBlank (Fin 2)) :
    ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0] s) =
      ListBlank.append [0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [ListBlank.append_pow_succ, ListBlank.append_pow_succ, ih]
    rfl

theorem append_zero_10_pow_one (k : ℕ) (s : ListBlank (Fin 2)) :
    ListBlank.append [0]
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] s)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] s) := by
  rw [append_10_pow_one]
  change ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) s) = _
  exact (ListBlank.append_pow_comm ([0, 1] : List (Fin 2)) k s).symm

theorem append_zero_10_pow_one_succ (k : ℕ) (s : ListBlank (Fin 2)) :
    ListBlank.append [0]
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] s)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) s := by
  rw [append_10_pow_one, ListBlank.append_pow_succ]
  rfl

theorem init_nil_eq_headRight :
    (init ([] : List Γ) : Cfg Γ Λ) = Cfg.headRight default default default :=
  rfl

theorem init_nil_eq_headLeft :
    (init ([] : List Γ) : Cfg Γ Λ) = Cfg.headLeft default default default := by
  simp [init, Cfg.headLeft, Tape.mk₁, Tape.mk₂, Tape.mk']

omit [Inhabited Λ] in
theorem Cfg.headRight_cons (q : Λ) (a : Γ) (l r : ListBlank Γ) :
    Cfg.headRight q l (ListBlank.cons a r) = Cfg.headLeft q (ListBlank.cons a l) r := by
  simp [Cfg.headRight, Cfg.headLeft]

omit [Inhabited Λ] in
theorem Cfg.headLeft_cons (q : Λ) (a : Γ) (l r : ListBlank Γ) :
    Cfg.headLeft q (ListBlank.cons a l) r = Cfg.headRight q l (ListBlank.cons a r) := by
  simp [Cfg.headRight, Cfg.headLeft]

theorem step_headRight_right {M : Machine Γ Λ} {q q' : Λ} {a b : Γ}
    (hM : M q a = some (some q', Stmt.write b Dir.right)) (l r : ListBlank Γ) :
    step M (Cfg.headRight q l (ListBlank.cons a r)) =
      some (Cfg.headRight q' (ListBlank.cons b l) r) := by
  simp [Cfg.headRight, step, hM, Tape.write, Tape.move]

theorem step_headRight_left {M : Machine Γ Λ} {q q' : Λ} {a b : Γ}
    (hM : M q a = some (some q', Stmt.write b Dir.left)) (l r : ListBlank Γ) :
    step M (Cfg.headRight q l (ListBlank.cons a r)) =
      some (Cfg.headLeft q' l (ListBlank.cons b r)) := by
  simp [Cfg.headRight, Cfg.headLeft, step, hM, Tape.write, Tape.move]

theorem step_headLeft_right {M : Machine Γ Λ} {q q' : Λ} {a b : Γ}
    (hM : M q a = some (some q', Stmt.write b Dir.right)) (l r : ListBlank Γ) :
    step M (Cfg.headLeft q (ListBlank.cons a l) r) =
      some (Cfg.headRight q' (ListBlank.cons b l) r) := by
  simp [Cfg.headRight, Cfg.headLeft, step, hM, Tape.write, Tape.move]

theorem step_headLeft_left {M : Machine Γ Λ} {q q' : Λ} {a b : Γ}
    (hM : M q a = some (some q', Stmt.write b Dir.left)) (l r : ListBlank Γ) :
    step M (Cfg.headLeft q (ListBlank.cons a l) r) =
      some (Cfg.headLeft q' l (ListBlank.cons b r)) := by
  simp [Cfg.headLeft, step, hM, Tape.write, Tape.move]

theorem step_headRight_none {M : Machine Γ Λ} {q : Λ} {a : Γ}
    (hM : M q a = none) (l r : ListBlank Γ) :
    step M (Cfg.headRight q l (ListBlank.cons a r)) = none := by
  simp [Cfg.headRight, step, hM]

theorem step_headLeft_none {M : Machine Γ Λ} {q : Λ} {a : Γ}
    (hM : M q a = none) (l r : ListBlank Γ) :
    step M (Cfg.headLeft q (ListBlank.cons a l) r) = none := by
  simp [Cfg.headLeft, step, hM]

theorem step_headRight_default_right {M : Machine Γ Λ} {q q' : Λ} {b : Γ}
    (hM : M q default = some (some q', Stmt.write b Dir.right)) (l : ListBlank Γ) :
    step M (Cfg.headRight q l default) =
      some (Cfg.headRight q' (ListBlank.cons b l) default) := by
  simpa using step_headRight_right hM l default

theorem step_headRight_default_left {M : Machine Γ Λ} {q q' : Λ} {b : Γ}
    (hM : M q default = some (some q', Stmt.write b Dir.left)) (l : ListBlank Γ) :
    step M (Cfg.headRight q l default) =
      some (Cfg.headLeft q' l (ListBlank.cons b default)) := by
  simpa using step_headRight_left hM l default

theorem step_headLeft_default_right {M : Machine Γ Λ} {q q' : Λ} {b : Γ}
    (hM : M q default = some (some q', Stmt.write b Dir.right)) (r : ListBlank Γ) :
    step M (Cfg.headLeft q default r) =
      some (Cfg.headRight q' (ListBlank.cons b default) r) := by
  simpa using step_headLeft_right hM default r

theorem step_headLeft_default_left {M : Machine Γ Λ} {q q' : Λ} {b : Γ}
    (hM : M q default = some (some q', Stmt.write b Dir.left)) (r : ListBlank Γ) :
    step M (Cfg.headLeft q default r) =
      some (Cfg.headLeft q' default (ListBlank.cons b r)) := by
  simpa using step_headLeft_left hM default r

/-! ## Tape Pattern Evaluation (`evalTapeExpr`, `evalTapePattern`) -/

@[simp]
theorem evalTapeExpr_default (vars : ℕ → ℕ) :
    evalTapeExpr (TapeExpr.default : TapeExpr Γ) vars = default :=
  rfl

@[simp]
theorem evalTapeExpr_sym (a : Γ) (rest : TapeExpr Γ) (vars : ℕ → ℕ) :
    evalTapeExpr (.sym a rest) vars = ListBlank.cons a (evalTapeExpr rest vars) :=
  rfl

@[simp]
theorem evalTapeExpr_rep (blk : List Γ) (v : ℕ) (rest : TapeExpr Γ) (vars : ℕ → ℕ) :
    evalTapeExpr (.rep blk v rest) vars =
      ListBlank.append (blk ^ vars v) (evalTapeExpr rest vars) :=
  rfl

@[simp]
theorem evalTapePattern_some (q : Λ) (l r : TapeExpr Γ) (vars : ℕ → ℕ) :
    evalTapePattern ⟨l, some q, r⟩ vars =
      Cfg.headRight q (evalTapeExpr l vars) (evalTapeExpr r vars) :=
  rfl

/-- Configuration `cfg` advances in `ReachesPlus` either to a member of `ps` or to a halting
configuration of `M`. -/
def StepsToClosed (M : Machine Γ Λ) (ps : TapePatternSet Γ Λ) (cfg : Cfg Γ Λ) : Prop :=
  ∃ cfg', ReachesPlus M cfg cfg' ∧
    (IsInPatternSet ps cfg' ∨ (step M cfg').isNone)

theorem StepsToClosed.of_reachesPlus {M : Machine Γ Λ} {ps : TapePatternSet Γ Λ}
    {c₁ c₂ : Cfg Γ Λ} (h : ReachesPlus M c₁ c₂) (hc₂ : StepsToClosed M ps c₂) :
    StepsToClosed M ps c₁ := by
  obtain ⟨cfg', h', h_end⟩ := hc₂
  exact ⟨cfg', h.trans h', h_end⟩

theorem StepsToClosed.of_reachesStar {M : Machine Γ Λ} {ps : TapePatternSet Γ Λ}
    {c₁ c₂ : Cfg Γ Λ} (h : ReachesStar M c₁ c₂) (hc₂ : StepsToClosed M ps c₂) :
    StepsToClosed M ps c₁ := by
  obtain ⟨cfg', h', h_end⟩ := hc₂
  exact ⟨cfg', h.trans_plus h', h_end⟩

theorem StepsToClosed.of_isInPatternSet {M : Machine Γ Λ} {ps : TapePatternSet Γ Λ}
    {c₁ c₂ : Cfg Γ Λ} (h : ReachesPlus M c₁ c₂) (hc₂ : IsInPatternSet ps c₂) :
    StepsToClosed M ps c₁ :=
  ⟨c₂, h, Or.inl hc₂⟩

theorem StepsToClosed.of_halting {M : Machine Γ Λ} {ps : TapePatternSet Γ Λ}
    {c₁ c₂ : Cfg Γ Λ} (h : ReachesPlus M c₁ c₂) (hc₂ : (step M c₂).isNone) :
    StepsToClosed M ps c₁ :=
  ⟨c₂, h, Or.inr hc₂⟩

/-! ## Collatz-Like Acceleration (`CollatzHalts`, `IsValidAcceleration`) -/

theorem CollatzHalts.of_next_eq_none {S : Type*} {next : S → Option S} {s : S}
    (h : next s = none) :
    CollatzHalts next s :=
  ⟨1, by simp [h]⟩

theorem CollatzHalts.of_next_eq_some {S : Type*} {next : S → Option S} {s s' : S}
    (h : next s = some s') (h' : CollatzHalts next s') :
    CollatzHalts next s := by
  obtain ⟨n, hn⟩ := h'
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply]
  simpa [h] using hn

theorem IsValidAcceleration.haltsFrom_of_collatzHalts {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    (h : IsValidAcceleration M start encode next) {s : S} (hs : CollatzHalts next s) :
    HaltsFrom M (encode s) := by
  obtain ⟨n, hn⟩ := hs
  induction n generalizing s with
  | zero =>
    simp at hn
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hn
    rcases hnext : next s with _ | s'
    · exact h.step_none s hnext
    · refine HaltsFrom.of_reachesStar (h.step_some s s' hnext).to_star (ih ?_)
      simpa [hnext] using hn

/-- A valid Collatz-like acceleration of `M` preserves and reflects halting: `M` halts from the
blank tape if and only if the accelerated transition function `next` halts from `start`. -/
theorem IsValidAcceleration.isHalt_iff {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    (h : IsValidAcceleration M start encode next) :
    IsHalt M ↔ CollatzHalts next start := by
  constructor
  · intro h_halt
    by_contra h_not_collatz
    have h_not_halt : IsNotHalt M :=
      IsNotHalt.of_reachesPlus_invariant
        (P := fun cfg => ∃ s, cfg = encode s ∧ ¬ CollatzHalts next s)
        h.init_reaches
        ⟨start, rfl, h_not_collatz⟩
        (fun cfg hP => by
          obtain ⟨s, rfl, hns⟩ := hP
          rcases hnext : next s with _ | s'
          · exact False.elim (hns (CollatzHalts.of_next_eq_none hnext))
          · refine ⟨encode s', h.step_some s s' hnext, s', rfl, ?_⟩
            intro hs'
            exact hns (CollatzHalts.of_next_eq_some hnext hs'))
    obtain ⟨cfg, hreach, hnone⟩ := h_halt
    have hsome := h_not_halt cfg hreach
    rw [Option.isNone_iff_eq_none] at hnone
    simp [hnone] at hsome
  · intro h_collatz
    exact HaltsFrom.of_reachesStar h.init_reaches (h.haltsFrom_of_collatzHalts h_collatz)

/-! ## Standard 6-State Labels (`SixState`)

Standard control state labels `A..F` (`0..5 : Fin 6`) for 6-state Busy Beaver machines. -/

namespace SixState

/-- State `A` (`0 : Fin 6`), the initial state. -/
abbrev A : Fin 6 := 0
/-- State `B` (`1 : Fin 6`). -/
abbrev B : Fin 6 := 1
/-- State `C` (`2 : Fin 6`). -/
abbrev C : Fin 6 := 2
/-- State `D` (`3 : Fin 6`). -/
abbrev D : Fin 6 := 3
/-- State `E` (`4 : Fin 6`). -/
abbrev E : Fin 6 := 4
/-- State `F` (`5 : Fin 6`). -/
abbrev F : Fin 6 := 5

end SixState

/-! ## Standard 3-State Labels (`ThreeState`)

Standard control state labels `A..C` (`0..2 : Fin 3`) for 3-state Busy Beaver machines. -/

namespace ThreeState

/-- State `A` (`0 : Fin 3`), the initial state. -/
abbrev A : Fin 3 := 0
/-- State `B` (`1 : Fin 3`). -/
abbrev B : Fin 3 := 1
/-- State `C` (`2 : Fin 3`). -/
abbrev C : Fin 3 := 2

end ThreeState

/-! ## Concrete Step Execution Tactics (`bb_refl`, `bb_step`, `bb_steps`, `bb_halt`) -/

/-- Close a reflexive `ReachesStar` goal after normalizing directed-head configurations and
`ListBlank` prefixes. -/
macro "bb_refl" : tactic =>
  `(tactic| (
    try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
      List.cons_append, List.nil_append, List.append_nil,
      ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
      ListBlank.cons_default_default, ListBlank.cons_zero_default]
    exact ReachesStar.refl _ _))

/-- Execute one concrete `BusyBeaver.step` on a `ReachesPlus` or `ReachesStar` goal and normalize
the resulting tape configuration. -/
macro "bb_step" : tactic =>
  `(tactic| (
    first
    | refine ReachesPlus.head (by
        try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
          List.cons_append, List.nil_append, List.append_nil,
          ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons,
          ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
          ListBlank.cons_default_default, ListBlank.cons_zero_default]
        rfl) ?_
    | refine ReachesStar.head (by
        try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
          List.cons_append, List.nil_append, List.append_nil,
          ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons,
          ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
          ListBlank.cons_default_default, ListBlank.cons_zero_default]
        rfl) ?_
    try simp only [Tape.write, Tape.move, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
      ListBlank.cons_default_default, ListBlank.cons_zero_default]))

/-- Repeatedly step a `ReachesPlus` or `ReachesStar` goal until it closes by reflexivity (`bb_refl`)
or reaches a symbolic head symbol. -/
macro "bb_steps" : tactic =>
  `(tactic| repeat (first | bb_refl | bb_step))

/-- Close a `(step M cfg).isNone` halting goal after normalizing directed-head configurations and
`ListBlank` prefixes. -/
macro "bb_halt" : tactic =>
  `(tactic| (
    try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
      List.cons_append, List.nil_append, List.append_nil,
      ListBlank.mk_nil, ListBlank.append, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.head_default, ListBlank.head_default_fin, ListBlank.tail_default,
      ListBlank.cons_default_default, ListBlank.cons_zero_default]
    rfl))


/-! ## Directed-Head and Reachability Notations
(Defined in `BusyBeaver.Defs`) -/

/-! ## Additional Half-Tape Power Lemmas -/

/-- Reversed addition law for repeated block appendages on a `ListBlank`. -/
theorem ListBlank.append_pow_add_rev (s : ListBlank Γ) (u : List Γ) (m n : ℕ) :
    ListBlank.append (u ^ (m + n)) s = ListBlank.append (u ^ n) (ListBlank.append (u ^ m) s) := by
  rw [Nat.add_comm, ListBlank.append_pow_add]

/-- Absorb one trailing copy of `u` into `u ^ k` on a `ListBlank`. -/
theorem ListBlank.append_pow_succ' (u : List Γ) (k : ℕ) (r : ListBlank Γ) :
    ListBlank.append (u ^ k) (ListBlank.append u r) = ListBlank.append (u ^ (k + 1)) r := by
  rw [ListBlank.append_append, list_pow_succ']

/-- Shift `[0, 1] ^ c` on the blank half-tape into `0 :: [1, 0] ^ c`. -/
theorem default_append_01_pow (c : ℕ) :
    ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default =
      ListBlank.cons 0 (ListBlank.append (([1, 0] : List (Fin 2)) ^ c) default) := by
  conv_lhs => rw [ListBlank.default_eq_append_zero]
  exact append_01_pow_zero c default

/-- Construct `IsValidAcceleration` from an initial reachability proof and a unified step theorem
dispatching on `next s`. -/
theorem IsValidAcceleration.of_step {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    (h_init : ReachesStar M (init []) (encode start))
    (h_step : ∀ s, match next s with
      | some s' => ReachesPlus M (encode s) (encode s')
      | none => ∃ cfg', ReachesStar M (encode s) cfg' ∧ (step M cfg').isNone) :
    IsValidAcceleration M start encode next where
  init_reaches := h_init
  step_some s s' h := by
    have hs := h_step s
    rw [h] at hs
    exact hs
  step_none s h := by
    have hs := h_step s
    rw [h] at hs
    exact hs

/-- Derive `IsClosedPatternSet M ps` from a valid acceleration `IsValidAcceleration M start encode
next` whose image `encode` characterizes `ps` and whose halting states step in `ReachesPlus` to a
halting configuration. -/
theorem IsValidAcceleration.isClosedPatternSet {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    {ps : TapePatternSet Γ Λ}
    (h : IsValidAcceleration M start encode next)
    (h_in : ∀ s, IsInPatternSet ps (encode s))
    (h_of_in : ∀ cfg, IsInPatternSet ps cfg → ∃ s, cfg = encode s)
    (h_halt_plus : ∀ s, next s = none →
      ∃ cfg', ReachesPlus M (encode s) cfg' ∧ (step M cfg').isNone) :
    IsClosedPatternSet M ps := by
  refine ⟨⟨encode start, h.init_reaches, h_in start⟩, fun cfg hcfg => ?_⟩
  obtain ⟨s, rfl⟩ := h_of_in cfg hcfg
  rcases hnext : next s with _ | s'
  · obtain ⟨cfg', hplus, hnone⟩ := h_halt_plus s hnext
    exact ⟨cfg', hplus, Or.inr hnone⟩
  · exact ⟨encode s', h.step_some s s' hnext, Or.inl (h_in s')⟩

/-- Derive `IsClosedStackPatternSet M ps` from a valid acceleration `IsValidAcceleration M start
encode next` whose image `encode` characterizes a well-formed `ps` and whose halting states step in
`ReachesPlus` to a halting configuration. -/
theorem IsValidAcceleration.isClosedStackPatternSet [DecidableEq Γ] {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    {ps : StackPatternSet Γ Λ}
    (h : IsValidAcceleration M start encode next)
    (h_in : ∀ s, IsInStackPatternSet ps (encode s))
    (h_of_in : ∀ cfg, IsInStackPatternSet ps cfg → ∃ s, cfg = encode s)
    (h_halt_plus : ∀ s, next s = none →
      ∃ cfg', ReachesPlus M (encode s) cfg' ∧ (step M cfg').isNone)
    (h_wf : IsWellFormedStackPatternSet ps := by rfl) :
    IsClosedStackPatternSet M ps := by
  refine ⟨h_wf, ⟨encode start, h.init_reaches, h_in start⟩, fun cfg hcfg => ?_⟩
  obtain ⟨s, rfl⟩ := h_of_in cfg hcfg
  rcases hnext : next s with _ | s'
  · obtain ⟨cfg', hplus, hnone⟩ := h_halt_plus s hnext
    exact ⟨cfg', hplus, Or.inr hnone⟩
  · exact ⟨encode s', h.step_some s s' hnext, Or.inl (h_in s')⟩

omit [Inhabited Γ] in
private theorem evalStackSeg_two_word_of_bool (a₀ a₁ : Γ) (w : List Bool) :
    (((w.map fun b => if b then 1 else 0).map fun d =>
        ([[a₀], [a₁]] : List (List Γ)).getD d []).flatten) =
      w.map (fun b => if b then a₁ else a₀) := by
  induction w with
  | nil => rfl
  | cons b rest ih =>
    cases b <;> simpa using ih

omit [Inhabited Γ] in
private theorem exists_bool_of_evalStackSeg_two_word (a₀ a₁ : Γ) (ds : List ℕ) :
    ∃ w : List Bool,
      ((ds.map fun d => ([[a₀], [a₁]] : List (List Γ)).getD d []).flatten) =
        w.map (fun b => if b then a₁ else a₀) := by
  induction ds with
  | nil => exact ⟨[], rfl⟩
  | cons d rest ih =>
    obtain ⟨w, hw⟩ := ih
    rcases d with _ | _ | d
    · refine ⟨false :: w, ?_⟩
      simpa using hw
    · refine ⟨true :: w, ?_⟩
      simpa using hw
    · refine ⟨w, ?_⟩
      simpa using hw

/-- Characterize a single two-symbol `.word [[a₀], [a₁]] 0` `StackExpr` as the image of a
`List Bool` word `w` mapped by `fun b => if b then a₁ else a₀`. -/
theorem exists_evalStackExpr_single_word_iff (a₀ a₁ : Γ) (s : ListBlank Γ) :
    (∃ (vars : ℕ → ℕ) (stks : ℕ → List ℕ),
      s = evalStackExpr [.word [[a₀], [a₁]] 0] vars stks) ↔
    ∃ w : List Bool,
      s = ListBlank.append (w.map (fun b => if b then a₁ else a₀)) default := by
  constructor
  · rintro ⟨vars, stks, rfl⟩
    obtain ⟨w, hw⟩ := exists_bool_of_evalStackSeg_two_word a₀ a₁ (stks 0)
    refine ⟨w, ?_⟩
    dsimp only [evalStackExpr, evalStackSeg]
    rw [hw]
  · rintro ⟨w, rfl⟩
    refine ⟨fun _ => 0, fun _ => w.map (fun b => if b then 1 else 0), ?_⟩
    have hw := evalStackSeg_two_word_of_bool a₀ a₁ w
    dsimp only [evalStackExpr, evalStackSeg]
    rw [hw]

/-! ## Higher-Level Acceleration Reduction (`CollatzReachesStar`, `CollatzStepsTo`) -/

/-- Any two valid Collatz-like accelerations of the same machine `M` have equivalent halting
problems. -/
theorem IsValidAcceleration.collatzHalts_iff {M : Machine Γ Λ} {S₁ S₂ : Type*}
    {start₁ : S₁} {encode₁ : S₁ → Cfg Γ Λ} {next₁ : S₁ → Option S₁}
    {start₂ : S₂} {encode₂ : S₂ → Cfg Γ Λ} {next₂ : S₂ → Option S₂}
    (h₁ : IsValidAcceleration M start₁ encode₁ next₁)
    (h₂ : IsValidAcceleration M start₂ encode₂ next₂) :
    CollatzHalts next₁ start₁ ↔ CollatzHalts next₂ start₂ :=
  h₁.isHalt_iff.symm.trans h₂.isHalt_iff

/-- `next` reaches `s₂` from `s₁` in `n` steps. -/
def CollatzReachesIn {S : Type*} (next : S → Option S) (n : ℕ) (s₁ s₂ : S) : Prop :=
  (Option.bind · next)^[n] (some s₁) = some s₂

/-- `next` reaches `s₂` from `s₁` in zero or more steps. -/
def CollatzReachesStar {S : Type*} (next : S → Option S) (s₁ s₂ : S) : Prop :=
  ∃ n : ℕ, CollatzReachesIn next n s₁ s₂

/-- `next` reaches `s₂` from `s₁` in one or more steps. -/
def CollatzReachesPlus {S : Type*} (next : S → Option S) (s₁ s₂ : S) : Prop :=
  ∃ n : ℕ, n > 0 ∧ CollatzReachesIn next n s₁ s₂

/-- `next` from `s` either reaches `s'` in one or more steps (`some s'`) or halts (`none`). -/
def CollatzStepsTo {S : Type*} (next : S → Option S) (s : S) : Option S → Prop
  | some s' => CollatzReachesPlus next s s'
  | none => CollatzHalts next s

@[simp]
private theorem iterate_bind_none {S : Type*} (next : S → Option S) (n : ℕ) :
    (Option.bind · next)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Option.bind_none, ih]

private theorem CollatzReachesIn.head {next : S → Option S} {n : ℕ} {s₁ s₂ s₃ : S}
    (h₁ : next s₁ = some s₂) (h₂ : CollatzReachesIn next n s₂ s₃) :
    CollatzReachesIn next (n + 1) s₁ s₃ := by
  unfold CollatzReachesIn at *
  rw [Function.iterate_succ_apply]
  simpa [h₁] using h₂

private theorem CollatzReachesIn.trans {next : S → Option S} {m n : ℕ} {s₁ s₂ s₃ : S}
    (h₁ : CollatzReachesIn next m s₁ s₂) (h₂ : CollatzReachesIn next n s₂ s₃) :
    CollatzReachesIn next (m + n) s₁ s₃ := by
  unfold CollatzReachesIn at *
  rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]

theorem CollatzReachesStar.refl (next : S → Option S) (s : S) :
    CollatzReachesStar next s s :=
  ⟨0, rfl⟩

theorem CollatzReachesStar.head {next : S → Option S} {s₁ s₂ s₃ : S}
    (h₁ : next s₁ = some s₂) (h₂ : CollatzReachesStar next s₂ s₃) :
    CollatzReachesStar next s₁ s₃ :=
  let ⟨n, hn⟩ := h₂
  ⟨n + 1, CollatzReachesIn.head h₁ hn⟩

theorem CollatzReachesStar.single {next : S → Option S} {s₁ s₂ : S}
    (h : next s₁ = some s₂) :
    CollatzReachesStar next s₁ s₂ :=
  CollatzReachesStar.head h (CollatzReachesStar.refl next s₂)

theorem CollatzReachesPlus.single {next : S → Option S} {s₁ s₂ : S}
    (h : next s₁ = some s₂) :
    CollatzReachesPlus next s₁ s₂ :=
  ⟨1, Nat.succ_pos 0, CollatzReachesIn.head h rfl⟩

theorem CollatzReachesPlus.to_star {next : S → Option S} {s₁ s₂ : S}
    (h : CollatzReachesPlus next s₁ s₂) :
    CollatzReachesStar next s₁ s₂ :=
  let ⟨n, _, hn⟩ := h
  ⟨n, hn⟩

theorem CollatzReachesPlus.head {next : S → Option S} {s₁ s₂ s₃ : S}
    (h₁ : next s₁ = some s₂) (h₂ : CollatzReachesStar next s₂ s₃) :
    CollatzReachesPlus next s₁ s₃ :=
  let ⟨n, hn⟩ := h₂
  ⟨n + 1, Nat.succ_pos n, CollatzReachesIn.head h₁ hn⟩

private theorem CollatzReachesStar.trans_plus {next : S → Option S} {s₁ s₂ s₃ : S}
    (h₁ : CollatzReachesStar next s₁ s₂) (h₂ : CollatzReachesPlus next s₂ s₃) :
    CollatzReachesPlus next s₁ s₃ :=
  let ⟨m, hm⟩ := h₁
  let ⟨n, hn_pos, hn⟩ := h₂
  ⟨m + n, Nat.add_pos_right m hn_pos, hm.trans hn⟩

private theorem CollatzHalts.of_reachesStar {next : S → Option S} {s₁ s₂ : S}
    (h₁ : CollatzReachesStar next s₁ s₂) (h₂ : CollatzHalts next s₂) :
    CollatzHalts next s₁ := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  refine ⟨m + n, ?_⟩
  unfold CollatzReachesIn at hm
  rw [Nat.add_comm, Function.iterate_add_apply, hm, hn]

theorem CollatzStepsTo.of_eq {next : S → Option S} {s : S} {res : Option S}
    (h : next s = res) :
    CollatzStepsTo next s res := by
  rcases res with _ | s'
  · exact CollatzHalts.of_next_eq_none h
  · exact CollatzReachesPlus.single h

theorem CollatzStepsTo.head {next : S → Option S} {s₁ s₂ : S} {res : Option S}
    (h₁ : next s₁ = some s₂) (h₂ : CollatzStepsTo next s₂ res) :
    CollatzStepsTo next s₁ res := by
  rcases res with _ | s'
  · exact CollatzHalts.of_next_eq_some h₁ h₂
  · exact CollatzReachesPlus.head h₁ h₂.to_star

theorem CollatzStepsTo.of_reachesStar {next : S → Option S} {s₁ s₂ : S} {res : Option S}
    (h₁ : CollatzReachesStar next s₁ s₂) (h₂ : CollatzStepsTo next s₂ res) :
    CollatzStepsTo next s₁ res := by
  rcases res with _ | s'
  · exact CollatzHalts.of_reachesStar h₁ h₂
  · exact h₁.trans_plus h₂

private theorem IsValidAcceleration.reachesStar_of_collatzReachesIn {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    (h : IsValidAcceleration M start encode next) {n : ℕ} {s₁ s₂ : S}
    (hs : CollatzReachesIn next n s₁ s₂) :
    ReachesStar M (encode s₁) (encode s₂) := by
  induction n generalizing s₁ with
  | zero =>
    unfold CollatzReachesIn at hs
    simp only [Function.iterate_zero_apply, Option.some.injEq] at hs
    subst hs
    exact ReachesStar.refl M (encode s₁)
  | succ n ih =>
    unfold CollatzReachesIn at hs
    rw [Function.iterate_succ_apply] at hs
    rcases hnext : next s₁ with _ | s'
    · simp [hnext] at hs
    · refine (h.step_some s₁ s' hnext).to_star.trans (ih ?_)
      change (Option.bind · next)^[n] (some s') = some s₂
      simpa [hnext] using hs

private theorem IsValidAcceleration.reachesStar_of_collatzReachesStar {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    (h : IsValidAcceleration M start encode next) {s₁ s₂ : S}
    (hs : CollatzReachesStar next s₁ s₂) :
    ReachesStar M (encode s₁) (encode s₂) := by
  obtain ⟨n, hn⟩ := hs
  exact h.reachesStar_of_collatzReachesIn hn

private theorem IsValidAcceleration.reachesPlus_of_collatzReachesPlus {M : Machine Γ Λ} {S : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    (h : IsValidAcceleration M start encode next) {s₁ s₂ : S}
    (hs : CollatzReachesPlus next s₁ s₂) :
    ReachesPlus M (encode s₁) (encode s₂) := by
  obtain ⟨n, hn_pos, hn⟩ := hs
  rcases n with _ | n
  · omega
  · unfold CollatzReachesIn at hn
    rw [Function.iterate_succ_apply] at hn
    rcases hnext : next s₁ with _ | s'
    · simp [hnext] at hn
    · refine (h.step_some s₁ s' hnext).trans_star (h.reachesStar_of_collatzReachesIn (n := n) ?_)
      unfold CollatzReachesIn
      simpa [hnext] using hn

/-- Construct a higher-level `IsValidAcceleration` from a base `IsValidAcceleration` by showing
that `start` reaches `embed highLevelStart` under `next` and each step of `highLevelNext` is
simulated by one or more steps of `next`. -/
theorem IsValidAcceleration.of_collatz {M : Machine Γ Λ} {S H : Type*}
    {start : S} {encode : S → Cfg Γ Λ} {next : S → Option S}
    {highLevelStart : H} {embed : H → S} {highLevelNext : H → Option H}
    (h : IsValidAcceleration M start encode next)
    (h_init : CollatzReachesStar next start (embed highLevelStart))
    (h_step : ∀ u, CollatzStepsTo next (embed u) ((highLevelNext u).map embed)) :
    IsValidAcceleration M highLevelStart (fun u => encode (embed u)) highLevelNext where
  init_reaches := h.init_reaches.trans (h.reachesStar_of_collatzReachesStar h_init)
  step_some u u' hu := by
    have hs := h_step u
    rw [hu, Option.map_some] at hs
    exact h.reachesPlus_of_collatzReachesPlus hs
  step_none u hu := by
    have hs := h_step u
    rw [hu, Option.map_none] at hs
    exact h.haltsFrom_of_collatzHalts hs

end BusyBeaver
