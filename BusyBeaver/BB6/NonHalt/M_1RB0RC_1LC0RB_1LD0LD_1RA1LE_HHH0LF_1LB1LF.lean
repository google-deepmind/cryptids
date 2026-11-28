/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat
import BusyBeaver.Stack
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import BusyBeaver.Calculi.Longitudinal

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RC_1LC0RB_1LD0LD_1RA1LE_HHH0LF_1LB1LF


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0RC_1LC0RB_1LD0LD_1RA1LE_HHH0LF_1LB1LF` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RC_1LC0RB_1LD0LD_1RA1LE_HHH0LF_1LB1LF"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => none
  | 4, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 5, Stmt.write 1 Dir.left)


namespace SafeBudget
open BusyBeaver.Longitudinal in
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-! ## Local Multi-Step Helpers & Budget-Indexed Safety Calculus (`safe`) -/

@[scoped simp] private theorem multiStep_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    multiStep M c 0 = some c := rfl

private theorem multiStep_succ (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = (multiStep M c n).bind (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

private theorem multiStep_add (M : Machine Γ Λ) (c : Cfg Γ Λ) (m n : ℕ) :
    multiStep M c (m + n) = (multiStep M c m).bind (fun c' => multiStep M c' n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    congr 1
    funext c'
    exact (multiStep_succ M c' n).symm

/-- Budget-indexed safety: configuration `c` can execute for at least `N` steps without halting,
i.e., every configuration reachable in `M' ≤ N` steps has a valid next step. -/
private def safe (M : Machine Γ Λ) (c : Cfg Γ Λ) (N : ℕ) : Prop :=
  ∀ M' ≤ N, ∀ cfg, multiStep M c M' = some cfg → (step M cfg).isSome

/-- If `c` reaches `cfg` in `K` steps, then at every strictly earlier step `M' < K` the reached
configuration `cfgM` has a valid next step. -/
private theorem multiStep_lt_isSome {M : Machine Γ Λ} {c cfg : Cfg Γ Λ} {K M' : ℕ}
    (h : multiStep M c K = some cfg) (hM : M' < K) :
    ∀ cfgM, multiStep M c M' = some cfgM → (step M cfgM).isSome := by
  intro cfgM hcfgM
  have hsplit : K = (M' + 1) + (K - (M' + 1)) := by omega
  rw [hsplit, multiStep_add, multiStep_succ, hcfgM, Option.bind_some] at h
  cases hstep : step M cfgM with
  | none =>
    rw [hstep, Option.bind_none] at h
    contradiction
  | some _ => rfl

/-- If `c` reaches `c'` in `K` steps and `c` reaches `cfg` in `M' ≥ K` steps, then `c'` reaches
`cfg` in `M' - K` steps. -/
private theorem multiStep_ge_drop {M : Machine Γ Λ} {c c' cfg : Cfg Γ Λ} {K M' : ℕ}
    (h1 : multiStep M c K = some c') (h2 : K ≤ M') (h3 : multiStep M c M' = some cfg) :
    multiStep M c' (M' - K) = some cfg := by
  have hsplit : M' = K + (M' - K) := by omega
  rw [hsplit, multiStep_add, h1, Option.bind_some] at h3
  exact h3

/-- Safety pulls back across `⊢*`. -/
private theorem safe_ev {M : Machine Γ Λ} {c c' : Cfg Γ Λ} {N : ℕ}
    (hev : c [M]⊢* c') (hs : safe M c' N) : safe M c N := by
  rcases hev with ⟨K, hK⟩
  intro M' hM cfg hcfg
  by_cases hlt : M' < K
  · exact multiStep_lt_isSome hK hlt cfg hcfg
  · have hge : K ≤ M' := by omega
    have hrem : M' - K ≤ N := by omega
    exact hs (M' - K) hrem cfg (multiStep_ge_drop hK hge hcfg)

/-- Safety pulls back across a positive transition `⊢⁺` while decrementing the budget from `N` to
`N - 1`. -/
private theorem safe_prog {M : Machine Γ Λ} {c c' : Cfg Γ Λ} {N : ℕ}
    (hp : c [M]⊢⁺ c') (hs : safe M c' (N - 1)) : safe M c N := by
  rcases hp with ⟨K, hKpos, hK⟩
  intro M' hM cfg hcfg
  by_cases hlt : M' < K
  · exact multiStep_lt_isSome hK hlt cfg hcfg
  · have hge : K ≤ M' := by omega
    have hrem : M' - K ≤ N - 1 := by omega
    exact hs (M' - K) hrem cfg (multiStep_ge_drop hK hge hcfg)

/-- Any positive transition `c ⊢⁺ c'` witnesses 0-step safety `safe M c 0`. -/
private theorem safe_prog0 {M : Machine Γ Λ} {c c' : Cfg Γ Λ}
    (hp : c [M]⊢⁺ c') : safe M c 0 := by
  rcases hp with ⟨K, hKpos, hK⟩
  intro M' hM cfg hcfg
  exact multiStep_lt_isSome hK (by omega) cfg hcfg

/-- `M` never halts when started from configuration `c` (`BusyBeaver.NeverHaltsFrom`). -/
private abbrev NeverHaltsFrom (M : Machine Γ Λ) (c : Cfg Γ Λ) : Prop :=
  ∀ cfg, (c [M]⊢* cfg) → (step M cfg).isSome

/-- If `c₀ ⊢* c` and `c` is `N`-safe for all `N : ℕ`, then `NeverHaltsFrom M c₀`. -/
private theorem nonhalt_of_safe_all {M : Machine Γ Λ} {c₀ c : Cfg Γ Λ}
    (h0 : c₀ [M]⊢* c) (hall : ∀ N, safe M c N) : NeverHaltsFrom M c₀ := by
  intro cfg ⟨K, hK⟩
  exact safe_ev h0 (hall K) K (Nat.le_refl K) cfg hK

/-- If `init [] ⊢* c` and `c` is `N`-safe for all `N : ℕ`, then `IsNotHalt M`. -/
private theorem isNotHalt_of_safe_all {M : Machine Γ Λ} {c : Cfg Γ Λ}
    (h0 : (init []) [M]⊢* c) (hall : ∀ N, safe M c N) : IsNotHalt M :=
  nonhalt_of_safe_all h0 hall

/-- Strong induction combinator for raw TM step budgets. -/
private theorem nat_strong_ind {P : ℕ → Prop}
    (h : ∀ n, (∀ m < n, P m) → P n) (n : ℕ) : P n := by
  suffices hall : ∀ k ≤ n, P k from hall n (Nat.le_refl n)
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact h 0 (fun m hm => by omega)
  | succ n ih =>
    intro k hk
    by_cases hkn : k ≤ n
    · exact ih k hkn
    · have hkeq : k = n + 1 := by omega
      subst hkeq
      exact h (n + 1) (fun m hm => ih m (by omega))

end SafeBudget


namespace Solution

open SafeBudget

/-! ## Tape Encoding, `SafeRet`, and Basic `ListBlank` Helpers -/

private abbrev Sym := Fin 2
private abbrev State := Fin 6
private abbrev TM := target_tm

private def sA : State := 0
private def sB : State := 1
private def sC : State := 2
private def sD : State := 3
private def sE : State := 4
private def sF : State := 5

private def encR : List ℕ → ListBlank Sym
  | [] => default
  | d :: Rr => (([1] : List Sym) ^ d) +> ((0 : Sym) >> encR Rr)

private def bumpR : List ℕ → ℕ → List ℕ
  | [], k => [k]
  | d :: Rr, k => (d + k) :: Rr

private def BR (l : ListBlank Sym) (m : ℕ) (R : List ℕ) : Cfg Sym State :=
  ((l <+ ([0] : List Sym)) <+ (([1] : List Sym) ^ m)) {{sB}}> encR R

private def BL (l : ListBlank Sym) (R : List ℕ) : Cfg Sym State :=
  l <{{sB}} encR R

private def B0 (l : ListBlank Sym) (R : List ℕ) : Cfg Sym State :=
  ⟨some sB, ⟨0, l, encR R⟩⟩

private theorem cons_zero_def : (0 : Sym) >> (default : ListBlank Sym) = default :=
  ListBlank.cons_zero_default

private theorem append_zeros_def
    (k : ℕ) : (default : ListBlank Sym) <+ (([0] : List Sym) ^ k) = default := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (0 : Sym) >> ((default : ListBlank Sym) <+ (([0] : List Sym) ^ k)) = default
    rw [ih, cons_zero_def]

private theorem append_pow_add (b : Sym) (l : ListBlank Sym) (a c : ℕ) :
    (l <+ (([b] : List Sym) ^ a)) <+ (([b] : List Sym) ^ c) = l <+ (([b] : List Sym) ^ (a + c)) :=
        by
  rw [listblank_append_append, list_pow_add_comm, ← list_pow_add]

private theorem append_pow_right (b : Sym) (r : ListBlank Sym) (a c : ℕ) :
    (([b] : List Sym) ^ a) +> ((([b] : List Sym) ^ c) +> r) = (([b] : List Sym) ^ (a + c)) +> r :=
        by
  rw [list_pow_add, ← BusyBeaver.PairStack.listblank_append_right_assoc]

private theorem encR_bumpR (R : List ℕ) (k : ℕ) :
    (([1] : List Sym) ^ k) +> encR R = encR (bumpR R k) := by
  cases R with
  | nil =>
    change (([1] : List Sym) ^ k) +> default = (([1] : List Sym) ^ k) +> ((0 : Sym) >> default)
    rw [cons_zero_def]
  | cons d Rr =>
    change (([1] : List Sym) ^ k) +> ((([1] : List Sym) ^ d) +> ((0 : Sym) >> encR Rr)) =
      (([1] : List Sym) ^ (d + k)) +> ((0 : Sym) >> encR Rr)
    rw [append_pow_right, Nat.add_comm]

private theorem encR_bumpR_one (R : List ℕ) :
    (1 : Sym) >> encR R = encR (bumpR R 1) := by
  have h := encR_bumpR R 1
  simpa [pow_succ_list, pow_zero_list, listblank_append_cons, listblank_append_nil] using h

private theorem encR_bumpR_three (R : List ℕ) :
    (1 : Sym) >> ((1 : Sym) >> ((1 : Sym) >> encR R)) = encR (bumpR R 3) := by
  have h := encR_bumpR R 3
  simpa [pow_succ_list, pow_zero_list, listblank_append_cons, listblank_append_nil] using h

private theorem safe_of_reachesIn {c c' : Cfg Sym State} {k N : ℕ}
    (hk : c [TM]⊢^{k} c') (hle : k ≤ N) (hs : safe TM c' (N - k)) : safe TM c N := by
  induction k generalizing c N with
  | zero =>
    simp only [multiStep_zero, Option.some.injEq] at hk
    subst hk
    simpa using hs
  | succ k ih =>
    rw [multiStep_succ] at hk
    cases h1 : step TM c with
    | none => rw [h1, Option.bind_none] at hk; cases hk
    | some c1 =>
      rw [h1, Option.bind_some] at hk
      refine safe_prog (ReachesPlus.single h1) ?_
      have hsub : N - 1 - k = N - (k + 1) := by omega
      rw [← hsub] at hs
      exact ih hk (by omega) hs

private theorem safe_of_reachesIn_lt {c c' : Cfg Sym State} {k N : ℕ}
    (hk : c [TM]⊢^{k} c') (hlt : N < k) : safe TM c N := by
  induction k generalizing c N with
  | zero => omega
  | succ k ih =>
    rw [multiStep_succ] at hk
    cases h1 : step TM c with
    | none => rw [h1, Option.bind_none] at hk; cases hk
    | some c1 =>
      rw [h1, Option.bind_some] at hk
      cases N with
      | zero => exact safe_prog0 (ReachesPlus.single h1)
      | succ N' => exact safe_prog (ReachesPlus.single h1) (ih hk (by omega))

/-- Budget-indexed return specification: starting from `c`, either `c` is `N`-safe without needing
to return yet, or within `1 ≤ k ≤ N` raw TM steps `c` reaches `BL l R'` with `Q R'`. -/
private def SafeRet (N : ℕ) (l : ListBlank Sym) (c : Cfg Sym State) (Q : List ℕ → Prop) : Prop :=
  safe TM c N ∨ ∃ k R', 0 < k ∧ k ≤ N ∧ (c [TM]⊢^{k} BL l R') ∧ Q R'

private theorem SafeRet.mono_Q {N : ℕ} {l : ListBlank Sym} {c : Cfg Sym State}
    {Q₁ Q₂ : List ℕ → Prop} (h : SafeRet N l c Q₁) (himp : ∀ R, Q₁ R → Q₂ R) :
    SafeRet N l c Q₂ := by
  rcases h with hs | ⟨k, R', hpos, hle, hk, hq⟩
  · exact Or.inl hs
  · exact Or.inr ⟨k, R', hpos, hle, hk, himp R' hq⟩

private theorem SafeRet.done_plus {N : ℕ} {l : ListBlank Sym} {c : Cfg Sym State} {R' : List ℕ}
    {Q : List ℕ → Prop} (hp : c [TM]⊢⁺ BL l R') (hQ : Q R') : SafeRet N l c Q := by
  rcases hp with ⟨s, hs_pos, hs⟩
  by_cases hlt : N < s
  · exact Or.inl (safe_of_reachesIn_lt hs hlt)
  · exact Or.inr ⟨s, R', hs_pos, by omega, hs, hQ⟩

private theorem SafeRet.step_plus {N : ℕ} {l : ListBlank Sym} {c c' : Cfg Sym State}
    {Q : List ℕ → Prop} (hp : c [TM]⊢⁺ c') (hnext : ∀ N' < N, SafeRet N' l c' Q) :
    SafeRet N l c Q := by
  rcases hp with ⟨s, hs_pos, hs⟩
  by_cases hlt : N < s
  · exact Or.inl (safe_of_reachesIn_lt hs hlt)
  · rcases hnext (N - s) (by omega) with hs' | ⟨k, R', hk_pos, hk_le, hk, hQ⟩
    · exact Or.inl (safe_of_reachesIn hs (by omega) hs')
    · exact Or.inr ⟨s + k, R', by omega, by omega, multiStep_trans hs hk, hQ⟩

private theorem SafeRet.bind {N : ℕ} {l_sub l_out : ListBlank Sym} {c : Cfg Sym State}
    {Q_sub Q_out : List ℕ → Prop}
    (hsub : SafeRet N l_sub c Q_sub)
    (hcont : ∀ N' < N, ∀ R_sub, Q_sub R_sub → SafeRet N' l_out (BL l_sub R_sub) Q_out) :
    SafeRet N l_out c Q_out := by
  rcases hsub with hs | ⟨k, R_sub, hk_pos, hk_le, hk, hQ⟩
  · exact Or.inl hs
  · rcases hcont (N - k) (by omega) R_sub hQ with hs' | ⟨k', R', hk'_pos, hk'_le, hk', hQ'⟩
    · exact Or.inl (safe_of_reachesIn hk hk_le hs')
    · exact Or.inr ⟨k + k', R', by omega, by omega, multiStep_trans hk hk', hQ'⟩

/-! ## Elementary Raw-TM Transitions and `step2` Rules -/

private theorem BL_zero (l : ListBlank Sym) (R : List ℕ) :
    BL ((0 : Sym) >> l) R = B0 l R := by
  unfold BL B0
  simp only [ListBlank.head_cons, ListBlank.tail_cons]

private theorem pow0_lb (b : Sym) (l : ListBlank Sym) :
    l <+ (([b] : List Sym) ^ 0) = l := rfl

private theorem pow1_lb (b : Sym) (l : ListBlank Sym) :
    l <+ (([b] : List Sym) ^ 1) = b >> l := rfl

private theorem pow2_lb (b : Sym) (l : ListBlank Sym) :
    l <+ (([b] : List Sym) ^ 2) = b >> (b >> l) := rfl

private theorem pow3_lb (b : Sym) (l : ListBlank Sym) :
    l <+ (([b] : List Sym) ^ 3) = b >> (b >> (b >> l)) := rfl

private theorem step_A0_R (l r : ListBlank Sym) :
    (l {{sA}}> ((0 : Sym) >> r)) [TM]⊢ (((1 : Sym) >> l) {{sB}}> r) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem step_A1_R (l r : ListBlank Sym) :
    (l {{sA}}> ((1 : Sym) >> r)) [TM]⊢ (((0 : Sym) >> l) {{sC}}> r) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem step_B0 (l r : ListBlank Sym) :
    (⟨some sB, ⟨0, l, r⟩⟩ : Cfg Sym State) [TM]⊢ (l <{{sC}} ((1 : Sym) >> r)) := rfl

private theorem step_B1_R (l r : ListBlank Sym) :
    (l {{sB}}> ((1 : Sym) >> r)) [TM]⊢ (((0 : Sym) >> l) {{sB}}> r) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem step_B1_L (l r : ListBlank Sym) :
    (((1 : Sym) >> l) <{{sB}} r) [TM]⊢ (((0 : Sym) >> l) {{sB}}> r) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem step_C0_L (l r : ListBlank Sym) :
    (((0 : Sym) >> l) <{{sC}} r) [TM]⊢ (l <{{sD}} ((1 : Sym) >> r)) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem step_C1_L (l r : ListBlank Sym) :
    (((1 : Sym) >> l) <{{sC}} r) [TM]⊢ (l <{{sD}} ((0 : Sym) >> r)) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem step_C1_R (l r : ListBlank Sym) :
    (l {{sC}}> ((1 : Sym) >> r)) [TM]⊢ (l <{{sD}} ((0 : Sym) >> r)) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem step_D0_L (l r : ListBlank Sym) :
    (((0 : Sym) >> l) <{{sD}} r) [TM]⊢ (((1 : Sym) >> l) {{sA}}> r) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem step_D1_L (l r : ListBlank Sym) :
    (((1 : Sym) >> l) <{{sD}} r) [TM]⊢ (l <{{sE}} ((1 : Sym) >> r)) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem step_E1_L (l r : ListBlank Sym) :
    (((1 : Sym) >> l) <{{sE}} r) [TM]⊢ (l <{{sF}} ((0 : Sym) >> r)) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem step_F0_L (l r : ListBlank Sym) :
    (((0 : Sym) >> l) <{{sF}} r) [TM]⊢ (l <{{sB}} ((1 : Sym) >> r)) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem step_F1_L (l r : ListBlank Sym) :
    (((1 : Sym) >> l) <{{sF}} r) [TM]⊢ (l <{{sF}} ((1 : Sym) >> r)) := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]; rfl

private theorem sweep_B1 (d : ℕ) (l r : ListBlank Sym) :
    (l {{sB}}> ((([1] : List Sym) ^ d) +> ((0 : Sym) >> r))) [TM]⊢*
      ⟨some sB, ⟨0, l <+ (([0] : List Sym) ^ d), r⟩⟩ := by
  induction d generalizing l with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil, ListBlank.head_cons, ListBlank.tail_cons]
    exact ReachesStar.refl TM _
  | succ d ih =>
    have h1 : (l {{sB}}> ((([1] : List Sym) ^ (d + 1)) +> ((0 : Sym) >> r))) [TM]⊢
        (((0 : Sym) >> l) {{sB}}> ((([1] : List Sym) ^ d) +> ((0 : Sym) >> r))) :=
      step_B1_R l ((([1] : List Sym) ^ d) +> ((0 : Sym) >> r))
    have h2 := ih ((0 : Sym) >> l)
    have hl : ((0 : Sym) >> l) <+ (([0] : List Sym) ^ d) = l <+ (([0] : List Sym) ^ (d + 1)) := by
      have hcomm : (0 : Sym) >> l = l <+ (([0] : List Sym) ^ 1) := rfl
      rw [hcomm, append_pow_add, Nat.add_comm]
    rw [hl] at h2
    exact ReachesStar.head h1 h2

private theorem sweep_F1 (k : ℕ) (l r : ListBlank Sym) :
    ((l <+ (([1] : List Sym) ^ k)) <{{sF}} r) [TM]⊢* (l <{{sF}} ((([1] : List Sym) ^ k) +> r)) := by
  induction k generalizing r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    exact ReachesStar.refl TM _
  | succ k ih =>
    have h1 : ((l <+ (([1] : List Sym) ^ (k + 1))) <{{sF}} r) [TM]⊢
        ((l <+ (([1] : List Sym) ^ k)) <{{sF}} ((1 : Sym) >> r)) :=
      step_F1_L (l <+ (([1] : List Sym) ^ k)) r
    have h2 := ih ((1 : Sym) >> r)
    have hr : (([1] : List Sym) ^ k) +> ((1 : Sym) >> r) = (([1] : List Sym) ^ (k + 1)) +> r := by
      have h1r : (1 : Sym) >> r = (([1] : List Sym) ^ 1) +> r := rfl
      rw [h1r, append_pow_right, Nat.add_comm]
    rw [hr] at h2
    exact ReachesStar.head h1 h2

private theorem rule_B0_z2 (l : ListBlank Sym) (R : List ℕ) :
    (B0 ((0 : Sym) >> ((0 : Sym) >> l)) R) [TM]⊢⁺
      ((l <+ (([1] : List Sym) ^ 3)) {{sB}}> encR R) := by
  refine ReachesPlus.head (step_B0 _ _) ?_
  refine ReachesStar.head (step_C0_L _ _) ?_
  refine ReachesStar.head (step_D0_L _ _) ?_
  refine ReachesStar.head (step_A1_R _ _) ?_
  refine ReachesStar.head (step_C1_R _ _) ?_
  refine ReachesStar.head (step_D0_L _ _) ?_
  exact ReachesStar.single (step_A0_R _ _)

private theorem rule_B0_11 (l : ListBlank Sym) (R : List ℕ) :
    (B0 ((1 : Sym) >> ((0 : Sym) >> l)) R) [TM]⊢⁺
      ((l <+ (([1] : List Sym) ^ 2)) {{sB}}> encR (bumpR R 1)) := by
  refine ReachesPlus.head (step_B0 _ _) ?_
  refine ReachesStar.head (step_C1_L _ _) ?_
  refine ReachesStar.head (step_D0_L _ _) ?_
  rw [← encR_bumpR_one]
  exact ReachesStar.single (step_A0_R ((1 : Sym) >> l) ((1 : Sym) >> encR R))

private theorem rule_B0_01_1m (l : ListBlank Sym) (m : ℕ) (R : List ℕ) :
    (B0 ((0 : Sym) >> (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (m + 2)))) R) [TM]⊢⁺
      BL l ((m + 1) :: bumpR R 3) := by
  refine ReachesPlus.head (step_B0 _ _) ?_
  refine ReachesStar.head (step_C0_L _ _) ?_
  refine ReachesStar.head (step_D1_L _ _) ?_
  refine ReachesStar.head (step_E1_L _ _) ?_
  refine ReachesStar.trans
      (sweep_F1 m ((0 : Sym) >> l) ((0 : Sym) >>
      ((1 : Sym) >> ((1 : Sym) >> ((1 : Sym) >> encR R))))) ?_
  dsimp only [BL, encR]
  rw [← encR_bumpR_three]
  exact ReachesStar.single
      (step_F0_L l ((([1] : List Sym) ^ m) +>
      ((0 : Sym) >> ((1 : Sym) >> ((1 : Sym) >> ((1 : Sym) >> encR R))))))

private theorem rule_B0_1m (l : ListBlank Sym) (m : ℕ) (R : List ℕ) :
    (B0 (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (m + 3))) R) [TM]⊢⁺
      BL l ((m + 1) :: 1 :: bumpR R 1) := by
  refine ReachesPlus.head (step_B0 _ _) ?_
  refine ReachesStar.head (step_C1_L _ _) ?_
  refine ReachesStar.head (step_D1_L _ _) ?_
  refine ReachesStar.head (step_E1_L _ _) ?_
  refine ReachesStar.trans
      (sweep_F1 m ((0 : Sym) >> l) ((0 : Sym) >>
      ((1 : Sym) >> ((0 : Sym) >> ((1 : Sym) >> encR R))))) ?_
  dsimp only [BL, encR]
  rw [← encR_bumpR_one]
  exact ReachesStar.single
      (step_F0_L l ((([1] : List Sym) ^ m) +>
      ((0 : Sym) >> ((1 : Sym) >> ((0 : Sym) >> ((1 : Sym) >> encR R))))))

/-! ### Derived `step2` Raw-TM Lemmas -/

private theorem step_BR_nil (l : ListBlank Sym) (m : ℕ) (hm : 3 ≤ m) :
    (BR l m []) [TM]⊢⁺ BL l [m - 2, 1, 1] := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have h0 : BR l (k + 3) [] = B0 (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 3))) [] := rfl
  rw [h0]
  simpa [bumpR] using rule_B0_1m l k []

private theorem step_BR_1 (l : ListBlank Sym) (m : ℕ) (hm : 2 ≤ m) (Rr : List ℕ) :
    (BR l m (1 :: Rr)) [TM]⊢⁺ BL l ((m - 1) :: bumpR Rr 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have h1 := sweep_B1 1 (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 2))) (encR Rr)
  have hk : k + 2 - 1 = k + 1 := by omega
  rw [hk]
  exact ReachesStar.trans_plus h1 (rule_B0_01_1m l k Rr)

private theorem step_BR_2 (l : ListBlank Sym) (m : ℕ) (Rr : List ℕ) :
    (BR l m (2 :: Rr)) [TM]⊢⁺ BR l (m + 3) Rr := by
  have h1 := sweep_B1 2 (((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) (encR Rr)
  rw [pow2_lb] at h1
  have h2 := rule_B0_z2 (((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) Rr
  rw [append_pow_add] at h2
  exact ReachesStar.trans_plus h1 h2

private theorem step_BR_ge3 (l : ListBlank Sym) (m d : ℕ) (Rr : List ℕ) :
    (BR l m ((d + 3) :: Rr)) [TM]⊢⁺
      BR ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ d)) 3 Rr := by
  have h1 := sweep_B1 (d + 3) (((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) (encR Rr)
  have hl : ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ (d + 3))) =
      (0 : Sym) >> ((0 : Sym) >>
          ((0 : Sym) >>
          (((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ d))))) := by
    rw [← append_pow_add]
    rfl
  rw [hl] at h1
  exact ReachesStar.trans_plus h1 (rule_B0_z2 _ Rr)

private theorem step_BL_empty (R : List ℕ) :
    (BL default R) [TM]⊢⁺ BR default 3 R := by
  have h0 : BL default R = B0 ((0 : Sym) >> ((0 : Sym) >> (default : ListBlank Sym))) R := by
    rw [← BL_zero, cons_zero_def, cons_zero_def, cons_zero_def]
  rw [h0]
  unfold BR
  have hdef : (default : ListBlank Sym) <+ ([0] : List Sym) = default := cons_zero_def
  rw [hdef]
  exact rule_B0_z2 default R

private theorem step_BL_z1_1 (l : ListBlank Sym) (m : ℕ) (hm : 2 ≤ m) (Rr : List ℕ) :
    (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ 0)) (1 :: Rr)) [TM]⊢⁺
      BR l (m + 2) Rr := by
  rw [pow0_lb]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have h1 : (BL (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 2))) (1 :: Rr)) [TM]⊢
      (((0 : Sym) >> (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1)))) {{sB}}> encR (1 :: Rr)) :=
    step_B1_L (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1))) (encR (1 :: Rr))
  have h2 := sweep_B1 1 ((0 : Sym) >> (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1)))) (encR Rr)
  rw [pow1_lb] at h2
  have h3 := rule_B0_z2 (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1))) Rr
  rw [append_pow_add] at h3
  have hk : k + 1 + 3 = k + 2 + 2 := by omega
  rw [hk] at h3
  exact ReachesPlus.head h1 (ReachesStar.trans h2 (ReachesPlus.to_star h3))

private theorem step_BL_z1_ge2 (l : ListBlank Sym) (m d : ℕ) (hm : 2 ≤ m) (Rr : List ℕ) :
    (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ 0)) ((d + 2) ::
        Rr)) [TM]⊢⁺
      BR ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ (m - 1))) <+ (([0] : List Sym) ^ d)) 3 Rr := by
  rw [pow0_lb]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have h1 : (BL (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 2))) ((d + 2) :: Rr)) [TM]⊢
      (((0 : Sym) >> (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1)))) {{sB}}> encR ((d + 2) ::
          Rr)) :=
    step_B1_L (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1))) (encR ((d + 2) :: Rr))
  have h2 :=
      sweep_B1 (d + 2) ((0 : Sym) >> (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1)))) (encR Rr)
  have hl :
      ((0 : Sym) >>
      (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1)))) <+ (([0] : List Sym) ^ (d + 2)) =
      (0 : Sym) >> ((0 : Sym) >>
          ((0 : Sym) >>
          ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1))) <+ (([0] : List Sym) ^ d)))) := by
    have h1a : (0 : Sym) >> (((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1))) =
        ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1))) <+ (([0] : List Sym) ^ 1)) := rfl
    rw [h1a, append_pow_add]
    have hadd : 1 + (d + 2) = d + 3 := by omega
    rw [hadd, ← append_pow_add]
    rfl
  rw [hl] at h2
  have h3 :=
      rule_B0_z2
      ((0 : Sym) >>
      ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ (k + 1))) <+ (([0] : List Sym) ^ d))) Rr
  have hm1 : k + 2 - 1 = k + 1 := by omega
  rw [hm1]
  exact ReachesPlus.head h1 (ReachesStar.trans h2 (ReachesPlus.to_star h3))

private theorem step_BL_z1_m1 (l' : ListBlank Sym) (d : ℕ) (Rr : List ℕ) :
    (BL ((((0 : Sym) >> l') <+ (([1] : List Sym) ^ 1)) <+ (([0] : List Sym) ^ 0)) ((d + 1) ::
        Rr)) [TM]⊢⁺
      BR (l' <+ (([0] : List Sym) ^ d)) 3 Rr := by
  rw [pow0_lb, pow1_lb]
  have h1 : (BL ((1 : Sym) >> ((0 : Sym) >> l')) ((d + 1) :: Rr)) [TM]⊢
      (((0 : Sym) >> ((0 : Sym) >> l')) {{sB}}> encR ((d + 1) :: Rr)) :=
    step_B1_L ((0 : Sym) >> l') (encR ((d + 1) :: Rr))
  have h2 := sweep_B1 (d + 1) ((0 : Sym) >> ((0 : Sym) >> l')) (encR Rr)
  have hl : ((0 : Sym) >> ((0 : Sym) >> l')) <+ (([0] : List Sym) ^ (d + 1)) =
      (0 : Sym) >> ((0 : Sym) >> ((0 : Sym) >> (l' <+ (([0] : List Sym) ^ d)))) := by
    have h2a : (0 : Sym) >> ((0 : Sym) >> l') = l' <+ (([0] : List Sym) ^ 2) := rfl
    rw [h2a, append_pow_add]
    have hadd : 2 + (d + 1) = d + 3 := by omega
    rw [hadd, ← append_pow_add]
    rfl
  rw [hl] at h2
  exact ReachesPlus.head h1 (ReachesStar.trans h2 (ReachesPlus.to_star (rule_B0_z2 _ Rr)))

private theorem step_BL_z2 (l : ListBlank Sym) (m : ℕ) (hm : 3 ≤ m) (R : List ℕ) :
    (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ 1)) R) [TM]⊢⁺
      BL l ((m - 2) :: 1 :: bumpR R 1) := by
  rw [pow1_lb, BL_zero]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  simpa using rule_B0_1m l k R

private theorem step_BL_z3 (l : ListBlank Sym) (m : ℕ) (hm : 2 ≤ m) (R : List ℕ) :
    (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ 2)) R) [TM]⊢⁺
      BL l ((m - 1) :: bumpR R 3) := by
  rw [pow2_lb, BL_zero]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  simpa using rule_B0_01_1m l k R

private theorem step_BL_z4 (l : ListBlank Sym) (m : ℕ) (R : List ℕ) :
    (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ 3)) R) [TM]⊢⁺
      BR l (m + 3) R := by
  rw [pow3_lb, BL_zero]
  have h := rule_B0_z2 (((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) R
  rw [append_pow_add] at h
  exact h

private theorem step_BL_zge5 (l : ListBlank Sym) (m z : ℕ) (R : List ℕ) :
    (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ (z + 4))) R) [TM]⊢⁺
      BR ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ z)) 3 R := by
  have hl : ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ (z + 4))) =
      (0 : Sym) >> ((0 : Sym) >>
          ((0 : Sym) >>
          ((0 : Sym) >>
          ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ z))))) := by
    rw [← append_pow_add]
    rfl
  rw [hl, BL_zero]
  exact rule_B0_z2 _ R

/-! ### Four Concrete Multi-Step Base Rules (`rule_41`, `rule_43511`, `rule_436511`, `rule_66511`)
-/

private theorem rule_41 (l : ListBlank Sym) (m : ℕ) (hm : 3 ≤ m) (R : List ℕ) :
    (BR l m (4 :: 1 :: R)) [TM]⊢⁺ BL l ((m - 2) :: 1 :: 3 :: bumpR R 3) := by
  refine ReachesPlus.trans (step_BR_ge3 l m 1 (1 :: R)) ?_
  refine ReachesPlus.trans (step_BR_1 _ 3 (by omega) R) ?_
  simpa [bumpR] using step_BL_z2 l m hm (2 :: bumpR R 3)

private theorem rule_43511 (l : ListBlank Sym) (m : ℕ) (hm : 3 ≤ m) :
    (BR l m [4, 3, 5, 1, 1]) [TM]⊢⁺ BL l ((m - 2) :: 1 :: [3, 6, 5, 1, 1]) := by
  refine ReachesPlus.trans (step_BR_ge3 l m 1 [3, 5, 1, 1]) ?_
  refine ReachesPlus.trans (step_BR_ge3 _ 3 0 [5, 1, 1]) ?_
  refine ReachesPlus.trans (step_BR_ge3 _ 3 2 [1, 1]) ?_
  refine ReachesPlus.trans (step_BR_1 _ 3 (by omega) [1]) ?_
  refine ReachesPlus.trans (step_BL_z3 _ 3 (by omega) [2, 4]) ?_
  refine ReachesPlus.trans (step_BL_z1_ge2 _ 3 0 (by omega) [5, 4]) ?_
  refine ReachesPlus.trans (step_BR_ge3 _ 3 2 [4]) ?_
  refine ReachesPlus.trans (step_BR_ge3 _ 3 1 []) ?_
  refine ReachesPlus.trans (step_BR_nil _ 3 (by omega)) ?_
  refine ReachesPlus.trans (step_BL_z2 _ 3 (by omega) [1, 1, 1]) ?_
  refine ReachesPlus.trans (step_BL_z3 _ 3 (by omega) [1, 1, 2, 1, 1]) ?_
  refine ReachesPlus.trans (step_BL_z1_ge2 _ 2 0 (by omega) [4, 1, 2, 1, 1]) ?_
  refine ReachesPlus.trans (step_BR_ge3 _ 3 1 [1, 2, 1, 1]) ?_
  refine ReachesPlus.trans (step_BR_1 _ 3 (by omega) [2, 1, 1]) ?_
  refine ReachesPlus.trans (step_BL_z2 _ 3 (by omega) [2, 5, 1, 1]) ?_
  refine ReachesPlus.trans (step_BL_z1_m1 _ 0 [1, 3, 5, 1, 1]) ?_
  rw [pow0_lb]
  refine ReachesPlus.trans (step_BR_1 _ 3 (by omega) [3, 5, 1, 1]) ?_
  simpa [bumpR] using step_BL_z2 l m hm [2, 6, 5, 1, 1]

private theorem rule_436511 (l : ListBlank Sym) (m : ℕ) (hm : 3 ≤ m) :
    (BR l m [4, 3, 6, 5, 1, 1]) [TM]⊢⁺ BL l ((m - 2) :: 1 :: [2, 5, 4, 3, 5, 1, 1]) := by
  let l1 := (((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ 1)
  refine ReachesPlus.trans (step_BR_ge3 l m 1 [3, 6, 5, 1, 1]) ?_
  change (BR l1 3 [3, 6, 5, 1, 1]) [TM]⊢⁺ _
  refine ReachesPlus.trans (step_BR_ge3 l1 3 0 [6, 5, 1, 1]) ?_
  let l2 := (((0 : Sym) >> l1) <+ (([1] : List Sym) ^ 3)) <+ (([0] : List Sym) ^ 0)
  change (BR l2 3 [6, 5, 1, 1]) [TM]⊢⁺ _
  refine ReachesPlus.trans (step_BR_ge3 l2 3 3 [5, 1, 1]) ?_
  let l3 := (((0 : Sym) >> l2) <+ (([1] : List Sym) ^ 3)) <+ (([0] : List Sym) ^ 3)
  change (BR l3 3 [5, 1, 1]) [TM]⊢⁺ _
  refine ReachesPlus.trans (step_BR_ge3 l3 3 2 [1, 1]) ?_
  refine ReachesPlus.trans (step_BR_1 _ 3 (by omega) [1]) ?_
  refine ReachesPlus.trans (step_BL_z3 l3 3 (by omega) [2, 4]) ?_
  refine ReachesPlus.trans (step_BL_z4 l2 3 [2, 5, 4]) ?_
  refine ReachesPlus.trans (step_BR_2 l2 6 [5, 4]) ?_
  refine ReachesPlus.trans (step_BR_ge3 l2 9 2 [4]) ?_
  let l4 := (((0 : Sym) >> l2) <+ (([1] : List Sym) ^ 9)) <+ (([0] : List Sym) ^ 2)
  change (BR l4 3 [4]) [TM]⊢⁺ _
  refine ReachesPlus.trans (step_BR_ge3 l4 3 1 []) ?_
  refine ReachesPlus.trans (step_BR_nil _ 3 (by omega)) ?_
  refine ReachesPlus.trans (step_BL_z2 l4 3 (by omega) [1, 1, 1]) ?_
  refine ReachesPlus.trans (step_BL_z3 l2 9 (by omega) [1, 1, 2, 1, 1]) ?_
  refine ReachesPlus.trans (step_BL_z1_ge2 l1 3 6 (by omega) [4, 1, 2, 1, 1]) ?_
  let l5 := (((0 : Sym) >> l1) <+ (([1] : List Sym) ^ 2)) <+ (([0] : List Sym) ^ 6)
  change (BR l5 3 [4, 1, 2, 1, 1]) [TM]⊢⁺ _
  refine ReachesPlus.trans (rule_41 l5 3 (by omega) [2, 1, 1]) ?_
  refine ReachesPlus.trans (step_BL_zge5 l1 2 2 [1, 1, 3, 5, 1, 1]) ?_
  refine ReachesPlus.trans (step_BR_1 _ 3 (by omega) [1, 3, 5, 1, 1]) ?_
  refine ReachesPlus.trans (step_BL_z3 l1 2 (by omega) [2, 4, 3, 5, 1, 1]) ?_
  simpa [l1, bumpR] using step_BL_z2 l m hm [1, 5, 4, 3, 5, 1, 1]

private theorem rule_66511 (l : ListBlank Sym) :
    (BR l 3 [6, 6, 5, 1, 1]) [TM]⊢⁺ BL l [4, 1, 3, 4, 3, 5, 1, 1] := by
  let l1 := (((0 : Sym) >> l) <+ (([1] : List Sym) ^ 3)) <+ (([0] : List Sym) ^ 3)
  refine ReachesPlus.trans (step_BR_ge3 l 3 3 [6, 5, 1, 1]) ?_
  change (BR l1 3 [6, 5, 1, 1]) [TM]⊢⁺ _
  refine ReachesPlus.trans (step_BR_ge3 l1 3 3 [5, 1, 1]) ?_
  let l2 := (((0 : Sym) >> l1) <+ (([1] : List Sym) ^ 3)) <+ (([0] : List Sym) ^ 3)
  change (BR l2 3 [5, 1, 1]) [TM]⊢⁺ _
  refine ReachesPlus.trans (step_BR_ge3 l2 3 2 [1, 1]) ?_
  refine ReachesPlus.trans (step_BR_1 _ 3 (by omega) [1]) ?_
  refine ReachesPlus.trans (step_BL_z3 l2 3 (by omega) [2, 4]) ?_
  refine ReachesPlus.trans (step_BL_z4 l1 3 [2, 5, 4]) ?_
  refine ReachesPlus.trans (step_BR_2 l1 6 [5, 4]) ?_
  refine ReachesPlus.trans (step_BR_ge3 l1 9 2 [4]) ?_
  let l3 := (((0 : Sym) >> l1) <+ (([1] : List Sym) ^ 9)) <+ (([0] : List Sym) ^ 2)
  change (BR l3 3 [4]) [TM]⊢⁺ _
  refine ReachesPlus.trans (step_BR_ge3 l3 3 1 []) ?_
  refine ReachesPlus.trans (step_BR_nil _ 3 (by omega)) ?_
  refine ReachesPlus.trans (step_BL_z2 l3 3 (by omega) [1, 1, 1]) ?_
  refine ReachesPlus.trans (step_BL_z3 l1 9 (by omega) [1, 1, 2, 1, 1]) ?_
  refine ReachesPlus.trans (step_BL_z4 l 3 [8, 4, 1, 2, 1, 1]) ?_
  refine ReachesPlus.trans (step_BR_ge3 l 6 5 [4, 1, 2, 1, 1]) ?_
  let l4 := (((0 : Sym) >> l) <+ (([1] : List Sym) ^ 6)) <+ (([0] : List Sym) ^ 5)
  change (BR l4 3 [4, 1, 2, 1, 1]) [TM]⊢⁺ _
  refine ReachesPlus.trans (rule_41 l4 3 (by omega) [2, 1, 1]) ?_
  refine ReachesPlus.trans (step_BL_zge5 l 6 1 [1, 1, 3, 5, 1, 1]) ?_
  refine ReachesPlus.trans (step_BR_1 _ 3 (by omega) [1, 3, 5, 1, 1]) ?_
  simpa [bumpR] using step_BL_z2 l 6 (by omega) [2, 4, 3, 5, 1, 1]

/-! ## Executable `stepM` Bootstrap from `init []` to `BL default R0` -/

private inductive ModeM
  | br
  | bl
  | b0
  deriving DecidableEq

private def encL : List (Bool × ℕ) → ListBlank Sym
  | [] => default
  | (false, k) :: Ls => encL Ls <+ (([0] : List Sym) ^ k)
  | (true, k) :: Ls => encL Ls <+ (([1] : List Sym) ^ k)

private def encM : ModeM × List (Bool × ℕ) × List ℕ → Cfg Sym State
  | (.br, L, R) => encL L {{sB}}> encR R
  | (.bl, L, R) => encL L <{{sB}} encR R
  | (.b0, L, R) => B0 (encL L) R

private def pushL (L : List (Bool × ℕ)) (b : Bool) (k : ℕ) : List (Bool × ℕ) :=
  match k with
  | 0 => L
  | k' + 1 =>
    match L with
    | [] => if b then [(true, k' + 1)] else []
    | (b0, k0) :: Lr =>
      if b0 = b then (b, k0 + (k' + 1)) :: Lr else (b, k' + 1) :: (b0, k0) :: Lr

private theorem encL_pushL (L : List (Bool × ℕ)) (b : Bool) (k : ℕ) :
    encL (pushL L b k) = encL L <+ (([if b then (1 : Sym) else 0] : List Sym) ^ k) := by
  cases k with
  | zero => rfl
  | succ k' =>
    cases L with
    | nil =>
      cases b with
      | false =>
        simp only [pushL, Bool.false_eq_true, ↓reduceIte, encL]
        exact (append_zeros_def (k' + 1)).symm
      | true =>
        simp [pushL, encL]
    | cons hd tl =>
      rcases hd with ⟨b0, k0⟩
      cases b0 <;> cases b <;>
        simp [pushL, encL, append_pow_add]

private def stepM : ModeM × List (Bool × ℕ) × List ℕ → Option (ModeM × List (Bool × ℕ) × List ℕ)
  | (.br, L, []) => some (.b0, L, [])
  | (.br, L, d :: Rr) => some (.b0, pushL L false d, Rr)
  | (.bl, [], R) => some (.b0, [], R)
  | (.bl, (false, k + 1) :: Lr, R) =>
      some (.b0, if k = 0 then Lr else (false, k) :: Lr, R)
  | (.bl, (true, k + 1) :: Lr, R) =>
      some (.br, pushL (if k = 0 then Lr else (true, k) :: Lr) false 1, R)
  | (.b0, [], R) => some (.br, [(true, 3)], R)
  | (.b0, (false, k + 2) :: Lr, R) =>
      some (.br, pushL (if k = 0 then Lr else (false, k) :: Lr) true 3, R)
  | (.b0, (false, 1) :: (true, m + 2) :: [], R) =>
      some (.bl, [], (m + 1) :: bumpR R 3)
  | (.b0, (false, 1) :: (true, m + 2) :: (false, z + 1) :: L2, R) =>
      some (.bl, if z = 0 then L2 else (false, z) :: L2, (m + 1) :: bumpR R 3)
  | (.b0, (true, 1) :: [], R) =>
      some (.br, [(true, 2)], bumpR R 1)
  | (.b0, (true, 1) :: (false, z + 1) :: L2, R) =>
      some (.br, pushL (if z = 0 then L2 else (false, z) :: L2) true 2, bumpR R 1)
  | (.b0, (true, m + 3) :: [], R) =>
      some (.bl, [], (m + 1) :: 1 :: bumpR R 1)
  | (.b0, (true, m + 3) :: (false, z + 1) :: L2, R) =>
      some (.bl, if z = 0 then L2 else (false, z) :: L2, (m + 1) :: 1 :: bumpR R 1)
  | _ => none

private theorem encL_drop1_0 (z : ℕ) (L2 : List (Bool × ℕ)) :
    encL ((false, z + 1) :: L2) = (0 : Sym) >> encL (if z = 0 then L2 else (false, z) :: L2) := by
  cases z with
  | zero => rfl
  | succ z' => rfl

private theorem encL_drop1_1 (k : ℕ) (Lr : List (Bool × ℕ)) :
    encL ((true, k + 1) :: Lr) = (1 : Sym) >> encL (if k = 0 then Lr else (true, k) :: Lr) := by
  cases k with
  | zero => rfl
  | succ k' => rfl

private theorem encL_drop2_0 (k : ℕ) (Lr : List (Bool × ℕ)) :
    encL ((false, k + 2) :: Lr) =
      (0 : Sym) >> ((0 : Sym) >> encL (if k = 0 then Lr else (false, k) :: Lr)) := by
  cases k with
  | zero => rfl
  | succ k' => rfl

private theorem stepM_sound (s s' : ModeM × List (Bool × ℕ) × List ℕ)
    (h : stepM s = some s') : (encM s) [TM]⊢* encM s' := by
  rcases s with ⟨mode, L, R⟩
  cases mode with
  | br =>
    cases R with
    | nil =>
      simp only [stepM, Option.some.injEq] at h
      subst h
      exact ReachesStar.refl TM _
    | cons d Rr =>
      simp only [stepM, Option.some.injEq] at h
      subst h
      have hs := sweep_B1 d (encL L) (encR Rr)
      dsimp only [encM, B0, encR]
      rw [encL_pushL]
      exact hs
  | bl =>
    cases L with
    | nil =>
      simp only [stepM, Option.some.injEq] at h
      subst h
      exact ReachesStar.refl TM _
    | cons hd Lr =>
      rcases hd with ⟨b, k⟩
      cases b with
      | false =>
        cases k with
        | zero => simp [stepM] at h
        | succ k' =>
          simp only [stepM, Option.some.injEq] at h
          subst h
          have heq := encL_drop1_0 k' Lr
          simp only [encM, heq, ListBlank.head_cons, ListBlank.tail_cons]
          exact ReachesStar.refl TM _
      | true =>
        cases k with
        | zero => simp [stepM] at h
        | succ k' =>
          simp only [stepM, Option.some.injEq] at h
          subst h
          have heq := encL_drop1_1 k' Lr
          simp only [encM, heq, encL_pushL]
          exact ReachesStar.single (step_B1_L _ _)
  | b0 =>
    cases L with
    | nil =>
      simp only [stepM, Option.some.injEq] at h
      subst h
      have h0 :
          B0 (default : ListBlank Sym) R =
          B0 ((0 : Sym) >> ((0 : Sym) >> (default : ListBlank Sym))) R := by
        rw [cons_zero_def, cons_zero_def]
      simpa [encM, encL, h0] using ReachesPlus.to_star (rule_B0_z2 default R)
    | cons hd Lr =>
      rcases hd with ⟨b, k⟩
      cases b with
      | false =>
        cases k with
        | zero => simp [stepM] at h
        | succ k1 =>
          cases k1 with
          | zero =>
            cases Lr with
            | nil => simp [stepM] at h
            | cons hd2 L2 =>
              rcases hd2 with ⟨b2, m⟩
              cases b2 with
              | false => simp [stepM] at h
              | true =>
                cases m with
                | zero => simp [stepM] at h
                | succ m1 =>
                  cases m1 with
                  | zero => simp [stepM] at h
                  | succ m2 =>
                    cases L2 with
                    | nil =>
                      simp only [stepM, Option.some.injEq] at h
                      subst h
                      have hdef : (0 : Sym) >> (default : ListBlank Sym) = default := cons_zero_def
                      have hrule := rule_B0_01_1m default m2 R
                      rw [hdef] at hrule
                      exact ReachesPlus.to_star hrule
                    | cons hd3 L3 =>
                      rcases hd3 with ⟨b3, z⟩
                      cases b3 with
                      | true => simp [stepM] at h
                      | false =>
                        cases z with
                        | zero => simp [stepM] at h
                        | succ z' =>
                          simp only [stepM, Option.some.injEq] at h
                          subst h
                          have heq := encL_drop1_0 z' L3
                          have hrule :=
                              rule_B0_01_1m (encL (if z' = 0 then L3 else (false, z') :: L3)) m2 R
                          dsimp only [encM]
                          have hl : encL ((false, 1) :: (true, m2 + 2) :: (false, z' + 1) :: L3) =
                              (0 : Sym) >> (((0 : Sym) >> encL (if z' = 0 then L3 else (false,
                                  z') :: L3)) <+ (([1] : List Sym) ^ (m2 + 2))) := by
                            change ((encL ((false,
                                z' + 1) :: L3) <+
                                (([1] : List Sym) ^ (m2 + 2))) <+ (([0] : List Sym) ^ 1)) = _
                            rw [heq, pow1_lb]
                          rw [hl]
                          exact ReachesPlus.to_star hrule
          | succ k2 =>
            simp only [stepM, Option.some.injEq] at h
            subst h
            have heq := encL_drop2_0 k2 Lr
            have hrule := rule_B0_z2 (encL (if k2 = 0 then Lr else (false, k2) :: Lr)) R
            simpa [encM, encL_pushL, heq] using ReachesPlus.to_star hrule
      | true =>
        cases k with
        | zero => simp [stepM] at h
        | succ k1 =>
          cases k1 with
          | zero =>
            cases Lr with
            | nil =>
              simp only [stepM, Option.some.injEq] at h
              subst h
              have hdef : (0 : Sym) >> (default : ListBlank Sym) = default := cons_zero_def
              have hrule := rule_B0_11 default R
              rw [hdef] at hrule
              exact ReachesPlus.to_star hrule
            | cons hd2 L2 =>
              rcases hd2 with ⟨b2, z⟩
              cases b2 with
              | true => simp [stepM] at h
              | false =>
                cases z with
                | zero => simp [stepM] at h
                | succ z' =>
                  simp only [stepM, Option.some.injEq] at h
                  subst h
                  have heq := encL_drop1_0 z' L2
                  have hrule := rule_B0_11 (encL (if z' = 0 then L2 else (false, z') :: L2)) R
                  dsimp only [encM]
                  rw [encL_pushL]
                  have hl : encL ((true, 1) :: (false, z' + 1) :: L2) =
                      (1 : Sym) >> ((0 : Sym) >> encL (if z' = 0 then L2 else (false, z') :: L2)) :=
                          by
                    change (encL ((false, z' + 1) :: L2) <+ (([1] : List Sym) ^ 1)) = _
                    rw [heq, pow1_lb]
                  rw [hl]
                  exact ReachesPlus.to_star hrule
          | succ k2 =>
            cases k2 with
            | zero => simp [stepM] at h
            | succ k3 =>
              cases Lr with
              | nil =>
                simp only [stepM, Option.some.injEq] at h
                subst h
                have hdef : (0 : Sym) >> (default : ListBlank Sym) = default := cons_zero_def
                have hrule := rule_B0_1m default k3 R
                rw [hdef] at hrule
                exact ReachesPlus.to_star hrule
              | cons hd2 L2 =>
                rcases hd2 with ⟨b2, z⟩
                cases b2 with
                | true => simp [stepM] at h
                | false =>
                  cases z with
                  | zero => simp [stepM] at h
                  | succ z' =>
                    simp only [stepM, Option.some.injEq] at h
                    subst h
                    have heq := encL_drop1_0 z' L2
                    have hrule := rule_B0_1m (encL (if z' = 0 then L2 else (false, z') :: L2)) k3 R
                    dsimp only [encM]
                    have hl : encL ((true, k3 + 3) :: (false, z' + 1) :: L2) =
                        ((0 : Sym) >> encL (if z' = 0 then L2 else (false,
                            z') :: L2)) <+ (([1] : List Sym) ^ (k3 + 3)) := by
                      change (encL ((false, z' + 1) :: L2) <+ (([1] : List Sym) ^ (k3 + 3))) = _
                      rw [heq]
                    rw [hl]
                    exact ReachesPlus.to_star hrule

private def runStepM :
    ℕ → ModeM × List (Bool × ℕ) × List ℕ → Option (ModeM × List (Bool × ℕ) × List ℕ)
  | 0, s => some s
  | n + 1, s => (stepM s).bind (runStepM n)

private theorem runStepM_sound (n : ℕ) (s s' : ModeM × List (Bool × ℕ) × List ℕ)
    (h : runStepM n s = some s') : (encM s) [TM]⊢* encM s' := by
  induction n generalizing s with
  | zero =>
    simp only [runStepM, Option.some.injEq] at h
    subst h
    exact ReachesStar.refl TM _
  | succ n ih =>
    simp only [runStepM] at h
    cases hs : stepM s with
    | none => simp [hs] at h
    | some s1 =>
      rw [hs, Option.bind_some] at h
      exact ReachesStar.trans (stepM_sound s s1 hs) (ih s1 h)

private def R0 : List ℕ :=
  [4, 1, 5, 6, 4, 1, 5, 6, 5, 5, 4, 1, 3, 6, 8, 4, 5, 6, 6, 4, 1, 3, 6, 6, 5, 5,
   4, 3, 9, 8, 4, 5, 4, 6, 4, 3, 6, 6, 5, 1, 1]

private theorem init_reaches_R0 : (init ([] : List Sym)) [TM]⊢* BL default R0 := by
  have h1 : (init ([] : List Sym)) [TM]⊢ encM (.b0, [(true, 1)], []) := rfl
  have h2 : runStepM 3884 (.b0, [(true, 1)], []) = some (.bl, [], R0) := by decide +kernel
  exact ReachesStar.head h1 (runStepM_sound 3884 _ _ h2)

/-! ## Exact Right-Tape Grammar and Return Shapes -/

private inductive GramTag
  | valid
  | post41
  | post41Out
  | rareT
  | body2T

private inductive Gram : GramTag → List ℕ → Prop
  -- ValidR := 4 · 1? · Post41
  | v4 {R} : Gram .post41 R → Gram .valid (4 :: R)
  | v41 {R} : Gram .post41 R → Gram .valid (4 :: 1 :: R)
  -- Post41 := [3, 5, 1, 1] | Post41Out
  | p_end0 : Gram .post41 [3, 5, 1, 1]
  | p_out {R} : Gram .post41Out R → Gram .post41 R
  -- Post41Out
  | po_end1 : Gram .post41Out [3, 6, 5, 1, 1]
  | po_3 {R} : Gram .body2T R → Gram .post41Out (3 :: R)
  | po_5 {R} : Gram .body2T R → Gram .post41Out (5 :: R)
  | po_6 {R} : Gram .rareT R → Gram .post41Out (6 :: R)
  | po_8 {R} : Gram .rareT R → Gram .post41Out (8 :: R)
  | po_25 {R} : Gram .rareT R → Gram .post41Out (2 :: 5 :: R)
  | po_213 {R} : Gram .rareT R → Gram .post41Out (2 :: 1 :: 3 :: R)
  | po_413 {R} : Gram .rareT R → Gram .post41Out (4 :: 1 :: 3 :: R)
  -- RareTail := {6, 8}^* · ValidR
  | rt_v {R} : Gram .valid R → Gram .rareT R
  | rt_6 {R} : Gram .rareT R → Gram .rareT (6 :: R)
  | rt_8 {R} : Gram .rareT R → Gram .rareT (8 :: R)
  -- Body2Tail := {6, 8}^* · (RareTail | RareAtom · RareTail | [6, 6, 5, 1, 1])
  | bt_rt {R} : Gram .rareT R → Gram .body2T R
  | bt_end2 : Gram .body2T [6, 6, 5, 1, 1]
  | bt_9 {R} : Gram .rareT R → Gram .body2T (9 :: R)
  | bt_11 {R} : Gram .rareT R → Gram .body2T (11 :: R)
  | bt_55 {R} : Gram .rareT R → Gram .body2T (5 :: 5 :: R)
  | bt_513 {R} : Gram .rareT R → Gram .body2T (5 :: 1 :: 3 :: R)
  | bt_713 {R} : Gram .rareT R → Gram .body2T (7 :: 1 :: 3 :: R)
  | bt_6 {R} : Gram .body2T R → Gram .body2T (6 :: R)
  | bt_8 {R} : Gram .body2T R → Gram .body2T (8 :: R)

private abbrev ValidR := Gram .valid
private abbrev Post41Out := Gram .post41Out
private abbrev RareTail := Gram .rareT
private abbrev Body2Tail := Gram .body2T

private theorem bumpR_post41Out {R : List ℕ} (h : Post41Out R) : Body2Tail (bumpR R 3) := by
  cases h with
  | po_end1 => exact Gram.bt_end2
  | po_3 h => exact Gram.bt_6 h
  | po_5 h => exact Gram.bt_8 h
  | po_6 h => exact Gram.bt_9 h
  | po_8 h => exact Gram.bt_11 h
  | po_25 h => exact Gram.bt_55 h
  | po_213 h => exact Gram.bt_513 h
  | po_413 h => exact Gram.bt_713 h

private theorem R0_valid : ValidR R0 := by
  unfold R0
  exact Gram.v41 (Gram.p_out (Gram.po_5 (Gram.bt_6 (Gram.bt_rt (Gram.rt_v (
    Gram.v41 (Gram.p_out (Gram.po_5 (Gram.bt_6 (Gram.bt_55 (Gram.rt_v (
    Gram.v41 (Gram.p_out (Gram.po_3 (Gram.bt_6 (Gram.bt_8 (Gram.bt_rt (Gram.rt_v (
    Gram.v4 (Gram.p_out (Gram.po_5 (Gram.bt_6 (Gram.bt_6 (Gram.bt_rt (Gram.rt_v (
    Gram.v41 (Gram.p_out (Gram.po_3 (Gram.bt_6 (Gram.bt_6 (Gram.bt_55 (Gram.rt_v (
    Gram.v4 (Gram.p_out (Gram.po_3 (Gram.bt_9 (Gram.rt_8 (Gram.rt_v (
    Gram.v4 (Gram.p_out (Gram.po_5 (Gram.bt_rt (Gram.rt_v (
    Gram.v4 (Gram.p_out (Gram.po_6 (Gram.rt_v (
    Gram.v4 (Gram.p_out (Gram.po_3 Gram.bt_end2))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The 3 return shapes of `RareTail`. -/
private inductive RareRet : List ℕ → Prop
  | r11 {T} : Post41Out T → RareRet (1 :: 1 :: T)
  | r5 {V} : ValidR V → RareRet (5 :: V)
  | r113 {V} : ValidR V → RareRet (1 :: 1 :: 3 :: V)

/-- The 9 return shapes of `Body2Tail`. -/
private inductive Body2Ret : List ℕ → Prop
  | b11 {T} : Post41Out T → Body2Ret (1 :: 1 :: T)
  | b5 {B} : Body2Tail B → Body2Ret (5 :: B)
  | b113 {B} : Body2Tail B → Body2Ret (1 :: 1 :: 3 :: B)
  | b15 {B} : Body2Tail B → Body2Ret (1 :: 5 :: B)
  | b25 {Rt} : RareTail Rt → Body2Ret (2 :: 5 :: Rt)
  | b11213 {Rt} : RareTail Rt → Body2Ret (1 :: 1 :: 2 :: 1 :: 3 :: Rt)
  | b413 {Rt} : RareTail Rt → Body2Ret (4 :: 1 :: 3 :: Rt)
  | b8 {Rt} : RareTail Rt → Body2Ret (8 :: Rt)
  | b116 {Rt} : RareTail Rt → Body2Ret (1 :: 1 :: 6 :: Rt)

private theorem rareRet_to_body2Ret {R : List ℕ} (h : RareRet R) : Body2Ret R := by
  cases h with
  | r11 hT => exact Body2Ret.b11 hT
  | r5 hV => exact Body2Ret.b5 (Gram.bt_rt (Gram.rt_v hV))
  | r113 hV => exact Body2Ret.b113 (Gram.bt_rt (Gram.rt_v hV))

private theorem bumpR_rareRet {R : List ℕ} (h : RareRet R) : RareTail (bumpR R 3) := by
  cases h with
  | r11 hT => exact Gram.rt_v (Gram.v41 (Gram.p_out hT))
  | r5 hV => exact Gram.rt_8 (Gram.rt_v hV)
  | r113 hV => exact Gram.rt_v (Gram.v41 (Gram.p_out (Gram.po_3 (Gram.bt_rt (Gram.rt_v hV)))))

private theorem bumpR_body2Ret {R : List ℕ} (h : Body2Ret R) : Body2Tail (bumpR R 3) := by
  cases h with
  | b11 hT => exact Gram.bt_rt (Gram.rt_v (Gram.v41 (Gram.p_out hT)))
  | b5 hB => exact Gram.bt_8 hB
  | b113 hB => exact Gram.bt_rt (Gram.rt_v (Gram.v41 (Gram.p_out (Gram.po_3 hB))))
  | b15 hB => exact Gram.bt_rt (Gram.rt_v (Gram.v4 (Gram.p_out (Gram.po_5 hB))))
  | b25 hRt => exact Gram.bt_55 hRt
  | b11213 hRt => exact Gram.bt_rt (Gram.rt_v (Gram.v41 (Gram.p_out (Gram.po_213 hRt))))
  | b413 hRt => exact Gram.bt_713 hRt
  | b8 hRt => exact Gram.bt_11 hRt
  | b116 hRt => exact Gram.bt_rt (Gram.rt_v (Gram.v41 (Gram.p_out (Gram.po_6 hRt))))

/-! ## Strong Induction on Raw TM Step Budget `N` -/

private def PValid (N : ℕ) : Prop :=
  ∀ l m R, 3 ≤ m → ValidR R →
    SafeRet N l (BR l m R) (fun R' => ∃ T, Post41Out T ∧ R' = (m - 2) :: 1 :: T)

private def PRare (N : ℕ) : Prop :=
  ∀ l R, RareTail R → SafeRet N l (BR l 3 R) RareRet

private def PBody2 (N : ℕ) : Prop :=
  ∀ l R, Body2Tail R → SafeRet N l (BR l 3 R) Body2Ret

/-- Parameterized `z = 4` wrapper on `RareRet` (`m ≥ 2`): returns `(m + 2) :: V` with `ValidR V`. -/
private theorem wrap_z4_rare {N : ℕ} (ihV : ∀ k < N, PValid k)
    (l : ListBlank Sym) (m : ℕ) (hm : 2 ≤ m) {R : List ℕ} (hR : RareRet R) :
    SafeRet N l (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ 3)) R)
      (fun R' => ∃ V, ValidR V ∧ R' = (m + 2) :: V) := by
  cases hR with
  | r11 hT =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 _ => ?_)
    exact SafeRet.done_plus (step_BR_1 l (m + 3) (by omega) _)
      ⟨4 :: _, Gram.v4 (Gram.p_out hT), by simp [bumpR]⟩
  | r5 hV =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 hN1 => ?_)
    refine SafeRet.step_plus (step_BR_ge3 l (m + 3) 2 _) (fun N2 hN2 => ?_)
    refine SafeRet.bind (ihV N2 (by omega) _ 3 _ (by omega) hV) (fun N3 _ _ ⟨T, hT, hEq⟩ => ?_)
    subst hEq
    exact SafeRet.done_plus (step_BL_z3 l (m + 3) (by omega) _)
      ⟨4 :: 1 :: T, Gram.v41 (Gram.p_out hT), by simp [bumpR]⟩
  | r113 hV =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 _ => ?_)
    exact SafeRet.done_plus (step_BR_1 l (m + 3) (by omega) _)
      ⟨4 :: 3 :: _, Gram.v4 (Gram.p_out (Gram.po_3 (Gram.bt_rt (Gram.rt_v hV)))), by simp [bumpR]⟩

/-- Parameterized `z = 6` wrapper on `RareRet` (`m ≥ 3`): returns `(m - 2) :: 1 :: 3 :: V`. -/
private theorem wrap_z6_rare {N : ℕ} (ihV : ∀ k < N, PValid k)
    (l : ListBlank Sym) (m : ℕ) (hm : 3 ≤ m) {R : List ℕ} (hR : RareRet R) :
    SafeRet N l (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ 5)) R)
      (fun R' => ∃ V, ValidR V ∧ R' = (m - 2) :: 1 :: 3 :: V) := by
  cases hR with
  | r11 hT =>
    refine SafeRet.step_plus (step_BL_zge5 l m 1 _) (fun N1 _ => ?_)
    refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N2 _ => ?_)
    exact SafeRet.done_plus (step_BL_z2 l m hm _)
      ⟨4 :: _, Gram.v4 (Gram.p_out hT), by simp [bumpR]⟩
  | r5 hV =>
    refine SafeRet.step_plus (step_BL_zge5 l m 1 _) (fun N1 hN1 => ?_)
    refine SafeRet.step_plus (step_BR_ge3 _ 3 2 _) (fun N2 hN2 => ?_)
    refine SafeRet.bind (ihV N2 (by omega) _ 3 _ (by omega) hV) (fun N3 _ _ ⟨T, hT, hEq⟩ => ?_)
    subst hEq
    refine SafeRet.step_plus (step_BL_z3 _ 3 (by omega) _) (fun N4 _ => ?_)
    exact SafeRet.done_plus (step_BL_z2 l m hm _)
      ⟨4 :: 1 :: T, Gram.v41 (Gram.p_out hT), by simp [bumpR]⟩
  | r113 hV =>
    refine SafeRet.step_plus (step_BL_zge5 l m 1 _) (fun N1 _ => ?_)
    refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N2 _ => ?_)
    exact SafeRet.done_plus (step_BL_z2 l m hm _)
      ⟨4 :: 3 :: _, Gram.v4 (Gram.p_out (Gram.po_3 (Gram.bt_rt (Gram.rt_v hV)))), by simp [bumpR]⟩

/-- Parameterized `z = 7` wrapper on `RareRet` (`m ≥ 2`): returns `(m - 1) :: 5 :: V`. -/
private theorem wrap_z7_rare {N : ℕ} (ihV : ∀ k < N, PValid k)
    (l : ListBlank Sym) (m : ℕ) (hm : 2 ≤ m) {R : List ℕ} (hR : RareRet R) :
    SafeRet N l (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ 6)) R)
      (fun R' => ∃ V, ValidR V ∧ R' = (m - 1) :: 5 :: V) := by
  cases hR with
  | r11 hT =>
    refine SafeRet.step_plus (step_BL_zge5 l m 2 _) (fun N1 _ => ?_)
    refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N2 _ => ?_)
    exact SafeRet.done_plus (step_BL_z3 l m hm _)
      ⟨4 :: _, Gram.v4 (Gram.p_out hT), by simp [bumpR]⟩
  | r5 hV =>
    refine SafeRet.step_plus (step_BL_zge5 l m 2 _) (fun N1 hN1 => ?_)
    refine SafeRet.step_plus (step_BR_ge3 _ 3 2 _) (fun N2 hN2 => ?_)
    refine SafeRet.bind (ihV N2 (by omega) _ 3 _ (by omega) hV) (fun N3 _ _ ⟨T, hT, hEq⟩ => ?_)
    subst hEq
    refine SafeRet.step_plus (step_BL_z3 _ 3 (by omega) _) (fun N4 _ => ?_)
    exact SafeRet.done_plus (step_BL_z3 l m hm _)
      ⟨4 :: 1 :: T, Gram.v41 (Gram.p_out hT), by simp [bumpR]⟩
  | r113 hV =>
    refine SafeRet.step_plus (step_BL_zge5 l m 2 _) (fun N1 _ => ?_)
    refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N2 _ => ?_)
    exact SafeRet.done_plus (step_BL_z3 l m hm _)
      ⟨4 :: 3 :: _, Gram.v4 (Gram.p_out (Gram.po_3 (Gram.bt_rt (Gram.rt_v hV)))), by simp [bumpR]⟩

/-- Return predicate for `wrap_z4_body2`: parameterized by `m ≥ 2`. -/
private inductive Z4BodyRet (m : ℕ) : List ℕ → Prop
  | z4_body {B} : Body2Tail B → Z4BodyRet m ((m + 2) :: B)
  | z4_rare {Rt} : RareTail Rt → Z4BodyRet m ((m + 5) :: Rt)
  | z4_13 {Rt} : RareTail Rt → Z4BodyRet m ((m + 1) :: 1 :: 3 :: Rt)

/-- Parameterized `z = 4` wrapper on `Body2Ret` (`m ≥ 2`): handles BOTH `d = 6` on `Body2Tail`
(`m = 3`) and `4 · 3 · Body2Tail` subcall `b5` (`m = 2`)! -/
private theorem wrap_z4_body2 {N : ℕ}
    (ihV : ∀ k < N, PValid k) (ihR : ∀ k < N, PRare k) (ihB : ∀ k < N, PBody2 k)
    (l : ListBlank Sym) (m : ℕ) (hm : 2 ≤ m) {R : List ℕ} (hR : Body2Ret R) :
    SafeRet N l (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ m)) <+ (([0] : List Sym) ^ 3)) R)
      (Z4BodyRet m) := by
  cases hR with
  | b11 hT =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 _ => ?_)
    exact SafeRet.done_plus (step_BR_1 l (m + 3) (by omega) _)
      (by simpa [bumpR] using Z4BodyRet.z4_body (m := m)
            (Gram.bt_rt (Gram.rt_v (Gram.v4 (Gram.p_out hT)))))
  | b5 hB =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 hN1 => ?_)
    refine SafeRet.step_plus (step_BR_ge3 l (m + 3) 2 _) (fun N2 hN2 => ?_)
    refine SafeRet.bind (ihB N2 (by omega) _ _ hB) (fun N3 _ Rsub hsub => ?_)
    exact SafeRet.done_plus (step_BL_z3 l (m + 3) (by omega) Rsub)
      (by simpa [bumpR] using Z4BodyRet.z4_body (m := m) (bumpR_body2Ret hsub))
    | b113 hB =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 _ => ?_)
    exact SafeRet.done_plus (step_BR_1 l (m + 3) (by omega) _)
      (by simpa [bumpR] using Z4BodyRet.z4_body (m := m)
            (Gram.bt_rt (Gram.rt_v (Gram.v4 (Gram.p_out (Gram.po_3 hB))))))
  | b15 hB =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 _ => ?_)
    exact SafeRet.done_plus (step_BR_1 l (m + 3) (by omega) _)
      (by simpa [bumpR] using Z4BodyRet.z4_body (m := m) (Gram.bt_8 hB))
    | b25 hRt =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 hN1 => ?_)
    refine SafeRet.step_plus (step_BR_2 l (m + 3) _) (fun N2 hN2 => ?_)
    refine SafeRet.step_plus (step_BR_ge3 l (m + 6) 2 _) (fun N3 hN3 => ?_)
    refine SafeRet.bind (ihR N3 (by omega) _ _ hRt) (fun N4 _ Rsub hsub => ?_)
    exact SafeRet.done_plus (step_BL_z3 l (m + 6) (by omega) Rsub)
      (by simpa [bumpR] using Z4BodyRet.z4_rare (m := m) (bumpR_rareRet hsub))
    | b11213 hRt =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 _ => ?_)
    exact SafeRet.done_plus (step_BR_1 l (m + 3) (by omega) _)
      (by simpa [bumpR] using Z4BodyRet.z4_body (m := m)
            (Gram.bt_rt (Gram.rt_v (Gram.v4 (Gram.p_out (Gram.po_213 hRt))))))
  | b413 hRt =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 _ => ?_)
    exact SafeRet.done_plus (rule_41 l (m + 3) (by omega) _)
      (by
        have hEq : m + 3 - 2 = m + 1 := by omega
        simpa [hEq, bumpR] using Z4BodyRet.z4_13 (m := m) (Gram.rt_6 hRt))
  | b8 hRt =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 hN1 => ?_)
    refine SafeRet.step_plus (step_BR_ge3 l (m + 3) 5 _) (fun N2 hN2 => ?_)
    refine SafeRet.bind (ihR N2 (by omega) _ _ hRt) (fun N3 hN3 Rsub hsub => ?_)
    refine SafeRet.mono_Q (wrap_z6_rare (fun k hk => ihV k (by omega)) l (m + 3) (by omega) hsub) ?_
    rintro R' ⟨V, hV, rfl⟩
    have hEq : m + 3 - 2 = m + 1 := by omega
    simpa [hEq] using Z4BodyRet.z4_13 (m := m) (Gram.rt_v hV)
  | b116 hRt =>
    refine SafeRet.step_plus (step_BL_z4 l m _) (fun N1 _ => ?_)
    exact SafeRet.done_plus (step_BR_1 l (m + 3) (by omega) _)
      (by simpa [bumpR] using Z4BodyRet.z4_body (m := m)
            (Gram.bt_rt (Gram.rt_v (Gram.v4 (Gram.p_out (Gram.po_6 hRt))))))

/-- Wrapper for `z = 6, m = 3` on `Body2Ret` (for `d = 8` on `Body2Tail`). -/
private theorem wrap_z6_body2 {N : ℕ}
    (ihV : ∀ k < N, PValid k) (ihR : ∀ k < N, PRare k) (ihB : ∀ k < N, PBody2 k)
    (l : ListBlank Sym) {R : List ℕ} (hR : Body2Ret R) :
    SafeRet N l (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ 3)) <+ (([0] : List Sym) ^ 5)) R)
      Body2Ret := by
  cases hR with
  | b11 hT =>
    refine SafeRet.step_plus (step_BL_zge5 l 3 1 _) (fun N1 _ => ?_)
    refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N2 _ => ?_)
    exact SafeRet.done_plus (step_BL_z2 l 3 (by omega) _)
      (by simpa [bumpR] using Body2Ret.b113 (Gram.bt_rt (Gram.rt_v (Gram.v4 (Gram.p_out hT)))))
    | b5 hB =>
    refine SafeRet.step_plus (step_BL_zge5 l 3 1 _) (fun N1 hN1 => ?_)
    refine SafeRet.step_plus (step_BR_ge3 _ 3 2 _) (fun N2 hN2 => ?_)
    refine SafeRet.bind (ihB N2 (by omega) _ _ hB) (fun N3 _ Rsub hsub => ?_)
    refine SafeRet.step_plus (step_BL_z3 _ 3 (by omega) Rsub) (fun N4 _ => ?_)
    exact SafeRet.done_plus (step_BL_z2 l 3 (by omega) _)
      (by simpa [bumpR] using Body2Ret.b113 (bumpR_body2Ret hsub))
    | b113 hB =>
    refine SafeRet.step_plus (step_BL_zge5 l 3 1 _) (fun N1 _ => ?_)
    refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N2 _ => ?_)
    exact SafeRet.done_plus (step_BL_z2 l 3 (by omega) _)
      (by simpa [bumpR] using Body2Ret.b113
            (Gram.bt_rt (Gram.rt_v (Gram.v4 (Gram.p_out (Gram.po_3 hB))))))
  | b15 hB =>
    refine SafeRet.step_plus (step_BL_zge5 l 3 1 _) (fun N1 _ => ?_)
    refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N2 _ => ?_)
    exact SafeRet.done_plus (step_BL_z2 l 3 (by omega) _)
      (by simpa [bumpR] using Body2Ret.b113 (Gram.bt_8 hB))
    | b25 hRt =>
    refine SafeRet.step_plus (step_BL_zge5 l 3 1 _) (fun N1 hN1 => ?_)
    refine SafeRet.step_plus (step_BR_2 _ 3 _) (fun N2 hN2 => ?_)
    refine SafeRet.step_plus (step_BR_ge3 _ 6 2 _) (fun N3 hN3 => ?_)
    refine SafeRet.bind (ihR N3 (by omega) _ _ hRt) (fun N4 _ Rsub hsub => ?_)
    refine SafeRet.step_plus (step_BL_z3 _ 6 (by omega) Rsub) (fun N5 _ => ?_)
    exact SafeRet.done_plus (step_BL_z2 l 3 (by omega) _)
      (by simpa [bumpR] using Body2Ret.b116 (bumpR_rareRet hsub))
    | b11213 hRt =>
    refine SafeRet.step_plus (step_BL_zge5 l 3 1 _) (fun N1 _ => ?_)
    refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N2 _ => ?_)
    exact SafeRet.done_plus (step_BL_z2 l 3 (by omega) _)
      (by simpa [bumpR] using Body2Ret.b113
            (Gram.bt_rt (Gram.rt_v (Gram.v4 (Gram.p_out (Gram.po_213 hRt))))))
  | b413 hRt =>
    refine SafeRet.step_plus (step_BL_zge5 l 3 1 _) (fun N1 _ => ?_)
    refine SafeRet.step_plus (rule_41 _ 3 (by omega) _) (fun N2 _ => ?_)
    exact SafeRet.done_plus (step_BL_z2 l 3 (by omega) _)
      (by simpa [bumpR] using Body2Ret.b11213 (Gram.rt_6 hRt))
    | b8 hRt =>
    refine SafeRet.step_plus (step_BL_zge5 l 3 1 _) (fun N1 hN1 => ?_)
    refine SafeRet.step_plus (step_BR_ge3 _ 3 5 _) (fun N2 hN2 => ?_)
    refine SafeRet.bind (ihR N2 (by omega) _ _ hRt) (fun N3 hN3 Rsub hsub => ?_)
    refine SafeRet.bind (wrap_z6_rare (fun k hk => ihV k (by omega)) _ 3 (by omega) hsub)
      (fun N4 _ _ ⟨V, hV, hEq⟩ => ?_)
    subst hEq
    exact SafeRet.done_plus (step_BL_z2 l 3 (by omega) _)
      (by simpa [bumpR] using Body2Ret.b11213 (Gram.rt_v hV))
    | b116 hRt =>
    refine SafeRet.step_plus (step_BL_zge5 l 3 1 _) (fun N1 _ => ?_)
    refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N2 _ => ?_)
    exact SafeRet.done_plus (step_BL_z2 l 3 (by omega) _)
      (by simpa [bumpR] using Body2Ret.b113
            (Gram.bt_rt (Gram.rt_v (Gram.v4 (Gram.p_out (Gram.po_6 hRt))))))

/-- Main Strong Induction on Raw TM Step Budget `N`: proves `PValid N ∧ PRare N ∧ PBody2 N`. -/
private theorem callR_main (N : ℕ) : PValid N ∧ PRare N ∧ PBody2 N := by
  induction N using nat_strong_ind with
  | h N ih =>
    have ihV : ∀ k < N, PValid k := fun k hk => (ih k hk).1
    have ihR : ∀ k < N, PRare k := fun k hk => (ih k hk).2.1
    have ihB : ∀ k < N, PBody2 k := fun k hk => (ih k hk).2.2
    -- 1. Prove PValid N (every ValidR starts with 4, so the first step decrements N!)
    have hValid : PValid N := by
      intro l m R hm hV
      cases hV with
      | v41 hP =>
        cases hP with
        | p_end0 =>
          exact SafeRet.done_plus (rule_41 l m hm [3, 5, 1, 1])
            ⟨[3, 6, 5, 1, 1], Gram.po_end1, rfl⟩
        | p_out hPo =>
          exact SafeRet.done_plus (rule_41 l m hm _)
            ⟨_, Gram.po_3 (bumpR_post41Out hPo), rfl⟩
      | v4 hP =>
        cases hP with
        | p_end0 =>
          exact SafeRet.done_plus (rule_43511 l m hm) ⟨[3, 6, 5, 1, 1], Gram.po_end1, rfl⟩
        | p_out hPo =>
          cases hPo with
          | po_end1 =>
            exact SafeRet.done_plus (rule_436511 l m hm)
              ⟨[2, 5, 4, 3, 5, 1, 1], Gram.po_25 (Gram.rt_v (Gram.v4 Gram.p_end0)), rfl⟩
          | po_5 hB =>
            refine SafeRet.step_plus (step_BR_ge3 l m 1 _) (fun N1 hN1 => ?_)
            refine SafeRet.step_plus (step_BR_ge3 _ 3 2 _) (fun N2 hN2 => ?_)
            refine SafeRet.bind (ihB N2 (by omega) _ _ hB) (fun N3 _ Rsub hsub => ?_)
            refine SafeRet.step_plus (step_BL_z3 _ 3 (by omega) Rsub) (fun N4 _ => ?_)
            exact SafeRet.done_plus (step_BL_z2 l m hm _)
              ⟨3 :: bumpR Rsub 3, Gram.po_3 (bumpR_body2Ret hsub), by simp [bumpR]⟩
          | po_6 hRt =>
            refine SafeRet.step_plus (step_BR_ge3 l m 1 _) (fun N1 hN1 => ?_)
            refine SafeRet.step_plus (step_BR_ge3 _ 3 3 _) (fun N2 hN2 => ?_)
            refine SafeRet.bind (ihR N2 (by omega) _ _ hRt) (fun N3 hN3 Rsub hsub => ?_)
            refine SafeRet.bind (wrap_z4_rare (fun k hk => ihV k (by omega)) _ 3 (by omega) hsub)
              (fun N4 _ _ ⟨V, hV, hEq⟩ => ?_)
            subst hEq
            exact SafeRet.done_plus (step_BL_z2 l m hm _)
              ⟨6 :: V, Gram.po_6 (Gram.rt_v hV), by simp [bumpR]⟩
          | po_8 hRt =>
            refine SafeRet.step_plus (step_BR_ge3 l m 1 _) (fun N1 hN1 => ?_)
            refine SafeRet.step_plus (step_BR_ge3 _ 3 5 _) (fun N2 hN2 => ?_)
            refine SafeRet.bind (ihR N2 (by omega) _ _ hRt) (fun N3 hN3 Rsub hsub => ?_)
            refine SafeRet.bind (wrap_z6_rare (fun k hk => ihV k (by omega)) _ 3 (by omega) hsub)
              (fun N4 _ _ ⟨V, hV, hEq⟩ => ?_)
            subst hEq
            exact SafeRet.done_plus (step_BL_z2 l m hm _)
              ⟨2 :: 1 :: 3 :: V, Gram.po_213 (Gram.rt_v hV), by simp [bumpR]⟩
          | po_25 hRt =>
            refine SafeRet.step_plus (step_BR_ge3 l m 1 _) (fun N1 hN1 => ?_)
            refine SafeRet.step_plus (step_BR_2 _ 3 _) (fun N2 hN2 => ?_)
            refine SafeRet.step_plus (step_BR_ge3 _ 6 2 _) (fun N3 hN3 => ?_)
            refine SafeRet.bind (ihR N3 (by omega) _ _ hRt) (fun N4 _ Rsub hsub => ?_)
            refine SafeRet.step_plus (step_BL_z3 _ 6 (by omega) Rsub) (fun N5 _ => ?_)
            exact SafeRet.done_plus (step_BL_z2 l m hm _)
              ⟨6 :: bumpR Rsub 3, Gram.po_6 (bumpR_rareRet hsub), by simp [bumpR]⟩
          | po_213 hRt =>
            refine SafeRet.step_plus (step_BR_ge3 l m 1 _) (fun N1 _ => ?_)
            refine SafeRet.step_plus (step_BR_2 _ 3 _) (fun N2 _ => ?_)
            refine SafeRet.step_plus (step_BR_1 _ 6 (by omega) _) (fun N3 _ => ?_)
            exact SafeRet.done_plus (step_BL_z2 l m hm _)
              ⟨6 :: 6 :: _, Gram.po_6 (Gram.rt_6 hRt), by simp [bumpR]⟩
          | po_413 hRt =>
            refine SafeRet.step_plus (step_BR_ge3 l m 1 _) (fun N1 _ => ?_)
            refine SafeRet.step_plus (rule_41 _ 3 (by omega) _) (fun N2 _ => ?_)
            exact SafeRet.done_plus (step_BL_z2 l m hm _)
              ⟨2 :: 1 :: 3 :: 6 :: _, Gram.po_213 (Gram.rt_6 hRt), by simp [bumpR]⟩
          | po_3 hB =>
            refine SafeRet.step_plus (step_BR_ge3 l m 1 _) (fun N1 hN1 => ?_)
            refine SafeRet.step_plus (step_BR_ge3 _ 3 0 _) (fun N2 hN2 => ?_)
            refine SafeRet.bind (ihB N2 (by omega) _ _ hB) (fun N3 hN3 Rsub hsub => ?_)
            cases hsub with
            | b11 hT =>
              refine SafeRet.step_plus (step_BL_z1_1 _ 3 (by omega) _) (fun N4 _ => ?_)
              refine SafeRet.step_plus (step_BR_1 _ 5 (by omega) _) (fun N5 _ => ?_)
              exact SafeRet.done_plus (step_BL_z2 l m hm _)
                ⟨5 :: bumpR _ 3, Gram.po_5 (bumpR_post41Out hT), by simp [bumpR]⟩
            | b113 hB2 =>
              refine SafeRet.step_plus (step_BL_z1_1 _ 3 (by omega) _) (fun N4 _ => ?_)
              refine SafeRet.step_plus (step_BR_1 _ 5 (by omega) _) (fun N5 _ => ?_)
              exact SafeRet.done_plus (step_BL_z2 l m hm _)
                ⟨5 :: 6 :: _, Gram.po_5 (Gram.bt_6 hB2), by simp [bumpR]⟩
            | b15 hB2 =>
              refine SafeRet.step_plus (step_BL_z1_1 _ 3 (by omega) _) (fun N4 hN4 => ?_)
              refine SafeRet.step_plus (step_BR_ge3 _ 5 2 _) (fun N5 hN5 => ?_)
              refine SafeRet.bind (ihB N5 (by omega) _ _ hB2) (fun N6 _ R2 h2 => ?_)
              refine SafeRet.step_plus (step_BL_z3 _ 5 (by omega) R2) (fun N7 _ => ?_)
              exact SafeRet.done_plus (step_BL_z2 l m hm _)
                ⟨5 :: bumpR R2 3, Gram.po_5 (bumpR_body2Ret h2), by simp [bumpR]⟩
            | b11213 hRt =>
              refine SafeRet.step_plus (step_BL_z1_1 _ 3 (by omega) _) (fun N4 _ => ?_)
              refine SafeRet.step_plus (step_BR_1 _ 5 (by omega) _) (fun N5 _ => ?_)
              exact SafeRet.done_plus (step_BL_z2 l m hm _)
                ⟨5 :: 5 :: 1 :: 3 :: _, Gram.po_5 (Gram.bt_513 hRt), by simp [bumpR]⟩
            | b413 hRt =>
              refine SafeRet.step_plus (step_BL_z1_ge2 _ 3 2 (by omega) _) (fun N4 _ => ?_)
              refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N5 _ => ?_)
              refine SafeRet.step_plus (step_BL_z3 _ 2 (by omega) _) (fun N6 _ => ?_)
              exact SafeRet.done_plus (step_BL_z2 l m hm _)
                ⟨2 :: 5 :: 6 :: _, Gram.po_25 (Gram.rt_6 hRt), by simp [bumpR]⟩
            | b116 hRt =>
              refine SafeRet.step_plus (step_BL_z1_1 _ 3 (by omega) _) (fun N4 _ => ?_)
              refine SafeRet.step_plus (step_BR_1 _ 5 (by omega) _) (fun N5 _ => ?_)
              exact SafeRet.done_plus (step_BL_z2 l m hm _)
                ⟨5 :: 9 :: _, Gram.po_5 (Gram.bt_9 hRt), by simp [bumpR]⟩
            | b5 hB2 =>
              refine SafeRet.step_plus (step_BL_z1_ge2 _ 3 3 (by omega) _) (fun N4 hN4 => ?_)
              refine SafeRet.bind (ihB N4 (by omega) _ _ hB2) (fun N5 hN5 R2 h2 => ?_)
              refine SafeRet.bind
                (wrap_z4_body2 (fun k hk => ihV k (by omega)) (fun k hk => ihR k (by omega))
                  (fun k hk => ihB k (by omega)) _ 2 (by omega) h2)
                (fun N6 _ R3 h3 => ?_)
              cases h3 with
              | z4_body hB3 =>
                exact SafeRet.done_plus (step_BL_z2 l m hm _)
                  ⟨5 :: _, Gram.po_5 hB3, by simp [bumpR]⟩
              | z4_rare hRt3 =>
                exact SafeRet.done_plus (step_BL_z2 l m hm _)
                  ⟨8 :: _, Gram.po_8 hRt3, by simp [bumpR]⟩
              | z4_13 hRt3 =>
                exact SafeRet.done_plus (step_BL_z2 l m hm _)
                  ⟨4 :: 1 :: 3 :: _, Gram.po_413 hRt3, by simp [bumpR]⟩
            | b8 hRt =>
              refine SafeRet.step_plus (step_BL_z1_ge2 _ 3 6 (by omega) _) (fun N4 hN4 => ?_)
              refine SafeRet.bind (ihR N4 (by omega) _ _ hRt) (fun N5 hN5 R2 h2 => ?_)
              refine SafeRet.bind (wrap_z7_rare (fun k hk => ihV k (by omega)) _ 2 (by omega) h2)
                (fun N6 _ _ ⟨V, hV, hEq⟩ => ?_)
              subst hEq
              exact SafeRet.done_plus (step_BL_z2 l m hm _)
                ⟨2 :: 5 :: V, Gram.po_25 (Gram.rt_v hV), by simp [bumpR]⟩
            | b25 hRt =>
              refine SafeRet.step_plus (step_BL_z1_ge2 _ 3 0 (by omega) _) (fun N4 hN4 => ?_)
              refine SafeRet.step_plus (step_BR_ge3 _ 3 2 _) (fun N5 hN5 => ?_)
              refine SafeRet.bind (ihR N5 (by omega) _ _ hRt) (fun N6 hN6 R2 h2 => ?_)
              cases h2 with
              | r11 hT =>
                refine SafeRet.step_plus (step_BL_z3 _ 3 (by omega) _) (fun N7 hN7 => ?_)
                refine SafeRet.step_plus (step_BL_z1_ge2 _ 2 0 (by omega) _) (fun N8 hN8 => ?_)
                refine SafeRet.bind (ihV N8 (by omega) _ 3 _ (by omega) (Gram.v41 (Gram.p_out hT)))
                  (fun N9 _ _ ⟨T2, hT2, hEq⟩ => ?_)
                subst hEq
                refine SafeRet.step_plus (step_BL_z1_m1 _ 0 _) (fun N10 _ => ?_)
                refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N11 _ => ?_)
                exact SafeRet.done_plus (step_BL_z2 l m hm _)
                  ⟨3 :: bumpR T2 3, Gram.po_3 (bumpR_post41Out hT2), by simp [bumpR]⟩
              | r5 hV =>
                refine SafeRet.step_plus (step_BL_z3 _ 3 (by omega) _) (fun N7 hN7 => ?_)
                refine SafeRet.step_plus (step_BL_z1_ge2 _ 2 0 (by omega) _) (fun N8 hN8 => ?_)
                refine SafeRet.step_plus (step_BR_ge3 _ 3 5 _) (fun N9 hN9 => ?_)
                refine SafeRet.bind (ihV N9 (by omega) _ 3 _ (by omega) hV)
                  (fun N10 _ _ ⟨T2, hT2, hEq⟩ => ?_)
                subst hEq
                refine SafeRet.step_plus (step_BL_zge5 _ 3 1 _) (fun N11 _ => ?_)
                refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N12 _ => ?_)
                refine SafeRet.step_plus (step_BL_z2 _ 3 (by omega) _) (fun N13 _ => ?_)
                refine SafeRet.step_plus (step_BL_z1_m1 _ 0 _) (fun N14 _ => ?_)
                refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N15 _ => ?_)
                exact SafeRet.done_plus (step_BL_z2 l m hm _)
                  ⟨3 :: 6 :: 4 :: T2,
                      Gram.po_3 (Gram.bt_6
                      (Gram.bt_rt (Gram.rt_v (Gram.v4 (Gram.p_out hT2))))), by simp [bumpR]⟩
              | r113 hV =>
                refine SafeRet.step_plus (step_BL_z3 _ 3 (by omega) _) (fun N7 _ => ?_)
                refine SafeRet.step_plus (step_BL_z1_ge2 _ 2 0 (by omega) _) (fun N8 _ => ?_)
                refine SafeRet.step_plus (rule_41 _ 3 (by omega) _) (fun N9 _ => ?_)
                refine SafeRet.step_plus (step_BL_z1_m1 _ 0 _) (fun N10 _ => ?_)
                refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N11 _ => ?_)
                exact SafeRet.done_plus (step_BL_z2 l m hm _)
                  ⟨3 :: 6 :: 6 :: _, Gram.po_3 (Gram.bt_6 (Gram.bt_6 (Gram.bt_rt (Gram.rt_v hV)))),
                      by simp [bumpR]⟩
    -- 2. Prove PRare N (base calls hValid at N; cons 6/8 takes >= 1 step and calls ih!)
    have hRare : PRare N := by
      intro l R hRt
      cases hRt with
      | rt_v hV =>
        refine SafeRet.mono_Q (hValid l 3 R (by omega) hV) ?_
        rintro R' ⟨T, hT, rfl⟩
        exact RareRet.r11 hT
      | rt_6 hRt2 =>
        refine SafeRet.step_plus (step_BR_ge3 l 3 3 _) (fun N1 hN1 => ?_)
        refine SafeRet.bind (ihR N1 (by omega) _ _ hRt2) (fun N2 hN2 Rsub hsub => ?_)
        refine SafeRet.mono_Q (wrap_z4_rare (fun k hk => ihV k (by omega)) l 3 (by omega) hsub) ?_
        rintro R' ⟨V, hV, rfl⟩
        exact RareRet.r5 hV
      | rt_8 hRt2 =>
        refine SafeRet.step_plus (step_BR_ge3 l 3 5 _) (fun N1 hN1 => ?_)
        refine SafeRet.bind (ihR N1 (by omega) _ _ hRt2) (fun N2 hN2 Rsub hsub => ?_)
        refine SafeRet.mono_Q (wrap_z6_rare (fun k hk => ihV k (by omega)) l 3 (by omega) hsub) ?_
        rintro R' ⟨V, hV, rfl⟩
        exact RareRet.r113 hV
    -- 3. Prove PBody2 N (base calls hRare at N; all other constructors take >= 1 step!)
    have hBody2 : PBody2 N := by
      intro l R hB
      cases hB with
      | bt_rt hRt =>
        exact SafeRet.mono_Q (hRare l R hRt) (fun _ h => rareRet_to_body2Ret h)
      | bt_end2 =>
        exact SafeRet.done_plus (rule_66511 l)
          (Body2Ret.b413 (Gram.rt_v (Gram.v4 Gram.p_end0)))
      | bt_9 hRt =>
        refine SafeRet.step_plus (step_BR_ge3 l 3 6 _) (fun N1 hN1 => ?_)
        refine SafeRet.bind (ihR N1 (by omega) _ _ hRt) (fun N2 hN2 Rsub hsub => ?_)
        refine SafeRet.mono_Q (wrap_z7_rare (fun k hk => ihV k (by omega)) l 3 (by omega) hsub) ?_
        rintro R' ⟨V, hV, rfl⟩
        exact Body2Ret.b25 (Gram.rt_v hV)
      | bt_11 hRt =>
        refine SafeRet.step_plus (step_BR_ge3 l 3 8 _) (fun N1 hN1 => ?_)
        refine SafeRet.bind (ihR N1 (by omega) _ _ hRt) (fun N2 hN2 Rsub hsub => ?_)
        -- After BL_zge5(z=9 -> z=5), all 3 RareRet cases converge to BL_zge5(z=5, m=3) with [2,
        -- V']!
        have hconv :
            SafeRet N2 l
            (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ 3)) <+ (([0] : List Sym) ^ 8)) Rsub)
            Body2Ret := by
          have finish_z5 : ∀ (k : ℕ), k ≤ N2 → ∀ V', ValidR V' →
              SafeRet k l
                  (BL ((((0 : Sym) >> l) <+ (([1] : List Sym) ^ 3)) <+ (([0] : List Sym) ^ 4)) (2 ::
                  V')) Body2Ret := by
            intro k hk V' hV'
            refine SafeRet.step_plus (step_BL_zge5 l 3 0 _) (fun k1 hk1 => ?_)
            refine SafeRet.step_plus (step_BR_2 _ 3 _) (fun k2 hk2 => ?_)
            refine SafeRet.bind (ihV k2 (by omega) _ 6 _ (by omega) hV') (fun k3 _ _ ⟨T, hT,
                hEq⟩ => ?_)
            subst hEq
            refine SafeRet.step_plus (step_BL_z1_ge2 l 3 2 (by omega) _) (fun k4 _ => ?_)
            refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun k5 _ => ?_)
            exact SafeRet.done_plus (step_BL_z3 l 2 (by omega) _)
              (by simpa [bumpR] using Body2Ret.b15 (bumpR_post41Out hT))
          cases hsub with
          | r11 hT =>
            refine SafeRet.step_plus (step_BL_zge5 l 3 4 _) (fun N3 hN3 => ?_)
            refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N4 hN4 => ?_)
            exact finish_z5 N4 (by omega) (4 :: _) (Gram.v4 (Gram.p_out hT))
          | r5 hV =>
            refine SafeRet.step_plus (step_BL_zge5 l 3 4 _) (fun N3 hN3 => ?_)
            refine SafeRet.step_plus (step_BR_ge3 _ 3 2 _) (fun N4 hN4 => ?_)
            refine SafeRet.bind (ihV N4 (by omega) _ 3 _ (by omega) hV) (fun N5 hN5 _ ⟨T, hT,
                hEq⟩ => ?_)
            subst hEq
            refine SafeRet.step_plus (step_BL_z3 _ 3 (by omega) _) (fun N6 hN6 => ?_)
            exact finish_z5 N6 (by omega) (4 :: 1 :: T) (Gram.v41 (Gram.p_out hT))
          | r113 hV =>
            refine SafeRet.step_plus (step_BL_zge5 l 3 4 _) (fun N3 hN3 => ?_)
            refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N4 hN4 => ?_)
            exact finish_z5 N4 (by omega) (4 :: 3 :: _)
                (Gram.v4 (Gram.p_out (Gram.po_3 (Gram.bt_rt (Gram.rt_v hV)))))
        exact hconv
      | bt_55 hRt =>
        refine SafeRet.step_plus (step_BR_ge3 l 3 2 _) (fun N1 hN1 => ?_)
        refine SafeRet.step_plus (step_BR_ge3 _ 3 2 _) (fun N2 hN2 => ?_)
        refine SafeRet.bind (ihR N2 (by omega) _ _ hRt) (fun N3 _ Rsub hsub => ?_)
        refine SafeRet.step_plus (step_BL_z3 _ 3 (by omega) Rsub) (fun N4 _ => ?_)
        exact SafeRet.done_plus (step_BL_z3 l 3 (by omega) _)
          (by simpa [bumpR] using Body2Ret.b25 (bumpR_rareRet hsub))
        | bt_513 hRt =>
        refine SafeRet.step_plus (step_BR_ge3 l 3 2 _) (fun N1 _ => ?_)
        refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N2 _ => ?_)
        exact SafeRet.done_plus (step_BL_z3 l 3 (by omega) _)
          (by simpa [bumpR] using Body2Ret.b25 (Gram.rt_6 hRt))
        | bt_713 hRt =>
        refine SafeRet.step_plus (step_BR_ge3 l 3 4 _) (fun N1 hN1 => ?_)
        refine SafeRet.step_plus (step_BR_1 _ 3 (by omega) _) (fun N2 hN2 => ?_)
        refine SafeRet.step_plus (step_BL_zge5 l 3 0 _) (fun N3 hN3 => ?_)
        refine SafeRet.step_plus (step_BR_2 _ 3 _) (fun N4 hN4 => ?_)
        refine SafeRet.step_plus (step_BR_ge3 _ 6 3 _) (fun N5 hN5 => ?_)
        refine SafeRet.bind (ihR N5 (by omega) _ _ hRt) (fun N6 hN6 Rsub hsub => ?_)
        refine SafeRet.bind (wrap_z4_rare (fun k hk => ihV k (by omega)) _ 6 (by omega) hsub)
          (fun N7 hN7 _ ⟨V', hV', hEq⟩ => ?_)
        subst hEq
        refine SafeRet.step_plus (step_BL_z1_ge2 l 3 6 (by omega) _) (fun N8 hN8 => ?_)
        refine SafeRet.bind (ihV N8 (by omega) _ 3 _ (by omega) hV') (fun N9 hN9 _ ⟨T, hT,
            hEq2⟩ => ?_)
        subst hEq2
        refine SafeRet.mono_Q (wrap_z7_rare (fun k hk =>
            ihV k (by omega)) l 2 (by omega) (RareRet.r11 hT)) ?_
        rintro R' ⟨V2, hV2, rfl⟩
        exact Body2Ret.b15 (Gram.bt_rt (Gram.rt_v hV2))
      | bt_6 hB2 =>
        refine SafeRet.step_plus (step_BR_ge3 l 3 3 _) (fun N1 hN1 => ?_)
        refine SafeRet.bind (ihB N1 (by omega) _ _ hB2) (fun N2 hN2 Rsub hsub => ?_)
        refine SafeRet.mono_Q
          (wrap_z4_body2 (fun k hk => ihV k (by omega)) (fun k hk => ihR k (by omega))
            (fun k hk => ihB k (by omega)) l 3 (by omega) hsub) ?_
        intro R' hZ4
        cases hZ4 with
        | z4_body hB3 => exact Body2Ret.b5 hB3
        | z4_rare hRt3 => exact Body2Ret.b8 hRt3
        | z4_13 hRt3 => exact Body2Ret.b413 hRt3
      | bt_8 hB2 =>
        refine SafeRet.step_plus (step_BR_ge3 l 3 5 _) (fun N1 hN1 => ?_)
        refine SafeRet.bind (ihB N1 (by omega) _ _ hB2) (fun N2 hN2 Rsub hsub => ?_)
        exact wrap_z6_body2 (fun k hk => ihV k (by omega)) (fun k hk => ihR k (by omega))
          (fun k hk => ihB k (by omega)) l hsub
    exact ⟨hValid, hRare, hBody2⟩

/-- Top-level closure: every `BL default R` with `ValidR R` is `N`-safe for all `N : ℕ`. -/
private theorem BL_valid_safe (N : ℕ) : ∀ R, ValidR R → safe TM (BL default R) N := by
  induction N using nat_strong_ind with
  | h N ih =>
    intro R hV
    have step1 : (BL default R) [TM]⊢⁺ BR default 3 R := step_BL_empty R
    rcases step1 with ⟨s1, hs1_pos, hs1⟩
    by_cases hlt1 : N < s1
    · exact safe_of_reachesIn_lt hs1 hlt1
    · refine safe_of_reachesIn hs1 (by omega) ?_
      rcases (callR_main (N - s1)).1 default 3 R (by omega) hV with hs | ⟨k1, _, hk1_pos, hk1_le,
          hk1, T1, hT1, rfl⟩
      · exact hs
      · refine safe_of_reachesIn hk1 hk1_le ?_
        -- BL default (1 :: 1 :: T1) ⊢⁺ BR default 6 (4 :: T1)
        have hmid : (BL default (1 :: 1 :: T1)) [TM]⊢⁺ BR default 6 (4 :: T1) := by
          refine ReachesPlus.trans (step_BL_empty (1 :: 1 :: T1)) ?_
          refine ReachesPlus.trans (step_BR_1 default 3 (by omega) (1 :: T1)) ?_
          refine ReachesPlus.trans (step_BL_empty (2 :: 4 :: T1)) ?_
          exact step_BR_2 default 3 (4 :: T1)
        rcases hmid with ⟨s2, hs2_pos, hs2⟩
        by_cases hlt2 : N - s1 - k1 < s2
        · exact safe_of_reachesIn_lt hs2 hlt2
        · refine safe_of_reachesIn hs2 (by omega) ?_
          rcases (callR_main (N - s1 - k1 - s2)).1 default 6 (4 :: T1) (by omega)
              (Gram.v4 (Gram.p_out hT1)) with
            hs2' | ⟨k2, _, hk2_pos, hk2_le, hk2, T2, hT2, rfl⟩
          · exact hs2'
          · refine safe_of_reachesIn hk2 hk2_le ?_
            exact ih (N - s1 - k1 - s2 - k2) (by omega) (4 :: 1 :: T2) (Gram.v41 (Gram.p_out hT2))

end Solution


private theorem is_does_not_halt : IsNotHalt target_tm :=
  SafeBudget.isNotHalt_of_safe_all Solution.init_reaches_R0
    (fun N => Solution.BL_valid_safe N Solution.R0 Solution.R0_valid)


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0RC_1LC0RB_1LD0LD_1RA1LE_---0LF_1LB1LF` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0RC_1LC0RB_1LD0LD_1RA1LE_HHH0LF_1LB1LF
