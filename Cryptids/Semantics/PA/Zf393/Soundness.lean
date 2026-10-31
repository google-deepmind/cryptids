/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.PA.Zf393.Program
public import Cryptids.Semantics.PA.Zf380

/-!
# Internalized `ZF` Soundness & Completeness of `zf_393` and `zf_380` in `PA`

Completes Layer 3 of the `zf_393` proof inside arbitrary first-order models `PAM M` of Peano
Arithmetic (`[PAStructure M] [PAModel M]`):

1. **Internalized Soundness (`mZfInconsistent_of_mZf393MainHalts`)**:
   Maintains a first-order definable invariant `MStackProofInv` along $\beta$-coded `main()`
   traces witnessing a $\beta$-coded `MIsZFStep` derivation `(L, pc, pd)` and a $\beta$-coded
   formula-stack spine `(depth, sc, sd)` whose entries all appear in `(pc, pd)`. When `main()`
   halts (`topwff = 1 = mZfMem 0 0`), `(pc, pd)` witnesses `MZFInconsistent M`.
2. **Internalized Completeness (`mZf393MainHalts_of_mZfInconsistent`)**:
   Compiles any $\beta$-coded `ZF` derivation `(n, pc, pd)` of `mZfMem 0 0` into a $\beta$-coded
   sequence of 4-tuple `zf393` instructions via `PAM.strong_ind1`, folds it into a Cantor-paired
   `prooflist` code via `PAM.ind1`, advances `nextproof` to that code, and executes `main()` to
   halting (`topwff = 1`).
3. **`PAProvable` Main Theorems**:
   By Gödel–Henkin completeness (`paProvable_iff_holdsIn_all_models`), establishes:
   - `paProvable_halts_zf393_iff_zfInconsistent :
       PAProvable ((paHalts Machines.zf393).iff paZFInconsistent)`
   - `paProvable_halts_zf380_iff_zfInconsistent :
       PAProvable ((paHalts Machines.zf380).iff paZFInconsistent)`
-/

@[expose] public section

namespace ConjectureMachines.Semantics.PA

open Machines
open ConjectureMachines.Zf393
open ConjectureMachines.Zf393.Layer2
open PAM

section Model

variable {M : Type*} [PAStructure M] [PAModel M]

/-! ## Section 1: Pairing Bounds, Zero Axiom, and Prefix Congruence -/

@[simp]
theorem mZfEq_zero_zero : mZfEq (0 : PAM M) 0 = 0 := by
  simp [mZfEq, mPair_zero_zero]

theorem mIsZFAxiom_zero : MIsZFAxiom (0 : PAM M) :=
  Or.inl mZfEq_zero_zero.symm

theorem mIsZFStep_zero (c d i : PAM M) : MIsZFStep c d i 0 :=
  Or.inl mIsZFAxiom_zero

theorem mUnpair_snd_le (z : PAM M) : (mUnpair z).2 ≤ z := by
  conv_rhs => rw [← mPair_mUnpair z]
  exact le_mPair_right _ _

attribute [local irreducible] mPair mUnpair

theorem mIsZFStep_congr_prefix {c d c' d' i w : PAM M}
    (hprev : ∀ j < i, mBeta c' d' j = mBeta c d j)
    (hst : MIsZFStep c d i w) : MIsZFStep c' d' i w := by
  rcases hst with hax | ⟨φ, χ, j₁, j₂, hj₁, hj₂, hb₁, hb₂, hχ⟩ | ⟨x, φ, j, hj, hbj, hw⟩
  · exact Or.inl hax
  · exact Or.inr (Or.inl ⟨φ, χ, j₁, j₂, hj₁, hj₂,
      (hprev j₁ hj₁).trans hb₁, (hprev j₂ hj₂).trans hb₂, hχ⟩)
  · exact Or.inr (Or.inr ⟨x, φ, j, hj, (hprev j hj).trans hbj, hw⟩)

/-! ## Section 2: Soundness (`mZfInconsistent_of_mZf393MainHalts`) -/

/-- $\beta$-coded derivation prefix `(L, pc, pd)` with `mBeta pc pd 0 = 0` and valid `ZF` steps. -/
def MDerivInv (L pc pd : PAM M) : Prop :=
  1 ≤ L ∧ mBeta pc pd 0 = 0 ∧ ∀ i < L, MIsZFStep pc pd i (mBeta pc pd i)

/-- $\beta$-coded stack spine `(depth, sc, sd)` for `stk` whose formulas lie in `(L, pc, pd)`. -/
def MStackSpine (L pc pd depth sc sd stk : PAM M) : Prop :=
  mBeta sc sd 0 = 0 ∧
  (∀ k < depth, ∃ j < L, mBeta sc sd (k + 1) = mPair (mBeta pc pd j) (mBeta sc sd k)) ∧
  stk = mBeta sc sd depth

/-- Combined derivation + formula-stack invariant on `(top, stk)`. -/
def MStackProofInv (top stk : PAM M) : Prop :=
  ∃ L pc pd depth sc sd : PAM M,
    MDerivInv L pc pd ∧
    MStackSpine L pc pd depth sc sd stk ∧
    ∃ j < L, top = mBeta pc pd j

theorem paDef_mStackProofInv {n : ℕ} {ftop fstk : (Fin n → PAM M) → PAM M}
    (htop : PAFunN n ftop) (hstk : PAFunN n fstk) :
    PADefN n (fun u ↦ MStackProofInv (ftop u) (fstk u)) := by
  let fL : (Fin (n + 6) → PAM M) → PAM M :=
    fun v ↦ (Fin.init (Fin.init (Fin.init (Fin.init (Fin.init v))))) (Fin.last n)
  let fpc : (Fin (n + 6) → PAM M) → PAM M :=
    fun v ↦ (Fin.init (Fin.init (Fin.init (Fin.init v)))) (Fin.last (n + 1))
  let fpd : (Fin (n + 6) → PAM M) → PAM M :=
    fun v ↦ (Fin.init (Fin.init (Fin.init v))) (Fin.last (n + 2))
  let fdep : (Fin (n + 6) → PAM M) → PAM M :=
    fun v ↦ (Fin.init (Fin.init v)) (Fin.last (n + 3))
  let fsc : (Fin (n + 6) → PAM M) → PAM M :=
    fun v ↦ (Fin.init v) (Fin.last (n + 4))
  let fsd : (Fin (n + 6) → PAM M) → PAM M :=
    fun v ↦ v (Fin.last (n + 5))
  have hL : PAFunN (n + 6) fL :=
    paFun_weaken (paFun_weaken (paFun_weaken (paFun_weaken (paFun_weaken
      (paFun_proj (Fin.last n))))))
  have hpc : PAFunN (n + 6) fpc :=
    paFun_weaken (paFun_weaken (paFun_weaken (paFun_weaken (paFun_proj (Fin.last (n + 1))))))
  have hpd : PAFunN (n + 6) fpd :=
    paFun_weaken (paFun_weaken (paFun_weaken (paFun_proj (Fin.last (n + 2)))))
  have hdep : PAFunN (n + 6) fdep :=
    paFun_weaken (paFun_weaken (paFun_proj (Fin.last (n + 3))))
  have hsc : PAFunN (n + 6) fsc :=
    paFun_weaken (paFun_proj (Fin.last (n + 4)))
  have hsd : PAFunN (n + 6) fsd :=
    paFun_proj (Fin.last (n + 5))
  have htop6 : PAFunN (n + 6) (fun v ↦
      ftop (Fin.init (Fin.init (Fin.init (Fin.init (Fin.init (Fin.init v))))))) :=
    paFun_weaken (paFun_weaken (paFun_weaken (paFun_weaken (paFun_weaken (paFun_weaken htop)))))
  have hstk6 : PAFunN (n + 6) (fun v ↦
      fstk (Fin.init (Fin.init (Fin.init (Fin.init (Fin.init (Fin.init v))))))) :=
    paFun_weaken (paFun_weaken (paFun_weaken (paFun_weaken (paFun_weaken (paFun_weaken hstk)))))
  have h1leL : PADefN (n + 6) (fun v ↦ 1 ≤ fL v) :=
    paDef_le (paFun_const 1) hL
  have hpc0 : PADefN (n + 6) (fun v ↦ mBeta (fpc v) (fpd v) 0 = 0) :=
    paDef_eq (paFun_mBeta hpc hpd (paFun_const 0)) (paFun_const 0)
  have hsteps : PADefN (n + 6) (fun v ↦
      ∀ i < fL v, MIsZFStep (fpc v) (fpd v) i (mBeta (fpc v) (fpd v) i)) := by
    have hi : PAFunN (n + 7) (fun w ↦ w (Fin.last (n + 6))) :=
      paFun_proj (M := M) (Fin.last (n + 6))
    have hL7 := paFun_weaken hL
    have hpc7 := paFun_weaken hpc
    have hpd7 := paFun_weaken hpd
    refine paDefN_congr (fun v ↦ ?_)
      (paDef_all (paDef_imp (paDef_lt hi hL7)
        (paDef_mIsZFStep hpc7 hpd7 hi (paFun_mBeta hpc7 hpd7 hi))))
    simp only [Fin.init_snoc, Fin.snoc_last]
  have hsc0 : PADefN (n + 6) (fun v ↦ mBeta (fsc v) (fsd v) 0 = 0) :=
    paDef_eq (paFun_mBeta hsc hsd (paFun_const 0)) (paFun_const 0)
  have hspine : PADefN (n + 6) (fun v ↦
      ∀ k < fdep v, ∃ j < fL v,
        mBeta (fsc v) (fsd v) (k + 1) =
          mPair (mBeta (fpc v) (fpd v) j) (mBeta (fsc v) (fsd v) k)) := by
    have hk8 : PAFunN (n + 8) (fun w ↦ (Fin.init w) (Fin.last (n + 6))) :=
      paFun_weaken (paFun_proj (M := M) (Fin.last (n + 6)))
    have hj8 : PAFunN (n + 8) (fun w ↦ w (Fin.last (n + 7))) :=
      paFun_proj (M := M) (Fin.last (n + 7))
    have hL8 := paFun_weaken (paFun_weaken hL)
    have hpc8 := paFun_weaken (paFun_weaken hpc)
    have hpd8 := paFun_weaken (paFun_weaken hpd)
    have hsc8 := paFun_weaken (paFun_weaken hsc)
    have hsd8 := paFun_weaken (paFun_weaken hsd)
    have hex_j : PADefN (n + 7) (fun u7 ↦
        ∃ j < fL (Fin.init u7),
          mBeta (fsc (Fin.init u7)) (fsd (Fin.init u7)) (u7 (Fin.last (n + 6)) + 1) =
            mPair (mBeta (fpc (Fin.init u7)) (fpd (Fin.init u7)) j)
              (mBeta (fsc (Fin.init u7)) (fsd (Fin.init u7)) (u7 (Fin.last (n + 6))))) := by
      refine paDefN_congr (fun u7 ↦ ?_)
        (paDef_ex (paDef_and (paDef_lt hj8 hL8)
          (paDef_eq
            (paFun_mBeta hsc8 hsd8 (paFun_add hk8 (paFun_const 1)))
            (paFun_mPair (paFun_mBeta hpc8 hpd8 hj8) (paFun_mBeta hsc8 hsd8 hk8)))))
      simp only [Fin.init_snoc, Fin.snoc_last]
    have hk7 : PAFunN (n + 7) (fun u7 ↦ u7 (Fin.last (n + 6))) :=
      paFun_proj (M := M) (Fin.last (n + 6))
    refine paDefN_congr (fun v ↦ ?_)
      (paDef_all (paDef_imp (paDef_lt hk7 (paFun_weaken hdep)) hex_j))
    simp only [Fin.init_snoc, Fin.snoc_last]
  have hstk_eq : PADefN (n + 6) (fun v ↦
      fstk (Fin.init (Fin.init (Fin.init (Fin.init (Fin.init (Fin.init v)))))) =
        mBeta (fsc v) (fsd v) (fdep v)) :=
    paDef_eq hstk6 (paFun_mBeta hsc hsd hdep)
  have htop_mem : PADefN (n + 6) (fun v ↦
      ∃ j < fL v,
        ftop (Fin.init (Fin.init (Fin.init (Fin.init (Fin.init (Fin.init v)))))) =
          mBeta (fpc v) (fpd v) j) := by
    have hj7 : PAFunN (n + 7) (fun w ↦ w (Fin.last (n + 6))) :=
      paFun_proj (M := M) (Fin.last (n + 6))
    refine paDefN_congr (fun v ↦ ?_)
      (paDef_ex (paDef_and (paDef_lt hj7 (paFun_weaken hL))
        (paDef_eq (paFun_weaken htop6)
          (paFun_mBeta (paFun_weaken hpc) (paFun_weaken hpd) hj7))))
    simp only [Fin.init_snoc, Fin.snoc_last]
  have hbody :=
    paDef_and (paDef_and h1leL (paDef_and hpc0 hsteps))
      (paDef_and (paDef_and hsc0 (paDef_and hspine hstk_eq)) htop_mem)
  refine paDefN_congr (fun u ↦ ?_)
    (paDef_ex (paDef_ex (paDef_ex (paDef_ex (paDef_ex (paDef_ex hbody))))))
  simp only [MStackProofInv, MDerivInv, MStackSpine,
    fL, fpc, fpd, fdep, fsc, fsd, Fin.init_snoc, Fin.snoc_last]

theorem mDerivInv_append {L pc pd w : PAM M}
    (hD : MDerivInv L pc pd) (hw : MIsZFStep pc pd L w) :
    ∃ pc' pd' : PAM M,
      MDerivInv (L + 1) pc' pd' ∧
      (∀ i < L, mBeta pc' pd' i = mBeta pc pd i) ∧
      mBeta pc' pd' L = w := by
  obtain ⟨pc', pd', hprev, hlast⟩ := mBeta_snoc L pc pd w
  rcases hD with ⟨h1L, h0, hst⟩
  have h0ltL : (0 : PAM M) < L := lt_of_lt_of_le zero_lt_one_pam h1L
  refine ⟨pc', pd', ⟨le_trans h1L ⟨1, rfl⟩, (hprev 0 h0ltL).trans h0, ?_⟩, hprev, hlast⟩
  intro i hi
  rcases le_iff_lt_or_eq.mp (lt_add_one_iff_le.mp hi) with hilt | rfl
  · rw [hprev i hilt]
    exact mIsZFStep_congr_prefix (fun j hj ↦ hprev j (lt_trans hj hilt)) (hst i hilt)
  · rw [hlast]
    exact mIsZFStep_congr_prefix hprev hw

theorem mStackSpine_upgrade {L L' pc pd pc' pd' depth sc sd stk : PAM M}
    (hS : MStackSpine L pc pd depth sc sd stk)
    (hL : L ≤ L')
    (hprev : ∀ i < L, mBeta pc' pd' i = mBeta pc pd i) :
    MStackSpine L' pc' pd' depth sc sd stk := by
  rcases hS with ⟨h0, hstep, hstk⟩
  refine ⟨h0, fun k hk ↦ ?_, hstk⟩
  obtain ⟨j, hj, heq⟩ := hstep k hk
  exact ⟨j, lt_of_lt_of_le hj hL, by rw [hprev j hj, heq]⟩

theorem mStackSpine_push {L pc pd depth sc sd stk top j₀ : PAM M}
    (hS : MStackSpine L pc pd depth sc sd stk)
    (hj₀ : j₀ < L) (htop : top = mBeta pc pd j₀) :
    ∃ sc' sd' : PAM M, MStackSpine L pc pd (depth + 1) sc' sd' (mPair top stk) := by
  rcases hS with ⟨h0, hstep, hstk⟩
  obtain ⟨sc', sd', hprev, hlast⟩ := mBeta_snoc (depth + 1) sc sd (mPair top stk)
  refine ⟨sc', sd', ?_, ?_, hlast.symm⟩
  · rw [hprev 0 ⟨depth, by ring⟩, h0]
  · intro k hk
    rcases le_iff_lt_or_eq.mp (lt_add_one_iff_le.mp hk) with hklt | rfl
    · obtain ⟨j, hj, heq⟩ := hstep k hklt
      refine ⟨j, hj, ?_⟩
      rw [hprev (k + 1) (add_lt_add_right_pam hklt 1),
        hprev k (lt_trans hklt (lt_succ_self_pam depth)), heq]
    · refine ⟨j₀, hj₀, ?_⟩
      rw [hlast, hprev k (lt_succ_self_pam k), ← hstk, htop]

theorem mStackSpine_pop {L pc pd depth sc sd stk : PAM M}
    (hD : MDerivInv L pc pd)
    (hS : MStackSpine L pc pd depth sc sd stk) :
    (∃ j < L, (mUnpair stk).1 = mBeta pc pd j) ∧
    MStackSpine L pc pd (depth - 1) sc sd (mUnpair stk).2 := by
  rcases hS with ⟨h0, hstep, hstk⟩
  rcases eq_zero_or_exists_succ depth with rfl | ⟨d', rfl⟩
  · have hstk0 : stk = 0 := hstk.trans h0
    have h0sub : (0 : PAM M) - 1 = 0 := sub_eq_zero_of_le_pam (zero_le_pam 1)
    rw [hstk0, mUnpair_zero, h0sub]
    refine ⟨⟨0, lt_of_lt_of_le zero_lt_one_pam hD.1, hD.2.1.symm⟩, h0, ?_, h0.symm⟩
    intro k hk
    exact absurd hk (not_lt_zero_pam k)
  · rw [add_one_sub_one_pam]
    obtain ⟨j, hj, heq⟩ := hstep d' (lt_succ_self_pam d')
    have hunp : mUnpair stk = (mBeta pc pd j, mBeta sc sd d') := by
      rw [hstk, heq, mUnpair_mPair]
    rw [hunp]
    exact ⟨⟨j, hj, rfl⟩, h0, fun k hk ↦ hstep k (lt_trans hk (lt_succ_self_pam d')), rfl⟩

theorem mStackProofInv_push_step {top stk w : PAM M}
    (hInv : MStackProofInv top stk)
    (hw : ∀ L pc pd : PAM M, MIsZFStep pc pd L w) :
    MStackProofInv w (mPair top stk) := by
  rcases hInv with ⟨L, pc, pd, depth, sc, sd, hD, hS, j₀, hj₀, htop⟩
  obtain ⟨sc', sd', hS'⟩ := mStackSpine_push hS hj₀ htop
  obtain ⟨pc', pd', hD', hprev, hlast⟩ := mDerivInv_append hD (hw L pc pd)
  exact ⟨L + 1, pc', pd', depth + 1, sc', sd', hD',
    mStackSpine_upgrade hS' ⟨1, rfl⟩ hprev,
    L, lt_succ_self_pam L, hlast.symm⟩

theorem mStackProofInv_init : MStackProofInv (0 : PAM M) 0 := by
  refine ⟨1, 0, 0 + 1, 0, 0, 0 + 1, ?_, ?_, 0, zero_lt_one_pam, (mBeta_singleton 0).symm⟩
  · refine ⟨le_rfl, mBeta_singleton 0, fun i hi ↦ ?_⟩
    have hi0 : i = 0 := le_zero_iff_pam.mp (lt_add_one_iff_le.mp (by simpa using hi))
    subst hi0
    rw [mBeta_singleton 0]
    exact mIsZFStep_zero 0 (0 + 1) 0
  · exact ⟨mBeta_singleton 0, fun k hk ↦ absurd hk (not_lt_zero_pam k), (mBeta_singleton 0).symm⟩

theorem mZf393ClauseDispatch_preserves_inv {top stk : PAM M}
    (hInv : MStackProofInv top stk) (ac p1 p2 p3 : PAM M) :
    let res := mZf393ClauseDispatch top stk ac p1 p2 p3
    MStackProofInv res.1 res.2 := by
  dsimp only
  have hax_step : ∀ {w : PAM M}, MIsZFAxiom w → MStackProofInv w (mPair top stk) :=
    fun hw ↦ mStackProofInv_push_step hInv (fun _ _ _ ↦ Or.inl hw)
  rcases lt_or_ge ac ((20 : ℕ) : PAM M) with hlt20 | hge20
  · obtain ⟨k, hk20, rfl⟩ := lt_natCast_iff.mp hlt20
    have hk_cases :
        k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
        k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 :=
      by omega
    rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [mZf393ClauseDispatch, ↓reduceIte]
      exact hax_step mIsZFAxiom_zero
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p1, rfl⟩))))))))))))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inl ⟨p1, rfl⟩)))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inl ⟨p1, p2, rfl⟩))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨p1, p2, p3, rfl⟩)))))))))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      split_ifs with hcond
      · exact hax_step mIsZFAxiom_zero
      · rcases not_or.mp hcond with ⟨hne1, hne2⟩
        exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨p1, p2, p3, hne1, Ne.symm hne2, rfl⟩))))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨p1, p2, p3, rfl⟩)))))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨p1, p2, rfl⟩)))))))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p1, p2, p3, rfl⟩)))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨p1, p2, p3, rfl⟩))))))))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨p1, p2, p3, rfl⟩)))))))))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨p1, p2, p3, rfl⟩))))))))))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inl ⟨p1, p2, p3, rfl⟩))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))
    · -- Clause 16: `DET` (Modus Ponens)
      simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      rcases hInv with ⟨L, pc, pd, depth, sc, sd, hD, hS, j₀, hj₀, htop⟩
      obtain ⟨sc₀, sd₀, hS₀⟩ := mStackSpine_push hS hj₀ htop
      obtain ⟨⟨j₁, hj₁, hφ_eq⟩, hS₁⟩ := mStackSpine_pop hD hS₀
      obtain ⟨⟨j₂, hj₂, hmaj_eq⟩, hS₂⟩ := mStackSpine_pop hD hS₁
      split_ifs with hmp
      · have hmp_step : MIsZFStep pc pd L p1 :=
          Or.inr (Or.inl ⟨(mUnpair (mPair top stk)).1,
            (mUnpair (mUnpair (mPair top stk)).2).1,
            j₁, j₂, hj₁, hj₂, hφ_eq.symm, hmaj_eq.symm, hmp.symm⟩)
        obtain ⟨pc', pd', hD', hprev, hlast⟩ := mDerivInv_append hD hmp_step
        exact ⟨L + 1, pc', pd', depth + 1 - 1 - 1, sc₀, sd₀, hD',
          mStackSpine_upgrade hS₂ ⟨1, rfl⟩ hprev,
          L, lt_succ_self_pam L, hlast.symm⟩
      · exact ⟨L, pc, pd, depth + 1 - 1 - 1, sc₀, sd₀, hD, hS₂,
          0, lt_of_lt_of_le zero_lt_one_pam hD.1, hD.2.1.symm⟩
    · -- Clause 17: `GEN` (Generalization)
      simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      rcases hInv with ⟨L, pc, pd, depth, sc, sd, hD, hS, j₀, hj₀, htop⟩
      obtain ⟨sc₀, sd₀, hS₀⟩ := mStackSpine_push hS hj₀ htop
      obtain ⟨⟨j₁, hj₁, hφ_eq⟩, hS₁⟩ := mStackSpine_pop hD hS₀
      have hgen_step : MIsZFStep pc pd L (mZfAll p1 (mUnpair (mPair top stk)).1) :=
        Or.inr (Or.inr ⟨p1, (mUnpair (mPair top stk)).1, j₁, hj₁, hφ_eq.symm, rfl⟩)
      obtain ⟨pc', pd', hD', hprev, hlast⟩ := mDerivInv_append hD hgen_step
      exact ⟨L + 1, pc', pd', depth + 1 - 1, sc₀, sd₀, hD',
        mStackSpine_upgrade hS₁ ⟨1, rfl⟩ hprev,
        L, lt_succ_self_pam L, hlast.symm⟩
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨p1, p2, p3, rfl⟩)))))))
    · simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
      exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨p1, p2, rfl⟩))))))))
  · have hne : ∀ (n : ℕ), n < 20 → ac ≠ (n : PAM M) :=
      fun n hn heq ↦ not_lt_of_ge hge20 (heq ▸ natCast_lt_iff.mpr hn)
    unfold mZf393ClauseDispatch
    simp only [hne 0 (by decide), hne 1 (by decide), hne 2 (by decide), hne 3 (by decide),
      hne 4 (by decide), hne 5 (by decide), hne 6 (by decide), hne 7 (by decide),
      hne 8 (by decide), hne 9 (by decide), hne 10 (by decide), hne 11 (by decide),
      hne 12 (by decide), hne 13 (by decide), hne 14 (by decide), hne 15 (by decide),
      hne 16 (by decide), hne 17 (by decide), hne 18 (by decide), hne 19 (by decide),
      ↓reduceIte]
    exact hax_step (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))))))))))

theorem mZf393MainNext_preserves_inv {c : MZfMainCfg M}
    (hInv : MStackProofInv c.topwff c.wffstack) :
    MStackProofInv (mZf393MainNext c).topwff (mZf393MainNext c).wffstack := by
  unfold mZf393MainNext
  exact mZf393ClauseDispatch_preserves_inv hInv _ _ _ _

/-- **Internalized Soundness**: if `zf393`'s `main()` loop halts in `PAM M`, then
`MZFInconsistent M` holds. -/
theorem mZfInconsistent_of_mZf393MainHalts (hHalts : MZf393MainHalts M) :
    MZFInconsistent M := by
  rcases hHalts with ⟨N, c_end, ⟨tc, td, h0, hstep, hN⟩, hnone⟩
  have hdef : PADef1 (fun k : PAM M ↦ k ≤ N →
      MStackProofInv (mUnpackMainCfg (mBeta tc td k)).topwff
        (mUnpackMainCfg (mBeta tc td k)).wffstack) := by
    have hz : PAFunN 1 (fun a : Fin 1 → PAM M ↦ mBeta tc td (a 0)) :=
      paFun_mBeta (paFun_const tc) (paFun_const td) (paFun_proj 0)
    have htop : PAFunN 1 (fun a : Fin 1 → PAM M ↦ (mUnpackMainCfg (mBeta tc td (a 0))).topwff) :=
      paFun_mUnpair_fst (paFun_mUnpair_snd (paFun_mUnpair_snd hz))
    have hstk : PAFunN 1 (fun a : Fin 1 → PAM M ↦ (mUnpackMainCfg (mBeta tc td (a 0))).wffstack) :=
      paFun_mUnpair_snd (paFun_mUnpair_snd (paFun_mUnpair_snd hz))
    exact paDef_imp (paDef_le (paFun_proj 0) (paFun_const N)) (paDef_mStackProofInv htop hstk)
  have hinv_end := ind1 hdef
    (fun _ ↦ by
      rw [h0, mUnpackMainCfg_mPackMainCfg]
      exact mStackProofInv_init)
    (fun k ih hk1 ↦ by
      have hklt : k < N := hk1
      have hst := hstep k hklt
      obtain ⟨_, heq⟩ := mZf393MainStep_eq_some_iff.mp hst
      rw [heq]
      exact mZf393MainNext_preserves_inv (ih (le_of_lt hklt)))
    N le_rfl
  rw [hN, mUnpackMainCfg_mPackMainCfg] at hinv_end
  have hinv_next := mZf393MainNext_preserves_inv hinv_end
  unfold mZf393MainStep at hnone
  split_ifs at hnone with htop1
  rcases hinv_next with ⟨L, pc, pd, _, _, _, ⟨_, _, hsteps⟩, _, j, hj, htop_j⟩
  refine ⟨j, pc, pd, fun i hi ↦ hsteps i (lt_of_le_of_lt hi hj), ?_⟩
  rw [← htop_j, htop1, mZfMem_zero_zero]

/-! ## Section 3: Completeness (`mZf393MainHalts_of_mZfInconsistent`) -/

/-- Pack a 4-tuple `(ac, p1, p2, p3)` into a single element of `PAM M`. -/
noncomputable def mPackInstr (ac p1 p2 p3 : PAM M) : PAM M :=
  mPair ac (mPair p1 (mPair p2 p3))

/-- Execute one packed 4-tuple instruction `s` on `(top, stk)`. -/
noncomputable def mExecInstr (s top stk : PAM M) : PAM M × PAM M :=
  let u1 := mUnpair s
  let u2 := mUnpair u1.2
  let u3 := mUnpair u2.2
  mZf393ClauseDispatch top stk u1.1 u2.1 u3.1 u3.2

@[simp]
theorem mExecInstr_mPackInstr (ac p1 p2 p3 top stk : PAM M) :
    mExecInstr (mPackInstr ac p1 p2 p3) top stk =
      mZf393ClauseDispatch top stk ac p1 p2 p3 := by
  simp [mExecInstr, mPackInstr]

theorem paFun_mExecInstr {k : ℕ} {fs ftop fstk : (Fin k → PAM M) → PAM M}
    (hs : PAFunN k fs) (htop : PAFunN k ftop) (hstk : PAFunN k fstk) :
    PAFunN k (fun u ↦ (mExecInstr (fs u) (ftop u) (fstk u)).1) ∧
    PAFunN k (fun u ↦ (mExecInstr (fs u) (ftop u) (fstk u)).2) := by
  have hac := paFun_mUnpair_fst hs
  have hu1 := paFun_mUnpair_snd hs
  have hp1 := paFun_mUnpair_fst hu1
  have hu2 := paFun_mUnpair_snd hu1
  have hp2 := paFun_mUnpair_fst hu2
  have hp3 := paFun_mUnpair_snd hu2
  exact paFun_mZf393ClauseDispatch htop hstk hac hp1 hp2 hp3

/-- $\beta$-coded execution of instruction sequence `(len, lc, ld)` from `(top₀, stk₀)` to
`(top₁, stk₁)`. -/
def MInstrSeqExec (len lc ld top₀ stk₀ top₁ stk₁ : PAM M) : Prop :=
  ∃ ec ed : PAM M,
    mBeta ec ed 0 = mPair top₀ stk₀ ∧
    (∀ k < len,
      let p := mUnpair (mBeta ec ed k)
      let p' := mExecInstr (mBeta lc ld k) p.1 p.2
      mBeta ec ed (k + 1) = mPair p'.1 p'.2) ∧
    mBeta ec ed len = mPair top₁ stk₁

theorem paDef_mInstrSeqExec {n : ℕ}
    {flen flc fld ftop₀ fstk₀ ftop₁ fstk₁ : (Fin n → PAM M) → PAM M}
    (hlen : PAFunN n flen) (hlc : PAFunN n flc) (hld : PAFunN n fld)
    (htop₀ : PAFunN n ftop₀) (hstk₀ : PAFunN n fstk₀)
    (htop₁ : PAFunN n ftop₁) (hstk₁ : PAFunN n fstk₁) :
    PADefN n (fun u ↦
      MInstrSeqExec (flen u) (flc u) (fld u) (ftop₀ u) (fstk₀ u) (ftop₁ u) (fstk₁ u)) := by
  let fec : (Fin (n + 2) → PAM M) → PAM M := fun v ↦ (Fin.init v) (Fin.last n)
  let fed : (Fin (n + 2) → PAM M) → PAM M := fun v ↦ v (Fin.last (n + 1))
  have hec : PAFunN (n + 2) fec := paFun_weaken (paFun_proj (Fin.last n))
  have hed : PAFunN (n + 2) fed := paFun_proj (Fin.last (n + 1))
  have hlen2 := paFun_weaken (paFun_weaken hlen)
  have hlc2 := paFun_weaken (paFun_weaken hlc)
  have hld2 := paFun_weaken (paFun_weaken hld)
  have htop₀2 := paFun_weaken (paFun_weaken htop₀)
  have hstk₀2 := paFun_weaken (paFun_weaken hstk₀)
  have htop₁2 := paFun_weaken (paFun_weaken htop₁)
  have hstk₁2 := paFun_weaken (paFun_weaken hstk₁)
  have h0 : PADefN (n + 2) (fun v ↦
      mBeta (fec v) (fed v) 0 =
        mPair (ftop₀ (Fin.init (Fin.init v))) (fstk₀ (Fin.init (Fin.init v)))) :=
    paDef_eq (paFun_mBeta hec hed (paFun_const 0)) (paFun_mPair htop₀2 hstk₀2)
  have hlast : PADefN (n + 2) (fun v ↦
      mBeta (fec v) (fed v) (flen (Fin.init (Fin.init v))) =
        mPair (ftop₁ (Fin.init (Fin.init v))) (fstk₁ (Fin.init (Fin.init v)))) :=
    paDef_eq (paFun_mBeta hec hed hlen2) (paFun_mPair htop₁2 hstk₁2)
  have hstep : PADefN (n + 2) (fun v ↦
      ∀ k < flen (Fin.init (Fin.init v)),
        let p := mUnpair (mBeta (fec v) (fed v) k)
        let p' := mExecInstr (mBeta (flc (Fin.init (Fin.init v))) (fld (Fin.init (Fin.init v))) k)
          p.1 p.2
        mBeta (fec v) (fed v) (k + 1) = mPair p'.1 p'.2) := by
    have hk3 : PAFunN (n + 3) (fun w ↦ w (Fin.last (n + 2))) :=
      paFun_proj (M := M) (Fin.last (n + 2))
    have hec3 := paFun_weaken hec
    have hed3 := paFun_weaken hed
    have hlc3 := paFun_weaken hlc2
    have hld3 := paFun_weaken hld2
    have hlen3 := paFun_weaken hlen2
    have hbk := paFun_mBeta hec3 hed3 hk3
    have hbk1 := paFun_mBeta hec3 hed3 (paFun_add hk3 (paFun_const 1))
    have hlck := paFun_mBeta hlc3 hld3 hk3
    obtain ⟨hex1, hex2⟩ :=
      paFun_mExecInstr hlck (paFun_mUnpair_fst hbk) (paFun_mUnpair_snd hbk)
    refine paDefN_congr (fun v ↦ ?_)
      (paDef_all (paDef_imp (paDef_lt hk3 hlen3) (paDef_eq hbk1 (paFun_mPair hex1 hex2))))
    simp only [Fin.init_snoc, Fin.snoc_last]
  refine paDefN_congr (fun u ↦ ?_) (paDef_ex (paDef_ex (paDef_and h0 (paDef_and hstep hlast))))
  simp only [MInstrSeqExec, fec, fed, Fin.init_snoc, Fin.snoc_last]

theorem mInstrSeqExec_singleton (s top₀ stk₀ : PAM M) :
    MInstrSeqExec 1 s (s + 1) top₀ stk₀
      (mExecInstr s top₀ stk₀).1 (mExecInstr s top₀ stk₀).2 := by
  let p₀ := mPair top₀ stk₀
  let p₁ := mPair (mExecInstr s top₀ stk₀).1 (mExecInstr s top₀ stk₀).2
  obtain ⟨ec, ed, hprev, hlast⟩ := mBeta_snoc 1 p₀ (p₀ + 1) p₁
  refine ⟨ec, ed, (hprev 0 zero_lt_one_pam).trans (mBeta_singleton p₀), ?_, hlast⟩
  intro k hk
  have hk0 : k = 0 := le_zero_iff_pam.mp (lt_add_one_iff_le.mp (by simpa using hk))
  subst hk0
  dsimp only
  rw [zero_add, hlast, hprev 0 zero_lt_one_pam, mBeta_singleton p₀, mBeta_singleton s,
    mUnpair_mPair]

theorem mInstrSeqExec_concat {len₁ lc₁ ld₁ len₂ lc₂ ld₂ : PAM M}
    (hlen₂ : 1 ≤ len₂) :
    ∃ lc ld : PAM M,
      ∀ {top₀ stk₀ top₁ stk₁ top₂ stk₂ : PAM M},
        MInstrSeqExec len₁ lc₁ ld₁ top₀ stk₀ top₁ stk₁ →
        MInstrSeqExec len₂ lc₂ ld₂ top₁ stk₁ top₂ stk₂ →
        MInstrSeqExec (len₁ + len₂) lc ld top₀ stk₀ top₂ stk₂ := by
  obtain ⟨lc, ld, hlc_l, hlc_r⟩ := mBeta_concat len₁ lc₁ ld₁ len₂ lc₂ ld₂
  refine ⟨lc, ld, ?_⟩
  rintro top₀ stk₀ top₁ stk₁ top₂ stk₂ ⟨ec₁, ed₁, he0₁, hest₁, hel₁⟩ ⟨ec₂, ed₂, he0₂, hest₂, hel₂⟩
  obtain ⟨m₂, rfl⟩ : ∃ m₂ : PAM M, len₂ = m₂ + 1 := by
    rcases eq_zero_or_exists_succ len₂ with rfl | ⟨m₂, rfl⟩
    · exact absurd hlen₂ (not_le_of_gt zero_lt_one_pam)
    · exact ⟨m₂, rfl⟩
  obtain ⟨ec, ed, he_l, he_r⟩ := mBeta_concat len₁ ec₁ ed₁ (m₂ + 1 + 1) ec₂ ed₂
  refine ⟨ec, ed, ?_, ?_, ?_⟩
  · rcases eq_zero_or_exists_succ len₁ with rfl | ⟨m₁, rfl⟩
    · have h0 := he_r 0 ⟨m₂ + 1, by ring⟩
      rw [zero_add] at h0
      exact h0.trans (he0₂.trans (hel₁.symm.trans he0₁))
    · exact (he_l 0 ⟨m₁, by ring⟩).trans he0₁
  · intro i hi
    dsimp only
    rcases lt_or_ge i len₁ with hilt | hige
    · rw [hlc_l i hilt, he_l i hilt]
      rcases lt_or_eq_of_le (show i + 1 ≤ len₁ from hilt) with hilt1 | hi1_eq
      · rw [he_l (i + 1) hilt1]
        exact hest₁ i hilt
      · have hst_i := hest₁ i hilt
        dsimp only at hst_i
        rw [hi1_eq] at hst_i ⊢
        have h0 := he_r 0 ⟨m₂ + 1, by ring⟩
        rw [add_zero] at h0
        rw [h0, he0₂, ← hel₁]
        exact hst_i
    · let j := i - len₁
      have hij : len₁ + j = i := add_sub_of_le_pam hige
      have hjlt : j < m₂ + 1 := by
        rcases hi with ⟨w, hw⟩
        exact ⟨w, (add_left_inj_pam len₁).mp (by
          calc len₁ + (j + 1 + w)
            _ = (len₁ + j) + 1 + w := by ring
            _ = i + 1 + w := by rw [hij]
            _ = len₁ + (m₂ + 1) := hw)⟩
      have hij1 : i + 1 = len₁ + (j + 1) := by rw [← hij]; ring
      rw [← hij, hlc_r j hjlt, he_r j (lt_trans hjlt (lt_succ_self_pam (m₂ + 1))), hij,
        hij1, he_r (j + 1) (add_lt_add_right_pam hjlt 1)]
      exact hest₂ j hjlt
  · exact (he_r (m₂ + 1) (lt_succ_self_pam (m₂ + 1))).trans hel₂

private theorem mInstrSeq_of_axiom {w : PAM M} (hax : MIsZFAxiom w) :
    ∃ len lc ld : PAM M,
      1 ≤ len ∧ ∀ top stk : PAM M, MInstrSeqExec len lc ld top stk w (mPair top stk) := by
  have single : ∀ ac p1 p2 p3 : PAM M,
      (∀ top stk : PAM M, mZf393ClauseDispatch top stk ac p1 p2 p3 = (w, mPair top stk)) →
      ∃ len lc ld : PAM M,
        1 ≤ len ∧ ∀ top stk : PAM M, MInstrSeqExec len lc ld top stk w (mPair top stk) := by
    intro ac p1 p2 p3 hev
    let s := mPackInstr ac p1 p2 p3
    refine ⟨1, s, s + 1, le_rfl, fun top stk ↦ ?_⟩
    have h := mInstrSeqExec_singleton s top stk
    dsimp only [s] at h
    rw [mExecInstr_mPackInstr, hev top stk] at h
    exact h
  rcases hax with rfl | ⟨φ, ψ, χ, rfl⟩ | ⟨φ, rfl⟩ | ⟨φ, ψ, rfl⟩ | ⟨x, φ, ψ, rfl⟩ |
      ⟨x, y, z, hxz, hzy, rfl⟩ | ⟨x, y, φ, rfl⟩ | ⟨x, φ, rfl⟩ | ⟨x, y, rfl⟩ |
      ⟨x, y, z, rfl⟩ | ⟨x, y, z, rfl⟩ | ⟨x, y, z, rfl⟩ | rfl | ⟨φ, rfl⟩ | rfl | rfl | rfl
  · refine single ((0 : ℕ) : PAM M) 0 0 0 (fun top stk ↦ ?_)
    simp [mZf393ClauseDispatch]
  · refine single ((14 : ℕ) : PAM M) φ ψ χ (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((3 : ℕ) : PAM M) φ 0 0 (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((5 : ℕ) : PAM M) φ ψ 0 (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((10 : ℕ) : PAM M) x φ ψ (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((7 : ℕ) : PAM M) x y z (fun top stk ↦ ?_)
    have hcond : ¬ (x = z ∨ y = z) := not_or.mpr ⟨hxz, Ne.symm hzy⟩
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, hcond, ↓reduceIte]
  · refine single ((8 : ℕ) : PAM M) x y φ (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((19 : ℕ) : PAM M) x φ 0 (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((9 : ℕ) : PAM M) x y 0 (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((11 : ℕ) : PAM M) x y z (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((6 : ℕ) : PAM M) x y z (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((13 : ℕ) : PAM M) x y z (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((15 : ℕ) : PAM M) 0 0 0 (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((1 : ℕ) : PAM M) φ 0 0 (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((2 : ℕ) : PAM M) 0 0 0 (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((4 : ℕ) : PAM M) 0 0 0 (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]
  · refine single ((20 : ℕ) : PAM M) 0 0 0 (fun top stk ↦ ?_)
    simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff, ↓reduceIte]

theorem exists_mInstrSeq_of_mZfInconsistent (hInc : MZFInconsistent M) :
    ∃ m lc ld : PAM M,
      ∀ top stk : PAM M, MInstrSeqExec (m + 1) lc ld top stk 1 (mPair top stk) := by
  rcases hInc with ⟨n_prf, pc, pd, hsteps, hgoal⟩
  have hdef : PADef1 (fun i : PAM M ↦ i ≤ n_prf →
      ∃ len lc ld : PAM M,
        1 ≤ len ∧
        ∀ top stk : PAM M, MInstrSeqExec len lc ld top stk (mBeta pc pd i) (mPair top stk)) := by
    let flen : (Fin 4 → PAM M) → PAM M :=
      fun v ↦ (Fin.init (Fin.init v)) (Fin.last 1)
    let flc : (Fin 4 → PAM M) → PAM M :=
      fun v ↦ (Fin.init v) (Fin.last 2)
    let fld : (Fin 4 → PAM M) → PAM M :=
      fun v ↦ v (Fin.last 3)
    have hlen4 : PAFunN 4 flen := paFun_weaken (paFun_weaken (paFun_proj (M := M) (Fin.last 1)))
    have hlc4 : PAFunN 4 flc := paFun_weaken (paFun_proj (M := M) (Fin.last 2))
    have fld4 : PAFunN 4 fld := paFun_proj (M := M) (Fin.last 3)
    have hi6 : PAFunN 6 (fun w ↦
        (Fin.init (Fin.init (Fin.init (Fin.init (Fin.init w))))) 0) :=
      paFun_weaken (paFun_weaken (paFun_weaken
        (paFun_weaken (paFun_weaken (paFun_proj (M := M) 0)))))
    have htop6 : PAFunN 6 (fun w ↦ (Fin.init w) (Fin.last 4)) :=
      paFun_weaken (paFun_proj (M := M) (Fin.last 4))
    have hstk6 : PAFunN 6 (fun w ↦ w (Fin.last 5)) :=
      paFun_proj (M := M) (Fin.last 5)
    have hexec6 := paDef_mInstrSeqExec
      (paFun_weaken (paFun_weaken hlen4))
      (paFun_weaken (paFun_weaken hlc4))
      (paFun_weaken (paFun_weaken fld4))
      htop6 hstk6
      (paFun_mBeta (paFun_const pc) (paFun_const pd) hi6)
      (paFun_mPair htop6 hstk6)
    have hall4 : PADefN 4 (fun v ↦ ∀ top stk : PAM M,
        MInstrSeqExec (flen v) (flc v) (fld v) top stk
          (mBeta pc pd ((Fin.init (Fin.init (Fin.init v))) 0)) (mPair top stk)) := by
      refine paDefN_congr (fun v ↦ ?_) (paDef_all (paDef_all hexec6))
      simp only [Fin.init_snoc, Fin.snoc_last]
    have hex1 : PADefN 1 (fun a ↦ ∃ len lc ld : PAM M,
        1 ≤ len ∧
        ∀ top stk : PAM M,
          MInstrSeqExec len lc ld top stk (mBeta pc pd (a 0)) (mPair top stk)) := by
      refine paDefN_congr (fun a ↦ ?_)
        (paDef_ex (paDef_ex (paDef_ex
          (paDef_and (paDef_le (paFun_const 1) hlen4) hall4))))
      simp only [flen, flc, fld, Fin.init_snoc, Fin.snoc_last]
    exact paDef_imp (paDef_le (paFun_proj 0) (paFun_const n_prf)) hex1
  have hall := strong_ind1 hdef (fun i ih hi ↦ ?_)
  · obtain ⟨len, lc, ld, h1len, hexec⟩ := hall n_prf le_rfl
    rw [hgoal, mZfMem_zero_zero] at hexec
    rcases eq_zero_or_exists_succ len with rfl | ⟨m, rfl⟩
    · exact absurd h1len (not_le_of_gt zero_lt_one_pam)
    · exact ⟨m, lc, ld, hexec⟩
  · rcases hsteps i hi with hax | ⟨φ, χ, j₁, j₂, hj₁, hj₂, hb₁, hb₂, hχ⟩ | ⟨x, φ, j, hj, hbj, hw⟩
    · exact mInstrSeq_of_axiom hax
    · obtain ⟨len₂, lc₂, ld₂, h1₂, hex₂⟩ := ih j₂ hj₂ (le_trans (le_of_lt hj₂) hi)
      obtain ⟨len₁, lc₁, ld₁, h1₁, hex₁⟩ := ih j₁ hj₁ (le_trans (le_of_lt hj₁) hi)
      rw [hb₂, hχ] at hex₂
      rw [hb₁] at hex₁
      obtain ⟨lc₁₂, ld₁₂, hcat₁₂⟩ := mInstrSeqExec_concat (lc₁ := lc₂) (ld₁ := ld₂) h1₁
      let s_mp := mPackInstr ((16 : ℕ) : PAM M) (mBeta pc pd i) 0 0
      obtain ⟨lc', ld', hcat'⟩ :=
        mInstrSeqExec_concat (len₁ := len₂ + len₁) (lc₁ := lc₁₂) (ld₁ := ld₁₂)
          (len₂ := 1) (lc₂ := s_mp) (ld₂ := s_mp + 1) le_rfl
      refine ⟨len₂ + len₁ + 1, lc', ld', le_trans h1₂ ⟨len₁ + 1, by ring⟩, fun top stk ↦ ?_⟩
      have hstep_mp : MInstrSeqExec 1 s_mp (s_mp + 1)
          φ (mPair (mZfImp φ (mBeta pc pd i)) (mPair top stk))
          (mBeta pc pd i) (mPair top stk) := by
        have h := mInstrSeqExec_singleton s_mp φ
          (mPair (mZfImp φ (mBeta pc pd i)) (mPair top stk))
        dsimp only [s_mp] at h
        rw [mExecInstr_mPackInstr] at h
        simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff,
          mUnpair_mPair, ↓reduceIte] at h
        exact h
      exact hcat' (hcat₁₂ (hex₂ top stk) (hex₁ _ _)) hstep_mp
    · obtain ⟨len₁, lc₁, ld₁, h1₁, hex₁⟩ := ih j hj (le_trans (le_of_lt hj) hi)
      rw [hbj] at hex₁
      let s_gen := mPackInstr ((17 : ℕ) : PAM M) x 0 0
      obtain ⟨lc', ld', hcat'⟩ :=
        mInstrSeqExec_concat (len₁ := len₁) (lc₁ := lc₁) (ld₁ := ld₁)
          (len₂ := 1) (lc₂ := s_gen) (ld₂ := s_gen + 1) le_rfl
      refine ⟨len₁ + 1, lc', ld', le_trans h1₁ ⟨1, rfl⟩, fun top stk ↦ ?_⟩
      have hstep_gen : MInstrSeqExec 1 s_gen (s_gen + 1)
          φ (mPair top stk) (mBeta pc pd i) (mPair top stk) := by
        have h := mInstrSeqExec_singleton s_gen φ (mPair top stk)
        dsimp only [s_gen] at h
        rw [mExecInstr_mPackInstr] at h
        simp only [mZf393ClauseDispatch, natCast_inj_pam, Nat.reduceEqDiff,
          mUnpair_mPair, ↓reduceIte, ← hw] at h
        exact h
      exact hcat' (hex₁ top stk) hstep_gen

/-- Prepend a packed 4-tuple instruction `s` onto a Cantor-paired `prooflist` code `rest`. -/
noncomputable def mPackProofStep (s rest : PAM M) : PAM M :=
  let u1 := mUnpair s
  let u2 := mUnpair u1.2
  let u3 := mUnpair u2.2
  mPair u1.1 (mPair u2.1 (mPair u3.1 (mPair u3.2 rest))) + 1

theorem paFun_mPackProofStep {k : ℕ} {fs frest : (Fin k → PAM M) → PAM M}
    (hs : PAFunN k fs) (hrest : PAFunN k frest) :
    PAFunN k (fun u ↦ mPackProofStep (fs u) (frest u)) := by
  have hu1 := paFun_mUnpair_snd hs
  have hu2 := paFun_mUnpair_snd hu1
  exact paFun_add
    (paFun_mPair (paFun_mUnpair_fst hs)
      (paFun_mPair (paFun_mUnpair_fst hu1)
        (paFun_mPair (paFun_mUnpair_fst hu2)
          (paFun_mPair (paFun_mUnpair_snd hu2) hrest))))
    (paFun_const 1)

theorem mZf393MainNext_mPackProofStep (s rest np top stk : PAM M) :
    mZf393MainNext ⟨mPackProofStep s rest, np, top, stk⟩ =
      ⟨rest, np, (mExecInstr s top stk).1, (mExecInstr s top stk).2⟩ := by
  have hne : mPackProofStep s rest ≠ 0 := add_one_ne_zero_pam _
  simp only [mZf393MainNext, hne, ↓reduceIte]
  unfold mPackProofStep mExecInstr
  rw [add_one_sub_one_pam]
  simp only [mUnpair_mPair]

theorem mZf393MainNext_zero_prooflist (P top stk : PAM M) :
    mZf393MainNext ⟨0, P, top, stk⟩ = mZf393MainNext ⟨P + 1, P + 1, top, stk⟩ := by
  simp [mZf393MainNext]

theorem mZf393MainNext_prooflist_lt {c : MZfMainCfg M} {pl' : PAM M}
    (hpl : c.prooflist = pl' + 1) :
    (mZf393MainNext c).prooflist < c.prooflist ∧
    (mZf393MainNext c).nextproof = c.nextproof := by
  rw [mZf393MainNext]
  simp only [hpl, add_one_ne_zero_pam, ↓reduceIte, add_one_sub_one_pam]
  have hle : (mUnpair (mUnpair (mUnpair (mUnpair pl').2).2).2).2 ≤ pl' :=
    le_trans (mUnpair_snd_le _)
      (le_trans (mUnpair_snd_le _) (le_trans (mUnpair_snd_le _) (mUnpair_snd_le _)))
  exact ⟨lt_of_le_of_lt hle (lt_succ_self_pam pl'), trivial⟩

/-- Fold instructions `mBeta lc ld 0 .. mBeta lc ld m` from right to left into a $\beta$-coded
`prooflist` suffix table `(fc, fd)` with `plSuffix k = mBeta fc fd (m + 1 - k)`. -/
theorem exists_mProofListSuffix (m lc ld : PAM M) :
    ∃ fc fd : PAM M,
      mBeta fc fd 0 = 0 ∧
      ∀ k ≤ m, mBeta fc fd (m + 1 - k) =
        mPackProofStep (mBeta lc ld k) (mBeta fc fd (m - k)) := by
  have hdef : PADef1 (fun r : PAM M ↦ r ≤ m + 1 →
      ∃ fc fd : PAM M,
        mBeta fc fd 0 = 0 ∧
        ∀ j < r, mBeta fc fd (j + 1) =
          mPackProofStep (mBeta lc ld (m - j)) (mBeta fc fd j)) := by
    let ffc : (Fin 3 → PAM M) → PAM M := fun v ↦ (Fin.init v) (Fin.last 1)
    let ffd : (Fin 3 → PAM M) → PAM M := fun v ↦ v (Fin.last 2)
    have hfc : PAFunN 3 ffc := paFun_weaken (paFun_proj (Fin.last 1))
    have hfd : PAFunN 3 ffd := paFun_proj (Fin.last 2)
    have h0 : PADefN 3 (fun v ↦ mBeta (ffc v) (ffd v) 0 = 0) :=
      paDef_eq (paFun_mBeta hfc hfd (paFun_const 0)) (paFun_const 0)
    have hstep : PADefN 3 (fun v ↦
        ∀ j < (Fin.init (Fin.init v)) 0,
          mBeta (ffc v) (ffd v) (j + 1) =
            mPackProofStep (mBeta lc ld (m - j)) (mBeta (ffc v) (ffd v) j)) := by
      have hj4 : PAFunN 4 (fun w ↦ w (Fin.last 3)) := paFun_proj (M := M) (Fin.last 3)
      have hr4 : PAFunN 4 (fun w ↦ (Fin.init (Fin.init (Fin.init w))) 0) :=
        paFun_weaken (paFun_weaken (paFun_weaken (paFun_proj (M := M) 0)))
      have hfc4 := paFun_weaken hfc
      have hfd4 := paFun_weaken hfd
      refine paDefN_congr (fun v ↦ ?_)
        (paDef_all (paDef_imp (paDef_lt hj4 hr4)
          (paDef_eq
            (paFun_mBeta hfc4 hfd4 (paFun_add hj4 (paFun_const 1)))
            (paFun_mPackProofStep
              (paFun_mBeta (paFun_const lc) (paFun_const ld) (paFun_sub (paFun_const m) hj4))
              (paFun_mBeta hfc4 hfd4 hj4)))))
      simp only [Fin.init_snoc, Fin.snoc_last]
    have hex1 : PADefN 1 (fun a ↦ ∃ fc fd : PAM M,
        mBeta fc fd 0 = 0 ∧
        ∀ j < a 0, mBeta fc fd (j + 1) =
          mPackProofStep (mBeta lc ld (m - j)) (mBeta fc fd j)) := by
      refine paDefN_congr (fun a ↦ ?_) (paDef_ex (paDef_ex (paDef_and h0 hstep)))
      simp only [ffc, ffd, Fin.init_snoc, Fin.snoc_last]
    exact paDef_imp (paDef_le (paFun_proj 0) (paFun_const (m + 1))) hex1
  obtain ⟨fc, fd, h0, hstep⟩ := ind1 hdef
    (fun _ ↦ ⟨0, 0 + 1, mBeta_singleton 0, fun _ hj ↦ absurd hj (not_lt_zero_pam _)⟩)
    (fun r ih hr1 ↦ by
      have hrlt : r < m + 1 := hr1
      obtain ⟨fc₀, fd₀, h0₀, hst₀⟩ := ih (le_of_lt hrlt)
      obtain ⟨fc', fd', hprev, hlast⟩ :=
        mBeta_snoc (r + 1) fc₀ fd₀ (mPackProofStep (mBeta lc ld (m - r)) (mBeta fc₀ fd₀ r))
      refine ⟨fc', fd', (hprev 0 ⟨r, by ring⟩).trans h0₀, fun j hj ↦ ?_⟩
      rcases le_iff_lt_or_eq.mp (lt_add_one_iff_le.mp hj) with hjlt | rfl
      · rw [hprev (j + 1) (add_lt_add_right_pam hjlt 1),
          hprev j (lt_trans hjlt (lt_succ_self_pam r)), hst₀ j hjlt]
      · rw [hlast, hprev j (lt_succ_self_pam j)])
    (m + 1) le_rfl
  refine ⟨fc, fd, h0, fun k hk ↦ ?_⟩
  let r := m - k
  have hkr : k + r = m := add_sub_of_le_pam hk
  have hrlt : r < m + 1 := ⟨k, by rw [← hkr]; ring⟩
  have hm1k : m + 1 - k = r + 1 :=
    (sub_eq_iff_eq_add_pam (le_trans hk ⟨1, rfl⟩)).mpr (by rw [← hkr]; ring)
  have hmr : m - r = k :=
    (sub_eq_iff_eq_add_pam ⟨k, by rw [← hkr]; ring⟩).mpr (by rw [← hkr]; ring)
  rw [hm1k]
  have h := hstep r hrlt
  rwa [hmr] at h

private theorem mStep_of_not_halts {n : PAM M} {c : MZfMainCfg M}
    (hno : ¬ MZf393MainHalts M) (htr : mMainTracesTo n mZfMainInit c) :
    mZf393MainStep c = some (mZf393MainNext c) := by
  rcases hs : mZf393MainStep c with _ | c'
  · exact False.elim (hno ⟨n, c, htr, hs⟩)
  · obtain ⟨_, heq⟩ := mZf393MainStep_eq_some_iff.mp hs
    exact congrArg some heq

private theorem mDrain_prooflist (hno : ¬ MZf393MainHalts M) (pl : PAM M) :
    ∀ {n : PAM M} {c : MZfMainCfg M},
      mMainTracesTo n mZfMainInit c →
      c.prooflist = pl →
      ∃ (m : PAM M) (c' : MZfMainCfg M),
        mMainTracesTo m mZfMainInit c' ∧ c'.prooflist = 0 ∧ c'.nextproof = c.nextproof := by
  have hdef : PADef1 (fun p : PAM M ↦
      ∀ n z : PAM M,
        mMainTracesTo n mZfMainInit (mUnpackMainCfg z) →
        (mUnpackMainCfg z).prooflist = p →
        ∃ m z' : PAM M,
          mMainTracesTo m mZfMainInit (mUnpackMainCfg z') ∧
          (mUnpackMainCfg z').prooflist = 0 ∧
          (mUnpackMainCfg z').nextproof = (mUnpackMainCfg z).nextproof) := by
    let fp : (Fin 3 → PAM M) → PAM M := fun v ↦ (Fin.init (Fin.init v)) 0
    let fn : (Fin 3 → PAM M) → PAM M := fun v ↦ (Fin.init v) (Fin.last 1)
    let fz : (Fin 3 → PAM M) → PAM M := fun v ↦ v (Fin.last 2)
    have hp3 : PAFunN 3 fp := paFun_weaken (paFun_weaken (paFun_proj (M := M) 0))
    have hn3 : PAFunN 3 fn := paFun_weaken (paFun_proj (Fin.last 1))
    have hz3 : PAFunN 3 fz := paFun_proj (Fin.last 2)
    have htr_in : PADefN 3 (fun v ↦
        mMainTracesTo (fn v) mZfMainInit (mUnpackMainCfg (fz v))) :=
      paDef_mMainTracesTo hn3 (paFun_const (mPackMainCfg mZfMainInit))
        (paFunN_congr (fun v ↦ (mPackMainCfg_mUnpackMainCfg (fz v)).symm) hz3)
    have hpl_in : PADefN 3 (fun v ↦ (mUnpackMainCfg (fz v)).prooflist = fp v) :=
      paDef_eq (paFun_mUnpair_fst hz3) hp3
    let fm5 : (Fin 5 → PAM M) → PAM M := fun w ↦ (Fin.init w) (Fin.last 3)
    let fz'5 : (Fin 5 → PAM M) → PAM M := fun w ↦ w (Fin.last 4)
    have hm5 : PAFunN 5 fm5 := paFun_weaken (paFun_proj (Fin.last 3))
    have hz'5 : PAFunN 5 fz'5 := paFun_proj (Fin.last 4)
    have hz5 := paFun_weaken (paFun_weaken hz3)
    have htr_out : PADefN 5 (fun w ↦
        mMainTracesTo (fm5 w) mZfMainInit (mUnpackMainCfg (fz'5 w))) :=
      paDef_mMainTracesTo hm5 (paFun_const (mPackMainCfg mZfMainInit))
        (paFunN_congr (fun w ↦ (mPackMainCfg_mUnpackMainCfg (fz'5 w)).symm) hz'5)
    have hex3 : PADefN 3 (fun v ↦ ∃ m z' : PAM M,
        mMainTracesTo m mZfMainInit (mUnpackMainCfg z') ∧
        (mUnpackMainCfg z').prooflist = 0 ∧
        (mUnpackMainCfg z').nextproof = (mUnpackMainCfg (fz v)).nextproof) := by
      refine paDefN_congr (fun v ↦ ?_)
        (paDef_ex (paDef_ex
          (paDef_and htr_out
            (paDef_and
              (paDef_eq (paFun_mUnpair_fst hz'5) (paFun_const 0))
              (paDef_eq
                (paFun_mUnpair_fst (paFun_mUnpair_snd hz'5))
                (paFun_mUnpair_fst (paFun_mUnpair_snd hz5)))))))
      simp only [fm5, fz'5, mUnpackMainCfg, Fin.init_snoc, Fin.snoc_last]
    refine paDefN_congr (fun a ↦ ?_)
      (paDef_all (paDef_all (paDef_imp htr_in (paDef_imp hpl_in hex3))))
    simp only [fp, fn, fz, Fin.init_snoc, Fin.snoc_last]
  have hall := strong_ind1 hdef (fun p ih n z htr hpl ↦ ?_)
  · intro n c htr hpl
    obtain ⟨m, z', htr', hpl', hnp'⟩ :=
      hall pl n (mPackMainCfg c) (by rwa [mUnpackMainCfg_mPackMainCfg])
        (by rwa [mUnpackMainCfg_mPackMainCfg])
    rw [mUnpackMainCfg_mPackMainCfg] at hnp'
    exact ⟨m, mUnpackMainCfg z', htr', hpl', hnp'⟩
  · rcases eq_zero_or_exists_succ p with rfl | ⟨p', rfl⟩
    · exact ⟨n, z, htr, hpl, rfl⟩
    · have hst := mStep_of_not_halts hno htr
      have htr1 := mMainTracesTo_snoc htr hst
      obtain ⟨hlt, hnp⟩ := mZf393MainNext_prooflist_lt hpl
      obtain ⟨m, z', htr', hpl', hnp'⟩ :=
        ih (mZf393MainNext (mUnpackMainCfg z)).prooflist (hlt.trans_eq hpl)
          (n + 1) (mPackMainCfg (mZf393MainNext (mUnpackMainCfg z)))
          (by rwa [mUnpackMainCfg_mPackMainCfg])
          (by rw [mUnpackMainCfg_mPackMainCfg])
      rw [mUnpackMainCfg_mPackMainCfg] at hnp'
      exact ⟨m, z', htr', hpl', hnp'.trans hnp⟩

private theorem mReaches_nextproof (hno : ¬ MZf393MainHalts M) (N : PAM M) :
    ∃ (n : PAM M) (c : MZfMainCfg M),
      mMainTracesTo n mZfMainInit c ∧ c.prooflist = 0 ∧ c.nextproof = N := by
  have hdef : PADef1 (fun P : PAM M ↦
      ∃ n z : PAM M,
        mMainTracesTo n mZfMainInit (mUnpackMainCfg z) ∧
        (mUnpackMainCfg z).prooflist = 0 ∧
        (mUnpackMainCfg z).nextproof = P) := by
    let fn : (Fin 3 → PAM M) → PAM M := fun v ↦ (Fin.init v) (Fin.last 1)
    let fz : (Fin 3 → PAM M) → PAM M := fun v ↦ v (Fin.last 2)
    have hn3 : PAFunN 3 fn := paFun_weaken (paFun_proj (Fin.last 1))
    have hz3 : PAFunN 3 fz := paFun_proj (Fin.last 2)
    have hp3 : PAFunN 3 (fun v ↦ (Fin.init (Fin.init v)) 0) :=
      paFun_weaken (paFun_weaken (paFun_proj (M := M) 0))
    refine paDefN_congr (fun a ↦ ?_)
      (paDef_ex (paDef_ex
        (paDef_and
          (paDef_mMainTracesTo hn3 (paFun_const (mPackMainCfg mZfMainInit))
            (paFunN_congr (fun v ↦ (mPackMainCfg_mUnpackMainCfg (fz v)).symm) hz3))
          (paDef_and
            (paDef_eq (paFun_mUnpair_fst hz3) (paFun_const 0))
            (paDef_eq (paFun_mUnpair_fst (paFun_mUnpair_snd hz3)) hp3)))))
    simp only [fn, fz, mUnpackMainCfg, Fin.init_snoc, Fin.snoc_last]
  obtain ⟨n, z, htr, hpl, hnp⟩ := ind1 hdef
    ⟨0, mPackMainCfg mZfMainInit,
      by rw [mUnpackMainCfg_mPackMainCfg]; exact mMainTracesTo_zero mZfMainInit,
      by rw [mUnpackMainCfg_mPackMainCfg]; rfl,
      by rw [mUnpackMainCfg_mPackMainCfg]; rfl⟩
    (fun P ⟨n, z, htr, hpl0, hnp⟩ ↦ by
      have hst := mStep_of_not_halts hno htr
      have htr1 := mMainTracesTo_snoc htr hst
      have hnp_next : (mZf393MainNext (mUnpackMainCfg z)).nextproof = P + 1 := by
        simp [mZf393MainNext, hpl0, hnp]
      obtain ⟨m, c', htr', hpl', hnp'⟩ := mDrain_prooflist hno _ htr1 rfl
      exact ⟨m, mPackMainCfg c', by rwa [mUnpackMainCfg_mPackMainCfg],
        by rwa [mUnpackMainCfg_mPackMainCfg],
        by rw [mUnpackMainCfg_mPackMainCfg]; exact hnp'.trans hnp_next⟩)
    N
  exact ⟨n, mUnpackMainCfg z, htr, hpl, hnp⟩

/-- **Internalized Completeness**: if `MZFInconsistent M` holds, then `zf393`'s `main()` loop
halts in `PAM M`. -/
theorem mZf393MainHalts_of_mZfInconsistent (hInc : MZFInconsistent M) :
    MZf393MainHalts M := by
  by_contra hno
  obtain ⟨m, lc, ld, hexec⟩ := exists_mInstrSeq_of_mZfInconsistent hInc
  obtain ⟨fc, fd, hfc0, hfc_step⟩ := exists_mProofListSuffix m lc ld
  let pl₀ := mBeta fc fd (m + 1)
  have hpl₀_eq : pl₀ = mPackProofStep (mBeta lc ld 0) (mBeta fc fd m) := by
    simpa [pl₀, sub_zero_pam] using hfc_step 0 (zero_le_pam m)
  let P := pl₀ - 1
  have hP1 : P + 1 = pl₀ := by
    dsimp only [P]
    rw [hpl₀_eq, mPackProofStep, add_one_sub_one_pam]
  obtain ⟨n₀, c₀, htr₀, hpl_c₀, hnp_c₀⟩ := mReaches_nextproof hno P
  have hc₀_eq : c₀ = ⟨0, P, c₀.topwff, c₀.wffstack⟩ := by
    cases c₀; dsimp at hpl_c₀ hnp_c₀; subst hpl_c₀ hnp_c₀; rfl
  rw [hc₀_eq] at htr₀
  obtain ⟨ec, ed, he0, hest, hel⟩ := hexec c₀.topwff c₀.wffstack
  rcases eq_zero_or_exists_succ m with rfl | ⟨m', rfl⟩
  · -- Single-instruction proof (`m = 0`): step 0 already produces `topwff = 1`.
    have hnext : (mZf393MainNext ⟨0, P, c₀.topwff, c₀.wffstack⟩).topwff = 1 := by
      rw [mZf393MainNext_zero_prooflist, hP1, hpl₀_eq, mZf393MainNext_mPackProofStep]
      have h0 := hest 0 (lt_succ_self_pam 0)
      dsimp only at h0
      rw [hel, he0, mUnpair_mPair] at h0
      dsimp only at h0
      exact (mPair_injective h0).1.symm
    have hnone : mZf393MainStep ⟨0, P, c₀.topwff, c₀.wffstack⟩ = none := by
      simp [mZf393MainStep, hnext]
    exact hno ⟨n₀, ⟨0, P, c₀.topwff, c₀.wffstack⟩, htr₀, hnone⟩
  · -- Multi-instruction proof (`m = m' + 1`): step 0 enters `P + 1`, then run up to `k = m' + 1`.
    let cfgAt : PAM M → MZfMainCfg M := fun k ↦
      ⟨mBeta fc fd (m' + 1 + 1 - k), P + 1,
       (mUnpair (mBeta ec ed k)).1, (mUnpair (mBeta ec ed k)).2⟩
    have hstep0 := mStep_of_not_halts hno htr₀
    have hnext0 : mZf393MainNext ⟨0, P, c₀.topwff, c₀.wffstack⟩ = cfgAt 1 := by
      rw [mZf393MainNext_zero_prooflist, hP1, hpl₀_eq, mZf393MainNext_mPackProofStep]
      have hsub1 : m' + 1 + 1 - 1 = m' + 1 := add_one_sub_one_pam (m' + 1)
      have he1 := hest 0 ⟨m' + 1, by ring⟩
      dsimp only at he1
      rw [zero_add, he0, mUnpair_mPair] at he1
      dsimp only at he1
      dsimp only [cfgAt]
      rw [hsub1, he1, mUnpair_mPair, ← hpl₀_eq, hP1]
    rw [hnext0] at hstep0
    have htr1 : mMainTracesTo (n₀ + 1) mZfMainInit (cfgAt 1) := mMainTracesTo_snoc htr₀ hstep0
    have hdef : PADef1 (fun k : PAM M ↦ 1 ≤ k → k ≤ m' + 1 →
        mMainTracesTo (n₀ + k) mZfMainInit (cfgAt k)) := by
      have hk : PAFunN 1 (fun a : Fin 1 → PAM M ↦ a 0) := paFun_proj 0
      have hpl_k := paFun_mBeta (paFun_const fc) (paFun_const fd)
        (paFun_sub (paFun_const (m' + 1 + 1)) hk)
      have hek := paFun_mBeta (paFun_const ec) (paFun_const ed) hk
      have hpack_k : PAFunN 1 (fun a : Fin 1 → PAM M ↦ mPackMainCfg (cfgAt (a 0))) :=
        paFun_mPair hpl_k
          (paFun_mPair (paFun_const (P + 1))
            (paFun_mPair (paFun_mUnpair_fst hek) (paFun_mUnpair_snd hek)))
      exact paDef_imp (paDef_le (paFun_const 1) hk)
        (paDef_imp (paDef_le hk (paFun_const (m' + 1)))
          (paDef_mMainTracesTo (paFun_add (paFun_const n₀) hk)
            (paFun_const (mPackMainCfg mZfMainInit)) hpack_k))
    have htr_m := ind1 hdef
      (fun h10 _ ↦ absurd h10 (not_le_of_gt zero_lt_one_pam))
      (fun k ih _ hk1_le ↦ by
        rcases eq_zero_or_exists_succ k with rfl | ⟨k', rfl⟩
        · simpa using htr1
        · have h1k : 1 ≤ k' + 1 := ⟨k', by ring⟩
          have hkle : k' + 1 ≤ m' + 1 := le_trans ⟨1, rfl⟩ hk1_le
          have hk_lt_m : k' + 1 < m' + 1 := hk1_le
          have htr_k := ih h1k hkle
          have hst_k := mStep_of_not_halts hno htr_k
          have hpl_step := hfc_step (k' + 1) hkle
          have he_step := hest (k' + 1) (lt_trans hk_lt_m (lt_succ_self_pam (m' + 1)))
          dsimp only at he_step
          have hsub_eq : m' + 1 - (k' + 1) = m' + 1 + 1 - (k' + 1 + 1) := by
            have ⟨d, hd⟩ := hkle
            have h1 : m' + 1 - (k' + 1) = d :=
              (sub_eq_iff_eq_add_pam hkle).mpr (by rw [← hd])
            have h2 : m' + 1 + 1 - (k' + 1 + 1) = d :=
              (sub_eq_iff_eq_add_pam ⟨d, by rw [← hd]; ring⟩).mpr (by rw [← hd]; ring)
            exact h1.trans h2.symm
          have hnext_k : mZf393MainNext (cfgAt (k' + 1)) = cfgAt (k' + 1 + 1) := by
            dsimp only [cfgAt]
            rw [hpl_step, mZf393MainNext_mPackProofStep, hsub_eq, he_step, mUnpair_mPair]
          rw [hnext_k] at hst_k
          have htr_succ := mMainTracesTo_snoc htr_k hst_k
          rwa [add_assoc] at htr_succ)
      (m' + 1) ⟨m', by ring⟩ le_rfl
    -- Now `cfgAt (m' + 1)` executes the final instruction `m' + 1`, producing `topwff = 1`.
    have hpl_last := hfc_step (m' + 1) le_rfl
    have he_last := hest (m' + 1) (lt_succ_self_pam (m' + 1))
    dsimp only at he_last
    rw [hel] at he_last
    have htop_last : (mZf393MainNext (cfgAt (m' + 1))).topwff = 1 := by
      dsimp only [cfgAt]
      rw [hpl_last, mZf393MainNext_mPackProofStep]
      exact (mPair_injective he_last).1.symm
    have hnone_last : mZf393MainStep (cfgAt (m' + 1)) = none := by
      simp [mZf393MainStep, htop_last]
    exact hno ⟨n₀ + (m' + 1), cfgAt (m' + 1), htr_m, hnone_last⟩

/-! ## Section 4: Bidirectional Equivalence in `PAM M` and `PAProvable` Main Theorems -/

/-- Layer 3 equivalence in `PAM M`: `MZf393MainHalts M ↔ MZFInconsistent M`. -/
theorem mZf393MainHalts_iff_mZfInconsistent :
    MZf393MainHalts M ↔ MZFInconsistent M :=
  ⟨mZfInconsistent_of_mZf393MainHalts, mZf393MainHalts_of_mZfInconsistent⟩

/-- End-to-end equivalence in every first-order `PAModel M`:
`Machines.zf393` halts iff `MZFInconsistent M` holds. -/
theorem mHalts_zf393_iff_mZfInconsistent :
    mHalts M Machines.zf393 ↔ MZFInconsistent M :=
  ⟨fun h ↦ mZfInconsistent_of_mZf393MainHalts (mZf393MainHalts_of_mHalts_zf393 h),
   fun h ↦ mHalts_zf393_of_mZf393MainHalts (mZf393MainHalts_of_mZfInconsistent h)⟩

/-- End-to-end equivalence in every first-order `PAModel M`:
`Machines.zf380` halts iff `MZFInconsistent M` holds. -/
theorem mHalts_zf380_iff_mZfInconsistent :
    mHalts M Machines.zf380 ↔ MZFInconsistent M :=
  mHalts_zf380_iff_zf393.trans mHalts_zf393_iff_mZfInconsistent

end Model

/-- **Peano Arithmetic proves `zf_393` halts iff `ZF` is inconsistent**
($\mathrm{PA} \vdash \mathrm{Halts}(\mathtt{zf\_393}) \leftrightarrow
  \neg\mathrm{Con}(\mathrm{ZF})$). -/
theorem paProvable_halts_zf393_iff_zfInconsistent :
    PAProvable ((paHalts Machines.zf393).iff paZFInconsistent) := by
  rw [paProvable_iff_holdsIn_all_models]
  intro M _ _ v
  rw [← PAM.holdsIn_iff_raw (fun x ↦ ⟨v x⟩)]
  simp only [PAFormula.HoldsIn, paHalts_holdsIn_iff, paZFInconsistent_holdsIn_iff]
  exact ⟨(mHalts_zf393_iff_mZfInconsistent (M := M)).mp,
    (mHalts_zf393_iff_mZfInconsistent (M := M)).mpr⟩

/-- **Peano Arithmetic proves `zf_380` halts iff `ZF` is inconsistent**
($\mathrm{PA} \vdash \mathrm{Halts}(\mathtt{zf\_380}) \leftrightarrow
  \neg\mathrm{Con}(\mathrm{ZF})$). -/
theorem paProvable_halts_zf380_iff_zfInconsistent :
    PAProvable ((paHalts Machines.zf380).iff paZFInconsistent) := by
  rw [paProvable_iff_holdsIn_all_models]
  intro M _ _ v
  rw [← PAM.holdsIn_iff_raw (fun x ↦ ⟨v x⟩)]
  simp only [PAFormula.HoldsIn, paHalts_holdsIn_iff, paZFInconsistent_holdsIn_iff]
  exact ⟨(mHalts_zf380_iff_mZfInconsistent (M := M)).mp,
    (mHalts_zf380_iff_mZfInconsistent (M := M)).mpr⟩

end ConjectureMachines.Semantics.PA
end
