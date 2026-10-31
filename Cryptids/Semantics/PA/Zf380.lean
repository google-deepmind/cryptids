/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.PA.Arithmetic
public import Cryptids.Zf380

/-!
# Internal `PA` Equivalence Between `zf_380` and `zf_393`

This module internalizes the macro-step state-renumbering bisimulation between `Machines.zf380` and
`Machines.zf393` from `Cryptids.Zf380` inside an arbitrary first-order `PAModel M` via `PAM M`,
yielding:

- `mHalts_zf380_iff_zf393`: in every `PAModel M`,
  `mHalts M Machines.zf380 ↔ mHalts M Machines.zf393`.
- `paProvable_halts_zf380_iff_zf393`:
  `PAProvable ((paHalts Machines.zf380).iff (paHalts Machines.zf393))`.
-/

@[expose] public section

namespace ConjectureMachines.Semantics.PA

open Turing (Dir)
open StateTransition
open ConjectureMachines.Zf380
  (candM refM zf380Trans candM_transition_eq_nat
   renum mapState validState validState1 validState1_of_validState validState_next checkNext
   expectedTransition isThreeStep isFiveStepLRLR isFiveStepLLRR isSevenStepLLLRRR
   isNineStepLRLLLRRR isMultiStep
   midP midS lrlrP1 lrlrS1 lrlrP2 lrlrS2 llrrP1 llrrP2 llrrS1 llrrS2
   lllrrrP1 lllrrrP2 lllrrrP3 lllrrrS1 lllrrrS2 lllrrrS3
   transition_oneStep
   transition_threeStep_1 transition_threeStep_2 transition_threeStep_3 threeStep_not_none
   transition_fiveStepLRLR_1 transition_fiveStepLRLR_2 transition_fiveStepLRLR_3
   transition_fiveStepLRLR_4 transition_fiveStepLRLR_5 fiveStepLRLR_not_none
   transition_fiveStepLLRR_1 transition_fiveStepLLRR_2 transition_fiveStepLLRR_3
   transition_fiveStepLLRR_4 transition_fiveStepLLRR_5 fiveStepLLRR_not_none
   transition_sevenStepLLLRRR_1 transition_sevenStepLLLRRR_2 transition_sevenStepLLLRRR_3
   transition_sevenStepLLLRRR_4 transition_sevenStepLLLRRR_5 transition_sevenStepLLLRRR_6
   transition_sevenStepLLLRRR_7 sevenStepLLLRRR_not_none
   transition_nineStep_0a transition_nineStep_0b transition_nineStep_1 transition_nineStep_2
   transition_nineStep_3 transition_nineStep_4 transition_nineStep_5 transition_nineStep_6
   transition_nineStep_7 nineStepLRLLLRRR_not_none
   cfgOfFast bootR_39753 boot_cand boot_ref rel_boot)

section Model
variable {M : Type*} [PAStructure M] [PAModel M]
open PAM

/-! ## Section 1: Standard `nSteps` Equivalence and Boot Lifting -/

private theorem zf380_nSteps_eq_layer1_nSteps {N : ℕ} [NeZero N] (tm : Machine N 2) :
    ∀ (k : ℕ) (c : Cfg N 2),
      ConjectureMachines.Zf380.nSteps tm k c =
        ConjectureMachines.Semantics.Riemann.Layer1.nSteps tm k c
  | 0, _ => rfl
  | k + 1, c => by
    simp only [ConjectureMachines.Zf380.nSteps_succ,
      ConjectureMachines.Semantics.Riemann.Layer1.nSteps_succ]
    cases step tm c with
    | none => rfl
    | some c' => exact zf380_nSteps_eq_layer1_nSteps tm k c'

/-- Standard `k : ℕ` step counts in `mTracesTo` coincide with `mNSteps`. -/
theorem mTracesTo_natCast_iff_mNSteps {states : ℕ} {tm : Machine states 2}
    (k : ℕ) (a b : MCfg states M) :
    mTracesTo tm (k : PAM M) a b ↔ mNSteps tm k a = some b := by
  refine ⟨fun htr ↦ ?_, mTracesTo_of_mNSteps⟩
  rcases htr with ⟨c, d, h0, hsteps, hlast⟩
  have hwalk : ∀ j : ℕ, j ≤ k →
      ∃ bj : MCfg states M, mNSteps tm j a = some bj ∧ mBeta c d (j : PAM M) = mEncodeCfg bj := by
    intro j hj
    induction j with
    | zero => exact ⟨a, rfl, by simpa using h0⟩
    | succ j ih =>
      obtain ⟨bj, hns, hbj⟩ := ih (Nat.le_of_succ_le hj)
      have hjlt : (j : PAM M) < (k : PAM M) := (natCast_lt_iff (M := M)).mpr hj
      obtain ⟨x, y, hx, hy, hst⟩ := hsteps (j : PAM M) hjlt
      have hxb : x = bj := mEncodeCfg_injective (hx.symm.trans hbj)
      subst hxb
      refine ⟨y, ?_, by simpa [Nat.cast_succ] using hy⟩
      rw [mNSteps_add tm j 1 a, hns]
      simpa [mNSteps] using hst
  obtain ⟨bk, hnsk, hbk⟩ := hwalk k le_rfl
  have hbkeq : bk = b := mEncodeCfg_injective (hbk.symm.trans hlast)
  subst hbkeq
  exact hnsk

private theorem mBoot_cand :
    mTracesTo Machines.zf380 ((39753 : ℕ) : PAM M) mInit
      (embedCfg (M := M) (cfgOfFast 64 [] 0 bootR_39753)) := by
  have hb := boot_cand
  rw [zf380_nSteps_eq_layer1_nSteps] at hb
  have htr := mTracesTo_of_nSteps (M := M) hb
  simpa only [embedCfg_init] using htr

private theorem mBoot_ref :
    mTracesTo Machines.zf393 ((39753 : ℕ) : PAM M) mInit
      (embedCfg (M := M) (cfgOfFast 64 [] 0 bootR_39753)) := by
  have hb := boot_ref
  rw [zf380_nSteps_eq_layer1_nSteps] at hb
  have htr := mTracesTo_of_nSteps (M := M) hb
  simpa only [embedCfg_init] using htr

/-! ## Section 2: `MCfg` Macro-Steps and Simulation Relation `MRel` -/

/-- Simulation relation between `Machines.zf393` and `Machines.zf380` on `MCfg` over `PAM M`. -/
def MRel (c₁ : MCfg 393 M) (c₂ : MCfg 380 M) : Prop :=
  validState c₁.state.val
    (mBit (mHalf (mHalf c₁.left))) (mBit (mHalf c₁.left)) (mBit c₁.left)
    c₁.head (mBit c₁.right) = true ∧
  c₂ = ⟨mapState c₁.state.val (mBit c₁.left) c₁.head, c₁.head, c₁.left, c₁.right⟩

private theorem mBit_eq_iff_mod_eq (x : PAM M) (b : Fin 2) :
    mBit x = b ↔ x % 2 = (b.val : PAM M) := by
  rw [← mBit_val_eq_mod]
  exact ⟨fun h ↦ congrArg (fun u : Fin 2 ↦ (u.val : PAM M)) h,
    fun h ↦ Fin.ext (natCast_inj_pam.mp h)⟩

/-- First-order definability of `MRel` on configuration codes in `PAM M`. -/
theorem paDef_mRelCode {k : ℕ} {fx₁ fx₂ : (Fin k → PAM M) → PAM M}
    (hx₁ : PAFunN k fx₁) (hx₂ : PAFunN k fx₂) :
    PADefN k (fun a ↦ ∃ (c₁ : MCfg 393 M) (c₂ : MCfg 380 M),
      fx₁ a = mEncodeCfg c₁ ∧ fx₂ a = mEncodeCfg c₂ ∧ MRel c₁ c₂) := by
  have htuple : ∀ (q : Fin 393) (h l0 l1 l2 r0 : Fin 2),
      PADefN k (fun a ↦
        validState q.val l2 l1 l0 h r0 = true ∧
        ∃ L R : PAM M,
          L % 2 = (l0.val : PAM M) ∧
          (L / 2) % 2 = (l1.val : PAM M) ∧
          ((L / 2) / 2) % 2 = (l2.val : PAM M) ∧
          R % 2 = (r0.val : PAM M) ∧
          fx₁ a = mPair (q.val : PAM M) (mPair (h.val : PAM M) (mPair L R)) ∧
          fx₂ a = mPair ((mapState q.val l0 h).val : PAM M)
            (mPair (h.val : PAM M) (mPair L R))) := by
    intro q h l0 l1 l2 r0
    let fL : (Fin (k + 2) → PAM M) → PAM M := fun w ↦ w ⟨k, by omega⟩
    let fR : (Fin (k + 2) → PAM M) → PAM M := fun w ↦ w (Fin.last (k + 1))
    have hL : PAFunN (k + 2) fL := paFun_proj ⟨k, by omega⟩
    have hR : PAFunN (k + 2) fR := paFun_proj (Fin.last (k + 1))
    have hx₁' : PAFunN (k + 2) (fun w ↦ fx₁ (Fin.init (Fin.init w))) :=
      paFun_weaken (paFun_weaken hx₁)
    have hx₂' : PAFunN (k + 2) (fun w ↦ fx₂ (Fin.init (Fin.init w))) :=
      paFun_weaken (paFun_weaken hx₂)
    have hLdiv1 := paFun_div hL (paFun_const 2)
    have hLdiv2 := paFun_div hLdiv1 (paFun_const 2)
    have hbody : PADefN (k + 2) (fun w : Fin (k + 2) → PAM M ↦
        fL w % 2 = (l0.val : PAM M) ∧
        (fL w / 2) % 2 = (l1.val : PAM M) ∧
        ((fL w / 2) / 2) % 2 = (l2.val : PAM M) ∧
        fR w % 2 = (r0.val : PAM M) ∧
        fx₁ (Fin.init (Fin.init w)) =
          mPair (q.val : PAM M) (mPair (h.val : PAM M) (mPair (fL w) (fR w))) ∧
        fx₂ (Fin.init (Fin.init w)) =
          mPair ((mapState q.val l0 h).val : PAM M)
            (mPair (h.val : PAM M) (mPair (fL w) (fR w)))) :=
      paDef_and (paDef_eq (paFun_mod hL (paFun_const 2)) (paFun_const _))
        (paDef_and (paDef_eq (paFun_mod hLdiv1 (paFun_const 2)) (paFun_const _))
          (paDef_and (paDef_eq (paFun_mod hLdiv2 (paFun_const 2)) (paFun_const _))
            (paDef_and (paDef_eq (paFun_mod hR (paFun_const 2)) (paFun_const _))
              (paDef_and
                (paDef_eq hx₁'
                  (paFun_mPair (paFun_const _) (paFun_mPair (paFun_const _) (paFun_mPair hL hR))))
                (paDef_eq hx₂'
                  (paFun_mPair (paFun_const _)
                    (paFun_mPair (paFun_const _) (paFun_mPair hL hR))))))))
    have hp : PADefN k (fun _ : Fin k → PAM M ↦ validState q.val l2 l1 l0 h r0 = true) := by
      cases validState q.val l2 l1 l0 h r0
      · exact paDefN_congr (fun _ ↦ by simp) (paDef_false k)
      · exact paDefN_congr (fun _ ↦ by simp) (paDef_true k)
    refine paDef_and hp (paDefN_congr (fun a ↦ ?_) (paDef_ex (paDef_ex hbody)))
    refine exists_congr fun L ↦ exists_congr fun R ↦ ?_
    dsimp only [fL, fR]
    rw [Fin.snoc_last, Fin.init_snoc, Fin.init_snoc,
      fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k), fin_snoc_eq]
  refine paDefN_congr (fun a ↦ ?_)
    (paDef_fin_exists fun q ↦ paDef_fin_exists fun h ↦ paDef_fin_exists fun l0 ↦
      paDef_fin_exists fun l1 ↦ paDef_fin_exists fun l2 ↦ paDef_fin_exists fun r0 ↦
        htuple q h l0 l1 l2 r0)
  constructor
  · rintro ⟨q, h, l0, l1, l2, r0, hv, L, R, hl0, hl1, hl2, hr0, hx1, hx2⟩
    have hb0 : mBit L = l0 := (mBit_eq_iff_mod_eq L l0).mpr hl0
    have hb1 : mBit (mHalf L) = l1 := (mBit_eq_iff_mod_eq (L / 2) l1).mpr hl1
    have hb2 : mBit (mHalf (mHalf L)) = l2 := (mBit_eq_iff_mod_eq ((L / 2) / 2) l2).mpr hl2
    have hbr : mBit R = r0 := (mBit_eq_iff_mod_eq R r0).mpr hr0
    refine ⟨⟨q, h, L, R⟩, ⟨mapState q.val l0 h, h, L, R⟩, hx1, hx2, ?_⟩
    simp only [MRel, hb0, hb1, hb2, hbr, hv, true_and]
  · rintro ⟨⟨q, h, L, R⟩, c₂, hx1, hx2, hv, rfl⟩
    refine ⟨q, h, mBit L, mBit (mHalf L), mBit (mHalf (mHalf L)), mBit R, hv, L, R,
      (mBit_eq_iff_mod_eq L _).mp rfl,
      (mBit_eq_iff_mod_eq (L / 2) _).mp rfl,
      (mBit_eq_iff_mod_eq ((L / 2) / 2) _).mp rfl,
      (mBit_eq_iff_mod_eq R _).mp rfl, hx1, hx2⟩

private theorem mRel_boot :
    MRel (embedCfg (M := M) (cfgOfFast 64 [] 0 bootR_39753))
      (embedCfg (M := M) (cfgOfFast 64 [] 0 bootR_39753)) := by
  obtain ⟨hv, hmap⟩ := rel_boot
  have hst := congrArg Cfg.state hmap
  dsimp only [cfgOfFast] at hv hst ⊢
  simp only [MRel, embedCfg, mHalf_embedHalf, mBit_embedHalf]
  exact ⟨hv, by rw [← hst]⟩

private theorem mStep_of_transition_eq {q : Fin 393} {S : Fin 380} (h : Fin 2) (L R : PAM M)
    (htr : zf380Trans S.val h =
      expectedTransition q.val (mBit (mHalf L)) (mBit L) h (mBit R)) :
    mStep candM ⟨S, h, L, R⟩ =
      (mStep refM ⟨q, h, L, R⟩).map fun c ↦
        ⟨mapState c.state.val (mBit c.left) c.head, c.head, c.left, c.right⟩ := by
  dsimp only [mStep]
  rw [candM_transition_eq_nat S h, htr, ConjectureMachines.Zf393.zf393Trans_eq q h]
  rcases e : ConjectureMachines.Zf393.zf393Trans q h with _ | ⟨w, d, q'⟩
  · simp [expectedTransition, Nat.mod_eq_of_lt q.isLt, e]
  · cases d <;> simp [expectedTransition, Nat.mod_eq_of_lt q.isLt, e]

private theorem mStep_lr_pair {q₁ P S : Fin 380} (h : Fin 2) (L R : PAM M)
    (h1 : zf380Trans q₁.val h = some (h, Dir.left, P))
    (h2 : zf380Trans P.val (mBit L) = some (mBit L, Dir.right, S)) :
    mNSteps candM 2 ⟨q₁, h, L, R⟩ = some ⟨S, h, L, R⟩ := by
  have hs1 : mStep candM ⟨q₁, h, L, R⟩ = some ⟨P, mBit L, mHalf L, mCons h R⟩ := by
    simp [mStep, candM_transition_eq_nat, h1]
  have hs2 : mStep candM ⟨P, mBit L, mHalf L, mCons h R⟩ = some ⟨S, h, L, R⟩ := by
    simp [mStep, candM_transition_eq_nat, h2]
  simp [mNSteps, hs1, hs2]

private theorem mStep_three_left_right {q₁ P S : Fin 380} {h : Fin 2} {L R : PAM M}
    (h1 : zf380Trans q₁.val h = some (h, Dir.left, P))
    (h2 : zf380Trans P.val (mBit L) = some (mBit L, Dir.right, S))
    {c' : MCfg 380 M} (h3 : mStep candM ⟨S, h, L, R⟩ = some c') :
    mNSteps candM 3 ⟨q₁, h, L, R⟩ = some c' := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, mNSteps_add, mStep_lr_pair h L R h1 h2]
  simpa [mNSteps] using h3

private theorem mStep_five_left_right {q₁ P₁ S₁ P₂ S₂ : Fin 380} {h : Fin 2} {L R : PAM M}
    (h1 : zf380Trans q₁.val h = some (h, Dir.left, P₁))
    (h2 : zf380Trans P₁.val (mBit L) = some (mBit L, Dir.right, S₁))
    (h3 : zf380Trans S₁.val h = some (h, Dir.left, P₂))
    (h4 : zf380Trans P₂.val (mBit L) = some (mBit L, Dir.right, S₂))
    {c' : MCfg 380 M} (h5 : mStep candM ⟨S₂, h, L, R⟩ = some c') :
    mNSteps candM 5 ⟨q₁, h, L, R⟩ = some c' := by
  rw [show (5 : ℕ) = 2 + 3 from rfl, mNSteps_add, mStep_lr_pair h L R h1 h2]
  exact mStep_three_left_right h3 h4 h5

private theorem mStep_five_left_left_right_right {q₁ P₁ P₂ S₁ S₂ : Fin 380}
    {h : Fin 2} {L R : PAM M}
    (h1 : zf380Trans q₁.val h = some (h, Dir.left, P₁))
    (h2 : zf380Trans P₁.val (mBit L) = some (mBit L, Dir.left, P₂))
    (h3 : zf380Trans P₂.val (mBit (mHalf L)) = some (mBit (mHalf L), Dir.right, S₁))
    (h4 : zf380Trans S₁.val (mBit L) = some (mBit L, Dir.right, S₂))
    {c' : MCfg 380 M} (h5 : mStep candM ⟨S₂, h, L, R⟩ = some c') :
    mNSteps candM 5 ⟨q₁, h, L, R⟩ = some c' := by
  have hs1 : mStep candM ⟨q₁, h, L, R⟩ = some ⟨P₁, mBit L, mHalf L, mCons h R⟩ := by
    simp [mStep, candM_transition_eq_nat, h1]
  have hs23 := mStep_lr_pair (mBit L) (mHalf L) (mCons h R) h2 h3
  have hs4 : mStep candM ⟨S₁, mBit L, mHalf L, mCons h R⟩ = some ⟨S₂, h, L, R⟩ := by
    simp [mStep, candM_transition_eq_nat, h4]
  rw [show (5 : ℕ) = 1 + (2 + (1 + 1)) from rfl, mNSteps_add,
    show mNSteps candM 1 ⟨q₁, h, L, R⟩ = some ⟨P₁, mBit L, mHalf L, mCons h R⟩ by
      simpa [mNSteps] using hs1]
  dsimp only [Option.bind]
  rw [mNSteps_add, hs23]
  dsimp only [Option.bind]
  simp [mNSteps, hs4, h5]

private theorem mStep_seven_left_left_left_right_right_right
    {q₁ P₁ P₂ P₃ S₁ S₂ S₃ : Fin 380} {h : Fin 2} {L R : PAM M}
    (h1 : zf380Trans q₁.val h = some (h, Dir.left, P₁))
    (h2 : zf380Trans P₁.val (mBit L) = some (mBit L, Dir.left, P₂))
    (h3 : zf380Trans P₂.val (mBit (mHalf L)) = some (mBit (mHalf L), Dir.left, P₃))
    (h4 : zf380Trans P₃.val (mBit (mHalf (mHalf L))) =
      some (mBit (mHalf (mHalf L)), Dir.right, S₁))
    (h5 : zf380Trans S₁.val (mBit (mHalf L)) = some (mBit (mHalf L), Dir.right, S₂))
    (h6 : zf380Trans S₂.val (mBit L) = some (mBit L, Dir.right, S₃))
    {c' : MCfg 380 M} (h7 : mStep candM ⟨S₃, h, L, R⟩ = some c') :
    mNSteps candM 7 ⟨q₁, h, L, R⟩ = some c' := by
  have hs1 : mStep candM ⟨q₁, h, L, R⟩ = some ⟨P₁, mBit L, mHalf L, mCons h R⟩ := by
    simp [mStep, candM_transition_eq_nat, h1]
  have hs6 : mStep candM ⟨S₂, mBit L, mHalf L, mCons h R⟩ = some ⟨S₃, h, L, R⟩ := by
    simp [mStep, candM_transition_eq_nat, h6]
  have hmid := mStep_five_left_left_right_right
    (L := mHalf L) (R := mCons h R) h2 h3 h4 h5 hs6
  rw [show (7 : ℕ) = 1 + (5 + 1) from rfl, mNSteps_add,
    show mNSteps candM 1 ⟨q₁, h, L, R⟩ = some ⟨P₁, mBit L, mHalf L, mCons h R⟩ by
      simpa [mNSteps] using hs1]
  dsimp only [Option.bind]
  rw [mNSteps_add, hmid]
  simpa [mNSteps] using h7

private theorem mStep_nine_left_right_left_left_left_right_right_right
    {q₁ P₀ q₂ P₁ P₂ P₃ S₁ S₂ S₃ : Fin 380} {h : Fin 2} {L R : PAM M}
    (h0a : zf380Trans q₁.val h = some (h, Dir.left, P₀))
    (h0b : zf380Trans P₀.val (mBit L) = some (mBit L, Dir.right, q₂))
    (h1 : zf380Trans q₂.val h = some (h, Dir.left, P₁))
    (h2 : zf380Trans P₁.val (mBit L) = some (mBit L, Dir.left, P₂))
    (h3 : zf380Trans P₂.val (mBit (mHalf L)) = some (mBit (mHalf L), Dir.left, P₃))
    (h4 : zf380Trans P₃.val (mBit (mHalf (mHalf L))) =
      some (mBit (mHalf (mHalf L)), Dir.right, S₁))
    (h5 : zf380Trans S₁.val (mBit (mHalf L)) = some (mBit (mHalf L), Dir.right, S₂))
    (h6 : zf380Trans S₂.val (mBit L) = some (mBit L, Dir.right, S₃))
    {c' : MCfg 380 M} (h7 : mStep candM ⟨S₃, h, L, R⟩ = some c') :
    mNSteps candM 9 ⟨q₁, h, L, R⟩ = some c' := by
  rw [show (9 : ℕ) = 2 + 7 from rfl, mNSteps_add, mStep_lr_pair h L R h0a h0b]
  exact mStep_seven_left_left_left_right_right_right h1 h2 h3 h4 h5 h6 h7

private theorem mStep_preserves_valid (q : Fin 393) (h : Fin 2) (L R : PAM M)
    (hv : validState q.val (mBit (mHalf (mHalf L))) (mBit (mHalf L)) (mBit L) h (mBit R) = true) :
    match mStep refM ⟨q, h, L, R⟩ with
    | none => True
    | some c =>
      validState c.state.val (mBit (mHalf (mHalf c.left))) (mBit (mHalf c.left)) (mBit c.left)
        c.head (mBit c.right) = true := by
  have hnext := validState_next q (mBit (mHalf (mHalf L))) (mBit (mHalf L)) (mBit L) h (mBit R)
  dsimp only [mStep]
  rw [ConjectureMachines.Zf393.zf393Trans_eq q h]
  rcases e : ConjectureMachines.Zf393.zf393Trans q h with _ | ⟨w, d, q'⟩
  · trivial
  · cases d
    · simpa [checkNext, Nat.mod_eq_of_lt q.isLt, e] using
        hnext (mBit (mHalf (mHalf (mHalf L)))) hv
    · simpa [checkNext, Nat.mod_eq_of_lt q.isLt, e] using
        hnext (mBit (mHalf R)) hv

private theorem zf393Trans_eq_none_of_mStep_none {q : Fin 393} {hd : Fin 2} {L R : PAM M}
    (e : mStep refM ⟨q, hd, L, R⟩ = none) :
    ConjectureMachines.Zf393.zf393Trans q hd = none := by
  dsimp only [mStep] at e
  rw [ConjectureMachines.Zf393.zf393Trans_eq] at e
  rcases htr : ConjectureMachines.Zf393.zf393Trans q hd with _ | ⟨w, d, q'⟩
  · rfl
  · cases d <;> simp [htr] at e

/-- Single-step lockstep/macro-step simulation of `refM` (`zf_393`) by `candM` (`zf_380`) in
`PAM M`. -/
theorem mRespects {c₁ : MCfg 393 M} {c₂ : MCfg 380 M} (hrel : MRel c₁ c₂) :
    match mStep refM c₁ with
    | none => mStep candM c₂ = none
    | some c₁' =>
      ∃ (k : Fin 9) (c₂' : MCfg 380 M),
        MRel c₁' c₂' ∧ mNSteps candM (k.val + 1) c₂ = some c₂' := by
  obtain ⟨hv, h⟩ := hrel
  subst h
  rcases c₁ with ⟨q, hd, L, R⟩
  have hpres := mStep_preserves_valid q hd L R hv
  have hv1 := validState1_of_validState q.val
    (mBit (mHalf (mHalf L))) (mBit (mHalf L)) (mBit L) hd (mBit R) hv
  cases h3 : isThreeStep q.val (mBit L) hd
  · cases h5a : isFiveStepLRLR q.val hd
    · cases h5b : isFiveStepLLRR q.val (mBit L) hd
      · cases h7 : isSevenStepLLLRRR q.val hd
        · cases h9 : isNineStepLRLLLRRR q.val hd
          · have hm : isMultiStep q.val (mBit L) hd = false := by
              simp [isMultiStep, h3, h5a, h5b, h7, h9]
            have hstep := mStep_of_transition_eq hd L R
              (transition_oneStep q (mBit (mHalf L)) (mBit L) hd (mBit R) hm hv1)
            rcases e : mStep refM ⟨q, hd, L, R⟩ with _ | c
            · simpa [hstep] using e
            · rw [e] at hpres
              exact ⟨⟨0, by decide⟩, ⟨mapState c.state.val (mBit c.left) c.head,
                c.head, c.left, c.right⟩, ⟨hpres, rfl⟩,
                by simp [mNSteps, hstep, e]⟩
          · have h0a := transition_nineStep_0a q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
              (mBit L) hd (mBit R) h9 hv
            have h0b := transition_nineStep_0b q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
              (mBit L) hd (mBit R) h9 hv
            have h1 := transition_nineStep_1 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
              (mBit L) hd (mBit R) h9 hv
            have h2 := transition_nineStep_2 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
              (mBit L) hd (mBit R) h9 hv
            have h3' := transition_nineStep_3 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
              (mBit L) hd (mBit R) h9 hv
            have h4 := transition_nineStep_4 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
              (mBit L) hd (mBit R) h9 hv
            have h5 := transition_nineStep_5 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
              (mBit L) hd (mBit R) h9 hv
            have h6 := transition_nineStep_6 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
              (mBit L) hd (mBit R) h9 hv
            have hstep9 := mStep_of_transition_eq hd L R
              (transition_nineStep_7 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
                (mBit L) hd (mBit R) h9 hv)
            rcases e : mStep refM ⟨q, hd, L, R⟩ with _ | c
            · exact absurd (zf393Trans_eq_none_of_mStep_none e)
                (nineStepLRLLLRRR_not_none q hd h9)
            · rw [e] at hpres hstep9
              exact ⟨⟨8, by decide⟩, ⟨mapState c.state.val (mBit c.left) c.head,
                c.head, c.left, c.right⟩, ⟨hpres, rfl⟩,
                mStep_nine_left_right_left_left_left_right_right_right
                  h0a h0b h1 h2 h3' h4 h5 h6 hstep9⟩
        · have h1 := transition_sevenStepLLLRRR_1 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
            (mBit L) hd (mBit R) h7 hv
          have h2 := transition_sevenStepLLLRRR_2 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
            (mBit L) hd (mBit R) h7 hv
          have h3' := transition_sevenStepLLLRRR_3 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
            (mBit L) hd (mBit R) h7 hv
          have h4 := transition_sevenStepLLLRRR_4 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
            (mBit L) hd (mBit R) h7 hv
          have h5 := transition_sevenStepLLLRRR_5 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
            (mBit L) hd (mBit R) h7 hv
          have h6 := transition_sevenStepLLLRRR_6 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
            (mBit L) hd (mBit R) h7 hv
          have hstep7 := mStep_of_transition_eq hd L R
            (transition_sevenStepLLLRRR_7 q (mBit (mHalf (mHalf L))) (mBit (mHalf L))
              (mBit L) hd (mBit R) h7 hv)
          rcases e : mStep refM ⟨q, hd, L, R⟩ with _ | c
          · exact absurd (zf393Trans_eq_none_of_mStep_none e)
              (sevenStepLLLRRR_not_none q hd h7)
          · rw [e] at hpres hstep7
            exact ⟨⟨6, by decide⟩, ⟨mapState c.state.val (mBit c.left) c.head,
              c.head, c.left, c.right⟩, ⟨hpres, rfl⟩,
              mStep_seven_left_left_left_right_right_right h1 h2 h3' h4 h5 h6 hstep7⟩
      · have h1 := transition_fiveStepLLRR_1 q (mBit (mHalf L)) (mBit L) hd (mBit R) h5b hv1
        have h2 := transition_fiveStepLLRR_2 q (mBit (mHalf L)) (mBit L) hd (mBit R) h5b hv1
        have h3' := transition_fiveStepLLRR_3 q (mBit (mHalf L)) (mBit L) hd (mBit R) h5b hv1
        have h4 := transition_fiveStepLLRR_4 q (mBit (mHalf L)) (mBit L) hd (mBit R) h5b hv1
        have hstep5 := mStep_of_transition_eq hd L R
          (transition_fiveStepLLRR_5 q (mBit (mHalf L)) (mBit L) hd (mBit R) h5b hv1)
        rcases e : mStep refM ⟨q, hd, L, R⟩ with _ | c
        · exact absurd (zf393Trans_eq_none_of_mStep_none e)
            (fiveStepLLRR_not_none q (mBit L) hd h5b)
        · rw [e] at hpres hstep5
          exact ⟨⟨4, by decide⟩, ⟨mapState c.state.val (mBit c.left) c.head,
            c.head, c.left, c.right⟩, ⟨hpres, rfl⟩,
            mStep_five_left_left_right_right h1 h2 h3' h4 hstep5⟩
    · have h1 := transition_fiveStepLRLR_1 q (mBit (mHalf L)) (mBit L) hd (mBit R) h5a hv1
      have h2 := transition_fiveStepLRLR_2 q (mBit (mHalf L)) (mBit L) hd (mBit R) h5a hv1
      have h3' := transition_fiveStepLRLR_3 q (mBit (mHalf L)) (mBit L) hd (mBit R) h5a hv1
      have h4 := transition_fiveStepLRLR_4 q (mBit (mHalf L)) (mBit L) hd (mBit R) h5a hv1
      have hstep5 := mStep_of_transition_eq hd L R
        (transition_fiveStepLRLR_5 q (mBit (mHalf L)) (mBit L) hd (mBit R) h5a hv1)
      rcases e : mStep refM ⟨q, hd, L, R⟩ with _ | c
      · exact absurd (zf393Trans_eq_none_of_mStep_none e)
          (fiveStepLRLR_not_none q hd h5a)
      · rw [e] at hpres hstep5
        exact ⟨⟨4, by decide⟩, ⟨mapState c.state.val (mBit c.left) c.head,
          c.head, c.left, c.right⟩, ⟨hpres, rfl⟩,
          mStep_five_left_right h1 h2 h3' h4 hstep5⟩
  · have h1 := transition_threeStep_1 q (mBit (mHalf L)) (mBit L) hd (mBit R) h3 hv1
    have h2 := transition_threeStep_2 q (mBit (mHalf L)) (mBit L) hd (mBit R) h3 hv1
    have hstep3 := mStep_of_transition_eq hd L R
      (transition_threeStep_3 q (mBit (mHalf L)) (mBit L) hd (mBit R) h3 hv1)
    rcases e : mStep refM ⟨q, hd, L, R⟩ with _ | c
    · exact absurd (zf393Trans_eq_none_of_mStep_none e)
        (threeStep_not_none q (mBit L) hd h3)
    · rw [e] at hpres hstep3
      exact ⟨⟨2, by decide⟩, ⟨mapState c.state.val (mBit c.left) c.head,
        c.head, c.left, c.right⟩, ⟨hpres, rfl⟩,
        mStep_three_left_right h1 h2 hstep3⟩

/-! ## Section 3: Bidirectional Trace Simulation in `PAM M` -/

/-- Forward trace simulation: if `MRel a₁ a₂` and `refM` (`zf_393`) halts from `a₁`, then `candM`
(`zf_380`) halts from `a₂`. -/
theorem mHaltsFrom_cand_of_ref {a₁ : MCfg 393 M} {a₂ : MCfg 380 M}
    (hrel₀ : MRel a₁ a₂) (hhalts : mHaltsFrom refM a₁) :
    mHaltsFrom candM a₂ := by
  rcases hhalts with ⟨N, f₁, ⟨c₀, d₀, h0, hsteps, hN⟩, hnone⟩
  have hdef : PADef1 (fun i : PAM M ↦ i ≤ N →
      ∃ n₂ x₂ : PAM M,
        (∃ (b₁ : MCfg 393 M) (b₂ : MCfg 380 M),
          mBeta c₀ d₀ i = mEncodeCfg b₁ ∧ x₂ = mEncodeCfg b₂ ∧ MRel b₁ b₂) ∧
        (∃ (u₂ b₂ : MCfg 380 M),
          mEncodeCfg a₂ = mEncodeCfg u₂ ∧ x₂ = mEncodeCfg b₂ ∧ mTracesTo candM n₂ u₂ b₂)) := by
    have hi_le : PADefN 1 (fun u ↦ u 0 ≤ N) := paDef_le (paFun_proj 0) (paFun_const N)
    let fn₂ : (Fin 3 → PAM M) → PAM M := fun w ↦ w 1
    let fx₂ : (Fin 3 → PAM M) → PAM M := fun w ↦ w 2
    let fbi : (Fin 3 → PAM M) → PAM M := fun w ↦ mBeta c₀ d₀ (w 0)
    have hn₂ : PAFunN 3 fn₂ := paFun_proj 1
    have hx₂ : PAFunN 3 fx₂ := paFun_proj 2
    have hbi : PAFunN 3 fbi := paFun_mBeta (paFun_const c₀) (paFun_const d₀) (paFun_proj 0)
    have hbody := paDef_and (paDef_mRelCode hbi hx₂)
      (paDef_mTracesToCode candM hn₂ (paFun_const (mEncodeCfg a₂)) hx₂)
    refine paDefN_congr (fun u ↦ ?_) (paDef_imp hi_le (paDef_ex (paDef_ex hbody)))
    refine imp_congr Iff.rfl (exists_congr fun n₂ ↦ exists_congr fun x₂ ↦ ?_)
    dsimp only [fn₂, fx₂, fbi]
    simp [Fin.snoc]
  have hsim := ind1 hdef ?_ ?_ N le_rfl
  · rcases hsim with ⟨n₂, x₂, ⟨b₁, b₂, hb₁, hx₂, hrel⟩, ⟨u₂, b₂', hu₂, hx₂', htr₂⟩⟩
    have hb₁f : b₁ = f₁ := mEncodeCfg_injective (hb₁.symm.trans hN)
    have hu₂a : u₂ = a₂ := mEncodeCfg_injective hu₂.symm
    have hb₂eq : b₂' = b₂ := mEncodeCfg_injective (hx₂'.symm.trans hx₂)
    subst b₁ u₂ b₂'
    have hres := mRespects hrel
    rw [hnone] at hres
    exact ⟨n₂, b₂, htr₂, hres⟩
  · intro _
    exact ⟨0, mEncodeCfg a₂, ⟨a₁, a₂, h0, rfl, hrel₀⟩,
      ⟨a₂, a₂, rfl, rfl, mTracesTo_zero candM a₂⟩⟩
  · intro i ih hi1
    have hilt : i < N := hi1
    rcases ih (le_of_lt hilt) with ⟨n₂, x₂, ⟨b₁, b₂, hb₁, hx₂, hrel⟩, ⟨u₂, b₂', hu₂, hx₂', htr₂⟩⟩
    have hu₂a : u₂ = a₂ := mEncodeCfg_injective hu₂.symm
    have hb₂eq : b₂' = b₂ := mEncodeCfg_injective (hx₂'.symm.trans hx₂)
    subst u₂ b₂'
    obtain ⟨p₁, q₁, hp₁, hq₁, hst₁⟩ := hsteps i hilt
    have hp₁b : p₁ = b₁ := mEncodeCfg_injective (hp₁.symm.trans hb₁)
    subst p₁
    have hres := mRespects hrel
    rw [hst₁] at hres
    rcases hres with ⟨k, c₂', hrel', hns⟩
    have htr_step := mTracesTo_of_mNSteps (M := M) hns
    exact ⟨n₂ + ((k.val + 1 : ℕ) : PAM M), mEncodeCfg c₂',
      ⟨q₁, c₂', hq₁, rfl, hrel'⟩,
      ⟨a₂, c₂', rfl, rfl, mTracesTo_trans htr₂ htr_step⟩⟩

/-- Backward trace simulation: if `MRel a₁ a₂` and `candM` (`zf_380`) halts from `a₂`, then `refM`
(`zf_393`) halts from `a₁`. -/
theorem mHaltsFrom_ref_of_cand {a₁ : MCfg 393 M} {a₂ : MCfg 380 M}
    (hrel₀ : MRel a₁ a₂) (hhalts : mHaltsFrom candM a₂) :
    mHaltsFrom refM a₁ := by
  rcases hhalts with ⟨N, f₂, ⟨c₀, d₀, h0, hsteps, hN⟩, hnone⟩
  have hdef : PADef1 (fun i : PAM M ↦ i ≤ N →
      ∃ (r : Fin 9) (n₁ x₁ x₂ : PAM M),
        (∃ (c₁ : MCfg 393 M) (c₂ : MCfg 380 M),
          x₁ = mEncodeCfg c₁ ∧ x₂ = mEncodeCfg c₂ ∧ MRel c₁ c₂) ∧
        (∃ (u₁ c₁ : MCfg 393 M),
          mEncodeCfg a₁ = mEncodeCfg u₁ ∧ x₁ = mEncodeCfg c₁ ∧ mTracesTo refM n₁ u₁ c₁) ∧
        (∃ (b₂ c₂ : MCfg 380 M),
          mBeta c₀ d₀ i = mEncodeCfg b₂ ∧ x₂ = mEncodeCfg c₂ ∧
          mTracesTo candM (r.val : PAM M) b₂ c₂)) := by
    have hi_le : PADefN 1 (fun u ↦ u 0 ≤ N) := paDef_le (paFun_proj 0) (paFun_const N)
    have hr_case : ∀ r : Fin 9, PADefN 1 (fun u ↦
        ∃ n₁ x₁ x₂ : PAM M,
          (∃ (c₁ : MCfg 393 M) (c₂ : MCfg 380 M),
            x₁ = mEncodeCfg c₁ ∧ x₂ = mEncodeCfg c₂ ∧ MRel c₁ c₂) ∧
          (∃ (u₁ c₁ : MCfg 393 M),
            mEncodeCfg a₁ = mEncodeCfg u₁ ∧ x₁ = mEncodeCfg c₁ ∧ mTracesTo refM n₁ u₁ c₁) ∧
          (∃ (b₂ c₂ : MCfg 380 M),
            mBeta c₀ d₀ (u 0) = mEncodeCfg b₂ ∧ x₂ = mEncodeCfg c₂ ∧
            mTracesTo candM (r.val : PAM M) b₂ c₂)) := by
      intro r
      let fn₁ : (Fin 4 → PAM M) → PAM M := fun w ↦ w 1
      let fx₁ : (Fin 4 → PAM M) → PAM M := fun w ↦ w 2
      let fx₂ : (Fin 4 → PAM M) → PAM M := fun w ↦ w 3
      let fbi : (Fin 4 → PAM M) → PAM M := fun w ↦ mBeta c₀ d₀ (w 0)
      have hn₁ : PAFunN 4 fn₁ := paFun_proj 1
      have hx₁ : PAFunN 4 fx₁ := paFun_proj 2
      have hx₂ : PAFunN 4 fx₂ := paFun_proj 3
      have hbi : PAFunN 4 fbi := paFun_mBeta (paFun_const c₀) (paFun_const d₀) (paFun_proj 0)
      have hbody := paDef_and (paDef_mRelCode hx₁ hx₂)
        (paDef_and
          (paDef_mTracesToCode refM hn₁ (paFun_const (mEncodeCfg a₁)) hx₁)
          (paDef_mTracesToCode candM (paFun_const (r.val : PAM M)) hbi hx₂))
      refine paDefN_congr (fun u ↦ ?_) (paDef_ex (paDef_ex (paDef_ex hbody)))
      refine exists_congr fun n₁ ↦ exists_congr fun x₁ ↦ exists_congr fun x₂ ↦ ?_
      dsimp only [fn₁, fx₁, fx₂, fbi]
      simp [Fin.snoc]
    exact paDef_imp hi_le (paDef_fin_exists hr_case)
  have hsim := ind1 hdef ?_ ?_ N le_rfl
  · rcases hsim with ⟨r, n₁, x₁, x₂, ⟨c₁, c₂, hx₁, hx₂, hrel⟩,
      ⟨u₁, c₁', hu₁, hx₁', htr₁⟩, ⟨b₂, c₂', hb₂, hx₂', htr_r⟩⟩
    have hu₁a : u₁ = a₁ := mEncodeCfg_injective hu₁.symm
    have hc₁eq : c₁' = c₁ := mEncodeCfg_injective (hx₁'.symm.trans hx₁)
    have hc₂eq : c₂' = c₂ := mEncodeCfg_injective (hx₂'.symm.trans hx₂)
    have hb₂f : b₂ = f₂ := mEncodeCfg_injective (hb₂.symm.trans hN)
    subst u₁ c₁' c₂' b₂
    have hns_r := (mTracesTo_natCast_iff_mNSteps r.val f₂ c₂).mp htr_r
    rcases hr : r.val with _ | r'
    · rw [hr] at hns_r
      simp only [mNSteps, Option.some.injEq] at hns_r
      subst c₂
      have hres := mRespects hrel
      rcases e : mStep refM c₁ with _ | d₁
      · exact ⟨n₁, c₁, htr₁, e⟩
      · rw [e] at hres
        rcases hres with ⟨k, d₂, _, hnsk⟩
        simp [mNSteps, hnone] at hnsk
    · rw [hr] at hns_r
      simp [mNSteps, hnone] at hns_r
  · intro _
    exact ⟨⟨0, by decide⟩, 0, mEncodeCfg a₁, mEncodeCfg a₂,
      ⟨a₁, a₂, rfl, rfl, hrel₀⟩,
      ⟨a₁, a₁, rfl, rfl, mTracesTo_zero refM a₁⟩,
      ⟨a₂, a₂, h0, rfl, by simpa using mTracesTo_zero candM a₂⟩⟩
  · intro i ih hi1
    have hilt : i < N := hi1
    rcases ih (le_of_lt hilt) with ⟨r, n₁, x₁, x₂, ⟨c₁, c₂, hx₁, hx₂, hrel⟩,
      ⟨u₁, c₁', hu₁, hx₁', htr₁⟩, ⟨b₂, c₂', hb₂, hx₂', htr_r⟩⟩
    have hu₁a : u₁ = a₁ := mEncodeCfg_injective hu₁.symm
    have hc₁eq : c₁' = c₁ := mEncodeCfg_injective (hx₁'.symm.trans hx₁)
    have hc₂eq : c₂' = c₂ := mEncodeCfg_injective (hx₂'.symm.trans hx₂)
    subst u₁ c₁' c₂'
    obtain ⟨p₂, q₂, hp₂, hq₂, hst₂⟩ := hsteps i hilt
    have hp₂b : p₂ = b₂ := mEncodeCfg_injective (hp₂.symm.trans hb₂)
    subst b₂
    have hns_r := (mTracesTo_natCast_iff_mNSteps r.val p₂ c₂).mp htr_r
    rcases hr : r.val with _ | r'
    · rw [hr] at hns_r
      simp only [mNSteps, Option.some.injEq] at hns_r
      subst c₂
      have hres := mRespects hrel
      rcases e : mStep refM c₁ with _ | d₁
      · rw [e] at hres
        rw [hres] at hst₂
        cases hst₂
      · rw [e] at hres
        rcases hres with ⟨k, d₂, hrel', hnsk⟩
        simp only [mNSteps, hst₂, Option.bind_some] at hnsk
        exact ⟨k, n₁ + 1, mEncodeCfg d₁, mEncodeCfg d₂,
          ⟨d₁, d₂, rfl, rfl, hrel'⟩,
          ⟨a₁, d₁, rfl, rfl, mTracesTo_snoc htr₁ e⟩,
          ⟨q₂, d₂, hq₂, rfl, mTracesTo_of_mNSteps hnsk⟩⟩
    · rw [hr] at hns_r
      simp only [mNSteps, hst₂, Option.bind_some] at hns_r
      have hr'_lt : r' < 9 := by have := r.isLt; omega
      exact ⟨⟨r', hr'_lt⟩, n₁, mEncodeCfg c₁, mEncodeCfg c₂,
        ⟨c₁, c₂, rfl, rfl, hrel⟩,
        ⟨a₁, c₁, rfl, rfl, htr₁⟩,
        ⟨q₂, c₂, hq₂, rfl, mTracesTo_of_mNSteps hns_r⟩⟩

/-- In every first-order `PAModel M`, `Machines.zf380` halts iff `Machines.zf393` halts. -/
theorem mHalts_zf380_iff_zf393 :
    mHalts M Machines.zf380 ↔ mHalts M Machines.zf393 := by
  unfold mHalts
  rw [mHaltsFrom_iff_of_mTracesTo (mBoot_cand (M := M)),
    mHaltsFrom_iff_of_mTracesTo (mBoot_ref (M := M))]
  exact ⟨mHaltsFrom_ref_of_cand mRel_boot, mHaltsFrom_cand_of_ref mRel_boot⟩

end Model

/-- Peano Arithmetic proves that `zf_380` halts if and only if `zf_393` halts. -/
theorem paProvable_halts_zf380_iff_zf393 :
    PAProvable ((paHalts Machines.zf380).iff (paHalts Machines.zf393)) := by
  rw [paProvable_iff_holdsIn_all_models]
  intro M _ _ v
  rw [← PAM.holdsIn_iff_raw (fun x ↦ ⟨v x⟩)]
  simp only [PAFormula.HoldsIn, paHalts_holdsIn_iff]
  exact ⟨(mHalts_zf380_iff_zf393 (M := M)).mp, (mHalts_zf380_iff_zf393 (M := M)).mpr⟩

end ConjectureMachines.Semantics.PA
