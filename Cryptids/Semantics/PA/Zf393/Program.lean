/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.PA.Zf393.Backend

/-!
# Internal `PA` Layer 2 Program & Spine Verification for `zf_393`

This module internalizes the Layer 2 decision-tree program (`69..392`), the 13-step `unpair`
header (`k = 0..13`), the 20 reordered `ZF` axiom/rule clauses (`k = 13..123`, including the
bugfixed `B6a` check at states `255..256`), the halt check (`k = 123, 124`), and the forward and
backward step-for-step equivalence between `Machines.zf393` halting and `MZf393MainHalts M` inside
an arbitrary first-order `PAModel M` (`mHalts_zf393_iff_mZf393MainHalts`).
-/

@[expose] public section

namespace ConjectureMachines.Semantics.PA

open Turing (Dir)
open StateTransition ConjectureMachines
open ConjectureMachines.Zf393
open ConjectureMachines.Zf393.Layer2
open PAM

section ProgramInternal

variable {M : Type*} [PAStructure M] [PAModel M]

/-! ## Section 1: Arithmetic Helpers, `PAFunRegs`, and Generic `PAM.ind1` Loop Combinators -/

@[simp]
theorem add_one_sub_one_pam (v : PAM M) : v + 1 - 1 = v :=
  (sub_eq_iff_eq_add_pam ⟨v, add_comm 1 v⟩).mpr (add_comm v 1)

@[simp]
theorem zero_sub_pam (a : PAM M) : (0 : PAM M) - a = 0 :=
  sub_eq_zero_of_le_pam (zero_le_pam a)

@[simp]
theorem zero_lt_add_one_pam (x : PAM M) : (0 : PAM M) < x + 1 := by
  rw [PAM.lt_def, zero_add]
  exact ⟨x, add_comm 1 x⟩

@[simp]
theorem add_one_add_one_ne_one_pam (x : PAM M) : x + 1 + 1 ≠ 1 := by
  intro h
  have h1 : x + 1 + 1 = (0 : PAM M) + 1 := by simpa using h
  have h0 : x + 1 = 0 := (add_right_inj_pam 1).mp h1
  exact add_one_ne_zero x h0

theorem add_eq_zero_iff_pam {a b : PAM M} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨ha, hb⟩ ↦ by rw [ha, hb, add_zero]⟩
  have ha : a ≤ a + b := ⟨b, rfl⟩
  have hb : b ≤ a + b := ⟨a, add_comm b a⟩
  rw [h] at ha hb
  exact ⟨le_zero_iff_pam.mp ha, le_zero_iff_pam.mp hb⟩

theorem mPair_zero_succ (x : PAM M) : mPair 0 (x + 1) = mPair x 0 + 1 := by
  apply mul_left_cancel_pam two_ne_zero_pam
  rw [mul_add, two_mul_mPair, two_mul_mPair]
  ring

theorem mPair_succ_left (x y : PAM M) : mPair (x + 1) y = mPair x (y + 1) + 1 := by
  apply mul_left_cancel_pam two_ne_zero_pam
  rw [mul_add, two_mul_mPair, two_mul_mPair]
  ring

theorem mPair_step_inv {out₀ x y m : PAM M} (hxy : x + y = m + 1) :
    (out₀ + x + 1) + mPair m 0 = out₀ + mPair x y := by
  apply mul_left_cancel_pam two_ne_zero_pam
  rw [mul_add 2 (out₀ + x + 1), mul_add 2 out₀, two_mul_mPair, two_mul_mPair, add_zero, hxy]
  ring

@[simp]
theorem mUnpair_zero : mUnpair (0 : PAM M) = (0, 0) := by
  have h := mUnpair_mPair (0 : PAM M) 0
  rwa [mPair_zero_zero] at h

attribute [local irreducible] mPair mUnpair

omit [PAModel M] in
theorem paFun_ite {k : ℕ} {P : (Fin k → PAM M) → Prop} [DecidablePred P]
    {f g : (Fin k → PAM M) → PAM M}
    (hP : PADefN k P) (hf : PAFunN k f) (hg : PAFunN k g) :
    PAFunN k (fun a ↦ if P a then f a else g a) := by
  refine paDefN_congr (fun a ↦ ?_)
    (paDef_or
      (paDef_and (paDef_weaken hP) hf)
      (paDef_and (paDef_not (paDef_weaken hP)) hg))
  by_cases hp : P (Fin.init a) <;> simp [hp]

/-- Concatenate a `k`-tuple and an `m`-tuple into a `(k + m)`-tuple. -/
def finCat {k : ℕ} (a : Fin k → PAM M) :
    ∀ {m : ℕ}, (Fin m → PAM M) → (Fin (k + m) → PAM M)
  | 0, _ => a
  | m + 1, b => Fin.snoc (finCat a (Fin.init b)) (b (Fin.last m))

omit [PAStructure M] [PAModel M] in
theorem finCat_left {k : ℕ} (a : Fin k → PAM M) :
    ∀ {m : ℕ} (b : Fin m → PAM M) (i : Fin k),
      finCat a b ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right k m)⟩ = a i
  | 0, _, _ => rfl
  | m + 1, b, i => by
    dsimp only [finCat]
    rw [fin_snoc_lt _ _ _ (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right k m))]
    exact finCat_left a (Fin.init b) i

omit [PAStructure M] [PAModel M] in
theorem finCat_right {k : ℕ} (a : Fin k → PAM M) :
    ∀ {m : ℕ} (b : Fin m → PAM M) (j : Fin m),
      finCat a b ⟨k + j.val, Nat.add_lt_add_left j.isLt k⟩ = b j
  | 0, _, j => Fin.elim0 j
  | m + 1, b, j => by
    dsimp only [finCat]
    refine Fin.lastCases ?_ ?_ j
    · change Fin.snoc (α := fun _ ↦ PAM M) (finCat a (Fin.init b)) (b (Fin.last m))
          (Fin.last (k + m)) = b (Fin.last m)
      exact Fin.snoc_last _ _
    · intro j₀
      dsimp only [Fin.val_castSucc]
      rw [fin_snoc_lt _ _ _ (Nat.add_lt_add_left j₀.isLt k)]
      exact finCat_right a (Fin.init b) j₀

omit [PAModel M] in
theorem paDef_forall_vec {k : ℕ} :
    ∀ {m : ℕ} {P : (Fin (k + m) → PAM M) → Prop},
      PADefN (k + m) P →
      PADefN k (fun a ↦ ∀ b : Fin m → PAM M, P (finCat a b))
  | 0, P, hP =>
    paDefN_congr (fun a ↦ ⟨fun hp _ ↦ hp, fun hall ↦ hall Fin.elim0⟩) hP
  | m + 1, P, hP => by
    refine paDefN_congr (fun a ↦ ?_) (paDef_forall_vec (m := m) (paDef_all hP))
    constructor
    · intro h b
      exact h (Fin.init b) (b (Fin.last m))
    · intro h b₀ x
      have hb := h (Fin.snoc b₀ x)
      simpa [finCat, Fin.init_snoc, Fin.snoc_last] using hb

omit [PAModel M] in
theorem paDef_exists_vec {k : ℕ} :
    ∀ {m : ℕ} {P : (Fin (k + m) → PAM M) → Prop},
      PADefN (k + m) P →
      PADefN k (fun a ↦ ∃ b : Fin m → PAM M, P (finCat a b))
  | 0, P, hP =>
    paDefN_congr (fun a ↦ ⟨fun hp ↦ ⟨Fin.elim0, hp⟩, fun ⟨_, hp⟩ ↦ hp⟩) hP
  | m + 1, P, hP => by
    refine paDefN_congr (fun a ↦ ?_) (paDef_exists_vec (m := m) (paDef_ex hP))
    constructor
    · rintro ⟨b₀, x, hx⟩
      refine ⟨Fin.snoc b₀ x, ?_⟩
      simpa [finCat, Fin.init_snoc, Fin.snoc_last] using hx
    · rintro ⟨b, hb⟩
      exact ⟨Fin.init b, b (Fin.last m), hb⟩

omit [PAModel M] in
theorem ofFn_getD_eq_self {regs : List (PAM M)} (hlen : regs.length = 11) :
    List.ofFn (fun i : Fin 11 ↦ regs.getD i.val 0) = regs := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    rw [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2,
      Option.getD_some]

omit [PAModel M] in
theorem mGetD_set_self (regs : List (PAM M)) (r : ℕ) (v : PAM M) (hr : r < regs.length) :
    (regs.set r v).getD r 0 = v := by
  simp [List.getD_eq_getElem?_getD, hr]

omit [PAModel M] in
theorem mGetD_set_ne (regs : List (PAM M)) {r₁ r₂ : ℕ} (v : PAM M) (hne : r₁ ≠ r₂) :
    (regs.set r₁ v).getD r₂ 0 = regs.getD r₂ 0 := by
  simp [List.getD_eq_getElem?_getD, hne]

omit [PAModel M] in
theorem mSet_getD_self (regs : List (PAM M)) (r : ℕ) :
    regs.set r (regs.getD r 0) = regs := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    rw [List.getElem_set]
    split_ifs with heq
    · subst heq
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some]
    · rfl

omit [PAModel M] in
theorem mSet_eq_self_of_getD_eq {regs : List (PAM M)} {r : ℕ} {v : PAM M}
    (h : regs.getD r 0 = v) : regs.set r v = regs := by
  rw [← h, mSet_getD_self]

omit [PAStructure M] [PAModel M] in
theorem mSet_comm_of_ne (regs : List (PAM M)) {r₁ r₂ : ℕ} (v₁ v₂ : PAM M) (hne : r₁ ≠ r₂) :
    (regs.set r₁ v₁).set r₂ v₂ = (regs.set r₂ v₂).set r₁ v₁ :=
  List.set_comm v₁ v₂ hne

/-- First-order definable 11-register bank family on `PAM M`. -/
def PAFunRegs (n : ℕ) (R : (Fin n → PAM M) → List (PAM M)) : Prop :=
  (∀ u, (R u).length = 11) ∧ ∀ i : Fin 11, PAFunN n (fun u ↦ (R u).getD i.val 0)

omit [PAModel M] in
theorem paFunRegs_ofFn {n : ℕ} {f : Fin 11 → (Fin n → PAM M) → PAM M}
    (hf : ∀ i : Fin 11, PAFunN n (f i)) :
    PAFunRegs n (fun u ↦ List.ofFn (fun i : Fin 11 ↦ f i u)) := by
  refine ⟨fun _ ↦ by simp, fun i ↦ paFunN_congr (fun u ↦ ?_) (hf i)⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

omit [PAModel M] in
theorem paFunRegs_weaken {n : ℕ} {R : (Fin n → PAM M) → List (PAM M)}
    (hR : PAFunRegs n R) : PAFunRegs (n + 1) (fun u ↦ R (Fin.init u)) :=
  ⟨fun u ↦ hR.1 (Fin.init u), fun i ↦ paFun_weaken (hR.2 i)⟩

omit [PAModel M] in
theorem paFunRegs_getD {n : ℕ} {R : (Fin n → PAM M) → List (PAM M)}
    (hR : PAFunRegs n R) (r : ℕ) :
    PAFunN n (fun u ↦ (R u).getD r 0) := by
  by_cases hr : r < 11
  · exact hR.2 ⟨r, hr⟩
  · refine paFunN_congr (fun u ↦ ?_) (paFun_const 0)
    have hge : (R u).length ≤ r := by rw [hR.1 u]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]

omit [PAModel M] in
theorem paFunRegs_set {n : ℕ} {R : (Fin n → PAM M) → List (PAM M)}
    (hR : PAFunRegs n R) (r : ℕ) {fv : (Fin n → PAM M) → PAM M} (hv : PAFunN n fv) :
    PAFunRegs n (fun u ↦ (R u).set r (fv u)) := by
  refine ⟨fun u ↦ by rw [List.length_set, hR.1 u], fun i ↦ ?_⟩
  by_cases hri : r = i.val
  · subst hri
    refine paFunN_congr (fun u ↦ ?_) hv
    exact (mGetD_set_self (R u) i.val (fv u) (by rw [hR.1 u]; exact i.isLt)).symm
  · refine paFunN_congr (fun u ↦ ?_) (hR.2 i)
    exact (mGetD_set_ne (R u) (fv u) hri).symm

theorem paFun_mZfLogCfg_of_regs (ip : List (Fin 2)) {n : ℕ}
    {fslot : (Fin n → PAM M) → PAM M} {R : (Fin n → PAM M) → List (PAM M)}
    (hslot : PAFunN n fslot) (hR : PAFunRegs n R) :
    PAFunN n (fun u ↦ mEncodeCfg (mZfLogCfg (fslot u) ip (R u))) := by
  refine paFunN_congr (fun u ↦ ?_) (paFun_mZfLogCfg ip hslot hR.2)
  rw [ofFn_getD_eq_self (hR.1 u)]

theorem paDef_mZfLogInv (ip : List (Fin 2)) {n : ℕ}
    {fslot : (Fin n → PAM M) → PAM M} {R : (Fin n → PAM M) → List (PAM M)}
    (hslot : PAFunN n fslot) (hR : PAFunRegs n R) :
    PADefN n (fun u ↦ MZfLogInv (fslot u) ip (R u)) := by
  refine paDefN_congr (fun u ↦ ?_)
    (paDef_and (paDef_prop (ip.length ≤ 136 ∧ Layer1.staysInDag 99 ip.dropLast = true))
      (paDef_le (paFun_const (Layer1.minSlot ip : PAM M)) hslot))
  simp [MZfLogInv, hR.1 u, and_assoc]

theorem paDef_mReach {n : ℕ} {ca cb : (Fin n → PAM M) → MCfg 393 M}
    (ha : PAFunN n (fun u ↦ mEncodeCfg (ca u)))
    (hb : PAFunN n (fun u ↦ mEncodeCfg (cb u))) :
    PADefN n (fun u ↦ mReach (ca u) (cb u)) := by
  refine paDefN_congr (fun u ↦ ?_)
    (paDef_ex (paDef_mTracesTo zf393 (paFun_proj (Fin.last n))
      (paFun_weaken ha) (paFun_weaken hb)))
  simp [mReach]

theorem paDef_mReachPos {n : ℕ} {ca cb : (Fin n → PAM M) → MCfg 393 M}
    (ha : PAFunN n (fun u ↦ mEncodeCfg (ca u)))
    (hb : PAFunN n (fun u ↦ mEncodeCfg (cb u))) :
    PADefN n (fun u ↦ mReachPos (ca u) (cb u)) := by
  refine paDefN_congr (fun u ↦ ?_)
    (paDef_ex (paDef_and
      (paDef_le (paFun_const 1) (paFun_proj (Fin.last n)))
      (paDef_mTracesTo zf393 (paFun_proj (Fin.last n))
        (paFun_weaken ha) (paFun_weaken hb))))
  simp [mReachPos]

theorem paDef_exists_slot_reachPos (ip₁ ip₂ : List (Fin 2)) {n : ℕ}
    {fslot : (Fin n → PAM M) → PAM M}
    {R₁ R₂ : (Fin n → PAM M) → List (PAM M)}
    (hslot : PAFunN n fslot) (hR₁ : PAFunRegs n R₁) (hR₂ : PAFunRegs n R₂) :
    PADefN n (fun u ↦
      ∃ slot' : PAM M, MZfLogInv slot' ip₂ (R₂ u) ∧
        mReachPos (mZfLogCfg (fslot u) ip₁ (R₁ u)) (mZfLogCfg slot' ip₂ (R₂ u))) := by
  have hsl' : PAFunN (n + 1) (fun b : Fin (n + 1) → PAM M ↦ b (Fin.last n)) :=
    paFun_proj (Fin.last n)
  have hR₂' : PAFunRegs (n + 1) (fun b ↦ R₂ (Fin.init b)) := paFunRegs_weaken hR₂
  refine paDefN_congr (fun u ↦ ?_)
    (paDef_ex (paDef_and
      (paDef_mZfLogInv ip₂ hsl' hR₂')
      (paDef_mReachPos
        (paFun_weaken (paFun_mZfLogCfg_of_regs ip₁ hslot hR₁))
        (paFun_mZfLogCfg_of_regs ip₂ hsl' hR₂'))))
  simp

/-- Extract the 11 registers `w 2 .. w 12` from `w : Fin 13 → PAM M`. -/
def regsOfVec13 (w : Fin 13 → PAM M) : List (PAM M) :=
  List.ofFn (fun i : Fin 11 ↦ w ⟨i.val + 2, by omega⟩)

omit [PAModel M] in
theorem paFunRegs_regsOfVec13 : PAFunRegs 13 (regsOfVec13 (M := M)) :=
  paFunRegs_ofFn (fun i ↦ paFun_proj ⟨i.val + 2, by omega⟩)

omit [PAStructure M] [PAModel M] in
private theorem regsOfVec13_finCat (a : Fin 1 → PAM M) (b : Fin 12 → PAM M) :
    regsOfVec13 (finCat a b) = List.ofFn (fun i : Fin 11 ↦ b i.succ) := by
  unfold regsOfVec13
  congr 1
  funext i
  have hidx : (⟨i.val + 2, by omega⟩ : Fin 13) =
      ⟨1 + i.succ.val, Nat.add_lt_add_left i.succ.isLt 1⟩ := by
    ext; dsimp; omega
  rw [hidx, finCat_right a b i.succ]

/-- Generic `PAM.ind1` principle for subroutines transitioning from `ip₁` to `ip₂` over all
`(slot, regs)` satisfying `MZfLogInv slot ip₁ regs`. -/
theorem ind1_subEval_loop (ip₁ ip₂ : List (Fin 2))
    (Cond : PAM M → List (PAM M) → Prop)
    (F : PAM M → List (PAM M) → List (PAM M))
    (hCond : PADefN 13 (fun w : Fin 13 → PAM M ↦ Cond (w 0) (regsOfVec13 w)))
    (hF : PAFunRegs 13 (fun w : Fin 13 → PAM M ↦ F (w 0) (regsOfVec13 w)))
    (h0 : ∀ (slot : PAM M) (regs : List (PAM M)),
      MZfLogInv slot ip₁ regs → Cond 0 regs →
      ∃ slot' : PAM M, MZfLogInv slot' ip₂ (F 0 regs) ∧
        mReachPos (mZfLogCfg slot ip₁ regs) (mZfLogCfg slot' ip₂ (F 0 regs)))
    (hs : ∀ (v : PAM M),
      (∀ (slot : PAM M) (regs : List (PAM M)),
        MZfLogInv slot ip₁ regs → Cond v regs →
        ∃ slot' : PAM M, MZfLogInv slot' ip₂ (F v regs) ∧
          mReachPos (mZfLogCfg slot ip₁ regs) (mZfLogCfg slot' ip₂ (F v regs))) →
      ∀ (slot : PAM M) (regs : List (PAM M)),
        MZfLogInv slot ip₁ regs → Cond (v + 1) regs →
        ∃ slot' : PAM M, MZfLogInv slot' ip₂ (F (v + 1) regs) ∧
          mReachPos (mZfLogCfg slot ip₁ regs) (mZfLogCfg slot' ip₂ (F (v + 1) regs))) :
    ∀ (v slot : PAM M) (regs : List (PAM M)),
      MZfLogInv slot ip₁ regs → Cond v regs →
      ∃ slot' : PAM M, MZfLogInv slot' ip₂ (F v regs) ∧
        mReachPos (mZfLogCfg slot ip₁ regs) (mZfLogCfg slot' ip₂ (F v regs)) := by
  have hbody13 : PADefN 13 (fun w : Fin 13 → PAM M ↦
      MZfLogInv (w 1) ip₁ (regsOfVec13 w) →
      Cond (w 0) (regsOfVec13 w) →
      ∃ slot' : PAM M, MZfLogInv slot' ip₂ (F (w 0) (regsOfVec13 w)) ∧
        mReachPos (mZfLogCfg (w 1) ip₁ (regsOfVec13 w))
          (mZfLogCfg slot' ip₂ (F (w 0) (regsOfVec13 w)))) :=
    paDef_imp (paDef_mZfLogInv ip₁ (paFun_proj 1) paFunRegs_regsOfVec13)
      (paDef_imp hCond
        (paDef_exists_slot_reachPos ip₁ ip₂ (paFun_proj 1) paFunRegs_regsOfVec13 hF))
  have hall1 : PADef1 (fun v : PAM M ↦
      ∀ (slot : PAM M) (regs : List (PAM M)),
        MZfLogInv slot ip₁ regs → Cond v regs →
        ∃ slot' : PAM M, MZfLogInv slot' ip₂ (F v regs) ∧
          mReachPos (mZfLogCfg slot ip₁ regs) (mZfLogCfg slot' ip₂ (F v regs))) := by
    refine paDefN_congr (fun a ↦ ?_) (paDef_forall_vec (k := 1) (m := 12) hbody13)
    have ha0 : ∀ b : Fin 12 → PAM M, finCat a b 0 = a 0 := fun b ↦ finCat_left a b 0
    have hb0 : ∀ b : Fin 12 → PAM M, finCat a b 1 = b 0 := fun b ↦ finCat_right a b 0
    constructor
    · intro hvec slot regs hinv hc
      let b : Fin 12 → PAM M := Fin.cons slot (fun i : Fin 11 ↦ regs.getD i.val 0)
      have hb_slot : b 0 = slot := rfl
      have hb_regs : List.ofFn (fun i : Fin 11 ↦ b i.succ) = regs := ofFn_getD_eq_self hinv.1
      have hinst := hvec b
      rw [ha0 b, hb0 b, regsOfVec13_finCat a b, hb_slot, hb_regs] at hinst
      exact hinst hinv hc
    · intro hall b
      rw [ha0 b, hb0 b, regsOfVec13_finCat a b]
      exact hall (b 0) (List.ofFn (fun i : Fin 11 ↦ b i.succ))
  exact ind1 hall1 h0 hs

/-! ## Section 2: Logical Step Lemmas & Subroutine Combinators (`MSubEval`) -/

theorem mLogStep_of_jump {slot : PAM M} {ip ip' : List (Fin 2)} {regs : List (PAM M)}
    (hinv : MZfLogInv slot ip regs) (hev : evalStack ip = .jump ip') :
    ∃ slot' : PAM M, MZfLogInv slot' ip' regs ∧
      mReachPos (mZfLogCfg slot ip regs) (mZfLogCfg slot' ip' regs) := by
  have h := mTm_simulates_evalStack hinv
  rwa [hev] at h

theorem mLogStep_of_inc {slot : PAM M} {ip ip' : List (Fin 2)} {r : ℕ} {regs : List (PAM M)}
    (hinv : MZfLogInv slot ip regs) (hev : evalStack ip = .inc r ip') :
    ∃ slot' : PAM M, MZfLogInv slot' ip' (regs.set r (regs.getD r 0 + 1)) ∧
      mReachPos (mZfLogCfg slot ip regs)
        (mZfLogCfg slot' ip' (regs.set r (regs.getD r 0 + 1))) := by
  have h := mTm_simulates_evalStack hinv
  rwa [hev] at h

theorem mLogStep_of_decnz_zero {slot : PAM M} {ip ip_succ ip_fail : List (Fin 2)} {r : ℕ}
    {regs : List (PAM M)} (hinv : MZfLogInv slot ip regs)
    (hev : evalStack ip = .decnz r ip_succ ip_fail) (hz : regs.getD r 0 = 0) :
    ∃ slot' : PAM M, MZfLogInv slot' ip_fail regs ∧
      mReachPos (mZfLogCfg slot ip regs) (mZfLogCfg slot' ip_fail regs) := by
  have h := mTm_simulates_evalStack hinv
  rw [hev] at h
  exact h.1 hz

theorem mLogStep_of_decnz_succ {slot : PAM M} {ip ip_succ ip_fail : List (Fin 2)} {r : ℕ}
    {v : PAM M} {regs : List (PAM M)} (hinv : MZfLogInv slot ip regs)
    (hev : evalStack ip = .decnz r ip_succ ip_fail) (hv : regs.getD r 0 = v + 1) :
    ∃ slot' : PAM M, MZfLogInv slot' ip_succ (regs.set r v) ∧
      mReachPos (mZfLogCfg slot ip regs) (mZfLogCfg slot' ip_succ (regs.set r v)) := by
  have h := mTm_simulates_evalStack hinv
  rw [hev] at h
  have hne : regs.getD r 0 ≠ 0 := by rw [hv]; exact add_one_ne_zero v
  have hres := h.2 hne
  rwa [hv, add_one_sub_one_pam] at hres

theorem mLogStep_of_halt {slot : PAM M} {ip : List (Fin 2)} {regs : List (PAM M)}
    (hinv : MZfLogInv slot ip regs) (hev : evalStack ip = .halt) :
    mHaltsFrom zf393 (mZfLogCfg slot ip regs) := by
  have h := mTm_simulates_evalStack hinv
  rwa [hev] at h

/-- Subroutine specification at decision-tree node `q` over `PAM M`. -/
def MSubEval (q : Fin 393) (f : List (PAM M) → List (PAM M)) : Prop :=
  ∀ (P : List (Fin 2)),
    walkInternal 99 P = some q →
    ∀ (slot : PAM M) (regs : List (PAM M)),
      MZfLogInv slot (trimZeros P) regs →
      (f regs).length = 11 ∧
      ∃ slot' : PAM M, MZfLogInv slot' (retStack P) (f regs) ∧
        mReachPos (mZfLogCfg slot (trimZeros P) regs) (mZfLogCfg slot' (retStack P) (f regs))

theorem MSubEval.congr {q : Fin 393} {f g : List (PAM M) → List (PAM M)}
    (h : MSubEval q f) (heq : ∀ regs : List (PAM M), regs.length = 11 → f regs = g regs) :
    MSubEval q g := by
  intro P hP slot regs hinv
  obtain ⟨hlen_f, slot', hinv', hreach⟩ := h P hP slot regs hinv
  rw [heq regs hinv.1] at hlen_f hinv' hreach
  exact ⟨hlen_f, slot', hinv', hreach⟩

theorem mSubEval_seq {q q₀ q₁ : Fin 393} {f₀ f₁ f : List (PAM M) → List (PAM M)}
    (htr0 : zf393Trans q 0 = some (0, .right, q₀)) (hq₀ : 69 ≤ q₀.val)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁)) (hq₁ : 69 ≤ q₁.val)
    (h0 : MSubEval q₀ f₀) (h1 : MSubEval q₁ f₁)
    (heq : (fun regs ↦ f₁ (f₀ regs)) = f := by rfl) :
    MSubEval q f := by
  subst heq
  intro P hP slot regs hinv
  have hP0 : walkInternal 99 (P ++ [0]) = some q₀ := walkInternal_snoc hP htr0 hq₀
  have hP1 : walkInternal 99 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  have hinv0 : MZfLogInv slot (trimZeros (P ++ [0])) regs := by rwa [trimZeros_append_zero]
  obtain ⟨_, slot₀, hinv₀, hreach₀⟩ := h0 (P ++ [0]) hP0 slot regs hinv0
  rw [trimZeros_append_zero, retStack_append_zero] at hreach₀
  rw [retStack_append_zero] at hinv₀
  have hinv1 : MZfLogInv slot₀ (trimZeros (P ++ [1])) (f₀ regs) := by
    rwa [trimZeros_append_one]
  obtain ⟨hlen₁, slot₁, hinv₁, hreach₁⟩ := h1 (P ++ [1]) hP1 slot₀ (f₀ regs) hinv1
  rw [trimZeros_append_one, retStack_append_one] at hreach₁
  rw [retStack_append_one] at hinv₁
  exact ⟨hlen₁, slot₁, hinv₁, mReachPos_trans hreach₀ hreach₁⟩

theorem mSubEval_seq_inc {q q₀ q₁ : Fin 393} {f₀ : List (PAM M) → List (PAM M)}
    (htr0 : zf393Trans q 0 = some (0, .right, q₀)) (hq₀ : 69 ≤ q₀.val)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁))
    (h29 : 29 ≤ q₁.val) (h50 : q₁.val ≤ 50) (hinc : isLeafInc q₁ = true)
    (h0 : MSubEval q₀ f₀) :
    MSubEval q (fun regs ↦
      let r := f₀ regs
      r.set (logLeafReg q₁) (r.getD (logLeafReg q₁) 0 + 1)) := by
  intro P hP slot regs hinv
  have hP0 : walkInternal 99 (P ++ [0]) = some q₀ := walkInternal_snoc hP htr0 hq₀
  have hinv0 : MZfLogInv slot (trimZeros (P ++ [0])) regs := by rwa [trimZeros_append_zero]
  obtain ⟨hlen₀, slot₀, hinv₀, hreach₀⟩ := h0 (P ++ [0]) hP0 slot regs hinv0
  rw [trimZeros_append_zero, retStack_append_zero] at hreach₀
  rw [retStack_append_zero] at hinv₀
  have hev1 := evalStack_leaf1_inc_of_walkInternal hP htr1 h29 h50 hinc
  obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_inc hinv₀ hev1
  exact ⟨by simp [hlen₀], slot₁, hinv₁, mReachPos_trans hreach₀ hreach₁⟩

theorem mSubEval_inc_inc {q q₀ q₁ : Fin 393}
    (htr0 : zf393Trans q 0 = some (0, .right, q₀))
    (h0_29 : 29 ≤ q₀.val) (h0_50 : q₀.val ≤ 50) (hinc0 : isLeafInc q₀ = true)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁))
    (h1_29 : 29 ≤ q₁.val) (h1_50 : q₁.val ≤ 50) (hinc1 : isLeafInc q₁ = true) :
    MSubEval (M := M) q (fun regs : List (PAM M) ↦
      let r₁ := regs.set (logLeafReg q₀) (regs.getD (logLeafReg q₀) 0 + 1)
      r₁.set (logLeafReg q₁) (r₁.getD (logLeafReg q₁) 0 + 1)) := by
  intro P hP slot regs hinv
  have hev0 : evalStack (trimZeros P) = .inc (logLeafReg q₀) (P ++ [1]) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 h0_29 h0_50]
    simp [hinc0]
  obtain ⟨slot₀, hinv₀, hreach₀⟩ := mLogStep_of_inc hinv hev0
  have hev1 := evalStack_leaf1_inc_of_walkInternal hP htr1 h1_29 h1_50 hinc1
  obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_inc hinv₀ hev1
  exact ⟨by simp [hinv.1], slot₁, hinv₁, mReachPos_trans hreach₀ hreach₁⟩

theorem mSubEval_inc_seq {q q₀ q₁ : Fin 393} {f₁ : List (PAM M) → List (PAM M)}
    (htr0 : zf393Trans q 0 = some (0, .right, q₀))
    (h29 : 29 ≤ q₀.val) (h50 : q₀.val ≤ 50) (hinc : isLeafInc q₀ = true)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁)) (hq₁ : 69 ≤ q₁.val)
    (h1 : MSubEval q₁ f₁) :
    MSubEval q (fun regs ↦
      f₁ (regs.set (logLeafReg q₀) (regs.getD (logLeafReg q₀) 0 + 1))) := by
  intro P hP slot regs hinv
  have hev0 : evalStack (trimZeros P) = .inc (logLeafReg q₀) (P ++ [1]) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 h29 h50]
    simp [hinc]
  obtain ⟨slot₀, hinv₀, hreach₀⟩ := mLogStep_of_inc hinv hev0
  have hP1 : walkInternal 99 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  have hinv1 : MZfLogInv slot₀ (trimZeros (P ++ [1]))
      (regs.set (logLeafReg q₀) (regs.getD (logLeafReg q₀) 0 + 1)) := by
    rwa [trimZeros_append_one]
  obtain ⟨hlen₁, slot₁, hinv₁, hreach₁⟩ := h1 (P ++ [1]) hP1 slot₀ _ hinv1
  rw [trimZeros_append_one, retStack_append_one] at hreach₁
  rw [retStack_append_one] at hinv₁
  exact ⟨hlen₁, slot₁, hinv₁, mReachPos_trans hreach₀ hreach₁⟩

theorem mSubEval_cond {q q₀ q₁ : Fin 393} {cond : List (PAM M) → Prop} [DecidablePred cond]
    {f₀ f₁ f : List (PAM M) → List (PAM M)}
    (htr0 : zf393Trans q 0 = some (0, .right, q₀)) (hq₀ : 69 ≤ q₀.val)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁)) (hq₁ : 69 ≤ q₁.val)
    (h0 : ∀ (Q : List (Fin 2)), walkInternal 99 Q = some q₀ →
      ∀ (slot : PAM M) (regs : List (PAM M)),
        MZfLogInv slot (trimZeros Q) regs →
        (f₀ regs).length = 11 ∧
        ∃ slot' : PAM M,
          MZfLogInv slot'
            (if cond regs then retStack Q else (popBreakRev 1 Q.reverse).reverse) (f₀ regs) ∧
          mReachPos (mZfLogCfg slot (trimZeros Q) regs)
            (mZfLogCfg slot'
              (if cond regs then retStack Q else (popBreakRev 1 Q.reverse).reverse) (f₀ regs)))
    (h1 : MSubEval q₁ f₁)
    (heq : (fun regs ↦ if cond regs then f₁ (f₀ regs) else f₀ regs) = f := by rfl) :
    MSubEval q f := by
  subst heq
  intro P hP slot regs hinv
  have hP0 : walkInternal 99 (P ++ [0]) = some q₀ := walkInternal_snoc hP htr0 hq₀
  have hP1 : walkInternal 99 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  have hinv0 : MZfLogInv slot (trimZeros (P ++ [0])) regs := by rwa [trimZeros_append_zero]
  obtain ⟨hlen₀, slot₀, hinv₀, hreach₀⟩ := h0 (P ++ [0]) hP0 slot regs hinv0
  have hbrk : (popBreakRev 1 (P ++ [0]).reverse).reverse = retStack P := by simp [retStack]
  rw [trimZeros_append_zero, retStack_append_zero, hbrk] at hreach₀
  rw [retStack_append_zero, hbrk] at hinv₀
  by_cases hc : cond regs
  · simp only [hc, ↓reduceIte] at hinv₀ hreach₀ ⊢
    have hinv1 : MZfLogInv slot₀ (trimZeros (P ++ [1])) (f₀ regs) := by
      rwa [trimZeros_append_one]
    obtain ⟨hlen₁, slot₁, hinv₁, hreach₁⟩ := h1 (P ++ [1]) hP1 slot₀ (f₀ regs) hinv1
    rw [trimZeros_append_one, retStack_append_one] at hreach₁
    rw [retStack_append_one] at hinv₁
    exact ⟨hlen₁, slot₁, hinv₁, mReachPos_trans hreach₀ hreach₁⟩
  · simp only [hc, ↓reduceIte] at hinv₀ hreach₀ ⊢
    exact ⟨hlen₀, slot₀, hinv₀, hreach₀⟩

/-! ## Section 3: Parametric `PAM.ind1` Loop Theorems & Concrete Subroutine Instantiations -/

theorem mSubEval_while_clear {q q_dec : Fin 393} (r : ℕ) (hr : r < 11)
    (htr0 : zf393Trans q 0 = some (0, .right, q_dec))
    (h29 : 29 ≤ q_dec.val) (h50 : q_dec.val ≤ 50) (hdec : isLeafInc q_dec = false)
    (hlr : logLeafReg q_dec = r)
    (htr1 : zf393Trans q 1 = some (0, .left, 64)) :
    MSubEval (M := M) q (fun regs ↦ regs.set r 0) := by
  intro P hP
  have hev0 : evalStack (trimZeros P) = .decnz r (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 h29 h50]
    simp [hdec, hlr]
  have hev1 : evalStack (P ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (k := 0) (by omega) hP htr1
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop := ind1_subEval_loop (M := M) (trimZeros P) (retStack P)
    (fun v regs ↦ regs.getD r 0 = v)
    (fun _ regs ↦ regs.set r 0)
    (paDef_eq (paFunRegs_getD paFunRegs_regsOfVec13 r) (paFun_proj 0))
    (paFunRegs_set paFunRegs_regsOfVec13 r (paFun_const 0))
    (fun slot regs hinv hv ↦ by
      obtain ⟨slot', hinv', hreach⟩ := mLogStep_of_decnz_zero hinv hev0 hv
      rw [mSet_eq_self_of_getD_eq hv]
      exact ⟨slot', hinv', hreach⟩)
    (fun v ih slot regs hinv hv ↦ by
      obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_succ hinv hev0 hv
      obtain ⟨slot₂, hinv₂, hreach₂⟩ := mLogStep_of_jump hinv₁ hev1
      have hv' : (regs.set r v).getD r 0 = v := mGetD_set_self regs r v (by rw [hinv.1]; exact hr)
      obtain ⟨slot₃, hinv₃, hreach₃⟩ := ih slot₂ (regs.set r v) hinv₂ hv'
      rw [List.set_set] at hinv₃ hreach₃
      exact ⟨slot₃, hinv₃, mReachPos_trans hreach₁ (mReachPos_trans hreach₂ hreach₃)⟩)
  intro slot regs hinv
  exact ⟨by rw [List.length_set, hinv.1], hloop (regs.getD r 0) slot regs hinv rfl⟩

theorem mSubEval_while_move1 {q q_dec q₁ q_inc : Fin 393} (r₁ r₂ : ℕ)
    (hr₁ : r₁ < 11) (_hr₂ : r₂ < 11) (hne : r₁ ≠ r₂)
    (htr0 : zf393Trans q 0 = some (0, .right, q_dec))
    (hdec29 : 29 ≤ q_dec.val) (hdec50 : q_dec.val ≤ 50) (hdec : isLeafInc q_dec = false)
    (hlr1 : logLeafReg q_dec = r₁)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁)) (hq₁ : 69 ≤ q₁.val)
    (htr10 : zf393Trans q₁ 0 = some (0, .right, q_inc))
    (hinc29 : 29 ≤ q_inc.val) (hinc50 : q_inc.val ≤ 50) (hinc : isLeafInc q_inc = true)
    (hlr2 : logLeafReg q_inc = r₂)
    (htr11 : zf393Trans q₁ 1 = some (0, .left, 65)) :
    MSubEval (M := M) q (fun regs ↦ (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + regs.getD r₁ 0)) := by
  intro P hP
  have hP1 : walkInternal 99 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  have hev0 : evalStack (trimZeros P) = .decnz r₁ (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 hdec29 hdec50]
    simp [hdec, hlr1]
  have hev10 : evalStack (P ++ [1]) = .inc r₂ (P ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hP1 htr10 hinc29 hinc50
    simpa [hinc, hlr2] using h
  have hev11 : evalStack (P ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1]) (k := 1) (by omega) hP1 htr11
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop := ind1_subEval_loop (M := M) (trimZeros P) (retStack P)
    (fun v regs ↦ regs.getD r₁ 0 = v)
    (fun v regs ↦ (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v))
    (paDef_eq (paFunRegs_getD paFunRegs_regsOfVec13 r₁) (paFun_proj 0))
    (paFunRegs_set (paFunRegs_set paFunRegs_regsOfVec13 r₁ (paFun_const 0)) r₂
      (paFun_add (paFunRegs_getD paFunRegs_regsOfVec13 r₂) (paFun_proj 0)))
    (fun slot regs hinv hv ↦ by
      obtain ⟨slot', hinv', hreach⟩ := mLogStep_of_decnz_zero hinv hev0 hv
      have hset : (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + 0) = regs := by
        rw [add_zero, mSet_eq_self_of_getD_eq hv, mSet_getD_self]
      rw [hset]
      exact ⟨slot', hinv', hreach⟩)
    (fun v ih slot regs hinv hv ↦ by
      obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_succ hinv hev0 hv
      obtain ⟨slot₂, hinv₂, hreach₂⟩ := mLogStep_of_inc hinv₁ hev10
      rw [mGetD_set_ne _ _ hne] at hinv₂ hreach₂
      let regs₁ := (regs.set r₁ v).set r₂ (regs.getD r₂ 0 + 1)
      obtain ⟨slot₃, hinv₃, hreach₃⟩ := mLogStep_of_jump (regs := regs₁) hinv₂ hev11
      have hv₁ : regs₁.getD r₁ 0 = v := by
        dsimp [regs₁]
        rw [mGetD_set_ne _ _ hne.symm, mGetD_set_self regs r₁ v (by rw [hinv.1]; exact hr₁)]
      obtain ⟨slot₄, hinv₄, hreach₄⟩ := ih slot₃ regs₁ hinv₃ hv₁
      have hregs_eq : (regs₁.set r₁ 0).set r₂ (regs₁.getD r₂ 0 + v) =
          (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + (v + 1)) := by
        have hr₂_get : regs₁.getD r₂ 0 = regs.getD r₂ 0 + 1 :=
          mGetD_set_self (regs.set r₁ v) r₂ (regs.getD r₂ 0 + 1)
            (by rw [List.length_set, hinv.1]; exact _hr₂)
        rw [hr₂_get]
        dsimp only [regs₁]
        rw [mSet_comm_of_ne (regs.set r₁ v) (regs.getD r₂ 0 + 1) 0 hne.symm,
          List.set_set, List.set_set, add_assoc, add_comm 1 v]
      rw [hregs_eq] at hinv₄ hreach₄
      exact ⟨slot₄, hinv₄, mReachPos_trans hreach₁
        (mReachPos_trans hreach₂ (mReachPos_trans hreach₃ hreach₄))⟩)
  intro slot regs hinv
  exact ⟨by simp [hinv.1], hloop (regs.getD r₁ 0) slot regs hinv rfl⟩

theorem mSubEval_while_move2 {q q_dec q₁ q₂ q_inc1 q_inc2 : Fin 393} (r₁ r₂ r₃ : ℕ)
    (hr₁ : r₁ < 11) (hr₂ : r₂ < 11) (hr₃ : r₃ < 11)
    (hne12 : r₁ ≠ r₂) (hne13 : r₁ ≠ r₃) (hne23 : r₂ ≠ r₃)
    (htr0 : zf393Trans q 0 = some (0, .right, q_dec))
    (hdec29 : 29 ≤ q_dec.val) (hdec50 : q_dec.val ≤ 50) (hdec : isLeafInc q_dec = false)
    (hlr1 : logLeafReg q_dec = r₁)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁)) (hq₁ : 69 ≤ q₁.val)
    (htr10 : zf393Trans q₁ 0 = some (0, .right, q₂)) (hq₂ : 69 ≤ q₂.val)
    (htr11 : zf393Trans q₁ 1 = some (0, .left, 65))
    (htr20 : zf393Trans q₂ 0 = some (0, .right, q_inc1))
    (hinc1_29 : 29 ≤ q_inc1.val) (hinc1_50 : q_inc1.val ≤ 50) (hinc1 : isLeafInc q_inc1 = true)
    (hlr2 : logLeafReg q_inc1 = r₂)
    (htr21 : zf393Trans q₂ 1 = some (1, .right, q_inc2))
    (hinc2_29 : 29 ≤ q_inc2.val) (hinc2_50 : q_inc2.val ≤ 50) (hinc2 : isLeafInc q_inc2 = true)
    (hlr3 : logLeafReg q_inc2 = r₃) :
    MSubEval (M := M) q (fun regs ↦
      ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + regs.getD r₁ 0)).set
        r₃ (regs.getD r₃ 0 + regs.getD r₁ 0)) := by
  intro P hP
  have hP1 : walkInternal 99 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  have hP10 : walkInternal 99 (P ++ [1] ++ [0]) = some q₂ := walkInternal_snoc hP1 htr10 hq₂
  have hbody := mSubEval_inc_inc (M := M) htr20 hinc1_29 hinc1_50 hinc1
    htr21 hinc2_29 hinc2_50 hinc2
  have hev0 : evalStack (trimZeros P) = .decnz r₁ (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 hdec29 hdec50]
    simp [hdec, hlr1]
  have hev11 : evalStack (P ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1]) (k := 1) (by omega) hP1 htr11
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop := ind1_subEval_loop (M := M) (trimZeros P) (retStack P)
    (fun v regs ↦ regs.getD r₁ 0 = v)
    (fun v regs ↦ ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)).set r₃ (regs.getD r₃ 0 + v))
    (paDef_eq (paFunRegs_getD paFunRegs_regsOfVec13 r₁) (paFun_proj 0))
    (paFunRegs_set
      (paFunRegs_set (paFunRegs_set paFunRegs_regsOfVec13 r₁ (paFun_const 0)) r₂
        (paFun_add (paFunRegs_getD paFunRegs_regsOfVec13 r₂) (paFun_proj 0)))
      r₃ (paFun_add (paFunRegs_getD paFunRegs_regsOfVec13 r₃) (paFun_proj 0)))
    (fun slot regs hinv hv ↦ by
      obtain ⟨slot', hinv', hreach⟩ := mLogStep_of_decnz_zero hinv hev0 hv
      have hset :
          ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + 0)).set r₃ (regs.getD r₃ 0 + 0) = regs := by
        rw [add_zero, add_zero, mSet_eq_self_of_getD_eq hv, mSet_getD_self, mSet_getD_self]
      rw [hset]
      exact ⟨slot', hinv', hreach⟩)
    (fun v ih slot regs hinv hv ↦ by
      obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_succ hinv hev0 hv
      have hinv10 : MZfLogInv slot₁ (trimZeros (P ++ [1] ++ [0])) (regs.set r₁ v) := by
        rwa [trimZeros_append_zero, trimZeros_append_one]
      obtain ⟨_, slot₂, hinv₂, hreach_b⟩ :=
        hbody (P ++ [1] ++ [0]) hP10 slot₁ (regs.set r₁ v) hinv10
      rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero, hlr2, hlr3] at hreach_b
      rw [retStack_append_zero, hlr2, hlr3] at hinv₂
      let regs₁ := ((regs.set r₁ v).set r₂ (regs.getD r₂ 0 + 1)).set r₃ (regs.getD r₃ 0 + 1)
      have hb_eq : ((regs.set r₁ v).set r₂ ((regs.set r₁ v).getD r₂ 0 + 1)).set
          r₃ (((regs.set r₁ v).set r₂ ((regs.set r₁ v).getD r₂ 0 + 1)).getD r₃ 0 + 1) = regs₁ := by
        dsimp only [regs₁]
        rw [mGetD_set_ne _ _ hne12, mGetD_set_ne _ _ hne23, mGetD_set_ne _ _ hne13]
      dsimp only at hinv₂ hreach_b
      rw [hb_eq] at hinv₂ hreach_b
      obtain ⟨slot₃, hinv₃, hreach₃⟩ := mLogStep_of_jump (regs := regs₁) hinv₂ hev11
      have hv₁ : regs₁.getD r₁ 0 = v := by
        dsimp [regs₁]
        rw [mGetD_set_ne _ _ hne13.symm, mGetD_set_ne _ _ hne12.symm,
          mGetD_set_self regs r₁ v (by rw [hinv.1]; exact hr₁)]
      obtain ⟨slot₄, hinv₄, hreach₄⟩ := ih slot₃ regs₁ hinv₃ hv₁
      have hregs_eq :
          ((regs₁.set r₁ 0).set r₂ (regs₁.getD r₂ 0 + v)).set r₃ (regs₁.getD r₃ 0 + v) =
          ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + (v + 1))).set
            r₃ (regs.getD r₃ 0 + (v + 1)) := by
        have hr₂_get : regs₁.getD r₂ 0 = regs.getD r₂ 0 + 1 := by
          dsimp [regs₁]
          rw [mGetD_set_ne _ _ hne23.symm,
            mGetD_set_self (regs.set r₁ v) r₂ (regs.getD r₂ 0 + 1)
              (by rw [List.length_set, hinv.1]; exact hr₂)]
        have hr₃_get : regs₁.getD r₃ 0 = regs.getD r₃ 0 + 1 := by
          dsimp [regs₁]
          exact mGetD_set_self _ r₃ (regs.getD r₃ 0 + 1)
            (by rw [List.length_set, List.length_set, hinv.1]; exact hr₃)
        rw [hr₂_get, hr₃_get]
        dsimp only [regs₁]
        rw [mSet_comm_of_ne _ (regs.getD r₃ 0 + 1) 0 hne13.symm,
          mSet_comm_of_ne (regs.set r₁ v) (regs.getD r₂ 0 + 1) 0 hne12.symm,
          List.set_set,
          mSet_comm_of_ne _ (regs.getD r₃ 0 + 1) (regs.getD r₂ 0 + 1 + v) hne23.symm,
          List.set_set, List.set_set,
          add_assoc (regs.getD r₂ 0) 1 v, add_comm (1 : PAM M) v,
          add_assoc (regs.getD r₃ 0) 1 v, add_comm (1 : PAM M) v]
      rw [hregs_eq] at hinv₄ hreach₄
      exact ⟨slot₄, hinv₄, mReachPos_trans hreach₁
        (mReachPos_trans hreach_b (mReachPos_trans hreach₃ hreach₄))⟩)
  intro slot regs hinv
  exact ⟨by simp [hinv.1], hloop (regs.getD r₁ 0) slot regs hinv rfl⟩

/-- Closed-form Cantor pairing register operation `pair(out, r1, r2)` on `PAM M`. -/
noncomputable def mRegPairOp (out r1 r2 : ℕ) (regs : List (PAM M)) : List (PAM M) :=
  ((regs.set r1 0).set r2 0).set out
    (regs.getD out 0 + mPair (regs.getD r1 0) (regs.getD r2 0))

theorem paFunRegs_mRegPairOp (out r1 r2 : ℕ) {n : ℕ} {R : (Fin n → PAM M) → List (PAM M)}
    (hR : PAFunRegs n R) : PAFunRegs n (fun u ↦ mRegPairOp out r1 r2 (R u)) :=
  paFunRegs_set (paFunRegs_set (paFunRegs_set hR r1 (paFun_const 0)) r2 (paFun_const 0)) out
    (paFun_add (paFunRegs_getD hR out)
      (paFun_mPair (paFunRegs_getD hR r1) (paFunRegs_getD hR r2)))

theorem mSubEval_pair {q q_move2 q1 q_dec q2 q3 : Fin 393} (out r1 r2 : ℕ)
    (hout : out < 11) (hr1 : r1 < 11) (hr2 : r2 < 11)
    (hne12 : r1 ≠ r2) (hne1o : r1 ≠ out) (hne2o : r2 ≠ out)
    (htr0 : zf393Trans q 0 = some (0, .right, q_move2)) (hq_move2 : 69 ≤ q_move2.val)
    (htr1 : zf393Trans q 1 = some (1, .right, q1)) (hq1 : 69 ≤ q1.val)
    (htr10 : zf393Trans q1 0 = some (0, .right, q_dec))
    (hdec29 : 29 ≤ q_dec.val) (hdec50 : q_dec.val ≤ 50) (hdec : isLeafInc q_dec = false)
    (hlr_dec : logLeafReg q_dec = r2)
    (htr11 : zf393Trans q1 1 = some (1, .right, q2)) (hq2 : 69 ≤ q2.val)
    (htr20 : zf393Trans q2 0 = some (0, .right, q3)) (hq3 : 69 ≤ q3.val)
    (htr21 : zf393Trans q2 1 = some (0, .left, 66))
    (hmove2 : MSubEval (M := M) q_move2 (fun regs ↦
      ((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
        out (regs.getD out 0 + regs.getD r1 0)))
    (hbody : MSubEval (M := M) q3 (fun regs ↦
      let r₀ := regs.set out (regs.getD out 0 + 1)
      (r₀.set r2 0).set r1 (r₀.getD r1 0 + r₀.getD r2 0))) :
    MSubEval (M := M) q (mRegPairOp out r1 r2) := by
  intro P hP
  have hP0 : walkInternal 99 (P ++ [0]) = some q_move2 := walkInternal_snoc hP htr0 hq_move2
  have hP1 : walkInternal 99 (P ++ [1]) = some q1 := walkInternal_snoc hP htr1 hq1
  have hP11 : walkInternal 99 (P ++ [1] ++ [1]) = some q2 := walkInternal_snoc hP1 htr11 hq2
  have hP110 : walkInternal 99 (P ++ [1] ++ [1] ++ [0]) = some q3 :=
    walkInternal_snoc hP11 htr20 hq3
  have hev10 : evalStack (P ++ [1]) = .decnz r2 (P ++ [1] ++ [1]) (retStack P) := by
    have h := evalStack_leaf0_of_walkInternal hP1 htr10 hdec29 hdec50
    simpa [hdec, hlr_dec] using h
  have hev21 : evalStack (P ++ [1] ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h :=
      evalStack_continue1_of_walkInternal (P := P ++ [1] ++ [1]) (k := 2) (by omega) hP11 htr21
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop := ind1_subEval_loop (M := M) (trimZeros P) (retStack P)
    (fun n regs ↦ regs.getD r1 0 + regs.getD r2 0 = n)
    (fun _ regs ↦ mRegPairOp out r1 r2 regs)
    (paDef_eq
      (paFun_add (paFunRegs_getD paFunRegs_regsOfVec13 r1)
        (paFunRegs_getD paFunRegs_regsOfVec13 r2))
      (paFun_proj 0))
    (paFunRegs_mRegPairOp out r1 r2 paFunRegs_regsOfVec13)
    (fun slot regs hinv hn ↦ by
      obtain ⟨hr1_z, hr2_z⟩ := add_eq_zero_iff_pam.mp hn
      have hinv0 : MZfLogInv slot (trimZeros (P ++ [0])) regs := by rwa [trimZeros_append_zero]
      obtain ⟨_, slot₁, hinv₁, hreach₀⟩ := hmove2 (P ++ [0]) hP0 slot regs hinv0
      rw [trimZeros_append_zero, retStack_append_zero] at hreach₀
      rw [retStack_append_zero] at hinv₁
      dsimp only at hinv₁ hreach₀
      let regs₁ := ((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
        out (regs.getD out 0 + regs.getD r1 0)
      have hr2_zero : regs₁.getD r2 0 = 0 := by
        dsimp [regs₁]
        rw [mGetD_set_ne _ _ hne2o.symm,
          mGetD_set_self _ r2 _ (by rw [List.length_set, hinv.1]; exact hr2),
          hr1_z, hr2_z, add_zero]
      obtain ⟨slot₂, hinv₂, hreach₁⟩ := mLogStep_of_decnz_zero (regs := regs₁) hinv₁ hev10 hr2_zero
      have hreach₀₁ := mReachPos_trans hreach₀ hreach₁
      have hregs_eq : regs₁ = mRegPairOp out r1 r2 regs := by
        dsimp [regs₁, mRegPairOp]
        rw [hr1_z, hr2_z, add_zero, mPair_zero_zero]
      rw [hregs_eq] at hinv₂ hreach₀₁
      exact ⟨slot₂, hinv₂, hreach₀₁⟩)
    (fun m ih slot regs hinv hn ↦ by
      have hinv0 : MZfLogInv slot (trimZeros (P ++ [0])) regs := by rwa [trimZeros_append_zero]
      obtain ⟨_, slot₁, hinv₁, hreach₀⟩ := hmove2 (P ++ [0]) hP0 slot regs hinv0
      rw [trimZeros_append_zero, retStack_append_zero] at hreach₀
      rw [retStack_append_zero] at hinv₁
      dsimp only at hinv₁ hreach₀
      let regs₁ := ((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
        out (regs.getD out 0 + regs.getD r1 0)
      have hr2_succ : regs₁.getD r2 0 = m + 1 := by
        dsimp [regs₁]
        rw [mGetD_set_ne _ _ hne2o.symm,
          mGetD_set_self _ r2 _ (by rw [List.length_set, hinv.1]; exact hr2),
          add_comm, hn]
      obtain ⟨slot₂, hinv₂, hreach₁⟩ := mLogStep_of_decnz_succ (regs := regs₁) hinv₁ hev10 hr2_succ
      have hinv110 : MZfLogInv slot₂ (trimZeros (P ++ [1] ++ [1] ++ [0])) (regs₁.set r2 m) := by
        rwa [trimZeros_append_zero, trimZeros_append_one]
      obtain ⟨_, slot₃, hinv₃, hreach₃⟩ :=
        hbody (P ++ [1] ++ [1] ++ [0]) hP110 slot₂ (regs₁.set r2 m) hinv110
      rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hreach₃
      rw [retStack_append_zero] at hinv₃
      dsimp only at hinv₃ hreach₃
      let regs₂ := ((regs.set r1 m).set r2 0).set out (regs.getD out 0 + regs.getD r1 0 + 1)
      have hbody_eq :
          (let r₀ := (regs₁.set r2 m).set out ((regs₁.set r2 m).getD out 0 + 1)
           (r₀.set r2 0).set r1 (r₀.getD r1 0 + r₀.getD r2 0)) = regs₂ := by
        dsimp only [regs₁, regs₂]
        have hout_get :
            ((((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
              out (regs.getD out 0 + regs.getD r1 0)).set r2 m).getD out 0 =
            regs.getD out 0 + regs.getD r1 0 := by
          rw [mGetD_set_ne _ _ hne2o,
            mGetD_set_self _ out _ (by simp [hinv.1, hout])]
        rw [hout_get]
        have hr0_eq :
            ((((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
              out (regs.getD out 0 + regs.getD r1 0)).set r2 m).set
              out (regs.getD out 0 + regs.getD r1 0 + 1) =
            ((regs.set r1 0).set r2 m).set out (regs.getD out 0 + regs.getD r1 0 + 1) := by
          rw [mSet_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0) m hne2o.symm,
            List.set_set, List.set_set]
        rw [hr0_eq]
        have hr1_get :
            (((regs.set r1 0).set r2 m).set
              out (regs.getD out 0 + regs.getD r1 0 + 1)).getD r1 0 = 0 := by
          rw [mGetD_set_ne _ _ hne1o.symm, mGetD_set_ne _ _ hne12.symm,
            mGetD_set_self regs r1 0 (by rw [hinv.1]; exact hr1)]
        have hr2_get :
            (((regs.set r1 0).set r2 m).set
              out (regs.getD out 0 + regs.getD r1 0 + 1)).getD r2 0 = m := by
          rw [mGetD_set_ne _ _ hne2o.symm, mGetD_set_self _ r2 m (by simp [hinv.1, hr2])]
        rw [hr1_get, hr2_get, zero_add,
          mSet_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) 0 hne2o.symm,
          List.set_set,
          mSet_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) m hne1o.symm,
          mSet_comm_of_ne (regs.set r1 0) 0 m hne12.symm,
          List.set_set]
      rw [hbody_eq] at hinv₃ hreach₃
      obtain ⟨slot₄, hinv₄, hreach_jmp⟩ := mLogStep_of_jump (regs := regs₂) hinv₃ hev21
      have hr1_₂ : regs₂.getD r1 0 = m := by
        dsimp [regs₂]
        rw [mGetD_set_ne _ _ hne1o.symm, mGetD_set_ne _ _ hne12.symm,
          mGetD_set_self regs r1 m (by rw [hinv.1]; exact hr1)]
      have hr2_₂ : regs₂.getD r2 0 = 0 := by
        dsimp [regs₂]
        rw [mGetD_set_ne _ _ hne2o.symm, mGetD_set_self _ r2 0 (by simp [hinv.1, hr2])]
      have hout_₂ : regs₂.getD out 0 = regs.getD out 0 + regs.getD r1 0 + 1 := by
        dsimp [regs₂]
        exact mGetD_set_self _ out _ (by simp [hinv.1, hout])
      obtain ⟨slot₅, hinv₅, hreach_ih⟩ :=
        ih slot₄ regs₂ hinv₄ (by rw [hr1_₂, hr2_₂, add_zero])
      have hfinal_eq : mRegPairOp out r1 r2 regs₂ = mRegPairOp out r1 r2 regs := by
        unfold mRegPairOp
        rw [hout_₂, hr1_₂, hr2_₂, mPair_step_inv hn]
        dsimp only [regs₂]
        rw [mSet_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) 0 hne1o.symm,
          mSet_comm_of_ne (regs.set r1 m) 0 0 hne12.symm,
          List.set_set,
          mSet_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) 0 hne2o.symm,
          List.set_set, List.set_set]
      rw [hfinal_eq] at hinv₅ hreach_ih
      exact ⟨slot₅, hinv₅, mReachPos_trans hreach₀
        (mReachPos_trans hreach₁
          (mReachPos_trans hreach₃ (mReachPos_trans hreach_jmp hreach_ih)))⟩)
  intro slot regs hinv
  exact ⟨by simp [mRegPairOp, hinv.1],
    hloop (regs.getD r1 0 + regs.getD r2 0) slot regs hinv rfl⟩

/-- Closed-form Cantor unpairing register operation `unpair(out1, out2, rin)` on `PAM M`. -/
noncomputable def mRegUnpairGen (out1 out2 rin : ℕ) (regs : List (PAM M)) : List (PAM M) :=
  let p := mUnpair (regs.getD rin 0 + mPair (regs.getD out1 0) (regs.getD out2 0))
  ((regs.set rin 0).set out1 p.1).set out2 p.2

theorem paFunRegs_mRegUnpairGen (out1 out2 rin : ℕ) {n : ℕ} {R : (Fin n → PAM M) → List (PAM M)}
    (hR : PAFunRegs n R) : PAFunRegs n (fun u ↦ mRegUnpairGen out1 out2 rin (R u)) := by
  have harg : PAFunN n (fun u ↦
      (R u).getD rin 0 + mPair ((R u).getD out1 0) ((R u).getD out2 0)) :=
    paFun_add (paFunRegs_getD hR rin)
      (paFun_mPair (paFunRegs_getD hR out1) (paFunRegs_getD hR out2))
  exact paFunRegs_set
    (paFunRegs_set (paFunRegs_set hR rin (paFun_const 0)) out1 (paFun_mUnpair_fst harg))
    out2 (paFun_mUnpair_snd harg)

theorem mSubEval_unpair {q q_dec q1 q_inc1 q2 q3 q_move : Fin 393} (out1 rin : ℕ)
    (hout1 : out1 < 11) (hrin : rin < 11)
    (hne_in_1 : rin ≠ out1) (hne_in_9 : rin ≠ 9) (hne_1_9 : out1 ≠ 9)
    (htr0 : zf393Trans q 0 = some (0, .right, q_dec))
    (hdec29 : 29 ≤ q_dec.val) (hdec50 : q_dec.val ≤ 50) (hdec : isLeafInc q_dec = false)
    (hlr_dec : logLeafReg q_dec = rin)
    (htr1 : zf393Trans q 1 = some (1, .right, q1)) (hq1 : 69 ≤ q1.val)
    (htr10 : zf393Trans q1 0 = some (0, .right, q_inc1))
    (hinc29 : 29 ≤ q_inc1.val) (hinc50 : q_inc1.val ≤ 50) (hinc : isLeafInc q_inc1 = true)
    (hlr_inc : logLeafReg q_inc1 = out1)
    (htr11 : zf393Trans q1 1 = some (1, .right, q2)) (hq2 : 69 ≤ q2.val)
    (htr20 : zf393Trans q2 0 = some (0, .right, 309))
    (htr21 : zf393Trans q2 1 = some (1, .right, q3)) (hq3 : 69 ≤ q3.val)
    (htr30 : zf393Trans q3 0 = some (0, .right, q_move)) (hq_move : 69 ≤ q_move.val)
    (htr31 : zf393Trans q3 1 = some (0, .left, 67))
    (hmove : MSubEval (M := M) q_move (fun regs ↦
      (regs.set out1 0).set 9 (regs.getD 9 0 + regs.getD out1 0))) :
    MSubEval (M := M) q (mRegUnpairGen out1 9 rin) := by
  intro P hP
  have hP1 : walkInternal 99 (P ++ [1]) = some q1 := walkInternal_snoc hP htr1 hq1
  have hP11 : walkInternal 99 (P ++ [1] ++ [1]) = some q2 := walkInternal_snoc hP1 htr11 hq2
  have hP110 : walkInternal 99 (P ++ [1] ++ [1] ++ [0]) = some 309 :=
    walkInternal_snoc hP11 htr20 (by decide)
  have hP111 : walkInternal 99 (P ++ [1] ++ [1] ++ [1]) = some q3 :=
    walkInternal_snoc hP11 htr21 hq3
  have hP1110 : walkInternal 99 (P ++ [1] ++ [1] ++ [1] ++ [0]) = some q_move :=
    walkInternal_snoc hP111 htr30 hq_move
  have hev0 : evalStack (trimZeros P) = .decnz rin (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 hdec29 hdec50]
    simp [hdec, hlr_dec]
  have hev10 : evalStack (P ++ [1]) = .inc out1 (P ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hP1 htr10 hinc29 hinc50
    simpa [hinc, hlr_inc] using h
  have hev11 : evalStack (P ++ [1] ++ [1]) =
      .decnz 9 (P ++ [1] ++ [1] ++ [0] ++ [1]) (P ++ [1] ++ [1] ++ [1]) := by
    have htrim := evalStack_trimZeros_of_walkInternal hP110
    rw [trimZeros_append_zero, trimZeros_append_one] at htrim
    have hleaf := evalStack_leaf0_of_walkInternal (q' := 43) hP110 rfl (by decide) (by decide)
    rw [htrim, hleaf, retStack_append_zero]
    rfl
  have hev1101 : evalStack (P ++ [1] ++ [1] ++ [0] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal
      (P := P ++ [1] ++ [1] ++ [0]) (k := 2) (by omega) hP110 rfl
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hev1111 : evalStack (P ++ [1] ++ [1] ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal
      (P := P ++ [1] ++ [1] ++ [1]) (k := 3) (by omega) hP111 htr31
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop := ind1_subEval_loop (M := M) (trimZeros P) (retStack P)
    (fun z regs ↦ regs.getD rin 0 = z)
    (fun _ regs ↦ mRegUnpairGen out1 9 rin regs)
    (paDef_eq (paFunRegs_getD paFunRegs_regsOfVec13 rin) (paFun_proj 0))
    (paFunRegs_mRegUnpairGen out1 9 rin paFunRegs_regsOfVec13)
    (fun slot regs hinv hz ↦ by
      obtain ⟨slot', hinv', hreach⟩ := mLogStep_of_decnz_zero hinv hev0 hz
      have hset : mRegUnpairGen out1 9 rin regs = regs := by
        unfold mRegUnpairGen
        rw [hz, zero_add, mUnpair_mPair]
        dsimp only
        rw [mSet_eq_self_of_getD_eq hz, mSet_getD_self, mSet_getD_self]
      rw [hset]
      exact ⟨slot', hinv', hreach⟩)
    (fun z ih slot regs hinv hz ↦ by
      obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_succ hinv hev0 hz
      obtain ⟨slot₂, hinv₂, hreach₂⟩ := mLogStep_of_inc hinv₁ hev10
      rw [mGetD_set_ne _ _ hne_in_1] at hinv₂ hreach₂
      let regs₁ := (regs.set rin z).set out1 (regs.getD out1 0 + 1)
      have hr9_₁ : regs₁.getD 9 0 = regs.getD 9 0 := by
        dsimp [regs₁]
        rw [mGetD_set_ne _ _ hne_1_9, mGetD_set_ne _ _ hne_in_9]
      rcases eq_zero_or_exists_succ (regs.getD 9 0) with hy | ⟨y, hy⟩
      · obtain ⟨slot₃, hinv₃, hreach₃⟩ :=
          mLogStep_of_decnz_zero (regs := regs₁) hinv₂ hev11 (by rw [hr9_₁, hy])
        have hinv1110 : MZfLogInv slot₃ (trimZeros (P ++ [1] ++ [1] ++ [1] ++ [0])) regs₁ := by
          rwa [trimZeros_append_zero, trimZeros_append_one]
        obtain ⟨_, slot₄, hinv₄, hreach_m⟩ :=
          hmove (P ++ [1] ++ [1] ++ [1] ++ [0]) hP1110 slot₃ regs₁ hinv1110
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hreach_m
        rw [retStack_append_zero] at hinv₄
        dsimp only at hinv₄ hreach_m
        let regs₂ := ((regs.set rin z).set out1 0).set 9 (regs.getD out1 0 + 1)
        have hm_eq :
            (regs₁.set out1 0).set 9 (regs₁.getD 9 0 + regs₁.getD out1 0) = regs₂ := by
          rw [hr9_₁, hy, zero_add]
          dsimp [regs₁, regs₂]
          rw [mGetD_set_self _ out1 _ (by simp [hinv.1, hout1]), List.set_set]
        rw [hm_eq] at hinv₄ hreach_m
        obtain ⟨slot₅, hinv₅, hreach_jmp⟩ := mLogStep_of_jump (regs := regs₂) hinv₄ hev1111
        have hrin_₂ : regs₂.getD rin 0 = z := by
          dsimp [regs₂]
          rw [mGetD_set_ne _ _ hne_in_9.symm, mGetD_set_ne _ _ hne_in_1.symm,
            mGetD_set_self regs rin z (by rw [hinv.1]; exact hrin)]
        obtain ⟨slot₆, hinv₆, hreach_ih⟩ := ih slot₅ regs₂ hinv₅ hrin_₂
        have hgen_eq : mRegUnpairGen out1 9 rin regs₂ = mRegUnpairGen out1 9 rin regs := by
          unfold mRegUnpairGen
          have hout1_₂ : regs₂.getD out1 0 = 0 := by
            dsimp [regs₂]
            rw [mGetD_set_ne _ _ hne_1_9.symm, mGetD_set_self _ out1 0 (by simp [hinv.1, hout1])]
          have hr9_₂ : regs₂.getD 9 0 = regs.getD out1 0 + 1 := by
            dsimp [regs₂]
            exact mGetD_set_self _ 9 _ (by simp [hinv.1])
          have hpair_eq : z + mPair 0 (regs.getD out1 0 + 1) =
              (z + 1) + mPair (regs.getD out1 0) 0 := by
            rw [mPair_zero_succ]
            ring
          rw [hrin_₂, hout1_₂, hr9_₂, hz, hy, hpair_eq]
          dsimp only [regs₂]
          rw [mSet_comm_of_ne _ (regs.getD out1 0 + 1) 0 hne_in_9.symm,
            mSet_comm_of_ne (regs.set rin z) 0 0 hne_in_1.symm,
            List.set_set,
            mSet_comm_of_ne _ (regs.getD out1 0 + 1) _ hne_1_9.symm,
            List.set_set, List.set_set]
        rw [hgen_eq] at hinv₆ hreach_ih
        exact ⟨slot₆, hinv₆, mReachPos_trans hreach₁
          (mReachPos_trans hreach₂
            (mReachPos_trans hreach₃
              (mReachPos_trans hreach_m (mReachPos_trans hreach_jmp hreach_ih))))⟩
      · obtain ⟨slot₃, hinv₃, hreach₃⟩ :=
          mLogStep_of_decnz_succ (regs := regs₁) hinv₂ hev11 (by rw [hr9_₁, hy])
        let regs₂ := regs₁.set 9 y
        obtain ⟨slot₄, hinv₄, hreach_jmp⟩ := mLogStep_of_jump (regs := regs₂) hinv₃ hev1101
        have hrin_₂ : regs₂.getD rin 0 = z := by
          dsimp [regs₂, regs₁]
          rw [mGetD_set_ne _ _ hne_in_9.symm, mGetD_set_ne _ _ hne_in_1.symm,
            mGetD_set_self regs rin z (by rw [hinv.1]; exact hrin)]
        obtain ⟨slot₅, hinv₅, hreach_ih⟩ := ih slot₄ regs₂ hinv₄ hrin_₂
        have hgen_eq : mRegUnpairGen out1 9 rin regs₂ = mRegUnpairGen out1 9 rin regs := by
          unfold mRegUnpairGen
          have hout1_₂ : regs₂.getD out1 0 = regs.getD out1 0 + 1 := by
            dsimp [regs₂, regs₁]
            rw [mGetD_set_ne _ _ hne_1_9.symm,
              mGetD_set_self _ out1 _ (by simp [hinv.1, hout1])]
          have hr9_₂ : regs₂.getD 9 0 = y := by
            dsimp [regs₂, regs₁]
            exact mGetD_set_self _ 9 y (by simp [hinv.1])
          have hpair_eq : z + mPair (regs.getD out1 0 + 1) y =
              (z + 1) + mPair (regs.getD out1 0) (y + 1) := by
            rw [mPair_succ_left]
            ring
          rw [hrin_₂, hout1_₂, hr9_₂, hz, hy, hpair_eq]
          dsimp only [regs₂, regs₁]
          rw [mSet_comm_of_ne _ y 0 hne_in_9.symm,
            mSet_comm_of_ne (regs.set rin z) (regs.getD out1 0 + 1) 0 hne_in_1.symm,
            List.set_set,
            mSet_comm_of_ne _ y _ hne_1_9.symm,
            List.set_set, List.set_set]
        rw [hgen_eq] at hinv₅ hreach_ih
        exact ⟨slot₅, hinv₅, mReachPos_trans hreach₁
          (mReachPos_trans hreach₂
            (mReachPos_trans hreach₃ (mReachPos_trans hreach_jmp hreach_ih)))⟩)
  intro slot regs hinv
  exact ⟨by simp [mRegUnpairGen, hinv.1], hloop (regs.getD rin 0) slot regs hinv rfl⟩

/-! ## Section 4: Concrete Subroutine Instantiations (`69..392`) -/

theorem mSubEval_342 : MSubEval (M := M) 342 (fun regs ↦ regs.set 4 0) :=
  mSubEval_while_clear 4 (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_346 : MSubEval (M := M) 346 (fun regs ↦ regs.set 5 0) :=
  mSubEval_while_clear 5 (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_352 : MSubEval (M := M) 352 (fun regs ↦ regs.set 6 0) :=
  mSubEval_while_clear 6 (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_356 : MSubEval (M := M) 356 (fun regs ↦ regs.set 7 0) :=
  mSubEval_while_clear 7 (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_359 : MSubEval (M := M) 359 (fun regs ↦ regs.set 8 0) :=
  mSubEval_while_clear 8 (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_376 : MSubEval (M := M) 376 (fun regs ↦ regs.set 9 0) :=
  mSubEval_while_clear 9 (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_381 : MSubEval (M := M) 381 (fun regs ↦ regs.set 10 0) :=
  mSubEval_while_clear 10 (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_382 : MSubEval (M := M) 382 (fun regs ↦ regs.set 2 0) :=
  mSubEval_while_clear 2 (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_360 :
    MSubEval (M := M) 360 (fun regs ↦ (regs.set 8 0).set 4 (regs.getD 4 0 + regs.getD 8 0)) :=
  mSubEval_while_move1 8 4 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_362 :
    MSubEval (M := M) 362 (fun regs ↦ (regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0)) :=
  mSubEval_while_move1 8 1 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_364 :
    MSubEval (M := M) 364 (fun regs ↦ (regs.set 8 0).set 5 (regs.getD 5 0 + regs.getD 8 0)) :=
  mSubEval_while_move1 8 5 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_366 :
    MSubEval (M := M) 366 (fun regs ↦ (regs.set 8 0).set 6 (regs.getD 6 0 + regs.getD 8 0)) :=
  mSubEval_while_move1 8 6 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_368 :
    MSubEval (M := M) 368 (fun regs ↦ (regs.set 8 0).set 7 (regs.getD 7 0 + regs.getD 8 0)) :=
  mSubEval_while_move1 8 7 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_370 :
    MSubEval (M := M) 370 (fun regs ↦ (regs.set 8 0).set 9 (regs.getD 9 0 + regs.getD 8 0)) :=
  mSubEval_while_move1 8 9 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_371 :
    MSubEval (M := M) 371 (fun regs ↦ (regs.set 8 0).set 2 (regs.getD 2 0 + regs.getD 8 0)) :=
  mSubEval_while_move1 8 2 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_372 :
    MSubEval (M := M) 372 (fun regs ↦ (regs.set 8 0).set 3 (regs.getD 3 0 + regs.getD 8 0)) :=
  mSubEval_while_move1 8 3 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_377 :
    MSubEval (M := M) 377 (fun regs ↦ (regs.set 9 0).set 0 (regs.getD 0 0 + regs.getD 9 0)) :=
  mSubEval_while_move1 9 0 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_379 :
    MSubEval (M := M) 379 (fun regs ↦ (regs.set 9 0).set 2 (regs.getD 2 0 + regs.getD 9 0)) :=
  mSubEval_while_move1 9 2 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_380 :
    MSubEval (M := M) 380 (fun regs ↦ (regs.set 9 0).set 3 (regs.getD 3 0 + regs.getD 9 0)) :=
  mSubEval_while_move1 9 3 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_386 :
    MSubEval (M := M) 386 (fun regs ↦ (regs.set 2 0).set 8 (regs.getD 8 0 + regs.getD 2 0)) :=
  mSubEval_while_move1 2 8 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_388 :
    MSubEval (M := M) 388 (fun regs ↦ (regs.set 2 0).set 9 (regs.getD 9 0 + regs.getD 2 0)) :=
  mSubEval_while_move1 2 9 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_389 :
    MSubEval (M := M) 389 (fun regs ↦ (regs.set 3 0).set 2 (regs.getD 2 0 + regs.getD 3 0)) :=
  mSubEval_while_move1 3 2 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

theorem mSubEval_343 :
    MSubEval (M := M) 343 (fun regs ↦
      ((regs.set 1 0).set 8 (regs.getD 8 0 + regs.getD 1 0)).set
        0 (regs.getD 0 0 + regs.getD 1 0)) :=
  mSubEval_while_move2 1 8 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

theorem mSubEval_351 :
    MSubEval (M := M) 351 (fun regs ↦
      ((regs.set 5 0).set 8 (regs.getD 8 0 + regs.getD 5 0)).set
        9 (regs.getD 9 0 + regs.getD 5 0)) :=
  mSubEval_while_move2 5 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

theorem mSubEval_347 :
    MSubEval (M := M) 347 (fun regs ↦
      ((regs.set 5 0).set 2 (regs.getD 2 0 + regs.getD 5 0)).set
        8 (regs.getD 8 0 + regs.getD 5 0)) :=
  mSubEval_while_move2 5 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

theorem mSubEval_348 :
    MSubEval (M := M) 348 (fun regs ↦
      ((regs.set 5 0).set 8 (regs.getD 8 0 + regs.getD 5 0)).set
        2 (regs.getD 2 0 + regs.getD 5 0)) :=
  mSubEval_while_move2 5 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

theorem mSubEval_355 :
    MSubEval (M := M) 355 (fun regs ↦
      ((regs.set 6 0).set 8 (regs.getD 8 0 + regs.getD 6 0)).set
        9 (regs.getD 9 0 + regs.getD 6 0)) :=
  mSubEval_while_move2 6 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

theorem mSubEval_353 :
    MSubEval (M := M) 353 (fun regs ↦
      ((regs.set 6 0).set 2 (regs.getD 2 0 + regs.getD 6 0)).set
        8 (regs.getD 8 0 + regs.getD 6 0)) :=
  mSubEval_while_move2 6 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

theorem mSubEval_354 :
    MSubEval (M := M) 354 (fun regs ↦
      ((regs.set 6 0).set 8 (regs.getD 8 0 + regs.getD 6 0)).set
        10 (regs.getD 10 0 + regs.getD 6 0)) :=
  mSubEval_while_move2 6 8 10 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

theorem mSubEval_357 :
    MSubEval (M := M) 357 (fun regs ↦
      ((regs.set 7 0).set 2 (regs.getD 2 0 + regs.getD 7 0)).set
        8 (regs.getD 8 0 + regs.getD 7 0)) :=
  mSubEval_while_move2 7 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

theorem mSubEval_358 :
    MSubEval (M := M) 358 (fun regs ↦
      ((regs.set 7 0).set 8 (regs.getD 8 0 + regs.getD 7 0)).set
        10 (regs.getD 10 0 + regs.getD 7 0)) :=
  mSubEval_while_move2 7 8 10 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

theorem mSubEval_373 :
    MSubEval (M := M) 373 (fun regs ↦
      ((regs.set 8 0).set 2 (regs.getD 2 0 + regs.getD 8 0)).set
        9 (regs.getD 9 0 + regs.getD 8 0)) :=
  mSubEval_while_move2 8 2 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

theorem mSubEval_383 :
    MSubEval (M := M) 383 (fun regs ↦
      ((regs.set 2 0).set 3 (regs.getD 3 0 + regs.getD 2 0)).set
        8 (regs.getD 8 0 + regs.getD 2 0)) :=
  mSubEval_while_move2 2 3 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

theorem mSubEval_293 :
    MSubEval (M := M) 293 (fun regs ↦
      let r₀ := regs.set 8 (regs.getD 8 0 + 1)
      (r₀.set 3 0).set 2 (r₀.getD 2 0 + r₀.getD 3 0)) :=
  mSubEval_inc_seq (q₀ := 42) rfl (by decide) (by decide) rfl rfl (by decide) mSubEval_389

theorem mSubEval_297 :
    MSubEval (M := M) 297 (fun regs ↦
      let r₀ := regs.set 9 (regs.getD 9 0 + 1)
      (r₀.set 2 0).set 8 (r₀.getD 8 0 + r₀.getD 2 0)) :=
  mSubEval_inc_seq (q₀ := 44) rfl (by decide) (by decide) rfl rfl (by decide) mSubEval_386

theorem mSubEval_290 : MSubEval (M := M) 290 (mRegPairOp 8 2 3) :=
  mSubEval_pair 8 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl mSubEval_383 mSubEval_293

theorem mSubEval_294 : MSubEval (M := M) 294 (mRegPairOp 9 8 2) :=
  mSubEval_pair 9 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl mSubEval_373 mSubEval_297

theorem mSubEval_313 : MSubEval (M := M) 313 (mRegUnpairGen 8 9 0) :=
  mSubEval_unpair 8 0 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl mSubEval_370

theorem mSubEval_314 : MSubEval (M := M) 314 (mRegUnpairGen 8 9 3) :=
  mSubEval_unpair 8 3 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl mSubEval_370

theorem mSubEval_315 : MSubEval (M := M) 315 (mRegUnpairGen 2 9 3) :=
  mSubEval_unpair 2 3 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl mSubEval_388

noncomputable def mReg269Op (regs : List (PAM M)) : List (PAM M) :=
  let r := mRegUnpairGen 8 9 0 regs
  (r.set 9 0).set 0 (r.getD 0 0 + r.getD 9 0)

theorem mSubEval_269 : MSubEval (M := M) 269 mReg269Op := by
  unfold mReg269Op
  exact mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_313 mSubEval_377

noncomputable def mReg289Op (regs : List (PAM M)) : List (PAM M) :=
  let r := mRegUnpairGen 8 9 3 regs
  (r.set 9 0).set 3 (r.getD 3 0 + r.getD 9 0)

theorem mSubEval_289 : MSubEval (M := M) 289 mReg289Op := by
  unfold mReg289Op
  exact mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_314 mSubEval_380

noncomputable def mReg70Op (regs : List (PAM M)) : List (PAM M) :=
  let r := mRegPairOp 9 8 2 regs
  (r.set 9 0).set 2 (r.getD 2 0 + r.getD 9 0)

theorem mSubEval_70 : MSubEval (M := M) 70 mReg70Op := by
  unfold mReg70Op
  exact mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_294 mSubEval_379

noncomputable def mRegConsOp (regs : List (PAM M)) : List (PAM M) :=
  mReg70Op (mReg289Op regs)

theorem mSubEval_69 : MSubEval (M := M) 69 mRegConsOp := by
  unfold mRegConsOp
  exact mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_289 mSubEval_70

noncomputable def mRegPushwffOp (regs : List (PAM M)) : List (PAM M) :=
  let r := mRegPairOp 8 2 3 regs
  (r.set 8 0).set 3 (r.getD 3 0 + r.getD 8 0)

theorem mSubEval_304 : MSubEval (M := M) 304 mRegPushwffOp := by
  unfold mRegPushwffOp
  exact mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_290 mSubEval_372

noncomputable def mRegV1Op (regs : List (PAM M)) : List (PAM M) :=
  let r := mRegPushwffOp regs
  r.set 2 (r.getD 2 0 + 1)

theorem mSubEval_319 : MSubEval (M := M) 319 mRegV1Op := by
  unfold mRegV1Op
  exact mSubEval_seq_inc (q₁ := 48) rfl (by decide) rfl (by decide) (by decide) rfl mSubEval_304

theorem mSubEval_288 :
    MSubEval (M := M) 288 (fun regs ↦ regs.set 2 (regs.getD 2 0 + 2)) := by
  refine (mSubEval_inc_inc (M := M) rfl (by decide) (by decide) rfl
    rfl (by decide) (by decide) rfl).congr ?_
  intro regs hlen
  change (regs.set 2 (regs.getD 2 0 + 1)).set 2
    ((regs.set 2 (regs.getD 2 0 + 1)).getD 2 0 + 1) = regs.set 2 (regs.getD 2 0 + 2)
  rw [mGetD_set_self regs 2 (regs.getD 2 0 + 1) (by omega), List.set_set]
  congr 1
  ring

noncomputable def mRegV2Op (regs : List (PAM M)) : List (PAM M) :=
  let r := mRegV1Op regs
  r.set 2 (r.getD 2 0 + 1)

theorem mSubEval_320 : MSubEval (M := M) 320 mRegV2Op := by
  refine (mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_304 mSubEval_288).congr ?_
  intro regs hlen
  dsimp only [mRegV2Op, mRegV1Op]
  have hlen0 : 2 < (mRegPushwffOp regs).length := by simp [mRegPushwffOp, mRegPairOp, hlen]
  rw [mGetD_set_self (mRegPushwffOp regs) 2 _ hlen0, List.set_set]
  congr 1
  ring

noncomputable def mRegV3Op (regs : List (PAM M)) : List (PAM M) :=
  let r := mRegV2Op regs
  r.set 2 (r.getD 2 0 + 1)

theorem mSubEval_321 : MSubEval (M := M) 321 mRegV3Op := by
  refine (mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_319 mSubEval_288).congr ?_
  intro regs hlen
  dsimp only [mRegV3Op, mRegV2Op]
  have hlen1 : 2 < (mRegV1Op regs).length := by simp [mRegV1Op, mRegPushwffOp, mRegPairOp, hlen]
  rw [mGetD_set_self (mRegV1Op regs) 2 _ hlen1, List.set_set]
  congr 1
  ring

noncomputable def mRegV4Op (regs : List (PAM M)) : List (PAM M) :=
  let r := mRegV3Op regs
  r.set 2 (r.getD 2 0 + 1)

theorem mSubEval_322 : MSubEval (M := M) 322 mRegV4Op := by
  refine (mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_320 mSubEval_288).congr ?_
  intro regs hlen
  dsimp only [mRegV4Op, mRegV3Op]
  have hlen2 : 2 < (mRegV2Op regs).length := by
    simp [mRegV2Op, mRegV1Op, mRegPushwffOp, mRegPairOp, hlen]
  rw [mGetD_set_self (mRegV2Op regs) 2 _ hlen2, List.set_set]
  congr 1
  ring

noncomputable def mReg330Op (regs : List (PAM M)) : List (PAM M) :=
  mRegConsOp (mRegPushwffOp regs)

theorem mSubEval_330 : MSubEval (M := M) 330 mReg330Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_304 mSubEval_69

noncomputable def mRegWeqOp (regs : List (PAM M)) : List (PAM M) :=
  mReg330Op (mRegConsOp regs)

theorem mSubEval_329 : MSubEval (M := M) 329 mRegWeqOp :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_69 mSubEval_330

noncomputable def mReg328Op (regs : List (PAM M)) : List (PAM M) :=
  mRegConsOp (mRegV1Op regs)

theorem mSubEval_328 : MSubEval (M := M) 328 mReg328Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_319 mSubEval_69

noncomputable def mRegWelOp (regs : List (PAM M)) : List (PAM M) :=
  mReg328Op (mRegConsOp regs)

theorem mSubEval_327 : MSubEval (M := M) 327 mRegWelOp :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_69 mSubEval_328

noncomputable def mReg391Op (regs : List (PAM M)) : List (PAM M) :=
  mRegConsOp (mRegV2Op regs)

theorem mSubEval_391 : MSubEval (M := M) 391 mReg391Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_320 mSubEval_69

noncomputable def mRegWimOp (regs : List (PAM M)) : List (PAM M) :=
  mReg391Op (mRegConsOp regs)

theorem mSubEval_390 : MSubEval (M := M) 390 mRegWimOp :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_69 mSubEval_391

noncomputable def mRegWnOp (regs : List (PAM M)) : List (PAM M) :=
  mRegConsOp (mRegV3Op regs)

theorem mSubEval_392 : MSubEval (M := M) 392 mRegWnOp :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_321 mSubEval_69

noncomputable def mReg326Op (regs : List (PAM M)) : List (PAM M) :=
  mRegConsOp (mRegV4Op regs)

theorem mSubEval_326 : MSubEval (M := M) 326 mReg326Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_322 mSubEval_69

noncomputable def mRegWalOp (regs : List (PAM M)) : List (PAM M) :=
  mReg326Op (mRegConsOp regs)

theorem mSubEval_325 : MSubEval (M := M) 325 mRegWalOp :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_69 mSubEval_326

noncomputable def mReg332Op (regs : List (PAM M)) : List (PAM M) :=
  mRegWnOp (mRegWalOp regs)

theorem mSubEval_332 : MSubEval (M := M) 332 mReg332Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_325 mSubEval_392

noncomputable def mRegWexOp (regs : List (PAM M)) : List (PAM M) :=
  mReg332Op (mRegWnOp regs)

theorem mSubEval_331 : MSubEval (M := M) 331 mRegWexOp :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_392 mSubEval_332

noncomputable def mReg324Op (regs : List (PAM M)) : List (PAM M) :=
  mRegWnOp (mRegWimOp regs)

theorem mSubEval_324 : MSubEval (M := M) 324 mReg324Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_390 mSubEval_392

noncomputable def mRegWaOp (regs : List (PAM M)) : List (PAM M) :=
  mReg324Op (mRegWnOp regs)

theorem mSubEval_323 : MSubEval (M := M) 323 mRegWaOp :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_392 mSubEval_324

def mReg299Op (regs : List (PAM M)) : List (PAM M) :=
  let r := ((regs.set 5 0).set 2 (regs.getD 2 0 + regs.getD 5 0)).set
    8 (regs.getD 8 0 + regs.getD 5 0)
  (r.set 8 0).set 5 (r.getD 5 0 + r.getD 8 0)

theorem mSubEval_299 : MSubEval (M := M) 299 mReg299Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_347 mSubEval_364

noncomputable def mRegPar1Op (regs : List (PAM M)) : List (PAM M) :=
  mReg299Op (mRegPushwffOp regs)

theorem mSubEval_298 : MSubEval (M := M) 298 mRegPar1Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_304 mSubEval_299

def mReg301Op (regs : List (PAM M)) : List (PAM M) :=
  let r := ((regs.set 6 0).set 2 (regs.getD 2 0 + regs.getD 6 0)).set
    8 (regs.getD 8 0 + regs.getD 6 0)
  (r.set 8 0).set 6 (r.getD 6 0 + r.getD 8 0)

theorem mSubEval_301 : MSubEval (M := M) 301 mReg301Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_353 mSubEval_366

noncomputable def mRegPar2Op (regs : List (PAM M)) : List (PAM M) :=
  mReg301Op (mRegPushwffOp regs)

theorem mSubEval_300 : MSubEval (M := M) 300 mRegPar2Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_304 mSubEval_301

def mReg303Op (regs : List (PAM M)) : List (PAM M) :=
  let r := ((regs.set 7 0).set 2 (regs.getD 2 0 + regs.getD 7 0)).set
    8 (regs.getD 8 0 + regs.getD 7 0)
  (r.set 8 0).set 7 (r.getD 7 0 + r.getD 8 0)

theorem mSubEval_303 : MSubEval (M := M) 303 mReg303Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_357 mSubEval_368

noncomputable def mRegPar3Op (regs : List (PAM M)) : List (PAM M) :=
  mReg303Op (mRegPushwffOp regs)

theorem mSubEval_302 : MSubEval (M := M) 302 mRegPar3Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_304 mSubEval_303

theorem mSubEval_98 :
    MSubEval (M := M) 98 (fun regs ↦
      (regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0 + 1)) := by
  refine (mSubEval_seq_inc rfl (by decide) rfl (by decide) (by decide) rfl mSubEval_362).congr ?_
  intro regs hlen
  change ((regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0)).set 1
    (((regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0)).getD 1 0 + 1) =
    (regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0 + 1)
  rw [mGetD_set_self _ 1 _ (by simp [hlen]), List.set_set]

def mReg97Op (regs : List (PAM M)) : List (PAM M) :=
  let r := ((regs.set 1 0).set 8 (regs.getD 8 0 + regs.getD 1 0)).set 0
    (regs.getD 0 0 + regs.getD 1 0)
  (r.set 8 0).set 1 (r.getD 1 0 + r.getD 8 0 + 1)

theorem mSubEval_97 : MSubEval (M := M) 97 mReg97Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_343 mSubEval_98

noncomputable def mReg95Op (regs : List (PAM M)) : List (PAM M) :=
  if regs.getD 0 0 = 0 then
    mReg97Op regs
  else
    regs.set 0 (regs.getD 0 0 - 1)

theorem mSubEval_95 : MSubEval (M := M) 95 mReg95Op := by
  intro P hP slot regs hinv
  unfold mReg95Op
  have hP0 : walkInternal 99 (P ++ [0]) = some 96 := walkInternal_snoc hP rfl (by decide)
  have hP1 : walkInternal 99 (P ++ [1]) = some 97 := walkInternal_snoc hP rfl (by decide)
  have hev0 : evalStack (trimZeros P) = .decnz 0 (P ++ [0] ++ [1]) (P ++ [1]) := by
    rw [← trimZeros_append_zero P, evalStack_trimZeros_of_walkInternal hP0,
      evalStack_leaf0_of_walkInternal hP0 rfl (by decide) (by decide)]
    simp [isLeafInc, logLeafReg]
  rcases eq_zero_or_exists_succ (regs.getD 0 0) with hv | ⟨v, hv⟩
  · simp only [hv, ↓reduceIte]
    obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_zero hinv hev0 hv
    have hinv1' : MZfLogInv slot₁ (trimZeros (P ++ [1])) regs := by rwa [trimZeros_append_one]
    obtain ⟨hlen', slot₂, hinv₂, hreach₂⟩ := mSubEval_97 (P ++ [1]) hP1 slot₁ regs hinv1'
    rw [trimZeros_append_one, retStack_append_one] at hreach₂
    rw [retStack_append_one] at hinv₂
    exact ⟨hlen', slot₂, hinv₂, mReachPos_trans hreach₁ hreach₂⟩
  · have hne : regs.getD 0 0 ≠ 0 := by rw [hv]; exact add_one_ne_zero v
    simp only [hne, ↓reduceIte]
    rw [hv, add_one_sub_one_pam]
    obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_succ hinv hev0 hv
    have hev_brk : evalStack (P ++ [0] ++ [1]) = .jump (retStack P) := by
      have h := evalStack_break1_of_walkInternal (P := P ++ [0]) (k := 1) (by decide) hP0 rfl
      simpa [retStack] using h
    obtain ⟨slot₂, hinv₂, hreach₂⟩ := mLogStep_of_jump hinv₁ hev_brk
    exact ⟨by simp [hinv.1], slot₂, hinv₂, mReachPos_trans hreach₁ hreach₂⟩

theorem mSubEval_84 :
    MSubEval (M := M) 84 (fun regs ↦ (regs.set 8 0).set 2 (regs.getD 8 0)) := by
  refine (mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_382 mSubEval_371).congr ?_
  intro regs hlen
  have hget2 : (regs.set 2 0).getD 2 0 = 0 := mGetD_set_self regs 2 0 (by omega)
  have hget8 : (regs.set 2 0).getD 8 0 = regs.getD 8 0 := mGetD_set_ne regs 0 (by decide)
  rw [hget2, hget8, zero_add, mSet_comm_of_ne regs 0 0 (by decide), List.set_set]

noncomputable def mReg83Op (regs : List (PAM M)) : List (PAM M) :=
  if regs.getD 4 0 = 0 then
    regs
  else
    ((regs.set 4 (regs.getD 4 0 - 1)).set 8 0).set 2 (regs.getD 8 0)

theorem mSubEval_83 : MSubEval (M := M) 83 mReg83Op := by
  intro P hP slot regs hinv
  unfold mReg83Op
  have hP1 : walkInternal 99 (P ++ [1]) = some 84 := walkInternal_snoc hP rfl (by decide)
  have hev0 : evalStack (trimZeros P) = .decnz 4 (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP rfl (by decide) (by decide)]
    simp [isLeafInc, logLeafReg]
  rcases eq_zero_or_exists_succ (regs.getD 4 0) with hv | ⟨v, hv⟩
  · simp only [hv, ↓reduceIte]
    exact ⟨hinv.1, mLogStep_of_decnz_zero hinv hev0 hv⟩
  · have hne : regs.getD 4 0 ≠ 0 := by rw [hv]; exact add_one_ne_zero v
    simp only [hne, ↓reduceIte]
    rw [hv, add_one_sub_one_pam]
    obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_succ hinv hev0 hv
    have hinv1' : MZfLogInv slot₁ (trimZeros (P ++ [1])) (regs.set 4 v) := by
      rwa [trimZeros_append_one]
    obtain ⟨hlen', slot₂, hinv₂, hreach₂⟩ := mSubEval_84 (P ++ [1]) hP1 slot₁ (regs.set 4 v) hinv1'
    rw [trimZeros_append_one, retStack_append_one] at hreach₂
    rw [retStack_append_one] at hinv₂
    dsimp only at hlen' hinv₂ hreach₂
    rw [mGetD_set_ne regs v (by decide)] at hlen' hinv₂ hreach₂
    exact ⟨hlen', slot₂, hinv₂, mReachPos_trans hreach₁ hreach₂⟩

noncomputable def mReg308Op (regs : List (PAM M)) : List (PAM M) :=
  (mReg83Op regs).set 8 0

theorem mSubEval_308 : MSubEval (M := M) 308 mReg308Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_83 mSubEval_359

noncomputable def mReg307Op (regs : List (PAM M)) : List (PAM M) :=
  mReg308Op ((regs.set 9 0).set 3 (regs.getD 3 0 + regs.getD 9 0))

theorem mSubEval_307 : MSubEval (M := M) 307 mReg307Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_380 mSubEval_308

noncomputable def mReg306Op (f315 : List (PAM M) → List (PAM M)) (regs : List (PAM M)) :
    List (PAM M) :=
  mReg307Op (f315 regs)

theorem mSubEval_306 {f315 : List (PAM M) → List (PAM M)} (h315 : MSubEval (M := M) 315 f315) :
    MSubEval (M := M) 306 (mReg306Op f315) :=
  mSubEval_seq rfl (by decide) rfl (by decide) h315 mSubEval_307

noncomputable def mRegSelectGenOp (f315 : List (PAM M) → List (PAM M)) (regs : List (PAM M)) :
    List (PAM M) :=
  mReg306Op f315 ((regs.set 2 0).set 8 (regs.getD 8 0 + regs.getD 2 0))

theorem mSubEval_305 {f315 : List (PAM M) → List (PAM M)} (h315 : MSubEval (M := M) 315 f315) :
    MSubEval (M := M) 305 (mRegSelectGenOp f315) :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_386 (mSubEval_306 h315)

theorem mSubEval_76 :
    MSubEval (M := M) 76 (fun regs ↦ regs.set 4 (regs.getD 4 0 + 2)) := by
  refine (mSubEval_inc_inc (M := M) (q₀ := 30) (q₁ := 30)
    rfl (by decide) (by decide) rfl rfl (by decide) (by decide) rfl).congr ?_
  intro regs hlen
  change (regs.set 4 (regs.getD 4 0 + 1)).set 4
    ((regs.set 4 (regs.getD 4 0 + 1)).getD 4 0 + 1) = regs.set 4 (regs.getD 4 0 + 2)
  rw [mGetD_set_self regs 4 _ (by omega), List.set_set]
  congr 1
  ring

theorem mSubEval_78 {f289 : List (PAM M) → List (PAM M)} (h289 : MSubEval (M := M) 289 f289) :
    MSubEval (M := M) 78 (fun regs ↦ f289 (regs.set 4 (regs.getD 4 0 + 1))) :=
  mSubEval_inc_seq (q₀ := 30) (q₁ := 289) rfl (by decide) (by decide) rfl rfl (by decide) h289

theorem mSubEval_71 {f289 : List (PAM M) → List (PAM M)} (h289 : MSubEval (M := M) 289 f289)
    (Q : List (Fin 2)) (hQ : walkInternal 99 Q = some 71)
    (slot : PAM M) (regs : List (PAM M)) (hinv : MZfLogInv slot (trimZeros Q) regs) :
    (if regs.getD 4 0 = 1 then f289 regs else regs).length = 11 ∧
    ∃ slot' : PAM M,
      MZfLogInv slot'
        (if regs.getD 4 0 = 1 then retStack Q else (popBreakRev 1 Q.reverse).reverse)
        (if regs.getD 4 0 = 1 then f289 regs else regs) ∧
      mReachPos (mZfLogCfg slot (trimZeros Q) regs)
        (mZfLogCfg slot'
          (if regs.getD 4 0 = 1 then retStack Q else (popBreakRev 1 Q.reverse).reverse)
          (if regs.getD 4 0 = 1 then f289 regs else regs)) := by
  have hQ0 : walkInternal 99 (Q ++ [0]) = some 72 := walkInternal_snoc hQ rfl (by decide)
  have hQ01 : walkInternal 99 (Q ++ [0] ++ [1]) = some 73 :=
    walkInternal_snoc hQ0 rfl (by decide)
  have hQ010 : walkInternal 99 (Q ++ [0] ++ [1] ++ [0]) = some 74 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ0101 : walkInternal 99 (Q ++ [0] ++ [1] ++ [0] ++ [1]) = some 75 :=
    walkInternal_snoc hQ010 rfl (by decide)
  have hQ01010 : walkInternal 99 (Q ++ [0] ++ [1] ++ [0] ++ [1] ++ [0]) = some 76 :=
    walkInternal_snoc hQ0101 rfl (by decide)
  have hQ011 : walkInternal 99 (Q ++ [0] ++ [1] ++ [1]) = some 77 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ0110 : walkInternal 99 (Q ++ [0] ++ [1] ++ [1] ++ [0]) = some 78 :=
    walkInternal_snoc hQ011 rfl (by decide)
  have hev99 : evalStack (trimZeros Q) = .decnz 4 (Q ++ [0] ++ [1]) (Q ++ [1]) := by
    rw [← trimZeros_append_zero Q, evalStack_trimZeros_of_walkInternal hQ0,
      evalStack_leaf0_of_walkInternal hQ0 rfl (by decide) (by decide)]
    simp [isLeafInc, logLeafReg]
  have hev98_brk : evalStack (Q ++ [1]) = .jump (popBreakRev 1 Q.reverse).reverse :=
    evalStack_break1_of_walkInternal (k := 1) (by decide) hQ rfl
  have hev101 : evalStack (Q ++ [0] ++ [1]) =
      .decnz 4 (Q ++ [0] ++ [1] ++ [0] ++ [1]) (Q ++ [0] ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hQ010 rfl (by decide) (by decide)
    rw [← evalStack_trimZeros_of_walkInternal hQ010, trimZeros_append_zero,
      trimZeros_append_one, retStack_append_zero] at h
    exact h
  rcases eq_zero_or_exists_succ (regs.getD 4 0) with hv | ⟨u, hu⟩
  · have hne1 : (regs.getD 4 0) ≠ 1 := by rw [hv]; exact one_ne_zero_pam.symm
    simp only [hne1, ↓reduceIte]
    obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_zero hinv hev99 hv
    obtain ⟨slot₂, hinv₂, hreach₂⟩ := mLogStep_of_jump hinv₁ hev98_brk
    exact ⟨hinv.1, slot₂, hinv₂, mReachPos_trans hreach₁ hreach₂⟩
  · rcases eq_zero_or_exists_succ u with rfl | ⟨v, rfl⟩
    · have hv1 : regs.getD 4 0 = 1 := by simpa using hu
      simp only [hv1, ↓reduceIte]
      obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_succ hinv hev99 hu
      have hv0 : (regs.set 4 0).getD 4 0 = 0 := mGetD_set_self regs 4 0 (by rw [hinv.1]; decide)
      obtain ⟨slot₂, hinv₂, hreach₂⟩ := mLogStep_of_decnz_zero hinv₁ hev101 hv0
      have hinv105 : MZfLogInv slot₂ (trimZeros (Q ++ [0] ++ [1] ++ [1] ++ [0])) (regs.set 4 0) :=
        by rwa [trimZeros_append_zero, trimZeros_append_one]
      obtain ⟨hlen_105, slot₃, hinv₃, hreach_105⟩ :=
        mSubEval_78 h289 (Q ++ [0] ++ [1] ++ [1] ++ [0]) hQ0110 slot₂ (regs.set 4 0) hinv105
      rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hreach_105
      rw [retStack_append_zero] at hinv₃
      dsimp only [logLeafReg] at hlen_105 hinv₃ hreach_105
      have hrestore : (regs.set 4 0).set 4 ((regs.set 4 0).getD 4 0 + 1) = regs := by
        rw [hv0, zero_add, List.set_set, mSet_eq_self_of_getD_eq hv1]
      rw [hrestore] at hlen_105 hinv₃ hreach_105
      have hev104_brk : evalStack (Q ++ [0] ++ [1] ++ [1] ++ [1]) = .jump (retStack Q) := by
        have h := evalStack_break1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [1])
          (k := 1) (by decide) hQ011 rfl
        simpa [retStack] using h
      obtain ⟨slot₄, hinv₄, hreach₄⟩ := mLogStep_of_jump (regs := f289 regs) hinv₃ hev104_brk
      exact ⟨hlen_105, slot₄, hinv₄,
        mReachPos_trans hreach₁ (mReachPos_trans hreach₂ (mReachPos_trans hreach_105 hreach₄))⟩
    · have hne1 : regs.getD 4 0 ≠ 1 := by rw [hu]; exact add_one_add_one_ne_one_pam v
      simp only [hne1, ↓reduceIte]
      obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_succ hinv hev99 hu
      have hv1 : (regs.set 4 (v + 1)).getD 4 0 = v + 1 :=
        mGetD_set_self regs 4 (v + 1) (by rw [hinv.1]; decide)
      obtain ⟨slot₂, hinv₂, hreach₂⟩ := mLogStep_of_decnz_succ hinv₁ hev101 hv1
      rw [List.set_set] at hinv₂ hreach₂
      have hinv103 :
          MZfLogInv slot₂ (trimZeros (Q ++ [0] ++ [1] ++ [0] ++ [1] ++ [0])) (regs.set 4 v) := by
        rwa [trimZeros_append_zero, trimZeros_append_one]
      obtain ⟨_, slot₃, hinv₃, hreach_103⟩ :=
        mSubEval_76 (Q ++ [0] ++ [1] ++ [0] ++ [1] ++ [0]) hQ01010 slot₂ (regs.set 4 v) hinv103
      rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hreach_103
      rw [retStack_append_zero] at hinv₃
      dsimp only at hinv₃ hreach_103
      have hrestore : (regs.set 4 v).set 4 ((regs.set 4 v).getD 4 0 + 2) = regs := by
        rw [mGetD_set_self regs 4 v (by rw [hinv.1]; decide), List.set_set]
        have hv2 : v + 2 = v + 1 + 1 := by ring
        rw [hv2, mSet_eq_self_of_getD_eq hu]
      rw [hrestore] at hinv₃ hreach_103
      have hev102_brk : evalStack (Q ++ [0] ++ [1] ++ [0] ++ [1] ++ [1]) = .jump (Q ++ [1]) := by
        have h := evalStack_break1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [0] ++ [1])
          (k := 1) (by decide) hQ0101 rfl
        simpa using h
      obtain ⟨slot₄, hinv₄, hreach₄⟩ := mLogStep_of_jump hinv₃ hev102_brk
      obtain ⟨slot₅, hinv₅, hreach₅⟩ := mLogStep_of_jump hinv₄ hev98_brk
      exact ⟨hinv.1, slot₅, hinv₅, mReachPos_trans hreach₁
        (mReachPos_trans hreach₂
          (mReachPos_trans hreach_103 (mReachPos_trans hreach₄ hreach₅)))⟩

theorem mSubEval_80 :
    MSubEval (M := M) 80 (fun regs ↦ (regs.set 8 0).set 6 (regs.getD 8 0)) := by
  refine (mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_352 mSubEval_366).congr ?_
  intro regs hlen
  have hget6 : (regs.set 6 0).getD 6 0 = 0 := mGetD_set_self regs 6 0 (by omega)
  have hget8 : (regs.set 6 0).getD 8 0 = regs.getD 8 0 := mGetD_set_ne regs 0 (by decide)
  rw [hget6, hget8, zero_add, mSet_comm_of_ne regs 0 0 (by decide), List.set_set]

theorem mSubEval_79 {f289 : List (PAM M) → List (PAM M)} (h289 : MSubEval (M := M) 289 f289) :
    MSubEval (M := M) 79 (fun regs ↦
      if regs.getD 4 0 = 1 then
        let r := f289 regs
        (r.set 8 0).set 6 (r.getD 8 0)
      else
        regs) := by
  refine (mSubEval_cond (cond := fun regs ↦ regs.getD 4 0 = 1)
    rfl (by decide) rfl (by decide) (mSubEval_71 h289) mSubEval_80).congr ?_
  intro regs _hlen
  split_ifs <;> rfl

theorem mSubEval_82 :
    MSubEval (M := M) 82 (fun regs ↦ (regs.set 8 0).set 7 (regs.getD 8 0)) := by
  refine (mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_356 mSubEval_368).congr ?_
  intro regs hlen
  have hget7 : (regs.set 7 0).getD 7 0 = 0 := mGetD_set_self regs 7 0 (by omega)
  have hget8 : (regs.set 7 0).getD 8 0 = regs.getD 8 0 := mGetD_set_ne regs 0 (by decide)
  rw [hget7, hget8, zero_add, mSet_comm_of_ne regs 0 0 (by decide), List.set_set]

theorem mSubEval_81 {f289 : List (PAM M) → List (PAM M)} (h289 : MSubEval (M := M) 289 f289) :
    MSubEval (M := M) 81 (fun regs ↦
      if regs.getD 4 0 = 1 then
        let r := f289 regs
        (r.set 8 0).set 7 (r.getD 8 0)
      else
        regs) := by
  refine (mSubEval_cond (cond := fun regs ↦ regs.getD 4 0 = 1)
    rfl (by decide) rfl (by decide) (mSubEval_71 h289) mSubEval_82).congr ?_
  intro regs _hlen
  split_ifs <;> rfl

theorem mSubEval_85 (Q : List (Fin 2)) (hQ : walkInternal 99 Q = some 85)
    (slot : PAM M) (regs : List (PAM M)) (hinv : MZfLogInv slot (trimZeros Q) regs) :
    ((regs.set 9 0).set 10 0).length = 11 ∧
    ∃ slot' : PAM M,
      MZfLogInv slot'
        (if regs.getD 9 0 = regs.getD 10 0 then retStack Q
         else (popBreakRev 1 Q.reverse).reverse)
        ((regs.set 9 0).set 10 0) ∧
      mReachPos (mZfLogCfg slot (trimZeros Q) regs)
        (mZfLogCfg slot'
          (if regs.getD 9 0 = regs.getD 10 0 then retStack Q
           else (popBreakRev 1 Q.reverse).reverse)
          ((regs.set 9 0).set 10 0)) := by
  have hQ0 : walkInternal 99 (Q ++ [0]) = some 86 := walkInternal_snoc hQ rfl (by decide)
  have hQ01 : walkInternal 99 (Q ++ [0] ++ [1]) = some 87 :=
    walkInternal_snoc hQ0 rfl (by decide)
  have hQ010 : walkInternal 99 (Q ++ [0] ++ [1] ++ [0]) = some 88 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ011 : walkInternal 99 (Q ++ [0] ++ [1] ++ [1]) = some 89 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ0110 : walkInternal 99 (Q ++ [0] ++ [1] ++ [1] ++ [0]) = some 376 :=
    walkInternal_snoc hQ011 rfl (by decide)
  have hQ1 : walkInternal 99 (Q ++ [1]) = some 90 := walkInternal_snoc hQ rfl (by decide)
  have hQ11 : walkInternal 99 (Q ++ [1] ++ [1]) = some 91 := walkInternal_snoc hQ1 rfl (by decide)
  have hQ110 : walkInternal 99 (Q ++ [1] ++ [1] ++ [0]) = some 381 :=
    walkInternal_snoc hQ11 rfl (by decide)
  have hev113 : evalStack (trimZeros Q) = .decnz 9 (Q ++ [0] ++ [1]) (Q ++ [1]) := by
    rw [← trimZeros_append_zero Q, evalStack_trimZeros_of_walkInternal hQ0,
      evalStack_leaf0_of_walkInternal hQ0 rfl (by decide) (by decide)]
    simp [isLeafInc, logLeafReg]
  have hev115 : evalStack (Q ++ [0] ++ [1]) =
      .decnz 10 (Q ++ [0] ++ [1] ++ [0] ++ [1]) (Q ++ [0] ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hQ010 rfl (by decide) (by decide)
    rw [← evalStack_trimZeros_of_walkInternal hQ010, trimZeros_append_zero,
      trimZeros_append_one, retStack_append_zero] at h
    exact h
  have hev115_cont : evalStack (Q ++ [0] ++ [1] ++ [0] ++ [1]) = .jump (trimZeros Q) := by
    have h := evalStack_continue1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [0])
      (k := 1) (by decide) hQ010 rfl
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hev116_brk : evalStack (Q ++ [0] ++ [1] ++ [1] ++ [1]) =
      .jump (popBreakRev 1 Q.reverse).reverse := by
    have h := evalStack_break1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [1])
      (k := 2) (by decide) hQ011 rfl
    simpa using h
  have hev117 : evalStack (Q ++ [1]) = .decnz 10 (Q ++ [1] ++ [1]) (retStack Q) := by
    have h := evalStack_leaf0_of_walkInternal hQ1 rfl (by decide) (by decide)
    simpa [isLeafInc, logLeafReg] using h
  have hev118_brk : evalStack (Q ++ [1] ++ [1] ++ [1]) =
      .jump (popBreakRev 1 Q.reverse).reverse := by
    have h := evalStack_break1_of_walkInternal (P := Q ++ [1] ++ [1])
      (k := 1) (by decide) hQ11 rfl
    simpa using h
  let ip_eq := retStack Q
  let ip_ne := (popBreakRev 1 Q.reverse).reverse
  have hdef : PADef1 (fun v : PAM M ↦
      ∀ (sl : PAM M) (rs : List (PAM M)),
        MZfLogInv sl (trimZeros Q) rs → rs.getD 9 0 = v →
        ∃ sl' : PAM M,
          MZfLogInv sl' (if v = rs.getD 10 0 then ip_eq else ip_ne) ((rs.set 9 0).set 10 0) ∧
          mReachPos (mZfLogCfg sl (trimZeros Q) rs)
            (mZfLogCfg sl' (if v = rs.getD 10 0 then ip_eq else ip_ne)
              ((rs.set 9 0).set 10 0))) := by
    let R_clr : (Fin 13 → PAM M) → List (PAM M) :=
      fun w ↦ ((regsOfVec13 w).set 9 0).set 10 0
    have hR_clr : PAFunRegs 13 R_clr :=
      paFunRegs_set (paFunRegs_set paFunRegs_regsOfVec13 9 (paFun_const 0)) 10 (paFun_const 0)
    have hce : PADefN 13 (fun w : Fin 13 → PAM M ↦ w 0 = (regsOfVec13 w).getD 10 0) :=
      paDef_eq (paFun_proj 0) (paFunRegs_getD paFunRegs_regsOfVec13 10)
    have hres13 : PADefN 13 (fun w : Fin 13 → PAM M ↦
        ∃ sl' : PAM M,
          MZfLogInv sl' (if w 0 = (regsOfVec13 w).getD 10 0 then ip_eq else ip_ne) (R_clr w) ∧
          mReachPos (mZfLogCfg (w 1) (trimZeros Q) (regsOfVec13 w))
            (mZfLogCfg sl' (if w 0 = (regsOfVec13 w).getD 10 0 then ip_eq else ip_ne)
              (R_clr w))) := by
      refine paDefN_congr (fun w ↦ ?_)
        (paDef_or
          (paDef_and hce
            (paDef_exists_slot_reachPos (trimZeros Q) ip_eq
              (paFun_proj 1) paFunRegs_regsOfVec13 hR_clr))
          (paDef_and (paDef_not hce)
            (paDef_exists_slot_reachPos (trimZeros Q) ip_ne
              (paFun_proj 1) paFunRegs_regsOfVec13 hR_clr)))
      by_cases hc : w 0 = (regsOfVec13 w).getD 10 0
      · simp only [hc, ↓reduceIte, not_true_eq_false, true_and, false_and, or_false]
      · simp only [hc, ↓reduceIte, not_false_eq_true, true_and, false_and, false_or]
    have hbody13 := paDef_imp
      (paDef_mZfLogInv (trimZeros Q) (paFun_proj 1) paFunRegs_regsOfVec13)
      (paDef_imp (paDef_eq (paFunRegs_getD paFunRegs_regsOfVec13 9) (paFun_proj 0)) hres13)
    refine paDefN_congr (fun a ↦ ?_) (paDef_forall_vec (k := 1) (m := 12) hbody13)
    have ha0 : ∀ b : Fin 12 → PAM M, finCat a b 0 = a 0 := fun b ↦ finCat_left a b 0
    have hb0 : ∀ b : Fin 12 → PAM M, finCat a b 1 = b 0 := fun b ↦ finCat_right a b 0
    constructor
    · intro hvec sl rs hinv_rs hv
      let b : Fin 12 → PAM M := Fin.cons sl (fun i : Fin 11 ↦ rs.getD i.val 0)
      have hb_sl : b 0 = sl := rfl
      have hb_rs : List.ofFn (fun i : Fin 11 ↦ b i.succ) = rs := ofFn_getD_eq_self hinv_rs.1
      have hinst := hvec b
      dsimp only [R_clr] at hinst
      rw [ha0 b, hb0 b, regsOfVec13_finCat a b, hb_sl, hb_rs] at hinst
      exact hinst hinv_rs hv
    · intro hall b
      dsimp only [R_clr]
      rw [ha0 b, hb0 b, regsOfVec13_finCat a b]
      exact hall (b 0) (List.ofFn (fun i : Fin 11 ↦ b i.succ))
  have hloop := ind1 hdef
    (fun sl rs hinv_rs hv ↦ by
      obtain ⟨sl₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_zero hinv_rs hev113 hv
      rcases eq_zero_or_exists_succ (rs.getD 10 0) with hw | ⟨w, hw⟩
      · simp only [hw, ↓reduceIte]
        obtain ⟨sl₂, hinv₂, hreach₂⟩ := mLogStep_of_decnz_zero hinv₁ hev117 hw
        have hset : (rs.set 9 0).set 10 0 = rs := by
          rw [mSet_eq_self_of_getD_eq hv, mSet_eq_self_of_getD_eq hw]
        rw [hset]
        exact ⟨sl₂, hinv₂, mReachPos_trans hreach₁ hreach₂⟩
      · have hne : (0 : PAM M) ≠ w + 1 := (add_one_ne_zero w).symm
        simp only [hw, hne, ↓reduceIte]
        obtain ⟨sl₂, hinv₂, hreach₂⟩ := mLogStep_of_decnz_succ hinv₁ hev117 hw
        have hinv420 : MZfLogInv sl₂ (trimZeros (Q ++ [1] ++ [1] ++ [0])) (rs.set 10 w) := by
          rwa [trimZeros_append_zero, trimZeros_append_one]
        obtain ⟨_, sl₃, hinv₃, hreach_420⟩ :=
          mSubEval_381 (Q ++ [1] ++ [1] ++ [0]) hQ110 sl₂ (rs.set 10 w) hinv420
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hreach_420
        rw [retStack_append_zero] at hinv₃
        dsimp only at hinv₃ hreach_420
        rw [List.set_set] at hinv₃ hreach_420
        obtain ⟨sl₄, hinv₄, hreach₄⟩ := mLogStep_of_jump (regs := rs.set 10 0) hinv₃ hev118_brk
        rw [mSet_eq_self_of_getD_eq hv]
        exact ⟨sl₄, hinv₄,
          mReachPos_trans hreach₁ (mReachPos_trans hreach₂ (mReachPos_trans hreach_420 hreach₄))⟩)
    (fun v ih sl rs hinv_rs hv ↦ by
      obtain ⟨sl₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_succ hinv_rs hev113 hv
      rcases eq_zero_or_exists_succ (rs.getD 10 0) with hw | ⟨w, hw⟩
      · have hne : v + 1 ≠ (0 : PAM M) := add_one_ne_zero v
        simp only [hw, hne, ↓reduceIte]
        have hw' : (rs.set 9 v).getD 10 0 = 0 := by rw [mGetD_set_ne _ _ (by decide), hw]
        obtain ⟨sl₂, hinv₂, hreach₂⟩ := mLogStep_of_decnz_zero hinv₁ hev115 hw'
        have hinv415 :
            MZfLogInv sl₂ (trimZeros (Q ++ [0] ++ [1] ++ [1] ++ [0])) (rs.set 9 v) := by
          rwa [trimZeros_append_zero, trimZeros_append_one]
        obtain ⟨_, sl₃, hinv₃, hreach_415⟩ :=
          mSubEval_376 (Q ++ [0] ++ [1] ++ [1] ++ [0]) hQ0110 sl₂ (rs.set 9 v) hinv415
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hreach_415
        rw [retStack_append_zero] at hinv₃
        dsimp only at hinv₃ hreach_415
        rw [List.set_set] at hinv₃ hreach_415
        obtain ⟨sl₄, hinv₄, hreach₄⟩ := mLogStep_of_jump (regs := rs.set 9 0) hinv₃ hev116_brk
        have hset10 : (rs.set 9 0).set 10 0 = rs.set 9 0 :=
          mSet_eq_self_of_getD_eq (by rw [mGetD_set_ne _ _ (by decide), hw])
        rw [hset10]
        exact ⟨sl₄, hinv₄,
          mReachPos_trans hreach₁ (mReachPos_trans hreach₂ (mReachPos_trans hreach_415 hreach₄))⟩
      · have hw' : (rs.set 9 v).getD 10 0 = w + 1 := by rw [mGetD_set_ne _ _ (by decide), hw]
        obtain ⟨sl₂, hinv₂, hreach₂⟩ := mLogStep_of_decnz_succ hinv₁ hev115 hw'
        let rs₁ := (rs.set 9 v).set 10 w
        obtain ⟨sl₃, hinv₃, hreach₃⟩ := mLogStep_of_jump (regs := rs₁) hinv₂ hev115_cont
        have hv₁ : rs₁.getD 9 0 = v := by
          dsimp only [rs₁]
          rw [mGetD_set_ne _ _ (by decide), mGetD_set_self rs 9 v (by rw [hinv_rs.1]; decide)]
        have hw₁ : rs₁.getD 10 0 = w := by
          dsimp only [rs₁]
          exact mGetD_set_self (rs.set 9 v) 10 w (by simp [hinv_rs.1])
        obtain ⟨sl₄, hinv₄, hreach_ih⟩ := ih sl₃ rs₁ hinv₃ hv₁
        have hset_eq : (rs₁.set 9 0).set 10 0 = (rs.set 9 0).set 10 0 := by
          dsimp only [rs₁]
          rw [mSet_comm_of_ne (rs.set 9 v) w 0 (by decide), List.set_set, List.set_set]
        have heq_iff : (v = w) ↔ (v + 1 = w + 1) :=
          ⟨congrArg (· + 1), (add_right_inj_pam 1).mp⟩
        rw [hw₁, hset_eq] at hinv₄ hreach_ih
        have hcond_eq : (if v = w then ip_eq else ip_ne) =
            (if v + 1 = rs.getD 10 0 then ip_eq else ip_ne) := by
          rw [hw]
          simp only [heq_iff]
        rw [hcond_eq] at hinv₄ hreach_ih
        exact ⟨sl₄, hinv₄,
          mReachPos_trans hreach₁ (mReachPos_trans hreach₂ (mReachPos_trans hreach₃ hreach_ih))⟩)
  exact ⟨by simp [hinv.1], hloop (regs.getD 9 0) slot regs hinv rfl⟩

def mReg94Op (regs : List (PAM M)) : List (PAM M) :=
  let r := ((regs.set 5 0).set 8 (regs.getD 8 0 + regs.getD 5 0)).set 2
    (regs.getD 2 0 + regs.getD 5 0)
  (r.set 8 0).set 5 (r.getD 5 0 + r.getD 8 0)

theorem mSubEval_94 : MSubEval (M := M) 94 mReg94Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_348 mSubEval_364

noncomputable def mReg93Op (regs : List (PAM M)) : List (PAM M) :=
  if regs.getD 9 0 = regs.getD 10 0 then
    mReg94Op ((regs.set 9 0).set 10 0)
  else
    (regs.set 9 0).set 10 0

theorem mSubEval_93 : MSubEval (M := M) 93 mReg93Op :=
  mSubEval_cond (cond := fun regs ↦ regs.getD 9 0 = regs.getD 10 0)
    rfl (by decide) rfl (by decide) mSubEval_85 mSubEval_94

noncomputable def mReg92Op (regs : List (PAM M)) : List (PAM M) :=
  if regs.getD 9 0 = regs.getD 10 0 then
    ((regs.set 9 0).set 10 0).set 2 0
  else
    (regs.set 9 0).set 10 0

theorem mSubEval_92 : MSubEval (M := M) 92 mReg92Op :=
  mSubEval_cond (cond := fun regs ↦ regs.getD 9 0 = regs.getD 10 0)
    rfl (by decide) rfl (by decide) mSubEval_85 mSubEval_382

noncomputable def mReg256Op (regs : List (PAM M)) : List (PAM M) :=
  mReg92Op ((regs.set 8 0).set 7 (regs.getD 7 0 + regs.getD 8 0))

theorem mSubEval_256 : MSubEval (M := M) 256 mReg256Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_368 mSubEval_92

noncomputable def mReg255Op (regs : List (PAM M)) : List (PAM M) :=
  mReg256Op (((regs.set 7 0).set 8 (regs.getD 8 0 + regs.getD 7 0)).set 10
    (regs.getD 10 0 + regs.getD 7 0))

theorem mSubEval_255 : MSubEval (M := M) 255 mReg255Op :=
  mSubEval_seq rfl (by decide) rfl (by decide) mSubEval_358 mSubEval_256

noncomputable def mRegSelectOp (regs : List (PAM M)) : List (PAM M) :=
  mRegSelectGenOp (mRegUnpairGen 2 9 3) regs

theorem mSubEval_305_inst : MSubEval (M := M) 305 mRegSelectOp :=
  mSubEval_305 mSubEval_315

noncomputable def mRegCparam2Op (regs : List (PAM M)) : List (PAM M) :=
  if regs.getD 4 0 = 1 then
    let r := mReg289Op regs
    (r.set 8 0).set 6 (r.getD 8 0)
  else
    regs

theorem mSubEval_79_inst : MSubEval (M := M) 79 mRegCparam2Op :=
  mSubEval_79 mSubEval_289

noncomputable def mRegCparam3Op (regs : List (PAM M)) : List (PAM M) :=
  if regs.getD 4 0 = 1 then
    let r := mReg289Op regs
    (r.set 8 0).set 7 (r.getD 8 0)
  else
    regs

theorem mSubEval_81_inst : MSubEval (M := M) 81 mRegCparam3Op :=
  mSubEval_81 mSubEval_289


/-! ## Section 5: `MWffState`, RPN Clauses, and Spine Segment `k = 13..123` -/

@[simp]
theorem one_ne_zero_pam_simp : (1 : PAM M) ≠ 0 := one_ne_zero_pam

@[simp]
theorem zero_ne_one_pam_simp : (0 : PAM M) ≠ 1 := one_ne_zero_pam.symm

@[simp]
theorem add_one_ne_zero_pam (x : PAM M) : x + 1 ≠ 0 := add_one_ne_zero x

@[simp]
theorem one_sub_one_pam : (1 : PAM M) - 1 = 0 := by
  simp

@[simp]
theorem one_add_one_ne_one_pam : (1 : PAM M) + 1 ≠ 1 := by
  simpa using add_one_add_one_ne_one_pam (0 : PAM M)

/-- The 6 active RPN formula-stack and parameter registers on `PAM M`. -/
structure MWffState (M : Type*) [PAStructure M] where
  topwff : PAM M
  wffstack : PAM M
  axiomcode : PAM M
  param1 : PAM M
  param2 : PAM M
  param3 : PAM M

/-- Canonical 11-register bank for a given `MWffState M` (with scratch registers `8..10 = 0`). -/
def mWffStateToRegs (pl np : PAM M) (s : MWffState M) : List (PAM M) :=
  [pl, np, s.topwff, s.wffstack, s.axiomcode, s.param1, s.param2, s.param3, 0, 0, 0]

noncomputable def mRpnVk (k : PAM M) (s : MWffState M) : MWffState M :=
  { s with topwff := k, wffstack := mPair s.topwff s.wffstack }

noncomputable def mRpnCons (s : MWffState M) : MWffState M :=
  let p := mUnpair s.wffstack
  { s with topwff := mPair p.1 s.topwff, wffstack := p.2 }

noncomputable def mRpnWeq (s : MWffState M) : MWffState M := mRpnCons (mRpnVk 0 (mRpnCons s))
noncomputable def mRpnWel (s : MWffState M) : MWffState M := mRpnCons (mRpnVk 1 (mRpnCons s))
noncomputable def mRpnWim (s : MWffState M) : MWffState M := mRpnCons (mRpnVk 2 (mRpnCons s))
noncomputable def mRpnWn (s : MWffState M) : MWffState M := mRpnCons (mRpnVk 3 s)
noncomputable def mRpnWal (s : MWffState M) : MWffState M := mRpnCons (mRpnVk 4 (mRpnCons s))
noncomputable def mRpnWex (s : MWffState M) : MWffState M := mRpnWn (mRpnWal (mRpnWn s))
noncomputable def mRpnWa (s : MWffState M) : MWffState M := mRpnWn (mRpnWim (mRpnWn s))

noncomputable def mRpnPar1 (s : MWffState M) : MWffState M :=
  { s with topwff := s.param1, wffstack := mPair s.topwff s.wffstack }

noncomputable def mRpnPar2 (s : MWffState M) : MWffState M :=
  { s with topwff := s.param2, wffstack := mPair s.topwff s.wffstack }

noncomputable def mRpnPar3 (s : MWffState M) : MWffState M :=
  { s with topwff := s.param3, wffstack := mPair s.topwff s.wffstack }

noncomputable def mRpnSelect (s : MWffState M) : MWffState M :=
  let p := mUnpair s.wffstack
  if s.axiomcode = 0 then
    { s with topwff := p.1, wffstack := p.2 }
  else
    { s with topwff := s.topwff, wffstack := p.2, axiomcode := s.axiomcode - 1 }

noncomputable def mRpnCparam2 (s : MWffState M) : MWffState M :=
  if s.axiomcode = 1 then
    let p := mUnpair s.wffstack
    { s with wffstack := p.2, param2 := p.1 }
  else s

noncomputable def mRpnCparam3 (s : MWffState M) : MWffState M :=
  if s.axiomcode = 1 then
    let p := mUnpair s.wffstack
    { s with wffstack := p.2, param3 := p.1 }
  else s

noncomputable def mRpnDetCheck (s : MWffState M) : MWffState M :=
  { s with topwff := if s.topwff = s.param2 then s.param1 else 0 }

noncomputable def mRpnZf393B6aCheck1 (s : MWffState M) : MWffState M :=
  { s with topwff := if s.param1 = s.param3 then 0 else s.topwff }

noncomputable def mRpnZf393B6aCheck2 (s : MWffState M) : MWffState M :=
  { s with topwff := if s.param2 = s.param3 then 0 else s.topwff }

theorem mRegPushwffOp_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegPushwffOp (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnVk 0 s) := by
  simp [mWffStateToRegs, mRegPushwffOp, mRegPairOp, mRpnVk, List.getD]

theorem mRegV1Op_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegV1Op (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnVk 1 s) := by
  rw [mRegV1Op, mRegPushwffOp_wffStateToRegs]
  simp [mWffStateToRegs, mRpnVk, List.getD]

theorem mRegV2Op_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegV2Op (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnVk 2 s) := by
  rw [mRegV2Op, mRegV1Op_wffStateToRegs]
  simp only [mWffStateToRegs, mRpnVk, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.set_cons_zero, List.set_cons_succ]
  congr 3
  ring

theorem mRegV3Op_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegV3Op (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnVk 3 s) := by
  rw [mRegV3Op, mRegV2Op_wffStateToRegs]
  simp only [mWffStateToRegs, mRpnVk, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.set_cons_zero, List.set_cons_succ]
  congr 3

theorem mRegV4Op_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegV4Op (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnVk 4 s) := by
  rw [mRegV4Op, mRegV3Op_wffStateToRegs]
  simp only [mWffStateToRegs, mRpnVk, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.set_cons_zero, List.set_cons_succ]
  congr 3

theorem mRegConsOp_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegConsOp (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnCons s) := by
  simp [mWffStateToRegs, mRegConsOp, mReg70Op, mReg289Op, mRegUnpairGen, mRegPairOp,
    mRpnCons, List.getD]

theorem mRegWeqOp_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegWeqOp (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnWeq s) := by
  rw [mRegWeqOp, mReg330Op, mRegConsOp_wffStateToRegs, mRegPushwffOp_wffStateToRegs,
    mRegConsOp_wffStateToRegs]
  rfl

theorem mRegWelOp_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegWelOp (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnWel s) := by
  rw [mRegWelOp, mReg328Op, mRegConsOp_wffStateToRegs, mRegV1Op_wffStateToRegs,
    mRegConsOp_wffStateToRegs]
  rfl

theorem mRegWimOp_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegWimOp (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnWim s) := by
  rw [mRegWimOp, mReg391Op, mRegConsOp_wffStateToRegs, mRegV2Op_wffStateToRegs,
    mRegConsOp_wffStateToRegs]
  rfl

theorem mRegWnOp_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegWnOp (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnWn s) := by
  rw [mRegWnOp, mRegV3Op_wffStateToRegs, mRegConsOp_wffStateToRegs]
  rfl

theorem mRegWalOp_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegWalOp (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnWal s) := by
  rw [mRegWalOp, mReg326Op, mRegConsOp_wffStateToRegs, mRegV4Op_wffStateToRegs,
    mRegConsOp_wffStateToRegs]
  rfl

theorem mRegWexOp_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegWexOp (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnWex s) := by
  rw [mRegWexOp, mReg332Op, mRegWnOp_wffStateToRegs, mRegWalOp_wffStateToRegs,
    mRegWnOp_wffStateToRegs]
  rfl

theorem mRegWaOp_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegWaOp (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnWa s) := by
  rw [mRegWaOp, mReg324Op, mRegWnOp_wffStateToRegs, mRegWimOp_wffStateToRegs,
    mRegWnOp_wffStateToRegs]
  rfl

theorem mRegPar1Op_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegPar1Op (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnPar1 s) := by
  rw [mRegPar1Op, mRegPushwffOp_wffStateToRegs]
  simp [mWffStateToRegs, mReg299Op, mRpnVk, mRpnPar1, List.getD]

theorem mRegPar2Op_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegPar2Op (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnPar2 s) := by
  rw [mRegPar2Op, mRegPushwffOp_wffStateToRegs]
  simp [mWffStateToRegs, mReg301Op, mRpnVk, mRpnPar2, List.getD]

theorem mRegPar3Op_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegPar3Op (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnPar3 s) := by
  rw [mRegPar3Op, mRegPushwffOp_wffStateToRegs]
  simp [mWffStateToRegs, mReg303Op, mRpnVk, mRpnPar3, List.getD]

theorem mRegSelectOp_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegSelectOp (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnSelect s) := by
  by_cases hac : s.axiomcode = 0 <;>
    simp [mWffStateToRegs, mRegSelectOp, mRegSelectGenOp, mReg306Op, mReg307Op, mReg308Op,
      mReg83Op, mRegUnpairGen, mRpnSelect, hac, List.getD]

theorem mRegCparam2Op_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegCparam2Op (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnCparam2 s) := by
  by_cases hac : s.axiomcode = 1 <;>
    simp [mWffStateToRegs, mRegCparam2Op, mReg289Op, mRegUnpairGen, mRpnCparam2, hac, List.getD]

theorem mRegCparam3Op_wffStateToRegs (pl np : PAM M) (s : MWffState M) :
    mRegCparam3Op (mWffStateToRegs pl np s) = mWffStateToRegs pl np (mRpnCparam3 s) := by
  by_cases hac : s.axiomcode = 1 <;>
    simp [mWffStateToRegs, mRegCparam3Op, mReg289Op, mRegUnpairGen, mRpnCparam3, hac, List.getD]

/-- Register-level spine segment evaluation on `PAM M`. -/
def MRegSpineEval (k₁ k₂ : ℕ) (f : List (PAM M) → List (PAM M)) : Prop :=
  ∀ (slot : PAM M) (regs : List (PAM M)),
    MZfLogInv slot (List.replicate k₁ 1) regs →
    (f regs).length = 11 ∧
    ∃ slot' : PAM M,
      MZfLogInv slot' (List.replicate k₂ 1) (f regs) ∧
      mReachPos (mZfLogCfg slot (List.replicate k₁ 1) regs)
        (mZfLogCfg slot' (List.replicate k₂ 1) (f regs))

theorem mRegSpineEval_step {k k' : ℕ} {q_k q_sub : Fin 393}
    {f : List (PAM M) → List (PAM M)}
    (hwalk : walkInternal 99 (List.replicate k 1) = some q_k)
    (htr0 : zf393Trans q_k 0 = some (0, .right, q_sub))
    (hq_sub : 69 ≤ q_sub.val)
    (hsub : MSubEval (M := M) q_sub f)
    (hk : k + 1 = k' := by rfl) :
    MRegSpineEval (M := M) k k' f := by
  subst hk
  intro slot regs hinv
  have hwalk0 : walkInternal 99 (List.replicate k 1 ++ [0]) = some q_sub :=
    walkInternal_snoc hwalk htr0 hq_sub
  have hinv0 : MZfLogInv slot (trimZeros (List.replicate k 1 ++ [0])) regs := by
    rwa [trimZeros_append_zero, trimZeros_replicate_one]
  obtain ⟨hlen, slot', hinv', hreach⟩ := hsub (List.replicate k 1 ++ [0]) hwalk0 slot regs hinv0
  rw [trimZeros_append_zero, trimZeros_replicate_one, retStack_append_zero,
    ← List.replicate_succ'] at hreach
  rw [retStack_append_zero, ← List.replicate_succ'] at hinv'
  exact ⟨hlen, slot', hinv', hreach⟩

theorem mRegSpineEval_trans {k₁ k₂ k₃ : ℕ} {f₁ f₂ f : List (PAM M) → List (PAM M)}
    (h1 : MRegSpineEval (M := M) k₁ k₂ f₁) (h2 : MRegSpineEval (M := M) k₂ k₃ f₂)
    (heq : (fun regs ↦ f₂ (f₁ regs)) = f := by rfl) :
    MRegSpineEval (M := M) k₁ k₃ f := by
  subst heq
  intro slot regs hinv
  obtain ⟨_, slot₁, hinv₁, hreach₁⟩ := h1 slot regs hinv
  obtain ⟨hlen₂, slot₂, hinv₂, hreach₂⟩ := h2 slot₁ (f₁ regs) hinv₁
  exact ⟨hlen₂, slot₂, hinv₂, mReachPos_trans hreach₁ hreach₂⟩

/-- `MWffState`-level subroutine evaluation at node `q` on `PAM M`. -/
def MWffSubEval (q : Fin 393) (op : MWffState M → MWffState M) : Prop :=
  ∀ (P : List (Fin 2)),
    walkInternal 99 P = some q →
    ∀ (slot pl np : PAM M) (s : MWffState M),
      MZfLogInv slot (trimZeros P) (mWffStateToRegs pl np s) →
      ∃ slot' : PAM M,
        MZfLogInv slot' (retStack P) (mWffStateToRegs pl np (op s)) ∧
        mReachPos (mZfLogCfg slot (trimZeros P) (mWffStateToRegs pl np s))
          (mZfLogCfg slot' (retStack P) (mWffStateToRegs pl np (op s)))

theorem mWffSubEval_of_mSubEval {q : Fin 393} {f : List (PAM M) → List (PAM M)}
    {op : MWffState M → MWffState M} (hsub : MSubEval (M := M) q f)
    (heq : ∀ pl np s, f (mWffStateToRegs pl np s) = mWffStateToRegs pl np (op s)) :
    MWffSubEval (M := M) q op := by
  intro P hP slot pl np s hinv
  obtain ⟨_, slot', hinv', hreach⟩ := hsub P hP slot (mWffStateToRegs pl np s) hinv
  rw [heq pl np s] at hinv' hreach
  exact ⟨slot', hinv', hreach⟩

theorem mWffSubEval_seq {q q0 q1 : Fin 393} {op0 op1 op : MWffState M → MWffState M}
    (htr0 : zf393Trans q 0 = some (0, .right, q0)) (hq0 : 69 ≤ q0.val)
    (htr1 : zf393Trans q 1 = some (1, .right, q1)) (hq1 : 69 ≤ q1.val)
    (h0 : MWffSubEval (M := M) q0 op0) (h1 : MWffSubEval (M := M) q1 op1)
    (heq : (fun s ↦ op1 (op0 s)) = op := by rfl) :
    MWffSubEval (M := M) q op := by
  subst heq
  intro P hP slot pl np s hinv
  have hP0 : walkInternal 99 (P ++ [0]) = some q0 := walkInternal_snoc hP htr0 hq0
  have hP1 : walkInternal 99 (P ++ [1]) = some q1 := walkInternal_snoc hP htr1 hq1
  have hinv0 : MZfLogInv slot (trimZeros (P ++ [0])) (mWffStateToRegs pl np s) := by
    rwa [trimZeros_append_zero]
  obtain ⟨slot₀, hinv₀, hreach₀⟩ := h0 (P ++ [0]) hP0 slot pl np s hinv0
  rw [trimZeros_append_zero, retStack_append_zero] at hreach₀
  rw [retStack_append_zero] at hinv₀
  have hinv1 : MZfLogInv slot₀ (trimZeros (P ++ [1])) (mWffStateToRegs pl np (op0 s)) := by
    rwa [trimZeros_append_one]
  obtain ⟨slot₁, hinv₁, hreach₁⟩ := h1 (P ++ [1]) hP1 slot₀ pl np (op0 s) hinv1
  rw [trimZeros_append_one, retStack_append_one] at hreach₁
  rw [retStack_append_one] at hinv₁
  exact ⟨slot₁, hinv₁, mReachPos_trans hreach₀ hreach₁⟩

theorem mWffSubEval_79 : MWffSubEval (M := M) 79 mRpnCparam2 :=
  mWffSubEval_of_mSubEval mSubEval_79_inst mRegCparam2Op_wffStateToRegs
theorem mWffSubEval_81 : MWffSubEval (M := M) 81 mRpnCparam3 :=
  mWffSubEval_of_mSubEval mSubEval_81_inst mRegCparam3Op_wffStateToRegs
theorem mWffSubEval_298 : MWffSubEval (M := M) 298 mRpnPar1 :=
  mWffSubEval_of_mSubEval mSubEval_298 mRegPar1Op_wffStateToRegs
theorem mWffSubEval_300 : MWffSubEval (M := M) 300 mRpnPar2 :=
  mWffSubEval_of_mSubEval mSubEval_300 mRegPar2Op_wffStateToRegs
theorem mWffSubEval_302 : MWffSubEval (M := M) 302 mRpnPar3 :=
  mWffSubEval_of_mSubEval mSubEval_302 mRegPar3Op_wffStateToRegs
theorem mWffSubEval_304 : MWffSubEval (M := M) 304 (mRpnVk 0) :=
  mWffSubEval_of_mSubEval mSubEval_304 mRegPushwffOp_wffStateToRegs
theorem mWffSubEval_305 : MWffSubEval (M := M) 305 mRpnSelect :=
  mWffSubEval_of_mSubEval mSubEval_305_inst mRegSelectOp_wffStateToRegs
theorem mWffSubEval_319 : MWffSubEval (M := M) 319 (mRpnVk 1) :=
  mWffSubEval_of_mSubEval mSubEval_319 mRegV1Op_wffStateToRegs
theorem mWffSubEval_320 : MWffSubEval (M := M) 320 (mRpnVk 2) :=
  mWffSubEval_of_mSubEval mSubEval_320 mRegV2Op_wffStateToRegs
theorem mWffSubEval_321 : MWffSubEval (M := M) 321 (mRpnVk 3) :=
  mWffSubEval_of_mSubEval mSubEval_321 mRegV3Op_wffStateToRegs
theorem mWffSubEval_323 : MWffSubEval (M := M) 323 mRpnWa :=
  mWffSubEval_of_mSubEval mSubEval_323 mRegWaOp_wffStateToRegs
theorem mWffSubEval_325 : MWffSubEval (M := M) 325 mRpnWal :=
  mWffSubEval_of_mSubEval mSubEval_325 mRegWalOp_wffStateToRegs
theorem mWffSubEval_327 : MWffSubEval (M := M) 327 mRpnWel :=
  mWffSubEval_of_mSubEval mSubEval_327 mRegWelOp_wffStateToRegs
theorem mWffSubEval_329 : MWffSubEval (M := M) 329 mRpnWeq :=
  mWffSubEval_of_mSubEval mSubEval_329 mRegWeqOp_wffStateToRegs
theorem mWffSubEval_331 : MWffSubEval (M := M) 331 mRpnWex :=
  mWffSubEval_of_mSubEval mSubEval_331 mRegWexOp_wffStateToRegs
theorem mWffSubEval_390 : MWffSubEval (M := M) 390 mRpnWim :=
  mWffSubEval_of_mSubEval mSubEval_390 mRegWimOp_wffStateToRegs
theorem mWffSubEval_392 : MWffSubEval (M := M) 392 mRpnWn :=
  mWffSubEval_of_mSubEval mSubEval_392 mRegWnOp_wffStateToRegs

noncomputable abbrev mWffOp_277 (s : MWffState M) : MWffState M := (mRpnVk 2) ((mRpnVk 1) s)
theorem mWffSubEval_277 : MWffSubEval (M := M) 277 mWffOp_277 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_319 mWffSubEval_320
noncomputable abbrev mWffOp_266 (s : MWffState M) : MWffState M := mRpnWal (mRpnPar1 s)
theorem mWffSubEval_266 : MWffSubEval (M := M) 266 mWffOp_266 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_298 mWffSubEval_325
noncomputable abbrev mWffOp_265 (s : MWffState M) : MWffState M := mWffOp_266 ((mRpnVk 1) s)
theorem mWffSubEval_265 : MWffSubEval (M := M) 265 mWffOp_265 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_319 mWffSubEval_266
noncomputable abbrev mWffOp_258 (s : MWffState M) : MWffState M := mRpnWim (mRpnWeq s)
theorem mWffSubEval_258 : MWffSubEval (M := M) 258 mWffOp_258 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_329 mWffSubEval_390
noncomputable abbrev mWffOp_257 (s : MWffState M) : MWffState M := mWffOp_258 ((mRpnVk 1) s)
theorem mWffSubEval_257 : MWffSubEval (M := M) 257 mWffOp_257 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_319 mWffSubEval_258
noncomputable abbrev mWffOp_270 (s : MWffState M) : MWffState M := mRpnWex (mRpnWal s)
theorem mWffSubEval_270 : MWffSubEval (M := M) 270 mWffOp_270 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_325 mWffSubEval_331
noncomputable abbrev mWffOp_280 (s : MWffState M) : MWffState M := mRpnWel ((mRpnVk 1) s)
theorem mWffSubEval_280 : MWffSubEval (M := M) 280 mWffOp_280 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_319 mWffSubEval_327
noncomputable abbrev mWffOp_263 (s : MWffState M) : MWffState M := mWffOp_280 ((mRpnVk 2) s)
theorem mWffSubEval_263 : MWffSubEval (M := M) 263 mWffOp_263 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_320 mWffSubEval_280
noncomputable abbrev mWffOp_249 (s : MWffState M) : MWffState M := mWffOp_263 ((mRpnVk 2) s)
theorem mWffSubEval_249 : MWffSubEval (M := M) 249 mWffOp_249 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_320 mWffSubEval_263
noncomputable abbrev mWffOp_287 (s : MWffState M) : MWffState M := mRpnWel ((mRpnVk 0) s)
theorem mWffSubEval_287 : MWffSubEval (M := M) 287 mWffOp_287 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_304 mWffSubEval_327
noncomputable abbrev mWffOp_264 (s : MWffState M) : MWffState M := mWffOp_287 ((mRpnVk 3) s)
theorem mWffSubEval_264 : MWffSubEval (M := M) 264 mWffOp_264 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_321 mWffSubEval_287
noncomputable abbrev mWffOp_278 (s : MWffState M) : MWffState M := mRpnWex (mRpnWa s)
theorem mWffSubEval_278 : MWffSubEval (M := M) 278 mWffOp_278 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_323 mWffSubEval_331
noncomputable abbrev mWffOp_240 (s : MWffState M) : MWffState M := mWffOp_278 (mWffOp_265 s)
theorem mWffSubEval_240 : MWffSubEval (M := M) 240 mWffOp_240 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_265 mWffSubEval_278
noncomputable abbrev mWffOp_239 (s : MWffState M) : MWffState M := mWffOp_240 (mWffOp_264 s)
theorem mWffSubEval_239 : MWffSubEval (M := M) 239 mWffOp_239 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_264 mWffSubEval_240
noncomputable abbrev mWffOp_238 (s : MWffState M) : MWffState M := mWffOp_239 ((mRpnVk 3) s)
theorem mWffSubEval_238 : MWffSubEval (M := M) 238 mWffOp_238 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_321 mWffSubEval_239
noncomputable abbrev mWffOp_248 (s : MWffState M) : MWffState M := mRpnWim (mWffOp_263 s)
theorem mWffSubEval_248 : MWffSubEval (M := M) 248 mWffOp_248 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_263 mWffSubEval_390
noncomputable abbrev mWffOp_281 (s : MWffState M) : MWffState M := mRpnSelect (mRpnWim s)
theorem mWffSubEval_281 : MWffSubEval (M := M) 281 mWffOp_281 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_390 mWffSubEval_305
noncomputable abbrev mWffOp_267 (s : MWffState M) : MWffState M := (mRpnVk 1) (mWffOp_281 s)
theorem mWffSubEval_267 : MWffSubEval (M := M) 267 mWffOp_267 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_281 mWffSubEval_319
noncomputable abbrev mWffOp_285 (s : MWffState M) : MWffState M := (mRpnVk 3) ((mRpnVk 2) s)
theorem mWffSubEval_285 : MWffSubEval (M := M) 285 mWffOp_285 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_320 mWffSubEval_321
noncomputable abbrev mWffOp_245 (s : MWffState M) : MWffState M := mWffOp_285 (mWffOp_267 s)
theorem mWffSubEval_245 : MWffSubEval (M := M) 245 mWffOp_245 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_267 mWffSubEval_285
noncomputable abbrev mWffOp_247 (s : MWffState M) : MWffState M := mWffOp_264 (mRpnWel s)
theorem mWffSubEval_247 : MWffSubEval (M := M) 247 mWffOp_247 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_327 mWffSubEval_264
noncomputable abbrev mWffOp_272 (s : MWffState M) : MWffState M := mRpnWal (mRpnWim s)
theorem mWffSubEval_272 : MWffSubEval (M := M) 272 mWffOp_272 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_390 mWffSubEval_325
noncomputable abbrev mWffOp_283 (s : MWffState M) : MWffState M := mRpnPar1 (mRpnSelect s)
theorem mWffSubEval_283 : MWffSubEval (M := M) 283 mWffOp_283 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_305 mWffSubEval_298
noncomputable abbrev mWffOp_242 (s : MWffState M) : MWffState M := mWffOp_283 (mWffOp_270 s)
theorem mWffSubEval_242 : MWffSubEval (M := M) 242 mWffOp_242 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_270 mWffSubEval_283
noncomputable abbrev mWffOp_241 (s : MWffState M) : MWffState M := mWffOp_242 (mWffOp_248 s)
theorem mWffSubEval_241 : MWffSubEval (M := M) 241 mWffOp_241 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_248 mWffSubEval_242
noncomputable abbrev mWffOp_274 (s : MWffState M) : MWffState M := mRpnPar1 (mRpnWim s)
theorem mWffSubEval_274 : MWffSubEval (M := M) 274 mWffOp_274 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_390 mWffSubEval_298
noncomputable abbrev mWffOp_268 (s : MWffState M) : MWffState M := mWffOp_281 (mRpnWim s)
theorem mWffSubEval_268 : MWffSubEval (M := M) 268 mWffOp_268 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_390 mWffSubEval_281
noncomputable abbrev mWffOp_279 (s : MWffState M) : MWffState M := mRpnPar2 (mRpnPar1 s)
theorem mWffSubEval_279 : MWffSubEval (M := M) 279 mWffOp_279 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_298 mWffSubEval_300
noncomputable abbrev mWffOp_246 (s : MWffState M) : MWffState M := mWffOp_279 (mWffOp_268 s)
theorem mWffSubEval_246 : MWffSubEval (M := M) 246 mWffOp_246 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_268 mWffSubEval_279
noncomputable abbrev mWffOp_284 (s : MWffState M) : MWffState M := mRpnPar3 (mRpnPar1 s)
theorem mWffSubEval_284 : MWffSubEval (M := M) 284 mWffOp_284 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_298 mWffSubEval_302
noncomputable abbrev mWffOp_286 (s : MWffState M) : MWffState M := mWffOp_284 (mRpnWeq s)
theorem mWffSubEval_286 : MWffSubEval (M := M) 286 mWffOp_286 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_329 mWffSubEval_284
noncomputable abbrev mWffOp_243 (s : MWffState M) : MWffState M := mWffOp_286 (mWffOp_246 s)
theorem mWffSubEval_243 : MWffSubEval (M := M) 243 mWffOp_243 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_246 mWffSubEval_286
noncomputable abbrev mWffOp_273 (s : MWffState M) : MWffState M := mRpnPar3 (mRpnPar2 s)
theorem mWffSubEval_273 : MWffSubEval (M := M) 273 mWffOp_273 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_300 mWffSubEval_302
noncomputable abbrev mWffOp_244 (s : MWffState M) : MWffState M := mWffOp_246 (mRpnWel s)
theorem mWffSubEval_244 : MWffSubEval (M := M) 244 mWffOp_244 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_327 mWffSubEval_246
noncomputable abbrev mWffOp_282 (s : MWffState M) : MWffState M := mRpnPar1 (mRpnPar3 s)
theorem mWffSubEval_282 : MWffSubEval (M := M) 282 mWffOp_282 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_302 mWffSubEval_298
noncomputable abbrev mWffOp_230 (s : MWffState M) : MWffState M := mWffOp_282 (mRpnWeq s)
theorem mWffSubEval_230 : MWffSubEval (M := M) 230 mWffOp_230 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_329 mWffSubEval_282
noncomputable abbrev mWffOp_229 (s : MWffState M) : MWffState M := mWffOp_230 (mWffOp_244 s)
theorem mWffSubEval_229 : MWffSubEval (M := M) 229 mWffOp_229 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_244 mWffSubEval_230
noncomputable abbrev mWffOp_228 (s : MWffState M) : MWffState M := mWffOp_229 (mWffOp_273 s)
theorem mWffSubEval_228 : MWffSubEval (M := M) 228 mWffOp_228 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_273 mWffSubEval_229
noncomputable abbrev mWffOp_227 (s : MWffState M) : MWffState M := mWffOp_228 (mRpnWel s)
theorem mWffSubEval_227 : MWffSubEval (M := M) 227 mWffOp_227 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_327 mWffSubEval_228
noncomputable abbrev mWffOp_226 (s : MWffState M) : MWffState M := mWffOp_227 (mWffOp_243 s)
theorem mWffSubEval_226 : MWffSubEval (M := M) 226 mWffOp_226 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_243 mWffSubEval_227
noncomputable abbrev mWffOp_271 (s : MWffState M) : MWffState M := mRpnWim (mRpnWal s)
theorem mWffSubEval_271 : MWffSubEval (M := M) 271 mWffOp_271 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_325 mWffSubEval_390
noncomputable abbrev mWffOp_254 (s : MWffState M) : MWffState M := mRpnWel (mWffOp_279 s)
theorem mWffSubEval_254 : MWffSubEval (M := M) 254 mWffOp_254 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_279 mWffSubEval_327
noncomputable abbrev mWffOp_253 (s : MWffState M) : MWffState M := mWffOp_273 (mWffOp_283 s)
theorem mWffSubEval_253 : MWffSubEval (M := M) 253 mWffOp_253 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_283 mWffSubEval_273
noncomputable abbrev mWffOp_259 (s : MWffState M) : MWffState M := mRpnWal (mWffOp_284 s)
theorem mWffSubEval_259 : MWffSubEval (M := M) 259 mWffOp_259 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_284 mWffSubEval_325
noncomputable abbrev mWffOp_237 (s : MWffState M) : MWffState M := mWffOp_279 (mWffOp_283 s)
theorem mWffSubEval_237 : MWffSubEval (M := M) 237 mWffOp_237 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_283 mWffSubEval_279
noncomputable abbrev mWffOp_236 (s : MWffState M) : MWffState M := mWffOp_237 (mWffOp_271 s)
theorem mWffSubEval_236 : MWffSubEval (M := M) 236 mWffOp_236 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_271 mWffSubEval_237
noncomputable abbrev mWffOp_235 (s : MWffState M) : MWffState M := mWffOp_236 (mWffOp_259 s)
theorem mWffSubEval_235 : MWffSubEval (M := M) 235 mWffOp_235 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_259 mWffSubEval_236
noncomputable abbrev mWffOp_234 (s : MWffState M) : MWffState M := mWffOp_235 (mRpnPar2 s)
theorem mWffSubEval_234 : MWffSubEval (M := M) 234 mWffOp_234 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_300 mWffSubEval_235
noncomputable abbrev mWffOp_233 (s : MWffState M) : MWffState M := mWffOp_234 (mRpnWal s)
theorem mWffSubEval_233 : MWffSubEval (M := M) 233 mWffOp_233 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_325 mWffSubEval_234
noncomputable abbrev mWffOp_232 (s : MWffState M) : MWffState M := mWffOp_233 (mRpnWal s)
theorem mWffSubEval_232 : MWffSubEval (M := M) 232 mWffOp_232 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_325 mWffSubEval_233
noncomputable abbrev mWffOp_231 (s : MWffState M) : MWffState M := mWffOp_232 (mWffOp_253 s)
theorem mWffSubEval_231 : MWffSubEval (M := M) 231 mWffOp_231 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_253 mWffSubEval_232
noncomputable abbrev mWffOp_275 (s : MWffState M) : MWffState M := (mRpnVk 0) ((mRpnVk 2) s)
theorem mWffSubEval_275 : MWffSubEval (M := M) 275 mWffOp_275 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_320 mWffSubEval_304
noncomputable abbrev mWffOp_252 (s : MWffState M) : MWffState M := mRpnWal (mRpnWa s)
theorem mWffSubEval_252 : MWffSubEval (M := M) 252 mWffOp_252 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_323 mWffSubEval_325
noncomputable abbrev mWffOp_251 (s : MWffState M) : MWffState M := mWffOp_252 (mRpnWim s)
theorem mWffSubEval_251 : MWffSubEval (M := M) 251 mWffOp_251 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_390 mWffSubEval_252
noncomputable abbrev mWffOp_250 (s : MWffState M) : MWffState M := mWffOp_251 (mRpnWel s)
theorem mWffSubEval_250 : MWffSubEval (M := M) 250 mWffOp_250 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_327 mWffSubEval_251
noncomputable abbrev mWffOp_276 (s : MWffState M) : MWffState M := mRpnCparam3 (mRpnSelect s)
theorem mWffSubEval_276 : MWffSubEval (M := M) 276 mWffOp_276 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_305 mWffSubEval_81
noncomputable abbrev mWffOp_260 (s : MWffState M) : MWffState M := mWffOp_280 ((mRpnVk 0) s)
theorem mWffSubEval_260 : MWffSubEval (M := M) 260 mWffOp_260 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_304 mWffSubEval_280
noncomputable abbrev mWffOp_262 (s : MWffState M) : MWffState M := mRpnWeq ((mRpnVk 0) s)
theorem mWffSubEval_262 : MWffSubEval (M := M) 262 mWffOp_262 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_304 mWffSubEval_329
noncomputable abbrev mWffOp_261 (s : MWffState M) : MWffState M := mWffOp_262 ((mRpnVk 1) s)
theorem mWffSubEval_261 : MWffSubEval (M := M) 261 mWffOp_261 :=
  mWffSubEval_seq rfl (by decide) rfl (by decide) mWffSubEval_319 mWffSubEval_262

/-- `MWffState`-level spine segment evaluation on `PAM M`. -/
def MWffSpineEval (k₁ k₂ : ℕ) (op : MWffState M → MWffState M) : Prop :=
  ∀ (slot pl np : PAM M) (s : MWffState M),
    MZfLogInv slot (List.replicate k₁ 1) (mWffStateToRegs pl np s) →
    ∃ slot' : PAM M,
      MZfLogInv slot' (List.replicate k₂ 1) (mWffStateToRegs pl np (op s)) ∧
      mReachPos (mZfLogCfg slot (List.replicate k₁ 1) (mWffStateToRegs pl np s))
        (mZfLogCfg slot' (List.replicate k₂ 1) (mWffStateToRegs pl np (op s)))

theorem mWffSpineEval_step {k k' : ℕ} {q_k q_sub : Fin 393}
    {op : MWffState M → MWffState M}
    (hwalk : walkInternal 99 (List.replicate k 1) = some q_k)
    (htr0 : zf393Trans q_k 0 = some (0, .right, q_sub))
    (hq_sub : 69 ≤ q_sub.val)
    (hsub : MWffSubEval (M := M) q_sub op)
    (hk : k + 1 = k' := by rfl) :
    MWffSpineEval (M := M) k k' op := by
  subst hk
  intro slot pl np s hinv
  have hwalk0 : walkInternal 99 (List.replicate k 1 ++ [0]) = some q_sub :=
    walkInternal_snoc hwalk htr0 hq_sub
  have hinv0 :
      MZfLogInv slot (trimZeros (List.replicate k 1 ++ [0])) (mWffStateToRegs pl np s) := by
    rwa [trimZeros_append_zero, trimZeros_replicate_one]
  obtain ⟨slot', hinv', hreach⟩ := hsub (List.replicate k 1 ++ [0]) hwalk0 slot pl np s hinv0
  rw [trimZeros_append_zero, trimZeros_replicate_one, retStack_append_zero,
    ← List.replicate_succ'] at hreach
  rw [retStack_append_zero, ← List.replicate_succ'] at hinv'
  exact ⟨slot', hinv', hreach⟩

theorem mWffSpineEval_trans {k₁ k₂ k₃ : ℕ} {op₁ op₂ op : MWffState M → MWffState M}
    (h1 : MWffSpineEval (M := M) k₁ k₂ op₁) (h2 : MWffSpineEval (M := M) k₂ k₃ op₂)
    (heq : (fun s ↦ op₂ (op₁ s)) = op := by rfl) :
    MWffSpineEval (M := M) k₁ k₃ op := by
  subst heq
  intro slot pl np s hinv
  obtain ⟨slot₁, hinv₁, hreach₁⟩ := h1 slot pl np s hinv
  obtain ⟨slot₂, hinv₂, hreach₂⟩ := h2 slot₁ pl np (op₁ s) hinv₁
  exact ⟨slot₂, hinv₂, mReachPos_trans hreach₁ hreach₂⟩

theorem mWffSpineEval_of_mRegSpineEval {k₁ k₂ : ℕ} {f : List (PAM M) → List (PAM M)}
    {op : MWffState M → MWffState M} (h : MRegSpineEval (M := M) k₁ k₂ f)
    (heq : ∀ pl np s, f (mWffStateToRegs pl np s) = mWffStateToRegs pl np (op s)) :
    MWffSpineEval (M := M) k₁ k₂ op := by
  intro slot pl np s hinv
  obtain ⟨_, slot', hinv', hreach⟩ := h slot (mWffStateToRegs pl np s) hinv
  rw [heq pl np s] at hinv' hreach
  exact ⟨slot', hinv', hreach⟩

theorem mWffSpineEval_55_58 : MWffSpineEval (M := M) 55 58 mRpnZf393B6aCheck1 := by
  refine mWffSpineEval_of_mRegSpineEval
    (mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_55 rfl (by decide) mSubEval_351) <|
     mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_56 rfl (by decide) mSubEval_364) <|
     mRegSpineEval_step walkInternal_spine_57 rfl (by decide) mSubEval_255) ?_
  intro pl np s
  simp only [mWffStateToRegs, mReg255Op, mReg256Op, mReg92Op, mRpnZf393B6aCheck1, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.set_cons_zero, List.set_cons_succ, zero_add]
  split_ifs <;> rfl

theorem mWffSpineEval_58_61 : MWffSpineEval (M := M) 58 61 mRpnZf393B6aCheck2 := by
  refine mWffSpineEval_of_mRegSpineEval
    (mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_58 rfl (by decide) mSubEval_355) <|
     mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_59 rfl (by decide) mSubEval_366) <|
     mRegSpineEval_step walkInternal_spine_60 rfl (by decide) mSubEval_255) ?_
  intro pl np s
  simp only [mWffStateToRegs, mReg255Op, mReg256Op, mReg92Op, mRpnZf393B6aCheck2, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.set_cons_zero, List.set_cons_succ, zero_add]
  split_ifs <;> rfl

theorem mWffSpineEval_97_101 : MWffSpineEval (M := M) 97 101 mRpnDetCheck := by
  refine mWffSpineEval_of_mRegSpineEval
    (mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_97 rfl (by decide) mSubEval_388) <|
     mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_98 rfl (by decide) mSubEval_354) <|
     mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_99 rfl (by decide) mSubEval_366) <|
     mRegSpineEval_step walkInternal_spine_100 rfl (by decide) mSubEval_93) ?_
  intro pl np s
  simp only [mWffStateToRegs, mReg93Op, mReg94Op, mRpnDetCheck, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.set_cons_zero, List.set_cons_succ, zero_add]
  split_ifs <;> rfl

noncomputable abbrev mWffSpineOp_13_21 (s : MWffState M) : MWffState M :=
  mRpnWal (mWffOp_270 (mWffOp_257 ((mRpnVk 2) (mWffOp_265 (mWffOp_277 ((mRpnVk 3)
    ((mRpnVk 0) s)))))))
theorem mWffSpineEval_13_21 : MWffSpineEval (M := M) 13 21 mWffSpineOp_13_21 :=
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_13 rfl (by decide) mWffSubEval_304) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_14 rfl (by decide) mWffSubEval_321) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_15 rfl (by decide) mWffSubEval_277) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_16 rfl (by decide) mWffSubEval_265) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_17 rfl (by decide) mWffSubEval_320) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_18 rfl (by decide) mWffSubEval_257) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_19 rfl (by decide) mWffSubEval_270) <|
  mWffSpineEval_step walkInternal_spine_20 rfl (by decide) mWffSubEval_325

noncomputable abbrev mWffSpineOp_21_29 (s : MWffState M) : MWffState M :=
  mWffOp_270 (mRpnWa (mWffOp_248 (mWffOp_238 (mRpnWim (mWffOp_238 (mWffOp_249 ((mRpnVk 1) s)))))))
theorem mWffSpineEval_21_29 : MWffSpineEval (M := M) 21 29 mWffSpineOp_21_29 :=
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_21 rfl (by decide) mWffSubEval_319) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_22 rfl (by decide) mWffSubEval_249) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_23 rfl (by decide) mWffSubEval_238) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_24 rfl (by decide) mWffSubEval_390) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_25 rfl (by decide) mWffSubEval_238) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_26 rfl (by decide) mWffSubEval_248) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_27 rfl (by decide) mWffSubEval_323) <|
  mWffSpineEval_step walkInternal_spine_28 rfl (by decide) mWffSubEval_270

noncomputable abbrev mWffSpineOp_29_37 (s : MWffState M) : MWffState M :=
  mRpnPar1 (mRpnWn (mWffOp_241 (mWffOp_272 (mWffOp_247 ((mRpnVk 2) ((mRpnVk 3) (mWffOp_245 s)))))))
theorem mWffSpineEval_29_37 : MWffSpineEval (M := M) 29 37 mWffSpineOp_29_37 :=
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_29 rfl (by decide) mWffSubEval_245) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_30 rfl (by decide) mWffSubEval_321) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_31 rfl (by decide) mWffSubEval_320) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_32 rfl (by decide) mWffSubEval_247) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_33 rfl (by decide) mWffSubEval_272) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_34 rfl (by decide) mWffSubEval_241) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_35 rfl (by decide) mWffSubEval_392) <|
  mWffSpineEval_step walkInternal_spine_36 rfl (by decide) mWffSubEval_298

noncomputable abbrev mWffSpineOp_37_45 (s : MWffState M) : MWffState M :=
  mRpnWn (mRpnPar1 (mWffOp_241 (mWffOp_278 (mWffOp_247 (mWffOp_285 (mWffOp_245 (mWffOp_274 s)))))))
theorem mWffSpineEval_37_45 : MWffSpineEval (M := M) 37 45 mWffSpineOp_37_45 :=
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_37 rfl (by decide) mWffSubEval_274) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_38 rfl (by decide) mWffSubEval_245) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_39 rfl (by decide) mWffSubEval_285) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_40 rfl (by decide) mWffSubEval_247) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_41 rfl (by decide) mWffSubEval_278) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_42 rfl (by decide) mWffSubEval_241) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_43 rfl (by decide) mWffSubEval_298) <|
  mWffSpineEval_step walkInternal_spine_44 rfl (by decide) mWffSubEval_392

noncomputable abbrev mWffSpineOp_45_55 (s : MWffState M) : MWffState M :=
  mRpnWa (mWffOp_271 (mWffOp_254 (mRpnPar3 (mWffOp_254 (mWffOp_271
    (mRpnWeq (mRpnPar2 (mWffOp_226 (mRpnPar2 s)))))))))
theorem mWffSpineEval_45_55 : MWffSpineEval (M := M) 45 55 mWffSpineOp_45_55 :=
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_45 rfl (by decide) mWffSubEval_300) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_46 rfl (by decide) mWffSubEval_226) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_47 rfl (by decide) mWffSubEval_300) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_48 rfl (by decide) mWffSubEval_329) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_49 rfl (by decide) mWffSubEval_271) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_50 rfl (by decide) mWffSubEval_254) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_51 rfl (by decide) mWffSubEval_302) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_52 rfl (by decide) mWffSubEval_254) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_53 rfl (by decide) mWffSubEval_271) <|
  mWffSpineEval_step walkInternal_spine_54 rfl (by decide) mWffSubEval_323

noncomputable abbrev mWffSpineOp_55_65 (s : MWffState M) : MWffState M :=
  mWffOp_253 (mRpnWex (mRpnWeq (mWffOp_231 (mRpnZf393B6aCheck2 (mRpnZf393B6aCheck1 s)))))
theorem mWffSpineEval_55_65 : MWffSpineEval (M := M) 55 65 mWffSpineOp_55_65 :=
  mWffSpineEval_trans mWffSpineEval_55_58 <|
  mWffSpineEval_trans mWffSpineEval_58_61 <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_61 rfl (by decide) mWffSubEval_231) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_62 rfl (by decide) mWffSubEval_329) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_63 rfl (by decide) mWffSubEval_331) <|
  mWffSpineEval_step walkInternal_spine_64 rfl (by decide) mWffSubEval_253

noncomputable abbrev mWffSpineOp_65_73 (s : MWffState M) : MWffState M :=
  mRpnWeq (mWffOp_273 (mRpnWeq (mWffOp_243 (mWffOp_259 (mRpnWal (mWffOp_279 (mWffOp_272 s)))))))
theorem mWffSpineEval_65_73 : MWffSpineEval (M := M) 65 73 mWffSpineOp_65_73 :=
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_65 rfl (by decide) mWffSubEval_272) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_66 rfl (by decide) mWffSubEval_279) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_67 rfl (by decide) mWffSubEval_325) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_68 rfl (by decide) mWffSubEval_259) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_69 rfl (by decide) mWffSubEval_243) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_70 rfl (by decide) mWffSubEval_329) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_71 rfl (by decide) mWffSubEval_273) <|
  mWffSpineEval_step walkInternal_spine_72 rfl (by decide) mWffSubEval_329

noncomputable abbrev mWffSpineOp_73_81 (s : MWffState M) : MWffState M :=
  mWffOp_274 (mWffOp_273 (mRpnWim (mWffOp_244 (mRpnPar2 (mRpnPar3 (mRpnWel (mWffOp_226 s)))))))
theorem mWffSpineEval_73_81 : MWffSpineEval (M := M) 73 81 mWffSpineOp_73_81 :=
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_73 rfl (by decide) mWffSubEval_226) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_74 rfl (by decide) mWffSubEval_327) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_75 rfl (by decide) mWffSubEval_302) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_76 rfl (by decide) mWffSubEval_300) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_77 rfl (by decide) mWffSubEval_244) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_78 rfl (by decide) mWffSubEval_390) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_79 rfl (by decide) mWffSubEval_273) <|
  mWffSpineEval_step walkInternal_spine_80 rfl (by decide) mWffSubEval_274

noncomputable abbrev mWffSpineOp_81_89 (s : MWffState M) : MWffState M :=
  mWffOp_263 (mWffOp_248 (mRpnWel (mWffOp_275 ((mRpnVk 2) (mWffOp_268 (mRpnWim (mRpnPar3 s)))))))
theorem mWffSpineEval_81_89 : MWffSpineEval (M := M) 81 89 mWffSpineOp_81_89 :=
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_81 rfl (by decide) mWffSubEval_302) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_82 rfl (by decide) mWffSubEval_390) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_83 rfl (by decide) mWffSubEval_268) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_84 rfl (by decide) mWffSubEval_320) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_85 rfl (by decide) mWffSubEval_275) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_86 rfl (by decide) mWffSubEval_327) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_87 rfl (by decide) mWffSubEval_248) <|
  mWffSpineEval_step walkInternal_spine_88 rfl (by decide) mWffSubEval_263

noncomputable abbrev mWffSpineOp_89_97 (s : MWffState M) : MWffState M :=
  mRpnWim (mWffOp_282 (mRpnCparam2 (mWffOp_276 (mWffOp_257 ((mRpnVk 0)
    (mWffOp_250 (mWffOp_275 s)))))))
theorem mWffSpineEval_89_97 : MWffSpineEval (M := M) 89 97 mWffSpineOp_89_97 :=
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_89 rfl (by decide) mWffSubEval_275) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_90 rfl (by decide) mWffSubEval_250) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_91 rfl (by decide) mWffSubEval_304) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_92 rfl (by decide) mWffSubEval_257) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_93 rfl (by decide) mWffSubEval_276) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_94 rfl (by decide) mWffSubEval_79) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_95 rfl (by decide) mWffSubEval_282) <|
  mWffSpineEval_step walkInternal_spine_96 rfl (by decide) mWffSubEval_390

noncomputable abbrev mWffSpineOp_97_106 (s : MWffState M) : MWffState M :=
  mRpnPar2 (mWffOp_270 (mWffOp_231 (mWffOp_259 (mWffOp_276 (mRpnDetCheck s)))))
theorem mWffSpineEval_97_106 : MWffSpineEval (M := M) 97 106 mWffSpineOp_97_106 :=
  mWffSpineEval_trans mWffSpineEval_97_101 <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_101 rfl (by decide) mWffSubEval_276) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_102 rfl (by decide) mWffSubEval_259) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_103 rfl (by decide) mWffSubEval_231) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_104 rfl (by decide) mWffSubEval_270) <|
  mWffSpineEval_step walkInternal_spine_105 rfl (by decide) mWffSubEval_300

noncomputable abbrev mWffSpineOp_106_114 (s : MWffState M) : MWffState M :=
  mRpnWel (mWffOp_277 ((mRpnVk 1) (mWffOp_249 (mWffOp_260 ((mRpnVk 0)
    (mWffOp_260 (mWffOp_267 s)))))))
theorem mWffSpineEval_106_114 : MWffSpineEval (M := M) 106 114 mWffSpineOp_106_114 :=
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_106 rfl (by decide) mWffSubEval_267) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_107 rfl (by decide) mWffSubEval_260) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_108 rfl (by decide) mWffSubEval_304) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_109 rfl (by decide) mWffSubEval_260) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_110 rfl (by decide) mWffSubEval_249) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_111 rfl (by decide) mWffSubEval_319) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_112 rfl (by decide) mWffSubEval_277) <|
  mWffSpineEval_step walkInternal_spine_113 rfl (by decide) mWffSubEval_327

noncomputable abbrev mWffSpineOp_114_123 (s : MWffState M) : MWffState M :=
  mRpnSelect (mWffOp_278 (mWffOp_272 (mWffOp_278 (mWffOp_250 (mWffOp_277 (mWffOp_261
    (mRpnWim (mWffOp_261 s))))))))
theorem mWffSpineEval_114_123 : MWffSpineEval (M := M) 114 123 mWffSpineOp_114_123 :=
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_114 rfl (by decide) mWffSubEval_261) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_115 rfl (by decide) mWffSubEval_390) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_116 rfl (by decide) mWffSubEval_261) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_117 rfl (by decide) mWffSubEval_277) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_118 rfl (by decide) mWffSubEval_250) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_119 rfl (by decide) mWffSubEval_278) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_120 rfl (by decide) mWffSubEval_272) <|
  mWffSpineEval_trans (mWffSpineEval_step walkInternal_spine_121 rfl (by decide) mWffSubEval_278) <|
  mWffSpineEval_step walkInternal_spine_122 rfl (by decide) mWffSubEval_305

/-! ### RPN Clause Definitions and Closed-Form `mZf393ClauseDispatch` Equivalence -/

noncomputable def mRpnClauseDET (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnDetCheck (mRpnWim (mRpnPar1 (mRpnPar3 (mRpnCparam2 (mRpnCparam3 s))))))

noncomputable def mRpnClauseGEN (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnWal (mRpnPar3 (mRpnPar1 (mRpnCparam3 s))))

noncomputable def mRpnClauseB1 (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnWim (mRpnWim (mRpnWim (mRpnPar3 (mRpnPar1 (mRpnWim
    (mRpnPar3 (mRpnPar2 (mRpnWim (mRpnPar2 (mRpnPar1 s)))))))))))

noncomputable def mRpnClauseB2 (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnWim (mRpnPar1 (mRpnWim (mRpnPar1 (mRpnWn (mRpnPar1 s))))))

noncomputable def mRpnClauseB3 (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnWim (mRpnWim (mRpnPar2 (mRpnWn (mRpnPar1 (mRpnPar1 s))))))

noncomputable def mRpnClauseB4 (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnWim (mRpnWim (mRpnWal (mRpnPar3 (mRpnPar1 (mRpnWal
    (mRpnPar2 (mRpnPar1 (mRpnWal (mRpnWim (mRpnPar3 (mRpnPar2 (mRpnPar1 s)))))))))))))

noncomputable def mRpnZf393ClauseB6a (s : MWffState M) : MWffState M :=
  let s1 :=
    mRpnWim (mRpnWal (mRpnWeq (mRpnPar2 (mRpnPar1 (mRpnPar3 (mRpnWeq (mRpnPar2 (mRpnPar1 s))))))))
  let s2 :=
    mRpnWa (mRpnWim (mRpnWal (mRpnWel (mRpnPar2 (mRpnPar1 (mRpnPar3
      (mRpnWel (mRpnPar2 (mRpnPar1 s1)))))))))
  mRpnSelect (mRpnZf393B6aCheck2 (mRpnZf393B6aCheck1 s2))

noncomputable def mRpnClauseB6b (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnWim (mRpnWal (mRpnWal (mRpnPar3 (mRpnPar1 (mRpnPar2
    (mRpnWal (mRpnWal (mRpnPar3 (mRpnPar2 (mRpnPar1 s)))))))))))

noncomputable def mRpnClauseB6c (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnWim (mRpnPar2 (mRpnWex (mRpnWal (mRpnPar2 (mRpnPar1 (mRpnPar1 s)))))))

noncomputable def mRpnClauseB7 (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnWex (mRpnWeq (mRpnPar2 (mRpnPar1 (mRpnPar1 s)))))

noncomputable def mRpnClauseB8a (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnWim (mRpnWim (mRpnWeq (mRpnPar3 (mRpnPar2 (mRpnWeq
    (mRpnPar3 (mRpnPar1 (mRpnWeq (mRpnPar2 (mRpnPar1 s)))))))))))

noncomputable def mRpnClauseB8b (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnWim (mRpnWim (mRpnWel (mRpnPar3 (mRpnPar2 (mRpnWel
    (mRpnPar3 (mRpnPar1 (mRpnWeq (mRpnPar2 (mRpnPar1 s)))))))))))

noncomputable def mRpnClauseB8c (s : MWffState M) : MWffState M :=
  mRpnSelect (mRpnWim (mRpnWim (mRpnWel (mRpnPar2 (mRpnPar3 (mRpnWel
    (mRpnPar1 (mRpnPar3 (mRpnWeq (mRpnPar2 (mRpnPar1 s)))))))))))

noncomputable def mRpnClauseEXT (s : MWffState M) : MWffState M :=
  let s1 := mRpnWim (mRpnWel (mRpnVk 1 (mRpnVk 2 (mRpnWel (mRpnVk 0 (mRpnVk 2 (mRpnVk 2 s)))))))
  let s2 := mRpnWa (mRpnWim (mRpnWel (mRpnVk 0 (mRpnVk 2 (mRpnWel (mRpnVk 1 (mRpnVk 2 s1)))))))
  mRpnSelect (mRpnWim (mRpnWeq (mRpnVk 1 (mRpnVk 0 (mRpnWal s2)))))

noncomputable def mRpnClauseREP (s : MWffState M) : MWffState M :=
  let s1 := mRpnWal (mRpnWex (mRpnWal (mRpnWim (mRpnWeq (mRpnVk 1 (mRpnVk 2
    (mRpnWal (mRpnPar1 (mRpnVk 1 (mRpnVk 2 (mRpnVk 1 (mRpnVk 3 s))))))))))))
  let s2 := mRpnWel (mRpnVk 1 (mRpnVk 2 (mRpnVk 2 (mRpnVk 1 s1))))
  let s3 := mRpnWim (mRpnWex (mRpnWa (mRpnWal (mRpnPar1 (mRpnVk 1
    (mRpnWel (mRpnVk 0 (mRpnVk 3 (mRpnVk 3 s2)))))))))
  let s4 := mRpnWex (mRpnWa (mRpnWal (mRpnPar1 (mRpnVk 1
    (mRpnWel (mRpnVk 0 (mRpnVk 3 (mRpnVk 3 s3))))))))
  let s5 := mRpnWa (mRpnWim (mRpnWel (mRpnVk 1 (mRpnVk 2 s4))))
  mRpnSelect (mRpnWim (mRpnWex (mRpnWal s5)))

noncomputable def mRpnClausePOW (s : MWffState M) : MWffState M :=
  let s1 := mRpnWal (mRpnWim (mRpnWel (mRpnVk 0 (mRpnVk 3 (mRpnWel
    (mRpnVk 2 (mRpnVk 3 (mRpnVk 3 (mRpnVk 2 (mRpnVk 1 s))))))))))
  mRpnSelect (mRpnWex (mRpnWal (mRpnWim (mRpnWel (mRpnVk 1 (mRpnVk 2 s1))))))

noncomputable def mRpnClauseUNI (s : MWffState M) : MWffState M :=
  let s1 := mRpnWex (mRpnWa (mRpnWel (mRpnVk 0 (mRpnVk 3 (mRpnWel
    (mRpnVk 3 (mRpnVk 2 (mRpnVk 3 (mRpnVk 2 (mRpnVk 1 s))))))))))
  mRpnSelect (mRpnWex (mRpnWal (mRpnWim (mRpnWel (mRpnVk 1 (mRpnVk 2 s1))))))

noncomputable def mRpnClauseINF (s : MWffState M) : MWffState M :=
  let s1 := mRpnWel (mRpnVk 1 (mRpnVk 2 (mRpnVk 2 (mRpnWel (mRpnVk 1
    (mRpnVk 0 (mRpnVk 0 (mRpnWel (mRpnVk 1 (mRpnVk 0 (mRpnVk 1 s)))))))))))
  let s2 := mRpnWim (mRpnWeq (mRpnVk 0 (mRpnVk 1 (mRpnWel (mRpnVk 2 (mRpnVk 1 (mRpnVk 1 s1)))))))
  let s3 := mRpnWal (mRpnWa (mRpnWim (mRpnWel (mRpnVk 2 (mRpnVk 1
    (mRpnWeq (mRpnVk 0 (mRpnVk 1 s2))))))))
  mRpnSelect (mRpnWex (mRpnWa (mRpnWal (mRpnWim (mRpnWex (mRpnWa s3))))))

noncomputable def mRpnZf393AllClausesOp (s : MWffState M) : MWffState M :=
  let s0 := mRpnVk 0 s
  mRpnClauseINF (mRpnClauseB6c (mRpnClauseB6b (mRpnClauseGEN (mRpnClauseDET
    (mRpnClauseEXT (mRpnClauseB1 (mRpnClauseB8c (mRpnClauseB8b (mRpnClauseB8a
      (mRpnClauseB4 (mRpnClauseB7 (mRpnClauseB6b (mRpnZf393ClauseB6a (mRpnClauseB8b
        (mRpnClauseB3 (mRpnClauseUNI (mRpnClauseB2
          (mRpnClausePOW (mRpnClauseREP s0)))))))))))))))))))

noncomputable def mRpnZf393AllClauses (top stk ac p1 p2 p3 : PAM M) : MWffState M :=
  mRpnZf393AllClausesOp ⟨top, stk, ac, p1, p2, p3⟩

set_option maxRecDepth 50000 in
theorem mWffSpineEval_13_123 : MWffSpineEval (M := M) 13 123 mRpnZf393AllClausesOp :=
  mWffSpineEval_trans mWffSpineEval_13_21 <|
  mWffSpineEval_trans mWffSpineEval_21_29 <|
  mWffSpineEval_trans mWffSpineEval_29_37 <|
  mWffSpineEval_trans mWffSpineEval_37_45 <|
  mWffSpineEval_trans mWffSpineEval_45_55 <|
  mWffSpineEval_trans mWffSpineEval_55_65 <|
  mWffSpineEval_trans mWffSpineEval_65_73 <|
  mWffSpineEval_trans mWffSpineEval_73_81 <|
  mWffSpineEval_trans mWffSpineEval_81_89 <|
  mWffSpineEval_trans mWffSpineEval_89_97 <|
  mWffSpineEval_trans mWffSpineEval_97_106 <|
  mWffSpineEval_trans mWffSpineEval_106_114 <|
  mWffSpineEval_114_123

@[simp]
theorem mRpnCons_mPair (x y stk ac p1 p2 p3 : PAM M) :
    mRpnCons ⟨y, mPair x stk, ac, p1, p2, p3⟩ = ⟨mPair x y, stk, ac, p1, p2, p3⟩ := by
  simp [mRpnCons]

@[simp]
theorem mRpnWeq_eval (x y stk ac p1 p2 p3 : PAM M) :
    mRpnWeq ⟨y, mPair x stk, ac, p1, p2, p3⟩ = ⟨mZfEq x y, stk, ac, p1, p2, p3⟩ := by
  simp [mRpnWeq, mRpnVk, mZfEq]

@[simp]
theorem mRpnWel_eval (x y stk ac p1 p2 p3 : PAM M) :
    mRpnWel ⟨y, mPair x stk, ac, p1, p2, p3⟩ = ⟨mZfMem x y, stk, ac, p1, p2, p3⟩ := by
  simp [mRpnWel, mRpnVk, mZfMem]

@[simp]
theorem mRpnWim_eval (φ ψ stk ac p1 p2 p3 : PAM M) :
    mRpnWim ⟨ψ, mPair φ stk, ac, p1, p2, p3⟩ = ⟨mZfImp φ ψ, stk, ac, p1, p2, p3⟩ := by
  simp [mRpnWim, mRpnVk, mZfImp]

@[simp]
theorem mRpnWn_eval (φ stk ac p1 p2 p3 : PAM M) :
    mRpnWn ⟨φ, stk, ac, p1, p2, p3⟩ = ⟨mZfNot φ, stk, ac, p1, p2, p3⟩ := by
  simp [mRpnWn, mRpnVk, mZfNot]

@[simp]
theorem mRpnWal_eval (x φ stk ac p1 p2 p3 : PAM M) :
    mRpnWal ⟨φ, mPair x stk, ac, p1, p2, p3⟩ = ⟨mZfAll x φ, stk, ac, p1, p2, p3⟩ := by
  simp [mRpnWal, mRpnVk, mZfAll]

@[simp]
theorem mRpnWex_eval (x φ stk ac p1 p2 p3 : PAM M) :
    mRpnWex ⟨φ, mPair x stk, ac, p1, p2, p3⟩ = ⟨mZfEx x φ, stk, ac, p1, p2, p3⟩ := by
  simp [mRpnWex, mZfEx]

@[simp]
theorem mRpnWa_eval (φ ψ stk ac p1 p2 p3 : PAM M) :
    mRpnWa ⟨ψ, mPair φ stk, ac, p1, p2, p3⟩ = ⟨mZfAnd φ ψ, stk, ac, p1, p2, p3⟩ := by
  simp [mRpnWa, mZfAnd]

@[simp]
theorem mRpnSelect_eval (candidate prev stk ac p1 p2 p3 : PAM M) :
    mRpnSelect ⟨candidate, mPair prev stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then prev else candidate, stk, ac - 1, p1, p2, p3⟩ := by
  by_cases hac : ac = 0 <;> simp [mRpnSelect, hac]

@[simp]
theorem mRpnClauseB1_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseB1 ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxB1 p1 p2 p3, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseB1, mRpnPar1, mRpnPar2, mRpnPar3, mAxB1]

@[simp]
theorem mRpnClauseB2_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseB2 ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxB2 p1, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseB2, mRpnPar1, mAxB2]

@[simp]
theorem mRpnClauseB3_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseB3 ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxB3 p1 p2, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseB3, mRpnPar1, mRpnPar2, mAxB3]

@[simp]
theorem mRpnClauseB4_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseB4 ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxB4 p1 p2 p3, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseB4, mRpnPar1, mRpnPar2, mRpnPar3, mAxB4]

@[simp]
theorem mRpnZf393ClauseB6a_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnZf393ClauseB6a ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else (if p1 = p3 ∨ p2 = p3 then 0 else mAxB6a p1 p2 p3),
       stk, ac - 1, p1, p2, p3⟩ := by
  by_cases hp1 : p1 = p3 <;> by_cases hp2 : p2 = p3 <;>
    simp [mRpnZf393ClauseB6a, mRpnZf393B6aCheck1, mRpnZf393B6aCheck2,
      mRpnPar1, mRpnPar2, mRpnPar3, mAxB6a, hp1, hp2]

@[simp]
theorem mRpnClauseB6b_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseB6b ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxB6b p1 p2 p3, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseB6b, mRpnPar1, mRpnPar2, mRpnPar3, mAxB6b]

@[simp]
theorem mRpnClauseB6c_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseB6c ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxB6c p1 p2, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseB6c, mRpnPar1, mRpnPar2, mAxB6c]

@[simp]
theorem mRpnClauseB7_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseB7 ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxB7 p1 p2, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseB7, mRpnPar1, mRpnPar2, mAxB7]

@[simp]
theorem mRpnClauseB8a_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseB8a ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxB8a p1 p2 p3, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseB8a, mRpnPar1, mRpnPar2, mRpnPar3, mAxB8a]

@[simp]
theorem mRpnClauseB8b_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseB8b ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxB8b p1 p2 p3, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseB8b, mRpnPar1, mRpnPar2, mRpnPar3, mAxB8b]

@[simp]
theorem mRpnClauseB8c_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseB8c ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxB8c p1 p2 p3, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseB8c, mRpnPar1, mRpnPar2, mRpnPar3, mAxB8c]

@[simp]
theorem mRpnClauseEXT_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseEXT ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxExt, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseEXT, mRpnVk, mAxExt]

@[simp]
theorem mRpnClauseREP_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseREP ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxRep p1, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseREP, mRpnVk, mRpnPar1, mAxRep, mAxRepRhs]

@[simp]
theorem mRpnClausePOW_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClausePOW ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxPow, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClausePOW, mRpnVk, mAxPow]

@[simp]
theorem mRpnClauseUNI_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseUNI ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxUni, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseUNI, mRpnVk, mAxUni]

@[simp]
theorem mRpnClauseINF_eval (top stk ac p1 p2 p3 : PAM M) :
    mRpnClauseINF ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac = 0 then top else mAxInf, stk, ac - 1, p1, p2, p3⟩ := by
  simp [mRpnClauseINF, mRpnVk, mAxInf, mAxInfSingleton]

/-- Closed-form 20-clause dispatch of `zf393` inside `PAM M`. -/
noncomputable def mZf393ClauseDispatch (topwff wffstack ac p1 p2 p3 : PAM M) : PAM M × PAM M :=
  let stk0 := mPair topwff wffstack
  if ac = ((0 : ℕ) : PAM M) then (0, stk0)
  else if ac = ((1 : ℕ) : PAM M) then (mAxRep p1, stk0)
  else if ac = ((2 : ℕ) : PAM M) then (mAxPow, stk0)
  else if ac = ((3 : ℕ) : PAM M) then (mAxB2 p1, stk0)
  else if ac = ((4 : ℕ) : PAM M) then (mAxUni, stk0)
  else if ac = ((5 : ℕ) : PAM M) then (mAxB3 p1 p2, stk0)
  else if ac = ((6 : ℕ) : PAM M) then (mAxB8b p1 p2 p3, stk0)
  else if ac = ((7 : ℕ) : PAM M) then
    if p1 = p3 ∨ p2 = p3 then (0, stk0) else (mAxB6a p1 p2 p3, stk0)
  else if ac = ((8 : ℕ) : PAM M) then (mAxB6b p1 p2 p3, stk0)
  else if ac = ((9 : ℕ) : PAM M) then (mAxB7 p1 p2, stk0)
  else if ac = ((10 : ℕ) : PAM M) then (mAxB4 p1 p2 p3, stk0)
  else if ac = ((11 : ℕ) : PAM M) then (mAxB8a p1 p2 p3, stk0)
  else if ac = ((12 : ℕ) : PAM M) then (mAxB8b p1 p2 p3, stk0)
  else if ac = ((13 : ℕ) : PAM M) then (mAxB8c p1 p2 p3, stk0)
  else if ac = ((14 : ℕ) : PAM M) then (mAxB1 p1 p2 p3, stk0)
  else if ac = ((15 : ℕ) : PAM M) then (mAxExt, stk0)
  else if ac = ((16 : ℕ) : PAM M) then
    let pop1 := mUnpair stk0
    let φ := pop1.1
    let pop2 := mUnpair pop1.2
    let maj := pop2.1
    let stk2 := pop2.2
    if mZfImp φ p1 = maj then (p1, stk2) else (0, stk2)
  else if ac = ((17 : ℕ) : PAM M) then
    let pop1 := mUnpair stk0
    (mZfAll p1 pop1.1, pop1.2)
  else if ac = ((18 : ℕ) : PAM M) then (mAxB6b p1 p2 p3, stk0)
  else if ac = ((19 : ℕ) : PAM M) then (mAxB6c p1 p2, stk0)
  else (mAxInf, stk0)

private def pamSuccChain : ℕ → PAM M → PAM M
  | 0, d => d
  | n + 1, d => pamSuccChain n d + 1

private theorem add_natCast_eq_pamSuccChain (d : PAM M) :
    ∀ k : ℕ, d + (k : PAM M) = pamSuccChain k d
  | 0 => by simp [pamSuccChain]
  | k + 1 => by
    rw [Nat.cast_succ, ← add_assoc, add_natCast_eq_pamSuccChain d k]
    rfl

private theorem natCast_eq_pamSuccChain (k : ℕ) : (k : PAM M) = pamSuccChain k 0 := by
  simpa using add_natCast_eq_pamSuccChain (0 : PAM M) k

@[simp]
private theorem prod_mk_ite {α β : Type*} (c : Prop) [Decidable c] (a b : α) (y : β) :
    (if c then a else b, y) = if c then (a, y) else (b, y) := by
  split_ifs <;> rfl

theorem mRpnZf393AllClauses_eq_mZf393ClauseDispatch (topwff wffstack ac p1 p2 p3 : PAM M) :
    let out := mRpnZf393AllClauses topwff wffstack ac p1 p2 p3
    (out.topwff, out.wffstack) = mZf393ClauseDispatch topwff wffstack ac p1 p2 p3 := by
  dsimp only
  rcases lt_or_ge ac ((20 : ℕ) : PAM M) with hlt20 | hge20
  · obtain ⟨k, hk20, rfl⟩ := lt_natCast_iff.mp hlt20
    have hk_cases :
        k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
        k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 :=
      by omega
    rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [mZf393ClauseDispatch, natCast_inj_pam, OfNat.ofNat_ne_zero,
        one_ne_zero, Nat.reduceEqDiff, ↓reduceIte]
      rw [natCast_eq_pamSuccChain]
      dsimp only [pamSuccChain]
      unfold mRpnZf393AllClauses mRpnZf393AllClausesOp
      simp [mRpnVk, mRpnClauseDET, mRpnDetCheck, mRpnClauseGEN, mRpnCparam2, mRpnCparam3,
        mRpnPar1, mRpnPar3]
  · have hne : ∀ (n : ℕ), n < 20 → ac ≠ (n : PAM M) :=
      fun n hn heq ↦ not_lt_of_ge hge20 (heq ▸ natCast_lt_iff.mpr hn)
    unfold mZf393ClauseDispatch
    simp only [hne 0 (by decide), hne 1 (by decide), hne 2 (by decide), hne 3 (by decide),
      hne 4 (by decide), hne 5 (by decide), hne 6 (by decide), hne 7 (by decide),
      hne 8 (by decide), hne 9 (by decide), hne 10 (by decide), hne 11 (by decide),
      hne 12 (by decide), hne 13 (by decide), hne 14 (by decide), hne 15 (by decide),
      hne 16 (by decide), hne 17 (by decide), hne 18 (by decide), hne 19 (by decide),
      ↓reduceIte]
    rcases hge20 with ⟨d, hd⟩
    have hac_eq : ac = pamSuccChain 20 d := by
      rw [← hd, add_comm, add_natCast_eq_pamSuccChain]
    rw [hac_eq]
    dsimp only [pamSuccChain]
    unfold mRpnZf393AllClauses mRpnZf393AllClausesOp
    simp [mRpnVk, mRpnClauseDET, mRpnDetCheck, mRpnClauseGEN, mRpnCparam2, mRpnCparam3,
      mRpnPar1, mRpnPar3]

/-! ## Section 6: Header Unpairing (`k = 0..13`), Halt Check (`k = 123, 124`), and One-Iteration
Simulation -/

/-- The 4 persistent registers of `main()` in `zf393` inside `PAM M`. -/
structure MZfMainCfg (M : Type*) [PAStructure M] where
  prooflist : PAM M
  nextproof : PAM M
  topwff : PAM M
  wffstack : PAM M

def mZfMainInit : MZfMainCfg M := ⟨0, 0, 0, 0⟩

def mRegsToMainCfg (regs : List (PAM M)) : MZfMainCfg M :=
  ⟨regs.getD 0 0, regs.getD 1 0, regs.getD 2 0, regs.getD 3 0⟩

/-- One body-iteration transition of `main()` in `zf393` inside `PAM M`. -/
noncomputable def mZf393MainNext (c : MZfMainCfg M) : MZfMainCfg M :=
  let prooflist₁ := if c.prooflist = 0 then c.nextproof else c.prooflist - 1
  let nextproof' := if c.prooflist = 0 then c.nextproof + 1 else c.nextproof
  let u1 := mUnpair prooflist₁
  let ac := u1.1
  let u2 := mUnpair u1.2
  let p1 := u2.1
  let u3 := mUnpair u2.2
  let p2 := u3.1
  let u4 := mUnpair u3.2
  let p3 := u4.1
  let prooflist' := u4.2
  let res := mZf393ClauseDispatch c.topwff c.wffstack ac p1 p2 p3
  ⟨prooflist', nextproof', res.1, res.2⟩

/-- Partial step of `main()` in `zf393`: halts (`none`) iff the newly produced `topwff` is `1`. -/
noncomputable def mZf393MainStep (c : MZfMainCfg M) : Option (MZfMainCfg M) :=
  if (mZf393MainNext c).topwff = 1 then none else some (mZf393MainNext c)

/-- Invariant at `ip = []`: 11 registers with scratch registers `8, 9, 10` cleared to `0`. -/
def MRegsInv (regs : List (PAM M)) : Prop :=
  regs.length = 11 ∧ regs.getD 8 0 = 0 ∧ regs.getD 9 0 = 0 ∧ regs.getD 10 0 = 0

omit [PAModel M] in
theorem mRegsInv_init : MRegsInv (List.replicate 11 (0 : PAM M)) :=
  ⟨by simp, rfl, rfl, rfl⟩

omit [PAModel M] in
theorem paDef_mRegsInv {n : ℕ} {R : (Fin n → PAM M) → List (PAM M)} (hR : PAFunRegs n R) :
    PADefN n (fun u ↦ MRegsInv (R u)) := by
  refine paDefN_congr (fun u ↦ ?_)
    (paDef_and (paDef_eq (paFunRegs_getD hR 8) (paFun_const 0))
      (paDef_and (paDef_eq (paFunRegs_getD hR 9) (paFun_const 0))
        (paDef_eq (paFunRegs_getD hR 10) (paFun_const 0))))
  simp [MRegsInv, hR.1 u]

omit [PAModel M] in
theorem mRegs_eq_of_mRegsInv {regs : List (PAM M)} (hInv : MRegsInv regs) :
    regs = [regs.getD 0 0, regs.getD 1 0, regs.getD 2 0, regs.getD 3 0,
            regs.getD 4 0, regs.getD 5 0, regs.getD 6 0, regs.getD 7 0, 0, 0, 0] := by
  rcases hInv with ⟨hlen, h8, h9, h10⟩
  rcases regs with _ | ⟨r0, _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, _ | ⟨r4, _ | ⟨r5, _ |
    ⟨r6, _ | ⟨r7, _ | ⟨r8, _ | ⟨r9, _ | ⟨r10, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen; done)
  dsimp [List.getD] at h8 h9 h10
  subst h8 h9 h10
  rfl

noncomputable def mRegHeader05Op (regs : List (PAM M)) : List (PAM M) :=
  ((((mReg95Op regs).set 4 0).set 5 0).set 6 0).set 7 0

theorem mRegSpineEval_0_5 : MRegSpineEval (M := M) 0 5 mRegHeader05Op :=
  mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_0 rfl (by decide) mSubEval_95) <|
  mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_1 rfl (by decide) mSubEval_342) <|
  mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_2 rfl (by decide) mSubEval_346) <|
  mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_3 rfl (by decide) mSubEval_352) <|
  mRegSpineEval_step walkInternal_spine_4 rfl (by decide) mSubEval_356

theorem mRegHeader05Op_eval (pl np top stk ac0 p1_0 p2_0 p3_0 : PAM M) :
    mRegHeader05Op [pl, np, top, stk, ac0, p1_0, p2_0, p3_0, 0, 0, 0] =
      [if pl = 0 then np else pl - 1, if pl = 0 then np + 1 else np,
       top, stk, 0, 0, 0, 0, 0, 0, 0] := by
  by_cases hpl : pl = 0 <;>
    simp [mRegHeader05Op, mReg95Op, mReg97Op, hpl, List.getD]

theorem mReg269Op_eval (pl np top stk ac p1 p2 p3 : PAM M) :
    mReg269Op [pl, np, top, stk, ac, p1, p2, p3, 0, 0, 0] =
      [(mUnpair pl).2, np, top, stk, ac, p1, p2, p3, (mUnpair pl).1, 0, 0] := by
  simp [mReg269Op, mRegUnpairGen, List.getD]

noncomputable def mRegUnpairMoveOp (r : ℕ) (regs : List (PAM M)) : List (PAM M) :=
  let u := mReg269Op regs
  (u.set 8 0).set r (u.getD r 0 + u.getD 8 0)

theorem mRegSpineEval_5_7 : MRegSpineEval (M := M) 5 7 (mRegUnpairMoveOp 4) :=
  mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_5 rfl (by decide) mSubEval_269) <|
  mRegSpineEval_step walkInternal_spine_6 rfl (by decide) mSubEval_360

theorem mRegSpineEval_7_9 : MRegSpineEval (M := M) 7 9 (mRegUnpairMoveOp 5) :=
  mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_7 rfl (by decide) mSubEval_269) <|
  mRegSpineEval_step walkInternal_spine_8 rfl (by decide) mSubEval_364

theorem mRegSpineEval_9_11 : MRegSpineEval (M := M) 9 11 (mRegUnpairMoveOp 6) :=
  mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_9 rfl (by decide) mSubEval_269) <|
  mRegSpineEval_step walkInternal_spine_10 rfl (by decide) mSubEval_366

theorem mRegSpineEval_11_13 : MRegSpineEval (M := M) 11 13 (mRegUnpairMoveOp 7) :=
  mRegSpineEval_trans (mRegSpineEval_step walkInternal_spine_11 rfl (by decide) mSubEval_269) <|
  mRegSpineEval_step walkInternal_spine_12 rfl (by decide) mSubEval_368

theorem mRegSpineEval_0_13 :
    MRegSpineEval (M := M) 0 13 (fun regs ↦
      mRegUnpairMoveOp 7 (mRegUnpairMoveOp 6 (mRegUnpairMoveOp 5
        (mRegUnpairMoveOp 4 (mRegHeader05Op regs))))) :=
  mRegSpineEval_trans mRegSpineEval_0_5 <|
  mRegSpineEval_trans mRegSpineEval_5_7 <|
  mRegSpineEval_trans mRegSpineEval_7_9 <|
  mRegSpineEval_trans mRegSpineEval_9_11 <|
  mRegSpineEval_11_13

theorem mUnpair_header_eval {slot : PAM M} {regs : List (PAM M)}
    (hLog : MZfLogInv slot [] regs) (hInv : MRegsInv regs) :
    let prooflist₁ := if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1
    let nextproof' := if regs.getD 0 0 = 0 then regs.getD 1 0 + 1 else regs.getD 1 0
    let u1 := mUnpair prooflist₁
    let ac := u1.1
    let u2 := mUnpair u1.2
    let p1 := u2.1
    let u3 := mUnpair u2.2
    let p2 := u3.1
    let u4 := mUnpair u3.2
    let p3 := u4.1
    let prooflist' := u4.2
    let regs₁₃ := mWffStateToRegs prooflist' nextproof'
      ⟨regs.getD 2 0, regs.getD 3 0, ac, p1, p2, p3⟩
    ∃ slot' : PAM M,
      MZfLogInv slot' (List.replicate 13 1) regs₁₃ ∧
      mReachPos (mZfLogCfg slot [] regs) (mZfLogCfg slot' (List.replicate 13 1) regs₁₃) := by
  dsimp only
  obtain ⟨_, slot', hinv', hreach⟩ := mRegSpineEval_0_13 slot regs hLog
  dsimp only [List.replicate] at hinv' hreach
  have h05 : mRegHeader05Op regs =
      [if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1,
       if regs.getD 0 0 = 0 then regs.getD 1 0 + 1 else regs.getD 1 0,
       regs.getD 2 0, regs.getD 3 0, 0, 0, 0, 0, 0, 0, 0] := by
    conv_lhs => rw [mRegs_eq_of_mRegsInv hInv]
    exact mRegHeader05Op_eval _ _ _ _ _ _ _ _
  have h13 : mRegUnpairMoveOp 7 (mRegUnpairMoveOp 6 (mRegUnpairMoveOp 5
      (mRegUnpairMoveOp 4 (mRegHeader05Op regs)))) =
      mWffStateToRegs
        (mUnpair (mUnpair (mUnpair (mUnpair
          (if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1)).2).2).2).2
        (if regs.getD 0 0 = 0 then regs.getD 1 0 + 1 else regs.getD 1 0)
        ⟨regs.getD 2 0, regs.getD 3 0,
         (mUnpair (if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1)).1,
         (mUnpair (mUnpair (if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1)).2).1,
         (mUnpair (mUnpair (mUnpair
           (if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1)).2).2).1,
         (mUnpair (mUnpair (mUnpair (mUnpair
           (if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1)).2).2).2).1⟩ := by
    rw [h05]
    simp [mRegUnpairMoveOp, mReg269Op_eval, mWffStateToRegs, List.getD]
  rw [h13] at hinv' hreach
  exact ⟨slot', hinv', hreach⟩

theorem mSpine_0_123_eval {slot : PAM M} {regs : List (PAM M)}
    (hLog : MZfLogInv slot [] regs) (hInv : MRegsInv regs) :
    let prooflist₁ := if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1
    let nextproof' := if regs.getD 0 0 = 0 then regs.getD 1 0 + 1 else regs.getD 1 0
    let u1 := mUnpair prooflist₁
    let ac := u1.1
    let u2 := mUnpair u1.2
    let p1 := u2.1
    let u3 := mUnpair u2.2
    let p2 := u3.1
    let u4 := mUnpair u3.2
    let p3 := u4.1
    let prooflist' := u4.2
    let out := mRpnZf393AllClauses (regs.getD 2 0) (regs.getD 3 0) ac p1 p2 p3
    let regs' := mWffStateToRegs prooflist' nextproof' out
    ∃ slot' : PAM M,
      MZfLogInv slot' (List.replicate 123 1) regs' ∧
      mReachPos (mZfLogCfg slot [] regs) (mZfLogCfg slot' (List.replicate 123 1) regs') := by
  dsimp only
  obtain ⟨slot₁, hinv₁, hreach₁⟩ := mUnpair_header_eval hLog hInv
  obtain ⟨slot₂, hinv₂, hreach₂⟩ := mWffSpineEval_13_123 slot₁ _ _ _ hinv₁
  exact ⟨slot₂, hinv₂, mReachPos_trans hreach₁ hreach₂⟩

theorem mHalt_check_eval {slot : PAM M} {regs : List (PAM M)}
    (hinv : MZfLogInv slot (List.replicate 123 1) regs) :
    (regs.getD 2 0 = 1 →
      mHaltsFrom zf393 (mZfLogCfg slot (List.replicate 123 1) regs)) ∧
    (regs.getD 2 0 ≠ 1 →
      ∃ slot' : PAM M,
        MZfLogInv slot' [] regs ∧
        mReachPos (mZfLogCfg slot (List.replicate 123 1) regs) (mZfLogCfg slot' [] regs)) := by
  constructor
  · intro h1
    have h01 : regs.getD 2 0 = (0 : PAM M) + 1 := by rw [h1, zero_add]
    obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_succ hinv evalStack_spine_123 h01
    have hz : (regs.set 2 0).getD 2 0 = 0 := mGetD_set_self regs 2 0 (by rw [hinv.1]; decide)
    obtain ⟨slot₂, hinv₂, hreach₂⟩ := mLogStep_of_decnz_zero hinv₁ evalStack_spine_124 hz
    have hhalt := mLogStep_of_halt hinv₂ evalStack_spine_125
    obtain ⟨s, _, htr⟩ := mReachPos_trans hreach₁ hreach₂
    exact (mHaltsFrom_iff_of_mTracesTo htr).mpr hhalt
  · intro hne1
    rcases eq_zero_or_exists_succ (regs.getD 2 0) with hv0 | ⟨u, hu⟩
    · exact mLogStep_of_decnz_zero hinv evalStack_spine_123 hv0
    · rcases eq_zero_or_exists_succ u with rfl | ⟨v, rfl⟩
      · rw [zero_add] at hu
        exact absurd hu hne1
      · obtain ⟨slot₁, hinv₁, hreach₁⟩ := mLogStep_of_decnz_succ hinv evalStack_spine_123 hu
        have hv1 : (regs.set 2 (v + 1)).getD 2 0 = v + 1 :=
          mGetD_set_self regs 2 (v + 1) (by rw [hinv.1]; decide)
        obtain ⟨slot₂, hinv₂, hreach₂⟩ := mLogStep_of_decnz_succ hinv₁ evalStack_spine_124 hv1
        rw [List.set_set] at hinv₂ hreach₂
        have h224 : walkInternal 99 (List.replicate 124 1 ++ [0]) = some 224 :=
          walkInternal_snoc walkInternal_spine_124 rfl (by decide)
        have h225 : walkInternal 99 (List.replicate 124 1 ++ [0] ++ [1]) = some 225 :=
          walkInternal_snoc h224 rfl (by decide)
        have h288 : walkInternal 99 (List.replicate 124 1 ++ [0] ++ [1] ++ [0]) = some 288 :=
          walkInternal_snoc h225 rfl (by decide)
        have hinv288 : MZfLogInv slot₂
            (trimZeros (List.replicate 124 1 ++ [0] ++ [1] ++ [0])) (regs.set 2 v) := by
          rwa [trimZeros_append_zero, trimZeros_append_one]
        obtain ⟨_, slot₃, hinv₃, hreach₃⟩ := mSubEval_288
          (List.replicate 124 1 ++ [0] ++ [1] ++ [0]) h288 slot₂ (regs.set 2 v) hinv288
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hreach₃
        rw [retStack_append_zero] at hinv₃
        dsimp only at hinv₃ hreach₃
        have hv2 : v + 2 = v + 1 + 1 := by ring
        rw [mGetD_set_self regs 2 v (by rw [hinv.1]; decide), List.set_set, hv2,
          mSet_eq_self_of_getD_eq hu] at hinv₃ hreach₃
        obtain ⟨slot₄, hinv₄, hreach₄⟩ := mLogStep_of_jump hinv₃ evalStack_225_break
        exact ⟨slot₄, hinv₄, mReachPos_trans hreach₁
          (mReachPos_trans hreach₂ (mReachPos_trans hreach₃ hreach₄))⟩

theorem mSpine_body_eval {slot : PAM M} {regs : List (PAM M)}
    (hLog : MZfLogInv slot [] regs) (hInv : MRegsInv regs) :
    ∃ (slot' : PAM M) (regs' : List (PAM M)),
      MZfLogInv slot' (List.replicate 123 1) regs' ∧
      MRegsInv regs' ∧
      mRegsToMainCfg regs' = mZf393MainNext (mRegsToMainCfg regs) ∧
      mReachPos (mZfLogCfg slot [] regs) (mZfLogCfg slot' (List.replicate 123 1) regs') := by
  obtain ⟨slot', hinv', hreach⟩ := mSpine_0_123_eval hLog hInv
  refine ⟨slot', _, hinv', ⟨rfl, rfl, rfl, rfl⟩, ?_, hreach⟩
  let pl1 := if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1
  let ac := (mUnpair pl1).1
  let u2 := mUnpair (mUnpair pl1).2
  let p1 := u2.1
  let u3 := mUnpair u2.2
  let p2 := u3.1
  let p3 := (mUnpair u3.2).1
  have h := mRpnZf393AllClauses_eq_mZf393ClauseDispatch
    (regs.getD 2 0) (regs.getD 3 0) ac p1 p2 p3
  dsimp only at h
  rw [Prod.mk.injEq] at h
  have hcfg : ∀ (pl np : PAM M) (st : MWffState M),
      mRegsToMainCfg (mWffStateToRegs pl np st) = ⟨pl, np, st.topwff, st.wffstack⟩ :=
    fun _ _ _ ↦ rfl
  rw [hcfg, h.1, h.2]
  rfl

theorem mMain_iter_sim {slot : PAM M} {regs : List (PAM M)}
    (hLog : MZfLogInv slot [] regs) (hInv : MRegsInv regs) :
    match mZf393MainStep (mRegsToMainCfg regs) with
    | none =>
      mHaltsFrom zf393 (mZfLogCfg slot [] regs)
    | some c' =>
      ∃ (slot' : PAM M) (regs' : List (PAM M)),
        MZfLogInv slot' [] regs' ∧
        MRegsInv regs' ∧
        mRegsToMainCfg regs' = c' ∧
        mReachPos (mZfLogCfg slot [] regs) (mZfLogCfg slot' [] regs') := by
  obtain ⟨slot₁, regs', hLog₁, hInv', hnext, hreach₁⟩ := mSpine_body_eval hLog hInv
  have htop_eq : (mZf393MainNext (mRegsToMainCfg regs)).topwff = regs'.getD 2 0 := by
    rw [← hnext]; rfl
  have hhalt := mHalt_check_eval hLog₁
  unfold mZf393MainStep
  by_cases h1 : (mZf393MainNext (mRegsToMainCfg regs)).topwff = 1
  · simp only [h1, ↓reduceIte]
    rw [htop_eq] at h1
    obtain ⟨s₁, _, htr₁⟩ := hreach₁
    exact (mHaltsFrom_iff_of_mTracesTo htr₁).mpr (hhalt.1 h1)
  · simp only [h1, ↓reduceIte]
    rw [htop_eq] at h1
    obtain ⟨slot₂, hLog₂, hreach₂⟩ := hhalt.2 h1
    exact ⟨slot₂, regs', hLog₂, hInv', hnext, mReachPos_trans hreach₁ hreach₂⟩

/-! ## Section 7: $\beta$-Coded `main()` Traces and Bidirectional Halting Equivalence in `PAM M` -/

noncomputable def mPackMainCfg (c : MZfMainCfg M) : PAM M :=
  mPair c.prooflist (mPair c.nextproof (mPair c.topwff c.wffstack))

noncomputable def mUnpackMainCfg (z : PAM M) : MZfMainCfg M :=
  let u1 := mUnpair z
  let u2 := mUnpair u1.2
  let u3 := mUnpair u2.2
  ⟨u1.1, u2.1, u3.1, u3.2⟩

@[simp]
theorem mUnpackMainCfg_mPackMainCfg (c : MZfMainCfg M) :
    mUnpackMainCfg (mPackMainCfg c) = c := by
  cases c
  simp [mPackMainCfg, mUnpackMainCfg]

@[simp]
theorem mPackMainCfg_mUnpackMainCfg (z : PAM M) :
    mPackMainCfg (mUnpackMainCfg z) = z := by
  simp [mPackMainCfg, mUnpackMainCfg]

theorem mPackMainCfg_injective {c₁ c₂ : MZfMainCfg M}
    (h : mPackMainCfg c₁ = mPackMainCfg c₂) : c₁ = c₂ := by
  have h' := congrArg mUnpackMainCfg h
  simpa using h'

theorem mZf393MainStep_eq_some_iff {c c' : MZfMainCfg M} :
    mZf393MainStep c = some c' ↔
      (mZf393MainNext c).topwff ≠ 1 ∧ c' = mZf393MainNext c := by
  unfold mZf393MainStep
  split_ifs with h1 <;> simp [h1, eq_comm]

theorem paFun_mZfEq {k : ℕ} {fx fy : (Fin k → PAM M) → PAM M}
    (hx : PAFunN k fx) (hy : PAFunN k fy) :
    PAFunN k (fun u ↦ mZfEq (fx u) (fy u)) :=
  paFun_mPair (paFun_mPair hx hy) (paFun_const 0)

theorem paFun_mZfMem {k : ℕ} {fx fy : (Fin k → PAM M) → PAM M}
    (hx : PAFunN k fx) (hy : PAFunN k fy) :
    PAFunN k (fun u ↦ mZfMem (fx u) (fy u)) :=
  paFun_mPair (paFun_mPair hx hy) (paFun_const 1)

theorem paFun_mZfImp {k : ℕ} {fφ fψ : (Fin k → PAM M) → PAM M}
    (hφ : PAFunN k fφ) (hψ : PAFunN k fψ) :
    PAFunN k (fun u ↦ mZfImp (fφ u) (fψ u)) :=
  paFun_mPair (paFun_mPair hφ hψ) (paFun_const 2)

theorem paFun_mZfNot {k : ℕ} {fφ : (Fin k → PAM M) → PAM M} (hφ : PAFunN k fφ) :
    PAFunN k (fun u ↦ mZfNot (fφ u)) :=
  paFun_mPair hφ (paFun_const 3)

theorem paFun_mZfAll {k : ℕ} {fx fφ : (Fin k → PAM M) → PAM M}
    (hx : PAFunN k fx) (hφ : PAFunN k fφ) :
    PAFunN k (fun u ↦ mZfAll (fx u) (fφ u)) :=
  paFun_mPair (paFun_mPair hx hφ) (paFun_const 4)

theorem paFun_mZfEx {k : ℕ} {fx fφ : (Fin k → PAM M) → PAM M}
    (hx : PAFunN k fx) (hφ : PAFunN k fφ) :
    PAFunN k (fun u ↦ mZfEx (fx u) (fφ u)) :=
  paFun_mZfNot (paFun_mZfAll hx (paFun_mZfNot hφ))

theorem paFun_mZfAnd {k : ℕ} {fφ fψ : (Fin k → PAM M) → PAM M}
    (hφ : PAFunN k fφ) (hψ : PAFunN k fψ) :
    PAFunN k (fun u ↦ mZfAnd (fφ u) (fψ u)) :=
  paFun_mZfNot (paFun_mZfImp hφ (paFun_mZfNot hψ))

theorem paFun_mZf393ClauseDispatch {k : ℕ}
    {ftop fstk fac fp1 fp2 fp3 : (Fin k → PAM M) → PAM M}
    (htop : PAFunN k ftop) (hstk : PAFunN k fstk) (hac : PAFunN k fac)
    (hp1 : PAFunN k fp1) (hp2 : PAFunN k fp2) (hp3 : PAFunN k fp3) :
    PAFunN k (fun u ↦
      (mZf393ClauseDispatch (ftop u) (fstk u) (fac u) (fp1 u) (fp2 u) (fp3 u)).1) ∧
    PAFunN k (fun u ↦
      (mZf393ClauseDispatch (ftop u) (fstk u) (fac u) (fp1 u) (fp2 u) (fp3 u)).2) := by
  have hstk0 : PAFunN k (fun u ↦ mPair (ftop u) (fstk u)) := paFun_mPair htop hstk
  have hpop1_1 := paFun_mUnpair_fst hstk0
  have hpop1_2 := paFun_mUnpair_snd hstk0
  have hpop2_1 := paFun_mUnpair_fst hpop1_2
  have hpop2_2 := paFun_mUnpair_snd hpop1_2
  have hrep : PAFunN k (fun u ↦ mAxRep (fp1 u)) := by
    have hrhs : PAFunN k (fun u ↦ mAxRepRhs (fp1 u)) :=
      paFun_mZfEx (paFun_const 3)
        (paFun_mZfAnd (paFun_mZfMem (paFun_const 3) (paFun_const 0))
          (paFun_mZfAll (paFun_const 1) hp1))
    exact paFun_mZfImp
      (paFun_mZfAll (paFun_const 3)
        (paFun_mZfEx (paFun_const 1)
          (paFun_mZfAll (paFun_const 2)
            (paFun_mZfImp (paFun_mZfAll (paFun_const 1) hp1)
              (paFun_mZfEq (paFun_const 2) (paFun_const 1))))))
      (paFun_mZfEx (paFun_const 1)
        (paFun_mZfAll (paFun_const 2)
          (paFun_mZfAnd
            (paFun_mZfImp (paFun_mZfMem (paFun_const 2) (paFun_const 1)) hrhs)
            (paFun_mZfImp hrhs (paFun_mZfMem (paFun_const 2) (paFun_const 1))))))
  have hb1 : PAFunN k (fun u ↦ mAxB1 (fp1 u) (fp2 u) (fp3 u)) :=
    paFun_mZfImp (paFun_mZfImp hp1 hp2) (paFun_mZfImp (paFun_mZfImp hp2 hp3) (paFun_mZfImp hp1 hp3))
  have hb2 : PAFunN k (fun u ↦ mAxB2 (fp1 u)) :=
    paFun_mZfImp (paFun_mZfImp (paFun_mZfNot hp1) hp1) hp1
  have hb3 : PAFunN k (fun u ↦ mAxB3 (fp1 u) (fp2 u)) :=
    paFun_mZfImp hp1 (paFun_mZfImp (paFun_mZfNot hp1) hp2)
  have hb4 : PAFunN k (fun u ↦ mAxB4 (fp1 u) (fp2 u) (fp3 u)) :=
    paFun_mZfImp (paFun_mZfAll hp1 (paFun_mZfImp hp2 hp3))
      (paFun_mZfImp (paFun_mZfAll hp1 hp2) (paFun_mZfAll hp1 hp3))
  have hb6a : PAFunN k (fun u ↦ mAxB6a (fp1 u) (fp2 u) (fp3 u)) :=
    paFun_mZfAnd
      (paFun_mZfImp (paFun_mZfEq hp1 hp2) (paFun_mZfAll hp3 (paFun_mZfEq hp1 hp2)))
      (paFun_mZfImp (paFun_mZfMem hp1 hp2) (paFun_mZfAll hp3 (paFun_mZfMem hp1 hp2)))
  have hb6b : PAFunN k (fun u ↦ mAxB6b (fp1 u) (fp2 u) (fp3 u)) :=
    paFun_mZfImp (paFun_mZfAll hp1 (paFun_mZfAll hp2 hp3))
      (paFun_mZfAll hp2 (paFun_mZfAll hp1 hp3))
  have hb6c : PAFunN k (fun u ↦ mAxB6c (fp1 u) (fp2 u)) :=
    paFun_mZfImp (paFun_mZfEx hp1 (paFun_mZfAll hp1 hp2)) hp2
  have hb7 : PAFunN k (fun u ↦ mAxB7 (fp1 u) (fp2 u)) := paFun_mZfEx hp1 (paFun_mZfEq hp1 hp2)
  have hb8a : PAFunN k (fun u ↦ mAxB8a (fp1 u) (fp2 u) (fp3 u)) :=
    paFun_mZfImp (paFun_mZfEq hp1 hp2) (paFun_mZfImp (paFun_mZfEq hp1 hp3) (paFun_mZfEq hp2 hp3))
  have hb8b : PAFunN k (fun u ↦ mAxB8b (fp1 u) (fp2 u) (fp3 u)) :=
    paFun_mZfImp (paFun_mZfEq hp1 hp2)
      (paFun_mZfImp (paFun_mZfMem hp1 hp3) (paFun_mZfMem hp2 hp3))
  have hb8c : PAFunN k (fun u ↦ mAxB8c (fp1 u) (fp2 u) (fp3 u)) :=
    paFun_mZfImp (paFun_mZfEq hp1 hp2)
      (paFun_mZfImp (paFun_mZfMem hp3 hp1) (paFun_mZfMem hp3 hp2))
  have h7_1 := paFun_ite (paDef_or (paDef_eq hp1 hp3) (paDef_eq hp2 hp3)) (paFun_const 0) hb6a
  have h16_1 := paFun_ite (paDef_eq (paFun_mZfImp hpop1_1 hp1) hpop2_1) hp1 (paFun_const 0)
  have h17_1 := paFun_mZfAll hp1 hpop1_1
  have eqc : ∀ n : ℕ, PADefN k (fun u ↦ fac u = ((n : ℕ) : PAM M)) :=
    fun n ↦ paDef_eq hac (paFun_const ((n : ℕ) : PAM M))
  constructor
  · refine paFunN_congr (fun u ↦ ?_)
      (paFun_ite (eqc 0) (paFun_const 0) <|
       paFun_ite (eqc 1) hrep <|
       paFun_ite (eqc 2) (paFun_const mAxPow) <|
       paFun_ite (eqc 3) hb2 <|
       paFun_ite (eqc 4) (paFun_const mAxUni) <|
       paFun_ite (eqc 5) hb3 <|
       paFun_ite (eqc 6) hb8b <|
       paFun_ite (eqc 7) h7_1 <|
       paFun_ite (eqc 8) hb6b <|
       paFun_ite (eqc 9) hb7 <|
       paFun_ite (eqc 10) hb4 <|
       paFun_ite (eqc 11) hb8a <|
       paFun_ite (eqc 12) hb8b <|
       paFun_ite (eqc 13) hb8c <|
       paFun_ite (eqc 14) hb1 <|
       paFun_ite (eqc 15) (paFun_const mAxExt) <|
       paFun_ite (eqc 16) h16_1 <|
       paFun_ite (eqc 17) h17_1 <|
       paFun_ite (eqc 18) hb6b <|
       paFun_ite (eqc 19) hb6c <|
       paFun_const mAxInf)
    unfold mZf393ClauseDispatch
    dsimp only [eqc]
    by_cases c0 : fac u = ((0 : ℕ) : PAM M); · simp only [c0, ↓reduceIte]
    simp only [c0, ↓reduceIte]
    by_cases c1 : fac u = ((1 : ℕ) : PAM M); · simp only [c1, ↓reduceIte]
    simp only [c1, ↓reduceIte]
    by_cases c2 : fac u = ((2 : ℕ) : PAM M); · simp only [c2, ↓reduceIte]
    simp only [c2, ↓reduceIte]
    by_cases c3 : fac u = ((3 : ℕ) : PAM M); · simp only [c3, ↓reduceIte]
    simp only [c3, ↓reduceIte]
    by_cases c4 : fac u = ((4 : ℕ) : PAM M); · simp only [c4, ↓reduceIte]
    simp only [c4, ↓reduceIte]
    by_cases c5 : fac u = ((5 : ℕ) : PAM M); · simp only [c5, ↓reduceIte]
    simp only [c5, ↓reduceIte]
    by_cases c6 : fac u = ((6 : ℕ) : PAM M); · simp only [c6, ↓reduceIte]
    simp only [c6, ↓reduceIte]
    by_cases c7 : fac u = ((7 : ℕ) : PAM M)
    · simp only [c7, ↓reduceIte]
      by_cases c7i : fp1 u = fp3 u ∨ fp2 u = fp3 u <;> simp only [c7i, ↓reduceIte]
    simp only [c7, ↓reduceIte]
    by_cases c8 : fac u = ((8 : ℕ) : PAM M); · simp only [c8, ↓reduceIte]
    simp only [c8, ↓reduceIte]
    by_cases c9 : fac u = ((9 : ℕ) : PAM M); · simp only [c9, ↓reduceIte]
    simp only [c9, ↓reduceIte]
    by_cases c10 : fac u = ((10 : ℕ) : PAM M); · simp only [c10, ↓reduceIte]
    simp only [c10, ↓reduceIte]
    by_cases c11 : fac u = ((11 : ℕ) : PAM M); · simp only [c11, ↓reduceIte]
    simp only [c11, ↓reduceIte]
    by_cases c12 : fac u = ((12 : ℕ) : PAM M); · simp only [c12, ↓reduceIte]
    simp only [c12, ↓reduceIte]
    by_cases c13 : fac u = ((13 : ℕ) : PAM M); · simp only [c13, ↓reduceIte]
    simp only [c13, ↓reduceIte]
    by_cases c14 : fac u = ((14 : ℕ) : PAM M); · simp only [c14, ↓reduceIte]
    simp only [c14, ↓reduceIte]
    by_cases c15 : fac u = ((15 : ℕ) : PAM M); · simp only [c15, ↓reduceIte]
    simp only [c15, ↓reduceIte]
    by_cases c16 : fac u = ((16 : ℕ) : PAM M)
    · simp only [c16, ↓reduceIte]
      by_cases c16i : mZfImp (mUnpair (mPair (ftop u) (fstk u))).1 (fp1 u) =
          (mUnpair (mUnpair (mPair (ftop u) (fstk u))).2).1 <;>
        simp only [c16i, ↓reduceIte]
    simp only [c16, ↓reduceIte]
    by_cases c17 : fac u = ((17 : ℕ) : PAM M); · simp only [c17, ↓reduceIte]
    simp only [c17, ↓reduceIte]
    by_cases c18 : fac u = ((18 : ℕ) : PAM M); · simp only [c18, ↓reduceIte]
    simp only [c18, ↓reduceIte]
    by_cases c19 : fac u = ((19 : ℕ) : PAM M) <;> simp only [c19, ↓reduceIte]
  · refine paFunN_congr (fun u ↦ ?_)
      (paFun_ite (eqc 0) hstk0 <|
       paFun_ite (eqc 1) hstk0 <|
       paFun_ite (eqc 2) hstk0 <|
       paFun_ite (eqc 3) hstk0 <|
       paFun_ite (eqc 4) hstk0 <|
       paFun_ite (eqc 5) hstk0 <|
       paFun_ite (eqc 6) hstk0 <|
       paFun_ite (eqc 7) hstk0 <|
       paFun_ite (eqc 8) hstk0 <|
       paFun_ite (eqc 9) hstk0 <|
       paFun_ite (eqc 10) hstk0 <|
       paFun_ite (eqc 11) hstk0 <|
       paFun_ite (eqc 12) hstk0 <|
       paFun_ite (eqc 13) hstk0 <|
       paFun_ite (eqc 14) hstk0 <|
       paFun_ite (eqc 15) hstk0 <|
       paFun_ite (eqc 16) hpop2_2 <|
       paFun_ite (eqc 17) hpop1_2 <|
       paFun_ite (eqc 18) hstk0 <|
       paFun_ite (eqc 19) hstk0 <|
       hstk0)
    unfold mZf393ClauseDispatch
    dsimp only [eqc]
    by_cases c0 : fac u = ((0 : ℕ) : PAM M); · simp only [c0, ↓reduceIte]
    simp only [c0, ↓reduceIte]
    by_cases c1 : fac u = ((1 : ℕ) : PAM M); · simp only [c1, ↓reduceIte]
    simp only [c1, ↓reduceIte]
    by_cases c2 : fac u = ((2 : ℕ) : PAM M); · simp only [c2, ↓reduceIte]
    simp only [c2, ↓reduceIte]
    by_cases c3 : fac u = ((3 : ℕ) : PAM M); · simp only [c3, ↓reduceIte]
    simp only [c3, ↓reduceIte]
    by_cases c4 : fac u = ((4 : ℕ) : PAM M); · simp only [c4, ↓reduceIte]
    simp only [c4, ↓reduceIte]
    by_cases c5 : fac u = ((5 : ℕ) : PAM M); · simp only [c5, ↓reduceIte]
    simp only [c5, ↓reduceIte]
    by_cases c6 : fac u = ((6 : ℕ) : PAM M); · simp only [c6, ↓reduceIte]
    simp only [c6, ↓reduceIte]
    by_cases c7 : fac u = ((7 : ℕ) : PAM M)
    · simp only [c7, ↓reduceIte]
      by_cases c7i : fp1 u = fp3 u ∨ fp2 u = fp3 u <;> simp only [c7i, ↓reduceIte]
    simp only [c7, ↓reduceIte]
    by_cases c8 : fac u = ((8 : ℕ) : PAM M); · simp only [c8, ↓reduceIte]
    simp only [c8, ↓reduceIte]
    by_cases c9 : fac u = ((9 : ℕ) : PAM M); · simp only [c9, ↓reduceIte]
    simp only [c9, ↓reduceIte]
    by_cases c10 : fac u = ((10 : ℕ) : PAM M); · simp only [c10, ↓reduceIte]
    simp only [c10, ↓reduceIte]
    by_cases c11 : fac u = ((11 : ℕ) : PAM M); · simp only [c11, ↓reduceIte]
    simp only [c11, ↓reduceIte]
    by_cases c12 : fac u = ((12 : ℕ) : PAM M); · simp only [c12, ↓reduceIte]
    simp only [c12, ↓reduceIte]
    by_cases c13 : fac u = ((13 : ℕ) : PAM M); · simp only [c13, ↓reduceIte]
    simp only [c13, ↓reduceIte]
    by_cases c14 : fac u = ((14 : ℕ) : PAM M); · simp only [c14, ↓reduceIte]
    simp only [c14, ↓reduceIte]
    by_cases c15 : fac u = ((15 : ℕ) : PAM M); · simp only [c15, ↓reduceIte]
    simp only [c15, ↓reduceIte]
    by_cases c16 : fac u = ((16 : ℕ) : PAM M)
    · simp only [c16, ↓reduceIte]
      by_cases c16i : mZfImp (mUnpair (mPair (ftop u) (fstk u))).1 (fp1 u) =
          (mUnpair (mUnpair (mPair (ftop u) (fstk u))).2).1 <;>
        simp only [c16i, ↓reduceIte]
    simp only [c16, ↓reduceIte]
    by_cases c17 : fac u = ((17 : ℕ) : PAM M); · simp only [c17, ↓reduceIte]
    simp only [c17, ↓reduceIte]
    by_cases c18 : fac u = ((18 : ℕ) : PAM M); · simp only [c18, ↓reduceIte]
    simp only [c18, ↓reduceIte]
    by_cases c19 : fac u = ((19 : ℕ) : PAM M) <;> simp only [c19, ↓reduceIte]

theorem paFun_mZf393MainNextParts {k : ℕ} {fz : (Fin k → PAM M) → PAM M}
    (hz : PAFunN k fz) :
    PAFunN k (fun u ↦ mPackMainCfg (mZf393MainNext (mUnpackMainCfg (fz u)))) ∧
    PAFunN k (fun u ↦ (mZf393MainNext (mUnpackMainCfg (fz u))).topwff) := by
  have hpl := paFun_mUnpair_fst hz
  have hu1_2 := paFun_mUnpair_snd hz
  have hnp := paFun_mUnpair_fst hu1_2
  have hu2_2 := paFun_mUnpair_snd hu1_2
  have htop := paFun_mUnpair_fst hu2_2
  have hstk := paFun_mUnpair_snd hu2_2
  have hpl0 : PADefN k (fun u ↦ (mUnpair (fz u)).1 = 0) := paDef_eq hpl (paFun_const 0)
  have hpl1 := paFun_ite hpl0 hnp (paFun_sub hpl (paFun_const 1))
  have hnp' := paFun_ite hpl0 (paFun_add hnp (paFun_const 1)) hnp
  have hac := paFun_mUnpair_fst hpl1
  have hv1 := paFun_mUnpair_snd hpl1
  have hp1 := paFun_mUnpair_fst hv1
  have hv2 := paFun_mUnpair_snd hv1
  have hp2 := paFun_mUnpair_fst hv2
  have hv3 := paFun_mUnpair_snd hv2
  have hp3 := paFun_mUnpair_fst hv3
  have hpl' := paFun_mUnpair_snd hv3
  obtain ⟨hres1, hres2⟩ := paFun_mZf393ClauseDispatch htop hstk hac hp1 hp2 hp3
  exact ⟨paFun_mPair hpl' (paFun_mPair hnp' (paFun_mPair hres1 hres2)), hres1⟩

/-- $\beta$-coded execution trace of `mZf393MainStep` of length `n` from `a` to `b`. -/
def MValidMainTrace (n tc td : PAM M) (a b : MZfMainCfg M) : Prop :=
  mBeta tc td 0 = mPackMainCfg a ∧
  (∀ i < n, mZf393MainStep (mUnpackMainCfg (mBeta tc td i)) =
    some (mUnpackMainCfg (mBeta tc td (i + 1)))) ∧
  mBeta tc td n = mPackMainCfg b

def mMainTracesTo (n : PAM M) (a b : MZfMainCfg M) : Prop :=
  ∃ tc td : PAM M, MValidMainTrace n tc td a b

theorem mMainTracesTo_zero (a : MZfMainCfg M) : mMainTracesTo 0 a a :=
  ⟨mPackMainCfg a, mPackMainCfg a + 1, mBeta_singleton _,
   fun _ hi ↦ absurd hi (not_lt_zero_pam _), mBeta_singleton _⟩

theorem mMainTracesTo_snoc {n : PAM M} {a b c : MZfMainCfg M}
    (htr : mMainTracesTo n a b) (hst : mZf393MainStep b = some c) :
    mMainTracesTo (n + 1) a c := by
  rcases htr with ⟨tc, td, h0, hstep, hn⟩
  obtain ⟨tc', td', hprev, hlast⟩ := mBeta_snoc (n + 1) tc td (mPackMainCfg c)
  refine ⟨tc', td', ?_, ?_, hlast⟩
  · rw [hprev 0 ⟨n, by ring⟩, h0]
  · intro i hi
    rcases le_iff_lt_or_eq.mp (lt_add_one_iff_le.mp hi) with hilt | rfl
    · rw [hprev i (lt_trans hilt (lt_succ_self_pam n)),
        hprev (i + 1) (add_lt_add_right_pam hilt 1)]
      exact hstep i hilt
    · rw [hprev i (lt_succ_self_pam i), hn, mUnpackMainCfg_mPackMainCfg, hlast,
        mUnpackMainCfg_mPackMainCfg]
      exact hst

theorem mMainTracesTo_one {a b : MZfMainCfg M} (hst : mZf393MainStep a = some b) :
    mMainTracesTo 1 a b := by
  simpa using mMainTracesTo_snoc (mMainTracesTo_zero a) hst

theorem mMainTracesTo_trans {n₁ n₂ : PAM M} {a b c : MZfMainCfg M}
    (h₁ : mMainTracesTo n₁ a b) (h₂ : mMainTracesTo n₂ b c) :
    mMainTracesTo (n₁ + n₂) a c := by
  rcases eq_zero_or_exists_succ n₂ with rfl | ⟨m₂, rfl⟩
  · rcases h₂ with ⟨tc₂, td₂, hb₂, _, hc₂⟩
    have hbc : b = c := mPackMainCfg_injective (hb₂.symm.trans hc₂)
    subst hbc
    simpa using h₁
  · rcases h₁ with ⟨c₁, d₁, ha₁, hst₁, hb₁⟩
    rcases h₂ with ⟨c₂, d₂, hb₂, hst₂, hc₂⟩
    obtain ⟨c', d', hleft, hright⟩ := mBeta_concat n₁ c₁ d₁ (m₂ + 1 + 1) c₂ d₂
    refine ⟨c', d', ?_, ?_, ?_⟩
    · rcases eq_zero_or_exists_succ n₁ with rfl | ⟨m₁, rfl⟩
      · have h0 := hright 0 ⟨m₂ + 1, by ring⟩
        rw [zero_add] at h0
        have hab : a = b := mPackMainCfg_injective (ha₁.symm.trans hb₁)
        subst hab
        exact h0.trans hb₂
      · exact (hleft 0 ⟨m₁, by ring⟩).trans ha₁
    · intro i hi
      rcases lt_or_ge i n₁ with hilt | hige
      · rw [hleft i hilt]
        rcases lt_or_eq_of_le (show i + 1 ≤ n₁ from hilt) with hilt1 | hi1_eq
        · rw [hleft (i + 1) hilt1]
          exact hst₁ i hilt
        · have hstep_i := hst₁ i hilt
          rw [hi1_eq] at hstep_i ⊢
          have h0 := hright 0 ⟨m₂ + 1, by ring⟩
          rw [add_zero] at h0
          rw [h0, hb₂, ← hb₁]
          exact hstep_i
      · let j := i - n₁
        have hij : n₁ + j = i := add_sub_of_le_pam hige
        have hjlt : j < m₂ + 1 := by
          rcases hi with ⟨w, hw⟩
          exact ⟨w, (add_left_inj_pam n₁).mp (by
            calc n₁ + (j + 1 + w)
              _ = (n₁ + j) + 1 + w := by ring
              _ = i + 1 + w := by rw [hij]
              _ = n₁ + (m₂ + 1) := hw)⟩
        have hij1 : i + 1 = n₁ + (j + 1) := by rw [← hij]; ring
        rw [← hij, hright j (lt_trans hjlt (lt_succ_self_pam (m₂ + 1))), hij,
          hij1, hright (j + 1) (add_lt_add_right_pam hjlt 1)]
        exact hst₂ j hjlt
    · exact (hright (m₂ + 1) (lt_succ_self_pam (m₂ + 1))).trans hc₂

theorem paDef_mMainTracesTo {k : ℕ} {fn : (Fin k → PAM M) → PAM M}
    {ca cb : (Fin k → PAM M) → MZfMainCfg M}
    (hn : PAFunN k fn)
    (ha : PAFunN k (fun u ↦ mPackMainCfg (ca u)))
    (hb : PAFunN k (fun u ↦ mPackMainCfg (cb u))) :
    PADefN k (fun u ↦ mMainTracesTo (fn u) (ca u) (cb u)) := by
  let tcProj : (Fin (k + 2) → PAM M) → PAM M := fun v ↦ v ⟨k, by omega⟩
  let tdProj : (Fin (k + 2) → PAM M) → PAM M := fun v ↦ v (Fin.last (k + 1))
  have htc : PAFunN (k + 2) tcProj := paFun_proj ⟨k, by omega⟩
  have htd : PAFunN (k + 2) tdProj := paFun_proj (Fin.last (k + 1))
  have hn2 : PAFunN (k + 2) (fun v ↦ fn (Fin.init (Fin.init v))) := paFun_weaken (paFun_weaken hn)
  have ha2 : PAFunN (k + 2) (fun v ↦ mPackMainCfg (ca (Fin.init (Fin.init v)))) :=
    paFun_weaken (paFun_weaken ha)
  have hb2 : PAFunN (k + 2) (fun v ↦ mPackMainCfg (cb (Fin.init (Fin.init v)))) :=
    paFun_weaken (paFun_weaken hb)
  have h0 : PADefN (k + 2) (fun v ↦
      mBeta (tcProj v) (tdProj v) 0 = mPackMainCfg (ca (Fin.init (Fin.init v)))) :=
    paDef_eq (paFun_mBeta htc htd (paFun_const 0)) ha2
  have hlast : PADefN (k + 2) (fun v ↦
      mBeta (tcProj v) (tdProj v) (fn (Fin.init (Fin.init v))) =
        mPackMainCfg (cb (Fin.init (Fin.init v)))) :=
    paDef_eq (paFun_mBeta htc htd hn2) hb2
  have hstep : PADefN (k + 2) (fun v ↦ ∀ i < fn (Fin.init (Fin.init v)),
      mZf393MainStep (mUnpackMainCfg (mBeta (tcProj v) (tdProj v) i)) =
        some (mUnpackMainCfg (mBeta (tcProj v) (tdProj v) (i + 1)))) := by
    let iProj : (Fin (k + 3) → PAM M) → PAM M := fun w ↦ w (Fin.last (k + 2))
    have hi : PAFunN (k + 3) iProj := paFun_proj (Fin.last (k + 2))
    have htc3 := paFun_weaken htc
    have htd3 := paFun_weaken htd
    have hn3 := paFun_weaken hn2
    have hbi := paFun_mBeta htc3 htd3 hi
    have hbi1 := paFun_mBeta htc3 htd3 (paFun_add hi (paFun_const 1))
    obtain ⟨hnextCode, hnextTop⟩ := paFun_mZf393MainNextParts hbi
    refine paDefN_congr (fun v ↦ ?_)
      (paDef_all (paDef_imp (paDef_lt hi hn3)
        (paDef_and (paDef_not (paDef_eq hnextTop (paFun_const 1)))
          (paDef_eq hbi1 hnextCode))))
    simp only [iProj, Fin.snoc_last, Fin.init_snoc]
    refine forall_congr' fun i ↦ imp_congr Iff.rfl ?_
    rw [mZf393MainStep_eq_some_iff]
    exact and_congr Iff.rfl
      ⟨fun h ↦ by simpa using congrArg (mUnpackMainCfg (M := M)) h,
       fun h ↦ by simpa using congrArg (mPackMainCfg (M := M)) h⟩
  refine paDefN_congr (fun u ↦ ?_) (paDef_ex (paDef_ex (paDef_and h0 (paDef_and hstep hlast))))
  constructor
  · rintro ⟨tc, td, hv⟩
    dsimp only [tcProj, tdProj] at hv
    rw [Fin.snoc_last, Fin.init_snoc, Fin.init_snoc,
      fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k), fin_snoc_eq] at hv
    exact ⟨tc, td, hv⟩
  · rintro ⟨tc, td, hv⟩
    refine ⟨tc, td, ?_⟩
    dsimp only [tcProj, tdProj]
    rw [Fin.snoc_last, Fin.init_snoc, Fin.init_snoc,
      fin_snoc_lt _ _ (by omega) (Nat.lt_succ_self k), fin_snoc_eq]
    exact hv

/-- Internal halting predicate for `zf393`'s `main()` loop inside `PAM M`. -/
def MZf393MainHalts (M : Type*) [PAStructure M] [PAModel M] : Prop :=
  ∃ (n : PAM M) (c : MZfMainCfg M), mMainTracesTo n mZfMainInit c ∧ mZf393MainStep c = none

def regsOfAfterN (n : ℕ) (w : Fin (n + 12) → PAM M) : List (PAM M) :=
  List.ofFn (fun i : Fin 11 ↦ w ⟨n + i.val + 1, by omega⟩)

omit [PAModel M] in
theorem paFunRegs_regsOfAfterN (n : ℕ) : PAFunRegs (n + 12) (regsOfAfterN (M := M) n) :=
  paFunRegs_ofFn (fun i ↦ paFun_proj ⟨n + i.val + 1, by omega⟩)

omit [PAStructure M] [PAModel M] in
private theorem regsOfAfterN_finCat {n : ℕ} (a : Fin n → PAM M) (b : Fin 12 → PAM M) :
    regsOfAfterN n (finCat a b) = List.ofFn (fun i : Fin 11 ↦ b i.succ) := by
  unfold regsOfAfterN
  congr 1
  funext i
  have hidx : (⟨n + i.val + 1, by omega⟩ : Fin (n + 12)) =
      ⟨n + i.succ.val, Nat.add_lt_add_left i.succ.isLt n⟩ := by
    ext; dsimp; omega
  rw [hidx, finCat_right]

omit [PAModel M] in
theorem paDef_exists_slot_regs {n : ℕ}
    {P : (Fin n → PAM M) → PAM M → List (PAM M) → Prop}
    (hP : PADefN (n + 12) (fun w ↦
      P (fun i : Fin n ↦ w ⟨i.val, by omega⟩) (w ⟨n, by omega⟩) (regsOfAfterN n w))) :
    PADefN n (fun a ↦ ∃ (slot : PAM M) (regs : List (PAM M)),
      regs.length = 11 ∧ P a slot regs) := by
  refine paDefN_congr (fun a ↦ ?_) (paDef_exists_vec (k := n) (m := 12) hP)
  have ha : ∀ b : Fin 12 → PAM M,
      (fun i : Fin n ↦ finCat a b ⟨i.val, by omega⟩) = a := by
    intro b; funext i; exact finCat_left a b i
  have hb0 : ∀ b : Fin 12 → PAM M, finCat a b ⟨n, by omega⟩ = b 0 := by
    intro b
    have h0 : (⟨n, by omega⟩ : Fin (n + 12)) = ⟨n + (0 : Fin 12).val, by omega⟩ := by ext; simp
    rw [h0, finCat_right]
  constructor
  · rintro ⟨b, hb⟩
    rw [ha b, hb0 b, regsOfAfterN_finCat a b] at hb
    exact ⟨b 0, List.ofFn (fun i : Fin 11 ↦ b i.succ), by simp, hb⟩
  · rintro ⟨slot, regs, hlen, hp⟩
    let b : Fin 12 → PAM M := Fin.cons slot (fun i : Fin 11 ↦ regs.getD i.val 0)
    refine ⟨b, ?_⟩
    rw [ha b, hb0 b, regsOfAfterN_finCat a b]
    have hb_sl : b 0 = slot := rfl
    have hb_rs : List.ofFn (fun i : Fin 11 ↦ b i.succ) = regs := ofFn_getD_eq_self hlen
    rwa [hb_sl, hb_rs]

theorem paFun_mPack_mRegsToMainCfg {n : ℕ} {R : (Fin n → PAM M) → List (PAM M)}
    (hR : PAFunRegs n R) :
    PAFunN n (fun u ↦ mPackMainCfg (mRegsToMainCfg (R u))) :=
  paFun_mPair (paFunRegs_getD hR 0)
    (paFun_mPair (paFunRegs_getD hR 1)
      (paFun_mPair (paFunRegs_getD hR 2) (paFunRegs_getD hR 3)))

/-- Backward simulation in `PAM M`: if `MZf393MainHalts M`, then `Machines.zf393` halts. -/
theorem mHalts_zf393_of_mZf393MainHalts (hMain : MZf393MainHalts M) : mHalts M zf393 := by
  rcases hMain with ⟨N, c_end, ⟨tc, td, htr⟩, hnone⟩
  let root₀ : MCfg 393 M := mZfLogCfg 19 [] (List.replicate 11 (0 : PAM M))
  have hdef : PADef1 (fun k : PAM M ↦ k ≤ N →
      ∃ (slot : PAM M) (regs : List (PAM M)),
        regs.length = 11 ∧
        MZfLogInv slot [] regs ∧
        MRegsInv regs ∧
        mPackMainCfg (mRegsToMainCfg regs) = mBeta tc td k ∧
        mReach root₀ (mZfLogCfg slot [] regs)) := by
    have hR := paFunRegs_regsOfAfterN (M := M) 1
    have hsl : PAFunN 13 (fun w : Fin 13 → PAM M ↦ w ⟨1, by omega⟩) := paFun_proj ⟨1, by omega⟩
    have hk13 : PAFunN 13 (fun w : Fin 13 → PAM M ↦ w ⟨0, by omega⟩) := paFun_proj ⟨0, by omega⟩
    have hex : PADefN 1 (fun a ↦ ∃ (slot : PAM M) (regs : List (PAM M)),
        regs.length = 11 ∧
        MZfLogInv slot [] regs ∧
        MRegsInv regs ∧
        mPackMainCfg (mRegsToMainCfg regs) = mBeta tc td (a 0) ∧
        mReach root₀ (mZfLogCfg slot [] regs)) :=
      paDef_exists_slot_regs (n := 1)
        (paDef_and (paDef_mZfLogInv [] hsl hR)
          (paDef_and (paDef_mRegsInv hR)
            (paDef_and
              (paDef_eq (paFun_mPack_mRegsToMainCfg hR)
                (paFun_mBeta (paFun_const tc) (paFun_const td) hk13))
              (paDef_mReach (paFun_const (mEncodeCfg root₀))
                (paFun_mZfLogCfg_of_regs [] hsl hR)))))
    exact paDef_imp (paDef_le (paFun_proj 0) (paFun_const N)) hex
  have hsim := ind1 hdef
    (fun _ ↦ by
      refine ⟨19, List.replicate 11 0, by simp, mZfLogInv_init, mRegsInv_init, ?_,
        mReach_refl root₀⟩
      have hcfg0 : mRegsToMainCfg (List.replicate 11 (0 : PAM M)) = mZfMainInit := rfl
      rw [hcfg0, htr.1])
    (fun k ih hk1 ↦ by
      have hklt : k < N := hk1
      obtain ⟨slot, regs, _, hLog, hInv, hpack, hreach⟩ := ih (le_of_lt hklt)
      have hcfg_eq : mRegsToMainCfg regs = mUnpackMainCfg (mBeta tc td k) := by
        simpa using congrArg mUnpackMainCfg hpack
      have hstep_k := htr.2.1 k hklt
      rw [← hcfg_eq] at hstep_k
      have hiter := mMain_iter_sim hLog hInv
      rw [hstep_k] at hiter
      obtain ⟨slot', regs', hLog', hInv', hcfg', hreachPos⟩ := hiter
      have hpack' : mPackMainCfg (mRegsToMainCfg regs') = mBeta tc td (k + 1) := by
        rw [hcfg', mPackMainCfg_mUnpackMainCfg]
      exact ⟨slot', regs', hLog'.1, hLog', hInv', hpack',
        mReach_trans hreach (mReachPos_to_mReach hreachPos)⟩)
    N le_rfl
  obtain ⟨slot_end, regs_end, _, hLog_end, hInv_end, hpack_end, ⟨S, htr_end⟩⟩ := hsim
  have hcfg_end : mRegsToMainCfg regs_end = c_end :=
    mPackMainCfg_injective (hpack_end.trans htr.2.2)
  have hiter_end := mMain_iter_sim hLog_end hInv_end
  rw [hcfg_end, hnone] at hiter_end
  exact mHalts_zf393_iff_rootInit.mpr ((mHaltsFrom_iff_of_mTracesTo htr_end).mpr hiter_end)

/-- Forward simulation in `PAM M`: if `Machines.zf393` halts, then `MZf393MainHalts M`. -/
theorem mZf393MainHalts_of_mHalts_zf393 (hTM : mHalts M zf393) : MZf393MainHalts M := by
  let root₀ : MCfg 393 M := mZfLogCfg 19 [] (List.replicate 11 (0 : PAM M))
  obtain ⟨T, c_halt, ⟨tc_tm, td_tm, hv_tm⟩, hnone_tm⟩ := mHalts_zf393_iff_rootInit.mp hTM
  by_contra hno
  have hdef : PADef1 (fun k : PAM M ↦
      ∃ (S slot : PAM M) (regs : List (PAM M)),
        regs.length = 11 ∧
        k ≤ S ∧
        MZfLogInv slot [] regs ∧
        MRegsInv regs ∧
        mMainTracesTo k mZfMainInit (mRegsToMainCfg regs) ∧
        mTracesTo zf393 S root₀ (mZfLogCfg slot [] regs)) := by
    have hR := paFunRegs_regsOfAfterN (M := M) 2
    have hk14 : PAFunN 14 (fun w : Fin 14 → PAM M ↦ w ⟨0, by omega⟩) := paFun_proj ⟨0, by omega⟩
    have hS14 : PAFunN 14 (fun w : Fin 14 → PAM M ↦ w ⟨1, by omega⟩) := paFun_proj ⟨1, by omega⟩
    have hsl14 : PAFunN 14 (fun w : Fin 14 → PAM M ↦ w ⟨2, by omega⟩) := paFun_proj ⟨2, by omega⟩
    have hex2 : PADefN 2 (fun a ↦ ∃ (slot : PAM M) (regs : List (PAM M)),
        regs.length = 11 ∧
        a 0 ≤ a 1 ∧
        MZfLogInv slot [] regs ∧
        MRegsInv regs ∧
        mMainTracesTo (a 0) mZfMainInit (mRegsToMainCfg regs) ∧
        mTracesTo zf393 (a 1) root₀ (mZfLogCfg slot [] regs)) :=
      paDef_exists_slot_regs (n := 2)
        (paDef_and (paDef_le hk14 hS14)
          (paDef_and (paDef_mZfLogInv [] hsl14 hR)
            (paDef_and (paDef_mRegsInv hR)
              (paDef_and
                (paDef_mMainTracesTo hk14 (paFun_const (mPackMainCfg mZfMainInit))
                  (paFun_mPack_mRegsToMainCfg hR))
                (paDef_mTracesTo zf393 hS14 (paFun_const (mEncodeCfg root₀))
                  (paFun_mZfLogCfg_of_regs [] hsl14 hR))))))
    refine paDefN_congr (fun a ↦ ?_) (paDef_ex hex2)
    simp [Fin.snoc]
  have hrun := ind1 hdef
    (by
      refine ⟨0, 19, List.replicate 11 0, by simp, le_rfl, mZfLogInv_init, mRegsInv_init, ?_,
        mTracesTo_zero zf393 root₀⟩
      have hcfg0 : mRegsToMainCfg (List.replicate 11 (0 : PAM M)) = mZfMainInit := rfl
      rw [hcfg0]
      exact mMainTracesTo_zero mZfMainInit)
    (fun k ⟨S, slot, regs, _, hkS, hLog, hInv, hmain_k, htm_k⟩ ↦ by
      have hiter := mMain_iter_sim hLog hInv
      rcases hs : mZf393MainStep (mRegsToMainCfg regs) with _ | c'
      · exact False.elim (hno ⟨k, mRegsToMainCfg regs, hmain_k, hs⟩)
      · rw [hs] at hiter
        obtain ⟨slot', regs', hLog', hInv', hcfg', s, hs1, htr_s⟩ := hiter
        rw [← hcfg'] at hs
        have hk1S : k + 1 ≤ S + s := by
          rcases hkS with ⟨d₁, rfl⟩
          rcases hs1 with ⟨d₂, rfl⟩
          exact ⟨d₁ + d₂, by ring⟩
        exact ⟨S + s, slot', regs', hLog'.1, hk1S, hLog', hInv',
          mMainTracesTo_snoc hmain_k hs, mTracesTo_trans htm_k htr_s⟩)
    (T + 1)
  obtain ⟨S, slot, regs, _, hT1_S, _, _, _, c_s, d_s, hv_s⟩ := hrun
  have hT_lt_S : T < S := hT1_S
  have hag := mValidTrace_agree hv_tm hv_s T le_rfl (le_of_lt hT_lt_S)
  obtain ⟨x, y, hx, _, hst⟩ := hv_s.2.1 T hT_lt_S
  have hxh : x = c_halt := mEncodeCfg_injective (hx.symm.trans (hag.symm.trans hv_tm.2.2))
  subst hxh
  rw [hnone_tm] at hst
  cases hst

/-- Full Layer 1 + Layer 2 equivalence inside an arbitrary `PAModel M`: `Machines.zf393` halts iff
the abstract proof-enumerating register machine `MZf393MainHalts M` halts. -/
theorem mHalts_zf393_iff_mZf393MainHalts : mHalts M zf393 ↔ MZf393MainHalts M :=
  ⟨mZf393MainHalts_of_mHalts_zf393, mHalts_zf393_of_mZf393MainHalts⟩

end ProgramInternal

end ConjectureMachines.Semantics.PA

end
