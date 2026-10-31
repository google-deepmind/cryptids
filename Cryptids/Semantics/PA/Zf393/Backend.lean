/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.PA.Arithmetic
public import Cryptids.Semantics.Zf393.Backend
public import Cryptids.Semantics.Zf393.Program

/-!
# Internal `PA` Layer 1 Backend Verification for `zf_393`

This module internalizes the Layer 1 execution backend of Andrew Wade's 393-state `ZF` consistency
Turing machine `Machines.zf393` inside an arbitrary first-order `PAModel M` via `PAM M`:

1. Binary half-tape and unary-register encodings (`mLB01`, `mAppend`, `mMk'`, `mMkL`, `mRepBit`,
   `mEncodeReg`, `mAppendRegs`, `mRegsTape`, `mRootCfg`, `mZf393RootCfg`, `mZfLogCfg`) and their
   first-order `PAFunN` / `PADefN` definability lemmas.
2. Exact bootstrap lifting (`mBoot_reaches_main0`, `39,773` steps) yielding
   `mHalts M Machines.zf393 ↔ mHaltsFrom Machines.zf393 (mZfLogCfg 19 [] (List.replicate 11 0))`.
3. `PAM.ind1` unary scan lemmas (`mRightScan`, `mLeftScan`), return scans (`mZfScan_rev`,
   `mZfScan_bounce_default`, `mScan_reaches_main0`, `mContinue_k_reaches_main0`,
   `mBreak_k_reaches_main0`), moving `00` selector (`mSel_step_reaches_main0`), register increment
   and decrement gadgets (`mInc_leaf_reaches_main0`, `mDecnz_leaf_reaches_main0`), and the
   1-step logical stack-instruction simulator `mTm_simulates_evalStack`.
-/

@[expose] public section

namespace ConjectureMachines.Semantics.PA

open Turing (Dir)
open StateTransition ConjectureMachines
open ConjectureMachines.Zf393
open ConjectureMachines.Zf393.Layer1
  (prefix190 prefix190_ne_nil boot_reaches_main0
   zfScanState scanZerosOk scanZerosOk_tail
   breakState continueState rawContinueRev
   popBreakRev_length_le scanZerosOk_popBreakRev
   popBreakRev_head_one popBreakRev_overflow
   popBreakRev_replicate_one_append popBreakRev_dropLast_prefix
   popContinueRev_length_le rawContinueRev_length_le
   popContinueRev_eq_zero_rawContinueRev popContinueRev_zero_pad
   continueState_step0 continueState_step1 scanZerosOk_rawContinueRev
   popContinueRev_prefix
   breakSlot breakSlot_ge
   regIncStage3 regDecnzStage3
   regIncStage3_step1 regDecnzStage3_step1 regIncStage3_step0 regDecnzStage3_step0
   leafReg_inc_spec leafReg_decnz_spec
   walkTape_dag_props staysInDag staysInDag_of_walkTape walkTape_extend_zeros
   walkTape_self_on_regLeaf walkTape_slot_tail staysInDag_prefix
   fastWalk_eq_walkTape lookupSmall minSlot zf393Inv_init
   checkSmallStackEntry checkSmallStackEntry_of_lookup minSlot_le_150)
open ConjectureMachines.Zf393.Layer2
  (logLeafReg ten_sub_leafReg_eq_logLeafReg StackInstr evalStack)
open ConjectureMachines.Semantics.Riemann.Layer1
  (fin2_cases default_cons_zero encodeReg encodeRegs regsTape)

section Model
variable {M : Type*} [PAStructure M] [PAModel M]
open PAM

/-! ## Section 1: Arithmetic Helpers, Half-Tape Encodings, and `MCfg` Constructors -/

theorem sub_zero_pam (a : PAM M) : a - 0 = a := by
  rw [sub_eq_iff_eq_add_pam (zero_le_pam a), zero_add]

theorem add_le_add_right_pam {a b : PAM M} (h : a ≤ b) (c : PAM M) : a + c ≤ b + c := by
  rcases h with ⟨d, rfl⟩
  exact ⟨d, by ring⟩

theorem sub_sub_pam (a b c : PAM M) : a - b - c = a - (b + c) := by
  by_cases hbc : b + c ≤ a
  · have hb : b ≤ a := le_trans (le_add_right_pam b c) hbc
    have hab : a - b = c + (a - (b + c)) := by
      rw [sub_eq_iff_eq_add_pam hb]
      calc a
        _ = (b + c) + (a - (b + c)) := (add_sub_of_le_pam hbc).symm
        _ = b + (c + (a - (b + c))) := by ring
    have hc : c ≤ a - b := ⟨a - (b + c), hab.symm⟩
    rw [sub_eq_iff_eq_add_pam hc]
    exact hab
  · have hlt : a < b + c := lt_of_not_ge hbc
    rw [sub_eq_zero_of_le_pam (le_of_lt hlt)]
    have hab_le : a - b ≤ c := by
      by_cases hb : b ≤ a
      · by_contra hgt
        have hlt_ab : c < a - b := lt_of_not_ge hgt
        have := add_lt_add_left_pam hlt_ab b
        rw [add_sub_of_le_pam hb] at this
        exact not_lt_of_ge (le_of_lt hlt) this
      · rw [sub_eq_zero_of_le_pam (le_of_lt (lt_of_not_ge hb))]
        exact zero_le_pam c
    exact sub_eq_zero_of_le_pam hab_le

theorem sub_split_add {s a b : PAM M} (ha : a ≤ b) (hb : b ≤ s) :
    (b - a) + (s - b) = s - a := by
  symm
  rw [sub_eq_iff_eq_add_pam (le_trans ha hb)]
  calc s
    _ = b + (s - b) := (add_sub_of_le_pam hb).symm
    _ = (a + (b - a)) + (s - b) := by rw [add_sub_of_le_pam ha]
    _ = a + ((b - a) + (s - b)) := by ring

theorem sub_add_one_of_lt_pam {a b : PAM M} (h : b < a) :
    a - b = (a - (b + 1)) + 1 := by
  have hb1 : b + 1 ≤ a := h
  rw [sub_eq_iff_eq_add_pam (le_of_lt h)]
  calc a
    _ = (b + 1) + (a - (b + 1)) := (add_sub_of_le_pam hb1).symm
    _ = b + ((a - (b + 1)) + 1) := by ring

theorem add_one_sub_of_le_pam {a b : PAM M} (h : b ≤ a) :
    (a + 1) - b = (a - b) + 1 := by
  rw [sub_eq_iff_eq_add_pam (le_trans h (le_add_right_pam a 1))]
  calc a + 1
    _ = (b + (a - b)) + 1 := by rw [add_sub_of_le_pam h]
    _ = b + ((a - b) + 1) := by ring

/-- Left sentinel half-tape `LB01 = 1 :: 0^ω` encoded in `PAM M`. -/
def mLB01 : PAM M :=
  mCons 1 0

/-- Prepend a finite bit list `xs : List (Fin 2)` onto a half-tape code `R : PAM M`. -/
def mAppend (xs : List (Fin 2)) (R : PAM M) : PAM M :=
  xs.foldr mCons R

@[simp]
theorem mAppend_nil (R : PAM M) : mAppend [] R = R := rfl

@[simp]
theorem mAppend_cons (b : Fin 2) (xs : List (Fin 2)) (R : PAM M) :
    mAppend (b :: xs) R = mCons b (mAppend xs R) := rfl

theorem mAppend_append (xs ys : List (Fin 2)) (R : PAM M) :
    mAppend (xs ++ ys) R = mAppend xs (mAppend ys R) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [ih]

theorem mAppend_snoc (xs : List (Fin 2)) (b : Fin 2) (R : PAM M) :
    mAppend (xs ++ [b]) R = mAppend xs (mCons b R) := by
  rw [mAppend_append, mAppend_cons, mAppend_nil]

theorem mAppend_reverse_cons (xs : List (Fin 2)) (b : Fin 2) (L : PAM M) :
    mCons b (mAppend xs.reverse L) = mAppend (xs ++ [b]).reverse L := by
  simp [List.reverse_append]

theorem mCons_zero_zero : mCons 0 (0 : PAM M) = 0 := by
  simp [mCons]

theorem mAppend_replicate_zero (n : ℕ) (R : PAM M) :
    mAppend (List.replicate n 0) R = mRep0 (n : PAM M) R := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, mAppend_cons, ih, Nat.cast_succ, mRep0_succ]

theorem mAppend_replicate_one (n : ℕ) (R : PAM M) :
    mAppend (List.replicate n 1) R = mRep1 (n : PAM M) R := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, mAppend_cons, ih, Nat.cast_succ, mRep1_succ]

theorem mRep1_inner_cons (r L : PAM M) :
    mRep1 r (mCons 1 L) = mCons 1 (mRep1 r L) := by
  rw [mRep1_mCons_one, mRep1_succ]

theorem mRep0_inner_cons (r L : PAM M) :
    mRep0 r (mCons 0 L) = mCons 0 (mRep0 r L) := by
  rw [mRep0_mCons_zero, mRep0_succ]

/-- Unary `a`-block `a^r :: R` on binary half-tape codes in `PAM M`. -/
noncomputable def mRepBit (a : Fin 2) (r R : PAM M) : PAM M :=
  if a = 0 then mRep0 r R else mRep1 r R

@[simp]
theorem mRepBit_zero_bit (r R : PAM M) : mRepBit 0 r R = mRep0 r R := rfl

@[simp]
theorem mRepBit_one_bit (r R : PAM M) : mRepBit 1 r R = mRep1 r R := rfl

@[simp]
theorem mRepBit_zero_len (a : Fin 2) (R : PAM M) : mRepBit a 0 R = R := by
  rcases fin2_cases a with rfl | rfl <;> simp [mRepBit]

theorem mRepBit_succ (a : Fin 2) (r R : PAM M) :
    mRepBit a (r + 1) R = mCons a (mRepBit a r R) := by
  rcases fin2_cases a with rfl | rfl
  · exact mRep0_succ r R
  · exact mRep1_succ r R

theorem mRepBit_mCons (a : Fin 2) (r R : PAM M) :
    mRepBit a r (mCons a R) = mRepBit a (r + 1) R := by
  rcases fin2_cases a with rfl | rfl
  · exact mRep0_mCons_zero r R
  · exact mRep1_mCons_one r R

theorem mRepBit_add (a : Fin 2) (r₁ r₂ R : PAM M) :
    mRepBit a (r₁ + r₂) R = mRepBit a r₁ (mRepBit a r₂ R) := by
  rcases fin2_cases a with rfl | rfl
  · exact mRep0_add r₁ r₂ R
  · exact mRep1_add r₁ r₂ R

/-- Right-facing `MCfg 393 M`: head stands on `mBit R`, with left `L` and right tail `mHalf R`. -/
noncomputable def mMk' (q : Fin 393) (L R : PAM M) : MCfg 393 M :=
  ⟨q, mBit R, L, mHalf R⟩

/-- Left-facing `MCfg 393 M`: head stands on `mBit L`, with left tail `mHalf L` and right `R`. -/
noncomputable def mMkL (q : Fin 393) (L R : PAM M) : MCfg 393 M :=
  ⟨q, mBit L, mHalf L, R⟩

theorem mMkL_mCons_eq_mMk'_mCons (q : Fin 393) (b : Fin 2) (L R : PAM M) :
    mMkL q (mCons b L) R = mMk' q L (mCons b R) := by
  simp [mMkL, mMk']

theorem mStep_mMk'_none {q : Fin 393} {a : Fin 2} (htr : zf393Trans q a = none)
    (L R : PAM M) :
    mStep zf393 (mMk' q L (mCons a R)) = none := by
  simp [mMk', mStep, htr]

theorem mStep_mMk'_right {q q' : Fin 393} {a b : Fin 2}
    (htr : zf393Trans q a = some (b, .right, q')) (L R : PAM M) :
    mStep zf393 (mMk' q L (mCons a R)) = some (mMk' q' (mCons b L) R) := by
  simp [mMk', mStep, htr]

theorem mStep_mMk'_left {q q' : Fin 393} {a b : Fin 2}
    (htr : zf393Trans q a = some (b, .left, q')) (L R : PAM M) :
    mStep zf393 (mMk' q L (mCons a R)) = some (mMkL q' L (mCons b R)) := by
  simp [mMk', mMkL, mStep, htr]

theorem mStep_mMkL_left {q q' : Fin 393} {a b : Fin 2}
    (htr : zf393Trans q a = some (b, .left, q')) (L R : PAM M) :
    mStep zf393 (mMkL q (mCons a L) R) = some (mMkL q' L (mCons b R)) := by
  simp [mMkL, mStep, htr]

theorem mStep_mMkL_right {q q' : Fin 393} {a b : Fin 2}
    (htr : zf393Trans q a = some (b, .right, q')) (L R : PAM M) :
    mStep zf393 (mMkL q (mCons a L) R) = some (mMk' q' (mCons b L) R) := by
  simp [mMk', mMkL, mStep, htr]

/-- Reachability in `≥ 0` internal `zf393` steps. -/
def mReach (a b : MCfg 393 M) : Prop :=
  ∃ s : PAM M, mTracesTo zf393 s a b

/-- Reachability in `≥ 1` internal `zf393` steps. -/
def mReachPos (a b : MCfg 393 M) : Prop :=
  ∃ s : PAM M, 1 ≤ s ∧ mTracesTo zf393 s a b

theorem mReach_refl (a : MCfg 393 M) : mReach a a :=
  ⟨0, mTracesTo_zero zf393 a⟩

theorem mReachPos_to_mReach {a b : MCfg 393 M} (h : mReachPos a b) : mReach a b :=
  let ⟨s, _, hs⟩ := h
  ⟨s, hs⟩

theorem mReachPos_step {a b : MCfg 393 M} (hst : mStep zf393 a = some b) :
    mReachPos a b :=
  ⟨1, le_rfl, mTracesTo_one hst⟩

theorem mReach_trans {a b c : MCfg 393 M} (h₁ : mReach a b) (h₂ : mReach b c) :
    mReach a c := by
  rcases h₁ with ⟨s₁, hs₁⟩
  rcases h₂ with ⟨s₂, hs₂⟩
  exact ⟨s₁ + s₂, mTracesTo_trans hs₁ hs₂⟩

theorem mReach_mReachPos {a b c : MCfg 393 M} (h₁ : mReach a b) (h₂ : mReachPos b c) :
    mReachPos a c := by
  rcases h₁ with ⟨s₁, hs₁⟩
  rcases h₂ with ⟨s₂, ⟨d, rfl⟩, hs₂⟩
  exact ⟨s₁ + (1 + d), ⟨s₁ + d, by ring⟩, mTracesTo_trans hs₁ hs₂⟩

theorem mReachPos_mReach {a b c : MCfg 393 M} (h₁ : mReachPos a b) (h₂ : mReach b c) :
    mReachPos a c := by
  rcases h₁ with ⟨s₁, ⟨d, rfl⟩, hs₁⟩
  rcases h₂ with ⟨s₂, hs₂⟩
  exact ⟨(1 + d) + s₂, ⟨d + s₂, by ring⟩, mTracesTo_trans hs₁ hs₂⟩

theorem mReachPos_trans {a b c : MCfg 393 M} (h₁ : mReachPos a b) (h₂ : mReachPos b c) :
    mReachPos a c :=
  mReachPos_mReach h₁ (mReachPos_to_mReach h₂)

theorem mStep_mReach {a b c : MCfg 393 M} (hst : mStep zf393 a = some b) (h : mReach b c) :
    mReach a c :=
  mReach_trans (mReachPos_to_mReach (mReachPos_step hst)) h

theorem mStep_mReachPos {a b c : MCfg 393 M} (hst : mStep zf393 a = some b) (h : mReach b c) :
    mReachPos a c :=
  mReachPos_mReach (mReachPos_step hst) h

/-! ## Section 2: First-Order Definability & `PAM.ind1` Unary Scan Lemmas -/

omit [PAModel M] in
theorem paDef_prop {k : ℕ} (P : Prop) : PADefN k (fun _ : Fin k → PAM M ↦ P) := by
  rcases Classical.em P with h | h
  · exact paDefN_congr (fun _ ↦ ⟨fun _ ↦ h, fun _ ↦ trivial⟩) (paDef_true k)
  · exact paDefN_congr (fun _ ↦ ⟨False.elim, fun hp ↦ absurd hp h⟩) (paDef_false k)

theorem paFun_mCons (b : Fin 2) {k : ℕ} {fx : (Fin k → PAM M) → PAM M}
    (hx : PAFunN k fx) : PAFunN k (fun u ↦ mCons b (fx u)) :=
  paFun_add (paFun_mul (paFun_const 2) hx) (paFun_const (b.val : PAM M))

theorem paFun_mAppend (xs : List (Fin 2)) {k : ℕ} {fR : (Fin k → PAM M) → PAM M}
    (hR : PAFunN k fR) : PAFunN k (fun u ↦ mAppend xs (fR u)) := by
  induction xs with
  | nil => exact hR
  | cons b xs ih => exact paFun_mCons b ih

theorem paFun_mRepBit (a : Fin 2) {k : ℕ} {fr fR : (Fin k → PAM M) → PAM M}
    (hr : PAFunN k fr) (hR : PAFunN k fR) :
    PAFunN k (fun u ↦ mRepBit a (fr u) (fR u)) := by
  rcases fin2_cases a with rfl | rfl
  · exact paFun_mRep0 hr hR
  · exact paFun_mRep1 hr hR

theorem paFun_mEncode_mMk' (q : Fin 393) {k : ℕ} {fL fR : (Fin k → PAM M) → PAM M}
    (hL : PAFunN k fL) (hR : PAFunN k fR) :
    PAFunN k (fun u ↦ mEncodeCfg (mMk' q (fL u) (fR u))) := by
  refine paFunN_congr (fun u ↦ ?_)
    (paFun_mPair (paFun_const (q.val : PAM M))
      (paFun_mPair (paFun_mod hR (paFun_const 2))
        (paFun_mPair hL (paFun_div hR (paFun_const 2)))))
  simp [mEncodeCfg, mMk', mBit_val_eq_mod, mHalf]

theorem paFun_mEncode_mMkL (q : Fin 393) {k : ℕ} {fL fR : (Fin k → PAM M) → PAM M}
    (hL : PAFunN k fL) (hR : PAFunN k fR) :
    PAFunN k (fun u ↦ mEncodeCfg (mMkL q (fL u) (fR u))) := by
  refine paFunN_congr (fun u ↦ ?_)
    (paFun_mPair (paFun_const (q.val : PAM M))
      (paFun_mPair (paFun_mod hL (paFun_const 2))
        (paFun_mPair (paFun_div hL (paFun_const 2)) hR)))
  simp [mEncodeCfg, mMkL, mBit_val_eq_mod, mHalf]

theorem paDef_mTracesTo {states : ℕ} (tm : Machine states 2) {k : ℕ}
    {fn : (Fin k → PAM M) → PAM M} {ca cb : (Fin k → PAM M) → MCfg states M}
    (hn : PAFunN k fn)
    (ha : PAFunN k (fun u ↦ mEncodeCfg (ca u)))
    (hb : PAFunN k (fun u ↦ mEncodeCfg (cb u))) :
    PADefN k (fun u ↦ mTracesTo tm (fn u) (ca u) (cb u)) := by
  refine paDefN_congr (fun u ↦ ?_) (paDef_mTracesToCode tm hn ha hb)
  constructor
  · rintro ⟨a₀, b₀, ha₀, hb₀, htr⟩
    rwa [mEncodeCfg_injective ha₀, mEncodeCfg_injective hb₀]
  · intro htr
    exact ⟨ca u, cb u, rfl, rfl, htr⟩

/-- Right-scanning `N : PAM M` copies of `a` into `b` in state `q`. -/
theorem mRightScan {q : Fin 393} {a b : Fin 2}
    (htr : zf393Trans q a = some (b, .right, q)) (N L₀ R₀ : PAM M) :
    mTracesTo zf393 N (mMk' q L₀ (mRepBit a N R₀)) (mMk' q (mRepBit b N L₀) R₀) := by
  have hdef : PADef1 (fun k : PAM M ↦ k ≤ N →
      mTracesTo zf393 k
        (mMk' q L₀ (mRepBit a N R₀))
        (mMk' q (mRepBit b k L₀) (mRepBit a (N - k) R₀))) :=
    paDef_imp (paDef_le (paFun_proj 0) (paFun_const N))
      (paDef_mTracesTo zf393 (paFun_proj 0)
        (paFun_const _)
        (paFun_mEncode_mMk' q
          (paFun_mRepBit b (paFun_proj 0) (paFun_const L₀))
          (paFun_mRepBit a (paFun_sub (paFun_const N) (paFun_proj 0)) (paFun_const R₀))))
  have hall := ind1 hdef ?_ ?_ N le_rfl
  · simpa using hall
  · intro _
    simpa [sub_zero_pam] using mTracesTo_zero zf393 (mMk' q L₀ (mRepBit a N R₀))
  · intro k ih hk1
    have hklt : k < N := hk1
    have htr_k := ih (le_of_lt hklt)
    have hsub := sub_add_one_of_lt_pam hklt
    rw [hsub, mRepBit_succ] at htr_k
    have hst := mStep_mMk'_right htr (mRepBit b k L₀) (mRepBit a (N - (k + 1)) R₀)
    have hb_succ : mCons b (mRepBit b k L₀) = mRepBit b (k + 1) L₀ :=
      (mRepBit_succ b k L₀).symm
    rw [hb_succ] at hst
    exact mTracesTo_snoc htr_k hst

/-- Left-scanning `N : PAM M` copies of `a` into `b` in state `q`. -/
theorem mLeftScan {q : Fin 393} {a b : Fin 2}
    (htr : zf393Trans q a = some (b, .left, q)) (N L₀ R₀ : PAM M) :
    mTracesTo zf393 N (mMkL q (mRepBit a N L₀) R₀) (mMkL q L₀ (mRepBit b N R₀)) := by
  have hdef : PADef1 (fun k : PAM M ↦ k ≤ N →
      mTracesTo zf393 k
        (mMkL q (mRepBit a N L₀) R₀)
        (mMkL q (mRepBit a (N - k) L₀) (mRepBit b k R₀))) :=
    paDef_imp (paDef_le (paFun_proj 0) (paFun_const N))
      (paDef_mTracesTo zf393 (paFun_proj 0)
        (paFun_const _)
        (paFun_mEncode_mMkL q
          (paFun_mRepBit a (paFun_sub (paFun_const N) (paFun_proj 0)) (paFun_const L₀))
          (paFun_mRepBit b (paFun_proj 0) (paFun_const R₀))))
  have hall := ind1 hdef ?_ ?_ N le_rfl
  · simpa using hall
  · intro _
    simpa [sub_zero_pam] using mTracesTo_zero zf393 (mMkL q (mRepBit a N L₀) R₀)
  · intro k ih hk1
    have hklt : k < N := hk1
    have htr_k := ih (le_of_lt hklt)
    have hsub := sub_add_one_of_lt_pam hklt
    rw [hsub, mRepBit_succ] at htr_k
    have hst := mStep_mMkL_left htr (mRepBit a (N - (k + 1)) L₀) (mRepBit b k R₀)
    have hb_succ : mCons b (mRepBit b k R₀) = mRepBit b (k + 1) R₀ :=
      (mRepBit_succ b k R₀).symm
    rw [hb_succ] at hst
    exact mTracesTo_snoc htr_k hst

theorem mRightScan_reach {q : Fin 393} {a b : Fin 2}
    (htr : zf393Trans q a = some (b, .right, q)) (N L₀ R₀ : PAM M) :
    mReach (mMk' q L₀ (mRepBit a N R₀)) (mMk' q (mRepBit b N L₀) R₀) :=
  ⟨N, mRightScan htr N L₀ R₀⟩

theorem mLeftScan_reach {q : Fin 393} {a b : Fin 2}
    (htr : zf393Trans q a = some (b, .left, q)) (N L₀ R₀ : PAM M) :
    mReach (mMkL q (mRepBit a N L₀) R₀) (mMkL q L₀ (mRepBit b N R₀)) :=
  ⟨N, mLeftScan htr N L₀ R₀⟩

/-! ## Section 3: Unary Register Encodings, Root Normal Form, and Bootstrap Lifting -/

/-- Unary register `1^(u + 1) :: 0 :: R` on right half-tapes in `PAM M`. -/
noncomputable def mEncodeReg (u R : PAM M) : PAM M :=
  mRep1 (u + 1) (mCons 0 R)

/-- Reversed unary register `0 :: 1^(u + 1) :: L` on left half-tapes in `PAM M`. -/
noncomputable def mEncodeRegRev (u L : PAM M) : PAM M :=
  mCons 0 (mRep1 (u + 1) L)

/-- Prepend a list of registers `rs : List (PAM M)` onto a right half-tape `R : PAM M`. -/
noncomputable def mAppendRegs (rs : List (PAM M)) (R : PAM M) : PAM M :=
  rs.foldr mEncodeReg R

/-- Prepend the reversed bit-encoding of `rs : List (PAM M)` onto a left half-tape `L : PAM M`. -/
noncomputable def mAppendRegsRev (rs : List (PAM M)) (L : PAM M) : PAM M :=
  rs.reverse.foldr mEncodeRegRev L

/-- Right half-tape encoding of a register list `rs : List (PAM M)` followed by `0^ω`. -/
noncomputable def mRegsTape (rs : List (PAM M)) : PAM M :=
  mAppendRegs rs 0

@[simp]
theorem mAppendRegs_nil (R : PAM M) : mAppendRegs [] R = R := rfl

@[simp]
theorem mAppendRegs_cons (u : PAM M) (rs : List (PAM M)) (R : PAM M) :
    mAppendRegs (u :: rs) R = mEncodeReg u (mAppendRegs rs R) := rfl

theorem mAppendRegs_append (xs ys : List (PAM M)) (R : PAM M) :
    mAppendRegs (xs ++ ys) R = mAppendRegs xs (mAppendRegs ys R) := by
  induction xs with
  | nil => rfl
  | cons u xs ih => simp [ih]

@[simp]
theorem mAppendRegsRev_nil (L : PAM M) : mAppendRegsRev [] L = L := rfl

theorem mAppendRegsRev_snoc (rs : List (PAM M)) (u L : PAM M) :
    mAppendRegsRev (rs ++ [u]) L = mEncodeRegRev u (mAppendRegsRev rs L) := by
  simp [mAppendRegsRev]

theorem mAppendRegsRev_append (xs ys : List (PAM M)) (L : PAM M) :
    mAppendRegsRev (xs ++ ys) L = mAppendRegsRev ys (mAppendRegsRev xs L) := by
  simp [mAppendRegsRev, List.reverse_append, List.foldr_append]

theorem mAppendRegsRev_cons (u : PAM M) (rs : List (PAM M)) (L : PAM M) :
    mAppendRegsRev (u :: rs) L = mAppendRegsRev rs (mEncodeRegRev u L) := by
  simp [mAppendRegsRev]

@[simp]
theorem mRegsTape_nil : mRegsTape ([] : List (PAM M)) = 0 := rfl

@[simp]
theorem mRegsTape_cons (u : PAM M) (rs : List (PAM M)) :
    mRegsTape (u :: rs) = mEncodeReg u (mRegsTape rs) := rfl

theorem mRegsTape_append (xs ys : List (PAM M)) :
    mRegsTape (xs ++ ys) = mAppendRegs xs (mRegsTape ys) :=
  mAppendRegs_append xs ys 0

/-- Embed a standard `List ℕ` register list into `List (PAM M)`. -/
def mCastRegs (ns : List ℕ) : List (PAM M) :=
  ns.map (fun n : ℕ ↦ (n : PAM M))

/-- The 190 fixed unary blocks preceding the 11 active registers in `PAM M`. -/
def mPrefix190 : List (PAM M) :=
  mCastRegs prefix190

theorem mPrefix190_ne_nil : mPrefix190 (M := M) ≠ [] := by
  simp [mPrefix190, mCastRegs, prefix190_ne_nil]

instance mPrefix190_ne_nil_fact : Fact (mPrefix190 (M := M) ≠ []) :=
  ⟨mPrefix190_ne_nil⟩

/-- Canonical configuration at `main().0` (`State 99`) in `MCfg 393 M` (tape register order). -/
noncomputable def mRootCfg (pre : List (PAM M)) (slot : PAM M) (ip : List (Fin 2))
    (regs_tape : List (PAM M)) : MCfg 393 M :=
  mMk' 99 mLB01
    (mAppend ip (mRep0 (slot - (ip.length : PAM M)) (mAppendRegs pre (mRegsTape regs_tape))))

/-- Canonical `zf393` root configuration in tape register order (`0=scratch3 .. 10=prooflist`). -/
noncomputable abbrev mZf393RootCfg (slot : PAM M) (ip : List (Fin 2))
    (regs_tape : List (PAM M)) : MCfg 393 M :=
  mRootCfg mPrefix190 slot ip regs_tape

/-- Canonical `zf393` root configuration in logical register order (`0=prooflist..10=scratch3`). -/
noncomputable def mZfLogCfg (slot : PAM M) (ip : List (Fin 2))
    (regs : List (PAM M)) : MCfg 393 M :=
  mZf393RootCfg slot ip regs.reverse

theorem paFun_mEncodeReg {k : ℕ} {fu fR : (Fin k → PAM M) → PAM M}
    (hu : PAFunN k fu) (hR : PAFunN k fR) :
    PAFunN k (fun a ↦ mEncodeReg (fu a) (fR a)) :=
  paFun_mRep1 (paFun_add hu (paFun_const 1)) (paFun_mCons 0 hR)

theorem paFun_mAppendRegs_const (pre : List (PAM M)) {k : ℕ}
    {fR : (Fin k → PAM M) → PAM M} (hR : PAFunN k fR) :
    PAFunN k (fun a ↦ mAppendRegs pre (fR a)) := by
  induction pre with
  | nil => exact hR
  | cons u pre ih => exact paFun_mEncodeReg (paFun_const u) ih

theorem paFun_mZfLogCfg (ip : List (Fin 2)) {k : ℕ}
    {fslot : (Fin k → PAM M) → PAM M}
    {fregs : Fin 11 → (Fin k → PAM M) → PAM M}
    (hslot : PAFunN k fslot) (hregs : ∀ i : Fin 11, PAFunN k (fregs i)) :
    PAFunN k (fun a ↦
      mEncodeCfg (mZfLogCfg (fslot a) ip (List.ofFn (fun i : Fin 11 ↦ fregs i a)))) := by
  have hregsTape : PAFunN k (fun a ↦
      mRegsTape (List.ofFn (fun i : Fin 11 ↦ fregs i a)).reverse) := by
    have haux : ∀ (idxs : List (Fin 11)),
        PAFunN k (fun a ↦ mRegsTape (idxs.map (fun i ↦ fregs i a))) := by
      intro idxs
      induction idxs with
      | nil => exact paFun_const 0
      | cons i rest ih => exact paFun_mEncodeReg (hregs i) ih
    refine paFunN_congr (fun a ↦ ?_) (haux (List.finRange 11).reverse)
    have hfn : List.ofFn (fun i : Fin 11 ↦ fregs i a) =
        (List.finRange 11).map (fun i ↦ fregs i a) := List.ofFn_eq_map
    rw [hfn, List.map_reverse]
  exact paFun_mEncode_mMk' 99 (paFun_const mLB01)
    (paFun_mAppend ip
      (paFun_mRep0 (paFun_sub hslot (paFun_const (ip.length : PAM M)))
        (paFun_mAppendRegs_const mPrefix190 hregsTape)))

private theorem embedHalf_default : embedHalf (M := M) default = 0 := by
  have h0 : encodeHalf (default : ListBlank (Fin 2)) = 0 := rfl
  simp [embedHalf, h0]

private theorem embedHalf_LB01 : embedHalf (M := M) LB01 = mLB01 := by
  rw [LB01, embedHalf_cons, embedHalf_default]
  rfl

private theorem embedHalf_append (xs : List (Fin 2)) (L : ListBlank (Fin 2)) :
    embedHalf (M := M) (ListBlank.append xs L) = mAppend xs (embedHalf (M := M) L) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change embedHalf (M := M) ((ListBlank.append xs L).cons b) = _
    rw [embedHalf_cons, ih, mAppend_cons]

private theorem mAppend_encodeReg (n : ℕ) (R : PAM M) :
    mAppend (encodeReg n) R = mEncodeReg (n : PAM M) R := by
  unfold encodeReg mEncodeReg
  rw [mAppend_snoc, mAppend_replicate_one, Nat.cast_succ]

private theorem mAppend_encodeRegs (ns : List ℕ) (R : PAM M) :
    mAppend (encodeRegs ns) R = mAppendRegs (mCastRegs ns) R := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    rw [ConjectureMachines.Semantics.Riemann.Layer1.encodeRegs_cons,
      mAppend_append, ih, mAppend_encodeReg]
    rfl

private theorem embedCfg_mk' (q : Fin 393) (L R : ListBlank (Fin 2)) :
    embedCfg (M := M) ⟨q, Tape.mk' L R⟩ =
      mMk' q (embedHalf (M := M) L) (embedHalf (M := M) R) := by
  simp [embedCfg, Tape.mk', mMk', mBit_embedHalf, mHalf_embedHalf]

theorem embedCfg_zf393RootCfg_init :
    embedCfg (M := M) (ConjectureMachines.Zf393.Layer1.zf393RootCfg 19 [] (List.replicate 11 0)) =
      mZfLogCfg 19 [] (List.replicate 11 (0 : PAM M)) := by
  unfold ConjectureMachines.Zf393.Layer1.zf393RootCfg ConjectureMachines.Zf393.Layer1.rootCfg
    mZfLogCfg mZf393RootCfg mRootCfg
  rw [embedCfg_mk', embedHalf_LB01, List.nil_append, List.length_nil, Nat.sub_zero,
    ListBlank.append_assoc, embedHalf_append, embedHalf_append, mAppend_replicate_zero,
    mAppend_encodeRegs]
  unfold regsTape
  rw [embedHalf_append, embedHalf_default, mAppend_encodeRegs]
  have hrep : mCastRegs (M := M) (List.replicate 11 0) =
      (List.replicate 11 (0 : PAM M)).reverse := by
    simp [mCastRegs]
  rw [hrep]
  simp [mPrefix190, mRegsTape, Nat.cast_zero, sub_zero_pam]

/-- In `39,773` internal steps from `mInit`, `Machines.zf393` reaches `mZfLogCfg 19 [] 0^11`. -/
theorem mBoot_reaches_main0 :
    mTracesTo zf393 ((39773 : ℕ) : PAM M) mInit
      (mZfLogCfg 19 [] (List.replicate 11 (0 : PAM M))) := by
  have htr := mTracesTo_of_nSteps (M := M) boot_reaches_main0
  simpa only [embedCfg_init, embedCfg_zf393RootCfg_init] using htr

/-- `Machines.zf393` halts from blank tape in `PAM M` iff it halts from `mZfLogCfg 19 [] 0^11`. -/
theorem mHalts_zf393_iff_rootInit :
    mHalts M zf393 ↔ mHaltsFrom zf393 (mZfLogCfg 19 [] (List.replicate 11 (0 : PAM M))) :=
  mHaltsFrom_iff_of_mTracesTo mBoot_reaches_main0

/-! ## Section 4: Return Scans & Call-Stack Operations (`continue`, `break`) -/

section GenericPrefix
variable {pre : List (PAM M)} [hpre : Fact (pre ≠ [])]

theorem mZfScan_rev (rev : List (Fin 2)) (z : ℕ) (hz : z ≤ 9)
    (hok : scanZerosOk z rev = true) (R : PAM M) :
    ∃ z', z' ≤ 9 ∧
      mReach (mMkL (zfScanState z) (mAppend rev 0) R)
        (mMkL (zfScanState z') 0 (mAppend rev.reverse R)) := by
  induction rev generalizing z R with
  | nil => exact ⟨z, hz, mReach_refl _⟩
  | cons a xs ih =>
    rcases fin2_cases a with rfl | rfl
    · simp only [scanZerosOk] at hok
      by_cases hz9 : 9 ≤ z
      · simp [hz9] at hok
      · simp only [Fin.isValue, BEq.rfl, ↓reduceIte, Bool.ite_false_left, Bool.and_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_le] at hok
        have hz8 : z ≤ 8 := by omega
        have htr0 : zf393Trans (zfScanState z) 0 = some (0, .left, zfScanState (z + 1)) := by
          match z with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl | _ + 9 => omega
        have hstep := mStep_mMkL_left htr0 (mAppend xs 0) R
        obtain ⟨z', hz', hrest⟩ := ih (z + 1) (by omega) hok.2 (mCons 0 R)
        rw [← mAppend_snoc, ← List.reverse_cons] at hrest
        exact ⟨z', hz', mStep_mReach hstep hrest⟩
    · have htr1 : zf393Trans (zfScanState z) 1 = some (1, .left, zfScanState 0) := by
        match z with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl | _ + 10 => omega
      have hstep := mStep_mMkL_left htr1 (mAppend xs 0) R
      obtain ⟨z', hz', hrest⟩ := ih 0 (by decide) hok (mCons 1 R)
      rw [← mAppend_snoc, ← List.reverse_cons] at hrest
      exact ⟨z', hz', mStep_mReach hstep hrest⟩

theorem mZfScan_bounce_default (z : ℕ) (hz : z ≤ 9) (R : PAM M) :
    mReachPos (mMkL (zfScanState z) 0 R) (mMk' 60 0 R) := by
  generalize hd : 9 - z = d
  induction d generalizing z R with
  | zero =>
    have hz9 : z = 9 := by omega
    subst hz9
    have hstep := mStep_mMkL_right (q := zfScanState 9) (q' := 60) (a := 0) (b := 0) (by rfl) 0 R
    simpa only [mCons_zero_zero] using mReachPos_step hstep
  | succ d ih =>
    have hz8 : z ≤ 8 := by omega
    have htr0 : zf393Trans (zfScanState z) 0 = some (0, .left, zfScanState (z + 1)) := by
      match z with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl | _ + 9 => omega
    have h1 : mStep zf393 (mMkL (zfScanState z) 0 R) =
        some (mMkL (zfScanState (z + 1)) 0 (mCons 0 R)) := by
      simpa only [mCons_zero_zero] using mStep_mMkL_left htr0 0 R
    have h2 := ih (z + 1) (by omega) (mCons 0 R) (by omega)
    have h3 : mStep zf393 (mMk' 60 0 (mCons 0 R)) = some (mMk' 60 0 R) := by
      simpa only [mCons_zero_zero] using
        mStep_mMk'_right (q := 60) (q' := 60) (a := 0) (b := 0) (by rfl) 0 R
    exact mStep_mReachPos h1 (mReachPos_to_mReach (mReachPos_trans h2 (mReachPos_step h3)))

theorem mRoot_scan_to_main0 (R : PAM M) :
    mStep zf393 (mMk' 60 0 (mCons 1 R)) = some (mMk' 99 mLB01 R) :=
  mStep_mMk'_right (by rfl) 0 R

theorem mScan_reaches_main0 (z : ℕ) (hz : z ≤ 9) (ip : List (Fin 2))
    (hok : scanZerosOk z (ip.reverse ++ [1]) = true) (R : PAM M) :
    mReachPos (mMkL (zfScanState z) (mAppend ip.reverse mLB01) R)
      (mMk' 99 mLB01 (mAppend ip R)) := by
  have hL : mAppend ip.reverse (mLB01 : PAM M) = mAppend (ip.reverse ++ [1]) (0 : PAM M) := by
    rw [mAppend_snoc]; rfl
  rw [hL]
  obtain ⟨z', hz', hscan⟩ := mZfScan_rev (ip.reverse ++ [1]) z hz hok R
  have hrev : (ip.reverse ++ [1]).reverse = 1 :: ip := by
    simp [List.reverse_append]
  rw [hrev, mAppend_cons] at hscan
  have hbounce := mZfScan_bounce_default z' hz' (mCons 1 (mAppend ip R))
  have hroot := mReachPos_step (mRoot_scan_to_main0 (mAppend ip R))
  exact mReach_mReachPos hscan (mReachPos_trans hbounce hroot)

theorem mContinue_scan_to_64 (k : ℕ) (hk4 : k ≤ 4) (rev : List (Fin 2))
    (h1 : k ≤ rev.count 1) (L R : PAM M) :
    let w' := (rawContinueRev k rev).reverse
    mReach (mMkL (continueState k) (mAppend rev L) R)
      (mMkL 64 (mAppend w'.reverse L) (mRep0 ((rev.length - w'.length : ℕ) : PAM M) R)) := by
  induction rev generalizing k R with
  | nil =>
    intro w'
    have hk0 : k = 0 := by simp at h1; omega
    subst hk0
    simpa [w', rawContinueRev, continueState] using mReach_refl _
  | cons b xs ih =>
    intro w'
    cases k with
    | zero =>
      have hsub : (b :: xs).length - w'.length = 0 := by simp [w', rawContinueRev]
      rw [hsub, Nat.cast_zero, mRep0_zero]
      simpa [w', rawContinueRev, continueState] using mReach_refl _
    | succ k' =>
      have hk'3 : k' < 4 := by omega
      rcases fin2_cases b with rfl | rfl
      · have htr0 := continueState_step0 ⟨k', hk'3⟩
        have hstep := mStep_mMkL_left htr0 (mAppend xs L) R
        have hrec := ih (k' + 1) hk4 (by simpa using h1) (mCons 0 R)
        dsimp only at hrec
        have hw'_eq : (rawContinueRev (k' + 1) xs).reverse = w' := rfl
        have hlen_le : w'.length ≤ xs.length := by
          rw [← hw'_eq, List.length_reverse]; exact rawContinueRev_length_le (k' + 1) xs
        have hsub : (0 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by simp; omega
        rw [hw'_eq, mRep0_mCons_zero, ← Nat.cast_add_one, ← hsub] at hrec
        exact mStep_mReach hstep hrec
      · have htr1 := continueState_step1 ⟨k', hk'3⟩
        have hstep := mStep_mMkL_left htr1 (mAppend xs L) R
        have hrec := ih k' (by omega) (by rw [List.count_cons_self] at h1; omega) (mCons 0 R)
        dsimp only at hrec
        have hw'_eq : (rawContinueRev k' xs).reverse = w' := rfl
        have hlen_le : w'.length ≤ xs.length := by
          rw [← hw'_eq, List.length_reverse]; exact rawContinueRev_length_le k' xs
        have hsub : (1 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by simp; omega
        rw [hw'_eq, mRep0_mCons_zero, ← Nat.cast_add_one, ← hsub] at hrec
        exact mStep_mReach hstep hrec

omit hpre in
theorem mContinue_k_reaches_main0 (k : ℕ) (hk4 : k ≤ 4) (slot : PAM M) (P : List (Fin 2))
    (h1 : k ≤ P.count 1) (hsl : (P.length : PAM M) ≤ slot)
    (hok : scanZerosOk 0 (P.reverse ++ [1]) = true) (regs_tape : List (PAM M)) :
    let ip' := (popContinueRev k P.reverse).reverse
    mReachPos
      (mMkL (continueState k) (mAppend P.reverse mLB01)
        (mRep0 (slot - (P.length : PAM M)) (mAppendRegs pre (mRegsTape regs_tape))))
      (mRootCfg pre slot ip' regs_tape) := by
  intro ip'
  have h1_rev : k ≤ P.reverse.count 1 := by rwa [List.count_reverse]
  set R_end := mAppendRegs pre (mRegsTape regs_tape)
  have hs₁ := mContinue_scan_to_64 k hk4 P.reverse h1_rev mLB01
    (mRep0 (slot - (P.length : PAM M)) R_end)
  let raw := rawContinueRev k P.reverse
  have hlen_raw : raw.length ≤ P.length := by
    rw [← P.length_reverse]; exact rawContinueRev_length_le k P.reverse
  have hlen_ip' : ip'.length ≤ raw.length := by
    dsimp only [ip', raw]
    rw [popContinueRev_eq_zero_rawContinueRev, List.length_reverse]
    exact popContinueRev_length_le 0 _
  have hok_raw : scanZerosOk 0 (raw.reverse.reverse ++ [1]) = true := by
    rw [List.reverse_reverse]
    exact scanZerosOk_rawContinueRev k P.reverse hok
  have hs₂ := mScan_reaches_main0 0 (by decide) raw.reverse hok_raw
    (mRep0 ((P.reverse.length - raw.reverse.length : ℕ) : PAM M)
      (mRep0 (slot - (P.length : PAM M)) R_end))
  have hraw_pad : raw.reverse = ip' ++ List.replicate (raw.length - ip'.length) 0 := by
    dsimp only [ip', raw]
    rw [popContinueRev_eq_zero_rawContinueRev, List.length_reverse]
    exact popContinueRev_zero_pad _
  have hnat_sum : ((raw.length - ip'.length : ℕ) : PAM M) +
      ((P.reverse.length - raw.reverse.length : ℕ) : PAM M) =
      (P.length : PAM M) - (ip'.length : PAM M) := by
    have hnat : (raw.length - ip'.length) + (P.reverse.length - raw.reverse.length) =
        P.length - ip'.length := by simp only [List.length_reverse]; omega
    rw [← Nat.cast_add, hnat]
    exact ((sub_eq_iff_eq_add_pam (natCast_le_iff.mpr (le_trans hlen_ip' hlen_raw))).mpr (by
      rw [← Nat.cast_add, Nat.add_sub_of_le (le_trans hlen_ip' hlen_raw)])).symm
  have htot : ((raw.length - ip'.length : ℕ) : PAM M) +
      (((P.reverse.length - raw.reverse.length : ℕ) : PAM M) + (slot - (P.length : PAM M))) =
      slot - (ip'.length : PAM M) := by
    rw [← add_assoc, hnat_sum]
    exact sub_split_add (natCast_le_iff.mpr (le_trans hlen_ip' hlen_raw)) hsl
  have hR : mAppend raw.reverse
      (mRep0 ((P.reverse.length - raw.reverse.length : ℕ) : PAM M)
        (mRep0 (slot - (P.length : PAM M)) R_end)) =
      mAppend ip' (mRep0 (slot - (ip'.length : PAM M)) R_end) := by
    conv_lhs => arg 1; rw [hraw_pad]
    rw [mAppend_append, mAppend_replicate_zero, ← mRep0_add, ← mRep0_add, add_assoc, htot]
  rw [hR] at hs₂
  exact mReach_mReachPos hs₁ hs₂

theorem mBreak_scan_to_64 (k : ℕ) (hk2 : k ≤ 2) (rev : List (Fin 2))
    (h0 : k + 1 ≤ rev.count 0) (L R : PAM M) :
    let w' := (popBreakRev k rev).reverse
    mReachPos (mMkL (breakState k) (mAppend rev L) R)
      (mMkL 64 (mAppend w'.reverse.tail L)
        (mCons 1 (mRep0 ((rev.length - w'.length : ℕ) : PAM M) R))) := by
  induction rev generalizing k R with
  | nil => simp at h0
  | cons b xs ih =>
    intro w'
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero =>
        have hstep := mStep_mMkL_left (q := 61) (q' := 64) (a := 0) (b := 1) (by rfl)
          (mAppend xs L) R
        have hw'_rev : w'.reverse = 1 :: xs := by simp [w', popBreakRev]
        have hsub : (0 :: xs).length - w'.length = 0 := by
          have : w'.length = (0 :: xs).length := by rw [← List.length_reverse, hw'_rev]; rfl
          omega
        rw [hw'_rev, List.tail_cons, hsub, Nat.cast_zero, mRep0_zero]
        exact mReachPos_step hstep
      | succ k' =>
        have htr0 : zf393Trans (breakState (k' + 1)) 0 = some (0, .left, breakState k') := by
          match k' with | 0 | 1 => rfl | _ + 2 => omega
        have hstep := mStep_mMkL_left htr0 (mAppend xs L) R
        have hrec := ih k' (by omega) (by rw [List.count_cons_self] at h0; omega) (mCons 0 R)
        dsimp only at hrec
        have hw'_eq : (popBreakRev k' xs).reverse = w' := rfl
        have hlen_le : w'.length ≤ xs.length := by
          rw [← hw'_eq, List.length_reverse]; exact popBreakRev_length_le k' xs
        have hsub : (0 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by simp; omega
        rw [hw'_eq, mRep0_mCons_zero, ← Nat.cast_add_one, ← hsub] at hrec
        exact mStep_mReachPos hstep (mReachPos_to_mReach hrec)
    · have htr1 : zf393Trans (breakState k) 1 = some (0, .left, breakState k) := by
        match k with | 0 | 1 | 2 => rfl | _ + 3 => omega
      have hstep := mStep_mMkL_left htr1 (mAppend xs L) R
      have hrec := ih k hk2 (by simpa using h0) (mCons 0 R)
      dsimp only at hrec
      have hw'_eq : (popBreakRev k xs).reverse = w' := rfl
      have hlen_le : w'.length ≤ xs.length := by
        rw [← hw'_eq, List.length_reverse]; exact popBreakRev_length_le k xs
      have hsub : (1 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by simp; omega
      rw [hw'_eq, mRep0_mCons_zero, ← Nat.cast_add_one, ← hsub] at hrec
      exact mStep_mReachPos hstep (mReachPos_to_mReach hrec)

/-- Slot size in `PAM M` after `6.break.k` (`k ∈ {0..2}`) on `P`. -/
def mBreakSlot (k : ℕ) (slot : PAM M) (P : List (Fin 2)) : PAM M :=
  if k + 1 ≤ P.count 0 then slot else slot + ((k - P.count 0 : ℕ) : PAM M) + 1

theorem mBreakSlot_natCast (k sl : ℕ) (P : List (Fin 2)) :
    mBreakSlot k (sl : PAM M) P = (breakSlot k sl P : PAM M) := by
  unfold mBreakSlot breakSlot
  split_ifs <;> push_cast <;> rfl

theorem mBreakSlot_mono (k : ℕ) {s₁ s₂ : PAM M} (hs : s₁ ≤ s₂) (P : List (Fin 2)) :
    mBreakSlot k s₁ P ≤ mBreakSlot k s₂ P := by
  unfold mBreakSlot
  split_ifs
  · exact hs
  · rcases hs with ⟨d, rfl⟩
    exact ⟨d, by ring⟩

theorem le_mBreakSlot (k : ℕ) (slot : PAM M) (P : List (Fin 2)) :
    slot ≤ mBreakSlot k slot P := by
  unfold mBreakSlot
  split_ifs
  · exact le_rfl
  · exact ⟨((k - P.count 0 : ℕ) : PAM M) + 1, by ring⟩

theorem mBreakSlot_append_ones (k : ℕ) (s : PAM M) (m : ℕ) (walked : List (Fin 2)) :
    mBreakSlot k s (walked ++ List.replicate m 1) = mBreakSlot k s walked := by
  unfold mBreakSlot
  rw [List.count_append, List.count_replicate]
  simp

omit hpre in
theorem mBreak_k_reaches_main0 (k : ℕ) (hk2 : k ≤ 2) (slot : PAM M) (P : List (Fin 2))
    (hsl : (P.length : PAM M) ≤ slot) (hok : scanZerosOk 0 (P.reverse ++ [1]) = true)
    (regs_tape : List (PAM M)) :
    let ip' := (popBreakRev k P.reverse).reverse
    mReachPos
      (mMkL (breakState k) (mAppend P.reverse mLB01)
        (mRep0 (slot - (P.length : PAM M)) (mAppendRegs pre (mRegsTape regs_tape))))
      (mRootCfg pre (mBreakSlot k slot P) ip' regs_tape) := by
  intro ip'
  set R_end := mAppendRegs pre (mRegsTape regs_tape)
  by_cases hlt : k + 1 ≤ P.count 0
  · have hlt_rev : k + 1 ≤ P.reverse.count 0 := by rwa [List.count_reverse]
    have hs₁ := mBreak_scan_to_64 k hk2 P.reverse hlt_rev mLB01
      (mRep0 (slot - (P.length : PAM M)) R_end)
    have hhead := popBreakRev_head_one k P.reverse hlt_rev
    have hip'_rev : ip'.reverse = 1 :: ip'.reverse.tail := by simpa [ip'] using hhead
    have hok' : scanZerosOk 0 (ip'.reverse.tail ++ [1]) = true := by
      have hfull : scanZerosOk 0 (ip'.reverse ++ [1]) = true := by
        simpa [ip'] using scanZerosOk_popBreakRev k P.reverse hok
      rw [hip'_rev] at hfull
      exact scanZerosOk_tail hfull
    have hs₂ := mScan_reaches_main0 0 (by decide) ip'.reverse.tail.reverse
      (by simpa [List.reverse_reverse] using hok')
      (mCons 1 (mRep0 ((P.reverse.length - ip'.length : ℕ) : PAM M)
        (mRep0 (slot - (P.length : PAM M)) R_end)))
    rw [List.reverse_reverse] at hs₂
    have hlen_le : ip'.length ≤ P.length := by
      have := popBreakRev_length_le k P.reverse; simpa [ip'] using this
    have hsub_cast : ((P.reverse.length - ip'.length : ℕ) : PAM M) =
        (P.length : PAM M) - (ip'.length : PAM M) := by
      rw [List.length_reverse]
      exact ((sub_eq_iff_eq_add_pam (natCast_le_iff.mpr hlen_le)).mpr (by
        rw [← Nat.cast_add, Nat.add_sub_of_le hlen_le])).symm
    have hpad : ((P.reverse.length - ip'.length : ℕ) : PAM M) + (slot - (P.length : PAM M)) =
        slot - (ip'.length : PAM M) := by
      rw [hsub_cast]
      exact sub_split_add (natCast_le_iff.mpr hlen_le) hsl
    have hip'_snoc : ip'.reverse.tail.reverse ++ [1] = ip' := by
      conv_rhs => rw [← List.reverse_reverse ip', hip'_rev]
      simp
    have hR : mAppend ip'.reverse.tail.reverse
        (mCons 1 (mRep0 ((P.reverse.length - ip'.length : ℕ) : PAM M)
          (mRep0 (slot - (P.length : PAM M)) R_end))) =
        mAppend ip' (mRep0 (slot - (ip'.length : PAM M)) R_end) := by
      rw [← mAppend_snoc, hip'_snoc, ← mRep0_add, hpad]
    rw [hR] at hs₂
    have hbs : mBreakSlot k slot P = slot := by simp only [mBreakSlot, hlt, ↓reduceIte]
    rw [hbs]
    exact mReachPos_trans hs₁ hs₂
  · have hle : P.reverse.count 0 ≤ k := by rw [List.count_reverse]; omega
    obtain ⟨hpop_nil, hpop_full⟩ := popBreakRev_overflow k P.reverse hle
    have hip'_nil : ip' = [] := by simp [ip', hpop_nil]
    set full_rev := P.reverse ++ [1] ++ List.replicate (k + 1) 0
    have hrep0_zero : ∀ m : ℕ, mAppend (List.replicate m 0) (0 : PAM M) = 0 := by
      intro m; rw [mAppend_replicate_zero]; simp [mRep0]
    have hL_eq : mAppend P.reverse (mLB01 : PAM M) = mAppend full_rev 0 := by
      unfold full_rev
      rw [mAppend_append, mAppend_append, hrep0_zero]
      rfl
    have hfull0 : k + 1 ≤ full_rev.count 0 := by unfold full_rev; simp; omega
    rw [hL_eq]
    have hs₁ := mBreak_scan_to_64 k hk2 full_rev hfull0 0
      (mRep0 (slot - (P.length : PAM M)) R_end)
    dsimp only at hs₁
    have hw_rev : (popBreakRev k full_rev).reverse.reverse.tail =
        List.replicate (P.reverse.count 0) 0 := by
      rw [List.reverse_reverse, hpop_full, List.tail_cons]
    have hw_len : (popBreakRev k full_rev).reverse.length = P.count 0 + 1 := by
      rw [List.length_reverse, hpop_full, List.length_cons, List.length_replicate,
        List.count_reverse]
    have hfull_len : full_rev.length - (popBreakRev k full_rev).reverse.length =
        P.length + (k - P.count 0) + 1 := by
      rw [hw_len]; unfold full_rev; simp; omega
    rw [hw_rev, hfull_len, hrep0_zero] at hs₁
    set extra : ℕ := P.length + (k - P.count 0) + 1
    have hbounce := mZfScan_bounce_default 0 (by decide)
      (mCons 1 (mRep0 (extra : PAM M) (mRep0 (slot - (P.length : PAM M)) R_end)))
    have hroot := mReachPos_step (mRoot_scan_to_main0
      (mRep0 (extra : PAM M) (mRep0 (slot - (P.length : PAM M)) R_end)))
    have hbs : mBreakSlot k slot P = slot + ((k - P.count 0 : ℕ) : PAM M) + 1 := by
      simp only [mBreakSlot, hlt, ↓reduceIte]
    have hpad : (extra : PAM M) + (slot - (P.length : PAM M)) =
        slot + ((k - P.count 0 : ℕ) : PAM M) + 1 := by
      dsimp only [extra]
      push_cast
      calc (P.length : PAM M) + ((k - P.count 0 : ℕ) : PAM M) + 1 + (slot - (P.length : PAM M))
        _ = ((P.length : PAM M) + (slot - (P.length : PAM M))) +
            ((k - P.count 0 : ℕ) : PAM M) + 1 := by ring
        _ = slot + ((k - P.count 0 : ℕ) : PAM M) + 1 := by rw [add_sub_of_le_pam hsl]
    rw [hip'_nil, hbs]
    have htot := mReachPos_trans hs₁ (mReachPos_trans hbounce hroot)
    simpa only [mRootCfg, mAppend_nil, List.length_nil, Nat.cast_zero, sub_zero_pam,
      ← mRep0_add, hpad] using htot

/-! ## Section 5: Moving `00` Selector, `1.inc`, `1.decnz`, & Leaf Gadgets in `PAM M` -/

/-- Selector tape suffix in `PAM M` with `m` registers shifted to the right of `00`. -/
noncomputable def mZf393SelRight (pre : List (PAM M)) (m : ℕ)
    (regs_tape : List (PAM M)) : PAM M :=
  mAppendRegs (pre ++ regs_tape.take (11 - m)) (mCons 0 (mRegsTape (regs_tape.drop (11 - m))))

omit hpre in
theorem mZf393SelRight_zero (pre regs_tape : List (PAM M)) (h : regs_tape.length = 11) :
    mZf393SelRight pre 0 regs_tape = mAppendRegs pre (mRegsTape regs_tape) := by
  unfold mZf393SelRight
  rw [Nat.sub_zero, List.take_of_length_le (by omega), List.drop_of_length_le (by omega),
    mRegsTape_nil, mCons_zero_zero, mAppendRegs_append]
  rfl

theorem mRet1_scan_reg (u L R : PAM M) :
    mReach (mMkL 23 (mEncodeRegRev u L) R) (mMkL 23 L (mEncodeReg u R)) := by
  unfold mEncodeRegRev mEncodeReg
  rw [mRep1_succ]
  have h1 := mStep_mMkL_left (q := 23) (q' := 24) (a := 0) (b := 0) (by rfl)
    (mCons 1 (mRep1 u L)) R
  have h2 := mStep_mMkL_left (q := 24) (q' := 23) (a := 1) (b := 1) (by rfl)
    (mRep1 u L) (mCons 0 R)
  have hscan := mLeftScan_reach (q := 23) (a := 1) (b := 1) (by rfl) u L (mCons 1 (mCons 0 R))
  rw [mRepBit_one_bit, mRepBit_one_bit, mRep1_mCons_one] at hscan
  exact mStep_mReach h1 (mStep_mReach h2 hscan)

theorem mRet1_scan_regs (rs : List (PAM M)) (L R : PAM M) :
    mReach (mMkL 23 (mAppendRegsRev rs L) R) (mMkL 23 L (mAppendRegs rs R)) := by
  induction rs using List.reverseRecOn generalizing R with
  | nil => exact mReach_refl _
  | append_singleton rs u ih =>
    rw [mAppendRegsRev_snoc, mAppendRegs_append, mAppendRegs_cons, mAppendRegs_nil]
    exact mReach_trans (mRet1_scan_reg u (mAppendRegsRev rs L) R) (ih (mEncodeReg u R))

theorem mRet1_finish (rs : List (PAM M)) (z L R : PAM M) :
    mReachPos
      (mMkL 23 (mAppendRegsRev rs (mRep0 (z + 2) (mCons 1 L))) R)
      (mMkL 61 L (mRep0 (z + 3) (mAppendRegs rs R))) := by
  have h1 := mRet1_scan_regs rs (mRep0 (z + 2) (mCons 1 L)) R
  set R₁ := mAppendRegs rs R
  have hz_split : mRep0 (z + 2) (mCons 1 L) = mCons 0 (mCons 0 (mRep0 z (mCons 1 L))) := by
    rw [show z + 2 = (z + 1) + 1 by ring, mRep0_succ, mRep0_succ]
  conv at h1 => arg 2; rw [hz_split]
  have hz1 := mStep_mMkL_left (q := 23) (q' := 24) (a := 0) (b := 0) (by rfl)
    (mCons 0 (mRep0 z (mCons 1 L))) R₁
  have hz2 := mStep_mMkL_left (q := 24) (q' := 25) (a := 0) (b := 0) (by rfl)
    (mRep0 z (mCons 1 L)) (mCons 0 R₁)
  have hscan := mLeftScan_reach (q := 25) (a := 0) (b := 0) (by rfl) z (mCons 1 L)
    (mCons 0 (mCons 0 R₁))
  rw [mRepBit_zero_bit, mRepBit_zero_bit] at hscan
  have hm1 := mStep_mMkL_left (q := 25) (q' := 61) (a := 1) (b := 0) (by rfl) L
    (mRep0 z (mCons 0 (mCons 0 R₁)))
  have hrep : mCons 0 (mRep0 z (mCons 0 (mCons 0 R₁))) = mRep0 (z + 3) R₁ := by
    rw [mRep0_mCons_zero, mRep0_mCons_zero, ← mRep0_succ]
    exact congrArg (fun x ↦ mRep0 x R₁) (by ring)
  rw [hrep] at hm1
  exact mReach_mReachPos h1 (mStep_mReachPos hz1 (mStep_mReach hz2
    (mReach_trans hscan (mReachPos_to_mReach (mReachPos_step hm1)))))

theorem mRet2_scan_reg (u L R : PAM M) :
    mReach (mMkL 26 (mEncodeRegRev u L) R) (mMkL 26 L (mEncodeReg u R)) := by
  unfold mEncodeRegRev mEncodeReg
  rw [mRep1_succ]
  have h1 := mStep_mMkL_left (q := 26) (q' := 27) (a := 0) (b := 0) (by rfl)
    (mCons 1 (mRep1 u L)) R
  have h2 := mStep_mMkL_left (q := 27) (q' := 26) (a := 1) (b := 1) (by rfl)
    (mRep1 u L) (mCons 0 R)
  have hscan := mLeftScan_reach (q := 26) (a := 1) (b := 1) (by rfl) u L (mCons 1 (mCons 0 R))
  rw [mRepBit_one_bit, mRepBit_one_bit, mRep1_mCons_one] at hscan
  exact mStep_mReach h1 (mStep_mReach h2 hscan)

theorem mRet2_scan_regs (rs : List (PAM M)) (L R : PAM M) :
    mReach (mMkL 26 (mAppendRegsRev rs L) R) (mMkL 26 L (mAppendRegs rs R)) := by
  induction rs using List.reverseRecOn generalizing R with
  | nil => exact mReach_refl _
  | append_singleton rs u ih =>
    rw [mAppendRegsRev_snoc, mAppendRegs_append, mAppendRegs_cons, mAppendRegs_nil]
    exact mReach_trans (mRet2_scan_reg u (mAppendRegsRev rs L) R) (ih (mEncodeReg u R))

theorem mRet2_finish (rs : List (PAM M)) (z L R : PAM M) :
    mReachPos
      (mMkL 26 (mAppendRegsRev rs (mRep0 (z + 2) (mCons 1 L))) R)
      (mMkL 62 L (mRep0 (z + 3) (mAppendRegs rs R))) := by
  have h1 := mRet2_scan_regs rs (mRep0 (z + 2) (mCons 1 L)) R
  set R₁ := mAppendRegs rs R
  have hz_split : mRep0 (z + 2) (mCons 1 L) = mCons 0 (mCons 0 (mRep0 z (mCons 1 L))) := by
    rw [show z + 2 = (z + 1) + 1 by ring, mRep0_succ, mRep0_succ]
  conv at h1 => arg 2; rw [hz_split]
  have hz1 := mStep_mMkL_left (q := 26) (q' := 27) (a := 0) (b := 0) (by rfl)
    (mCons 0 (mRep0 z (mCons 1 L))) R₁
  have hz2 := mStep_mMkL_left (q := 27) (q' := 28) (a := 0) (b := 0) (by rfl)
    (mRep0 z (mCons 1 L)) (mCons 0 R₁)
  have hscan := mLeftScan_reach (q := 28) (a := 0) (b := 0) (by rfl) z (mCons 1 L)
    (mCons 0 (mCons 0 R₁))
  rw [mRepBit_zero_bit, mRepBit_zero_bit] at hscan
  have hm1 := mStep_mMkL_left (q := 28) (q' := 62) (a := 1) (b := 0) (by rfl) L
    (mRep0 z (mCons 0 (mCons 0 R₁)))
  have hrep : mCons 0 (mRep0 z (mCons 0 (mCons 0 R₁))) = mRep0 (z + 3) R₁ := by
    rw [mRep0_mCons_zero, mRep0_mCons_zero, ← mRep0_succ]
    exact congrArg (fun x ↦ mRep0 x R₁) (by ring)
  rw [hrep] at hm1
  exact mReach_mReachPos h1 (mStep_mReachPos hz1 (mStep_mReach hz2
    (mReach_trans hscan (mReachPos_to_mReach (mReachPos_step hm1)))))

theorem mSel_scan_reg (u L R : PAM M) :
    mReach (mMk' 20 L (mEncodeReg u R)) (mMk' 20 (mEncodeRegRev u L) R) := by
  unfold mEncodeReg mEncodeRegRev
  rw [mRep1_succ]
  have h1 := mStep_mMk'_right (q := 20) (q' := 19) (a := 1) (b := 1) (by rfl) L
    (mRep1 u (mCons 0 R))
  have hscan := mRightScan_reach (q := 19) (a := 1) (b := 1) (by rfl) u (mCons 1 L) (mCons 0 R)
  rw [mRepBit_one_bit, mRepBit_one_bit] at hscan
  have h2 := mStep_mMk'_right (q := 19) (q' := 20) (a := 0) (b := 0) (by rfl)
    (mRep1 u (mCons 1 L)) R
  conv at h2 => rhs; rw [mRep1_mCons_one]
  exact mStep_mReach h1 (mReach_trans hscan (mReachPos_to_mReach (mReachPos_step h2)))

theorem mSel_scan_regs (rs : List (PAM M)) (L R : PAM M) :
    mReach (mMk' 20 L (mAppendRegs rs R)) (mMk' 20 (mAppendRegsRev rs L) R) := by
  induction rs generalizing L with
  | nil => exact mReach_refl _
  | cons u rs ih =>
    rw [mAppendRegs_cons, mAppendRegsRev_cons]
    exact mReach_trans (mSel_scan_reg u L (mAppendRegs rs R)) (ih (mEncodeRegRev u L))

theorem mSel_pass_to_61 (m : ℕ) (hm : m < 11) (z : PAM M) (regs_tape : List (PAM M))
    (hregs : regs_tape.length = 11) (L : PAM M) :
    mReachPos
      (mMk' 17 L (mRep0 (z + 3) (mZf393SelRight pre m regs_tape)))
      (mMkL 61 L (mRep0 (z + 3) (mZf393SelRight pre (m + 1) regs_tape))) := by
  have htake : regs_tape.take (11 - m) = regs_tape.take (10 - m) ++ [regs_tape[10 - m]] := by
    have h11 : 11 - m = (10 - m) + 1 := by omega
    rw [h11, List.take_add_one, getElem?_pos regs_tape (10 - m) (by omega), Option.toList_some]
  set v := regs_tape[10 - m]
  set rs_pre := pre ++ regs_tape.take (10 - m)
  have hrs_ne : rs_pre ≠ [] := by simp [rs_pre, hpre.out]
  have hrs_split : pre ++ regs_tape.take (11 - m) = rs_pre ++ [v] := by
    rw [htake, List.append_assoc]
  unfold mZf393SelRight
  rw [hrs_split, mAppendRegs_append, mAppendRegs_cons, mAppendRegs_nil]
  set R_tail := mRegsTape (regs_tape.drop (11 - m))
  have hz3 : mRep0 (z + 3) (mAppendRegs rs_pre (mEncodeReg v (mCons 0 R_tail))) =
      mCons 0 (mRep0 (z + 2) (mAppendRegs rs_pre (mEncodeReg v (mCons 0 R_tail)))) := by
    rw [show z + 3 = (z + 2) + 1 by ring, mRep0_succ]
  rw [hz3]
  have hs1 := mStep_mMk'_right (q := 17) (q' := 18) (a := 0) (b := 1) (by rfl) L
    (mRep0 (z + 2) (mAppendRegs rs_pre (mEncodeReg v (mCons 0 R_tail))))
  have hscan0 := mRightScan_reach (q := 18) (a := 0) (b := 0) (by rfl) (z + 2) (mCons 1 L)
    (mAppendRegs rs_pre (mEncodeReg v (mCons 0 R_tail)))
  rw [mRepBit_zero_bit, mRepBit_zero_bit] at hscan0
  set L_z := mRep0 (z + 2) (mCons 1 L)
  obtain ⟨u₀, rs_rest, hpre_cons⟩ : ∃ u₀ rs_rest, rs_pre = u₀ :: rs_rest := by
    rcases h : rs_pre with _ | ⟨u₀, rs_rest⟩
    · exact absurd h hrs_ne
    · exact ⟨u₀, rs_rest, rfl⟩
  have h18_to_20 : mReach
      (mMk' 18 L_z (mAppendRegs rs_pre (mEncodeReg v (mCons 0 R_tail))))
      (mMk' 20 (mAppendRegsRev rs_pre L_z) (mEncodeReg v (mCons 0 R_tail))) := by
    rw [hpre_cons, mAppendRegs_cons, mAppendRegsRev_cons]
    set R_u0 := mAppendRegs rs_rest (mEncodeReg v (mCons 0 R_tail))
    have hfirst : mReach (mMk' 18 L_z (mEncodeReg u₀ R_u0))
        (mMk' 20 (mEncodeRegRev u₀ L_z) R_u0) := by
      unfold mEncodeReg mEncodeRegRev
      rw [mRep1_succ]
      have ha1 := mStep_mMk'_right (q := 18) (q' := 19) (a := 1) (b := 1) (by rfl) L_z
        (mRep1 u₀ (mCons 0 R_u0))
      have hasc := mRightScan_reach (q := 19) (a := 1) (b := 1) (by rfl) u₀ (mCons 1 L_z)
        (mCons 0 R_u0)
      rw [mRepBit_one_bit, mRepBit_one_bit] at hasc
      have ha2 := mStep_mMk'_right (q := 19) (q' := 20) (a := 0) (b := 0) (by rfl)
        (mRep1 u₀ (mCons 1 L_z)) R_u0
      conv at ha2 => rhs; rw [mRep1_mCons_one]
      exact mStep_mReach ha1 (mReach_trans hasc (mReachPos_to_mReach (mReachPos_step ha2)))
    exact mReach_trans hfirst (mSel_scan_regs rs_rest (mEncodeRegRev u₀ L_z)
      (mEncodeReg v (mCons 0 R_tail)))
  set L_pre := mAppendRegsRev rs_pre L_z
  have hv_scan := mSel_scan_reg v L_pre (mCons 0 R_tail)
  unfold mEncodeRegRev at hv_scan
  set L_ones := mRep1 (v + 1) L_pre
  have hd0 := mStep_mMk'_left (q := 20) (q' := 21) (a := 0) (b := 0) (by rfl)
    (mCons 0 L_ones) R_tail
  have he0 := mStep_mMkL_left (q := 21) (q' := 22) (a := 0) (b := 1) (by rfl)
    L_ones (mCons 0 R_tail)
  have hf_ones := mLeftScan_reach (q := 22) (a := 1) (b := 1) (by rfl) (v + 1) L_pre
    (mCons 1 (mCons 0 R_tail))
  rw [mRepBit_one_bit, mRepBit_one_bit, mRep1_inner_cons] at hf_ones
  have henc_v : mCons 1 (mRep1 (v + 1) (mCons 0 R_tail)) = mCons 1 (mEncodeReg v R_tail) := rfl
  rw [henc_v] at hf_ones
  obtain ⟨rs_init, u_last, hpre_snoc⟩ : ∃ rs_init u_last, rs_pre = rs_init ++ [u_last] := by
    rcases rs_pre.eq_nil_or_concat with hnil | ⟨rs_init, u_last, hcat⟩
    · exact absurd hnil hrs_ne
    · exact ⟨rs_init, u_last, by rw [hcat, List.concat_eq_append]⟩
  have hL_pre_0 : L_pre = mCons 0 (mRep1 (u_last + 1) (mAppendRegsRev rs_init L_z)) := by
    dsimp only [L_pre]
    rw [hpre_snoc, mAppendRegsRev_snoc]
    rfl
  have hf0 : mStep zf393 (mMkL 22 L_pre (mCons 1 (mEncodeReg v R_tail))) =
      some (mMk' 21 L_pre (mCons 1 (mEncodeReg v R_tail))) := by
    rw [hL_pre_0]
    exact mStep_mMkL_right (by rfl) _ _
  have he1 := mStep_mMk'_left (q := 21) (q' := 23) (a := 1) (b := 0) (by rfl) L_pre
    (mEncodeReg v R_tail)
  have hret := mRet1_finish rs_pre z L (mCons 0 (mEncodeReg v R_tail))
  have hdrop : regs_tape.drop (11 - (m + 1)) = v :: regs_tape.drop (11 - m) := by
    have hsub1 : 11 - (m + 1) = 10 - m := by omega
    have hsub2 : 11 - m = (10 - m) + 1 := by omega
    rw [hsub1, hsub2]
    exact (List.getElem_cons_drop (by omega)).symm
  have hsub_take : 11 - (m + 1) = 10 - m := by omega
  rw [hdrop, hsub_take, mRegsTape_cons]
  exact mStep_mReachPos hs1 (mReach_trans hscan0 (mReach_trans h18_to_20
    (mReach_trans hv_scan (mStep_mReach hd0 (mStep_mReach he0 (mReach_trans hf_ones
      (mStep_mReach hf0 (mStep_mReach he1 (mReachPos_to_mReach hret)))))))))

theorem mSel_step_reaches_main0 (m : ℕ) (hm : m < 11) (slot : PAM M) (walked : List (Fin 2))
    (hsl : ((walked.length + m + 4 : ℕ) : PAM M) ≤ slot)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true)
    (regs_tape : List (PAM M)) (hregs : regs_tape.length = 11) :
    mReachPos
      (mMk' 17 (mAppend (walked ++ List.replicate m 1 ++ [0]).reverse mLB01)
        (mRep0 (slot - ((walked.length + m + 1 : ℕ) : PAM M))
          (mZf393SelRight pre m regs_tape)))
      (mMk' 99 mLB01
        (mAppend (walked ++ List.replicate (m + 1) 1)
          (mRep0 (slot - ((walked.length + m + 1 : ℕ) : PAM M))
            (mZf393SelRight pre (m + 1) regs_tape)))) := by
  set P := walked ++ List.replicate m 1 ++ [0]
  set base : PAM M := ((walked.length + m + 1 : ℕ) : PAM M)
  have hbase3 : base + 3 ≤ slot := by
    have hnat : walked.length + m + 4 = (walked.length + m + 1) + 3 := by omega
    simpa only [base, hnat, Nat.cast_add, Nat.cast_ofNat] using hsl
  set z := slot - (base + 3)
  have hz_eq : slot - base = z + 3 := by
    dsimp only [z]
    have hle : base ≤ slot := le_trans (le_add_right_pam base 3) hbase3
    rw [sub_eq_iff_eq_add_pam hle]
    calc slot
      _ = (base + 3) + (slot - (base + 3)) := (add_sub_of_le_pam hbase3).symm
      _ = base + (slot - (base + 3) + 3) := by ring
  rw [hz_eq]
  have hs₁ := @mSel_pass_to_61 M _ _ pre hpre m hm z regs_tape hregs (mAppend P.reverse mLB01)
  set R_sel := mRep0 (z + 3) (mZf393SelRight pre (m + 1) regs_tape)
  have hP_rev : mAppend P.reverse (mLB01 : PAM M) =
      mCons 0 (mAppend (walked ++ List.replicate m 1).reverse mLB01) := by
    simp [P, List.reverse_append]
  have hb0 : mStep zf393 (mMkL 61 (mAppend P.reverse mLB01) R_sel) =
      some (mMkL 64 (mAppend (walked ++ List.replicate m 1).reverse mLB01) (mCons 1 R_sel)) := by
    rw [hP_rev]
    exact mStep_mMkL_left (by rfl) _ _
  have hscan_ones : ∀ n xs, scanZerosOk 0 (List.replicate n (1 : Fin 2) ++ xs) =
      scanZerosOk 0 xs := by
    intro n xs; induction n with
    | zero => rfl
    | succ n ih => exact ih
  have hok_ones : scanZerosOk 0 ((walked ++ List.replicate m 1).reverse ++ [1]) = true := by
    rw [List.reverse_append, List.reverse_replicate, List.append_assoc, hscan_ones m]
    exact hok
  have hs₂ := mScan_reaches_main0 0 (by decide) (walked ++ List.replicate m 1) hok_ones
    (mCons 1 R_sel)
  have hR : mAppend (walked ++ List.replicate m 1) (mCons 1 R_sel) =
      mAppend (walked ++ List.replicate (m + 1) 1) R_sel := by
    rw [← mAppend_snoc, List.append_assoc walked, ← List.replicate_succ']
  rw [hR] at hs₂
  exact mReachPos_trans hs₁ (mStep_mReachPos hb0 (mReachPos_to_mReach hs₂))

theorem mInc_scan_reg (u L R : PAM M) :
    mReach (mMk' 16 L (mEncodeReg u R)) (mMk' 16 (mEncodeRegRev u L) R) := by
  unfold mEncodeReg mEncodeRegRev
  rw [mRep1_succ]
  have h1 := mStep_mMk'_right (q := 16) (q' := 15) (a := 1) (b := 1) (by rfl) L
    (mRep1 u (mCons 0 R))
  have hscan := mRightScan_reach (q := 15) (a := 1) (b := 1) (by rfl) u (mCons 1 L) (mCons 0 R)
  rw [mRepBit_one_bit, mRepBit_one_bit] at hscan
  have h2 := mStep_mMk'_right (q := 15) (q' := 16) (a := 0) (b := 0) (by rfl)
    (mRep1 u (mCons 1 L)) R
  conv at h2 => rhs; rw [mRep1_mCons_one]
  exact mStep_mReach h1 (mReach_trans hscan (mReachPos_to_mReach (mReachPos_step h2)))

theorem mInc_scan_regs (rs : List (PAM M)) (L R : PAM M) :
    mReach (mMk' 16 L (mAppendRegs rs R)) (mMk' 16 (mAppendRegsRev rs L) R) := by
  induction rs generalizing L with
  | nil => exact mReach_refl _
  | cons u rs ih =>
    rw [mAppendRegs_cons, mAppendRegsRev_cons]
    exact mReach_trans (mInc_scan_reg u L (mAppendRegs rs R)) (ih (mEncodeRegRev u L))

theorem mInc_pass_to_61 (r : Fin 11) (z : PAM M) (regs_tape : List (PAM M))
    (hregs : regs_tape.length = 11) (L : PAM M) :
    mReachPos
      (mMk' 13 L (mRep0 (z + 3) (mZf393SelRight pre (11 - r.val) regs_tape)))
      (mMkL 61 L (mRep0 (z + 3)
        (mAppendRegs pre (mRegsTape (regs_tape.set r.val (regs_tape[r.val] + 1)))))) := by
  have hsub : 11 - (11 - r.val) = r.val := by omega
  unfold mZf393SelRight
  rw [hsub]
  set rs_pre := pre ++ regs_tape.take r.val
  set R_after := mRegsTape (regs_tape.drop r.val)
  have hz3 : mRep0 (z + 3) (mAppendRegs rs_pre (mCons 0 R_after)) =
      mCons 0 (mRep0 (z + 2) (mAppendRegs rs_pre (mCons 0 R_after))) := by
    rw [show z + 3 = (z + 2) + 1 by ring, mRep0_succ]
  rw [hz3]
  have hs1 := mStep_mMk'_right (q := 13) (q' := 14) (a := 0) (b := 1) (by rfl) L
    (mRep0 (z + 2) (mAppendRegs rs_pre (mCons 0 R_after)))
  have hscan0 := mRightScan_reach (q := 14) (a := 0) (b := 0) (by rfl) (z + 2) (mCons 1 L)
    (mAppendRegs rs_pre (mCons 0 R_after))
  rw [mRepBit_zero_bit, mRepBit_zero_bit] at hscan0
  set L_z := mRep0 (z + 2) (mCons 1 L)
  have hpre_ne : rs_pre ≠ [] := by simp [rs_pre, hpre.out]
  obtain ⟨u₀, rs_rest, hpre_cons⟩ : ∃ u₀ rs_rest, rs_pre = u₀ :: rs_rest := by
    rcases h : rs_pre with _ | ⟨u₀, rs_rest⟩
    · exact absurd h hpre_ne
    · exact ⟨u₀, rs_rest, rfl⟩
  have h14_to_16 : mReach
      (mMk' 14 L_z (mAppendRegs rs_pre (mCons 0 R_after)))
      (mMk' 16 (mAppendRegsRev rs_pre L_z) (mCons 0 R_after)) := by
    rw [hpre_cons, mAppendRegs_cons, mAppendRegsRev_cons]
    set R_u0 := mAppendRegs rs_rest (mCons 0 R_after)
    have hfirst : mReach (mMk' 14 L_z (mEncodeReg u₀ R_u0))
        (mMk' 16 (mEncodeRegRev u₀ L_z) R_u0) := by
      unfold mEncodeReg mEncodeRegRev
      rw [mRep1_succ]
      have ha1 := mStep_mMk'_right (q := 14) (q' := 15) (a := 1) (b := 1) (by rfl) L_z
        (mRep1 u₀ (mCons 0 R_u0))
      have hasc := mRightScan_reach (q := 15) (a := 1) (b := 1) (by rfl) u₀ (mCons 1 L_z)
        (mCons 0 R_u0)
      rw [mRepBit_one_bit, mRepBit_one_bit] at hasc
      have ha2 := mStep_mMk'_right (q := 15) (q' := 16) (a := 0) (b := 0) (by rfl)
        (mRep1 u₀ (mCons 1 L_z)) R_u0
      conv at ha2 => rhs; rw [mRep1_mCons_one]
      exact mStep_mReach ha1 (mReach_trans hasc (mReachPos_to_mReach (mReachPos_step ha2)))
    exact mReach_trans hfirst (mInc_scan_regs rs_rest (mEncodeRegRev u₀ L_z) (mCons 0 R_after))
  have hd0 := mStep_mMk'_left (q := 16) (q' := 23) (a := 0) (b := 1) (by rfl)
    (mAppendRegsRev rs_pre L_z) R_after
  have hret := mRet1_finish rs_pre z L (mCons 1 R_after)
  have htake_set_drop : ∀ (xs : List (PAM M)) (i : ℕ) (w : PAM M),
      i < xs.length → xs.take i ++ (w :: xs.drop (i + 1)) = xs.set i w := by
    intro xs i w hi
    induction xs generalizing i with
    | nil => simp at hi
    | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => simp [ih i (by simpa using hi)]
  have hset : mAppendRegs rs_pre (mCons 1 R_after) =
      mAppendRegs pre (mRegsTape (regs_tape.set r.val (regs_tape[r.val] + 1))) := by
    have hdrop : regs_tape.drop r.val = regs_tape[r.val] :: regs_tape.drop (r.val + 1) :=
      (List.getElem_cons_drop (by omega)).symm
    have henc1 : mCons 1 (mRegsTape (regs_tape[r.val] :: regs_tape.drop (r.val + 1))) =
        mRegsTape ((regs_tape[r.val] + 1) :: regs_tape.drop (r.val + 1)) := by
      conv_lhs => rw [mRegsTape, mAppendRegs_cons, mEncodeReg]
      conv_rhs => rw [mRegsTape, mAppendRegs_cons, mEncodeReg, mRep1_succ]
    dsimp only [R_after, rs_pre]
    rw [hdrop, henc1, mAppendRegs_append, ← mRegsTape_append,
      htake_set_drop regs_tape r.val (regs_tape[r.val] + 1) (by omega)]
  rw [hset] at hret
  exact mStep_mReachPos hs1 (mReach_trans hscan0
    (mReach_trans h14_to_16 (mStep_mReach hd0 (mReachPos_to_mReach hret))))

theorem mInc_step_reaches_main0 (r : Fin 11) (slot : PAM M) (walked : List (Fin 2))
    (hsl : ((walked.length + (11 - r.val) + 3 : ℕ) : PAM M) ≤ slot)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true)
    (regs_tape : List (PAM M)) (hregs : regs_tape.length = 11) :
    mReachPos
      (mMk' 13 (mAppend (walked ++ List.replicate (11 - r.val) 1).reverse mLB01)
        (mRep0 (slot - ((walked.length + (11 - r.val) : ℕ) : PAM M))
          (mZf393SelRight pre (11 - r.val) regs_tape)))
      (mRootCfg pre (mBreakSlot 0 slot walked) (retStack walked)
        (regs_tape.set r.val (regs_tape[r.val] + 1))) := by
  set m := 11 - r.val
  set base : PAM M := ((walked.length + m : ℕ) : PAM M)
  have hbase3 : base + 3 ≤ slot := by
    dsimp only [base, m]
    simpa [Nat.cast_add] using hsl
  set z := slot - (base + 3)
  have hz_eq : slot - base = z + 3 := by
    dsimp only [z]
    have hle : base ≤ slot := le_trans (le_add_right_pam base 3) hbase3
    rw [sub_eq_iff_eq_add_pam hle]
    calc slot
      _ = (base + 3) + (slot - (base + 3)) := (add_sub_of_le_pam hbase3).symm
      _ = base + (slot - (base + 3) + 3) := by ring
  rw [hz_eq]
  have hs₁ := @mInc_pass_to_61 M _ _ pre hpre r z regs_tape hregs
    (mAppend (walked ++ List.replicate m 1).reverse mLB01)
  have hscan_ones : ∀ n xs, scanZerosOk 0 (List.replicate n (1 : Fin 2) ++ xs) =
      scanZerosOk 0 xs := by
    intro n xs; induction n with
    | zero => rfl
    | succ n ih => exact ih
  have hok_m : scanZerosOk 0 ((walked ++ List.replicate m 1).reverse ++ [1]) = true := by
    rw [List.reverse_append, List.reverse_replicate, List.append_assoc, hscan_ones m]
    exact hok
  have hlen_m : ((walked ++ List.replicate m 1).length : PAM M) ≤ slot := by
    rw [List.length_append, List.length_replicate]
    exact le_trans (le_add_right_pam base 3) hbase3
  have hs₂ := @mBreak_k_reaches_main0 M _ _ pre 0 (by decide) slot
    (walked ++ List.replicate m 1) hlen_m hok_m
    (regs_tape.set r.val (regs_tape[r.val] + 1))
  have hsub_m : slot - ((walked ++ List.replicate m 1).length : PAM M) = z + 3 := by
    rw [List.length_append, List.length_replicate]; exact hz_eq
  have hpop : (popBreakRev 0 (walked ++ List.replicate m 1).reverse).reverse = retStack walked := by
    rw [List.reverse_append, List.reverse_replicate, popBreakRev_replicate_one_append]
    rfl
  rw [hsub_m, hpop, mBreakSlot_append_ones] at hs₂
  exact mReachPos_trans hs₁ hs₂

theorem mDecnz_shift_right (rs : List (PAM M)) (L R : PAM M) :
    mReachPos (mMk' 8 L (mAppendRegs rs (mCons 0 R)))
      (mMk' 9 (mAppendRegsRev rs (mCons 0 L)) R) := by
  induction rs generalizing L with
  | nil =>
    exact mReachPos_step (mStep_mMk'_right (by rfl) L R)
  | cons u rs ih =>
    rw [mAppendRegs_cons, mAppendRegsRev_cons]
    set R_rs := mAppendRegs rs (mCons 0 R)
    have h1 : mReach (mMk' 8 L (mEncodeReg u R_rs))
        (mMk' 8 (mRep1 (u + 1) (mCons 0 L)) R_rs) := by
      unfold mEncodeReg
      rw [mRep1_succ]
      have ha1 := mStep_mMk'_right (q := 8) (q' := 7) (a := 1) (b := 0) (by rfl) L
        (mRep1 u (mCons 0 R_rs))
      have hasc := mRightScan_reach (q := 7) (a := 1) (b := 1) (by rfl) u (mCons 0 L)
        (mCons 0 R_rs)
      rw [mRepBit_one_bit, mRepBit_one_bit] at hasc
      have ha2 := mStep_mMk'_right (q := 7) (q' := 8) (a := 0) (b := 1) (by rfl)
        (mRep1 u (mCons 0 L)) R_rs
      rw [← mRep1_succ] at ha2
      exact mStep_mReach ha1 (mReach_trans hasc (mReachPos_to_mReach (mReachPos_step ha2)))
    have hs₂ := ih (mRep1 (u + 1) (mCons 0 L))
    exact mReach_mReachPos h1 hs₂

theorem mDecnz_shift_left (rs : List (PAM M)) (L : PAM M) :
    mReachPos (mMk' 11 L (mCons 0 (mRegsTape rs)))
      (mMkL 23 (mAppendRegsRev rs L) 0) := by
  induction rs generalizing L with
  | nil =>
    have h1 := mStep_mMk'_right (q := 11) (q' := 12) (a := 0) (b := 1) (by rfl) L 0
    have h2 : mStep zf393 (mMk' 12 (mCons 1 L) 0) = some (mMkL 17 (mCons 1 L) 0) := by
      simpa only [mCons_zero_zero] using
        mStep_mMk'_left (q := 12) (q' := 17) (a := 0) (b := 0) (by rfl) (mCons 1 L) 0
    have h3 : mStep zf393 (mMkL 17 (mCons 1 L) 0) = some (mMkL 23 L 0) := by
      simpa only [mCons_zero_zero] using
        mStep_mMkL_left (q := 17) (q' := 23) (a := 1) (b := 0) (by rfl) L 0
    exact mStep_mReachPos h1 (mStep_mReach h2 (mReachPos_to_mReach (mReachPos_step h3)))
  | cons u rs ih =>
    rw [mRegsTape_cons, mAppendRegsRev_cons]
    unfold mEncodeReg mEncodeRegRev
    rw [mRep1_succ]
    set R_u := mCons 0 (mRegsTape rs)
    have h1 := mStep_mMk'_right (q := 11) (q' := 12) (a := 0) (b := 1) (by rfl) L
      (mCons 1 (mRep1 u R_u))
    have h2 := mStep_mMk'_right (q := 12) (q' := 9) (a := 1) (b := 1) (by rfl) (mCons 1 L)
      (mRep1 u R_u)
    have hscan := mRightScan_reach (q := 9) (a := 1) (b := 1) (by rfl) u
      (mCons 1 (mCons 1 L)) R_u
    rw [mRepBit_one_bit, mRepBit_one_bit, mRep1_inner_cons, mRep1_inner_cons] at hscan
    have h3 : mStep zf393 (mMk' 9 (mCons 1 (mCons 1 (mRep1 u L))) R_u) =
        some (mMkL 5 (mCons 1 (mCons 1 (mRep1 u L))) R_u) := by
      dsimp only [R_u]
      exact mStep_mMk'_left (by rfl) _ _
    have h4 := mStep_mMkL_left (q := 5) (q' := 10) (a := 1) (b := 1) (by rfl)
      (mCons 1 (mRep1 u L)) R_u
    have h5 := mStep_mMkL_right (q := 10) (q' := 11) (a := 1) (b := 1) (by rfl)
      (mRep1 u L) (mCons 1 R_u)
    have h6 := mStep_mMk'_right (q := 11) (q' := 11) (a := 1) (b := 0) (by rfl)
      (mCons 1 (mRep1 u L)) R_u
    conv at h6 => rhs; rw [← mRep1_succ]
    have hrest := ih (mCons 0 (mRep1 (u + 1) L))
    exact mStep_mReachPos h1 (mStep_mReach h2 (mReach_trans hscan
      (mStep_mReach h3 (mStep_mReach h4 (mStep_mReach h5
        (mStep_mReach h6 (mReachPos_to_mReach hrest)))))))

theorem mDecnz_pass_to_break (r : Fin 11) (z : PAM M) (regs_tape : List (PAM M))
    (hregs : regs_tape.length = 11) (L : PAM M) :
    (regs_tape[r.val] = 0 →
      mReachPos
        (mMk' 5 L (mRep0 (z + 3) (mZf393SelRight pre (11 - r.val) regs_tape)))
        (mMkL 62 L (mRep0 (z + 4) (mAppendRegs pre (mRegsTape regs_tape))))) ∧
    (regs_tape[r.val] ≠ 0 →
      mReachPos
        (mMk' 5 L (mRep0 (z + 3) (mZf393SelRight pre (11 - r.val) regs_tape)))
        (mMkL 61 L (mRep0 (z + 4)
          (mAppendRegs pre (mRegsTape (regs_tape.set r.val (regs_tape[r.val] - 1))))))) := by
  have hsub : 11 - (11 - r.val) = r.val := by omega
  set rs_pre := pre ++ regs_tape.take r.val
  set R_after := mRegsTape (regs_tape.drop r.val)
  have hsel_eq : mZf393SelRight pre (11 - r.val) regs_tape =
      mAppendRegs rs_pre (mCons 0 R_after) := by
    unfold mZf393SelRight; rw [hsub]
  have hz3 : mRep0 (z + 3) (mZf393SelRight pre (11 - r.val) regs_tape) =
      mCons 0 (mRep0 (z + 2) (mAppendRegs rs_pre (mCons 0 R_after))) := by
    rw [hsel_eq, show z + 3 = (z + 2) + 1 by ring, mRep0_succ]
  have hs1 : mStep zf393 (mMk' 5 L (mRep0 (z + 3) (mZf393SelRight pre (11 - r.val) regs_tape))) =
      some (mMk' 6 (mCons 1 L) (mRep0 (z + 2) (mAppendRegs rs_pre (mCons 0 R_after)))) := by
    rw [hz3]
    exact mStep_mMk'_right (by rfl) L _
  have hscan0 := mRightScan_reach (q := 6) (a := 0) (b := 0) (by rfl) (z + 2) (mCons 1 L)
    (mAppendRegs rs_pre (mCons 0 R_after))
  rw [mRepBit_zero_bit, mRepBit_zero_bit] at hscan0
  set L_z := mRep0 (z + 2) (mCons 1 L)
  have hrs_ne : rs_pre ≠ [] := by simp [rs_pre, hpre.out]
  obtain ⟨u₀, rs_rest, hpre_cons⟩ : ∃ u₀ rs_rest, rs_pre = u₀ :: rs_rest := by
    rcases h : rs_pre with _ | ⟨u₀, rs_rest⟩
    · exact absurd h hrs_ne
    · exact ⟨u₀, rs_rest, rfl⟩
  have h6_shift : mReachPos
      (mMk' 6 L_z (mAppendRegs rs_pre (mCons 0 R_after)))
      (mMk' 9 (mAppendRegsRev rs_pre (mCons 0 L_z)) R_after) := by
    rw [hpre_cons, mAppendRegs_cons, mAppendRegsRev_cons]
    set R_u0 := mAppendRegs rs_rest (mCons 0 R_after)
    have hfirst : mReach (mMk' 6 L_z (mEncodeReg u₀ R_u0))
        (mMk' 8 (mRep1 (u₀ + 1) (mCons 0 L_z)) R_u0) := by
      unfold mEncodeReg
      rw [mRep1_succ]
      have ha1 := mStep_mMk'_right (q := 6) (q' := 7) (a := 1) (b := 0) (by rfl) L_z
        (mRep1 u₀ (mCons 0 R_u0))
      have hasc := mRightScan_reach (q := 7) (a := 1) (b := 1) (by rfl) u₀ (mCons 0 L_z)
        (mCons 0 R_u0)
      rw [mRepBit_one_bit, mRepBit_one_bit] at hasc
      have ha2 := mStep_mMk'_right (q := 7) (q' := 8) (a := 0) (b := 1) (by rfl)
        (mRep1 u₀ (mCons 0 L_z)) R_u0
      rw [← mRep1_succ] at ha2
      exact mStep_mReach ha1 (mReach_trans hasc (mReachPos_to_mReach (mReachPos_step ha2)))
    exact mReach_mReachPos hfirst
      (mDecnz_shift_right rs_rest (mRep1 (u₀ + 1) (mCons 0 L_z)) R_after)
  set L_pre := mAppendRegsRev rs_pre (mCons 0 L_z)
  have hdrop : regs_tape.drop r.val = regs_tape[r.val] :: regs_tape.drop (r.val + 1) :=
    (List.getElem_cons_drop (by omega)).symm
  set v := regs_tape[r.val]
  set rs_tail := regs_tape.drop (r.val + 1)
  have hR_after : R_after = mRep1 (v + 1) (mCons 0 (mRegsTape rs_tail)) := by
    dsimp only [R_after, v, rs_tail]
    rw [hdrop, mRegsTape_cons]
    rfl
  set R_t0 := mCons 0 (mRegsTape rs_tail)
  have hscan_v := mRightScan_reach (q := 9) (a := 1) (b := 1) (by rfl) (v + 1) L_pre R_t0
  rw [mRepBit_one_bit, mRepBit_one_bit, ← hR_after] at hscan_v
  have he0 : mStep zf393 (mMk' 9 (mRep1 (v + 1) L_pre) R_t0) =
      some (mMkL 5 (mRep1 (v + 1) L_pre) R_t0) := by
    dsimp only [R_t0]
    exact mStep_mMk'_left (by rfl) _ _
  have hd1 : mStep zf393 (mMkL 5 (mRep1 (v + 1) L_pre) R_t0) =
      some (mMkL 10 (mRep1 v L_pre) (mCons 1 R_t0)) := by
    rw [mRep1_succ]
    exact mStep_mMkL_left (by rfl) _ _
  have hL_z_cons : mCons 0 L_z = mRep0 ((z + 1) + 2) (mCons 1 L) := by
    dsimp only [L_z]
    rw [← mRep0_succ]
    exact congrArg (fun x ↦ mRep0 x (mCons 1 L)) (by ring)
  have hz4 : (z + 1) + 3 = z + 4 := by ring
  rcases eq_zero_or_exists_succ v with hv | ⟨v', hv⟩
  · refine ⟨fun _ ↦ ?_, fun hne ↦ absurd hv hne⟩
    rw [hv] at hscan_v he0 hd1
    rw [mRep1_zero] at hd1
    obtain ⟨rs_init, u_last, hpre_snoc⟩ : ∃ rs_init u_last, rs_pre = rs_init ++ [u_last] := by
      rcases rs_pre.eq_nil_or_concat with hnil | ⟨rs_init, u_last, hcat⟩
      · exact absurd hnil hrs_ne
      · exact ⟨rs_init, u_last, by rw [hcat, List.concat_eq_append]⟩
    have hL_pre_0 :
        L_pre = mCons 0 (mRep1 (u_last + 1) (mAppendRegsRev rs_init (mCons 0 L_z))) := by
      dsimp only [L_pre]
      rw [hpre_snoc, mAppendRegsRev_snoc]
      rfl
    have hg0 : mStep zf393 (mMkL 10 L_pre (mCons 1 R_t0)) =
        some (mMkL 26 (mRep1 (u_last + 1) (mAppendRegsRev rs_init (mCons 0 L_z)))
          (mCons 0 (mCons 1 R_t0))) := by
      rw [hL_pre_0]
      exact mStep_mMkL_left (by rfl) _ _
    have hscan_last := mLeftScan_reach (q := 26) (a := 1) (b := 1) (by rfl) (u_last + 1)
      (mAppendRegsRev rs_init (mCons 0 L_z)) (mCons 0 (mCons 1 R_t0))
    rw [mRepBit_one_bit, mRepBit_one_bit] at hscan_last
    conv at hscan_last => arg 2; rw [hL_z_cons]
    have hret := mRet2_finish rs_init (z + 1) L (mRep1 (u_last + 1) (mCons 0 (mCons 1 R_t0)))
    have hR_eq : mAppendRegs rs_init (mRep1 (u_last + 1) (mCons 0 (mCons 1 R_t0))) =
        mAppendRegs pre (mRegsTape regs_tape) := by
      have henc0 : mCons 1 R_t0 = mRegsTape (0 :: rs_tail) := by
        unfold R_t0 mRegsTape
        rw [mAppendRegs_cons, mEncodeReg, mRep1_succ, mRep1_zero]
      have henc_u : mRep1 (u_last + 1) (mCons 0 (mRegsTape (0 :: rs_tail))) =
          mAppendRegs [u_last] (mRegsTape (0 :: rs_tail)) := by
        simp [mEncodeReg]
      have hr_list : rs_init ++ [u_last] ++ (0 :: rs_tail) = pre ++ regs_tape := by
        rw [← hpre_snoc, ← hv, ← hdrop]
        dsimp only [rs_pre, v, rs_tail]
        rw [List.append_assoc, List.take_append_drop]
      rw [henc0, henc_u, ← mAppendRegs_append, ← mRegsTape_append, hr_list, mRegsTape_append]
    rw [hz4, hR_eq] at hret
    exact mStep_mReachPos hs1 (mReach_trans hscan0
      (mReach_trans (mReachPos_to_mReach h6_shift)
        (mReach_trans hscan_v (mStep_mReach he0 (mStep_mReach hd1
          (mStep_mReach hg0 (mReach_trans hscan_last (mReachPos_to_mReach hret))))))))
  · refine ⟨fun h0 ↦ absurd (hv.symm.trans h0) (add_one_ne_zero v'), fun _ ↦ ?_⟩
    rw [hv] at hscan_v he0 hd1
    conv at hd1 => rhs; rw [mRep1_succ]
    have hg1 : mStep zf393 (mMkL 10 (mCons 1 (mRep1 v' L_pre)) (mCons 1 R_t0)) =
        some (mMk' 11 (mCons 1 (mRep1 v' L_pre)) (mCons 1 R_t0)) :=
      mStep_mMkL_right (by rfl) _ _
    have hh1 : mStep zf393 (mMk' 11 (mCons 1 (mRep1 v' L_pre)) (mCons 1 R_t0)) =
        some (mMk' 11 (mEncodeRegRev v' L_pre) R_t0) := by
      have h := mStep_mMk'_right (q := 11) (q' := 11) (a := 1) (b := 0) (by rfl)
        (mCons 1 (mRep1 v' L_pre)) R_t0
      have henc : mCons 0 (mCons 1 (mRep1 v' L_pre)) = mEncodeRegRev v' L_pre := by
        simp [mEncodeRegRev, mRep1_succ]
      rwa [henc] at h
    have hleft := mDecnz_shift_left rs_tail (mEncodeRegRev v' L_pre)
    have hL_all : mAppendRegsRev rs_tail (mEncodeRegRev v' L_pre) =
        mAppendRegsRev (rs_pre ++ [v'] ++ rs_tail) (mRep0 ((z + 1) + 2) (mCons 1 L)) := by
      change mAppendRegsRev rs_tail
          (mEncodeRegRev v' (mAppendRegsRev rs_pre (mCons 0 L_z))) = _
      rw [← mAppendRegsRev_snoc, ← mAppendRegsRev_append, hL_z_cons]
    rw [hL_all] at hleft
    have hret := mRet1_finish (rs_pre ++ [v'] ++ rs_tail) (z + 1) L 0
    have hv_sub : regs_tape[r.val] - 1 = v' := by
      change v - 1 = v'
      rw [hv, add_sub_cancel_right_pam]
    have htake_set_drop : ∀ (xs : List (PAM M)) (i : ℕ) (w : PAM M),
        i < xs.length → xs.take i ++ (w :: xs.drop (i + 1)) = xs.set i w := by
      intro xs i w hi
      induction xs generalizing i with
      | nil => simp at hi
      | cons x xs ih =>
        cases i with
        | zero => rfl
        | succ i => simp [ih i (by simpa using hi)]
    have hR_eq : mAppendRegs (rs_pre ++ [v'] ++ rs_tail) 0 =
        mAppendRegs pre (mRegsTape (regs_tape.set r.val (regs_tape[r.val] - 1))) := by
      rw [hv_sub]
      change mRegsTape (rs_pre ++ [v'] ++ rs_tail) = _
      have hr_eq : rs_pre ++ [v'] ++ rs_tail = pre ++ regs_tape.set r.val v' := by
        simp only [rs_pre, rs_tail, List.append_assoc, List.singleton_append]
        rw [htake_set_drop regs_tape r.val v' (by omega)]
      rw [hr_eq, mRegsTape_append]
    rw [hz4, hR_eq] at hret
    exact mStep_mReachPos hs1 (mReach_trans hscan0
      (mReach_trans (mReachPos_to_mReach h6_shift)
        (mReach_trans hscan_v (mStep_mReach he0 (mStep_mReach hd1
          (mStep_mReach hg1 (mStep_mReach hh1
            (mReachPos_to_mReach (mReachPos_trans hleft hret)))))))))

theorem mDecnz_step_reaches_main0 (r : Fin 11) (slot : PAM M) (walked : List (Fin 2))
    (hsl : ((walked.length + (11 - r.val) + 3 : ℕ) : PAM M) ≤ slot)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true)
    (regs_tape : List (PAM M)) (hregs : regs_tape.length = 11) :
    (regs_tape[r.val] = 0 →
      mReachPos
        (mMk' 5 (mAppend (walked ++ List.replicate (11 - r.val) 1).reverse mLB01)
          (mRep0 (slot - ((walked.length + (11 - r.val) : ℕ) : PAM M))
            (mZf393SelRight pre (11 - r.val) regs_tape)))
        (mRootCfg pre (mBreakSlot 1 (slot + 1) walked)
          ((popBreakRev 1 walked.reverse).reverse) regs_tape)) ∧
    (regs_tape[r.val] ≠ 0 →
      mReachPos
        (mMk' 5 (mAppend (walked ++ List.replicate (11 - r.val) 1).reverse mLB01)
          (mRep0 (slot - ((walked.length + (11 - r.val) : ℕ) : PAM M))
            (mZf393SelRight pre (11 - r.val) regs_tape)))
        (mRootCfg pre (mBreakSlot 0 (slot + 1) walked) (retStack walked)
          (regs_tape.set r.val (regs_tape[r.val] - 1)))) := by
  set m := 11 - r.val
  set base : PAM M := ((walked.length + m : ℕ) : PAM M)
  have hbase3 : base + 3 ≤ slot := by
    dsimp only [base, m]
    simpa [Nat.cast_add] using hsl
  have hle : base ≤ slot := le_trans (le_add_right_pam base 3) hbase3
  set z := slot - (base + 3)
  have hz_eq : slot - base = z + 3 := by
    dsimp only [z]
    rw [sub_eq_iff_eq_add_pam hle]
    calc slot
      _ = (base + 3) + (slot - (base + 3)) := (add_sub_of_le_pam hbase3).symm
      _ = base + (slot - (base + 3) + 3) := by ring
  rw [hz_eq]
  have hs₁ := @mDecnz_pass_to_break M _ _ pre hpre r z regs_tape hregs
    (mAppend (walked ++ List.replicate m 1).reverse mLB01)
  have hscan_ones : ∀ n xs, scanZerosOk 0 (List.replicate n (1 : Fin 2) ++ xs) =
      scanZerosOk 0 xs := by
    intro n xs; induction n with
    | zero => rfl
    | succ n ih => exact ih
  have hok_m : scanZerosOk 0 ((walked ++ List.replicate m 1).reverse ++ [1]) = true := by
    rw [List.reverse_append, List.reverse_replicate, List.append_assoc, hscan_ones m]
    exact hok
  have hlen_m : ((walked ++ List.replicate m 1).length : PAM M) ≤ slot + 1 := by
    rw [List.length_append, List.length_replicate]
    exact le_trans hle (le_add_right_pam slot 1)
  have hsub_m : (slot + 1) - ((walked ++ List.replicate m 1).length : PAM M) = z + 4 := by
    rw [List.length_append, List.length_replicate]
    change (slot + 1) - base = z + 4
    rw [add_one_sub_of_le_pam hle, hz_eq]
    ring
  refine ⟨fun hv0 ↦ ?_, fun hvne ↦ ?_⟩
  · have hs₂ := @mBreak_k_reaches_main0 M _ _ pre 1 (by decide) (slot + 1)
      (walked ++ List.replicate m 1) hlen_m hok_m regs_tape
    have hpop : (popBreakRev 1 (walked ++ List.replicate m 1).reverse).reverse =
        (popBreakRev 1 walked.reverse).reverse := by
      rw [List.reverse_append, List.reverse_replicate, popBreakRev_replicate_one_append]
    rw [hsub_m, hpop, mBreakSlot_append_ones] at hs₂
    exact mReachPos_trans (hs₁.1 hv0) hs₂
  · have hs₂ := @mBreak_k_reaches_main0 M _ _ pre 0 (by decide) (slot + 1)
      (walked ++ List.replicate m 1) hlen_m hok_m
      (regs_tape.set r.val (regs_tape[r.val] - 1))
    have hpop : (popBreakRev 0 (walked ++ List.replicate m 1).reverse).reverse =
        retStack walked := by
      rw [List.reverse_append, List.reverse_replicate, popBreakRev_replicate_one_append]
      rfl
    rw [hsub_m, hpop, mBreakSlot_append_ones] at hs₂
    exact mReachPos_trans (hs₁.2 hvne) hs₂

omit hpre in
theorem mStage3_walk_ones_inc (r : Fin 11) (j : ℕ) (hj : r.val + j ≤ 10) (L R : PAM M) :
    mReach (mMk' (regIncStage3 r) L (mAppend (List.replicate j 1) R))
      (mMk' (regIncStage3 ⟨r.val + j, by omega⟩) (mAppend (List.replicate j 1) L) R) := by
  induction j generalizing r L with
  | zero =>
    simp only [Nat.add_zero, Fin.eta, List.replicate_zero, mAppend_nil]
    exact mReach_refl _
  | succ j ih =>
    have htr1 : zf393Trans (regIncStage3 r) 1 =
        some (1, .right, regIncStage3 ⟨r.val + 1, by omega⟩) :=
      regIncStage3_step1 ⟨r.val, by omega⟩
    rw [List.replicate_succ, mAppend_cons]
    have hs1 := mStep_mMk'_right htr1 L (mAppend (List.replicate j 1) R)
    have hj' : (⟨r.val + 1, by omega⟩ : Fin 11).val + j ≤ 10 := by dsimp; omega
    have hrest := ih ⟨r.val + 1, by omega⟩ hj' (mCons 1 L)
    have hidx : (⟨(⟨r.val + 1, by omega⟩ : Fin 11).val + j, by omega⟩ : Fin 11) =
        ⟨r.val + (j + 1), by omega⟩ := by
      ext; dsimp; omega
    have hL : mAppend (List.replicate j 1) (mCons 1 L) =
        mCons 1 (mAppend (List.replicate j 1) L) := by
      rw [mAppend_replicate_one, mAppend_replicate_one, mRep1_inner_cons]
    rw [hL, hidx] at hrest
    exact mStep_mReach hs1 hrest

omit hpre in
theorem mStage3_walk_ones_decnz (r : Fin 11) (j : ℕ) (hj : r.val + j ≤ 10) (L R : PAM M) :
    mReach (mMk' (regDecnzStage3 r) L (mAppend (List.replicate j 1) R))
      (mMk' (regDecnzStage3 ⟨r.val + j, by omega⟩) (mAppend (List.replicate j 1) L) R) := by
  induction j generalizing r L with
  | zero =>
    simp only [Nat.add_zero, Fin.eta, List.replicate_zero, mAppend_nil]
    exact mReach_refl _
  | succ j ih =>
    have htr1 : zf393Trans (regDecnzStage3 r) 1 =
        some (1, .right, regDecnzStage3 ⟨r.val + 1, by omega⟩) :=
      regDecnzStage3_step1 ⟨r.val, by omega⟩
    rw [List.replicate_succ, mAppend_cons]
    have hs1 := mStep_mMk'_right htr1 L (mAppend (List.replicate j 1) R)
    have hj' : (⟨r.val + 1, by omega⟩ : Fin 11).val + j ≤ 10 := by dsimp; omega
    have hrest := ih ⟨r.val + 1, by omega⟩ hj' (mCons 1 L)
    have hidx : (⟨(⟨r.val + 1, by omega⟩ : Fin 11).val + j, by omega⟩ : Fin 11) =
        ⟨r.val + (j + 1), by omega⟩ := by
      ext; dsimp; omega
    have hL : mAppend (List.replicate j 1) (mCons 1 L) =
        mCons 1 (mAppend (List.replicate j 1) L) := by
      rw [mAppend_replicate_one, mAppend_replicate_one, mRep1_inner_cons]
    rw [hL, hidx] at hrest
    exact mStep_mReach hs1 hrest

/-! ## Section 6: Decision-Tree Dispatcher & `mTm_simulates_evalStack` -/

/-- Tree-walk configuration in `MCfg 393 M`. -/
noncomputable def mTreeWalkCfg (q : Fin 393) (walked rem : List (Fin 2))
    (L₀ R_tail : PAM M) : MCfg 393 M :=
  mMk' q (mAppend walked.reverse L₀) (mAppend rem R_tail)

omit hpre in
theorem mWalkTape_sound (q : Fin 393) (walked rem : List (Fin 2)) (L₀ R_tail : PAM M) :
    match walkTape q walked rem with
    | .halt q_h walked_h rem_h =>
      mReach (mTreeWalkCfg q walked rem L₀ R_tail) (mTreeWalkCfg q_h walked_h rem_h L₀ R_tail) ∧
      mStep zf393 (mTreeWalkCfg q_h walked_h rem_h L₀ R_tail) = none
    | .jumpLeft q' walked_j rem' =>
      (∃ b, walked_j ++ (b :: rem') = walked ++ rem) ∧
      mReachPos (mTreeWalkCfg q walked rem L₀ R_tail)
        (mMkL q' (mAppend walked_j.reverse L₀) (mAppend (0 :: rem') R_tail))
    | .regLeaf q' walked_l rem' =>
      walked_l ++ rem' = walked ++ rem ∧
      mReachPos (mTreeWalkCfg q walked rem L₀ R_tail) (mTreeWalkCfg q' walked_l rem' L₀ R_tail)
    | .outOfFuel => True := by
  induction rem generalizing q walked with
  | nil => trivial
  | cons b rem' ih =>
    simp only [walkTape]
    rcases htr : zf393Trans q b with _ | ⟨w, d, q'⟩
    · refine ⟨mReach_refl _, ?_⟩
      exact mStep_mMk'_none htr (mAppend walked.reverse L₀) (mAppend rem' R_tail)
    · cases d with
      | left =>
        by_cases hw : (w == 0) = true
        · simp only [hw, ↓reduceIte]
          have hw0 : w = 0 := beq_iff_eq.mp hw
          subst hw0
          refine ⟨⟨b, rfl⟩, ?_⟩
          exact mReachPos_step
            (mStep_mMk'_left htr (mAppend walked.reverse L₀) (mAppend rem' R_tail))
        · simp only [hw, Bool.false_eq_true, ↓reduceIte]
      | right =>
        by_cases hw : (w == b) = true
        · simp only [hw, ↓reduceIte]
          have hwb : w = b := beq_iff_eq.mp hw
          subst hwb
          have hstep1 : mStep zf393 (mTreeWalkCfg q walked (w :: rem') L₀ R_tail) =
              some (mTreeWalkCfg q' (walked ++ [w]) rem' L₀ R_tail) := by
            unfold mTreeWalkCfg
            rw [mAppend_cons, mStep_mMk'_right htr, mAppend_reverse_cons]
          by_cases hleaf : isLeafState q' = true
          · simp only [hleaf, ↓reduceIte]
            exact ⟨by simp, mReachPos_step hstep1⟩
          · simp only [hleaf, Bool.false_eq_true, ↓reduceIte]
            have hrec := ih q' (walked ++ [w])
            rcases hout : walkTape q' (walked ++ [w]) rem' with
              ⟨q_h, w_h, r_h⟩ | ⟨q_j, w_j, r_j⟩ | ⟨q_l, w_l, r_l⟩ | _
            · rw [hout] at hrec
              exact ⟨mStep_mReach hstep1 hrec.1, hrec.2⟩
            · rw [hout] at hrec
              obtain ⟨⟨b', heq⟩, hs⟩ := hrec
              exact ⟨⟨b', by simpa using heq⟩, mStep_mReachPos hstep1 (mReachPos_to_mReach hs)⟩
            · rw [hout] at hrec
              obtain ⟨heq, hs⟩ := hrec
              exact ⟨by simpa using heq, mStep_mReachPos hstep1 (mReachPos_to_mReach hs)⟩
            · trivial
        · simp only [hw, Bool.false_eq_true, ↓reduceIte]

theorem mInc_leaf_reaches_main0 (r : Fin 11) (slot : PAM M) (walked : List (Fin 2))
    (hwalk : walkTape 99 [] walked = .regLeaf (regIncStage3 r) walked [])
    (hsl : ((walked.length + (11 - r.val) + 3 : ℕ) : PAM M) ≤ slot)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true)
    (regs_tape : List (PAM M)) (hregs : regs_tape.length = 11) :
    mReachPos
      (mMk' 99 mLB01
        (mAppend walked (mRep0 (slot - (walked.length : PAM M))
          (mAppendRegs pre (mRegsTape regs_tape)))))
      (mRootCfg pre (mBreakSlot 0 slot walked) (retStack walked)
        (regs_tape.set r.val (regs_tape[r.val] + 1))) := by
  have walk_exact : ∀ (R_rem : PAM M),
      mReachPos
        (mMk' 99 mLB01 (mAppend walked R_rem))
        (mMk' (regIncStage3 r) (mAppend walked.reverse mLB01) R_rem) := by
    intro R_rem
    have hws := mWalkTape_sound 99 [] walked mLB01 R_rem
    rw [hwalk] at hws
    simpa [mTreeWalkCfg] using hws.2
  have loop : ∀ m k : ℕ, m + k = 11 - r.val →
      mReachPos
        (mMk' 99 mLB01
          (mAppend walked
            (mAppend (List.replicate m 1)
              (mRep0 (slot - ((walked.length + m : ℕ) : PAM M))
                (mZf393SelRight pre m regs_tape)))))
        (mRootCfg pre (mBreakSlot 0 slot walked) (retStack walked)
          (regs_tape.set r.val (regs_tape[r.val] + 1))) := by
    intro m k hmk
    induction k generalizing m with
    | zero =>
      have hm_eq : m = 11 - r.val := by omega
      subst hm_eq
      have hrep_split : List.replicate (11 - r.val) (1 : Fin 2) =
          List.replicate (10 - r.val) 1 ++ [1] := by
        have h11 : 11 - r.val = (10 - r.val) + 1 := by omega
        rw [h11, List.replicate_succ']
      rw [hrep_split, mAppend_append]
      set R_sel := mRep0 (slot - ((walked.length + (11 - r.val) : ℕ) : PAM M))
        (mZf393SelRight pre (11 - r.val) regs_tape)
      have hsw := walk_exact (mAppend (List.replicate (10 - r.val) 1) (mAppend [1] R_sel))
      have hones := mStage3_walk_ones_inc r (10 - r.val) (by omega)
        (mAppend walked.reverse mLB01) (mAppend [1] R_sel)
      have hr10 : (⟨r.val + (10 - r.val), by omega⟩ : Fin 11) = 10 := by ext; dsimp; omega
      rw [hr10] at hones
      have hs10 : mStep zf393
          (mMk' (regIncStage3 10)
            (mAppend (List.replicate (10 - r.val) 1) (mAppend walked.reverse mLB01))
            (mAppend [1] R_sel)) =
          some (mMk' 13
            (mAppend (walked ++ List.replicate (11 - r.val) 1).reverse mLB01) R_sel) := by
        have h := mStep_mMk'_right (q := regIncStage3 10) (q' := 13) (a := 1) (b := 1) (by rfl)
          (mAppend (List.replicate (10 - r.val) 1) (mAppend walked.reverse mLB01)) R_sel
        have hL_eq : mCons 1 (mAppend (List.replicate (10 - r.val) 1)
            (mAppend walked.reverse (mLB01 : PAM M))) =
            mAppend (walked ++ List.replicate (11 - r.val) 1).reverse (mLB01 : PAM M) := by
          rw [hrep_split, List.reverse_append, List.reverse_append, List.reverse_replicate,
            mAppend_append, mAppend_append]
          rfl
        rwa [hL_eq] at h
      have hinc := @mInc_step_reaches_main0 M _ _ pre hpre r slot walked hsl hok regs_tape hregs
      exact mReachPos_trans (mReachPos_mReach hsw hones)
        (mStep_mReachPos hs10 (mReachPos_to_mReach hinc))
    | succ k' ih =>
      have hrm : r.val + m < 11 := by omega
      have hsl_m : ((walked.length + m + 4 : ℕ) : PAM M) ≤ slot :=
        le_trans (natCast_le_iff.mpr (by omega)) hsl
      have hlt_slot : ((walked.length + m : ℕ) : PAM M) < slot :=
        lt_of_lt_of_le (by
          have : walked.length + m < walked.length + m + 4 := by omega
          exact natCast_lt_iff.mpr this) hsl_m
      set R_m := mZf393SelRight pre m regs_tape
      have hsw := walk_exact
        (mAppend (List.replicate m 1)
          (mRep0 (slot - ((walked.length + m : ℕ) : PAM M)) R_m))
      have hones := mStage3_walk_ones_inc r m (by omega)
        (mAppend walked.reverse mLB01)
        (mRep0 (slot - ((walked.length + m : ℕ) : PAM M)) R_m)
      have hsub_z : slot - ((walked.length + m : ℕ) : PAM M) =
          (slot - ((walked.length + m + 1 : ℕ) : PAM M)) + 1 := by
        simpa [Nat.cast_add] using sub_add_one_of_lt_pam hlt_slot
      rw [hsub_z, mRep0_succ] at hsw hones ⊢
      have htr0 : zf393Trans (regIncStage3 ⟨r.val + m, hrm⟩) 0 = some (0, .right, 17) :=
        regIncStage3_step0 ⟨r.val + m, hrm⟩
      have hs0 : mStep zf393
          (mMk' (regIncStage3 ⟨r.val + m, hrm⟩)
            (mAppend (List.replicate m 1) (mAppend walked.reverse mLB01))
            (mCons 0 (mRep0 (slot - ((walked.length + m + 1 : ℕ) : PAM M)) R_m))) =
          some (mMk' 17 (mAppend (walked ++ List.replicate m 1 ++ [0]).reverse mLB01)
            (mRep0 (slot - ((walked.length + m + 1 : ℕ) : PAM M)) R_m)) := by
        have h := mStep_mMk'_right htr0
          (mAppend (List.replicate m 1) (mAppend walked.reverse mLB01))
          (mRep0 (slot - ((walked.length + m + 1 : ℕ) : PAM M)) R_m)
        have hL_eq : mCons 0 (mAppend (List.replicate m 1)
            (mAppend walked.reverse (mLB01 : PAM M))) =
            mAppend (walked ++ List.replicate m 1 ++ [0]).reverse (mLB01 : PAM M) := by
          simp [List.reverse_append, mAppend_append]
        rwa [hL_eq] at h
      have hsel := @mSel_step_reaches_main0 M _ _ pre hpre m (by omega) slot walked
        hsl_m hok regs_tape hregs
      have hrest := ih (m + 1) (by omega)
      rw [mAppend_append] at hsel
      have hadd_assoc : walked.length + (m + 1) = walked.length + m + 1 := by omega
      rw [hadd_assoc] at hrest
      exact mReachPos_trans (mReachPos_mReach hsw hones)
        (mStep_mReachPos hs0 (mReachPos_to_mReach (mReachPos_trans hsel hrest)))
  have hs := loop 0 (11 - r.val) (Nat.zero_add _)
  simpa only [List.replicate_zero, Nat.add_zero, mZf393SelRight_zero pre regs_tape hregs,
    mAppend_nil] using hs

theorem mDecnz_leaf_reaches_main0 (r : Fin 11) (slot : PAM M) (walked : List (Fin 2))
    (hwalk : walkTape 99 [] walked = .regLeaf (regDecnzStage3 r) walked [])
    (hsl : ((walked.length + (11 - r.val) + 3 : ℕ) : PAM M) ≤ slot)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true)
    (regs_tape : List (PAM M)) (hregs : regs_tape.length = 11) :
    (regs_tape[r.val] = 0 →
      mReachPos
        (mMk' 99 mLB01
          (mAppend walked (mRep0 (slot - (walked.length : PAM M))
            (mAppendRegs pre (mRegsTape regs_tape)))))
        (mRootCfg pre (mBreakSlot 1 (slot + 1) walked)
          ((popBreakRev 1 walked.reverse).reverse) regs_tape)) ∧
    (regs_tape[r.val] ≠ 0 →
      mReachPos
        (mMk' 99 mLB01
          (mAppend walked (mRep0 (slot - (walked.length : PAM M))
            (mAppendRegs pre (mRegsTape regs_tape)))))
        (mRootCfg pre (mBreakSlot 0 (slot + 1) walked) (retStack walked)
          (regs_tape.set r.val (regs_tape[r.val] - 1)))) := by
  have walk_exact : ∀ (R_rem : PAM M),
      mReachPos
        (mMk' 99 mLB01 (mAppend walked R_rem))
        (mMk' (regDecnzStage3 r) (mAppend walked.reverse mLB01) R_rem) := by
    intro R_rem
    have hws := mWalkTape_sound 99 [] walked mLB01 R_rem
    rw [hwalk] at hws
    simpa [mTreeWalkCfg] using hws.2
  have sel_passes : ∀ m k : ℕ, m + k = 11 - r.val →
      mReach
        (mMk' 99 mLB01
          (mAppend walked
            (mAppend (List.replicate m 1)
              (mRep0 (slot - ((walked.length + m : ℕ) : PAM M))
                (mZf393SelRight pre m regs_tape)))))
        (mMk' 99 mLB01
          (mAppend walked
            (mAppend (List.replicate (11 - r.val) 1)
              (mRep0 (slot - ((walked.length + (11 - r.val) : ℕ) : PAM M))
                (mZf393SelRight pre (11 - r.val) regs_tape))))) := by
    intro m k hmk
    induction k generalizing m with
    | zero =>
      have hm_eq : m = 11 - r.val := by omega
      subst hm_eq
      exact mReach_refl _
    | succ k' ih =>
      have hrm : r.val + m < 11 := by omega
      have hsl_m : ((walked.length + m + 4 : ℕ) : PAM M) ≤ slot :=
        le_trans (natCast_le_iff.mpr (by omega)) hsl
      have hlt_slot : ((walked.length + m : ℕ) : PAM M) < slot :=
        lt_of_lt_of_le (by
          have : walked.length + m < walked.length + m + 4 := by omega
          exact natCast_lt_iff.mpr this) hsl_m
      set R_m := mZf393SelRight pre m regs_tape
      have hsw := walk_exact
        (mAppend (List.replicate m 1)
          (mRep0 (slot - ((walked.length + m : ℕ) : PAM M)) R_m))
      have hones := mStage3_walk_ones_decnz r m (by omega)
        (mAppend walked.reverse mLB01)
        (mRep0 (slot - ((walked.length + m : ℕ) : PAM M)) R_m)
      have hsub_z : slot - ((walked.length + m : ℕ) : PAM M) =
          (slot - ((walked.length + m + 1 : ℕ) : PAM M)) + 1 := by
        simpa [Nat.cast_add] using sub_add_one_of_lt_pam hlt_slot
      rw [hsub_z, mRep0_succ] at hsw hones
      have htr0 : zf393Trans (regDecnzStage3 ⟨r.val + m, hrm⟩) 0 = some (0, .right, 17) :=
        regDecnzStage3_step0 ⟨r.val + m, hrm⟩
      have hs0 : mStep zf393
          (mMk' (regDecnzStage3 ⟨r.val + m, hrm⟩)
            (mAppend (List.replicate m 1) (mAppend walked.reverse mLB01))
            (mCons 0 (mRep0 (slot - ((walked.length + m + 1 : ℕ) : PAM M)) R_m))) =
          some (mMk' 17 (mAppend (walked ++ List.replicate m 1 ++ [0]).reverse mLB01)
            (mRep0 (slot - ((walked.length + m + 1 : ℕ) : PAM M)) R_m)) := by
        have h := mStep_mMk'_right htr0
          (mAppend (List.replicate m 1) (mAppend walked.reverse mLB01))
          (mRep0 (slot - ((walked.length + m + 1 : ℕ) : PAM M)) R_m)
        have hL_eq : mCons 0 (mAppend (List.replicate m 1)
            (mAppend walked.reverse (mLB01 : PAM M))) =
            mAppend (walked ++ List.replicate m 1 ++ [0]).reverse (mLB01 : PAM M) := by
          simp [List.reverse_append, mAppend_append]
        rwa [hL_eq] at h
      have hsel := @mSel_step_reaches_main0 M _ _ pre hpre m (by omega) slot walked
        hsl_m hok regs_tape hregs
      have hrest := ih (m + 1) (by omega)
      rw [mAppend_append] at hsel
      have hadd_assoc : walked.length + (m + 1) = walked.length + m + 1 := by omega
      rw [hadd_assoc] at hrest
      have hfirst : mReach
          (mMk' 99 mLB01
            (mAppend walked
              (mAppend (List.replicate m 1)
                (mRep0 (slot - ((walked.length + m : ℕ) : PAM M)) R_m))))
          (mMk' 99 mLB01
            (mAppend walked
              (mAppend (List.replicate (m + 1) 1)
                (mRep0 (slot - ((walked.length + m + 1 : ℕ) : PAM M))
                  (mZf393SelRight pre (m + 1) regs_tape))))) := by
        rw [hsub_z, mRep0_succ]
        exact mReachPos_to_mReach (mReachPos_trans (mReachPos_mReach hsw hones)
          (mStep_mReachPos hs0 (mReachPos_to_mReach hsel)))
      exact mReach_trans hfirst hrest
  have hpasses0 := sel_passes 0 (11 - r.val) (Nat.zero_add _)
  simp only [List.replicate_zero, Nat.add_zero, mZf393SelRight_zero pre regs_tape hregs,
    mAppend_nil] at hpasses0
  have hrep_split : List.replicate (11 - r.val) (1 : Fin 2) =
      List.replicate (10 - r.val) 1 ++ [1] := by
    have h11 : 11 - r.val = (10 - r.val) + 1 := by omega
    rw [h11, List.replicate_succ']
  set R_sel := mRep0 (slot - ((walked.length + (11 - r.val) : ℕ) : PAM M))
    (mZf393SelRight pre (11 - r.val) regs_tape)
  have hsw := walk_exact (mAppend (List.replicate (10 - r.val) 1) (mAppend [1] R_sel))
  have hones := mStage3_walk_ones_decnz r (10 - r.val) (by omega)
    (mAppend walked.reverse mLB01) (mAppend [1] R_sel)
  have hr10 : (⟨r.val + (10 - r.val), by omega⟩ : Fin 11) = 10 := by ext; dsimp; omega
  rw [hr10] at hones
  have hs10 : mStep zf393
      (mMk' (regDecnzStage3 10)
        (mAppend (List.replicate (10 - r.val) 1) (mAppend walked.reverse mLB01))
        (mAppend [1] R_sel)) =
      some (mMk' 5
        (mAppend (walked ++ List.replicate (11 - r.val) 1).reverse mLB01) R_sel) := by
    have h := mStep_mMk'_right (q := regDecnzStage3 10) (q' := 5) (a := 1) (b := 1) (by rfl)
      (mAppend (List.replicate (10 - r.val) 1) (mAppend walked.reverse mLB01)) R_sel
    have hL_eq : mCons 1 (mAppend (List.replicate (10 - r.val) 1)
        (mAppend walked.reverse (mLB01 : PAM M))) =
        mAppend (walked ++ List.replicate (11 - r.val) 1).reverse (mLB01 : PAM M) := by
      rw [hrep_split, List.reverse_append, List.reverse_append, List.reverse_replicate,
        mAppend_append, mAppend_append]
      rfl
    rwa [hL_eq] at h
  have hto5 : mReachPos
      (mMk' 99 mLB01
        (mAppend walked (mRep0 (slot - (walked.length : PAM M))
          (mAppendRegs pre (mRegsTape regs_tape)))))
      (mMk' 5 (mAppend (walked ++ List.replicate (11 - r.val) 1).reverse mLB01) R_sel) := by
    rw [hrep_split, mAppend_append] at hpasses0
    exact mReach_mReachPos hpasses0
      (mReachPos_trans (mReachPos_mReach hsw hones) (mReachPos_step hs10))
  have hdec := @mDecnz_step_reaches_main0 M _ _ pre hpre r slot walked hsl hok regs_tape hregs
  exact ⟨fun hv0 ↦ mReachPos_trans hto5 (hdec.1 hv0),
    fun hvne ↦ mReachPos_trans hto5 (hdec.2 hvne)⟩

end GenericPrefix

/-- Logical Layer 1/2 invariant in `PAM M`: `regs` has length `11`, `ip.length ≤ 136`,
`staysInDag 99 ip.dropLast = true`, and `(minSlot ip : PAM M) ≤ slot`. -/
def MZfLogInv (slot : PAM M) (ip : List (Fin 2)) (regs : List (PAM M)) : Prop :=
  regs.length = 11 ∧ ip.length ≤ 136 ∧
  staysInDag 99 ip.dropLast = true ∧ (minSlot ip : PAM M) ≤ slot

theorem mZfLogInv_init : MZfLogInv (19 : PAM M) [] (List.replicate 11 (0 : PAM M)) :=
  ⟨by simp, by decide, by decide, natCast_le_iff.mpr zf393Inv_init.2.2.2⟩

omit [PAModel M] in
theorem mRev11_getD_set {regs : List (PAM M)} (hlen : regs.length = 11) (k : Fin 11) :
    (regs.reverse)[k.val]'(by rw [List.length_reverse, hlen]; exact k.isLt) =
      regs.getD (10 - k.val) 0 ∧
    ∀ v, regs.reverse.set k.val v = (regs.set (10 - k.val) v).reverse := by
  rcases regs with _ | ⟨r0, _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, _ | ⟨r4, _ | ⟨r5, _ |
    ⟨r6, _ | ⟨r7, _ | ⟨r8, _ | ⟨r9, _ | ⟨r10, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen; done)
  rcases k with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, hn⟩
  · exact ⟨rfl, fun _ ↦ rfl⟩
  · exact ⟨rfl, fun _ ↦ rfl⟩
  · exact ⟨rfl, fun _ ↦ rfl⟩
  · exact ⟨rfl, fun _ ↦ rfl⟩
  · exact ⟨rfl, fun _ ↦ rfl⟩
  · exact ⟨rfl, fun _ ↦ rfl⟩
  · exact ⟨rfl, fun _ ↦ rfl⟩
  · exact ⟨rfl, fun _ ↦ rfl⟩
  · exact ⟨rfl, fun _ ↦ rfl⟩
  · exact ⟨rfl, fun _ ↦ rfl⟩
  · exact ⟨rfl, fun _ ↦ rfl⟩
  · exfalso; omega

/-- Forward 1-step logical stack-instruction simulation in `PAM M`: from `mZfLogCfg slot ip regs`
satisfying `MZfLogInv slot ip regs`, `Machines.zf393` executes `evalStack ip` in `≥ 1` steps (or
halts if `evalStack ip = .halt`) while preserving `MZfLogInv`. -/
theorem mTm_simulates_evalStack {slot : PAM M} {ip : List (Fin 2)} {regs : List (PAM M)}
    (hinv : MZfLogInv slot ip regs) :
    match evalStack ip with
    | .halt =>
      mHaltsFrom zf393 (mZfLogCfg slot ip regs)
    | .jump ip' =>
      ∃ slot' : PAM M, MZfLogInv slot' ip' regs ∧
        mReachPos (mZfLogCfg slot ip regs) (mZfLogCfg slot' ip' regs)
    | .inc r ip' =>
      ∃ slot' : PAM M, MZfLogInv slot' ip' (regs.set r (regs.getD r 0 + 1)) ∧
        mReachPos (mZfLogCfg slot ip regs)
          (mZfLogCfg slot' ip' (regs.set r (regs.getD r 0 + 1)))
    | .decnz r ip_succ ip_fail =>
      (regs.getD r 0 = 0 →
        ∃ slot' : PAM M, MZfLogInv slot' ip_fail regs ∧
          mReachPos (mZfLogCfg slot ip regs) (mZfLogCfg slot' ip_fail regs)) ∧
      (regs.getD r 0 ≠ 0 →
        ∃ slot' : PAM M, MZfLogInv slot' ip_succ (regs.set r (regs.getD r 0 - 1)) ∧
          mReachPos (mZfLogCfg slot ip regs)
            (mZfLogCfg slot' ip_succ (regs.set r (regs.getD r 0 - 1)))) := by
  obtain ⟨hregs, hip136, hdag_in, hmin⟩ := hinv
  have hregs_rev : regs.reverse.length = 11 := by rw [List.length_reverse, hregs]
  have hdag_walk := walkTape_dag_props 99 [] ip (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hstays_walk := staysInDag_of_walkTape 99 [] (ip ++ List.replicate 10 0)
  have hpad_data : ∃ pad : ℕ,
      let slot₀ := ip.length + pad
      (slot₀ : PAM M) ≤ slot ∧
      match walkTape 99 [] (ip ++ List.replicate 10 0) with
      | .outOfFuel => False
      | .halt q_h w_h _ =>
        ∃ r_s, walkTape 99 [] (ip ++ List.replicate pad 0) = .halt q_h w_h r_s
      | .jumpLeft q' w_j _ =>
        (∃ r_s, walkTape 99 [] (ip ++ List.replicate pad 0) = .jumpLeft q' w_j r_s) ∧
        ((w_j.length + 1 : ℕ) : PAM M) ≤ slot ∧
        match q'.val with
        | 61 => (minSlot ((popBreakRev 0 w_j.reverse).reverse) : PAM M) ≤ mBreakSlot 0 slot w_j
        | 62 => (minSlot ((popBreakRev 1 w_j.reverse).reverse) : PAM M) ≤ mBreakSlot 1 slot w_j
        | 63 => (minSlot ((popBreakRev 2 w_j.reverse).reverse) : PAM M) ≤ mBreakSlot 2 slot w_j
        | 64 => (minSlot ((popContinueRev 0 w_j.reverse).reverse) : PAM M) ≤ slot
        | 65 => (minSlot ((popContinueRev 1 w_j.reverse).reverse) : PAM M) ≤ slot
        | 66 => (minSlot ((popContinueRev 2 w_j.reverse).reverse) : PAM M) ≤ slot
        | 67 => (minSlot ((popContinueRev 3 w_j.reverse).reverse) : PAM M) ≤ slot
        | 68 => (minSlot ((popContinueRev 4 w_j.reverse).reverse) : PAM M) ≤ slot
        | _ => False
      | .regLeaf q' w_l _ =>
        let r := leafReg q'
        (∃ r_s, walkTape 99 [] (ip ++ List.replicate pad 0) = .regLeaf q' w_l r_s) ∧
        ((w_l.length + (11 - r.val) + 3 : ℕ) : PAM M) ≤ slot ∧
        (if isLeafInc q' then
          (minSlot (retStack w_l) : PAM M) ≤ mBreakSlot 0 slot w_l
        else
          (minSlot ((popBreakRev 1 w_l.reverse).reverse) : PAM M) ≤ mBreakSlot 1 (slot + 1) w_l ∧
          (minSlot (retStack w_l) : PAM M) ≤ mBreakSlot 0 (slot + 1) w_l) := by
    unfold minSlot at hmin
    cases hlk : lookupSmall ip with
    | none =>
      simp only [hlk, Option.getD_none] at hmin
      have hsl150 : ((ip.length + 10 : ℕ) : PAM M) ≤ slot :=
        le_trans (natCast_le_iff.mpr (by omega)) hmin
      refine ⟨10, hsl150, ?_⟩
      rcases h10 : walkTape 99 [] (ip ++ List.replicate 10 0) with
        ⟨q_h, w_h, r_h⟩ | ⟨q', w_j, r_j⟩ | ⟨q', w_l, r_l⟩ | _
      · exact ⟨r_h, rfl⟩
      · rw [h10] at hdag_walk
        obtain ⟨hwj135, _, hqv⟩ := hdag_walk
        have hwj_sl : ((w_j.length + 1 : ℕ) : PAM M) ≤ slot :=
          le_trans (natCast_le_iff.mpr (by omega)) hmin
        refine ⟨⟨r_j, rfl⟩, hwj_sl, ?_⟩
        have h150_le : ∀ ip', (minSlot ip' : PAM M) ≤ slot := fun ip' ↦
          le_trans (natCast_le_iff.mpr (minSlot_le_150 ip')) hmin
        rcases hqv with (hq61 | hq62 | hq63) | ⟨hq64, _⟩ | ⟨hq65, _⟩ |
            ⟨hq66, _⟩ | ⟨hq67, _⟩ | ⟨hq68, _⟩
        · rw [hq61]; exact le_trans (h150_le _) (le_mBreakSlot 0 slot w_j)
        · rw [hq62]; exact le_trans (h150_le _) (le_mBreakSlot 1 slot w_j)
        · rw [hq63]; exact le_trans (h150_le _) (le_mBreakSlot 2 slot w_j)
        · rw [hq64]; exact h150_le _
        · rw [hq65]; exact h150_le _
        · rw [hq66]; exact h150_le _
        · rw [hq67]; exact h150_le _
        · rw [hq68]; exact h150_le _
      · rw [h10] at hdag_walk
        obtain ⟨_, hwl136, _⟩ := hdag_walk
        have hwl_sl : ((w_l.length + (11 - (leafReg q').val) + 3 : ℕ) : PAM M) ≤ slot :=
          le_trans (natCast_le_iff.mpr (by omega)) hmin
        refine ⟨⟨r_l, rfl⟩, hwl_sl, ?_⟩
        have h150_le : ∀ ip', (minSlot ip' : PAM M) ≤ slot := fun ip' ↦
          le_trans (natCast_le_iff.mpr (minSlot_le_150 ip')) hmin
        split
        · exact le_trans (h150_le _) (le_mBreakSlot 0 slot w_l)
        · exact ⟨le_trans (h150_le _)
            (le_trans (le_add_right_pam slot 1) (le_mBreakSlot 1 (slot + 1) w_l)),
            le_trans (h150_le _)
              (le_trans (le_add_right_pam slot 1) (le_mBreakSlot 0 (slot + 1) w_l))⟩
      · rw [h10] at hdag_walk; exact hdag_walk
    | some sl =>
      simp only [hlk, Option.getD_some] at hmin
      have hall := checkSmallStackEntry_of_lookup hlk
      simp only [checkSmallStackEntry, Bool.and_eq_true] at hall
      let m := Nat.min 10 (sl - ip.length)
      have hm10 : m ≤ 10 := Nat.min_le_left _ _
      have hmsl : m ≤ sl - ip.length := Nat.min_le_right _ _
      have hip_sl : ip.length ≤ sl := of_decide_eq_true hall.1.2
      have hsl0 : ((ip.length + m : ℕ) : PAM M) ≤ slot :=
        le_trans (natCast_le_iff.mpr (by omega)) hmin
      refine ⟨m, hsl0, ?_⟩
      have hext10 := walkTape_extend_zeros 99 [] (ip ++ List.replicate m 0) (10 - m)
      have hrep10 : (ip ++ List.replicate m 0) ++ List.replicate (10 - m) 0 =
          ip ++ List.replicate 10 0 := by
        rw [List.append_assoc, ← List.replicate_add]
        congr 2; omega
      rw [hrep10] at hext10
      have hall2 := hall.2
      rw [fastWalk_eq_walkTape, List.reverse_nil] at hall2
      rcases hm : walkTape 99 [] (ip ++ List.replicate m 0) with
        ⟨q_h, w_h, r_h⟩ | ⟨q', w_j, r_j⟩ | ⟨q', w_l, r_l⟩ | _
      · rw [hm] at hext10; rw [hext10]; exact ⟨r_h, rfl⟩
      · rw [hm] at hall2 hext10
        rw [hext10] at hdag_walk ⊢
        simp only [Bool.and_eq_true] at hall2
        have hwj_sl : ((w_j.length + 1 : ℕ) : PAM M) ≤ slot :=
          le_trans (natCast_le_iff.mpr (of_decide_eq_true hall2.1)) hmin
        refine ⟨⟨r_j, rfl⟩, hwj_sl, ?_⟩
        have hms := hall2.2
        rcases hdag_walk.2.2 with (hq61 | hq62 | hq63) | ⟨hq64, _⟩ | ⟨hq65, _⟩ |
            ⟨hq66, _⟩ | ⟨hq67, _⟩ | ⟨hq68, _⟩
        · rw [hq61] at hms ⊢
          exact le_trans (natCast_le_iff.mpr (of_decide_eq_true hms))
            (by rw [← mBreakSlot_natCast]; exact mBreakSlot_mono 0 hmin w_j)
        · rw [hq62] at hms ⊢
          exact le_trans (natCast_le_iff.mpr (of_decide_eq_true hms))
            (by rw [← mBreakSlot_natCast]; exact mBreakSlot_mono 1 hmin w_j)
        · rw [hq63] at hms ⊢
          exact le_trans (natCast_le_iff.mpr (of_decide_eq_true hms))
            (by rw [← mBreakSlot_natCast]; exact mBreakSlot_mono 2 hmin w_j)
        · rw [hq64] at hms ⊢; exact le_trans (natCast_le_iff.mpr (of_decide_eq_true hms)) hmin
        · rw [hq65] at hms ⊢; exact le_trans (natCast_le_iff.mpr (of_decide_eq_true hms)) hmin
        · rw [hq66] at hms ⊢; exact le_trans (natCast_le_iff.mpr (of_decide_eq_true hms)) hmin
        · rw [hq67] at hms ⊢; exact le_trans (natCast_le_iff.mpr (of_decide_eq_true hms)) hmin
        · rw [hq68] at hms ⊢; exact le_trans (natCast_le_iff.mpr (of_decide_eq_true hms)) hmin
      · rw [hm] at hall2 hext10
        rw [hext10]
        simp only [Bool.and_eq_true] at hall2
        have hwl_sl : ((w_l.length + (11 - (leafReg q').val) + 3 : ℕ) : PAM M) ≤ slot :=
          le_trans (natCast_le_iff.mpr (of_decide_eq_true hall2.1)) hmin
        refine ⟨⟨r_l, rfl⟩, hwl_sl, ?_⟩
        have hms := hall2.2
        have hsl1 : ((sl + 1 : ℕ) : PAM M) ≤ slot + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
          exact add_le_add_right_pam hmin 1
        by_cases hinc_q : isLeafInc q' = true <;>
          simp only [hinc_q, ↓reduceIte, Bool.false_eq_true] at hms ⊢
        · exact le_trans (natCast_le_iff.mpr (of_decide_eq_true hms))
            (by rw [← mBreakSlot_natCast]; exact mBreakSlot_mono 0 hmin w_l)
        · simp only [Bool.and_eq_true] at hms
          exact ⟨le_trans (natCast_le_iff.mpr (of_decide_eq_true hms.1))
              (by rw [← mBreakSlot_natCast]; exact mBreakSlot_mono 1 hsl1 w_l),
            le_trans (natCast_le_iff.mpr (of_decide_eq_true hms.2))
              (by rw [← mBreakSlot_natCast]; exact mBreakSlot_mono 0 hsl1 w_l)⟩
      · rw [hm] at hall2; cases hall2
  rcases hpad_data with ⟨pad, hsl0, hslot_match⟩
  let slot₀ : ℕ := ip.length + pad
  have htail := walkTape_slot_tail (slot := slot₀) (ip := ip) (by dsimp [slot₀]; omega) hdag_in
  have hsub0 : slot₀ - ip.length = pad := by dsimp [slot₀]; omega
  rw [hsub0] at htail
  set R_end := mAppendRegs mPrefix190 (mRegsTape regs.reverse)
  set R_rem := mRep0 (slot - (slot₀ : PAM M)) R_end
  have hroot_eq : mZfLogCfg slot ip regs =
      mTreeWalkCfg 99 [] (ip ++ List.replicate pad 0) mLB01 R_rem := by
    unfold mZfLogCfg mZf393RootCfg mRootCfg mTreeWalkCfg
    have hpad_split : (pad : PAM M) + (slot - (slot₀ : PAM M)) = slot - (ip.length : PAM M) := by
      have hcast : (pad : PAM M) = (slot₀ : PAM M) - (ip.length : PAM M) := by
        symm
        apply (sub_eq_iff_eq_add_pam (natCast_le_iff.mpr (by dsimp [slot₀]; omega))).mpr
        dsimp [slot₀]; push_cast; rfl
      rw [hcast]
      exact sub_split_add (natCast_le_iff.mpr (by dsimp [slot₀]; omega)) hsl0
    simp only [List.reverse_nil, mAppend_nil, mAppend_append, mAppend_replicate_zero,
      R_rem, ← mRep0_add, hpad_split, R_end]
  have hreach := mWalkTape_sound 99 [] (ip ++ List.replicate pad 0) mLB01 R_rem
  unfold evalStack
  rcases h10 : walkTape 99 [] (ip ++ List.replicate 10 0) with
    ⟨q_h, w_h, r_h⟩ | ⟨q', w_j, r_j⟩ | ⟨q', w_l, r_l⟩ | _
  · dsimp only
    rw [h10] at hslot_match
    obtain ⟨r_s, hr_s⟩ := hslot_match
    rw [hr_s] at hreach
    obtain ⟨⟨s, hs⟩, hnone⟩ := hreach
    exact ⟨s, _, by rwa [hroot_eq], hnone⟩
  · rw [h10] at hdag_walk hstays_walk hslot_match
    obtain ⟨hwj135, hok_j, hqv⟩ := hdag_walk
    obtain ⟨_, hw_eq, hstays_wj⟩ := hstays_walk
    rw [List.nil_append] at hw_eq
    rw [← hw_eq] at hstays_wj
    obtain ⟨⟨r_s, hr_s⟩, hwj_sl, hms⟩ := hslot_match
    rw [hr_s] at hreach htail
    obtain ⟨⟨b₀, hb₀⟩, hs₁⟩ := hreach
    have hwj_lt0 : w_j.length + 1 ≤ slot₀ := by
      have hlen_eq := congrArg List.length hb₀
      simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_replicate] at hlen_eq
      dsimp [slot₀]; omega
    subst htail
    have hR_eq : mAppend (0 :: List.replicate (slot₀ - (w_j.length + 1)) 0) R_rem =
        mRep0 (slot - (w_j.length : PAM M)) R_end := by
      have hrep_succ : (0 : Fin 2) :: List.replicate (slot₀ - (w_j.length + 1)) 0 =
          List.replicate (slot₀ - w_j.length) 0 := by
        have hsub : slot₀ - w_j.length = (slot₀ - (w_j.length + 1)) + 1 := by omega
        rw [hsub, List.replicate_succ]
      have hcast_sub : ((slot₀ - w_j.length : ℕ) : PAM M) =
          (slot₀ : PAM M) - (w_j.length : PAM M) := by
        symm
        apply (sub_eq_iff_eq_add_pam (natCast_le_iff.mpr (by omega))).mpr
        rw [← Nat.cast_add, Nat.add_sub_of_le (by omega)]
      rw [hrep_succ, mAppend_replicate_zero, ← mRep0_add, hcast_sub,
        sub_split_add (natCast_le_iff.mpr (by omega)) hsl0]
    rw [hR_eq, ← hroot_eq] at hs₁
    have hwj_le_sl : (w_j.length : PAM M) ≤ slot :=
      le_trans (by
        have : w_j.length ≤ w_j.length + 1 := by omega
        exact natCast_le_iff.mpr this) hwj_sl
    rcases hqv with (hq61 | hq62 | hq63) | ⟨hq64, hc0⟩ | ⟨hq65, hc1⟩ |
        ⟨hq66, hc2⟩ | ⟨hq67, hc3⟩ | ⟨hq68, hc4⟩
    · have hq'_eq : q' = breakState 0 := by ext; exact hq61
      simp only [hq61] at hms ⊢
      rw [hq'_eq] at hs₁
      have hs₂ := mBreak_k_reaches_main0 (pre := mPrefix190) 0 (by decide) slot w_j
        hwj_le_sl hok_j regs.reverse
      have hip_len : (popBreakRev 0 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popBreakRev_length_le 0 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popBreakRev 0 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99 ((popBreakRev_dropLast_prefix 0 w_j).trans w_j.dropLast_prefix)
          hstays_wj
      exact ⟨_, ⟨hregs, hip_len, hdag', hms⟩, mReachPos_trans hs₁ hs₂⟩
    · have hq'_eq : q' = breakState 1 := by ext; exact hq62
      simp only [hq62] at hms ⊢
      rw [hq'_eq] at hs₁
      have hs₂ := mBreak_k_reaches_main0 (pre := mPrefix190) 1 (by decide) slot w_j
        hwj_le_sl hok_j regs.reverse
      have hip_len : (popBreakRev 1 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popBreakRev_length_le 1 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popBreakRev 1 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99 ((popBreakRev_dropLast_prefix 1 w_j).trans w_j.dropLast_prefix)
          hstays_wj
      exact ⟨_, ⟨hregs, hip_len, hdag', hms⟩, mReachPos_trans hs₁ hs₂⟩
    · have hq'_eq : q' = breakState 2 := by ext; exact hq63
      simp only [hq63] at hms ⊢
      rw [hq'_eq] at hs₁
      have hs₂ := mBreak_k_reaches_main0 (pre := mPrefix190) 2 (by decide) slot w_j
        hwj_le_sl hok_j regs.reverse
      have hip_len : (popBreakRev 2 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popBreakRev_length_le 2 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popBreakRev 2 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99 ((popBreakRev_dropLast_prefix 2 w_j).trans w_j.dropLast_prefix)
          hstays_wj
      exact ⟨_, ⟨hregs, hip_len, hdag', hms⟩, mReachPos_trans hs₁ hs₂⟩
    · have hq'_eq : q' = continueState 0 := by ext; exact hq64
      simp only [hq64] at hms ⊢
      rw [hq'_eq] at hs₁
      have hs₂ := mContinue_k_reaches_main0 (pre := mPrefix190) 0 (by decide) slot w_j
        hc0 hwj_le_sl hok_j regs.reverse
      have hip_len : (popContinueRev 0 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popContinueRev_length_le 0 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popContinueRev 0 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99
          ((popContinueRev 0 w_j.reverse).reverse.dropLast_prefix.trans
            (popContinueRev_prefix 0 w_j))
          hstays_wj
      exact ⟨slot, ⟨hregs, hip_len, hdag', hms⟩, mReachPos_trans hs₁ hs₂⟩
    · have hq'_eq : q' = continueState 1 := by ext; exact hq65
      simp only [hq65] at hms ⊢
      rw [hq'_eq] at hs₁
      have hs₂ := mContinue_k_reaches_main0 (pre := mPrefix190) 1 (by decide) slot w_j
        hc1 hwj_le_sl hok_j regs.reverse
      have hip_len : (popContinueRev 1 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popContinueRev_length_le 1 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popContinueRev 1 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99
          ((popContinueRev 1 w_j.reverse).reverse.dropLast_prefix.trans
            (popContinueRev_prefix 1 w_j))
          hstays_wj
      exact ⟨slot, ⟨hregs, hip_len, hdag', hms⟩, mReachPos_trans hs₁ hs₂⟩
    · have hq'_eq : q' = continueState 2 := by ext; exact hq66
      simp only [hq66] at hms ⊢
      rw [hq'_eq] at hs₁
      have hs₂ := mContinue_k_reaches_main0 (pre := mPrefix190) 2 (by decide) slot w_j
        hc2 hwj_le_sl hok_j regs.reverse
      have hip_len : (popContinueRev 2 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popContinueRev_length_le 2 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popContinueRev 2 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99
          ((popContinueRev 2 w_j.reverse).reverse.dropLast_prefix.trans
            (popContinueRev_prefix 2 w_j))
          hstays_wj
      exact ⟨slot, ⟨hregs, hip_len, hdag', hms⟩, mReachPos_trans hs₁ hs₂⟩
    · have hq'_eq : q' = continueState 3 := by ext; exact hq67
      simp only [hq67] at hms ⊢
      rw [hq'_eq] at hs₁
      have hs₂ := mContinue_k_reaches_main0 (pre := mPrefix190) 3 (by decide) slot w_j
        hc3 hwj_le_sl hok_j regs.reverse
      have hip_len : (popContinueRev 3 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popContinueRev_length_le 3 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popContinueRev 3 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99
          ((popContinueRev 3 w_j.reverse).reverse.dropLast_prefix.trans
            (popContinueRev_prefix 3 w_j))
          hstays_wj
      exact ⟨slot, ⟨hregs, hip_len, hdag', hms⟩, mReachPos_trans hs₁ hs₂⟩
    · have hq'_eq : q' = continueState 4 := by ext; exact hq68
      simp only [hq68] at hms ⊢
      rw [hq'_eq] at hs₁
      have hs₂ := mContinue_k_reaches_main0 (pre := mPrefix190) 4 (by decide) slot w_j
        hc4 hwj_le_sl hok_j regs.reverse
      have hip_len : (popContinueRev 4 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popContinueRev_length_le 4 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popContinueRev 4 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99
          ((popContinueRev 4 w_j.reverse).reverse.dropLast_prefix.trans
            (popContinueRev_prefix 4 w_j))
          hstays_wj
      exact ⟨slot, ⟨hregs, hip_len, hdag', hms⟩, mReachPos_trans hs₁ hs₂⟩
  · dsimp only
    rw [h10] at hdag_walk hstays_walk hslot_match
    obtain ⟨hleaf_q, hwl136, hok_l⟩ := hdag_walk
    obtain ⟨_, hw_eq, hstays_wl⟩ := hstays_walk
    rw [List.nil_append] at hw_eq
    rw [← hw_eq] at hstays_wl
    obtain ⟨⟨r_s, hr_s⟩, hwl_sl, hms⟩ := hslot_match
    rw [hr_s] at hreach htail
    obtain ⟨hu_eq, _⟩ := hreach
    rw [List.nil_append] at hu_eq
    have hwl_le0 : w_l.length ≤ slot₀ := by
      have hlen_eq := congrArg List.length hu_eq
      simp only [List.length_append, List.length_replicate] at hlen_eq
      dsimp [slot₀]; omega
    subst htail
    have hroot_wl : mZfLogCfg slot ip regs =
        mMk' 99 mLB01
          (mAppend w_l (mRep0 (slot - (w_l.length : PAM M)) R_end)) := by
      rw [hroot_eq]
      unfold mTreeWalkCfg
      rw [← hu_eq, List.reverse_nil, mAppend_nil, mAppend_append, mAppend_replicate_zero,
        ← mRep0_add]
      have hcast_sub : ((slot₀ - w_l.length : ℕ) : PAM M) =
          (slot₀ : PAM M) - (w_l.length : PAM M) := by
        symm
        apply (sub_eq_iff_eq_add_pam (natCast_le_iff.mpr hwl_le0)).mpr
        rw [← Nat.cast_add, Nat.add_sub_of_le hwl_le0]
      rw [hcast_sub, sub_split_add (natCast_le_iff.mpr hwl_le0) hsl0]
    have hself := walkTape_self_on_regLeaf 99 [] (ip ++ List.replicate 10 0) q' w_l r_l
      (by simpa using h10)
    rw [List.nil_append] at hself
    obtain ⟨hget, hset⟩ := mRev11_getD_set hregs (leafReg q')
    rw [ten_sub_leafReg_eq_logLeafReg q'] at hget hset
    have hip0_len : (retStack w_l).length ≤ 136 := by
      unfold retStack; rw [List.length_reverse]
      exact (popBreakRev_length_le 0 w_l.reverse).trans (by rw [List.length_reverse]; omega)
    have hdag0 : staysInDag 99 (retStack w_l).dropLast = true := by
      unfold retStack
      exact staysInDag_prefix 99 (popBreakRev_dropLast_prefix 0 w_l) hstays_wl
    by_cases hinc : isLeafInc q' = true
    · simp only [hinc, ↓reduceIte] at hms ⊢
      have hq_inc := leafReg_inc_spec q' hleaf_q hinc
      rw [hq_inc] at hself
      have hs₂ := mInc_leaf_reaches_main0 (pre := mPrefix190) (leafReg q') slot w_l hself
        hwl_sl hok_l regs.reverse hregs_rev
      rw [← hroot_wl, hget, hset] at hs₂
      have hset_len : (regs.set (logLeafReg q') (regs.getD (logLeafReg q') 0 + 1)).length = 11 := by
        rw [List.length_set, hregs]
      exact ⟨_, ⟨hset_len, hip0_len, hdag0, hms⟩, hs₂⟩
    · simp only [Bool.not_eq_true] at hinc
      simp only [hinc, Bool.false_eq_true, ↓reduceIte] at hms ⊢
      have hq_dec := leafReg_decnz_spec q' hleaf_q hinc
      rw [hq_dec] at hself
      have hs₂ := mDecnz_leaf_reaches_main0 (pre := mPrefix190) (leafReg q') slot w_l
        hself hwl_sl hok_l regs.reverse hregs_rev
      rw [← hroot_wl, hget, hset] at hs₂
      have hip1_len : (popBreakRev 1 w_l.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popBreakRev_length_le 1 w_l.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag1 : staysInDag 99 (popBreakRev 1 w_l.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99 (popBreakRev_dropLast_prefix 1 w_l) hstays_wl
      refine ⟨fun hv0 ↦ ⟨_, ⟨hregs, hip1_len, hdag1, hms.1⟩, hs₂.1 hv0⟩,
        fun hvne ↦ ⟨_, ⟨by rw [List.length_set, hregs], hip0_len, hdag0, hms.2⟩, hs₂.2 hvne⟩⟩
  · rw [h10] at hslot_match; exact False.elim hslot_match

end Model

end ConjectureMachines.Semantics.PA

end
