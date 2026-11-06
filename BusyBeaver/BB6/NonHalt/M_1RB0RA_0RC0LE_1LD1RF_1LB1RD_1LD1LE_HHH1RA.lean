/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Basic
import BusyBeaver.Calculi.Counter
import BusyBeaver.Calculi.SegmentChain

namespace BusyBeaver.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

section

open Mathlib Relation Nat Turing BusyBeaver SixState BusyBeaver.SegmentChain

set_option maxRecDepth 2000

private theorem if_pos {c : Prop} [Decidable c] (hc : c) {α : Sort*} {t e : α} :
    (if c then t else e) = t := by
  simp [hc]

private theorem if_neg {c : Prop} [Decidable c] (hnc : ¬c) {α : Sort*} {t e : α} :
    (if c then t else e) = e := by
  simp [hnc]

theorem target_eq : target = target_tm := by
  funext q s
  fin_cases q <;> fin_cases s <;> rfl

namespace ChainClosure

theorem dec_or (P : Prop) : P ∨ ¬ P :=
  Classical.em P

-- ============================================================================
-- Section 5g.1: Normalized Segment Representation & 1-Step Chain Equivalence
-- ============================================================================

structure SegState where
  b : Bool
  segs : List (Nat × Nat)
  zl : Nat
  cp1 : Nat
  kb : Nat
  mrg : Nat
  ds : List Nat

def normSeg (z m : Nat) : Nat × Nat :=
  if m = 0 then (z + 1, 0) else (z, m)

def pushSeg (has_p5 : Bool) (z_new m_rem : Nat) (rest : List (Nat × Nat)) (zl : Nat) :
    List (Nat × Nat) × Nat :=
  if has_p5 then (normSeg z_new m_rem :: rest, zl) else ([], z_new)

def encSegs : List (Nat × Nat) → Nat → List LTok
  | [], zl => z0Rep zl []
  | (z, 0) :: rest, zl => z0Rep z (.p5 :: encSegs rest zl)
  | (z, m + 1) :: rest, zl => z0Rep z (.p3z (m + 1) :: .p5 :: encSegs rest zl)

theorem z0Rep_succ_right (n : Nat) (rest : List LTok) :
    z0Rep (n + 1) rest = z0Rep n (.p3z 0 :: rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change LTok.p3z 0 :: z0Rep (n + 1) rest = LTok.p3z 0 :: z0Rep n (.p3z 0 :: rest)
    rw [ih]

theorem encSegs_normSeg (z m : Nat) (rest : List (Nat × Nat)) (zl : Nat) :
    encSegs (normSeg z m :: rest) zl = z0Rep z (.p3z m :: .p5 :: encSegs rest zl) := by
  cases m with
  | zero =>
    dsimp only [normSeg, ite_true, encSegs]
    exact z0Rep_succ_right z (.p5 :: encSegs rest zl)
  | succ m' => rfl

theorem encSegs_pushSeg (hp : Bool) (z_new m_rem : Nat) (rest : List (Nat × Nat)) (zl : Nat) :
    encSegs (pushSeg hp z_new m_rem rest zl).1 (pushSeg hp z_new m_rem rest zl).2 =
      z0Rep z_new (if hp then .p3z m_rem :: .p5 :: encSegs rest zl else []) := by
  cases hp with
  | false => rfl
  | true => exact encSegs_normSeg z_new m_rem rest zl

theorem z0_z0Rep_of_zero {rest : List LTok} (h : z0 rest = 0) (n : Nat) :
    z0 (z0Rep n rest) = n := by
  induction n with
  | zero => exact h
  | succ n ih => simp only [z0Rep, z0, ih]; omega

theorem dropZ0_z0Rep_of_nonz0 {rest : List LTok} (h : dropZ0 rest = rest) (n : Nat) :
    dropZ0 (z0Rep n rest) = rest := by
  induction n with
  | zero => exact h
  | succ n ih => simp only [z0Rep, dropZ0, ih]

theorem hasOdd_z0Rep (n : Nat) (rest : List LTok) :
    hasOdd (z0Rep n rest) = hasOdd rest := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [z0Rep, hasOdd, ih]; rfl

theorem hasP5_z0Rep (n : Nat) (rest : List LTok) :
    hasP5 (z0Rep n rest) = hasP5 rest := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [z0Rep, hasP5, ih]

theorem p5Suf_z0Rep (n : Nat) (rest : List LTok) :
    p5Suf (z0Rep n rest) = p5Suf rest := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [z0Rep, p5Suf, ih]

theorem MustDrain_z0Rep (n : Nat) (rest : List LTok) :
    MustDrain (z0Rep n rest) = MustDrain rest := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [z0Rep, MustDrain, ih]; rfl

theorem ep_z0Rep (n : Nat) (rest : List LTok) :
    ep (z0Rep n rest) = n + ep rest := by
  induction n with
  | zero => simp only [z0Rep, Nat.zero_add]
  | succ n ih =>
    have h0 : (0 : Nat) % 2 = 1 ↔ False := by decide
    simp only [z0Rep, ep, h0, ite_false, ih]
    omega

theorem epSum_z0Rep (n : Nat) (rest : List LTok) :
    epSum (z0Rep n rest) = epSum rest := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h0 : (0 : Nat) % 2 = 1 ↔ False := by decide
    simp only [z0Rep, epSum, h0, ite_false, Nat.zero_add, ih]

theorem epW_z0Rep_nil (n : Nat) : epW (z0Rep n []) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n' =>
      change (if 0 % 2 = 1 then 0 else 1 + epW (z0Rep (n' + 1) [])) = n' + 2
      rw [ih, if_neg (by decide)]; omega

theorem epW_z0Rep_p3z (n m : Nat) (suf : List LTok) :
    epW (z0Rep n (.p3z m :: .p5 :: suf)) = n := by
  induction n with
  | zero =>
    dsimp [z0Rep, epW]
    rcases dec_or (m % 2 = 1) with hm | hm
    · rw [if_pos hm]
    · rw [if_neg hm]
  | succ n ih =>
    cases n with
    | zero =>
      change (if 0 % 2 = 1 then 0 else 1 + epW (.p3z m :: .p5 :: suf)) = 1
      have h0 : epW (.p3z m :: .p5 :: suf) = 0 := ih
      rw [h0]; rfl
    | succ n' =>
      change (if 0 % 2 = 1 then 0 else 1 + epW (z0Rep (n' + 1) (.p3z m :: .p5 :: suf))) = n' + 2
      rw [ih, if_neg (by decide)]; omega

theorem isHeadP5_z0Rep_p3z (n m : Nat) (suf : List LTok) :
    isHeadP5 (z0Rep n (.p3z m :: suf)) = false := by
  cases n <;> rfl

def isDrainRstDs : List Nat → Bool
  | [d] => decide (d ≥ 8)
  | [d, 0] => decide (d ≥ 8)
  | _ => false

def isRank0 : List Nat → Bool
  | [] => true
  | [0] => true
  | [1] => true
  | [2] => true
  | _ => false

theorem isRank0_iff (ds : List Nat) :
    isRank0 ds = true ↔ (ds = [] ∨ ds = [0] ∨ ds = [1] ∨ ds = [2]) := by
  rcases ds with _ | ⟨d, _ | ⟨d2, ds2⟩⟩
  · simp [isRank0]
  · rcases d with _ | _ | _ | d3 <;> simp [isRank0]
  · simp [isRank0]

def drainPopGuards (phiWp1 : Nat) (ds : List Nat) : Bool :=
  if isDrainRstDs ds then
    decide (phiWp1 ≥ if isOddDrainDs ds then 18 else 16)
  else if isRank0 ds then
    decide (phiWp1 ≥ 2)
  else
    match ds with
    | d :: d2 :: ds2 =>
      decide (d ≥ 3 ∧ d2 ≥ 1) &&
      (!decide (d % 2 = 0 ∧ d ≤ 2 * d2 + 4) || GoodDs ((d2 - 1) :: ds2)) &&
      (!decide (d % 2 = 0 ∧ d + 14 ≤ 2 * d2) || GoodDs ((d2 - 2) :: ds2)) &&
      decide (phiWp1 ≥ 16)
    | _ => false

def drainPopStep (has_p5 : Bool) (phiWp1 m_rem : Nat) (rest : List (Nat × Nat)) (zl : Nat)
    (ds : List Nat) : SegState :=
  if isDrainRstDs ds then
    let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl
    let m_rst := headNat ds - 7
    if m_rst = 1 then
      ⟨false, p.1, p.2, 2, 1, 0, [3, 1]⟩
    else
      ⟨true, normSeg 0 (m_rst - 2) :: p.1, p.2, 3, 0, 8, [1]⟩
  else if isRank0 ds then
    if ds = [] then
      let p := pushSeg has_p5 (phiWp1 + 1) m_rem rest zl
      ⟨false, p.1, p.2, 1, 1, 0, []⟩
    else if ds = [0] then
      let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl
      ⟨true, p.1, p.2, 2, 2, 6, []⟩
    else if ds = [1] then
      let p := pushSeg has_p5 (phiWp1 + 3) m_rem rest zl
      ⟨true, p.1, p.2, 2, 0, 6, []⟩
    else
      let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl
      ⟨false, p.1, p.2, 1, 1, 0, [0]⟩
  else
    match ds with
    | d :: d2 :: ds2 =>
      let p := pushSeg has_p5 (phiWp1 + 2) m_rem rest zl
      if d2 = 1 ∧ ds2 = [] ∧ d ≥ 25 then
        ⟨true, normSeg 0 (d - 11) :: p.1, p.2, 5, 0, 12, [2]⟩
      else
        ⟨true, normSeg 0 (d - 3) :: p.1, p.2, d2 - 1, 0, 2 * d2, ds2⟩
    | _ => ⟨true, [], 0, 0, 0, 0, []⟩

def stepGuards (s : SegState) : Bool :=
  match s.b with
  | false =>
    let c := s.cp1
    let k := s.kb
    match s.segs with
    | [] =>
      let cz := c + s.zl
      GoodPhiW (cz - 1) s.ds false && GoodPsi (cz - 1) s.ds
    | (_, 0) :: _ => true
    | (z0, m + 1) :: _ =>
      let m0 := m + 1
      let cz := c + z0
      let kz := k + 2 * z0
      GoodPhiW (cz - 1) s.ds false &&
      if m0 = 1 then GoodPsi cz s.ds
      else
        GoodPsi (cz - 1) s.ds &&
        if m0 % 2 = 0 ∧ m0 ≤ 2 * kz + 10 then true
        else if m0 % 2 = 1 ∧ m0 ≤ 2 * kz + 11 then GoodDs ((kz + 2) :: cz :: s.ds)
        else true
  | true =>
    match s.segs with
    | [] => drainPopGuards (s.cp1 + s.zl) s.ds
    | (_, 0) :: _ => decide (s.mrg ≥ s.kb)
    | (z0, m + 1) :: _ =>
      let m0 := m + 1
      if m0 % 2 = 1 then
        if decide (s.mrg ≥ s.kb + m) then GoodDs ((s.cp1 + z0) :: s.ds)
        else drainPopGuards (s.cp1 + z0) s.ds
      else
        if decide (s.mrg ≥ s.kb + m0) then true
        else drainPopGuards (s.cp1 + z0) s.ds

def stepSegs (s : SegState) : SegState :=
  match s.b with
  | false =>
    let c := s.cp1
    let k := s.kb
    match s.segs with
    | [] =>
      let cz := c + s.zl
      let kz := k + 2 * s.zl
      ⟨true, [], 0, kz + 2, 0, 2 * kz + 6, cz :: s.ds⟩
    | (z0, 0) :: rest =>
      let cz := c + z0
      let kz := k + 2 * z0
      ⟨true, rest, s.zl, cz + 3, kz + 3, 2 * cz + 8, s.ds⟩
    | (z0, m + 1) :: rest =>
      let m0 := m + 1
      let cz := c + z0
      let kz := k + 2 * z0
      if m0 = 1 then
        ⟨false, rest, s.zl, kz + 4, 1, 0, (cz + 1) :: s.ds⟩
      else if m0 % 2 = 0 ∧ m0 ≤ 2 * kz + 10 then
        ⟨false, rest, s.zl, kz + 4, m0 + 1, 0, cz :: s.ds⟩
      else if m0 % 2 = 1 ∧ m0 ≤ 2 * kz + 11 then
        ⟨false, rest, s.zl, m0 - 1, 1, 0, (kz + 2) :: cz :: s.ds⟩
      else
        ⟨true, normSeg 0 (m0 - 4) :: rest, s.zl, kz + 2, 0, 2 * kz + 6, cz :: s.ds⟩
  | true =>
    match s.segs with
    | [] => drainPopStep false (s.cp1 + s.zl) 0 [] s.zl s.ds
    | (z0, 0) :: rest => ⟨false, rest, s.zl, s.cp1 + z0 + 1, s.kb + 2 * z0 + 3, 0, s.ds⟩
    | (z0, m + 1) :: rest =>
      let m0 := m + 1
      if m0 % 2 = 1 then
        if decide (s.mrg ≥ s.kb + m) then
          ⟨false, rest, s.zl, s.kb + m + 2 * z0 + 4, 1, 0, (s.cp1 + z0) :: s.ds⟩
        else
          drainPopStep true (s.cp1 + z0) (s.kb + m0 - (s.mrg + 2)) rest s.zl s.ds
      else
        if decide (s.mrg ≥ s.kb + m0) then
          ⟨false, rest, s.zl, s.cp1 + z0 + 2, s.kb + m0 + 2 * z0 + 5, 0, s.ds⟩
        else
          drainPopStep true (s.cp1 + z0) (s.kb + m0 - (s.mrg + 2)) rest s.zl s.ds

theorem drainPop_eq_checkChain (fuel : Nat) (ls : List LTok) (cp1 kb mrg : Nat) (ds : List Nat)
    (has_p5 : Bool) (m_rem_arg : Nat) (rest : List (Nat × Nat)) (zl : Nat)
    (h1 : (hasOdd ls && decide (mrg ≥ kb + epSum ls)) = false)
    (h2 : (!hasOdd ls && hasP5 ls && (isHeadP5 ls || decide (mrg ≥ kb + epSum ls))) = false)
    (hp5 : hasP5 ls = has_p5)
    (hsuf : has_p5 = true → p5Suf ls = encSegs rest zl)
    (hmrem : has_p5 = true → kb + epSum ls + (if hasOdd ls then 1 else 0) - (mrg + 2) = m_rem_arg)
    (hg : drainPopGuards (cp1 + epW ls) ds = true) :
    checkChainAux (fuel + 1) true ls cp1 kb mrg ds =
      let s' := drainPopStep has_p5 (cp1 + epW ls) m_rem_arg rest zl ds
      checkChainAux fuel s'.b (encSegs s'.segs s'.zl) s'.cp1 s'.kb s'.mrg s'.ds := by
  conv_lhs => unfold checkChainAux
  rw [if_neg (by rw [h1]; decide), if_neg (by rw [h2]; decide)]
  have htail :
      (if hasP5 ls = true then
        LTok.p3z (kb + epSum ls + (if hasOdd ls =
          true then 1 else 0) - (mrg + 2)) :: .p5 :: p5Suf ls
      else []) =
      (if has_p5 then LTok.p3z m_rem_arg :: .p5 :: encSegs rest zl else []) := by
    cases has_p5 with
    | false => simp [hp5]
    | true => simp only [hp5, ite_true, hsuf rfl, hmrem rfl]
  unfold drainPopGuards drainPopStep at *
  rcases ds with _ | ⟨d, _ | ⟨_ | d2, ds2⟩⟩
  · -- ds = []
    simp only [isDrainRstDs, isRank0, Bool.false_eq_true, ite_false, ite_true,
      decide_eq_true_eq] at hg ⊢
    have hlt2 : ¬ (cp1 + epW ls < 2) := by omega
    rw [if_pos (Or.inl trivial), if_neg hlt2, encSegs_pushSeg, htail]
  · -- ds = [d]
    rcases dec_or (d ≥ 8) with hd8 | hd8
    · have hd8b : decide (d ≥ 8) = true := decide_eq_true hd8
      simp only [isDrainRstDs, hd8b, ite_true] at hg ⊢
      have hlt : ¬ (cp1 + epW ls < if isOddDrainDs [d] = true then 18 else 16) := by
        simp only [decide_eq_true_eq] at hg; omega
      rw [if_neg hlt]
      rcases dec_or (headNat [d] - 7 = 1) with hm1 | hm1
      · rw [if_pos hm1, if_pos hm1]; dsimp only; rw [encSegs_pushSeg, htail]
      · rw [if_neg hm1, if_neg hm1]; dsimp only; rw [encSegs_normSeg, z0Rep, encSegs_pushSeg, htail]
    · have hd8b : decide (d ≥ 8) = false := decide_eq_false hd8
      simp only [isDrainRstDs, hd8b, Bool.false_eq_true, ite_false] at hg ⊢
      cases h_r0 : isRank0 [d] with
      | false => simp [h_r0] at hg
      | true =>
        have hr0_prop : ([d] : List Nat) = [] ∨ [d] = [0] ∨ [d] = [1] ∨ [d] = [2] :=
          (isRank0_iff [d]).mp h_r0
        rw [if_pos hr0_prop]
        simp only [h_r0, ite_true, decide_eq_true_eq] at hg ⊢
        have hlt2 : ¬ (cp1 + epW ls < 2) := by omega
        rw [if_neg hlt2]
        rcases hr0_prop with hnil | h0 | h1' | h2'
        · cases hnil
        · injection h0 with hd0; subst hd0
          have h01 : ([0] : List Nat) ≠ [1] := by decide
          have h0nil : ([0] : List Nat) ≠ [] := by decide
          simp only [h0nil, h01, ite_false, ite_true]; rw [encSegs_pushSeg, htail]
        · injection h1' with hd1; subst hd1
          have h10 : ([1] : List Nat) ≠ [0] := by decide
          have h1nil : ([1] : List Nat) ≠ [] := by decide
          simp only [h1nil, h10, ite_false, ite_true]; rw [encSegs_pushSeg, htail]
        · injection h2' with hd2; subst hd2
          have h2nil : ([2] : List Nat) ≠ [] := by decide
          have h20 : ([2] : List Nat) ≠ [0] := by decide
          have h21 : ([2] : List Nat) ≠ [1] := by decide
          simp only [h2nil, h20, h21, ite_false]; rw [encSegs_pushSeg, htail]
  · -- ds = d :: 0 :: ds2
    rcases ds2 with _ | ⟨d3, ds3⟩
    · -- ds = [d, 0]
      rcases dec_or (d ≥ 8) with hd8 | hd8
      · have hd8b : decide (d ≥ 8) = true := decide_eq_true hd8
        simp only [isDrainRstDs, hd8b, ite_true] at hg ⊢
        have hlt : ¬ (cp1 + epW ls < if isOddDrainDs [d, 0] = true then 18 else 16) := by
          simp only [decide_eq_true_eq] at hg; omega
        rw [if_neg hlt]
        rcases dec_or (headNat [d, 0] - 7 = 1) with hm1 | hm1
        · rw [if_pos hm1, if_pos hm1]; dsimp only; rw [encSegs_pushSeg, htail]
        · rw [if_neg hm1, if_neg hm1]; dsimp only; rw [encSegs_normSeg, z0Rep, encSegs_pushSeg,
          htail]
      · have hd8b : decide (d ≥ 8) = false := decide_eq_false hd8
        simp [isDrainRstDs, isRank0, hd8b] at hg
    · -- ds = d :: 0 :: d3 :: ds3
      simp [isDrainRstDs, isRank0] at hg
  · -- ds = d :: (d2 + 1) :: ds2
    have h_ge2_step : ∀ ts : List Nat,
        isDrainRstDs (d :: (d2 + 1) :: ts) = false →
        ((decide (d ≥ 3 ∧ d2 + 1 ≥ 1) &&
          (!decide (d % 2 = 0 ∧ d ≤ 2 * (d2 + 1) + 4) || GoodDs (((d2 + 1) - 1) :: ts)) &&
          (!decide (d % 2 = 0 ∧ d + 14 ≤ 2 * (d2 + 1)) || GoodDs (((d2 + 1) - 2) :: ts)) &&
          decide (cp1 + epW ls ≥ 16)) = true) →
        (if d :: (d2 + 1) :: ts = [] ∨ d :: (d2 + 1) :: ts = [0] ∨
            d :: (d2 + 1) :: ts = [1] ∨ d :: (d2 + 1) :: ts = [2] then
          let phiWp1 := cp1 + epW ls
          if phiWp1 < 2 then true
          else
            let m_rem := kb + epSum ls + (if hasOdd ls then 1 else 0) - (mrg + 2)
            let tail_b2 := if hasP5 ls then LTok.p3z m_rem :: LTok.p5 :: p5Suf ls else []
            if d :: (d2 + 1) :: ts =
              [] then checkChainAux fuel false (z0Rep (phiWp1 + 1) tail_b2) 1 1 0 []
            else if d :: (d2 + 1) :: ts =
              [0] then checkChainAux fuel true (z0Rep (phiWp1 + 2) tail_b2) 2 2 6 []
            else if d :: (d2 + 1) :: ts =
              [1] then checkChainAux fuel true (z0Rep (phiWp1 + 3) tail_b2) 2 0 6 []
            else checkChainAux fuel false (z0Rep (phiWp1 + 2) tail_b2) 1 1 0 [0]
        else
          if d ≥ 3 ∧ d2 + 1 ≥ 1 then
            if d % 2 = 0 ∧ d ≤ 2 * (d2 + 1) + 4 ∧ GoodDs (((d2 + 1) - 1) :: ts) = false then false
            else if d % 2 = 0 ∧ d + 14 ≤ 2 * (d2 + 1) ∧
              GoodDs (((d2 + 1) - 2) :: ts) = false then false
            else if cp1 + epW ls < 16 then false
            else
              let phiWp1 := cp1 + epW ls
              let m_rem := kb + epSum ls + (if hasOdd ls then 1 else 0) - (mrg + 2)
              let tail_b2 := if hasP5 ls then LTok.p3z m_rem :: LTok.p5 :: p5Suf ls else []
              let ls_b2 := z0Rep phiWp1 tail_b2
              if d2 + 1 = 1 ∧ ts = [] ∧ d ≥ 25 then
                checkChainAux fuel true (LTok.p3z (d -
                  11) :: LTok.p5 :: LTok.p3z 0 :: LTok.p3z 0 :: ls_b2) 5 0 12 [2]
              else
                checkChainAux fuel true (LTok.p3z (d -
                  3) :: LTok.p5 :: LTok.p3z 0 :: LTok.p3z 0 :: ls_b2)
                  ((d2 + 1) - 1) 0 (2 * (d2 + 1)) ts
          else true) =
        (let p := pushSeg has_p5 (cp1 + epW ls + 2) m_rem_arg rest zl
         let s' : SegState :=
           if d2 + 1 = 1 ∧ ts = [] ∧ d ≥ 25 then
             ⟨true, normSeg 0 (d - 11) :: p.1, p.2, 5, 0, 12, [2]⟩
           else
             ⟨true, normSeg 0 (d - 3) :: p.1, p.2, (d2 + 1) - 1, 0, 2 * (d2 + 1), ts⟩
         checkChainAux fuel s'.b (encSegs s'.segs s'.zl) s'.cp1 s'.kb s'.mrg s'.ds) := by
      intro ts _ hg_ts
      dsimp only
      rw [if_neg (by simp)]
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq] at hg_ts
      rcases hg_ts with ⟨⟨⟨hd32, hg1⟩, hg2⟩, hphi16⟩
      rw [if_pos hd32]
      have hc1 : ¬ (d % 2 = 0 ∧ d ≤ 2 * (d2 + 1) + 4 ∧ GoodDs (((d2 + 1) - 1) :: ts) = false) := by
        intro ⟨he, hle, hgf⟩
        rcases hg1 with hnot | hgt
        · exact hnot ⟨he, hle⟩
        · rw [hgf] at hgt; cases hgt
      have hc2 : ¬ (d % 2 = 0 ∧ d + 14 ≤ 2 * (d2 + 1) ∧ GoodDs (((d2 + 1) - 2) :: ts) = false) := by
        intro ⟨he, hle, hgf⟩
        rcases hg2 with hnot | hgt
        · exact hnot ⟨he, hle⟩
        · rw [hgf] at hgt; cases hgt
      have hc3 : ¬ (cp1 + epW ls < 16) := by omega
      rw [if_neg hc1, if_neg hc2, if_neg hc3]
      rcases dec_or (d2 + 1 = 1 ∧ ts = [] ∧ d ≥ 25) with hrst2 | hrst2
      · rw [if_pos hrst2]; rw [if_pos hrst2]; dsimp only; rw [encSegs_normSeg, z0Rep,
        encSegs_pushSeg, htail]; rfl
      · rw [if_neg hrst2]; rw [if_neg hrst2]; dsimp only; rw [encSegs_normSeg, z0Rep,
        encSegs_pushSeg, htail]; rfl
    rcases ds2 with _ | ⟨d3, ds3⟩
    · change (if false = true then _ else _) = _
      rw [if_neg Bool.false_ne_true]
      have hf1 : isDrainRstDs [d, d2 + 1] = false := rfl
      have hf2 : isRank0 [d, d2 + 1] = false := by rcases d with _ | _ | _ | _ <;> rfl
      rw [hf1, hf2, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true] at hg ⊢
      dsimp only
      exact h_ge2_step [] hf1 hg
    · change (if false = true then _ else _) = _
      rw [if_neg Bool.false_ne_true]
      have hf1 : isDrainRstDs (d :: (d2 + 1) :: d3 :: ds3) = false := rfl
      have hf2 : isRank0 (d :: (d2 + 1) :: d3 :: ds3) = false := by
        rcases d with _ | _ | _ | _ <;> rfl
      rw [hf1, hf2, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true] at hg ⊢
      dsimp only
      exact h_ge2_step (d3 :: ds3) hf1 hg

theorem checkChainAux_eq_of_guards (fuel : Nat) (s : SegState) (hg : stepGuards s = true) :
    checkChainAux (fuel + 1) s.b (encSegs s.segs s.zl) s.cp1 s.kb s.mrg s.ds =
      let s' := stepSegs s
      checkChainAux fuel s'.b (encSegs s'.segs s'.zl) s'.cp1 s'.kb s'.mrg s'.ds := by
  rcases s with ⟨b, segs, zl, cp1, kb, mrg, ds⟩
  cases b with
  | false =>
    rcases segs with _ | ⟨⟨z, m⟩, rest⟩
    · dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
      simp only [Bool.and_eq_true] at hg
      rcases hg with ⟨hphi, hpsi⟩
      conv_lhs => unfold checkChainAux
      rw [z0_z0Rep_of_zero rfl zl, dropZ0_z0Rep_of_nonz0 rfl zl]
      have hhd : (!isHeadP5 [] && !GoodPhiW (cp1 + zl - 1) ds false) = false := by
        simp [isHeadP5, hphi]
      rw [if_neg (by rw [hhd]; decide)]
      dsimp only
      rw [hpsi, Bool.true_and]
      have h6 : 2 * (kb + 2 * zl + 1) + 4 = 2 * (kb + 2 * zl) + 6 := by omega
      rw [h6]; rfl
    · cases m with
      | zero =>
        dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
        conv_lhs => unfold checkChainAux
        rw [z0_z0Rep_of_zero rfl z, dropZ0_z0Rep_of_nonz0 rfl z]
        have hhd : (!isHeadP5 (.p5 :: encSegs rest zl) && !GoodPhiW (cp1 + z - 1) ds false) =
          false := by
          simp [isHeadP5]
        rw [if_neg (by rw [hhd]; decide)]
        dsimp only
        have h8 : 2 * (cp1 + z + 2) + 4 = 2 * (cp1 + z) + 8 := by omega
        rw [h8]
      | succ m' =>
        dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
        simp only [Bool.and_eq_true] at hg
        rcases hg with ⟨hphi, hg_rest⟩
        conv_lhs => unfold checkChainAux
        rw [z0_z0Rep_of_zero rfl z, dropZ0_z0Rep_of_nonz0 rfl z]
        have hhd : (!isHeadP5 (.p3z (m' + 1) :: .p5 :: encSegs rest zl) &&
            !GoodPhiW (cp1 + z - 1) ds false) = false := by
          simp [isHeadP5, hphi]
        rw [if_neg (by rw [hhd]; decide)]
        dsimp only [drop1L]
        rcases dec_or (m' + 1 = 1) with hm1 | hm1
        · rw [if_pos hm1] at hg_rest
          rw [if_pos hm1, if_pos hm1]
          dsimp only
          rw [hg_rest, Bool.true_and]
        · rw [if_neg hm1] at hg_rest
          rw [if_neg hm1, if_neg hm1]
          simp only [Bool.and_eq_true] at hg_rest
          rcases hg_rest with ⟨hpsi, hg_sub⟩
          have hnpsi : (!GoodPsi (cp1 + z - 1) ds) = false := by simp [hpsi]
          rw [if_neg (by rw [hnpsi]; decide)]
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (kb + 2 * z) + 10) with hev | hev
          · rw [if_pos hev, if_pos hev]
          · rw [if_neg hev] at hg_sub
            rw [if_neg hev, if_neg hev]
            rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (kb + 2 * z) + 11) with hod | hod
            · rw [if_pos hod] at hg_sub
              rw [if_pos hod, if_pos hod]
              dsimp only
              rw [hg_sub, Bool.true_and]
              rfl
            · rw [if_neg hod, if_neg hod]
              dsimp only
              rw [encSegs_normSeg, z0Rep]
              have h6 : 2 * (kb + 2 * z + 1) + 4 = 2 * (kb + 2 * z) + 6 := by omega
              rw [h6]
  | true =>
    rcases segs with _ | ⟨⟨z, m⟩, rest⟩
    · dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
      have hepw : epW (z0Rep zl []) = zl := epW_z0Rep_nil zl
      have h1 : (hasOdd (z0Rep zl []) && decide (mrg ≥ kb + epSum (z0Rep zl []))) = false := by
        rw [hasOdd_z0Rep]; rfl
      have h2 : (!hasOdd (z0Rep zl []) && hasP5 (z0Rep zl []) &&
          (isHeadP5 (z0Rep zl []) || decide (mrg ≥ kb + epSum (z0Rep zl [])))) = false := by
        rw [hasP5_z0Rep]; simp [hasP5]
      have h_eq := drainPop_eq_checkChain fuel (z0Rep zl []) cp1 kb mrg ds false 0 [] zl
        h1 h2 (by rw [hasP5_z0Rep]; rfl) (by intro h; cases h) (by intro h; cases h)
        (by rw [hepw]; exact hg)
      rw [hepw] at h_eq
      exact h_eq
    · cases m with
      | zero =>
        dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
        simp only [decide_eq_true_eq] at hg
        conv_lhs => unfold checkChainAux
        have hodd : hasOdd (z0Rep z (.p5 :: encSegs rest zl)) = false := by
          rw [hasOdd_z0Rep]; rfl
        have hp5 : hasP5 (z0Rep z (.p5 :: encSegs rest zl)) = true := by
          rw [hasP5_z0Rep]; rfl
        have heps : epSum (z0Rep z (.p5 :: encSegs rest zl)) = 0 := by
          rw [epSum_z0Rep]; rfl
        have hep : ep (z0Rep z (.p5 :: encSegs rest zl)) = z := by
          rw [ep_z0Rep]; simp [ep]
        have hsuf : p5Suf (z0Rep z (.p5 :: encSegs rest zl)) = encSegs rest zl := by
          rw [p5Suf_z0Rep]; rfl
        have h1 : (hasOdd (z0Rep z (.p5 :: encSegs rest zl)) &&
            decide (mrg ≥ kb + epSum (z0Rep z (.p5 :: encSegs rest zl)))) = false := by
          rw [hodd]; rfl
        have h2 : (!hasOdd (z0Rep z (.p5 :: encSegs rest zl)) &&
            hasP5 (z0Rep z (.p5 :: encSegs rest zl)) &&
            (isHeadP5 (z0Rep z (.p5 :: encSegs rest zl)) ||
              decide (mrg ≥ kb + epSum (z0Rep z (.p5 :: encSegs rest zl))))) = true := by
          rw [hodd, hp5, heps]
          have hdec : decide (mrg ≥ kb + 0) = true := decide_eq_true (by omega)
          rw [hdec, Bool.or_true]; rfl
        rw [if_neg (by rw [h1]; decide), if_pos h2, hsuf, hep, heps]
        have hk3 : kb + 0 + 2 * z + 3 = kb + 2 * z + 3 := by omega
        rw [hk3]
      | succ m' =>
        dsimp [stepGuards, stepSegs, encSegs] at hg ⊢
        set ls := z0Rep z (.p3z (m' + 1) :: .p5 :: encSegs rest zl)
        have hp5 : hasP5 ls = true := by rw [hasP5_z0Rep]; rfl
        have hsuf : p5Suf ls = encSegs rest zl := by rw [p5Suf_z0Rep]; rfl
        have hhd : isHeadP5 ls = false := isHeadP5_z0Rep_p3z z (m' + 1) (.p5 :: encSegs rest zl)
        have hepw : epW ls = z := epW_z0Rep_p3z z (m' + 1) (encSegs rest zl)
        rcases dec_or ((m' + 1) % 2 = 1) with hm_odd | hm_even
        · rw [if_pos hm_odd] at hg ⊢
          have hodd : hasOdd ls = true := by
            rw [hasOdd_z0Rep]; dsimp [hasOdd]; rw [if_pos hm_odd]
          have hmd : MustDrain ls = false := by
            rw [MustDrain_z0Rep]; dsimp [MustDrain]; rw [if_pos hm_odd]
          have hep : ep ls = z := by
            rw [ep_z0Rep]; dsimp [ep]; rw [if_pos hm_odd]; omega
          have heps : epSum ls = m' := by
            rw [epSum_z0Rep]; dsimp [epSum]; rw [if_pos hm_odd]
          cases hd_mrg : decide (mrg ≥ kb + m') with
          | true =>
            simp only [hd_mrg, ite_true] at hg ⊢
            conv_lhs => unfold checkChainAux
            have h1 : (hasOdd ls && decide (mrg ≥ kb + epSum ls)) = true := by
              rw [hodd, heps, hd_mrg]; rfl
            rw [if_pos h1]
            dsimp only
            rw [hmd, hp5, hsuf, hep, heps]
            change (GoodDs ((cp1 + z) :: ds) &&
              checkChainAux fuel false (encSegs rest zl) (kb + m' + 2 * z + 4) 1 0 ((cp1 +
                z) :: ds)) = _
            rw [hg, Bool.true_and]
          | false =>
            simp only [hd_mrg, Bool.false_eq_true, ite_false] at hg ⊢
            have h1 : (hasOdd ls && decide (mrg ≥ kb + epSum ls)) = false := by
              rw [hodd, heps, hd_mrg]; rfl
            have h2 : (!hasOdd ls && hasP5 ls &&
                (isHeadP5 ls || decide (mrg ≥ kb + epSum ls))) = false := by
              rw [hodd]; rfl
            have h_eq := drainPop_eq_checkChain fuel ls cp1 kb mrg ds true
              (kb + (m' + 1) - (mrg + 2)) rest zl h1 h2 hp5 (fun _ => hsuf)
              (fun _ => by rw [heps, hodd]; simp only [ite_true, Nat.add_assoc])
              (by rw [hepw]; exact hg)
            rw [hepw] at h_eq
            exact h_eq
        · rw [if_neg hm_even] at hg ⊢
          have hodd : hasOdd ls = false := by
            rw [hasOdd_z0Rep]; dsimp [hasOdd]; rw [if_neg hm_even]
          have hep : ep ls = z + 1 := by
            rw [ep_z0Rep]; dsimp [ep]; rw [if_neg hm_even]
          have heps : epSum ls = m' + 1 := by
            rw [epSum_z0Rep]; dsimp [epSum]; rw [if_neg hm_even]
          cases hd_mrg : decide (mrg ≥ kb + (m' + 1)) with
          | true =>
            simp only [hd_mrg, ite_true] at hg ⊢
            conv_lhs => unfold checkChainAux
            have h1 : (hasOdd ls && decide (mrg ≥ kb + epSum ls)) = false := by
              rw [hodd]; rfl
            have h2 : (!hasOdd ls && hasP5 ls &&
                (isHeadP5 ls || decide (mrg ≥ kb + epSum ls))) = true := by
              rw [hodd, hp5, hhd, heps, hd_mrg]; rfl
            rw [if_neg (by rw [h1]; decide), if_pos h2, hsuf, hep, heps]
            have hc2 : cp1 + (z + 1) + 1 = cp1 + z + 2 := by omega
            have hk5 : kb + (m' + 1) + 2 * (z + 1) + 3 = kb + (m' + 1) + 2 * z + 5 := by omega
            rw [hc2, hk5]
          | false =>
            simp only [hd_mrg, Bool.false_eq_true, ite_false] at hg ⊢
            have h1 : (hasOdd ls && decide (mrg ≥ kb + epSum ls)) = false := by
              rw [hodd]; rfl
            have h2 : (!hasOdd ls && hasP5 ls &&
                (isHeadP5 ls || decide (mrg ≥ kb + epSum ls))) = false := by
              rw [hodd, hp5, hhd, heps, hd_mrg]; rfl
            have h_eq := drainPop_eq_checkChain fuel ls cp1 kb mrg ds true
              (kb + (m' + 1) - (mrg + 2)) rest zl h1 h2 hp5 (fun _ => hsuf)
              (fun _ => by rw [heps, hodd]; simp only [Bool.false_eq_true, ite_false, Nat.add_zero])
              (by rw [hepw]; exact hg)
            rw [hepw] at h_eq
            exact h_eq


-- ============================================================================
-- Section 5g.2: Fuel-Bounded LeadsUpTo Framework & Stack-Polymorphic Excursion
-- ============================================================================

def FailsIn (s : SegState) (n : Nat) : Prop :=
  checkChainAux n s.b (encSegs s.segs s.zl) s.cp1 s.kb s.mrg s.ds = false

def ChainLeadsUpTo (N : Nat) (s : SegState) (P : SegState → Prop) : Prop :=
  ∀ n, n ≤ N → FailsIn s n → ∃ m s', m ≤ n ∧ P s' ∧ FailsIn s' m

def ChainLeads (s : SegState) (P : SegState → Prop) : Prop :=
  ∀ N, ChainLeadsUpTo N s P

def ChainAdvances (s : SegState) (P : SegState → Prop) : Prop :=
  stepGuards s = true ∧ ChainLeads (stepSegs s) P

theorem not_failsIn_zero (s : SegState) : ¬FailsIn s 0 := by
  intro h; cases h

theorem chainLeadsUpTo_here {N : Nat} {s : SegState} {P : SegState → Prop} (hp : P s) :
    ChainLeadsUpTo N s P := by
  intro n _ hf
  exact ⟨n, s, Nat.le_refl n, hp, hf⟩

theorem chainLeadsUpTo_mono {M N : Nat} (hle : M ≤ N) {s : SegState} {P : SegState → Prop}
    (h : ChainLeadsUpTo N s P) : ChainLeadsUpTo M s P := by
  intro n hn hf
  exact h n (Nat.le_trans hn hle) hf

theorem chainLeadsUpTo_imp {N : Nat} {s : SegState} {P Q : SegState → Prop}
    (h : ChainLeadsUpTo N s P) (himp : ∀ s', P s' → Q s') : ChainLeadsUpTo N s Q := by
  intro n hn hf
  obtain ⟨m, s', hm, hp, hfm⟩ := h n hn hf
  exact ⟨m, s', hm, himp s' hp, hfm⟩

theorem chainLeadsUpTo_trans {N : Nat} {s : SegState} {P Q : SegState → Prop}
    (h1 : ChainLeadsUpTo N s P)
    (h2 : ∀ m s', m ≤ N → P s' → ChainLeadsUpTo m s' Q) :
    ChainLeadsUpTo N s Q := by
  intro n hn hf
  obtain ⟨m, s', hm, hp, hfm⟩ := h1 n hn hf
  obtain ⟨k, s'', hk, hq, hfk⟩ := h2 m s' (Nat.le_trans hm hn) hp m (Nat.le_refl m) hfm
  exact ⟨k, s'', Nat.le_trans hk hm, hq, hfk⟩

theorem chainLeadsUpTo_step {N : Nat} {s : SegState} {P : SegState → Prop}
    (hg : stepGuards s = true)
    (hnext : ∀ m, m < N → ChainLeadsUpTo m (stepSegs s) P) :
    ChainLeadsUpTo N s P := by
  intro n hn hf
  cases n with
  | zero => exact False.elim (not_failsIn_zero s hf)
  | succ m =>
    have h_eq := checkChainAux_eq_of_guards m s hg
    dsimp only [FailsIn] at hf
    rw [h_eq] at hf
    obtain ⟨k, s', hk, hp, hfk⟩ := hnext m (by omega) m (Nat.le_refl m) hf
    exact ⟨k, s', by omega, hp, hfk⟩

theorem chainLeadsUpTo_step1 {N : Nat} {s : SegState} {P : SegState → Prop}
    (hg : stepGuards s = true)
    (hnext : ChainLeadsUpTo N (stepSegs s) P) :
    ChainLeadsUpTo N s P :=
  chainLeadsUpTo_step hg (fun m hm => chainLeadsUpTo_mono (by omega) hnext)

theorem checkChainAux_true_of_advances {P : SegState → Prop}
    (hadv : ∀ s, P s → ChainAdvances s P) :
    ∀ fuel s, P s → checkChainAux fuel s.b (encSegs s.segs s.zl) s.cp1 s.kb s.mrg s.ds = true := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h n ih =>
    intro s hp
    cases n with
    | zero => rfl
    | succ m =>
      obtain ⟨hg, hleads⟩ := hadv s hp
      cases hval : checkChainAux (m + 1) s.b (encSegs s.segs s.zl) s.cp1 s.kb s.mrg s.ds with
      | true => rfl
      | false =>
        have h_eq := checkChainAux_eq_of_guards m s hg
        rw [h_eq] at hval
        obtain ⟨k, s', hk, hps', hfk⟩ := hleads m m (Nat.le_refl m) hval
        have htr := ih k (by omega) s' hps'
        dsimp only [FailsIn] at hfk
        rw [htr] at hfk
        cases hfk

-- ============================================================================
-- Segment Validity, SafeStack, and Standalone Arithmetic Lemmas
-- ============================================================================

def ValidSegs40 (segs : List (Nat × Nat)) (zl : Nat) : Prop :=
  (∀ p ∈ segs, 40 ≤ p.1) ∧ 230 ≤ zl

def ValidTail40 (segs : List (Nat × Nat)) (zl : Nat) : Prop :=
  match segs with
  | [] => 230 ≤ zl
  | _ :: rest => ValidSegs40 rest zl

def fzOf (segs : List (Nat × Nat)) (zl : Nat) : Nat :=
  match segs with
  | [] => zl
  | (z, _) :: _ => z

theorem fzOf_ge_40 {segs : List (Nat × Nat)} {zl : Nat} (hv : ValidSegs40 segs zl) :
    40 ≤ fzOf segs zl := by
  rcases segs with _ | ⟨⟨z, m⟩, rest⟩
  · exact Nat.le_trans (by decide) hv.2
  · exact hv.1 (z, m) List.mem_cons_self

theorem validTail40_of_validSegs40 {segs : List (Nat × Nat)} {zl : Nat}
    (hv : ValidSegs40 segs zl) : ValidTail40 segs zl := by
  rcases segs with _ | ⟨p, rest⟩
  · exact hv.2
  · exact ⟨fun q hq => hv.1 q (List.mem_cons_of_mem _ hq), hv.2⟩

theorem validSegs40_tail {p : Nat × Nat} {rest : List (Nat × Nat)} {zl : Nat}
    (hv : ValidSegs40 (p :: rest) zl) : ValidSegs40 rest zl :=
  ⟨fun q hq => hv.1 q (List.mem_cons_of_mem _ hq), hv.2⟩

theorem normSeg_fst_ge (z m : Nat) : z ≤ (normSeg z m).1 := by
  dsimp [normSeg]
  rcases dec_or (m = 0) with hm | hm
  · rw [if_pos hm]; omega
  · rw [if_neg hm]

theorem validSegs40_pushSeg (hp : Bool) {z m : Nat} {rest : List (Nat × Nat)} {zl : Nat}
    (hz : 40 ≤ z) (hv : hp = true → ValidSegs40 rest zl) (hzl : hp = false → 230 ≤ z) :
    ValidSegs40 (pushSeg hp z m rest zl).1 (pushSeg hp z m rest zl).2 := by
  cases hp with
  | false =>
    exact ⟨(by intro _ h; cases h), hzl rfl⟩
  | true =>
    have hvr := hv rfl
    refine ⟨?_, hvr.2⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact Nat.le_trans hz (normSeg_fst_ge z m)
    · exact hvr.1 q hq'

theorem validTail40_pushSeg (hp : Bool) {z m : Nat} {rest : List (Nat × Nat)} {zl : Nat}
    (hv : hp = true → ValidSegs40 rest zl) (hzl : hp = false → 230 ≤ z) :
    ValidTail40 (pushSeg hp z m rest zl).1 (pushSeg hp z m rest zl).2 := by
  cases hp with
  | false => exact hzl rfl
  | true => exact hv rfl

theorem fzOf_pushSeg_ge (hp : Bool) (z m : Nat) (rest : List (Nat × Nat)) (zl : Nat) :
    z ≤ fzOf (pushSeg hp z m rest zl).1 (pushSeg hp z m rest zl).2 := by
  cases hp with
  | false => exact Nat.le_refl z
  | true => exact normSeg_fst_ge z m

theorem goodPhiW_of_ge35 {phiW : Nat} {ds : List Nat} (hne2 : ds ≠ [2]) (h35 : 35 ≤ phiW) :
    GoodPhiW phiW ds false = true := by
  dsimp only [GoodPhiW]
  rw [if_neg hne2]
  rcases dec_or (ds = [0]) with h0 | h0
  · rw [if_pos h0]; exact decide_eq_true (by omega)
  · rw [if_neg h0]
    rcases dec_or (ds = [1]) with h1 | h1
    · rw [if_pos h1]; exact decide_eq_true (by omega)
    · rw [if_neg h1]
      rcases dec_or (ds = []) with hn | hn
      · rw [if_pos hn, Bool.false_or]; exact decide_eq_true (by omega)
      · rw [if_neg hn]
        have hd35 : decide (phiW ≥ 35) = true := decide_eq_true (by omega)
        have hd17 : decide (phiW ≥ 17) = true := decide_eq_true (by omega)
        have hd15 : decide (phiW ≥ 15) = true := decide_eq_true (by omega)
        rcases ds with _ | ⟨d, _ | ⟨d2, _ | ⟨d3, ds3⟩⟩⟩
        · exact False.elim (hn rfl)
        · dsimp only; rw [if_neg Bool.false_ne_true]
          cases isOddDrainDs [d] <;> simp only [ite_true, Bool.false_eq_true, ite_false, hd17, hd15]
        · cases d2 with
          | zero =>
            cases isOddDrainDs [d, 0] <;> simp only [ite_true, Bool.false_eq_true, ite_false, hd17,
              hd15]
          | succ d2' =>
            cases d2' with
            | zero =>
              cases hd25 : decide (d ≥ 25) <;>
                simp only [hd25, ite_true, Bool.false_eq_true, ite_false, isOddDrainDs, hd35, hd15]
            | succ _ =>
              simp only [Bool.false_eq_true, ite_false, isOddDrainDs, hd15]
        · simp only [Bool.false_eq_true, ite_false, isOddDrainDs, hd15]

def SafeStack (m : Nat) (S : List Nat) : Prop :=
  S ≠ [2] ∧ GoodDs S = true ∧ ∀ u, m ≤ u → GoodDs (u :: S) = true

theorem safeStack_mono {m1 m2 : Nat} {S : List Nat} (hle : m1 ≤ m2) (hs : SafeStack m1 S) :
    SafeStack m2 S :=
  ⟨hs.1, hs.2.1, fun u hu => hs.2.2 u (Nat.le_trans hle hu)⟩

theorem isOddDrain1_eq_false_of_ge18 {x : Nat} (hx : 18 ≤ x) : isOddDrain1 x = false := by
  dsimp only [isOddDrain1]
  exact decide_eq_false (by omega)

theorem safeStack_cons {m x : Nat} {S : List Nat}
    (hs : SafeStack m S) (hx18 : 18 ≤ x) (hxm : m + 2 ≤ x) :
    SafeStack 39 (x :: S) := by
  refine ⟨(by intro h; injection h with h1; omega), hs.2.2 x (by omega), ?_⟩
  intro u hu
  rcases S with _ | ⟨d3, ds3⟩
  · dsimp only [GoodDs, GoodDsAux, GoodDs2]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hod : isOddDrain1 x = false := isOddDrain1_eq_false_of_ge18 hx18
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hg0 : GoodDs1 x = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg1 : GoodDs1 (x - 1) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg2 : GoodDs1 (x - 2) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    rw [hod, hu17, hg0, hg1, hg2]
    simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
      Bool.false_eq_true, ite_false]
  · dsimp only [GoodDs, GoodDsAux]
    rw [if_neg (by omega)]
    have h31 : decide (x = 3 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 19) = false := decide_eq_false (by omega)
    have hod : isOddDrainDs (x :: d3 :: ds3) = false := by
      cases d3 with
      | zero =>
        rcases ds3 with _ | ⟨d4, ds4⟩
        · dsimp only [isOddDrainDs]; exact isOddDrain1_eq_false_of_ge18 hx18
        · rfl
      | succ _ => rfl
    have hd25 : decide (x ≥ 25 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 39) = false :=
      decide_eq_false (by omega)
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hg0 : GoodDsAux x (d3 :: ds3) = true := hs.2.2 x (by omega)
    have hg1 : GoodDsAux (x - 1) (d3 :: ds3) = true := hs.2.2 (x - 1) (by omega)
    have hg2 : GoodDsAux (x - 2) (d3 :: ds3) = true := hs.2.2 (x - 2) (by omega)
    rw [h31, hod, hd25, hu17, hg0, hg1, hg2]
    simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
      Bool.false_eq_true, ite_false]

theorem safeStack_cons_ne1 {m x : Nat} {S : List Nat}
    (hne1 : S ≠ [1]) (hs : SafeStack m S) (hx18 : 18 ≤ x) (hxm : m + 2 ≤ x) :
    SafeStack 19 (x :: S) := by
  refine ⟨(by intro h; injection h with h1; omega), hs.2.2 x (by omega), ?_⟩
  intro u hu
  rcases S with _ | ⟨d3, ds3⟩
  · dsimp only [GoodDs, GoodDsAux, GoodDs2]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hod : isOddDrain1 x = false := isOddDrain1_eq_false_of_ge18 hx18
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hg0 : GoodDs1 x = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg1 : GoodDs1 (x - 1) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg2 : GoodDs1 (x - 2) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    rw [hod, hu17, hg0, hg1, hg2]
    simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
      Bool.false_eq_true, ite_false]
  · dsimp only [GoodDs, GoodDsAux]
    rw [if_neg (by omega)]
    have h31 : decide (x = 3 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 19) = false := decide_eq_false (by omega)
    have hod : isOddDrainDs (x :: d3 :: ds3) = false := by
      cases d3 with
      | zero =>
        rcases ds3 with _ | ⟨d4, ds4⟩
        · dsimp only [isOddDrainDs]; exact isOddDrain1_eq_false_of_ge18 hx18
        · rfl
      | succ _ => rfl
    have hd25 : decide (x ≥ 25 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 39) = false := by
      apply decide_eq_false
      rintro ⟨_, rfl, rfl, _⟩
      exact hne1 rfl
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hg0 : GoodDsAux x (d3 :: ds3) = true := hs.2.2 x (by omega)
    have hg1 : GoodDsAux (x - 1) (d3 :: ds3) = true := hs.2.2 (x - 1) (by omega)
    have hg2 : GoodDsAux (x - 2) (d3 :: ds3) = true := hs.2.2 (x - 2) (by omega)
    rw [h31, hod, hd25, hu17, hg0, hg1, hg2]
    simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
      Bool.false_eq_true, ite_false]

def ox (kz cz : Nat) : Nat := cz - (3 * cz - kz) / 30 - 2
def odw (kz cz : Nat) : Nat := ox kz cz - 1
def oxw (kz cz : Nat) : Nat := cz + kz / 20 + 36

theorem ox_spec_lt {kz cz : Nat} (hlt : kz < 3 * cz) :
    ∃ q r, r < 30 ∧ 3 * cz = kz + 30 * q + r ∧ ox kz cz = cz - q - 2 := by
  set d := 3 * cz - kz
  refine ⟨d / 30, d % 30, Nat.mod_lt d (by decide), ?_, rfl⟩
  have hdiv := Nat.div_add_mod d 30
  omega

theorem div20_spec (kz : Nat) : ∃ q r, r < 20 ∧ kz = 20 * q + r ∧ kz / 20 = q :=
  ⟨kz / 20, kz % 20, Nat.mod_lt kz (by decide), (Nat.div_add_mod kz 20).symm, rfl⟩

theorem div10_spec (kz : Nat) : ∃ q r, r < 10 ∧ kz = 10 * q + r ∧ kz / 10 = q :=
  ⟨kz / 10, kz % 10, Nat.mod_lt kz (by decide), (Nat.div_add_mod kz 10).symm, rfl⟩

theorem ox_bounds_relaxed {c k fz : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz : 35 ≤ fz) (hcz : 42 ≤ c + fz) (hkz : 73 ≤ k + 2 * fz) :
    39 ≤ ox (k + 2 * fz) (c + fz) ∧ ox (k + 2 * fz) (c + fz) + 3 ≤ c + fz := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  omega

theorem ox_ge41_of_c5 {c k fz : Nat}
    (_hc : 5 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz) :
    41 ≤ ox (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  omega

theorem arith_fb_t0 {c k z0 z1 fz2 : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hz1 : 40 ≤ z1) (_hfz2 : 40 ≤ fz2) :
    ox (k + 2 * z0) (c + z0) ≤
      ox (k + 2 * z0 + 3 + 2 * z1 + 3 + 2 * fz2) (c + z0 + 3 + z1 + 1 + fz2) ∧
    odw (k + 2 * z0) (c + z0) ≤
      odw (k + 2 * z0 + 3 + 2 * z1 + 3 + 2 * fz2) (c + z0 + 3 + z1 + 1 + fz2) ∧
    oxw (k + 2 * z0) (c + z0) ≤
      oxw (k + 2 * z0 + 3 + 2 * z1 + 3 + 2 * fz2) (c + z0 + 3 + z1 + 1 + fz2) := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨q2, r2, hr2, heq2, hox2⟩ :=
    ox_spec_lt (kz := k + 2 * z0 + 3 + 2 * z1 + 3 + 2 * fz2) (cz :=
      c + z0 + 3 + z1 + 1 + fz2) (by omega)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  obtain ⟨qw2, rw2, hrw2, hkw2, hdw2⟩ := div20_spec (k + 2 * z0 + 3 + 2 * z1 + 3 + 2 * fz2)
  dsimp only [odw, oxw]
  rw [hdw1, hdw2, hox1, hox2]
  omega

theorem arith_fb_to {c k z0 z1 m1' fz2 : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hz1 : 40 ≤ z1) (_hfz2 : 40 ≤ fz2) :
    ox (k + 2 * z0) (c + z0) ≤ c + z0 + 3 + z1 ∧
    30 * ox (k + 2 * z0) (c + z0) ≤
      (k + 2 * z0 + 3 + m1' + 2 * z1 + 4 + fz2) + 27 * (c + z0 + 3 + z1) + 900 ∧
    60 * ox (k + 2 * z0) (c + z0) + 120 ≤
      2 * (k + 2 * z0 + 3 + m1' + 2 * z1 + 4 + fz2) + 55 * (c + z0 + 3 + z1) ∧
    10 * oxw (k + 2 * z0) (c + z0) + 40 ≤
      9 * (k + 2 * z0 + 3 + m1' + 2 * z1 + 4 + fz2) + 10 * (c + z0 + 3 + z1) ∧
    20 * oxw (k + 2 * z0) (c + z0) ≤
      (k + 2 * z0 + 3 + m1' + 2 * z1 + 4 + fz2) + 20 * (c + z0 + 3 + z1) + 800 := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  dsimp only [oxw]
  rw [hdw1, hox1]
  omega

theorem arith_fb_te {c k z0 z1 m1' fz2 : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hz1 : 40 ≤ z1) (_hfz2 : 40 ≤ fz2)
    (_hmrg : 2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) :
    ox (k + 2 * z0) (c + z0) ≤
      ox ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5 + 2 * fz2) (c + z0 + 3 + z1 + 2 + fz2) ∧
    odw (k + 2 * z0) (c + z0) ≤
      odw ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5 + 2 * fz2) (c + z0 + 3 + z1 + 2 + fz2) ∧
    oxw (k + 2 * z0) (c + z0) ≤
      oxw ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5 + 2 * fz2) (c + z0 + 3 + z1 + 2 + fz2) := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨q2, r2, hr2, heq2, hox2⟩ :=
    ox_spec_lt (kz := (k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5 + 2 * fz2) (cz :=
      c + z0 + 3 + z1 + 2 + fz2) (by omega)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  obtain ⟨qw2, rw2, hrw2, hkw2, hdw2⟩ :=
    div20_spec ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5 + 2 * fz2)
  dsimp only [odw, oxw]
  rw [hdw1, hdw2, hox1, hox2]
  omega

theorem arith_fb_m1_ev {c k z0 fz1 dx : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hfz1 : 40 ≤ fz1) (_hdx : dx ≤ 1) :
    ox (k + 2 * z0) (c + z0) ≤ c + z0 + dx ∧
    30 * ox (k + 2 * z0) (c + z0) ≤ (k + 2 * z0 + 4 + fz1) + 27 * (c + z0 + dx) + 900 ∧
    60 * ox (k + 2 * z0) (c + z0) + 120 ≤ 2 * (k + 2 * z0 + 4 + fz1) + 55 * (c + z0 + dx) ∧
    10 * oxw (k + 2 * z0) (c + z0) + 40 ≤ 9 * (k + 2 * z0 + 4 + fz1) + 10 * (c + z0 + dx) ∧
    20 * oxw (k + 2 * z0) (c + z0) ≤ (k + 2 * z0 + 4 + fz1) + 20 * (c + z0 + dx) + 800 := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  dsimp only [oxw]
  rw [hdw1, hox1]
  omega

theorem arith_fb_os_r10 {c k z0 y1 phi1 fz4 : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hy1_lo : 9 * ((k + 2 * z0) / 10) - 2 ≤ y1)
    (_hy1_hi : y1 ≤ 2 * (c + z0) + 3)
    (_hphi1 : 38 ≤ phi1)
    (_hyw : k + 2 * z0 + 35 ≤ y1 + phi1)
    (_hfz4 : phi1 + 2 ≤ fz4) :
    ox (k + 2 * z0) (c + z0) ≤ ox (y1 + 2 + 2 * fz4) (c + z0 + 1 + fz4) ∧
    odw (k + 2 * z0) (c + z0) ≤ odw (y1 + 2 + 2 * fz4) (c + z0 + 1 + fz4) ∧
    oxw (k + 2 * z0) (c + z0) ≤ oxw (y1 + 2 + 2 * fz4) (c + z0 + 1 + fz4) := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨q4, r4, hr4, heq4, hox4⟩ := ox_spec_lt (kz := y1 + 2 + 2 * fz4) (cz :=
    c + z0 + 1 + fz4) (by omega)
  obtain ⟨q10, r10, hr10, hkz10, hdw10⟩ := div10_spec (k + 2 * z0)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  obtain ⟨qw4, rw4, hrw4, hkw4, hdw4⟩ := div20_spec (y1 + 2 + 2 * fz4)
  rw [hdw10] at _hy1_lo
  dsimp only [odw, oxw]
  rw [hdw1, hdw4, hox1, hox4]
  omega

theorem arith_fb_os_r11 {c k z0 y1 phi1 fz4 : Nat}
    (_hc : 1 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (_hfz0 : 35 ≤ z0) (_hcz : 42 ≤ c + z0) (_hkz : 73 ≤ k + 2 * z0)
    (_hyw : k + 2 * z0 + 35 ≤ y1 + phi1)
    (_hfz4 : phi1 + 2 ≤ fz4) :
    ox (k + 2 * z0) (c + z0) ≤ c + z0 - 1 ∧
    30 * ox (k + 2 * z0) (c + z0) ≤ (y1 + fz4) + 27 * (c + z0 - 1) + 900 ∧
    60 * ox (k + 2 * z0) (c + z0) + 120 ≤ 2 * (y1 + fz4) + 55 * (c + z0 - 1) ∧
    10 * oxw (k + 2 * z0) (c + z0) + 40 ≤ 9 * (y1 + fz4) + 10 * (c + z0 - 1) ∧
    20 * oxw (k + 2 * z0) (c + z0) ≤ (y1 + fz4) + 20 * (c + z0 - 1) + 800 := by
  obtain ⟨q1, r1, hr1, heq1, hox1⟩ := ox_spec_lt (kz := k + 2 * z0) (cz := c + z0) (by omega)
  obtain ⟨qw1, rw1, hrw1, hkw1, hdw1⟩ := div20_spec (k + 2 * z0)
  dsimp only [oxw]
  rw [hdw1, hox1]
  omega

theorem arith_lb_r10 {c k fz x tx txw y phi fz3 : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz)
    (_htx21 : 21 ≤ tx) (_htx_x : tx ≤ x)
    (_hi1 : 30 * tx ≤ (c + fz) + 27 * x + 900)
    (_hi2 : 60 * tx + 120 ≤ 2 * (c + fz) + 55 * x)
    (_hi3 : 10 * txw + 40 ≤ 9 * (c + fz) + 10 * x)
    (_hi4 : 20 * txw ≤ (c + fz) + 20 * x + 800)
    (_hy_lo : ox (k + 2 * fz) (c + fz) ≤ y)
    (_hy_hi : y ≤ 2 * x + 3)
    (_hphi38 : 38 ≤ phi)
    (_hyw : oxw (k + 2 * fz) (c + fz) ≤ y + phi)
    (_hfz3 : phi + 2 ≤ fz3) :
    tx ≤ ox (y + 2 + 2 * fz3) (x + 1 + fz3) ∧
    tx - 1 ≤ odw (y + 2 + 2 * fz3) (x + 1 + fz3) ∧
    txw ≤ oxw (y + 2 + 2 * fz3) (x + 1 + fz3) := by
  obtain ⟨q2, r2, hr2, heq2, hox2⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨q3, r3, hr3, heq3, hox3⟩ := ox_spec_lt (kz := y + 2 + 2 * fz3) (cz :=
    x + 1 + fz3) (by omega)
  obtain ⟨qw2, rw2, hrw2, hkw2, hdw2⟩ := div20_spec (k + 2 * fz)
  obtain ⟨qw3, rw3, hrw3, hkw3, hdw3⟩ := div20_spec (y + 2 + 2 * fz3)
  dsimp only [oxw] at _hyw
  rw [hdw2] at _hyw
  rw [hox2] at _hy_lo
  dsimp only [odw, oxw]
  rw [hdw3, hox3]
  omega

theorem arith_lb_r11 {c k fz x tx txw y phi fz3 : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz)
    (_htx21 : 21 ≤ tx) (_htx_x : tx ≤ x)
    (_hi1 : 30 * tx ≤ (c + fz) + 27 * x + 900)
    (_hi2 : 60 * tx + 120 ≤ 2 * (c + fz) + 55 * x)
    (_hi3 : 10 * txw + 40 ≤ 9 * (c + fz) + 10 * x)
    (_hi4 : 20 * txw ≤ (c + fz) + 20 * x + 800)
    (_hy_lo : ox (k + 2 * fz) (c + fz) ≤ y)
    (_hy_hi : y ≤ 2 * x + 4)
    (_hphi38 : 38 ≤ phi)
    (_hyw : oxw (k + 2 * fz) (c + fz) ≤ y + phi)
    (_hfz3 : phi + 2 ≤ fz3) :
    5 ≤ y ∧
    tx ≤ x - 1 ∧
    30 * tx ≤ (y + fz3) + 27 * (x - 1) + 900 ∧
    60 * tx + 120 ≤ 2 * (y + fz3) + 55 * (x - 1) ∧
    10 * txw + 40 ≤ 9 * (y + fz3) + 10 * (x - 1) ∧
    20 * txw ≤ (y + fz3) + 20 * (x - 1) + 800 := by
  obtain ⟨q2, r2, hr2, heq2, hox2⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨qw2, rw2, hrw2, hkw2, hdw2⟩ := div20_spec (k + 2 * fz)
  dsimp only [oxw] at _hyw
  rw [hdw2] at _hyw
  rw [hox2] at _hy_lo
  omega

-- ============================================================================
-- Pre-Pop Bounce Predicate & R9/R10/R11 Pop Dispatcher
-- ============================================================================

inductive IsBounce : Nat → List Nat → SegState → Prop where
  | nil {zl cp1 kb mrg : Nat} {ds : List Nat}
      (hphi : 230 ≤ cp1 + zl) :
      IsBounce (cp1 + zl) ds ⟨true, [], zl, cp1, kb, mrg, ds⟩
  | cons {z0 m zl cp1 kb mrg : Nat} {rest : List (Nat × Nat)} {ds : List Nat}
      (hv : ValidSegs40 rest zl)
      (hphi : 16 ≤ cp1 + z0)
      (hnm : if (m + 1) % 2 = 1 then mrg < kb + m else mrg < kb + (m + 1)) :
      IsBounce (cp1 + z0) ds ⟨true, (z0, m + 1) :: rest, zl, cp1, kb, mrg, ds⟩

theorem isBounce_step {phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi ds s) (hg_pop : drainPopGuards phi ds = true) :
    stepGuards s = true ∧ 16 ≤ phi ∧
      ∃ hp m_rem rest zl,
        (hp = true → ValidSegs40 rest zl) ∧
        (hp = false → 230 ≤ phi) ∧
        stepSegs s = drainPopStep hp phi m_rem rest zl ds := by
  cases hb with
  | @nil zl cp1 kb mrg ds hphi =>
    refine ⟨hg_pop, by omega, false, 0, [], zl, ?_, ?_, rfl⟩
    · intro h; cases h
    · intro _; exact hphi
  | @cons z0 m zl cp1 kb mrg rest ds hv hphi hnm =>
    refine ⟨?_, hphi, true, kb + (m + 1) - (mrg + 2), rest, zl, ?_, ?_, ?_⟩
    · dsimp only [stepGuards]
      rcases dec_or ((m + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod] at hnm ⊢
        rw [decide_eq_false (by omega)]; exact hg_pop
      · rw [if_neg hev] at hnm ⊢
        rw [decide_eq_false (by omega)]; exact hg_pop
    · intro _; exact hv
    · intro h; cases h
    · dsimp only [stepSegs]
      rcases dec_or ((m + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod] at hnm ⊢
        rw [decide_eq_false (by omega)]; rfl
      · rw [if_neg hev] at hnm ⊢
        rw [decide_eq_false (by omega)]; rfl

def Exit (tx tdw txw : Nat) (S : List Nat) (s : SegState) : Prop :=
  (∃ phi, tdw ≤ phi ∧ IsBounce phi S s) ∨
  (∃ y phi, tx ≤ y ∧ 38 ≤ phi ∧ txw ≤ y + phi ∧ IsBounce phi (y :: S) s)

theorem exit_mono {tx1 tdw1 txw1 tx2 tdw2 txw2 : Nat} {S : List Nat} {s : SegState}
    (he : Exit tx2 tdw2 txw2 S s)
    (h1 : tx1 ≤ tx2) (h2 : tdw1 ≤ tdw2) (h3 : txw1 ≤ txw2) :
    Exit tx1 tdw1 txw1 S s := by
  rcases he with ⟨phi, hp, hb⟩ | ⟨y, phi, hy, hp38, hyw, hb⟩
  · exact Or.inl ⟨phi, Nat.le_trans h2 hp, hb⟩
  · exact Or.inr ⟨y, phi, Nat.le_trans h1 hy, hp38, Nat.le_trans h3 hyw, hb⟩

theorem drainPop_two (hp : Bool) (phi m_rem zl y x : Nat) (rest : List (Nat × Nat)) (S : List Nat)
    (hy : 19 ≤ y) (hx : 19 ≤ x) (hphi : 16 ≤ phi)
    (hg1 : GoodDs ((x - 1) :: S) = true)
    (hg2 : y % 2 = 0 ∧ y + 14 ≤ 2 * x → GoodDs ((x - 2) :: S) = true) :
    drainPopGuards phi (y :: x :: S) = true ∧
      drainPopStep hp phi m_rem rest zl (y :: x :: S) =
        let p := pushSeg hp (phi + 2) m_rem rest zl
        ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ := by
  have hnrst : isDrainRstDs (y :: x :: S) = false := by
    cases x with
    | zero => omega
    | succ _ => rfl
  have hnr0 : isRank0 (y :: x :: S) = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  refine ⟨?_, ?_⟩
  · dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ x ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : (!decide (y % 2 = 0 ∧ y ≤ 2 * x + 4) || GoodDs ((x - 1) :: S)) = true := by
      rw [hg1, Bool.or_true]
    have hc3 : (!decide (y % 2 = 0 ∧ y + 14 ≤ 2 * x) || GoodDs ((x - 2) :: S)) = true := by
      rcases dec_or (y % 2 = 0 ∧ y + 14 ≤ 2 * x) with h | h
      · rw [hg2 h, Bool.or_true]
      · rw [decide_eq_false h]; rfl
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  · dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    rw [if_neg (by omega)]
    have hnorm : normSeg 0 (y - 3) = (0, y - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]

theorem amega_pop_step {N x y phi : Nat} {S : List Nat} {sb : SegState} {P : SegState → Prop}
    (hb : IsBounce phi (y :: x :: S) sb)
    (hphi38 : 38 ≤ phi) (hy : 19 ≤ y) (hx : 19 ≤ x)
    (hg1 : GoodDs ((x - 1) :: S) = true)
    (hg2 : y % 2 = 0 ∧ y + 14 ≤ 2 * x → GoodDs ((x - 2) :: S) = true)
    (hr9 : 2 * x + 5 ≤ y → ∀ m, m < N → ∀ p1 p2, ValidSegs40 p1 p2 → phi + 2 ≤ fzOf p1 p2 →
      ChainLeadsUpTo m ⟨true, (0, y - 3) :: p1, p2, x - 1, 0, 2 * x, S⟩ P)
    (hr10 : y ≤ 2 * x + 3 → y % 2 = 1 → ∀ m, m < N → ∀ p1 p2, ValidSegs40 p1 p2 →
      phi + 2 ≤ fzOf p1 p2 →
      ChainLeadsUpTo m ⟨false, p1, p2, x + 1, y + 2, 0, S⟩ P)
    (hr11 : y ≤ 2 * x + 4 → y % 2 = 0 → ∀ m, m < N → ∀ p1 p2, ValidSegs40 p1 p2 →
      phi + 2 ≤ fzOf p1 p2 →
      ChainLeadsUpTo m ⟨false, p1, p2, y, 1, 0, (x - 1) :: S⟩ P) :
    ChainLeadsUpTo N sb P := by
  have hg_pop : drainPopGuards phi (y :: x :: S) = true :=
    (drainPop_two false phi 0 0 y x [] S hy hx (by omega) hg1 hg2).1
  obtain ⟨hg_sb, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep_sb⟩ := isBounce_step hb hg_pop
  have hdp_eq := (drainPop_two hp phi m_rem zl y x rest S hy hx (by omega) hg1 hg2).2
  rw [hdp_eq] at hstep_sb
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  apply chainLeadsUpTo_step hg_sb
  intro m hm
  rw [hstep_sb]
  rcases dec_or (2 * x + 5 ≤ y) with hbig | hsmall
  · exact hr9 hbig m hm p.1 p.2 hvp hfzp
  · have hy_sub : y - 3 = (y - 4) + 1 := by omega
    rcases dec_or (y % 2 = 1) with hy_odd | hy_even
    · have hm_ev : ¬(((y - 4) + 1) % 2 = 1) := by omega
      have hmrg : decide (2 * x ≥ 0 + ((y - 4) + 1)) = true := decide_eq_true (by omega)
      have hg_mid : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ = true := by
        rw [hy_sub]
        dsimp only [stepGuards]
        rw [if_neg hm_ev, hmrg, if_pos rfl]
      have hs_mid : stepSegs ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ =
          ⟨false, p.1, p.2, x + 1, y + 2, 0, S⟩ := by
        rw [hy_sub]
        dsimp only [stepSegs]
        rw [if_neg hm_ev, hmrg, if_pos rfl]
        have hc : x - 1 + 0 + 2 = x + 1 := by omega
        have hk : 0 + (y - 4 + 1) + 2 * 0 + 5 = y + 2 := by omega
        rw [hc, hk]
      apply chainLeadsUpTo_step1 hg_mid
      rw [hs_mid]
      exact hr10 (by omega) hy_odd m hm p.1 p.2 hvp hfzp
    · have hm_od : ((y - 4) + 1) % 2 = 1 := by omega
      have hmrg : decide (2 * x ≥ 0 + (y - 4)) = true := decide_eq_true (by omega)
      have hg_mid : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ = true := by
        rw [hy_sub]
        dsimp only [stepGuards]
        rw [if_pos hm_od, hmrg, if_pos rfl]
        simpa only [Nat.add_zero] using hg1
      have hs_mid : stepSegs ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ =
          ⟨false, p.1, p.2, y, 1, 0, (x - 1) :: S⟩ := by
        rw [hy_sub]
        dsimp only [stepSegs]
        rw [if_pos hm_od, hmrg, if_pos rfl]
        have hc : 0 + (y - 4) + 2 * 0 + 4 = y := by omega
        have hx0 : x - 1 + 0 = x - 1 := by omega
        rw [hc, hx0]
      apply chainLeadsUpTo_step1 hg_mid
      rw [hs_mid]
      exact hr11 (by omega) (by omega) m hm p.1 p.2 hvp hfzp

theorem isBounce_r9 {x y : Nat} {p1 : List (Nat × Nat)} {p2 : Nat} {S : List Nat}
    (hx : 19 ≤ x) (hbig : 2 * x + 5 ≤ y) (hvp : ValidSegs40 p1 p2) :
    IsBounce (x - 1) S ⟨true, (0, y - 3) :: p1, p2, x - 1, 0, 2 * x, S⟩ := by
  have hy_sub : y - 3 = (y - 4) + 1 := by omega
  rw [hy_sub]
  have h := IsBounce.cons (z0 := 0) (m := y - 4) (zl := p2) (cp1 := x - 1) (kb := 0)
    (mrg := 2 * x) (rest := p1) (ds := S) hvp (by omega)
      (by split_ifs <;> omega)
  simpa only [Nat.add_zero] using h

-- ============================================================================
-- Main Fuel-Indexed Excursion Bundle (`FBound N ∧ LoopBound N`)
-- ============================================================================

def FBound (N : Nat) : Prop :=
  ∀ ms S segs zl c k,
    19 ≤ ms → SafeStack ms S →
    ValidTail40 segs zl →
    1 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
    35 ≤ fzOf segs zl →
    42 ≤ c + fzOf segs zl →
    73 ≤ k + 2 * fzOf segs zl →
    ms + 2 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) →
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, S⟩
      (Exit (ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
        (odw (k + 2 * fzOf segs zl) (c + fzOf segs zl))
        (oxw (k + 2 * fzOf segs zl) (c + fzOf segs zl)) S)

def LoopBound (N : Nat) : Prop :=
  ∀ ms S segs zl c k x tx txw,
    19 ≤ ms → SafeStack ms S →
    (S ≠ [1] ∨ 5 ≤ c) →
    ValidSegs40 segs zl →
    2 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
    ms + 2 ≤ tx → tx ≤ x →
    30 * tx ≤ (c + fzOf segs zl) + 27 * x + 900 →
    60 * tx + 120 ≤ 2 * (c + fzOf segs zl) + 55 * x →
    10 * txw + 40 ≤ 9 * (c + fzOf segs zl) + 10 * x →
    20 * txw ≤ (c + fzOf segs zl) + 20 * x + 800 →
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: S⟩
      (Exit tx (tx - 1) txw S)

theorem excursion_bundle (N : Nat) : FBound N ∧ LoopBound N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have hFB : FBound N := by
      intro ms S segs zl c k hms19 hS hvt hc hk1 hkc hfz35 hcz42 hkz73 hms_ox
      obtain ⟨hox39, hox_cz3⟩ := ox_bounds_relaxed hc hk1 hkc hfz35 hcz42 hkz73
      rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
      · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73 hms_ox hox39 hox_cz3 ⊢
        have hg : stepGuards ⟨false, [], zl, c, k, 0, S⟩ = true := by
          dsimp only [stepGuards]
          rw [goodPhiW_of_ge35 hS.1 (by omega), Bool.true_and]
          dsimp only [GoodPsi]
          have hcz : c + zl - 1 + 1 = c + zl := by omega
          rw [hcz]; exact hS.2.2 (c + zl) (by omega)
        apply chainLeadsUpTo_step1 hg
        dsimp only [stepSegs]
        apply chainLeadsUpTo_here
        obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * zl)
        refine Or.inr ⟨c + zl, k + 2 * zl + 2, by omega, by omega, ?_, ?_⟩
        · dsimp only [oxw]; rw [hdw]; omega
        · simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
            (mrg := 2 * (k + 2 * zl) + 6) (ds := (c + zl) :: S) (by omega)
      · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73 hms_ox hox39 hox_cz3 ⊢
        have hv_rest : ValidSegs40 rest zl := hvt
        cases m0 with
        | zero =>
          have hg1 : stepGuards ⟨false, (z0, 0) :: rest, zl, c, k, 0, S⟩ = true := rfl
          apply chainLeadsUpTo_step hg1
          intro m1 hm1
          dsimp only [stepSegs]
          rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
          · have hzl230 : 230 ≤ zl := hv_rest.2
            exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + zl, by dsimp only [odw]; omega,
              IsBounce.nil (by omega)⟩)
          · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
            have hv_rest2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
            have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_rest2
            cases m1_seg with
            | zero =>
              have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 +
                3, 2 * (c + z0) + 8, S⟩ = true := by
                dsimp only [stepGuards]; exact decide_eq_true (by omega)
              apply chainLeadsUpTo_step hg2
              intro m2 hm2
              dsimp only [stepSegs]
              have hmono := arith_fb_t0 hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40
              exact chainLeadsUpTo_imp
                ((ih m2 (by omega)).1 ms S rest2 zl (c + z0 + 3 + z1 + 1) (k + 2 * z0 + 3 + 2 * z1 +
                  3)
                  hms19 hS (validTail40_of_validSegs40 hv_rest2)
                  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  (Nat.le_trans hms_ox hmono.1))
                (fun s' he => exit_mono he hmono.1 hmono.2.1 hmono.2.2)
            | succ m1' =>
              rcases dec_or ((m1' + 1) % 2 = 1) with hm1_odd | hm1_even
              · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
                | true =>
                  have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3, k + 2 * z0 +
                    3, 2 * (c + z0) + 8, S⟩ = true := by
                    dsimp only [stepGuards]
                    rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
                    exact hS.2.2 (c + z0 + 3 + z1) (by omega)
                  apply chainLeadsUpTo_step hg2
                  intro m2 hm2
                  dsimp only [stepSegs]
                  rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
                  have hi := arith_fb_to (m1' := m1') hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40
                  exact (ih m2 (by omega)).2 ms S rest2 zl
                    ((k + 2 * z0 + 3) + m1' + 2 * z1 + 4) 1 (c + z0 + 3 + z1)
                    (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
                    hms19 hS (Or.inr (by omega)) hv_rest2
                    (by omega) (by omega) (by omega) hms_ox hi.1
                    hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
                | false =>
                  have h_nm : ¬(2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') :=
                    of_decide_eq_false hd_mrg
                  exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by dsimp only [odw]; omega,
                    IsBounce.cons hv_rest2 (by omega) (by rw [if_pos hm1_odd]; omega)⟩)
              · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
                | true =>
                  have h_mrg : 2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1) :=
                    of_decide_eq_true hd_mrg
                  have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3, k + 2 * z0 +
                    3, 2 * (c + z0) + 8, S⟩ = true := by
                    dsimp only [stepGuards]
                    rw [if_neg hm1_even, hd_mrg, if_pos rfl]
                  apply chainLeadsUpTo_step hg2
                  intro m2 hm2
                  dsimp only [stepSegs]
                  rw [if_neg hm1_even, hd_mrg, if_pos rfl]
                  have hmono := arith_fb_te hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40 h_mrg
                  exact chainLeadsUpTo_imp
                    ((ih m2 (by omega)).1 ms S rest2 zl (c + z0 + 3 + z1 + 2) ((k + 2 * z0 + 3) +
                      (m1' + 1) + 2 * z1 + 5)
                      hms19 hS (validTail40_of_validSegs40 hv_rest2)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      (Nat.le_trans hms_ox hmono.1))
                    (fun s' he => exit_mono he hmono.1 hmono.2.1 hmono.2.2)
                | false =>
                  have h_nm : ¬(2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) :=
                    of_decide_eq_false hd_mrg
                  exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by dsimp only [odw]; omega,
                    IsBounce.cons hv_rest2 (by omega) (by rw [if_neg hm1_even]; omega)⟩)
        | succ m' =>
          have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
          have hphiw : GoodPhiW (c + z0 - 1) S false = true := goodPhiW_of_ge35 hS.1 (by omega)
          rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
          · have hm0_eq : m' = 0 := by omega
            subst hm0_eq
            have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, S⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) S false && if 1 = 1 then GoodPsi (c + z0) S else _) =
                true
              rw [hphiw, Bool.true_and, if_pos rfl]
              exact hS.2.2 (c + z0 + 1) (by omega)
            apply chainLeadsUpTo_step hg
            intro m1 hm1
            dsimp only [stepSegs]
            change ChainLeadsUpTo m1 (if 1 = 1 then _ else _) _
            rw [if_pos rfl]
            have hi := arith_fb_m1_ev (dx := 1) hc hk1 hkc hfz35 hcz42 hkz73 hfz1_40 (by decide)
            exact (ih m1 hm1).2 ms S rest zl (k + 2 * z0 + 4) 1 (c + z0 + 1)
              (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
              hms19 hS (Or.inr (by omega)) hv_rest
              (by omega) (by omega) (by omega) hms_ox hi.1
              hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
          · have hpsi_cz : GoodPsi (c + z0 - 1) S = true := by
              dsimp only [GoodPsi]
              have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
              rw [hcz_eq]; exact hS.2.2 (c + z0) (by omega)
            rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) S false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
              apply chainLeadsUpTo_step hg
              intro m1 hm1
              dsimp only [stepSegs]
              change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
              rw [if_neg hm_gt1, if_pos hev_sm]
              have hi := arith_fb_m1_ev (dx := 0) hc hk1 hkc hfz35 hcz42 hkz73 hfz1_40 (by decide)
              have hcz0 : c + z0 + 0 = c + z0 := by omega
              rw [hcz0] at hi
              exact (ih m1 hm1).2 ms S rest zl (k + 2 * z0 + 4) (m' + 2) (c + z0)
                (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
                hms19 hS (Or.inr (by omega)) hv_rest
                (by omega) (by omega) (by omega) hms_ox hi.1
                hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
            · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
              · have hS_cz : SafeStack 39 ((c + z0) :: S) := safeStack_cons hS (by omega) (by omega)
                have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                  dsimp only [stepGuards]
                  change (GoodPhiW (c + z0 - 1) S false &&
                    if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                      if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                      if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                        GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: S) else true) = true
                  rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                    if_neg hnot_ev, if_pos hod_sm]
                  exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
                apply chainLeadsUpTo_step hg
                intro m1 hm1
                dsimp only [stepSegs]
                change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
                rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
                obtain ⟨q10, r10, hr10, hkz10, hdw10⟩ := div10_spec (k + 2 * z0)
                have hos_in : 39 + 2 ≤ 9 * q10 - 2 ∧ 9 * q10 - 2 ≤ k + 2 * z0 + 2 ∧
                    30 * (9 * q10 - 2) ≤ (m' + fzOf rest zl) + 27 * (k + 2 * z0 + 2) + 900 ∧
                    60 * (9 * q10 - 2) + 120 ≤ 2 * (m' + fzOf rest zl) + 55 * (k + 2 * z0 + 2) ∧
                    10 * (k + 2 * z0 + 35) + 40 ≤ 9 * (m' + fzOf rest zl) + 10 * (k + 2 * z0 + 2) ∧
                    20 * (k + 2 * z0 + 35) ≤ (m' + fzOf rest zl) + 20 * (k + 2 * z0 + 2) + 800 := by
                      omega
                have hm_sub : m' + 1 - 1 = m' := by omega
                rw [hm_sub]
                have hne1_cz : ((c + z0) :: S) ≠ [1] := by intro h; injection h with h1; omega
                have h_loop1 := (ih m1 hm1).2 39 ((c + z0) :: S) rest zl m' 1
                  (k + 2 * z0 + 2) (9 * q10 - 2) (k + 2 * z0 + 35)
                  (by decide) hS_cz (Or.inl hne1_cz) hv_rest
                  (by omega) (by omega) (by omega) hos_in.1 hos_in.2.1
                  hos_in.2.2.1 hos_in.2.2.2.1 hos_in.2.2.2.2.1 hos_in.2.2.2.2.2
                refine chainLeadsUpTo_trans h_loop1 ?_
                intro m2 s_mid hm2 hexit1
                rcases hexit1 with ⟨phi1, hphi1, hb1⟩ | ⟨y1, phi1, hy1_tx1, hphi1_38, hyw1, hb1⟩
                · apply chainLeadsUpTo_here
                  obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * z0)
                  refine Or.inr ⟨c + z0, phi1, by omega, by omega, ?_, hb1⟩
                  dsimp only [oxw]; rw [hdw]; omega
                · exact amega_pop_step hb1 hphi1_38 (by omega) (by omega)
                    (hS.2.2 (c + z0 - 1) (by omega))
                    (fun _ => hS.2.2 (c + z0 - 2) (by omega))
                    (fun hbig _ _ p1 p2 hvp _ =>
                      chainLeadsUpTo_here (Or.inl ⟨c + z0 - 1, by dsimp only [odw]; omega,
                        isBounce_r9 (by omega) hbig hvp⟩))
                    (fun hy1_le _ m3 hm3 p1 p2 hvp hfzp => by
                      have hy1_lo : 9 * ((k + 2 * z0) / 10) - 2 ≤ y1 := by rw [hdw10]; exact hy1_tx1
                      have hmono :=
                        arith_fb_os_r10 hc hk1 hkc hfz35 hcz42 hkz73 hy1_lo hy1_le hphi1_38 hyw1
                        hfzp
                      exact chainLeadsUpTo_imp
                        ((ih m3 (by omega)).1 ms S p1 p2 (c + z0 + 1) (y1 + 2) hms19 hS
                          (validTail40_of_validSegs40 hvp)
                          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                          (Nat.le_trans hms_ox hmono.1))
                        (fun s' he => exit_mono he hmono.1 hmono.2.1 hmono.2.2))
                    (fun hy1_le _ m3 hm3 p1 p2 hvp hfzp => by
                      have hi := arith_fb_os_r11 hc hk1 hkc hfz35 hcz42 hkz73 hyw1 hfzp
                      exact (ih m3 (by omega)).2 ms S p1 p2 y1 1 (c + z0 - 1)
                        (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
                        hms19 hS (Or.inr (by omega)) hvp
                        (by omega) (by omega) (by omega) hms_ox hi.1
                        hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2)
              · have hm0_big : 2 * (k + 2 * z0) + 12 ≤ m' + 1 := by omega
                have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                  dsimp only [stepGuards]
                  change (GoodPhiW (c + z0 - 1) S false &&
                    if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                      if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                      if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                  rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                    if_neg hnot_ev, if_neg hbig_m]
                apply chainLeadsUpTo_step1 hg
                dsimp only [stepSegs]
                change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
                rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
                have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                  dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
                rw [hnorm]
                apply chainLeadsUpTo_here
                obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * z0)
                refine Or.inr ⟨c + z0, k + 2 * z0 + 2, by omega, by omega, ?_, ?_⟩
                · dsimp only [oxw]; rw [hdw]; omega
                · have hbc := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                    (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                    (rest := rest) (ds := (c + z0) :: S) hv_rest (by omega)
                      (by split_ifs <;> omega)
                  simpa only [Nat.add_zero] using hbc
    have hLB : LoopBound N := by
      intro ms S segs zl c k x tx txw hms19 hS hSc5 hv hc hk1 hkc hms_tx htx_x hi1 hi2 hi3 hi4
      have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
      have hox39 : 39 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) :=
        (ox_bounds_relaxed (by omega) hk1 hkc (by omega) (by omega) (by omega)).1
      have hfb : ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: S⟩
          (Exit (ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
            (odw (k + 2 * fzOf segs zl) (c + fzOf segs zl))
            (oxw (k + 2 * fzOf segs zl) (c + fzOf segs zl)) (x :: S)) := by
        rcases hSc5 with hne1 | hc5
        · exact hFB 19 (x :: S) segs zl c k (by decide)
            (safeStack_cons_ne1 hne1 hS (by omega) (by omega))
            (validTail40_of_validSegs40 hv)
            (by omega) hk1 hkc (by omega) (by omega) (by omega) (by omega)
        · have hox41 := ox_ge41_of_c5 hc5 hk1 hkc hfz40
          exact hFB 39 (x :: S) segs zl c k (by decide)
            (safeStack_cons hS (by omega) (by omega))
            (validTail40_of_validSegs40 hv)
            (by omega) hk1 hkc (by omega) (by omega) (by omega) hox41
      refine chainLeadsUpTo_trans hfb ?_
      intro m1 s_mid hm1 hexit
      rcases hexit with ⟨phi, hphi_odw, hb⟩ | ⟨y, phi, hy_ox, hphi38, hyw, hb⟩
      · apply chainLeadsUpTo_here
        obtain ⟨q, r, hr, heq, hox⟩ :=
          ox_spec_lt (kz := k + 2 * fzOf segs zl) (cz := c + fzOf segs zl) (by omega)
        dsimp only [odw] at hphi_odw
        rw [hox] at hphi_odw hox39
        exact Or.inr ⟨x, phi, htx_x, by omega, by omega, hb⟩
      · exact amega_pop_step hb hphi38 (by omega) (by omega)
          (hS.2.2 (x - 1) (by omega)) (fun _ => hS.2.2 (x - 2) (by omega))
          (fun hbig _ _ p1 p2 hvp _ =>
            chainLeadsUpTo_here (Or.inl ⟨x - 1, by omega, isBounce_r9 (by omega) hbig hvp⟩))
          (fun hy_le _ m2 hm2 p1 p2 hvp hfzp => by
            have hmono := arith_lb_r10 hc hk1 hkc hfz40 (by omega) htx_x
              hi1 hi2 hi3 hi4 hy_ox hy_le hphi38 hyw hfzp
            exact chainLeadsUpTo_imp
              ((ih m2 (by omega)).1 ms S p1 p2 (x + 1) (y + 2) hms19 hS
                (validTail40_of_validSegs40 hvp)
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                (Nat.le_trans hms_tx hmono.1))
              (fun s' he => exit_mono he hmono.1 hmono.2.1 hmono.2.2))
          (fun hy_le _ m2 hm2 p1 p2 hvp hfzp => by
            have hr11 := arith_lb_r11 hc hk1 hkc hfz40 (by omega) htx_x
              hi1 hi2 hi3 hi4 hy_ox hy_le hphi38 hyw hfzp
            exact (ih m2 (by omega)).2 ms S p1 p2 y 1 (x - 1) tx txw
              hms19 hS (Or.inr hr11.1) hvp
              (by omega) (by omega) (by omega) hms_tx hr11.2.1
              hr11.2.2.1 hr11.2.2.2.1 hr11.2.2.2.2.1 hr11.2.2.2.2.2)
    exact ⟨hFB, hLB⟩


-- ============================================================================
-- Section 5g.3a: SafeStack Bases & High-Excursion Bundle (`FHigh`, `LoopHigh`, `LoopOS`)
-- ============================================================================

theorem safeStack_nil : SafeStack 19 [] := by
  refine ⟨(by intro h; cases h), rfl, ?_⟩
  intro u hu
  dsimp only [GoodDs, GoodDsAux, GoodDs1]
  exact decide_eq_true (by omega)

theorem safeStack_zero : SafeStack 19 [0] := by
  refine ⟨(by intro h; injection h with h1; omega), rfl, ?_⟩
  intro u hu
  dsimp only [GoodDs, GoodDsAux, GoodDs2]
  rw [if_pos rfl]
  exact decide_eq_true (by omega)

theorem safeStack_one : SafeStack 25 [1] := by
  refine ⟨(by intro h; injection h with h1; omega), rfl, ?_⟩
  intro u hu
  dsimp only [GoodDs, GoodDsAux, GoodDs2]
  rw [if_neg (by decide), if_pos rfl]
  exact decide_eq_true (by omega)

theorem safeStack_31 : SafeStack 19 [3, 1] := by
  refine ⟨(by intro h; injection h with _ h2; cases h2), rfl, ?_⟩
  intro u hu
  dsimp only [GoodDs]
  rw [GoodDsAux.eq_3, if_neg (by decide)]
  have h1 : decide (3 = 3 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ u < 19) = false :=
    decide_eq_false (by omega)
  have h2 : isOddDrainDs [3, 1] = false := rfl
  have h3 : decide (3 ≥ 25 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ u < 39) = false := rfl
  have h4 : decide (u < 17) = false := decide_eq_false (by omega)
  have h5 : GoodDsAux 3 [1] = true := rfl
  have h6 : decide (u % 2 = 0 ∧ u ≤ 2 * 3 + 4) = false := decide_eq_false (by omega)
  have h7 : decide (u % 2 = 0 ∧ u + 14 ≤ 2 * 3) = false := decide_eq_false (by omega)
  rw [h1, h2, h3, h4, h5, h6, h7]
  simp only [Bool.false_and, Bool.not_true, Bool.or_false,
    Bool.false_eq_true, ite_false]

theorem safeStack_x_31 {x : Nat} (hx20 : 20 ≤ x) (hx22 : x ≤ 22) :
    SafeStack 39 [x, 3, 1] := by
  have hgx : GoodDs [x, 3, 1] = true := safeStack_31.2.2 x (by omega)
  have hgx1 : GoodDs [x - 1, 3, 1] = true := safeStack_31.2.2 (x - 1) (by omega)
  refine ⟨(by intro h; injection h with _ h2; cases h2), hgx, ?_⟩
  intro u hu
  dsimp only [GoodDs]
  rw [GoodDsAux.eq_3, if_neg (by omega)]
  have h1 : decide (x = 3 ∧ 3 = 1 ∧ [1] = [] ∧ u < 19) = false := decide_eq_false (by omega)
  have h2 : isOddDrainDs [x, 3, 1] = false := rfl
  have h3 : decide (x ≥ 25 ∧ 3 = 1 ∧ [1] = [] ∧ u < 39) = false := decide_eq_false (by omega)
  have h4 : decide (u < 17) = false := decide_eq_false (by omega)
  have h7 : decide (u % 2 = 0 ∧ u + 14 ≤ 2 * x) = false := decide_eq_false (by omega)
  have hgx' : GoodDsAux x [3, 1] = true := hgx
  have hgx1' : GoodDsAux (x - 1) [3, 1] = true := hgx1
  rw [h1, h2, h3, h4, hgx', hgx1', h7]
  simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
    Bool.false_eq_true, ite_false]

theorem safeStack_d {d : Nat} (hd8 : 8 ≤ d) : SafeStack 21 [d] := by
  refine ⟨(by intro h; injection h with h1; omega), ?_, ?_⟩
  · dsimp only [GoodDs, GoodDsAux, GoodDs1]; exact decide_eq_true (by omega)
  · intro u hu
    dsimp only [GoodDs, GoodDsAux, GoodDs2]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hu19 : decide (u < 19) = false := decide_eq_false (by omega)
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hgd : GoodDs1 d = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hc1 : (decide (u % 2 = 0 ∧ u ≤ 2 * d + 4) && !GoodDs1 (d - 1)) = false := by
      rcases dec_or (d = 8) with rfl | hd9
      · rw [decide_eq_false (by omega), Bool.false_and]
      · have hg1 : GoodDs1 (d - 1) = true := by
          dsimp only [GoodDs1]; exact decide_eq_true (by omega)
        rw [hg1, Bool.not_true, Bool.and_false]
    have hc2 : (decide (u % 2 = 0 ∧ u + 14 ≤ 2 * d) && !GoodDs1 (d - 2)) = false := by
      rcases dec_or (d ≤ 9) with hd9 | hd10
      · rw [decide_eq_false (by omega), Bool.false_and]
      · have hg2 : GoodDs1 (d - 2) = true := by
          dsimp only [GoodDs1]; exact decide_eq_true (by omega)
        rw [hg2, Bool.not_true, Bool.and_false]
    rw [hu19, hu17, hgd, hc1, hc2]
    simp only [Bool.and_false, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]

theorem safeStack_d0 {d : Nat} (hd8 : 8 ≤ d) : SafeStack 21 [d, 0] := by
  refine ⟨(by intro h; injection h with _ h2; cases h2), ?_, ?_⟩
  · dsimp only [GoodDs, GoodDsAux, GoodDs2]; rw [if_pos rfl]; exact decide_eq_true (by omega)
  · intro u hu
    dsimp only [GoodDs]
    rw [GoodDsAux.eq_3, if_neg (by omega)]
    have h1 : decide (d = 3 ∧ 0 = 1 ∧ ([] : List Nat) = [] ∧ u < 19) = false :=
      decide_eq_false (by omega)
    have hu19 : decide (u < 19) = false := decide_eq_false (by omega)
    have h3 : decide (d ≥ 25 ∧ 0 = 1 ∧ ([] : List Nat) = [] ∧ u < 39) = false :=
      decide_eq_false (by omega)
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hgd : GoodDsAux d [0] = true := by
      dsimp only [GoodDsAux, GoodDs2]; rw [if_pos rfl]; exact decide_eq_true (by omega)
    have hc1 : (decide (u % 2 = 0 ∧ u ≤ 2 * d + 4) && !GoodDsAux (d - 1) [0]) = false := by
      rcases dec_or (d = 8) with rfl | hd9
      · rw [decide_eq_false (by omega), Bool.false_and]
      · have hg1 : GoodDsAux (d - 1) [0] = true := by
          dsimp only [GoodDsAux, GoodDs2]; rw [if_pos rfl]; exact decide_eq_true (by omega)
        rw [hg1, Bool.not_true, Bool.and_false]
    have hc2 : (decide (u % 2 = 0 ∧ u + 14 ≤ 2 * d) && !GoodDsAux (d - 2) [0]) = false := by
      rcases dec_or (d ≤ 9) with hd9 | hd10
      · rw [decide_eq_false (by omega), Bool.false_and]
      · have hg2 : GoodDsAux (d - 2) [0] = true := by
          dsimp only [GoodDsAux, GoodDs2]; rw [if_pos rfl]; exact decide_eq_true (by omega)
        rw [hg2, Bool.not_true, Bool.and_false]
    rw [h1, hu19, h3, hu17, hgd, hc1, hc2]
    simp only [Bool.and_false, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]

theorem safeStack_d1 {d : Nat} (hd26 : 26 ≤ d) : SafeStack 39 [d, 1] := by
  refine ⟨(by intro h; injection h with _ h2; cases h2), safeStack_one.2.2 d (by omega), ?_⟩
  intro u hu
  dsimp only [GoodDs]
  rw [GoodDsAux.eq_3, if_neg (by omega)]
  have h1 : decide (d = 3 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ u < 19) = false :=
    decide_eq_false (by omega)
  have h2 : isOddDrainDs [d, 1] = false := rfl
  have h3 : decide (d ≥ 25 ∧ 1 = 1 ∧ ([] : List Nat) = [] ∧ u < 39) = false :=
    decide_eq_false (by omega)
  have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
  have hgd : GoodDsAux d [1] = true := safeStack_one.2.2 d (by omega)
  have hg1 : GoodDsAux (d - 1) [1] = true := safeStack_one.2.2 (d - 1) (by omega)
  have hc2 : (decide (u % 2 = 0 ∧ u + 14 ≤ 2 * d) && !GoodDsAux (d - 2) [1]) = false := by
    rcases dec_or (d = 26) with rfl | hd27
    · rw [decide_eq_false (by omega), Bool.false_and]
    · have hg2 : GoodDsAux (d - 2) [1] = true := safeStack_one.2.2 (d - 2) (by omega)
      rw [hg2, Bool.not_true, Bool.and_false]
  rw [h1, h2, h3, hu17, hgd, hg1, hc2]
  simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
    Bool.false_eq_true, ite_false]

theorem safeStack_of_gt2d2 {m d2 d3 : Nat} {ds3 : List Nat}
    (_hm39 : 39 ≤ m) (hm_gt : 2 * d2 + 5 ≤ m) (hd2 : 17 ≤ d2)
    (hg : GoodDs (d2 :: d3 :: ds3) = true) :
    SafeStack m (d2 :: d3 :: ds3) := by
  refine ⟨(by intro h; injection h with _ h2; cases h2), hg, ?_⟩
  intro u hu
  dsimp only [GoodDs]
  rw [GoodDsAux.eq_3, if_neg (by omega)]
  have h1 : decide (d2 = 3 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 19) = false := decide_eq_false (by omega)
  have hu19 : decide (u < 19) = false := decide_eq_false (by omega)
  have h3 : decide (d2 ≥ 25 ∧ d3 = 1 ∧ ds3 = [] ∧ u < 39) = false := decide_eq_false (by omega)
  have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
  have hg0 : GoodDsAux d2 (d3 :: ds3) = true := hg
  have hc1 : decide (u % 2 = 0 ∧ u ≤ 2 * d2 + 4) = false := decide_eq_false (by omega)
  have hc2 : decide (u % 2 = 0 ∧ u + 14 ≤ 2 * d2) = false := decide_eq_false (by omega)
  rw [h1, hu19, h3, hu17, hg0, hc1, hc2]
  simp only [Bool.and_false, Bool.false_and, Bool.not_true, Bool.or_false,
    Bool.false_eq_true, ite_false]

theorem safeStack_25_1 : SafeStack 55 [25, 1] :=
  safeStack_of_gt2d2 (by decide) (by decide) (by decide) rfl

theorem safeStack_17_8_0 : SafeStack 39 [17, 8, 0] :=
  safeStack_of_gt2d2 (by decide) (by decide) (by decide) rfl

theorem safeStack_20_3_1 : SafeStack 27 [20, 3, 1] := by
  refine ⟨(by intro h; injection h with _ h2; cases h2), rfl, ?_⟩
  intro u hu
  dsimp only [GoodDs]
  rw [GoodDsAux.eq_3, if_neg (by decide)]
  have h1 : decide (20 = 3 ∧ 3 = 1 ∧ [1] = [] ∧ u < 19) = false := rfl
  have h2 : isOddDrainDs [20, 3, 1] = false := rfl
  have h3 : decide (20 ≥ 25 ∧ 3 = 1 ∧ [1] = [] ∧ u < 39) = false := rfl
  have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
  have hg0 : GoodDsAux 20 [3, 1] = true := rfl
  have hg1 : GoodDsAux 19 [3, 1] = true := rfl
  have hc2 : decide (u % 2 = 0 ∧ u + 14 ≤ 2 * 20) = false := decide_eq_false (by omega)
  rw [h1, h2, h3, hu17, hg0, hg1, hc2]
  simp only [Bool.false_and, Bool.not_true, Bool.or_false, Bool.and_false,
    Bool.false_eq_true, ite_false]

theorem safeStack_19_9 : SafeStack 43 [19, 9] :=
  safeStack_of_gt2d2 (by decide) (by decide) (by decide) rfl

theorem safeStack_19_9_0 : SafeStack 43 [19, 9, 0] :=
  safeStack_of_gt2d2 (by decide) (by decide) (by decide) rfl

theorem safeStack_47_25_1 : SafeStack 99 [47, 25, 1] :=
  safeStack_of_gt2d2 (by decide) (by decide) (by decide) rfl

-- ============================================================================
-- High-Excursion Arithmetic Lemmas & Bundle (`FHigh`, `LoopHigh`, `LoopOS`)
-- ============================================================================

def ExitHigh (S : List Nat) (s : SegState) : Prop :=
  (∃ phi, 48 ≤ phi ∧ IsBounce phi S s) ∨
  (∃ y phi, 49 ≤ y ∧ ((53 ≤ y ∧ 90 ≤ phi) ∨ 100 ≤ phi) ∧ IsBounce phi (y :: S) s)

theorem arith_lh_bounds {c k fz : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz) (_hcz : 131 ≤ c + fz) :
    119 ≤ ox (k + 2 * fz) (c + fz) ∧ 118 ≤ odw (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  dsimp only [odw]
  omega

theorem arith_los_r11 {c k fz x y phi fz3 : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz)
    (_hx : 91 ≤ x) (_hpot : 2220 ≤ (c + fz) + 22 * x)
    (_hy_lo : ox (k + 2 * fz) (c + fz) ≤ y) (_hy_hi : y ≤ 2 * x + 4)
    (_hphi38 : 38 ≤ phi) (_hyw : oxw (k + 2 * fz) (c + fz) ≤ y + phi)
    (_hfz3 : phi + 2 ≤ fz3) :
    39 ≤ y ∧ 91 ≤ x - 1 ∧ 2220 ≤ (y + fz3) + 22 * (x - 1) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * fz)
  dsimp only [oxw] at _hyw
  rw [hdw] at _hyw
  rw [hox] at _hy_lo
  omega

def FHigh (N : Nat) : Prop :=
  ∀ S segs zl c k,
    S ≠ [1] → SafeStack 43 S →
    ValidSegs40 segs zl →
    2 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
    53 ≤ c + fzOf segs zl →
    97 ≤ k + 2 * fzOf segs zl →
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, S⟩ (ExitHigh S)

def LoopHigh (N : Nat) : Prop :=
  ∀ S segs zl c k x,
    S ≠ [1] → SafeStack 43 S →
    ValidSegs40 segs zl →
    2 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
    49 ≤ x →
    131 ≤ c + fzOf segs zl →
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: S⟩ (ExitHigh S)

def LoopOS (N : Nat) : Prop :=
  ∀ S segs zl c k x cz_out,
    S ≠ [1] → SafeStack 43 S →
    ValidSegs40 segs zl →
    2 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
    53 ≤ cz_out →
    91 ≤ x →
    2220 ≤ (c + fzOf segs zl) + 22 * x →
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: cz_out :: S⟩ (ExitHigh S)

theorem fhigh_bundle (N : Nat) : FHigh N ∧ LoopHigh N ∧ LoopOS N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have hFH : FHigh N := by
      intro S segs zl c k hne1 hS hv hc hk1 hkc hcz53 hkz99
      rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
      · dsimp only [fzOf] at hcz53 hkz99
        have hzl230 : 230 ≤ zl := hv.2
        have hg : stepGuards ⟨false, [], zl, c, k, 0, S⟩ = true := by
          dsimp only [stepGuards]
          rw [goodPhiW_of_ge35 hS.1 (by omega), Bool.true_and]
          dsimp only [GoodPsi]
          have hcz : c + zl - 1 + 1 = c + zl := by omega
          rw [hcz]; exact hS.2.2 (c + zl) (by omega)
        apply chainLeadsUpTo_step1 hg
        dsimp only [stepSegs]
        apply chainLeadsUpTo_here
        refine Or.inr ⟨c + zl, k + 2 * zl + 2, by omega, Or.inr (by omega), ?_⟩
        simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
          (mrg := 2 * (k + 2 * zl) + 6) (ds := (c + zl) :: S) (by omega)
      · have hz0_40 : 40 ≤ z0 := fzOf_ge_40 hv
        have hv_rest : ValidSegs40 rest zl := validSegs40_tail hv
        dsimp only [fzOf] at hcz53 hkz99
        cases m0 with
        | zero =>
          have hg1 : stepGuards ⟨false, (z0, 0) :: rest, zl, c, k, 0, S⟩ = true := rfl
          apply chainLeadsUpTo_step hg1
          intro m1 hm1
          dsimp only [stepSegs]
          rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
          · have hzl230 : 230 ≤ zl := hv_rest.2
            exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + zl, by omega, IsBounce.nil (by omega)⟩)
          · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
            have hv_rest2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
            have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_rest2
            cases m1_seg with
            | zero =>
              have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 +
                3, 2 * (c + z0) + 8, S⟩ = true := by
                dsimp only [stepGuards]; exact decide_eq_true (by omega)
              apply chainLeadsUpTo_step hg2
              intro m2 hm2
              dsimp only [stepSegs]
              exact (ih m2 (by omega)).1 S rest2 zl (c + z0 + 3 + z1 + 1) (k + 2 * z0 + 3 + 2 * z1 +
                3)
                hne1 hS hv_rest2 (by omega) (by omega) (by omega) (by omega) (by omega)
            | succ m1' =>
              rcases dec_or ((m1' + 1) % 2 = 1) with hm1_odd | hm1_even
              · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
                | true =>
                  have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3, k + 2 * z0 +
                    3, 2 * (c + z0) + 8, S⟩ = true := by
                    dsimp only [stepGuards]
                    rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
                    exact hS.2.2 (c + z0 + 3 + z1) (by omega)
                  apply chainLeadsUpTo_step hg2
                  intro m2 hm2
                  dsimp only [stepSegs]
                  rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
                  exact (ih m2 (by omega)).2.1 S rest2 zl ((k + 2 * z0 + 3) + m1' + 2 * z1 + 4) 1
                    (c + z0 + 3 + z1) hne1 hS hv_rest2
                    (by omega) (by omega) (by omega) (by omega) (by omega)
                | false =>
                  have h_nm : ¬(2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') :=
                    of_decide_eq_false hd_mrg
                  exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by omega,
                    IsBounce.cons hv_rest2 (by omega) (by rw [if_pos hm1_odd]; omega)⟩)
              · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
                | true =>
                  have h_mrg : 2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1) :=
                    of_decide_eq_true hd_mrg
                  have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3, k + 2 * z0 +
                    3, 2 * (c + z0) + 8, S⟩ = true := by
                    dsimp only [stepGuards]
                    rw [if_neg hm1_even, hd_mrg, if_pos rfl]
                  apply chainLeadsUpTo_step hg2
                  intro m2 hm2
                  dsimp only [stepSegs]
                  rw [if_neg hm1_even, hd_mrg, if_pos rfl]
                  exact (ih m2 (by omega)).1 S rest2 zl (c + z0 + 3 + z1 + 2)
                    ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5)
                    hne1 hS hv_rest2 (by omega) (by omega) (by omega) (by omega) (by omega)
                | false =>
                  have h_nm : ¬(2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) :=
                    of_decide_eq_false hd_mrg
                  exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by omega,
                    IsBounce.cons hv_rest2 (by omega) (by rw [if_neg hm1_even]; omega)⟩)
        | succ m' =>
          have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
          have hphiw : GoodPhiW (c + z0 - 1) S false = true := goodPhiW_of_ge35 hS.1 (by omega)
          rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
          · have hm0_eq : m' = 0 := by omega
            subst hm0_eq
            have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, S⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) S false && if 1 = 1 then GoodPsi (c + z0) S else _) =
                true
              rw [hphiw, Bool.true_and, if_pos rfl]
              exact hS.2.2 (c + z0 + 1) (by omega)
            apply chainLeadsUpTo_step hg
            intro m1 hm1
            dsimp only [stepSegs]
            change ChainLeadsUpTo m1 (if 1 = 1 then _ else _) _
            rw [if_pos rfl]
            exact (ih m1 hm1).2.1 S rest zl (k + 2 * z0 + 4) 1 (c + z0 + 1)
              hne1 hS hv_rest (by omega) (by omega) (by omega) (by omega) (by omega)
          · have hpsi_cz : GoodPsi (c + z0 - 1) S = true := by
              dsimp only [GoodPsi]
              have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
              rw [hcz_eq]; exact hS.2.2 (c + z0) (by omega)
            rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) S false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
              apply chainLeadsUpTo_step hg
              intro m1 hm1
              dsimp only [stepSegs]
              change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
              rw [if_neg hm_gt1, if_pos hev_sm]
              exact (ih m1 hm1).2.1 S rest zl (k + 2 * z0 + 4) (m' + 2) (c + z0)
                hne1 hS hv_rest (by omega) (by omega) (by omega) (by omega) (by omega)
            · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
              · have hS_cz : SafeStack 19 ((c + z0) :: S) :=
                  safeStack_cons_ne1 hne1 hS (by omega) (by omega)
                have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                  dsimp only [stepGuards]
                  change (GoodPhiW (c + z0 - 1) S false &&
                    if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                      if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                      if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                        GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: S) else true) = true
                  rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                    if_neg hnot_ev, if_pos hod_sm]
                  exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
                apply chainLeadsUpTo_step hg
                intro m1 hm1
                dsimp only [stepSegs]
                change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
                rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
                have hm_sub : m' + 1 - 1 = m' := by omega
                rw [hm_sub]
                exact (ih m1 hm1).2.2 S rest zl m' 1 (k + 2 * z0 + 2) (c + z0)
                  hne1 hS hv_rest (by omega) (by omega) (by omega) hcz53 (by omega) (by omega)
              · have hm0_big : 2 * (k + 2 * z0) + 12 ≤ m' + 1 := by omega
                have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
                  dsimp only [stepGuards]
                  change (GoodPhiW (c + z0 - 1) S false &&
                    if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                      if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                      if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                  rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                    if_neg hnot_ev, if_neg hbig_m]
                apply chainLeadsUpTo_step1 hg
                dsimp only [stepSegs]
                change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
                rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
                have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                  dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
                rw [hnorm]
                apply chainLeadsUpTo_here
                refine Or.inr ⟨c + z0, k + 2 * z0 + 2, by omega, Or.inl ⟨hcz53, by omega⟩, ?_⟩
                have hbc := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                  (rest := rest) (ds := (c + z0) :: S) hv_rest (by omega)
                    (by split_ifs <;> omega)
                simpa only [Nat.add_zero] using hbc
    have hLH : LoopHigh N := by
      intro S segs zl c k x hne1 hS hv hc hk1 hkc hx49 hcz135
      have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
      obtain ⟨hox101, hodw100⟩ := arith_lh_bounds hc hk1 hkc hfz40 hcz135
      have hSx : SafeStack 19 (x :: S) := safeStack_cons_ne1 hne1 hS (by omega) (by omega)
      have hfb := (excursion_bundle N).1 19 (x :: S) segs zl c k (by decide) hSx
        (validTail40_of_validSegs40 hv) (by omega) hk1 hkc (by omega) (by omega) (by omega)
          (by omega)
      refine chainLeadsUpTo_trans hfb ?_
      intro m1 s_mid hm1 hexit
      rcases hexit with ⟨phi, hphi_odw, hb⟩ | ⟨y, phi, hy_ox, hphi38, _, hb⟩
      · exact chainLeadsUpTo_here (Or.inr ⟨x, phi, hx49, Or.inr (by omega), hb⟩)
      · exact amega_pop_step hb hphi38 (by omega) (by omega)
          (hS.2.2 (x - 1) (by omega)) (fun _ => hS.2.2 (x - 2) (by omega))
          (fun hbig _ _ p1 p2 hvp _ =>
            chainLeadsUpTo_here (Or.inl ⟨x - 1, by omega, isBounce_r9 (by omega) hbig hvp⟩))
          (fun _ _ m2 hm2 p1 p2 hvp _ => by
            have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
            exact (ih m2 (by omega)).1 S p1 p2 (x + 1) (y + 2) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
          (fun hy_le _ m2 hm2 p1 p2 hvp _ => by
            have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
            exact (ih m2 (by omega)).2.1 S p1 p2 y 1 (x - 1) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
    have hLOS : LoopOS N := by
      intro S segs zl c k x cz_out hne1 hS hv hc hk1 hkc hcz_out hx96 hpot
      have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
      have hox39 : 39 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) :=
        (ox_bounds_relaxed (by omega) hk1 hkc (by omega) (by omega) (by omega)).1
      have hS_cz : SafeStack 19 (cz_out :: S) := safeStack_cons_ne1 hne1 hS (by omega) (by omega)
      have hne1_cz : (cz_out :: S) ≠ [1] := by intro h; injection h with h1; omega
      have hS_xcz : SafeStack 19 (x :: cz_out :: S) :=
        safeStack_cons_ne1 hne1_cz hS_cz (by omega) (by omega)
      have hfb := (excursion_bundle N).1 19 (x :: cz_out :: S) segs zl c k (by decide) hS_xcz
        (validTail40_of_validSegs40 hv) (by omega) hk1 hkc (by omega) (by omega) (by omega)
          (by omega)
      refine chainLeadsUpTo_trans hfb ?_
      intro m1 s_mid hm1 hexit
      rcases hexit with ⟨phi, hphi_odw, hb⟩ | ⟨y, phi, hy_ox, hphi38, hyw, hb⟩
      · have hphi38 : 38 ≤ phi := by
          obtain ⟨q, r, hr, heq, hox⟩ :=
            ox_spec_lt (kz := k + 2 * fzOf segs zl) (cz := c + fzOf segs zl) (by omega)
          dsimp only [odw] at hphi_odw; rw [hox] at hphi_odw hox39; omega
        exact amega_pop_step hb hphi38 (by omega) (by omega)
          (hS.2.2 (cz_out - 1) (by omega)) (fun _ => hS.2.2 (cz_out - 2) (by omega))
          (fun hbig _ _ p1 p2 hvp _ =>
            chainLeadsUpTo_here (Or.inl ⟨cz_out - 1, by omega, isBounce_r9 (by omega) hbig hvp⟩))
          (fun _ _ m2 hm2 p1 p2 hvp _ => by
            have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
            exact (ih m2 (by omega)).1 S p1 p2 (cz_out + 1) (x + 2) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
          (fun _ _ m2 hm2 p1 p2 hvp _ => by
            have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
            exact (ih m2 (by omega)).2.1 S p1 p2 x 1 (cz_out - 1) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
      · exact amega_pop_step hb hphi38 (by omega) (by omega)
          (hS_cz.2.2 (x - 1) (by omega)) (fun _ => hS_cz.2.2 (x - 2) (by omega))
          (fun hbig _ _ p1 p2 hvp _ =>
            chainLeadsUpTo_here (Or.inr ⟨cz_out, x - 1, by omega,
              Or.inl ⟨hcz_out, by omega⟩, isBounce_r9 (by omega) hbig hvp⟩))
          (fun _ _ m2 hm2 p1 p2 hvp _ => by
            have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
            exact (ih m2 (by omega)).2.1 S p1 p2 (x + 1) (y + 2) cz_out hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
          (fun hy_le _ m2 hm2 p1 p2 hvp hfzp => by
            have hlos := arith_los_r11 hc hk1 hkc hfz40 hx96 hpot hy_ox hy_le hphi38 hyw hfzp
            exact (ih m2 (by omega)).2.2 S p1 p2 y 1 (x - 1) cz_out hne1 hS hvp
              (by omega) (by omega) (by omega) hcz_out hlos.2.1 hlos.2.2)
    exact ⟨hFH, hLH, hLOS⟩


-- ============================================================================
-- Section 5g.3b: Excursion Helpers, Root Invariant, and Drain-Pop Closures
-- ============================================================================

theorem chainLeads_trans {s : SegState} {P Q : SegState → Prop}
    (h1 : ChainLeads s P) (h2 : ∀ s', P s' → ChainLeads s' Q) :
    ChainLeads s Q :=
  fun N => chainLeadsUpTo_trans (h1 N) (fun m s' _ hp => h2 s' hp m)

-- ============================================================================
-- Generic Forced-R9 & k=1 Boost Helpers (`fbound_force_r9`, `fbound_k1_boost`)
-- ============================================================================

theorem fbound_force_r9 {N x d3 : Nat} {ds3 : List Nat} {segs : List (Nat × Nat)} {zl c k : Nat}
    {P : SegState → Prop}
    (hx19 : 19 ≤ x)
    (hgx : GoodDs (x :: d3 :: ds3) = true)
    (hg_pop1 : GoodDs ((x - 1) :: d3 :: ds3) = true)
    (hv : ValidSegs40 segs zl)
    (hc : 1 ≤ c) (hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hcz42 : 42 ≤ c + fzOf segs zl)
    (hox : 2 * x + 7 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
    (hcont1 : ∀ m phi, m ≤ N → 2 * x + 6 ≤ phi → ∀ s',
      IsBounce phi (x :: d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (hcont2 : ∀ m, m < N → ∀ s',
      IsBounce (x - 1) (d3 :: ds3) s' → ChainLeadsUpTo m s' P) :
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: d3 :: ds3⟩ P := by
  have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
  have hS : SafeStack (2 * x + 5) (x :: d3 :: ds3) :=
    safeStack_of_gt2d2 (by omega) (Nat.le_refl _) (by omega) hgx
  have hfb := (excursion_bundle N).1 (2 * x + 5) (x :: d3 :: ds3) segs zl c k
    (by omega) hS (validTail40_of_validSegs40 hv) hc hk1 hkc
    (by omega) hcz42 (by omega) hox
  refine chainLeadsUpTo_trans hfb ?_
  intro m1 s_mid hm1 hexit
  rcases hexit with ⟨phi, hphi_odw, hb⟩ | ⟨y, phi, hy_ox, hphi38, _, hb⟩
  · have hphi_ge : 2 * x + 6 ≤ phi := by dsimp only [odw] at hphi_odw; omega
    exact hcont1 m1 phi hm1 hphi_ge s_mid hb
  · exact amega_pop_step hb hphi38 (by omega) hx19 hg_pop1
      (by rintro ⟨_, h⟩; omega)
      (fun hbig m2 hm2 p1 p2 hvp _ =>
        hcont2 m2 (Nat.lt_of_lt_of_le hm2 hm1) _ (isBounce_r9 hx19 hbig hvp))
      (fun hle => False.elim (by omega))
      (fun hle => False.elim (by omega))

theorem arith_boost_c85 {c k fz : Nat}
    (_hc : 85 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz) :
    114 ≤ ox (k + 2 * fz) (c + fz) ∧ 113 ≤ odw (k + 2 * fz) (c + fz) ∧
    165 ≤ oxw (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * fz)
  dsimp only [odw, oxw]; rw [hdw, hox]; omega

theorem arith_boost_r10 {c k fz : Nat}
    (_hc : 43 ≤ c) (_hk : 72 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz) :
    73 ≤ ox (k + 2 * fz) (c + fz) ∧ 72 ≤ odw (k + 2 * fz) (c + fz) ∧
    126 ≤ oxw (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * fz)
  dsimp only [odw, oxw]; rw [hdw, hox]; omega

theorem arith_boost_cz {c fz cz_lo ox_lo : Nat}
    (_hc : 2 ≤ c) (_hfz : 40 ≤ fz) (_hcz : cz_lo ≤ c + fz)
    (_h : (cz_lo = 109 ∧ ox_lo = 99) ∨ (cz_lo = 118 ∧ ox_lo = 107) ∨
          (cz_lo = 148 ∧ ox_lo = 134) ∨ (cz_lo = 154 ∧ ox_lo = 140)) :
    ox_lo ≤ ox (1 + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := 1 + 2 * fz) (cz := c + fz) (by omega)
  omega

theorem fbound_k1_boost {N d2 : Nat} {ds2 : List Nat} {segs : List (Nat × Nat)} {zl c1 : Nat}
    (hne1 : (d2 :: ds2) ≠ [1]) (hS1 : SafeStack 19 (d2 :: ds2))
    (hv : ValidSegs40 segs zl) (hc1 : 2 ≤ c1) :
    ChainLeadsUpTo N ⟨false, segs, zl, c1, 1, 0, d2 :: ds2⟩ (Exit 39 38 107 (d2 :: ds2)) := by
  rcases segs with _ | ⟨⟨z1, m1⟩, rest1⟩
  · have hzl230 : 230 ≤ zl := hv.2
    have hg : stepGuards ⟨false, [], zl, c1, 1, 0, d2 :: ds2⟩ = true := by
      dsimp only [stepGuards]
      rw [goodPhiW_of_ge35 hS1.1 (by omega), Bool.true_and]
      dsimp only [GoodPsi]
      have hcz : c1 + zl - 1 + 1 = c1 + zl := by omega
      rw [hcz]; exact hS1.2.2 (c1 + zl) (by omega)
    apply chainLeadsUpTo_step1 hg
    dsimp only [stepSegs]
    apply chainLeadsUpTo_here
    refine Or.inr ⟨c1 + zl, 1 + 2 * zl + 2, by omega, by omega, by omega, ?_⟩
    simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := 1 + 2 * zl + 2) (kb := 0)
      (mrg := 2 * (1 + 2 * zl) + 6) (ds := (c1 + zl) :: d2 :: ds2) (by omega)
  · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv
    have hv_r1 : ValidSegs40 rest1 zl := validSegs40_tail hv
    cases m1 with
    | zero =>
      have hg1 : stepGuards ⟨false, (z1, 0) :: rest1, zl, c1, 1, 0, d2 :: ds2⟩ = true := rfl
      apply chainLeadsUpTo_step hg1
      intro m_a hm_a
      dsimp only [stepSegs]
      rcases rest1 with _ | ⟨⟨z2, m2⟩, rest2⟩
      · have hzl230 : 230 ≤ zl := hv_r1.2
        exact chainLeadsUpTo_here (Or.inl ⟨c1 + z1 + 3 + zl, by omega, IsBounce.nil (by omega)⟩)
      · have hz2_40 : 40 ≤ z2 := fzOf_ge_40 hv_r1
        have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_r1
        have hfz3_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
        cases m2 with
        | zero =>
          have hg2 : stepGuards ⟨true, (z2, 0) :: rest2, zl, c1 + z1 + 3, 1 + 2 * z1 + 3,
              2 * (c1 + z1) + 8, d2 :: ds2⟩ = true := by
            dsimp only [stepGuards]; exact decide_eq_true (by omega)
          apply chainLeadsUpTo_step hg2
          intro m_b hm_b
          dsimp only [stepSegs]
          have hb := arith_boost_c85 (c := c1 + z1 + 3 + z2 + 1) (k := 1 + 2 * z1 + 3 + 2 * z2 + 3)
            (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz3_40
          exact chainLeadsUpTo_imp
            ((excursion_bundle m_b).1 19 (d2 :: ds2) rest2 zl
              (c1 + z1 + 3 + z2 + 1) (1 + 2 * z1 + 3 + 2 * z2 + 3) (by decide) hS1
              (validTail40_of_validSegs40 hv_r2) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega))
            (fun _ he => exit_mono he (by omega) (by omega) (by omega))
        | succ m2' =>
          rcases dec_or ((m2' + 1) % 2 = 1) with hm2_od | hm2_ev
          · cases hd_mrg : decide (2 * (c1 + z1) + 8 ≥ (1 + 2 * z1 + 3) + m2') with
            | true =>
              have hg2 : stepGuards ⟨true, (z2, m2' + 1) :: rest2, zl, c1 + z1 + 3,
                  1 + 2 * z1 + 3, 2 * (c1 + z1) + 8, d2 :: ds2⟩ = true := by
                dsimp only [stepGuards]; rw [if_pos hm2_od, hd_mrg, if_pos rfl]
                exact hS1.2.2 (c1 + z1 + 3 + z2) (by omega)
              apply chainLeadsUpTo_step hg2
              intro m_b hm_b
              dsimp only [stepSegs]; rw [if_pos hm2_od, hd_mrg, if_pos rfl]
              exact (excursion_bundle m_b).2 19 (d2 :: ds2) rest2 zl
                ((1 + 2 * z1 + 3) + m2' + 2 * z2 + 4) 1 (c1 + z1 + 3 + z2) 39 107
                (by decide) hS1 (Or.inl hne1) hv_r2
                (by omega) (by omega) (by omega) (by decide) (by omega)
                (by omega) (by omega) (by omega) (by omega)
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact chainLeadsUpTo_here (Or.inl ⟨c1 + z1 + 3 + z2, by omega,
                IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm2_od]; omega)⟩)
          · cases hd_mrg : decide (2 * (c1 + z1) + 8 ≥ (1 + 2 * z1 + 3) + (m2' + 1)) with
            | true =>
              have h_mrg := of_decide_eq_true hd_mrg
              have hg2 : stepGuards ⟨true, (z2, m2' + 1) :: rest2, zl, c1 + z1 + 3,
                  1 + 2 * z1 + 3, 2 * (c1 + z1) + 8, d2 :: ds2⟩ = true := by
                dsimp only [stepGuards]; rw [if_neg hm2_ev, hd_mrg, if_pos rfl]
              apply chainLeadsUpTo_step hg2
              intro m_b hm_b
              dsimp only [stepSegs]; rw [if_neg hm2_ev, hd_mrg, if_pos rfl]
              have hb := arith_boost_c85 (c := c1 + z1 + 3 + z2 + 2)
                (k := (1 + 2 * z1 + 3) + (m2' + 1) + 2 * z2 + 5)
                (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz3_40
              exact chainLeadsUpTo_imp
                ((excursion_bundle m_b).1 19 (d2 :: ds2) rest2 zl
                  (c1 + z1 + 3 + z2 + 2) ((1 + 2 * z1 + 3) + (m2' + 1) + 2 * z2 + 5)
                  (by decide) hS1 (validTail40_of_validSegs40 hv_r2)
                  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                (fun _ he => exit_mono he (by omega) (by omega) (by omega))
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact chainLeadsUpTo_here (Or.inl ⟨c1 + z1 + 3 + z2, by omega,
                IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm2_ev]; omega)⟩)
    | succ m' =>
      have hfz2_40 : 40 ≤ fzOf rest1 zl := fzOf_ge_40 hv_r1
      have hphiw : GoodPhiW (c1 + z1 - 1) (d2 :: ds2) false = true :=
        goodPhiW_of_ge35 hS1.1 (by omega)
      -- Helper for x0 >= 42 pushed onto (d2 :: ds2) with c' >= 85:
      have h_push85 : ∀ m_b x0 k', 42 ≤ x0 → 1 ≤ k' → k' ≤ 2 * (1 + 2 * z1 + 4) + 3 →
          ChainLeadsUpTo m_b ⟨false, rest1, zl, 1 + 2 * z1 + 4, k', 0, x0 :: d2 :: ds2⟩
            (Exit 39 38 107 (d2 :: ds2)) := by
        intro m_b x0 k' hx0 hk'1 hk'c
        rcases dec_or (67 ≤ x0) with hx67 | hx66
        · exact (excursion_bundle m_b).2 19 (d2 :: ds2) rest1 zl (1 + 2 * z1 + 4) k' x0 39 107
            (by decide) hS1 (Or.inl hne1) hv_r1 (by omega) hk'1 hk'c (by decide) (by omega)
            (by omega) (by omega) (by omega) (by omega)
        · have hb85 := arith_boost_c85 (c := 1 + 2 * z1 + 4) (k := k') (fz := fzOf rest1 zl)
            (by omega) hk'1 hk'c hfz2_40
          have hSx0 : SafeStack 19 (x0 :: d2 :: ds2) :=
            safeStack_cons_ne1 hne1 hS1 (by omega) (by omega)
          have hfb1 := (excursion_bundle m_b).1 19 (x0 :: d2 :: ds2) rest1 zl
            (1 + 2 * z1 + 4) k' (by decide) hSx0 (validTail40_of_validSegs40 hv_r1)
            (by omega) hk'1 hk'c (by omega) (by omega) (by omega) (by omega)
          refine chainLeadsUpTo_trans hfb1 ?_
          intro m_c s_mid hm_c hex1
          rcases hex1 with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy_ox, hphi38, hyw, hb⟩
          · exact chainLeadsUpTo_here (Or.inr ⟨x0, phi, by omega, by omega, by omega, hb⟩)
          · exact amega_pop_step hb hphi38 (by omega) (by omega)
              (hS1.2.2 (x0 - 1) (by omega)) (fun _ => hS1.2.2 (x0 - 2) (by omega))
              (fun hbig _ _ p1 p2 hvp _ =>
                chainLeadsUpTo_here (Or.inl ⟨x0 - 1, by omega, isBounce_r9 (by omega) hbig hvp⟩))
              (fun _ _ m_d hm_d p1 p2 hvp _ => by
                have hfp := fzOf_ge_40 hvp
                have hr10 := arith_boost_r10 (c := x0 + 1) (k := y + 2) (fz := fzOf p1 p2)
                  (by omega) (by omega) (by omega) hfp
                exact chainLeadsUpTo_imp
                  ((excursion_bundle m_d).1 19 (d2 :: ds2) p1 p2 (x0 + 1) (y + 2)
                    (by decide) hS1 (validTail40_of_validSegs40 hvp)
                    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                  (fun _ he => exit_mono he (by omega) (by omega) (by omega)))
              (fun hy_le _ m_d hm_d p1 p2 hvp _ => by
                have hfp := fzOf_ge_40 hvp
                have hox140 := arith_boost_cz (c := y) (fz := fzOf p1 p2) (cz_lo := 154) (ox_lo :=
                  140)
                  (by omega) hfp (by omega) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                exact fbound_force_r9 (x := x0 - 1) (d3 := d2) (ds3 := ds2) (by omega)
                  (hS1.2.2 (x0 - 1) (by omega)) (hS1.2.2 (x0 - 2) (by omega)) hvp
                  (by omega) (by omega) (by omega) (by omega) (by omega)
                  (fun _ phi2 _ hphi2 _ hb2 =>
                    chainLeadsUpTo_here (Or.inr ⟨x0 - 1, phi2, by omega, by omega, by omega, hb2⟩))
                  (fun _ _ _ hb2 => chainLeadsUpTo_here (Or.inl ⟨x0 - 2, by omega, hb2⟩)))
      rcases dec_or (m' + 1 = 1) with hm_eq1 | hm_gt1
      · have hm0_eq : m' = 0 := by omega
        subst hm0_eq
        have hg : stepGuards ⟨false, (z1, 1) :: rest1, zl, c1, 1, 0, d2 :: ds2⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (c1 + z1 - 1) (d2 :: ds2) false &&
            if 1 = 1 then GoodPsi (c1 + z1) (d2 :: ds2) else _) = true
          rw [hphiw, Bool.true_and, if_pos rfl]
          exact hS1.2.2 (c1 + z1 + 1) (by omega)
        apply chainLeadsUpTo_step hg
        intro m_b hm_b
        dsimp only [stepSegs]
        change ChainLeadsUpTo m_b (if 1 = 1 then _ else _) _
        rw [if_pos rfl]
        exact h_push85 m_b (c1 + z1 + 1) 1 (by omega) (by omega) (by omega)
      · have hpsi_cz : GoodPsi (c1 + z1 - 1) (d2 :: ds2) = true := by
          dsimp only [GoodPsi]
          have hcz_eq : c1 + z1 - 1 + 1 = c1 + z1 := by omega
          rw [hcz_eq]; exact hS1.2.2 (c1 + z1) (by omega)
        rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10) with hev_sm | hnot_ev
        · have hg : stepGuards ⟨false, (z1, m' + 1) :: rest1, zl, c1, 1, 0, d2 :: ds2⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c1 + z1 - 1) (d2 :: ds2) false &&
              if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) (d2 :: ds2) &&
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else _) = true
            rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
          apply chainLeadsUpTo_step hg
          intro m_b hm_b
          dsimp only [stepSegs]
          change ChainLeadsUpTo m_b (if m' + 1 = 1 then _ else
            if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else _) _
          rw [if_neg hm_gt1, if_pos hev_sm]
          exact h_push85 m_b (c1 + z1) (m' + 2) (by omega) (by omega) (by omega)
        · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11) with hod_sm | hbig_m
          · have hS_cz : SafeStack 19 ((c1 + z1) :: d2 :: ds2) :=
              safeStack_cons_ne1 hne1 hS1 (by omega) (by omega)
            have hg : stepGuards ⟨false, (z1, m' + 1) :: rest1, zl, c1, 1, 0, d2 :: ds2⟩ = true :=
              by
              dsimp only [stepGuards]
              change (GoodPhiW (c1 + z1 - 1) (d2 :: ds2) false &&
                if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) (d2 :: ds2) &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then
                    GoodDs ((1 + 2 * z1 + 2) :: (c1 + z1) :: d2 :: ds2) else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_pos hod_sm]
              exact hS_cz.2.2 (1 + 2 * z1 + 2) (by omega)
            apply chainLeadsUpTo_step hg
            intro m_b hm_b
            dsimp only [stepSegs]
            change ChainLeadsUpTo m_b (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
            obtain ⟨q10, r10, hr10, hkz10, _⟩ := div10_spec (1 + 2 * z1)
            have hm_sub : m' + 1 - 1 = m' := by omega
            rw [hm_sub]
            have hne1_cz : ((c1 + z1) :: d2 :: ds2) ≠ [1] := by intro h; injection h with h1; omega
            have hl1 := (excursion_bundle m_b).2 19 ((c1 + z1) :: d2 :: ds2) rest1 zl
              m' 1 (1 + 2 * z1 + 2) (9 * q10 - 2) (1 + 2 * z1 + 35)
              (by decide) hS_cz (Or.inl hne1_cz) hv_r1
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega)
            refine chainLeadsUpTo_trans hl1 ?_
            intro m_c s_mid hm_c hex1
            rcases hex1 with ⟨phi0, hphi0, hb0⟩ | ⟨y0, phi0, hy0, hphi0_38, hyw0, hb0⟩
            · exact chainLeadsUpTo_here (Or.inr ⟨c1 + z1, phi0, by omega, by omega, by omega, hb0⟩)
            · exact amega_pop_step hb0 hphi0_38 (by omega) (by omega)
                (hS1.2.2 (c1 + z1 - 1) (by omega)) (fun _ => hS1.2.2 (c1 + z1 - 2) (by omega))
                (fun hbig _ _ p1 p2 hvp _ =>
                  chainLeadsUpTo_here (Or.inl ⟨c1 + z1 - 1,
                    by omega, isBounce_r9 (by omega) hbig hvp⟩))
                (fun _ _ m_d hm_d p1 p2 hvp _ => by
                  have hfp := fzOf_ge_40 hvp
                  have hr10 := arith_boost_r10 (c := c1 + z1 + 1) (k := y0 + 2) (fz := fzOf p1 p2)
                    (by omega) (by omega) (by omega) hfp
                  exact chainLeadsUpTo_imp
                    ((excursion_bundle m_d).1 19 (d2 :: ds2) p1 p2 (c1 + z1 + 1) (y0 + 2)
                      (by decide) hS1 (validTail40_of_validSegs40 hvp)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                    (fun _ he => exit_mono he (by omega) (by omega) (by omega)))
                (fun hy0_le _ m_d hm_d p1 p2 hvp hfzp => by
                  have hfp := fzOf_ge_40 hvp
                  rcases dec_or (62 ≤ c1 + z1 - 1) with hx62 | hx61
                  · exact (excursion_bundle m_d).2 19 (d2 :: ds2) p1 p2 y0 1 (c1 + z1 - 1) 39 107
                      (by decide) hS1 (Or.inl hne1) hvp (by omega) (by omega) (by omega)
                      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
                  · obtain ⟨x0, hx0⟩ : ∃ x0, c1 + z1 - 1 = x0 + 2 := ⟨c1 + z1 - 3, by omega⟩
                    rw [hx0] at hx61 ⊢
                    have hx0_lo : 39 ≤ x0 := by omega
                    have hx0_hi : x0 ≤ 59 := by omega
                    have hox107 := arith_boost_cz (c := y0) (fz := fzOf p1 p2)
                      (cz_lo := 118) (ox_lo := 107) (by omega) hfp (by omega)
                      (Or.inr (Or.inl ⟨rfl, rfl⟩))
                    have hSx' : SafeStack 19 ((x0 + 2) :: d2 :: ds2) :=
                      safeStack_cons_ne1 hne1 hS1 (by omega) (by omega)
                    have hfb2 := (excursion_bundle m_d).1 19 ((x0 + 2) :: d2 :: ds2)
                      p1 p2 y0 1 (by decide) hSx' (validTail40_of_validSegs40 hvp)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                    refine chainLeadsUpTo_trans hfb2 ?_
                    intro m_e s_m2 hm_e hex2
                    rcases hex2 with ⟨phi2, hphi2, hb2⟩ | ⟨y2, phi2, hy2_ox, hphi2_38, _, hb2⟩
                    · have hphi2_106 : 106 ≤ phi2 := by dsimp only [odw] at hphi2; omega
                      exact chainLeadsUpTo_here (Or.inr ⟨x0 + 2, phi2,
                        by omega, by omega, by omega, hb2⟩)
                    · exact amega_pop_step hb2 hphi2_38 (by omega) (by omega)
                        (hS1.2.2 (x0 + 1) (by omega)) (fun _ => hS1.2.2 x0 (by omega))
                        (fun hbig _ _ q1 q2 hvq _ =>
                          chainLeadsUpTo_here (Or.inl ⟨x0 + 1,
                            by omega, isBounce_r9 (by omega) hbig hvq⟩))
                        (fun _ _ m_f hm_f q1 q2 hvq _ => by
                          have hfq := fzOf_ge_40 hvq
                          have hr10 := arith_boost_r10 (c := x0 + 3) (k := y2 + 2) (fz :=
                            fzOf q1 q2)
                            (by omega) (by omega) (by omega) hfq
                          exact chainLeadsUpTo_imp
                            ((excursion_bundle m_f).1 19 (d2 :: ds2) q1 q2 (x0 + 3) (y2 + 2)
                              (by decide) hS1 (validTail40_of_validSegs40 hvq)
                              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                                (by omega))
                            (fun _ he => exit_mono he (by omega) (by omega) (by omega)))
                        (fun hy2_le _ m_f hm_f q1 q2 hvq _ => by
                          have hfq := fzOf_ge_40 hvq
                          have hox134 := arith_boost_cz (c := y2) (fz := fzOf q1 q2)
                            (cz_lo := 148) (ox_lo := 134) (by omega) hfq (by omega)
                            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                          exact fbound_force_r9 (x := x0 + 1) (d3 := d2) (ds3 := ds2) (by omega)
                            (hS1.2.2 (x0 + 1) (by omega)) (hS1.2.2 x0 (by omega)) hvq
                            (by omega) (by omega) (by omega) (by omega) (by omega)
                            (fun _ phi3 _ hphi3 _ hb3 =>
                              chainLeadsUpTo_here (Or.inr ⟨x0 + 1, phi3,
                                by omega, by omega, by omega, hb3⟩))
                            (fun _ _ _ hb3 => chainLeadsUpTo_here (Or.inl ⟨x0, by omega, hb3⟩))))
          · have hm1_big : 2 * (1 + 2 * z1) + 12 ≤ m' + 1 := by omega
            have hg : stepGuards ⟨false, (z1, m' + 1) :: rest1, zl, c1, 1, 0, d2 :: ds2⟩ = true :=
              by
              dsimp only [stepGuards]
              change (GoodPhiW (c1 + z1 - 1) (d2 :: ds2) false &&
                if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) (d2 :: ds2) &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_neg hbig_m]
            apply chainLeadsUpTo_step1 hg
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
            have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
              dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
            rw [hnorm]
            apply chainLeadsUpTo_here
            refine Or.inr ⟨c1 + z1, 1 + 2 * z1 + 2, by omega, by omega, by omega, ?_⟩
            have hbc := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
              (cp1 := 1 + 2 * z1 + 2) (kb := 0) (mrg := 2 * (1 + 2 * z1) + 6)
              (rest := rest1) (ds := (c1 + z1) :: d2 :: ds2) hv_r1 (by omega)
                (by split_ifs <;> omega)
            simpa only [Nat.add_zero] using hbc

theorem loop_k1_le47 {N x1 d3 : Nat} {ds3 : List Nat} {segs : List (Nat × Nat)} {zl c1 : Nat}
    {P : SegState → Prop}
    (hne1_0 : (d3 :: ds3) ≠ [1])
    (hS0 : SafeStack 21 (d3 :: ds3))
    (hx_lo : 23 ≤ x1 ∨ (x1 = 21 ∧ SafeStack 19 (d3 :: ds3)))
    (hx_hi : x1 ≤ 47)
    (hv : ValidSegs40 segs zl) (hc1 : 2 ≤ c1)
    (h_top : ∀ m z phi, m ≤ N → (z = x1 ∨ z = x1 - 1) → 38 ≤ phi → ∀ s',
      IsBounce phi (z :: d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_b1 : ∀ m, m < N → ∀ s', IsBounce (x1 - 1) (d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_b2 : ∀ m, m < N → ∀ s', IsBounce (x1 - 2) (d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_r10 : ∀ m c' k' p1 p2, m < N → c' = x1 + 1 → 41 ≤ k' → k' ≤ 2 * c' + 3 →
      ValidSegs40 p1 p2 → ChainLeadsUpTo m ⟨false, p1, p2, c', k', 0, d3 :: ds3⟩ P) :
    ChainLeadsUpTo N ⟨false, segs, zl, c1, 1, 0, x1 :: d3 :: ds3⟩ P := by
  have hx21 : 21 ≤ x1 := by rcases hx_lo with h | ⟨rfl, _⟩ <;> omega
  have hS1 : SafeStack 19 (x1 :: d3 :: ds3) := by
    rcases hx_lo with h23 | ⟨rfl, h19⟩
    · exact safeStack_cons_ne1 hne1_0 hS0 (by omega) (by omega)
    · exact safeStack_cons_ne1 hne1_0 h19 (by omega) (by omega)
  have hg_x1_1 : GoodDs ((x1 - 1) :: d3 :: ds3) = true := by
    rcases hx_lo with h23 | ⟨rfl, h19⟩
    · exact hS0.2.2 (x1 - 1) (by omega)
    · exact h19.2.2 20 (by decide)
  have hg_x1_2 : GoodDs ((x1 - 2) :: d3 :: ds3) = true := by
    rcases hx_lo with h23 | ⟨rfl, h19⟩
    · exact hS0.2.2 (x1 - 2) (by omega)
    · exact h19.2.2 19 (by decide)
  have hne1_1 : (x1 :: d3 :: ds3) ≠ [1] := by intro h; injection h with _ h2; cases h2
  have hb := fbound_k1_boost hne1_1 hS1 hv hc1 (N := N)
  refine chainLeadsUpTo_trans hb ?_
  intro m1 s_mid hm1 hex
  rcases hex with ⟨phi, hphi38, hsb⟩ | ⟨y1, phi1, hy1_39, hphi1_38, hyw1, hsb⟩
  · exact h_top m1 x1 phi hm1 (Or.inl rfl) hphi38 s_mid hsb
  · exact amega_pop_step hsb hphi1_38 (by omega) (by omega) hg_x1_1 (fun _ => hg_x1_2)
      (fun hbig m2 hm2 p1 p2 hvp _ =>
        h_b1 m2 (Nat.lt_of_lt_of_le hm2 hm1) _ (isBounce_r9 (by omega) hbig hvp))
      (fun _ _ m2 hm2 p1 p2 hvp _ =>
        h_r10 m2 (x1 + 1) (y1 + 2) p1 p2 (Nat.lt_of_lt_of_le hm2 hm1)
          rfl (by omega) (by omega) hvp)
      (fun hy1_le _ m2 hm2 p1 p2 hvp hfzp => by
        have hfp := fzOf_ge_40 hvp
        have hox99 := arith_boost_cz (c := y1) (fz := fzOf p1 p2) (cz_lo := 109) (ox_lo := 99)
          (by omega) hfp (by omega) (Or.inl ⟨rfl, rfl⟩)
        exact fbound_force_r9 (x := x1 - 1) (d3 := d3) (ds3 := ds3) (by omega)
          hg_x1_1 hg_x1_2 hvp (by omega) (by omega) (by omega) (by omega) (by omega)
          (fun m3 phi2 hm3 hphi2 s' hb2 =>
            h_top m3 (x1 - 1) phi2 (Nat.le_trans hm3 (Nat.le_of_lt (Nat.lt_of_lt_of_le hm2 hm1)))
              (Or.inr rfl) (by omega) s' hb2)
          (fun m3 hm3 s' hb2 =>
            h_b2 m3 (Nat.lt_trans hm3 (Nat.lt_of_lt_of_le hm2 hm1)) s' hb2))

-- ============================================================================
-- Odd-cz53 High Excursion Extension (`ExitHighOdd`, `loopOS_odd`, `fhigh_ext`)
-- ============================================================================

def ExitHighExt (S : List Nat) (s : SegState) : Prop :=
  ExitHigh S s ∨ (∃ y phi, 53 ≤ y ∧ y % 2 = 1 ∧ 88 ≤ phi ∧ IsBounce phi (y :: S) s)

theorem arith_los_odd_r11 {c k fz x y phi fz3 : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz)
    (_hx : 89 ≤ x) (_hpot : 2079 ≤ (c + fz) + 21 * x)
    (_hy_lo : ox (k + 2 * fz) (c + fz) ≤ y) (_hy_hi : y ≤ 2 * x + 4)
    (_hphi38 : 38 ≤ phi) (_hyw : oxw (k + 2 * fz) (c + fz) ≤ y + phi)
    (_hfz3 : phi + 2 ≤ fz3) :
    39 ≤ y ∧ 89 ≤ x - 1 ∧ 2079 ≤ (y + fz3) + 21 * (x - 1) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * fz)
  dsimp only [oxw] at _hyw
  rw [hdw] at _hyw
  rw [hox] at _hy_lo
  omega

theorem loopOS_odd (N : Nat) :
    ∀ S segs zl c k x cz_out,
      S ≠ [1] → SafeStack 43 S → ValidSegs40 segs zl →
      2 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
      53 ≤ cz_out → cz_out % 2 = 1 →
      89 ≤ x → 2079 ≤ (c + fzOf segs zl) + 21 * x →
      ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, x :: cz_out :: S⟩ (ExitHighExt S) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro S segs zl c k x cz_out hne1 hS hv hc hk1 hkc hcz_out hcz_odd hx89 hpot
    have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
    have hox39 : 39 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) :=
      (ox_bounds_relaxed (by omega) hk1 hkc (by omega) (by omega) (by omega)).1
    have hS_cz : SafeStack 19 (cz_out :: S) := safeStack_cons_ne1 hne1 hS (by omega) (by omega)
    have hne1_cz : (cz_out :: S) ≠ [1] := by intro h; injection h with h1; omega
    have hS_xcz : SafeStack 19 (x :: cz_out :: S) :=
      safeStack_cons_ne1 hne1_cz hS_cz (by omega) (by omega)
    have hfb := (excursion_bundle N).1 19 (x :: cz_out :: S) segs zl c k (by decide) hS_xcz
      (validTail40_of_validSegs40 hv) (by omega) hk1 hkc (by omega) (by omega) (by omega) (by omega)
    refine chainLeadsUpTo_trans hfb ?_
    intro m1 s_mid hm1 hexit
    rcases hexit with ⟨phi, hphi_odw, hb⟩ | ⟨y, phi, hy_ox, hphi38, hyw, hb⟩
    · obtain ⟨q0, r0, hr0, heq0, hox0⟩ :=
        ox_spec_lt (kz := k + 2 * fzOf segs zl) (cz := c + fzOf segs zl) (by omega)
      dsimp only [odw] at hphi_odw
      rw [hox0] at hphi_odw hox39
      have hphi38 : 38 ≤ phi := by omega
      exact amega_pop_step hb hphi38 (by omega) (by omega)
        (hS.2.2 (cz_out - 1) (by omega)) (fun _ => hS.2.2 (cz_out - 2) (by omega))
        (fun hbig _ _ p1 p2 hvp _ =>
          chainLeadsUpTo_here (Or.inl (Or.inl ⟨cz_out - 1,
            by omega, isBounce_r9 (by omega) hbig hvp⟩)))
        (fun _ _ m2 hm2 p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          exact chainLeadsUpTo_imp
            ((fhigh_bundle m2).1 S p1 p2 (cz_out + 1) (x + 2) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ he => Or.inl he))
        (fun _ _ m2 hm2 p1 p2 hvp hfzp => by
          have hfp := fzOf_ge_40 hvp
          exact chainLeadsUpTo_imp
            ((fhigh_bundle m2).2.1 S p1 p2 x 1 (cz_out - 1) hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ he => Or.inl he))
    · exact amega_pop_step hb hphi38 (by omega) (by omega)
        (hS_cz.2.2 (x - 1) (by omega)) (fun _ => hS_cz.2.2 (x - 2) (by omega))
        (fun hbig _ _ p1 p2 hvp _ =>
          chainLeadsUpTo_here (Or.inr ⟨cz_out, x - 1, hcz_out, hcz_odd, by omega,
            isBounce_r9 (by omega) hbig hvp⟩))
        (fun hy_hi _ m2 hm2 p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          obtain ⟨q0, r0, hr0, heq0, hox0⟩ :=
            ox_spec_lt (kz := k + 2 * fzOf segs zl) (cz := c + fzOf segs zl) (by omega)
          rw [hox0] at hy_ox
          exact chainLeadsUpTo_imp
            ((fhigh_bundle m2).2.1 S p1 p2 (x + 1) (y + 2) cz_out hne1 hS hvp
              (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ he => Or.inl he))
        (fun hy_le _ m2 hm2 p1 p2 hvp hfzp => by
          have hlos := arith_los_odd_r11 hc hk1 hkc hfz40 hx89 hpot hy_ox hy_le hphi38 hyw hfzp
          exact ih m2 (by omega) S p1 p2 y 1 (x - 1) cz_out hne1 hS hvp
            (by omega) (by omega) (by omega) hcz_out hcz_odd hlos.2.1 hlos.2.2)

theorem fhigh_ext {N : Nat} {S : List Nat} {segs : List (Nat × Nat)} {zl c : Nat}
    (hne1 : S ≠ [1]) (hS : SafeStack 43 S) (hv : ValidSegs40 segs zl)
    (hc : 2 ≤ c) (hcz53 : 53 ≤ c + fzOf segs zl)
    (hkz95 : 95 ≤ 1 + 2 * fzOf segs zl)
    (hodd : 1 + 2 * fzOf segs zl < 97 → (c + fzOf segs zl) % 2 = 1) :
    ChainLeadsUpTo N ⟨false, segs, zl, c, 1, 0, S⟩ (ExitHighExt S) := by
  rcases dec_or (97 ≤ 1 + 2 * fzOf segs zl) with h97 | hlt97
  · exact chainLeadsUpTo_imp
      ((fhigh_bundle N).1 S segs zl c 1 hne1 hS hv hc (by decide) (by omega) hcz53 h97)
      (fun _ he => Or.inl he)
  · have hcz_odd : (c + fzOf segs zl) % 2 = 1 := hodd (by omega)
    rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf] at hlt97; have := hv.2; omega
    · dsimp only [fzOf] at hcz53 hkz95 hlt97 hcz_odd
      have hz0_eq : z0 = 47 := by omega
      subst hz0_eq
      have hv_rest : ValidSegs40 rest zl := validSegs40_tail hv
      cases m0 with
      | zero =>
        have hg1 : stepGuards ⟨false, (47, 0) :: rest, zl, c, 1, 0, S⟩ = true := rfl
        apply chainLeadsUpTo_step hg1
        intro m1 hm1
        dsimp only [stepSegs]
        rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
        · have := hv_rest.2
          exact chainLeadsUpTo_here (Or.inl (Or.inl ⟨c + 47 + 3 + zl,
            by omega, IsBounce.nil (by omega)⟩))
        · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
          have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
          have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
          cases m1_seg with
          | zero =>
            have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + 50, 98, 2 * (c + 47) + 8, S⟩ =
              true := by
              dsimp only [stepGuards]; exact decide_eq_true (by omega)
            apply chainLeadsUpTo_step hg2
            intro m2 _
            dsimp only [stepSegs]
            exact chainLeadsUpTo_imp
              ((fhigh_bundle m2).1 S rest2 zl (c + 50 + z1 + 1) (98 + 2 * z1 + 3)
                hne1 hS hv_r2 (by omega) (by omega) (by omega) (by omega) (by omega))
              (fun _ he => Or.inl he)
          | succ m1' =>
            rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
            · cases hd_mrg : decide (2 * (c + 47) + 8 ≥ 98 + m1') with
              | true =>
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + 50, 98,
                    2 * (c + 47) + 8, S⟩ = true := by
                  dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                  exact hS.2.2 (c + 50 + z1) (by omega)
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_imp
                  ((fhigh_bundle m2).2.1 S rest2 zl (98 + m1' + 2 * z1 + 4) 1 (c + 50 + z1)
                    hne1 hS hv_r2 (by omega) (by omega) (by omega) (by omega) (by omega))
                  (fun _ he => Or.inl he)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact chainLeadsUpTo_here (Or.inl (Or.inl ⟨c + 50 + z1, by omega,
                  IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega)⟩))
            · cases hd_mrg : decide (2 * (c + 47) + 8 ≥ 98 + (m1' + 1)) with
              | true =>
                have h_mrg := of_decide_eq_true hd_mrg
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + 50, 98,
                    2 * (c + 47) + 8, S⟩ = true := by
                  dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_imp
                  ((fhigh_bundle m2).1 S rest2 zl (c + 50 + z1 + 2) (98 + (m1' + 1) + 2 * z1 + 5)
                    hne1 hS hv_r2 (by omega) (by omega) (by omega) (by omega) (by omega))
                  (fun _ he => Or.inl he)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact chainLeadsUpTo_here (Or.inl (Or.inl ⟨c + 50 + z1, by omega,
                  IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega)⟩))
      | succ m' =>
        have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
        have hphiw : GoodPhiW (c + 47 - 1) S false = true := goodPhiW_of_ge35 hS.1 (by omega)
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (47, 1) :: rest, zl, c, 1, 0, S⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + 47 - 1) S false && if 1 = 1 then GoodPsi (c + 47) S else _) = true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact hS.2.2 (c + 48) (by omega)
          apply chainLeadsUpTo_step hg
          intro m1 _
          dsimp only [stepSegs]
          change ChainLeadsUpTo m1 (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact chainLeadsUpTo_imp
            ((fhigh_bundle m1).2.1 S rest zl 99 1 (c + 48)
              hne1 hS hv_rest (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ he => Or.inl he)
        · have hpsi_cz : GoodPsi (c + 47 - 1) S = true := by
            dsimp only [GoodPsi]
            have hcz_eq : c + 47 - 1 + 1 = c + 47 := by omega
            rw [hcz_eq]; exact hS.2.2 (c + 47) (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (47, m' + 1) :: rest, zl, c, 1, 0, S⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + 47 - 1) S false &&
                if m' + 1 = 1 then _ else GoodPsi (c + 47 - 1) S &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            apply chainLeadsUpTo_step hg
            intro m1 _
            dsimp only [stepSegs]
            change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact chainLeadsUpTo_imp
              ((fhigh_bundle m1).2.1 S rest zl 99 (m' + 2) (c + 47)
                hne1 hS hv_rest (by omega) (by omega) (by omega) (by omega) (by omega))
              (fun _ he => Or.inl he)
          · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 201) with hod_sm | hbig_m
            · have hS_cz : SafeStack 19 ((c + 47) :: S) :=
                safeStack_cons_ne1 hne1 hS (by omega) (by omega)
              have hg : stepGuards ⟨false, (47, m' + 1) :: rest, zl, c, 1, 0, S⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + 47 - 1) S false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + 47 - 1) S &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 201 then
                      GoodDs (97 :: (c + 47) :: S) else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_pos hod_sm]
                exact hS_cz.2.2 97 (by decide)
              apply chainLeadsUpTo_step hg
              intro m1 _
              dsimp only [stepSegs]
              change ChainLeadsUpTo m1 (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 201 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
              have hm_sub : m' + 1 - 1 = m' := by omega
              rw [hm_sub]
              exact loopOS_odd m1 S rest zl m' 1 97 (c + 47) hne1 hS hv_rest
                (by omega) (by decide) (by omega) hcz53 hcz_odd (by decide) (by omega)
            · have hg : stepGuards ⟨false, (47, m' + 1) :: rest, zl, c, 1, 0, S⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + 47 - 1) S false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + 47 - 1) S &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 201 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              apply chainLeadsUpTo_step1 hg
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 200 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 201 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              apply chainLeadsUpTo_here
              refine Or.inl (Or.inr ⟨c + 47, 97, by omega, Or.inl ⟨hcz53, by decide⟩, ?_⟩)
              have hbc := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                (cp1 := 97) (kb := 0) (mrg := 196)
                (rest := rest) (ds := (c + 47) :: S) hv_rest (by omega)
                  (by split_ifs <;> omega)
              simpa only [Nat.add_zero] using hbc

-- ============================================================================
-- Root Invariant (`Root0`, `Root1`, `Root31`, `RootD`, `RootD1`, `RootInv`)
-- ============================================================================

def Root0A (s : SegState) : Prop :=
  s.ds = [] ∧ s.cp1 = 1 ∧ s.kb = 1 ∧
  ∃ z1 m0 m1 rest,
    s.segs = (8, m0) :: (z1, m1) :: rest ∧
    (m0 = 1 ∨ m0 = 2) ∧ 36 ≤ z1 ∧ ValidSegs40 rest s.zl

def Root0B (s : SegState) : Prop :=
  (s.ds = [] ∨ s.ds = [0]) ∧
  ValidTail40 s.segs s.zl ∧
  1 ≤ s.cp1 ∧ 1 ≤ s.kb ∧ s.kb ≤ 2 * s.cp1 + 3 ∧
  7 ≤ fzOf s.segs s.zl ∧ 8 ≤ s.cp1 + fzOf s.segs s.zl ∧
  (s.cp1 + fzOf s.segs s.zl = 8 → ∃ m0 rest,
    s.segs = (7, m0) :: rest ∧ s.cp1 = 1 ∧ s.kb = 1 ∧ s.ds = [0] ∧ 44 ≤ fzOf rest s.zl) ∧
  (fzOf s.segs s.zl < 39 →
    (s.cp1 = 1 ∧ s.kb = 1) ∨ (s.cp1 = 2 ∧ s.kb = 5 ∧ 20 ≤ fzOf s.segs s.zl)) ∧
  (∀ z0 m0 rest, s.segs = (z0, m0) :: rest → s.cp1 + fzOf s.segs s.zl = 9 →
    3 ≤ m0 → m0 % 2 = 1 →
      53 ≤ (m0 - 1) + fzOf rest s.zl ∧ 95 ≤ 1 + 2 * fzOf rest s.zl ∧
      (1 + 2 * fzOf rest s.zl < 97 → ((m0 - 1) + fzOf rest s.zl) % 2 = 1))

def Root0 (s : SegState) : Prop :=
  Root0A s ∨ Root0B s

def Root1 (s : SegState) : Prop :=
  s.ds = [1] ∧
  ValidTail40 s.segs s.zl ∧
  5 ≤ s.cp1 ∧ 1 ≤ s.kb ∧ s.kb ≤ 2 * s.cp1 + 3 ∧
  20 ≤ fzOf s.segs s.zl ∧ 45 ≤ s.kb + 2 * fzOf s.segs s.zl ∧
  (s.cp1 + fzOf s.segs s.zl = 25 → ∃ m0 rest,
    s.segs = (20, m0) :: rest ∧ s.cp1 = 5 ∧ s.kb = 5 ∧ 6 ≤ m0 ∧
    (m0 % 2 = 1 → 102 ≤ (m0 - 1) + fzOf rest s.zl ∧ 185 ≤ 1 + 2 * fzOf rest s.zl)) ∧
  (26 ≤ s.cp1 + fzOf s.segs s.zl → 47 ≤ s.kb + 2 * fzOf s.segs s.zl)

def Root31A (s : SegState) : Prop :=
  s.ds = [3, 1] ∧ ValidTail40 s.segs s.zl ∧
  s.cp1 = 2 ∧ s.kb = 1 ∧
  (fzOf s.segs s.zl = 18 ∨ fzOf s.segs s.zl = 19 ∨ ∃ rest, s.segs = (20, 0) :: rest)

def Root31B (s : SegState) : Prop :=
  s.ds = [3, 1] ∧
  ValidTail40 s.segs s.zl ∧
  2 ≤ s.cp1 ∧ 1 ≤ s.kb ∧ s.kb ≤ 2 * s.cp1 + 3 ∧
  21 ≤ fzOf s.segs s.zl ∧ 25 ≤ s.cp1 + fzOf s.segs s.zl ∧ 43 ≤ s.kb + 2 * fzOf s.segs s.zl ∧
  (∀ z0 m0 rest, s.segs = (z0, m0) :: rest → (s.cp1 + z0) % 2 = 0 → 3 ≤ m0 → m0 % 2 = 1 →
    (s.cp1 = 4 ∧ s.kb = 1 ∧ z0 = 22) ∨ 47 ≤ s.kb + 2 * z0)

def Root31 (s : SegState) : Prop :=
  Root31A s ∨ Root31B s

def RootD (s : SegState) : Prop :=
  (∃ d, 8 ≤ d ∧ (s.ds = [d] ∨ s.ds = [d, 0])) ∧
  ValidTail40 s.segs s.zl ∧
  1 ≤ s.cp1 ∧ 1 ≤ s.kb ∧ s.kb ≤ 2 * s.cp1 + 3 ∧
  35 ≤ fzOf s.segs s.zl ∧ 42 ≤ s.cp1 + fzOf s.segs s.zl ∧ 73 ≤ s.kb + 2 * fzOf s.segs s.zl

def RootD1 (s : SegState) : Prop :=
  (∃ d, 25 ≤ d ∧ s.ds = [d, 1]) ∧
  ValidTail40 s.segs s.zl ∧
  2 ≤ s.cp1 ∧ 1 ≤ s.kb ∧ s.kb ≤ 2 * s.cp1 + 3 ∧
  40 ≤ fzOf s.segs s.zl ∧ 62 ≤ s.cp1 + fzOf s.segs s.zl ∧ 81 ≤ s.kb + 2 * fzOf s.segs s.zl

def RootInv (s : SegState) : Prop :=
  s.b = false ∧ s.mrg = 0 ∧ (Root0 s ∨ Root1 s ∨ Root31 s ∨ RootD s ∨ RootD1 s)

theorem rootInv_of_0A {z1 m0 m1 zl : Nat} {rest : List (Nat × Nat)}
    (hm0 : m0 = 1 ∨ m0 = 2) (hz1 : 36 ≤ z1) (hv : ValidSegs40 rest zl) :
    RootInv ⟨false, (8, m0) :: (z1, m1) :: rest, zl, 1, 1, 0, []⟩ :=
  ⟨rfl, rfl, Or.inl (Or.inl ⟨rfl, rfl, rfl, z1, m0, m1, rest, rfl, hm0, hz1, hv⟩)⟩

theorem rootInv_of_0B {segs : List (Nat × Nat)} {zl c k : Nat} {ds : List Nat}
    (hds : ds = [] ∨ ds = [0]) (hvt : ValidTail40 segs zl)
    (hc : 1 ≤ c) (hk : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz : 7 ≤ fzOf segs zl) (hcz : 8 ≤ c + fzOf segs zl)
    (h8 : c + fzOf segs zl = 8 → ∃ m0 rest,
      segs = (7, m0) :: rest ∧ c = 1 ∧ k = 1 ∧ ds = [0] ∧ 44 ≤ fzOf rest zl)
    (h39 : fzOf segs zl < 39 → (c = 1 ∧ k = 1) ∨ (c = 2 ∧ k = 5 ∧ 20 ≤ fzOf segs zl))
    (h9 : ∀ z0 m0 rest, segs = (z0, m0) :: rest → c + fzOf segs zl = 9 →
      3 ≤ m0 → m0 % 2 = 1 →
        53 ≤ (m0 - 1) + fzOf rest zl ∧ 95 ≤ 1 + 2 * fzOf rest zl ∧
        (1 + 2 * fzOf rest zl < 97 → ((m0 - 1) + fzOf rest zl) % 2 = 1)) :
    RootInv ⟨false, segs, zl, c, k, 0, ds⟩ :=
  ⟨rfl, rfl, Or.inl (Or.inr ⟨hds, hvt, hc, hk, hkc, hfz, hcz, h8, h39, h9⟩)⟩

theorem rootInv_of_1 {segs : List (Nat × Nat)} {zl c k : Nat}
    (hvt : ValidTail40 segs zl)
    (hc : 5 ≤ c) (hk : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz : 20 ≤ fzOf segs zl) (hkz : 45 ≤ k + 2 * fzOf segs zl)
    (h25 : c + fzOf segs zl = 25 → ∃ m0 rest,
      segs = (20, m0) :: rest ∧ c = 5 ∧ k = 5 ∧ 6 ≤ m0 ∧
      (m0 % 2 = 1 → 102 ≤ (m0 - 1) + fzOf rest zl ∧ 185 ≤ 1 + 2 * fzOf rest zl))
    (h26 : 26 ≤ c + fzOf segs zl → 47 ≤ k + 2 * fzOf segs zl) :
    RootInv ⟨false, segs, zl, c, k, 0, [1]⟩ :=
  ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, hvt, hc, hk, hkc, hfz, hkz, h25, h26⟩)⟩

theorem rootInv_of_31A {segs : List (Nat × Nat)} {zl : Nat}
    (hvt : ValidTail40 segs zl)
    (hfz : fzOf segs zl = 18 ∨ fzOf segs zl = 19 ∨ ∃ rest, segs = (20, 0) :: rest) :
    RootInv ⟨false, segs, zl, 2, 1, 0, [3, 1]⟩ :=
  ⟨rfl, rfl, Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, hvt, rfl, rfl, hfz⟩)))⟩

theorem rootInv_of_31B {segs : List (Nat × Nat)} {zl c k : Nat} {ds : List Nat}
    (hds : ds = [3, 1]) (hvt : ValidTail40 segs zl)
    (hc : 2 ≤ c) (hk : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz : 21 ≤ fzOf segs zl) (hcz : 25 ≤ c + fzOf segs zl) (hkz : 43 ≤ k + 2 * fzOf segs zl)
    (hod : ∀ z0 m0 rest, segs = (z0, m0) :: rest → (c + z0) % 2 = 0 → 3 ≤ m0 → m0 % 2 = 1 →
      (c = 4 ∧ k = 1 ∧ z0 = 22) ∨ 47 ≤ k + 2 * z0) :
    RootInv ⟨false, segs, zl, c, k, 0, ds⟩ :=
  ⟨rfl, rfl, Or.inr (Or.inr (Or.inl (Or.inr ⟨hds, hvt, hc, hk, hkc, hfz, hcz, hkz, hod⟩)))⟩

theorem rootInv_of_D {segs : List (Nat × Nat)} {zl c k d : Nat} {ds : List Nat}
    (hd : 8 ≤ d) (hds : ds = [d] ∨ ds = [d, 0]) (hvt : ValidTail40 segs zl)
    (hc : 1 ≤ c) (hk : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz : 35 ≤ fzOf segs zl) (hcz : 42 ≤ c + fzOf segs zl) (hkz : 73 ≤ k + 2 * fzOf segs zl) :
    RootInv ⟨false, segs, zl, c, k, 0, ds⟩ :=
  ⟨rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨d, hd, hds⟩, hvt, hc, hk, hkc, hfz, hcz, hkz⟩)))⟩

theorem rootInv_of_D1 {segs : List (Nat × Nat)} {zl c k d : Nat}
    (hd : 25 ≤ d) (hvt : ValidTail40 segs zl)
    (hc : 2 ≤ c) (hk : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz : 40 ≤ fzOf segs zl) (hcz : 62 ≤ c + fzOf segs zl) (hkz : 81 ≤ k + 2 * fzOf segs zl) :
    RootInv ⟨false, segs, zl, c, k, 0, [d, 1]⟩ :=
  ⟨rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨d, hd, rfl⟩, hvt, hc, hk, hkc, hfz, hcz, hkz⟩)))⟩

-- ============================================================================
-- Drain-Pop Closure Lemmas (`IsBounce phi ds s -> ChainLeadsUpTo N s RootInv`)
-- ============================================================================

theorem bounce_nil_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [] s) (hphi : 9 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hg_pop : drainPopGuards phi [] = true := by
    change decide (phi ≥ 2) = true
    exact decide_eq_true (by omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step1 hg_s
  rw [hstep]
  set p := pushSeg hp (phi + 1) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [] = ⟨false, p.1, p.2, 1, 1, 0, []⟩ := rfl
  rw [hdp]
  have hvt : ValidTail40 p.1 p.2 :=
    validTail40_pushSeg hp hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 1 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 1) m_rem rest zl
  exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvt (by decide) (by decide) (by decide)
    (by omega) (by omega) (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩)
    (by intro _ _ _ _ hcz9; omega))

theorem bounce_zero_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [0] s) (hphi : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hg_pop : drainPopGuards phi [0] = true := by
    change decide (phi ≥ 2) = true
    exact decide_eq_true (by omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [0] = ⟨true, p.1, p.2, 2, 2, 6, []⟩ := rfl
  rw [hdp]
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  rcases h_p1 : p.1 with _ | ⟨⟨z1, m1_seg⟩, r2⟩
  · have hzl230 : 230 ≤ p.2 := by rw [h_p1] at hvp; exact hvp.2
    exact bounce_nil_leads (IsBounce.nil (by omega)) (by omega)
  · rw [h_p1] at hvp
    have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hvp
    have hv_r2 : ValidSegs40 r2 p.2 := validSegs40_tail hvp
    have hfz2_40 : 40 ≤ fzOf r2 p.2 := fzOf_ge_40 hv_r2
    cases m1_seg with
    | zero =>
      have hg2 : stepGuards ⟨true, (z1, 0) :: r2, p.2, 2, 2, 6, []⟩ = true := rfl
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]
      exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hv_r2)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
    | succ m1' =>
      rcases dec_or ((m1' + 1) % 2 = 1) with hod | hev
      · cases hd_mrg : decide (6 ≥ 2 + m1') with
        | true =>
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, p.2, 2, 2, 6, []⟩ = true := by
            dsimp only [stepGuards]; rw [if_pos hod, hd_mrg, if_pos rfl]
            exact safeStack_nil.2.2 (2 + z1) (by omega)
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_pos hod, hd_mrg, if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_D (d := 2 + z1) (by omega) (Or.inl rfl)
            (validTail40_of_validSegs40 hv_r2) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_nil_leads
            (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hod]; omega)) (by omega)
      · cases hd_mrg : decide (6 ≥ 2 + (m1' + 1)) with
        | true =>
          have h_mrg := of_decide_eq_true hd_mrg
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, p.2, 2, 2, 6, []⟩ = true := by
            dsimp only [stepGuards]; rw [if_neg hev, hd_mrg, if_pos rfl]
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_neg hev, hd_mrg, if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hv_r2)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_nil_leads (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hev]; omega))
            (by omega)

theorem bounce_one_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [1] s) (hphi : 24 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hg_pop : drainPopGuards phi [1] = true := by
    change decide (phi ≥ 2) = true
    exact decide_eq_true (by omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hdp : drainPopStep hp phi m_rem rest zl [1] =
      ⟨true, (pushSeg hp (phi + 3) m_rem rest zl).1, (pushSeg hp (phi + 3) m_rem rest zl).2,
        2, 0, 6, []⟩ := rfl
  rw [hdp]
  cases hp with
  | false =>
    have hzl230 : 230 ≤ phi := hzl_false rfl
    change ChainLeadsUpTo m1 ⟨true, [], phi + 3, 2, 0, 6, []⟩ RootInv
    exact bounce_nil_leads (IsBounce.nil (by omega)) (by omega)
  | true =>
    have hv_r : ValidSegs40 rest zl := hv_rest rfl
    have hfz_r : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_r
    dsimp only [pushSeg, ite_true]
    cases m_rem with
    | zero =>
      dsimp only [normSeg, ite_true]
      have hg2 : stepGuards ⟨true, (phi + 3 + 1, 0) :: rest, zl, 2, 0, 6, []⟩ = true := rfl
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]
      exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hv_r)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
    | succ mr' =>
      have hnorm : normSeg (phi + 3) (mr' + 1) = (phi + 3, mr' + 1) := rfl
      rw [hnorm]
      rcases dec_or ((mr' + 1) % 2 = 1) with hod | hev
      · cases hd_mrg : decide (6 ≥ 0 + mr') with
        | true =>
          have hg2 : stepGuards ⟨true, (phi + 3, mr' + 1) :: rest, zl, 2, 0, 6, []⟩ = true := by
            dsimp only [stepGuards]; rw [if_pos hod, hd_mrg, if_pos rfl]
            exact safeStack_nil.2.2 (2 + (phi + 3)) (by omega)
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_pos hod, hd_mrg, if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_D (d := 2 + (phi + 3)) (by omega) (Or.inl rfl)
            (validTail40_of_validSegs40 hv_r) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_nil_leads (IsBounce.cons hv_r (by omega) (by rw [if_pos hod]; omega))
            (by omega)
      · cases hd_mrg : decide (6 ≥ 0 + (mr' + 1)) with
        | true =>
          have h_mrg := of_decide_eq_true hd_mrg
          have hg2 : stepGuards ⟨true, (phi + 3, mr' + 1) :: rest, zl, 2, 0, 6, []⟩ = true := by
            dsimp only [stepGuards]; rw [if_neg hev, hd_mrg, if_pos rfl]
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_neg hev, hd_mrg, if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hv_r)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_nil_leads (IsBounce.cons hv_r (by omega) (by rw [if_neg hev]; omega))
            (by omega)

theorem bounce_31_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [3, 1] s) (hphi : 18 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hg_pop : drainPopGuards phi [3, 1] = true := by
    change (true && true && true && decide (phi ≥ 16)) = true
    rw [Bool.true_and, Bool.true_and, Bool.true_and]
    exact decide_eq_true (by omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [3, 1] = ⟨true, (1, 0) :: p.1, p.2, 0, 0, 2, []⟩ :=
    rfl
  rw [hdp]
  have hvt : ValidTail40 p.1 p.2 :=
    validTail40_pushSeg hp hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  have hg2 : stepGuards ⟨true, (1, 0) :: p.1, p.2, 0, 0, 2, []⟩ = true := rfl
  apply chainLeadsUpTo_step1 hg2
  dsimp only [stepSegs]
  exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvt
    (by decide) (by decide) (by decide) (by omega) (by omega)
    (by intro h; omega) (fun _ => Or.inr ⟨rfl, rfl, by omega⟩)
    (by intro _ _ _ _ hcz9; omega))

theorem bounce_cz_31_leads {N cz phi : Nat} {s : SegState}
    (hb : IsBounce phi [cz, 3, 1] s)
    (hcases : ((cz = 20 ∨ cz = 21) ∧ 34 ≤ phi) ∨
              (22 ≤ cz ∧ cz % 2 = 1 ∧ 38 ≤ phi) ∨
              (26 ≤ cz ∧ cz % 2 = 0 ∧ (46 ≤ phi ∨ (cz = 26 ∧ phi = 45)))) :
    ChainLeadsUpTo N s RootInv := by
  have hcz20 : 20 ≤ cz := by rcases hcases with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hphi34 : 34 ≤ phi := by
    rcases hcases with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h | ⟨_, rfl⟩⟩ <;> omega
  have hnrst : isDrainRstDs [cz, 3, 1] = false := rfl
  have hnr0 : isRank0 [cz, 3, 1] = false := by
    rcases cz with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop' : drainPopGuards phi [cz, 3, 1] = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (cz ≥ 3 ∧ 3 ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (cz % 2 = 0 ∧ cz ≤ 2 * 3 + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (cz % 2 = 0 ∧ cz + 14 ≤ 2 * 3) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop'
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [cz, 3, 1] =
      ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      if_neg (by rintro ⟨h31, _, _⟩; cases h31)]
    have hnorm : normSeg 0 (cz - 3) = (0, cz - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]
  rw [hdp] at hstep
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  -- Step 1: <true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]> bounces on [1] with phi' = 2, m_rem' = cz
  -- - 11
  have hg_b1 : stepGuards ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ = true := by
    have hsub : cz - 3 = (cz - 4) + 1 := by omega
    rw [hsub]; dsimp only [stepGuards]
    rcases dec_or (((cz - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs_b1 : stepSegs ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ =
      ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ := by
    have hsub : cz - 3 = (cz - 4) + 1 := by omega
    have hm_eq : 0 + ((cz - 4) + 1) - (6 + 2) = (cz - 12) + 1 := by omega
    have h11 : cz - 11 = (cz - 12) + 1 := by omega
    rw [hsub, h11]; dsimp only [stepSegs]
    rcases dec_or (((cz - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
  apply chainLeadsUpTo_step hg_b1
  intro m2 _
  rw [hs_b1]
  -- Step 2: <true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []> bounces on [] with phi'' = 7, m_rem'' =
  -- cz - 19
  have hg_b2 : stepGuards ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
    have hsub : cz - 11 = (cz - 12) + 1 := by omega
    rw [hsub]; dsimp only [stepGuards]
    rcases dec_or (((cz - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs_b2 : stepSegs ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ =
      ⟨false, (8, cz - 19) :: p.1, p.2, 1, 1, 0, []⟩ := by
    have hsub : cz - 11 = (cz - 12) + 1 := by omega
    have hm_eq : 0 + ((cz - 12) + 1) - (6 + 2) = (cz - 20) + 1 := by omega
    have h19 : cz - 19 = (cz - 20) + 1 := by omega
    rw [hsub, h19]; dsimp only [stepSegs]
    rcases dec_or (((cz - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
  apply chainLeadsUpTo_step1 hg_b2
  rw [hs_b2]
  apply chainLeadsUpTo_here
  rcases hcases with ⟨hcz2021, _⟩ | ⟨hcz22, hcz_od, hphi38⟩ | ⟨hcz26, hcz_ev, hphi_ev⟩
  · -- Root0A (`cz = 20` or `cz = 21`, `34 <= phi => 36 <= fzOf p.1 p.2`):
    cases hp with
    | false =>
      have := hzl_false rfl
      have hvp : ValidSegs40 p.1 p.2 :=
        validSegs40_pushSeg false (by omega) hv_rest (fun _ => by omega)
      exact rootInv_of_0B (Or.inl rfl) hvp
        (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega)
          (by dsimp only [fzOf]; omega)
        (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩)
        (by intro z0 m0 r hseg _; injection hseg with hhd _; injection hhd with _ hm0; omega)
    | true =>
      have hvr := hv_rest rfl
      dsimp only [p, pushSeg, ite_true] at hfzp ⊢
      exact rootInv_of_0A (by omega) (Nat.le_trans (by omega) (normSeg_fst_ge (phi + 2) m_rem)) hvr
  · -- `cz >= 22` odd => `cz - 19` is EVEN (`m0 % 2 = 1` vacuous!):
    have hvp : ValidSegs40 p.1 p.2 :=
      validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
    exact rootInv_of_0B (Or.inl rfl) hvp
      (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega)
      (by dsimp only [fzOf]; omega)
      (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩)
      (by intro z0 m0 r hseg _ _ hm0_od; injection hseg with hhd _; injection hhd with _ hm0; omega)
  · -- `cz >= 26` even => `cz - 19 >= 7` odd:
    have hphi45 : 45 ≤ phi := by rcases hphi_ev with h | ⟨_, rfl⟩ <;> omega
    have hvp : ValidSegs40 p.1 p.2 :=
      validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
    refine rootInv_of_0B (Or.inl rfl) hvp
      (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega)
      (by dsimp only [fzOf]; omega)
      (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩) ?_
    intro z0 m0 r hseg _ _ _
    injection hseg with hhd htl
    injection hhd with hz0 hm0
    subst hz0 hm0 htl
    rcases hphi_ev with hphi46 | ⟨rfl, rfl⟩
    · exact ⟨by omega, by omega, fun hlt => False.elim (by omega)⟩
    · exact ⟨by omega, by omega, fun _ => by omega⟩

theorem bounce_d1_leads {N d phi : Nat} {s : SegState}
    (hb : IsBounce phi [d, 1] s) (hd25 : 25 ≤ d) (hphi42 : 42 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hnrst : isDrainRstDs [d, 1] = false := rfl
  have hnr0 : isRank0 [d, 1] = false := by
    rcases d with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi [d, 1] = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (d ≥ 3 ∧ 1 ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (d % 2 = 0 ∧ d ≤ 2 * 1 + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (d % 2 = 0 ∧ d + 14 ≤ 2 * 1) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [d, 1] =
      ⟨true, normSeg 0 (d - 11) :: p.1, p.2, 5, 0, 12, [2]⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_pos ⟨rfl, rfl, hd25⟩]
  rw [hdp]
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  have hnorm0 : normSeg 0 (d - 11) = (0, (d - 12) + 1) := by
    dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
  rw [hnorm0]
  -- <true, (0, d - 11) :: p.1, p.2, 5, 0, 12, [2]> bounces on [2] with phi' = 5, m_rem' = d - 25
  have hg2 : stepGuards ⟨true, (0, (d - 12) + 1) :: p.1, p.2, 5, 0, 12, [2]⟩ = true := by
    dsimp only [stepGuards]
    rcases dec_or (((d - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs2 : stepSegs ⟨true, (0, (d - 12) + 1) :: p.1, p.2, 5, 0, 12, [2]⟩ =
      ⟨false, normSeg 7 (d - 25) :: p.1, p.2, 1, 1, 0, [0]⟩ := by
    have hm_eq : 0 + ((d - 12) + 1) - (12 + 2) = d - 25 := by omega
    dsimp only [stepSegs]
    rcases dec_or (((d - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
  apply chainLeadsUpTo_step1 hg2
  rw [hs2]
  apply chainLeadsUpTo_here
  rcases dec_or (d = 25) with rfl | hd26
  · have hnorm8 : normSeg 7 (25 - 25) = (8, 0) := rfl
    rw [hnorm8]
    exact rootInv_of_0B (Or.inr rfl) hvp
      (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega)
      (by dsimp only [fzOf]; omega)
      (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩)
      (by intro z0 m0 r hseg _ h3; injection hseg with hhd _; injection hhd with _ hm0; omega)
  · have hnorm7 : normSeg 7 (d - 25) = (7, d - 25) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm7]
    exact rootInv_of_0B (Or.inr rfl) hvp
      (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega)
      (by dsimp only [fzOf]; omega)
      (fun _ => ⟨d - 25, p.1, rfl, rfl, rfl, rfl, by omega⟩)
      (fun _ => Or.inl ⟨rfl, rfl⟩)
      (by intro _ _ _ _ hcz9; cases hcz9)

theorem bounce_d_leads {N d phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi ds s)
    (hds : ds = [d] ∨ ds = [d, 0])
    (hcases : (d = 8 ∧ (phi = 16 ∨ phi = 17 ∨ 38 ≤ phi)) ∨
              (d = 9 ∧ 19 ≤ phi) ∨
              (10 ≤ d ∧ d ≤ 18 ∧ 19 ≤ phi ∧ (12 ≤ d → d % 2 = 0 → 23 ≤ phi)) ∨
              (d = 19 ∧ 37 ≤ phi) ∨
              (20 ≤ d ∧ 38 ≤ phi)) :
    ChainLeadsUpTo N s RootInv := by
  have hd8 : 8 ≤ d := by
    rcases hcases with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨h, _⟩ | ⟨rfl, _⟩ | ⟨h, _⟩ <;> omega
  have hrst : isDrainRstDs ds = true := by
    rcases hds with rfl | rfl <;> (dsimp only [isDrainRstDs]; exact decide_eq_true hd8)
  have hhd_ds : headNat ds = d := by rcases hds with rfl | rfl <;> rfl
  have hg_pop : drainPopGuards phi ds = true := by
    dsimp only [drainPopGuards]; rw [hrst, if_pos rfl]
    apply decide_eq_true
    rcases hcases with ⟨rfl, h16⟩ | ⟨_, h19⟩ | ⟨_, _, h19, _⟩ | ⟨_, h19⟩ | ⟨_, h19⟩
    · rcases hds with rfl | rfl <;> (change 16 ≤ phi; omega)
    all_goals (cases isOddDrainDs ds <;> simp only [Bool.false_eq_true, ite_false,
      ite_true] <;> omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  dsimp only [drainPopStep]
  rw [hrst, if_pos rfl, hhd_ds]
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hvt : ValidTail40 p.1 p.2 :=
    validTail40_pushSeg hp hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  rcases hcases with ⟨rfl, hphi_d8⟩ | ⟨rfl, hphi19⟩ | ⟨hd10, hd18, hphi19, hd_ev23⟩ |
      ⟨rfl, hphi37⟩ | ⟨hd20, hphi38⟩
  · -- d = 8 (`d - 7 = 1` -> `[3, 1]` with `c = 2, k = 1`):
    rw [if_pos rfl]
    apply chainLeadsUpTo_here
    rcases hphi_d8 with rfl | rfl | hphi38
    · refine rootInv_of_31A hvt ?_
      cases hp with
      | false => have := hzl_false rfl; omega
      | true =>
        cases m_rem with
        | zero => exact Or.inr (Or.inl rfl)
        | succ _ => exact Or.inl rfl
    · refine rootInv_of_31A hvt ?_
      cases hp with
      | false => have := hzl_false rfl; omega
      | true =>
        cases m_rem with
        | zero => exact Or.inr (Or.inr ⟨rest, rfl⟩)
        | succ _ => exact Or.inr (Or.inl rfl)
    · refine rootInv_of_31B rfl hvt (by decide) (by decide) (by decide)
        (by omega) (by omega) (by omega) ?_
      intro z0 m0 r hseg _ _ _
      have hz0 : fzOf p.1 p.2 = z0 := by rw [hseg]; rfl
      exact Or.inr (by omega)
  · -- d = 9 (`9 - 7 = 2`, `normSeg 0 0 = (1, 0)` on `[1]`, steps to `c = 5, k = 5, fz >= 21`):
    rw [if_neg (by decide)]
    dsimp only [Nat.reduceSub, normSeg, ite_true]
    have hg2 : stepGuards ⟨true, (1, 0) :: p.1, p.2, 3, 0, 8, [1]⟩ = true := rfl
    apply chainLeadsUpTo_step1 hg2
    dsimp only [stepSegs]
    exact chainLeadsUpTo_here (rootInv_of_1 hvt
      (by decide) (by decide) (by decide) (by omega) (by omega)
      (by intro h; omega) (fun _ => by omega))
  · -- 10 <= d <= 18 (`1 <= d - 9 <= 9`):
    rw [if_neg (by omega)]
    have hnorm : normSeg 0 (d - 7 - 2) = (0, (d - 10) + 1) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
    rw [hnorm]
    rcases dec_or (((d - 10) + 1) % 2 = 1) with hod | hev
    · -- d even in {10, 12, 14, 16, 18} -> `[3, 1]` with `c = d - 6, k = 1`:
      have hmrg : decide (8 ≥ 0 + (d - 10)) = true := decide_eq_true (by omega)
      have hg2 : stepGuards ⟨true, (0, (d - 10) + 1) :: p.1, p.2, 3, 0, 8, [1]⟩ = true := by
        dsimp only [stepGuards]; rw [if_pos hod, hmrg, if_pos rfl]; rfl
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]; rw [if_pos hod, hmrg, if_pos rfl]
      apply chainLeadsUpTo_here
      refine rootInv_of_31B rfl hvt (by omega) (by decide) (by omega)
        (by omega) (by omega) (by omega) ?_
      intro z0 m0 r hseg hpar _ _
      have hz0 : fzOf p.1 p.2 = z0 := by rw [hseg]; rfl
      rcases dec_or (d = 10) with rfl | hd12
      · omega
      · have h23 := hd_ev23 (by omega) (by omega)
        exact Or.inr (by omega)
    · -- d odd in {11, 13, 15, 17} -> `[1]` with `c = 5, k = d - 4 >= 7, fz >= 21`:
      have hmrg : decide (8 ≥ 0 + ((d - 10) + 1)) = true := decide_eq_true (by omega)
      have hg2 : stepGuards ⟨true, (0, (d - 10) + 1) :: p.1, p.2, 3, 0, 8, [1]⟩ = true := by
        dsimp only [stepGuards]; rw [if_neg hev, hmrg, if_pos rfl]
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]; rw [if_neg hev, hmrg, if_pos rfl]
      exact chainLeadsUpTo_here (rootInv_of_1 hvt
        (by decide) (by omega) (by omega) (by omega) (by omega)
        (by intro h; omega) (fun _ => by omega))
  · -- d = 19 (`19 - 9 = 10`, bounces on `[1]` with `m_rem' = 0`):
    rw [if_neg (by decide)]
    have hnorm : normSeg 0 (19 - 7 - 2) = (0, 10) := rfl
    rw [hnorm]
    have hg2 : stepGuards ⟨true, (0, 10) :: p.1, p.2, 3, 0, 8, [1]⟩ = true := rfl
    have hs2 : stepSegs ⟨true, (0, 10) :: p.1, p.2, 3, 0, 8, [1]⟩ =
        ⟨true, (7, 0) :: p.1, p.2, 2, 0, 6, []⟩ := rfl
    apply chainLeadsUpTo_step hg2
    intro m2 _
    rw [hs2]
    have hg3 : stepGuards ⟨true, (7, 0) :: p.1, p.2, 2, 0, 6, []⟩ = true := rfl
    apply chainLeadsUpTo_step1 hg3
    dsimp only [stepSegs]
    exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvt
      (by decide) (by decide) (by decide) (by omega) (by omega)
      (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
  · -- d >= 20 (`38 <= phi` => `ValidSegs40 p.1 p.2`, bounces on `[1]` with `m_rem' = d - 19 >= 1`):
    rw [if_neg (by omega)]
    have hvp : ValidSegs40 p.1 p.2 :=
      validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
    have hfzp40 : 40 ≤ fzOf p.1 p.2 := fzOf_ge_40 hvp
    have hnorm : normSeg 0 (d - 7 - 2) = (0, (d - 10) + 1) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
    rw [hnorm]
    have hg2 : stepGuards ⟨true, (0, (d - 10) + 1) :: p.1, p.2, 3, 0, 8, [1]⟩ = true := by
      dsimp only [stepGuards]
      rcases dec_or (((d - 10) + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod, decide_eq_false (by omega)]; rfl
      · rw [if_neg hev, decide_eq_false (by omega)]; rfl
    have hs2 : stepSegs ⟨true, (0, (d - 10) + 1) :: p.1, p.2, 3, 0, 8, [1]⟩ =
        ⟨true, (6, (d - 20) + 1) :: p.1, p.2, 2, 0, 6, []⟩ := by
      have hm_eq : 0 + ((d - 10) + 1) - (8 + 2) = (d - 20) + 1 := by omega
      dsimp only [stepSegs]
      rcases dec_or (((d - 10) + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
      · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
    apply chainLeadsUpTo_step hg2
    intro m2 _
    rw [hs2]
    rcases dec_or (((d - 20) + 1) % 2 = 1) with hod2 | hev2
    · cases hd_mrg2 : decide (6 ≥ 0 + (d - 20)) with
      | true =>
        have hg3 : stepGuards ⟨true, (6, (d - 20) + 1) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_pos hod2, hd_mrg2, if_pos rfl]; rfl
        apply chainLeadsUpTo_step1 hg3
        dsimp only [stepSegs]; rw [if_pos hod2, hd_mrg2, if_pos rfl]
        exact chainLeadsUpTo_here (rootInv_of_D (d := 8) (by decide) (Or.inl rfl)
          (validTail40_of_validSegs40 hvp) (by omega) (by decide) (by omega)
          (by omega) (by omega) (by omega))
      | false =>
        have hg3 : stepGuards ⟨true, (6, (d - 20) + 1) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_pos hod2, hd_mrg2, if_neg Bool.false_ne_true]; rfl
        apply chainLeadsUpTo_step1 hg3
        dsimp only [stepSegs]; rw [if_pos hod2, hd_mrg2, if_neg Bool.false_ne_true]
        set q := pushSeg true 9 (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2
        have hdp3 : drainPopStep true (2 + 6) (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2 [] =
            ⟨false, q.1, q.2, 1, 1, 0, []⟩ := rfl
        rw [hdp3]
        have hvtq : ValidTail40 q.1 q.2 :=
          validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
        have hfzq : 9 ≤ fzOf q.1 q.2 :=
          fzOf_pushSeg_ge true 9 (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
    · cases hd_mrg2 : decide (6 ≥ 0 + ((d - 20) + 1)) with
      | true =>
        have h_mrg2 := of_decide_eq_true hd_mrg2
        have hg3 : stepGuards ⟨true, (6, (d - 20) + 1) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_neg hev2, hd_mrg2, if_pos rfl]
        apply chainLeadsUpTo_step1 hg3
        dsimp only [stepSegs]; rw [if_neg hev2, hd_mrg2, if_pos rfl]
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hvp)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
      | false =>
        have hg3 : stepGuards ⟨true, (6, (d - 20) + 1) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_neg hev2, hd_mrg2, if_neg Bool.false_ne_true]; rfl
        apply chainLeadsUpTo_step1 hg3
        dsimp only [stepSegs]; rw [if_neg hev2, hd_mrg2, if_neg Bool.false_ne_true]
        set q := pushSeg true 9 (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2
        have hdp3 : drainPopStep true (2 + 6) (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2 [] =
            ⟨false, q.1, q.2, 1, 1, 0, []⟩ := rfl
        rw [hdp3]
        have hvtq : ValidTail40 q.1 q.2 :=
          validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
        have hfzq : 9 ≤ fzOf q.1 q.2 :=
          fzOf_pushSeg_ge true 9 (0 + ((d - 20) + 1) - (6 + 2)) p.1 p.2
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))


-- ============================================================================
-- Section 5g.3c: RootD, RootD1, and Root1 Advancement Closures
-- ============================================================================

theorem chainAdvances_trans {s : SegState} {P Q : SegState → Prop}
    (h1 : ChainAdvances s P) (h2 : ∀ s', P s' → ChainLeads s' Q) :
    ChainAdvances s Q :=
  ⟨h1.1, chainLeads_trans h1.2 h2⟩

theorem fbound_advances {ms : Nat} {S : List Nat} {segs : List (Nat × Nat)} {zl c k : Nat}
    (hms19 : 19 ≤ ms) (hS : SafeStack ms S)
    (hvt : ValidTail40 segs zl)
    (hc : 1 ≤ c) (hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3)
    (hfz35 : 35 ≤ fzOf segs zl) (hcz42 : 42 ≤ c + fzOf segs zl)
    (hkz73 : 73 ≤ k + 2 * fzOf segs zl)
    (hms_ox : ms + 2 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl)) :
    ChainAdvances ⟨false, segs, zl, c, k, 0, S⟩
      (Exit (ox (k + 2 * fzOf segs zl) (c + fzOf segs zl))
        (odw (k + 2 * fzOf segs zl) (c + fzOf segs zl))
        (oxw (k + 2 * fzOf segs zl) (c + fzOf segs zl)) S) := by
  obtain ⟨hox39, hox_cz3⟩ := ox_bounds_relaxed hc hk1 hkc hfz35 hcz42 hkz73
  rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
  · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73 hms_ox hox39 hox_cz3 ⊢
    have hg : stepGuards ⟨false, [], zl, c, k, 0, S⟩ = true := by
      dsimp only [stepGuards]
      rw [goodPhiW_of_ge35 hS.1 (by omega), Bool.true_and]
      dsimp only [GoodPsi]
      have hcz : c + zl - 1 + 1 = c + zl := by omega
      rw [hcz]; exact hS.2.2 (c + zl) (by omega)
    refine ⟨hg, fun N => ?_⟩
    dsimp only [stepSegs]
    apply chainLeadsUpTo_here
    obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * zl)
    refine Or.inr ⟨c + zl, k + 2 * zl + 2, by omega, by omega, ?_, ?_⟩
    · dsimp only [oxw]; rw [hdw]; omega
    · simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
        (mrg := 2 * (k + 2 * zl) + 6) (ds := (c + zl) :: S) (by omega)
  · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73 hms_ox hox39 hox_cz3 ⊢
    have hv_rest : ValidSegs40 rest zl := hvt
    cases m0 with
    | zero =>
      refine ⟨rfl, fun N => ?_⟩
      dsimp only [stepSegs]
      rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
      · have hzl230 : 230 ≤ zl := hv_rest.2
        exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + zl, by dsimp only [odw]; omega,
          IsBounce.nil (by omega)⟩)
      · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
        have hv_rest2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
        have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_rest2
        cases m1_seg with
        | zero =>
          have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3,
              2 * (c + z0) + 8, S⟩ = true := by
            dsimp only [stepGuards]; exact decide_eq_true (by omega)
          apply chainLeadsUpTo_step hg2
          intro m2 _
          dsimp only [stepSegs]
          have hmono := arith_fb_t0 hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40
          exact chainLeadsUpTo_imp
            ((excursion_bundle m2).1 ms S rest2 zl (c + z0 + 3 + z1 + 1)
              (k + 2 * z0 + 3 + 2 * z1 + 3) hms19 hS (validTail40_of_validSegs40 hv_rest2)
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (Nat.le_trans hms_ox hmono.1))
            (fun _ he => exit_mono he hmono.1 hmono.2.1 hmono.2.2)
        | succ m1' =>
          rcases dec_or ((m1' + 1) % 2 = 1) with hm1_odd | hm1_even
          · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
            | true =>
              have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                  k + 2 * z0 + 3, 2 * (c + z0) + 8, S⟩ = true := by
                dsimp only [stepGuards]; rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
                exact hS.2.2 (c + z0 + 3 + z1) (by omega)
              apply chainLeadsUpTo_step hg2
              intro m2 _
              dsimp only [stepSegs]; rw [if_pos hm1_odd, hd_mrg, if_pos rfl]
              have hi := arith_fb_to (m1' := m1') hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40
              exact (excursion_bundle m2).2 ms S rest2 zl
                ((k + 2 * z0 + 3) + m1' + 2 * z1 + 4) 1 (c + z0 + 3 + z1)
                (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
                hms19 hS (Or.inr (by omega)) hv_rest2
                (by omega) (by omega) (by omega) hms_ox hi.1
                hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by dsimp only [odw]; omega,
                IsBounce.cons hv_rest2 (by omega) (by rw [if_pos hm1_odd]; omega)⟩)
          · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
            | true =>
              have h_mrg := of_decide_eq_true hd_mrg
              have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                  k + 2 * z0 + 3, 2 * (c + z0) + 8, S⟩ = true := by
                dsimp only [stepGuards]; rw [if_neg hm1_even, hd_mrg, if_pos rfl]
              apply chainLeadsUpTo_step hg2
              intro m2 _
              dsimp only [stepSegs]; rw [if_neg hm1_even, hd_mrg, if_pos rfl]
              have hmono := arith_fb_te hc hk1 hkc hfz35 hcz42 hkz73 hz1_40 hfz2_40 h_mrg
              exact chainLeadsUpTo_imp
                ((excursion_bundle m2).1 ms S rest2 zl (c + z0 + 3 + z1 + 2)
                  ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5)
                  hms19 hS (validTail40_of_validSegs40 hv_rest2)
                  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                  (Nat.le_trans hms_ox hmono.1))
                (fun _ he => exit_mono he hmono.1 hmono.2.1 hmono.2.2)
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact chainLeadsUpTo_here (Or.inl ⟨c + z0 + 3 + z1, by dsimp only [odw]; omega,
                IsBounce.cons hv_rest2 (by omega) (by rw [if_neg hm1_even]; omega)⟩)
    | succ m' =>
      have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
      have hphiw : GoodPhiW (c + z0 - 1) S false = true := goodPhiW_of_ge35 hS.1 (by omega)
      rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
      · have hm0_eq : m' = 0 := by omega
        subst hm0_eq
        have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, S⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (c + z0 - 1) S false && if 1 = 1 then GoodPsi (c + z0) S else _) = true
          rw [hphiw, Bool.true_and, if_pos rfl]
          exact hS.2.2 (c + z0 + 1) (by omega)
        refine ⟨hg, fun N => ?_⟩
        dsimp only [stepSegs]
        change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
        rw [if_pos rfl]
        have hi := arith_fb_m1_ev (dx := 1) hc hk1 hkc hfz35 hcz42 hkz73 hfz1_40 (by decide)
        exact (excursion_bundle N).2 ms S rest zl (k + 2 * z0 + 4) 1 (c + z0 + 1)
          (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
          hms19 hS (Or.inr (by omega)) hv_rest
          (by omega) (by omega) (by omega) hms_ox hi.1
          hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
      · have hpsi_cz : GoodPsi (c + z0 - 1) S = true := by
          dsimp only [GoodPsi]
          have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
          rw [hcz_eq]; exact hS.2.2 (c + z0) (by omega)
        rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
        · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) S false &&
              if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
            rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
            if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
          rw [if_neg hm_gt1, if_pos hev_sm]
          have hi := arith_fb_m1_ev (dx := 0) hc hk1 hkc hfz35 hcz42 hkz73 hfz1_40 (by decide)
          have hcz0 : c + z0 + 0 = c + z0 := by omega
          rw [hcz0] at hi
          exact (excursion_bundle N).2 ms S rest zl (k + 2 * z0 + 4) (m' + 2) (c + z0)
            (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
            hms19 hS (Or.inr (by omega)) hv_rest
            (by omega) (by omega) (by omega) hms_ox hi.1
            hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2
        · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
          · have hS_cz : SafeStack 39 ((c + z0) :: S) := safeStack_cons hS (by omega) (by omega)
            have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) S false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                    GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: S) else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_pos hod_sm]
              exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
            obtain ⟨q10, r10, hr10, hkz10, hdw10⟩ := div10_spec (k + 2 * z0)
            have hos_in : 39 + 2 ≤ 9 * q10 - 2 ∧ 9 * q10 - 2 ≤ k + 2 * z0 + 2 ∧
                30 * (9 * q10 - 2) ≤ (m' + fzOf rest zl) + 27 * (k + 2 * z0 + 2) + 900 ∧
                60 * (9 * q10 - 2) + 120 ≤ 2 * (m' + fzOf rest zl) + 55 * (k + 2 * z0 + 2) ∧
                10 * (k + 2 * z0 + 35) + 40 ≤ 9 * (m' + fzOf rest zl) + 10 * (k + 2 * z0 + 2) ∧
                20 * (k + 2 * z0 + 35) ≤ (m' + fzOf rest zl) + 20 * (k + 2 * z0 + 2) + 800 := by
                  omega
            have hm_sub : m' + 1 - 1 = m' := by omega
            rw [hm_sub]
            have hne1_cz : ((c + z0) :: S) ≠ [1] := by intro h; injection h with h1; omega
            have h_loop1 := (excursion_bundle N).2 39 ((c + z0) :: S) rest zl m' 1
              (k + 2 * z0 + 2) (9 * q10 - 2) (k + 2 * z0 + 35)
              (by decide) hS_cz (Or.inl hne1_cz) hv_rest
              (by omega) (by omega) (by omega) hos_in.1 hos_in.2.1
              hos_in.2.2.1 hos_in.2.2.2.1 hos_in.2.2.2.2.1 hos_in.2.2.2.2.2
            refine chainLeadsUpTo_trans h_loop1 ?_
            intro m2 s_mid hm2 hexit1
            rcases hexit1 with ⟨phi1, hphi1, hb1⟩ | ⟨y1, phi1, hy1_tx1, hphi1_38, hyw1, hb1⟩
            · apply chainLeadsUpTo_here
              obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * z0)
              refine Or.inr ⟨c + z0, phi1, by omega, by omega, ?_, hb1⟩
              dsimp only [oxw]; rw [hdw]; omega
            · exact amega_pop_step hb1 hphi1_38 (by omega) (by omega)
                (hS.2.2 (c + z0 - 1) (by omega))
                (fun _ => hS.2.2 (c + z0 - 2) (by omega))
                (fun hbig _ _ p1 p2 hvp _ =>
                  chainLeadsUpTo_here (Or.inl ⟨c + z0 - 1, by dsimp only [odw]; omega,
                    isBounce_r9 (by omega) hbig hvp⟩))
                (fun hy1_le _ m3 _ p1 p2 hvp hfzp => by
                  have hy1_lo : 9 * ((k + 2 * z0) / 10) - 2 ≤ y1 := by rw [hdw10]; exact hy1_tx1
                  have hmono :=
                    arith_fb_os_r10 hc hk1 hkc hfz35 hcz42 hkz73 hy1_lo hy1_le hphi1_38 hyw1 hfzp
                  exact chainLeadsUpTo_imp
                    ((excursion_bundle m3).1 ms S p1 p2 (c + z0 + 1) (y1 + 2) hms19 hS
                      (validTail40_of_validSegs40 hvp)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                      (Nat.le_trans hms_ox hmono.1))
                    (fun _ he => exit_mono he hmono.1 hmono.2.1 hmono.2.2))
                (fun _ _ m3 _ p1 p2 hvp hfzp => by
                  have hi := arith_fb_os_r11 hc hk1 hkc hfz35 hcz42 hkz73 hyw1 hfzp
                  exact (excursion_bundle m3).2 ms S p1 p2 y1 1 (c + z0 - 1)
                    (ox (k + 2 * z0) (c + z0)) (oxw (k + 2 * z0) (c + z0))
                    hms19 hS (Or.inr (by omega)) hvp
                    (by omega) (by omega) (by omega) hms_ox hi.1
                    hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2)
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, S⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) S false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) S &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_neg hbig_m]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
            have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
              dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
            rw [hnorm]
            apply chainLeadsUpTo_here
            obtain ⟨qw, rw_, hrw, hkw, hdw⟩ := div20_spec (k + 2 * z0)
            refine Or.inr ⟨c + z0, k + 2 * z0 + 2, by omega, by omega, ?_, ?_⟩
            · dsimp only [oxw]; rw [hdw]; omega
            · have hbc := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                (rest := rest) (ds := (c + z0) :: S) hv_rest (by omega)
                  (by split_ifs <;> omega)
              simpa only [Nat.add_zero] using hbc

theorem ox_ge_of_c {c k fz : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (_hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz) :
    c + 38 - (c + 13) / 10 ≤ ox (k + 2 * fz) (c + fz) ∧
    c + 37 - (c + 13) / 10 ≤ odw (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  dsimp only [odw]; omega

theorem ox_ge57_of_cz62 {c k fz : Nat}
    (_hc : 2 ≤ c) (_hk1 : 1 ≤ k) (_hkc : k ≤ 2 * c + 3) (_hfz : 40 ≤ fz)
    (_hcz : 62 ≤ c + fz) (_hkz : 81 ≤ k + 2 * fz) :
    57 ≤ ox (k + 2 * fz) (c + fz) ∧ 56 ≤ odw (k + 2 * fz) (c + fz) := by
  obtain ⟨q, r, hr, heq, hox⟩ := ox_spec_lt (kz := k + 2 * fz) (cz := c + fz) (by omega)
  dsimp only [odw]; omega

theorem r9_pop_step {N x y phi : Nat} {S : List Nat} {sb : SegState} {P : SegState → Prop}
    (hb : IsBounce phi (y :: x :: S) sb)
    (hphi38 : 38 ≤ phi) (hx19 : 19 ≤ x) (hbig : 2 * x + 5 ≤ y)
    (hcont : ∀ m, m < N → ∀ p1 p2, ValidSegs40 p1 p2 → phi + 2 ≤ fzOf p1 p2 →
      ChainLeadsUpTo m ⟨true, (0, y - 3) :: p1, p2, x - 1, 0, 2 * x, S⟩ P) :
    ChainLeadsUpTo N sb P := by
  have hnrst : isDrainRstDs (y :: x :: S) = false := by
    cases x with | zero => omega | succ _ => rfl
  have hnr0 : isRank0 (y :: x :: S) = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi (y :: x :: S) = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ x ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (y % 2 = 0 ∧ y ≤ 2 * x + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (y % 2 = 0 ∧ y + 14 ≤ 2 * x) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_sb, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl (y :: x :: S) =
      ⟨true, (0, y - 3) :: p.1, p.2, x - 1, 0, 2 * x, S⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg (by omega)]
    have hnorm : normSeg 0 (y - 3) = (0, y - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  apply chainLeadsUpTo_step hg_sb
  intro m hm
  rw [hstep, hdp]
  exact hcont m hm p.1 p.2 hvp hfzp

-- ============================================================================
-- Auxiliary Bounce & Drain-Pop Lemmas for RootD / RootD1 / Root1
-- ============================================================================

theorem bounce_r9_zero_leads {N d y : Nat} {p1 : List (Nat × Nat)} {p2 : Nat}
    (hd8 : 8 ≤ d) (hbig : 2 * d + 5 ≤ y) (hvp : ValidSegs40 p1 p2) :
    ChainLeadsUpTo N ⟨true, (0, y - 3) :: p1, p2, d - 1, 0, 2 * d, [0]⟩ RootInv := by
  have hy_sub : y - 3 = (y - 4) + 1 := by omega
  have hpop0 : drainPopGuards (d - 1 + 0) [0] = true := by
    change decide (d - 1 + 0 ≥ 2) = true; exact decide_eq_true (by omega)
  have hg1 : stepGuards ⟨true, (0, y - 3) :: p1, p2, d - 1, 0, 2 * d, [0]⟩ = true := by
    rw [hy_sub]; dsimp only [stepGuards]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; exact hpop0
    · rw [if_neg hev, decide_eq_false (by omega)]; exact hpop0
  have hs1 : stepSegs ⟨true, (0, y - 3) :: p1, p2, d - 1, 0, 2 * d, [0]⟩ =
      ⟨true, normSeg (d + 1) (y - 2 * d - 5) :: p1, p2, 2, 2, 6, []⟩ := by
    have hm_eq : 0 + ((y - 4) + 1) - (2 * d + 2) = y - 2 * d - 5 := by omega
    have hd_eq : d - 1 + 0 + 2 = d + 1 := by omega
    rw [hy_sub]; dsimp only [stepSegs]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]
      dsimp only [drainPopStep, isDrainRstDs, isRank0, pushSeg, ite_true, ite_false]
      rw [hd_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]
      dsimp only [drainPopStep, isDrainRstDs, isRank0, pushSeg, ite_true, ite_false]
      rw [hd_eq]; rfl
  apply chainLeadsUpTo_step hg1
  intro m1 _
  rw [hs1]
  have hfp40 : 40 ≤ fzOf p1 p2 := fzOf_ge_40 hvp
  rcases hmr : y - 2 * d - 5 with _ | mr'
  · dsimp only [normSeg, ite_true]
    have hg2 : stepGuards ⟨true, (d + 1 + 1, 0) :: p1, p2, 2, 2, 6, []⟩ = true := rfl
    apply chainLeadsUpTo_step1 hg2
    dsimp only [stepSegs]
    exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hvp)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
  · have hn : normSeg (d + 1) (mr' + 1) = (d + 1, mr' + 1) := rfl
    rw [hn]
    rcases dec_or ((mr' + 1) % 2 = 1) with hod | hev
    · cases hd_mrg : decide (6 ≥ 2 + mr') with
      | true =>
        have hg2 : stepGuards ⟨true, (d + 1, mr' + 1) :: p1, p2, 2, 2, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_pos hod, hd_mrg, if_pos rfl]
          exact (safeStack_d (by omega)).2.1
        apply chainLeadsUpTo_step1 hg2
        dsimp only [stepSegs]; rw [if_pos hod, hd_mrg, if_pos rfl]
        exact chainLeadsUpTo_here (rootInv_of_D (d := 2 + (d + 1)) (by omega) (Or.inl rfl)
          (validTail40_of_validSegs40 hvp) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega))
      | false =>
        have hg2 : stepGuards ⟨true, (d + 1, mr' + 1) :: p1, p2, 2, 2, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_pos hod, hd_mrg, if_neg Bool.false_ne_true]
          change decide (2 + (d + 1) ≥ 2) = true; exact decide_eq_true (by omega)
        apply chainLeadsUpTo_step1 hg2
        dsimp only [stepSegs]; rw [if_pos hod, hd_mrg, if_neg Bool.false_ne_true]
        set q := pushSeg true (2 + (d + 1) + 1) (2 + (mr' + 1) - (6 + 2)) p1 p2
        have hdp : drainPopStep true (2 + (d + 1)) (2 + (mr' + 1) - (6 + 2)) p1 p2 [] =
            ⟨false, q.1, q.2, 1, 1, 0, []⟩ := rfl
        rw [hdp]
        have hvtq : ValidTail40 q.1 q.2 :=
          validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
        have hfzq : 2 + (d + 1) + 1 ≤ fzOf q.1 q.2 :=
          fzOf_pushSeg_ge true (2 + (d + 1) + 1) (2 + (mr' + 1) - (6 + 2)) p1 p2
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
    · cases hd_mrg : decide (6 ≥ 2 + (mr' + 1)) with
      | true =>
        have h_mrg := of_decide_eq_true hd_mrg
        have hg2 : stepGuards ⟨true, (d + 1, mr' + 1) :: p1, p2, 2, 2, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_neg hev, hd_mrg, if_pos rfl]
        apply chainLeadsUpTo_step1 hg2
        dsimp only [stepSegs]; rw [if_neg hev, hd_mrg, if_pos rfl]
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) (validTail40_of_validSegs40 hvp)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
      | false =>
        have hg2 : stepGuards ⟨true, (d + 1, mr' + 1) :: p1, p2, 2, 2, 6, []⟩ = true := by
          dsimp only [stepGuards]; rw [if_neg hev, hd_mrg, if_neg Bool.false_ne_true]
          change decide (2 + (d + 1) ≥ 2) = true; exact decide_eq_true (by omega)
        apply chainLeadsUpTo_step1 hg2
        dsimp only [stepSegs]; rw [if_neg hev, hd_mrg, if_neg Bool.false_ne_true]
        set q := pushSeg true (2 + (d + 1) + 1) (2 + (mr' + 1) - (6 + 2)) p1 p2
        have hdp : drainPopStep true (2 + (d + 1)) (2 + (mr' + 1) - (6 + 2)) p1 p2 [] =
            ⟨false, q.1, q.2, 1, 1, 0, []⟩ := rfl
        rw [hdp]
        have hvtq : ValidTail40 q.1 q.2 :=
          validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
        have hfzq : 2 + (d + 1) + 1 ≤ fzOf q.1 q.2 :=
          fzOf_pushSeg_ge true (2 + (d + 1) + 1) (2 + (mr' + 1) - (6 + 2)) p1 p2
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))

theorem bounce_y_8_ge46_leads {N y phi : Nat} {s : SegState}
    (hb : IsBounce phi [y, 8] s) (hy28 : 28 ≤ y) (hphi46 : 46 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hnrst : isDrainRstDs [y, 8] = false := rfl
  have hnr0 : isRank0 [y, 8] = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi [y, 8] = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ 8 ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (y % 2 = 0 ∧ y ≤ 2 * 8 + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (y % 2 = 0 ∧ y + 14 ≤ 2 * 8) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [y, 8] =
      ⟨true, (0, (y - 4) + 1) :: p.1, p.2, 7, 0, 16, []⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      if_neg (by rintro ⟨h81, _, _⟩; cases h81)]
    have hnorm : normSeg 0 (y - 3) = (0, (y - 4) + 1) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
    rw [hnorm]
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hg2 : stepGuards ⟨true, (0, (y - 4) + 1) :: p.1, p.2, 7, 0, 16, []⟩ = true := by
    dsimp only [stepGuards]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs2 : stepSegs ⟨true, (0, (y - 4) + 1) :: p.1, p.2, 7, 0, 16, []⟩ =
      ⟨false, (8, y - 21) :: p.1, p.2, 1, 1, 0, []⟩ := by
    have hm_eq : 0 + ((y - 4) + 1) - (16 + 2) = y - 21 := by omega
    have hn8 : normSeg 8 (y - 21) = (8, y - 21) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    have hdp2 : drainPopStep true (7 + 0) (y - 21) p.1 p.2 [] =
        ⟨false, normSeg 8 (y - 21) :: p.1, p.2, 1, 1, 0, []⟩ := rfl
    dsimp only [stepSegs]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), if_neg Bool.false_ne_true, hm_eq, hdp2, hn8]
    · rw [if_neg hev, decide_eq_false (by omega), if_neg Bool.false_ne_true, hm_eq, hdp2, hn8]
  apply chainLeadsUpTo_step1 hg2
  rw [hs2]
  apply chainLeadsUpTo_here
  refine rootInv_of_0B (Or.inl rfl) hvp
    (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
    (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩) ?_
  intro z0 m0 r hseg _ _ _
  injection hseg with hhd htl
  injection hhd with hz0 hm0
  subst hz0 hm0 htl
  exact ⟨by omega, by omega, fun hlt => False.elim (by omega)⟩

theorem bounce_y_d_small_leads {N d y phi : Nat} {tl : List Nat} {s : SegState}
    (hb : IsBounce phi (y :: d :: tl) s)
    (hd_lo : 8 ≤ d) (hd_hi : d ≤ 18)
    (htl : tl = [] ∨ tl = [0])
    (h8_tl : d = 8 → tl = [0])
    (hy39 : 39 ≤ y) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hg1 : 9 ≤ d → GoodDs ((d - 1) :: tl) = true := by
    intro hd9
    rcases htl with rfl | rfl
    · exact (safeStack_d (by omega)).2.1
    · exact (safeStack_d0 (by omega)).2.1
  have hnrst : isDrainRstDs (y :: d :: tl) = false := by
    cases d with | zero => omega | succ _ => rfl
  have hnr0 : isRank0 (y :: d :: tl) = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi (y :: d :: tl) = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ d ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : (!decide (y % 2 = 0 ∧ y ≤ 2 * d + 4) || GoodDs ((d - 1) :: tl)) = true := by
      rcases dec_or (d = 8) with rfl | hd9
      · rw [decide_eq_false (by omega)]; rfl
      · rw [hg1 (by omega), Bool.or_true]
    have hc3 : decide (y % 2 = 0 ∧ y + 14 ≤ 2 * d) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl (y :: d :: tl) =
      ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, tl⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg (by omega)]
    have hnorm : normSeg 0 (y - 3) = (0, y - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp40 : 40 ≤ fzOf p.1 p.2 := fzOf_ge_40 hvp
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  rcases dec_or (2 * d + 5 ≤ y) with hbig | hsm
  · rcases htl with rfl | rfl
    · have hd9 : 9 ≤ d := by
        rcases dec_or (d = 8) with rfl | h9
        · cases h8_tl rfl
        · omega
      have hy_sub : y - 3 = (y - 4) + 1 := by omega
      have hpop_nil : drainPopGuards (d - 1 + 0) [] = true := by
        change decide (d - 1 + 0 ≥ 2) = true; exact decide_eq_true (by omega)
      have hg2 : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, []⟩ = true := by
        rw [hy_sub]; dsimp only [stepGuards]
        rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
        · rw [if_pos hod, decide_eq_false (by omega)]; exact hpop_nil
        · rw [if_neg hev, decide_eq_false (by omega)]; exact hpop_nil
      apply chainLeadsUpTo_step1 hg2
      rw [hy_sub]; dsimp only [stepSegs]
      set q := pushSeg true (d - 1 + 0 + 1) (0 + ((y - 4) + 1) - (2 * d + 2)) p.1 p.2
      have hvtq : ValidTail40 q.1 q.2 :=
        validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
      have hfzq : d - 1 + 0 + 1 ≤ fzOf q.1 q.2 :=
        fzOf_pushSeg_ge true (d - 1 + 0 + 1) (0 + ((y - 4) + 1) - (2 * d + 2)) p.1 p.2
      rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod, decide_eq_false (by omega)]
        change ChainLeadsUpTo m1 ⟨false, q.1, q.2, 1, 1, 0, []⟩ RootInv
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
      · rw [if_neg hev, decide_eq_false (by omega)]
        change ChainLeadsUpTo m1 ⟨false, q.1, q.2, 1, 1, 0, []⟩ RootInv
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
    · exact bounce_r9_zero_leads hd_lo hbig hvp
  · -- Only possible when `d = 18` and `y = 39` or `y = 40`:
    have hd18 : d = 18 := by omega
    subst hd18
    rcases dec_or (y = 39) with rfl | hy40
    · have hg2 : stepGuards ⟨true, (0, 39 - 3) :: p.1, p.2, 18 - 1, 0, 2 * 18, tl⟩ = true := rfl
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]
      exact chainLeadsUpTo_here (rootInv_of_0B htl (validTail40_of_validSegs40 hvp)
        (by decide) (by decide) (by decide) (by omega) (by omega)
        (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
    · have hy_eq : y = 40 := by omega
      subst hy_eq
      have hg2 : stepGuards ⟨true, (0, 40 - 3) :: p.1, p.2, 18 - 1, 0, 2 * 18, tl⟩ = true := by
        change stepGuards ⟨true, (0, 36 + 1) :: p.1, p.2, 17, 0, 36, tl⟩ = true
        dsimp only [stepGuards]
        rw [if_pos (by decide), decide_eq_true (by decide), if_pos rfl]
        exact hg1 (by decide)
      apply chainLeadsUpTo_step1 hg2
      change ChainLeadsUpTo m1 (stepSegs ⟨true, (0, 36 + 1) :: p.1, p.2, 17, 0, 36, tl⟩) RootInv
      dsimp only [stepSegs]
      rw [if_pos (by decide), decide_eq_true (by decide), if_pos rfl]
      have hds17 : (17 :: tl) = [17] ∨ (17 :: tl) = [17, 0] := by
        rcases htl with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
      exact chainLeadsUpTo_here (rootInv_of_D (d := 17) (by decide) hds17
        (validTail40_of_validSegs40 hvp) (by decide) (by decide) (by decide)
        (by omega) (by omega) (by omega))

-- ============================================================================
-- 1. `rootD_advances` (`RootD s -> ChainAdvances s RootInv`)
-- ============================================================================

theorem x_8_high_leads {N x zl c k : Nat} {segs : List (Nat × Nat)}
    (hx41 : 41 ≤ x) (hv : ValidSegs40 segs zl)
    (hc : (66 ≤ c ∧ k = 1) ∨ (77 ≤ c ∧ 1 ≤ k ∧ k ≤ 2 * c + 3)) :
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, [x, 8]⟩ RootInv := by
  have hc2 : 2 ≤ c := by rcases hc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hk1 : 1 ≤ k := by rcases hc with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
  have hkc : k ≤ 2 * c + 3 := by rcases hc with ⟨_, rfl⟩ | ⟨_, _, h⟩ <;> omega
  have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
  have hox97 : 97 ≤ ox (k + 2 * fzOf segs zl) (c + fzOf segs zl) ∧
      96 ≤ odw (k + 2 * fzOf segs zl) (c + fzOf segs zl) := by
    have h := ox_ge_of_c hc2 hk1 hkc hfz40
    have hc66 : 66 ≤ c := by rcases hc with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    omega
  have hS8_21 : SafeStack 21 [8] := safeStack_d (by decide)
  have hS8 : SafeStack 43 [8] := safeStack_mono (by decide) hS8_21
  have hSx8 : SafeStack 19 [x, 8] :=
    safeStack_cons_ne1 (by decide) hS8_21 (by omega) (by omega)
  have hfb := (excursion_bundle N).1 19 [x, 8] segs zl c k (by decide) hSx8
    (validTail40_of_validSegs40 hv) (by omega) hk1 hkc (by omega) (by omega) (by omega) (by omega)
  refine chainLeadsUpTo_trans hfb ?_
  intro m1 s_mid hm1 hex
  rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
  · exact bounce_y_8_ge46_leads hb (by omega) (by omega)
  · exact amega_pop_step hb hphi38 (by omega) (by omega)
      (hS8_21.2.2 (x - 1) (by omega))
      (fun _ => hS8_21.2.2 (x - 2) (by omega))
      (fun hbig _ _ p1 p2 hvp _ =>
        bounce_d_leads (isBounce_r9 (by omega) hbig hvp) (Or.inl rfl)
          (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩))
      (fun _ _ _ _ p1 p2 hvp _ => by
        have hfp := fzOf_ge_40 hvp
        exact chainLeadsUpTo_here (rootInv_of_D (d := 8) (by decide) (Or.inl rfl)
          (validTail40_of_validSegs40 hvp) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)))
      (fun hy_le _ m2 _ p1 p2 hvp _ => by
        have hfp := fzOf_ge_40 hvp
        have hox124 : 124 ≤ ox (1 + 2 * fzOf p1 p2) (y + fzOf p1 p2) ∧
            123 ≤ odw (1 + 2 * fzOf p1 p2) (y + fzOf p1 p2) := by
          have h := ox_ge_of_c (c := y) (k := 1) (fz := fzOf p1 p2)
            (by omega) (by decide) (by omega) hfp
          omega
        have hSx1 : SafeStack 19 [x - 1, 8] :=
          safeStack_cons_ne1 (by decide) hS8_21 (by omega) (by omega)
        have hfb2 := (excursion_bundle m2).1 19 [x - 1, 8] p1 p2 y 1 (by decide) hSx1
          (validTail40_of_validSegs40 hvp) (by omega) (by decide) (by omega)
          (by omega) (by omega) (by omega) (by omega)
        refine chainLeadsUpTo_trans hfb2 ?_
        intro m3 s_m2 _ hex2
        rcases hex2 with ⟨phi2, hphi2, hb2⟩ | ⟨y2, phi2, hy2, hphi2_38, _, hb2⟩
        · exact bounce_y_8_ge46_leads hb2 (by omega) (by omega)
        · exact amega_pop_step hb2 hphi2_38 (by omega) (by omega)
            (hS8_21.2.2 (x - 1 - 1) (by omega))
            (fun _ => hS8_21.2.2 (x - 1 - 2) (by omega))
            (fun hbig _ _ q1 q2 hvq _ =>
              bounce_d_leads (isBounce_r9 (by omega) hbig hvq) (Or.inl rfl)
                (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩))
            (fun _ _ _ _ q1 q2 hvq _ => by
              have hfq := fzOf_ge_40 hvq
              exact chainLeadsUpTo_here (rootInv_of_D (d := 8) (by decide) (Or.inl rfl)
                (validTail40_of_validSegs40 hvq) (by omega) (by omega) (by omega)
                (by omega) (by omega) (by omega)))
            (fun hy2_le _ m4 _ q1 q2 hvq _ => by
              have hfq := fzOf_ge_40 hvq
              have hx2_49 : 49 ≤ x - 1 - 1 := by omega
              have hlh := (fhigh_bundle m4).2.1 [8] q1 q2 y2 1 (x - 1 - 1)
                (by decide) hS8 hvq (by omega) (by decide) (by omega) hx2_49 (by omega)
              refine chainLeadsUpTo_trans hlh ?_
              intro m5 s_eh _ heh
              rcases heh with ⟨phi3, hphi3, hb3⟩ | ⟨y3, phi3, hy3, hphi3, hb3⟩
              · exact bounce_d_leads hb3 (Or.inl rfl) (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩)
              · exact bounce_y_8_ge46_leads hb3 (by omega) (by omega)))

theorem exitHigh_8_leads {N : Nat} {s : SegState} (heh : ExitHigh [8] s) :
    ChainLeadsUpTo N s RootInv := by
  rcases heh with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi, hb⟩
  · exact bounce_d_leads hb (Or.inl rfl) (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩)
  · exact bounce_y_8_ge46_leads hb (by omega) (by omega)

theorem rootD_advances {s : SegState} (hb0 : s.b = false) (hm0_z : s.mrg = 0) (hr : RootD s) :
    ChainAdvances s RootInv := by
  rcases s with ⟨b, segs, zl, c, k, mrg, ds⟩
  dsimp only at hb0 hm0_z
  subst hb0 hm0_z
  obtain ⟨⟨d, hd8, hds⟩, hvt, hc, hk1, hkc, hfz35, hcz42, hkz73⟩ := hr
  dsimp only at hds hvt hc hk1 hkc hfz35 hcz42 hkz73
  rcases dec_or (ds = [8]) with rfl | hnot8
  · -- Dedicated 1-step unrolling for `ds = [8]` (ensures `46 <= phi` on all `[y, 8]` exits):
    have hS8_21 : SafeStack 21 [8] := safeStack_d (by decide)
    have hS8_43 : SafeStack 43 [8] := safeStack_mono (by decide) hS8_21
    rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73
      have hg : stepGuards ⟨false, [], zl, c, k, 0, [8]⟩ = true := by
        dsimp only [stepGuards]
        rw [goodPhiW_of_ge35 hS8_21.1 (by omega), Bool.true_and]
        dsimp only [GoodPsi]
        have hcz : c + zl - 1 + 1 = c + zl := by omega
        rw [hcz]; exact hS8_21.2.2 (c + zl) (by omega)
      refine ⟨hg, fun N => ?_⟩
      dsimp only [stepSegs]
      have hbc : IsBounce (k + 2 * zl + 2) [c + zl, 8]
          ⟨true, [], 0, k + 2 * zl + 2, 0, 2 * (k + 2 * zl) + 6, [c + zl, 8]⟩ := by
        simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
          (mrg := 2 * (k + 2 * zl) + 6) (ds := [c + zl, 8]) (by omega)
      exact bounce_y_8_ge46_leads hbc (by omega) (by omega)
    · dsimp only [fzOf, ValidTail40] at hvt hfz35 hcz42 hkz73
      have hv_rest : ValidSegs40 rest zl := hvt
      cases m0 with
      | zero =>
        refine ⟨rfl, fun N => ?_⟩
        dsimp only [stepSegs]
        rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
        · have := hv_rest.2
          exact bounce_d_leads (IsBounce.nil (by omega)) (Or.inl rfl)
            (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩)
        · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
          have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
          have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
          cases m1_seg with
          | zero =>
            have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3,
                2 * (c + z0) + 8, [8]⟩ = true := by
              dsimp only [stepGuards]; exact decide_eq_true (by omega)
            apply chainLeadsUpTo_step hg2
            intro m2 _
            dsimp only [stepSegs]
            exact chainLeadsUpTo_trans
              ((fhigh_bundle m2).1 [8] rest2 zl (c + z0 + 3 + z1 + 1) (k + 2 * z0 + 3 + 2 * z1 + 3)
                (by decide) hS8_43 hv_r2 (by omega) (by omega) (by omega) (by omega) (by omega))
              (fun _ _ _ heh => exitHigh_8_leads heh)
          | succ m1' =>
            rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
              | true =>
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [8]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                  exact hS8_21.2.2 (c + z0 + 3 + z1) (by omega)
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_trans
                  ((fhigh_bundle m2).2.1 [8] rest2 zl ((k + 2 * z0 + 3) + m1' + 2 * z1 + 4) 1
                    (c + z0 + 3 + z1) (by decide) hS8_43 hv_r2
                    (by omega) (by decide) (by omega) (by omega) (by omega))
                  (fun _ _ _ heh => exitHigh_8_leads heh)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_d_leads (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega))
                  (Or.inl rfl) (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩)
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
              | true =>
                have h_mrg := of_decide_eq_true hd_mrg
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [8]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_trans
                  ((fhigh_bundle m2).1 [8] rest2 zl (c + z0 + 3 + z1 + 2)
                    ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5)
                    (by decide) hS8_43 hv_r2 (by omega) (by omega) (by omega) (by omega) (by omega))
                  (fun _ _ _ heh => exitHigh_8_leads heh)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_d_leads (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega))
                  (Or.inl rfl) (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩)
      | succ m' =>
        have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
        have hphiw : GoodPhiW (c + z0 - 1) [8] false = true := goodPhiW_of_ge35 hS8_21.1 (by omega)
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, [8]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) [8] false && if 1 = 1 then GoodPsi (c + z0) [8] else _) =
              true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact hS8_21.2.2 (c + z0 + 1) (by omega)
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact x_8_high_leads (by omega) hv_rest (Or.inr ⟨by omega, by decide, by omega⟩)
        · have hpsi_cz : GoodPsi (c + z0 - 1) [8] = true := by
            dsimp only [GoodPsi]
            have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
            rw [hcz_eq]; exact hS8_21.2.2 (c + z0) (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [8]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) [8] false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [8] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact x_8_high_leads (by omega) hv_rest (Or.inr ⟨by omega, by omega, by omega⟩)
          · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
            · have hS_cz : SafeStack 19 [c + z0, 8] :=
                safeStack_cons_ne1 (by decide) hS8_21 (by omega) (by omega)
              have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [8]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [8] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [8] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                      GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: [8]) else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_pos hod_sm]
                exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
              have hm_sub : m' + 1 - 1 = m' := by omega
              rw [hm_sub]
              have hne1_cz : ([c + z0, 8] : List Nat) ≠ [1] := by
                intro h; injection h with _ h2; cases h2
              have hlb := (excursion_bundle N).2 19 [c + z0, 8] rest zl m' 1
                (k + 2 * z0 + 2) 65 0 (by decide) hS_cz (Or.inl hne1_cz) hv_rest
                (by omega) (by decide) (by omega) (by decide) (by omega)
                (by omega) (by omega) (by omega) (by omega)
              refine chainLeadsUpTo_trans hlb ?_
              intro m1 s_mid _ hex
              rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
              · exact bounce_y_8_ge46_leads hb (by omega) (by omega)
              · exact amega_pop_step hb hphi38 (by omega) (by omega)
                  (hS8_21.2.2 (c + z0 - 1) (by omega))
                  (fun _ => hS8_21.2.2 (c + z0 - 2) (by omega))
                  (fun hbig _ _ p1 p2 hvp _ =>
                    bounce_d_leads (isBounce_r9 (by omega) hbig hvp) (Or.inl rfl)
                      (Or.inl ⟨rfl, Or.inr (Or.inr (by omega))⟩))
                  (fun _ _ _ _ p1 p2 hvp _ => by
                    have hfp := fzOf_ge_40 hvp
                    exact chainLeadsUpTo_here (rootInv_of_D (d := 8) (by decide) (Or.inl rfl)
                      (validTail40_of_validSegs40 hvp) (by omega) (by omega) (by omega)
                      (by omega) (by omega) (by omega)))
                  (fun _ _ m2 _ p1 p2 hvp _ =>
                    x_8_high_leads (by omega) hvp (Or.inl ⟨by omega, rfl⟩))
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [8]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [8] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [8] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              have hbc : IsBounce (k + 2 * z0 + 2) [c + z0, 8]
                  ⟨true, (0, (m' - 4) + 1) :: rest, zl, k + 2 * z0 + 2, 0,
                    2 * (k + 2 * z0) + 6, [c + z0, 8]⟩ := by
                have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                  (rest := rest) (ds := [c + z0, 8]) hv_rest (by omega)
                    (by split_ifs <;> omega)
                simpa only [Nat.add_zero] using h
              exact bounce_y_8_ge46_leads hbc (by omega) (by omega)
  · -- General `RootD` (`9 <= d` or `ds = [8, 0]`):
    have hS : SafeStack 21 ds := by
      rcases hds with rfl | rfl
      · exact safeStack_d hd8
      · exact safeStack_d0 hd8
    obtain ⟨hox39, _⟩ := ox_bounds_relaxed hc hk1 hkc hfz35 hcz42 hkz73
    have hadv := fbound_advances (ms :=
      21) (by decide) hS hvt hc hk1 hkc hfz35 hcz42 hkz73 (by omega)
    refine chainAdvances_trans hadv ?_
    intro s' hex N
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · have hphi38 : 38 ≤ phi := by dsimp only [odw] at hphi; omega
      refine bounce_d_leads hb hds ?_
      rcases dec_or (d = 8) with rfl | hd9
      · exact Or.inl ⟨rfl, Or.inr (Or.inr hphi38)⟩
      · rcases dec_or (d = 9) with rfl | hd10
        · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
        · rcases dec_or (d ≤ 18) with hd18 | hd19
          · exact Or.inr (Or.inr (Or.inl ⟨by omega, hd18, by omega, fun _ _ => by omega⟩))
          · rcases dec_or (d = 19) with rfl | hd20
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, hphi38⟩)))
    · obtain ⟨tl, hds_eq, htl, h8_tl⟩ :
          ∃ tl, ds = d :: tl ∧ (tl = [] ∨ tl = [0]) ∧ (d = 8 → tl = [0]) := by
        rcases hds with rfl | rfl
        · exact ⟨[], rfl, Or.inl rfl, fun hd => False.elim (hnot8 (by rw [hd]))⟩
        · exact ⟨[0], rfl, Or.inr rfl, fun _ => rfl⟩
      rw [hds_eq] at hb
      rcases dec_or (d ≤ 18) with hd18 | hd19
      · exact bounce_y_d_small_leads hb hd8 hd18 htl h8_tl (by omega) hphi38
      · have hg1 : GoodDs ((d - 1) :: tl) = true := by
          rcases htl with rfl | rfl
          · exact (safeStack_d (by omega)).2.1
          · exact (safeStack_d0 (by omega)).2.1
        have hg2 : GoodDs ((d - 2) :: tl) = true := by
          rcases htl with rfl | rfl
          · exact (safeStack_d (by omega)).2.1
          · exact (safeStack_d0 (by omega)).2.1
        exact amega_pop_step hb hphi38 (by omega) (by omega) hg1 (fun _ => hg2)
          (fun hbig _ _ p1 p2 hvp _ => by
            rcases htl with rfl | rfl
            · exact bounce_nil_leads (isBounce_r9 (by omega) hbig hvp) (by omega)
            · exact bounce_r9_zero_leads (by omega) hbig hvp)
          (fun _ _ _ _ p1 p2 hvp _ => by
            have hfp := fzOf_ge_40 hvp
            exact chainLeadsUpTo_here (rootInv_of_0B htl (validTail40_of_validSegs40 hvp)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega)))
          (fun _ _ _ _ p1 p2 hvp _ => by
            have hfp := fzOf_ge_40 hvp
            have hds_d1 : ((d - 1) :: tl) = [d - 1] ∨ ((d - 1) :: tl) = [d - 1, 0] := by
              rcases htl with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
            exact chainLeadsUpTo_here (rootInv_of_D (d := d - 1) (by omega) hds_d1
              (validTail40_of_validSegs40 hvp) (by omega) (by decide) (by omega)
              (by omega) (by omega) (by omega)))

-- ============================================================================
-- 2. `rootD1_advances` (`RootD1 s -> ChainAdvances s RootInv`)
-- ============================================================================

theorem exit_d1_leads {N d tx tdw txw : Nat} {s : SegState}
    (hd25 : 25 ≤ d) (htx : 43 ≤ tx) (htdw : 42 ≤ tdw)
    (h25_tx : d = 25 → 57 ≤ tx)
    (hex : Exit tx tdw txw [d, 1] s) :
    ChainLeadsUpTo N s RootInv := by
  rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
  · exact bounce_d1_leads hb hd25 (by omega)
  · rcases dec_or (d = 25) with rfl | hd26
    · have h57 : 57 ≤ tx := h25_tx rfl
      exact r9_pop_step hb hphi38 (by decide) (by omega)
        (fun _ _ p1 p2 hvp _ =>
          bounce_one_leads (isBounce_r9 (by decide) (by omega) hvp) (by decide))
    · exact amega_pop_step hb hphi38 (by omega) (by omega)
        (safeStack_one.2.2 (d - 1) (by omega))
        (fun _ => safeStack_one.2.2 (d - 2) (by omega))
        (fun hbig _ _ p1 p2 hvp _ =>
          bounce_one_leads (isBounce_r9 (by omega) hbig hvp) (by omega))
        (fun _ _ _ _ p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          exact chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 hvp)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by intro h; omega) (fun _ => by omega)))
        (fun _ _ _ _ p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          exact chainLeadsUpTo_here (rootInv_of_D1 (by omega) (validTail40_of_validSegs40 hvp)
            (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)))

theorem rootD1_advances {s : SegState} (hb0 : s.b = false) (hm0_z : s.mrg = 0) (hr : RootD1 s) :
    ChainAdvances s RootInv := by
  rcases s with ⟨b, segs, zl, c, k, mrg, ds⟩
  dsimp only at hb0 hm0_z
  subst hb0 hm0_z
  obtain ⟨⟨d, hd25, hds⟩, hvt, hc, hk1, hkc, hfz40, hcz62, hkz81⟩ := hr
  dsimp only at hds hvt hc hk1 hkc hfz40 hcz62 hkz81
  subst hds
  rcases dec_or (d = 25) with rfl | hd26
  · -- Dedicated 1-step unrolling for `d = 25` (`SafeStack 55 [25, 1]`):
    have hS55 : SafeStack 55 [25, 1] := safeStack_25_1
    have hne1 : ([25, 1] : List Nat) ≠ [1] := by intro h; cases h
    rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf, ValidTail40] at hvt hfz40 hcz62 hkz81
      have hg : stepGuards ⟨false, [], zl, c, k, 0, [25, 1]⟩ = true := by
        dsimp only [stepGuards]
        rw [goodPhiW_of_ge35 hS55.1 (by omega), Bool.true_and]
        dsimp only [GoodPsi]
        have hcz : c + zl - 1 + 1 = c + zl := by omega
        rw [hcz]; exact hS55.2.2 (c + zl) (by omega)
      refine ⟨hg, fun N => ?_⟩
      dsimp only [stepSegs]
      have hbc : IsBounce (k + 2 * zl + 2) [c + zl, 25, 1]
          ⟨true, [], 0, k + 2 * zl + 2, 0, 2 * (k + 2 * zl) + 6, [c + zl, 25, 1]⟩ := by
        simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
          (mrg := 2 * (k + 2 * zl) + 6) (ds := [c + zl, 25, 1]) (by omega)
      exact exit_d1_leads (tx := 57) (tdw := 42) (txw := 0) (by decide) (by decide) (by decide)
        (fun _ => by decide) (Or.inr ⟨c + zl, k + 2 * zl + 2, by omega, by omega, by omega, hbc⟩)
    · dsimp only [fzOf, ValidTail40] at hvt hfz40 hcz62 hkz81
      have hv_rest : ValidSegs40 rest zl := hvt
      cases m0 with
      | zero =>
        refine ⟨rfl, fun N => ?_⟩
        dsimp only [stepSegs]
        rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
        · have := hv_rest.2
          exact bounce_d1_leads (IsBounce.nil (by omega)) (by decide) (by omega)
        · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
          have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
          have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
          cases m1_seg with
          | zero =>
            have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3,
                2 * (c + z0) + 8, [25, 1]⟩ = true := by
              dsimp only [stepGuards]; exact decide_eq_true (by omega)
            apply chainLeadsUpTo_step hg2
            intro m2 _
            dsimp only [stepSegs]
            have hox := ox_ge_of_c (c := c + z0 + 3 + z1 + 1) (k := k + 2 * z0 + 3 + 2 * z1 + 3)
              (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz2_40
            exact chainLeadsUpTo_trans
              ((excursion_bundle m2).1 55 [25, 1] rest2 zl (c + z0 + 3 + z1 + 1)
                (k + 2 * z0 + 3 + 2 * z1 + 3) (by decide) hS55 (validTail40_of_validSegs40 hv_r2)
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
              (fun _ _ _ hex => exit_d1_leads (by decide) (by omega) (by omega)
                (fun _ => by omega) hex)
          | succ m1' =>
            rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
              | true =>
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [25, 1]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                  exact hS55.2.2 (c + z0 + 3 + z1) (by omega)
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_trans
                  ((excursion_bundle m2).2 55 [25, 1] rest2 zl
                    ((k + 2 * z0 + 3) + m1' + 2 * z1 + 4) 1 (c + z0 + 3 + z1) 57 0
                    (by decide) hS55 (Or.inl hne1) hv_r2
                    (by omega) (by decide) (by omega) (by decide) (by omega)
                    (by omega) (by omega) (by omega) (by omega))
                  (fun _ _ _ hex => exit_d1_leads (by decide) (by decide) (by decide)
                    (fun _ => by decide) hex)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_d1_leads
                  (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega))
                  (by decide) (by omega)
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
              | true =>
                have h_mrg := of_decide_eq_true hd_mrg
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [25, 1]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                apply chainLeadsUpTo_step hg2
                intro m2 _
                dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                have hox := ox_ge_of_c (c := c + z0 + 3 + z1 + 2)
                  (k := (k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5)
                  (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz2_40
                exact chainLeadsUpTo_trans
                  ((excursion_bundle m2).1 55 [25, 1] rest2 zl (c + z0 + 3 + z1 + 2)
                    ((k + 2 * z0 + 3) + (m1' + 1) + 2 * z1 + 5)
                    (by decide) hS55 (validTail40_of_validSegs40 hv_r2)
                    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                  (fun _ _ _ hex => exit_d1_leads (by decide) (by omega) (by omega)
                    (fun _ => by omega) hex)
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_d1_leads
                  (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega))
                  (by decide) (by omega)
      | succ m' =>
        have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
        have hphiw : GoodPhiW (c + z0 - 1) [25, 1] false = true :=
          goodPhiW_of_ge35 hS55.1 (by omega)
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, [25, 1]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) [25, 1] false &&
              if 1 = 1 then GoodPsi (c + z0) [25, 1] else _) = true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact hS55.2.2 (c + z0 + 1) (by omega)
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact chainLeadsUpTo_trans
            ((excursion_bundle N).2 55 [25, 1] rest zl (k + 2 * z0 + 4) 1 (c + z0 + 1) 57 0
              (by decide) hS55 (Or.inl hne1) hv_rest
              (by omega) (by decide) (by omega) (by decide) (by omega)
              (by omega) (by omega) (by omega) (by omega))
            (fun _ _ _ hex => exit_d1_leads (by decide) (by decide) (by decide)
              (fun _ => by decide) hex)
        · have hpsi_cz : GoodPsi (c + z0 - 1) [25, 1] = true := by
            dsimp only [GoodPsi]
            have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
            rw [hcz_eq]; exact hS55.2.2 (c + z0) (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [25, 1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) [25, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [25, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact chainLeadsUpTo_trans
              ((excursion_bundle N).2 55 [25, 1] rest zl (k + 2 * z0 + 4) (m' + 2) (c + z0) 57 0
                (by decide) hS55 (Or.inl hne1) hv_rest
                (by omega) (by omega) (by omega) (by decide) (by omega)
                (by omega) (by omega) (by omega) (by omega))
              (fun _ _ _ hex => exit_d1_leads (by decide) (by decide) (by decide)
                (fun _ => by decide) hex)
          · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
            · have hS_cz : SafeStack 19 [c + z0, 25, 1] :=
                safeStack_cons_ne1 hne1 hS55 (by omega) (by omega)
              have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [25, 1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [25, 1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [25, 1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                      GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: [25, 1]) else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_pos hod_sm]
                exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
              have hm_sub : m' + 1 - 1 = m' := by omega
              rw [hm_sub]
              have hne1_cz : ([c + z0, 25, 1] : List Nat) ≠ [1] := by
                intro h; injection h with _ h2; cases h2
              have hlb := (excursion_bundle N).2 19 [c + z0, 25, 1] rest zl m' 1
                (k + 2 * z0 + 2) 65 0 (by decide) hS_cz (Or.inl hne1_cz) hv_rest
                (by omega) (by decide) (by omega) (by decide) (by omega)
                (by omega) (by omega) (by omega) (by omega)
              refine chainLeadsUpTo_trans hlb ?_
              intro m1 s_mid _ hex
              rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
              · exact exit_d1_leads (tx := 57) (tdw := 42) (txw := 0)
                  (by decide) (by decide) (by decide) (fun _ => by decide)
                  (Or.inr ⟨c + z0, phi, by omega, by omega, by omega, hb⟩)
              · exact amega_pop_step hb hphi38 (by omega) (by omega)
                  (hS55.2.2 (c + z0 - 1) (by omega))
                  (fun _ => hS55.2.2 (c + z0 - 2) (by omega))
                  (fun hbig _ _ p1 p2 hvp _ =>
                    bounce_d1_leads (isBounce_r9 (by omega) hbig hvp) (by decide) (by omega))
                  (fun _ _ m2 _ p1 p2 hvp _ => by
                    have hfp := fzOf_ge_40 hvp
                    have hox := ox_ge_of_c (c := c + z0 + 1) (k := y + 2) (fz := fzOf p1 p2)
                      (by omega) (by omega) (by omega) hfp
                    exact chainLeadsUpTo_trans
                      ((excursion_bundle m2).1 55 [25, 1] p1 p2 (c + z0 + 1) (y + 2)
                        (by decide) hS55 (validTail40_of_validSegs40 hvp)
                        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                          (by omega))
                      (fun _ _ _ hex2 => exit_d1_leads (by decide) (by omega) (by omega)
                        (fun _ => by omega) hex2))
                  (fun _ _ m2 _ p1 p2 hvp _ => by
                    have hfp := fzOf_ge_40 hvp
                    exact chainLeadsUpTo_trans
                      ((excursion_bundle m2).2 55 [25, 1] p1 p2 y 1 (c + z0 - 1) 57 0
                        (by decide) hS55 (Or.inl hne1) hvp
                        (by omega) (by decide) (by omega) (by decide) (by omega)
                        (by omega) (by omega) (by omega) (by omega))
                      (fun _ _ _ hex2 => exit_d1_leads (by decide) (by decide) (by decide)
                        (fun _ => by decide) hex2))
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [25, 1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [25, 1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [25, 1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              have hbc : IsBounce (k + 2 * z0 + 2) [c + z0, 25, 1]
                  ⟨true, (0, (m' - 4) + 1) :: rest, zl, k + 2 * z0 + 2, 0,
                    2 * (k + 2 * z0) + 6, [c + z0, 25, 1]⟩ := by
                have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                  (rest := rest) (ds := [c + z0, 25, 1]) hv_rest (by omega)
                    (by split_ifs <;> omega)
                simpa only [Nat.add_zero] using h
              exact exit_d1_leads (tx := 57) (tdw := 42) (txw := 0)
                (by decide) (by decide) (by decide) (fun _ => by decide)
                (Or.inr ⟨c + z0, k + 2 * z0 + 2, by omega, by omega, by omega, hbc⟩)
  · -- General `26 <= d` (`SafeStack 39 [d, 1]`):
    have hS : SafeStack 39 [d, 1] := safeStack_d1 (by omega)
    have hox57 := ox_ge57_of_cz62 hc hk1 hkc hfz40 hcz62 hkz81
    have hadv := fbound_advances (ms := 39) (by decide) hS hvt (by omega) hk1 hkc
      (by omega) (by omega) (by omega) (by omega)
    exact chainAdvances_trans hadv
      (fun _ hex _ => exit_d1_leads hd25 (by omega) (by omega) (fun h25 => False.elim (hd26 h25))
        hex)

-- ============================================================================
-- 3. `root1_advances` (`Root1 s -> ChainAdvances s RootInv`)
-- ============================================================================

theorem pop_47_25_1_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [47, 25, 1] s) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hg_pop : drainPopGuards phi [47, 25, 1] = true := by
    change (true && true && true && decide (phi ≥ 16)) = true
    rw [Bool.true_and, Bool.true_and, Bool.true_and]
    exact decide_eq_true (by omega)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [47, 25, 1] =
      ⟨true, (0, 44) :: p.1, p.2, 24, 0, 50, [1]⟩ := rfl
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfp := fzOf_ge_40 hvp
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep, hdp]
  have hg2 : stepGuards ⟨true, (0, 44) :: p.1, p.2, 24, 0, 50, [1]⟩ = true := rfl
  apply chainLeadsUpTo_step1 hg2
  dsimp only [stepSegs]
  exact chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 hvp)
    (by decide) (by decide) (by decide) (by omega) (by omega)
    (by intro h; omega) (fun _ => by omega))

theorem exit_47_25_1_leads {N tx tdw txw : Nat} {s : SegState}
    (htx99 : 99 ≤ tx) (htdw38 : 38 ≤ tdw)
    (hex : Exit tx tdw txw [47, 25, 1] s) :
    ChainLeadsUpTo N s RootInv := by
  rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
  · exact pop_47_25_1_leads hb (by omega)
  · exact r9_pop_step hb hphi38 (by decide) (by omega)
      (fun _ _ p1 p2 hvp _ =>
        bounce_d1_leads (isBounce_r9 (by decide) (by omega) hvp) (by decide) (by decide))

theorem x_47_25_1_high_leads {N x zl c k : Nat} {segs : List (Nat × Nat)}
    (hx101 : 101 ≤ x) (hv : ValidSegs40 segs zl)
    (hc : (170 ≤ c ∧ k = 1) ∨ (189 ≤ c ∧ 1 ≤ k ∧ k ≤ 2 * c + 3)) :
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, [x, 47, 25, 1]⟩ RootInv := by
  have hc170 : 170 ≤ c := by rcases hc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hk1 : 1 ≤ k := by rcases hc with ⟨_, h⟩ | ⟨_, h, _⟩ <;> omega
  have hkc : k ≤ 2 * c + 3 := by rcases hc with ⟨_, rfl⟩ | ⟨_, _, h⟩ <;> omega
  have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
  have hS47 : SafeStack 99 [47, 25, 1] := safeStack_47_25_1
  have hne1 : ([47, 25, 1] : List Nat) ≠ [1] := by intro h; cases h
  rcases dec_or (105 ≤ x) with hx105 | hx104
  · exact chainLeadsUpTo_trans
      ((excursion_bundle N).2 99 [47, 25, 1] segs zl c k x 101 0
        (by decide) hS47 (Or.inl hne1) hv
        (by omega) hk1 hkc (by decide) (by omega)
        (by omega) (by omega) (by omega) (by omega))
      (fun _ _ _ hex => exit_47_25_1_leads (by decide) (by decide) hex)
  · have hox190 := ox_ge_of_c (by omega) hk1 hkc hfz40
    have hSx : SafeStack 19 [x, 47, 25, 1] :=
      safeStack_cons_ne1 hne1 hS47 (by omega) (by omega)
    have hfb := (excursion_bundle N).1 19 [x, 47, 25, 1] segs zl c k (by decide) hSx
      (validTail40_of_validSegs40 hv) (by omega) hk1 hkc (by omega) (by omega) (by omega) (by omega)
    refine chainLeadsUpTo_trans hfb ?_
    intro m1 s_mid _ hex
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · exact exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
        (Or.inr ⟨x, phi, by omega, by omega, by omega, hb⟩)
    · exact amega_pop_step hb hphi38 (by omega) (by omega)
        (hS47.2.2 (x - 1) (by omega)) (fun _ => hS47.2.2 (x - 2) (by omega))
        (fun hbig _ _ p1 p2 hvp _ =>
          pop_47_25_1_leads (isBounce_r9 (by omega) hbig hvp) (by omega))
        (fun _ _ m2 _ p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          have hox129 := ox_ge_of_c (c := x + 1) (k := y + 2) (fz := fzOf p1 p2)
            (by omega) (by omega) (by omega) hfp
          exact chainLeadsUpTo_trans
            ((excursion_bundle m2).1 99 [47, 25, 1] p1 p2 (x + 1) (y + 2)
              (by decide) hS47 (validTail40_of_validSegs40 hvp)
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ _ _ hex2 => exit_47_25_1_leads (by omega) (by omega) hex2))
        (fun _ _ m2 _ p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          have hox208 := ox_ge_of_c (c := y) (k := 1) (fz := fzOf p1 p2)
            (by omega) (by decide) (by omega) hfp
          rcases dec_or (x = 101) with rfl | hx102
          · exact fbound_force_r9 (x := 100) (d3 := 47) (ds3 := [25, 1]) (by decide)
              (hS47.2.2 100 (by decide)) (hS47.2.2 99 (by decide)) hvp
              (by omega) (by decide) (by omega) (by omega) (by omega)
              (fun _ phi2 _ hphi2 _ hb2 =>
                exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
                  (Or.inr ⟨100, phi2, by decide, by omega, by omega, hb2⟩))
              (fun _ _ _ hb2 => pop_47_25_1_leads hb2 (by decide))
          · have hSx1 : SafeStack 19 [x - 1, 47, 25, 1] :=
              safeStack_cons_ne1 hne1 hS47 (by omega) (by omega)
            have hfb2 := (excursion_bundle m2).1 19 [x - 1, 47, 25, 1] p1 p2 y 1
              (by decide) hSx1 (validTail40_of_validSegs40 hvp)
              (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
            refine chainLeadsUpTo_trans hfb2 ?_
            intro m3 s_m2 _ hex2
            rcases hex2 with ⟨phi2, hphi2, hb2⟩ | ⟨y2, phi2, hy2, hphi2_38, _, hb2⟩
            · exact exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
                (Or.inr ⟨x - 1, phi2, by omega, by omega, by omega, hb2⟩)
            · exact amega_pop_step hb2 hphi2_38 (by omega) (by omega)
                (hS47.2.2 (x - 1 - 1) (by omega)) (fun _ => hS47.2.2 (x - 1 - 2) (by omega))
                (fun hbig _ _ q1 q2 hvq _ =>
                  pop_47_25_1_leads (isBounce_r9 (by omega) hbig hvq) (by omega))
                (fun _ _ m4 _ q1 q2 hvq _ => by
                  have hfq := fzOf_ge_40 hvq
                  have hox129 := ox_ge_of_c (c := x - 1 + 1) (k := y2 + 2) (fz := fzOf q1 q2)
                    (by omega) (by omega) (by omega) hfq
                  exact chainLeadsUpTo_trans
                    ((excursion_bundle m4).1 99 [47, 25, 1] q1 q2 (x - 1 + 1) (y2 + 2)
                      (by decide) hS47 (validTail40_of_validSegs40 hvq)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                    (fun _ _ _ hex3 => exit_47_25_1_leads (by omega) (by omega) hex3))
                (fun _ _ _ _ q1 q2 hvq _ => by
                  have hfq := fzOf_ge_40 hvq
                  have hox224 := ox_ge_of_c (c := y2) (k := 1) (fz := fzOf q1 q2)
                    (by omega) (by decide) (by omega) hfq
                  exact fbound_force_r9 (x := x - 1 - 1) (d3 := 47) (ds3 := [25, 1]) (by omega)
                    (hS47.2.2 (x - 1 - 1) (by omega)) (hS47.2.2 (x - 1 - 1 - 1) (by omega)) hvq
                    (by omega) (by decide) (by omega) (by omega) (by omega)
                    (fun _ phi3 _ hphi3 _ hb3 =>
                      exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
                        (Or.inr ⟨x - 1 - 1, phi3, by omega, by omega, by omega, hb3⟩))
                    (fun _ _ _ hb3 => pop_47_25_1_leads hb3 (by omega))))

theorem stack_47_25_1_leads {N zl c1 : Nat} {segs : List (Nat × Nat)}
    (hv : ValidSegs40 segs zl) (hc1 : 6 ≤ c1)
    (hcz102 : 102 ≤ c1 + fzOf segs zl) (hkz185 : 185 ≤ 1 + 2 * fzOf segs zl) :
    ChainLeadsUpTo N ⟨false, segs, zl, c1, 1, 0, [47, 25, 1]⟩ RootInv := by
  have hS47 : SafeStack 99 [47, 25, 1] := safeStack_47_25_1
  have hne1 : ([47, 25, 1] : List Nat) ≠ [1] := by intro h; cases h
  rcases segs with _ | ⟨⟨z1, m1⟩, rest⟩
  · have := hv.2
    have hg : stepGuards ⟨false, [], zl, c1, 1, 0, [47, 25, 1]⟩ = true := by
      dsimp only [stepGuards]
      rw [goodPhiW_of_ge35 hS47.1 (by omega), Bool.true_and]
      dsimp only [GoodPsi]
      have hcz : c1 + zl - 1 + 1 = c1 + zl := by omega
      rw [hcz]; exact hS47.2.2 (c1 + zl) (by omega)
    apply chainLeadsUpTo_step1 hg
    dsimp only [stepSegs]
    have hbc : IsBounce (1 + 2 * zl + 2) [c1 + zl, 47, 25, 1]
        ⟨true, [], 0, 1 + 2 * zl + 2, 0, 2 * (1 + 2 * zl) + 6, [c1 + zl, 47, 25, 1]⟩ := by
      simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := 1 + 2 * zl + 2) (kb := 0)
        (mrg := 2 * (1 + 2 * zl) + 6) (ds := [c1 + zl, 47, 25, 1]) (by omega)
    exact exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
      (Or.inr ⟨c1 + zl, 1 + 2 * zl + 2, by omega, by omega, by omega, hbc⟩)
  · dsimp only [fzOf] at hcz102 hkz185
    have hv_rest : ValidSegs40 rest zl := validSegs40_tail hv
    cases m1 with
    | zero =>
      have hg1 : stepGuards ⟨false, (z1, 0) :: rest, zl, c1, 1, 0, [47, 25, 1]⟩ = true := rfl
      apply chainLeadsUpTo_step hg1
      intro m_a _
      dsimp only [stepSegs]
      rcases rest with _ | ⟨⟨z2, m2⟩, rest2⟩
      · have := hv_rest.2
        exact pop_47_25_1_leads (IsBounce.nil (by omega)) (by omega)
      · have hz2_40 : 40 ≤ z2 := fzOf_ge_40 hv_rest
        have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
        have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
        cases m2 with
        | zero =>
          have hg2 : stepGuards ⟨true, (z2, 0) :: rest2, zl, c1 + z1 + 3, 1 + 2 * z1 + 3,
              2 * (c1 + z1) + 8, [47, 25, 1]⟩ = true := by
            dsimp only [stepGuards]; exact decide_eq_true (by omega)
          apply chainLeadsUpTo_step hg2
          intro m_b _
          dsimp only [stepSegs]
          have hox := ox_ge_of_c (c := c1 + z1 + 3 + z2 + 1) (k := 1 + 2 * z1 + 3 + 2 * z2 + 3)
            (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz2_40
          exact chainLeadsUpTo_trans
            ((excursion_bundle m_b).1 99 [47, 25, 1] rest2 zl (c1 + z1 + 3 + z2 + 1)
              (1 + 2 * z1 + 3 + 2 * z2 + 3) (by decide) hS47 (validTail40_of_validSegs40 hv_r2)
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            (fun _ _ _ hex => exit_47_25_1_leads (by omega) (by omega) hex)
        | succ m2' =>
          rcases dec_or ((m2' + 1) % 2 = 1) with hm2_od | hm2_ev
          · cases hd_mrg : decide (2 * (c1 + z1) + 8 ≥ (1 + 2 * z1 + 3) + m2') with
            | true =>
              have hg2 : stepGuards ⟨true, (z2, m2' + 1) :: rest2, zl, c1 + z1 + 3,
                  1 + 2 * z1 + 3, 2 * (c1 + z1) + 8, [47, 25, 1]⟩ = true := by
                dsimp only [stepGuards]; rw [if_pos hm2_od, hd_mrg, if_pos rfl]
                exact hS47.2.2 (c1 + z1 + 3 + z2) (by omega)
              apply chainLeadsUpTo_step hg2
              intro m_b _
              dsimp only [stepSegs]; rw [if_pos hm2_od, hd_mrg, if_pos rfl]
              exact x_47_25_1_high_leads (by omega) hv_r2 (Or.inl ⟨by omega, rfl⟩)
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact pop_47_25_1_leads
                (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm2_od]; omega)) (by omega)
          · cases hd_mrg : decide (2 * (c1 + z1) + 8 ≥ (1 + 2 * z1 + 3) + (m2' + 1)) with
            | true =>
              have h_mrg := of_decide_eq_true hd_mrg
              have hg2 : stepGuards ⟨true, (z2, m2' + 1) :: rest2, zl, c1 + z1 + 3,
                  1 + 2 * z1 + 3, 2 * (c1 + z1) + 8, [47, 25, 1]⟩ = true := by
                dsimp only [stepGuards]; rw [if_neg hm2_ev, hd_mrg, if_pos rfl]
              apply chainLeadsUpTo_step hg2
              intro m_b _
              dsimp only [stepSegs]; rw [if_neg hm2_ev, hd_mrg, if_pos rfl]
              have hox := ox_ge_of_c (c := c1 + z1 + 3 + z2 + 2)
                (k := (1 + 2 * z1 + 3) + (m2' + 1) + 2 * z2 + 5)
                (fz := fzOf rest2 zl) (by omega) (by omega) (by omega) hfz2_40
              exact chainLeadsUpTo_trans
                ((excursion_bundle m_b).1 99 [47, 25, 1] rest2 zl (c1 + z1 + 3 + z2 + 2)
                  ((1 + 2 * z1 + 3) + (m2' + 1) + 2 * z2 + 5)
                  (by decide) hS47 (validTail40_of_validSegs40 hv_r2)
                  (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                (fun _ _ _ hex => exit_47_25_1_leads (by omega) (by omega) hex)
            | false =>
              have h_nm := of_decide_eq_false hd_mrg
              exact pop_47_25_1_leads
                (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm2_ev]; omega)) (by omega)
    | succ m' =>
      have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
      have hphiw : GoodPhiW (c1 + z1 - 1) [47, 25, 1] false = true :=
        goodPhiW_of_ge35 hS47.1 (by omega)
      rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
      · have hm0_eq : m' = 0 := by omega
        subst hm0_eq
        have hg : stepGuards ⟨false, (z1, 1) :: rest, zl, c1, 1, 0, [47, 25, 1]⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (c1 + z1 - 1) [47, 25, 1] false &&
            if 1 = 1 then GoodPsi (c1 + z1) [47, 25, 1] else _) = true
          rw [hphiw, Bool.true_and, if_pos rfl]
          exact hS47.2.2 (c1 + z1 + 1) (by omega)
        apply chainLeadsUpTo_step hg
        intro m_a _
        dsimp only [stepSegs]
        change ChainLeadsUpTo m_a (if 1 = 1 then _ else _) _
        rw [if_pos rfl]
        exact x_47_25_1_high_leads (by omega) hv_rest (Or.inl ⟨by omega, rfl⟩)
      · have hpsi_cz : GoodPsi (c1 + z1 - 1) [47, 25, 1] = true := by
          dsimp only [GoodPsi]
          have hcz_eq : c1 + z1 - 1 + 1 = c1 + z1 := by omega
          rw [hcz_eq]; exact hS47.2.2 (c1 + z1) (by omega)
        rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10) with hev_sm | hnot_ev
        · have hg : stepGuards ⟨false, (z1, m' + 1) :: rest, zl, c1, 1, 0, [47, 25, 1]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c1 + z1 - 1) [47, 25, 1] false &&
              if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) [47, 25, 1] &&
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else _) = true
            rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
          apply chainLeadsUpTo_step hg
          intro m_a _
          dsimp only [stepSegs]
          change ChainLeadsUpTo m_a (if m' + 1 = 1 then _ else
            if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else _) _
          rw [if_neg hm_gt1, if_pos hev_sm]
          exact x_47_25_1_high_leads (by omega) hv_rest (Or.inr ⟨by omega, by omega, by omega⟩)
        · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11) with hod_sm | hbig_m
          · have hS_cz : SafeStack 19 [c1 + z1, 47, 25, 1] :=
              safeStack_cons_ne1 hne1 hS47 (by omega) (by omega)
            have hg : stepGuards ⟨false, (z1, m' + 1) :: rest, zl, c1, 1, 0, [47, 25, 1]⟩ = true :=
              by
              dsimp only [stepGuards]
              change (GoodPhiW (c1 + z1 - 1) [47, 25, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) [47, 25, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then
                    GoodDs ((1 + 2 * z1 + 2) :: (c1 + z1) :: [47, 25, 1]) else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_pos hod_sm]
              exact hS_cz.2.2 (1 + 2 * z1 + 2) (by omega)
            apply chainLeadsUpTo_step hg
            intro m_a _
            dsimp only [stepSegs]
            change ChainLeadsUpTo m_a (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
            have hm_sub : m' + 1 - 1 = m' := by omega
            rw [hm_sub]
            have hne1_cz : ([c1 + z1, 47, 25, 1] : List Nat) ≠ [1] := by
              intro h; injection h with _ h2; cases h2
            have hlb := (excursion_bundle m_a).2 19 [c1 + z1, 47, 25, 1] rest zl m' 1
              (1 + 2 * z1 + 2) 170 0 (by decide) hS_cz (Or.inl hne1_cz) hv_rest
              (by omega) (by decide) (by omega) (by decide) (by omega)
              (by omega) (by omega) (by omega) (by omega)
            refine chainLeadsUpTo_trans hlb ?_
            intro m_b s_mid _ hex
            rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
            · exact exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
                (Or.inr ⟨c1 + z1, phi, by omega, by omega, by omega, hb⟩)
            · exact amega_pop_step hb hphi38 (by omega) (by omega)
                (hS47.2.2 (c1 + z1 - 1) (by omega))
                (fun _ => hS47.2.2 (c1 + z1 - 2) (by omega))
                (fun hbig _ _ p1 p2 hvp _ =>
                  pop_47_25_1_leads (isBounce_r9 (by omega) hbig hvp) (by omega))
                (fun _ _ m_c _ p1 p2 hvp _ => by
                  have hfp := fzOf_ge_40 hvp
                  have hox := ox_ge_of_c (c := c1 + z1 + 1) (k := y + 2) (fz := fzOf p1 p2)
                    (by omega) (by omega) (by omega) hfp
                  exact chainLeadsUpTo_trans
                    ((excursion_bundle m_c).1 99 [47, 25, 1] p1 p2 (c1 + z1 + 1) (y + 2)
                      (by decide) hS47 (validTail40_of_validSegs40 hvp)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
                    (fun _ _ _ hex2 => exit_47_25_1_leads (by omega) (by omega) hex2))
                (fun _ _ _ _ p1 p2 hvp _ =>
                  x_47_25_1_high_leads (by omega) hvp (Or.inl ⟨by omega, rfl⟩))
          · have hg : stepGuards ⟨false, (z1, m' + 1) :: rest, zl, c1, 1, 0, [47, 25, 1]⟩ = true :=
            by
              dsimp only [stepGuards]
              change (GoodPhiW (c1 + z1 - 1) [47, 25, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c1 + z1 - 1) [47, 25, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_neg hbig_m]
            apply chainLeadsUpTo_step1 hg
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z1) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
            have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
              dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
            rw [hnorm]
            have hbc : IsBounce (1 + 2 * z1 + 2) [c1 + z1, 47, 25, 1]
                ⟨true, (0, (m' - 4) + 1) :: rest, zl, 1 + 2 * z1 + 2, 0,
                  2 * (1 + 2 * z1) + 6, [c1 + z1, 47, 25, 1]⟩ := by
              have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                (cp1 := 1 + 2 * z1 + 2) (kb := 0) (mrg := 2 * (1 + 2 * z1) + 6)
                (rest := rest) (ds := [c1 + z1, 47, 25, 1]) hv_rest (by omega)
                  (by split_ifs <;> omega)
              simpa only [Nat.add_zero] using h
            exact exit_47_25_1_leads (tx := 99) (tdw := 38) (txw := 0) (by decide) (by decide)
              (Or.inr ⟨c1 + z1, 1 + 2 * z1 + 2, by omega, by omega, by omega, hbc⟩)

theorem root1_advances {s : SegState} (hb0 : s.b = false) (hm0_z : s.mrg = 0) (hr : Root1 s) :
    ChainAdvances s RootInv := by
  rcases s with ⟨b, segs, zl, c, k, mrg, ds⟩
  dsimp only at hb0 hm0_z
  subst hb0 hm0_z
  obtain ⟨hds, hvt, hc5, hk1, hkc, hfz20, hkz45, h25, h26⟩ := hr
  dsimp only at hds hvt hc5 hk1 hkc hfz20 hkz45 h25 h26
  subst hds
  have hS1 : SafeStack 25 [1] := safeStack_one
  rcases dec_or (c + fzOf segs zl = 25) with hcz25 | hcz_ne25
  · obtain ⟨m0, rest, hseg, rfl, rfl, hm0_6, hm0_odd⟩ := h25 hcz25
    subst hseg
    dsimp only [ValidTail40] at hvt
    obtain ⟨m', rfl⟩ : ∃ m', m0 = m' + 1 := ⟨m0 - 1, by omega⟩
    have hm_gt1 : ¬(m' + 1 = 1) := by omega
    have hphiw : GoodPhiW (5 + 20 - 1) [1] false = true := rfl
    have hpsi_cz : GoodPsi (5 + 20 - 1) [1] = true := rfl
    rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10) with hev_sm | hnot_ev
    · have hg : stepGuards ⟨false, (20, m' + 1) :: rest, zl, 5, 5, 0, [1]⟩ = true := by
        dsimp only [stepGuards]
        change (GoodPhiW (5 + 20 - 1) [1] false &&
          if m' + 1 = 1 then _ else GoodPsi (5 + 20 - 1) [1] &&
            if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then true else _) = true
        rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
      refine ⟨hg, fun N => ?_⟩
      dsimp only [stepSegs]
      change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
        if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then _ else _) _
      rw [if_neg hm_gt1, if_pos hev_sm]
      have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hvt
      have hox := ox_ge_of_c (c := 5 + 2 * 20 + 4) (k := m' + 2) (fz := fzOf rest zl)
        (by decide) (by omega) (by omega) hfz1_40
      exact chainLeadsUpTo_trans
        ((excursion_bundle N).1 55 [25, 1] rest zl (5 + 2 * 20 + 4) (m' + 2)
          (by decide) safeStack_25_1 (validTail40_of_validSegs40 hvt)
          (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
        (fun _ _ _ hex => exit_d1_leads (by decide) (by omega) (by omega) (fun _ => by omega) hex)
    · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 11) with hod_sm | hbig_m
      · have hg : stepGuards ⟨false, (20, m' + 1) :: rest, zl, 5, 5, 0, [1]⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (5 + 20 - 1) [1] false &&
            if m' + 1 = 1 then _ else GoodPsi (5 + 20 - 1) [1] &&
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then true else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 11 then
                GoodDs [47, 25, 1] else true) = true
          rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
            if_neg hnot_ev, if_pos hod_sm]
          rfl
        refine ⟨hg, fun N => ?_⟩
        dsimp only [stepSegs]
        change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
          if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then _ else
          if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 11 then _ else _) _
        rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
        have hm_sub : m' + 1 - 1 = m' := by omega
        rw [hm_sub]
        obtain ⟨h102, h185⟩ := hm0_odd hod_sm.1
        rw [hm_sub] at h102
        exact stack_47_25_1_leads hvt (by omega) h102 h185
      · have hg : stepGuards ⟨false, (20, m' + 1) :: rest, zl, 5, 5, 0, [1]⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (5 + 20 - 1) [1] false &&
            if m' + 1 = 1 then _ else GoodPsi (5 + 20 - 1) [1] &&
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then true else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 11 then _ else true) = true
          rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
            if_neg hnot_ev, if_neg hbig_m]
        refine ⟨hg, fun N => ?_⟩
        dsimp only [stepSegs]
        change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
          if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 10 then _ else
          if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (5 + 2 * 20) + 11 then _ else _) _
        rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
        have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
          dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
        rw [hnorm]
        have hbc : IsBounce 47 [25, 1]
            ⟨true, (0, (m' - 4) + 1) :: rest, zl, 47, 0, 96, [25, 1]⟩ := by
          have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
            (cp1 := 47) (kb := 0) (mrg := 96)
            (rest := rest) (ds := [25, 1]) hvt (by decide)
              (by split_ifs <;> omega)
          simpa only [Nat.add_zero] using h
        exact bounce_d1_leads hbc (by decide) (by decide)
  · -- `26 <= c + fz`:
    have hcz26 : 26 ≤ c + fzOf segs zl := by omega
    have hkz47 : 47 ≤ k + 2 * fzOf segs zl := h26 hcz26
    rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf, ValidTail40] at hvt hfz20 hcz26 hkz47
      have hg : stepGuards ⟨false, [], zl, c, k, 0, [1]⟩ = true := by
        dsimp only [stepGuards]
        have hpw : GoodPhiW (c + zl - 1) [1] false = true := by
          dsimp only [GoodPhiW]; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
          exact decide_eq_true (by omega)
        rw [hpw, Bool.true_and]
        dsimp only [GoodPsi]
        have hcz : c + zl - 1 + 1 = c + zl := by omega
        rw [hcz]; exact hS1.2.2 (c + zl) (by omega)
      refine ⟨hg, fun N => ?_⟩
      dsimp only [stepSegs]
      have hbc : IsBounce (k + 2 * zl + 2) [c + zl, 1]
          ⟨true, [], 0, k + 2 * zl + 2, 0, 2 * (k + 2 * zl) + 6, [c + zl, 1]⟩ := by
        simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2) (kb := 0)
          (mrg := 2 * (k + 2 * zl) + 6) (ds := [c + zl, 1]) (by omega)
      exact bounce_d1_leads hbc (by omega) (by omega)
    · dsimp only [fzOf, ValidTail40] at hvt hfz20 hcz26 hkz47
      have hv_rest : ValidSegs40 rest zl := hvt
      cases m0 with
      | zero =>
        refine ⟨rfl, fun N => ?_⟩
        dsimp only [stepSegs]
        rcases rest with _ | ⟨⟨z1, m1_seg⟩, rest2⟩
        · have := hv_rest.2
          exact bounce_one_leads (IsBounce.nil (by omega)) (by omega)
        · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
          have hv_r2 : ValidSegs40 rest2 zl := validSegs40_tail hv_rest
          have hfz2_40 : 40 ≤ fzOf rest2 zl := fzOf_ge_40 hv_r2
          cases m1_seg with
          | zero =>
            have hg2 : stepGuards ⟨true, (z1, 0) :: rest2, zl, c + z0 + 3, k + 2 * z0 + 3,
                2 * (c + z0) + 8, [1]⟩ = true := by
              dsimp only [stepGuards]; exact decide_eq_true (by omega)
            apply chainLeadsUpTo_step1 hg2
            dsimp only [stepSegs]
            exact chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 hv_r2)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by intro h; omega) (fun _ => by omega))
          | succ m1' =>
            rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
              | true =>
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [1]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                  exact hS1.2.2 (c + z0 + 3 + z1) (by omega)
                apply chainLeadsUpTo_step1 hg2
                dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_here (rootInv_of_D1 (by omega)
                  (validTail40_of_validSegs40 hv_r2)
                  (by omega) (by decide) (by omega) (by omega) (by omega) (by omega))
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_one_leads
                  (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega)) (by omega)
            · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
              | true =>
                have h_mrg := of_decide_eq_true hd_mrg
                have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: rest2, zl, c + z0 + 3,
                    k + 2 * z0 + 3, 2 * (c + z0) + 8, [1]⟩ = true := by
                  dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                apply chainLeadsUpTo_step1 hg2
                dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
                exact chainLeadsUpTo_here (rootInv_of_1 (validTail40_of_validSegs40 hv_r2)
                  (by omega) (by omega) (by omega) (by omega) (by omega)
                  (by intro h; omega) (fun _ => by omega))
              | false =>
                have h_nm := of_decide_eq_false hd_mrg
                exact bounce_one_leads
                  (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega)) (by omega)
      | succ m' =>
        have hfz1_40 : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
        have hphiw : GoodPhiW (c + z0 - 1) [1] false = true := by
          dsimp only [GoodPhiW]; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
          exact decide_eq_true (by omega)
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, [1]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) [1] false &&
              if 1 = 1 then GoodPsi (c + z0) [1] else _) = true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact hS1.2.2 (c + z0 + 1) (by omega)
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_D1 (by omega)
            (validTail40_of_validSegs40 hv_rest)
            (by omega) (by decide) (by omega) (by omega) (by omega) (by omega))
        · have hpsi_cz : GoodPsi (c + z0 - 1) [1] = true := by
            dsimp only [GoodPsi]
            have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
            rw [hcz_eq]; exact hS1.2.2 (c + z0) (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) [1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact chainLeadsUpTo_here (rootInv_of_D1 (by omega)
              (validTail40_of_validSegs40 hv_rest)
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
          · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
            · have hS_cz : SafeStack 39 [c + z0, 1] := safeStack_d1 hcz26
              have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                      GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: [1]) else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_pos hod_sm]
                exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
              have hm_sub : m' + 1 - 1 = m' := by omega
              rw [hm_sub]
              have hne1_cz : ([c + z0, 1] : List Nat) ≠ [1] := by
                intro h; injection h with _ h2; cases h2
              exact chainLeadsUpTo_trans
                ((excursion_bundle N).2 39 [c + z0, 1] rest zl m' 1
                  (k + 2 * z0 + 2) 43 0 (by decide) hS_cz (Or.inl hne1_cz) hv_rest
                  (by omega) (by decide) (by omega) (by decide) (by omega)
                  (by omega) (by omega) (by omega) (by omega))
                (fun _ _ _ hex => exit_d1_leads (by omega) (by decide) (by decide)
                  (fun h25 => False.elim (by omega)) hex)
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) [1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              have hbc : IsBounce (k + 2 * z0 + 2) [c + z0, 1]
                  ⟨true, (0, (m' - 4) + 1) :: rest, zl, k + 2 * z0 + 2, 0,
                    2 * (k + 2 * z0) + 6, [c + z0, 1]⟩ := by
                have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                  (rest := rest) (ds := [c + z0, 1]) hv_rest (by omega)
                    (by split_ifs <;> omega)
                simpa only [Nat.add_zero] using h
              exact bounce_d1_leads hbc (by omega) (by omega)


-- ============================================================================
-- Section 5g.3d: Root31, Root0, Global Root Advancement, and `inv_s0`
-- ============================================================================

theorem goodPhiW_31 {w : Nat} (hw : 15 ≤ w) : GoodPhiW w [3, 1] false = true := by
  dsimp only [GoodPhiW]
  rw [if_neg (by intro h; injection h with _ h2; cases h2),
      if_neg (by intro h; injection h with _ h2; cases h2),
      if_neg (by intro h; injection h with _ h2; cases h2),
      if_neg (by intro h; cases h)]
  change (if decide (3 ≥ 25) = true then _ else if false = true then _ else decide (w ≥ 15)) = true
  rw [if_neg (by decide), if_neg Bool.false_ne_true]
  exact decide_eq_true hw

theorem bounce_19_31_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [19, 3, 1] s) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hg_pop : drainPopGuards phi [19, 3, 1] = true := by
    have hnrst : isDrainRstDs [19, 3, 1] = false := rfl
    have hnr0 : isRank0 [19, 3, 1] = false := rfl
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [19, 3, 1] =
      ⟨true, (0, 16) :: p.1, p.2, 2, 0, 6, [1]⟩ := rfl
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hg_b1 : stepGuards ⟨true, (0, 16) :: p.1, p.2, 2, 0, 6, [1]⟩ = true := rfl
  have hs_b1 : stepSegs ⟨true, (0, 16) :: p.1, p.2, 2, 0, 6, [1]⟩ =
      ⟨true, (5, 8) :: p.1, p.2, 2, 0, 6, []⟩ := rfl
  apply chainLeadsUpTo_step hg_b1
  intro m2 _
  rw [hs_b1]
  have hg_b2 : stepGuards ⟨true, (5, 8) :: p.1, p.2, 2, 0, 6, []⟩ = true := rfl
  have hs_b2 : stepSegs ⟨true, (5, 8) :: p.1, p.2, 2, 0, 6, []⟩ =
      ⟨false, (9, 0) :: p.1, p.2, 1, 1, 0, []⟩ := rfl
  apply chainLeadsUpTo_step1 hg_b2
  rw [hs_b2]
  exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvp
    (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
    (by intro h; dsimp only [fzOf] at h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩)
    (by intro _ _ _ _ hcz9; dsimp only [fzOf] at hcz9; omega))

theorem bounce_cz_31_even_extra {N cz phi : Nat} {s : SegState}
    (hb : IsBounce phi [cz, 3, 1] s)
    (hcases : (22 ≤ cz ∧ cz % 2 = 0 ∧ 49 ≤ phi) ∨
              (26 ≤ cz ∧ cz % 2 = 0 ∧ 45 ≤ phi)) :
    ChainLeadsUpTo N s RootInv := by
  have hcz22 : 22 ≤ cz := by rcases hcases with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hphi45 : 45 ≤ phi := by rcases hcases with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> omega
  have hnrst : isDrainRstDs [cz, 3, 1] = false := rfl
  have hnr0 : isRank0 [cz, 3, 1] = false := by
    rcases cz with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi [cz, 3, 1] = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (cz ≥ 3 ∧ 3 ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (cz % 2 = 0 ∧ cz ≤ 2 * 3 + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (cz % 2 = 0 ∧ cz + 14 ≤ 2 * 3) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [cz, 3, 1] =
      ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      if_neg (by rintro ⟨h31, _, _⟩; cases h31)]
    have hnorm : normSeg 0 (cz - 3) = (0, cz - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp : phi + 2 ≤ fzOf p.1 p.2 := fzOf_pushSeg_ge hp (phi + 2) m_rem rest zl
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hg_b1 : stepGuards ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ = true := by
    have hsub : cz - 3 = (cz - 4) + 1 := by omega
    rw [hsub]; dsimp only [stepGuards]
    rcases dec_or (((cz - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs_b1 : stepSegs ⟨true, (0, cz - 3) :: p.1, p.2, 2, 0, 6, [1]⟩ =
      ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ := by
    have hsub : cz - 3 = (cz - 4) + 1 := by omega
    have hm_eq : 0 + ((cz - 4) + 1) - (6 + 2) = (cz - 12) + 1 := by omega
    have h11 : cz - 11 = (cz - 12) + 1 := by omega
    rw [hsub, h11]; dsimp only [stepSegs]
    rcases dec_or (((cz - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
  apply chainLeadsUpTo_step hg_b1
  intro m2 _
  rw [hs_b1]
  have hg_b2 : stepGuards ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ = true := by
    have hsub : cz - 11 = (cz - 12) + 1 := by omega
    rw [hsub]; dsimp only [stepGuards]
    rcases dec_or (((cz - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; rfl
    · rw [if_neg hev, decide_eq_false (by omega)]; rfl
  have hs_b2 : stepSegs ⟨true, (5, cz - 11) :: p.1, p.2, 2, 0, 6, []⟩ =
      ⟨false, (8, cz - 19) :: p.1, p.2, 1, 1, 0, []⟩ := by
    have hsub : cz - 11 = (cz - 12) + 1 := by omega
    have hm_eq : 0 + ((cz - 12) + 1) - (6 + 2) = (cz - 20) + 1 := by omega
    have h19 : cz - 19 = (cz - 20) + 1 := by omega
    rw [hsub, h19]; dsimp only [stepSegs]
    rcases dec_or (((cz - 12) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), hm_eq]; rfl
    · rw [if_neg hev, decide_eq_false (by omega), hm_eq]; rfl
  apply chainLeadsUpTo_step1 hg_b2
  rw [hs_b2]
  apply chainLeadsUpTo_here
  refine rootInv_of_0B (Or.inl rfl) hvp
    (by decide) (by decide) (by decide) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
    (by intro h; cases h) (fun _ => Or.inl ⟨rfl, rfl⟩) ?_
  intro z0 m0 r hseg _ _ _
  injection hseg with hhd htl
  injection hhd with hz0 hm0
  subst hz0 hm0 htl
  rcases hcases with ⟨_, _, hphi49⟩ | ⟨hcz26, hcz_ev, _⟩
  · exact ⟨by omega, by omega, fun hlt => False.elim (by omega)⟩
  · exact ⟨by omega, by omega, fun hlt => by omega⟩

theorem bounce_cz_31_ge25_leads {N cz phi : Nat} {s : SegState}
    (hb : IsBounce phi [cz, 3, 1] s) (hcz25 : 25 ≤ cz) (hphi45 : 45 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  rcases dec_or (cz % 2 = 1) with hod | hev
  · exact bounce_cz_31_leads hb (Or.inr (Or.inl ⟨by omega, hod, by omega⟩))
  · exact bounce_cz_31_even_extra hb (Or.inr ⟨by omega, by omega, hphi45⟩)

theorem x_31_high_aux (d : Nat) :
    ∀ N x segs zl c k,
      23 ≤ x → x - 23 ≤ d →
      ValidSegs40 segs zl →
      40 ≤ c → 1 ≤ k → k ≤ 2 * c + 3 →
      ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, [x, 3, 1]⟩ RootInv := by
  induction d with
  | zero =>
    intro N x segs zl c k hx23 hxd hv hc40 hk1 hkc
    have hx_eq : x = 23 := by omega
    subst hx_eq
    have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
    obtain ⟨hox, hodw⟩ := ox_ge_of_c (by omega) hk1 hkc hfz40
    have hS : SafeStack 19 [23, 3, 1] :=
      safeStack_cons_ne1 (by decide) safeStack_31 (by decide) (by decide)
    have hfb := (excursion_bundle N).1 19 [23, 3, 1] segs zl c k (by decide) hS
      (validTail40_of_validSegs40 hv) (by omega) hk1 hkc
      (by omega) (by omega) (by omega) (by omega)
    refine chainLeadsUpTo_trans hfb ?_
    intro m1 s_mid hm1 hex
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · exact bounce_cz_31_leads hb (Or.inr (Or.inl ⟨by decide, by decide, by omega⟩))
    · exact r9_pop_step hb hphi38 (by decide) (by omega)
        (fun m2 _ p1 p2 hvp _ => bounce_31_leads (isBounce_r9 (by decide) (by omega) hvp) (by
          decide))
  | succ d ih =>
    intro N x segs zl c k hx23 hxd hv hc40 hk1 hkc
    have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
    obtain ⟨hox, hodw⟩ := ox_ge_of_c (by omega) hk1 hkc hfz40
    have hS : SafeStack 19 [x, 3, 1] :=
      safeStack_cons_ne1 (by decide) safeStack_31 (by omega) (by omega)
    have hfb := (excursion_bundle N).1 19 [x, 3, 1] segs zl c k (by decide) hS
      (validTail40_of_validSegs40 hv) (by omega) hk1 hkc
      (by omega) (by omega) (by omega) (by omega)
    refine chainLeadsUpTo_trans hfb ?_
    intro m1 s_mid hm1 hex
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · rcases dec_or (x % 2 = 1) with hod | hev
      · exact bounce_cz_31_leads hb (Or.inr (Or.inl ⟨by omega, hod, by omega⟩))
      · exact bounce_cz_31_even_extra hb (Or.inl ⟨by omega, by omega, by omega⟩)
    · exact amega_pop_step hb hphi38 (by omega) (by omega)
        (safeStack_31.2.2 (x - 1) (by omega))
        (fun _ => safeStack_31.2.2 (x - 2) (by omega))
        (fun hbig _ _ p1 p2 hvp _ =>
          bounce_31_leads (isBounce_r9 (by omega) hbig hvp) (by omega))
        (fun hy_le _ _ _ p1 p2 hvp _ => by
          have hfp := fzOf_ge_40 hvp
          refine chainLeadsUpTo_here (rootInv_of_31B rfl (validTail40_of_validSegs40 hvp)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_)
          intro z0 m0 r hseg _ _ _
          have hz0 : fzOf p1 p2 = z0 := by rw [hseg]; rfl
          exact Or.inr (by omega))
        (fun hy_le _ m2 _ p1 p2 hvp _ =>
          ih m2 (x - 1) p1 p2 y 1 (by omega) (by omega) hvp (by omega) (by decide) (by omega))

theorem x_31_high_leads {N x : Nat} {segs : List (Nat × Nat)} {zl c k : Nat}
    (hx20 : 20 ≤ x) (hv : ValidSegs40 segs zl)
    (hc40 : 40 ≤ c) (hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) :
    ChainLeadsUpTo N ⟨false, segs, zl, c, k, 0, [x, 3, 1]⟩ RootInv := by
  rcases dec_or (x ≤ 22) with hx22 | hx23
  · have hfz40 : 40 ≤ fzOf segs zl := fzOf_ge_40 hv
    obtain ⟨hox, hodw⟩ := ox_ge_of_c (by omega) hk1 hkc hfz40
    have hS : SafeStack 39 [x, 3, 1] := safeStack_x_31 hx20 hx22
    have hfb := (excursion_bundle N).1 39 [x, 3, 1] segs zl c k (by decide) hS
      (validTail40_of_validSegs40 hv) (by omega) hk1 hkc
      (by omega) (by omega) (by omega) (by omega)
    refine chainLeadsUpTo_trans hfb ?_
    intro m1 s_mid hm1 hex
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · rcases dec_or (x = 22) with rfl | hx2021
      · exact bounce_cz_31_even_extra hb (Or.inl ⟨by decide, by decide, by omega⟩)
      · exact bounce_cz_31_leads hb (Or.inl ⟨by omega, by omega⟩)
    · exact r9_pop_step hb hphi38 (by omega) (by omega)
        (fun _ _ p1 p2 hvp _ => bounce_31_leads (isBounce_r9 (by omega) (by omega) hvp) (by omega))
  · exact x_31_high_aux (x - 23) N x segs zl c k (by omega) (Nat.le_refl _) hv hc40 hk1 hkc

theorem pop_z_cz_31_leads {N z cz phi : Nat} {s : SegState}
    (hb : IsBounce phi [z, cz, 3, 1] s)
    (hz44 : 44 ≤ z) (hcz25 : 25 ≤ cz) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  exact amega_pop_step hb hphi38 (by omega) (by omega)
    (safeStack_31.2.2 (cz - 1) (by omega))
    (fun _ => safeStack_31.2.2 (cz - 2) (by omega))
    (fun hbig _ _ p1 p2 hvp _ =>
      bounce_31_leads (isBounce_r9 (by omega) hbig hvp) (by omega))
    (fun _ _ _ _ p1 p2 hvp _ => by
      have hfp := fzOf_ge_40 hvp
      refine chainLeadsUpTo_here (rootInv_of_31B rfl (validTail40_of_validSegs40 hvp)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_)
      intro z0 m0 r hseg _ _ _
      have hz0 : fzOf p1 p2 = z0 := by rw [hseg]; rfl
      exact Or.inr (by omega))
    (fun _ _ m2 _ p1 p2 hvp _ =>
      x_31_high_leads (by omega) hvp (by omega) (by decide) (by omega))

theorem loop_k1_gen {N x1 d3 : Nat} {ds3 : List Nat} {segs : List (Nat × Nat)} {zl c1 : Nat}
    {P : SegState → Prop}
    (hx_lo : 21 ≤ x1) (hx_hi : x1 ≤ 47)
    (hS1 : SafeStack 19 (x1 :: d3 :: ds3))
    (hg_x1_1 : GoodDs ((x1 - 1) :: d3 :: ds3) = true)
    (hg_x1_2 : GoodDs ((x1 - 2) :: d3 :: ds3) = true)
    (hv : ValidSegs40 segs zl) (hc1 : 2 ≤ c1)
    (h_top : ∀ m z phi, m ≤ N → (z = x1 ∨ z = x1 - 1) → 38 ≤ phi → ∀ s',
      IsBounce phi (z :: d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_b1 : ∀ m, m < N → ∀ s', IsBounce (x1 - 1) (d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_b2 : ∀ m, m < N → ∀ s', IsBounce (x1 - 2) (d3 :: ds3) s' → ChainLeadsUpTo m s' P)
    (h_r10 : ∀ m c' k' p1 p2, m < N → c' = x1 + 1 → 41 ≤ k' → k' ≤ 2 * c' + 3 →
      ValidSegs40 p1 p2 → ChainLeadsUpTo m ⟨false, p1, p2, c', k', 0, d3 :: ds3⟩ P) :
    ChainLeadsUpTo N ⟨false, segs, zl, c1, 1, 0, x1 :: d3 :: ds3⟩ P := by
  have hne1_1 : (x1 :: d3 :: ds3) ≠ [1] := by intro h; injection h with _ h2; cases h2
  have hb := fbound_k1_boost hne1_1 hS1 hv hc1 (N := N)
  refine chainLeadsUpTo_trans hb ?_
  intro m1 s_mid hm1 hex
  rcases hex with ⟨phi, hphi38, hsb⟩ | ⟨y1, phi1, hy1_39, hphi1_38, hyw1, hsb⟩
  · exact h_top m1 x1 phi hm1 (Or.inl rfl) hphi38 s_mid hsb
  · exact amega_pop_step hsb hphi1_38 (by omega) (by omega) hg_x1_1 (fun _ => hg_x1_2)
      (fun hbig m2 hm2 p1 p2 hvp _ =>
        h_b1 m2 (Nat.lt_of_lt_of_le hm2 hm1) _ (isBounce_r9 (by omega) hbig hvp))
      (fun _ _ m2 hm2 p1 p2 hvp _ =>
        h_r10 m2 (x1 + 1) (y1 + 2) p1 p2 (Nat.lt_of_lt_of_le hm2 hm1)
          rfl (by omega) (by omega) hvp)
      (fun hy1_le _ m2 hm2 p1 p2 hvp hfzp => by
        have hfp := fzOf_ge_40 hvp
        have hox99 := arith_boost_cz (c := y1) (fz := fzOf p1 p2) (cz_lo := 109) (ox_lo := 99)
          (by omega) hfp (by omega) (Or.inl ⟨rfl, rfl⟩)
        exact fbound_force_r9 (x := x1 - 1) (d3 := d3) (ds3 := ds3) (by omega)
          hg_x1_1 hg_x1_2 hvp (by omega) (by omega) (by omega) (by omega) (by omega)
          (fun m3 phi2 hm3 hphi2 s' hb2 =>
            h_top m3 (x1 - 1) phi2 (Nat.le_trans hm3 (Nat.le_of_lt (Nat.lt_of_lt_of_le hm2 hm1)))
              (Or.inr rfl) (by omega) s' hb2)
          (fun m3 hm3 s' hb2 =>
            h_b2 m3 (Nat.lt_trans hm3 (Nat.lt_of_lt_of_le hm2 hm1)) s' hb2))

theorem step_m0_zero_31_advances {z0 zl c k : Nat} {rest : List (Nat × Nat)}
    (hv_rest : ValidSegs40 rest zl)
    (_hc : 2 ≤ c) (hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (hcz20 : 20 ≤ c + z0) :
    ChainAdvances ⟨false, (z0, 0) :: rest, zl, c, k, 0, [3, 1]⟩ RootInv := by
  refine ⟨rfl, fun N => ?_⟩
  dsimp only [stepSegs]
  rcases rest with _ | ⟨⟨z1, m1_seg⟩, r2⟩
  · have hzl230 : 230 ≤ zl := hv_rest.2
    exact bounce_31_leads (IsBounce.nil (by omega)) (by omega)
  · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
    have hv_r2 : ValidSegs40 r2 zl := validSegs40_tail hv_rest
    have hfz2_40 : 40 ≤ fzOf r2 zl := fzOf_ge_40 hv_r2
    cases m1_seg with
    | zero =>
      have hg2 : stepGuards ⟨true, (z1, 0) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
          2 * (c + z0) + 8, [3, 1]⟩ = true := by
        dsimp only [stepGuards]; exact decide_eq_true (by omega)
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]
      refine chainLeadsUpTo_here (rootInv_of_31B rfl (validTail40_of_validSegs40 hv_r2)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_)
      intro z2 m2 r3 hseg _ _ _
      have hz2 : fzOf r2 zl = z2 := by rw [hseg]; rfl
      exact Or.inr (by omega)
    | succ m1' =>
      rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
      · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
        | true =>
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
              2 * (c + z0) + 8, [3, 1]⟩ = true := by
            dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
            exact safeStack_31.2.2 (c + z0 + 3 + z1) (by omega)
          apply chainLeadsUpTo_step hg2
          intro m2 _
          dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
          exact x_31_high_leads (by omega) hv_r2 (by omega) (by decide) (by omega)
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_31_leads
            (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega)) (by omega)
      · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
        | true =>
          have h_mrg := of_decide_eq_true hd_mrg
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
              2 * (c + z0) + 8, [3, 1]⟩ = true := by
            dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
          refine chainLeadsUpTo_here (rootInv_of_31B rfl (validTail40_of_validSegs40 hv_r2)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_)
          intro z2 m2 r3 hseg _ _ _
          have hz2 : fzOf r2 zl = z2 := by rw [hseg]; rfl
          exact Or.inr (by omega)
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_31_leads
            (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega)) (by omega)

theorem root31A_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root31A s) :
    ChainAdvances s RootInv := by
  obtain ⟨hds, hvt, hc, hk, hcases⟩ := hr
  rcases s with ⟨b, segs, zl, cp1, kb, mrg, ds⟩
  dsimp only at hb hmrg hds hvt hc hk hcases
  subst hb hmrg hds hc hk
  rcases hcases with hfz | hfz | ⟨rest, rfl⟩
  all_goals (try exact step_m0_zero_31_advances hvt (by decide) (by decide) (by decide) (by decide))
  all_goals
    rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf, ValidTail40] at hvt hfz; omega
    · dsimp only [fzOf, ValidTail40] at hvt hfz
      have hv_rest : ValidSegs40 rest zl := hvt
      cases m0 with
      | zero =>
        exact step_m0_zero_31_advances hv_rest (by decide) (by decide) (by decide) (by omega)
      | succ m' =>
        have hphiw : GoodPhiW (2 + z0 - 1) [3, 1] false = true := goodPhiW_31 (by omega)
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, 2, 1, 0, [3, 1]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (2 + z0 - 1) [3, 1] false &&
              if 1 = 1 then GoodPsi (2 + z0) [3, 1] else _) = true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact safeStack_31.2.2 (2 + z0 + 1) (by omega)
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact x_31_high_leads (by omega) hv_rest (by omega) (by decide) (by omega)
        · have hpsi_cz : GoodPsi (2 + z0 - 1) [3, 1] = true := by
            dsimp only [GoodPsi]
            have hcz_eq : 2 + z0 - 1 + 1 = 2 + z0 := by omega
            rw [hcz_eq]; exact safeStack_31.2.2 (2 + z0) (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, 2, 1, 0, [3, 1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (2 + z0 - 1) [3, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (2 + z0 - 1) [3, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact x_31_high_leads (by omega) hv_rest (by omega) (by omega) (by omega)
          · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 11) with hod_sm | hbig_m
            · have hS_cz : SafeStack 27 [2 + z0, 3, 1] := by
                rcases dec_or (z0 = 18) with rfl | hz19
                · exact safeStack_20_3_1
                · have hz_eq : z0 = 19 := by omega
                  subst hz_eq
                  exact safeStack_mono (by decide)
                    (safeStack_cons_ne1 (by decide) safeStack_31 (by decide) (by decide))
              have hne1_cz : ([2 + z0, 3, 1] : List Nat) ≠ [1] := by
                intro h; injection h with _ h2; cases h2
              have hS1 : SafeStack 19 [1 + 2 * z0 + 2, 2 + z0, 3, 1] :=
                safeStack_cons_ne1 hne1_cz hS_cz (by omega) (by omega)
              have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, 2, 1, 0, [3, 1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (2 + z0 - 1) [3, 1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (2 + z0 - 1) [3, 1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 11 then
                      GoodDs ((1 + 2 * z0 + 2) :: (2 + z0) :: [3, 1]) else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_pos hod_sm]
                exact hS_cz.2.2 (1 + 2 * z0 + 2) (by omega)
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
              have hm_sub : m' + 1 - 1 = m' := by omega
              rw [hm_sub]
              refine loop_k1_gen (by omega) (by omega) hS1
                (hS_cz.2.2 (1 + 2 * z0 + 2 - 1) (by omega))
                (hS_cz.2.2 (1 + 2 * z0 + 2 - 2) (by omega))
                hv_rest (by omega) ?_ ?_ ?_ ?_
              · intro m1 z phi _ hz hphi38 s' hbz
                refine amega_pop_step hbz hphi38 (by omega) (by omega)
                  (safeStack_31.2.2 (2 + z0 - 1) (by omega))
                  (by intro hbad; omega)
                  (fun hbig => False.elim (by omega))
                  (fun _ _ _ _ p1 p2 hvp _ => by
                    have hfp := fzOf_ge_40 hvp
                    refine chainLeadsUpTo_here (rootInv_of_31B rfl (validTail40_of_validSegs40 hvp)
                      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_)
                    intro z2 m2 r3 hseg _ _ _
                    have hz2 : fzOf p1 p2 = z2 := by rw [hseg]; rfl
                    exact Or.inr (by omega))
                  (fun _ _ m2 _ p1 p2 hvp _ => by
                    have hfp := fzOf_ge_40 hvp
                    obtain ⟨hox, hodw⟩ := ox_ge_of_c (c := z) (k := 1) (fz := fzOf p1 p2)
                      (by omega) (by decide) (by omega) hfp
                    have hS45 : SafeStack 45 [2 + z0 - 1, 3, 1] :=
                      safeStack_of_gt2d2 (by decide) (by omega) (by omega)
                        (safeStack_31.2.2 (2 + z0 - 1) (by omega))
                    have hfb := (excursion_bundle m2).1 45 [2 + z0 - 1, 3, 1] p1 p2 z 1
                      (by decide) hS45 (validTail40_of_validSegs40 hvp)
                      (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
                    refine chainLeadsUpTo_trans hfb ?_
                    intro m3 s_m3 _ hex2
                    rcases hex2 with ⟨phi2, hphi2, hb2⟩ | ⟨y2, phi2, hy2, hphi2_38, _, hb2⟩
                    · rcases dec_or (2 + z0 - 1 = 19) with h19 | h20
                      · rw [h19] at hb2; exact bounce_19_31_leads hb2 (by omega)
                      · exact bounce_cz_31_leads hb2 (Or.inl ⟨by omega, by omega⟩)
                    · exact r9_pop_step hb2 hphi2_38 (by omega) (by omega)
                        (fun _ _ q1 q2 hvq _ =>
                          bounce_31_leads (isBounce_r9 (by omega) (by omega) hvq) (by omega)))
              · intro m1 _ s' hb1
                exact bounce_cz_31_leads hb1 (Or.inl ⟨by omega, by omega⟩)
              · intro m1 _ s' hb2
                exact bounce_cz_31_leads hb2 (Or.inl ⟨by omega, by omega⟩)
              · intro m1 c' k' p1 p2 _ hc' hk'41 hk'c hvp
                subst hc'
                exact x_31_high_leads (by omega) hvp (by omega) (by omega) hk'c
            · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, 2, 1, 0, [3, 1]⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (2 + z0 - 1) [3, 1] false &&
                  if m' + 1 = 1 then _ else GoodPsi (2 + z0 - 1) [3, 1] &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 11 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (1 + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              have hbc : IsBounce (1 + 2 * z0 + 2) [2 + z0, 3, 1]
                  ⟨true, (0, (m' - 4) + 1) :: rest, zl, 1 + 2 * z0 + 2, 0,
                    2 * (1 + 2 * z0) + 6, [2 + z0, 3, 1]⟩ := by
                have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := 1 + 2 * z0 + 2) (kb := 0) (mrg := 2 * (1 + 2 * z0) + 6)
                  (rest := rest) (ds := [2 + z0, 3, 1]) hv_rest (by omega)
                    (by split_ifs <;> omega)
                simpa only [Nat.add_zero] using h
              exact bounce_cz_31_leads hbc (Or.inl ⟨by omega, by omega⟩)

theorem root31B_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root31B s) :
    ChainAdvances s RootInv := by
  obtain ⟨hds, hvt, hc, hk1, hkc, hfz21, hcz25, hkz43, hod_inv⟩ := hr
  rcases s with ⟨b, segs, zl, c, k, mrg, ds⟩
  dsimp only at hb hmrg hds hvt hc hk1 hkc hfz21 hcz25 hkz43 hod_inv
  subst hb hmrg hds
  rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
  · dsimp only [fzOf, ValidTail40] at hvt hfz21 hcz25 hkz43
    have hg : stepGuards ⟨false, [], zl, c, k, 0, [3, 1]⟩ = true := by
      dsimp only [stepGuards]
      rw [goodPhiW_31 (by omega), Bool.true_and]
      dsimp only [GoodPsi]
      have hcz : c + zl - 1 + 1 = c + zl := by omega
      rw [hcz]; exact safeStack_31.2.2 (c + zl) (by omega)
    refine ⟨hg, fun N => ?_⟩
    dsimp only [stepSegs]
    have hbc : IsBounce (k + 2 * zl + 2) [c + zl, 3, 1]
        ⟨true, [], 0, k + 2 * zl + 2, 0, 2 * (k + 2 * zl) + 6, [c + zl, 3, 1]⟩ := by
      simpa only [Nat.add_zero] using IsBounce.nil (zl := 0) (cp1 := k + 2 * zl + 2)
        (kb := 0) (mrg := 2 * (k + 2 * zl) + 6) (ds := [c + zl, 3, 1]) (by omega)
    exact bounce_cz_31_ge25_leads hbc (by omega) (by omega)
  · dsimp only [fzOf, ValidTail40] at hvt hfz21 hcz25 hkz43
    have hv_rest : ValidSegs40 rest zl := hvt
    cases m0 with
    | zero =>
      exact step_m0_zero_31_advances hv_rest hc hk1 hkc (by omega)
    | succ m' =>
      have hphiw : GoodPhiW (c + z0 - 1) [3, 1] false = true := goodPhiW_31 (by omega)
      rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
      · have hm0_eq : m' = 0 := by omega
        subst hm0_eq
        have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, [3, 1]⟩ = true := by
          dsimp only [stepGuards]
          change (GoodPhiW (c + z0 - 1) [3, 1] false &&
            if 1 = 1 then GoodPsi (c + z0) [3, 1] else _) = true
          rw [hphiw, Bool.true_and, if_pos rfl]
          exact safeStack_31.2.2 (c + z0 + 1) (by omega)
        refine ⟨hg, fun N => ?_⟩
        dsimp only [stepSegs]
        change ChainLeadsUpTo N (if 1 = 1 then _ else _) _
        rw [if_pos rfl]
        exact x_31_high_leads (by omega) hv_rest (by omega) (by decide) (by omega)
      · have hpsi_cz : GoodPsi (c + z0 - 1) [3, 1] = true := by
          dsimp only [GoodPsi]
          have hcz_eq : c + z0 - 1 + 1 = c + z0 := by omega
          rw [hcz_eq]; exact safeStack_31.2.2 (c + z0) (by omega)
        rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
        · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [3, 1]⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) [3, 1] false &&
              if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [3, 1] &&
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
            rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
          refine ⟨hg, fun N => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
            if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
          rw [if_neg hm_gt1, if_pos hev_sm]
          exact x_31_high_leads (by omega) hv_rest (by omega) (by omega) (by omega)
        · rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
          · have hS_cz : SafeStack 19 [c + z0, 3, 1] :=
              safeStack_cons_ne1 (by decide) safeStack_31 (by omega) (by omega)
            have hne1_cz : ([c + z0, 3, 1] : List Nat) ≠ [1] := by
              intro h; injection h with _ h2; cases h2
            have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [3, 1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) [3, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [3, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                    GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: [3, 1]) else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_pos hod_sm]
              exact hS_cz.2.2 (k + 2 * z0 + 2) (by omega)
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
            have hm_sub : m' + 1 - 1 = m' := by omega
            rw [hm_sub]
            set x1 := k + 2 * z0 + 2
            rcases dec_or (x1 ≤ 47) with hx47 | hx48
            · refine loop_k1_le47 hne1_cz (safeStack_mono (by decide) hS_cz)
                (Or.inl (by omega)) hx47 hv_rest (by omega)
                (fun m1 z phi _ hz hphi38 _ hbz =>
                  pop_z_cz_31_leads hbz (by omega) hcz25 hphi38)
                ?_ ?_
                (fun m1 c' k' p1 p2 _ hc' hk'41 hk'c hvp => by
                  subst hc'
                  exact x_31_high_leads (by omega) hvp (by omega) (by omega) hk'c)
              · intro m1 _ s' hb1
                rcases dec_or ((c + z0) % 2 = 1) with hcz_od | hcz_ev
                · exact bounce_cz_31_leads hb1 (Or.inr (Or.inl ⟨by omega, hcz_od, by omega⟩))
                · have h_ev := hod_inv z0 (m' + 1) rest rfl (by omega) (by omega) hod_sm.1
                  rcases h_ev with ⟨rfl, rfl, rfl⟩ | h47
                  · exact bounce_cz_31_even_extra hb1 (Or.inr ⟨by decide, by decide, by omega⟩)
                  · omega
              · intro m1 _ s' hb2
                rcases dec_or ((c + z0) % 2 = 1) with hcz_od | hcz_ev
                · exact bounce_cz_31_leads hb2 (Or.inr (Or.inl ⟨by omega, hcz_od, by omega⟩))
                · have h_ev := hod_inv z0 (m' + 1) rest rfl (by omega) (by omega) hod_sm.1
                  rcases h_ev with ⟨rfl, rfl, rfl⟩ | h47
                  · exact bounce_cz_31_even_extra hb2 (Or.inr ⟨by decide, by decide, by omega⟩)
                  · omega
            · rcases dec_or (x1 ≤ 50) with hx50 | hx51
              · have hS_x1 : SafeStack 19 [x1, c + z0, 3, 1] :=
                  safeStack_cons_ne1 hne1_cz hS_cz (by omega) (by omega)
                have hne1_x1 : ([x1, c + z0, 3, 1] : List Nat) ≠ [1] := by
                  intro h; injection h with _ h2; cases h2
                refine chainLeadsUpTo_trans (fbound_k1_boost hne1_x1 hS_x1 hv_rest (by omega)) ?_
                intro m1 s_m1 hm1 hex1
                rcases hex1 with ⟨phi1, hphi1, hb1⟩ | ⟨y1, phi1, hy1, hphi1_38, hyw1, hb1⟩
                · exact pop_z_cz_31_leads hb1 (by omega) hcz25 hphi1
                · exact amega_pop_step hb1 hphi1_38 (by omega) (by omega)
                    (hS_cz.2.2 (x1 - 1) (by omega)) (fun _ => hS_cz.2.2 (x1 - 2) (by omega))
                    (fun hbig _ _ p1 p2 hvp _ =>
                      bounce_cz_31_ge25_leads (isBounce_r9 (by omega) hbig hvp) hcz25 (by omega))
                    (fun _ _ _ _ p1 p2 hvp _ =>
                      x_31_high_leads (by omega) hvp (by omega) (by omega) (by omega))
                    (fun hy1_le _ m2 _ p1 p2 hvp hfzp => by
                      have hfp := fzOf_ge_40 hvp
                      have hox99 := arith_boost_cz (c := y1) (fz := fzOf p1 p2)
                        (cz_lo := 109) (ox_lo := 99) (by omega) hfp (by omega) (Or.inl ⟨rfl, rfl⟩)
                      have hS_x1' : SafeStack 19 [x1 - 1, c + z0, 3, 1] :=
                        safeStack_cons_ne1 hne1_cz hS_cz (by omega) (by omega)
                      have hfb2 := (excursion_bundle m2).1 19 [x1 - 1, c + z0, 3, 1] p1 p2 y1 1
                        (by decide) hS_x1' (validTail40_of_validSegs40 hvp)
                        (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)
                          (by omega)
                      refine chainLeadsUpTo_trans hfb2 ?_
                      intro m3 s_m3 _ hex2
                      rcases hex2 with ⟨phi2, hphi2, hb2⟩ | ⟨y2, phi2, hy2, hphi2_38, _, hb2⟩
                      · have hp2 : 38 ≤ phi2 := by dsimp only [odw] at hphi2; omega
                        exact pop_z_cz_31_leads hb2 (by omega) hcz25 hp2
                      · exact amega_pop_step hb2 hphi2_38 (by omega) (by omega)
                          (hS_cz.2.2 (x1 - 2) (by omega)) (fun _ => hS_cz.2.2 (x1 - 3) (by omega))
                          (fun hbig _ _ q1 q2 hvq _ =>
                            bounce_cz_31_ge25_leads (isBounce_r9 (by omega) hbig hvq) hcz25 (by
                              omega))
                          (fun _ _ _ _ q1 q2 hvq _ =>
                            x_31_high_leads (by omega) hvq (by omega) (by omega) (by omega))
                          (fun hy2_le _ m4 _ q1 q2 hvq _ => by
                            have hfq := fzOf_ge_40 hvq
                            obtain ⟨hox_q, _⟩ := ox_ge_of_c (c := y2) (k := 1) (fz := fzOf q1 q2)
                              (by omega) (by decide) (by omega) hfq
                            exact fbound_force_r9 (x := x1 - 2) (d3 := c + z0) (ds3 := [3, 1])
                              (by omega) (hS_cz.2.2 (x1 - 2) (by omega))
                              (hS_cz.2.2 (x1 - 3) (by omega)) hvq
                              (by omega) (by decide) (by omega) (by omega) (by omega)
                              (fun _ phi3 _ hphi3 _ hb3 =>
                                pop_z_cz_31_leads hb3 (by omega) hcz25 (by omega))
                              (fun _ _ _ hb3 =>
                                bounce_cz_31_ge25_leads hb3 hcz25 (by omega))))
              · have hfz_r : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
                exact chainLeadsUpTo_trans
                  ((excursion_bundle N).2 19 [c + z0, 3, 1] rest zl m' 1 x1 46 0
                    (by decide) hS_cz (Or.inl hne1_cz) hv_rest
                    (by omega) (by decide) (by omega) (by decide) (by omega)
                    (by omega) (by omega) (by omega) (by omega))
                  (fun _ _ _ hex => by
                    rcases hex with ⟨phi, hphi, hb⟩ | ⟨z, phi, hz, hphi38, _, hb⟩
                    · exact bounce_cz_31_ge25_leads hb hcz25 hphi
                    · exact pop_z_cz_31_leads hb (by omega) hcz25 hphi38)
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, [3, 1]⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) [3, 1] false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) [3, 1] &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                if_neg hnot_ev, if_neg hbig_m]
            refine ⟨hg, fun N => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
              if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
            rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
            have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
              dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
            rw [hnorm]
            have hbc : IsBounce (k + 2 * z0 + 2) [c + z0, 3, 1]
                ⟨true, (0, (m' - 4) + 1) :: rest, zl, k + 2 * z0 + 2, 0,
                  2 * (k + 2 * z0) + 6, [c + z0, 3, 1]⟩ := by
              have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                (rest := rest) (ds := [c + z0, 3, 1]) hv_rest (by omega)
                  (by split_ifs <;> omega)
              simpa only [Nat.add_zero] using h
            exact bounce_cz_31_ge25_leads hbc hcz25 (by omega)

theorem root31_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root31 s) :
    ChainAdvances s RootInv := by
  rcases hr with ha | hb31
  · exact root31A_advances hb hmrg ha
  · exact root31B_advances hb hmrg hb31

-- ============================================================================
-- Helpers & Advancement Closure for `Root0` (`Root0A` and `Root0B`)
-- ============================================================================

theorem goodPhiW_0 {w : Nat} {ds : List Nat} (hds : ds = [] ∨ ds = [0]) (hw : 6 ≤ w) :
    GoodPhiW w ds false = true := by
  rcases hds with rfl | rfl
  · dsimp only [GoodPhiW]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl, Bool.false_or]
    exact decide_eq_true hw
  · dsimp only [GoodPhiW]
    rw [if_neg (by decide), if_pos rfl]
    exact decide_eq_true hw

theorem goodPsi_0 {w : Nat} {ds : List Nat} (hds : ds = [] ∨ ds = [0]) (hw : 7 ≤ w) :
    GoodPsi w ds = true := by
  rcases hds with rfl | rfl
  · dsimp only [GoodPsi, GoodDs, GoodDsAux, GoodDs1]
    exact decide_eq_true (by omega)
  · dsimp only [GoodPsi, GoodDs, GoodDsAux, GoodDs2]
    rw [if_pos rfl]
    exact decide_eq_true (by omega)

theorem safeStack_0 {ds : List Nat} (hds : ds = [] ∨ ds = [0]) : SafeStack 19 ds := by
  rcases hds with rfl | rfl
  · exact safeStack_nil
  · exact safeStack_zero

theorem safeStack19_d_ds {d : Nat} {ds : List Nat} (hd10 : 10 ≤ d) (hds : ds = [] ∨ ds = [0]) :
    SafeStack 19 (d :: ds) := by
  rcases hds with rfl | rfl
  · refine ⟨(by intro h; injection h with h1; omega), (safeStack_d (by omega)).2.1, ?_⟩
    intro u hu
    dsimp only [GoodDs, GoodDsAux, GoodDs2]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hu19 : decide (u < 19) = false := decide_eq_false (by omega)
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hgd : GoodDs1 d = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg1 : GoodDs1 (d - 1) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    have hg2 : GoodDs1 (d - 2) = true := by dsimp only [GoodDs1]; exact decide_eq_true (by omega)
    rw [hu19, hu17, hgd, hg1, hg2]
    simp only [Bool.and_false, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]
  · refine ⟨(by intro h; injection h with _ h2; cases h2), (safeStack_d0 (by omega)).2.1, ?_⟩
    intro u hu
    dsimp only [GoodDs]
    rw [GoodDsAux.eq_3, if_neg (by omega)]
    have h1 : decide (d = 3 ∧ 0 = 1 ∧ ([] : List Nat) = [] ∧ u < 19) = false :=
      decide_eq_false (by omega)
    have hu19 : decide (u < 19) = false := decide_eq_false (by omega)
    have h3 : decide (d ≥ 25 ∧ 0 = 1 ∧ ([] : List Nat) = [] ∧ u < 39) = false :=
      decide_eq_false (by omega)
    have hu17 : decide (u < 17) = false := decide_eq_false (by omega)
    have hgd : GoodDsAux d [0] = true := (safeStack_d0 (by omega)).2.1
    have hg1 : GoodDsAux (d - 1) [0] = true := (safeStack_d0 (by omega)).2.1
    have hg2 : GoodDsAux (d - 2) [0] = true := (safeStack_d0 (by omega)).2.1
    rw [h1, hu19, h3, hu17, hgd, hg1, hg2]
    simp only [Bool.and_false, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]

theorem bounce_0_leads {N phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi ds s) (hds : ds = [] ∨ ds = [0]) (hphi : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  rcases hds with rfl | rfl
  · exact bounce_nil_leads hb (by omega)
  · exact bounce_zero_leads hb hphi

theorem step_m0_zero_0_advances {z0 zl c k : Nat} {rest : List (Nat × Nat)} {ds : List Nat}
    (hds : ds = [] ∨ ds = [0]) (hv_rest : ValidSegs40 rest zl)
    (_hc : 1 ≤ c) (hk1 : 1 ≤ k) (hkc : k ≤ 2 * c + 3) (hcz8 : 8 ≤ c + z0) :
    ChainAdvances ⟨false, (z0, 0) :: rest, zl, c, k, 0, ds⟩ RootInv := by
  refine ⟨rfl, fun N => ?_⟩
  dsimp only [stepSegs]
  rcases rest with _ | ⟨⟨z1, m1_seg⟩, r2⟩
  · have hzl230 : 230 ≤ zl := hv_rest.2
    exact bounce_0_leads (IsBounce.nil (by omega)) hds (by omega)
  · have hz1_40 : 40 ≤ z1 := fzOf_ge_40 hv_rest
    have hv_r2 : ValidSegs40 r2 zl := validSegs40_tail hv_rest
    have hfz2_40 : 40 ≤ fzOf r2 zl := fzOf_ge_40 hv_r2
    cases m1_seg with
    | zero =>
      have hg2 : stepGuards ⟨true, (z1, 0) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
          2 * (c + z0) + 8, ds⟩ = true := by
        dsimp only [stepGuards]; exact decide_eq_true (by omega)
      apply chainLeadsUpTo_step1 hg2
      dsimp only [stepSegs]
      exact chainLeadsUpTo_here (rootInv_of_0B hds (validTail40_of_validSegs40 hv_r2)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
    | succ m1' =>
      rcases dec_or ((m1' + 1) % 2 = 1) with hm1_od | hm1_ev
      · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + m1') with
        | true =>
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
              2 * (c + z0) + 8, ds⟩ = true := by
            dsimp only [stepGuards]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
            exact (safeStack_0 hds).2.2 (c + z0 + 3 + z1) (by omega)
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_pos hm1_od, hd_mrg, if_pos rfl]
          have hds_d : ((c + z0 + 3 + z1) :: ds) = [c + z0 + 3 + z1] ∨
              ((c + z0 + 3 + z1) :: ds) = [c + z0 + 3 + z1, 0] := by
            rcases hds with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
          exact chainLeadsUpTo_here (rootInv_of_D (d := c + z0 + 3 + z1) (by omega) hds_d
            (validTail40_of_validSegs40 hv_r2) (by omega) (by decide) (by omega)
            (by omega) (by omega) (by omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_0_leads
            (IsBounce.cons hv_r2 (by omega) (by rw [if_pos hm1_od]; omega)) hds (by omega)
      · cases hd_mrg : decide (2 * (c + z0) + 8 ≥ (k + 2 * z0 + 3) + (m1' + 1)) with
        | true =>
          have h_mrg := of_decide_eq_true hd_mrg
          have hg2 : stepGuards ⟨true, (z1, m1' + 1) :: r2, zl, c + z0 + 3, k + 2 * z0 + 3,
              2 * (c + z0) + 8, ds⟩ = true := by
            dsimp only [stepGuards]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
          apply chainLeadsUpTo_step1 hg2
          dsimp only [stepSegs]; rw [if_neg hm1_ev, hd_mrg, if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_0B hds (validTail40_of_validSegs40 hv_r2)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
        | false =>
          have h_nm := of_decide_eq_false hd_mrg
          exact bounce_0_leads
            (IsBounce.cons hv_r2 (by omega) (by rw [if_neg hm1_ev]; omega)) hds (by omega)

theorem pop_17_8_0_leads {N phi : Nat} {s : SegState}
    (hb : IsBounce phi [17, 8, 0] s) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hg_pop : drainPopGuards phi [17, 8, 0] = true := by
    have hnrst : isDrainRstDs [17, 8, 0] = false := rfl
    have hnr0 : isRank0 [17, 8, 0] = false := rfl
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [17, 8, 0] =
      ⟨true, (0, 14) :: p.1, p.2, 7, 0, 16, [0]⟩ := rfl
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfp40 : 40 ≤ fzOf p.1 p.2 := fzOf_ge_40 hvp
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hg2 : stepGuards ⟨true, (0, 14) :: p.1, p.2, 7, 0, 16, [0]⟩ = true := rfl
  have hs2 : stepSegs ⟨true, (0, 14) :: p.1, p.2, 7, 0, 16, [0]⟩ =
      ⟨false, p.1, p.2, 9, 19, 0, [0]⟩ := rfl
  apply chainLeadsUpTo_step1 hg2
  rw [hs2]
  exact chainLeadsUpTo_here (rootInv_of_0B (Or.inr rfl) (validTail40_of_validSegs40 hvp)
    (by decide) (by decide) (by decide) (by omega) (by omega)
    (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))

theorem pop_y_17_8_0_leads {N y phi : Nat} {s : SegState}
    (hb : IsBounce phi [y, 17, 8, 0] s) (hy43 : 43 ≤ y) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hnrst : isDrainRstDs [y, 17, 8, 0] = false := rfl
  have hnr0 : isRank0 [y, 17, 8, 0] = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi [y, 17, 8, 0] = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ 17 ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : decide (y % 2 = 0 ∧ y ≤ 2 * 17 + 4) = false := decide_eq_false (by omega)
    have hc3 : decide (y % 2 = 0 ∧ y + 14 ≤ 2 * 17) = false := decide_eq_false (by omega)
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl [y, 17, 8, 0] =
      ⟨true, (0, (y - 4) + 1) :: p.1, p.2, 16, 0, 34, [8, 0]⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      if_neg (by rintro ⟨h17, _, _⟩; cases h17)]
    have hnorm : normSeg 0 (y - 3) = (0, (y - 4) + 1) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
    rw [hnorm]
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hbc : IsBounce 16 [8, 0] ⟨true, (0, (y - 4) + 1) :: p.1, p.2, 16, 0, 34, [8, 0]⟩ := by
    have h := IsBounce.cons (z0 := 0) (m := y - 4) (zl := p.2) (cp1 := 16) (kb := 0) (mrg := 34)
      (rest := p.1) (ds := [8, 0]) hvp (by omega)
        (by split_ifs <;> omega)
    simpa only [Nat.add_zero] using h
  exact bounce_d_leads hbc (Or.inr rfl) (Or.inl ⟨rfl, Or.inl rfl⟩)

theorem pop_19_9_leads {N phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi (19 :: 9 :: ds) s) (hds : ds = [] ∨ ds = [0]) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hg_pop : drainPopGuards phi (19 :: 9 :: ds) = true := by
    have hnrst : isDrainRstDs (19 :: 9 :: ds) = false := rfl
    have hnr0 : isRank0 (19 :: 9 :: ds) = false := rfl
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rcases hds with rfl | rfl <;> (rw [hc4]; rfl)
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl (19 :: 9 :: ds) =
      ⟨true, (0, 16) :: p.1, p.2, 8, 0, 18, ds⟩ := by
    rcases hds with rfl | rfl <;> rfl
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfp40 : 40 ≤ fzOf p.1 p.2 := fzOf_ge_40 hvp
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  have hg2 : stepGuards ⟨true, (0, 16) :: p.1, p.2, 8, 0, 18, ds⟩ = true := rfl
  have hs2 : stepSegs ⟨true, (0, 16) :: p.1, p.2, 8, 0, 18, ds⟩ =
      ⟨false, p.1, p.2, 10, 21, 0, ds⟩ := rfl
  apply chainLeadsUpTo_step1 hg2
  rw [hs2]
  exact chainLeadsUpTo_here (rootInv_of_0B hds (validTail40_of_validSegs40 hvp)
    (by decide) (by decide) (by decide) (by omega) (by omega)
    (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))

theorem pop_y_19_9_leads {N y phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi (y :: 19 :: 9 :: ds) s)
    (hds : ds = [] ∨ ds = [0])
    (hy49 : 49 ≤ y)
    (hphi_cases : (53 ≤ y ∧ 90 ≤ phi) ∨ 100 ≤ phi ∨ (53 ≤ y ∧ y % 2 = 1 ∧ 88 ≤ phi)) :
    ChainLeadsUpTo N s RootInv := by
  have hphi88 : 88 ≤ phi := by
    rcases hphi_cases with ⟨_, h⟩ | h | ⟨_, _, h⟩ <;> omega
  refine r9_pop_step hb (by omega) (by decide) (by omega) ?_
  intro m1 _ p0_1 p0_2 hvp0 hfzp0
  have hy_sub : y - 3 = (y - 4) + 1 := by omega
  have hg_pop9 : drainPopGuards (18 + 0) (9 :: ds) = true := by
    rcases hds with rfl | rfl <;> rfl
  have hg2 : stepGuards ⟨true, (0, y - 3) :: p0_1, p0_2, 18, 0, 38, 9 :: ds⟩ = true := by
    rw [hy_sub]; dsimp only [stepGuards]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega)]; exact hg_pop9
    · rw [if_neg hev, decide_eq_false (by omega)]; exact hg_pop9
  have hs2 : stepSegs ⟨true, (0, y - 3) :: p0_1, p0_2, 18, 0, 38, 9 :: ds⟩ =
      ⟨true, (1, 0) :: (20, y - 43) :: p0_1, p0_2, 3, 0, 8, [1]⟩ := by
    have hm_eq : 0 + ((y - 4) + 1) - (38 + 2) = y - 43 := by omega
    have hn20 : normSeg 20 (y - 43) = (20, y - 43) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    have hdp9 : drainPopStep true (18 + 0) (y - 43) p0_1 p0_2 (9 :: ds) =
        ⟨true, (1, 0) :: normSeg 20 (y - 43) :: p0_1, p0_2, 3, 0, 8, [1]⟩ := by
      rcases hds with rfl | rfl <;> rfl
    rw [hy_sub]; dsimp only [stepSegs]
    rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
    · rw [if_pos hod, decide_eq_false (by omega), if_neg Bool.false_ne_true, hm_eq, hdp9, hn20]
    · rw [if_neg hev, decide_eq_false (by omega), if_neg Bool.false_ne_true, hm_eq, hdp9, hn20]
  apply chainLeadsUpTo_step hg2
  intro m2 _
  rw [hs2]
  have hg3 : stepGuards ⟨true, (1, 0) :: (20, y - 43) :: p0_1, p0_2, 3, 0, 8, [1]⟩ = true := rfl
  have hs3 : stepSegs ⟨true, (1, 0) :: (20, y - 43) :: p0_1, p0_2, 3, 0, 8, [1]⟩ =
      ⟨false, (20, y - 43) :: p0_1, p0_2, 5, 5, 0, [1]⟩ := rfl
  apply chainLeadsUpTo_step1 hg3
  rw [hs3]
  apply chainLeadsUpTo_here
  refine rootInv_of_1 hvp0 (by decide) (by decide) (by decide)
    (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega)
    (fun _ => ⟨y - 43, p0_1, rfl, rfl, rfl, by omega, ?_⟩)
    (by intro h; dsimp only [fzOf] at h; omega)
  intro hm0_od
  rcases hphi_cases with ⟨hy53, hphi90⟩ | hphi100 | ⟨_, hy_od, _⟩ <;> omega

theorem pop_y_d_leads {N d y phi : Nat} {ds : List Nat} {s : SegState}
    (hb : IsBounce phi (y :: d :: ds) s)
    (hd10 : 10 ≤ d) (hds : ds = [] ∨ ds = [0])
    (hy20 : 20 ≤ y) (hphi38 : 38 ≤ phi) :
    ChainLeadsUpTo N s RootInv := by
  have hSd : SafeStack 19 (d :: ds) := safeStack19_d_ds hd10 hds
  have hg1 : GoodDs ((d - 1) :: ds) = true := by
    rcases hds with rfl | rfl
    · exact (safeStack_d (by omega)).2.1
    · exact (safeStack_d0 (by omega)).2.1
  have hg2 : GoodDs ((d - 2) :: ds) = true := by
    rcases hds with rfl | rfl
    · exact (safeStack_d (by omega)).2.1
    · exact (safeStack_d0 (by omega)).2.1
  have hnrst : isDrainRstDs (y :: d :: ds) = false := by
    cases d with | zero => omega | succ _ => rfl
  have hnr0 : isRank0 (y :: d :: ds) = false := by
    rcases y with _ | _ | _ | _ <;> try omega
    rfl
  have hg_pop : drainPopGuards phi (y :: d :: ds) = true := by
    dsimp only [drainPopGuards]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    have hc1 : decide (y ≥ 3 ∧ d ≥ 1) = true := decide_eq_true (by omega)
    have hc2 : (!decide (y % 2 = 0 ∧ y ≤ 2 * d + 4) || GoodDs ((d - 1) :: ds)) = true := by
      rw [hg1, Bool.or_true]
    have hc3 : (!decide (y % 2 = 0 ∧ y + 14 ≤ 2 * d) || GoodDs ((d - 2) :: ds)) = true := by
      rw [hg2, Bool.or_true]
    have hc4 : decide (phi ≥ 16) = true := decide_eq_true (by omega)
    rw [hc1, hc2, hc3, hc4]; rfl
  obtain ⟨hg_s, _, hp, m_rem, rest, zl, hv_rest, hzl_false, hstep⟩ := isBounce_step hb hg_pop
  set p := pushSeg hp (phi + 2) m_rem rest zl
  have hdp : drainPopStep hp phi m_rem rest zl (y :: d :: ds) =
      ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, ds⟩ := by
    dsimp only [drainPopStep]
    rw [hnrst, hnr0, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_neg (by omega)]
    have hnorm : normSeg 0 (y - 3) = (0, y - 3) := by
      dsimp only [normSeg]; rw [if_neg (by omega)]
    rw [hnorm]
  rw [hdp] at hstep
  have hvp : ValidSegs40 p.1 p.2 :=
    validSegs40_pushSeg hp (by omega) hv_rest (fun hf => by have := hzl_false hf; omega)
  have hfzp40 : 40 ≤ fzOf p.1 p.2 := fzOf_ge_40 hvp
  apply chainLeadsUpTo_step hg_s
  intro m1 _
  rw [hstep]
  rcases dec_or (2 * d + 5 ≤ y) with hbig | hsm
  · rcases hds with rfl | rfl
    · have hy_sub : y - 3 = (y - 4) + 1 := by omega
      have hpop_nil : drainPopGuards (d - 1 + 0) [] = true := by
        change decide (d - 1 + 0 ≥ 2) = true; exact decide_eq_true (by omega)
      have hg_s2 : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, []⟩ = true := by
        rw [hy_sub]; dsimp only [stepGuards]
        rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
        · rw [if_pos hod, decide_eq_false (by omega)]; exact hpop_nil
        · rw [if_neg hev, decide_eq_false (by omega)]; exact hpop_nil
      apply chainLeadsUpTo_step1 hg_s2
      rw [hy_sub]; dsimp only [stepSegs]
      set q := pushSeg true (d - 1 + 0 + 1) (0 + ((y - 4) + 1) - (2 * d + 2)) p.1 p.2
      have hvtq : ValidTail40 q.1 q.2 :=
        validTail40_pushSeg true (fun _ => hvp) (by intro hf; cases hf)
      have hfzq : d - 1 + 0 + 1 ≤ fzOf q.1 q.2 :=
        fzOf_pushSeg_ge true (d - 1 + 0 + 1) (0 + ((y - 4) + 1) - (2 * d + 2)) p.1 p.2
      rcases dec_or (((y - 4) + 1) % 2 = 1) with hod | hev
      · rw [if_pos hod, decide_eq_false (by omega)]
        change ChainLeadsUpTo m1 ⟨false, q.1, q.2, 1, 1, 0, []⟩ RootInv
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
      · rw [if_neg hev, decide_eq_false (by omega)]
        change ChainLeadsUpTo m1 ⟨false, q.1, q.2, 1, 1, 0, []⟩ RootInv
        exact chainLeadsUpTo_here (rootInv_of_0B (Or.inl rfl) hvtq
          (by decide) (by decide) (by decide) (by omega) (by omega)
          (by intro h; omega) (fun _ => Or.inl ⟨rfl, rfl⟩) (by intro _ _ _ _ hcz9; omega))
    · exact bounce_r9_zero_leads (by omega) hbig hvp
  · have hy_sub : y - 3 = (y - 4) + 1 := by omega
    rcases dec_or (y % 2 = 1) with hy_od | hy_ev
    · have hm_ev : ¬(((y - 4) + 1) % 2 = 1) := by omega
      have hmrg : decide (2 * d ≥ 0 + ((y - 4) + 1)) = true := decide_eq_true (by omega)
      have hg_mid : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, ds⟩ = true := by
        rw [hy_sub]; dsimp only [stepGuards]; rw [if_neg hm_ev, hmrg, if_pos rfl]
      have hs_mid : stepSegs ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, ds⟩ =
          ⟨false, p.1, p.2, d + 1, y + 2, 0, ds⟩ := by
        rw [hy_sub]; dsimp only [stepSegs]; rw [if_neg hm_ev, hmrg, if_pos rfl]
        have hc_eq : d - 1 + 0 + 2 = d + 1 := by omega
        have hk_eq : 0 + (y - 4 + 1) + 2 * 0 + 5 = y + 2 := by omega
        rw [hc_eq, hk_eq]
      apply chainLeadsUpTo_step1 hg_mid
      rw [hs_mid]
      exact chainLeadsUpTo_here (rootInv_of_0B hds (validTail40_of_validSegs40 hvp)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by intro h; omega) (by intro h; omega) (by intro _ _ _ _ hcz9; omega))
    · have hm_od : ((y - 4) + 1) % 2 = 1 := by omega
      have hmrg : decide (2 * d ≥ 0 + (y - 4)) = true := decide_eq_true (by omega)
      have hg_mid : stepGuards ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, ds⟩ = true := by
        rw [hy_sub]; dsimp only [stepGuards]; rw [if_pos hm_od, hmrg, if_pos rfl]
        simpa only [Nat.add_zero] using hg1
      have hs_mid : stepSegs ⟨true, (0, y - 3) :: p.1, p.2, d - 1, 0, 2 * d, ds⟩ =
          ⟨false, p.1, p.2, y, 1, 0, (d - 1) :: ds⟩ := by
        rw [hy_sub]; dsimp only [stepSegs]; rw [if_pos hm_od, hmrg, if_pos rfl]
        have hc_eq : 0 + (y - 4) + 2 * 0 + 4 = y := by omega
        have hd_eq : d - 1 + 0 = d - 1 := by omega
        rw [hc_eq, hd_eq]
      apply chainLeadsUpTo_step1 hg_mid
      rw [hs_mid]
      have hds_d1 : ((d - 1) :: ds) = [d - 1] ∨ ((d - 1) :: ds) = [d - 1, 0] := by
        rcases hds with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
      exact chainLeadsUpTo_here (rootInv_of_D (d := d - 1) (by omega) hds_d1
        (validTail40_of_validSegs40 hvp) (by omega) (by decide) (by omega)
        (by omega) (by omega) (by omega))

theorem root0A_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root0A s) :
    ChainAdvances s RootInv := by
  obtain ⟨hds, hc, hk, z1, m0, m1, rest, hsegs, hm0, hz1, hv⟩ := hr
  rcases s with ⟨b, segs, zl, cp1, kb, mrg, ds⟩
  dsimp only at hb hmrg hds hc hk hsegs hm0 hz1 hv
  subst hb hmrg hds hc hk hsegs
  rcases hm0 with rfl | rfl
  · refine ⟨rfl, fun _ => ?_⟩
    dsimp only [stepSegs]
    exact chainLeadsUpTo_here (rootInv_of_D (d := 10) (by decide) (Or.inl rfl) hv
      (by decide) (by decide) (by decide)
      (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega))
  · refine ⟨rfl, fun _ => ?_⟩
    dsimp only [stepSegs]
    exact chainLeadsUpTo_here (rootInv_of_D (d := 9) (by decide) (Or.inl rfl) hv
      (by decide) (by decide) (by decide)
      (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega) (by dsimp only [fzOf]; omega))

theorem root0B_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root0B s) :
    ChainAdvances s RootInv := by
  obtain ⟨hds, hvt, hc, hk1, hkc, hfz7, hcz8, h8, h39, h9⟩ := hr
  rcases s with ⟨b, segs, zl, c, k, mrg, ds⟩
  dsimp only at hb hmrg hds hvt hc hk1 hkc hfz7 hcz8 h8 h39 h9
  subst hb hmrg
  rcases dec_or (39 ≤ fzOf segs zl ∧ 42 ≤ c + fzOf segs zl) with ⟨hfz39, hcz42⟩ | hlow
  · have hS0 : SafeStack 19 ds := safeStack_0 hds
    obtain ⟨hox39, _⟩ := ox_bounds_relaxed hc hk1 hkc (by omega) hcz42 (by omega)
    refine chainAdvances_trans
      (fbound_advances (by decide) hS0 hvt hc hk1 hkc (by omega) hcz42 (by omega) (by omega)) ?_
    intro s' hex N
    rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
    · exact bounce_0_leads hb hds (by dsimp only [odw] at hphi; omega)
    · have hds_y : (y :: ds) = [y] ∨ (y :: ds) = [y, 0] := by
        rcases hds with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
      exact bounce_d_leads hb hds_y (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, hphi38⟩))))
  · rcases segs with _ | ⟨⟨z0, m0⟩, rest⟩
    · dsimp only [fzOf, ValidTail40] at hvt hlow; omega
    · dsimp only [fzOf, ValidTail40] at hvt hfz7 hcz8 h39 hlow
      have hv_rest : ValidSegs40 rest zl := hvt
      cases m0 with
      | zero =>
        exact step_m0_zero_0_advances hds hv_rest hc hk1 hkc hcz8
      | succ m' =>
        have hphiw : GoodPhiW (c + z0 - 1) ds false = true := goodPhiW_0 hds (by omega)
        have hds_cz : ((c + z0) :: ds) = [c + z0] ∨ ((c + z0) :: ds) = [c + z0, 0] := by
          rcases hds with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
        have hds_cz1 : ((c + z0 + 1) :: ds) = [c + z0 + 1] ∨
          ((c + z0 + 1) :: ds) = [c + z0 + 1, 0] := by
          rcases hds with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
        have hfz_r : 40 ≤ fzOf rest zl := fzOf_ge_40 hv_rest
        rcases dec_or (m' + 1 = 1) with hm1 | hm_gt1
        · have hm0_eq : m' = 0 := by omega
          subst hm0_eq
          have hg : stepGuards ⟨false, (z0, 1) :: rest, zl, c, k, 0, ds⟩ = true := by
            dsimp only [stepGuards]
            change (GoodPhiW (c + z0 - 1) ds false && if 1 = 1 then GoodPsi (c + z0) ds else _) =
              true
            rw [hphiw, Bool.true_and, if_pos rfl]
            exact goodPsi_0 hds (by omega)
          refine ⟨hg, fun _ => ?_⟩
          dsimp only [stepSegs]
          change ChainLeadsUpTo _ (if 1 = 1 then _ else _) _
          rw [if_pos rfl]
          exact chainLeadsUpTo_here (rootInv_of_D (d := c + z0 + 1) (by omega) hds_cz1
            (validTail40_of_validSegs40 hv_rest) (by omega) (by decide) (by omega)
            (by omega) (by omega) (by omega))
        · have hpsi_cz : GoodPsi (c + z0 - 1) ds = true := goodPsi_0 hds (by omega)
          rcases dec_or ((m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10) with hev_sm | hnot_ev
          · have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, ds⟩ = true := by
              dsimp only [stepGuards]
              change (GoodPhiW (c + z0 - 1) ds false &&
                if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) ds &&
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else _) = true
              rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and, if_pos hev_sm]
            refine ⟨hg, fun _ => ?_⟩
            dsimp only [stepSegs]
            change ChainLeadsUpTo _ (if m' + 1 = 1 then _ else
              if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else _) _
            rw [if_neg hm_gt1, if_pos hev_sm]
            exact chainLeadsUpTo_here (rootInv_of_D (d := c + z0) (by omega) hds_cz
              (validTail40_of_validSegs40 hv_rest) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega))
          · -- Helper for `bounce_d_leads` at `phi >= k + 2 * z0` when `10 <= c + z0`:
            have h_bounce_cz : 10 ≤ c + z0 → ∀ phi, k + 2 * z0 ≤ phi →
                (c + z0 = 8 ∧ (phi = 16 ∨ phi = 17 ∨ 38 ≤ phi)) ∨
                (c + z0 = 9 ∧ 19 ≤ phi) ∨
                (10 ≤ c + z0 ∧ c + z0 ≤ 18 ∧ 19 ≤ phi ∧
                  (12 ≤ c + z0 → (c + z0) % 2 = 0 → 23 ≤ phi)) ∨
                (c + z0 = 19 ∧ 37 ≤ phi) ∨
                (20 ≤ c + z0 ∧ 38 ≤ phi) := by
              intro hd10 phi hphi_kz
              rcases dec_or (39 ≤ z0) with hz39 | hz_lt39
              · rcases dec_or (c + z0 ≤ 18) with h18 | h19
                · omega
                · rcases dec_or (c + z0 = 19) with h_eq19 | h20
                  · omega
                  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
              · rcases h39 (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hz20⟩
                · rcases dec_or (1 + z0 ≤ 18) with h_le18 | h_ge19
                  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h_le18, by omega,
                      fun _ _ => by omega⟩))
                  · rcases dec_or (1 + z0 = 19) with h_eq19 | h_ge20
                    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h_eq19, by omega⟩)))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
                · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
            rcases dec_or ((m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11) with hod_sm | hbig_m
            · rcases dec_or (c + z0 = 8) with hcz_eq8 | hcz_ge9
              · obtain ⟨m0_, rest_, hseg_eq, rfl, rfl, rfl, hfz44⟩ := h8 hcz_eq8
                injection hseg_eq with hhd htl
                injection hhd with hz0_eq _
                subst hz0_eq htl
                clear h8 h9 h39
                have hg : stepGuards ⟨false, (7, m' + 1) :: rest, zl, 1, 1, 0, [0]⟩ = true := by
                  dsimp only [stepGuards]
                  change (GoodPhiW 7 [0] false &&
                    if m' + 1 = 1 then _ else GoodPsi 7 [0] &&
                      if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 40 then true else
                      if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 41 then
                        GoodDs [17, 8, 0] else true) = true
                  rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                    if_neg hnot_ev, if_pos hod_sm]
                  rfl
                refine ⟨hg, fun N => ?_⟩
                dsimp only [stepSegs]
                change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                  if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 40 then _ else
                  if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 41 then _ else _) _
                rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
                have hm_sub : m' + 1 - 1 = m' := by omega
                rw [hm_sub]
                have hox43 : 43 ≤ ox (1 + 2 * fzOf rest zl) (m' + fzOf rest zl) ∧
                    42 ≤ odw (1 + 2 * fzOf rest zl) (m' + fzOf rest zl) := by
                  obtain ⟨q, r, hr_lt, heq, hox_eq⟩ :=
                    ox_spec_lt (kz := 1 + 2 * fzOf rest zl) (cz := m' + fzOf rest zl) (by omega)
                  dsimp only [odw]
                  rw [hox_eq]
                  omega
                have hfb := (excursion_bundle N).1 39 [17, 8, 0] rest zl m' 1
                  (by decide) safeStack_17_8_0 (validTail40_of_validSegs40 hv_rest)
                  (by omega) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
                refine chainLeadsUpTo_trans hfb ?_
                intro m1 s_mid _ hex
                rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
                · exact pop_17_8_0_leads hb (by omega)
                · exact pop_y_17_8_0_leads hb (by omega) hphi38
              · clear h8
                rcases dec_or (c + z0 = 9) with hcz_eq9 | hcz_ge10
                · have hck1 : c = 1 ∧ k = 1 := by
                    rcases h39 (by clear h9; omega) with h | ⟨_, _, hz20⟩
                    · exact h
                    · clear h9 h39; omega
                  rcases hck1 with ⟨rfl, rfl⟩
                  clear h39
                  have hz8 : z0 = 8 := by clear h9; omega
                  subst hz8
                  have hm'2 : 2 ≤ m' := by clear h9; have := hod_sm.1; omega
                  have hm'3 : 3 ≤ m' + 1 := Nat.succ_le_succ hm'2
                  have h9_props := h9 8 (m' + 1) rest rfl hcz_eq9 hm'3 hod_sm.1
                  clear h9
                  have hm_sub : m' + 1 - 1 = m' := by omega
                  rw [hm_sub] at h9_props
                  have hS_19 : SafeStack 43 (19 :: 9 :: ds) := by
                    rcases hds with rfl | rfl
                    · exact safeStack_19_9
                    · exact safeStack_19_9_0
                  have hg : stepGuards ⟨false, (8, m' + 1) :: rest, zl, 1, 1, 0, ds⟩ = true := by
                    dsimp only [stepGuards]
                    change (GoodPhiW 8 ds false &&
                      if m' + 1 = 1 then _ else GoodPsi 8 ds &&
                        if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 44 then true else
                        if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 45 then
                          GoodDs (19 :: 9 :: ds) else true) = true
                    rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                      if_neg hnot_ev, if_pos hod_sm]
                    exact hS_19.2.1
                  refine ⟨hg, fun N => ?_⟩
                  dsimp only [stepSegs]
                  change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 44 then _ else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 45 then _ else _) _
                  rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm, hm_sub]
                  have hne1_19 : (19 :: 9 :: ds) ≠ [1] := by
                    intro h; injection h with h1; omega
                  refine chainLeadsUpTo_trans
                    (fhigh_ext hne1_19 hS_19 hv_rest hm'2
                      h9_props.1 h9_props.2.1 h9_props.2.2) ?_
                  intro m1 s_mid _ hex
                  rcases hex with (⟨phi, hphi, hb⟩ | ⟨y, phi, hy49, hpc, hb⟩) |
                      ⟨y, phi, hy53, hy_od, hphi88, hb⟩
                  · exact pop_19_9_leads hb hds (by omega)
                  · exact pop_y_19_9_leads hb hds hy49
                      (hpc.imp id Or.inl)
                  · exact pop_y_19_9_leads hb hds (by omega) (Or.inr (Or.inr ⟨hy53, hy_od, hphi88⟩))
                · -- `10 <= c + z0`:
                  have hd10 : 10 ≤ c + z0 := by omega
                  have hS_d : SafeStack 19 ((c + z0) :: ds) := safeStack19_d_ds hd10 hds
                  have hne1_d : ((c + z0) :: ds) ≠ [1] := by
                    intro h; injection h with h1; omega
                  have hx1_21 : 21 ≤ k + 2 * z0 + 2 := by
                    rcases dec_or (39 ≤ z0) with hz39 | hz_lt39
                    · omega
                    · rcases h39 (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl, _⟩ <;> omega
                  have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, ds⟩ = true := by
                    dsimp only [stepGuards]
                    change (GoodPhiW (c + z0 - 1) ds false &&
                      if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) ds &&
                        if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                        if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then
                          GoodDs ((k + 2 * z0 + 2) :: (c + z0) :: ds) else true) = true
                    rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                      if_neg hnot_ev, if_pos hod_sm]
                    exact hS_d.2.2 (k + 2 * z0 + 2) (by omega)
                  refine ⟨hg, fun N => ?_⟩
                  dsimp only [stepSegs]
                  change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
                  rw [if_neg hm_gt1, if_neg hnot_ev, if_pos hod_sm]
                  have hm_sub : m' + 1 - 1 = m' := by omega
                  rw [hm_sub]
                  set x1 := k + 2 * z0 + 2
                  rcases dec_or (x1 ≤ 47) with hx47 | hx48
                  · have hx_lo : 23 ≤ x1 ∨ (x1 = 21 ∧ SafeStack 19 ((c + z0) :: ds)) := by
                      rcases dec_or (x1 = 21) with h21 | hne21
                      · exact Or.inr ⟨h21, hS_d⟩
                      · rcases dec_or (39 ≤ z0) with hz39 | hz_lt39
                        · omega
                        · rcases h39 (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl, _⟩ <;> omega
                    exact loop_k1_le47 hne1_d (safeStack_mono (by decide) hS_d)
                      hx_lo hx47 hv_rest (by omega)
                      (fun _ z phi _ hz hphi38 _ hbz =>
                        pop_y_d_leads hbz hd10 hds (by omega) hphi38)
                      (fun _ _ _ hb1 =>
                        bounce_d_leads hb1 hds_cz (h_bounce_cz hd10 (x1 - 1) (by omega)))
                      (fun _ _ _ hb2 =>
                        bounce_d_leads hb2 hds_cz (h_bounce_cz hd10 (x1 - 2) (by omega)))
                      (fun _ c' k' p1 p2 _ hc' hk'41 hk'c hvp => by
                        subst hc'
                        have hfp := fzOf_ge_40 hvp
                        exact chainLeadsUpTo_here (rootInv_of_D (d := c + z0) (by omega) hds_cz
                          (validTail40_of_validSegs40 hvp) (by omega) (by omega) hk'c
                          (by omega) (by omega) (by omega)))
                  · exact chainLeadsUpTo_trans
                      ((excursion_bundle N).2 19 ((c + z0) :: ds) rest zl m' 1 x1 39 0
                        (by decide) hS_d (Or.inl hne1_d) hv_rest
                        (by omega) (by decide) (by omega) (by decide) (by omega)
                        (by omega) (by omega) (by omega) (by omega))
                      (fun _ _ _ hex => by
                        rcases hex with ⟨phi, hphi, hb⟩ | ⟨y, phi, hy, hphi38, _, hb⟩
                        · have hb_cases :
                            (c + z0 = 8 ∧ (phi = 16 ∨ phi = 17 ∨ 38 ≤ phi)) ∨
                            (c + z0 = 9 ∧ 19 ≤ phi) ∨
                            (10 ≤ c + z0 ∧ c + z0 ≤ 18 ∧ 19 ≤ phi ∧
                              (12 ≤ c + z0 → (c + z0) % 2 = 0 → 23 ≤ phi)) ∨
                            (c + z0 = 19 ∧ 37 ≤ phi) ∨
                            (20 ≤ c + z0 ∧ 38 ≤ phi) := by
                            rcases dec_or (c + z0 ≤ 18) with h_le18 | h_ge19
                            · exact Or.inr (Or.inr (Or.inl ⟨hd10, h_le18, by omega,
                                fun _ _ => by omega⟩))
                            · rcases dec_or (c + z0 = 19) with h_eq19 | h_ge20
                              · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h_eq19, by omega⟩)))
                              · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, hphi⟩)))
                          exact bounce_d_leads hb hds_cz hb_cases
                        · exact pop_y_d_leads hb hd10 hds (by omega) hphi38)
            · -- `m0 >= 2 * kz + 12`:
              have hg : stepGuards ⟨false, (z0, m' + 1) :: rest, zl, c, k, 0, ds⟩ = true := by
                dsimp only [stepGuards]
                change (GoodPhiW (c + z0 - 1) ds false &&
                  if m' + 1 = 1 then _ else GoodPsi (c + z0 - 1) ds &&
                    if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then true else
                    if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else true) = true
                rw [hphiw, Bool.true_and, if_neg hm_gt1, hpsi_cz, Bool.true_and,
                  if_neg hnot_ev, if_neg hbig_m]
              refine ⟨hg, fun N => ?_⟩
              dsimp only [stepSegs]
              change ChainLeadsUpTo N (if m' + 1 = 1 then _ else
                if (m' + 1) % 2 = 0 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 10 then _ else
                if (m' + 1) % 2 = 1 ∧ m' + 1 ≤ 2 * (k + 2 * z0) + 11 then _ else _) _
              rw [if_neg hm_gt1, if_neg hnot_ev, if_neg hbig_m]
              have hnorm : normSeg 0 (m' + 1 - 4) = (0, (m' - 4) + 1) := by
                dsimp only [normSeg]; rw [if_neg (by omega)]; congr 1; omega
              rw [hnorm]
              have hbc : IsBounce (k + 2 * z0 + 2) ((c + z0) :: ds)
                  ⟨true, (0, (m' - 4) + 1) :: rest, zl, k + 2 * z0 + 2, 0,
                    2 * (k + 2 * z0) + 6, (c + z0) :: ds⟩ := by
                have h := IsBounce.cons (z0 := 0) (m := m' - 4) (zl := zl)
                  (cp1 := k + 2 * z0 + 2) (kb := 0) (mrg := 2 * (k + 2 * z0) + 6)
                  (rest := rest) (ds := (c + z0) :: ds) hv_rest (by omega)
                    (by split_ifs <;> omega)
                simpa only [Nat.add_zero] using h
              rcases dec_or (c + z0 = 8) with h_eq8 | h_ge9
              · obtain ⟨m0_, rest_, hseg_eq, rfl, rfl, _, _⟩ := h8 h_eq8
                injection hseg_eq with hhd _
                injection hhd with hz0_eq _
                subst hz0_eq
                exact bounce_d_leads hbc hds_cz (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)
              · rcases dec_or (c + z0 = 9) with h_eq9 | h_ge10
                · have hck1 : c = 1 ∧ k = 1 := by
                    rcases h39 (by omega) with h | ⟨_, _, hz20⟩
                    · exact h
                    · omega
                  rcases hck1 with ⟨rfl, rfl⟩
                  exact bounce_d_leads hbc hds_cz (Or.inr (Or.inl ⟨h_eq9, by omega⟩))
                · exact bounce_d_leads hbc hds_cz (h_bounce_cz (by omega) (k + 2 * z0 + 2)
                  (by omega))

theorem root0_advances {s : SegState}
    (hb : s.b = false) (hmrg : s.mrg = 0) (hr : Root0 s) :
    ChainAdvances s RootInv := by
  rcases hr with ha | hb0
  · exact root0A_advances hb hmrg ha
  · exact root0B_advances hb hmrg hb0

-- ============================================================================
-- Master Root Advancement & Unconditional `inv_s0`
-- ============================================================================

theorem root_advances : ∀ s, RootInv s → ChainAdvances s RootInv := by
  intro s ⟨hb, hmrg, hroot⟩
  rcases hroot with h0 | h1 | h31 | hD | hD1
  · exact root0_advances hb hmrg h0
  · exact root1_advances hb hmrg h1
  · exact root31_advances hb hmrg h31
  · exact rootD_advances hb hmrg hD
  · exact rootD1_advances hb hmrg hD1

def iterGuards : Nat → SegState → Bool
  | 0, _ => true
  | n + 1, s => stepGuards s && iterGuards n (stepSegs s)

def iterStep : Nat → SegState → SegState
  | 0, s => s
  | n + 1, s => iterStep n (stepSegs s)

theorem checkChainAux_of_iter (k : Nat) :
    ∀ fuel s, iterGuards k s = true →
      (∀ f, checkChainAux f (iterStep k s).b (encSegs (iterStep k s).segs (iterStep k s).zl)
        (iterStep k s).cp1 (iterStep k s).kb (iterStep k s).mrg (iterStep k s).ds = true) →
      checkChainAux fuel s.b (encSegs s.segs s.zl) s.cp1 s.kb s.mrg s.ds = true := by
  induction k with
  | zero =>
    intro fuel s _ h
    exact h fuel
  | succ k ih =>
    intro fuel s hg h
    cases fuel with
    | zero => rfl
    | succ f =>
      dsimp only [iterGuards] at hg
      have hg1 : stepGuards s = true := by
        cases hgs : stepGuards s <;> simp_all
      have hg2 : iterGuards k (stepSegs s) = true := by
        cases hgs : stepGuards s <;> simp_all
      rw [checkChainAux_eq_of_guards f s hg1]
      exact ih f (stepSegs s) hg2 h

theorem inv_s0 : Inv (.ModeB_ge3 [] 1 1 []) := by
  refine ⟨rfl, fun fuel => ?_⟩
  change checkChainAux fuel true (encSegs [] 0) 3 0 8 [1] = true
  have hg28 : iterGuards 28 ⟨true, [], 0, 3, 0, 8, [1]⟩ = true := rfl
  have hs28 : iterStep 28 ⟨true, [], 0, 3, 0, 8, [1]⟩ =
      ⟨false, [(56, 223)], 489, 10, 21, 0, []⟩ := rfl
  refine checkChainAux_of_iter 28 fuel ⟨true, [], 0, 3, 0, 8, [1]⟩ hg28 (fun f => ?_)
  rw [hs28]
  exact checkChainAux_true_of_advances root_advances f
    ⟨false, [(56, 223)], 489, 10, 21, 0, []⟩
    (rootInv_of_0B (Or.inl rfl) ⟨(fun _ h => nomatch h),
      by decide⟩ (by decide) (by decide) (by decide)
      (by decide) (by decide) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ _ _ _ hcz9 => absurd hcz9 (by decide)))


end ChainClosure

theorem is_does_not_halt : IsNotHalt target_tm := by
  exact nonhalt_of_Inv_s0 ChainClosure.inv_s0

end

public section

theorem is_not_halt : IsNotHalt target := by
  rw [target_eq]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA
