/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Calculi.WordCalculusC
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Word Calculus Engine D (`BusyBeaver.Calculi.WordCalculusD`)

Formal word-rewriting calculus for structured tape transformations,
providing verified macro-step reductions and tile segment chains for family D.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.WordCalculus
set_option quotPrecheck false
set_option maxRecDepth 4000000

variable {α β γ : Type*}
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
private abbrev t : BitWord := [1, 1, 0, 0]
private abbrev d0 : BitWord := [0, 0]
private abbrev d1 : BitWord := [1, 0]
open Word
local notation "WordList" => List Word
def EntrySpec (q : Nat) (av high : WordList) (lim : Nat) : Prop :=
  let pre := List.replicate q V ++ av
  let alpha := wordMass pre
  5 <= q /\
  wordScale (List.replicate 16 V) * (1 / 2) <= alpha /\
  alpha <= wordScale (List.replicate 16 V) /\
  (3 / 2) * alpha * wordScale high <= wordMassK high /\
  wordMassK high + 1 <= (5 / 2) * alpha * wordScale high /\
  wordScale pre * (lim : Rat) <= alpha * 1024
theorem entrySpec_scale_bounds (p : Nat) (alpha : Rat)
    (hL : wordScale (List.replicate p V) * (1 / 2) <= alpha)
    (hR : alpha <= wordScale (List.replicate p V)) :
    1 / 2 <= alpha * ((2 ^ p : Nat) : Rat) /\ alpha * ((2 ^ p : Nat) : Rat) <= 1 := by
  have hW := (wordMass_and_scale_replicate_V p).2
  have hPos := rat_pow_two_pos p
  constructor <;> nlinarith
def checkEntryOne (q : Nat) (av high : WordList) (lim : Nat) (orig : WordList) : Bool :=
  match splitPrefixDigits orig with
  | none => false
  | some (u, tail) =>
    match stripWordPrefix [Q] tail.reverse with
    | none => false
    | some rd =>
      let da := rd.reverse
      match stripWordPrefix (List.replicate q V ++ av) u, heightShift u 0 with
      | some rest, some H =>
        if 29 <= H then
          if H == da.length then
            let (carry, _eff) := evalEffect 0 u
            let (last_c, db) := evalEffect carry da
            if last_c == 1 then
              match stripWordPrefix (List.replicate 7 Q) db,
                    stripWordPrefix high.reverse db.reverse with
              | some _, some _ =>
                decide (massUpperBound 65536 65536 rest.reverse 0 <= lim)
              | _, _ => false
            else false
          else false
        else false
      | _, _ => false
theorem good_of_checkEntryOne (q : Nat) (av high : WordList) (lim : Nat) (orig : WordList)
    (hEntry : EntrySpec q av high lim)
    (hCheck : checkEntryOne q av high lim orig = true) :
    AggState av 16 q orig := by
  rcases hEntry with ⟨hQ, hAlphaLow, hAlphaHigh, hDlow, hDhigh, hMassLimit⟩
  unfold checkEntryOne at hCheck
  cases hC : splitPrefixDigits orig with
  | none => rw [hC] at hCheck; contradiction
  | some utail =>
    rcases utail with ⟨u, tail⟩
    rw [hC] at hCheck; dsimp only at hCheck
    cases hTop : stripWordPrefix [Q] tail.reverse with
    | none => rw [hTop] at hCheck; contradiction
    | some rd =>
      rw [hTop] at hCheck; dsimp only at hCheck
      cases hStart : stripWordPrefix (List.replicate q V ++ av) u with
      | none => rw [hStart] at hCheck; contradiction
      | some rest =>
        rw [hStart] at hCheck
        cases hHeight : heightShift u 0 with
        | none => rw [hHeight] at hCheck; contradiction
        | some H =>
          rw [hHeight] at hCheck; dsimp only at hCheck
          split_ifs at hCheck with hHbound hWidth hLast
          simp only [beq_iff_eq] at hWidth
          have hE := evalEffect_sound u 0
          generalize hEff : evalEffect 0 u = ce at hCheck hE hLast
          rcases ce with ⟨carry, eff⟩
          dsimp only at hCheck hE hLast
          have hF := evalEffect_sound rd.reverse carry
          generalize hEffD : evalEffect carry rd.reverse = ldb at hCheck hF hLast
          rcases ldb with ⟨last_c, db⟩
          dsimp only at hCheck hF hLast
          simp only [beq_iff_eq] at hLast; subst hLast
          cases hLow : stripWordPrefix (List.replicate 7 Q) db with
          | none => rw [hLow] at hCheck; contradiction
          | some lo =>
            rw [hLow] at hCheck
            cases hHigh : stripWordPrefix high.reverse db.reverse with
            | none => rw [hHigh] at hCheck; contradiction
            | some hi =>
              rw [hHigh] at hCheck; dsimp only at hCheck
              have hMassNat : massUpperBound 65536 65536 rest.reverse 0 <= lim :=
                of_decide_eq_true hCheck
              have hMassQ : ((massUpperBound 65536 65536 rest.reverse 0 : Nat) : Rat) <=
                (lim : Rat) := by
                exact_mod_cast hMassNat
              have hR := massUpperBound_le 65536 65536 rest 0
              have hSplit := wordMass_eq_add rest
              have hSpre := wordScale_pos (List.replicate q V ++ av)
              have hMassBound : wordScale (List.replicate q V ++ av) * wordMass rest <=
                  wordMass (List.replicate q V ++ av) * (1 / 64) := by
                have h1 : 65536 * wordMass rest <= (lim : Rat) := by push_cast at hR; linarith
                nlinarith
              rcases splitPrefixDigits_sound orig u tail hC with ⟨hOrig, hDig⟩
              have hEnd := splitPrefixDigits_ends_with_V orig u tail hC
              have hTop_eq := stripWordPrefix_sound [Q] tail.reverse rd hTop
              have hTail : tail = rd.reverse ++ [Q] := by
                have hRev := congrArg List.reverse hTop_eq
                simpa using hRev
              rw [hTail, List.all_append, Bool.and_eq_true] at hDig
              rcases exists_digitVal_of_all_isDigitWord rd.reverse hDig.1 with ⟨A, hDA⟩
              rw [<- hWidth] at hDA
              rcases wordEffect_digitVal hF hDA with ⟨B, hDB, hSum⟩
              have hStart_eq := stripWordPrefix_sound (List.replicate q V ++ av) u rest hStart
              have hHeight_eq : wordScale u * ((2 ^ H : Nat) : Rat) = 1 := by
                have hsp := heightShift_sound u 0 H hHeight
                simpa using hsp
              have hHigh' : ∃ x, db = x ++ high := by
                have hHi_eq := stripWordPrefix_sound high.reverse db.reverse hi hHigh
                have hRev := congrArg List.reverse hHi_eq
                rw [List.reverse_reverse, List.reverse_append, List.reverse_reverse] at hRev
                exact ⟨hi.reverse, hRev⟩
              rcases good_of_aggState_entry u high (wordMass (List.replicate q V ++ av))
                hDB hHeight_eq hHigh' hDlow hDhigh with ⟨hDlo, hDhi⟩
              rcases entrySpec_scale_bounds 16 (wordMass (List.replicate q V ++
                av)) hAlphaLow hAlphaHigh
                with ⟨hApLow, hApHigh⟩
              have hOrig_full : orig = u ++ rd.reverse ++ [Q] := by
                rw [hOrig, hTail, <- List.append_assoc]
              rw [hOrig_full]
              refine AggState.intro 16 q H u A rd.reverse carry eff B db (1 / 32)
                (wordMass (List.replicate q V ++ av))
                (by omega) hQ hHbound ⟨rest, hStart_eq⟩ hEnd rfl
                hApLow hApHigh hHeight_eq hDA hE (by omega) hDB
                (Reserve.even 5 (1 / 32) (by norm_num))
                (by rw [hStart_eq, wordMass_append]; linarith)
                hDlo hDhi ⟨lo, stripWordPrefix_sound (List.replicate 7 Q) db lo hLow⟩
def checkEntryTwo (q : Nat) (av high : WordList) (lim : Nat) (orig : WordList) (c1 c2 : Nat) : Bool
    :=
  match splitPrefixDigits orig with
  | none => false
  | some (u, tail) =>
    match stripWordPrefix [Q] tail.reverse with
    | none => false
    | some rd =>
      let da:=rd.reverse
      match stripWordPrefix (List.replicate q V ++ av) u, heightShift u 0 with
      | some rest, some H =>
        if 29 <= H then
          if H == da.length then
            let u1:=u.take 500
            let u2:=u.drop 500
            if (evalEffect 0 u1).1 == c1 then
              if (evalEffect c1 u2).1 == c2 then
                let (last_c, db):=evalEffect c2 da
                if last_c == 1 then
                  match stripWordPrefix (List.replicate 7 Q) db,
                        stripWordPrefix high.reverse db.reverse with
                  | some _, some _ =>
                    decide (massUpperBound 65536 65536 rest.reverse 0 <= lim)
                  | _, _ => false
                else false
              else false
            else false
          else false
        else false
      | _, _ => false
theorem good_of_checkEntryTwo (q : Nat) (av high : WordList) (lim : Nat) (orig : WordList) (c1 c2 :
    Nat)
    (hEntry : EntrySpec q av high lim)
    (hCheck : checkEntryTwo q av high lim orig c1 c2 = true) :
    AggState av 16 q orig:= by
  rcases hEntry with ⟨hQ, hAlphaLow, hAlphaHigh, hDlow, hDhigh, hMassLimit⟩
  unfold checkEntryTwo at hCheck
  cases hC : splitPrefixDigits orig with
  | none => rw [hC] at hCheck; contradiction
  | some utail =>
    rcases utail with ⟨u, tail⟩
    rw [hC] at hCheck; dsimp only at hCheck
    cases hTop : stripWordPrefix [Q] tail.reverse with
    | none => rw [hTop] at hCheck; contradiction
    | some rd =>
      rw [hTop] at hCheck; dsimp only at hCheck
      cases hStart : stripWordPrefix (List.replicate q V ++ av) u with
      | none => rw [hStart] at hCheck; contradiction
      | some rest =>
        rw [hStart] at hCheck
        cases hHeight : heightShift u 0 with
        | none => rw [hHeight] at hCheck; contradiction
        | some H =>
          rw [hHeight] at hCheck; dsimp only at hCheck
          split_ifs at hCheck with hHbound hWidth hc1 hc2 hLast
          simp only [beq_iff_eq] at hWidth hc1 hc2
          have hE1:=evalEffect_sound (u.take 500) 0
          rw [hc1] at hE1
          have hE2:=evalEffect_sound (u.drop 500) c1
          rw [hc2] at hE2
          have hE:=wordEffect_append hE1 hE2
          rw [List.take_append_drop] at hE
          have hF:=evalEffect_sound rd.reverse c2
          generalize hEffD : evalEffect c2 rd.reverse = ldb at hCheck hF hLast
          rcases ldb with ⟨last_c, db⟩
          dsimp only at hCheck hF hLast
          simp only [beq_iff_eq] at hLast; subst hLast
          cases hLow : stripWordPrefix (List.replicate 7 Q) db with
          | none => rw [hLow] at hCheck; contradiction
          | some lo =>
            rw [hLow] at hCheck
            cases hHigh : stripWordPrefix high.reverse db.reverse with
            | none => rw [hHigh] at hCheck; contradiction
            | some hi =>
              rw [hHigh] at hCheck; dsimp only at hCheck
              have hMassNat : massUpperBound 65536 65536 rest.reverse 0 <=
                lim:=of_decide_eq_true hCheck
              have hMassQ : ((massUpperBound 65536 65536 rest.reverse 0 : Nat) : ℚ) <=
                (lim : ℚ):= by
                exact_mod_cast hMassNat
              have hR:=massUpperBound_le 65536 65536 rest 0
              have hSplit:=wordMass_eq_add rest
              have hSpre:=wordScale_pos (List.replicate q V ++ av)
              have hMassBound : wordScale (List.replicate q V ++ av) * wordMass rest <=
                  wordMass (List.replicate q V ++ av) * (1 / 64):= by
                have h1 : 65536 * wordMass rest <= (lim : ℚ):= by push_cast at hR; linarith
                nlinarith
              rcases splitPrefixDigits_sound orig u tail hC with ⟨hOrig, hDig⟩
              have hEnd:=splitPrefixDigits_ends_with_V orig u tail hC
              have hTop_eq:=stripWordPrefix_sound [Q] tail.reverse rd hTop
              have hTail : tail = rd.reverse ++ [Q]:= by
                have hRev:=congrArg List.reverse hTop_eq
                simpa using hRev
              rw [hTail, List.all_append, Bool.and_eq_true] at hDig
              rcases exists_digitVal_of_all_isDigitWord rd.reverse hDig.1 with ⟨A, hDA⟩
              rw [<- hWidth] at hDA
              rcases wordEffect_digitVal hF hDA with ⟨B, hDB, hSum⟩
              have hStart_eq:=stripWordPrefix_sound (List.replicate q V ++ av) u rest hStart
              have hHeight_eq : wordScale u * ((2 ^ H : Nat) : ℚ) = 1:= by
                have hsp:=heightShift_sound u 0 H hHeight
                simpa using hsp
              have hHigh' : ∃ x, db = x ++ high:= by
                have hHi_eq:=stripWordPrefix_sound high.reverse db.reverse hi hHigh
                have hRev:=congrArg List.reverse hHi_eq
                rw [List.reverse_reverse, List.reverse_append, List.reverse_reverse] at hRev
                exact ⟨hi.reverse, hRev⟩
              rcases good_of_aggState_entry u high (wordMass (List.replicate q V ++ av))
                hDB hHeight_eq hHigh' hDlow hDhigh with ⟨hDlo, hDhi⟩
              rcases entrySpec_scale_bounds 16 (wordMass (List.replicate q V ++
                av)) hAlphaLow hAlphaHigh
                with ⟨hApLow, hApHigh⟩
              have hOrig_full : orig = u ++ rd.reverse ++ [Q]:= by
                rw [hOrig, hTail, <- List.append_assoc]
              rw [hOrig_full]
              refine AggState.intro 16 q H u A rd.reverse c2
                ((evalEffect 0 (u.take 500)).2 ++ (evalEffect c1 (u.drop 500)).2) B db (1 / 32)
                (wordMass (List.replicate q V ++ av))
                (by omega) hQ hHbound ⟨rest, hStart_eq⟩ hEnd rfl
                hApLow hApHigh hHeight_eq hDA hE (by omega) hDB
                (Reserve.even 5 (1 / 32) (by norm_num))
                (by rw [hStart_eq, wordMass_append]; linarith)
                hDlo hDhi ⟨lo, stripWordPrefix_sound (List.replicate 7 Q) db lo hLow⟩
def wordListBEq : WordList -> WordList -> Bool
  | [], [] => true
  | V :: a, V :: b => wordListBEq a b
  | K :: a, K :: b => wordListBEq a b
  | Q :: a, Q :: b => wordListBEq a b
  | _, _ => false
theorem wordListBEq_eq (a : WordList) :
    ∀ (b : WordList), wordListBEq a b = true -> a = b := by
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons _ _ => contradiction
  | cons w a ih =>
    intro b h
    cases b with
    | nil => cases w <;> contradiction
    | cons x b =>
      cases w <;> cases x <;> try contradiction
      all_goals
        dsimp [wordListBEq] at h
        rw [ih b h]
def optionWordListBEq : Option WordList -> Option WordList -> Bool
  | some a, some b => wordListBEq a b
  | none, none => true
  | _, _ => false
theorem optionWordListBEq_eq (a b : Option WordList) (h : optionWordListBEq a b = true) : a =
    b := by
  cases a with
  | none => cases b <;> first | rfl | contradiction
  | some a =>
    cases b with
    | none => contradiction
    | some b => exact congrArg some (wordListBEq_eq a b h)
theorem rounds_cons_of_evalStep {u v w : WordList} (h : optionWordListBEq (evalStep u) (some v) =
    true) (hr : Rounds v w) :
    Rounds u w :=
  Rounds.next (evalStep_sound u v (optionWordListBEq_eq (evalStep u) (some v) h)) hr
def checkStepTwoPieces (u1 u2 : WordList) (c1 k1 k2 : Nat) (v1 v2 da : WordList) : Bool :=
  let (c1', eff1) := evalEffect 0 u1
  let (c2', eff2) := evalEffect c1 u2
  if c1' == c1 && c2' == 1 then
    match evalPhaseScan 600 eff1 12, evalPhaseScan 600 eff2 k1 with
    | some (k1', v1'), some (k2', v2') =>
      if k1' == k1 && k2' == k2 && v1' == v1 && v2' == v2 then
        match decodeDigits 512 k2 with
        | some da' => da' == da
        | none => false
      else false
    | _, _ => false
  else false
theorem step_of_checkStepTwoPieces (u1 u2 : WordList) (c1 k1 k2 : Nat) (v1 v2 da : WordList)
    (hR : checkStepTwoPieces u1 u2 c1 k1 k2 v1 v2 da = true) :
    Step (u1 ++ u2) (V :: ((v1 ++ v2) ++ V :: (da ++ [Q]))) := by
  unfold checkStepTwoPieces at hR
  have hE1 := evalEffect_sound u1 0
  generalize hEff1 : evalEffect 0 u1 = ce1 at hR hE1
  rcases ce1 with ⟨c1', eff1⟩
  have hE2 := evalEffect_sound u2 c1
  generalize hEff2 : evalEffect c1 u2 = ce2 at hR hE2
  rcases ce2 with ⟨c2', eff2⟩
  dsimp only at hR hE1 hE2
  split_ifs at hR with hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  rcases hc with ⟨hc1, hc2⟩
  subst c1'; subst c2'
  cases hS1 : evalPhaseScan 600 eff1 12 with
  | none => rw [hS1] at hR; contradiction
  | some kv1 =>
    rw [hS1] at hR
    cases hS2 : evalPhaseScan 600 eff2 k1 with
    | none => rw [hS2] at hR; contradiction
    | some kv2 =>
      rw [hS2] at hR
      rcases kv1 with ⟨k1', v1'⟩
      rcases kv2 with ⟨k2', v2'⟩
      dsimp only at hR
      split_ifs at hR with hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      rcases hk with ⟨⟨⟨hk1, hk2⟩, hv1⟩, hv2⟩
      subst k1'; subst k2'; subst v1'; subst v2'
      cases hPw : decodeDigits 512 k2 with
      | none => rw [hPw] at hR; contradiction
      | some da' =>
        rw [hPw] at hR
        dsimp only at hR
        simp only [beq_iff_eq] at hR; subst da'
        rcases evalPhaseScan_sound 600 eff1 12 k1 v1 hS1 with ⟨a1, b1, hI1⟩
        rcases evalPhaseScan_sound 600 eff2 k1 k2 v2 hS2 with ⟨a2, b2, hI2⟩
        rcases phaseScan_append hI1 hI2 with ⟨a, b, hI, _, _⟩
        rcases decodeDigits_sound 512 k2 da hPw with ⟨A, J, hDA, hSum⟩
        exact Step.intro (u1 ++ u2) (eff1 ++ eff2) k2 (v1 ++ v2) a b J A da
          (wordEffect_append hE1 hE2) hI hDA hSum
def checkStepThreePieces (u1 u2 u3 : WordList) (c1 c2 k1 k2 k3 : Nat) (v1 v2 v3 da1 da2 : WordList)
    : Bool :=
  let (c1', eff1) := evalEffect 0 u1
  let (c2', eff2) := evalEffect c1 u2
  let (c3', eff3) := evalEffect c2 u3
  if c1' == c1 && c2' == c2 && c3' == 1 then
    match evalPhaseScan 600 eff1 12, evalPhaseScan 600 eff2 k1, evalPhaseScan 600 eff3 k2 with
    | some (k1', v1'), some (k2', v2'), some (k3', v3') =>
      if k1' == k1 && k2' == k2 && k3' == k3 && v1' == v1 && v2' == v2 && v3' == v3 then
        match decodeDigits 512 k3 with
        | some da' => da' == (da1 ++ da2)
        | none => false
      else false
    | _, _, _ => false
  else false
theorem step_of_checkStepThreePieces (u1 u2 u3 : WordList) (c1 c2 k1 k2 k3 : Nat) (v1 v2 v3 da1 da2
    : WordList)
    (hR : checkStepThreePieces u1 u2 u3 c1 c2 k1 k2 k3 v1 v2 v3 da1 da2 = true) :
    Step (u1 ++ u2 ++ u3) (V :: ((v1 ++ v2 ++ v3) ++ V :: ((da1 ++ da2) ++ [Q]))) := by
  unfold checkStepThreePieces at hR
  have hE1 := evalEffect_sound u1 0
  generalize hEff1 : evalEffect 0 u1 = ce1 at hR hE1
  rcases ce1 with ⟨c1', eff1⟩
  have hE2 := evalEffect_sound u2 c1
  generalize hEff2 : evalEffect c1 u2 = ce2 at hR hE2
  rcases ce2 with ⟨c2', eff2⟩
  have hE3 := evalEffect_sound u3 c2
  generalize hEff3 : evalEffect c2 u3 = ce3 at hR hE3
  rcases ce3 with ⟨c3', eff3⟩
  dsimp only at hR hE1 hE2 hE3
  split_ifs at hR with hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  rcases hc with ⟨⟨hc1, hc2⟩, hc3⟩
  subst c1'; subst c2'; subst c3'
  cases hS1 : evalPhaseScan 600 eff1 12 with
  | none => rw [hS1] at hR; contradiction
  | some kv1 =>
    rw [hS1] at hR
    cases hS2 : evalPhaseScan 600 eff2 k1 with
    | none => rw [hS2] at hR; contradiction
    | some kv2 =>
      rw [hS2] at hR
      cases hS3 : evalPhaseScan 600 eff3 k2 with
      | none => rw [hS3] at hR; contradiction
      | some kv3 =>
        rw [hS3] at hR
        rcases kv1 with ⟨k1', v1'⟩
        rcases kv2 with ⟨k2', v2'⟩
        rcases kv3 with ⟨k3', v3'⟩
        dsimp only at hR
        split_ifs at hR with hk
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        rcases hk with ⟨⟨⟨⟨⟨hk1, hk2⟩, hk3⟩, hv1⟩, hv2⟩, hv3⟩
        subst k1'; subst k2'; subst k3'; subst v1'; subst v2'; subst v3'
        cases hPw : decodeDigits 512 k3 with
        | none => rw [hPw] at hR; contradiction
        | some da' =>
          rw [hPw] at hR
          dsimp only at hR
          simp only [beq_iff_eq] at hR; subst da'
          rcases evalPhaseScan_sound 600 eff1 12 k1 v1 hS1 with ⟨a1, b1, hI1⟩
          rcases evalPhaseScan_sound 600 eff2 k1 k2 v2 hS2 with ⟨a2, b2, hI2⟩
          rcases evalPhaseScan_sound 600 eff3 k2 k3 v3 hS3 with ⟨a3, b3, hI3⟩
          rcases phaseScan_append hI1 hI2 with ⟨a12, b12, hI12, _, _⟩
          rcases phaseScan_append hI12 hI3 with ⟨a, b, hI, _, _⟩
          rcases decodeDigits_sound 512 k3 (da1 ++ da2) hPw with ⟨A, J, hDA, hSum⟩
          exact Step.intro (u1 ++ u2 ++ u3) (eff1 ++ eff2 ++ eff3) k3 (v1 ++ v2 ++
            v3) a b J A (da1 ++ da2)
            (wordEffect_append (wordEffect_append hE1 hE2) hE3) hI hDA hSum
def checkEntryThreePieces (q : Nat) (av high : WordList) (lim : Nat)
    (u1 u2 u3 da1 da2 : WordList) (h1 h2 H c1 c2 carry cda r1 r2 : Nat) : Bool :=
  match stripWordPrefix (List.replicate q V ++ av) u1,
        stripWordPrefix [V] u3.reverse,
        heightShift u1 0, heightShift u2 h1, heightShift u3 h2 with
  | some rest1, some _u3_init_rev, some h1', some h2', some H' =>
    if h1' == h1 && h2' == h2 && H' == H && decide (29 <= H) then
      if H == (da1 ++ da2).length && (da1 ++ da2).all isDigitWord then
        let (c1', _) := evalEffect 0 u1
        let (c2', _) := evalEffect c1 u2
        let (c3', _) := evalEffect c2 u3
        let (cda', db1) := evalEffect carry da1
        let (last_c, db2) := evalEffect cda da2
        if c1' == c1 && c2' == c2 && c3' == carry && cda' == cda && last_c == 1 then
          match stripWordPrefix (List.replicate 7 Q) (db1 ++ db2),
                stripWordPrefix high.reverse (db1 ++ db2).reverse with
          | some _, some _ =>
            let r1' := massUpperBound 65536 65536 u3.reverse 0
            let r2' := massUpperBound 65536 65536 u2.reverse r1
            let r3' := massUpperBound 65536 65536 rest1.reverse r2
            (r1' == r1) && (r2' == r2) && decide (r3' <= lim)
          | _, _ => false
        else false
      else false
    else false
  | _, _, _, _, _ => false
theorem good_of_checkEntryThreePieces (q : Nat) (av high : WordList) (lim : Nat)
    (u1 u2 u3 da1 da2 : WordList) (h1 h2 H c1 c2 carry cda r1 r2 : Nat)
    (hEntry : EntrySpec q av high lim)
    (hCheck : checkEntryThreePieces q av high lim u1 u2 u3 da1 da2 h1 h2 H c1 c2 carry cda r1 r2 =
      true) :
    AggState av 16 q ((u1 ++ u2 ++ u3) ++ (da1 ++ da2) ++ [Q]) := by
  rcases hEntry with ⟨hQ, hAlphaLow, hAlphaHigh, hDlow, hDhigh, hMassLimit⟩
  unfold checkEntryThreePieces at hCheck
  cases hStart : stripWordPrefix (List.replicate q V ++ av) u1 with
  | none => rw [hStart] at hCheck; contradiction
  | some rest1 =>
    rw [hStart] at hCheck
    cases hEnd : stripWordPrefix [V] u3.reverse with
    | none => rw [hEnd] at hCheck; contradiction
    | some u3_init_rev =>
      rw [hEnd] at hCheck
      cases hH1 : heightShift u1 0 with
      | none => rw [hH1] at hCheck; contradiction
      | some h1' =>
        rw [hH1] at hCheck
        cases hH2 : heightShift u2 h1 with
        | none => rw [hH2] at hCheck; contradiction
        | some h2' =>
          rw [hH2] at hCheck
          cases hH3 : heightShift u3 h2 with
          | none => rw [hH3] at hCheck; contradiction
          | some H' =>
            rw [hH3] at hCheck; dsimp only at hCheck
            have hE1 := evalEffect_sound u1 0
            generalize hEff1 : evalEffect 0 u1 = ce1 at hCheck hE1
            rcases ce1 with ⟨c1', eff1⟩
            have hE2 := evalEffect_sound u2 c1
            generalize hEff2 : evalEffect c1 u2 = ce2 at hCheck hE2
            rcases ce2 with ⟨c2', eff2⟩
            have hE3 := evalEffect_sound u3 c2
            generalize hEff3 : evalEffect c2 u3 = ce3 at hCheck hE3
            rcases ce3 with ⟨c3', eff3⟩
            have hF1 := evalEffect_sound da1 carry
            generalize hEffD1 : evalEffect carry da1 = ldb1 at hCheck hF1
            rcases ldb1 with ⟨cda', db1⟩
            have hF2 := evalEffect_sound da2 cda
            generalize hEffD2 : evalEffect cda da2 = ldb2 at hCheck hF2
            rcases ldb2 with ⟨last_c, db2⟩
            dsimp only at hCheck hE1 hE2 hE3 hF1 hF2
            split_ifs at hCheck with hIf1 hIf2 hIf3
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hIf1 hIf2 hIf3
            rcases hIf1 with ⟨⟨⟨hh1, hh2⟩, hH⟩, hHbound⟩
            subst h1'; subst h2'; subst H'
            rcases hIf2 with ⟨hWidth, hDig⟩
            rcases hIf3 with ⟨⟨⟨⟨hc1, hc2⟩, hc3⟩, hcda⟩, hlast⟩
            subst c1'; subst c2'; subst c3'; subst cda'; subst last_c
            cases hLow : stripWordPrefix (List.replicate 7 Q) (db1 ++ db2) with
            | none => rw [hLow] at hCheck; contradiction
            | some lo =>
              rw [hLow] at hCheck
              cases hHigh : stripWordPrefix high.reverse (db1 ++ db2).reverse with
              | none => rw [hHigh] at hCheck; contradiction
              | some hi =>
                rw [hHigh] at hCheck; dsimp only at hCheck
                simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hCheck
                rcases hCheck with ⟨⟨hR1_eq, hR2_eq⟩, hR3_le⟩
                have hRF1 := massUpperBound_le 65536 65536 u3 0
                rw [hR1_eq] at hRF1
                have hRF2 := massUpperBound_le 65536 65536 u2 r1
                rw [hR2_eq] at hRF2
                have hRF3 := massUpperBound_le 65536 65536 rest1 r2
                have hMassQ : ((massUpperBound 65536 65536 rest1.reverse r2 : Nat) : Rat) <=
                  (lim : Rat) := by
                  exact_mod_cast hR3_le
                have hSp3 := wordMass_eq_add u3
                have hSp2 := wordMass_eq_add u2
                have hSp1 := wordMass_eq_add rest1
                have hSu2 := wordScale_pos u2
                have hSr1 := wordScale_pos rest1
                have hSpre := wordScale_pos (List.replicate q V ++ av)
                have hM3 : 65536 * wordMass u3 <= (r1 : Rat) := by push_cast at hRF1; linarith
                have hM2 : 65536 * (wordMass u2 + wordScale u2 * wordMass u3) <= (r2 : Rat) := by
                  push_cast at hRF2; nlinarith
                have hM1 : 65536 * (wordMass rest1 + wordScale rest1 * (wordMass u2 +
                  wordScale u2 * wordMass u3)) <= (lim : Rat) := by
                  push_cast at hRF3; nlinarith
                have hMrest : wordMass (rest1 ++ u2 ++ u3) =
                    wordMass rest1 + wordScale rest1 * (wordMass u2 +
                      wordScale u2 * wordMass u3) := by
                  rw [wordMass_append, wordMass_append, wordScale_append]; ring
                have hMassBound : wordScale (List.replicate q V ++ av) * wordMass (rest1 ++
                  u2 ++ u3) <=
                    wordMass (List.replicate q V ++ av) * (1 / 64) := by
                  rw [hMrest]; nlinarith
                have hStart_eq := stripWordPrefix_sound (List.replicate q V ++ av) u1 rest1 hStart
                have hU_start : u1 ++ u2 ++ u3 = (List.replicate q V ++ av) ++ (rest1 ++ u2 ++
                  u3) := by
                  rw [hStart_eq]; simp [List.append_assoc]
                have hEnd_eq := stripWordPrefix_sound [V] u3.reverse u3_init_rev hEnd
                have hU3_end : u3 = u3_init_rev.reverse ++ [V] := by
                  have hRev := congrArg List.reverse hEnd_eq
                  simpa using hRev
                have hU_end : ∃ rest, u1 ++ u2 ++ u3 = rest ++ [V] :=
                  ⟨u1 ++ u2 ++ u3_init_rev.reverse, by rw [hU3_end]; simp [List.append_assoc]⟩
                have hSpH1 := heightShift_sound u1 0 h1 hH1
                have hSpH2 := heightShift_sound u2 h1 h2 hH2
                have hSpH3 := heightShift_sound u3 h2 H hH3
                have hHeight_eq : wordScale (u1 ++ u2 ++ u3) * ((2 ^ H : Nat) : Rat) = 1 := by
                  rw [wordScale_append, wordScale_append]
                  calc (wordScale u1 * wordScale u2 * wordScale u3) * ((2 ^ H : Nat) : Rat)
                    _ = wordScale u1 * wordScale u2 * (wordScale u3 * ((2 ^ H : Nat) : Rat)) :=
                      by ring
                    _ = wordScale u1 * (wordScale u2 * ((2 ^ h2 : Nat) : Rat)) :=
                      by rw [hSpH3]; ring
                    _ = wordScale u1 * ((2 ^ h1 : Nat) : Rat) := by rw [hSpH2]
                    _ = ((2 ^ 0 : Nat) : Rat) := hSpH1
                    _ = 1 := by norm_num
                rcases exists_digitVal_of_all_isDigitWord (da1 ++ da2) hDig with ⟨A, hDA⟩
                rw [<- hWidth] at hDA
                have hE : WordEffect 0 (u1 ++ u2 ++ u3) carry (eff1 ++ eff2 ++ eff3) :=
                  wordEffect_append (wordEffect_append hE1 hE2) hE3
                have hF : WordEffect carry (da1 ++ da2) 1 (db1 ++ db2) :=
                  wordEffect_append hF1 hF2
                rcases wordEffect_digitVal hF hDA with ⟨B, hDB, hSum⟩
                have hHigh' : ∃ x, db1 ++ db2 = x ++ high := by
                  have hHi_eq := stripWordPrefix_sound high.reverse (db1 ++ db2).reverse hi hHigh
                  have hRev := congrArg List.reverse hHi_eq
                  rw [List.reverse_reverse, List.reverse_append, List.reverse_reverse] at hRev
                  exact ⟨hi.reverse, hRev⟩
                rcases good_of_aggState_entry (u1 ++ u2 ++
                  u3) high (wordMass (List.replicate q V ++ av))
                  hDB hHeight_eq hHigh' hDlow hDhigh with ⟨hDlo, hDhi⟩
                rcases entrySpec_scale_bounds 16 (wordMass (List.replicate q V ++
                  av)) hAlphaLow hAlphaHigh
                  with ⟨hApLow, hApHigh⟩
                refine AggState.intro 16 q H (u1 ++ u2 ++ u3) A (da1 ++ da2) carry
                  (eff1 ++ eff2 ++ eff3) B (db1 ++ db2) (1 / 32)
                  (wordMass (List.replicate q V ++ av))
                  (by omega) hQ hHbound ⟨rest1 ++ u2 ++ u3, hU_start⟩ hU_end rfl
                  hApLow hApHigh hHeight_eq hDA hE (by omega) hDB
                  (Reserve.even 5 (1 / 32) (by norm_num))
                  (by rw [hU_start, wordMass_append]; linarith)
                  hDlo hDhi ⟨lo, stripWordPrefix_sound (List.replicate 7 Q) (db1 ++ db2) lo hLow⟩
def wordScaleDen : WordList -> Nat
  | [] => 1
  | V :: v => wordScaleDen v * 2
  | _ :: v => wordScaleDen v
def wordMassNum : WordList -> Nat
  | [] => 0
  | V :: v => wordMassNum v
  | _ :: v => wordScaleDen v + wordMassNum v * 2
def wordMassKNum : WordList -> Nat
  | [] => 0
  | V :: v => wordMassKNum v
  | K :: v => wordScaleDen v + wordMassKNum v * 2
  | Q :: v => wordMassKNum v * 2
def wordScaleNum : WordList -> Nat
  | [] => 1
  | V :: v => wordScaleNum v
  | _ :: v => wordScaleNum v * 2
theorem wordDyadic_sound (u : WordList) :
    (0 : Rat) < wordScaleDen u /\
    wordMass u * (wordScaleDen u : Rat) = wordMassNum u /\
    wordMassK u * (wordScaleDen u : Rat) = wordMassKNum u /\
    wordScale u * (wordScaleDen u : Rat) = wordScaleNum u := by
  induction u with
  | nil => simp [wordScaleDen, wordMass, wordMassNum, wordMassK, wordMassKNum, wordScale,
    wordScaleNum]
  | cons a v ih =>
    rcases ih with ⟨hd, he, hf, hh⟩
    cases a <;> (
      simp only [wordScaleDen, wordMass, wordMassNum, wordMassK, wordMassKNum, wordScale,
        wordScaleNum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      refine ⟨by linarith, by nlinarith, by nlinarith, by nlinarith⟩)
def checkEntrySpec (q : Nat) (av high : WordList) (lim : Nat) : Bool :=
  let pre := List.replicate q V ++ av
  let dp := wordScaleDen pre
  let ep := wordMassNum pre
  let hp := wordScaleNum pre
  let dh := wordScaleDen high
  let fh := wordMassKNum high
  let hh := wordScaleNum high
  let d16 := wordScaleDen (List.replicate 16 V)
  let h16 := wordScaleNum (List.replicate 16 V)
  decide (5 <= q /\
    h16 * dp <= 2 * ep * d16 /\
    ep * d16 <= h16 * dp /\
    3 * ep * hh <= 2 * fh * dp /\
    2 * (fh + dh) * dp <= 5 * ep * hh /\
    hp * lim <= ep * 1024)

theorem checkMassBound_sound (z1e_p z1h_p z1f_k z1h_k z1h_16 : Rat)
    (dp dk d16 ep hp fk hk h16 lim : Nat)
    (hdp : 0 < dp) (hdk : 0 < dk) (hd16 : 0 < d16)
    (hep : z1e_p * dp = ep) (hhp : z1h_p * dp = hp)
    (hfk : z1f_k * dk = fk) (hhk : z1h_k * dk = hk) (hh16 : z1h_16 * d16 = h16)
    (hN : (h16 * dp : Rat) ≤ 2 * ep * d16 ∧
          (ep * d16 : Rat) ≤ h16 * dp ∧
          (3 * ep * hk : Rat) ≤ 2 * fk * dp ∧
          (2 * (fk + dk) * dp : Rat) ≤ 5 * ep * hk ∧
          (hp * lim : Rat) ≤ ep * 1024) :
    z1h_16 ≤ 2 * z1e_p ∧ z1e_p ≤ z1h_16 ∧ 3 * z1e_p * z1h_k ≤ 2 * z1f_k ∧
    2 * (z1f_k + 1) ≤ 5 * z1e_p * z1h_k ∧ z1h_p * (lim : Rat) ≤ z1e_p * 1024 := by
  rcases hN with ⟨c1, c2, c3, c4, c5⟩
  rw [← hep, ← hh16] at c1 c2
  rw [← hep, ← hhk, ← hfk] at c3 c4
  rw [← hep, ← hhp] at c5
  have hdpQ : (0 : Rat) < dp := by exact_mod_cast hdp
  have hd16Q : (0 : Rat) < d16 := by exact_mod_cast hd16
  have hdkQ : (0 : Rat) < dk := by exact_mod_cast hdk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_pos hdpQ hd16Q]
  · nlinarith [mul_pos hdpQ hd16Q]
  · nlinarith [mul_pos hdpQ hdkQ]
  · nlinarith [mul_pos hdpQ hdkQ]
  · nlinarith [hdpQ]

theorem entrySpec_of_checkEntrySpec {q : Nat} {av high : WordList} {lim : Nat}
    (h : checkEntrySpec q av high lim = true) : EntrySpec q av high lim := by
  unfold checkEntrySpec at h
  dsimp only at h
  rcases of_decide_eq_true h with ⟨hq, n1, n2, n3, n4, n5⟩
  unfold EntrySpec
  rcases wordDyadic_sound (List.replicate q V ++ av) with ⟨hdp, hep, _, hhp⟩
  rcases wordDyadic_sound high with ⟨hdh, _, hfh, hhh⟩
  rcases wordDyadic_sound (List.replicate 16 V) with ⟨hd16, _, _, hh16⟩
  have c1 : (wordScaleNum (List.replicate 16 V) * wordScaleDen (List.replicate q V ++
    av) : Rat) ≤ 2 * wordMassNum (List.replicate q V ++
    av) * wordScaleDen (List.replicate 16 V) := by exact_mod_cast n1
  have c2 : (wordMassNum (List.replicate q V ++
    av) * wordScaleDen (List.replicate 16 V) : Rat) ≤
    wordScaleNum (List.replicate 16 V) * wordScaleDen (List.replicate q V ++ av) := by
    exact_mod_cast n2
  have c3 : (3 * wordMassNum (List.replicate q V ++
    av) * wordScaleNum high : Rat) ≤ 2 * wordMassKNum high * wordScaleDen (List.replicate q V ++
    av) := by exact_mod_cast n3
  have c4 : (2 * (wordMassKNum high + wordScaleDen high) * wordScaleDen (List.replicate q V ++
    av) : Rat) ≤ 5 * wordMassNum (List.replicate q V ++ av) * wordScaleNum high := by
    exact_mod_cast n4
  have c5 : (wordScaleNum (List.replicate q V ++
    av) * lim : Rat) ≤ wordMassNum (List.replicate q V ++ av) * 1024 := by exact_mod_cast n5
  rcases checkMassBound_sound
      (wordMass (List.replicate q V ++ av)) (wordScale (List.replicate q V ++
        av)) (wordMassK high) (wordScale high) (wordScale (List.replicate 16 V))
      (wordScaleDen (List.replicate q V ++
        av)) (wordScaleDen high) (wordScaleDen (List.replicate 16 V))
      (wordMassNum (List.replicate q V ++ av)) (wordScaleNum (List.replicate q V ++
        av)) (wordMassKNum high) (wordScaleNum high) (wordScaleNum (List.replicate 16 V)) lim
      (by exact_mod_cast hdp) (by exact_mod_cast hdh) (by exact_mod_cast hd16)
      hep hhp hfh hhh hh16 ⟨c1, c2, c3, c4, c5⟩ with ⟨g1, g2, g3, g4, g5⟩
  exact ⟨hq, by linarith, by linarith, by linarith, by linarith, by linarith⟩
theorem exists_heightShift_of_mass_lt (u : WordList) :
    ∀ (h : Nat), wordMass u < ((2 ^ h : Nat) : ℚ) -> ∃ H, heightShift u h = some H:= by
  induction u with
  | nil => intro h _; exact ⟨h, rfl⟩
  | cons w u ih =>
    intro h hM
    cases w
    · dsimp [wordMass, heightShift] at hM ⊢
      refine ih (h + 1) ?_
      rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]
      linarith
    · cases h with
      | zero =>
        dsimp [wordMass] at hM
        have hw:=(wordMass_nonneg u).1
        norm_num at hM
        linarith
      | succ h =>
        dsimp [wordMass, heightShift] at hM ⊢
        rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat] at hM
        exact ih h (by linarith)
    · cases h with
      | zero =>
        dsimp [wordMass] at hM
        have hw:=(wordMass_nonneg u).1
        norm_num at hM
        linarith
      | succ h =>
        dsimp [wordMass, heightShift] at hM ⊢
        rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat] at hM
        exact ih h (by linarith)
theorem wordEffect_add_pow_of_heightShift {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (hI : WordEffect n u b v) :
    ∀ (h H : Nat), heightShift u h = some H -> WordEffect (n + 2 ^ h) u (b + 2 ^ H) v:= by
  induction hI with
  | nil n =>
    intro h H hE
    injection hE with hE; subst hE
    exact WordEffect.nil (n + 2 ^ h)
  | @T n u b v _ ih =>
    intro h H hE
    dsimp [heightShift] at hE
    have hIH:=ih (h + 1) H hE
    have heq : 1 + (n + 2 ^ h) * 2 = (1 + n * 2) + 2 ^ (h + 1):= by
      rw [Nat.pow_succ]; omega
    rw [<- heq] at hIH
    exact WordEffect.T hIH
  | @d00 n u b v _ ih =>
    intro h H hE
    cases h with
    | zero => contradiction
    | succ h =>
      dsimp [heightShift] at hE
      have hIH:=ih h H hE
      have heq : (n + 2 ^ h) * 2 = n * 2 + 2 ^ (h + 1):= by
        rw [Nat.pow_succ]; omega
      rw [<- heq]
      exact WordEffect.d00 hIH
  | @d01 n u b v _ ih =>
    intro h H hE
    cases h with
    | zero => contradiction
    | succ h =>
      dsimp [heightShift] at hE
      have hIH:=ih h H hE
      have heq : 1 + (n + 2 ^ h) * 2 = (1 + n * 2) + 2 ^ (h + 1):= by
        rw [Nat.pow_succ]; omega
      rw [<- heq]
      exact WordEffect.d01 hIH
  | @d10 n u b v _ ih =>
    intro h H hE
    cases h with
    | zero => contradiction
    | succ h =>
      dsimp [heightShift] at hE
      have hIH:=ih h H hE
      have heq : (n + 2 ^ h) * 2 = n * 2 + 2 ^ (h + 1):= by
        rw [Nat.pow_succ]; omega
      rw [<- heq]
      exact WordEffect.d10 hIH
  | @d11 n u b v _ ih =>
    intro h H hE
    cases h with
    | zero => contradiction
    | succ h =>
      dsimp [heightShift] at hE
      have hIH:=ih h H hE
      have heq1 : (1 + n) + 2 ^ h = 1 + (n + 2 ^ h):= by omega
      rw [heq1] at hIH
      have heq2 : 1 + (n + 2 ^ h) * 2 = (1 + n * 2) + 2 ^ (h + 1):= by
        rw [Nat.pow_succ]; omega
      rw [<- heq2]
      exact WordEffect.d11 hIH
theorem wordEffect_replicate_K_pad {u : WordList} {b : Nat} {v : WordList} {H : Nat}
    (hI : WordEffect 0 u b v) (hM : wordMass u <
      1) (hHeight : wordScale u * ((2 ^ H : Nat) : ℚ) = 1) :
    WordEffect 1 u (b + 2 ^ H) v:= by
  have hM' : wordMass u < ((2 ^ 0 : Nat) : ℚ):= by norm_num; exact hM
  rcases exists_heightShift_of_mass_lt u 0 hM' with ⟨J, hJ⟩
  have hSpec:=heightShift_sound u 0 J hJ
  have hPos:=wordScale_pos u
  have hPowQ : ((2 ^ J : Nat) : ℚ) = ((2 ^ H : Nat) : ℚ):= by
    change wordScale u * ((2 ^ J : Nat) : ℚ) = 1 at hSpec
    exact mul_left_cancel₀ (ne_of_gt hPos) (hSpec.trans hHeight.symm)
  have hPow : 2 ^ J = 2 ^ H:= by exact_mod_cast hPowQ
  have hShift:=wordEffect_add_pow_of_heightShift hI 0 J hJ
  rwa [hPow] at hShift
theorem exists_wordEffect_carry_of_add_eq {n : Nat} {da : WordList} {A H B : Nat}
    (hD : DigitVal A H da) (hSum : A + n = B + 2 ^ H) (hBound : B < 2 ^ H) :
    ∃ d, DigitVal B H d /\ WordEffect (n + 2 ^ H) (da ++ [K]) 1 (d ++ [K]):= by
  rcases exists_wordEffect da (n + 2 ^ H) with ⟨b, d, hE⟩
  rcases wordEffect_digitVal hE hD with ⟨C, hCd, hEq⟩
  have hCb:=lt_pow_of_digitVal hCd
  have hb2 : b = 2:= by
    rcases b with _ | _ | _ | b'
    · omega
    · omega
    · rfl
    · have : 2 ^ H + 2 ^ H + 2 ^ H <= (b' + 1 + 1 + 1) * 2 ^ H:= by
        have hmul : (b' + 1 + 1 + 1) * 2 ^ H = b' * 2 ^ H + 2 ^ H + 2 ^ H + 2 ^ H:= by ring
        omega
      omega
  subst hb2
  have hCB : C = B:= by omega
  subst hCB
  refine ⟨d, hCd, wordEffect_append hE ?_⟩
  exact @WordEffect.d00 1 [] 1 [] (WordEffect.nil 1)
theorem phaseScan_add_pow_replicate_K {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : ℚ}
    (hI : PhaseScan k u k' v a b) :
    ∀ (h m : Nat), k = m + 4 * 2 ^ h ->
      wordMass v < ((2 ^ h : Nat) : ℚ) ->
      8 * wordMass v < (m : ℚ) - 4 ->
      ∃ H m', heightShift v h = some H /\ k'=m' + 4 * 2 ^ H /\ PhaseScan m u m' v a b:= by
  induction hI with
  | nil k =>
    intro h m hEq _ _
    exact ⟨h, m, rfl, hEq, PhaseScan.nil m⟩
  | @T n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(wordMass_nonneg (V :: v)).1
    have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
    have hPos : 4 < m:= by exact_mod_cast hPosQ
    set n':=n - 4 * 2 ^ h
    have hN : n = 4 * 2 ^ h + n':= by omega
    have hE : m = 3 + n':= by omega
    subst hE
    dsimp [wordMass, heightShift] at hM hBound ⊢
    rcases ih (h + 1) (2 + n' * 2)
      (by rw [Nat.pow_succ]; omega)
      (by rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]; linarith)
      (by push_cast at hBound ⊢; linarith)
      with ⟨H, m', hHt, hK, hS⟩
    exact ⟨H, m', hHt, hK, PhaseScan.T hS⟩
  | @pair0 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(wordMass_nonneg (V :: v)).1
    have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
    have hPos : 4 < m:= by exact_mod_cast hPosQ
    set n':=n - 4 * 2 ^ h
    have hN : n = 4 * 2 ^ h + n':= by omega
    have hE : m = 1 + n':= by omega
    subst hE
    dsimp [wordMass, heightShift] at hM hBound ⊢
    rcases ih (h + 1) (n' * 2)
      (by rw [Nat.pow_succ]; omega)
      (by rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]; linarith)
      (by push_cast at hBound ⊢; linarith)
      with ⟨H, m', hHt, hK, hS⟩
    exact ⟨H, m', hHt, hK, PhaseScan.pair0 hS⟩
  | @pair1 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(wordMass_nonneg (V :: v)).1
    have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
    have hPos : 4 < m:= by exact_mod_cast hPosQ
    set n':=n - 4 * 2 ^ h
    have hN : n = 4 * 2 ^ h + n':= by omega
    have hE : m = 1 + n':= by omega
    subst hE
    dsimp [wordMass, heightShift] at hM hBound ⊢
    rcases ih (h + 1) (1 + n' * 2)
      (by rw [Nat.pow_succ]; omega)
      (by rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]; linarith)
      (by push_cast at hBound ⊢; linarith)
      with ⟨H, m', hHt, hK, hS⟩
    exact ⟨H, m', hHt, hK, PhaseScan.pair1 hS⟩
  | @short00 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(wordMass_nonneg v).1
    cases h with
    | zero =>
      dsimp [wordMass] at hM
      norm_num at hM
      linarith
    | succ h =>
      dsimp [wordMass, heightShift] at hM hBound ⊢
      have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
      have hPos : 4 < m:= by exact_mod_cast hPosQ
      rw [Nat.pow_succ] at hEq
      set n':=n - 2 * 2 ^ h
      have hN : n = 2 * 2 ^ h + n':= by omega
      have hE : m = 2 + n' * 4:= by omega
      subst hE
      rcases ih h (n' * 2)
        (by omega)
        (by rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat] at hM; linarith)
        (by push_cast at hBound ⊢; linarith)
        with ⟨H, m', hHt, hK, hS⟩
      exact ⟨H, m', hHt, hK, PhaseScan.short00 hS⟩
  | @short01 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(wordMass_nonneg v).1
    cases h with
    | zero =>
      dsimp [wordMass] at hM
      norm_num at hM
      linarith
    | succ h =>
      dsimp [wordMass, heightShift] at hM hBound ⊢
      have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
      have hPos : 4 < m:= by exact_mod_cast hPosQ
      rw [Nat.pow_succ] at hEq
      set n':=n - 2 * 2 ^ h
      have hN : n = 2 * 2 ^ h + n':= by omega
      have hE : m = 2 + n' * 4:= by omega
      subst hE
      rcases ih h (1 + n' * 2)
        (by omega)
        (by rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat] at hM; linarith)
        (by push_cast at hBound ⊢; linarith)
        with ⟨H, m', hHt, hK, hS⟩
      exact ⟨H, m', hHt, hK, PhaseScan.short01 hS⟩
  | @short10 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(wordMass_nonneg v).1
    cases h with
    | zero =>
      dsimp [wordMass] at hM
      norm_num at hM
      linarith
    | succ h =>
      dsimp [wordMass, heightShift] at hM hBound ⊢
      have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
      have hPos : 4 < m:= by exact_mod_cast hPosQ
      rw [Nat.pow_succ] at hEq
      set n':=n - 2 * 2 ^ h
      have hN : n = 2 * 2 ^ h + n':= by omega
      have hE : m = 4 + n' * 4:= by omega
      subst hE
      rcases ih h (n' * 2)
        (by omega)
        (by rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat] at hM; linarith)
        (by push_cast at hBound ⊢; linarith)
        with ⟨H, m', hHt, hK, hS⟩
      exact ⟨H, m', hHt, hK, PhaseScan.short10 hS⟩
  | @short11 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(wordMass_nonneg v).1
    cases h with
    | zero =>
      dsimp [wordMass] at hM
      norm_num at hM
      linarith
    | succ h =>
      dsimp [wordMass, heightShift] at hM hBound ⊢
      have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
      have hPos : 4 < m:= by exact_mod_cast hPosQ
      rw [Nat.pow_succ] at hEq
      set n':=n - 2 * 2 ^ h
      have hN : n = 2 * 2 ^ h + n':= by omega
      have hE : m = 4 + n' * 4:= by omega
      subst hE
      rcases ih h (1 + n' * 2)
        (by omega)
        (by rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat] at hM; linarith)
        (by push_cast at hBound ⊢; linarith)
        with ⟨H, m', hHt, hK, hS⟩
      exact ⟨H, m', hHt, hK, PhaseScan.short11 hS⟩
inductive LowerStep : WordList -> WordList -> Prop where
  | intro (orig : WordList) (padding : Nat) (eff : WordList) (k : Nat) (v : WordList)
      (a b : ℚ) (J : Nat) (da : WordList) :
      WordEffect 1 (orig ++ List.replicate padding K) 1 eff ->
      PhaseScan 8 eff k v a b ->
      0 < k ->
      DigitVal k J da ->
      LowerStep orig (V :: (v ++ V :: da))
set_option maxHeartbeats 2000000 in
-- Phase-scan + lower-step case analysis requires higher heartbeat budget
theorem aggState_lowerStep_of_copyTwelve (av ev : WordList) (hSafe : isSafePrefix ev = true)
    (hStable : ∀ q, 5 <= q -> CopyTwelve (List.replicate q V ++ av) (List.replicate q V ++ ev)) :
    ∀ (p q : Nat) (w : WordList), AggState av p q (w ++ [Q]) ->
      ∃ out, LowerStep w out /\ AggState av (1 + p) (1 + q) (out ++ [Q]):= by
  intro p q w hG
  generalize hWhole : w ++ [Q]=orig at hG
  rcases hG with ⟨H, u, A, da, carry, eff, B, db, tau, alpha,
    hP, hQ, hHbound, ⟨rest, hStart⟩, hEnd, hMass, hApLow, hApHigh, hHeight,
    hDA, hEff, hSum, hDB, hRes, hM, hDlo, hDhi, hLow⟩
  have hw_eq : w = u ++ da:= by
    have h1 : (u ++ da) ++ [Q]=w ++ [Q]:= by simpa [List.append_assoc] using hWhole.symm
    exact (List.append_inj_left' h1 rfl).symm
  subst hw_eq
  set pre:=List.replicate q V ++ av
  set pe:=List.replicate q V ++ ev
  set unit:=wordScale u
  have hPowP:=rat_pow_two_pos p
  have hAlpha : 0 < alpha:= by nlinarith
  have hUnit : 0 < unit:=wordScale_pos u
  set dyadic:=wordScale (List.replicate p V)
  have hDP : dyadic * ((2 ^ p : Nat) : ℚ) = 1:=(wordMass_and_scale_replicate_V p).2
  have hDyadic : 0 < dyadic:=wordScale_pos (List.replicate p V)
  have hAupper : alpha <= dyadic:= by nlinarith
  have hAsmall : dyadic <= 1 / 65536:=wordScale_replicate_V_le_inv_65536 p hP
  rcases reserve_pos_and_le hRes hP with ⟨hTau, hTauSmall⟩
  have hUsmall : unit <= alpha * (1 / 1024) :=
    unit_le_alpha_div_1024 p H alpha unit (by omega) hAlpha hUnit hApLow hHeight
  rcases hStable q hQ with ⟨bc, kc, hCopyPre⟩
  have hSafePre : isSafePrefix pe = true:=isSafePrefix_replicate_V_append q ev hSafe
  rcases copy_defect_bound hCopyPre with ⟨hLedger, hRhoLow, hRhoHigh⟩
  set rho:=copyDefect pre pe - 2 * alpha
  have hRho : 0 <= rho /\ rho <= 2 * alpha:= by
    unfold rho; rw [<- hMass]; push_cast at hLedger hRhoLow hRhoHigh; constructor <;> linarith
  rcases wordEffect_preserves_scale_and_mass hEff with ⟨hEffScale, hEffMass⟩
  rcases wordEffect_preserves_ends_with_V hEff hEnd with ⟨last_w, hElast⟩
  have hCut : notEndsWithQ eff = true:= by rw [hElast, notEndsWithQ_append_singleton]; rfl
  have hNe : eff ≠ []:= by rw [hElast]; simp
  have hEffHeight : wordScale eff * ((2 ^ H : Nat) : ℚ) = 1:= by rw [hEffScale]; exact hHeight
  have hEffBound : wordMass eff + wordScale eff * (1 + wordMassK db) <= 1 / 128:= by
    rw [hEffScale]; nlinarith
  rcases exists_phaseScan_twelve eff B H db hDB hEffHeight hCut hNe hEffBound with ⟨k, v, a, b,
    hIscan, hK⟩
  have hZ : 0 < wordMassK db:= by nlinarith
  rcases digitVal_massK_scale_bound p H B db dyadic unit hDB (by omega) (by omega)
    hDyadic hUnit (by linarith) hDP hHeight (by nlinarith) with ⟨hi, hHi⟩
  rcases digitVal_sandwich_split ((p - 2) / 2) (p - 2) hDB hZ hLow ⟨hi, hHi⟩
    with ⟨c, mid, t0, hSplit, hMidCut, hC, hT⟩
  rcases phaseScan_digitVal_length_bound eff db B H 12 k v a b p c mid t0 hDB hEffHeight hIscan
    hCut hMidCut hSplit hP hC hT with ⟨J, hJbound, hJheight⟩
  set new_u:=V :: (v ++ [V])
  set nu:=wordScale new_u
  have hNu : 0 < nu:=wordScale_pos new_u
  have hNuSmall : nu <= alpha * (1 / 1024) :=
    unit_le_alpha_div_1024 p J alpha nu (by omega) hAlpha hNu hApLow hJheight
  have hEffRest : ∃ w, eff = pe ++ w /\ WordEffect bc rest carry w:= by
    rw [hStart] at hEff
    exact copy_split_effect hCopyPre rest carry eff hEff
  rcases hEffRest with ⟨w, hEstart, hEw⟩
  rcases wordEffect_preserves_scale_and_mass hEw with ⟨hWscale, hWmass⟩
  have hWcut : notEndsWithQ w = true:= by
    rw [hEstart] at hCut; exact notEndsWithQ_of_append_left pe w hCut
  set e:=wordMass u - alpha
  have hEeq : e = wordScale pre * wordMass w:= by
    unfold e; rw [hStart, wordMass_append, <- hWmass, hMass]; ring
  have hWw:=wordMass_nonneg w
  have hSpre:=wordScale_pos pre
  have hEpos : 0 <= e:= by nlinarith
  have hEbound : e <= alpha * ((3 / 64) - tau):= by unfold e; linarith
  set s:=(p - 2) / 2
  set pow:=((2 ^ (s + s / 2) : Nat) : ℚ)
  have hPow : 0 < pow:=rat_pow_two_pos (s + s / 2)
  set f:=unit + 2 * unit * wordMassK db / pow
  have hFeq : f * pow = unit * pow + 2 * unit * wordMassK db:= by
    unfold f; have hne : pow ≠ 0:=ne_of_gt hPow
    calc (unit + 2 * unit * wordMassK db / pow) * pow
      _ = unit * pow + (2 * unit * wordMassK db / pow) * pow:= by ring
      _ = unit * pow + 2 * unit * wordMassK db:= by rw [div_mul_cancel₀ _ hne]
  have hFpos : 0 <= f:= by
    have h1 : 0 <= f * pow:= by rw [hFeq]; nlinarith
    nlinarith
  have hFbound : f <= alpha * tau * (1 / 4) :=
    reserve_height_bound p H s alpha unit tau f hRes hP hHbound rfl hAlpha hUnit hApLow hHeight (by
      nlinarith)
  have hLow' : ∃ c0 w0, (0 < c0 /\ s <= c0) /\ db = List.replicate c0 Q ++ K :: w0 :=
    ⟨c, mid ++ List.replicate t0 Q, ⟨by omega, hC⟩, hSplit⟩
  have hFactor : wordScale pre * wordScale w = unit:= by
    unfold unit; rw [hWscale, hStart, <- wordScale_append]
  have hScanStart : PhaseScan 12 (pe ++ w ++ db ++ [K]) k v a b:= by
    rw [hEstart] at hIscan; simpa [List.append_assoc] using hIscan
  rcases copy_phaseScan_digitVal_bound pre pe bc kc w db B H k v a b s e f hCopyPre hSafePre
    hScanStart hDB hWcut hLow' hEeq (by rw [hFactor]; nlinarith)
    with ⟨tail, hVstart, hMnext, hDl, hDu⟩
  change wordMass new_u <= wordMass pre * (1 / 2) + (e + f) * (1 / 2) at hMnext
  rw [hMass] at hMnext
  have hDl' : 2 * alpha + rho - e * (1 / 4) - 3 * f <= a - b:= by unfold rho; linarith
  have hDu' : a - b <= 2 * alpha + rho + 4 * e + 4 * f:= by unfold rho; linarith
  rcases exists_wordEffect new_u 0 with ⟨carry', eff', hEff'⟩
  have hNewStart : new_u = (V :: pre) ++ (tail ++ [V]):= by
    unfold new_u; rw [hVstart]; simp [List.append_assoc]
  have hPre_step : List.replicate (1 + q) V ++ av = V :: pre:= by
    unfold pre; rw [replicate_one_add_cons, List.cons_append]
  have hPe_step : List.replicate (1 + q) V ++ ev = V :: pe:= by
    unfold pe; rw [replicate_one_add_cons, List.cons_append]
  rcases hStable (1 + q) (by omega) with ⟨bc', kc', hCopyNew⟩
  rw [hPre_step, hPe_step] at hCopyNew
  have hEff'_rw : WordEffect 0 ((V :: pre) ++ (tail ++ [V])) carry' eff':= by
    rwa [<- hNewStart]
  have hRbounds:=copy_effect_phaseScan_combine (V :: pre) (V :: pe) bc' kc' (tail ++
    [V]) carry' eff' hCopyNew hEff'_rw
  rw [<- hNewStart] at hRbounds
  have hNewMass : wordMass new_u =
    alpha * (1 / 2) + (wordScale pre * (1 / 2)) * wordMass (tail ++ [V]):= by
    rw [hNewStart, wordMass_append]; dsimp [wordMass, wordScale]; rw [hMass]
  have hCloss_step : copyDefect (V :: pre) (V :: pe) - 2 * wordMass (V :: pre) = rho * (1 / 2):= by
    unfold rho copyDefect; dsimp [wordMass, wordMassQ, wordScale]; rw [hMass]; ring
  have hScale_step : wordScale (V :: pre) * wordMass (tail ++
    [V]) = wordMass new_u - alpha * (1 / 2):= by
    dsimp [wordScale]; linarith
  set R:=((1 + carry' : Nat) : ℚ) * nu - 1
  have hRb : rho * (1 / 2) <= R /\ R <= rho * (1 / 2) + 2 * (wordMass new_u - alpha * (1 / 2)):= by
    unfold R nu; constructor <;> linarith
  have hWtail:=wordMass_nonneg (tail ++ [V])
  have hEnew : 0 <= wordMass new_u - alpha * (1 / 2):= by nlinarith
  have hFtiny : f <= alpha * (1 / 128):= by nlinarith
  have hEtiny : e <= alpha * (3 / 64):= by nlinarith
  have hBudget:=phaseScan_twelve_scale_eq (eff ++ db ++ [K]) k v a b hIscan
  rcases carry_budget_contraction_ineq J k carry' alpha nu (a - b) R rho
    hAlpha (by linarith) hNu hNuSmall hJheight hRho.1 hRho.2
    (by linarith) (by linarith) hRb.1 (by linarith) hBudget (by unfold R; ring)
    with ⟨A', B', hAsum, hBsum, hAl, hAu, hBl, hBu⟩
  rcases exists_digitVal_of_lt_pow J A' hAu with ⟨da', hDA'⟩
  rcases exists_digitVal_of_lt_pow J B' hBu with ⟨db', hDB'⟩
  rcases reserve_step_contract hRes with ⟨tau', hRes', hTauStep⟩
  have hMkeep:=reserve_next_step_bound alpha tau tau' e f (wordMass new_u - alpha * (1 / 2))
    (by linarith) hTauStep hEbound hFbound (by linarith)
  have hDkeep:=step_mass_contraction_ineq alpha e f nu (a - b) R (wordMass new_u - alpha * (1 / 2))
    rho
    hAlpha hEpos hFpos (by linarith) hEtiny hFtiny hNuSmall hEnew (by linarith)
    hRb.1 hRb.2 hDl' hDu'
  have hDef:=phaseScan_twelve_height_sum (eff ++ db ++
    [K]) k v a b J A' B' carry' hIscan hJheight hAsum hBsum
  have hZnew:=digitVal_wordMassK_eq hDB'
  have hDnew : nu * wordMassK db'=(a - b) * (1 / 2) - 4 * nu - R:= by
    have hZ' : nu * wordMassK db'=1 - ((1 + B' : Nat) : ℚ) * nu:= by
      calc nu * wordMassK db'
        _ = nu * ((wordMassK db' + (B' : ℚ) + 1) - (1 + (B' : ℚ))):= by ring
        _ = nu * (((2 ^ J : Nat) : ℚ) - (1 + (B' : ℚ))):= by rw [hZnew]
        _ = nu * ((2 ^ J : Nat) : ℚ) - (1 + (B' : ℚ)) * nu:= by ring
        _ = 1 - (1 + (B' : ℚ)) * nu:= by rw [hJheight]
        _ = 1 - ((1 + B' : Nat) : ℚ) * nu:= by push_cast; ring
    rw [hZ']
    exact hDef
  have hLowNew : ∃ rest, db'=List.replicate (((1 + p) - 2) / 2) Q ++ rest:= by
    set r:=(((1 + p) - 2) / 2) - 1
    have hHr : 1 + r = ((1 + p) - 2) / 2 /\ 1 + r * 2 <= p - 2:= by omega
    have hHighEnd : ∃ z, db = z ++ List.replicate (1 + r * 2) Q:= by
      refine ⟨hi ++ List.replicate ((p - 2) - (1 + r * 2)) Q, ?_⟩
      have heq : ((p - 2) - (1 + r * 2)) + (1 + r * 2) = p - 2:= by omega
      rw [List.append_assoc, <- List.replicate_add, heq, <- hHi]
    rcases hHighEnd with ⟨z, hHZ⟩
    have hSC : PhaseScan 12 ((eff ++ z) ++ List.replicate (1 + r * 2) Q ++ [K]) k v a b:= by
      rw [hHZ] at hIscan; simpa [List.append_assoc] using hIscan
    rcases phaseScan_effect_split r 12 (eff ++ z) k v a b carry' eff' A' B' J db'
      hSC hEff' hDB' (by omega) hAsum hBsum with ⟨z', hL⟩
    rw [hHr.1] at hL
    exact ⟨z', hL⟩
  have hAp_step : (alpha * (1 / 2)) * ((2 ^ (1 + p) : Nat) : ℚ) = alpha * ((2 ^ p : Nat) : ℚ):= by
    rw [pow_two_one_add, Nat.cast_add]; ring
  rcases reserve_pos_and_le hRes' (by omega) with ⟨hTau', _⟩
  have hMv_eq : wordMass new_u = wordMass v * (1 / 2):= by
    unfold new_u; dsimp [wordMass]; rw [wordMass_append]; dsimp [wordMass]; ring
  have hMv_small : wordMass v < 1 / 64:= by
    linarith [hMv_eq, hMnext, hEtiny, hFtiny, hAupper, hAsmall]
  rcases phaseScan_add_pow_replicate_K hIscan 0 8 rfl (by norm_num; linarith)
    (by norm_num; linarith)
    with ⟨Hv, k', hVH, hKS, hSS⟩
  have hVHeight:=heightShift_sound v 0 Hv hVH
  have hScale_new : nu = wordScale v * (1 / 4):= by
    unfold nu new_u; dsimp [wordScale]; rw [wordScale_append]; dsimp [wordScale]; ring
  have hSv_pos:=wordScale_pos v
  have hPowQ : ((2 ^ J : Nat) : ℚ) = ((4 * 2 ^ Hv : Nat) : ℚ):= by
    change wordScale v * ((2 ^ Hv : Nat) : ℚ) = 1 at hVHeight
    rw [Nat.cast_mul, Nat.cast_ofNat]
    have h1 : nu * ((2 ^ J : Nat) : ℚ) = nu * (4 * ((2 ^ Hv : Nat) : ℚ)):= by
      calc nu * ((2 ^ J : Nat) : ℚ) = 1:=hJheight
        _ = wordScale v * ((2 ^ Hv : Nat) : ℚ):=hVHeight.symm
        _ = (nu * 4) * ((2 ^ Hv : Nat) : ℚ):= by rw [hScale_new]; ring
        _ = nu * (4 * ((2 ^ Hv : Nat) : ℚ)):= by ring
    exact mul_left_cancel₀ (ne_of_gt hNu) h1
  have hPowJ : 2 ^ J = 4 * 2 ^ Hv:= by exact_mod_cast hPowQ
  have hk'_eq : k'=A':= by omega
  rw [hk'_eq] at hSS
  have hMu_small : wordMass u < 1:= by
    have he_def : e = wordMass u - alpha:=rfl
    linarith [he_def, hEtiny, hAupper, hAsmall]
  have hEff1 : WordEffect 1 u (carry + 2 ^ H) eff :=
    wordEffect_replicate_K_pad hEff hMu_small hHeight
  rcases exists_wordEffect_carry_of_add_eq hDA hSum (lt_pow_of_digitVal hDB) with ⟨d, hDD, hEE1⟩
  have hd_eq : d = db:=digitVal_unique hDD hDB
  rw [hd_eq] at hEE1
  have hEffFull : WordEffect 1 ((u ++ da) ++ List.replicate 1 K) 1 (eff ++ db ++ [K]):= by
    simpa [List.append_assoc] using wordEffect_append hEff1 hEE1
  have hPosJ:=pow_two_pos J
  have hPosA' : 0 < A':= by omega
  refine ⟨new_u ++ da', ?_, ?_⟩
  · have hOut_eq : new_u ++ da'=V :: (v ++ V :: da'):= by
      unfold new_u; simp [List.append_assoc]
    rw [hOut_eq]
    exact LowerStep.intro (u ++ da) 1 (eff ++ db ++ [K]) A' v a b J da'
      hEffFull hSS hPosA' hDA'
  · refine AggState.intro (1 + p) (1 + q) J new_u A' da' carry' eff' B' db' tau' (alpha * (1 / 2))
      (by omega) (by omega) (by omega)
      ⟨tail ++ [V], by rw [hPre_step]; exact hNewStart⟩ ⟨V :: v, rfl⟩
      (by rw [hPre_step]; dsimp [wordMass]; rw [hMass])
      (by rw [hAp_step]; exact hApLow)
      (by rw [hAp_step]; exact hApHigh)
      hJheight hDA' hEff' (by omega) hDB' hRes'
      (by linarith) (by rw [hDnew]; linarith) (by rw [hDnew]; linarith) hLowNew
def evalLowerAfterEffect (eff : WordList) : Option (WordList) :=
  match evalPhaseScan 1024 eff 8 with
  | some (k, v) =>
    if 0 < k then
      match decodeDigits 512 k with
      | some da => some (V :: (v ++ V :: (da ++ [Q])))
      | none => none
    else none
  | none => none
def evalLowerStep (u : WordList) : Option (WordList) :=
  let (carry, eff):=evalEffect 1 (u ++ [K])
  if carry == 1 then evalLowerAfterEffect eff
  else if carry == 2 then evalLowerAfterEffect (eff ++ [K])
  else none
theorem lowerStep_of_evalLowerAfterEffect (u : WordList) (padding : Nat) (eff out : WordList)
    (hE : WordEffect 1 (u ++ List.replicate padding K) 1 eff)
    (hS : evalLowerAfterEffect eff = some out) :
    LowerStep u out:= by
  unfold evalLowerAfterEffect at hS
  cases hScan : evalPhaseScan 1024 eff 8 with
  | none => rw [hScan] at hS; contradiction
  | some kv =>
    rw [hScan] at hS
    rcases kv with ⟨k, v⟩
    dsimp only at hS
    split_ifs at hS with hk0
    cases hPw : decodeDigits 512 k with
    | none => rw [hPw] at hS; contradiction
    | some da =>
      rw [hPw] at hS
      injection hS with hS; subst hS
      rcases evalPhaseScan_sound 1024 eff 8 k v hScan with ⟨a, b, hI⟩
      rcases decodeDigits_sound 512 k da hPw with ⟨A, J, hDA, hSum⟩
      have hDFull : DigitVal k (J + 1) (da ++ [Q]):= by
        have h:=digitVal_append hDA (DigitVal.one DigitVal.nil)
        have heq : A + 1 * 2 ^ J = k:= by omega
        rwa [heq] at h
      exact LowerStep.intro u padding eff k v a b (J + 1) (da ++ [Q]) hE hI hk0 hDFull
theorem evalLowerStep_sound (u out : WordList) (hR : evalLowerStep u = some out) :
    LowerStep u out:= by
  unfold evalLowerStep at hR
  have hE:=evalEffect_sound (u ++ [K]) 1
  generalize hEff : evalEffect 1 (u ++ [K]) = ce at hR hE
  rcases ce with ⟨carry, eff⟩
  dsimp only at hR hE
  split_ifs at hR with hc1 hc2
  · simp only [beq_iff_eq] at hc1; subst hc1
    exact lowerStep_of_evalLowerAfterEffect u 1 eff out hE hR
  · simp only [beq_iff_eq] at hc2; subst hc2
    have hE2 : WordEffect 1 (u ++ List.replicate 2 K) 1 (eff ++ [K]):= by
      have h00 : WordEffect 2 [K] 1 [K]:=@WordEffect.d00 1 [] 1 [] (WordEffect.nil 1)
      simpa [List.replicate, List.append_assoc] using wordEffect_append hE h00
    exact lowerStep_of_evalLowerAfterEffect u 2 (eff ++ [K]) out hE2 hR
inductive LowerRounds : WordList -> WordList -> Prop where
  | refl (u : WordList) : LowerRounds u u
  | next {u v w : WordList} : LowerStep u v -> LowerRounds v w -> LowerRounds u w
theorem lowerRounds_trans {u v w : WordList} (h1 : LowerRounds u v) (h2 : LowerRounds v w) :
    LowerRounds u w:= by
  induction h1 with
  | refl _ => exact h2
  | next hS _ ih => exact LowerRounds.next hS (ih h2)
def evalLowerRounds : Nat -> WordList -> Option (WordList)
  | 0, u => some u
  | n + 1, u =>
    match evalLowerStep u with
    | none => none
    | some v => evalLowerRounds n v
theorem evalLowerRounds_sound (n : Nat) :
    ∀ (u w : WordList), evalLowerRounds n u = some w -> LowerRounds u w:= by
  induction n with
  | zero =>
    intro u w h; injection h with h; subst h; exact LowerRounds.refl u
  | succ n ih =>
    intro u w h
    dsimp [evalLowerRounds] at h
    cases hR : evalLowerStep u with
    | none => rw [hR] at h; contradiction
    | some v =>
      rw [hR] at h
      exact LowerRounds.next (evalLowerStep_sound u v hR) (ih v w h)


end BusyBeaver.WordCalculus
