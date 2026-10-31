module

public import BusyBeaver.WordCalculusC
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.WordCalculus

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {α β γ : Type*}
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
private abbrev t : zF := [1,1,0,0]
private abbrev d0 : zF := [0,0]
private abbrev d1 : zF := [1,0]
open Word
local notation "zW" => List Word
local notation "zR" => List.replicate
def z3G (q : Nat) (av high : zW) (lim : Nat) : Prop :=
  let pre := zR q V ++ av
  let alpha := z1e pre
  5 <= q /\
  z1h (zR 16 V) * (1 / 2) <= alpha /\
  alpha <= z1h (zR 16 V) /\
  (3 / 2) * alpha * z1h high <= z1f high /\
  z1f high + 1 <= (5 / 2) * alpha * z1h high /\
  z1h pre * (lim : Rat) <= alpha * 1024
lemma z3H (p : Nat) (alpha : Rat)
    (hL : z1h (zR p V) * (1 / 2) <= alpha)
    (hR : alpha <= z1h (zR p V)) :
    1 / 2 <= alpha * ((2 ^ p : Nat) : Rat) /\ alpha * ((2 ^ p : Nat) : Rat) <= 1 := by
  have hW := (z2s p).2
  have hPos := z2r p
  constructor <;> nlinarith
def z3I (q : Nat) (av high : zW) (lim : Nat) (orig : zW) : Bool :=
  match z2h orig with
  | none => false
  | some (u,tail) =>
    match zSw [Q] tail.reverse with
    | none => false
    | some rd =>
      let da := rd.reverse
      match zSw (zR q V ++ av) u,zHn u 0 with
      | some rest,some H =>
        if 29 <= H then
          if H == da.length then
            let (carry,eff) := zEe 0 u
            let (last_c,db) := zEe carry da
            if last_c == 1 then
              match zSw (zR 7 Q) db,
                    zSw high.reverse db.reverse with
              | some _,some _ =>
                decide (z2b 65536 65536 rest.reverse 0 <= lim)
              | _,_ => false
            else false
          else false
        else false
      | _,_ => false
lemma z3J (q : Nat) (av high : zW) (lim : Nat) (orig : zW)
    (hEntry : z3G q av high lim)
    (hCheck : z3I q av high lim orig = true) :
    zAg av 16 q orig := by
  rcases hEntry with ⟨hQ,hAlphaLow,hAlphaHigh,hDlow,hDhigh,hMassLimit⟩
  unfold z3I at hCheck
  cases hC : z2h orig with
  | none => rw [hC] at hCheck; contradiction
  | some utail =>
    rcases utail with ⟨u,tail⟩
    rw [hC] at hCheck; dsimp only at hCheck
    cases hTop : zSw [Q] tail.reverse with
    | none => rw [hTop] at hCheck; contradiction
    | some rd =>
      rw [hTop] at hCheck; dsimp only at hCheck
      cases hStart : zSw (zR q V ++ av) u with
      | none => rw [hStart] at hCheck; contradiction
      | some rest =>
        rw [hStart] at hCheck
        cases hHeight : zHn u 0 with
        | none => rw [hHeight] at hCheck; contradiction
        | some H =>
          rw [hHeight] at hCheck; dsimp only at hCheck
          split_ifs at hCheck with hHbound hWidth hLast
          simp only [beq_iff_eq] at hWidth
          have hE := zEs u 0
          generalize hEff : zEe 0 u = ce at hCheck hE hLast
          rcases ce with ⟨carry,eff⟩
          dsimp only at hCheck hE hLast
          have hF := zEs rd.reverse carry
          generalize hEffD : zEe carry rd.reverse = ldb at hCheck hF hLast
          rcases ldb with ⟨last_c,db⟩
          dsimp only at hCheck hF hLast
          simp only [beq_iff_eq] at hLast; subst hLast
          cases hLow : zSw (zR 7 Q) db with
          | none => rw [hLow] at hCheck; contradiction
          | some lo =>
            rw [hLow] at hCheck
            cases hHigh : zSw high.reverse db.reverse with
            | none => rw [hHigh] at hCheck; contradiction
            | some hi =>
              rw [hHigh] at hCheck; dsimp only at hCheck
              have hMassNat : z2b 65536 65536 rest.reverse 0 <= lim := of_decide_eq_true hCheck
              have hMassQ : ((z2b 65536 65536 rest.reverse 0 : Nat) : Rat) <= (lim : Rat) := by
                exact_mod_cast hMassNat
              have hR := z2d 65536 65536 rest 0
              have hSplit := z1i rest
              have hSpre := zSp (zR q V ++ av)
              have hMassBound : z1h (zR q V ++ av) * z1e rest <=
                  z1e (zR q V ++ av) * (1 / 64) := by
                have h1 : 65536 * z1e rest <= (lim : Rat) := by push_cast at hR; linarith
                nlinarith
              rcases z2i orig u tail hC with ⟨hOrig,hDig⟩
              have hEnd := z2p orig u tail hC
              have hTop_eq := z22 [Q] tail.reverse rd hTop
              have hTail : tail = rd.reverse ++ [Q] := by
                have hRev := congrArg List.reverse hTop_eq
                simpa using hRev
              rw [hTail,List.all_append,Bool.and_eq_true] at hDig
              rcases z26 rd.reverse hDig.1 with ⟨A,hDA⟩
              rw [<- hWidth] at hDA
              rcases z1G hF hDA with ⟨B,hDB,hSum⟩
              have hStart_eq := z22 (zR q V ++ av) u rest hStart
              have hHeight_eq : z1h u * ((2 ^ H : Nat) : Rat) = 1 := by
                have hsp := z2e u 0 H hHeight
                simpa using hsp
              have hHigh' : ∃ x,db = x ++ high := by
                have hHi_eq := z22 high.reverse db.reverse hi hHigh
                have hRev := congrArg List.reverse hHi_eq
                rw [List.reverse_reverse,List.reverse_append,List.reverse_reverse] at hRev
                exact ⟨hi.reverse,hRev⟩
              rcases z3F u high (z1e (zR q V ++ av))
                hDB hHeight_eq hHigh' hDlow hDhigh with ⟨hDlo,hDhi⟩
              rcases z3H 16 (z1e (zR q V ++ av)) hAlphaLow hAlphaHigh
                with ⟨hApLow,hApHigh⟩
              have hOrig_full : orig = u ++ rd.reverse ++ [Q] := by
                rw [hOrig,hTail,<- List.append_assoc]
              rw [hOrig_full]
              refine zAg.intro 16 q H u A rd.reverse carry eff B db (1 / 32)
                (z1e (zR q V ++ av))
                (by omega) hQ hHbound ⟨rest,hStart_eq⟩ hEnd rfl
                hApLow hApHigh hHeight_eq hDA hE (by omega) hDB
                (Reserve.even 5 (1 / 32) (by norm_num))
                (by rw [hStart_eq,z1j]; linarith)
                hDlo hDhi ⟨lo,z22 (zR 7 Q) db lo hLow⟩
def z3I_2 (q : Nat) (av high : zW) (lim : Nat) (orig : zW) (c1 c2 : Nat) : Bool :=
  match z2h orig with
  | none => false
  | some (u,tail) =>
    match zSw [Q] tail.reverse with
    | none => false
    | some rd =>
      let da:=rd.reverse
      match zSw (zR q V ++ av) u,zHn u 0 with
      | some rest,some H =>
        if 29 <= H then
          if H == da.length then
            let u1:=u.take 500
            let u2:=u.drop 500
            if (zEe 0 u1).1 == c1 then
              if (zEe c1 u2).1 == c2 then
                let (last_c,db):=zEe c2 da
                if last_c == 1 then
                  match zSw (zR 7 Q) db,
                        zSw high.reverse db.reverse with
                  | some _,some _ =>
                    decide (z2b 65536 65536 rest.reverse 0 <= lim)
                  | _,_ => false
                else false
              else false
            else false
          else false
        else false
      | _,_ => false
lemma z3J_2 (q : Nat) (av high : zW) (lim : Nat) (orig : zW) (c1 c2 : Nat)
    (hEntry : z3G q av high lim)
    (hCheck : z3I_2 q av high lim orig c1 c2=true) :
    zAg av 16 q orig:= by
  rcases hEntry with ⟨hQ,hAlphaLow,hAlphaHigh,hDlow,hDhigh,hMassLimit⟩
  unfold z3I_2 at hCheck
  cases hC : z2h orig with
  | none => rw [hC] at hCheck; contradiction
  | some utail =>
    rcases utail with ⟨u,tail⟩
    rw [hC] at hCheck; dsimp only at hCheck
    cases hTop : zSw [Q] tail.reverse with
    | none => rw [hTop] at hCheck; contradiction
    | some rd =>
      rw [hTop] at hCheck; dsimp only at hCheck
      cases hStart : zSw (zR q V ++ av) u with
      | none => rw [hStart] at hCheck; contradiction
      | some rest =>
        rw [hStart] at hCheck
        cases hHeight : zHn u 0 with
        | none => rw [hHeight] at hCheck; contradiction
        | some H =>
          rw [hHeight] at hCheck; dsimp only at hCheck
          split_ifs at hCheck with hHbound hWidth hc1 hc2 hLast
          simp only [beq_iff_eq] at hWidth hc1 hc2
          have hE1:=zEs (u.take 500) 0
          rw [hc1] at hE1
          have hE2:=zEs (u.drop 500) c1
          rw [hc2] at hE2
          have hE:=z1D hE1 hE2
          rw [List.take_append_drop] at hE
          have hF:=zEs rd.reverse c2
          generalize hEffD : zEe c2 rd.reverse=ldb at hCheck hF hLast
          rcases ldb with ⟨last_c,db⟩
          dsimp only at hCheck hF hLast
          simp only [beq_iff_eq] at hLast; subst hLast
          cases hLow : zSw (zR 7 Q) db with
          | none => rw [hLow] at hCheck; contradiction
          | some lo =>
            rw [hLow] at hCheck
            cases hHigh : zSw high.reverse db.reverse with
            | none => rw [hHigh] at hCheck; contradiction
            | some hi =>
              rw [hHigh] at hCheck; dsimp only at hCheck
              have hMassNat : z2b 65536 65536 rest.reverse 0 <= lim:=of_decide_eq_true hCheck
              have hMassQ : ((z2b 65536 65536 rest.reverse 0 : Nat) : ℚ) <= (lim : ℚ):= by
                exact_mod_cast hMassNat
              have hR:=z2d 65536 65536 rest 0
              have hSplit:=z1i rest
              have hSpre:=zSp (zR q V ++ av)
              have hMassBound : z1h (zR q V ++ av) * z1e rest <=
                  z1e (zR q V ++ av) * (1 / 64):= by
                have h1 : 65536 * z1e rest <= (lim : ℚ):= by push_cast at hR; linarith
                nlinarith
              rcases z2i orig u tail hC with ⟨hOrig,hDig⟩
              have hEnd:=z2p orig u tail hC
              have hTop_eq:=z22 [Q] tail.reverse rd hTop
              have hTail : tail=rd.reverse ++ [Q]:= by
                have hRev:=congrArg List.reverse hTop_eq
                simpa using hRev
              rw [hTail,List.all_append,Bool.and_eq_true] at hDig
              rcases z26 rd.reverse hDig.1 with ⟨A,hDA⟩
              rw [<- hWidth] at hDA
              rcases z1G hF hDA with ⟨B,hDB,hSum⟩
              have hStart_eq:=z22 (zR q V ++ av) u rest hStart
              have hHeight_eq : z1h u * ((2 ^ H : Nat) : ℚ)=1:= by
                have hsp:=z2e u 0 H hHeight
                simpa using hsp
              have hHigh' : ∃ x,db=x ++ high:= by
                have hHi_eq:=z22 high.reverse db.reverse hi hHigh
                have hRev:=congrArg List.reverse hHi_eq
                rw [List.reverse_reverse,List.reverse_append,List.reverse_reverse] at hRev
                exact ⟨hi.reverse,hRev⟩
              rcases z3F u high (z1e (zR q V ++ av))
                hDB hHeight_eq hHigh' hDlow hDhigh with ⟨hDlo,hDhi⟩
              rcases z3H 16 (z1e (zR q V ++ av)) hAlphaLow hAlphaHigh
                with ⟨hApLow,hApHigh⟩
              have hOrig_full : orig=u ++ rd.reverse ++ [Q]:= by
                rw [hOrig,hTail,<- List.append_assoc]
              rw [hOrig_full]
              refine zAg.intro 16 q H u A rd.reverse c2
                ((zEe 0 (u.take 500)).2 ++ (zEe c1 (u.drop 500)).2) B db (1 / 32)
                (z1e (zR q V ++ av))
                (by omega) hQ hHbound ⟨rest,hStart_eq⟩ hEnd rfl
                hApLow hApHigh hHeight_eq hDA hE (by omega) hDB
                (Reserve.even 5 (1 / 32) (by norm_num))
                (by rw [hStart_eq,z1j]; linarith)
                hDlo hDhi ⟨lo,z22 (zR 7 Q) db lo hLow⟩
def zWeqL : zW -> zW -> Bool
  | [],[] => true
  | V :: a,V :: b => zWeqL a b
  | K :: a,K :: b => zWeqL a b
  | Q :: a,Q :: b => zWeqL a b
  | _,_ => false
lemma zWeqL_eq (a : zW) :
    ∀ (b : zW),zWeqL a b = true -> a = b := by
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
        dsimp [zWeqL] at h
        rw [ih b h]
def zWeqO : Option zW -> Option zW -> Bool
  | some a,some b => zWeqL a b
  | none,none => true
  | _,_ => false
lemma zWeqO_eq (a b : Option zW) (h : zWeqO a b = true) : a = b := by
  cases a with
  | none => cases b <;> first | rfl | contradiction
  | some a =>
    cases b with
    | none => contradiction
    | some b => exact congrArg some (zWeqL_eq a b h)
lemma z3B' {u v w : zW} (h : zWeqO (z3A u) (some v) = true) (hr : Rounds v w) :
    Rounds u w :=
  Rounds.next (z3B u v (zWeqO_eq (z3A u) (some v) h)) hr
def z3Z_3 (u1 u2 : zW) (c1 k1 k2 : Nat) (v1 v2 da : zW) : Bool :=
  let (c1',eff1) := zEe 0 u1
  let (c2',eff2) := zEe c1 u2
  if c1' == c1 && c2' == 1 then
    match z2m 600 eff1 12,z2m 600 eff2 k1 with
    | some (k1',v1'),some (k2',v2') =>
      if k1' == k1 && k2' == k2 && v1' == v1 && v2' == v2 then
        match zPf 512 k2 with
        | some da' => da' == da
        | none => false
      else false
    | _,_ => false
  else false
lemma z40_3 (u1 u2 : zW) (c1 k1 k2 : Nat) (v1 v2 da : zW)
    (hR : z3Z_3 u1 u2 c1 k1 k2 v1 v2 da = true) :
    Step (u1 ++ u2) (V :: ((v1 ++ v2) ++ V :: (da ++ [Q]))) := by
  unfold z3Z_3 at hR
  have hE1 := zEs u1 0
  generalize hEff1 : zEe 0 u1 = ce1 at hR hE1
  rcases ce1 with ⟨c1',eff1⟩
  have hE2 := zEs u2 c1
  generalize hEff2 : zEe c1 u2 = ce2 at hR hE2
  rcases ce2 with ⟨c2',eff2⟩
  dsimp only at hR hE1 hE2
  split_ifs at hR with hc
  simp only [Bool.and_eq_true,beq_iff_eq] at hc
  rcases hc with ⟨hc1,hc2⟩
  subst c1'; subst c2'
  cases hS1 : z2m 600 eff1 12 with
  | none => rw [hS1] at hR; contradiction
  | some kv1 =>
    rw [hS1] at hR
    cases hS2 : z2m 600 eff2 k1 with
    | none => rw [hS2] at hR; contradiction
    | some kv2 =>
      rw [hS2] at hR
      rcases kv1 with ⟨k1',v1'⟩
      rcases kv2 with ⟨k2',v2'⟩
      dsimp only at hR
      split_ifs at hR with hk
      simp only [Bool.and_eq_true,beq_iff_eq] at hk
      rcases hk with ⟨⟨⟨hk1,hk2⟩,hv1⟩,hv2⟩
      subst k1'; subst k2'; subst v1'; subst v2'
      cases hPw : zPf 512 k2 with
      | none => rw [hPw] at hR; contradiction
      | some da' =>
        rw [hPw] at hR
        dsimp only at hR
        simp only [beq_iff_eq] at hR; subst da'
        rcases z2n 600 eff1 12 k1 v1 hS1 with ⟨a1,b1,hI1⟩
        rcases z2n 600 eff2 k1 k2 v2 hS2 with ⟨a2,b2,hI2⟩
        rcases z1P hI1 hI2 with ⟨a,b,hI,_,_⟩
        rcases z3z 512 k2 da hPw with ⟨A,J,hDA,hSum⟩
        exact Step.intro (u1 ++ u2) (eff1 ++ eff2) k2 (v1 ++ v2) a b J A da
          (z1D hE1 hE2) hI hDA hSum
def z41_3 (u1 u2 u3 : zW) (c1 c2 k1 k2 k3 : Nat) (v1 v2 v3 da1 da2 : zW) : Bool :=
  let (c1',eff1) := zEe 0 u1
  let (c2',eff2) := zEe c1 u2
  let (c3',eff3) := zEe c2 u3
  if c1' == c1 && c2' == c2 && c3' == 1 then
    match z2m 600 eff1 12,z2m 600 eff2 k1,z2m 600 eff3 k2 with
    | some (k1',v1'),some (k2',v2'),some (k3',v3') =>
      if k1' == k1 && k2' == k2 && k3' == k3 && v1' == v1 && v2' == v2 && v3' == v3 then
        match zPf 512 k3 with
        | some da' => da' == (da1 ++ da2)
        | none => false
      else false
    | _,_,_ => false
  else false
lemma z42_3 (u1 u2 u3 : zW) (c1 c2 k1 k2 k3 : Nat) (v1 v2 v3 da1 da2 : zW)
    (hR : z41_3 u1 u2 u3 c1 c2 k1 k2 k3 v1 v2 v3 da1 da2 = true) :
    Step (u1 ++ u2 ++ u3) (V :: ((v1 ++ v2 ++ v3) ++ V :: ((da1 ++ da2) ++ [Q]))) := by
  unfold z41_3 at hR
  have hE1 := zEs u1 0
  generalize hEff1 : zEe 0 u1 = ce1 at hR hE1
  rcases ce1 with ⟨c1',eff1⟩
  have hE2 := zEs u2 c1
  generalize hEff2 : zEe c1 u2 = ce2 at hR hE2
  rcases ce2 with ⟨c2',eff2⟩
  have hE3 := zEs u3 c2
  generalize hEff3 : zEe c2 u3 = ce3 at hR hE3
  rcases ce3 with ⟨c3',eff3⟩
  dsimp only at hR hE1 hE2 hE3
  split_ifs at hR with hc
  simp only [Bool.and_eq_true,beq_iff_eq] at hc
  rcases hc with ⟨⟨hc1,hc2⟩,hc3⟩
  subst c1'; subst c2'; subst c3'
  cases hS1 : z2m 600 eff1 12 with
  | none => rw [hS1] at hR; contradiction
  | some kv1 =>
    rw [hS1] at hR
    cases hS2 : z2m 600 eff2 k1 with
    | none => rw [hS2] at hR; contradiction
    | some kv2 =>
      rw [hS2] at hR
      cases hS3 : z2m 600 eff3 k2 with
      | none => rw [hS3] at hR; contradiction
      | some kv3 =>
        rw [hS3] at hR
        rcases kv1 with ⟨k1',v1'⟩
        rcases kv2 with ⟨k2',v2'⟩
        rcases kv3 with ⟨k3',v3'⟩
        dsimp only at hR
        split_ifs at hR with hk
        simp only [Bool.and_eq_true,beq_iff_eq] at hk
        rcases hk with ⟨⟨⟨⟨⟨hk1,hk2⟩,hk3⟩,hv1⟩,hv2⟩,hv3⟩
        subst k1'; subst k2'; subst k3'; subst v1'; subst v2'; subst v3'
        cases hPw : zPf 512 k3 with
        | none => rw [hPw] at hR; contradiction
        | some da' =>
          rw [hPw] at hR
          dsimp only at hR
          simp only [beq_iff_eq] at hR; subst da'
          rcases z2n 600 eff1 12 k1 v1 hS1 with ⟨a1,b1,hI1⟩
          rcases z2n 600 eff2 k1 k2 v2 hS2 with ⟨a2,b2,hI2⟩
          rcases z2n 600 eff3 k2 k3 v3 hS3 with ⟨a3,b3,hI3⟩
          rcases z1P hI1 hI2 with ⟨a12,b12,hI12,_,_⟩
          rcases z1P hI12 hI3 with ⟨a,b,hI,_,_⟩
          rcases z3z 512 k3 (da1 ++ da2) hPw with ⟨A,J,hDA,hSum⟩
          exact Step.intro (u1 ++ u2 ++ u3) (eff1 ++ eff2 ++ eff3) k3 (v1 ++ v2 ++ v3) a b J A (da1 ++ da2)
            (z1D (z1D hE1 hE2) hE3) hI hDA hSum
def z43_3 (q : Nat) (av high : zW) (lim : Nat)
    (u1 u2 u3 da1 da2 : zW) (h1 h2 H c1 c2 carry cda r1 r2 : Nat) : Bool :=
  match zSw (zR q V ++ av) u1,
        zSw [V] u3.reverse,
        zHn u1 0,zHn u2 h1,zHn u3 h2 with
  | some rest1,some u3_init_rev,some h1',some h2',some H' =>
    if h1' == h1 && h2' == h2 && H' == H && decide (29 <= H) then
      if H == (da1 ++ da2).length && (da1 ++ da2).all z25 then
        let (c1',eff1) := zEe 0 u1
        let (c2',eff2) := zEe c1 u2
        let (c3',eff3) := zEe c2 u3
        let (cda',db1) := zEe carry da1
        let (last_c,db2) := zEe cda da2
        if c1' == c1 && c2' == c2 && c3' == carry && cda' == cda && last_c == 1 then
          match zSw (zR 7 Q) (db1 ++ db2),
                zSw high.reverse (db1 ++ db2).reverse with
          | some _,some _ =>
            let r1' := z2b 65536 65536 u3.reverse 0
            let r2' := z2b 65536 65536 u2.reverse r1
            let r3' := z2b 65536 65536 rest1.reverse r2
            (r1' == r1) && (r2' == r2) && decide (r3' <= lim)
          | _,_ => false
        else false
      else false
    else false
  | _,_,_,_,_ => false
lemma z44_3 (q : Nat) (av high : zW) (lim : Nat)
    (u1 u2 u3 da1 da2 : zW) (h1 h2 H c1 c2 carry cda r1 r2 : Nat)
    (hEntry : z3G q av high lim)
    (hCheck : z43_3 q av high lim u1 u2 u3 da1 da2 h1 h2 H c1 c2 carry cda r1 r2 = true) :
    zAg av 16 q ((u1 ++ u2 ++ u3) ++ (da1 ++ da2) ++ [Q]) := by
  rcases hEntry with ⟨hQ,hAlphaLow,hAlphaHigh,hDlow,hDhigh,hMassLimit⟩
  unfold z43_3 at hCheck
  cases hStart : zSw (zR q V ++ av) u1 with
  | none => rw [hStart] at hCheck; contradiction
  | some rest1 =>
    rw [hStart] at hCheck
    cases hEnd : zSw [V] u3.reverse with
    | none => rw [hEnd] at hCheck; contradiction
    | some u3_init_rev =>
      rw [hEnd] at hCheck
      cases hH1 : zHn u1 0 with
      | none => rw [hH1] at hCheck; contradiction
      | some h1' =>
        rw [hH1] at hCheck
        cases hH2 : zHn u2 h1 with
        | none => rw [hH2] at hCheck; contradiction
        | some h2' =>
          rw [hH2] at hCheck
          cases hH3 : zHn u3 h2 with
          | none => rw [hH3] at hCheck; contradiction
          | some H' =>
            rw [hH3] at hCheck; dsimp only at hCheck
            have hE1 := zEs u1 0
            generalize hEff1 : zEe 0 u1 = ce1 at hCheck hE1
            rcases ce1 with ⟨c1',eff1⟩
            have hE2 := zEs u2 c1
            generalize hEff2 : zEe c1 u2 = ce2 at hCheck hE2
            rcases ce2 with ⟨c2',eff2⟩
            have hE3 := zEs u3 c2
            generalize hEff3 : zEe c2 u3 = ce3 at hCheck hE3
            rcases ce3 with ⟨c3',eff3⟩
            have hF1 := zEs da1 carry
            generalize hEffD1 : zEe carry da1 = ldb1 at hCheck hF1
            rcases ldb1 with ⟨cda',db1⟩
            have hF2 := zEs da2 cda
            generalize hEffD2 : zEe cda da2 = ldb2 at hCheck hF2
            rcases ldb2 with ⟨last_c,db2⟩
            dsimp only at hCheck hE1 hE2 hE3 hF1 hF2
            split_ifs at hCheck with hIf1 hIf2 hIf3
            simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hIf1 hIf2 hIf3
            rcases hIf1 with ⟨⟨⟨hh1,hh2⟩,hH⟩,hHbound⟩
            subst h1'; subst h2'; subst H'
            rcases hIf2 with ⟨hWidth,hDig⟩
            rcases hIf3 with ⟨⟨⟨⟨hc1,hc2⟩,hc3⟩,hcda⟩,hlast⟩
            subst c1'; subst c2'; subst c3'; subst cda'; subst last_c
            cases hLow : zSw (zR 7 Q) (db1 ++ db2) with
            | none => rw [hLow] at hCheck; contradiction
            | some lo =>
              rw [hLow] at hCheck
              cases hHigh : zSw high.reverse (db1 ++ db2).reverse with
              | none => rw [hHigh] at hCheck; contradiction
              | some hi =>
                rw [hHigh] at hCheck; dsimp only at hCheck
                simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hCheck
                rcases hCheck with ⟨⟨hR1_eq,hR2_eq⟩,hR3_le⟩
                have hRF1 := z2d 65536 65536 u3 0
                rw [hR1_eq] at hRF1
                have hRF2 := z2d 65536 65536 u2 r1
                rw [hR2_eq] at hRF2
                have hRF3 := z2d 65536 65536 rest1 r2
                have hMassQ : ((z2b 65536 65536 rest1.reverse r2 : Nat) : Rat) <= (lim : Rat) := by
                  exact_mod_cast hR3_le
                have hSp3 := z1i u3
                have hSp2 := z1i u2
                have hSp1 := z1i rest1
                have hSu2 := zSp u2
                have hSr1 := zSp rest1
                have hSpre := zSp (zR q V ++ av)
                have hM3 : 65536 * z1e u3 <= (r1 : Rat) := by push_cast at hRF1; linarith
                have hM2 : 65536 * (z1e u2 + z1h u2 * z1e u3) <= (r2 : Rat) := by
                  push_cast at hRF2; nlinarith
                have hM1 : 65536 * (z1e rest1 + z1h rest1 * (z1e u2 + z1h u2 * z1e u3)) <= (lim : Rat) := by
                  push_cast at hRF3; nlinarith
                have hMrest : z1e (rest1 ++ u2 ++ u3) =
                    z1e rest1 + z1h rest1 * (z1e u2 + z1h u2 * z1e u3) := by
                  rw [z1j,z1j,z1m]; ring
                have hMassBound : z1h (zR q V ++ av) * z1e (rest1 ++ u2 ++ u3) <=
                    z1e (zR q V ++ av) * (1 / 64) := by
                  rw [hMrest]; nlinarith
                have hStart_eq := z22 (zR q V ++ av) u1 rest1 hStart
                have hU_start : u1 ++ u2 ++ u3 = (zR q V ++ av) ++ (rest1 ++ u2 ++ u3) := by
                  rw [hStart_eq]; simp [List.append_assoc]
                have hEnd_eq := z22 [V] u3.reverse u3_init_rev hEnd
                have hU3_end : u3 = u3_init_rev.reverse ++ [V] := by
                  have hRev := congrArg List.reverse hEnd_eq
                  simpa using hRev
                have hU_end : ∃ rest,u1 ++ u2 ++ u3 = rest ++ [V] :=
                  ⟨u1 ++ u2 ++ u3_init_rev.reverse,by rw [hU3_end]; simp [List.append_assoc]⟩
                have hSpH1 := z2e u1 0 h1 hH1
                have hSpH2 := z2e u2 h1 h2 hH2
                have hSpH3 := z2e u3 h2 H hH3
                have hHeight_eq : z1h (u1 ++ u2 ++ u3) * ((2 ^ H : Nat) : Rat) = 1 := by
                  rw [z1m,z1m]
                  calc (z1h u1 * z1h u2 * z1h u3) * ((2 ^ H : Nat) : Rat)
                    _ = z1h u1 * z1h u2 * (z1h u3 * ((2 ^ H : Nat) : Rat)) := by ring
                    _ = z1h u1 * (z1h u2 * ((2 ^ h2 : Nat) : Rat)) := by rw [hSpH3]; ring
                    _ = z1h u1 * ((2 ^ h1 : Nat) : Rat) := by rw [hSpH2]
                    _ = ((2 ^ 0 : Nat) : Rat) := hSpH1
                    _ = 1 := by norm_num
                rcases z26 (da1 ++ da2) hDig with ⟨A,hDA⟩
                rw [<- hWidth] at hDA
                have hE : zEf 0 (u1 ++ u2 ++ u3) carry (eff1 ++ eff2 ++ eff3) :=
                  z1D (z1D hE1 hE2) hE3
                have hF : zEf carry (da1 ++ da2) 1 (db1 ++ db2) :=
                  z1D hF1 hF2
                rcases z1G hF hDA with ⟨B,hDB,hSum⟩
                have hHigh' : ∃ x,db1 ++ db2 = x ++ high := by
                  have hHi_eq := z22 high.reverse (db1 ++ db2).reverse hi hHigh
                  have hRev := congrArg List.reverse hHi_eq
                  rw [List.reverse_reverse,List.reverse_append,List.reverse_reverse] at hRev
                  exact ⟨hi.reverse,hRev⟩
                rcases z3F (u1 ++ u2 ++ u3) high (z1e (zR q V ++ av))
                  hDB hHeight_eq hHigh' hDlow hDhigh with ⟨hDlo,hDhi⟩
                rcases z3H 16 (z1e (zR q V ++ av)) hAlphaLow hAlphaHigh
                  with ⟨hApLow,hApHigh⟩
                refine zAg.intro 16 q H (u1 ++ u2 ++ u3) A (da1 ++ da2) carry
                  (eff1 ++ eff2 ++ eff3) B (db1 ++ db2) (1 / 32)
                  (z1e (zR q V ++ av))
                  (by omega) hQ hHbound ⟨rest1 ++ u2 ++ u3,hU_start⟩ hU_end rfl
                  hApLow hApHigh hHeight_eq hDA hE (by omega) hDB
                  (Reserve.even 5 (1 / 32) (by norm_num))
                  (by rw [hU_start,z1j]; linarith)
                  hDlo hDhi ⟨lo,z22 (zR 7 Q) (db1 ++ db2) lo hLow⟩
def z1_den : zW -> Nat
  | [] => 1
  | V :: v => z1_den v * 2
  | _ :: v => z1_den v
def z1e_num : zW -> Nat
  | [] => 0
  | V :: v => z1e_num v
  | _ :: v => z1_den v + z1e_num v * 2
def z1f_num : zW -> Nat
  | [] => 0
  | V :: v => z1f_num v
  | K :: v => z1_den v + z1f_num v * 2
  | Q :: v => z1f_num v * 2
def z1h_num : zW -> Nat
  | [] => 1
  | V :: v => z1h_num v
  | _ :: v => z1h_num v * 2
lemma z1_dyadic (u : zW) :
    (0 : Rat) < z1_den u /\
    z1e u * (z1_den u : Rat) = z1e_num u /\
    z1f u * (z1_den u : Rat) = z1f_num u /\
    z1h u * (z1_den u : Rat) = z1h_num u := by
  induction u with
  | nil => simp [z1_den, z1e, z1e_num, z1f, z1f_num, z1h, z1h_num]
  | cons a v ih =>
    rcases ih with ⟨hd, he, hf, hh⟩
    cases a <;> (
      simp only [z1_den, z1e, z1e_num, z1f, z1f_num, z1h, z1h_num, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      refine ⟨by linarith, by nlinarith, by nlinarith, by nlinarith⟩)
def check_z3G (q : Nat) (av high : zW) (lim : Nat) : Bool :=
  let pre := zR q V ++ av
  let dp := z1_den pre
  let ep := z1e_num pre
  let hp := z1h_num pre
  let dh := z1_den high
  let fh := z1f_num high
  let hh := z1h_num high
  let d16 := z1_den (zR 16 V)
  let h16 := z1h_num (zR 16 V)
  decide (5 <= q /\
    h16 * dp <= 2 * ep * d16 /\
    ep * d16 <= h16 * dp /\
    3 * ep * hh <= 2 * fh * dp /\
    2 * (fh + dh) * dp <= 5 * ep * hh /\
    hp * lim <= ep * 1024)

lemma check_z45_gen (z1e_p z1h_p z1f_k z1h_k z1h_16 : Rat)
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
  push_cast at c1 c2 c3 c4 c5 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_pos hdpQ hd16Q]
  · nlinarith [mul_pos hdpQ hd16Q]
  · nlinarith [mul_pos hdpQ hdkQ]
  · nlinarith [mul_pos hdpQ hdkQ]
  · nlinarith [hdpQ]

lemma z3G_of_check {q : Nat} {av high : zW} {lim : Nat}
    (h : check_z3G q av high lim = true) : z3G q av high lim := by
  unfold check_z3G at h
  dsimp only at h
  rcases of_decide_eq_true h with ⟨hq, n1, n2, n3, n4, n5⟩
  unfold z3G
  rcases z1_dyadic (zR q V ++ av) with ⟨hdp, hep, _, hhp⟩
  rcases z1_dyadic high with ⟨hdh, _, hfh, hhh⟩
  rcases z1_dyadic (zR 16 V) with ⟨hd16, _, _, hh16⟩
  have c1 : (z1h_num (zR 16 V) * z1_den (zR q V ++ av) : Rat) ≤ 2 * z1e_num (zR q V ++ av) * z1_den (zR 16 V) := by exact_mod_cast n1
  have c2 : (z1e_num (zR q V ++ av) * z1_den (zR 16 V) : Rat) ≤ z1h_num (zR 16 V) * z1_den (zR q V ++ av) := by exact_mod_cast n2
  have c3 : (3 * z1e_num (zR q V ++ av) * z1h_num high : Rat) ≤ 2 * z1f_num high * z1_den (zR q V ++ av) := by exact_mod_cast n3
  have c4 : (2 * (z1f_num high + z1_den high) * z1_den (zR q V ++ av) : Rat) ≤ 5 * z1e_num (zR q V ++ av) * z1h_num high := by exact_mod_cast n4
  have c5 : (z1h_num (zR q V ++ av) * lim : Rat) ≤ z1e_num (zR q V ++ av) * 1024 := by exact_mod_cast n5
  rcases check_z45_gen
      (z1e (zR q V ++ av)) (z1h (zR q V ++ av)) (z1f high) (z1h high) (z1h (zR 16 V))
      (z1_den (zR q V ++ av)) (z1_den high) (z1_den (zR 16 V))
      (z1e_num (zR q V ++ av)) (z1h_num (zR q V ++ av)) (z1f_num high) (z1h_num high) (z1h_num (zR 16 V)) lim
      (by exact_mod_cast hdp) (by exact_mod_cast hdh) (by exact_mod_cast hd16)
      hep hhp hfh hhh hh16 ⟨c1, c2, c3, c4, c5⟩ with ⟨g1, g2, g3, g4, g5⟩
  exact ⟨hq, by linarith, by linarith, by linarith, by linarith, by linarith⟩
lemma z3n_ls (u : zW) :
    ∀ (h : Nat),z1e u < ((2 ^ h : Nat) : ℚ) -> ∃ H,zHn u h=some H:= by
  induction u with
  | nil => intro h _; exact ⟨h,rfl⟩
  | cons w u ih =>
    intro h hM
    cases w
    · dsimp [z1e,zHn] at hM ⊢
      refine ih (h + 1) ?_
      rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]
      linarith
    · cases h with
      | zero =>
        dsimp [z1e] at hM
        have hw:=(zWn u).1
        norm_num at hM
        linarith
      | succ h =>
        dsimp [z1e,zHn] at hM ⊢
        rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat] at hM
        exact ih h (by linarith)
    · cases h with
      | zero =>
        dsimp [z1e] at hM
        have hw:=(zWn u).1
        norm_num at hM
        linarith
      | succ h =>
        dsimp [z1e,zHn] at hM ⊢
        rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat] at hM
        exact ih h (by linarith)
lemma z3o_ls {n : Nat} {u : zW} {b : Nat} {v : zW}
    (hI : zEf n u b v) :
    ∀ (h H : Nat),zHn u h=some H -> zEf (n + 2 ^ h) u (b + 2 ^ H) v:= by
  induction hI with
  | nil n =>
    intro h H hE
    injection hE with hE; subst hE
    exact zEf.nil (n + 2 ^ h)
  | @T n u b v _ ih =>
    intro h H hE
    dsimp [zHn] at hE
    have hIH:=ih (h + 1) H hE
    have heq : 1 + (n + 2 ^ h) * 2=(1 + n * 2) + 2 ^ (h + 1):= by
      rw [Nat.pow_succ]; omega
    rw [<- heq] at hIH
    exact zEf.T hIH
  | @d00 n u b v _ ih =>
    intro h H hE
    cases h with
    | zero => contradiction
    | succ h =>
      dsimp [zHn] at hE
      have hIH:=ih h H hE
      have heq : (n + 2 ^ h) * 2=n * 2 + 2 ^ (h + 1):= by
        rw [Nat.pow_succ]; omega
      rw [<- heq]
      exact zEf.d00 hIH
  | @d01 n u b v _ ih =>
    intro h H hE
    cases h with
    | zero => contradiction
    | succ h =>
      dsimp [zHn] at hE
      have hIH:=ih h H hE
      have heq : 1 + (n + 2 ^ h) * 2=(1 + n * 2) + 2 ^ (h + 1):= by
        rw [Nat.pow_succ]; omega
      rw [<- heq]
      exact zEf.d01 hIH
  | @d10 n u b v _ ih =>
    intro h H hE
    cases h with
    | zero => contradiction
    | succ h =>
      dsimp [zHn] at hE
      have hIH:=ih h H hE
      have heq : (n + 2 ^ h) * 2=n * 2 + 2 ^ (h + 1):= by
        rw [Nat.pow_succ]; omega
      rw [<- heq]
      exact zEf.d10 hIH
  | @d11 n u b v _ ih =>
    intro h H hE
    cases h with
    | zero => contradiction
    | succ h =>
      dsimp [zHn] at hE
      have hIH:=ih h H hE
      have heq1 : (1 + n) + 2 ^ h=1 + (n + 2 ^ h):= by omega
      rw [heq1] at hIH
      have heq2 : 1 + (n + 2 ^ h) * 2=(1 + n * 2) + 2 ^ (h + 1):= by
        rw [Nat.pow_succ]; omega
      rw [<- heq2]
      exact zEf.d11 hIH
lemma z3p_ls {u : zW} {b : Nat} {v : zW} {H : Nat}
    (hI : zEf 0 u b v) (hM : z1e u < 1) (hHeight : z1h u * ((2 ^ H : Nat) : ℚ)=1) :
    zEf 1 u (b + 2 ^ H) v:= by
  have hM' : z1e u < ((2 ^ 0 : Nat) : ℚ):= by norm_num; exact hM
  rcases z3n_ls u 0 hM' with ⟨J,hJ⟩
  have hSpec:=z2e u 0 J hJ
  have hPos:=zSp u
  have hPowQ : ((2 ^ J : Nat) : ℚ)=((2 ^ H : Nat) : ℚ):= by
    change z1h u * ((2 ^ J : Nat) : ℚ)=1 at hSpec
    exact mul_left_cancel₀ (ne_of_gt hPos) (hSpec.trans hHeight.symm)
  have hPow : 2 ^ J=2 ^ H:= by exact_mod_cast hPowQ
  have hShift:=z3o_ls hI 0 J hJ
  rwa [hPow] at hShift
lemma z3q_ls {n : Nat} {da : zW} {A H B : Nat}
    (hD : zDg A H da) (hSum : A + n=B + 2 ^ H) (hBound : B < 2 ^ H) :
    ∃ d,zDg B H d /\ zEf (n + 2 ^ H) (da ++ [K]) 1 (d ++ [K]):= by
  rcases z1B da (n + 2 ^ H) with ⟨b,d,hE⟩
  rcases z1G hE hD with ⟨C,hCd,hEq⟩
  have hCb:=z1b hCd
  have hb2 : b=2:= by
    rcases b with _ | _ | _ | b'
    · omega
    · omega
    · rfl
    · have : 2 ^ H + 2 ^ H + 2 ^ H <= (b' + 1 + 1 + 1) * 2 ^ H:= by
        have hmul : (b' + 1 + 1 + 1) * 2 ^ H=b' * 2 ^ H + 2 ^ H + 2 ^ H + 2 ^ H:= by ring
        omega
      omega
  subst hb2
  have hCB : C=B:= by omega
  subst hCB
  refine ⟨d,hCd,z1D hE ?_⟩
  exact @zEf.d00 1 [] 1 [] (zEf.nil 1)
lemma z3r_ls {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : ℚ}
    (hI : zPS k u k' v a b) :
    ∀ (h m : Nat),k=m + 4 * 2 ^ h ->
      z1e v < ((2 ^ h : Nat) : ℚ) ->
      8 * z1e v < (m : ℚ) - 4 ->
      ∃ H m',zHn v h=some H /\ k'=m' + 4 * 2 ^ H /\ zPS m u m' v a b:= by
  induction hI with
  | nil k =>
    intro h m hEq _ _
    exact ⟨h,m,rfl,hEq,zPS.nil m⟩
  | @T n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(zWn (V :: v)).1
    have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
    have hPos : 4 < m:= by exact_mod_cast hPosQ
    set n':=n - 4 * 2 ^ h
    have hN : n=4 * 2 ^ h + n':= by omega
    have hE : m=3 + n':= by omega
    subst hE
    dsimp [z1e,zHn] at hM hBound ⊢
    rcases ih (h + 1) (2 + n' * 2)
      (by rw [Nat.pow_succ]; omega)
      (by rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]; linarith)
      (by push_cast at hBound ⊢; linarith)
      with ⟨H,m',hHt,hK,hS⟩
    exact ⟨H,m',hHt,hK,zPS.T hS⟩
  | @pair0 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(zWn (V :: v)).1
    have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
    have hPos : 4 < m:= by exact_mod_cast hPosQ
    set n':=n - 4 * 2 ^ h
    have hN : n=4 * 2 ^ h + n':= by omega
    have hE : m=1 + n':= by omega
    subst hE
    dsimp [z1e,zHn] at hM hBound ⊢
    rcases ih (h + 1) (n' * 2)
      (by rw [Nat.pow_succ]; omega)
      (by rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]; linarith)
      (by push_cast at hBound ⊢; linarith)
      with ⟨H,m',hHt,hK,hS⟩
    exact ⟨H,m',hHt,hK,zPS.pair0 hS⟩
  | @pair1 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(zWn (V :: v)).1
    have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
    have hPos : 4 < m:= by exact_mod_cast hPosQ
    set n':=n - 4 * 2 ^ h
    have hN : n=4 * 2 ^ h + n':= by omega
    have hE : m=1 + n':= by omega
    subst hE
    dsimp [z1e,zHn] at hM hBound ⊢
    rcases ih (h + 1) (1 + n' * 2)
      (by rw [Nat.pow_succ]; omega)
      (by rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]; linarith)
      (by push_cast at hBound ⊢; linarith)
      with ⟨H,m',hHt,hK,hS⟩
    exact ⟨H,m',hHt,hK,zPS.pair1 hS⟩
  | @short00 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(zWn v).1
    cases h with
    | zero =>
      dsimp [z1e] at hM
      norm_num at hM
      linarith
    | succ h =>
      dsimp [z1e,zHn] at hM hBound ⊢
      have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
      have hPos : 4 < m:= by exact_mod_cast hPosQ
      rw [Nat.pow_succ] at hEq
      set n':=n - 2 * 2 ^ h
      have hN : n=2 * 2 ^ h + n':= by omega
      have hE : m=2 + n' * 4:= by omega
      subst hE
      rcases ih h (n' * 2)
        (by omega)
        (by rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat] at hM; linarith)
        (by push_cast at hBound ⊢; linarith)
        with ⟨H,m',hHt,hK,hS⟩
      exact ⟨H,m',hHt,hK,zPS.short00 hS⟩
  | @short01 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(zWn v).1
    cases h with
    | zero =>
      dsimp [z1e] at hM
      norm_num at hM
      linarith
    | succ h =>
      dsimp [z1e,zHn] at hM hBound ⊢
      have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
      have hPos : 4 < m:= by exact_mod_cast hPosQ
      rw [Nat.pow_succ] at hEq
      set n':=n - 2 * 2 ^ h
      have hN : n=2 * 2 ^ h + n':= by omega
      have hE : m=2 + n' * 4:= by omega
      subst hE
      rcases ih h (1 + n' * 2)
        (by omega)
        (by rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat] at hM; linarith)
        (by push_cast at hBound ⊢; linarith)
        with ⟨H,m',hHt,hK,hS⟩
      exact ⟨H,m',hHt,hK,zPS.short01 hS⟩
  | @short10 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(zWn v).1
    cases h with
    | zero =>
      dsimp [z1e] at hM
      norm_num at hM
      linarith
    | succ h =>
      dsimp [z1e,zHn] at hM hBound ⊢
      have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
      have hPos : 4 < m:= by exact_mod_cast hPosQ
      rw [Nat.pow_succ] at hEq
      set n':=n - 2 * 2 ^ h
      have hN : n=2 * 2 ^ h + n':= by omega
      have hE : m=4 + n' * 4:= by omega
      subst hE
      rcases ih h (n' * 2)
        (by omega)
        (by rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat] at hM; linarith)
        (by push_cast at hBound ⊢; linarith)
        with ⟨H,m',hHt,hK,hS⟩
      exact ⟨H,m',hHt,hK,zPS.short10 hS⟩
  | @short11 n u k v a b _ ih =>
    intro h m hEq hM hBound
    have hw:=(zWn v).1
    cases h with
    | zero =>
      dsimp [z1e] at hM
      norm_num at hM
      linarith
    | succ h =>
      dsimp [z1e,zHn] at hM hBound ⊢
      have hPosQ : (4 : ℚ) < (m : ℚ):= by linarith
      have hPos : 4 < m:= by exact_mod_cast hPosQ
      rw [Nat.pow_succ] at hEq
      set n':=n - 2 * 2 ^ h
      have hN : n=2 * 2 ^ h + n':= by omega
      have hE : m=4 + n' * 4:= by omega
      subst hE
      rcases ih h (1 + n' * 2)
        (by omega)
        (by rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat] at hM; linarith)
        (by push_cast at hBound ⊢; linarith)
        with ⟨H,m',hHt,hK,hS⟩
      exact ⟨H,m',hHt,hK,zPS.short11 hS⟩
inductive zLs : zW -> zW -> Prop where
  | intro (orig : zW) (padding : Nat) (eff : zW) (k : Nat) (v : zW)
      (a b : ℚ) (J : Nat) (da : zW) :
      zEf 1 (orig ++ zR padding K) 1 eff ->
      zPS 8 eff k v a b ->
      0 < k ->
      zDg k J da ->
      zLs orig (V :: (v ++ V :: da))
set_option maxHeartbeats 2000000 in
lemma z3s_ls (av ev : zW) (hSafe : z3h ev=true)
    (hStable : ∀ q,5 <= q -> z3m (zR q V ++ av) (zR q V ++ ev)) :
    ∀ (p q : Nat) (w : zW),zAg av p q (w ++ [Q]) ->
      ∃ out,zLs w out /\ zAg av (1 + p) (1 + q) (out ++ [Q]):= by
  intro p q w hG
  generalize hWhole : w ++ [Q]=orig at hG
  rcases hG with ⟨H,u,A,da,carry,eff,B,db,tau,alpha,
    hP,hQ,hHbound,⟨rest,hStart⟩,hEnd,hMass,hApLow,hApHigh,hHeight,
    hDA,hEff,hSum,hDB,hRes,hM,hDlo,hDhi,hLow⟩
  have hw_eq : w=u ++ da:= by
    have h1 : (u ++ da) ++ [Q]=w ++ [Q]:= by simpa [List.append_assoc] using hWhole.symm
    exact (List.append_inj_left' h1 rfl).symm
  subst hw_eq
  set pre:=zR q V ++ av
  set pe:=zR q V ++ ev
  set unit:=z1h u
  have hPowP:=z2r p
  have hAlpha : 0 < alpha:= by nlinarith
  have hUnit : 0 < unit:=zSp u
  set dyadic:=z1h (zR p V)
  have hDP : dyadic * ((2 ^ p : Nat) : ℚ)=1:=(z2s p).2
  have hDyadic : 0 < dyadic:=zSp (zR p V)
  have hAupper : alpha <= dyadic:= by nlinarith
  have hAsmall : dyadic <= 1 / 65536:=z35 p hP
  rcases z2L hRes hP with ⟨hTau,hTauSmall⟩
  have hUsmall : unit <= alpha * (1 / 1024) :=
    z36 p H alpha unit (by omega) hAlpha hUnit hApLow hHeight
  rcases hStable q hQ with ⟨bc,kc,hCopyPre⟩
  have hSafePre : z3h pe=true:=z3i q ev hSafe
  rcases z3f hCopyPre with ⟨hLedger,hRhoLow,hRhoHigh⟩
  set rho:=z3e pre pe - 2 * alpha
  have hRho : 0 <= rho /\ rho <= 2 * alpha:= by
    unfold rho; rw [<- hMass]; push_cast at hLedger hRhoLow hRhoHigh; constructor <;> linarith
  rcases z1I hEff with ⟨hEffScale,hEffMass⟩
  rcases z34 hEff hEnd with ⟨last_w,hElast⟩
  have hCut : z0Z eff=true:= by rw [hElast,z11]; rfl
  have hNe : eff ≠ []:= by rw [hElast]; simp
  have hEffHeight : z1h eff * ((2 ^ H : Nat) : ℚ)=1:= by rw [hEffScale]; exact hHeight
  have hEffBound : z1e eff + z1h eff * (1 + z1f db) <= 1 / 128:= by
    rw [hEffScale]; nlinarith
  rcases z2v eff B H db hDB hEffHeight hCut hNe hEffBound with ⟨k,v,a,b,hIscan,hK⟩
  have hZ : 0 < z1f db:= by nlinarith
  rcases z2X p H B db dyadic unit hDB (by omega) (by omega)
    hDyadic hUnit (by linarith) hDP hHeight (by nlinarith) with ⟨hi,hHi⟩
  rcases z33 ((p - 2) / 2) (p - 2) hDB hZ hLow ⟨hi,hHi⟩
    with ⟨c,mid,t0,hSplit,hMidCut,hC,hT⟩
  rcases z2V eff db B H 12 k v a b p c mid t0 hDB hEffHeight hIscan
    hCut hMidCut hSplit hP hC hT with ⟨J,hJbound,hJheight⟩
  set new_u:=V :: (v ++ [V])
  set nu:=z1h new_u
  have hNu : 0 < nu:=zSp new_u
  have hNuSmall : nu <= alpha * (1 / 1024) :=
    z36 p J alpha nu (by omega) hAlpha hNu hApLow hJheight
  have hEffRest : ∃ w,eff=pe ++ w /\ zEf bc rest carry w:= by
    rw [hStart] at hEff
    exact z3g hCopyPre rest carry eff hEff
  rcases hEffRest with ⟨w,hEstart,hEw⟩
  rcases z1I hEw with ⟨hWscale,hWmass⟩
  have hWcut : z0Z w=true:= by
    rw [hEstart] at hCut; exact z31 pe w hCut
  set e:=z1e u - alpha
  have hEeq : e=z1h pre * z1e w:= by
    unfold e; rw [hStart,z1j,<- hWmass,hMass]; ring
  have hWw:=zWn w
  have hSpre:=zSp pre
  have hEpos : 0 <= e:= by nlinarith
  have hEbound : e <= alpha * ((3 / 64) - tau):= by unfold e; linarith
  set s:=(p - 2) / 2
  set pow:=((2 ^ (s + s / 2) : Nat) : ℚ)
  have hPow : 0 < pow:=z2r (s + s / 2)
  set f:=unit + 2 * unit * z1f db / pow
  have hFeq : f * pow=unit * pow + 2 * unit * z1f db:= by
    unfold f; have hne : pow ≠ 0:=ne_of_gt hPow
    calc (unit + 2 * unit * z1f db / pow) * pow
      _ = unit * pow + (2 * unit * z1f db / pow) * pow:= by ring
      _ = unit * pow + 2 * unit * z1f db:= by rw [div_mul_cancel₀ _ hne]
  have hFpos : 0 <= f:= by
    have h1 : 0 <= f * pow:= by rw [hFeq]; nlinarith
    nlinarith
  have hFbound : f <= alpha * tau * (1 / 4) :=
    z2N p H s alpha unit tau f hRes hP hHbound rfl hAlpha hUnit hApLow hHeight (by nlinarith)
  have hLow' : ∃ c0 w0,(0 < c0 /\ s <= c0) /\ db=zR c0 Q ++ K :: w0 :=
    ⟨c,mid ++ zR t0 Q,⟨by omega,hC⟩,hSplit⟩
  have hFactor : z1h pre * z1h w=unit:= by
    unfold unit; rw [hWscale,hStart,<- z1m]
  have hScanStart : zPS 12 (pe ++ w ++ db ++ [K]) k v a b:= by
    rw [hEstart] at hIscan; simpa [List.append_assoc] using hIscan
  rcases z3k pre pe bc kc w db B H k v a b s e f hCopyPre hSafePre
    hScanStart hDB hWcut hLow' hEeq (by rw [hFactor]; nlinarith)
    with ⟨tail,hVstart,hMnext,hDl,hDu⟩
  change z1e new_u <= z1e pre * (1 / 2) + (e + f) * (1 / 2) at hMnext
  rw [hMass] at hMnext
  have hDl' : 2 * alpha + rho - e * (1 / 4) - 3 * f <= a - b:= by unfold rho; linarith
  have hDu' : a - b <= 2 * alpha + rho + 4 * e + 4 * f:= by unfold rho; linarith
  rcases z1B new_u 0 with ⟨carry',eff',hEff'⟩
  have hNewStart : new_u=(V :: pre) ++ (tail ++ [V]):= by
    unfold new_u; rw [hVstart]; simp [List.append_assoc]
  have hPre_step : zR (1 + q) V ++ av=V :: pre:= by
    unfold pre; rw [z3n,List.cons_append]
  have hPe_step : zR (1 + q) V ++ ev=V :: pe:= by
    unfold pe; rw [z3n,List.cons_append]
  rcases hStable (1 + q) (by omega) with ⟨bc',kc',hCopyNew⟩
  rw [hPre_step,hPe_step] at hCopyNew
  have hEff'_rw : zEf 0 ((V :: pre) ++ (tail ++ [V])) carry' eff':= by
    rwa [<- hNewStart]
  have hRbounds:=z3l (V :: pre) (V :: pe) bc' kc' (tail ++ [V]) carry' eff' hCopyNew hEff'_rw
  rw [<- hNewStart] at hRbounds
  have hNewMass : z1e new_u=alpha * (1 / 2) + (z1h pre * (1 / 2)) * z1e (tail ++ [V]):= by
    rw [hNewStart,z1j]; dsimp [z1e,z1h]; rw [hMass]
  have hCloss_step : z3e (V :: pre) (V :: pe) - 2 * z1e (V :: pre)=rho * (1 / 2):= by
    unfold rho z3e; dsimp [z1e,z1g,z1h]; rw [hMass]; ring
  have hScale_step : z1h (V :: pre) * z1e (tail ++ [V])=z1e new_u - alpha * (1 / 2):= by
    dsimp [z1h]; linarith
  set R:=((1 + carry' : Nat) : ℚ) * nu - 1
  have hRb : rho * (1 / 2) <= R /\ R <= rho * (1 / 2) + 2 * (z1e new_u - alpha * (1 / 2)):= by
    unfold R nu; constructor <;> linarith
  have hWtail:=zWn (tail ++ [V])
  have hEnew : 0 <= z1e new_u - alpha * (1 / 2):= by nlinarith
  have hFtiny : f <= alpha * (1 / 128):= by nlinarith
  have hEtiny : e <= alpha * (3 / 64):= by nlinarith
  have hBudget:=z2I (eff ++ db ++ [K]) k v a b hIscan
  rcases z38 J k carry' alpha nu (a - b) R rho
    hAlpha (by linarith) hNu hNuSmall hJheight hRho.1 hRho.2
    (by linarith) (by linarith) hRb.1 (by linarith) hBudget (by unfold R; ring)
    with ⟨A',B',hAsum,hBsum,hAl,hAu,hBl,hBu⟩
  rcases z18 J A' hAu with ⟨da',hDA'⟩
  rcases z18 J B' hBu with ⟨db',hDB'⟩
  rcases z2K hRes with ⟨tau',hRes',hTauStep⟩
  have hMkeep:=z2P alpha tau tau' e f (z1e new_u - alpha * (1 / 2))
    (by linarith) hTauStep hEbound hFbound (by linarith)
  have hDkeep:=z37 alpha e f nu (a - b) R (z1e new_u - alpha * (1 / 2)) rho
    hAlpha hEpos hFpos (by linarith) hEtiny hFtiny hNuSmall hEnew (by linarith)
    hRb.1 hRb.2 hDl' hDu'
  have hDef:=z2J (eff ++ db ++ [K]) k v a b J A' B' carry' hIscan hJheight hAsum hBsum
  have hZnew:=z1n hDB'
  have hDnew : nu * z1f db'=(a - b) * (1 / 2) - 4 * nu - R:= by
    have hZ' : nu * z1f db'=1 - ((1 + B' : Nat) : ℚ) * nu:= by
      calc nu * z1f db'
        _ = nu * ((z1f db' + (B' : ℚ) + 1) - (1 + (B' : ℚ))):= by ring
        _ = nu * (((2 ^ J : Nat) : ℚ) - (1 + (B' : ℚ))):= by rw [hZnew]
        _ = nu * ((2 ^ J : Nat) : ℚ) - (1 + (B' : ℚ)) * nu:= by ring
        _ = 1 - (1 + (B' : ℚ)) * nu:= by rw [hJheight]
        _ = 1 - ((1 + B' : Nat) : ℚ) * nu:= by push_cast; ring
    rw [hZ']
    exact hDef
  have hLowNew : ∃ rest,db'=zR (((1 + p) - 2) / 2) Q ++ rest:= by
    set r:=(((1 + p) - 2) / 2) - 1
    have hHr : 1 + r=((1 + p) - 2) / 2 /\ 1 + r * 2 <= p - 2:= by omega
    have hHighEnd : ∃ z,db=z ++ zR (1 + r * 2) Q:= by
      refine ⟨hi ++ zR ((p - 2) - (1 + r * 2)) Q,?_⟩
      have heq : ((p - 2) - (1 + r * 2)) + (1 + r * 2)=p - 2:= by omega
      rw [List.append_assoc,<- List.replicate_add,heq,<- hHi]
    rcases hHighEnd with ⟨z,hHZ⟩
    have hSC : zPS 12 ((eff ++ z) ++ zR (1 + r * 2) Q ++ [K]) k v a b:= by
      rw [hHZ] at hIscan; simpa [List.append_assoc] using hIscan
    rcases z2F r 12 (eff ++ z) k v a b carry' eff' A' B' J db'
      hSC hEff' hDB' (by omega) hAsum hBsum with ⟨z',hL⟩
    rw [hHr.1] at hL
    exact ⟨z',hL⟩
  have hAp_step : (alpha * (1 / 2)) * ((2 ^ (1 + p) : Nat) : ℚ)=alpha * ((2 ^ p : Nat) : ℚ):= by
    rw [zP2,Nat.cast_add]; ring
  rcases z2L hRes' (by omega) with ⟨hTau',_⟩
  have hMv_eq : z1e new_u=z1e v * (1 / 2):= by
    unfold new_u; dsimp [z1e]; rw [z1j]; dsimp [z1e]; ring
  have hMv_small : z1e v < 1 / 64:= by
    linarith [hMv_eq,hMnext,hEtiny,hFtiny,hAupper,hAsmall]
  rcases z3r_ls hIscan 0 8 rfl (by norm_num; linarith) (by norm_num; linarith)
    with ⟨Hv,k',hVH,hKS,hSS⟩
  have hVHeight:=z2e v 0 Hv hVH
  have hScale_new : nu=z1h v * (1 / 4):= by
    unfold nu new_u; dsimp [z1h]; rw [z1m]; dsimp [z1h]; ring
  have hSv_pos:=zSp v
  have hPowQ : ((2 ^ J : Nat) : ℚ)=((4 * 2 ^ Hv : Nat) : ℚ):= by
    change z1h v * ((2 ^ Hv : Nat) : ℚ)=1 at hVHeight
    rw [Nat.cast_mul,Nat.cast_ofNat]
    have h1 : nu * ((2 ^ J : Nat) : ℚ)=nu * (4 * ((2 ^ Hv : Nat) : ℚ)):= by
      calc nu * ((2 ^ J : Nat) : ℚ)=1:=hJheight
        _ = z1h v * ((2 ^ Hv : Nat) : ℚ):=hVHeight.symm
        _ = (nu * 4) * ((2 ^ Hv : Nat) : ℚ):= by rw [hScale_new]; ring
        _ = nu * (4 * ((2 ^ Hv : Nat) : ℚ)):= by ring
    exact mul_left_cancel₀ (ne_of_gt hNu) h1
  have hPowJ : 2 ^ J=4 * 2 ^ Hv:= by exact_mod_cast hPowQ
  have hk'_eq : k'=A':= by omega
  rw [hk'_eq] at hSS
  have hMu_small : z1e u < 1:= by
    have he_def : e=z1e u - alpha:=rfl
    linarith [he_def,hEtiny,hAupper,hAsmall]
  have hEff1 : zEf 1 u (carry + 2 ^ H) eff :=
    z3p_ls hEff hMu_small hHeight
  rcases z3q_ls hDA hSum (z1b hDB) with ⟨d,hDD,hEE1⟩
  have hd_eq : d=db:=z1d hDD hDB
  rw [hd_eq] at hEE1
  have hEffFull : zEf 1 ((u ++ da) ++ zR 1 K) 1 (eff ++ db ++ [K]):= by
    simpa [List.append_assoc] using z1D hEff1 hEE1
  have hPosJ:=zPp J
  have hPosA' : 0 < A':= by omega
  refine ⟨new_u ++ da',?_,?_⟩
  · have hOut_eq : new_u ++ da'=V :: (v ++ V :: da'):= by
      unfold new_u; simp [List.append_assoc]
    rw [hOut_eq]
    exact zLs.intro (u ++ da) 1 (eff ++ db ++ [K]) A' v a b J da'
      hEffFull hSS hPosA' hDA'
  · refine zAg.intro (1 + p) (1 + q) J new_u A' da' carry' eff' B' db' tau' (alpha * (1 / 2))
      (by omega) (by omega) (by omega)
      ⟨tail ++ [V],by rw [hPre_step]; exact hNewStart⟩ ⟨V :: v,rfl⟩
      (by rw [hPre_step]; dsimp [z1e]; rw [hMass])
      (by rw [hAp_step]; exact hApLow)
      (by rw [hAp_step]; exact hApHigh)
      hJheight hDA' hEff' (by omega) hDB' hRes'
      (by linarith) (by rw [hDnew]; linarith) (by rw [hDnew]; linarith) hLowNew
def z3E_ls (eff : zW) : Option (zW) :=
  match z2m 1024 eff 8 with
  | some (k,v) =>
    if 0 < k then
      match zPf 512 k with
      | some da => some (V :: (v ++ V :: (da ++ [Q])))
      | none => none
    else none
  | none => none
def z3F_ls (u : zW) : Option (zW) :=
  let (carry,eff):=zEe 1 (u ++ [K])
  if carry == 1 then z3E_ls eff
  else if carry == 2 then z3E_ls (eff ++ [K])
  else none
lemma z3G_ls (u : zW) (padding : Nat) (eff out : zW)
    (hE : zEf 1 (u ++ zR padding K) 1 eff)
    (hS : z3E_ls eff=some out) :
    zLs u out:= by
  unfold z3E_ls at hS
  cases hScan : z2m 1024 eff 8 with
  | none => rw [hScan] at hS; contradiction
  | some kv =>
    rw [hScan] at hS
    rcases kv with ⟨k,v⟩
    dsimp only at hS
    split_ifs at hS with hk0
    cases hPw : zPf 512 k with
    | none => rw [hPw] at hS; contradiction
    | some da =>
      rw [hPw] at hS
      injection hS with hS; subst hS
      rcases z2n 1024 eff 8 k v hScan with ⟨a,b,hI⟩
      rcases z3z 512 k da hPw with ⟨A,J,hDA,hSum⟩
      have hDFull : zDg k (J + 1) (da ++ [Q]):= by
        have h:=z19 hDA (zDg.one zDg.nil)
        have heq : A + 1 * 2 ^ J=k:= by omega
        rwa [heq] at h
      exact zLs.intro u padding eff k v a b (J + 1) (da ++ [Q]) hE hI hk0 hDFull
lemma z3H_ls (u out : zW) (hR : z3F_ls u=some out) :
    zLs u out:= by
  unfold z3F_ls at hR
  have hE:=zEs (u ++ [K]) 1
  generalize hEff : zEe 1 (u ++ [K])=ce at hR hE
  rcases ce with ⟨carry,eff⟩
  dsimp only at hR hE
  split_ifs at hR with hc1 hc2
  · simp only [beq_iff_eq] at hc1; subst hc1
    exact z3G_ls u 1 eff out hE hR
  · simp only [beq_iff_eq] at hc2; subst hc2
    have hE2 : zEf 1 (u ++ zR 2 K) 1 (eff ++ [K]):= by
      have h00 : zEf 2 [K] 1 [K]:=@zEf.d00 1 [] 1 [] (zEf.nil 1)
      simpa [List.replicate,List.append_assoc] using z1D hE h00
    exact z3G_ls u 2 (eff ++ [K]) out hE2 hR
inductive LowerRounds : zW -> zW -> Prop where
  | refl (u : zW) : LowerRounds u u
  | next {u v w : zW} : zLs u v -> LowerRounds v w -> LowerRounds u w
lemma z3I_ls {u v w : zW} (h1 : LowerRounds u v) (h2 : LowerRounds v w) :
    LowerRounds u w:= by
  induction h1 with
  | refl _ => exact h2
  | next hS _ ih => exact LowerRounds.next hS (ih h2)
def z3J_ls : Nat -> zW -> Option (zW)
  | 0,u => some u
  | n + 1,u =>
    match z3F_ls u with
    | none => none
    | some v => z3J_ls n v
lemma z3K_ls (n : Nat) :
    ∀ (u w : zW),z3J_ls n u=some w -> LowerRounds u w:= by
  induction n with
  | zero =>
    intro u w h; injection h with h; subst h; exact LowerRounds.refl u
  | succ n ih =>
    intro u w h
    dsimp [z3J_ls] at h
    cases hR : z3F_ls u with
    | none => rw [hR] at h; contradiction
    | some v =>
      rw [hR] at h
      exact LowerRounds.next (z3H_ls u v hR) (ih v w h)


end BusyBeaver.WordCalculus
