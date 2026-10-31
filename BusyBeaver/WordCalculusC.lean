module

public import BusyBeaver.WordCalculusB
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
inductive Reserve : Nat -> Rat -> Prop where
  | even (n : Nat) (tau : Rat) : tau * ((2 ^ n : Nat) : Rat) = 1 -> Reserve ((n + 3) * 2) tau
  | odd (n : Nat) (tau : Rat) : tau * ((2 ^ n : Nat) : Rat) = 3 / 4 -> Reserve (1 + (n + 3) * 2) tau
lemma z2K {p : Nat} {tau : Rat} (hI : Reserve p tau) :
    ∃ tau',Reserve (1 + p) tau' /\ tau' <= (3 / 4) * tau := by
  cases hI with
  | even n tau hEq =>
    exact ⟨(3 / 4) * tau,Reserve.odd n ((3 / 4) * tau) (by linarith),le_refl _⟩
  | odd n tau hEq =>
    have hPos := z2r n
    have hTau : 0 < tau := by nlinarith
    refine ⟨(2 / 3) * tau,?_,by linarith⟩
    have heq : 1 + (1 + (n + 3) * 2) = ((n + 1) + 3) * 2 := by omega
    rw [heq]
    refine Reserve.even (n + 1) ((2 / 3) * tau) ?_
    rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    linarith
lemma z2L {p : Nat} {tau : Rat} (hI : Reserve p tau) (hP : 16 <= p) :
    0 < tau /\ tau <= 1 / 32 := by
  cases hI with
  | even n tau hEq =>
    have hn : 5 <= n := by omega
    have hPos := z2r n
    have hB : (32 : Rat) <= ((2 ^ n : Nat) : Rat) := by
      have h1 : 2 ^ 5 <= 2 ^ n := Nat.pow_le_pow_right (by omega) hn
      exact_mod_cast h1
    constructor <;> nlinarith
  | odd n tau hEq =>
    have hn : 5 <= n := by omega
    have hPos := z2r n
    have hB : (32 : Rat) <= ((2 ^ n : Nat) : Rat) := by
      have h1 : 2 ^ 5 <= 2 ^ n := Nat.pow_le_pow_right (by omega) hn
      exact_mod_cast h1
    constructor <;> nlinarith
lemma z2M (alpha unit f t0 q tau : Rat)
    (ht : 0 < t0) (ha : 0 <= alpha) (hu : 0 <= unit)
    (h1 : 32 * t0 * unit <= alpha) (h2 : 32 * t0 <= q)
    (h3 : f * q <= unit * q + 5 * alpha) (h4 : 3 / 4 <= tau * t0) :
    f <= alpha * tau * (1 / 4) := by
  by_cases hfu : f <= unit
  · nlinarith
  · nlinarith
lemma z2N (p H s : Nat) (alpha unit tau f : Rat)
    (hI : Reserve p tau) (hP : 16 <= p) (hH : (3 * p) / 2 + 5 <= H) (hS : s = (p - 2) / 2)
    (hA : 0 < alpha) (hU : 0 < unit)
    (hAp : 1 / 2 <= alpha * ((2 ^ p : Nat) : Rat))
    (hUh : unit * ((2 ^ H : Nat) : Rat) = 1)
    (hF : f * ((2 ^ (s + s / 2) : Nat) : Rat) <= unit * ((2 ^ (s + s / 2) : Nat) : Rat) + 5 * alpha) :
    f <= alpha * tau * (1 / 4) := by
  cases hI with
  | even n tau hTau =>
    have hn : 5 <= n := by omega
    have hLow : 32 * ((2 ^ n : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) := by
      have h1 : 2 ^ (5 + n) <= 2 ^ (s + s / 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 2 ^ (5 + n) = 32 * 2 ^ n := by rw [Nat.pow_add]
      rw [h2] at h1; exact_mod_cast h1
    have hHigh : 64 * ((2 ^ ((n + 3) * 2) : Nat) : Rat) * ((2 ^ n : Nat) : Rat) <= ((2 ^ H : Nat) : Rat) := by
      have h1 : 2 ^ (6 + (n + 3) * 2 + n) <= 2 ^ H := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 2 ^ (6 + (n + 3) * 2 + n) = 64 * 2 ^ ((n + 3) * 2) * 2 ^ n := by
        rw [Nat.pow_add,Nat.pow_add]
      rw [h2] at h1; exact_mod_cast h1
    have hPosN := z2r n
    have hPosP := z2r ((n + 3) * 2)
    have hGap : 32 * ((2 ^ n : Nat) : Rat) * unit <= alpha := by nlinarith
    exact z2M alpha unit f ((2 ^ n : Nat) : Rat) ((2 ^ (s + s / 2) : Nat) : Rat) tau
      hPosN (by linarith) (by linarith) hGap hLow hF (by linarith)
  | odd n tau hTau =>
    have hn : 5 <= n := by omega
    have hLow : 32 * ((2 ^ n : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) := by
      have h1 : 2 ^ (5 + n) <= 2 ^ (s + s / 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 2 ^ (5 + n) = 32 * 2 ^ n := by rw [Nat.pow_add]
      rw [h2] at h1; exact_mod_cast h1
    have hHigh : 64 * ((2 ^ (1 + (n + 3) * 2) : Nat) : Rat) * ((2 ^ n : Nat) : Rat) <= ((2 ^ H : Nat) : Rat) := by
      have h1 : 2 ^ (6 + (1 + (n + 3) * 2) + n) <= 2 ^ H := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 2 ^ (6 + (1 + (n + 3) * 2) + n) = 64 * 2 ^ (1 + (n + 3) * 2) * 2 ^ n := by
        rw [Nat.pow_add,Nat.pow_add]
      rw [h2] at h1; exact_mod_cast h1
    have hPosN := z2r n
    have hPosP := z2r (1 + (n + 3) * 2)
    have hGap : 32 * ((2 ^ n : Nat) : Rat) * unit <= alpha := by nlinarith
    exact z2M alpha unit f ((2 ^ n : Nat) : Rat) ((2 ^ (s + s / 2) : Nat) : Rat) tau
      hPosN (by linarith) (by linarith) hGap hLow hF (by linarith)
lemma z2O (p : Nat) (hP : 16 <= p) :
    (3 * (p + 1)) / 2 + 5 <= 1 + 3 * (((p - 2) / 2 + 1) / 2) + 3 * ((p - 1) / 2) := by
  omega
lemma z2P (alpha tau tau' e f e' : Rat) (hA : 0 <= alpha)
    (hTau : tau' <= (3 / 4) * tau) (hE : e <= alpha * ((3 / 64) - tau))
    (hF : f <= alpha * tau * (1 / 4)) (hE' : e' <= (e + f) * (1 / 2)) :
    e' <= (alpha * (1 / 2)) * ((3 / 64) - tau') := by
  nlinarith
lemma z2Q {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k u k' v a b) :
    ∃ g : Nat,z1h u = z1h v * ((8 ^ g : Nat) : Rat) /\ u.length = v.length + g := by
  induction hI with
  | nil _ => exact ⟨0,by simp [z1h],rfl⟩
  | T _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring,by simp; omega⟩
  | pair0 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    refine ⟨g + 1,?_,by simp; omega⟩
    rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]; dsimp [z1h]; rw [hE]; ring
  | pair1 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    refine ⟨g + 1,?_,by simp; omega⟩
    rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]; dsimp [z1h]; rw [hE]; ring
  | short00 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring,by simp; omega⟩
  | short01 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring,by simp; omega⟩
  | short10 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring,by simp; omega⟩
  | short11 _ ih =>
    rcases ih with ⟨g,hE,hL⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring,by simp; omega⟩
lemma z2R {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k u k' v a b) : v.length <= u.length := by
  rcases z2Q hI with ⟨g,_,hL⟩
  omega
lemma z2S (c k k' : Nat) (v : zW) (l : Rat) (hC : 0 < c)
    (hI : Scan k (zR c Q ++ [K]) k' v l) :
    v.length + (c + 1) / 2 = c + 1 := by
  rcases z0U c with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · cases r with
    | zero => omega
    | succ r =>
      have heq : (r + 1) * 2 = 2 + r * 2 := by omega
      rw [heq] at hI ⊢
      rcases z1r r k k' v l hI with ⟨d,n,rfl,_,_⟩
      simp; omega
  · rcases zS1 r k k' v l hI with ⟨rfl,_,_⟩
    simp; omega
lemma z2T (c k k' : Nat) (v : zW) (a b : Rat) (hC : 0 < c)
    (hI : zPS k (zR c Q ++ [K]) k' v a b) :
    v.length + (c + 1) / 2 = c + 1 := by
  have hD := z19 (z1a c) (zDg.zero zDg.nil)
  rcases z1T hI hD with ⟨l,hJ,_,_⟩
  exact z2S c k k' v l hC hJ
lemma z2U (k : Nat) (u : zW) (c : Nat) (mid : zW) (t0 k' : Nat)
    (v : zW) (a b : Rat)
    (hC : 0 < c) (hT : 0 < t0) (hU : z0Z u = true) (hM : z0Z mid = true)
    (hI : zPS k (u ++ zR c Q ++ K :: (mid ++ zR t0 Q ++ [K])) k' v a b) :
    ∃ g : Nat,
      z1h (u ++ zR c Q ++ K :: (mid ++ zR t0 Q ++ [K])) =
        z1h v * ((8 ^ g : Nat) : Rat) /\
      (c + 1) / 2 + (t0 + 1) / 2 <= g := by
  rcases z2Q hI with ⟨g,hG,hL⟩
  refine ⟨g,hG,?_⟩
  have hEq0 : u ++ zR c Q ++ K :: (mid ++ zR t0 Q ++ [K]) =
      u ++ (zR c Q ++ K :: (mid ++ zR t0 Q ++ [K])) := by
    simp [List.append_assoc]
  rw [hEq0] at hI
  rcases z1Y hI u _ rfl (Or.inl hU) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,hV,_,_⟩
  have hSplit : zR c Q ++ K :: (mid ++ zR t0 Q ++ [K]) =
      (zR c Q ++ [K]) ++ (mid ++ zR t0 Q ++ [K]) := by
    simp [List.append_assoc]
  rcases z1Y hK (zR c Q ++ [K]) _ hSplit (Or.inl (by rw [z11]; rfl))
    with ⟨m1,x1,y1,a3,b3,a4,b4,hJ1,hK1,hV1,_,_⟩
  have hSplit2 : mid ++ zR t0 Q ++ [K] = mid ++ (zR t0 Q ++ [K]) := by
    simp [List.append_assoc]
  rcases z1Y hK1 mid (zR t0 Q ++ [K]) hSplit2 (Or.inl hM)
    with ⟨m2,x2,y2,a5,b5,a6,b6,hJ2,hK2,hV2,_,_⟩
  have hL1 := z2R hJ
  have hL2 := z2R hJ2
  have hO1 := z2T c m m1 x1 a3 b3 hC hJ1
  have hO2 := z2T t0 m2 k' y2 a6 b6 hT hK2
  rw [hV,hV1,hV2] at hL
  simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil] at hL
  omega
lemma z2V (u ds : zW) (A H k k' : Nat) (v : zW) (a b : Rat)
    (p c : Nat) (mid : zW) (t0 : Nat)
    (hD : zDg A H ds) (hHeight : z1h u * ((2 ^ H : Nat) : Rat) = 1)
    (hI : zPS k (u ++ ds ++ [K]) k' v a b)
    (hU : z0Z u = true) (hM : z0Z mid = true)
    (hDs : ds = zR c Q ++ K :: (mid ++ zR t0 Q))
    (hP : 16 <= p) (hC : (p - 2) / 2 <= c) (hT : p - 2 <= t0) :
    ∃ J : Nat,(3 * (p + 1)) / 2 + 5 <= J /\ z1h (V :: (v ++ [V])) * ((2 ^ J : Nat) : Rat) = 1 := by
  have hEq : u ++ ds ++ [K] =
      u ++ zR c Q ++ K :: (mid ++ zR t0 Q ++ [K]) := by
    rw [hDs]; simp [List.append_assoc]
  have hI' : zPS k (u ++ zR c Q ++ K :: (mid ++ zR t0 Q ++ [K])) k' v a b := by
    rwa [<- hEq]
  rcases z2U k u c mid t0 k' v a b (by omega) (by omega) hU hM hI' with ⟨g,hGain,hCount⟩
  refine ⟨1 + 3 * g,?_,?_⟩
  · have hArith := z2O p hP
    omega
  · rw [<- hEq] at hGain
    have hWidth := (zDw hD).1
    rw [z1m,z1m] at hGain
    dsimp [z1h] at hGain
    rw [hWidth] at hGain
    dsimp [z1h]
    rw [z1m]
    dsimp [z1h]
    have hPow8 : ((2 ^ (1 + 3 * g) : Nat) : Rat) = 2 * ((8 ^ g : Nat) : Rat) := by
      have h8 : 2 ^ (1 + 3 * g) = 2 * (2 ^ 3) ^ g := by
        rw [zP2,Nat.pow_mul]; ring
      rw [h8]; push_cast; ring
    rw [hPow8]
    nlinarith
lemma z2W (p H : Nat) (alpha unit : Rat) (hPH : p <= H)
    (hA : alpha * ((2 ^ p : Nat) : Rat) = 1) (hU : unit * ((2 ^ H : Nat) : Rat) = 1) :
    unit * ((2 ^ (H - p) : Nat) : Rat) = alpha := by
  have hPos := z2r p
  have hEq : 2 ^ H = 2 ^ (H - p) * 2 ^ p := by
    rw [<- Nat.pow_add,Nat.sub_add_cancel hPH]
  have hEqQ : ((2 ^ H : Nat) : Rat) = ((2 ^ (H - p) : Nat) : Rat) * ((2 ^ p : Nat) : Rat) := by
    exact_mod_cast hEq
  rw [hEqQ] at hU
  nlinarith
lemma z2X (p H B : Nat) (ds : zW) (alpha unit : Rat)
    (hD : zDg B H ds) (hP : 2 <= p) (hPH : p <= H)
    (hA : 0 < alpha) (hU : 0 < unit) (hSmall : unit <= alpha)
    (hAp : alpha * ((2 ^ p : Nat) : Rat) = 1) (hUh : unit * ((2 ^ H : Nat) : Rat) = 1)
    (hDef : unit * z1f ds <= (5 / 2) * alpha) :
    ∃ u,ds = u ++ zR (p - 2) Q := by
  have hShift : unit * ((2 ^ (H - (p - 2)) : Nat) : Rat) = 4 * alpha := by
    have heq : H - (p - 2) = (H - p) + 2 := by omega
    rw [heq,Nat.pow_add,Nat.cast_mul]
    have h4 : ((2 ^ 2 : Nat) : Rat) = 4 := by norm_num
    rw [h4]
    have hDS := z2W p H alpha unit hPH hAp hUh
    linarith
  have hZ := z1n hD
  have hD' : zDg B ((H - (p - 2)) + (p - 2)) ds := by
    have heq : (H - (p - 2)) + (p - 2) = H := by omega
    rwa [heq]
  refine z21 (H - (p - 2)) (p - 2) B ds hD' ?_
  have heq : (H - (p - 2)) + (p - 2) = H := by omega
  rw [heq]
  have hle_q : ((2 ^ H : Nat) : Rat) <= (B : Rat) + ((2 ^ (H - (p - 2)) : Nat) : Rat) := by
    nlinarith
  exact_mod_cast hle_q
lemma z2Y {B H : Nat} {ds : zW} (hI : zDg B H ds) (hZ : 0 < z1f ds) :
    ∃ c w,ds = zR c Q ++ K :: w := by
  induction hI with
  | nil => dsimp [z1f] at hZ; linarith
  | @zero A H u _ _ => exact ⟨0,u,rfl⟩
  | @one A H u _ ih =>
    dsimp [z1f] at hZ
    rcases ih (by linarith) with ⟨c,w,rfl⟩
    exact ⟨c + 1,w,by rw [List.replicate_succ,List.cons_append]⟩
lemma z2Z (c : Nat) :
    ∀ (s : Nat) (u v : zW),
      zR s Q ++ u = zR c Q ++ K :: v -> s <= c := by
  induction c with
  | zero =>
    intro s u v hE
    cases s with
    | zero => omega
    | succ s =>
      rw [List.replicate_succ,List.cons_append] at hE
      simp at hE
  | succ c ih =>
    intro s u v hE
    cases s with
    | zero => omega
    | succ s =>
      rw [List.replicate_succ,List.cons_append,List.replicate_succ,List.cons_append] at hE
      injection hE with _ hE'
      have hle := ih s u v hE'
      omega
lemma z30 (u v : zW) (c s : Nat) (hC : z0Z u = true)
    (hE : u ++ zR c Q = v ++ zR s Q) : s <= c := by
  by_contra hGt
  have hlt : c < s := by omega
  have hs : s = (s - c) + c := by omega
  rw [hs,List.replicate_add,<- List.append_assoc] at hE
  have hEq := List.append_inj_left' hE (by simp)
  subst hEq
  have hpos : 0 < s - c := by omega
  have hsc : s - c = (s - c - 1) + 1 := by omega
  rw [hsc,z13,<- List.append_assoc,z11] at hC
  contradiction
lemma z31 (u v : zW) (hC : z0Z (u ++ v) = true) : z0Z v = true := by
  induction u with
  | nil => exact hC
  | cons a u ih =>
    exact ih (zCo a (u ++ v) hC)
lemma z32 (c : Nat) (mid : zW) (hM : z0Z mid = true) :
    z0Z (zR c Q ++ K :: mid) = true := by
  induction c with
  | zero =>
    cases mid with
    | nil => rfl
    | cons x xs => exact hM
  | succ c ih =>
    rw [List.replicate_succ,List.cons_append]
    cases c with
    | zero => exact ih
    | succ c' => exact ih
lemma z33 {B H : Nat} {ds : zW} (s t0 : Nat)
    (hD : zDg B H ds) (hZ : 0 < z1f ds)
    (hLo : ∃ u,ds = zR s Q ++ u)
    (hHi : ∃ u,ds = u ++ zR t0 Q) :
    ∃ c mid n,ds = zR c Q ++ K :: (mid ++ zR n Q) /\
      z0Z mid = true /\ s <= c /\ t0 <= n := by
  rcases hLo with ⟨lo,hLo⟩
  rcases hHi with ⟨hi,hHi⟩
  rcases z2Y hD hZ with ⟨c,w,hE⟩
  rcases z14 w with ⟨mid,n,rfl,hM⟩
  refine ⟨c,mid,n,hE,hM,?_,?_⟩
  · exact z2Z c s lo (mid ++ zR n Q) (hLo.symm.trans hE)
  · have hEq : (zR c Q ++ K :: mid) ++ zR n Q =
        hi ++ zR t0 Q := by
      simpa [List.append_assoc] using hE.symm.trans hHi
    exact z30 (zR c Q ++ K :: mid) hi n t0
      (z32 c mid hM) hEq
lemma z34 {n : Nat} {u : zW} {b : Nat} {v : zW}
    (hI : zEf n u b v) (hEnd : ∃ w,u = w ++ [V]) :
    ∃ w,v = w ++ [V] := by
  rcases hEnd with ⟨w,rfl⟩
  change zEf n (w ++ zR 1 V) b v at hI
  rcases z1L w 1 n b v hI with ⟨x,_,hEq,_⟩
  exact ⟨x,hEq⟩
lemma z35 (p : Nat) (hP : 16 <= p) :
    z1h (zR p V) <= 1 / 65536 := by
  have hW := (z2s p).2
  have hPos := zSp (zR p V)
  have hB : (65536 : Rat) <= ((2 ^ p : Nat) : Rat) := by
    have h1 : 2 ^ 16 <= 2 ^ p := Nat.pow_le_pow_right (by omega) hP
    exact_mod_cast h1
  nlinarith
lemma z36 (p H : Nat) (alpha unit : Rat) (hPH : p + 11 <= H)
    (hA : 0 < alpha) (hU : 0 < unit)
    (hAp : 1 / 2 <= alpha * ((2 ^ p : Nat) : Rat))
    (hUh : unit * ((2 ^ H : Nat) : Rat) = 1) :
    unit <= alpha * (1 / 1024) := by
  have hHigh : 2048 * ((2 ^ p : Nat) : Rat) <= ((2 ^ H : Nat) : Rat) := by
    have h1 : 2 ^ (11 + p) <= 2 ^ H := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ (11 + p) = 2048 * 2 ^ p := by rw [Nat.pow_add]
    rw [h2] at h1; exact_mod_cast h1
  have hPos := z2r p
  nlinarith
lemma z37 (alpha e f unit delta R e' rho : Rat)
    (hA : 0 < alpha) (hE0 : 0 <= e) (hF0 : 0 <= f) (hU0 : 0 <= unit)
    (hE : e <= alpha * (3 / 64)) (hF : f <= alpha * (1 / 128)) (hU : unit <= alpha * (1 / 1024))
    (hE'0 : 0 <= e') (hE' : e' <= (e + f) * (1 / 2))
    (hRlo : rho * (1 / 2) <= R) (hRhi : R <= rho * (1 / 2) + 2 * e')
    (hDlo : 2 * alpha + rho - e * (1 / 4) - 3 * f <= delta)
    (hDhi : delta <= 2 * alpha + rho + 4 * e + 4 * f) :
    (3 / 4) * alpha <= delta * (1 / 2) - 4 * unit - R /\
    delta * (1 / 2) - 4 * unit - R <= (5 / 4) * alpha := by
  constructor <;> linarith
lemma z38 (J k carry : Nat) (alpha unit delta R rho : Rat)
    (hPos : 0 < alpha) (hSmall : alpha <= 1 / 32) (hUnit : 0 < unit) (hTiny : unit <= alpha * (1 / 1024))
    (hHeight : unit * ((2 ^ J : Nat) : Rat) = 1)
    (hRho0 : 0 <= rho) (hRho : rho <= 2 * alpha)
    (hDl : (7 / 4) * alpha + rho <= delta) (hDu : delta <= (9 / 4) * alpha + rho)
    (hRl : rho * (1 / 2) <= R) (hRu : R <= rho * (1 / 2) + alpha * (1 / 4))
    (hK : (k : Rat) * unit = 2 + 4 * unit - delta * (1 / 2))
    (hC : ((1 + carry : Nat) : Rat) * unit = 1 + R) :
    ∃ A B : Nat,A + 2 ^ J = k /\ B + 2 ^ J = A + carry /\
      2 ^ J <= A * 2 /\ A < 2 ^ J /\ 2 ^ J <= B * 2 /\ B < 2 ^ J := by
  push_cast at hC
  have hK_gt : ((2 ^ J : Nat) : Rat) + ((2 ^ J : Nat) : Rat) * (1 / 2) <= (k : Rat) := by nlinarith
  have hK_lt : (k : Rat) < ((2 ^ J : Nat) : Rat) * 2 := by nlinarith
  have hB_gt : ((2 ^ J : Nat) : Rat) * 2 + ((2 ^ J : Nat) : Rat) * (1 / 2) <= (k : Rat) + (carry : Rat) := by nlinarith
  have hB_lt : (k : Rat) + (carry : Rat) < ((2 ^ J : Nat) : Rat) * 3 := by nlinarith
  have hK2 : 2 ^ J * 3 <= k * 2 := by
    have h1 : ((2 ^ J : Nat) : Rat) * 3 <= (k : Rat) * 2 := by linarith
    exact_mod_cast h1
  have hK3 : k < 2 ^ J * 2 := by
    have h1 : (k : Rat) < ((2 ^ J : Nat) : Rat) * 2 := by linarith
    exact_mod_cast h1
  have hB2 : 2 ^ J * 5 <= (k + carry) * 2 := by
    have h1 : ((2 ^ J : Nat) : Rat) * 5 <= ((k : Rat) + (carry : Rat)) * 2 := by linarith
    exact_mod_cast h1
  have hB3 : k + carry < 2 ^ J * 3 := by
    have h1 : (k : Rat) + (carry : Rat) < ((2 ^ J : Nat) : Rat) * 3 := by linarith
    exact_mod_cast h1
  refine ⟨k - 2 ^ J,k + carry - (2 ^ J + 2 ^ J),by omega,by omega,by omega,by omega,by omega,by omega⟩
inductive Copy : Nat -> Nat -> zW -> zW -> Nat -> Nat -> Prop where
  | nil (n k : Nat) : Copy n k [] [] n k
  | T {n k : Nat} {u v : zW} {b k' : Nat} :
      Copy (1 + n * 2) (2 + k * 2) u v b k' -> Copy n (3 + k) (V :: u) (V :: v) b k'
  | d00 {n k : Nat} {u v : zW} {b k' : Nat} :
      Copy n (k * 2) u v b k' -> Copy (n * 2) (2 + k * 4) (K :: u) (K :: v) b k'
  | d01 {n k : Nat} {u v : zW} {b k' : Nat} :
      Copy n (1 + k * 2) u v b k' -> Copy (1 + n * 2) (2 + k * 4) (K :: u) (Q :: v) b k'
  | d10 {n k : Nat} {u v : zW} {b k' : Nat} :
      Copy n (1 + k * 2) u v b k' -> Copy (n * 2) (4 + k * 4) (Q :: u) (Q :: v) b k'
  | d11 {n k : Nat} {u v : zW} {b k' : Nat} :
      Copy (1 + n) (k * 2) u v b k' -> Copy (1 + n * 2) (4 + k * 4) (Q :: u) (K :: v) b k'
lemma z39 {n k : Nat} {u v : zW} {b k' : Nat} (hI : Copy n k u v b k') :
    zEf n u b v := by
  induction hI with
  | nil n k => exact zEf.nil n
  | T _ ih => exact zEf.T ih
  | d00 _ ih => exact zEf.d00 ih
  | d01 _ ih => exact zEf.d01 ih
  | d10 _ ih => exact zEf.d10 ih
  | d11 _ ih => exact zEf.d11 ih
lemma z3a {n k : Nat} {u v : zW} {b k' : Nat} (h1 : Copy n k u v b k') :
    ∀ {w x : zW} {c k'' : Nat},Copy b k' w x c k'' -> Copy n k (u ++ w) (v ++ x) c k'' := by
  induction h1 with
  | nil _ _ => intro w x c k'' h2; exact h2
  | T _ ih => intro w x c k'' h2; exact Copy.T (ih h2)
  | d00 _ ih => intro w x c k'' h2; exact Copy.d00 (ih h2)
  | d01 _ ih => intro w x c k'' h2; exact Copy.d01 (ih h2)
  | d10 _ ih => intro w x c k'' h2; exact Copy.d10 (ih h2)
  | d11 _ ih => intro w x c k'' h2; exact Copy.d11 (ih h2)
lemma z3b (q : Nat) :
    ∀ (n k : Nat),Copy n (4 + k) (zR q V) (zR q V) ((1 + n) * 2 ^ q - 1) (4 + k * 2 ^ q) := by
  induction q with
  | zero =>
    intro n k
    have h1 : (1 + n) * 2 ^ 0 - 1 = n := by simp
    have h2 : 4 + k * 2 ^ 0 = 4 + k := by simp
    rw [h1,h2]
    exact Copy.nil n (4 + k)
  | succ q ih =>
    intro n k
    rw [List.replicate_succ]
    have hpos := zPp q
    have hSub := ih (1 + n * 2) (k * 2)
    have h1 : (1 + (1 + n * 2)) * 2 ^ q - 1 = (1 + n) * 2 ^ (q + 1) - 1 := by
      rw [Nat.pow_succ]; ring_nf
    have h3 : 4 + (k * 2) * 2 ^ q = 4 + k * 2 ^ (q + 1) := by
      rw [Nat.pow_succ]; ring
    rw [h1,h3] at hSub
    have h4 : 4 + k = 3 + (1 + k) := by omega
    have h5 : 2 + (1 + k) * 2 = 4 + k * 2 := by omega
    rw [h4]
    refine Copy.T ?_
    rwa [h5]
lemma z3c {n : Nat} {u : zW} {b : Nat} {v : zW}
    (hI : zEf n u b v) :
    0 <= ((1 + b : Nat) : Rat) * z1h u - ((1 + n : Nat) : Rat) /\
    ((1 + b : Nat) : Rat) * z1h u - ((1 + n : Nat) : Rat) <= 2 * z1e u := by
  have hBud := z1J hI
  have hW := z1I hI
  have hSu := z1i u
  have hSv := z1i v
  have hNu := zWn u
  have hNv := zWn v
  constructor <;> linarith
lemma z3d {n : Nat} {da : zW} {A H B : Nat}
    (hD : zDg A H da) (hSum : A + n = B + 2 ^ H) (hBound : B < 2 ^ H) :
    ∃ d,zDg B H d /\ zEf n (da ++ [Q]) 1 (d ++ [K]) := by
  rcases z1B da n with ⟨b,d,hE⟩
  rcases z1G hE hD with ⟨C,hCd,hEq⟩
  have hCb := z1b hCd
  have hb1 : b = 1 := by
    rcases b with _ | _ | b'
    · omega
    · rfl
    · have : 2 ^ H + 2 ^ H <= (b' + 1 + 1) * 2 ^ H := by
        have hmul : (b' + 1 + 1) * 2 ^ H = b' * 2 ^ H + 2 ^ H + 2 ^ H := by ring
        omega
      omega
  subst hb1
  have hCB : C = B := by omega
  subst hCB
  refine ⟨d,hCd,z1D hE ?_⟩
  exact @zEf.d11 0 [] 1 [] (zEf.nil 1)
def z3e (u v : zW) : Rat := 3 * z1e u + z1g u - z1g v
lemma z3f {n k : Nat} {u v : zW} {b k' : Nat} (hI : Copy n k u v b k') :
    z3e u v - (((1 + b : Nat) : Rat) * z1h u - ((1 + n : Nat) : Rat)) = 2 * z1e u /\
    0 <= ((1 + b : Nat) : Rat) * z1h u - ((1 + n : Nat) : Rat) /\
    ((1 + b : Nat) : Rat) * z1h u - ((1 + n : Nat) : Rat) <= 2 * z1e u := by
  have hE := z39 hI
  have hBud := z1J hE
  have hBnd := z3c hE
  unfold z3e
  push_cast at hBud hBnd ⊢
  refine ⟨by linarith,by linarith,by linarith⟩
lemma z3g {n k : Nat} {u v : zW} {b k' : Nat} (hC : Copy n k u v b k') :
    ∀ (w : zW) (c : Nat) (x : zW),
      zEf n (u ++ w) c x -> ∃ y,x = v ++ y /\ zEf b w c y := by
  induction hC with
  | nil _ _ => intro w c x hE; exact ⟨x,rfl,hE⟩
  | T _ ih =>
    intro w c x hE
    cases hE with
    | T hSub =>
      rcases ih w c _ hSub with ⟨y,rfl,hY⟩
      exact ⟨y,rfl,hY⟩
  | @d00 n0 k0 u0 v0 b0 k0' _ ih =>
    intro w c x hE
    generalize hm : n0 * 2 = m at hE
    cases hE with
    | @d00 n1 _ _ _ hSub =>
      have hn : n0 = n1 := by omega
      subst hn
      rcases ih w c _ hSub with ⟨y,rfl,hY⟩
      exact ⟨y,rfl,hY⟩
    | d01 _ => omega
  | @d01 n0 k0 u0 v0 b0 k0' _ ih =>
    intro w c x hE
    generalize hm : 1 + n0 * 2 = m at hE
    cases hE with
    | d00 _ => omega
    | @d01 n1 _ _ _ hSub =>
      have hn : n0 = n1 := by omega
      subst hn
      rcases ih w c _ hSub with ⟨y,rfl,hY⟩
      exact ⟨y,rfl,hY⟩
  | @d10 n0 k0 u0 v0 b0 k0' _ ih =>
    intro w c x hE
    generalize hm : n0 * 2 = m at hE
    cases hE with
    | @d10 n1 _ _ _ hSub =>
      have hn : n0 = n1 := by omega
      subst hn
      rcases ih w c _ hSub with ⟨y,rfl,hY⟩
      exact ⟨y,rfl,hY⟩
    | d11 _ => omega
  | @d11 n0 k0 u0 v0 b0 k0' _ ih =>
    intro w c x hE
    generalize hm : 1 + n0 * 2 = m at hE
    cases hE with
    | d10 _ => omega
    | @d11 n1 _ _ _ hSub =>
      have hn : n0 = n1 := by omega
      subst hn
      rcases ih w c _ hSub with ⟨y,rfl,hY⟩
      exact ⟨y,rfl,hY⟩
def z3h : zW -> Bool
  | [] => true
  | Q :: V :: v => z3h (V :: v)
  | Q :: _ => false
  | _ :: v => z3h v
lemma z3i (q : Nat) (v : zW) (h : z3h v = true) :
    z3h (zR q V ++ v) = true := by
  induction q with
  | zero => exact h
  | succ q ih => rw [List.replicate_succ,List.cons_append]; exact ih
lemma z3j {n k : Nat} {u v : zW} {b k' : Nat} (hC : Copy n k u v b k') :
    z3h v = true ->
    ∀ (w : zW) (k'' : Nat) (x : zW) (a c : Rat),
      zPS k (v ++ w) k'' x a c ->
      ∃ y a' c',x = u ++ y /\ zPS k' w k'' y a' c' /\
        a = z3e u v + z1h u * a' /\ c = z1h u * c' := by
  induction hC with
  | nil _ _ =>
    intro _ w k'' x a c hI
    exact ⟨x,a,c,rfl,hI,by unfold z3e; simp [z1e,z1g,z1h],by simp [z1h]⟩
  | @T n0 k0 u0 v0 b0 k0' _ ih =>
    intro hSafe w k'' x a c hI
    have hSafe' : z3h v0 = true := hSafe
    generalize hm : 3 + k0 = m at hI
    cases hI with
    | @T m0 _ _ _ _ _ hSub =>
      have hk0 : k0 = m0 := by omega
      subst hk0
      rcases ih hSafe' w k'' _ _ _ hSub with ⟨y,a',c',rfl,hY,hA,hC'⟩
      refine ⟨y,a',c',rfl,hY,?_,?_⟩
      · unfold z3e at hA ⊢; dsimp [z1e,z1g,z1h]; linarith
      · dsimp [z1h]; linarith
  | @d00 n0 k0 u0 v0 b0 k0' _ ih =>
    intro hSafe w k'' x a c hI
    have hSafe' : z3h v0 = true := hSafe
    generalize hm : 2 + k0 * 4 = m at hI
    cases hI with
    | @short00 m0 _ _ _ _ _ hSub =>
      have hk0 : k0 = m0 := by omega
      subst hk0
      rcases ih hSafe' w k'' _ _ _ hSub with ⟨y,a',c',rfl,hY,hA,hC'⟩
      refine ⟨y,a',c',rfl,hY,?_,?_⟩
      · unfold z3e at hA ⊢; dsimp [z1e,z1g,z1h]; linarith
      · dsimp [z1h]; linarith
    | short10 _ => omega
  | @d01 n0 k0 u0 v0 b0 k0' _ ih =>
    intro hSafe w k'' x a c hI
    have hSafe' : z3h v0 = true := by
      cases v0 with
      | nil => contradiction
      | cons z zs => cases z <;> first | exact hSafe | contradiction
    have hv0 : ∃ zs,v0 = V :: zs := by
      cases v0 with
      | nil => contradiction
      | cons z zs => cases z <;> first | exact ⟨zs,rfl⟩ | contradiction
    rcases hv0 with ⟨zs,rfl⟩
    simp only [List.cons_append] at hI
    generalize hm : 2 + k0 * 4 = m at hI
    cases hI with
    | @short01 m0 _ _ _ _ _ hSub =>
      have hk0 : k0 = m0 := by omega
      subst hk0
      rcases ih hSafe' w k'' _ _ _ hSub with ⟨y,a',c',rfl,hY,hA,hC'⟩
      refine ⟨y,a',c',rfl,hY,?_,?_⟩
      · unfold z3e at hA ⊢; dsimp [z1e,z1g,z1h] at hA ⊢; linarith
      · dsimp [z1h]; linarith
    | short11 _ => omega
  | @d10 n0 k0 u0 v0 b0 k0' _ ih =>
    intro hSafe w k'' x a c hI
    have hSafe' : z3h v0 = true := by
      cases v0 with
      | nil => contradiction
      | cons z zs => cases z <;> first | exact hSafe | contradiction
    have hv0 : ∃ zs,v0 = V :: zs := by
      cases v0 with
      | nil => contradiction
      | cons z zs => cases z <;> first | exact ⟨zs,rfl⟩ | contradiction
    rcases hv0 with ⟨zs,rfl⟩
    simp only [List.cons_append] at hI
    generalize hm : 4 + k0 * 4 = m at hI
    cases hI with
    | short01 _ => omega
    | @short11 m0 _ _ _ _ _ hSub =>
      have hk0 : k0 = m0 := by omega
      subst hk0
      rcases ih hSafe' w k'' _ _ _ hSub with ⟨y,a',c',rfl,hY,hA,hC'⟩
      refine ⟨y,a',c',rfl,hY,?_,?_⟩
      · unfold z3e at hA ⊢; dsimp [z1e,z1g,z1h] at hA ⊢; linarith
      · dsimp [z1h]; linarith
  | @d11 n0 k0 u0 v0 b0 k0' _ ih =>
    intro hSafe w k'' x a c hI
    have hSafe' : z3h v0 = true := hSafe
    generalize hm : 4 + k0 * 4 = m at hI
    cases hI with
    | short00 _ => omega
    | @short10 m0 _ _ _ _ _ hSub =>
      have hk0 : k0 = m0 := by omega
      subst hk0
      rcases ih hSafe' w k'' _ _ _ hSub with ⟨y,a',c',rfl,hY,hA,hC'⟩
      refine ⟨y,a',c',rfl,hY,?_,?_⟩
      · unfold z3e at hA ⊢; dsimp [z1e,z1g,z1h]; linarith
      · dsimp [z1h]; linarith
lemma z3k (pre pe : zW) (carry budget : Nat) (u ds : zW)
    (A H k : Nat) (v : zW) (a b : Rat) (s : Nat) (e f : Rat)
    (hC : Copy 0 12 pre pe carry budget) (hSafe : z3h pe = true)
    (hI : zPS 12 (pe ++ u ++ ds ++ [K]) k v a b)
    (hD : zDg A H ds) (hCut : z0Z u = true)
    (hLow : ∃ c w,(0 < c /\ s <= c) /\ ds = zR c Q ++ K :: w)
    (hErr : e = z1h pre * z1e u)
    (hBound : (z1h pre * z1h u) * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds) <=
      f * ((2 ^ (s + s / 2) : Nat) : Rat)) :
    ∃ w,v = pre ++ w /\
      z1e (V :: (v ++ [V])) <= z1e pre * (1 / 2) + (e + f) * (1 / 2) /\
      z3e pre pe - e * (1 / 4) - 3 * f <= a - b /\
      a - b <= z3e pre pe + 4 * e + 4 * f := by
  have hEq : pe ++ u ++ ds ++ [K] = pe ++ (u ++ (ds ++ [K])) := by simp [List.append_assoc]
  rw [hEq] at hI
  rcases z3j hC hSafe (u ++ (ds ++ [K])) k v a b hI with ⟨w,c,d,rfl,hJ,hPos,hNeg⟩
  rcases z1Y hJ u (ds ++ [K]) rfl (Or.inl hCut)
    with ⟨m,x,y,a1,b1,a2,b2,hK,hL,rfl,hP,hN⟩
  have hBK := z1O hK
  have hBL := z1O hL
  have hSK := z1V hK
  have hSpre := zSp pre
  have hSu := zSp u
  have hSx := zSp x
  have hWds := zWn ds
  have hPow := z2r (s + s / 2)
  have hSpx : 0 <= z1h pre * z1h x := mul_nonneg (le_of_lt hSpre) (le_of_lt hSx)
  have hSx_le : z1h pre * z1h x <= z1h pre * z1h u := by nlinarith
  have hZ_pos : 0 <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds := by linarith
  have hF : (z1h pre * z1h x) * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds) <=
      f * ((2 ^ (s + s / 2) : Nat) : Rat) := by
    nlinarith
  rcases z2H s ds A H m k y a2 b2 (z1h pre * z1h x) f hD hL hLow
    hSpx hF with ⟨hMt,hPt,hNt⟩
  have hMt' : z1h pre * (z1h x * z1e y) <= f := by linarith
  have hPt' : z1h pre * (z1h x * a2) <= 4 * f := by linarith
  have hNt' : z1h pre * (z1h x * b2) <= 3 * f := by linarith
  have hPa : 0 <= z1h pre * (z1h x * a2) := by
    have := mul_nonneg hSpx hBL.2.1; linarith
  have hPb : 0 <= z1h pre * (z1h x * b2) := by
    have := mul_nonneg hSpx hBL.2.2.2.1; linarith
  have hMx : z1h pre * z1e x <= e := by nlinarith
  have hA1_0 : 0 <= z1h pre * a1 := by nlinarith
  have hA1 : z1h pre * a1 <= 4 * e := by nlinarith
  have hB1_0 : 0 <= z1h pre * b1 := by nlinarith
  have hB1 : z1h pre * b1 <= e * (1 / 4) := by nlinarith
  refine ⟨x ++ y,by simp [List.append_assoc],?_,?_,?_⟩
  · dsimp [z1e]
    rw [z1j,z1j,z1j]
    dsimp [z1e,z1h]
    linarith
  · rw [hP] at hPos; rw [hN] at hNeg
    linarith
  · rw [hP] at hPos; rw [hN] at hNeg
    linarith
lemma z3l (pre pe : zW) (b k : Nat) (u : zW) (carry : Nat) (eff : zW)
    (hC : Copy 0 12 pre pe b k) (hE : zEf 0 (pre ++ u) carry eff) :
    z3e pre pe - 2 * z1e pre <= ((1 + carry : Nat) : Rat) * z1h (pre ++ u) - 1 /\
    ((1 + carry : Nat) : Rat) * z1h (pre ++ u) - 1 <= z3e pre pe - 2 * z1e pre + 2 * z1h pre * z1e u := by
  rcases z3g hC u carry eff hE with ⟨v,_,hV⟩
  have hBnd := z3c hV
  have hSpre := zSp pre
  have hLed := (z3f hC).1
  rw [z1m]
  push_cast at hBnd hLed ⊢
  constructor <;> nlinarith
def z3m (u v : zW) : Prop := ∃ b k,Copy 0 12 u v b k
inductive Step : zW -> zW -> Prop where
  | intro (orig eff : zW) (k : Nat) (v : zW) (a b : Rat) (J A : Nat) (da : zW) :
      zEf 0 orig 1 eff -> zPS 12 eff k v a b ->
      zDg A J da -> A + 2 ^ J = k ->
      Step orig (V :: (v ++ V :: (da ++ [Q])))
inductive zAg (av : zW) : Nat -> Nat -> zW -> Prop where
  | intro (p q H : Nat) (u : zW) (A : Nat) (da : zW)
      (carry : Nat) (eff : zW) (B : Nat) (db : zW) (tau alpha : Rat) :
      16 <= p -> 5 <= q -> (3 * p) / 2 + 5 <= H ->
      (∃ rest,u = (zR q V ++ av) ++ rest) ->
      (∃ rest,u = rest ++ [V]) ->
      z1e (zR q V ++ av) = alpha ->
      1 / 2 <= alpha * ((2 ^ p : Nat) : Rat) ->
      alpha * ((2 ^ p : Nat) : Rat) <= 1 ->
      z1h u * ((2 ^ H : Nat) : Rat) = 1 ->
      zDg A H da ->
      zEf 0 u carry eff ->
      A + carry = B + 2 ^ H ->
      zDg B H db ->
      Reserve p tau ->
      z1e u <= alpha * (1 + (3 / 64) - tau) ->
      (3 / 2) * alpha <= z1h u * z1f db ->
      z1h u * z1f db <= (5 / 2) * alpha ->
      (∃ rest,db = zR ((p - 2) / 2) Q ++ rest) ->
      zAg av p q (u ++ da ++ [Q])
lemma z3n (q : Nat) (w : Word) :
    zR (1 + q) w = w :: zR q w := by
  rw [Nat.add_comm 1 q,List.replicate_succ]
lemma z3o (av ev : zW) (hSafe : z3h ev = true)
    (hStable : ∀ q,5 <= q -> z3m (zR q V ++ av) (zR q V ++ ev)) :
    ∀ (p q : Nat) (orig : zW),zAg av p q orig ->
      ∃ out,Step orig out /\ zAg av (1 + p) (1 + q) out := by
  intro p q orig hG
  rcases hG with ⟨H,u,A,da,carry,eff,B,db,tau,alpha,
    hP,hQ,hHbound,⟨rest,hStart⟩,hEnd,hMass,hApLow,hApHigh,hHeight,
    hDA,hEff,hSum,hDB,hRes,hM,hDlo,hDhi,hLow⟩
  set pre := zR q V ++ av
  set pe := zR q V ++ ev
  set unit := z1h u
  have hPowP := z2r p
  have hAlpha : 0 < alpha := by nlinarith
  have hUnit : 0 < unit := zSp u
  set dyadic := z1h (zR p V)
  have hDP : dyadic * ((2 ^ p : Nat) : Rat) = 1 := (z2s p).2
  have hDyadic : 0 < dyadic := zSp (zR p V)
  have hAupper : alpha <= dyadic := by nlinarith
  have hAsmall : dyadic <= 1 / 65536 := z35 p hP
  rcases z2L hRes hP with ⟨hTau,hTauSmall⟩
  have hUsmall : unit <= alpha * (1 / 1024) :=
    z36 p H alpha unit (by omega) hAlpha hUnit hApLow hHeight
  rcases hStable q hQ with ⟨bc,kc,hCopyPre⟩
  have hSafePre : z3h pe = true := z3i q ev hSafe
  rcases z3f hCopyPre with ⟨hLedger,hRhoLow,hRhoHigh⟩
  set rho := z3e pre pe - 2 * alpha
  have hRho : 0 <= rho /\ rho <= 2 * alpha := by
    unfold rho; rw [<- hMass]; push_cast at hLedger hRhoLow hRhoHigh; constructor <;> linarith
  rcases z1I hEff with ⟨hEffScale,hEffMass⟩
  rcases z34 hEff hEnd with ⟨last_w,hElast⟩
  have hCut : z0Z eff = true := by rw [hElast,z11]; rfl
  have hNe : eff ≠ [] := by rw [hElast]; simp
  have hEffHeight : z1h eff * ((2 ^ H : Nat) : Rat) = 1 := by rw [hEffScale]; exact hHeight
  have hEffBound : z1e eff + z1h eff * (1 + z1f db) <= 1 / 128 := by
    rw [hEffScale]; nlinarith
  rcases z2v eff B H db hDB hEffHeight hCut hNe hEffBound with ⟨k,v,a,b,hIscan,hK⟩
  have hZ : 0 < z1f db := by nlinarith
  rcases z2X p H B db dyadic unit hDB (by omega) (by omega)
    hDyadic hUnit (by linarith) hDP hHeight (by nlinarith) with ⟨hi,hHi⟩
  rcases z33 ((p - 2) / 2) (p - 2) hDB hZ hLow ⟨hi,hHi⟩
    with ⟨c,mid,t0,hSplit,hMidCut,hC,hT⟩
  rcases z2V eff db B H 12 k v a b p c mid t0 hDB hEffHeight hIscan
    hCut hMidCut hSplit hP hC hT with ⟨J,hJbound,hJheight⟩
  set new_u := V :: (v ++ [V])
  set nu := z1h new_u
  have hNu : 0 < nu := zSp new_u
  have hNuSmall : nu <= alpha * (1 / 1024) :=
    z36 p J alpha nu (by omega) hAlpha hNu hApLow hJheight
  have hEffRest : ∃ w,eff = pe ++ w /\ zEf bc rest carry w := by
    rw [hStart] at hEff
    exact z3g hCopyPre rest carry eff hEff
  rcases hEffRest with ⟨w,hEstart,hEw⟩
  rcases z1I hEw with ⟨hWscale,hWmass⟩
  have hWcut : z0Z w = true := by
    rw [hEstart] at hCut; exact z31 pe w hCut
  set e := z1e u - alpha
  have hEeq : e = z1h pre * z1e w := by
    unfold e; rw [hStart,z1j,<- hWmass,hMass]; ring
  have hWw := zWn w
  have hSpre := zSp pre
  have hEpos : 0 <= e := by nlinarith
  have hEbound : e <= alpha * ((3 / 64) - tau) := by unfold e; linarith
  set s := (p - 2) / 2
  set pow := ((2 ^ (s + s / 2) : Nat) : Rat)
  have hPow : 0 < pow := z2r (s + s / 2)
  set f := unit + 2 * unit * z1f db / pow
  have hFeq : f * pow = unit * pow + 2 * unit * z1f db := by
    unfold f; have hne : pow ≠ 0 := ne_of_gt hPow
    calc (unit + 2 * unit * z1f db / pow) * pow
      _ = unit * pow + (2 * unit * z1f db / pow) * pow := by ring
      _ = unit * pow + 2 * unit * z1f db := by rw [div_mul_cancel₀ _ hne]
  have hFpos : 0 <= f := by
    have h1 : 0 <= f * pow := by rw [hFeq]; nlinarith
    nlinarith
  have hFbound : f <= alpha * tau * (1 / 4) :=
    z2N p H s alpha unit tau f hRes hP hHbound rfl hAlpha hUnit hApLow hHeight (by nlinarith)
  have hLow' : ∃ c0 w0,(0 < c0 /\ s <= c0) /\ db = zR c0 Q ++ K :: w0 :=
    ⟨c,mid ++ zR t0 Q,⟨by omega,hC⟩,hSplit⟩
  have hFactor : z1h pre * z1h w = unit := by
    unfold unit; rw [hWscale,hStart,<- z1m]
  have hScanStart : zPS 12 (pe ++ w ++ db ++ [K]) k v a b := by
    rw [hEstart] at hIscan; simpa [List.append_assoc] using hIscan
  rcases z3k pre pe bc kc w db B H k v a b s e f hCopyPre hSafePre
    hScanStart hDB hWcut hLow' hEeq (by rw [hFactor]; nlinarith)
    with ⟨tail,hVstart,hMnext,hDl,hDu⟩
  change z1e new_u <= z1e pre * (1 / 2) + (e + f) * (1 / 2) at hMnext
  rw [hMass] at hMnext
  have hDl' : 2 * alpha + rho - e * (1 / 4) - 3 * f <= a - b := by unfold rho; linarith
  have hDu' : a - b <= 2 * alpha + rho + 4 * e + 4 * f := by unfold rho; linarith
  rcases z1B new_u 0 with ⟨carry',eff',hEff'⟩
  have hNewStart : new_u = (V :: pre) ++ (tail ++ [V]) := by
    unfold new_u; rw [hVstart]; simp [List.append_assoc]
  have hPre_step : zR (1 + q) V ++ av = V :: pre := by
    unfold pre; rw [z3n,List.cons_append]
  have hPe_step : zR (1 + q) V ++ ev = V :: pe := by
    unfold pe; rw [z3n,List.cons_append]
  rcases hStable (1 + q) (by omega) with ⟨bc',kc',hCopyNew⟩
  rw [hPre_step,hPe_step] at hCopyNew
  have hEff'_rw : zEf 0 ((V :: pre) ++ (tail ++ [V])) carry' eff' := by
    rwa [<- hNewStart]
  have hRbounds := z3l (V :: pre) (V :: pe) bc' kc' (tail ++ [V]) carry' eff' hCopyNew hEff'_rw
  rw [<- hNewStart] at hRbounds
  have hNewMass : z1e new_u = alpha * (1 / 2) + (z1h pre * (1 / 2)) * z1e (tail ++ [V]) := by
    rw [hNewStart,z1j]; dsimp [z1e,z1h]; rw [hMass]
  have hCloss_step : z3e (V :: pre) (V :: pe) - 2 * z1e (V :: pre) = rho * (1 / 2) := by
    unfold rho z3e; dsimp [z1e,z1g,z1h]; rw [hMass]; ring
  have hScale_step : z1h (V :: pre) * z1e (tail ++ [V]) = z1e new_u - alpha * (1 / 2) := by
    dsimp [z1h]; linarith
  set R := ((1 + carry' : Nat) : Rat) * nu - 1
  have hRb : rho * (1 / 2) <= R /\ R <= rho * (1 / 2) + 2 * (z1e new_u - alpha * (1 / 2)) := by
    unfold R nu; constructor <;> linarith
  have hWtail := zWn (tail ++ [V])
  have hEnew : 0 <= z1e new_u - alpha * (1 / 2) := by nlinarith
  have hFtiny : f <= alpha * (1 / 128) := by nlinarith
  have hEtiny : e <= alpha * (3 / 64) := by nlinarith
  have hBudget := z2I (eff ++ db ++ [K]) k v a b hIscan
  rcases z38 J k carry' alpha nu (a - b) R rho
    hAlpha (by linarith) hNu hNuSmall hJheight hRho.1 hRho.2
    (by linarith) (by linarith) hRb.1 (by linarith) hBudget (by unfold R; ring)
    with ⟨A',B',hAsum,hBsum,hAl,hAu,hBl,hBu⟩
  rcases z18 J A' hAu with ⟨da',hDA'⟩
  rcases z18 J B' hBu with ⟨db',hDB'⟩
  rcases z2K hRes with ⟨tau',hRes',hTauStep⟩
  have hMkeep := z2P alpha tau tau' e f (z1e new_u - alpha * (1 / 2))
    (by linarith) hTauStep hEbound hFbound (by linarith)
  have hDkeep := z37 alpha e f nu (a - b) R (z1e new_u - alpha * (1 / 2)) rho
    hAlpha hEpos hFpos (by linarith) hEtiny hFtiny hNuSmall hEnew (by linarith)
    hRb.1 hRb.2 hDl' hDu'
  have hDef := z2J (eff ++ db ++ [K]) k v a b J A' B' carry' hIscan hJheight hAsum hBsum
  have hZnew := z1n hDB'
  have hDnew : nu * z1f db' = (a - b) * (1 / 2) - 4 * nu - R := by
    have hZ' : nu * z1f db' = 1 - ((1 + B' : Nat) : Rat) * nu := by
      calc nu * z1f db'
        _ = nu * ((z1f db' + (B' : Rat) + 1) - (1 + (B' : Rat))) := by ring
        _ = nu * (((2 ^ J : Nat) : Rat) - (1 + (B' : Rat))) := by rw [hZnew]
        _ = nu * ((2 ^ J : Nat) : Rat) - (1 + (B' : Rat)) * nu := by ring
        _ = 1 - (1 + (B' : Rat)) * nu := by rw [hJheight]
        _ = 1 - ((1 + B' : Nat) : Rat) * nu := by push_cast; ring
    rw [hZ']
    exact hDef
  have hLowNew : ∃ rest,db' = zR (((1 + p) - 2) / 2) Q ++ rest := by
    set r := (((1 + p) - 2) / 2) - 1
    have hHr : 1 + r = ((1 + p) - 2) / 2 /\ 1 + r * 2 <= p - 2 := by omega
    have hHighEnd : ∃ z,db = z ++ zR (1 + r * 2) Q := by
      refine ⟨hi ++ zR ((p - 2) - (1 + r * 2)) Q,?_⟩
      have heq : ((p - 2) - (1 + r * 2)) + (1 + r * 2) = p - 2 := by omega
      rw [List.append_assoc,<- List.replicate_add,heq,<- hHi]
    rcases hHighEnd with ⟨z,hHZ⟩
    have hSC : zPS 12 ((eff ++ z) ++ zR (1 + r * 2) Q ++ [K]) k v a b := by
      rw [hHZ] at hIscan; simpa [List.append_assoc] using hIscan
    rcases z2F r 12 (eff ++ z) k v a b carry' eff' A' B' J db'
      hSC hEff' hDB' (by omega) hAsum hBsum with ⟨z',hL⟩
    rw [hHr.1] at hL
    exact ⟨z',hL⟩
  have hAp_step : (alpha * (1 / 2)) * ((2 ^ (1 + p) : Nat) : Rat) = alpha * ((2 ^ p : Nat) : Rat) := by
    rw [zP2,Nat.cast_add]; ring
  refine ⟨new_u ++ da' ++ [Q],?_,?_⟩
  · have hOut_eq : new_u ++ da' ++ [Q] = V :: (v ++ V :: (da' ++ [Q])) := by
      unfold new_u; simp [List.append_assoc]
    rw [hOut_eq]
    have hOrig_eq : (u ++ da ++ [Q]) = u ++ (da ++ [Q]) := by simp [List.append_assoc]
    rw [hOrig_eq]
    rcases z3d hDA hSum (z1b hDB) with ⟨d,hDD,hEE⟩
    have hd_eq : d = db := z1d hDD hDB
    rw [hd_eq] at hEE
    have hEffFull : zEf 0 (u ++ (da ++ [Q])) 1 (eff ++ db ++ [K]) := by
      simpa [List.append_assoc] using z1D hEff hEE
    exact Step.intro (u ++ (da ++ [Q])) (eff ++ db ++ [K]) k v a b J A' da'
      hEffFull hIscan hDA' hAsum
  · refine zAg.intro (1 + p) (1 + q) J new_u A' da' carry' eff' B' db' tau' (alpha * (1 / 2))
      (by omega) (by omega) (by omega)
      ⟨tail ++ [V],by rw [hPre_step]; exact hNewStart⟩ ⟨V :: v,rfl⟩
      (by rw [hPre_step]; dsimp [z1e]; rw [hMass])
      (by rw [hAp_step]; exact hApLow)
      (by rw [hAp_step]; exact hApHigh)
      hJheight hDA' hEff' (by omega) hDB' hRes'
      (by linarith) (by rw [hDnew]; linarith) (by rw [hDnew]; linarith) hLowNew
lemma z3r' {n k n' k' m b k'' : Nat} {u v : zW}
    (hn : n' = 1 + n * 2) (hk : k = 3 + m) (hk' : k' = 2 + m * 2)
    (h : Copy n' k' u v b k'') : Copy n k (V :: u) (V :: v) b k'' := by
  subst hn hk hk'; exact Copy.T h
lemma z3s' {n k n' k' m b k'' : Nat} {u v : zW}
    (hn : n = n' * 2) (hk : k = 2 + m * 4) (hk' : k' = m * 2)
    (h : Copy n' k' u v b k'') : Copy n k (K :: u) (K :: v) b k'' := by
  subst hn hk hk'; exact Copy.d00 h
lemma z3t' {n k n' k' m b k'' : Nat} {u v : zW}
    (hn : n = 1 + n' * 2) (hk : k = 2 + m * 4) (hk' : k' = 1 + m * 2)
    (h : Copy n' k' u v b k'') : Copy n k (K :: u) (Q :: v) b k'' := by
  subst hn hk hk'; exact Copy.d01 h
lemma z3u' {n k n' k' m b k'' : Nat} {u v : zW}
    (hn : n = n' * 2) (hk : k = 4 + m * 4) (hk' : k' = 1 + m * 2)
    (h : Copy n' k' u v b k'') : Copy n k (Q :: u) (Q :: v) b k'' := by
  subst hn hk hk'; exact Copy.d10 h
lemma z3v' {n k n' k' m b k'' : Nat} {u v : zW}
    (hn : n = 1 + (n' - 1) * 2) (hn' : n' = 1 + (n' - 1)) (hk : k = 4 + m * 4) (hk' : k' = m * 2)
    (h : Copy n' k' u v b k'') : Copy n k (Q :: u) (K :: v) b k'' := by
  rw [hn,hk]; rw [hn',hk'] at h; exact Copy.d11 h
def zPf : Nat -> Nat -> Option (zW)
  | 0,_ => none
  | fuel + 1,k =>
    if k == 0 then none
    else if k == 1 then some []
    else
      match zPf fuel (k / 2) with
      | none => none
      | some da => some ((if k % 2 == 0 then K else Q) :: da)
lemma z3z (fuel : Nat) :
    ∀ (k : Nat) (da : zW),
      zPf fuel k = some da ->
      ∃ A J,zDg A J da /\ A + 2 ^ J = k := by
  induction fuel with
  | zero => intro k da h; contradiction
  | succ fuel ih =>
    intro k da h
    dsimp [zPf] at h
    cases hk0 : (k == 0) with
    | true => rw [hk0] at h; contradiction
    | false =>
      rw [hk0] at h
      cases hk1 : (k == 1) with
      | true =>
        rw [hk1] at h
        simp only [beq_iff_eq] at hk1; subst hk1
        injection h with h; subst h
        exact ⟨0,0,zDg.nil,rfl⟩
      | false =>
        rw [hk1] at h
        have hk2 : 2 <= k := by
          simp only [beq_eq_false_iff_ne] at hk0 hk1
          omega
        cases hrec : zPf fuel (k / 2) with
        | none => rw [hrec] at h; contradiction
        | some da' =>
          rw [hrec] at h
          injection h with h; subst h
          rcases ih (k / 2) da' hrec with ⟨A,J,hD,hSum⟩
          rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
          · have hc : (k % 2 == 0) = true := beq_iff_eq.mpr hmod
            rw [hc]
            refine ⟨A * 2,1 + J,zDg.zero hD,?_⟩
            rw [zP2]; omega
          · have hc : (k % 2 == 0) = false := beq_false_of_ne (by omega)
            rw [hc]
            refine ⟨1 + A * 2,1 + J,zDg.one hD,?_⟩
            rw [zP2]; omega
def z3A (orig : zW) : Option (zW) :=
  let (carry,eff) := zEe 0 orig
  if carry == 1 then
    match z2m 1024 eff 12 with
    | some (k,v) =>
      match zPf 512 k with
      | some da => with_zw (V :: (v ++ V :: (da ++ [Q]))) (fun out => some out)
      | none => none
    | none => none
  else none
lemma z3B (orig out : zW) (hR : z3A orig = some out) :
    Step orig out := by
  unfold z3A at hR
  have hE := zEs orig 0
  generalize hEff : zEe 0 orig = ce at hR hE
  rcases ce with ⟨carry,eff⟩
  dsimp only at hR hE
  split_ifs at hR with hc1
  simp only [beq_iff_eq] at hc1; subst hc1
  cases hScan : z2m 1024 eff 12 with
  | none => rw [hScan] at hR; contradiction
  | some kv =>
    rw [hScan] at hR
    rcases kv with ⟨k,v⟩
    dsimp only at hR
    cases hPw : zPf 512 k with
    | none => rw [hPw] at hR; contradiction
    | some da =>
      rw [hPw] at hR
      simp only [with_zw_eq] at hR
      injection hR with hR; subst hR
      rcases z2n 1024 eff 12 k v hScan with ⟨a,b,hI⟩
      rcases z3z 512 k da hPw with ⟨A,J,hDA,hSum⟩
      exact Step.intro orig eff k v a b J A da hE hI hDA hSum
inductive Rounds : zW -> zW -> Prop where
  | refl (u : zW) : Rounds u u
  | next {u v w : zW} : Step u v -> Rounds v w -> Rounds u w
lemma z3C {u v w : zW} (h1 : Rounds u v) (h2 : Rounds v w) : Rounds u w := by
  induction h1 with
  | refl _ => exact h2
  | next hS _ ih => exact Rounds.next hS (ih h2)
def z3D : Nat -> zW -> Option (zW)
  | 0,u => some u
  | n + 1,u =>
    match z3A u with
    | none => none
    | some v => z3D n v
lemma z3E (n : Nat) :
    ∀ (u w : zW),z3D n u = some w -> Rounds u w := by
  induction n with
  | zero =>
    intro u w h; injection h with h; subst h; exact Rounds.refl u
  | succ n ih =>
    intro u w h
    dsimp [z3D] at h
    cases hV : z3A u with
    | none => rw [hV] at h; contradiction
    | some v =>
      rw [hV] at h
      exact Rounds.next (z3B u v hV) (ih v w h)
lemma z3F {B H : Nat} {db : zW} (u high : zW) (alpha : Rat)
    (hD : zDg B H db)
    (hHeight : z1h u * ((2 ^ H : Nat) : Rat) = 1)
    (hHi : ∃ lo,db = lo ++ high)
    (hL : (3 / 2) * alpha * z1h high <= z1f high)
    (hR : z1f high + 1 <= (5 / 2) * alpha * z1h high) :
    (3 / 2) * alpha <= z1h u * z1f db /\ z1h u * z1f db <= (5 / 2) * alpha := by
  rcases hHi with ⟨lo,rfl⟩
  have hDig := z2q hD
  rw [List.all_append,Bool.and_eq_true] at hDig
  rcases z26 lo hDig.1 with ⟨A,hDA⟩
  rcases zDw hDA with ⟨hLs,hLm,hLo⟩
  rcases zDw hD with ⟨hDs,_,_⟩
  have hSplit := z1i lo
  have hWlo := zWn lo
  have hSu := zSp u
  have hSlo := zSp lo
  have hShigh := zSp high
  rw [z1m] at hDs
  set x := z1h u * z1h lo
  have hX : x * z1h high = 1 := by unfold x; nlinarith
  have hXP : 0 < x := by unfold x; nlinarith
  have hXL : (3 / 2) * alpha <= x * z1f high := by nlinarith
  have hXR : x * (z1f high + 1) <= (5 / 2) * alpha := by nlinarith
  rw [z1k]
  unfold x at *
  constructor <;> nlinarith

end BusyBeaver.WordCalculus
