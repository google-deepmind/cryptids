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
lemma e_z1N {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k u k' v a b) :
    z0Y u = true -> z1h v * 8 <= z1h u := by
  induction hI with
  | nil _ => intro h; contradiction
  | T _ ih => intro h; have h1 := ih h; dsimp [z1h]; linarith
  | @pair0 _ u _ v _ _ hSub _ =>
    intro _
    have h1 := z1V hSub
    dsimp [z1h]; linarith
  | @pair1 _ u _ v _ _ hSub _ =>
    intro _
    have h1 := z1V hSub
    dsimp [z1h]; linarith
  | short00 _ ih => intro h; have h1 := ih h; dsimp [z1h]; linarith
  | @short01 n u _ _ _ _ hSub ih =>
    intro h
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => have h1 := ih h; dsimp [z1h] at h1 ⊢; linarith
      | K =>
        generalize hk : 1 + n * 2 = k0 at hSub
        cases hSub <;> omega
      | Q => have h1 := ih h; dsimp [z1h] at h1 ⊢; linarith
  | short10 _ ih => intro h; have h1 := ih h; dsimp [z1h]; linarith
  | @short11 n u _ _ _ _ hSub ih =>
    intro h
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => have h1 := ih h; dsimp [z1h] at h1 ⊢; linarith
      | K =>
        generalize hk : 1 + n * 2 = k0 at hSub
        cases hSub <;> omega
      | Q => have h1 := ih h; dsimp [z1h] at h1 ⊢; linarith
lemma e_z1O {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k u k' v a b) :
    a - b - z1g v <= 3 * z1e u := by
  induction hI with
  | nil _ => simp [z1g,z1e]
  | @T _ u _ _ _ _ _ ih => have hw := zWn u; dsimp [z1g,z1e]; linarith
  | @pair0 _ u _ _ _ _ _ ih => have hw := zWn u; dsimp [z1g,z1e]; linarith
  | @pair1 _ u _ _ _ _ _ ih => have hw := zWn u; dsimp [z1g,z1e]; linarith
  | @short00 _ u _ _ _ _ _ ih => have hw := zWn u; dsimp [z1g,z1e]; linarith
  | @short01 _ u _ _ _ _ _ ih => have hw := zWn u; dsimp [z1g,z1e]; linarith
  | @short10 _ u _ _ _ _ _ ih => have hw := zWn u; dsimp [z1g,z1e]; linarith
  | @short11 _ u _ _ _ _ _ ih => have hw := zWn u; dsimp [z1g,z1e]; linarith
lemma e_z1P {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k u k' v a b) :
    ∀ {A H : Nat},zDg A H u ->
      ∃ l,Scan k u k' v l /\ a - b - z1g v <= 2 * z1e v + l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0,Scan.nil k,by simp [z1e,z1g]⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (z0X hD)
  | pair0 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD0 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hL⟩
    exact ⟨(1 + l) * (1 / 2),Scan.pair0 hJ,by dsimp [z1e,z1g]; linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD1 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hL⟩
    exact ⟨(1 / 4) + l * (1 / 2),Scan.pair1 hJ,by dsimp [z1e,z1g]; linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨1 + l * 2,Scan.short00 hJ,by dsimp [z1e,z1g]; linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨l * 2,Scan.short01 hJ,by dsimp [z1e,z1g]; linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨1 + l * 2,Scan.short10 hJ,by dsimp [z1e,z1g]; linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨l * 2,Scan.short11 hJ,by dsimp [z1e,z1g]; linarith⟩
lemma e_z1Q {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b z : Rat}
    (hI : zPS k u k' v a b) (hT : zTd u z) :
    a - b - z1g v <= 3 * (1 + 2 * z) := by
  rcases z1w hT with ⟨A,H,hD⟩
  rcases e_z1P hI hD with ⟨l,hJ,hL⟩
  rcases z1x hJ hT with ⟨hMv,hLv,_⟩
  linarith
lemma e_z1R (h : Nat) (u : zW) (B H : Nat) (ds : zW) (sigma : Rat)
    (hDig : zDg B H ds)
    (hUnit : sigma * ((2 ^ h : Nat) : Rat) = 1)
    (hHeight : z1h u * ((2 ^ H : Nat) : Rat) = ((2 ^ h : Nat) : Rat))
    (hPair : z0Y u = true)
    (hCut : z0Z u = true)
    (hNe : u ≠ [])
    (hZ : 7 <= z1f ds)
    (hPhi : 4 * sigma * z1e u + sigma * z1h u * z1f ds + 2 * sigma <= 1 / 256) :
    ∃ k v a b,
      zPS (4 * 2 ^ h) (u ++ ds ++ [K]) k v a b /\ 4 < k /\
      sigma * z1e v <= sigma * z1e u + (15 / 56) * (sigma * z1h u * z1f ds) /\
      sigma * (a - b - z1g v) <= 3 * sigma * z1e u + (45 / 56) * (sigma * z1h u * z1f ds) := by
  have hPh : (0 : Rat) < ((2 ^ h : Nat) : Rat) := by exact_mod_cast zPp h
  have hPH : (0 : Rat) < ((2 ^ H : Nat) : Rat) := by exact_mod_cast zPp H
  have hS : 0 < sigma := by nlinarith
  have hSu := zSp u
  have hMu := zWn u
  have hMd := zWn ds
  have hDpos : 0 <= sigma * z1h u * z1f ds := by positivity
  have hSmall : 4 * sigma * z1e u + 2 * sigma <= 1 / 256 := by linarith
  have hDefSmall : sigma * z1h u * z1f ds <= 1 / 256 := by nlinarith
  have hBound : 8 * z1e u < (((2 * 2 ^ h) * 2 : Nat) : Rat) - 4 := by
    have hc : (((2 * 2 ^ h) * 2 : Nat) : Rat) = 4 * ((2 ^ h : Nat) : Rat) := by push_cast; ring
    rw [hc]; nlinarith
  rcases z1R u (2 * 2 ^ h) hBound with ⟨m,x,a1,b1,hI0,_⟩
  have hI : zPS (4 * 2 ^ h) u m x a1 b1 := by
    have heq : (2 * 2 ^ h) * 2 = 4 * 2 ^ h := by ring
    rwa [heq] at hI0
  rcases z1X hI hCut hNe with ⟨n,rfl⟩
  have hGain := e_z1N hI hPair
  have hBudget := z1N hI
  have hBounds := z1O hI
  have hSx := zSp x
  let s := sigma * z1h x
  have hSp : 0 < s := by positivity
  have hUnitTail : sigma * z1h u * ((2 ^ H : Nat) : Rat) = 1 := by
    calc sigma * z1h u * ((2 ^ H : Nat) : Rat)
      _ = sigma * (z1h u * ((2 ^ H : Nat) : Rat)) := by ring
      _ = sigma * ((2 ^ h : Nat) : Rat) := by rw [hHeight]
      _ = 1 := hUnit
  have hGs : 8 * s <= sigma * z1h u := by
    change 8 * (sigma * z1h x) <= sigma * z1h u
    nlinarith
  have hHt : s * ((2 ^ H : Nat) : Rat) <= 1 / 8 := by
    have h1 : 8 * s * ((2 ^ H : Nat) : Rat) <= sigma * z1h u * ((2 ^ H : Nat) : Rat) := by nlinarith
    linarith
  have hF : s * (1 + 2 * z1f ds) <= (15 / 56) * (sigma * z1h u * z1f ds) := by
    have h1 : 7 * s <= s * z1f ds := by nlinarith
    have h2 : 8 * s * z1f ds <= sigma * z1h u * z1f ds := by nlinarith
    linarith
  have hBudget' : (((n * 2 : Nat) : Rat) - 4) * s = 4 - 4 * sigma - 2 * sigma * (a1 - b1) := by
    change (((n * 2 : Nat) : Rat) - 4) * (sigma * z1h x) = 4 - 4 * sigma - 2 * sigma * (a1 - b1)
    have hc : ((4 * 2 ^ h : Nat) : Rat) = 4 * ((2 ^ h : Nat) : Rat) := by push_cast; ring
    rw [hc] at hBudget
    nlinarith
  have hCarry : 3 < (((n * 2 : Nat) : Rat) - 4) * s := by
    nlinarith
  rcases zDw hDig with ⟨hSd,hMassD,_⟩
  have hTail : 2 * (z1e (ds ++ [K]) + z1f (ds ++ [K])) * s < 3 := by
    rw [z1j,z1k]
    dsimp [z1e,z1f]
    have h1 : s * z1h ds <= 1 / 8 := by rwa [hSd]
    have h2 : s * z1e ds <= 1 / 8 := by nlinarith
    have h3 : s * z1f ds <= 1 / 256 := by nlinarith
    linarith
  have hTail1 : 2 * (z1e (ds ++ [K]) + z1f (ds ++ [K])) < ((n * 2 : Nat) : Rat) := by
    nlinarith
  have hTail2 : 8 * (1 + 2 * z1f ds) < ((n * 2 : Nat) : Rat) - 4 := by
    nlinarith
  rcases z1W (ds ++ [K]) (z1f ds) n (z1v hDig) hTail1 hTail2
    with ⟨k,y,a2,b2,hJ,hK⟩
  rcases z1P hI hJ with ⟨a,b,hIJ,hA,hB⟩
  have hIJ' : zPS (4 * 2 ^ h) (u ++ ds ++ [K]) k (x ++ y) a b := by
    simpa [List.append_assoc] using! hIJ
  have hTB := z1U hJ (z1v hDig)
  have hE1 := e_z1O hI
  have hE2 := e_z1Q hJ (z1v hDig)
  refine ⟨k,x ++ y,a,b,hIJ',hK,?_,?_⟩
  · rw [z1j]
    have h1 : sigma * (z1h x * z1e y) = s * z1e y := by ring
    have h2 : s * z1e y <= s * (1 + 2 * z1f ds) := by nlinarith
    nlinarith
  · rw [z1l,hA,hB]
    have h1 : sigma * (a - b - z1g (x ++ y)) = sigma * (a1 - b1 - z1g x) + s * (a2 - b2 - z1g y) := by
      rw [z1l,hA,hB]; change _ = _ + (sigma * z1h x) * _; ring
    have h2 : s * (a2 - b2 - z1g y) <= 3 * s * (1 + 2 * z1f ds) := by nlinarith
    nlinarith
def e_zHn : zW -> Nat -> Option Nat
  | [],h => some h
  | V :: u,h => e_zHn u (h + 1)
  | _ :: u,0 => none
  | _ :: u,h + 1 => e_zHn u h
lemma e_z1S (u : zW) :
    ∀ (h H : Nat),e_zHn u h = some H ->
      z1h u * ((2 ^ H : Nat) : Rat) = ((2 ^ h : Nat) : Rat) := by
  induction u with
  | nil =>
    intro h H hE
    injection hE with hE; subst hE
    simp [z1h]
  | cons w u ih =>
    intro h H hE
    cases w with
    | V =>
      dsimp [e_zHn,z1h] at hE ⊢
      have hIH := ih (h + 1) H hE
      rw [Nat.pow_succ] at hIH
      push_cast at hIH ⊢; linarith
    | K =>
      cases h with
      | zero => contradiction
      | succ h =>
        dsimp [e_zHn,z1h] at hE ⊢
        have hIH := ih h H hE
        rw [Nat.pow_succ]
        push_cast at hIH ⊢; linarith
    | Q =>
      cases h with
      | zero => contradiction
      | succ h =>
        dsimp [e_zHn,z1h] at hE ⊢
        have hIH := ih h H hE
        rw [Nat.pow_succ]
        push_cast at hIH ⊢; linarith
lemma e_z1T (u : zW) :
    ∀ (v : zW) (h H : Nat),e_zHn (u ++ v) h = some H ->
      ∃ j,e_zHn u h = some j /\ e_zHn v j = some H := by
  induction u with
  | nil =>
    intro v h H hE
    exact ⟨h,rfl,hE⟩
  | cons w u ih =>
    intro v h H hE
    cases w with
    | V => exact ih v (h + 1) H hE
    | K =>
      cases h with
      | zero => contradiction
      | succ h => exact ih v h H hE
    | Q =>
      cases h with
      | zero => contradiction
      | succ h => exact ih v h H hE
lemma e_z1U (n : Nat) :
    ∀ (h : Nat),e_zHn (zR n V) h = some (h + n) := by
  induction n with
  | zero => intro h; simp [e_zHn]
  | succ n ih =>
    intro h
    dsimp [List.replicate,e_zHn]
    rw [ih (h + 1)]
    congr 1; omega
lemma e_z1V (u : zW) (n h H : Nat)
    (hE : e_zHn (u ++ zR n V) h = some H) : n <= H := by
  rcases e_z1T u (zR n V) h H hE with ⟨j,_,hJ⟩
  rw [e_z1U] at hJ
  injection hJ with hJ
  (try omega)
lemma e_z1W (u : zW) :
    ∀ (h : Nat),z1e u < ((2 ^ h : Nat) : Rat) -> ∃ H,e_zHn u h = some H := by
  induction u with
  | nil => intro h _; exact ⟨h,rfl⟩
  | cons w u ih =>
    intro h hM
    cases w with
    | V =>
      dsimp [z1e,e_zHn] at hM ⊢
      apply ih (h + 1)
      rw [Nat.pow_succ]; push_cast at hM ⊢; linarith
    | K =>
      cases h with
      | zero =>
        have hw := (zWn u).1
        dsimp [z1e] at hM; push_cast at hM; linarith
      | succ h =>
        dsimp [z1e,e_zHn] at hM ⊢
        apply ih h
        rw [Nat.pow_succ] at hM; push_cast at hM ⊢; linarith
    | Q =>
      cases h with
      | zero =>
        have hw := (zWn u).1
        dsimp [z1e] at hM; push_cast at hM; linarith
      | succ h =>
        dsimp [z1e,e_zHn] at hM ⊢
        apply ih h
        rw [Nat.pow_succ] at hM; push_cast at hM ⊢; linarith
lemma e_z1X (u : zW) :
    ∀ (h H : Nat),e_zHn u h = some H -> e_zHn u (h + 1) = some (H + 1) := by
  induction u with
  | nil =>
    intro h H hE
    injection hE with hE; subst hE; rfl
  | cons w u ih =>
    intro h H hE
    cases w with
    | V => exact ih (h + 1) H hE
    | K =>
      cases h with
      | zero => contradiction
      | succ h => exact ih h H hE
    | Q =>
      cases h with
      | zero => contradiction
      | succ h => exact ih h H hE
lemma e_z1Y {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k u k' v a b) :
    ∀ (h H n n' : Nat) (eff : zW),
      e_zHn v h = some H -> zEf n v n' eff ->
      k + n * 2 + 3 <= 4 * 2 ^ h -> k' + n' * 2 + 3 <= 4 * 2 ^ H := by
  induction hI with
  | nil k =>
    intro h H n n' eff hHeight hEff hBound
    injection hHeight with hEq; subst hEq
    cases hEff
    exact hBound
  | T _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases hEff with
    | T hSub =>
      apply ih (h + 1) H (1 + n * 2) n' _ hHeight hSub
      rw [Nat.pow_succ]; omega
  | pair0 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases hEff with
    | T hSub =>
      apply ih (h + 1) H (1 + n * 2) n' _ hHeight hSub
      rw [Nat.pow_succ]; omega
  | pair1 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases hEff with
    | T hSub =>
      apply ih (h + 1) H (1 + n * 2) n' _ hHeight hSub
      rw [Nat.pow_succ]; omega
  | short00 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases h with
    | zero => contradiction
    | succ h =>
      rw [Nat.pow_succ] at hBound
      cases hEff with
      | d00 hSub => apply ih h H _ n' _ hHeight hSub; omega
      | d01 hSub => apply ih h H _ n' _ hHeight hSub; omega
  | short01 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases h with
    | zero => contradiction
    | succ h =>
      rw [Nat.pow_succ] at hBound
      cases hEff with
      | d00 hSub => apply ih h H _ n' _ hHeight hSub; omega
      | d01 hSub => apply ih h H _ n' _ hHeight hSub; omega
  | short10 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases h with
    | zero => contradiction
    | succ h =>
      rw [Nat.pow_succ] at hBound
      cases hEff with
      | d10 hSub => apply ih h H _ n' _ hHeight hSub; omega
      | d11 hSub => apply ih h H _ n' _ hHeight hSub; omega
  | short11 _ ih =>
    intro h H n n' eff hHeight hEff hBound
    cases h with
    | zero => contradiction
    | succ h =>
      rw [Nat.pow_succ] at hBound
      cases hEff with
      | d10 hSub => apply ih h H _ n' _ hHeight hSub; omega
      | d11 hSub => apply ih h H _ n' _ hHeight hSub; omega
lemma e_z1Z (n : Nat) :
    zEf 1 (zR n Q ++ [V]) 3 (zR n K ++ [V]) := by
  induction n with
  | zero => exact zEf.T (zEf.nil 3)
  | succ n ih => exact @zEf.d11 0 _ _ _ ih
lemma e_z20 (n : Nat) :
    ∀ (h k k' : Nat) (v : zW) (a b : Rat),
      zPS k (zR n K ++ [V]) k' v a b ->
      k + 4 = 4 * 2 ^ h ->
      ∃ H,v = zR n Q ++ [V] /\ e_zHn v h = some H /\ k' + 12 = 4 * 2 ^ H := by
  induction n with
  | zero =>
    intro h k k' v a b hI hEq
    generalize hk : k = k0 at hI
    cases hI with
    | @T m _ _ v0 a0 b0 hSub =>
      generalize hkSub : 2 + m * 2 = kSub at hSub
      cases hSub
      refine ⟨h + 1,rfl,rfl,?_⟩
      rw [Nat.pow_succ]; omega
  | succ n ih =>
    intro h k k' v a b hI hEq
    have hpos := zPp h
    cases h with
    | zero =>
      dsimp at hEq
      cases hI <;> omega
    | succ h =>
      rw [Nat.pow_succ] at hEq
      cases hI with
      | short00 _ => omega
      | @short10 m _ _ v0 a0 b0 hSub =>
        rcases ih h (m * 2) k' v0 a0 b0 hSub (by omega) with ⟨H,rfl,hHt,hK⟩
        exact ⟨H,rfl,hHt,hK⟩
inductive EGuard : zW -> Prop where
  | T (n : Nat) (w : zW) : EGuard (V :: (zR n Q ++ V :: w))
  | D (w : zW) : EGuard (Q :: V :: w)
lemma e_z21 {u v : zW} (hG : EGuard u) : EGuard (u ++ v) := by
  cases hG with
  | T n w =>
    have heq : (V :: (zR n Q ++ V :: w)) ++ v =
        V :: (zR n Q ++ V :: (w ++ v)) := by
      simp [List.append_assoc]
    rw [heq]; exact EGuard.T n (w ++ v)
  | D w =>
    exact EGuard.D (w ++ v)
lemma e_z22 (h : Nat) (orig eff : zW) (carry k : Nat) (v : zW) (a b : Rat)
    (hG : EGuard orig) (hE : zEf 0 orig carry eff)
    (hI : zPS (4 * 2 ^ h) eff k v a b) (hPos : 0 < k) :
    ∃ pre rest j m x a' b' c H,
      v = pre ++ rest /\ EGuard (pre ++ rest) /\
      e_zHn pre h = some H /\ zEf 0 pre c x /\
      zPS j m k rest a' b' /\ j + c * 2 + 3 <= 4 * 2 ^ H := by
  cases hG with
  | T n w =>
    have hEq : V :: (zR n Q ++ V :: w) =
        (V :: (zR n Q ++ [V])) ++ w := by
      simp [List.append_assoc]
    rw [hEq] at hE
    rcases z1E (V :: (zR n Q ++ [V])) hE
      with ⟨c,pre,tail,rfl,hEP,hET⟩
    have hEG : zEf 0 (V :: (zR n Q ++ [V])) 3 (V :: (zR n K ++ [V])) :=
      zEf.T (e_z1Z n)
    rcases z1C hEP hEG with ⟨rfl,rfl⟩
    have hCut : z10 (V :: (zR n K ++ [V])) tail := by
      left
      have heq_cut : (V :: (zR n K ++ [V])) = (V :: zR n K) ++ [V] := by
        simp [List.append_assoc]
      rw [heq_cut,z11]; rfl
    rcases z1Y hI (V :: (zR n K ++ [V])) tail rfl hCut
      with ⟨j,x,y,a1,b1,a2,b2,hSX,hSY,rfl,_,_⟩
    generalize hkSX : 4 * 2 ^ h = kSX at hSX
    cases hSX with
    | @T m _ _ v0 a0 b0 hJ =>
      have hEq_m : (2 + m * 2) + 4 = 4 * 2 ^ (h + 1) := by
        rw [Nat.pow_succ]; omega
      rcases e_z20 n (h + 1) (2 + m * 2) j v0 a0 b0 hJ hEq_m
        with ⟨hh,rfl,hHt,hK⟩
      refine ⟨V :: (zR n Q ++ [V]),y,j,tail,V :: (zR n K ++ [V]),a2,b2,3,hh,rfl,?_,hHt,hEG,hSY,by omega⟩
      have heq_g : (V :: (zR n Q ++ [V])) ++ y = V :: (zR n Q ++ V :: y) := by
        simp [List.append_assoc]
      rw [heq_g]; exact EGuard.T n y
  | D w =>
    generalize hk0 : (0 : Nat) = k0 at hE
    cases hE with
    | @d10 m _ _ _ hE1 =>
      have hm0 : m = 0 := by omega
      subst hm0
      generalize hk1 : (0 : Nat) = k1 at hE1
      cases hE1 with
      | T hE2 =>
        subst hk1
        have hpos_h := zPp h
        cases h with
        | zero =>
          dsimp at hI
          generalize hkI : (4 : Nat) = kI at hI
          cases hI with
          | @short01 m' _ _ _ _ _ _ => omega
          | @short11 m' _ _ _ _ _ hSub =>
            have hm'0 : m' = 0 := by omega
            subst hm'0
            dsimp at hSub
            generalize hkS : (1 : Nat) = kS at hSub
            cases hSub with
            | T _ => omega
        | succ h =>
          have hpow : 4 * 2 ^ (h + 1) = 4 + (2 * 2 ^ h - 1) * 4 := by
            have hp := zPp h
            rw [Nat.pow_succ]; omega
          rw [hpow] at hI
          generalize hkI : 4 + (2 * 2 ^ h - 1) * 4 = kI at hI
          cases hI with
          | @short01 m' _ _ _ _ _ _ => omega
          | @short11 m' _ _ _ _ _ hSub =>
            have hm' : m' = 2 * 2 ^ h - 1 := by omega
            subst hm'
            have h1 : 1 + (2 * 2 ^ h - 1) * 2 = 3 + (4 * 2 ^ h - 4) := by
              have hp := zPp h; omega
            rw [h1] at hSub
            generalize hkS : 3 + (4 * 2 ^ h - 4) = kS at hSub
            cases hSub with
            | @T m'' _ _ v0 a0 b0 hSub2 =>
              have hm'' : m'' = 4 * 2 ^ h - 4 := by omega
              subst hm''
              refine ⟨[Q,V],v0,2 + (4 * 2 ^ h - 4) * 2,_,[Q,V],a0,b0,1,h + 1,rfl,EGuard.D v0,rfl,?_,hSub2,?_⟩
              · exact zEf.d10 (zEf.T (zEf.nil 1))
              · have hp := zPp h
                rw [Nat.pow_succ]; omega
    | d11 _ => omega
lemma e_z23 {h : Nat} {orig eff : zW} {carry k : Nat} {v : zW} {a b : Rat}
    {H n : Nat} {out : zW}
    (hG : EGuard orig) (hE : zEf 0 orig carry eff)
    (hI : zPS (4 * 2 ^ h) eff k v a b) (hPos : 0 < k)
    (hHeight : e_zHn v h = some H) (hEff : zEf 0 v n out) :
    EGuard v /\ k + n * 2 + 3 <= 4 * 2 ^ H := by
  rcases e_z22 h orig eff carry k v a b hG hE hI hPos
    with ⟨pre,rest,j,m,x,a',b',c,H',rfl,hG',hHt,hEp,hJ,hBound⟩
  rcases e_z1T pre rest h H hHeight with ⟨hh,hHp,hHr⟩
  rw [hHt] at hHp
  injection hHp with hEq; subst hEq
  rcases z1E pre hEff with ⟨c',pre',out',_,hEp',hEr⟩
  rcases z1C hEp hEp' with ⟨rfl,_⟩
  exact ⟨hG',e_z1Y hJ H' H c n out' hHr hEr hBound⟩
lemma e_z24 (s : Nat) :
    ∀ (B H : Nat) (ds : zW),
      zDg B H ds -> s <= H -> (∃ n,B = n * 2 ^ s) ->
      ∃ rest,ds = zR s K ++ rest := by
  induction s with
  | zero =>
    intro B H ds _ _ _
    exact ⟨ds,rfl⟩
  | succ s ih =>
    intro B H ds hD hSH ⟨n,hN⟩
    have hN2 : B = (n * 2 ^ s) * 2 := by
      rw [Nat.pow_succ] at hN
      linarith
    cases hD with
    | nil => omega
    | @zero A' H' u' hSub =>
      rcases ih A' H' u' hSub (by omega) ⟨n,by omega⟩ with ⟨rest,rfl⟩
      exact ⟨rest,rfl⟩
    | one _ => omega
lemma e_z25 {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k (K :: K :: K :: u) k' v a b)
    (hN : ∃ n,k + 12 = n * 16) :
    ∃ w,v = Q :: Q :: K :: w := by
  rcases hN with ⟨n,hEq⟩
  generalize hk0 : k = k0 at hI
  cases hI with
  | short00 _ => omega
  | @short10 m1 _ _ _ _ _ hI1 =>
    generalize hk1 : m1 * 2 = k1 at hI1
    cases hI1 with
    | short00 _ => omega
    | @short10 m2 _ _ _ _ _ hI2 =>
      generalize hk2 : m2 * 2 = k2 at hI2
      cases hI2 with
      | @short00 m3 _ _ w0 _ _ _ => exact ⟨w0,rfl⟩
      | short10 _ => omega
lemma e_z26 {k : Nat} {u rest : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k ((u ++ zR 4 V) ++ K :: K :: K :: rest) k' v a b) :
    ∃ x y,v = (x ++ zR 4 V) ++ Q :: Q :: K :: y := by
  have hE1 : (u ++ zR 4 V) ++ K :: K :: K :: rest =
      u ++ (zR 4 V ++ K :: K :: K :: rest) := by
    simp [List.append_assoc]
  rw [hE1] at hI
  rcases z1Y hI u (zR 4 V ++ K :: K :: K :: rest) rfl (Or.inr ⟨_,rfl⟩)
    with ⟨m,x,y,_,_,_,_,_,hB,rfl,_,_⟩
  rcases z1Y hB (zR 4 V) (K :: K :: K :: rest) rfl (Or.inl (z12 4))
    with ⟨j,x',y',_,_,_,_,hC,hD,rfl,_,_⟩
  rcases z20 4 m j x' _ _ hC with ⟨rfl,hN,_,_⟩
  have hMod : ∃ q,j + 12 = q * 16 := ⟨m - 3,by omega⟩
  rcases e_z25 hD hMod with ⟨w,rfl⟩
  exact ⟨x,w,by simp [List.append_assoc]⟩
lemma e_z27 (u v : zW) (h : z0Y v = true) : z0Y (u ++ v) = true := by
  induction u with
  | nil => exact h
  | cons w u ih =>
    cases w with
    | V => exact ih
    | K => exact ih
    | Q =>
      cases u with
      | nil =>
        cases v with
        | nil => contradiction
        | cons w2 v' => cases w2 <;> simp [z0Y] at h ⊢ <;> exact h
      | cons w2 u' =>
        cases w2 with
        | V => exact ih
        | K => rfl
        | Q => exact ih
lemma e_z28 {u rest : zW} {n : Nat} {eff : zW}
    (hE : zEf 0 ((u ++ zR 4 V) ++ Q :: Q :: K :: rest) n eff) :
    z0Y eff = true := by
  rcases z1E (u ++ zR 4 V) hE with ⟨c,x,y,rfl,hA,hB⟩
  rcases z1L u 4 0 c x hA with ⟨z,m,_,hC⟩
  have h4 : (2 : Nat) ^ 4 = 16 := rfl
  rw [h4] at hC
  generalize hk0 : c = k0 at hB
  cases hB with
  | d10 _ => omega
  | @d11 c1 _ _ _ hB1 =>
    generalize hk1 : 1 + c1 = k1 at hB1
    cases hB1 with
    | @d10 c2 _ _ _ hB2 =>
      generalize hk2 : c2 = k2 at hB2
      cases hB2 with
      | @d00 c3 _ _ w0 _ =>
        exact e_z27 x (K :: Q :: K :: w0) rfl
      | d01 _ => omega
    | d11 _ => omega
lemma e_z29 (h : Nat) (u : zW) (n : Nat) (v : zW) (a b : Rat) (c : Nat) (eff : zW) (sigma : Rat)
    (hI : zPS (4 * 2 ^ h) u (n * 2) v a b)
    (hE : zEf 0 v c eff)
    (hS : 0 < sigma)
    (hUnit : sigma * ((2 ^ h : Nat) : Rat) = 1) :
    1 - ((n + c + 2 : Nat) : Rat) * (sigma * z1h v * (1 / 2)) <=
      (sigma + sigma * (a - b - z1g v)) * (1 / 2) - 3 * (sigma * z1h v * (1 / 2)) := by
  have hBudget := z1N hI
  have hCarry := z1J hE
  have hMass := (z1I hE).2
  have hSplit := z1i eff
  have hWeff := zWn eff
  have hO : z1g eff <= z1e v := by linarith
  have hSv := zSp v
  have hc4 : ((4 * 2 ^ h : Nat) : Rat) = 4 * ((2 ^ h : Nat) : Rat) := by push_cast; ring
  have hn2 : ((n * 2 : Nat) : Rat) = 2 * (n : Rat) := by push_cast; ring
  have hc1 : ((1 + c : Nat) : Rat) = 1 + (c : Rat) := by push_cast; ring
  have hc0 : ((1 + 0 : Nat) : Rat) = 1 := rfl
  have hnc : ((n + c + 2 : Nat) : Rat) = (n : Rat) + (c : Rat) + 2 := by push_cast; ring
  rw [hc4,hn2] at hBudget
  rw [hc1,hc0] at hCarry
  rw [hnc]
  have hB0 : (4 * ((2 ^ h : Nat) : Rat) - 4) - ((2 * (n : Rat) - 4) * z1h v + 2 * (a - b)) = 0 := by linarith
  have hC0 : (1 + (c : Rat)) * z1h v - (1 + z1e v + z1g v - z1g eff) = 0 := by linarith
  have hU0 : sigma * ((2 ^ h : Nat) : Rat) - 1 = 0 := by linarith
  have h_id :
    (sigma + sigma * (a - b - z1g v)) * (1 / 2) - 3 * (sigma * z1h v * (1 / 2)) -
      (1 - ((n : Rat) + (c : Rat) + 2) * (sigma * z1h v * (1 / 2))) =
    (sigma * ((2 ^ h : Nat) : Rat) - 1) -
      (1 / 4) * sigma * ((4 * ((2 ^ h : Nat) : Rat) - 4) - ((2 * (n : Rat) - 4) * z1h v + 2 * (a - b))) +
      (1 / 2) * sigma * ((1 + (c : Rat)) * z1h v - (1 + z1e v + z1g v - z1g eff)) +
      (1 / 2) * sigma * (z1e v - z1g eff) := by ring
  rw [hU0,hB0,hC0] at h_id
  have h_nonneg : 0 <= (1 / 2) * sigma * (z1e v - z1g eff) := by nlinarith
  linarith
lemma e_z2a (M D sigma M' D' : Rat)
    (_ : 0 <= M) (_ : 0 <= sigma)
    (hM' : M' <= (M + (15 / 56) * D) * (1 / 2))
    (hD' : D' <= (sigma + 3 * M + (45 / 56) * D) * (1 / 2)) :
    4 * M' + D' + sigma <= (15 / 16) * (4 * M + D + 2 * sigma) := by
  linarith
lemma e_z2b (n t0 B : Nat) (ds : zW)
    (hD : zDg B (n + t0) ds) (hL : 2 ^ (n + t0) <= B + 2 ^ n) :
    ∃ u,ds = u ++ zR t0 Q := by
  have hBound := z1b hD
  have hPos := zPp t0
  rw [Nat.pow_add] at hL hBound
  let a := B - (2 ^ t0 - 1) * 2 ^ n
  have hSum : a + (2 ^ t0 - 1) * 2 ^ n = B := by
    have : (2 ^ t0 - 1) * 2 ^ n + 2 ^ n = 2 ^ n * 2 ^ t0 := by
      have h1 : (2 ^ t0 - 1) + 1 = 2 ^ t0 := by omega
      calc (2 ^ t0 - 1) * 2 ^ n + 2 ^ n
        _ = ((2 ^ t0 - 1) + 1) * 2 ^ n := by ring
        _ = 2 ^ t0 * 2 ^ n := by rw [h1]
        _ = 2 ^ n * 2 ^ t0 := by ring
    (try omega)
  have ha_lt : a < 2 ^ n := by
    have : (2 ^ t0 - 1) * 2 ^ n + 2 ^ n = 2 ^ n * 2 ^ t0 := by
      have h1 : (2 ^ t0 - 1) + 1 = 2 ^ t0 := by omega
      calc (2 ^ t0 - 1) * 2 ^ n + 2 ^ n
        _ = ((2 ^ t0 - 1) + 1) * 2 ^ n := by ring
        _ = 2 ^ t0 * 2 ^ n := by rw [h1]
        _ = 2 ^ n * 2 ^ t0 := by ring
    (try omega)
  rcases z18 n a ha_lt with ⟨u,hU⟩
  refine ⟨u,z1d hD ?_⟩
  rw [<- hSum]
  exact z19 hU (z1a t0)
lemma e_z2c {B H : Nat} {ds : zW} {unit : Rat}
    (hD : zDg B H ds) (hU : 0 < unit)
    (hHeight : unit * ((2 ^ H : Nat) : Rat) = 1)
    (hZ : 7 <= z1f ds)
    (hSmall : unit * z1f ds <= 1 / 256) :
    ∃ rest,ds = rest ++ zR 7 Q := by
  have hH7 : 7 <= H := by
    by_contra hlt
    have hle : H <= 6 := by omega
    have hpow_le : 2 ^ H <= 64 := by
      calc 2 ^ H <= 2 ^ 6 := Nat.pow_le_pow_right (by decide) hle
      _ = 64 := by decide
    have hpow_q : ((2 ^ H : Nat) : Rat) <= 64 := by exact_mod_cast hpow_le
    nlinarith
  have hShift : unit * ((2 ^ (H - 7) : Nat) : Rat) = 1 / 128 := by
    have heq : H = (H - 7) + 7 := by omega
    have hpow : ((2 ^ H : Nat) : Rat) = ((2 ^ (H - 7) : Nat) : Rat) * 128 := by
      have hp : 2 ^ H = 2 ^ (H - 7) * 128 := by rw [heq,Nat.pow_add]; rfl
      rw [hp]; push_cast; ring
    rw [hpow] at hHeight
    linarith
  have hEq := z1n hD
  have hH_split : (H - 7) + 7 = H := by omega
  have hD' : zDg B ((H - 7) + 7) ds := by rwa [hH_split]
  apply e_z2b (H - 7) 7 B ds hD'
  have hL_q : ((2 ^ ((H - 7) + 7) : Nat) : Rat) <= ((B + 2 ^ (H - 7) : Nat) : Rat) := by
    rw [hH_split]
    push_cast at hEq hShift ⊢
    nlinarith
  exact_mod_cast hL_q
inductive EGood : Nat -> zW -> Prop where
  | intro (h H : Nat) (u : zW) (A : Nat) (da : zW) (carry : Nat) (eff : zW)
      (B : Nat) (db : zW) (sigma : Rat) :
      e_zHn u h = some H ->
      EGuard u ->
      (∃ w,u = w ++ zR 4 V) ->
      zDg A H da ->
      zEf 0 u carry eff ->
      A + carry = B ->
      zDg B H db ->
      z0Y eff = true ->
      (∃ w,db = K :: K :: K :: w) ->
      (∃ w,db = w ++ zR 7 Q) ->
      sigma * ((2 ^ h : Nat) : Rat) = 1 ->
      4 * sigma * z1e u + sigma * z1h u * z1f db + 2 * sigma <= 1 / 256 ->
      EGood h (u ++ da)
inductive EStep : Nat -> zW -> zW -> Prop where
  | intro (h : Nat) (orig eff : zW) (n : Nat) (v : zW) (a b : Rat) (J : Nat) (da : zW) :
      zEf 0 (orig ++ [K]) 0 eff ->
      zPS (4 * 2 ^ h) eff (n * 2) v a b ->
      0 < n ->
      zDg (1 + n) J da ->
      EStep h orig (v ++ da)
lemma e_z2d {h : Nat} {orig : zW} (hG : EGood h orig) :
    ∃ out,EStep h orig out /\ EGood (h + 1) out := by
  rcases hG with ⟨H,u,A,da,carry,eff,B,db,sigma,
    hHeight,hGuardU,hEnd,hDA,hE,hSum,hDB,hPair,hLow,hHigh,hUnit,hPhi⟩
  have hHt := e_z1S u h H hHeight
  rcases z1I hE with ⟨hSe,hMe⟩
  have hPh : (0 : Rat) < ((2 ^ h : Nat) : Rat) := by exact_mod_cast zPp h
  have hSig : 0 < sigma := by nlinarith
  have hWu := zWn u
  have hWdb := zWn db
  have hSu := zSp u
  have hDpos : 0 <= sigma * z1h u * z1f db :=
    mul_nonneg (mul_nonneg (le_of_lt hSig) (le_of_lt hSu)) hWdb.2.1
  have hMu : 0 <= sigma * z1e u :=
    mul_nonneg (le_of_lt hSig) hWu.1
  have hZ : 7 <= z1f db := by
    rcases hLow with ⟨w,rfl⟩
    have hw := zWn w
    dsimp [z1f]; linarith
  have hEe : ∃ p,eff = p ++ zR 4 V := by
    rcases hEnd with ⟨p,rfl⟩
    rcases z1L p 4 0 carry eff hE with ⟨w,q,hV,_⟩
    exact ⟨w,hV⟩
  have hCut : z0Z eff = true := by
    rcases hEe with ⟨p,rfl⟩
    have heq : p ++ zR 4 V = (p ++ [V,V,V]) ++ [V] := by
      simp [List.append_assoc]
    rw [heq,z11]; rfl
  have hNe : eff ≠ [] := by
    rcases hEe with ⟨p,rfl⟩
    simp
  have hHt_eff : z1h eff * ((2 ^ H : Nat) : Rat) = ((2 ^ h : Nat) : Rat) := by rwa [hSe]
  have hPhi_eff : 4 * sigma * z1e eff + sigma * z1h eff * z1f db + 2 * sigma <= 1 / 256 := by
    rwa [hSe,hMe]
  rcases e_z1R h eff B H db sigma hDB hUnit hHt_eff hPair hCut hNe hZ hPhi_eff
    with ⟨k,v,a,b,hI,hPos,hMass,hEnergy⟩
  rw [hSe,hMe] at hMass hEnergy
  rcases hHigh with ⟨hi,hHi⟩
  have hIH : zPS (4 * 2 ^ h) ((eff ++ hi) ++ zR (1 + 3 * 2) Q ++ [K]) k v a b := by
    have h7 : zR 7 Q = zR (1 + 3 * 2) Q := rfl
    rw [hHi,h7] at hI
    simpa [List.append_assoc] using! hI
  rcases z1Z 3 (4 * 2 ^ h) (eff ++ hi) k v a b hIH with ⟨p,n,hV,rfl⟩
  have h16 : 2 ^ (1 + 3) = 16 := rfl
  rw [h16] at hI hPos
  have hI' : zPS (4 * 2 ^ h) (eff ++ db ++ [K]) ((n * 8) * 2) v a b := by
    have heq : (n * 8) * 2 = n * 16 := by ring
    rwa [heq]
  have hMv : sigma * z1e v <= 1 / 256 := by linarith
  have hMv_pow : z1e v < ((2 ^ h : Nat) : Rat) := by nlinarith
  rcases e_z1W v h hMv_pow with ⟨Hv,hHeightV⟩
  rcases z1B v 0 with ⟨carry',eff',hE'⟩
  rcases z1H hDA hSum (z1b hDB) with ⟨db0,hDB0,hED⟩
  have hdb_eq : db0 = db := z1d hDB0 hDB
  rw [hdb_eq] at hED
  have hFull : zEf 0 ((u ++ da) ++ [K]) 0 (eff ++ db ++ [K]) := by
    simpa only [List.append_assoc] using!
      z1D hE (z1D hED (zEf.d00 (zEf.nil 0)))
  have hGuardFull : EGuard ((u ++ da) ++ [K]) := e_z21 (e_z21 hGuardU)
  rcases e_z23 hGuardFull hFull hI (by omega) hHeightV hE' with ⟨hGuardV,hBarrier⟩
  let J := Hv + 1
  let A' := 1 + n * 8
  let B' := A' + carry'
  have hUpper : B' < 2 ^ J := by
    change 1 + n * 8 + carry' < 2 ^ (Hv + 1)
    rw [Nat.pow_succ]; omega
  rcases z18 J A' (by omega) with ⟨da',hDA'⟩
  rcases z18 J B' hUpper with ⟨db',hDB'⟩
  have hHeightNew : e_zHn v (h + 1) = some J := e_z1X v h Hv hHeightV
  let unit := sigma * z1h v * (1 / 2)
  have hUp : 0 < unit := by
    have hSv := zSp v
    positivity
  have hUH : unit * ((2 ^ J : Nat) : Rat) = 1 := by
    have hHV := e_z1S v (h + 1) J hHeightNew
    have hp : ((2 ^ (h + 1) : Nat) : Rat) = ((2 ^ h : Nat) : Rat) * 2 := by
      rw [Nat.pow_succ]; push_cast; ring
    rw [hp] at hHV
    change (sigma * z1h v * (1 / 2)) * ((2 ^ J : Nat) : Rat) = 1
    calc (sigma * z1h v * (1 / 2)) * ((2 ^ J : Nat) : Rat)
      _ = sigma * (z1h v * ((2 ^ J : Nat) : Rat)) * (1 / 2) := by ring
      _ = sigma * (((2 ^ h : Nat) : Rat) * 2) * (1 / 2) := by rw [hHV]
      _ = sigma * ((2 ^ h : Nat) : Rat) := by ring
      _ = 1 := hUnit
  have hDnew : unit * z1f db' <= (sigma + 3 * sigma * z1e u + (45 / 56) * (sigma * z1h u * z1f db)) * (1 / 2) := by
    have hDef := e_z29 h (eff ++ db ++ [K]) (n * 8) v a b carry' eff' sigma hI' hE' hSig hUnit
    have hZeros := z1n hDB'
    have hEq_cast : ((n * 8 + carry' + 2 : Nat) : Rat) = (B' : Rat) + 1 := by
      change ((n * 8 + carry' + 2 : Nat) : Rat) = ((1 + n * 8 + carry' : Nat) : Rat) + 1
      push_cast; ring
    rw [hEq_cast] at hDef
    change 1 - ((B' : Rat) + 1) * unit <= (sigma + sigma * (a - b - z1g v)) * (1 / 2) - 3 * unit at hDef
    nlinarith
  have hPhiNew : 4 * (sigma * (1 / 2)) * z1e v + (sigma * (1 / 2)) * z1h v * z1f db' + 2 * (sigma * (1 / 2)) <= 1 / 256 := by
    have hDnew' : unit * z1f db' <= (sigma + 3 * (sigma * z1e u) + (45 / 56) * (sigma * z1h u * z1f db)) * (1 / 2) := by
      linarith
    have hBound := e_z2a (sigma * z1e u) (sigma * z1h u * z1f db) sigma
      (sigma * z1e v * (1 / 2)) (unit * z1f db') hMu (by linarith) (by linarith) hDnew'
    dsimp [unit] at hBound
    linarith
  have hPairNew : z0Y eff' = true := by
    rcases hEe with ⟨ue,rfl⟩
    rcases hLow with ⟨lo,rfl⟩
    have hI_shape : zPS (4 * 2 ^ h) ((ue ++ zR 4 V) ++ K :: K :: K :: (lo ++ [K])) (n * 16) v a b := by
      simpa [List.append_assoc] using! hI
    rcases e_z26 hI_shape with ⟨x,y,hVy⟩
    rw [hVy] at hE'
    exact e_z28 hE'
  have hJ4 : 4 <= J := by
    have hHv3 : 4 <= Hv := by
      apply e_z1V p 4 h Hv
      rw [<- hV]; exact hHeightV
    (try omega)
  have hLowNew : ∃ w,db' = K :: K :: K :: w := by
    have hE'_v : zEf 0 (p ++ zR 4 V) carry' eff' := by rwa [<- hV]
    rcases z1L p 4 0 carry' eff' hE'_v with ⟨w,m,_,hCm⟩
    have h4 : (2 : Nat) ^ 4 = 16 := rfl
    rw [h4] at hCm
    have hDiv8 : ∃ q,B' = q * 2 ^ 3 := ⟨n + m * 2,by change 1 + n * 8 + carry' = (n + m * 2) * 8; omega⟩
    rcases e_z24 3 B' J db' hDB' (by omega) hDiv8 with ⟨rest,hRest⟩
    exact ⟨rest,hRest⟩
  have hHighNew : ∃ w,db' = w ++ zR 7 Q := by
    refine e_z2c hDB' hUp hUH ?_ ?_
    · rcases hLowNew with ⟨w,rfl⟩
      have hw := zWn w
      dsimp [z1f]; linarith
    · have hWv := zWn v
      have hSuv : 0 <= (sigma * (1 / 2)) * z1e v := mul_nonneg (by linarith) hWv.1
      dsimp [unit]
      linarith
  refine ⟨v ++ da',?_,?_⟩
  · exact EStep.intro h (u ++ da) (eff ++ db ++ [K]) (n * 8) v a b J da' hFull hI' (by omega) hDA'
  · refine EGood.intro (h + 1) J v A' da' carry' eff' B' db' (sigma * (1 / 2))
      hHeightNew hGuardV ⟨p,hV⟩ hDA' hE' rfl hDB' hPairNew hLowNew hHighNew ?_ hPhiNew
    have hUnit' := hUnit
    rw [Nat.pow_succ]; push_cast at hUnit' ⊢; linarith
def e_zPf : Nat -> Nat -> Option (zW)
  | 0,_ => none
  | _ + 1,0 => none
  | _ + 1,1 => some [Q]
  | fuel + 1,m + 2 =>
    forceNat ((m + 2) / 2) (fun q =>
      match e_zPf fuel q with
      | none => none
      | some ws => forceWord (if (m + 2) % 2 == 0 then K else Q) (fun w => some (w :: ws)))
lemma e_z2e (fuel : Nat) :
    ∀ (m : Nat) (ws : zW),e_zPf fuel m = some ws ->
      ∃ H,zDg m H ws := by
  induction fuel with
  | zero => intro m ws h; contradiction
  | succ fuel ih =>
    intro m ws h
    rcases m with _ | _ | m
    · contradiction
    · injection h with h; subst h
      exact ⟨1,zDg.one zDg.nil⟩
    · dsimp [e_zPf, forceNat] at h
      simp only [forceWord_eq] at h
      cases hrec : e_zPf fuel ((m + 2) / 2) with
      | none => rw [hrec] at h; contradiction
      | some ws' =>
        rw [hrec] at h
        injection h with h; subst h
        rcases ih ((m + 2) / 2) ws' hrec with ⟨H,hD⟩
        rcases Nat.mod_two_eq_zero_or_one (m + 2) with hmod | hmod
        · have hcond : ((m + 2) % 2 == 0) = true := beq_iff_eq.mpr hmod
          rw [hcond]
          refine ⟨1 + H,?_⟩
          have heq : m + 2 = ((m + 2) / 2) * 2 := by omega
          rw [heq]; exact zDg.zero hD
        · have hcond : ((m + 2) % 2 == 0) = false := beq_false_of_ne (by omega)
          rw [hcond]
          refine ⟨1 + H,?_⟩
          have heq : m + 2 = 1 + ((m + 2) / 2) * 2 := by omega
          rw [heq]; exact zDg.one hD
def e_zSw : zW -> zW -> Option (zW)
  | [],u => some u
  | V :: p,V :: u => e_zSw p u
  | K :: p,K :: u => e_zSw p u
  | Q :: p,Q :: u => e_zSw p u
  | _,_ => none
lemma e_z2f (p : zW) :
    ∀ (u v : zW),e_zSw p u = some v -> u = p ++ v := by
  induction p with
  | nil => intro u v h; injection h
  | cons w p ih =>
    intro u v h
    cases u with
    | nil => cases w <;> contradiction
    | cons x u =>
      cases w <;> cases x <;> try contradiction
      all_goals
        dsimp [e_zSw] at h
        rw [ih u v h]; rfl
inductive e_Choice where
  | CT | CP0 | CP1 | CS00 | CS01 | CS10 | CS11
deriving DecidableEq
open e_Choice
inductive e_Code where
  | Stop (n : Nat)
  | More (ch : e_Choice) (n : Nat) (next : e_Code)
def e_z2g : e_Choice -> Nat -> Nat
  | CT,n => 3 + n
  | CP0,n | CP1,n => 1 + n
  | CS00,n | CS01,n => 2 + n * 4
  | CS10,n | CS11,n => 4 + n * 4
def e_z2h : e_Choice -> Nat -> Nat
  | CT,n => 2 + n * 2
  | CP0,n | CS00,n | CS10,n => n * 2
  | CP1,n | CS01,n | CS11,n => 1 + n * 2
def e_z2i : e_Choice -> zW
  | CT => [V]
  | CP0 => [Q,K]
  | CP1 => [Q,Q]
  | CS00 | CS10 => [K]
  | CS01 | CS11 => [Q]
def e_z2j : e_Choice -> Word
  | CT | CP0 | CP1 => V
  | CS00 | CS01 => K
  | CS10 | CS11 => Q
def e_z2k : e_Code -> Nat -> zW -> Option (Nat × zW)
  | .Stop n,k,[] =>
    if k == n * 2 && 0 < n then some (n,[]) else none
  | .Stop _,_,_ :: _ => none
  | .More ch m c,k,u =>
    if k == e_z2g ch m then
      match e_zSw (e_z2i ch) u with
      | none => none
      | some w =>
        forceNat (e_z2h ch m) (fun k' =>
          match e_z2k c k' w with
          | none => none
          | some (n,v) => forceWord (e_z2j ch) (fun wj => some (n,wj :: v)))
    else none
lemma e_z2l (c : e_Code) :
    ∀ (k : Nat) (u : zW) (n : Nat) (v : zW),
      e_z2k c k u = some (n,v) ->
      ∃ a b,zPS k u (n * 2) v a b /\ 0 < n := by
  induction c with
  | Stop m =>
    intro k u n v hE
    cases u with
    | cons _ _ => contradiction
    | nil =>
      dsimp [e_z2k, forceNat] at hE
      cases hcond : (k == m * 2 && decide (0 < m)) with
      | false => rw [hcond] at hE; contradiction
      | true =>
        rw [hcond] at hE
        injection hE with hE
        injection hE with hm hv; subst hm hv
        rcases Bool.and_eq_true_iff.mp hcond with ⟨hk,hpos⟩
        have rfl_k : k = m * 2 := beq_iff_eq.mp hk
        subst rfl_k
        exact ⟨0,0,zPS.nil (m * 2),of_decide_eq_true hpos⟩
  | More ch m c ih =>
    intro k u n v hE
    dsimp [e_z2k] at hE
    cases hk : (k == e_z2g ch m) with
    | false => rw [hk] at hE; contradiction
    | true =>
      rw [hk] at hE; dsimp at hE
      have rfl_k : k = e_z2g ch m := beq_iff_eq.mp hk
      subst rfl_k
      cases hU : e_zSw (e_z2i ch) u with
      | none => rw [hU] at hE; contradiction
      | some w =>
        rw [hU] at hE; dsimp at hE
        cases hC : e_z2k c (e_z2h ch m) w with
        | none => rw [hC] at hE; contradiction
        | some nv =>
          rw [hC] at hE
          rcases nv with ⟨n',x⟩
          dsimp [forceNat] at hE
          rw [forceWord_eq] at hE
          injection hE with hE
          injection hE with hn hv; subst hn hv
          have rfl_u := e_z2f (e_z2i ch) u w hU
          subst rfl_u
          rcases ih (e_z2h ch m) w n' x hC with ⟨a,b,hS,hPos⟩
          cases ch
          · exact ⟨a * (1 / 2),b * (1 / 2),zPS.T hS,hPos⟩
          · exact ⟨a * (1 / 2),(1 + b) * (1 / 2),zPS.pair0 hS,hPos⟩
          · exact ⟨a * (1 / 2),(3 / 4) + b * (1 / 2),zPS.pair1 hS,hPos⟩
          · exact ⟨3 + a * 2,b * 2,zPS.short00 hS,hPos⟩
          · exact ⟨2 + a * 2,b * 2,zPS.short01 hS,hPos⟩
          · exact ⟨4 + a * 2,b * 2,zPS.short10 hS,hPos⟩
          · exact ⟨3 + a * 2,b * 2,zPS.short11 hS,hPos⟩
def e_z2m (h : Nat) (c : e_Code) (orig : zW) : Option (zW) :=
  let (carry,eff) := zEe 0 (orig ++ [K])
  if carry == 0 then
    forceNat (4 * 2 ^ h) (fun k =>
      match e_z2k c k eff with
      | none => none
      | some (n,v) =>
        forceNat (1 + n) (fun m =>
          match e_zPf 64 m with
          | none => none
          | some da => some (v ++ da)))
  else none
lemma e_z2n (h : Nat) (c : e_Code) (orig out : zW)
    (hR : e_z2m h c orig = some out) :
    EStep h orig out := by
  dsimp [e_z2m, forceNat] at hR
  have hE := zEs (orig ++ [K]) 0
  generalize h_ev : zEe 0 (orig ++ [K]) = ce at hR hE
  rcases ce with ⟨carry,eff⟩
  dsimp at hE hR
  cases hc : (carry == 0) with
  | false => rw [hc] at hR; contradiction
  | true =>
    rw [hc] at hR; dsimp at hR
    have rfl_c : carry = 0 := beq_iff_eq.mp hc
    subst rfl_c
    cases hP : e_z2k c (4 * 2 ^ h) eff with
    | none => rw [hP] at hR; contradiction
    | some nv =>
      rw [hP] at hR
      rcases nv with ⟨n,v⟩
      dsimp at hR
      cases hD : e_zPf 64 (1 + n) with
      | none => rw [hD] at hR; contradiction
      | some da =>
        rw [hD] at hR
        injection hR with hR; subst hR
        rcases e_z2l c (4 * 2 ^ h) eff n v hP with ⟨a,b,hS,hPos⟩
        rcases e_z2e 64 (1 + n) da hD with ⟨J,hDig⟩
        exact EStep.intro h orig eff n v a b J da hE hS hPos hDig
inductive ERounds : Nat -> zW -> Nat -> zW -> Prop where
  | refl (h : Nat) (u : zW) : ERounds h u h u
  | next {h : Nat} {u v : zW} {j : Nat} {w : zW} :
      EStep h u v -> ERounds (h + 1) v j w -> ERounds h u j w
def e_z2o : Nat -> List e_Code -> zW -> Option (zW)
  | _,[],u => some u
  | h,c :: cs,u =>
    match e_z2m h c u with
    | none => none
    | some v => forceNat (h + 1) (fun h' => e_z2o h' cs v)
lemma e_z2p (cs : List e_Code) :
    ∀ (h : Nat) (u v : zW),
      e_z2o h cs u = some v ->
      ERounds h u (h + cs.length) v := by
  induction cs with
  | nil =>
    intro h u v hR
    injection hR with hR; subst hR
    simpa using! ERounds.refl h u
  | cons c cs ih =>
    intro h u v hR
    dsimp [e_z2o, forceNat] at hR
    cases hW : e_z2m h c u with
    | none => rw [hW] at hR; contradiction
    | some w =>
      rw [hW] at hR
      have hStep := e_z2n h c u w hW
      have hSub := ih (h + 1) w v hR
      have heq : (h + 1) + cs.length = h + (c :: cs).length := by simp; omega
      rw [heq] at hSub
      exact ERounds.next hStep hSub
def e_z2q : Word -> Bool
  | V => false
  | _ => true
lemma e_z2r (ds : zW) (h : ds.all e_z2q = true) :
    ∃ A,zDg A ds.length ds := by
  induction ds with
  | nil => exact ⟨0,zDg.nil⟩
  | cons w ds ih =>
    cases w
    · contradiction
    · dsimp [List.all,e_z2q] at h
      rcases ih h with ⟨A,hI⟩
      have heq : (K :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨A * 2,zDg.zero hI⟩
    · dsimp [List.all,e_z2q] at h
      rcases ih h with ⟨A,hI⟩
      have heq : (Q :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨1 + A * 2,zDg.one hI⟩
lemma e_z2s (h : Nat) (u da db : zW)
    (hHt : e_zHn u h = some da.length)
    (hGu : EGuard u)
    (hEnd : u = u.take (u.length - 4) ++ zR 4 V)
    (hDig : da.all e_z2q = true)
    (hLast : (zEe (zEe 0 u).1 da).1 = 0)
    (hDB_eq : (zEe (zEe 0 u).1 da).2 = db)
    (hPair : z0Y (zEe 0 u).2 = true)
    (hLo : db = K :: K :: K :: db.drop 3)
    (hHi : db = db.take (db.length - 7) ++ zR 7 Q)
    (hPhi : 4 * (1 / ((2 ^ h : Nat) : Rat)) * z1e u + (1 / ((2 ^ h : Nat) : Rat)) * z1h u * z1f db + 2 * (1 / ((2 ^ h : Nat) : Rat)) <= 1 / 256) :
    EGood h (u ++ da) := by
  rcases e_z2r da hDig with ⟨A,hDA⟩
  have hEU := zEs u 0
  let carry := (zEe 0 u).1
  let eff := (zEe 0 u).2
  have hED := zEs da carry
  rw [hLast,hDB_eq] at hED
  rcases z1G hED hDA with ⟨B,hDB,hSum⟩
  simp only [Nat.zero_mul,Nat.add_zero] at hSum
  refine EGood.intro h da.length u A da carry eff B db (1 / ((2 ^ h : Nat) : Rat))
    hHt hGu ⟨u.take (u.length - 4),hEnd⟩ hDA hEU hSum hDB hPair
    ⟨db.drop 3,hLo⟩ ⟨db.take (db.length - 7),hHi⟩ ?_ hPhi
  have hpos : ((2 ^ h : Nat) : Rat) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (zPp h)
  exact one_div_mul_cancel hpos

end BusyBeaver.WordCalculus
