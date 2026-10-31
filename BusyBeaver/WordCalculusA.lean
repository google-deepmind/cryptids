module

public import BusyBeaver.Defs
import Mathlib.Data.List.Induction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

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
local notation "t" => ([1,1,0,0] : zF)
local notation "d0" => ([0,0] : zF)
local notation "d1" => ([1,0] : zF)
lemma zPp (n : Nat) : 0 < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega
lemma zP2 (n : Nat) : 2 ^ (1 + n) = 2 ^ n + 2 ^ n := by
  rw [Nat.add_comm 1 n,Nat.pow_succ]; omega
lemma z0U (n : Nat) : (∃ a,n = a * 2) \/ (∃ a,n = 1 + a * 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · left; exact ⟨n / 2,by omega⟩
  · right; exact ⟨n / 2,by omega⟩
inductive Word where
  | V
  | K
  | Q
deriving DecidableEq
open Word
local notation "zW" => List Word
local notation "zR" => List.replicate
inductive zPr : Bool -> zW -> Prop where
  | nil (e : Bool) : zPr e []
  | T (e : Bool) {u : zW} : zPr true u -> zPr e (V :: u)
  | short0 {u : zW} : zPr true u -> zPr true (K :: u)
  | short1 {u : zW} : zPr false u -> zPr true (Q :: u)
  | pair0 (e : Bool) {u : zW} : zPr true u -> zPr e (Q :: K :: u)
  | pair1 (e : Bool) {u : zW} : zPr false u -> zPr e (Q :: Q :: u)
lemma z0V {u : zW} (h : zPr false u) : zPr true u := by
  cases h with
  | nil _ => exact zPr.nil true
  | T _ hu => exact zPr.T true hu
  | pair0 _ hu => exact zPr.pair0 true hu
  | pair1 _ hu => exact zPr.pair1 true hu
lemma z0W (u : zW) :
    zPr true u /\ (zPr false u \/ zPr false (Q :: u)) := by
  induction u with
  | nil => exact ⟨zPr.nil true,Or.inl (zPr.nil false)⟩
  | cons w u ih =>
    rcases ih with ⟨hI,hJ⟩
    cases w with
    | V => exact ⟨zPr.T true hI,Or.inl (zPr.T false hI)⟩
    | K => exact ⟨zPr.short0 hI,Or.inr (zPr.pair0 false hI)⟩
    | Q =>
      rcases hJ with hJ | hJ
      · exact ⟨zPr.short1 hJ,Or.inr (zPr.pair1 false hJ)⟩
      · exact ⟨z0V hJ,Or.inl hJ⟩
inductive zDg : Nat -> Nat -> zW -> Prop where
  | nil : zDg 0 0 []
  | zero {A H : Nat} {u : zW} : zDg A H u -> zDg (A * 2) (1 + H) (K :: u)
  | one {A H : Nat} {u : zW} : zDg A H u -> zDg (1 + A * 2) (1 + H) (Q :: u)
lemma z0X {A H : Nat} {u : zW} (h : zDg A H (V :: u)) : False := by
  cases h
lemma zD0 {A H : Nat} {u : zW} (h : zDg A H (K :: u)) :
    ∃ A' H',zDg A' H' u /\ A = A' * 2 /\ H = 1 + H' := by
  cases h with
  | zero hD => exact ⟨_,_,hD,rfl,rfl⟩
lemma zD1 {A H : Nat} {u : zW} (h : zDg A H (Q :: u)) :
    ∃ A' H',zDg A' H' u /\ A = 1 + A' * 2 /\ H = 1 + H' := by
  cases h with
  | one hD => exact ⟨_,_,hD,rfl,rfl⟩
def z0Y : zW -> Bool
  | Q :: K :: _ => true
  | _ :: v => z0Y v
  | [] => false
def z0Z : zW -> Bool
  | [] => true
  | [Q] => false
  | _ :: v => z0Z v
lemma zCo (w : Word) (u : zW) (h : z0Z (w :: u) = true) :
    z0Z u = true := by
  cases u with
  | nil => rfl
  | cons x xs => cases w <;> exact h
def z10 (p q : zW) : Prop :=
  z0Z p = true \/ ∃ r,q = V :: r
lemma zCt (w : Word) (p q : zW) (h : z10 (w :: p) q) :
    z10 p q := by
  rcases h with h | h
  · left; exact zCo w p h
  · right; exact h
lemma z11 (u : zW) (w : Word) :
    z0Z (u ++ [w]) = z0Z [w] := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    cases u with
    | nil => cases a <;> rfl
    | cons b u' => cases a <;> exact ih
lemma z12 (p : Nat) : z0Z (zR p V) = true := by
  induction p with
  | zero => rfl
  | succ p ih =>
    cases p with
    | zero => rfl
    | succ p' => exact ih
lemma z13 (w : Word) (n : Nat) :
    zR (n + 1) w = zR n w ++ [w] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv_lhs => rw [List.replicate_succ,ih]
    rfl
lemma z14 (u : zW) :
    ∃ p n,u = p ++ zR n Q /\ z0Z p = true := by
  induction u using List.reverseRecOn with
  | nil => exact ⟨[],0,rfl,rfl⟩
  | append_singleton u x ih =>
    rcases ih with ⟨p,n,rfl,hP⟩
    cases x with
    | V =>
      exact ⟨(p ++ zR n Q) ++ [V],0,by simp,by rw [z11]; rfl⟩
    | K =>
      exact ⟨(p ++ zR n Q) ++ [K],0,by simp,by rw [z11]; rfl⟩
    | Q =>
      refine ⟨p,n + 1,?_,hP⟩
      rw [z13,List.append_assoc]
def zTs : zW -> zB -> zB
  | [],r => r
  | V :: u,r => t +> zTs u r
  | K :: u,r => d0 +> zTs u r
  | Q :: u,r => d1 +> zTs u r
lemma z15 (u v : zW) (r : zB) :
    zTs (u ++ v) r = zTs u (zTs v r) := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> simp [zTs,ih]
def zWt : zW -> zF
  | [] => []
  | V :: u => t ++ zWt u
  | K :: u => d0 ++ zWt u
  | Q :: u => d1 ++ zWt u
lemma z16 (u : zW) (r : zB) :
    zWt u +> r = zTs u r := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    cases a <;> (dsimp [zWt,zTs]; rw [ih])
lemma z17 (u v : zW) :
    zWt (u ++ v) = zWt u ++ zWt v := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    cases a <;> (dsimp [zWt]; rw [ih])
lemma z18 (H : Nat) : ∀ A,A < 2 ^ H -> ∃ u,zDg A H u := by
  induction H with
  | zero =>
    intro A hA
    have h0 : A = 0 := by simpa using hA
    subst h0; exact ⟨[],zDg.nil⟩
  | succ H ih =>
    intro A hA
    have hpow : 2 ^ (H + 1) = 2 ^ H * 2 := Nat.pow_succ 2 H
    have h1H : H + 1 = 1 + H := by omega
    rcases z0U A with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · rcases ih a (by omega) with ⟨u,hI⟩
      rw [h1H]; exact ⟨K :: u,zDg.zero hI⟩
    · rcases ih a (by omega) with ⟨u,hI⟩
      rw [h1H]; exact ⟨Q :: u,zDg.one hI⟩
lemma z19 {A H : Nat} {u : zW} (h1 : zDg A H u) :
    ∀ {B J : Nat} {v : zW},zDg B J v -> zDg (A + B * 2 ^ H) (H + J) (u ++ v) := by
  induction h1 with
  | nil =>
    intro B J v h2
    simpa using h2
  | @zero A H u _ ih =>
    intro B J v h2
    have h3 := zDg.zero (ih h2)
    have heq1 : (A + B * 2 ^ H) * 2 = A * 2 + B * 2 ^ (1 + H) := by
      rw [zP2]; ring
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    rwa [heq1,heq2] at h3
  | @one A H u _ ih =>
    intro B J v h2
    have h3 := zDg.one (ih h2)
    have heq1 : 1 + (A + B * 2 ^ H) * 2 = (1 + A * 2) + B * 2 ^ (1 + H) := by
      rw [zP2]; ring
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    rwa [heq1,heq2] at h3
lemma z1a (n : Nat) : zDg (2 ^ n - 1) n (zR n Q) := by
  induction n with
  | zero => exact zDg.nil
  | succ n ih =>
    have hpos := zPp n
    have h1 := zDg.one ih
    have heq1 : 1 + (2 ^ n - 1) * 2 = 2 ^ (n + 1) - 1 := by
      rw [Nat.pow_succ]; omega
    have heq2 : 1 + n = n + 1 := by omega
    simpa [List.replicate,heq1,heq2] using h1
lemma z1b {A H : Nat} {u : zW} (h : zDg A H u) : A < 2 ^ H := by
  induction h with
  | nil => decide
  | @zero A H u _ ih => rw [zP2]; omega
  | @one A H u _ ih => rw [zP2]; omega
lemma z1c {A1 H1 : Nat} {u : zW} (h1 : zDg A1 H1 u) :
    ∀ {A2 H2 : Nat} {v : zW},zDg A2 H2 v -> A1 = A2 -> H1 = H2 -> u = v := by
  induction h1 with
  | nil =>
    intro A2 H2 v h2 hA hH
    cases h2 with
    | nil => rfl
    | zero _ => omega
    | one _ => omega
  | @zero A1 H1 u _ ih =>
    intro A2 H2 v h2 hA hH
    cases h2 with
    | nil => omega
    | @zero A2' H2' v' hD =>
      rw [ih hD (by omega) (by omega)]
    | one _ => omega
  | @one A1 H1 u _ ih =>
    intro A2 H2 v h2 hA hH
    cases h2 with
    | nil => omega
    | zero _ => omega
    | @one A2' H2' v' hD =>
      rw [ih hD (by omega) (by omega)]
lemma z1d {A H : Nat} {u v : zW} (h1 : zDg A H u) (h2 : zDg A H v) : u = v :=
  z1c h1 h2 rfl rfl
def z1e : zW -> Rat
  | [] => 0
  | V :: v => z1e v * (1 / 2)
  | _ :: v => 1 + z1e v * 2
def z1f : zW -> Rat
  | [] => 0
  | V :: v => z1f v * (1 / 2)
  | K :: v => 1 + z1f v * 2
  | Q :: v => z1f v * 2
def z1g : zW -> Rat
  | [] => 0
  | V :: v => z1g v * (1 / 2)
  | K :: v => z1g v * 2
  | Q :: v => 1 + z1g v * 2
def z1h : zW -> Rat
  | [] => 1
  | V :: v => z1h v * (1 / 2)
  | _ :: v => z1h v * 2
lemma zWn (u : zW) : 0 <= z1e u /\ 0 <= z1f u /\ 0 <= z1g u := by
  induction u with
  | nil => simp [z1e,z1f,z1g]
  | cons a u ih =>
    cases a <;> (dsimp [z1e,z1f,z1g]; constructor; linarith; constructor <;> linarith)
lemma z1i (u : zW) : z1e u = z1f u + z1g u := by
  induction u with
  | nil => simp [z1e,z1f,z1g]
  | cons a u ih => cases a <;> (dsimp [z1e,z1f,z1g]; rw [ih]; ring)
lemma zSp (u : zW) : 0 < z1h u := by
  induction u with
  | nil => simp [z1h]
  | cons a u ih => cases a <;> (dsimp [z1h]; linarith)
lemma z1j (u v : zW) : z1e (u ++ v) = z1e u + z1h u * z1e v := by
  induction u with
  | nil => simp [z1e,z1h]
  | cons a u ih => cases a <;> (dsimp [z1e,z1h]; rw [ih]; ring)
lemma z1k (u v : zW) : z1f (u ++ v) = z1f u + z1h u * z1f v := by
  induction u with
  | nil => simp [z1f,z1h]
  | cons a u ih => cases a <;> (dsimp [z1f,z1h]; rw [ih]; ring)
lemma z1l (u v : zW) : z1g (u ++ v) = z1g u + z1h u * z1g v := by
  induction u with
  | nil => simp [z1g,z1h]
  | cons a u ih => cases a <;> (dsimp [z1g,z1h]; rw [ih]; ring)
lemma z1m (u v : zW) : z1h (u ++ v) = z1h u * z1h v := by
  induction u with
  | nil => simp [z1h]
  | cons a u ih => cases a <;> (dsimp [z1h]; rw [ih]; ring)
lemma zDw {A H : Nat} {u : zW} (h : zDg A H u) :
    z1h u = ((2 ^ H : Nat) : Rat) /\ z1e u + 1 = ((2 ^ H : Nat) : Rat) /\ z1g u = (A : Rat) := by
  induction h with
  | nil => simp [z1h,z1e,z1g]
  | @zero A H u _ ih =>
    rw [zP2 H]; dsimp [z1h,z1e,z1g]
    push_cast at ih ⊢; constructor; linarith; constructor <;> linarith
  | @one A H u _ ih =>
    rw [zP2 H]; dsimp [z1h,z1e,z1g]
    push_cast at ih ⊢; constructor; linarith; constructor <;> linarith
lemma z1n {A H : Nat} {u : zW} (h : zDg A H u) :
    z1f u + (A : Rat) + 1 = ((2 ^ H : Nat) : Rat) := by
  have hd := zDw h
  have hm := z1i u
  linarith
inductive Scan : Nat -> zW -> Nat -> zW -> Rat -> Prop where
  | nil (k : Nat) : Scan k [] k [] 0
  | T {n : Nat} {u : zW} {k : Nat} {v : zW} {l : Rat} :
      Scan ((1 + n) * 2) u k v l -> Scan (1 + n) (V :: u) k (V :: v) (l * (1 / 2))
  | pair0 {n : Nat} {u : zW} {k : Nat} {v : zW} {l : Rat} :
      Scan (n * 2) u k v l -> Scan (1 + n) (Q :: K :: u) k (V :: v) ((1 + l) * (1 / 2))
  | pair1 {n : Nat} {u : zW} {k : Nat} {v : zW} {l : Rat} :
      Scan (1 + n * 2) u k v l -> Scan (1 + n) (Q :: Q :: u) k (V :: v) ((1 / 4) + l * (1 / 2))
  | short00 {n : Nat} {u : zW} {k : Nat} {v : zW} {l : Rat} :
      Scan (n * 2) u k v l -> Scan (2 + n * 4) (K :: u) k (K :: v) (1 + l * 2)
  | short01 {n : Nat} {u : zW} {k : Nat} {v : zW} {l : Rat} :
      Scan (1 + n * 2) u k v l -> Scan (2 + n * 4) (Q :: u) k (K :: v) (l * 2)
  | short10 {n : Nat} {u : zW} {k : Nat} {v : zW} {l : Rat} :
      Scan (n * 2) u k v l -> Scan (4 + n * 4) (K :: u) k (Q :: v) (1 + l * 2)
  | short11 {n : Nat} {u : zW} {k : Nat} {v : zW} {l : Rat} :
      Scan (1 + n * 2) u k v l -> Scan (4 + n * 4) (Q :: u) k (Q :: v) (l * 2)
lemma z1o {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) :
    0 <= l /\ z1e v <= z1e u /\ z1e v + l <= z1e u + z1f u := by
  induction h with
  | nil _ => simp [z1e,z1f]
  | T _ ih =>
    dsimp [z1e,z1f]; constructor; linarith; constructor <;> linarith
  | @pair0 n u k v l _ ih =>
    have hw := zWn v
    dsimp [z1e,z1f]; constructor; linarith; constructor <;> linarith
  | @pair1 n u k v l _ ih =>
    have hw := zWn v
    dsimp [z1e,z1f]; constructor; linarith; constructor <;> linarith
  | short00 _ ih =>
    dsimp [z1e,z1f]; constructor; linarith; constructor <;> linarith
  | short01 _ ih =>
    dsimp [z1e,z1f]; constructor; linarith; constructor <;> linarith
  | short10 _ ih =>
    dsimp [z1e,z1f]; constructor; linarith; constructor <;> linarith
  | short11 _ ih =>
    dsimp [z1e,z1f]; constructor; linarith; constructor <;> linarith
lemma z1p {e : Bool} {u : zW} (hI : zPr e u) :
    ∀ (k : Nat),(e = true -> ∃ n,k = n * 2) ->
      (z1e u + z1f u) * 2 < (k : Rat) ->
      ∃ b v l,Scan k u b v l /\ 0 < b := by
  induction hI with
  | nil e =>
    intro k _ hk
    dsimp [z1e,z1f] at hk
    have hk_pos : (0 : Rat) < (k : Rat) := by linarith
    have hk_nat : 0 < k := Nat.cast_pos.mp hk_pos
    exact ⟨k,[],0,Scan.nil k,hk_nat⟩
  | @T e u _ ih =>
    intro k _ hk
    have hw := zWn u
    dsimp [z1e,z1f] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih ((1 + k) * 2) (fun _ => ⟨1 + k,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,l,hS,hB⟩
      exact ⟨b,V :: v,l * (1 / 2),Scan.T hS,hB⟩
  | @short0 u _ ih =>
    intro k hEk hk
    have hw := zWn u
    dsimp [z1e,z1f] at hk
    rcases hEk rfl with ⟨n,rfl⟩
    rcases z0U n with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (a * 2) (fun _ => ⟨a,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,l,hS,hB⟩
        refine ⟨b,Q :: v,1 + l * 2,?_,hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact Scan.short10 hS
    · rcases ih (a * 2) (fun _ => ⟨a,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,l,hS,hB⟩
      refine ⟨b,K :: v,1 + l * 2,?_,hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact Scan.short00 hS
  | @short1 u _ ih =>
    intro k hEk hk
    have hw := zWn u
    dsimp [z1e,z1f] at hk
    rcases hEk rfl with ⟨n,rfl⟩
    rcases z0U n with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (1 + a * 2) (fun h => by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,l,hS,hB⟩
        refine ⟨b,Q :: v,l * 2,?_,hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact Scan.short11 hS
    · rcases ih (1 + a * 2) (fun h => by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,l,hS,hB⟩
      refine ⟨b,K :: v,l * 2,?_,hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact Scan.short01 hS
  | @pair0 e u _ ih =>
    intro k _ hk
    have hw := zWn u
    dsimp [z1e,z1f] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (k * 2) (fun _ => ⟨k,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,l,hS,hB⟩
      exact ⟨b,V :: v,(1 + l) * (1 / 2),Scan.pair0 hS,hB⟩
  | @pair1 e u _ ih =>
    intro k _ hk
    have hw := zWn u
    dsimp [z1e,z1f] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (1 + k * 2) (fun h => by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,l,hS,hB⟩
      exact ⟨b,V :: v,(1 / 4) + l * (1 / 2),Scan.pair1 hS,hB⟩
lemma z1q (u : zW) (k : Nat) (h : (z1e u + z1f u) * 2 < ((k * 2 : Nat) : Rat)) :
    ∃ b v l,Scan (k * 2) u b v l /\ 0 < b :=
  z1p (z0W u).1 (k * 2) (fun _ => ⟨k,rfl⟩) h
lemma zSz (n : Nat) (u : zW) (b : Nat) (v : zW) (l : Rat) :
    ¬ Scan (1 + n * 2) (K :: u) b v l := by
  intro h; generalize ha : 1 + n * 2 = a at h; cases h <;> omega
lemma zSo (r : Nat) :
    ∀ (n b : Nat) (v : zW) (l : Rat),
      ¬ Scan (1 + n * 2) (zR (r * 2) Q ++ [K]) b v l := by
  induction r with
  | zero =>
    intro n b v l hI
    exact zSz n [] b v l hI
  | succ r ih =>
    intro n b v l hI
    have heq : (r + 1) * 2 = r * 2 + 2 := by omega
    rw [heq] at hI
    change Scan (1 + n * 2) (Q :: Q :: (zR (r * 2) Q ++ [K])) b v l at hI
    generalize ha : 1 + n * 2 = a at hI
    cases hI with
    | @pair1 m _ _ _ _ hJ =>
      exact ih m _ _ _ hJ
    | short01 _ => omega
    | short11 _ => omega
lemma zS1 (r : Nat) :
    ∀ (a b : Nat) (v : zW) (l : Rat),
      Scan a (zR (1 + r * 2) Q ++ [K]) b v l ->
      v = zR (1 + r) V /\ b = (a - 1) * 2 ^ (1 + r) /\ l = 1 / 2 := by
  induction r with
  | zero =>
    intro a b v l hI
    change Scan a [Q,K] b v l at hI
    cases hI with
    | @pair0 m _ _ _ _ hJ =>
      generalize hk : m * 2 = k at hJ
      cases hJ
      exact ⟨rfl,by simp; omega,by ring⟩
    | short01 hJ => exact False.elim (zSz _ [] _ _ _ hJ)
    | short11 hJ => exact False.elim (zSz _ [] _ _ _ hJ)
  | succ r ih =>
    intro a b v l hI
    have heq : 1 + (r + 1) * 2 = (1 + r * 2) + 2 := by omega
    rw [heq] at hI
    change Scan a (Q :: Q :: (zR (1 + r * 2) Q ++ [K])) b v l at hI
    cases hI with
    | @pair1 n _ _ v0 l0 hJ =>
      rcases ih (1 + n * 2) b v0 l0 hJ with ⟨rfl,rfl,rfl⟩
      refine ⟨rfl,?_,by ring⟩
      have heq2 : 1 + (r + 1) = (1 + r) + 1 := by omega
      rw [heq2,Nat.pow_succ]; simp; ring
    | @short01 n _ _ _ _ hJ =>
      have heq2 : (1 + r * 2) + 1 = (r + 1) * 2 := by omega
      change Scan (1 + n * 2) (zR ((1 + r * 2) + 1) Q ++ [K]) _ _ _ at hJ
      rw [heq2] at hJ
      exact False.elim (zSo (r + 1) n _ _ _ hJ)
    | @short11 n _ _ _ _ hJ =>
      have heq2 : (1 + r * 2) + 1 = (r + 1) * 2 := by omega
      change Scan (1 + n * 2) (zR ((1 + r * 2) + 1) Q ++ [K]) _ _ _ at hJ
      rw [heq2] at hJ
      exact False.elim (zSo (r + 1) n _ _ _ hJ)
lemma z1r (r a b : Nat) (v : zW) (l : Rat)
    (hI : Scan a (zR (2 + r * 2) Q ++ [K]) b v l) :
    ∃ d n,v = d :: zR (1 + r) V /\ b = n * 2 ^ (2 + r) /\ l = 1 := by
  have heq0 : 2 + r * 2 = (r * 2) + 2 := by omega
  rw [heq0] at hI
  change Scan a (Q :: Q :: (zR (r * 2) Q ++ [K])) b v l at hI
  cases hI with
  | @pair1 n _ _ _ _ hJ =>
    exact False.elim (zSo r n _ _ _ hJ)
  | @short01 n _ _ v0 l0 hJ =>
    have heq1 : 1 + r * 2 = (r * 2) + 1 := by omega
    have hJ' : Scan (1 + n * 2) (zR (1 + r * 2) Q ++ [K]) b v0 l0 := by
      rw [heq1]; exact hJ
    rcases zS1 r (1 + n * 2) b v0 l0 hJ' with ⟨rfl,rfl,rfl⟩
    refine ⟨K,n,rfl,?_,by ring⟩
    have heq : 2 + r = (1 + r) + 1 := by omega
    rw [heq,Nat.pow_succ]; simp; ring
  | @short11 n _ _ v0 l0 hJ =>
    have heq1 : 1 + r * 2 = (r * 2) + 1 := by omega
    have hJ' : Scan (1 + n * 2) (zR (1 + r * 2) Q ++ [K]) b v0 l0 := by
      rw [heq1]; exact hJ
    rcases zS1 r (1 + n * 2) b v0 l0 hJ' with ⟨rfl,rfl,rfl⟩
    refine ⟨Q,n,rfl,?_,by ring⟩
    have heq : 2 + r = (1 + r) + 1 := by omega
    rw [heq,Nat.pow_succ]; simp; ring
lemma z1s (n r a b : Nat) (v : zW) (l : Rat)
    (hI : Scan a (zR (1 + r * 2 + n) Q ++ [K]) b v l) :
    ∃ w k,v = w ++ zR (1 + r) V /\ b = k * 2 ^ (1 + r) := by
  rcases z0U n with ⟨a0,rfl⟩ | ⟨a0,rfl⟩
  · have heq : 1 + r * 2 + a0 * 2 = 1 + (r + a0) * 2 := by omega
    rw [heq] at hI
    rcases zS1 (r + a0) a b v l hI with ⟨rfl,rfl,_⟩
    refine ⟨zR a0 V,(a - 1) * 2 ^ a0,?_,?_⟩
    · have heq2 : 1 + (r + a0) = a0 + (1 + r) := by omega
      rw [heq2,List.replicate_add]
    · have heq2 : 1 + (r + a0) = a0 + (1 + r) := by omega
      rw [heq2,Nat.pow_add]; ring
  · have heq : 1 + r * 2 + (1 + a0 * 2) = 2 + (r + a0) * 2 := by omega
    rw [heq] at hI
    rcases z1r (r + a0) a b v l hI with ⟨d,k,rfl,rfl,_⟩
    refine ⟨d :: zR a0 V,k * 2 ^ (1 + a0),?_,?_⟩
    · have heq2 : 1 + (r + a0) = a0 + (1 + r) := by omega
      rw [heq2,List.replicate_add]; rfl
    · have heq2 : 2 + (r + a0) = (1 + a0) + (1 + r) := by omega
      rw [heq2,Nat.pow_add]; ring
inductive zTd : zW -> Rat -> Prop where
  | tail_end : zTd [K] 0
  | tail_zero {u : zW} {z : Rat} : zTd u z -> zTd (K :: u) (1 + z * 2)
  | tail_one {u : zW} {z : Rat} : zTd u z -> zTd (Q :: u) (z * 2)
lemma z1t {u : zW} {z : Rat} (h : zTd u z) : 0 <= z := by
  induction h with
  | tail_end => linarith
  | tail_zero _ ih => linarith
  | tail_one _ ih => linarith
lemma z1u {u : zW} {z : Rat} (h : zTd (K :: u) z) :
    (u = [] /\ z = 0) \/ ∃ y,zTd u y /\ z = 1 + y * 2 := by
  cases h with
  | tail_end => left; exact ⟨rfl,rfl⟩
  | tail_zero hJ => right; exact ⟨_,hJ,rfl⟩
lemma zTo {u : zW} {z : Rat} (h : zTd (Q :: u) z) :
    ∃ y,zTd u y /\ z = y * 2 := by
  cases h with
  | tail_one hJ => exact ⟨_,hJ,rfl⟩
lemma z1v {A H : Nat} {u : zW} (h : zDg A H u) :
    zTd (u ++ [K]) (z1f u) := by
  induction h with
  | nil => exact zTd.tail_end
  | zero _ ih => exact zTd.tail_zero ih
  | one _ ih => exact zTd.tail_one ih
lemma z1w {u : zW} {z : Rat} (h : zTd u z) :
    ∃ A H,zDg A H u := by
  induction h with
  | tail_end => exact ⟨0,1,zDg.zero zDg.nil⟩
  | tail_zero _ ih =>
    rcases ih with ⟨A,H,hD⟩
    exact ⟨A * 2,1 + H,zDg.zero hD⟩
  | tail_one _ ih =>
    rcases ih with ⟨A,H,hD⟩
    exact ⟨1 + A * 2,1 + H,zDg.one hD⟩
lemma z1x {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) :
    ∀ {z : Rat},zTd u z ->
      z1e v <= 1 + z * 2 /\ l <= 1 + z * 2 /\
      (∀ n,a = 1 + n * 2 -> z1e v <= z * 2 /\ l <= (1 / 2) + z * 2) := by
  induction h with
  | nil _ => intro z hZ; cases hZ
  | T _ _ => intro z hZ; cases hZ
  | @pair0 m _ _ _ _ hI ih =>
    intro z hZ
    rcases zTo hZ with ⟨y,hJ,rfl⟩
    rcases z1u hJ with ⟨rfl,rfl⟩ | ⟨x,hJ',rfl⟩
    · generalize hk : m * 2 = k at hI
      cases hI
      dsimp [z1e]; refine ⟨by linarith,by linarith,fun _ _ => ⟨by linarith,by linarith⟩⟩
    · rcases ih hJ' with ⟨hM,hL,_⟩
      have hx := z1t hJ'
      dsimp [z1e]; refine ⟨by linarith,by linarith,fun _ _ => ⟨by linarith,by linarith⟩⟩
  | @pair1 m _ _ _ _ hI ih =>
    intro z hZ
    rcases zTo hZ with ⟨y,hJ,rfl⟩
    rcases zTo hJ with ⟨x,hJ',rfl⟩
    rcases (ih hJ').2.2 m rfl with ⟨hM,hL⟩
    have hx := z1t hJ'
    dsimp [z1e]; refine ⟨by linarith,by linarith,fun _ _ => ⟨by linarith,by linarith⟩⟩
  | @short00 m _ _ _ _ hI ih =>
    intro z hZ
    rcases z1u hZ with ⟨rfl,rfl⟩ | ⟨x,hJ,rfl⟩
    · generalize hk : m * 2 = k at hI
      cases hI
      dsimp [z1e]; refine ⟨by linarith,by linarith,fun _ h => by omega⟩
    · rcases ih hJ with ⟨hM,hL,_⟩
      dsimp [z1e]; refine ⟨by linarith,by linarith,fun _ h => by omega⟩
  | @short01 m _ _ _ _ _ ih =>
    intro z hZ
    rcases zTo hZ with ⟨x,hJ,rfl⟩
    rcases (ih hJ).2.2 m rfl with ⟨hM,hL⟩
    dsimp [z1e]; refine ⟨by linarith,by linarith,fun _ h => by omega⟩
  | @short10 m _ _ _ _ hI ih =>
    intro z hZ
    rcases z1u hZ with ⟨rfl,rfl⟩ | ⟨x,hJ,rfl⟩
    · generalize hk : m * 2 = k at hI
      cases hI
      dsimp [z1e]; refine ⟨by linarith,by linarith,fun _ h => by omega⟩
    · rcases ih hJ with ⟨hM,hL,_⟩
      dsimp [z1e]; refine ⟨by linarith,by linarith,fun _ h => by omega⟩
  | @short11 m _ _ _ _ _ ih =>
    intro z hZ
    rcases zTo hZ with ⟨x,hJ,rfl⟩
    rcases (ih hJ).2.2 m rfl with ⟨hM,hL⟩
    dsimp [z1e]; refine ⟨by linarith,by linarith,fun _ h => by omega⟩
lemma z1y {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (h1 : Scan a u b v l) :
    ∀ {w : zW} {c : Nat} {x : zW} {m : Rat},
      Scan b w c x m -> ∃ p,Scan a (u ++ w) c (v ++ x) p /\ p = l + z1h v * m := by
  induction h1 with
  | nil _ =>
    intro w c x m h2
    exact ⟨m,h2,by simp [z1h]⟩
  | T _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p,hK,hE⟩
    exact ⟨p * (1 / 2),Scan.T hK,by dsimp [z1h]; rw [hE]; ring⟩
  | pair0 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p,hK,hE⟩
    exact ⟨(1 + p) * (1 / 2),Scan.pair0 hK,by dsimp [z1h]; rw [hE]; ring⟩
  | pair1 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p,hK,hE⟩
    exact ⟨(1 / 4) + p * (1 / 2),Scan.pair1 hK,by dsimp [z1h]; rw [hE]; ring⟩
  | short00 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p,hK,hE⟩
    exact ⟨1 + p * 2,Scan.short00 hK,by dsimp [z1h]; rw [hE]; ring⟩
  | short01 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p,hK,hE⟩
    exact ⟨p * 2,Scan.short01 hK,by dsimp [z1h]; rw [hE]; ring⟩
  | short10 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p,hK,hE⟩
    exact ⟨1 + p * 2,Scan.short10 hK,by dsimp [z1h]; rw [hE]; ring⟩
  | short11 _ ih =>
    intro w c x m h2
    rcases ih h2 with ⟨p,hK,hE⟩
    exact ⟨p * 2,Scan.short11 hK,by dsimp [z1h]; rw [hE]; ring⟩
lemma z1z {a : Nat} {u : zW} {c : Nat} {z : zW} {l : Rat}
    (h : Scan a u c z l) :
    ∀ (p q : zW),u = p ++ q -> z10 p q ->
      ∃ b v w x y,Scan a p b v x /\ Scan b q c w y /\ z = v ++ w /\ l = x + z1h v * y := by
  induction h with
  | nil k =>
    intro p q hE _
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨k,[],[],0,0,Scan.nil k,Scan.nil k,rfl,by simp [z1h]⟩
    | cons s p => simp at hE
  | T hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.T hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt V p q hP) with ⟨b,v0,w,x,y,hJ,hK,rfl,hL⟩
      exact ⟨b,V :: v0,w,x * (1 / 2),y,Scan.T hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | pair0 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.pair0 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := zCt K p q (zCt Q (K :: p) q hP)
        rcases ih p q hE hP' with ⟨b,v0,w,x,y,hJ,hK,rfl,hL⟩
        exact ⟨b,V :: v0,w,(1 + x) * (1 / 2),y,Scan.pair0 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | pair1 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.pair1 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := zCt Q p q (zCt Q (Q :: p) q hP)
        rcases ih p q hE hP' with ⟨b,v0,w,x,y,hJ,hK,rfl,hL⟩
        exact ⟨b,V :: v0,w,(1 / 4) + x * (1 / 2),y,Scan.pair1 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | short00 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short00 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt K p q hP) with ⟨b,v0,w,x,y,hJ,hK,rfl,hL⟩
      exact ⟨b,K :: v0,w,1 + x * 2,y,Scan.short00 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | short01 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short01 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt Q p q hP) with ⟨b,v0,w,x,y,hJ,hK,rfl,hL⟩
      exact ⟨b,K :: v0,w,x * 2,y,Scan.short01 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | short10 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short10 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt K p q hP) with ⟨b,v0,w,x,y,hJ,hK,rfl,hL⟩
      exact ⟨b,Q :: v0,w,1 + x * 2,y,Scan.short10 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
  | short11 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,_,Scan.nil _,Scan.short11 hI,rfl,by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt Q p q hP) with ⟨b,v0,w,x,y,hJ,hK,rfl,hL⟩
      exact ⟨b,Q :: v0,w,x * 2,y,Scan.short11 hJ,hK,rfl,by dsimp [z1h]; rw [hL]; ring⟩
lemma z1A {a : Nat} {u : zW} {b : Nat} {v : zW} {l : Rat}
    (h : Scan a u b v l) :
    ∃ g : Nat,z1h u = z1h v * ((8 ^ g : Nat) : Rat) := by
  induction h with
  | nil _ => exact ⟨0,by simp [z1h]⟩
  | T _ ih =>
    rcases ih with ⟨g,hE⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring⟩
  | pair0 _ ih =>
    rcases ih with ⟨g,hE⟩
    refine ⟨g + 1,?_⟩
    rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]; dsimp [z1h]; rw [hE]; ring
  | pair1 _ ih =>
    rcases ih with ⟨g,hE⟩
    refine ⟨g + 1,?_⟩
    rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]; dsimp [z1h]; rw [hE]; ring
  | short00 _ ih =>
    rcases ih with ⟨g,hE⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring⟩
  | short01 _ ih =>
    rcases ih with ⟨g,hE⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring⟩
  | short10 _ ih =>
    rcases ih with ⟨g,hE⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring⟩
  | short11 _ ih =>
    rcases ih with ⟨g,hE⟩
    exact ⟨g,by dsimp [z1h]; rw [hE]; ring⟩
inductive zEf : Nat -> zW -> Nat -> zW -> Prop where
  | nil (n : Nat) : zEf n [] n []
  | T {n : Nat} {u : zW} {b : Nat} {v : zW} :
      zEf (1 + n * 2) u b v -> zEf n (V :: u) b (V :: v)
  | d00 {n : Nat} {u : zW} {b : Nat} {v : zW} :
      zEf n u b v -> zEf (n * 2) (K :: u) b (K :: v)
  | d01 {n : Nat} {u : zW} {b : Nat} {v : zW} :
      zEf n u b v -> zEf (1 + n * 2) (K :: u) b (Q :: v)
  | d10 {n : Nat} {u : zW} {b : Nat} {v : zW} :
      zEf n u b v -> zEf (n * 2) (Q :: u) b (Q :: v)
  | d11 {n : Nat} {u : zW} {b : Nat} {v : zW} :
      zEf (1 + n) u b v -> zEf (1 + n * 2) (Q :: u) b (K :: v)
def forceNat (e : Nat) (f : Nat -> α) : α :=
  Nat.casesOn (e + 1) (f 0) (fun n => f n)

@[scoped simp] lemma forceNat_eq (e : Nat) (f : Nat -> α) : forceNat e f = f e := rfl

def forceWord (w : Word) (f : Word -> α) : α :=
  Word.casesOn w (f V) (f K) (f Q)

@[scoped simp] lemma forceWord_eq (w : Word) (f : Word -> α) : forceWord w f = f w := by
  cases w <;> rfl

def forceProd (p : α × β) (f : α -> β -> γ) : γ :=
  Prod.casesOn p f

@[scoped simp] lemma forceProd_eq (p : α × β) (f : α -> β -> γ) : forceProd p f = f p.1 p.2 := by
  cases p; rfl

def with_zw (u : zW) (f : zW -> α) : α :=
  match u with
  | [] => f []
  | w :: ws => forceWord w (fun w' => with_zw ws (fun ws' => f (w' :: ws')))

@[scoped simp] lemma with_zw_eq (u : zW) (f : zW -> α) : with_zw u f = f u := by
  induction u generalizing f with
  | nil => rfl
  | cons w ws ih => simp [with_zw, ih]

def zEe : Nat -> zW -> Nat × zW
  | n,[] => (n,[])
  | n,V :: u =>
    forceNat (1 + n * 2) (fun m =>
      forceProd (zEe m u) (fun r1 r2 => (r1,V :: r2)))
  | n,K :: u =>
    forceNat (n / 2) (fun m =>
      forceWord (if n % 2 == 0 then K else Q) (fun w =>
        forceProd (zEe m u) (fun r1 r2 => (r1,w :: r2))))
  | n,Q :: u =>
    forceNat (if n % 2 == 0 then n / 2 else 1 + n / 2) (fun m =>
      forceWord (if n % 2 == 0 then Q else K) (fun w =>
        forceProd (zEe m u) (fun r1 r2 => (r1,w :: r2))))
lemma zEs (u : zW) :
    ∀ (n : Nat),zEf n u (zEe n u).1 (zEe n u).2 := by
  induction u with
  | nil => intro n; exact zEf.nil n
  | cons w u ih =>
    intro n
    cases w with
    | V =>
      dsimp [zEe]
      exact zEf.T (ih (1 + n * 2))
    | K =>
      dsimp [zEe]
      rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
      · have hcond : (n % 2 == 0) = true := beq_iff_eq.mpr hmod
        rw [hcond]; dsimp
        have h1 := zEf.d00 (ih (n / 2))
        have heq : (n / 2) * 2 = n := by omega
        rwa [heq] at h1
      · have hcond : (n % 2 == 0) = false := beq_false_of_ne (by omega)
        rw [hcond]; dsimp
        have h1 := zEf.d01 (ih (n / 2))
        have heq : 1 + (n / 2) * 2 = n := by omega
        rwa [heq] at h1
    | Q =>
      dsimp [zEe]
      rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
      · have hcond : (n % 2 == 0) = true := beq_iff_eq.mpr hmod
        rw [hcond]; dsimp
        have h1 := zEf.d10 (ih (n / 2))
        have heq : (n / 2) * 2 = n := by omega
        rwa [heq] at h1
      · have hcond : (n % 2 == 0) = false := beq_false_of_ne (by omega)
        rw [hcond]; dsimp
        have h1 := zEf.d11 (ih (1 + n / 2))
        have heq : 1 + (n / 2) * 2 = n := by omega
        rwa [heq] at h1
lemma z1B (u : zW) (n : Nat) : ∃ b v,zEf n u b v :=
  ⟨(zEe n u).1,(zEe n u).2,zEs u n⟩
lemma z1C {n : Nat} {u : zW} {b1 : Nat} {v1 : zW}
    (h1 : zEf n u b1 v1) :
    ∀ {b2 : Nat} {v2 : zW},zEf n u b2 v2 -> b1 = b2 /\ v1 = v2 := by
  induction h1 with
  | nil n =>
    intro b2 v2 h2; cases h2; exact ⟨rfl,rfl⟩
  | T _ ih =>
    intro b2 v2 h2
    cases h2 with
    | T h2' =>
      rcases ih h2' with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
  | @d00 n _ _ _ _ ih =>
    intro b2 v2 h2
    generalize hk : n * 2 = k at h2
    cases h2 with
    | @d00 m _ _ _ h2' =>
      have hnm : n = m := by omega
      subst hnm
      rcases ih h2' with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
    | d01 _ => omega
  | @d01 n _ _ _ _ ih =>
    intro b2 v2 h2
    generalize hk : 1 + n * 2 = k at h2
    cases h2 with
    | d00 _ => omega
    | @d01 m _ _ _ h2' =>
      have hnm : n = m := by omega
      subst hnm
      rcases ih h2' with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
  | @d10 n _ _ _ _ ih =>
    intro b2 v2 h2
    generalize hk : n * 2 = k at h2
    cases h2 with
    | @d10 m _ _ _ h2' =>
      have hnm : n = m := by omega
      subst hnm
      rcases ih h2' with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
    | d11 _ => omega
  | @d11 n _ _ _ _ ih =>
    intro b2 v2 h2
    generalize hk : 1 + n * 2 = k at h2
    cases h2 with
    | d10 _ => omega
    | @d11 m _ _ _ h2' =>
      have hnm : n = m := by omega
      subst hnm
      rcases ih h2' with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
lemma z1D {n : Nat} {u : zW} {b : Nat} {v : zW}
    (h1 : zEf n u b v) :
    ∀ {w : zW} {c : Nat} {x : zW},
      zEf b w c x -> zEf n (u ++ w) c (v ++ x) := by
  induction h1 with
  | nil _ => intro w c x h2; exact h2
  | T _ ih => intro w c x h2; exact zEf.T (ih h2)
  | d00 _ ih => intro w c x h2; exact zEf.d00 (ih h2)
  | d01 _ ih => intro w c x h2; exact zEf.d01 (ih h2)
  | d10 _ ih => intro w c x h2; exact zEf.d10 (ih h2)
  | d11 _ ih => intro w c x h2; exact zEf.d11 (ih h2)
lemma z1E (u : zW) :
    ∀ {n : Nat} {w : zW} {b : Nat} {out : zW},
      zEf n (u ++ w) b out ->
      ∃ m v x,out = v ++ x /\ zEf n u m v /\ zEf m w b x := by
  induction u with
  | nil =>
    intro n w b out hE
    exact ⟨n,[],out,rfl,zEf.nil n,hE⟩
  | cons s u ih =>
    intro n w b out hE
    cases hE with
    | T hSub =>
      rcases ih hSub with ⟨m,v1,x,rfl,hA,hB⟩
      exact ⟨m,V :: v1,x,rfl,zEf.T hA,hB⟩
    | d00 hSub =>
      rcases ih hSub with ⟨m,v1,x,rfl,hA,hB⟩
      exact ⟨m,K :: v1,x,rfl,zEf.d00 hA,hB⟩
    | d01 hSub =>
      rcases ih hSub with ⟨m,v1,x,rfl,hA,hB⟩
      exact ⟨m,Q :: v1,x,rfl,zEf.d01 hA,hB⟩
    | d10 hSub =>
      rcases ih hSub with ⟨m,v1,x,rfl,hA,hB⟩
      exact ⟨m,Q :: v1,x,rfl,zEf.d10 hA,hB⟩
    | d11 hSub =>
      rcases ih hSub with ⟨m,v1,x,rfl,hA,hB⟩
      exact ⟨m,K :: v1,x,rfl,zEf.d11 hA,hB⟩
lemma z1F (v : zW) :
    ∀ {n : Nat} {u : zW} {c : Nat} {w : zW},
      zEf n u c (v ++ w) ->
      ∃ u1 u2 b,u = u1 ++ u2 /\ zEf n u1 b v /\ zEf b u2 c w := by
  induction v with
  | nil =>
    intro n u c w hE
    exact ⟨[],u,n,rfl,zEf.nil n,hE⟩
  | cons x v ih =>
    intro n u c w hE
    cases hE with
    | T hSub =>
      rcases ih hSub with ⟨u1,u2,b,rfl,hL,hR⟩
      exact ⟨V :: u1,u2,b,rfl,zEf.T hL,hR⟩
    | d00 hSub =>
      rcases ih hSub with ⟨u1,u2,b,rfl,hL,hR⟩
      exact ⟨K :: u1,u2,b,rfl,zEf.d00 hL,hR⟩
    | d01 hSub =>
      rcases ih hSub with ⟨u1,u2,b,rfl,hL,hR⟩
      exact ⟨K :: u1,u2,b,rfl,zEf.d01 hL,hR⟩
    | d10 hSub =>
      rcases ih hSub with ⟨u1,u2,b,rfl,hL,hR⟩
      exact ⟨Q :: u1,u2,b,rfl,zEf.d10 hL,hR⟩
    | d11 hSub =>
      rcases ih hSub with ⟨u1,u2,b,rfl,hL,hR⟩
      exact ⟨Q :: u1,u2,b,rfl,zEf.d11 hL,hR⟩
lemma z1G {n : Nat} {u : zW} {b : Nat} {v : zW}
    (hI : zEf n u b v) :
    ∀ {A H : Nat},zDg A H u -> ∃ B,zDg B H v /\ A + n = B + b * 2 ^ H := by
  induction hI with
  | nil n =>
    intro A H hD; cases hD
    exact ⟨0,zDg.nil,by simp⟩
  | T _ _ =>
    intro A H hD; exact False.elim (z0X hD)
  | @d00 n _ b _ _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A',H',hD',rfl,rfl⟩
    rcases ih hD' with ⟨B,hBv,hEq⟩
    refine ⟨B * 2,zDg.zero hBv,?_⟩
    rw [zP2,Nat.mul_add]; omega
  | @d01 n _ b _ _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A',H',hD',rfl,rfl⟩
    rcases ih hD' with ⟨B,hBv,hEq⟩
    refine ⟨1 + B * 2,zDg.one hBv,?_⟩
    rw [zP2,Nat.mul_add]; omega
  | @d10 n _ b _ _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A',H',hD',rfl,rfl⟩
    rcases ih hD' with ⟨B,hBv,hEq⟩
    refine ⟨1 + B * 2,zDg.one hBv,?_⟩
    rw [zP2,Nat.mul_add]; omega
  | @d11 n _ b _ _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A',H',hD',rfl,rfl⟩
    rcases ih hD' with ⟨B,hBv,hEq⟩
    refine ⟨B * 2,zDg.zero hBv,?_⟩
    rw [zP2,Nat.mul_add]; omega
lemma z1H {n : Nat} {ds : zW} {A H B : Nat}
    (hD : zDg A H ds) (hSum : A + n = B) (hBound : B < 2 ^ H) :
    ∃ v,zDg B H v /\ zEf n ds 0 v := by
  rcases z1B ds n with ⟨b,v,hE⟩
  rcases z1G hE hD with ⟨C,hV,hEq⟩
  have hCb := z1b hV
  have hb0 : b = 0 := by
    cases b with
    | zero => rfl
    | succ b' =>
      have : 1 * 2 ^ H <= (b' + 1) * 2 ^ H := Nat.mul_le_mul_right (2 ^ H) (by omega)
      omega
  subst hb0
  have hCB : C = B := by omega
  subst hCB
  exact ⟨v,hV,hE⟩
lemma z1I {n : Nat} {u : zW} {b : Nat} {v : zW}
    (hI : zEf n u b v) :
    z1h v = z1h u /\ z1e v = z1e u := by
  induction hI with
  | nil _ => simp [z1h,z1e]
  | T _ ih => dsimp [z1h,z1e]; constructor <;> linarith
  | d00 _ ih => dsimp [z1h,z1e]; constructor <;> linarith
  | d01 _ ih => dsimp [z1h,z1e]; constructor <;> linarith
  | d10 _ ih => dsimp [z1h,z1e]; constructor <;> linarith
  | d11 _ ih => dsimp [z1h,z1e]; constructor <;> linarith
lemma z1J {n : Nat} {u : zW} {b : Nat} {v : zW}
    (hI : zEf n u b v) :
    ((1 + b : Nat) : Rat) * z1h u = ((1 + n : Nat) : Rat) + z1e u + z1g u - z1g v := by
  induction hI with
  | nil _ => simp [z1h,z1e,z1g]
  | T _ ih => dsimp [z1h,z1e,z1g]; push_cast at ih ⊢; linarith
  | d00 _ ih => dsimp [z1h,z1e,z1g]; push_cast at ih ⊢; linarith
  | d01 _ ih => dsimp [z1h,z1e,z1g]; push_cast at ih ⊢; linarith
  | d10 _ ih => dsimp [z1h,z1e,z1g]; push_cast at ih ⊢; linarith
  | d11 _ ih => dsimp [z1h,z1e,z1g]; push_cast at ih ⊢; linarith
lemma z1K (p : Nat) :
    ∀ (n b : Nat) (v : zW),
      zEf n (zR p V) b v ->
      v = zR p V /\ 1 + b = (1 + n) * 2 ^ p := by
  induction p with
  | zero =>
    intro n b v hI
    cases hI
    exact ⟨rfl,by simp⟩
  | succ p ih =>
    intro n b v hI
    cases hI with
    | T hSub =>
      rcases ih (1 + n * 2) b _ hSub with ⟨rfl,hEq⟩
      refine ⟨rfl,?_⟩
      rw [Nat.pow_succ]; ring_nf at hEq ⊢; omega
lemma z1L (u : zW) :
    ∀ (p n b : Nat) (v : zW),
      zEf n (u ++ zR p V) b v ->
      ∃ w q,v = w ++ zR p V /\ 1 + b = q * 2 ^ p := by
  induction u with
  | nil =>
    intro p n b v hI
    rcases z1K p n b v hI with ⟨rfl,hEq⟩
    exact ⟨[],1 + n,rfl,hEq⟩
  | cons x u ih =>
    intro p n b v hI
    cases hI with
    | T hSub =>
      rcases ih p (1 + n * 2) b _ hSub with ⟨w,q,rfl,hEq⟩
      exact ⟨V :: w,q,rfl,hEq⟩
    | d00 hSub =>
      rcases ih p _ b _ hSub with ⟨w,q,rfl,hEq⟩
      exact ⟨K :: w,q,rfl,hEq⟩
    | d01 hSub =>
      rcases ih p _ b _ hSub with ⟨w,q,rfl,hEq⟩
      exact ⟨Q :: w,q,rfl,hEq⟩
    | d10 hSub =>
      rcases ih p _ b _ hSub with ⟨w,q,rfl,hEq⟩
      exact ⟨Q :: w,q,rfl,hEq⟩
    | d11 hSub =>
      rcases ih p _ b _ hSub with ⟨w,q,rfl,hEq⟩
      exact ⟨K :: w,q,rfl,hEq⟩

end BusyBeaver.WordCalculus
