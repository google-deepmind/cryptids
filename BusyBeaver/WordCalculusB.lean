module

public import BusyBeaver.WordCalculusA
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
inductive zPS : Nat -> zW -> Nat -> zW -> Rat -> Rat -> Prop where
  | nil (k : Nat) : zPS k [] k [] 0 0
  | T {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      zPS (2 + n * 2) u k v a b -> zPS (3 + n) (V :: u) k (V :: v) (a * (1 / 2)) (b * (1 / 2))
  | pair0 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      zPS (n * 2) u k v a b -> zPS (1 + n) (Q :: K :: u) k (V :: v) (a * (1 / 2)) ((1 + b) * (1 / 2))
  | pair1 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      zPS (1 + n * 2) u k v a b -> zPS (1 + n) (Q :: Q :: u) k (V :: v) (a * (1 / 2)) ((3 / 4) + b * (1 / 2))
  | short00 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      zPS (n * 2) u k v a b -> zPS (2 + n * 4) (K :: u) k (K :: v) (3 + a * 2) (b * 2)
  | short01 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      zPS (1 + n * 2) u k v a b -> zPS (2 + n * 4) (Q :: u) k (K :: v) (2 + a * 2) (b * 2)
  | short10 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      zPS (n * 2) u k v a b -> zPS (4 + n * 4) (K :: u) k (Q :: v) (4 + a * 2) (b * 2)
  | short11 {n : Nat} {u : zW} {k : Nat} {v : zW} {a b : Rat} :
      zPS (1 + n * 2) u k v a b -> zPS (4 + n * 4) (Q :: u) k (Q :: v) (3 + a * 2) (b * 2)
lemma z1M {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : zPS k u k' v a b) (hk' : 0 < k') : 0 < k := by
  cases h <;> omega
lemma z1N {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : zPS k u k' v a b) :
    (k : Rat) - 4 = ((k' : Rat) - 4) * z1h v + 2 * (a - b) := by
  induction h with
  | nil k => simp [z1h]
  | T _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | pair0 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | pair1 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short00 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short01 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short10 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
  | short11 _ ih => dsimp [z1h]; push_cast at ih ⊢; linarith
lemma z1O {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : zPS k u k' v a b) :
    z1e v <= z1e u /\ 0 <= a /\ a <= 4 * z1e u /\ 0 <= b /\ b <= z1e u * (1 / 4) := by
  induction h with
  | nil _ => simp [z1e]
  | @T n u k v a b _ ih =>
    have hw := zWn u
    dsimp [z1e]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @pair0 n u k v a b _ ih =>
    have hw := zWn u
    dsimp [z1e]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @pair1 n u k v a b _ ih =>
    have hw := zWn u
    dsimp [z1e]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @short00 n u k v a b _ ih =>
    have hw := zWn u
    dsimp [z1e]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @short01 n u k v a b _ ih =>
    have hw := zWn u
    dsimp [z1e]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @short10 n u k v a b _ ih =>
    have hw := zWn u
    dsimp [z1e]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  | @short11 n u k v a b _ ih =>
    have hw := zWn u
    dsimp [z1e]; refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
lemma z1P {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h1 : zPS k u k' v a b) :
    ∀ {w : zW} {k'' : Nat} {x : zW} {c d : Rat},
      zPS k' w k'' x c d ->
      ∃ a' b',zPS k (u ++ w) k'' (v ++ x) a' b' /\
        a' = a + z1h v * c /\ b' = b + z1h v * d := by
  induction h1 with
  | nil _ =>
    intro w k'' x c d h2
    exact ⟨c,d,h2,by simp [z1h],by simp [z1h]⟩
  | T _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨a' * (1 / 2),b' * (1 / 2),zPS.T hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | pair0 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨a' * (1 / 2),(1 + b') * (1 / 2),zPS.pair0 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | pair1 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨a' * (1 / 2),(3 / 4) + b' * (1 / 2),zPS.pair1 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short00 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨3 + a' * 2,b' * 2,zPS.short00 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short01 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨2 + a' * 2,b' * 2,zPS.short01 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short10 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨4 + a' * 2,b' * 2,zPS.short10 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
  | short11 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a',b',hK,hA,hB⟩
    exact ⟨3 + a' * 2,b' * 2,zPS.short11 hK,by dsimp [z1h]; linarith,by dsimp [z1h]; linarith⟩
lemma z1Q {e : Bool} {u : zW} (hI : zPr e u) :
    ∀ (k : Nat),(e = true -> ∃ n,k = n * 2) ->
      8 * z1e u < (k : Rat) - 4 ->
      ∃ b v lp lm,zPS k u b v lp lm /\ 4 < b := by
  induction hI with
  | nil e =>
    intro k _ hk
    dsimp [z1e] at hk
    have hk_gt : (4 : Rat) < (k : Rat) := by linarith
    have hk_nat : 4 < k := by exact_mod_cast hk_gt
    exact ⟨k,[],0,0,zPS.nil k,hk_nat⟩
  | @T e u _ ih =>
    intro k _ hk
    have hw := zWn u
    dsimp [z1e] at hk
    rcases k with _ | _ | _ | k
    · push_cast at hk; linarith
    · push_cast at hk; linarith
    · push_cast at hk; linarith
    · have h3k : k + 3 = 3 + k := by omega
      rw [h3k] at hk ⊢
      rcases ih (2 + k * 2) (fun _ => ⟨1 + k,by omega⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      exact ⟨b,V :: v,lp * (1 / 2),lm * (1 / 2),zPS.T hS,hB⟩
  | @short0 u _ ih =>
    intro k hEk hk
    have hw := zWn u
    dsimp [z1e] at hk
    rcases hEk rfl with ⟨n,rfl⟩
    rcases z0U n with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (a * 2) (fun _ => ⟨a,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
        refine ⟨b,Q :: v,4 + lp * 2,lm * 2,?_,hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact zPS.short10 hS
    · rcases ih (a * 2) (fun _ => ⟨a,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      refine ⟨b,K :: v,3 + lp * 2,lm * 2,?_,hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact zPS.short00 hS
  | @short1 u _ ih =>
    intro k hEk hk
    have hw := zWn u
    dsimp [z1e] at hk
    rcases hEk rfl with ⟨n,rfl⟩
    rcases z0U n with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (1 + a * 2) (fun h => by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
        refine ⟨b,Q :: v,3 + lp * 2,lm * 2,?_,hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact zPS.short11 hS
    · rcases ih (1 + a * 2) (fun h => by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      refine ⟨b,K :: v,2 + lp * 2,lm * 2,?_,hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact zPS.short01 hS
  | @pair0 e u _ ih =>
    intro k _ hk
    have hw := zWn u
    dsimp [z1e] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (k * 2) (fun _ => ⟨k,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      exact ⟨b,V :: v,lp * (1 / 2),(1 + lm) * (1 / 2),zPS.pair0 hS,hB⟩
  | @pair1 e u _ ih =>
    intro k _ hk
    have hw := zWn u
    dsimp [z1e] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (1 + k * 2) (fun h => by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      exact ⟨b,V :: v,lp * (1 / 2),(3 / 4) + lm * (1 / 2),zPS.pair1 hS,hB⟩
lemma z1R (u : zW) (k : Nat) (h : 8 * z1e u < ((k * 2 : Nat) : Rat) - 4) :
    ∃ b v lp lm,zPS (k * 2) u b v lp lm /\ 4 < b :=
  z1Q (z0W u).1 (k * 2) (fun _ => ⟨k,rfl⟩) h
lemma z1S {k : Nat} {u : zW} {k' : Nat} {v : zW} {l : Rat}
    (hI : Scan k u k' v l) :
    ∀ {A H : Nat},zDg A H u ->
      ∃ a b,zPS k u k' v a b /\ a <= 3 * z1e v + l /\ b <= 3 * l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0,0,zPS.nil k,by simp [z1e],by linarith⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (z0X hD)
  | pair0 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD0 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨a * (1 / 2),(1 + b) * (1 / 2),zPS.pair0 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD1 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨a * (1 / 2),(3 / 4) + b * (1 / 2),zPS.pair1 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨3 + a * 2,b * 2,zPS.short00 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨2 + a * 2,b * 2,zPS.short01 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨4 + a * 2,b * 2,zPS.short10 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨3 + a * 2,b * 2,zPS.short11 hJ,by dsimp [z1e]; linarith,by linarith⟩
lemma z1T {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k u k' v a b) :
    ∀ {A H : Nat},zDg A H u ->
      ∃ l,Scan k u k' v l /\ a <= 3 * z1e v + l /\ b <= 3 * l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0,Scan.nil k,by simp [z1e],by linarith⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (z0X hD)
  | pair0 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD0 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hP,hM⟩
    exact ⟨(1 + l) * (1 / 2),Scan.pair0 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases zD1 hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hP,hM⟩
    exact ⟨(1 / 4) + l * (1 / 2),Scan.pair1 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨1 + l * 2,Scan.short00 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨l * 2,Scan.short01 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases zD0 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨1 + l * 2,Scan.short10 hJ,by dsimp [z1e]; linarith,by linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases zD1 hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨l * 2,Scan.short11 hJ,by dsimp [z1e]; linarith,by linarith⟩
lemma z1U {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k u k' v a b) {z : Rat} (hD : zTd u z) :
    z1e v <= 1 + 2 * z /\ a <= 4 * (1 + 2 * z) /\ b <= 3 * (1 + 2 * z) := by
  rcases z1w hD with ⟨A,H,hB⟩
  rcases z1T hI hB with ⟨l,hJ,hP,hM⟩
  rcases z1x hJ hD with ⟨hMv,hLv,_⟩
  refine ⟨by linarith,by linarith,by linarith⟩
lemma z1V {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : zPS k u k' v a b) : z1h v <= z1h u := by
  induction h with
  | nil _ => simp [z1h]
  | T _ ih => dsimp [z1h]; linarith
  | @pair0 _ u _ _ _ _ _ _ => have hp := zSp u; dsimp [z1h]; linarith
  | @pair1 _ u _ _ _ _ _ _ => have hp := zSp u; dsimp [z1h]; linarith
  | short00 _ ih => dsimp [z1h]; linarith
  | short01 _ ih => dsimp [z1h]; linarith
  | short10 _ ih => dsimp [z1h]; linarith
  | short11 _ ih => dsimp [z1h]; linarith
lemma z1W (u : zW) (z : Rat) (k : Nat)
    (hD : zTd u z)
    (hBudget : 2 * (z1e u + z1f u) < ((k * 2 : Nat) : Rat))
    (hLoss : 8 * (1 + 2 * z) < ((k * 2 : Nat) : Rat) - 4) :
    ∃ k' v a b,zPS (k * 2) u k' v a b /\ 4 < k' := by
  have hEx : (z1e u + z1f u) * 2 < ((k * 2 : Nat) : Rat) := by linarith
  rcases z1q u k hEx with ⟨k',v,l,hI,_⟩
  rcases z1w hD with ⟨A,H,hB⟩
  rcases z1S hI hB with ⟨a,b,hJ,_,_⟩
  refine ⟨k',v,a,b,hJ,?_⟩
  have hTB := z1U hJ hD
  have hBud := z1N hJ
  have hBnd := z1O hJ
  have hSv := zSp v
  have hk'_gt : (4 : Rat) < (k' : Rat) := by
    have h1 : 2 * (a - b) <= 8 * (1 + 2 * z) := by linarith
    have h2 : 0 < ((k' : Rat) - 4) * z1h v := by linarith
    nlinarith
  exact_mod_cast hk'_gt
lemma z1X {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (hI : zPS k u k' v a b) :
    z0Z u = true -> u ≠ [] -> ∃ n,k' = n * 2 := by
  induction hI with
  | nil _ => intro _ hNe; exact False.elim (hNe rfl)
  | @T n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => generalize hk : 2 + n * 2 = k0 at hSub; cases hSub; exact ⟨1 + n,by omega⟩
    | cons x u' => exact ih (zCo V (x :: u') hC) (by simp)
  | @pair0 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => generalize hk : n * 2 = k0 at hSub; cases hSub; exact ⟨n,by omega⟩
    | cons x u' =>
      have hC1 := zCo Q (K :: x :: u') hC
      have hC2 := zCo K (x :: u') hC1
      exact ih hC2 (by simp)
  | @pair1 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => contradiction
    | cons x u' =>
      have hC1 := zCo Q (Q :: x :: u') hC
      have hC2 := zCo Q (x :: u') hC1
      exact ih hC2 (by simp)
  | @short00 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => generalize hk : n * 2 = k0 at hSub; cases hSub; exact ⟨n,by omega⟩
    | cons x u' => exact ih (zCo K (x :: u') hC) (by simp)
  | @short01 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => contradiction
    | cons x u' => exact ih (zCo Q (x :: u') hC) (by simp)
  | @short10 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => generalize hk : n * 2 = k0 at hSub; cases hSub; exact ⟨n,by omega⟩
    | cons x u' => exact ih (zCo K (x :: u') hC) (by simp)
  | @short11 n u _ _ _ _ hSub ih =>
    intro hC _
    cases u with
    | nil => contradiction
    | cons x u' => exact ih (zCo Q (x :: u') hC) (by simp)
lemma z1Y {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : zPS k u k' v a b) :
    ∀ (p q : zW),u = p ++ q -> z10 p q ->
      ∃ m x y a1 b1 a2 b2,zPS k p m x a1 b1 /\ zPS m q k' y a2 b2 /\
        v = x ++ y /\ a = a1 + z1h x * a2 /\ b = b1 + z1h x * b2 := by
  induction h with
  | nil k =>
    intro p q hE _
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨k,[],[],0,0,0,0,zPS.nil k,zPS.nil k,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p => simp at hE
  | T hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,zPS.nil _,zPS.T hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt V p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,V :: x,y,a1 * (1 / 2),b1 * (1 / 2),a2,b2,zPS.T hJ,hK,rfl,
        by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | pair0 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,zPS.nil _,zPS.pair0 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := zCt K p q (zCt Q (K :: p) q hP)
        rcases ih p q hE hP' with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
        exact ⟨m,V :: x,y,a1 * (1 / 2),(1 + b1) * (1 / 2),a2,b2,zPS.pair0 hJ,hK,rfl,
          by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | pair1 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,zPS.nil _,zPS.pair1 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := zCt Q p q (zCt Q (Q :: p) q hP)
        rcases ih p q hE hP' with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
        exact ⟨m,V :: x,y,a1 * (1 / 2),(3 / 4) + b1 * (1 / 2),a2,b2,zPS.pair1 hJ,hK,rfl,
          by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | short00 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,zPS.nil _,zPS.short00 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt K p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,K :: x,y,3 + a1 * 2,b1 * 2,a2,b2,zPS.short00 hJ,hK,rfl,
        by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | short01 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,zPS.nil _,zPS.short01 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt Q p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,K :: x,y,2 + a1 * 2,b1 * 2,a2,b2,zPS.short01 hJ,hK,rfl,
        by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | short10 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,zPS.nil _,zPS.short10 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt K p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,Q :: x,y,4 + a1 * 2,b1 * 2,a2,b2,zPS.short10 hJ,hK,rfl,
        by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
  | short11 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,zPS.nil _,zPS.short11 hI,rfl,by simp [z1h],by simp [z1h]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (zCt Q p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,Q :: x,y,3 + a1 * 2,b1 * 2,a2,b2,zPS.short11 hJ,hK,rfl,
        by dsimp [z1h]; rw [hA]; ring,by dsimp [z1h]; rw [hB]; ring⟩
lemma z1Z (r k : Nat) (u : zW) (k' : Nat) (v : zW) (a b : Rat)
    (hI : zPS k (u ++ zR (1 + r * 2) Q ++ [K]) k' v a b) :
    ∃ w n,v = w ++ zR (1 + r) V /\ k' = n * 2 ^ (1 + r) := by
  rcases z14 u with ⟨p,n,rfl,hP⟩
  have hE : (p ++ zR n Q) ++ zR (1 + r * 2) Q ++ [K] =
      p ++ (zR (1 + r * 2 + n) Q ++ [K]) := by
    have heq : 1 + r * 2 + n = n + (1 + r * 2) := by omega
    rw [heq,List.replicate_add n (1 + r * 2)]; simp only [List.append_assoc]
  rw [hE] at hI
  rcases z1Y hI p (zR (1 + r * 2 + n) Q ++ [K]) rfl (Or.inl hP)
    with ⟨m,x,y,_,_,_,_,_,hK,rfl,_,_⟩
  have hD : zDg ((2 ^ (1 + r * 2 + n) - 1) + 0 * 2 ^ (1 + r * 2 + n)) ((1 + r * 2 + n) + 1)
      (zR (1 + r * 2 + n) Q ++ [K]) :=
    z19 (z1a (1 + r * 2 + n)) (zDg.zero zDg.nil)
  rcases z1T hK hD with ⟨l,hL,_,_⟩
  rcases z1s n r m k' y l hL with ⟨w,q,rfl,rfl⟩
  exact ⟨x ++ w,q,by rw [List.append_assoc],rfl⟩
lemma z20 (p : Nat) :
    ∀ (k k' : Nat) (v : zW) (a b : Rat),
      zPS k (zR p V) k' v a b ->
      v = zR p V /\ k' + 4 * 2 ^ p = k * 2 ^ p + 4 /\ a = 0 /\ b = 0 := by
  induction p with
  | zero =>
    intro k k' v a b hI
    cases hI
    exact ⟨rfl,by simp,rfl,rfl⟩
  | succ p ih =>
    intro k k' v a b hI
    cases hI with
    | @T n _ _ v0 a0 b0 hJ =>
      rcases ih (2 + n * 2) k' v0 a0 b0 hJ with ⟨rfl,hEq,rfl,rfl⟩
      refine ⟨rfl,?_,by ring,by ring⟩
      rw [Nat.pow_succ]; ring_nf at hEq ⊢; omega
lemma z21 (n t0 B : Nat) (ds : zW)
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
    omega
  have ha_lt : a < 2 ^ n := by
    have : (2 ^ t0 - 1) * 2 ^ n + 2 ^ n = 2 ^ n * 2 ^ t0 := by
      have h1 : (2 ^ t0 - 1) + 1 = 2 ^ t0 := by omega
      calc (2 ^ t0 - 1) * 2 ^ n + 2 ^ n
        _ = ((2 ^ t0 - 1) + 1) * 2 ^ n := by ring
        _ = 2 ^ t0 * 2 ^ n := by rw [h1]
        _ = 2 ^ n * 2 ^ t0 := by ring
    omega
  rcases z18 n a ha_lt with ⟨u,hU⟩
  refine ⟨u,z1d hD ?_⟩
  rw [<- hSum]
  exact z19 hU (z1a t0)
def zSw : zW -> zW -> Option (zW)
  | [],u => some u
  | V :: p,V :: u => zSw p u
  | K :: p,K :: u => zSw p u
  | Q :: p,Q :: u => zSw p u
  | _,_ => none
lemma z22 (p : zW) :
    ∀ (u v : zW),zSw p u = some v -> u = p ++ v := by
  induction p with
  | nil => intro u v h; injection h
  | cons w p ih =>
    intro u v h
    cases u with
    | nil => cases w <;> contradiction
    | cons x u =>
      cases w <;> cases x <;> try contradiction
      all_goals
        dsimp [zSw] at h
        rw [ih u v h]; rfl
def z23 : Word -> Bool
  | K => true
  | _ => false
lemma z24 (u : zW) (h : u.all z23 = true) :
    zTs u default = default := by
  induction u with
  | nil => rfl
  | cons w u ih =>
    cases w <;> try contradiction
    dsimp [List.all,z23] at h
    change d0 +> zTs u default = default
    rw [ih h]
    have h0 : (0 : Fin 2) >> (default : zB) = default := ListBlank.cons_head_tail default
    simp [d0, h0]
def z25 : Word -> Bool
  | V => false
  | _ => true
lemma z26 (ds : zW) (h : ds.all z25 = true) :
    ∃ A,zDg A ds.length ds := by
  induction ds with
  | nil => exact ⟨0,zDg.nil⟩
  | cons w ds ih =>
    cases w
    · contradiction
    · dsimp [List.all,z25] at h
      rcases ih h with ⟨A,hI⟩
      have heq : (K :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨A * 2,zDg.zero hI⟩
    · dsimp [List.all,z25] at h
      rcases ih h with ⟨A,hI⟩
      have heq : (Q :: ds).length = 1 + ds.length := by simp [Nat.add_comm]
      rw [heq]; exact ⟨1 + A * 2,zDg.one hI⟩
def z27 (e : Bool) (n : Nat) : Nat := if e then 1 + n * 2 else n * 2
def z28 (n : Nat) : Nat := (n + 1) / 2
lemma z29 (n : Nat) : n <= (z28 n) * 2 := by
  unfold z28; omega
lemma z2a (n : Nat) : (n : Rat) <= 2 * ((z28 n : Nat) : Rat) := by
  have h := z29 n
  have hq : (n : Rat) <= (((z28 n) * 2 : Nat) : Rat) := by exact_mod_cast h
  push_cast at hq
  linarith
def z2b (c0 c1 : Nat) : zW -> Nat -> Nat
  | [],n => n
  | V :: u,n => forceNat (z28 n) (fun m => z2b c0 c1 u m)
  | K :: u,n => forceNat (n * 2 + c0) (fun m => z2b c0 c1 u m)
  | Q :: u,n => forceNat (n * 2 + c1) (fun m => z2b c0 c1 u m)
lemma z2c (c0 c1 : Nat) (u : zW) :
    ∀ (n : Nat),
      (c0 : Rat) * z1f u.reverse + (c1 : Rat) * z1g u.reverse + z1h u.reverse * (n : Rat) <=
        ((z2b c0 c1 u n : Nat) : Rat) := by
  induction u with
  | nil =>
    intro n
    simp [z1f,z1g,z1h,z2b]
  | cons w u ih =>
    intro n
    have hsp := zSp u.reverse
    cases w
    · dsimp [z2b, forceNat_eq]
      rw [List.reverse_cons,z1k,z1l,z1m]
      dsimp [z1f,z1g,z1h]
      have hhu := z2a n
      have hih := ih (z28 n)
      nlinarith
    · dsimp [z2b, forceNat_eq]
      rw [List.reverse_cons,z1k,z1l,z1m]
      dsimp [z1f,z1g,z1h]
      have hih := ih (n * 2 + c0)
      push_cast at hih
      nlinarith
    · dsimp [z2b, forceNat_eq]
      rw [List.reverse_cons,z1k,z1l,z1m]
      dsimp [z1f,z1g,z1h]
      have hih := ih (n * 2 + c1)
      push_cast at hih
      nlinarith
lemma z2d (c0 c1 : Nat) (u : zW) (n : Nat) :
    (c0 : Rat) * z1f u + (c1 : Rat) * z1g u + z1h u * (n : Rat) <=
      ((z2b c0 c1 u.reverse n : Nat) : Rat) := by
  have h := z2c c0 c1 u.reverse n
  simpa [List.reverse_reverse] using h
def zHn : zW -> Nat -> Option Nat
  | [],h => some h
  | V :: u,h => zHn u (h + 1)
  | _ :: _,0 => none
  | _ :: u,h + 1 => zHn u h
lemma z2e (u : zW) :
    ∀ (h H : Nat),zHn u h = some H ->
      z1h u * ((2 ^ H : Nat) : Rat) = ((2 ^ h : Nat) : Rat) := by
  induction u with
  | nil =>
    intro h H hE
    injection hE with hE; subst hE
    simp [z1h]
  | cons w u ih =>
    intro h H hE
    cases w
    · dsimp [zHn,z1h] at hE ⊢
      have hih := ih (h + 1) H hE
      rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat] at hih
      linarith
    · cases h with
      | zero => contradiction
      | succ h =>
        dsimp [zHn,z1h] at hE ⊢
        have hih := ih h H hE
        rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]
        linarith
    · cases h with
      | zero => contradiction
      | succ h =>
        dsimp [zHn,z1h] at hE ⊢
        have hih := ih h H hE
        rw [Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]
        linarith
def z2f : zW -> zW -> Option (zW × zW)
  | [],_ => none
  | V :: u,ds => some (u.reverseAux [V],ds)
  | w :: u,ds => z2f u (w :: ds)
lemma z2g (u : zW) :
    ∀ (ds p tail : zW),z2f u ds = some (p,tail) ->
      ds.all z25 = true ->
      u.reverseAux ds = p ++ tail /\ tail.all z25 = true := by
  induction u with
  | nil => intro ds p tail hE _; contradiction
  | cons w u ih =>
    intro ds p tail hE hD
    cases w
    · dsimp [z2f] at hE
      injection hE with h1; injection h1 with h1 h2; subst h1; subst h2
      refine ⟨?_,hD⟩
      simp [List.reverseAux_eq]
    · dsimp [z2f] at hE
      have hD' : (K :: ds).all z25 = true := by simp [z25,hD]
      exact ih (K :: ds) p tail hE hD'
    · dsimp [z2f] at hE
      have hD' : (Q :: ds).all z25 = true := by simp [z25,hD]
      exact ih (Q :: ds) p tail hE hD'
def z2h (u : zW) : Option (zW × zW) :=
  z2f u.reverse []
lemma z2i (u p ds : zW) (hE : z2h u = some (p,ds)) :
    u = p ++ ds /\ ds.all z25 = true := by
  rcases z2g u.reverse [] p ds hE rfl with ⟨hU,hD⟩
  simp [List.reverseAux_eq] at hU
  exact ⟨hU,hD⟩
lemma z2j (n : Nat) (w : Word) : (zR n w).reverse = zR n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv_lhs => rw [z13,List.reverse_append,ih]
    rfl
def z2k : zW -> Bool
  | [] => true
  | K :: _ => true
  | V :: _ => false
  | Q :: u => !z2k u
def z2l (k : Nat) : Word :=
  if (k - 2) % 4 == 0 then K else Q
def z2m : Nat -> zW -> Nat -> Option (Nat × zW)
  | 0,_,_ => none
  | _ + 1,[],k => some (k,[])
  | fuel + 1,V :: u,k =>
    if k < 3 then none
    else forceNat (2 + (k - 3) * 2) (fun m => match z2m fuel u m with
    | none => none
    | some (k',v) => some (k',V :: v))
  | fuel + 1,K :: u,k =>
    if k < 2 || k % 2 != 0 then none
    else
      forceNat (((k - 2) / 4) * 2) (fun m => match z2m fuel u m with
      | none => none
      | some (k',v) => forceWord (z2l k) (fun w => some (k',w :: v)))
  | fuel + 1,Q :: u,k =>
    if k == 0 then none
    else if k % 2 == 0 && z2k (Q :: u) then
      forceNat (1 + ((k - 2) / 4) * 2) (fun m => match z2m fuel u m with
      | none => none
      | some (k',v) => forceWord (z2l k) (fun w => some (k',w :: v)))
    else match u with
    | K :: u' =>
      forceNat ((k - 1) * 2) (fun m => match z2m fuel u' m with
      | none => none
      | some (k',v) => some (k',V :: v))
    | Q :: u' =>
      forceNat (1 + (k - 1) * 2) (fun m => match z2m fuel u' m with
      | none => none
      | some (k',v) => some (k',V :: v))
    | _ => none
lemma z2n (fuel : Nat) :
    ∀ (u : zW) (k k' : Nat) (v : zW),
      z2m fuel u k = some (k',v) ->
      ∃ a b,zPS k u k' v a b := by
  induction fuel with
  | zero => intro u k k' v h; contradiction
  | succ fuel ih =>
    intro u k k' v h
    cases u with
    | nil =>
      dsimp [z2m, forceNat_eq] at h
      injection h with h; injection h with hk hv; subst hk; subst hv
      exact ⟨0,0,zPS.nil k⟩
    | cons w u =>
      cases w with
      | V =>
        dsimp [z2m, forceNat_eq] at h
        split_ifs at h with hk
        cases hrec : z2m fuel u (2 + (k - 3) * 2) with
        | none => rw [hrec] at h; contradiction
        | some kv =>
          rw [hrec] at h
          rcases kv with ⟨k0,v0⟩
          injection h with h; injection h with hk' hv'; subst hk'; subst hv'
          rcases ih u (2 + (k - 3) * 2) k0 v0 hrec with ⟨a,b,hSub⟩
          have heq : k = 3 + (k - 3) := by omega
          rw [heq]; exact ⟨a * (1 / 2),b * (1 / 2),zPS.T hSub⟩
      | K =>
        dsimp [z2m, forceNat_eq] at h
        split_ifs at h with hk
        have hk2 : 2 <= k /\ k % 2 = 0 := by
          simp only [Bool.or_eq_true,decide_eq_true_eq,bne_iff_ne,ne_eq,not_or,not_lt,not_not] at hk
          exact hk
        cases hrec : z2m fuel u (((k - 2) / 4) * 2) with
        | none => rw [hrec] at h; contradiction
        | some kv =>
          rw [hrec] at h
          rcases kv with ⟨k0,v0⟩
          simp only [forceWord_eq] at h
          injection h with h; injection h with hk' hv'; subst hk'; subst hv'
          rcases ih u (((k - 2) / 4) * 2) k0 v0 hrec with ⟨a,b,hSub⟩
          unfold z2l
          have hmod4 : (k - 2) % 4 = 0 \/ (k - 2) % 4 = 2 := by omega
          rcases hmod4 with hm | hm
          · have hc : ((k - 2) % 4 == 0) = true := beq_iff_eq.mpr hm
            rw [hc]
            have heq : k = 2 + ((k - 2) / 4) * 4 := by omega
            rw [heq]; exact ⟨3 + a * 2,b * 2,zPS.short00 hSub⟩
          · have hc : ((k - 2) % 4 == 0) = false := beq_false_of_ne (by omega)
            rw [hc]
            have heq : k = 4 + ((k - 2) / 4) * 4 := by omega
            rw [heq]; exact ⟨4 + a * 2,b * 2,zPS.short10 hSub⟩
      | Q =>
        dsimp [z2m, forceNat_eq] at h
        split_ifs at h with hk0 hks
        · have hk2 : 2 <= k /\ k % 2 = 0 := by
            simp only [beq_iff_eq] at hk0
            simp only [Bool.and_eq_true,beq_iff_eq] at hks
            omega
          cases hrec : z2m fuel u (1 + ((k - 2) / 4) * 2) with
          | none => rw [hrec] at h; contradiction
          | some kv =>
            rw [hrec] at h
            rcases kv with ⟨k0,v0⟩
            simp only [forceWord_eq] at h
            injection h with h; injection h with hk' hv'; subst hk'; subst hv'
            rcases ih u (1 + ((k - 2) / 4) * 2) k0 v0 hrec with ⟨a,b,hSub⟩
            unfold z2l
            have hmod4 : (k - 2) % 4 = 0 \/ (k - 2) % 4 = 2 := by omega
            rcases hmod4 with hm | hm
            · have hc : ((k - 2) % 4 == 0) = true := beq_iff_eq.mpr hm
              rw [hc]
              have heq : k = 2 + ((k - 2) / 4) * 4 := by omega
              rw [heq]; exact ⟨2 + a * 2,b * 2,zPS.short01 hSub⟩
            · have hc : ((k - 2) % 4 == 0) = false := beq_false_of_ne (by omega)
              rw [hc]
              have heq : k = 4 + ((k - 2) / 4) * 4 := by omega
              rw [heq]; exact ⟨3 + a * 2,b * 2,zPS.short11 hSub⟩
        · have hk_pos : 1 <= k := by simp only [beq_iff_eq] at hk0; omega
          cases u with
          | nil => contradiction
          | cons w2 u' =>
            cases w2 with
            | V => contradiction
            | K =>
              dsimp [forceNat_eq] at h
              cases hrec : z2m fuel u' ((k - 1) * 2) with
              | none => rw [hrec] at h; contradiction
              | some kv =>
                rw [hrec] at h
                rcases kv with ⟨k0,v0⟩
                injection h with h; injection h with hk' hv'; subst hk'; subst hv'
                rcases ih u' ((k - 1) * 2) k0 v0 hrec with ⟨a,b,hSub⟩
                have heq : k = 1 + (k - 1) := by omega
                rw [heq]; exact ⟨a * (1 / 2),(1 + b) * (1 / 2),zPS.pair0 hSub⟩
            | Q =>
              dsimp [forceNat_eq] at h
              cases hrec : z2m fuel u' (1 + (k - 1) * 2) with
              | none => rw [hrec] at h; contradiction
              | some kv =>
                rw [hrec] at h
                rcases kv with ⟨k0,v0⟩
                injection h with h; injection h with hk' hv'; subst hk'; subst hv'
                rcases ih u' (1 + (k - 1) * 2) k0 v0 hrec with ⟨a,b,hSub⟩
                have heq : k = 1 + (k - 1) := by omega
                rw [heq]; exact ⟨a * (1 / 2),(3 / 4) + b * (1 / 2),zPS.pair1 hSub⟩
lemma z2o (u : zW) :
    ∀ (ds p tail : zW),z2f u ds = some (p,tail) ->
      ∃ v,p = v ++ [V] := by
  induction u with
  | nil => intro ds p tail hE; contradiction
  | cons w u ih =>
    intro ds p tail hE
    cases w
    · dsimp [z2f] at hE
      injection hE with h1; injection h1 with h1 h2; subst h1
      exact ⟨u.reverse,by simp [List.reverseAux_eq]⟩
    · exact ih (K :: ds) p tail hE
    · exact ih (Q :: ds) p tail hE
lemma z2p (u p ds : zW) (hE : z2h u = some (p,ds)) :
    ∃ v,p = v ++ [V] :=
  z2o u.reverse [] p ds hE
lemma z2q {A H : Nat} {u : zW} (h : zDg A H u) :
    u.all z25 = true := by
  induction h with
  | nil => rfl
  | zero _ ih => simp [z25,ih]
  | one _ ih => simp [z25,ih]
lemma z2r (n : Nat) : (0 : Rat) < ((2 ^ n : Nat) : Rat) := by
  exact_mod_cast zPp n
lemma z2s (n : Nat) :
    z1e (zR n V) = 0 /\
    z1h (zR n V) * ((2 ^ n : Nat) : Rat) = 1 := by
  induction n with
  | zero => simp [z1e,z1h]
  | succ n ih =>
    rw [List.replicate_succ,Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    dsimp [z1e,z1h]
    refine ⟨by linarith [ih.1],?_⟩
    calc z1h (zR n V) * (1 / 2) * (((2 ^ n : Nat) : Rat) * 2)
      _ = z1h (zR n V) * ((2 ^ n : Nat) : Rat) := by ring
      _ = 1 := ih.2
lemma z2t (n : Nat) (x : Rat) :
    z1h (zR n V) * x * ((2 ^ n : Nat) : Rat) = x := by
  calc z1h (zR n V) * x * ((2 ^ n : Nat) : Rat)
    _ = (z1h (zR n V) * ((2 ^ n : Nat) : Rat)) * x := by ring
    _ = 1 * x := by rw [(z2s n).2]
    _ = x := by ring
lemma z2u (q : Nat) : z1g (zR q V) = 0 := by
  induction q with
  | zero => simp [z1g]
  | succ q ih => rw [List.replicate_succ]; dsimp [z1g]; linarith
lemma z2v (u : zW) (A H : Nat) (ds : zW)
    (hD : zDg A H ds)
    (hHeight : z1h u * ((2 ^ H : Nat) : Rat) = 1)
    (hCut : z0Z u = true) (hNe : u ≠ [])
    (hBound : z1e u + z1h u * (1 + z1f ds) <= 1 / 128) :
    ∃ k v a b,zPS 12 (u ++ ds ++ [K]) k v a b /\ 4 < k := by
  have hWu := zWn u
  have hWd := zWn ds
  have hSu := zSp u
  have hMu : z1e u <= 1 / 128 := by nlinarith
  rcases z1R u 6 (by push_cast; linarith) with ⟨k0,v,a,b,hI,hK0⟩
  rcases z1X hI hCut hNe with ⟨n,rfl⟩
  have hBudget := z1N hI
  have hLoss := z1O hI
  have hSv := z1V hI
  have hPv := zSp v
  have hCarry : 7 < (((n * 2 : Nat) : Rat) - 4) * z1h v := by
    push_cast at hBudget ⊢; linarith
  rcases zDw hD with ⟨hSd,hMd,hOd⟩
  have hRest : 2 * (z1e (ds ++ [K]) + z1f (ds ++ [K])) * z1h v < 7 := by
    rw [z1j,z1k]
    dsimp [z1e,z1f]
    have h1 : z1h u * z1f ds <= 1 / 128 := by nlinarith
    have h2 : z1h u * (3 * z1h ds - 1 + z1f ds) < 4 := by nlinarith
    have h3 : 0 <= 3 * z1h ds - 1 + z1f ds := by linarith
    nlinarith
  have hLoss2 : 8 * (1 + 2 * z1f ds) * z1h v < 1 := by
    have h1 : z1h u * z1f ds <= 1 / 128 := by nlinarith
    have h2 : z1h u <= 1 / 128 := by nlinarith
    nlinarith
  rcases z1W (ds ++ [K]) (z1f ds) n (z1v hD)
      (by nlinarith) (by nlinarith) with ⟨k,w,c,d,hJ,hK'⟩
  rcases z1P hI hJ with ⟨a',b',hS,_,_⟩
  rw [<- List.append_assoc] at hS
  exact ⟨k,v ++ w,a',b',hS,hK'⟩
lemma z2w (r a b : Nat) (v : zW) (l : Rat) (u : zW) (z : Rat)
    (hI : Scan a ((zR (1 + r * 2) Q ++ [K]) ++ u) b v l)
    (hZ : zTd u z) :
    z1e v * ((2 ^ (1 + r) : Nat) : Rat) <= 1 + 2 * z /\
    (l - 1 / 2) * ((2 ^ (1 + r) : Nat) : Rat) <= 1 + 2 * z := by
  have hCut : z10 (zR (1 + r * 2) Q ++ [K]) u := by
    left; rw [z11]; rfl
  rcases z1z hI (zR (1 + r * 2) Q ++ [K]) u rfl hCut
    with ⟨c,x,y,s,t0,hJ,hK,rfl,hL⟩
  rcases zS1 r a c x s hJ with ⟨rfl,_,rfl⟩
  have hTB := z1x hK hZ
  have hRT := z2s (1 + r)
  have hRF1 := z2t (1 + r) (z1e y)
  have hRF2 := z2t (1 + r) t0
  have hPos := z2r (1 + r)
  rw [z1j]
  constructor <;> nlinarith
lemma z2x (r a b : Nat) (v : zW) (l : Rat) (u : zW) (z : Rat)
    (hI : Scan a ((zR (2 + r * 2) Q ++ [K]) ++ u) b v l)
    (hZ : zTd u z) :
    (z1e v - 1) * ((2 ^ r : Nat) : Rat) <= 1 + 2 * z /\
    (l - 1) * ((2 ^ r : Nat) : Rat) <= 1 + 2 * z := by
  have hCut : z10 (zR (2 + r * 2) Q ++ [K]) u := by
    left; rw [z11]; rfl
  rcases z1z hI (zR (2 + r * 2) Q ++ [K]) u rfl hCut
    with ⟨c,x,y,s,t0,hJ,hK,rfl,hL⟩
  rcases z1r r a c x s hJ with ⟨d,n,rfl,_,rfl⟩
  have hTB := z1x hK hZ
  have hSB := z1o hK
  have hGe1 : (1 : Rat) <= ((2 ^ r : Nat) : Rat) := by exact_mod_cast zPp r
  have hWy := zWn y
  set sc := z1h (zR (1 + r) V)
  have hMrep : z1e (zR (1 + r) V ++ y) = sc * z1e y := by
    rw [z1j,(z2s (1 + r)).1,zero_add]
  have hRF1 := z2t (1 + r) (z1e y)
  have hRF2 := z2t (1 + r) t0
  have hpow : ((2 ^ (1 + r) : Nat) : Rat) = ((2 ^ r : Nat) : Rat) * 2 := by
    rw [zP2]; push_cast; ring
  rw [hpow] at hRF1 hRF2
  have hRF1' : sc * z1e y * ((2 ^ r : Nat) : Rat) = z1e y * (1 / 2) := by
    change z1h (zR (1 + r) V) * z1e y * ((2 ^ r : Nat) : Rat) = z1e y * (1 / 2)
    linarith [hRF1]
  have hRF2' : sc * t0 * ((2 ^ r : Nat) : Rat) = t0 * (1 / 2) := by
    change z1h (zR (1 + r) V) * t0 * ((2 ^ r : Nat) : Rat) = t0 * (1 / 2)
    linarith [hRF2]
  simp only [List.cons_append]
  cases d with
  | V =>
    change l = 1 + (sc * (1 / 2)) * t0 at hL
    have hM : z1e (V :: (zR (1 + r) V ++ y)) = (sc * z1e y) * (1 / 2) := by
      dsimp [z1e]; rw [hMrep]
    rw [hM,hL]
    have h1 : ((sc * z1e y) * (1 / 2) - 1) * ((2 ^ r : Nat) : Rat) = (sc * z1e y * ((2 ^ r : Nat) : Rat)) * (1 / 2) - ((2 ^ r : Nat) : Rat) := by ring
    have h2 : (1 + (sc * (1 / 2)) * t0 - 1) * ((2 ^ r : Nat) : Rat) = (sc * t0 * ((2 ^ r : Nat) : Rat)) * (1 / 2) := by ring
    rw [h1,h2,hRF1',hRF2']
    constructor <;> linarith [hWy.1,hSB.1,hGe1,hTB.1,hTB.2.1]
  | K =>
    change l = 1 + (sc * 2) * t0 at hL
    have hM : z1e (K :: (zR (1 + r) V ++ y)) = 1 + (sc * z1e y) * 2 := by
      dsimp [z1e]; rw [hMrep]
    rw [hM,hL]
    have h1 : (1 + (sc * z1e y) * 2 - 1) * ((2 ^ r : Nat) : Rat) = (sc * z1e y * ((2 ^ r : Nat) : Rat)) * 2 := by ring
    have h2 : (1 + (sc * 2) * t0 - 1) * ((2 ^ r : Nat) : Rat) = (sc * t0 * ((2 ^ r : Nat) : Rat)) * 2 := by ring
    rw [h1,h2,hRF1',hRF2']
    constructor <;> linarith [hWy.1,hSB.1,hGe1,hTB.1,hTB.2.1]
  | Q =>
    change l = 1 + (sc * 2) * t0 at hL
    have hM : z1e (Q :: (zR (1 + r) V ++ y)) = 1 + (sc * z1e y) * 2 := by
      dsimp [z1e]; rw [hMrep]
    rw [hM,hL]
    have h1 : (1 + (sc * z1e y) * 2 - 1) * ((2 ^ r : Nat) : Rat) = (sc * z1e y * ((2 ^ r : Nat) : Rat)) * 2 := by ring
    have h2 : (1 + (sc * 2) * t0 - 1) * ((2 ^ r : Nat) : Rat) = (sc * t0 * ((2 ^ r : Nat) : Rat)) * 2 := by ring
    rw [h1,h2,hRF1',hRF2']
    constructor <;> linarith [hWy.1,hSB.1,hGe1,hTB.1,hTB.2.1]
lemma z2y (c a b : Nat) (v : zW) (l : Rat) (u : zW) (z : Rat)
    (hI : Scan a ((zR c Q ++ [K]) ++ u) b v l)
    (hZ : zTd u z) (hC : 0 < c) :
    z1e v * ((2 ^ (c + c / 2) : Nat) : Rat) <= ((2 ^ (c + c / 2) : Nat) : Rat) + 2 * ((2 ^ c : Nat) : Rat) * (1 + 2 * z) /\
    l * ((2 ^ (c + c / 2) : Nat) : Rat) <= ((2 ^ (c + c / 2) : Nat) : Rat) + 2 * ((2 ^ c : Nat) : Rat) * (1 + 2 * z) := by
  have hZn := z1t hZ
  rcases z0U c with ⟨a0,rfl⟩ | ⟨a0,rfl⟩
  · cases a0 with
    | zero => omega
    | succ r =>
      have heq : (r + 1) * 2 = 2 + r * 2 := by omega
      rw [heq] at hI ⊢
      have hEven := z2x r a b v l u z hI hZ
      have hP : 2 + r * 2 + (2 + r * 2) / 2 = (2 + r * 2) + r + 1 := by omega
      have hPow : ((2 ^ (2 + r * 2 + (2 + r * 2) / 2) : Nat) : Rat) =
          ((2 ^ (2 + r * 2) : Nat) : Rat) * ((2 ^ r : Nat) : Rat) * 2 := by
        rw [hP,Nat.pow_add,Nat.pow_add]; push_cast; ring
      have hPos1 := z2r (2 + r * 2)
      have hPos2 := z2r r
      rw [hPow]
      constructor <;> nlinarith
  · have hOdd := z2w a0 a b v l u z hI hZ
    have hP : 1 + a0 * 2 + (1 + a0 * 2) / 2 = (1 + a0 * 2) + a0 := by omega
    have hPow : ((2 ^ (1 + a0 * 2 + (1 + a0 * 2) / 2) : Nat) : Rat) =
        ((2 ^ (1 + a0 * 2) : Nat) : Rat) * ((2 ^ a0 : Nat) : Rat) := by
      rw [hP,Nat.pow_add]; push_cast; ring
    have hPow1 : ((2 ^ (1 + a0) : Nat) : Rat) = ((2 ^ a0 : Nat) : Rat) * 2 := by
      rw [zP2]; push_cast; ring
    rw [hPow1] at hOdd
    have hPos1 := z2r (1 + a0 * 2)
    have hPos2 := z2r a0
    rw [hPow]
    constructor <;> nlinarith
lemma z2z (c : Nat) :
    ∀ (u : zW) (z : Rat),zTd (zR c Q ++ u) z ->
      ∃ z',zTd u z' /\ z = ((2 ^ c : Nat) : Rat) * z' := by
  induction c with
  | zero =>
    intro u z hI
    exact ⟨z,hI,by simp⟩
  | succ c ih =>
    intro u z hI
    rw [List.replicate_succ,List.cons_append] at hI
    rcases zTo hI with ⟨y,hJ,rfl⟩
    rcases ih u y hJ with ⟨x,hK,rfl⟩
    refine ⟨x,hK,?_⟩
    rw [Nat.pow_succ]; push_cast; ring
lemma z2A (x z p q : Rat) (hp : 0 < p) (hpq : p <= q) (hz : 0 <= z)
    (h : x * q <= q + 2 * z) : x * p <= p + 2 * z := by
  by_cases hx : x <= 1
  · nlinarith
  · nlinarith
lemma z2B (s c : Nat) (u : zW) (A H a b : Nat) (v : zW) (l : Rat)
    (hD : zDg A H (zR c Q ++ K :: u))
    (hI : Scan a ((zR c Q ++ K :: u) ++ [K]) b v l)
    (hC : 0 < c) (hSC : s <= c) :
    z1e v * ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f (zR c Q ++ K :: u) /\
    l * ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f (zR c Q ++ K :: u) := by
  have hZ := z1v hD
  rw [List.append_assoc] at hZ
  rcases z2z c (K :: u ++ [K]) (z1f (zR c Q ++ K :: u)) hZ with ⟨x,hU,hX⟩
  rcases z1u hU with ⟨hNil,_⟩ | ⟨z,hV,rfl⟩
  · simp at hNil
  · have hE : (zR c Q ++ K :: u) ++ [K] =
        (zR c Q ++ [K]) ++ (u ++ [K]) := by simp [List.append_assoc]
    rw [hE] at hI
    rcases z2y c a b v l (u ++ [K]) z hI hV hC with ⟨hM,hL⟩
    have hPos := z2r (s + s / 2)
    have hMono : ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (c + c / 2) : Nat) : Rat) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
    have hW := zWn (zR c Q ++ K :: u)
    constructor
    · exact z2A (z1e v) (z1f (zR c Q ++ K :: u)) _ _ hPos hMono hW.2.1 (by nlinarith)
    · exact z2A l (z1f (zR c Q ++ K :: u)) _ _ hPos hMono hW.2.1 (by nlinarith)
lemma z2C (s : Nat) (ds : zW) (A H k k' : Nat) (v : zW) (a b : Rat)
    (hD : zDg A H ds) (hI : zPS k (ds ++ [K]) k' v a b)
    (hLow : ∃ c u,(0 < c /\ s <= c) /\ ds = zR c Q ++ K :: u) :
    z1e v * ((2 ^ (s + s / 2) : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds /\
    a * ((2 ^ (s + s / 2) : Nat) : Rat) <= 4 * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds) /\
    b * ((2 ^ (s + s / 2) : Nat) : Rat) <= 3 * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds) := by
  rcases hLow with ⟨c,u,⟨hC,hSC⟩,rfl⟩
  have hFull := z19 hD (zDg.zero zDg.nil)
  rcases z1T hI hFull with ⟨l,hJ,hP,hN⟩
  have hCore := z2B s c u A H k k' v l hD hJ hC hSC
  have hPos := z2r (s + s / 2)
  refine ⟨hCore.1,by nlinarith,by nlinarith⟩
lemma z2D (r J k b A B : Nat) (hR : r <= J)
    (hK : ∃ n,k = n * 2 ^ r) (hB0 : ∃ n,1 + b = n * 2 ^ r)
    (hAsum : A + 2 ^ J = k) (hBsum : B + 2 ^ J = A + b) :
    ∃ n,1 + B = n * 2 ^ r := by
  rcases hK with ⟨n,rfl⟩
  rcases hB0 with ⟨m,hM⟩
  have hP : 2 ^ J = 2 ^ (J - r) * 2 ^ r := by
    rw [<- Nat.pow_add,Nat.sub_add_cancel hR]
  refine ⟨n + m - 2 * 2 ^ (J - r),?_⟩
  have hpos := zPp r
  have hle : 2 * 2 ^ (J - r) <= n + m := by
    have h1 : (2 * 2 ^ (J - r)) * 2 ^ r <= (n + m) * 2 ^ r := by
      calc (2 * 2 ^ (J - r)) * 2 ^ r = 2 ^ J + 2 ^ J := by rw [hP]; ring
        _ <= n * 2 ^ r + (1 + b) := by omega
        _ = (n + m) * 2 ^ r := by rw [hM]; ring
    exact Nat.le_of_mul_le_mul_right h1 hpos
  rw [Nat.sub_mul]
  have h2 : 2 * 2 ^ (J - r) * 2 ^ r = 2 ^ J + 2 ^ J := by rw [hP]; ring
  have h3 : (n + m) * 2 ^ r = n * 2 ^ r + (1 + b) := by rw [hM]; ring
  omega
lemma z2E (s : Nat) :
    ∀ (B H : Nat) (ds : zW),zDg B H ds -> s <= H ->
      (∃ n,1 + B = n * 2 ^ s) -> ∃ u,ds = zR s Q ++ u := by
  induction s with
  | zero =>
    intro B H ds _ _ _
    exact ⟨ds,rfl⟩
  | succ s ih =>
    intro B H ds hD hSH ⟨n,hN⟩
    have hpow : 2 ^ (s + 1) = 2 ^ s * 2 := Nat.pow_succ 2 s
    cases hD with
    | nil => omega
    | @zero A H' u hSub =>
      rw [hpow] at hN
      have hN2 : 1 + A * 2 = (n * 2 ^ s) * 2 := by rw [hN]; ring
      omega
    | @one A H' u hSub =>
      rw [hpow] at hN
      have hN2 : 1 + (1 + A * 2) = (n * 2 ^ s) * 2 := by rw [hN]; ring
      have hN' : 1 + A = n * 2 ^ s := by omega
      rcases ih A H' u hSub (by omega) ⟨n,hN'⟩ with ⟨w,rfl⟩
      refine ⟨w,?_⟩
      rw [List.replicate_succ,List.cons_append]
lemma z2F (r k : Nat) (u : zW) (k' : Nat) (v : zW) (a b : Rat)
    (carry : Nat) (eff : zW) (A B J : Nat) (ds : zW)
    (hI : zPS k (u ++ zR (1 + r * 2) Q ++ [K]) k' v a b)
    (hE : zEf 0 (V :: (v ++ [V])) carry eff)
    (hD : zDg B J ds) (hR : 1 + r <= J)
    (hAsum : A + 2 ^ J = k') (hBsum : B + 2 ^ J = A + carry) :
    ∃ w,ds = zR (1 + r) Q ++ w := by
  rcases z1Z r k u k' v a b hI with ⟨w,n,rfl,hK⟩
  have hEq : V :: ((w ++ zR (1 + r) V) ++ [V]) =
      (V :: w) ++ zR (2 + r) V := by
    have h2 : 2 + r = (1 + r) + 1 := by omega
    rw [h2,z13]
    simp only [List.cons_append,List.append_assoc]
  rw [hEq] at hE
  rcases z1L (V :: w) (2 + r) 0 carry eff hE with ⟨x,m,_,hC⟩
  have hCarry : ∃ n0,1 + carry = n0 * 2 ^ (1 + r) := by
    refine ⟨m * 2,?_⟩
    have hpow : 2 ^ (2 + r) = 2 * 2 ^ (1 + r) := by
      have h2 : 2 + r = 1 + (1 + r) := by omega
      rw [h2,zP2]; ring
    rw [hpow] at hC
    calc 1 + carry = m * (2 * 2 ^ (1 + r)) := hC
      _ = (m * 2) * 2 ^ (1 + r) := by ring
  exact z2E (1 + r) B J ds hD hR (z2D (1 + r) J k' carry A B hR ⟨n,hK⟩ hCarry hAsum hBsum)
lemma z2G (x p q s f : Rat) (hp : 0 < p) (hs : 0 <= s)
    (hxp : x * p <= q) (hsq : s * q <= f * p) : s * x <= f := by
  have h1 : (s * x) * p <= f * p := by
    calc (s * x) * p = s * (x * p) := by ring
      _ <= s * q := mul_le_mul_of_nonneg_left hxp hs
      _ <= f * p := hsq
  exact le_of_mul_le_mul_right h1 hp
lemma z2H (s : Nat) (ds : zW) (A H k k' : Nat) (v : zW) (a b sigma f : Rat)
    (hD : zDg A H ds) (hI : zPS k (ds ++ [K]) k' v a b)
    (hLow : ∃ c u,(0 < c /\ s <= c) /\ ds = zR c Q ++ K :: u)
    (hSig : 0 <= sigma)
    (hBound : sigma * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * z1f ds) <= f * ((2 ^ (s + s / 2) : Nat) : Rat)) :
    sigma * z1e v <= f /\ sigma * a <= 4 * f /\ sigma * b <= 3 * f := by
  rcases z2C s ds A H k k' v a b hD hI hLow with ⟨hM,hP,hN⟩
  have hPos := z2r (s + s / 2)
  refine ⟨?_,?_,?_⟩
  · exact z2G (z1e v) _ _ sigma f hPos hSig hM hBound
  · exact z2G a _ _ sigma (4 * f) hPos hSig hP (by linarith)
  · exact z2G b _ _ sigma (3 * f) hPos hSig hN (by linarith)
lemma z2I (u : zW) (k : Nat) (v : zW) (a b : Rat)
    (hI : zPS 12 u k v a b) :
    (k : Rat) * z1h (V :: (v ++ [V])) = 2 + 4 * z1h (V :: (v ++ [V])) - (a - b) * (1 / 2) := by
  have hEq := z1N hI
  dsimp [z1h]
  rw [z1m]
  dsimp [z1h]
  push_cast at hEq ⊢
  linarith
lemma z2J (u : zW) (k : Nat) (v : zW) (a b : Rat) (J A B carry : Nat)
    (hI : zPS 12 u k v a b)
    (hHeight : z1h (V :: (v ++ [V])) * ((2 ^ J : Nat) : Rat) = 1)
    (hAsum : A + 2 ^ J = k) (hBsum : B + 2 ^ J = A + carry) :
    1 - ((1 + B : Nat) : Rat) * z1h (V :: (v ++ [V])) =
      (a - b) * (1 / 2) - 4 * z1h (V :: (v ++ [V])) -
      (((1 + carry : Nat) : Rat) * z1h (V :: (v ++ [V])) - 1) := by
  have hBudget := z2I u k v a b hI
  have hSum : B + 2 ^ J + 2 ^ J = k + carry := by omega
  have hQsum : (B : Rat) + ((2 ^ J : Nat) : Rat) + ((2 ^ J : Nat) : Rat) = (k : Rat) + (carry : Rat) := by
    exact_mod_cast hSum
  set s := z1h (V :: (v ++ [V]))
  have hMul : (B : Rat) * s + 1 + 1 = (k : Rat) * s + (carry : Rat) * s := by
    calc (B : Rat) * s + 1 + 1
      _ = (B : Rat) * s + (s * ((2 ^ J : Nat) : Rat)) + (s * ((2 ^ J : Nat) : Rat)) := by rw [hHeight]
      _ = ((B : Rat) + ((2 ^ J : Nat) : Rat) + ((2 ^ J : Nat) : Rat)) * s := by ring
      _ = ((k : Rat) + (carry : Rat)) * s := by rw [hQsum]
      _ = (k : Rat) * s + (carry : Rat) * s := by ring
  push_cast
  calc 1 - (1 + (B : Rat)) * s
    _ = 3 - ((B : Rat) * s + 1 + 1) - s := by ring
    _ = 3 - ((k : Rat) * s + (carry : Rat) * s) - s := by rw [hMul]
    _ = 3 - ((2 + 4 * s - (a - b) * (1 / 2)) + (carry : Rat) * s) - s := by rw [hBudget]
    _ = (a - b) * (1 / 2) - 4 * s - ((1 + (carry : Rat)) * s - 1) := by ring

end BusyBeaver.WordCalculus
