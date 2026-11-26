/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.WeakCollatz75
public import Cryptids.Propositions

/-!
# Semantics of `weak_collatz_75` (`WeakCollatz75`)

Links blank-tape halting of the 75-state machine `weakCollatz75`
(`halts_weakCollatz75_iff_bounded_cycle`) to:
1. **Constructive nontrivial cycle existence (`halts_weakCollatz75_iff_exists_cycle`, zero
   `Classical.choice`)**: via a constructive finite-pigeonhole reduction on the cycle maximum `M`
   showing that any positive cycle `terras^[k] x = x` outside `{1, 2}` has a member `M ≥ 3` whose
   period `j` satisfies `1 ≤ j ≤ M - 2 ≤ M`;
2. **Constructive Böhm–Sontacchi (1978) Diophantine cycle equation
   (`halts_weakCollatz75_iff_bohmSontacchi`, zero `Classical.choice`)**: connecting halting directly
   to `(2 ^ n - 3 ^ (terrasParityWord n x).sum) * x = collatzCycleNum (terrasParityWord n x)`
   (the #1 audited paper on `ccchallenge.org`);
3. **Tao's Weak Collatz Conjecture (`halts_weakCollatz75_iff_not_weakCollatz`)**:
   `Halts weakCollatz75 ↔ ¬ WeakCollatzConjecture`.
-/

@[expose] public section

namespace ConjectureMachines.WeakCollatz75

private def findEq (f : ℕ → ℕ) (target : ℕ) : ℕ → Option ℕ
  | 0 => if f 0 = target then some 0 else none
  | r + 1 =>
    match findEq f target r with
    | some i => some i
    | none => if f (r + 1) = target then some (r + 1) else none

private theorem findEq_some_spec (f : ℕ → ℕ) (target r i : ℕ)
    (h : findEq f target r = some i) :
    i ≤ r ∧ f i = target := by
  induction r generalizing i with
  | zero =>
    dsimp [findEq] at h
    split_ifs at h with h0
    · injection h with hi
      subst hi
      exact ⟨Nat.le_refl 0, h0⟩
  | succ r ih =>
    dsimp [findEq] at h
    cases hprev : findEq f target r with
    | some j =>
      rw [hprev] at h
      injection h with hij
      subst hij
      rcases ih j hprev with ⟨hjr, hfj⟩
      exact ⟨by omega, hfj⟩
    | none =>
      rw [hprev] at h
      split_ifs at h with hr1
      · injection h with hi
        subst hi
        exact ⟨Nat.le_refl _, hr1⟩

private theorem findEq_none_spec (f : ℕ → ℕ) (target r : ℕ)
    (h : findEq f target r = none) :
    ∀ i : ℕ, i ≤ r → f i ≠ target := by
  induction r with
  | zero =>
    dsimp [findEq] at h
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    split_ifs at h with h0
    exact h0
  | succ r ih =>
    dsimp [findEq] at h
    cases hprev : findEq f target r with
    | some j =>
      rw [hprev] at h
      cases h
    | none =>
      rw [hprev] at h
      split_ifs at h with hr1
      intro i hi
      rcases Nat.lt_or_ge i (r + 1) with hlt | hge
      · exact ih hprev i (by omega)
      · have hieq : i = r + 1 := by omega
        subst hieq
        exact hr1

/-- Constructive finite pigeonhole principle on `ℕ` (zero `Classical.choice`). -/
private theorem nat_pigeonhole_constructive (N : ℕ) :
    ∀ f : ℕ → ℕ, (∀ i : ℕ, i ≤ N + 1 → f i < N + 1) →
      ∃ a b : ℕ, a < b ∧ b ≤ N + 1 ∧ f a = f b := by
  induction N with
  | zero =>
    intro f hf
    have h0 : f 0 < 1 := hf 0 (by omega)
    have h1 : f 1 < 1 := hf 1 (by omega)
    exact ⟨0, 1, by omega, by omega, by omega⟩
  | succ m ih =>
    intro f hf
    cases hfind : findEq f (f (m + 2)) (m + 1) with
    | some i =>
      rcases findEq_some_spec f (f (m + 2)) (m + 1) i hfind with ⟨hi_le, hfi⟩
      exact ⟨i, m + 2, by omega, by omega, hfi⟩
    | none =>
      have hne : ∀ i : ℕ, i ≤ m + 1 → f i ≠ f (m + 2) :=
        findEq_none_spec f (f (m + 2)) (m + 1) hfind
      let g : ℕ → ℕ := fun i => if f i < f (m + 2) then f i else f i - 1
      have hg_lt : ∀ i : ℕ, i ≤ m + 1 → g i < m + 1 := by
        intro i hi
        have hfi_lt : f i < m + 2 := hf i (by omega)
        have hfi_ne : f i ≠ f (m + 2) := hne i hi
        dsimp [g]
        split_ifs with hlt
        · have hv_lt : f (m + 2) < m + 2 := hf (m + 2) (by omega)
          omega
        · omega
      rcases ih g hg_lt with ⟨a, b, hab, hb_le, hgab⟩
      refine ⟨a, b, hab, by omega, ?_⟩
      have hfa_ne : f a ≠ f (m + 2) := hne a (by omega)
      have hfb_ne : f b ≠ f (m + 2) := hne b hb_le
      dsimp [g] at hgab
      split_ifs at hgab with ha_lt hb_lt hb_lt2 <;> omega

private theorem terras_le_two_inv (z : ℕ) (hz : z ≤ 2) : terras z ≤ 2 := by
  unfold terras
  split_ifs <;> omega

private theorem terras_iterate_le_two (t z : ℕ) (hz : z ≤ 2) : terras^[t] z ≤ 2 := by
  induction t generalizing z with
  | zero => exact hz
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    exact ih (terras z) (terras_le_two_inv z hz)

private theorem terras_iterate_mul_period (m k x : ℕ) (hcyc : terras^[k] x = x) :
    terras^[m * k] x = x := by
  induction m with
  | zero => rw [Nat.zero_mul]; rfl
  | succ m ih =>
    rw [Nat.succ_mul, Nat.add_comm (m * k) k, Function.iterate_add_apply, ih, hcyc]

private theorem terras_orbit_ge_three {x k : ℕ} (hx3 : 3 ≤ x) (hk1 : 1 ≤ k)
    (hcyc : terras^[k] x = x) (i : ℕ) :
    3 ≤ terras^[i] x := by
  by_cases hge : 3 ≤ terras^[i] x
  · exact hge
  · exfalso
    have hle2 : terras^[i] x ≤ 2 := by omega
    have hik : i ≤ i * k := Nat.le_mul_of_pos_right i hk1
    have hsplit : i * k = (i * k - i) + i := by omega
    have hx_eq : terras^[i * k] x = x := terras_iterate_mul_period i k x hcyc
    rw [hsplit, Function.iterate_add_apply] at hx_eq
    have hx_le2 : terras^[i * k - i] (terras^[i] x) ≤ 2 :=
      terras_iterate_le_two (i * k - i) (terras^[i] x) hle2
    omega

private def orbitMax (x : ℕ) : ℕ → ℕ
  | 0 => x
  | r + 1 => max (orbitMax x r) (terras^[r + 1] x)

private theorem orbitMax_spec (x r : ℕ) :
    (∃ i : ℕ, i ≤ r ∧ terras^[i] x = orbitMax x r) ∧
    (∀ i : ℕ, i ≤ r → terras^[i] x ≤ orbitMax x r) := by
  induction r with
  | zero =>
    refine ⟨⟨0, Nat.le_refl 0, rfl⟩, ?_⟩
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact Nat.le_refl x
  | succ r ih =>
    rcases ih with ⟨⟨i0, hi0_le, hi0_eq⟩, hle⟩
    dsimp only [orbitMax]
    refine ⟨?_, ?_⟩
    · by_cases hcmp : orbitMax x r ≤ terras^[r + 1] x
      · exact ⟨r + 1, Nat.le_refl _, (Nat.max_eq_right hcmp).symm⟩
      · have hle' : terras^[r + 1] x ≤ orbitMax x r := by omega
        exact ⟨i0, by omega, by rw [Nat.max_eq_left hle', hi0_eq]⟩
    · intro i hi
      rcases Nat.lt_or_ge i (r + 1) with hlt | hge
      · exact le_trans (hle i (by omega)) (Nat.le_max_left _ _)
      · have hieq : i = r + 1 := by omega
        subst hieq
        exact Nat.le_max_right _ _

/-- Constructive equivalence between arbitrary nontrivial positive cycles of `terras` and
bounded-period cycles `1 ≤ j ≤ x` on `x ≥ 3` (zero `Classical.choice`). -/
theorem bounded_cycle_iff_exists_cycle :
    (∃ x j : ℕ, 3 ≤ x ∧ 1 ≤ j ∧ j ≤ x ∧ terras^[j] x = x) ↔
      (∃ x k : ℕ, 1 ≤ x ∧ 1 ≤ k ∧ terras^[k] x = x ∧ x ≠ 1 ∧ x ≠ 2) := by
  constructor
  · rintro ⟨x, j, hx3, hj1, _, hcyc⟩
    exact ⟨x, j, by omega, hj1, hcyc, by omega, by omega⟩
  · rintro ⟨x, k, hx1, hk1, hcyc, hxne1, hxne2⟩
    have hx3 : 3 ≤ x := by omega
    let M := orbitMax x (k - 1)
    rcases orbitMax_spec x (k - 1) with ⟨⟨i0, hi0_le, hi0_eq⟩, h_le_M⟩
    have hi0_M : terras^[i0] x = M := hi0_eq
    have hM3 : 3 ≤ M := by
      rw [← hi0_M]
      exact terras_orbit_ge_three hx3 hk1 hcyc i0
    have hM_cyc : terras^[k] M = M := by
      rw [← hi0_M, ← Function.iterate_add_apply, Nat.add_comm k i0,
          Function.iterate_add_apply, hcyc]
    have hM_iter_le : ∀ t : ℕ, terras^[t] M ≤ M := by
      intro t
      have ht_eq : terras^[t] M = terras^[t + i0] x := by
        rw [← hi0_M, ← Function.iterate_add_apply]
      rw [ht_eq]
      let s := t + i0
      change terras^[s] x ≤ M
      have hdiv : s = s % k + (s / k) * k := by
        have hd := Nat.div_add_mod s k
        rw [Nat.mul_comm k (s / k), Nat.add_comm] at hd
        exact hd.symm
      rw [hdiv, Function.iterate_add_apply, terras_iterate_mul_period (s / k) k x hcyc]
      have hmod_lt : s % k < k := Nat.mod_lt s hk1
      exact h_le_M (s % k) (by omega)
    let N := M - 3
    let f : ℕ → ℕ := fun t => terras^[t] M - 3
    have hf_lt : ∀ t : ℕ, t ≤ N + 1 → f t < N + 1 := by
      intro t _
      have ht_ge3 : 3 ≤ terras^[t] M := terras_orbit_ge_three hM3 hk1 hM_cyc t
      have ht_leM : terras^[t] M ≤ M := hM_iter_le t
      dsimp [f, N]
      omega
    rcases nat_pigeonhole_constructive N f hf_lt with ⟨a, b, hab, hb_le, hfab⟩
    have ha_ge3 : 3 ≤ terras^[a] M := terras_orbit_ge_three hM3 hk1 hM_cyc a
    have hb_ge3 : 3 ≤ terras^[b] M := terras_orbit_ge_three hM3 hk1 hM_cyc b
    have hab_eq : terras^[a] M = terras^[b] M := by
      dsimp [f] at hfab
      omega
    let j := b - a
    have hj_pos : 1 ≤ j := by dsimp [j]; omega
    have hj_le : j ≤ M := by dsimp [j, N] at hb_le ⊢; omega
    have hj_cyc : terras^[j] M = M := by
      have happ := congrArg (fun z => terras^[a * (k - 1)] z) hab_eq
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at happ
      have hlhs : a * (k - 1) + a = a * k := by
        have hk_eq : k - 1 + 1 = k := by omega
        calc
          a * (k - 1) + a = a * (k - 1) + a * 1 := by rw [Nat.mul_one]
          _ = a * (k - 1 + 1) := (Nat.mul_add a (k - 1) 1).symm
          _ = a * k := by rw [hk_eq]
      have hrhs : a * (k - 1) + b = j + a * k := by
        dsimp [j]
        omega
      rw [hlhs, hrhs, Function.iterate_add_apply,
          terras_iterate_mul_period a k M hM_cyc] at happ
      exact happ.symm
    exact ⟨M, j, hM3, hj_pos, hj_le, hj_cyc⟩

/-- Constructive equivalence between `weakCollatz75` blank-tape halting and the existence of a
nontrivial positive cycle of `terras`. -/
theorem halts_weakCollatz75_iff_exists_cycle :
    ConjectureMachines.Halts weakCollatz75 ↔
      ∃ x k : ℕ, 1 ≤ x ∧ 1 ≤ k ∧ terras^[k] x = x ∧ x ≠ 1 ∧ x ≠ 2 := by
  exact halts_weakCollatz75_iff_bounded_cycle.trans bounded_cycle_iff_exists_cycle

private theorem two_pow_pos (n : ℕ) : 0 < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

private theorem three_pow_pos (n : ℕ) : 0 < 3 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

private theorem collatzCycleNum_eq_zero_iff (v : List ℕ) (hv : ∀ d ∈ v, d ≤ 1) :
    collatzCycleNum v = 0 ↔ v.sum = 0 := by
  induction v with
  | nil => simp [collatzCycleNum]
  | cons b rest ih =>
    have hb : b ≤ 1 := hv b List.mem_cons_self
    have hrest := ih (fun d hd => hv d (List.mem_cons_of_mem b hd))
    dsimp [collatzCycleNum]
    rcases Nat.eq_zero_or_pos b with rfl | hb_pos
    · simp only [↓reduceIte, Nat.zero_add]
      constructor
      · intro h2
        exact hrest.mp (by omega)
      · intro hs
        rw [hrest.mpr hs]
    · have hb1 : b = 1 := by omega
      subst hb1
      have h1ne0 : ¬ ((1 : ℕ) = 0) := by decide
      simp only [h1ne0, ↓reduceIte]
      have h3 : 0 < 3 ^ rest.sum := three_pow_pos rest.sum
      change 3 ^ rest.sum + 2 * collatzCycleNum rest = 0 ↔ 1 + rest.sum = 0
      constructor <;> intro h <;> omega

private theorem terrasParityWord_digits_le_one (n x d : ℕ)
    (hd : d ∈ terrasParityWord n x) : d ≤ 1 := by
  induction n generalizing x with
  | zero => cases hd
  | succ n ih =>
    dsimp [terrasParityWord] at hd
    rw [List.mem_cons] at hd
    rcases hd with rfl | htail
    · omega
    · exact ih (terras x) htail

private theorem two_pow_mul_terras_iterate_eq (n x : ℕ) :
    2 ^ n * terras^[n] x =
      3 ^ (terrasParityWord n x).sum * x + collatzCycleNum (terrasParityWord n x) := by
  induction n generalizing x with
  | zero =>
    simp [terrasParityWord, collatzCycleNum]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    dsimp only [terrasParityWord, collatzCycleNum, List.sum_cons]
    let rest := terrasParityWord n (terras x)
    have hrec : 2 ^ n * terras^[n] (terras x) = 3 ^ rest.sum * terras x + collatzCycleNum rest :=
      ih (terras x)
    rcases Nat.mod_two_eq_zero_or_one x with hev | hodd
    · have h2tx : 2 * terras x = x := by unfold terras; simp [hev]; omega
      simp only [hev, ↓reduceIte, Nat.zero_add]
      calc
        2 ^ (n + 1) * terras^[n] (terras x)
          = 2 * (2 ^ n * terras^[n] (terras x)) := by ring
        _ = 2 * (3 ^ rest.sum * terras x + collatzCycleNum rest) := by rw [hrec]
        _ = 3 ^ rest.sum * (2 * terras x) + 2 * collatzCycleNum rest := by ring
        _ = 3 ^ rest.sum * x + 2 * collatzCycleNum rest := by rw [h2tx]
    · have h2tx : 2 * terras x = 3 * x + 1 := by
        unfold terras
        have hne : ¬ (x % 2 = 0) := by omega
        simp [hne]; omega
      have h1ne0 : ¬ ((1 : ℕ) = 0) := by decide
      simp only [hodd, h1ne0, ↓reduceIte]
      calc
        2 ^ (n + 1) * terras^[n] (terras x)
          = 2 * (2 ^ n * terras^[n] (terras x)) := by ring
        _ = 2 * (3 ^ rest.sum * terras x + collatzCycleNum rest) := by rw [hrec]
        _ = 3 ^ rest.sum * (2 * terras x) + 2 * collatzCycleNum rest := by ring
        _ = 3 ^ rest.sum * (3 * x + 1) + 2 * collatzCycleNum rest := by rw [h2tx]
        _ = 3 ^ (1 + rest.sum) * x + (3 ^ rest.sum + 2 * collatzCycleNum rest) := by
              rw [Nat.add_comm 1 rest.sum, Nat.pow_succ]; ring

private theorem terras_cycle_iff_bohmSontacchi {x n : ℕ} (hx : 1 ≤ x) (hn : 1 ≤ n) :
    terras^[n] x = x ↔
      (3 ^ (terrasParityWord n x).sum < 2 ^ n ∧
        (2 ^ n - 3 ^ (terrasParityWord n x).sum) * x =
          collatzCycleNum (terrasParityWord n x)) := by
  let v := terrasParityWord n x
  let k := v.sum
  change terras^[n] x = x ↔ (3 ^ k < 2 ^ n ∧ (2 ^ n - 3 ^ k) * x = collatzCycleNum v)
  have hid : 2 ^ n * terras^[n] x = 3 ^ k * x + collatzCycleNum v :=
    two_pow_mul_terras_iterate_eq n x
  have hzero := collatzCycleNum_eq_zero_iff v (terrasParityWord_digits_le_one n x)
  constructor
  · intro hcyc
    have hid_cyc : 2 ^ n * x = 3 ^ k * x + collatzCycleNum v := by
      calc
        2 ^ n * x = 2 ^ n * terras^[n] x := by rw [hcyc]
        _ = 3 ^ k * x + collatzCycleNum v := hid
    have hnum_pos : 0 < collatzCycleNum v := by
      by_cases hz : collatzCycleNum v = 0
      · have hk0 : k = 0 := hzero.mp hz
        rw [hk0, hz] at hid_cyc
        have h2gt1 : 2 ≤ 2 ^ n := by
          rcases n with _ | m
          · omega
          · rw [Nat.pow_succ]; have := two_pow_pos m; omega
        have h2x : 2 * x ≤ 2 ^ n * x := Nat.mul_le_mul_right x h2gt1
        omega
      · omega
    have hlt_pow : 3 ^ k < 2 ^ n := by
      by_cases hle : 2 ^ n ≤ 3 ^ k
      · have hm : 2 ^ n * x ≤ 3 ^ k * x := Nat.mul_le_mul_right x hle
        omega
      · omega
    have hprod : (2 ^ n - 3 ^ k) * x = collatzCycleNum v := by
      rw [Nat.sub_mul, hid_cyc, Nat.add_sub_cancel_left]
    exact ⟨hlt_pow, hprod⟩
  · rintro ⟨hlt_pow, hprod⟩
    have hsub : (2 ^ n - 3 ^ k) * x + 3 ^ k * x = 2 ^ n * x := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hlt_pow)]
    have h2nx : 2 ^ n * terras^[n] x = 2 ^ n * x := by
      rw [hid, ← hprod, Nat.add_comm, hsub]
    exact Nat.eq_of_mul_eq_mul_left (two_pow_pos n) h2nx

/-- Constructive equivalence between `weakCollatz75` blank-tape halting and the Böhm–Sontacchi
(1978) Diophantine cycle equation on `x ≥ 3` (zero `Classical.choice`). -/
theorem halts_weakCollatz75_iff_bohmSontacchi :
    ConjectureMachines.Halts weakCollatz75 ↔
      ∃ x n : ℕ, 3 ≤ x ∧ 1 ≤ n ∧
        3 ^ (terrasParityWord n x).sum < 2 ^ n ∧
        (2 ^ n - 3 ^ (terrasParityWord n x).sum) * x =
          collatzCycleNum (terrasParityWord n x) := by
  rw [halts_weakCollatz75_iff_exists_cycle]
  constructor
  · rintro ⟨x, n, hx1, hn1, hcyc, hxne1, hxne2⟩
    rcases (terras_cycle_iff_bohmSontacchi hx1 hn1).mp hcyc with ⟨hlt, hprod⟩
    exact ⟨x, n, by omega, hn1, hlt, hprod⟩
  · rintro ⟨x, n, hx3, hn1, hlt, hprod⟩
    have hcyc := (terras_cycle_iff_bohmSontacchi (by omega) hn1).mpr ⟨hlt, hprod⟩
    exact ⟨x, n, by omega, hn1, hcyc, by omega, by omega⟩

/-- The 75-state machine `weakCollatz75` halts on the blank tape if and only if Tao's Weak Collatz
Conjecture is false. -/
theorem halts_weakCollatz75_iff_not_weakCollatz :
    ConjectureMachines.Halts weakCollatz75 ↔ ¬ WeakCollatzConjecture := by
  rw [halts_weakCollatz75_iff_exists_cycle]
  constructor
  · rintro ⟨x, k, hx1, hk1, hcyc, hxne1, hxne2⟩ hW
    rcases hW x k hx1 hk1 hcyc with rfl | rfl <;> contradiction
  · intro hnotW
    exact by_contra fun hne =>
      hnotW fun x k hx1 hk1 hcyc =>
        by_contra fun hnot12 =>
          hne ⟨x, k, hx1, hk1, hcyc, fun h1 => hnot12 (Or.inl h1),
            fun h2 => hnot12 (Or.inr h2)⟩

end ConjectureMachines.WeakCollatz75
