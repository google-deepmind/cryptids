/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann120
public import Cryptids.Semantics.Riemann.Schmidt

/-!
# Arithmetic-to-Analytic Bridge & One-Sided Landau Converse for `riemann_120`

This standalone file establishes the number-theoretic and complex-analytic bridge between the
self-sieving base-`n` offset digit deficit (`ShuniaCounterexample`) and Mathlib's
`RiemannHypothesis`:

1. **Arithmetic & Logarithmic Lemmas**:
   - `log_primorial_eq_theta`: `Real.log (primorial n) = Chebyshev.theta n`
   - `log_shuniaProd_eq`: `Real.log (shuniaProd n) = Real.log (n.factorial) + Chebyshev.theta n`
   - `factorial_centering_bounds`: `n * log n - n + 1 ≤ log (n!) ≤ n * log n - n + 1 + log n`
   - `shuniaProd_not_pow`: `shuniaProd n ≠ n ^ d` for all `n ≥ 3`
   - `pow_sub_one_le_of_offsetDigits` and `offsetDigits_pow_gt`: sharp power sandwiches for
     `offsetDigits`
   - `shuniaDeficit_mul_log_le` and `self_sub_theta_le_shuniaDeficit_mul_log`: two-sided bridge
     between `shuniaDeficit n * Real.log n` and `(n : ℝ) - Chebyshev.theta n`
2. **Quartering Clock & Unconditional Small-`n` Verification (`2 ≤ n ≤ 21845`)**:
   - `quarterClock_spec`:
     `4 ^ quarterClock (n - 1) ≤ 3 * n ∧ 3 * n < 4 ^ (quarterClock (n - 1) + 1)`
   - `not_shuniaCounterexample_of_le_21845`: unconditional verification for all `2 ≤ n ≤ 21845`
     using factorial centering (`n ≤ 1365`) and Chebyshev's prime lower bound (`1366 ≤ n ≤ 21845`)
3. **One-Sided Landau Converse (`¬ RiemannHypothesis → ∃ n ≥ 2, ShuniaCounterexample n`)**:
   - Analytic continuation and residue contradiction for `psiNegDefect C α t = C * t ^ α + ψ(t) - t`
   - `not_riemannHypothesis_imp_exists_shuniaCounterexample`
   - `exists_shuniaCounterexample_iff_not_riemannHypothesis_of_large`
-/

@[expose] public section

open Complex Finset Filter MeasureTheory Asymptotics Set Topology RiemannSchmidt
open scoped Real Topology Nat ENNReal LSeries.notation ArithmeticFunction

namespace Riemann120Analytic

open ConjectureMachines.Riemann120
  (shuniaProd offsetDigits shuniaDeficit quarterClock ShuniaCounterexample)

abbrev primorial : ℕ → ℕ := ConjectureMachines.Riemann120.primorial

/-!
## 2. Arithmetic & Logarithmic Lemmas
-/

theorem isPrimeBool_eq_true_iff (p : ℕ) :
    ConjectureMachines.Riemann120.isPrimeBool p = true ↔ Nat.Prime p := by
  simp only [ConjectureMachines.Riemann120.isPrimeBool, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    ← Nat.dvd_iff_mod_eq_zero]
  rw [Nat.prime_def_lt']
  exact ⟨fun ⟨hp, hall⟩ => ⟨hp, fun m hm hmp hdiv => (hall m hmp).resolve_left (by omega) hdiv⟩,
    fun ⟨hp, hall⟩ => ⟨hp, fun d hdp =>
      if hd2 : d < 2 then Or.inl hd2 else Or.inr (hall d (by omega) hdp)⟩⟩

theorem primorial_eq_root_primorial (n : ℕ) : primorial n = _root_.primorial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [primorial] at ih ⊢
    rw [ConjectureMachines.Riemann120.primorial, ih]
    conv_rhs => rw [_root_.primorial, Finset.range_add_one, Finset.filter_insert]
    by_cases hp : Nat.Prime (n + 1)
    · have hpb : ConjectureMachines.Riemann120.isPrimeBool (n + 1) = true :=
        (isPrimeBool_eq_true_iff (n + 1)).mpr hp
      simp [hp, hpb, _root_.primorial]
    · have hpb : ConjectureMachines.Riemann120.isPrimeBool (n + 1) = false :=
        Bool.eq_false_iff.mpr fun h => hp ((isPrimeBool_eq_true_iff (n + 1)).mp h)
      simp [hp, hpb, _root_.primorial]

theorem primorial_pos (n : ℕ) : 0 < primorial n := by
  rw [primorial_eq_root_primorial]
  exact _root_.primorial_pos n

theorem shuniaProd_pos (n : ℕ) : 0 < shuniaProd n :=
  Nat.mul_pos (Nat.factorial_pos n) (primorial_pos n)

theorem four_le_shuniaProd {n : ℕ} (hn : 2 ≤ n) : 4 ≤ shuniaProd n := by
  have hfac : 2 ≤ n.factorial := by
    calc 2 = (2 : ℕ).factorial := rfl
      _ ≤ n.factorial := Nat.factorial_le hn
  have hprim : 2 ≤ primorial n := by
    rw [primorial_eq_root_primorial]
    have hmem : 2 ∈ (Finset.range (n + 1)).filter Nat.Prime :=
      mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
    exact Nat.le_of_dvd (_root_.primorial_pos n) (dvd_prod_of_mem id hmem)
  unfold shuniaProd
  nlinarith

/-- `log(P(n)) = θ(n)` for every `n : ℕ`. -/
theorem log_primorial_eq_theta (n : ℕ) : Real.log (primorial n) = Chebyshev.theta n := by
  rw [primorial_eq_root_primorial, Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]

/-- `log(A_n) = log(n!) + θ(n)` for every `n : ℕ`. -/
theorem log_shuniaProd_eq (n : ℕ) :
    Real.log (shuniaProd n) = Real.log (n.factorial) + Chebyshev.theta n := by
  unfold shuniaProd
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by exact_mod_cast (primorial_pos n).ne'),
    log_primorial_eq_theta]

/-- Elementary step `((k + 1 : ℕ) : ℝ) * (Real.log k - Real.log (k + 1)) ≤ -1` for `k ≥ 1`. -/
lemma succ_mul_log_sub_log_succ_le_neg_one {k : ℕ} (hk : 1 ≤ k) :
    ((k + 1 : ℕ) : ℝ) * (Real.log k - Real.log (k + 1 : ℕ)) ≤ -1 := by
  have hk_pos : (0 : ℝ) < k := by positivity
  have hk1_pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hdiv_pos : (0 : ℝ) < (k : ℝ) / (k + 1 : ℕ) := div_pos hk_pos hk1_pos
  have hexp : (-1 / ((k + 1 : ℕ) : ℝ)) + 1 ≤ Real.exp (-1 / ((k + 1 : ℕ) : ℝ)) :=
    Real.add_one_le_exp _
  have heq : (-1 / ((k + 1 : ℕ) : ℝ)) + 1 = (k : ℝ) / (k + 1 : ℕ) := by
    push_cast; field_simp; ring
  rw [heq] at hexp
  have hlog : Real.log ((k : ℝ) / (k + 1 : ℕ)) ≤ -1 / ((k + 1 : ℕ) : ℝ) := by
    have h1 := Real.log_le_log hdiv_pos hexp
    rwa [Real.log_exp] at h1
  have hmul : ((k + 1 : ℕ) : ℝ) * Real.log ((k : ℝ) / (k + 1 : ℕ)) ≤ -1 := by
    have h := mul_le_mul_of_nonneg_left hlog hk1_pos.le
    have hc : ((k + 1 : ℕ) : ℝ) * (-1 / ((k + 1 : ℕ) : ℝ)) = -1 := by field_simp
    rwa [hc] at h
  rwa [Real.log_div hk_pos.ne' hk1_pos.ne'] at hmul

/-- Elementary step `(k : ℝ) * (Real.log (k + 1) - Real.log k) ≤ 1` for `k ≥ 1`. -/
lemma mul_log_succ_sub_log_le_one {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * (Real.log (k + 1 : ℕ) - Real.log k) ≤ 1 := by
  have hk_pos : (0 : ℝ) < k := by positivity
  have hk1_pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hexp : 1 / (k : ℝ) + 1 ≤ Real.exp (1 / (k : ℝ)) := Real.add_one_le_exp _
  have heq : 1 / (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) / (k : ℝ) := by
    push_cast; field_simp; ring
  rw [heq] at hexp
  have hlog : Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ≤ 1 / (k : ℝ) := by
    have h1 := Real.log_le_log (div_pos hk1_pos hk_pos) hexp
    rwa [Real.log_exp] at h1
  have hmul : (k : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hlog hk_pos.le
    have hc : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
    rwa [hc] at h
  rwa [Real.log_div hk1_pos.ne' hk_pos.ne'] at hmul

/-- Factorial centering bounds:
`n * log n - n + 1 ≤ log(n!) ≤ n * log n - n + 1 + log n` for all `n ≥ 1`. -/
theorem factorial_centering_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 ≤ Real.log (n.factorial) ∧
      Real.log (n.factorial) ≤ (n : ℝ) * Real.log n - n + 1 + Real.log n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
    · simp
    · obtain ⟨hlo, hhi⟩ := ih hk_pos
      have hfac : Real.log ((k + 1).factorial) =
          Real.log (k.factorial) + Real.log (k + 1 : ℕ) := by
        rw [Nat.factorial_succ, Nat.cast_mul,
          Real.log_mul (by positivity) (by positivity), add_comm]
      have hstep_hi := succ_mul_log_sub_log_succ_le_neg_one hk_pos
      have hstep_lo := mul_log_succ_sub_log_le_one hk_pos
      rw [hfac]
      push_cast at hfac hstep_lo hstep_hi ⊢
      constructor <;> linarith

/-- For `n ≥ 3`, `A_n = n! * P(n)` is never a power of `n`. -/
theorem shuniaProd_not_pow (n : ℕ) (hn : 3 ≤ n) (d : ℕ) : shuniaProd n ≠ n ^ d := by
  intro heq
  have hdvd_fac : n - 1 ∣ n.factorial := Nat.dvd_factorial (by omega) (by omega)
  have hdvd_prod : n - 1 ∣ shuniaProd n := dvd_mul_of_dvd_left hdvd_fac _
  rw [heq] at hdvd_prod
  have hcop : Nat.Coprime (n - 1) n := by
    have h1 : n = (n - 1) + 1 := by omega
    rw [h1]
    exact Nat.coprime_self_add_right.mpr (Nat.gcd_one_right _)
  have hdvd1 : n - 1 ∣ 1 := by
    have hpow := hcop.pow_right d
    exact hpow.dvd_of_dvd_mul_left (by simpa using hdvd_prod)
  have hle1 : n - 1 ≤ 1 := Nat.le_of_dvd zero_lt_one hdvd1
  omega

theorem offsetDigits_zero (b : ℕ) : offsetDigits b 0 = 0 := by
  rw [offsetDigits]

theorem offsetDigits_succ (b B : ℕ) :
    offsetDigits b (B + 1) = if 2 ≤ b then 1 + offsetDigits b (B / b) else 0 := by
  rw [offsetDigits]; split_ifs <;> rfl

/-- For `b ≥ 2` and `B ≥ 1`, `offsetDigits b B ≥ 1`. -/
theorem offsetDigits_pos {b B : ℕ} (hb : 2 ≤ b) (hB : 1 ≤ B) :
    1 ≤ offsetDigits b B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hB
  rw [offsetDigits_succ]
  simp only [hb, ↓reduceIte]
  omega

/-- Lower bound on `B` from `offsetDigits b B`: for `b ≥ 2` and `B ≥ 1`,
`b ^ (offsetDigits b B - 1) ≤ B`. -/
theorem pow_sub_one_le_of_offsetDigits {b : ℕ} (hb : 2 ≤ b) :
    ∀ {B : ℕ}, 1 ≤ B → b ^ (offsetDigits b B - 1) ≤ B
  | 0, hB => by omega
  | B + 1, _ => by
    rw [offsetDigits_succ]
    simp only [hb, ↓reduceIte, Nat.add_sub_cancel_left]
    rcases eq_or_lt_of_le (Nat.zero_le (B / b)) with h0 | hpos
    · rw [← h0, offsetDigits_zero, pow_zero]
      omega
    · calc b ^ offsetDigits b (B / b)
        _ = b * b ^ (offsetDigits b (B / b) - 1) := by
          have hd := offsetDigits_pos hb hpos
          conv_lhs => rw [← Nat.sub_add_cancel hd, pow_succ']
        _ ≤ b * (B / b) := Nat.mul_le_mul_left b (pow_sub_one_le_of_offsetDigits hb hpos)
        _ ≤ B := Nat.mul_div_le B b
        _ ≤ B + 1 := Nat.le_succ B
  termination_by B _ => B
  decreasing_by exact Nat.lt_succ_of_le (Nat.div_le_self B b)

/-- Strengthened induction invariant for `offsetDigits b B`: for `b ≥ 2` and every `B : ℕ`,
`B + b ≤ b ^ (offsetDigits b B + 1)`. -/
lemma add_le_pow_offsetDigits_add_one {b : ℕ} (hb : 2 ≤ b) :
    ∀ B : ℕ, B + b ≤ b ^ (offsetDigits b B + 1)
  | 0 => by
    rw [offsetDigits_zero, zero_add, zero_add, pow_one]
  | B + 1 => by
    rw [offsetDigits_succ]
    simp only [hb, ↓reduceIte]
    have ih := add_le_pow_offsetDigits_add_one hb (B / b)
    have hmul : b * (B / b + b) ≤ b * b ^ (offsetDigits b (B / b) + 1) :=
      Nat.mul_le_mul_left b ih
    have hdiv : B + 1 ≤ b * (B / b) + b := by
      have h1 := Nat.div_add_mod B b
      have h2 := Nat.mod_lt B (by omega : 0 < b)
      omega
    have hpow : b ^ (1 + offsetDigits b (B / b) + 1) =
        b * b ^ (offsetDigits b (B / b) + 1) := by
      rw [show 1 + offsetDigits b (B / b) + 1 = (offsetDigits b (B / b) + 1) + 1 by omega,
        pow_succ']
    rw [hpow]
    nlinarith
  termination_by B => B
  decreasing_by exact Nat.lt_succ_of_le (Nat.div_le_self B b)

/-- Upper bound on `B` from `offsetDigits b B`: for `b ≥ 2` and every `B : ℕ`,
`B < b ^ (offsetDigits b B + 1)`. -/
theorem offsetDigits_pow_gt {b : ℕ} (hb : 2 ≤ b) (B : ℕ) :
    B < b ^ (offsetDigits b B + 1) := by
  have h := add_le_pow_offsetDigits_add_one hb B
  omega

/-- Forward bridge inequality (`shuniaDeficit` to `θ`):
for every `n ≥ 2` with `1 ≤ shuniaDeficit n`, `(shuniaDeficit n : ℝ) * log n ≤ n - θ(n) - 1`. -/
theorem shuniaDeficit_mul_log_le {n : ℕ} (hn : 2 ≤ n) (hpos : 1 ≤ shuniaDeficit n) :
    (shuniaDeficit n : ℝ) * Real.log n ≤ (n : ℝ) - Chebyshev.theta n - 1 := by
  have hprod_le : shuniaProd n ≤ n ^ (offsetDigits n (shuniaProd n - 1) + 1) :=
    Nat.le_of_pred_lt (offsetDigits_pow_gt hn (shuniaProd n - 1))
  set d := offsetDigits n (shuniaProd n - 1)
  have hlog_le : Real.log (shuniaProd n) ≤ ((d + 1 : ℕ) : ℝ) * Real.log n := by
    have h1 : Real.log (shuniaProd n) ≤ Real.log ((n ^ (d + 1) : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast shuniaProd_pos n) (by exact_mod_cast hprod_le)
    rwa [Nat.cast_pow, Real.log_pow] at h1
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hfac_lo := (factorial_centering_bounds n (by omega)).1
  have hlog_eq := log_shuniaProd_eq n
  have hd_le : d ≤ n - 1 := by
    unfold shuniaDeficit at hpos
    omega
  unfold shuniaDeficit
  have hcast : ((n - 1 - d : ℕ) : ℝ) = (n : ℝ) - 1 - d := by
    rw [Nat.cast_sub hd_le, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hcast]
  push_cast at hlog_le
  nlinarith

/-- Reverse bridge inequality (`θ` to `shuniaDeficit`):
for every `n ≥ 2`, `(n : ℝ) - θ(n) ≤ (shuniaDeficit n + 3 : ℝ) * log n + 1`. -/
theorem self_sub_theta_le_shuniaDeficit_mul_log {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) - Chebyshev.theta n ≤ (shuniaDeficit n + 3 : ℝ) * Real.log n + 1 := by
  set d := offsetDigits n (shuniaProd n - 1)
  have h4 : 4 ≤ shuniaProd n := four_le_shuniaProd hn
  have hB1 : 1 ≤ shuniaProd n - 1 := by omega
  have hd1 : 1 ≤ d := offsetDigits_pos hn hB1
  have hpow_le : n ^ (d - 1) ≤ shuniaProd n :=
    (pow_sub_one_le_of_offsetDigits hn hB1).trans (Nat.sub_le _ 1)
  have hlog_lo : ((d - 1 : ℕ) : ℝ) * Real.log n ≤ Real.log (shuniaProd n) := by
    have h1 : Real.log ((n ^ (d - 1) : ℕ) : ℝ) ≤ Real.log (shuniaProd n) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hpow_le)
    rwa [Nat.cast_pow, Real.log_pow] at h1
  have hfac_hi := (factorial_centering_bounds n (by omega)).2
  have hlog_eq := log_shuniaProd_eq n
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hd_cast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd1, Nat.cast_one]
  rw [hd_cast] at hlog_lo
  have hdef_ge : (n : ℝ) - 1 - d ≤ (shuniaDeficit n : ℝ) := by
    unfold shuniaDeficit
    rcases le_or_gt d (n - 1) with hle | hgt
    · rw [Nat.cast_sub hle, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    · have hzero : n - 1 - d = 0 := Nat.sub_eq_zero_of_le hgt.le
      rw [hzero, Nat.cast_zero]
      have : (n - 1 : ℝ) < d := by
        have h1 : ((n - 1 : ℕ) : ℝ) < d := by exact_mod_cast hgt
        rwa [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h1
      linarith
  nlinarith

/-!
## 3. Quartering Clock & Unconditional Verification for `2 ≤ n ≤ 21845`
-/

lemma quarterClock_bounds_aux :
    ∀ z : ℕ, 4 ^ quarterClock z ≤ 3 * z + 1 ∧ 3 * z + 3 < 4 ^ (quarterClock z + 1)
  | 0 => by simp [quarterClock]
  | z + 1 => by
    rw [quarterClock]
    obtain ⟨hlo, hhi⟩ := quarterClock_bounds_aux (z / 4)
    have hdiv1 : 4 * (z / 4) ≤ z := Nat.mul_div_le z 4
    have hdiv2 : z < 4 * (z / 4) + 4 := by
      have h1 := Nat.div_add_mod z 4
      have h2 := Nat.mod_lt z (by omega : 0 < 4)
      omega
    have hpow1 : 4 ^ (1 + quarterClock (z / 4)) = 4 * 4 ^ quarterClock (z / 4) := by
      rw [Nat.add_comm 1, pow_succ']
    have hpow2 : 4 ^ (1 + quarterClock (z / 4) + 1) =
        4 * 4 ^ (quarterClock (z / 4) + 1) := by
      rw [show 1 + quarterClock (z / 4) + 1 = (quarterClock (z / 4) + 1) + 1 by omega,
        pow_succ']
    rw [hpow1, hpow2]
    constructor <;> omega

/-- Specification of the quartering clock:
`4 ^ quarterClock (n - 1) ≤ 3 * n < 4 ^ (quarterClock (n - 1) + 1)` for all `n ≥ 1`. -/
theorem quarterClock_spec (n : ℕ) (hn : 1 ≤ n) :
    4 ^ quarterClock (n - 1) ≤ 3 * n ∧ 3 * n < 4 ^ (quarterClock (n - 1) + 1) := by
  obtain ⟨hlo, hhi⟩ := quarterClock_bounds_aux (n - 1)
  exact ⟨by omega, by omega⟩

/-- Uniqueness of `quarterClock (n - 1)` from the `4 ^ q ≤ 3 * n < 4 ^ (q + 1)` sandwich. -/
theorem quarterClock_eq_of_bounds {n q : ℕ} (hn : 1 ≤ n)
    (hlo : 4 ^ q ≤ 3 * n) (hhi : 3 * n < 4 ^ (q + 1)) :
    quarterClock (n - 1) = q := by
  obtain ⟨hlo', hhi'⟩ := quarterClock_spec n hn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpow : 4 ^ (quarterClock (n - 1) + 1) ≤ 4 ^ q :=
      Nat.pow_le_pow_right (by omega) hlt
    omega
  · have hpow : 4 ^ (q + 1) ≤ 4 ^ quarterClock (n - 1) :=
      Nat.pow_le_pow_right (by omega) hgt
    omega

/-- General dyadic helper for `2 ≤ n ≤ 1365`:
if `a ≤ n ≤ b`, `4 ^ q ≤ 3 * n < 4 ^ (q + 1)`, `2 ^ m ≤ a ^ p` (`p ≥ 1`), and
`p * (b - 1) < (q + 1) * 2 ^ q * m * (693147 / 1000000)`, then `¬ ShuniaCounterexample n`. -/
lemma not_shuniaCounterexample_of_dyadic_small {n a b q m p : ℕ}
    (hn2 : 2 ≤ n) (ha : a ≤ n) (hb : n ≤ b) (hp : 1 ≤ p)
    (hlo : 4 ^ q ≤ 3 * n) (hhi : 3 * n < 4 ^ (q + 1))
    (hpow : 2 ^ m ≤ a ^ p)
    (hineq : (p : ℝ) * (b - 1 : ℝ) <
      ((q + 1) * 2 ^ q * m : ℝ) * (693147 / 1000000 : ℝ)) :
    ¬ ShuniaCounterexample n := by
  unfold ShuniaCounterexample
  rw [quarterClock_eq_of_bounds (by omega) hlo hhi]
  intro hce
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hpow_n : (2 : ℝ) ^ m ≤ (n : ℝ) ^ p := by
    have h1 : (a ^ p : ℕ) ≤ n ^ p := Nat.pow_le_pow_left ha p
    exact_mod_cast hpow.trans h1
  have hlog_m : (m : ℝ) * (693147 / 1000000 : ℝ) ≤ (p : ℝ) * Real.log n := by
    have h1 := Real.log_le_log (by positivity) hpow_n
    rw [Real.log_pow, Real.log_pow] at h1
    have hlog2 := Real.log_two_gt_d9
    nlinarith
  have hdef := shuniaDeficit_mul_log_le hn2 (by have := Nat.two_pow_pos q; nlinarith)
  have htheta : 0 ≤ Chebyshev.theta n := Chebyshev.theta_nonneg n
  have hce_r : (((q + 1) * 2 ^ q : ℕ) : ℝ) * Real.log n ≤ (n : ℝ) - 1 := by
    have h1 : (((q + 1) * 2 ^ q : ℕ) : ℝ) * Real.log n ≤
        (shuniaDeficit n : ℝ) * Real.log n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hce) hlog_pos.le
    linarith
  have hmul1 : (((q + 1) * 2 ^ q : ℕ) : ℝ) * ((m : ℝ) * (693147 / 1000000 : ℝ)) ≤
      (((q + 1) * 2 ^ q : ℕ) : ℝ) * ((p : ℝ) * Real.log n) :=
    mul_le_mul_of_nonneg_left hlog_m (by positivity)
  have hmul2 : (p : ℝ) * ((((q + 1) * 2 ^ q : ℕ) : ℝ) * Real.log n) ≤ (p : ℝ) * ((n : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left hce_r (by positivity)
  have hn_le_b : (n : ℝ) - 1 ≤ (b : ℝ) - 1 := by
    have : (n : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hmul3 : (p : ℝ) * ((n : ℝ) - 1) ≤ (p : ℝ) * ((b : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left hn_le_b (by positivity)
  push_cast at hmul1 hmul2
  linarith

/-- Unconditional verification for `2 ≤ n ≤ 1365` using only factorial centering. -/
theorem not_shuniaCounterexample_of_le_1365 {n : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ 1365) :
    ¬ ShuniaCounterexample n := by
  by_cases h3 : n ≤ 3
  · exact not_shuniaCounterexample_of_dyadic_small hn2 (a := 2) (b := 3) (q := 1)
      (m := 1) (p := 1) hn2 h3 (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
  by_cases h5 : n ≤ 5
  · exact not_shuniaCounterexample_of_dyadic_small hn2 (a := 4) (b := 5) (q := 1)
      (m := 2) (p := 1) (by omega) h5 (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
  by_cases h17 : n ≤ 17
  · exact not_shuniaCounterexample_of_dyadic_small hn2 (a := 6) (b := 17) (q := 2)
      (m := 2) (p := 1) (by omega) h17 (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
  by_cases h21 : n ≤ 21
  · exact not_shuniaCounterexample_of_dyadic_small hn2 (a := 18) (b := 21) (q := 2)
      (m := 4) (p := 1) (by omega) h21 (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
  by_cases h85 : n ≤ 85
  · exact not_shuniaCounterexample_of_dyadic_small hn2 (a := 22) (b := 85) (q := 3)
      (m := 4) (p := 1) (by omega) h85 (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
  by_cases h332 : n ≤ 332
  · exact not_shuniaCounterexample_of_dyadic_small hn2 (a := 86) (b := 332) (q := 4)
      (m := 6) (p := 1) (by omega) h332 (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
  by_cases h341 : n ≤ 341
  · exact not_shuniaCounterexample_of_dyadic_small hn2 (a := 333) (b := 341) (q := 4)
      (m := 8) (p := 1) (by omega) h341 (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
  by_cases h1023 : n ≤ 1023
  · exact not_shuniaCounterexample_of_dyadic_small hn2 (a := 342) (b := 1023) (q := 5)
      (m := 8) (p := 1) (by omega) h1023 (by omega) (by omega) (by omega) (by norm_num)
      (by norm_num)
  by_cases h1330 : n ≤ 1330
  · exact not_shuniaCounterexample_of_dyadic_small hn2 (a := 1024) (b := 1330) (q := 5)
      (m := 10) (p := 1) (by omega) h1330 (by omega) (by omega) (by omega) (by norm_num)
      (by norm_num)
  · exact not_shuniaCounterexample_of_dyadic_small hn2 (a := 1331) (b := 1365) (q := 5)
      (m := 31) (p := 3) (by omega) hn (by omega) (by omega) (by omega) (by norm_num) (by norm_num)

/-- General dyadic helper for `1366 ≤ n ≤ 21845` using `Chebyshev.theta_ge`:
if `a ≤ n ≤ b`, `4 ^ q ≤ 3 * n < 4 ^ (q + 1)`, `2 ^ m ≤ a`, `b ≤ S_hi ^ 2`, and
`(1 - 693147/1000000) * b < ((q + 1) * 2 ^ q - 2 * S_hi - 2) * m * 693147/1000000`,
then `¬ ShuniaCounterexample n`. -/
lemma not_shuniaCounterexample_of_chebyshev_dyadic {n a b q m S_hi : ℕ}
    (hn2 : 2 ≤ n) (ha : a ≤ n) (hb : n ≤ b)
    (hlo : 4 ^ q ≤ 3 * n) (hhi : 3 * n < 4 ^ (q + 1))
    (hpow : 2 ^ m ≤ a) (hsqrt : b ≤ S_hi ^ 2)
    (hW_pos : 2 * S_hi + 2 ≤ (q + 1) * 2 ^ q)
    (hineq : (1 - 693147 / 1000000 : ℝ) * (b : ℝ) <
      (((q + 1) * 2 ^ q : ℝ) - 2 * (S_hi : ℝ) - 2) * (m : ℝ) * (693147 / 1000000 : ℝ)) :
    ¬ ShuniaCounterexample n := by
  unfold ShuniaCounterexample
  rw [quarterClock_eq_of_bounds (by omega) hlo hhi]
  intro hce
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hpow_n : (2 : ℝ) ^ m ≤ (n : ℝ) := by
    exact_mod_cast hpow.trans ha
  have hlog_m : (m : ℝ) * (693147 / 1000000 : ℝ) ≤ Real.log n := by
    have h1 := Real.log_le_log (by positivity) hpow_n
    rw [Real.log_pow] at h1
    have hlog2 := Real.log_two_gt_d9
    nlinarith
  have hsqrt_le : Real.sqrt n ≤ (S_hi : ℝ) := by
    rw [Real.sqrt_le_left (by positivity)]
    exact_mod_cast hb.trans hsqrt
  have hlog_succ : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
    have hsq : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by
      have hn_r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      nlinarith
    have h1 := Real.log_le_log (by positivity) hsq
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  have htheta := Chebyshev.theta_ge n
  have hlog2 := Real.log_two_gt_d9
  have hdef := shuniaDeficit_mul_log_le hn2 (by have := Nat.two_pow_pos q; nlinarith)
  have hce_r : (((q + 1) * 2 ^ q : ℕ) : ℝ) * Real.log n ≤
      (shuniaDeficit n : ℝ) * Real.log n :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hce) hlog_pos.le
  have hn_le : (n : ℝ) ≤ b := by exact_mod_cast hb
  have hW_r : (0 : ℝ) ≤ ((q + 1) * 2 ^ q : ℝ) - 2 * (S_hi : ℝ) - 2 := by
    have : (2 * S_hi + 2 : ℝ) ≤ ((q + 1) * 2 ^ q : ℕ) := by exact_mod_cast hW_pos
    push_cast at this
    linarith
  push_cast at hce_r
  nlinarith

/-- **Unconditional Small-`n` Verification (`2 ≤ n ≤ 21845`)**:
No integer `n` in `[2, 21845]` satisfies `ShuniaCounterexample n` (`0` hypotheses). -/
theorem not_shuniaCounterexample_of_le_21845 {n : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ 21845) :
    ¬ ShuniaCounterexample n := by
  by_cases h1365 : n ≤ 1365
  · exact not_shuniaCounterexample_of_le_1365 hn2 h1365
  by_cases h5461 : n ≤ 5461
  · exact not_shuniaCounterexample_of_chebyshev_dyadic hn2 (a := 1366) (b := 5461) (q := 6)
      (m := 10) (S_hi := 74) (by omega) h5461 (by omega) (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  by_cases h16383 : n ≤ 16383
  · exact not_shuniaCounterexample_of_chebyshev_dyadic hn2 (a := 5462) (b := 16383) (q := 7)
      (m := 12) (S_hi := 128) (by omega) h16383 (by omega) (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  · exact not_shuniaCounterexample_of_chebyshev_dyadic hn2 (a := 16384) (b := 21845) (q := 7)
      (m := 14) (S_hi := 148) (by omega) hn (by omega) (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

/-!
## 4. One-Sided Landau Converse (`¬ RiemannHypothesis → ∃ n ≥ 2, ShuniaCounterexample n`)
-/

/-- The one-sided Chebyshev defect `g(t) = C * t ^ α + ψ(t) - t`. -/
noncomputable def psiNegDefect (C α : ℝ) (t : ℝ) : ℝ :=
  C * t ^ α + Chebyshev.psi t - t

theorem integrableOn_const_rpow_add_psi_sub_self_mul_cpow {s : ℂ} {C α : ℝ}
    (hα : α < s.re) (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ ↦
      ((C * t ^ α + Chebyshev.psi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hint_rpow :
      IntegrableOn (fun t : ℝ ↦ ((C * t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
    refine IntegrableOn.congr_fun ((integrableOn_rpow_mul_cpow hα).const_mul (C : ℂ))
      (fun t _ ↦ ?_) measurableSet_Ioi
    push_cast
    ring
  refine IntegrableOn.congr_fun
    ((hint_rpow.add (integrableOn_psi_mul_cpow hs)).sub (integrableOn_self_mul_cpow hs))
    (fun t _ ↦ ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, Pi.add_apply]
  push_cast
  ring

theorem mellin_const_rpow_add_psi_sub_self {s : ℂ} {C α : ℝ} (hα : α < s.re) (hs : 1 < s.re) :
    (C : ℂ) / (s - α) - 1 / (s - 1) - deriv riemannZeta s / (s * riemannZeta s) =
      ∫ t in Set.Ioi (1 : ℝ),
        ((C * t ^ α + Chebyshev.psi t - t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hpsi := neg_deriv_riemannZeta_div_eq_mul_integral_psi hs
  have hpsi_div :
      -deriv riemannZeta s / (s * riemannZeta s) =
        ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    calc
      -deriv riemannZeta s / (s * riemannZeta s)
        = (-deriv riemannZeta s / riemannZeta s) / s := by ring
      _ = (s * ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1))) / s := by
          rw [hpsi]
      _ = ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1)) :=
          mul_div_cancel_left₀ _ hs0
  have hrpow :
      (C : ℂ) / (s - α) =
        ∫ t in Set.Ioi (1 : ℝ), ((C * t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    calc
      (C : ℂ) / (s - α)
        = (C : ℂ) * ∫ t in Set.Ioi (1 : ℝ), ((t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
          rw [integral_Ioi_rpow_mul_cpow hα, mul_one_div]
      _ = ∫ t in Set.Ioi (1 : ℝ), (C : ℂ) * (((t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) :=
          (integral_const_mul _ _).symm
      _ = ∫ t in Set.Ioi (1 : ℝ), ((C * t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
          push_cast
          ring
  have hself := (integral_Ioi_self_mul_cpow hs).symm
  have hint_rpow :
      IntegrableOn (fun t : ℝ ↦ ((C * t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
    refine IntegrableOn.congr_fun ((integrableOn_rpow_mul_cpow hα).const_mul (C : ℂ))
      (fun t _ ↦ ?_) measurableSet_Ioi
    push_cast
    ring
  have hsub :
      (C : ℂ) / (s - α) - 1 / (s - 1) - deriv riemannZeta s / (s * riemannZeta s) =
        (C : ℂ) / (s - α) + (-deriv riemannZeta s / (s * riemannZeta s)) - 1 / (s - 1) := by
    ring
  rw [hsub, hrpow, hself, hpsi_div, ← integral_add hint_rpow (integrableOn_psi_mul_cpow hs)]
  have hint_add :
      IntegrableOn (fun a : ℝ ↦ ((C * a ^ α : ℝ) : ℂ) * (a : ℂ) ^ (-(s + 1)) +
        (Chebyshev.psi a : ℂ) * (a : ℂ) ^ (-(s + 1))) (Set.Ioi 1) :=
    hint_rpow.add (integrableOn_psi_mul_cpow hs)
  rw [← integral_sub hint_add (integrableOn_self_mul_cpow hs)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  push_cast
  ring

theorem mellin_neg_lhs_eq_completedPoleZeta {s : ℂ} {C α : ℝ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    (C : ℂ) / (s - α) - 1 / (s - 1) - deriv riemannZeta s / (s * riemannZeta s) =
      (C : ℂ) / (s - α) - 1 / s - deriv completedPoleZeta s / (s * completedPoleZeta s) := by
  have h1 : deriv completedPoleZeta s / (s * completedPoleZeta s) =
      (deriv completedPoleZeta s / completedPoleZeta s) / s := by ring
  rw [h1, deriv_completedPoleZeta_div_eq hs1 hz]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

theorem integrableOn_psiNegDefect_rpow_of_one_lt {C α σ : ℝ} (hα : α < σ) (hσ : 1 < σ) :
    IntegrableOn (fun t : ℝ ↦ psiNegDefect C α t * t ^ (-(σ + 1))) (Set.Ioi 1) := by
  have hα_c : α < (σ : ℂ).re := by simpa using hα
  have hσ_c : 1 < (σ : ℂ).re := by simpa using hσ
  have h_cpow := integrableOn_const_rpow_add_psi_sub_self_mul_cpow (C := C) hα_c hσ_c
  have h_re : IntegrableOn
      (fun t : ℝ ↦ (((C * t ^ α + Chebyshev.psi t - t : ℝ) : ℂ) *
        (t : ℂ) ^ (-((σ : ℂ) + 1))).re) (Set.Ioi 1) :=
    Complex.reCLM.integrable_comp h_cpow
  refine h_re.congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
  have ht_pos : 0 < t := zero_lt_one.trans ht
  have h_exp : -((σ : ℂ) + 1) = ((-(σ + 1) : ℝ) : ℂ) := by push_cast; ring
  dsimp [psiNegDefect]
  rw [h_exp, ← Complex.ofReal_cpow ht_pos.le, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem mellinLogDeriv_zero_psiNegDefect_eq_of_one_lt_re {C α : ℝ} {s : ℂ}
    (hα : α < s.re) (hs : 1 < s.re) :
    mellinLogDeriv (psiNegDefect C α) 0 s =
      (C : ℂ) / (s - α) - 1 / s - deriv completedPoleZeta s / (s * completedPoleZeta s) := by
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by
    intro h
    subst h
    simp at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  rw [← mellin_neg_lhs_eq_completedPoleZeta hs0 hs1 hz, mellin_const_rpow_add_psi_sub_self hα hs,
    mellinLogDeriv]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp [psiNegDefect]

theorem completedPoleZeta_mul_mellinLogDeriv_zero_psiNegDefect_eq {C α σ₀ : ℝ}
    (hα0 : 0 < α) (hασ₀ : α ≤ σ₀) (hσ₀1 : σ₀ ≤ 1)
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ psiNegDefect C α t)
    (hInt : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ ↦ psiNegDefect C α t * t ^ (-(σ + 1))) (Set.Ioi 1))
    {s : ℂ} (hs : σ₀ < s.re) :
    completedPoleZeta s * mellinLogDeriv (psiNegDefect C α) 0 s =
      ((C : ℂ) / (s - α) - 1 / s) * completedPoleZeta s - deriv completedPoleZeta s / s := by
  let U : Set ℂ := {z : ℂ | σ₀ < z.re}
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hPre : IsPreconnected U := (convex_halfPlane_re_gt σ₀).isPreconnected
  let G_lhs : ℂ → ℂ := fun z ↦ completedPoleZeta z * mellinLogDeriv (psiNegDefect C α) 0 z
  let G_rhs : ℂ → ℂ := fun z ↦
    ((C : ℂ) / (z - α) - 1 / z) * completedPoleZeta z - deriv completedPoleZeta z / z
  have hAn_lhs : AnalyticOnNhd ℂ G_lhs U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    exact (differentiable_completedPoleZeta z).differentiableWithinAt.mul
      (hasDerivAt_mellinLogDeriv hg_nonneg hInt 0 hz).differentiableAt.differentiableWithinAt
  have hAn_rhs : AnalyticOnNhd ℂ G_rhs U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    have hz_re : σ₀ < z.re := hz
    have hz_sub_ne : z - (α : ℂ) ≠ 0 := by
      intro hsub
      have hre := congrArg Complex.re (sub_eq_zero.mp hsub)
      simp only [ofReal_re] at hre
      linarith
    have hz_ne : z ≠ 0 := by
      intro hz0
      have hre := congrArg Complex.re hz0
      simp only [zero_re] at hre
      linarith
    have hd1 : DifferentiableAt ℂ (fun w : ℂ ↦ (C : ℂ) / (w - α) - 1 / w) z :=
      ((differentiableAt_const (C : ℂ)).div
        (differentiableAt_id.sub (differentiableAt_const (α : ℂ))) hz_sub_ne).sub
        ((differentiableAt_const (1 : ℂ)).div differentiableAt_id hz_ne)
    have hd2 : DifferentiableAt ℂ (fun w : ℂ ↦ deriv completedPoleZeta w / w) z :=
      (differentiable_completedPoleZeta.deriv z).div differentiableAt_id hz_ne
    exact ((hd1.mul (differentiable_completedPoleZeta z)).sub hd2).differentiableWithinAt
  have h2_mem : (2 : ℂ) ∈ U := by
    simp only [U, Set.mem_ofPred_eq]
    have : (2 : ℂ).re = 2 := by norm_num
    linarith
  have hEv : G_lhs =ᶠ[𝓝 (2 : ℂ)] G_rhs := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz_re : 1 < z.re := hz
    have hα_z : α < z.re := by linarith
    have hz0 : z ≠ 0 := ne_zero_of_one_lt_re hz_re
    have hz1 : z ≠ 1 := by
      intro h
      subst h
      simp at hz_re
    have hG_ne : completedPoleZeta z ≠ 0 := by
      rw [completedPoleZeta_of_ne_one hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_le_re hz_re.le)
    dsimp [G_lhs, G_rhs]
    rw [mellinLogDeriv_zero_psiNegDefect_eq_of_one_lt_re hα_z hz_re]
    field_simp
  exact hAn_lhs.eqOn_of_preconnected_of_eventuallyEq hAn_rhs hPre h2_mem hEv hs

theorem mellinLogDeriv_zero_psiNegDefect_eq_of_completedPoleZeta_ne_zero {C α σ₀ : ℝ}
    (hα0 : 0 < α) (hασ₀ : α ≤ σ₀) (hσ₀1 : σ₀ ≤ 1)
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ psiNegDefect C α t)
    (hInt : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ ↦ psiNegDefect C α t * t ^ (-(σ + 1))) (Set.Ioi 1))
    {s : ℂ} (hs : σ₀ < s.re) (hG : completedPoleZeta s ≠ 0) :
    mellinLogDeriv (psiNegDefect C α) 0 s =
      (C : ℂ) / (s - α) - 1 / s - deriv completedPoleZeta s / (s * completedPoleZeta s) := by
  have h_cleared :=
    completedPoleZeta_mul_mellinLogDeriv_zero_psiNegDefect_eq hα0 hασ₀ hσ₀1 hg_nonneg hInt hs
  have hs0 : s ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp only [zero_re] at hre
    linarith
  calc
    mellinLogDeriv (psiNegDefect C α) 0 s
      = (completedPoleZeta s * mellinLogDeriv (psiNegDefect C α) 0 s) / completedPoleZeta s := by
        rw [mul_div_cancel_left₀ _ hG]
    _ = (((C : ℂ) / (s - α) - 1 / s) * completedPoleZeta s - deriv completedPoleZeta s / s) /
          completedPoleZeta s := by
        rw [h_cleared]
    _ = (C : ℂ) / (s - α) - 1 / s - deriv completedPoleZeta s / (s * completedPoleZeta s) := by
        field_simp

/-- Pole-free analytic RHS `(C : ℂ) / (s - α) - 1 / s - deriv completedPoleZeta s / (s * G s)`. -/
noncomputable def poleFreeNegRHS (C α : ℝ) (s : ℂ) : ℂ :=
  (C : ℂ) / (s - α) - 1 / s - deriv completedPoleZeta s / (s * completedPoleZeta s)

/-- Domain of holomorphy `{s : ℂ | s - α ≠ 0 ∧ s ≠ 0 ∧ completedPoleZeta s ≠ 0}` is open and
`poleFreeNegRHS C α` is differentiable on it. -/
lemma isOpen_and_differentiableOn_poleFreeNegRHS (C α : ℝ) :
    let W : Set ℂ := {s : ℂ | s - (α : ℂ) ≠ 0 ∧ s ≠ 0 ∧ completedPoleZeta s ≠ 0}
    IsOpen W ∧ DifferentiableOn ℂ (poleFreeNegRHS C α) W := by
  intro W
  refine ⟨?_, ?_⟩
  · refine IsOpen.inter (IsOpen.preimage (continuous_id.sub continuous_const) isOpen_ne) ?_
    exact IsOpen.inter isOpen_ne (isOpen_ne.preimage differentiable_completedPoleZeta.continuous)
  · intro s hs
    obtain ⟨hs_α, hs_0, hs_G⟩ := hs
    have hd1 : DifferentiableAt ℂ (fun w : ℂ ↦ (C : ℂ) / (w - α) - 1 / w) s :=
      ((differentiableAt_const (C : ℂ)).div
        (differentiableAt_id.sub (differentiableAt_const (α : ℂ))) hs_α).sub
        ((differentiableAt_const (1 : ℂ)).div differentiableAt_id hs_0)
    have hd2 : DifferentiableAt ℂ
        (fun w : ℂ ↦ deriv completedPoleZeta w / (w * completedPoleZeta w)) s :=
      (differentiable_completedPoleZeta.deriv s).div
        (differentiableAt_id.mul (differentiable_completedPoleZeta s))
        (mul_ne_zero hs_0 hs_G)
    exact (hd1.sub hd2).differentiableWithinAt

/-- **Landau Continuation for `psiNegDefect`**:
If `0 ≤ C * t ^ α + ψ(t) - t` for all `t ≥ 1`, then its Mellin integral converges down to `α`. -/
theorem integrableOn_psiNegDefect_rpow_of_gt_alpha {C α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ psiNegDefect C α t) :
    ∀ σ : ℝ, α < σ →
      IntegrableOn (fun t : ℝ ↦ psiNegDefect C α t * t ^ (-(σ + 1))) (Set.Ioi 1) := by
  let S : Set ℝ := {σ₀ : ℝ | α ≤ σ₀ ∧
    ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ ↦ psiNegDefect C α t * t ^ (-(σ + 1))) (Set.Ioi 1)}
  have h1_mem : 1 ∈ S :=
    ⟨hα1.le, fun σ hσ ↦ integrableOn_psiNegDefect_rpow_of_one_lt (hα1.trans hσ) hσ⟩
  have hS_nonempty : S.Nonempty := ⟨1, h1_mem⟩
  have hS_bdd : BddBelow S := ⟨α, fun _ h ↦ h.1⟩
  let σ_star : ℝ := sInf S
  have hσ_star_ge : α ≤ σ_star := le_csInf hS_nonempty (fun _ h ↦ h.1)
  have hσ_star_le : σ_star ≤ 1 := csInf_le hS_bdd h1_mem
  have hσ_star_mem : σ_star ∈ S := by
    refine ⟨hσ_star_ge, fun σ hσ ↦ ?_⟩
    obtain ⟨σ₀, hσ₀_mem, hσ₀_lt⟩ := (csInf_lt_iff hS_bdd hS_nonempty).mp hσ
    exact hσ₀_mem.2 σ hσ₀_lt
  suffices h_eq : σ_star = α by
    intro σ hσ
    exact hσ_star_mem.2 σ (h_eq.symm ▸ hσ)
  by_contra h_ne
  have h_gt : α < σ_star := lt_of_le_of_ne hσ_star_ge (Ne.symm h_ne)
  have hσ_star_pos : 0 < σ_star := hα0.trans h_gt
  let W : Set ℂ := {s : ℂ | s - (α : ℂ) ≠ 0 ∧ s ≠ 0 ∧ completedPoleZeta s ≠ 0}
  obtain ⟨hW_open, hF_diff_W⟩ := isOpen_and_differentiableOn_poleFreeNegRHS C α
  have hz₀_mem : (σ_star : ℂ) ∈ W := by
    refine ⟨?_, Complex.ofReal_ne_zero.mpr hσ_star_pos.ne',
      completedPoleZeta_ofReal_ne_zero_of_pos hσ_star_pos⟩
    intro hsub
    have hre := congrArg Complex.re (sub_eq_zero.mp hsub)
    simp only [ofReal_re] at hre
    linarith
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.isOpen_iff.mp hW_open (σ_star : ℂ) hz₀_mem
  let r : ℝ := min (r₀ / 3) ((σ_star - α) / 2)
  have hr_pos : 0 < r := lt_min (by linarith) (by linarith)
  have hr_lt_r₀ : r ≤ r₀ / 3 := min_le_left _ _
  have hr_le_sub : r ≤ (σ_star - α) / 2 := min_le_right _ _
  let c : ℝ := σ_star + r / 2
  have hc_gt : σ_star < c := by dsimp [c]; linarith
  have hball_sub : Metric.ball (c : ℂ) r ⊆ W := by
    intro z hz
    apply hr₀_sub
    rw [Metric.mem_ball] at hz ⊢
    have hdist_c : dist (c : ℂ) (σ_star : ℂ) = r / 2 := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        show c - σ_star = r / 2 by dsimp [c]; ring, abs_of_pos (by linarith)]
    linarith [dist_triangle z (c : ℂ) (σ_star : ℂ)]
  have hc_mem_W : (c : ℂ) ∈ W := hball_sub (Metric.mem_ball_self hr_pos)
  have hEq : poleFreeNegRHS C α =ᶠ[𝓝 (c : ℂ)] mellinLogDeriv (psiNegDefect C α) 0 := by
    have h_nhds : W ∩ {z : ℂ | σ_star < z.re} ∈ 𝓝 (c : ℂ) :=
      Filter.inter_mem (hW_open.mem_nhds hc_mem_W)
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using hc_gt))
    filter_upwards [h_nhds] with z ⟨hzW, hz_re⟩
    exact (mellinLogDeriv_zero_psiNegDefect_eq_of_completedPoleZeta_ne_zero
      hα0 hσ_star_ge hσ_star_le hg_nonneg hσ_star_mem.2 hz_re hzW.2.2).symm
  have h_ext_mem : σ_star - r / 2 ∈ S := by
    refine ⟨by linarith, fun σ hσ ↦ ?_⟩
    exact integrableOn_of_analyticAt_real_of_gt hg_nonneg hσ_star_mem.2 hc_gt hr_pos
      (hF_diff_W.mono hball_sub) hEq (by dsimp [c]; linarith)
  linarith [csInf_le hS_bdd h_ext_mem]

lemma self_sub_psi_le_const_mul_rpow_of_forall_nat {K : ℝ} (hK : 0 < K)
    (h : ∀ x : ℕ, 253 < x → (x : ℝ) - Chebyshev.psi x ≤ K * Real.sqrt x * (Real.log x) ^ 2)
    {α : ℝ} (hα : 1 / 2 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → t - Chebyshev.psi t ≤ C * t ^ α := by
  set ε := (α - 1 / 2) / 2
  have hε : 0 < ε := by positivity
  refine ⟨K * (1 / ε) ^ 2 + 255, by positivity, fun t ht ↦ ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have ht_pos : 0 < t := by linarith
  have hlog_le : Real.log t ≤ t ^ ε / ε := Real.log_le_rpow_div ht0 hε
  have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht
  have hsq : (Real.log t) ^ 2 ≤ (1 / ε) ^ 2 * t ^ (α - 1 / 2) := by
    calc
      (Real.log t) ^ 2 ≤ (t ^ ε / ε) ^ 2 := pow_le_pow_left₀ hlog_nonneg hlog_le 2
      _ = (1 / ε) ^ 2 * (t ^ ε) ^ (2 : ℕ) := by ring
      _ = (1 / ε) ^ 2 * t ^ (ε * 2) := by
        rw [← Real.rpow_natCast (t ^ ε) 2, ← Real.rpow_mul ht0]
        norm_num
      _ = (1 / ε) ^ 2 * t ^ (α - 1 / 2) := by congr 2; ring
  have hrpow_ge_one : 1 ≤ t ^ α := Real.one_le_rpow ht (by linarith)
  by_cases hfloor : 253 < ⌊t⌋₊
  · have h_nat := h ⌊t⌋₊ hfloor
    have hfl_le : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
    have hfl_pos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (by omega : 0 < ⌊t⌋₊)
    have hlog_mono : Real.log ⌊t⌋₊ ≤ Real.log t := Real.log_le_log hfl_pos hfl_le
    have hlog_fl_nonneg : 0 ≤ Real.log ⌊t⌋₊ :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ ⌊t⌋₊))
    have hsq_mono : (Real.log ⌊t⌋₊) ^ 2 ≤ (Real.log t) ^ 2 :=
      pow_le_pow_left₀ hlog_fl_nonneg hlog_mono 2
    have hsqrt_mono : Real.sqrt ⌊t⌋₊ ≤ Real.sqrt t := Real.sqrt_le_sqrt hfl_le
    have hlt_add1 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
    have hmul_mono :
        K * Real.sqrt ⌊t⌋₊ * (Real.log ⌊t⌋₊) ^ 2 ≤ K * Real.sqrt t * (Real.log t) ^ 2 := by
      have h1 := mul_le_mul hsqrt_mono hsq_mono (by positivity) (by positivity)
      nlinarith
    have hrpow_prod : Real.sqrt t * t ^ (α - 1 / 2) = t ^ α := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht_pos]
      congr 1; ring
    have hmain : K * Real.sqrt t * (Real.log t) ^ 2 ≤ K * (1 / ε) ^ 2 * t ^ α := by
      have h1 := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ K * Real.sqrt t)
      calc K * Real.sqrt t * (Real.log t) ^ 2
        _ ≤ K * Real.sqrt t * ((1 / ε) ^ 2 * t ^ (α - 1 / 2)) := h1
        _ = K * (1 / ε) ^ 2 * (Real.sqrt t * t ^ (α - 1 / 2)) := by ring
        _ = K * (1 / ε) ^ 2 * t ^ α := by rw [hrpow_prod]
    have hpsi_eq : Chebyshev.psi t = Chebyshev.psi ⌊t⌋₊ := Chebyshev.psi_eq_psi_coe_floor t
    nlinarith
  · push Not at hfloor
    have hfl_le : (⌊t⌋₊ : ℝ) ≤ 253 := by exact_mod_cast hfloor
    have hlt_254 : t < 254 := by linarith [Nat.lt_floor_add_one t]
    have hpsi_nonneg : 0 ≤ Chebyshev.psi t := Chebyshev.psi_nonneg t
    have hpos_term : 0 ≤ K * (1 / ε) ^ 2 * t ^ α := by positivity
    nlinarith

/-- Residue contradiction at any zero `ρ` (`α < ρ.re < 1`) when `psiNegDefect C α ≥ 0`. -/
lemma not_riemannZeta_eq_zero_of_psiNegDefect_nonneg {C α : ℝ} {ρ : ℂ}
    (hα_pos : 0 < α) (hα_lt_ρ : α < ρ.re) (hρ_lt : ρ.re < 1)
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ psiNegDefect C α t) :
    riemannZeta ρ ≠ 0 := by
  intro hρ_zero
  have hα_lt_one : α < 1 := hα_lt_ρ.trans hρ_lt
  have hInt_α := integrableOn_psiNegDefect_rpow_of_gt_alpha hα_pos hα_lt_one hg_nonneg
  have h_cont_mellin : ContinuousAt (mellinLogDeriv (psiNegDefect C α) 0) ρ :=
    (hasDerivAt_mellinLogDeriv hg_nonneg hInt_α 0 hα_lt_ρ).continuousAt
  have h_lhs_tendsto :
      Tendsto (fun z : ℂ ↦ (z - ρ) * mellinLogDeriv (psiNegDefect C α) 0 z) (𝓝[≠] ρ) (𝓝 0) := by
    have h0 :=
      (continuousAt_id.tendsto.sub (tendsto_const_nhds (x := ρ))).mul h_cont_mellin.tendsto
    simpa using h0.mono_left nhdsWithin_le_nhds
  have hρ1 : ρ ≠ 1 := fun h1 ↦ by simp [h1] at hρ_lt
  have hρ0 : ρ ≠ 0 := fun h0 ↦ by rw [h0, zero_re] at hα_lt_ρ; linarith
  set m := analyticOrderNatAt riemannZeta ρ
  have hm_ge_one : 1 ≤ m := one_le_analyticOrderNatAt_of_riemannZeta_eq_zero hρ1 hρ_zero
  have hm_ne_zero : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_res := tendsto_sub_mul_deriv_riemannZeta_div_of_eq_zero hρ1 hρ_zero
  have h_zeta_ne : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z ≠ 0 := by
    filter_upwards [h_res.eventually_ne hm_ne_zero] with z hz h_zero
    exact hz (by simp [h_zero])
  have h_open_nhds : ∀ᶠ z in 𝓝[≠] ρ, α < z.re ∧ z ≠ 1 ∧ z ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds <|
      Filter.Eventually.and
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hα_lt_ρ)
        (Filter.Eventually.and (eventually_ne_nhds hρ1) (eventually_ne_nhds hρ0))
  have h_congr :
      (fun z : ℂ ↦ (z - ρ) * mellinLogDeriv (psiNegDefect C α) 0 z) =ᶠ[𝓝[≠] ρ]
        fun z : ℂ ↦ (z - ρ) * ((C : ℂ) / (z - α) - 1 / (z - 1)) -
          ((z - ρ) * (deriv riemannZeta z / riemannZeta z)) / z := by
    filter_upwards [h_zeta_ne, h_open_nhds] with z hz_zeta ⟨hz_α, hz_1, hz_0⟩
    have hG_ne : completedPoleZeta z ≠ 0 := by
      rw [completedPoleZeta_of_ne_one hz_1]
      exact mul_ne_zero (sub_ne_zero.mpr hz_1) hz_zeta
    rw [mellinLogDeriv_zero_psiNegDefect_eq_of_completedPoleZeta_ne_zero
      hα_pos le_rfl hα_lt_one.le hg_nonneg hInt_α hz_α hG_ne,
      ← mellin_neg_lhs_eq_completedPoleZeta hz_0 hz_1 hz_zeta]
    ring
  have h_ρ_sub_α : ρ - (α : ℂ) ≠ 0 := fun hsub ↦ by
    have hre := congrArg Complex.re (sub_eq_zero.mp hsub); simp only [ofReal_re] at hre; linarith
  have h_first_tendsto :
      Tendsto (fun z : ℂ ↦ (z - ρ) * ((C : ℂ) / (z - α) - 1 / (z - 1))) (𝓝[≠] ρ) (𝓝 0) := by
    have h_inner :
        Tendsto (fun z : ℂ ↦ (C : ℂ) / (z - α) - 1 / (z - 1)) (𝓝 ρ)
          (𝓝 ((C : ℂ) / (ρ - α) - 1 / (ρ - 1))) :=
      (tendsto_const_nhds.div (continuousAt_id.tendsto.sub tendsto_const_nhds) h_ρ_sub_α).sub
        (tendsto_const_nhds.div (continuousAt_id.tendsto.sub tendsto_const_nhds)
          (sub_ne_zero.mpr hρ1))
    simpa using
      ((continuousAt_id.tendsto.sub (tendsto_const_nhds (x := ρ))).mul h_inner).mono_left
        nhdsWithin_le_nhds
  have h_rhs_tendsto :
      Tendsto (fun z : ℂ ↦ (z - ρ) * ((C : ℂ) / (z - α) - 1 / (z - 1)) -
          ((z - ρ) * (deriv riemannZeta z / riemannZeta z)) / z)
        (𝓝[≠] ρ) (𝓝 (-(m : ℂ) / ρ)) := by
    simpa [neg_div] using h_first_tendsto.sub
      (h_res.div (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hρ0)
  have h_eq_lim : (0 : ℂ) = -(m : ℂ) / ρ :=
    tendsto_nhds_unique h_lhs_tendsto (h_rhs_tendsto.congr' h_congr.symm)
  exact div_ne_zero (neg_ne_zero.mpr hm_ne_zero) hρ0 h_eq_lim.symm

/-- **One-Sided Landau Oscillation Theorem (`t - ψ(t)`)**:
If `¬ RiemannHypothesis`, then for every constant `K > 0`, there exists `x : ℕ` with `253 < x`
and `K * Real.sqrt x * (Real.log x) ^ 2 < (x : ℝ) - Chebyshev.psi x`. -/
theorem not_riemannHypothesis_imp_exists_self_sub_psi_gt
    (hNotRH : ¬ RiemannHypothesis) {K : ℝ} (hK : 0 < K) :
    ∃ x : ℕ, 253 < x ∧ K * Real.sqrt x * (Real.log x) ^ 2 < (x : ℝ) - Chebyshev.psi x := by
  by_contra! h_no
  obtain ⟨ρ, hρ_zero, hρ_gt, hρ_lt⟩ :=
    exists_zero_in_right_critical_strip_of_not_riemannHypothesis hNotRH
  set α : ℝ := (1 / 2 + ρ.re) / 2 with hα
  obtain ⟨C, _hC_pos, h_bound⟩ :=
    self_sub_psi_le_const_mul_rpow_of_forall_nat (α := α) hK h_no (by linarith [hα])
  exact not_riemannZeta_eq_zero_of_psiNegDefect_nonneg (C := C) (α := α)
    (by linarith [hα]) (by linarith [hα]) hρ_lt
    (fun t ht ↦ by dsimp [psiNegDefect]; linarith [h_bound t ht]) hρ_zero

/-- If `x > 253` satisfies `10 * √x * (log x)^2 < x - ψ(x)`, then `ShuniaCounterexample x` holds. -/
theorem shuniaCounterexample_of_self_sub_psi_gt {x : ℕ} (hx : 253 < x)
    (hpsi : 10 * Real.sqrt x * (Real.log x) ^ 2 < (x : ℝ) - Chebyshev.psi x) :
    ShuniaCounterexample x := by
  by_contra hno
  unfold ShuniaCounterexample at hno
  push Not at hno
  set q := quarterClock (x - 1)
  have hx2 : 2 ≤ x := by omega
  obtain ⟨hlo, _⟩ := quarterClock_spec x (by omega)
  have h2q_sq : ((2 ^ q : ℕ) : ℝ) ^ 2 ≤ 3 * (x : ℝ) := by
    have h4 : (2 ^ q) ^ 2 = 4 ^ q := by
      calc (2 ^ q) ^ 2 = (2 ^ 2) ^ q := (pow_right_comm 2 q 2)
        _ = 4 ^ q := by norm_num
    exact_mod_cast h4.le.trans hlo
  have h2q_le : ((2 ^ q : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
    have hsq_x : (2 * Real.sqrt x) ^ 2 = 4 * (x : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      norm_num
    have hle4 : ((2 ^ q : ℕ) : ℝ) ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := by linarith
    exact le_of_sq_le_sq hle4 (by positivity)
  have hq_log : (q : ℝ) ≤ 3 * Real.log x := by
    have hpow_le : (2 : ℝ) ^ q ≤ (x : ℝ) ^ 2 := by
      have h3x : (3 * x : ℝ) ≤ (x : ℝ) ^ 2 := by
        have hx_r : (4 : ℝ) ≤ x := by exact_mod_cast (by omega : 4 ≤ x)
        nlinarith
      have h2_le_4 : (2 : ℝ) ^ q ≤ (4 : ℝ) ^ q :=
        pow_le_pow_left₀ (by positivity) (by norm_num) q
      have h4_le : (4 : ℝ) ^ q ≤ 3 * (x : ℝ) := by exact_mod_cast hlo
      linarith
    have hlog_ineq := Real.log_le_log (by positivity) hpow_le
    rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat] at hlog_ineq
    have hlog2 := Real.log_two_gt_d9
    nlinarith
  have hlog_pos : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx2)
  have hlog_ge5 : (5 : ℝ) ≤ Real.log x := by
    have hpow : (2 : ℝ) ^ 15 ≤ (x : ℝ) ^ 2 := by
      have hx_r : (254 : ℝ) ≤ x := by exact_mod_cast (by omega : 254 ≤ x)
      nlinarith
    have h1 := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat, Nat.cast_ofNat] at h1
    have hlog2 := Real.log_two_gt_d9
    linarith
  have hsqrt_ge15 : (15 : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have hx_r : (254 : ℝ) ≤ x := by exact_mod_cast (by omega : 254 ≤ x)
    nlinarith
  have hdef_le : (shuniaDeficit x : ℝ) ≤ 8 * Real.sqrt x * Real.log x := by
    have h1 : (shuniaDeficit x : ℝ) ≤ ((q + 1) * 2 ^ q : ℕ) := by exact_mod_cast hno.le
    have hq1 : ((q + 1 : ℕ) : ℝ) ≤ 4 * Real.log x := by push_cast; linarith
    have hprod : ((q + 1 : ℕ) : ℝ) * ((2 ^ q : ℕ) : ℝ) ≤
        (4 * Real.log x) * (2 * Real.sqrt x) :=
      mul_le_mul hq1 h2q_le (by positivity) (by positivity)
    push_cast at h1 hprod ⊢
    linarith
  have htheta_le := self_sub_theta_le_shuniaDeficit_mul_log hx2
  have hpsi_ge_theta : Chebyshev.theta x ≤ Chebyshev.psi x := Chebyshev.theta_le_psi x
  nlinarith

/-- **One-Sided Landau Converse (`¬ RiemannHypothesis → ∃ n ≥ 2, ShuniaCounterexample n`)**:
If `RiemannHypothesis` is false, there exists `n ≥ 2` satisfying `ShuniaCounterexample n`. -/
theorem not_riemannHypothesis_imp_exists_shuniaCounterexample
    (hNotRH : ¬ RiemannHypothesis) :
    ∃ n ≥ 2, ShuniaCounterexample n := by
  obtain ⟨x, hx, hpsi⟩ :=
    not_riemannHypothesis_imp_exists_self_sub_psi_gt hNotRH (K := 10) (by norm_num)
  exact ⟨x, by omega, shuniaCounterexample_of_self_sub_psi_gt hx hpsi⟩

/-!
## 5. Final Equivalence Bridge
-/

/-- If `(n : ℝ) - θ(n) < (q_n + 1) * 2 ^ q_n * log n` for `n ≥ 2`, then
`¬ ShuniaCounterexample n`. -/
theorem not_shuniaCounterexample_of_theta_bound {n : ℕ} (hn2 : 2 ≤ n)
    (hbound : (n : ℝ) - Chebyshev.theta n <
      ((quarterClock (n - 1) + 1) * 2 ^ quarterClock (n - 1) : ℝ) * Real.log n) :
    ¬ ShuniaCounterexample n := by
  intro hce
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hce_r :
      (((quarterClock (n - 1) + 1) * 2 ^ quarterClock (n - 1) : ℕ) : ℝ) * Real.log n ≤
        (shuniaDeficit n : ℝ) * Real.log n :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hce) hlog_pos.le
  have hdef := shuniaDeficit_mul_log_le hn2 (by
    have := Nat.two_pow_pos (quarterClock (n - 1))
    unfold ShuniaCounterexample at hce
    nlinarith)
  push_cast at hce_r
  linarith

/-- Schoenfeld's explicit bound `(n : ℝ) - θ(n) < √n * (log n)^2 / (8 * π)` (or even
`≤ (1 / 2) * √n * (log n)^2`) implies the large-`n` quartering threshold for all `n ≥ 2`. -/
theorem large_theta_bound_of_half_sqrt_log_sq {n : ℕ} (hn2 : 2 ≤ n)
    (hbound : (n : ℝ) - Chebyshev.theta n ≤ (1 / 2 : ℝ) * Real.sqrt n * (Real.log n) ^ 2) :
    (n : ℝ) - Chebyshev.theta n <
      ((quarterClock (n - 1) + 1) * 2 ^ quarterClock (n - 1) : ℝ) * Real.log n := by
  set q := quarterClock (n - 1)
  obtain ⟨_, hhi⟩ := quarterClock_spec n (by omega)
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hsqrt_lt : Real.sqrt n < ((2 ^ (q + 1) : ℕ) : ℝ) / Real.sqrt 3 := by
    rw [lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    have hsq_lhs : (Real.sqrt n * Real.sqrt 3) ^ 2 = 3 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
      ring
    have hsq_rhs : ((2 ^ (q + 1) : ℕ) : ℝ) ^ 2 = ((4 ^ (q + 1) : ℕ) : ℝ) := by
      have h4 : (2 ^ (q + 1)) ^ 2 = 4 ^ (q + 1) := by
        calc (2 ^ (q + 1)) ^ 2 = (2 ^ 2) ^ (q + 1) := pow_right_comm 2 (q + 1) 2
          _ = 4 ^ (q + 1) := by norm_num
      exact_mod_cast h4
    have hlt_sq : (Real.sqrt n * Real.sqrt 3) ^ 2 < ((2 ^ (q + 1) : ℕ) : ℝ) ^ 2 := by
      rw [hsq_lhs, hsq_rhs]
      exact_mod_cast hhi
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt_sq
  have hsqrt3_gt : (17 / 10 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrt_le : Real.sqrt n ≤ (20 / 17 : ℝ) * ((2 ^ q : ℕ) : ℝ) := by
    have h2 : ((2 ^ (q + 1) : ℕ) : ℝ) / (17 / 10 : ℝ) =
        (20 / 17 : ℝ) * ((2 ^ q : ℕ) : ℝ) := by
      rw [pow_succ']
      push_cast
      ring
    have hdiv : ((2 ^ (q + 1) : ℕ) : ℝ) / Real.sqrt 3 ≤
        ((2 ^ (q + 1) : ℕ) : ℝ) / (17 / 10 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hsqrt3_gt.le
    linarith
  have hlog_lt : Real.log n < ((q + 1 : ℕ) : ℝ) * (7 / 5 : ℝ) := by
    have h_lt4 : (n : ℝ) < ((4 ^ (q + 1) : ℕ) : ℝ) := by
      have h3 : (3 * n : ℝ) < ((4 ^ (q + 1) : ℕ) : ℝ) := by exact_mod_cast hhi
      linarith
    have h1 := Real.log_lt_log (by positivity) h_lt4
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at h1
    have hlog4 : Real.log 4 < 7 / 5 := by
      have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [h4, Real.log_pow, Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]
    have hq1_pos : (0 : ℝ) < (q + 1 : ℕ) := by positivity
    nlinarith
  have hprod :
      (1 / 2 : ℝ) * Real.sqrt n * Real.log n <
        (1 / 2 : ℝ) * ((20 / 17 : ℝ) * ((2 ^ q : ℕ) : ℝ)) * (((q + 1 : ℕ) : ℝ) * (7 / 5 : ℝ)) := by
    have h1 : Real.sqrt n * Real.log n <
        ((20 / 17 : ℝ) * ((2 ^ q : ℕ) : ℝ)) * (((q + 1 : ℕ) : ℝ) * (7 / 5 : ℝ)) :=
      mul_lt_mul' hsqrt_le hlog_lt hlog_pos.le (by positivity)
    nlinarith
  have hcoeff :
      (1 / 2 : ℝ) * ((20 / 17 : ℝ) * ((2 ^ q : ℕ) : ℝ)) * (((q + 1 : ℕ) : ℝ) * (7 / 5 : ℝ)) =
        (14 / 17 : ℝ) * ((q + 1) * 2 ^ q : ℝ) := by
    push_cast
    ring
  have hpos_rhs : (0 : ℝ) < ((q + 1) * 2 ^ q : ℝ) := by
    have h2 : (0 : ℝ) < ((2 ^ q : ℕ) : ℝ) := by positivity
    push_cast at h2 ⊢
    nlinarith
  nlinarith

/-- **Main Bridge Theorem (`ShuniaCounterexample ↔ ¬ RiemannHypothesis`)**:
Given the large-`n` RH bound (`n ≥ 21846`), there exists `n ≥ 2` satisfying
`ShuniaCounterexample n` if and only if `¬ RiemannHypothesis`. -/
theorem exists_shuniaCounterexample_iff_not_riemannHypothesis_of_large
    (hLarge : RiemannHypothesis → ∀ n : ℕ, 21846 ≤ n →
      (n : ℝ) - Chebyshev.theta n <
        ((quarterClock (n - 1) + 1) * 2 ^ quarterClock (n - 1) : ℝ) * Real.log n) :
    (∃ n ≥ 2, ShuniaCounterexample n) ↔ ¬ RiemannHypothesis := by
  constructor
  · rintro ⟨n, hn2, hce⟩ hRH
    rcases le_or_gt n 21845 with hsmall | hlarge
    · exact not_shuniaCounterexample_of_le_21845 hn2 hsmall hce
    · exact not_shuniaCounterexample_of_theta_bound hn2 (hLarge hRH n (by omega)) hce
  · exact not_riemannHypothesis_imp_exists_shuniaCounterexample

/-!
## 5. Exact 5-Register Machine Alignment Exports
-/

/-- Exact prime-product register value `P(n) = ∏_{1 ≤ p ≤ n, p prime} p`. -/
def shuniaPrimorial (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter Nat.Prime).prod id

/-- Exact base-`n` offset-digit deficit `Δ_n = n - 1 - offsetDigits n (n! * P(n) - 1)`. -/
def shuniaDeficitExact (n : ℕ) : ℕ :=
  n - 1 - offsetDigits n (shuniaProd n - 1)

/-- Exact recursive quartering clock step `quarterClockStep z = quarterClock z`. -/
def quarterClockStep : ℕ → ℕ
  | 0 => 0
  | z + 1 => 1 + quarterClockStep (z / 4)

/-- Exact machine counterexample predicate `2 ≤ n ∧ (q_n + 1) * 2 ^ q_n ≤ Δ_n`. -/
def ShuniaCounterexampleExact (n : ℕ) : Prop :=
  2 ≤ n ∧
    (quarterClockStep (n - 1) + 1) * 2 ^ quarterClockStep (n - 1) ≤
      shuniaDeficitExact n

theorem quarterClockStep_eq_quarterClock : ∀ z : ℕ, quarterClockStep z = quarterClock z
  | 0 => by simp [quarterClockStep, quarterClock]
  | z + 1 => by
    rw [quarterClockStep, quarterClock]
    exact congrArg (1 + ·) (quarterClockStep_eq_quarterClock (z / 4))

theorem shuniaCounterexampleExact_iff {n : ℕ} :
    ShuniaCounterexampleExact n ↔ 2 ≤ n ∧ ShuniaCounterexample n := by
  simp only [ShuniaCounterexampleExact, ShuniaCounterexample, quarterClockStep_eq_quarterClock,
    shuniaDeficitExact, shuniaDeficit]

theorem shuniaDeficitExact_mul_log_le {n : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ shuniaDeficitExact n) :
    (shuniaDeficitExact n : ℝ) * Real.log n ≤ (n : ℝ) - Chebyshev.theta n - 1 :=
  shuniaDeficit_mul_log_le hn hd

theorem not_shuniaCounterexampleExact_of_le_21845 {n : ℕ} (hn : n ≤ 21845) :
    ¬ ShuniaCounterexampleExact n := by
  rw [shuniaCounterexampleExact_iff]
  exact fun ⟨hn2, hce⟩ ↦ not_shuniaCounterexample_of_le_21845 hn2 hn hce

theorem exists_shuniaCounterexampleExact_iff_not_riemannHypothesis_of_large
    (hLarge : RiemannHypothesis → ∀ n : ℕ, 21845 < n →
      (n : ℝ) - Chebyshev.theta n ≤
        ((quarterClockStep (n - 1) + 1) * 2 ^ quarterClockStep (n - 1) : ℝ) * Real.log n) :
    (∃ n : ℕ, ShuniaCounterexampleExact n) ↔ ¬ RiemannHypothesis := by
  constructor
  · rintro ⟨n, hce⟩ hRH
    rcases le_or_gt n 21845 with hsmall | hlarge
    · exact not_shuniaCounterexampleExact_of_le_21845 hsmall hce
    · obtain ⟨hn2, hdef⟩ := hce
      have hpos : 1 ≤ shuniaDeficitExact n := by
        have hpow : 1 ≤ 2 ^ quarterClockStep (n - 1) := Nat.one_le_two_pow
        have lhs_ge : 1 ≤ (quarterClockStep (n - 1) + 1) * 2 ^ quarterClockStep (n - 1) := by
          nlinarith
        exact lhs_ge.trans hdef
      have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
      have hmul :
          ((quarterClockStep (n - 1) + 1) * 2 ^ quarterClockStep (n - 1) : ℝ) * Real.log n ≤
            (shuniaDeficitExact n : ℝ) * Real.log n :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hdef) hlog_pos.le
      have h_upper := shuniaDeficitExact_mul_log_le hn2 hpos
      have h_rh := hLarge hRH n hlarge
      linarith
  · intro hNotRH
    obtain ⟨n, hn2, hce⟩ := not_riemannHypothesis_imp_exists_shuniaCounterexample hNotRH
    exact ⟨n, shuniaCounterexampleExact_iff.mpr ⟨hn2, hce⟩⟩

end Riemann120Analytic

end

