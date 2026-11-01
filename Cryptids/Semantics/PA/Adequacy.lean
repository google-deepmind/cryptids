/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.PA.Syntax
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Standard-Model Adequacy of `paHalts` and `paZFInconsistent`

This module proves that the closed $\Sigma_1^0$ $\mathcal{L}_{\mathrm{PA}}$-sentences `paHalts M`
and `paZFInconsistent` (`Cryptids.Propositions`) faithfully represent binary Turing machine halting
and `ZF` inconsistency in the standard model `ℕ`:

- `paHalts_holds_iff_halts`: `(paHalts M).Holds v ↔ ConjectureMachines.Halts M`
- `paZFInconsistent_holds_iff_zfInconsistent`: `paZFInconsistent.Holds v ↔ ZFInconsistent`

Both equivalences are proved **constructively** without `Classical.choice` (verified by
`leanprover/comparator` under `comparator/constructive.json`).
-/

@[expose] public section

namespace ConjectureMachines

/-- Evaluate a symbolic `PAZFTerm` in `ℕ` under assignment `v`. -/
def PAZFTerm.eval (v : ℕ → ℕ) : PAZFTerm → ℕ
  | .var x => v x
  | .const n => n
  | .pair a b => cantorPair (a.eval v) (b.eval v)

/-- Smallest variable index strictly greater than every variable in a `PAZFTerm`. -/
def PAZFTerm.freshVar : PAZFTerm → ℕ
  | .var x => x + 1
  | .const _ => 0
  | .pair a b => max a.freshVar b.freshVar

end ConjectureMachines

namespace ConjectureMachines.Semantics.PA

attribute [-simp] Nat.add_eq_right Nat.left_eq_add Nat.right_eq_add
  Order.add_one_le_iff Order.lt_add_one_iff Function.update_idem

@[simp high] private theorem nat_add_eq_right {n m : ℕ} : n + m = n ↔ m = 0 := by
  constructor <;> intro h <;> omega

@[simp high] private theorem nat_left_eq_add {n m : ℕ} : n = n + m ↔ m = 0 := by
  constructor <;> intro h <;> omega

@[simp high] private theorem nat_right_eq_add {n m : ℕ} : n = m + n ↔ m = 0 := by
  constructor <;> intro h <;> omega

/-! ## Section 1: Basic Standard-Model Evaluation and Arithmetic Gadgets -/

@[simp]
theorem eval_ofNat (v : ℕ → ℕ) (n : ℕ) : (PATerm.ofNat n).eval v = n := by
  induction n with
  | zero => rfl
  | succ _ ih => exact congrArg (· + 1) ih

theorem eval_update_of_freshVar_le (v : ℕ → ℕ) {t : PATerm} {x : ℕ} (a : ℕ)
    (h : t.freshVar ≤ x) : t.eval (Function.update v x a) = t.eval v := by
  rw [← evalIn_nat_eq, ← evalIn_nat_eq]
  exact evalIn_update_of_hasVar_false v a (hasVar_false_of_freshVar_le h)

theorem paLe_holds_iff (v : ℕ → ℕ) (a b : PATerm) :
    (paLe a b).Holds v ↔ a.eval v ≤ b.eval v := by
  unfold paLe
  set k := max a.freshVar b.freshVar
  have ha : a.freshVar ≤ k := Nat.le_max_left _ _
  have hb : b.freshVar ≤ k := Nat.le_max_right _ _
  simp only [PAFormula.Holds, PATerm.eval, eval_update_of_freshVar_le v _ ha,
    eval_update_of_freshVar_le v _ hb, Function.update_self]
  exact ⟨fun ⟨w, hw⟩ ↦ Nat.le.intro hw, fun h ↦ ⟨b.eval v - a.eval v, Nat.add_sub_of_le h⟩⟩

theorem paLt_holds_iff (v : ℕ → ℕ) (a b : PATerm) :
    (paLt a b).Holds v ↔ a.eval v < b.eval v := by
  unfold paLt
  rw [paLe_holds_iff]
  rfl

private theorem two_dvd_mul_succ (n : ℕ) : 2 ∣ n * (n + 1) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + (n + 1), ?_⟩
    calc (n + 1) * (n + 2)
      _ = (n + 1) * n + (n + 1) * 2 := Nat.mul_add (n + 1) n 2
      _ = n * (n + 1) + 2 * (n + 1) := by rw [Nat.mul_comm (n + 1) n, Nat.mul_comm (n + 1) 2]
      _ = 2 * (k + (n + 1)) := by omega

theorem paCantorPairEq_holds_iff (v : ℕ → ℕ) (x y z : PATerm) :
    (paCantorPairEq x y z).Holds v ↔ z.eval v = cantorPair (x.eval v) (y.eval v) := by
  unfold paCantorPairEq cantorPair
  simp only [PAFormula.Holds, PATerm.eval, eval_ofNat]
  obtain ⟨k, hk⟩ := two_dvd_mul_succ (x.eval v + y.eval v)
  rw [hk, Nat.mul_div_right k (by decide : 0 < 2)]
  constructor <;> intro h <;> omega

theorem paBetaEq_holds_iff (v : ℕ → ℕ) (c d i r : PATerm) :
    (paBetaEq c d i r).Holds v ↔
      c.eval v % (1 + (i.eval v + 1) * d.eval v) = r.eval v := by
  let m := PATerm.succ (.mul (.succ i) d)
  let q := max (max c.freshVar m.freshVar) r.freshVar
  have hc : c.freshVar ≤ q := le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hm : m.freshVar ≤ q := le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hr : r.freshVar ≤ q := Nat.le_max_right _ _
  have hmev : m.eval v = 1 + (i.eval v + 1) * d.eval v := by
    simp only [m, PATerm.eval]
    omega
  change (PAFormula.ex q (.and (.eq c (.add (.mul (.var q) m) r)) (paLt r m))).Holds v ↔ _
  simp only [PAFormula.Holds, paLt_holds_iff, PATerm.eval]
  set mod := 1 + (i.eval v + 1) * d.eval v
  have hpos : 0 < mod := by omega
  constructor
  · rintro ⟨w, hcw, hrlt⟩
    rw [eval_update_of_freshVar_le v w hc, eval_update_of_freshVar_le v w hm,
      eval_update_of_freshVar_le v w hr, Function.update_self, hmev] at hcw
    rw [eval_update_of_freshVar_le v w hr, eval_update_of_freshVar_le v w hm, hmev] at hrlt
    have hcw' : c.eval v = r.eval v + mod * w := by
      rw [hcw, Nat.mul_comm w mod, Nat.add_comm]
    rw [hcw', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
  · intro hrem
    refine ⟨c.eval v / mod, ?_, ?_⟩
    · rw [eval_update_of_freshVar_le v _ hc, eval_update_of_freshVar_le v _ hm,
        eval_update_of_freshVar_le v _ hr, Function.update_self, hmev, ← hrem,
        Nat.mul_comm _ mod]
      exact (Nat.div_add_mod (c.eval v) mod).symm
    · rw [eval_update_of_freshVar_le v _ hr, eval_update_of_freshVar_le v _ hm, hmev, ← hrem]
      exact Nat.mod_lt _ hpos

theorem paDisjList_holds_iff (v : ℕ → ℕ) (L : List PAFormula) :
    (paDisjList L).Holds v ↔ ∃ φ ∈ L, φ.Holds v := by
  match L with
  | [] =>
    simp [paDisjList, PAFormula.Holds]
  | [φ] =>
    simp [paDisjList]
  | φ :: ψ :: rest =>
    simp only [paDisjList, PAFormula.Holds, paDisjList_holds_iff v (ψ :: rest), List.mem_cons,
      exists_eq_or_imp]

/-! ## Section 2: Cantor Pairing Injectivity and Symbolic `PAZFTerm` Evaluation -/

/-- Constructive injectivity of `cantorPair`. -/
theorem cantorPair_injective {x₁ y₁ x₂ y₂ : ℕ}
    (h : cantorPair x₁ y₁ = cantorPair x₂ y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  obtain ⟨k₁, hk₁⟩ := two_dvd_mul_succ (x₁ + y₁)
  obtain ⟨k₂, hk₂⟩ := two_dvd_mul_succ (x₂ + y₂)
  have h2 : 2 * x₁ + (x₁ + y₁) * (x₁ + y₁ + 1) = 2 * x₂ + (x₂ + y₂) * (x₂ + y₂ + 1) := by
    unfold cantorPair at h
    rw [hk₁, hk₂, Nat.mul_div_right _ (by decide : 0 < 2),
      Nat.mul_div_right _ (by decide : 0 < 2)] at h
    rw [hk₁, hk₂]
    omega
  have hnotlt : ∀ {a₁ b₁ a₂ b₂ : ℕ},
      2 * a₁ + (a₁ + b₁) * (a₁ + b₁ + 1) = 2 * a₂ + (a₂ + b₂) * (a₂ + b₂ + 1) →
      ¬ (a₁ + b₁ < a₂ + b₂) := by
    intro a₁ b₁ a₂ b₂ heq hlt
    have hle : (a₁ + b₁ + 1) * (a₁ + b₁ + 2) ≤ (a₂ + b₂) * (a₂ + b₂ + 1) :=
      Nat.mul_le_mul hlt (Nat.succ_le_succ hlt)
    have hexp : (a₁ + b₁ + 1) * (a₁ + b₁ + 2) =
        (a₁ + b₁) * (a₁ + b₁ + 1) + 2 * (a₁ + b₁) + 2 := by
      calc (a₁ + b₁ + 1) * (a₁ + b₁ + 2)
        _ = (a₁ + b₁) * (a₁ + b₁ + 2) + (a₁ + b₁ + 2) := Nat.succ_mul _ _
        _ = (a₁ + b₁) * (a₁ + b₁ + 1) + (a₁ + b₁) + (a₁ + b₁ + 2) := by
            rw [Nat.mul_succ]
        _ = (a₁ + b₁) * (a₁ + b₁ + 1) + 2 * (a₁ + b₁) + 2 := by omega
    omega
  have hs1 : ¬ (x₁ + y₁ < x₂ + y₂) := hnotlt h2
  have hs2 : ¬ (x₂ + y₂ < x₁ + y₁) := hnotlt h2.symm
  have hs : x₁ + y₁ = x₂ + y₂ := by omega
  rw [hs] at h2
  exact ⟨by omega, by omega⟩

theorem PAZFTerm.eval_congr {v₁ v₂ : ℕ → ℕ} {e : PAZFTerm}
    (h : ∀ x < e.freshVar, v₁ x = v₂ x) : e.eval v₁ = e.eval v₂ := by
  induction e with
  | var x => exact h x (Nat.lt_succ_self x)
  | const _ => rfl
  | pair a b iha ihb =>
    refine congrArg₂ cantorPair (iha fun x hx ↦ h x ?_) (ihb fun x hx ↦ h x ?_)
    · exact lt_of_lt_of_le hx (Nat.le_max_left _ _)
    · exact lt_of_lt_of_le hx (Nat.le_max_right _ _)

theorem PAZFTerm.eval_update_fresh (v : ℕ → ℕ) {e : PAZFTerm} {x : ℕ} (a : ℕ)
    (h : e.freshVar ≤ x) : e.eval (Function.update v x a) = e.eval v :=
  PAZFTerm.eval_congr fun y hy ↦ Function.update_of_ne (by omega) a v

theorem PAZFTerm.eqFormula_holds_iff (e : PAZFTerm) (out : PATerm) (base : ℕ) (v : ℕ → ℕ)
    (he : e.freshVar ≤ base) (hout : out.freshVar ≤ base) :
    (e.eqFormula out base).Holds v ↔ out.eval v = e.eval v := by
  induction e generalizing out base v with
  | var x =>
    simp [PAZFTerm.eqFormula, PAFormula.Holds, PATerm.eval, PAZFTerm.eval]
  | const n =>
    simp [PAZFTerm.eqFormula, PAFormula.Holds, PAZFTerm.eval]
  | pair a b iha ihb =>
    simp only [PAZFTerm.freshVar, Nat.max_le] at he
    rcases he with ⟨ha, hb⟩
    simp only [PAZFTerm.eqFormula, PAFormula.Holds]
    constructor
    · rintro ⟨va, vb, hpair, haeq, hbeq⟩
      set v' := Function.update (Function.update v base va) (base + 1) vb
      have hv_base : v' base = va := by simp [v']
      have hv_base1 : v' (base + 1) = vb := by simp [v']
      have hout_eq : out.eval v' = out.eval v := by
        dsimp only [v']
        rw [eval_update_of_freshVar_le _ _ (by omega), eval_update_of_freshVar_le _ _ hout]
      have hpair' : out.eval v = cantorPair va vb := by
        have hp := (paCantorPairEq_holds_iff v' (.var base) (.var (base + 1)) out).mp hpair
        simpa [PATerm.eval, hv_base, hv_base1, hout_eq] using hp
      have ha' : va = a.eval v := by
        have h1 := (iha (.var base) (base + 2) v' (by omega)
          (by simp [PATerm.freshVar])).mp haeq
        dsimp only [v'] at h1
        rw [PATerm.eval, PAZFTerm.eval_update_fresh _ _ (by omega),
          PAZFTerm.eval_update_fresh _ _ ha] at h1
        simpa [Function.update_of_ne (by omega : base ≠ base + 1)] using h1
      have hb' : vb = b.eval v := by
        have h2 := (ihb (.var (base + 1)) (base + 2 + a.numVars) v' (by omega)
          (by simp [PATerm.freshVar]; omega)).mp hbeq
        dsimp only [v'] at h2
        rw [PATerm.eval, PAZFTerm.eval_update_fresh _ _ (by omega),
          PAZFTerm.eval_update_fresh _ _ hb] at h2
        simpa using h2
      rw [hpair', ha', hb', PAZFTerm.eval]
    · intro heq
      refine ⟨a.eval v, b.eval v, ?_⟩
      set v' := Function.update (Function.update v base (a.eval v)) (base + 1) (b.eval v)
      have hv_base : v' base = a.eval v := by simp [v']
      have hv_base1 : v' (base + 1) = b.eval v := by simp [v']
      have hout_eq : out.eval v' = out.eval v := by
        dsimp only [v']
        rw [eval_update_of_freshVar_le _ _ (by omega), eval_update_of_freshVar_le _ _ hout]
      refine ⟨?_, ?_, ?_⟩
      · rw [paCantorPairEq_holds_iff]
        simp only [PATerm.eval, hv_base, hv_base1, hout_eq]
        exact heq
      · rw [iha (.var base) (base + 2) v' (by omega) (by simp [PATerm.freshVar])]
        rw [PATerm.eval, hv_base]
        dsimp only [v']
        rw [PAZFTerm.eval_update_fresh _ _ (by omega),
          PAZFTerm.eval_update_fresh _ _ ha]
      · rw [ihb (.var (base + 1)) (base + 2 + a.numVars) v' (by omega)
          (by simp [PATerm.freshVar]; omega)]
        rw [PATerm.eval, hv_base1]
        dsimp only [v']
        rw [PAZFTerm.eval_update_fresh _ _ (by omega),
          PAZFTerm.eval_update_fresh _ _ hb]

/-! ## Section 3: Constructive Gödel $\beta$-Lemma in `ℕ` -/

private def maxElem : List ℕ → ℕ
  | [] => 0
  | x :: xs => max x (maxElem xs)

private theorem getElem_le_maxElem (L : List ℕ) :
    ∀ (i : ℕ) (hi : i < L.length), L[i] ≤ maxElem L := by
  induction L with
  | nil => intro _ hi; cases hi
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero => exact Nat.le_max_left x (maxElem xs)
    | succ j =>
      exact le_trans (ih j (Nat.lt_of_succ_lt_succ hi)) (Nat.le_max_right x (maxElem xs))

private theorem beta_moduli_coprime {d i j : ℕ} (hij : i < j) (hd : j - i ∣ d) :
    Nat.Coprime (1 + (i + 1) * d) (1 + (j + 1) * d) := by
  set si := 1 + (i + 1) * d
  set sj := 1 + (j + 1) * d
  set g := Nat.gcd si sj
  have hid : (i + 1) * sj + (j - i) = (j + 1) * si := by
    have hmul : (i + 1) * ((j + 1) * d) = (j + 1) * ((i + 1) * d) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (i + 1) (j + 1), Nat.mul_assoc]
    calc (i + 1) * (1 + (j + 1) * d) + (j - i)
      _ = (i + 1) + (i + 1) * ((j + 1) * d) + (j - i) := by rw [Nat.mul_add, Nat.mul_one]
      _ = (j + 1) + (j + 1) * ((i + 1) * d) := by rw [hmul]; omega
      _ = (j + 1) * (1 + (i + 1) * d) := by rw [Nat.mul_add, Nat.mul_one]
  have hg1 : g ∣ (j + 1) * si := dvd_mul_of_dvd_right (Nat.gcd_dvd_left si sj) (j + 1)
  have hg2 : g ∣ (i + 1) * sj := dvd_mul_of_dvd_right (Nat.gcd_dvd_right si sj) (i + 1)
  have hg_sub : g ∣ j - i := (Nat.dvd_add_right hg2).mp (hid.symm ▸ hg1)
  have hg_d : g ∣ d := dvd_trans hg_sub hd
  have hg_mul : g ∣ (i + 1) * d := dvd_mul_of_dvd_right hg_d (i + 1)
  have hg_si : g ∣ (i + 1) * d + 1 := by
    simpa [si, Nat.add_comm] using Nat.gcd_dvd_left si sj
  have hg_one : g ∣ 1 := (Nat.dvd_add_right hg_mul).mp hg_si
  exact Nat.dvd_one.mp hg_one

private theorem crt2_constructive {m₁ m₂ : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hco : Nat.Coprime m₁ m₂) (r₁ r₂ : ℕ) :
    ∃ x : ℕ, x % m₁ = r₁ % m₁ ∧ x % m₂ = r₂ % m₂ := by
  let A : ℤ := Nat.gcdA m₁ m₂
  let B : ℤ := Nat.gcdB m₁ m₂
  have hbz : (m₁ : ℤ) * A + (m₂ : ℤ) * B = 1 := by
    have hg := Nat.gcd_eq_gcd_ab m₁ m₂
    rw [hco.gcd_eq_one] at hg
    simpa [A, B] using hg.symm
  let M : ℕ := m₁ * m₂
  have hM_pos : (0 : ℤ) < (M : ℤ) := Int.natCast_pos.mpr (Nat.mul_pos hm₁ hm₂)
  let z : ℤ := (r₁ : ℤ) + (m₁ : ℤ) * (((r₂ : ℤ) - (r₁ : ℤ)) * A)
  have hz2 : z = (r₂ : ℤ) + (m₂ : ℤ) * (((r₁ : ℤ) - (r₂ : ℤ)) * B) := by
    have h1 : (m₁ : ℤ) * A = 1 - (m₂ : ℤ) * B := by omega
    calc z
      _ = (r₁ : ℤ) + ((r₂ : ℤ) - (r₁ : ℤ)) * ((m₁ : ℤ) * A) := by
          simp only [z]
          rw [← Int.mul_assoc, Int.mul_comm (m₁ : ℤ) ((r₂ : ℤ) - (r₁ : ℤ)), Int.mul_assoc]
      _ = (r₁ : ℤ) + ((r₂ : ℤ) - (r₁ : ℤ)) * (1 - (m₂ : ℤ) * B) := by rw [h1]
      _ = (r₂ : ℤ) + (m₂ : ℤ) * (((r₁ : ℤ) - (r₂ : ℤ)) * B) := by
          rw [Int.mul_sub, Int.mul_one, ← Int.mul_assoc,
            Int.mul_comm ((r₂ : ℤ) - (r₁ : ℤ)) (m₂ : ℤ), Int.mul_assoc]
          have hsub : -((m₂ : ℤ) * (((r₂ : ℤ) - (r₁ : ℤ)) * B)) =
              (m₂ : ℤ) * (((r₁ : ℤ) - (r₂ : ℤ)) * B) := by
            rw [← Int.mul_neg, ← Int.neg_mul, Int.neg_sub]
          omega
  let z' : ℤ := z % (M : ℤ)
  have hz'_nonneg : 0 ≤ z' := Int.emod_nonneg z (ne_of_gt hM_pos)
  let x : ℕ := z'.toNat
  have hx_cast : (x : ℤ) = z' := Int.toNat_of_nonneg hz'_nonneg
  refine ⟨x, ?_, ?_⟩
  · apply Int.natCast_inj.mp
    rw [Int.natCast_emod, Int.natCast_emod, hx_cast]
    have hdvd1 : (m₁ : ℤ) ∣ (M : ℤ) := ⟨(m₂ : ℤ), by simp [M]⟩
    rw [Int.emod_emod_of_dvd z hdvd1]
    exact Int.add_mul_emod_self_left (r₁ : ℤ) (m₁ : ℤ) (((r₂ : ℤ) - (r₁ : ℤ)) * A)
  · apply Int.natCast_inj.mp
    rw [Int.natCast_emod, Int.natCast_emod, hx_cast]
    have hdvd2 : (m₂ : ℤ) ∣ (M : ℤ) := ⟨(m₁ : ℤ), by simp [M, Int.mul_comm]⟩
    rw [Int.emod_emod_of_dvd z hdvd2, hz2]
    exact Int.add_mul_emod_self_left (r₂ : ℤ) (m₂ : ℤ) (((r₁ : ℤ) - (r₂ : ℤ)) * B)

/-- Constructive Gödel $\beta$-sequence lemma: every finite sequence `L : List ℕ` is represented
by a pair `(c, d)` via $L_i = c \bmod (1 + (i + 1) d)$. -/
theorem exists_beta_nat (L : List ℕ) :
    ∃ c d : ℕ, ∀ (i : ℕ) (hi : i < L.length), c % (1 + (i + 1) * d) = L[i] := by
  let B := max (maxElem L) L.length + 1
  let d := B.factorial
  let s : ℕ → ℕ := fun i ↦ 1 + (i + 1) * d
  have hs_pos : ∀ i, 0 < s i := fun i ↦ by dsimp only [s]; omega
  have hco : ∀ i < L.length, ∀ j < L.length, i ≠ j → Nat.Coprime (s i) (s j) := by
    intro i hi j hj hij
    rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
    · refine beta_moduli_coprime hlt (Nat.dvd_factorial (by omega) ?_)
      have hB : L.length < B := by simp [B]
      omega
    · exact absurd rfl hij
    · refine Nat.coprime_comm.mp (beta_moduli_coprime hgt (Nat.dvd_factorial (by omega) ?_))
      have hB : L.length < B := by simp [B]
      omega
  have hstep : ∀ k (hkle : k ≤ L.length), ∃ c P : ℕ, 0 < P ∧
      (∀ i < k, s i ∣ P) ∧
      (∀ m, (∀ i < k, Nat.Coprime (s i) m) → Nat.Coprime P m) ∧
      (∀ (i : ℕ) (hi : i < k), c % s i = L[i]'(lt_of_lt_of_le hi hkle)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨0, 1, Nat.one_pos, fun _ hi ↦ absurd hi (Nat.not_lt_zero _),
        fun _ _ ↦ Nat.coprime_one_left _, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hkle
      have hklt : k < L.length := hkle
      obtain ⟨c₀, P₀, hP₀_pos, hdvd₀, hcop₀, hmod₀⟩ := ih (Nat.le_of_lt hklt)
      have hcop_sk : Nat.Coprime P₀ (s k) :=
        hcop₀ (s k) fun i hi ↦ hco i (lt_trans hi hklt) k hklt (Nat.ne_of_lt hi)
      obtain ⟨c, hc1, hc2⟩ := crt2_constructive hP₀_pos (hs_pos k) hcop_sk c₀ (L[k]'hklt)
      refine ⟨c, P₀ * s k, Nat.mul_pos hP₀_pos (hs_pos k), ?_, ?_, ?_⟩
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | rfl
        · exact dvd_mul_of_dvd_left (hdvd₀ i hilt) (s k)
        · exact dvd_mul_left (s i) P₀
      · intro m hm
        exact Nat.Coprime.mul_left
          (hcop₀ m fun i hi ↦ hm i (Nat.lt_succ_of_lt hi))
          (hm k (Nat.lt_succ_self k))
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | rfl
        · have hsi_dvd : s i ∣ P₀ := hdvd₀ i hilt
          rw [← Nat.mod_mod_of_dvd c hsi_dvd, hc1, Nat.mod_mod_of_dvd c₀ hsi_dvd]
          exact hmod₀ i hilt
        · have hlt_s : L[i]'hklt < s i := by
            have hle1 : L[i]'hklt ≤ maxElem L := getElem_le_maxElem L i hklt
            have hltB : L[i]'hklt < B := by simp [B]; omega
            have hB_le_d : B ≤ d := Nat.self_le_factorial B
            have hd_le : d ≤ (i + 1) * d := Nat.le_mul_of_pos_left d (Nat.succ_pos i)
            dsimp only [s]
            omega
          rw [hc2, Nat.mod_eq_of_lt hlt_s]
  obtain ⟨c, _, _, _, _, hc⟩ := hstep L.length (Nat.le_refl _)
  exact ⟨c, d, hc⟩

/-! ## Section 4: Binary Half-Tape Bijection and Adequacy of `paHalts` -/

/-- Little-endian binary encoding of a `List (Fin 2)` that ignores trailing `0` blanks. -/
def encodeListBin : List (Fin 2) → ℕ
  | [] => 0
  | a :: xs => 2 * encodeListBin xs + a.val

private theorem encodeListBin_replicate_default (k : ℕ) :
    encodeListBin (List.replicate k (default : Fin 2)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, encodeListBin, ih]
    rfl

private theorem encodeListBin_append_replicate (xs : List (Fin 2)) (k : ℕ) :
    encodeListBin (xs ++ List.replicate k (default : Fin 2)) = encodeListBin xs := by
  induction xs with
  | nil => simp only [List.nil_append, encodeListBin_replicate_default, encodeListBin]
  | cons a xs ih => simp only [List.cons_append, encodeListBin, ih]

/-- Constructive binary encoding of a `ListBlank (Fin 2)` half-tape as a natural number. -/
def encodeHalf (l : ListBlank (Fin 2)) : ℕ :=
  l.liftOn encodeListBin fun xs _ ⟨k, hk⟩ ↦ by
    subst hk
    exact (encodeListBin_append_replicate xs k).symm

/-- Inverse binary decoding from `ℕ` to `List (Fin 2)`. -/
def decodeListBin : ℕ → List (Fin 2)
  | 0 => []
  | n + 1 => ⟨(n + 1) % 2, Nat.mod_lt _ (by decide)⟩ :: decodeListBin ((n + 1) / 2)

/-- Constructive binary decoding from `ℕ` to `ListBlank (Fin 2)`. -/
def decodeHalf (n : ℕ) : ListBlank (Fin 2) :=
  ListBlank.mk (decodeListBin n)

@[simp]
theorem encodeHalf_mk (xs : List (Fin 2)) : encodeHalf (ListBlank.mk xs) = encodeListBin xs :=
  rfl

@[simp]
theorem encodeHalf_default : encodeHalf default = 0 := rfl

@[simp]
theorem encodeHalf_cons (l : ListBlank (Fin 2)) (a : Fin 2) :
    encodeHalf (l.cons a) = 2 * encodeHalf l + a.val :=
  l.induction_on fun _ ↦ rfl

theorem encodeHalf_eq_tail_head (l : ListBlank (Fin 2)) :
    encodeHalf l = 2 * encodeHalf l.tail + l.head.val := by
  conv_lhs => rw [← ListBlank.cons_head_tail l]
  exact encodeHalf_cons l.tail l.head

private theorem encodeListBin_decodeListBin (n : ℕ) : encodeListBin (decodeListBin n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [decodeListBin, encodeListBin]
    | succ m =>
      simp only [decodeListBin, encodeListBin]
      have hrec := ih ((m + 1) / 2) (Nat.div_lt_self (Nat.succ_pos m) (by decide))
      rw [hrec]
      omega

@[simp]
theorem encodeHalf_decodeHalf (n : ℕ) : encodeHalf (decodeHalf n) = n :=
  encodeListBin_decodeListBin n

private theorem mk_decodeListBin_encodeListBin (xs : List (Fin 2)) :
    ListBlank.mk (decodeListBin (encodeListBin xs)) = ListBlank.mk xs := by
  induction xs with
  | nil => simp [encodeListBin, decodeListBin]
  | cons a xs ih =>
    simp only [encodeListBin]
    rcases Decidable.eq_or_ne (2 * encodeListBin xs + a.val) 0 with h0 | hne
    · have hxs0 : encodeListBin xs = 0 := by omega
      have ha0 : a = default := by
        ext
        change a.val = 0
        omega
      have hd0 : decodeListBin 0 = [] := by simp [decodeListBin]
      rw [h0, ha0, hd0]
      rw [hxs0, hd0] at ih
      have hcons : ListBlank.mk ((default : Fin 2) :: xs) =
          (ListBlank.mk xs).cons default := rfl
      rw [hcons, ← ih]
      exact Quot.sound (Or.inl ⟨1, rfl⟩)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
      rw [hk, decodeListBin]
      have hdiv : (k + 1) / 2 = encodeListBin xs := by
        have := a.isLt
        omega
      have hmod : (⟨(k + 1) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = a := by
        ext
        have := a.isLt
        change (k + 1) % 2 = a.val
        omega
      rw [hdiv, hmod, ← ListBlank.cons_mk, ih, ListBlank.cons_mk]

@[simp]
theorem decodeHalf_encodeHalf (l : ListBlank (Fin 2)) : decodeHalf (encodeHalf l) = l :=
  l.induction_on mk_decodeListBin_encodeListBin

theorem encodeHalf_injective {l₁ l₂ : ListBlank (Fin 2)} (h : encodeHalf l₁ = encodeHalf l₂) :
    l₁ = l₂ := by
  rw [← decodeHalf_encodeHalf l₁, ← decodeHalf_encodeHalf l₂, h]

/-- Nested Cantor configuration code `(q, (h, (L, R)))` of a binary Turing machine configuration. -/
def encodeCfg {states : ℕ} (c : Cfg states 2) : ℕ :=
  cantorPair c.state.val
    (cantorPair c.tape.head.val
      (cantorPair (encodeHalf c.tape.left) (encodeHalf c.tape.right)))

theorem encodeCfg_init {states : ℕ} [NeZero states] :
    encodeCfg (init : Cfg states 2) = 0 := by
  have hq : (0 : Fin states).val = 0 := Fin.val_zero states
  have hh : (Tape.mk₁ ([] : List (Fin 2))).head.val = 0 := rfl
  have hl : encodeHalf (Tape.mk₁ ([] : List (Fin 2))).left = 0 := rfl
  have hr : encodeHalf (Tape.mk₁ ([] : List (Fin 2))).right = 0 := rfl
  simp only [encodeCfg, init, hq, hh, hl, hr]
  rfl

theorem encodeCfg_injective {states : ℕ} {c₁ c₂ : Cfg states 2}
    (h : encodeCfg c₁ = encodeCfg c₂) : c₁ = c₂ := by
  obtain ⟨hq, h1⟩ := cantorPair_injective h
  obtain ⟨hh, h2⟩ := cantorPair_injective h1
  obtain ⟨hl, hr⟩ := cantorPair_injective h2
  rcases c₁ with ⟨q₁, h₁, L₁, R₁⟩
  rcases c₂ with ⟨q₂, h₂, L₂, R₂⟩
  congr 1
  · exact Fin.ext hq
  · congr 1
    · exact Fin.ext hh
    · exact encodeHalf_injective hl
    · exact encodeHalf_injective hr

private theorem pzPackCfg_eval (v : ℕ → ℕ) (q h : ℕ) (L R : PAZFTerm) :
    (pzPackCfg q h L R).eval v = cantorPair q (cantorPair h (cantorPair (L.eval v) (R.eval v))) :=
  rfl

private theorem pzPackCfg_freshVar_le (q h : ℕ) (x y : ℕ) (hx : x < 10) (hy : y < 10) :
    (pzPackCfg q h (.var x) (.var y)).freshVar ≤ 10 := by
  simp only [pzPackCfg, PAZFTerm.freshVar]
  omega

theorem paStep_holds_iff {states : ℕ} (M : Machine states 2) (v : ℕ → ℕ) :
    (paStep M).Holds v ↔
      ∃ c c' : Cfg states 2, v 4 = encodeCfg c ∧ v 5 = encodeCfg c' ∧ step M c = some c' := by
  unfold paStep
  rw [paDisjList_holds_iff]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨φ, ⟨q, _, h, _, hmem⟩, hholds⟩
    cases htr : M.transition q h with
    | none =>
      rw [htr] at hmem
      cases hmem
    | some val =>
      rcases val with ⟨w, d, q'⟩
      cases d with
      | left =>
        rw [htr, List.mem_map] at hmem
        rcases hmem with ⟨h', hh'mem, rfl⟩
        have hh'lt : h' < 2 := by simp at hh'mem; omega
        let hFin : Fin 2 := ⟨h', hh'lt⟩
        simp only [PAFormula.Holds] at hholds
        rcases hholds with ⟨n6, n7, n8, n9, hc_eq, hc'_eq, hn6, hn9⟩
        set v' := Function.update (Function.update
          (Function.update (Function.update v 6 n6) 7 n7) 8 n8) 9 n9
        have hv4 : v' 4 = v 4 := by simp [v']
        have hv5 : v' 5 = v 5 := by simp [v']
        have hv6 : v' 6 = n6 := by simp [v']
        have hv7 : v' 7 = n7 := by simp [v']
        have hv8 : v' 8 = n8 := by simp [v']
        have hv9 : v' 9 = n9 := by simp [v']
        have e1 := (PAZFTerm.eqFormula_holds_iff _ (.var 4) 10 v'
          (pzPackCfg_freshVar_le q.val h.val 6 7 (by decide) (by decide))
          (by decide)).mp hc_eq
        have e2 := (PAZFTerm.eqFormula_holds_iff _ (.var 5) 10 v'
          (pzPackCfg_freshVar_le q'.val h' 8 9 (by decide) (by decide))
          (by decide)).mp hc'_eq
        simp only [PATerm.eval, pzPackCfg_eval, PAZFTerm.eval, eval_ofNat,
          hv4, hv5, hv6, hv7, hv8, hv9] at e1 e2 hn6 hn9
        let L' := decodeHalf n8
        let R := decodeHalf n7
        let L := L'.cons hFin
        have hL_enc : encodeHalf L = n6 := by
          simp [L, L', hFin, hn6]
        have hR_enc : encodeHalf R = n7 := encodeHalf_decodeHalf n7
        let c : Cfg states 2 := ⟨q, ⟨h, L, R⟩⟩
        let c' : Cfg states 2 := ⟨q', ⟨hFin, L', R.cons w⟩⟩
        refine ⟨c, c', ?_, ?_, ?_⟩
        · simp [encodeCfg, c, hL_enc, hR_enc, e1]
        · have hRw : encodeHalf (R.cons w) = n9 := by simp [R, hn9]
          simp [encodeCfg, c', L', hFin, hRw, e2]
        · simp [step, c, c', htr, Tape.write, Tape.move, L]
      | right =>
        rw [htr, List.mem_map] at hmem
        rcases hmem with ⟨h', hh'mem, rfl⟩
        have hh'lt : h' < 2 := by simp at hh'mem; omega
        let hFin : Fin 2 := ⟨h', hh'lt⟩
        simp only [PAFormula.Holds] at hholds
        rcases hholds with ⟨n6, n7, n8, n9, hc_eq, hc'_eq, hn8, hn7⟩
        set v' := Function.update (Function.update
          (Function.update (Function.update v 6 n6) 7 n7) 8 n8) 9 n9
        have hv4 : v' 4 = v 4 := by simp [v']
        have hv5 : v' 5 = v 5 := by simp [v']
        have hv6 : v' 6 = n6 := by simp [v']
        have hv7 : v' 7 = n7 := by simp [v']
        have hv8 : v' 8 = n8 := by simp [v']
        have hv9 : v' 9 = n9 := by simp [v']
        have e1 := (PAZFTerm.eqFormula_holds_iff _ (.var 4) 10 v'
          (pzPackCfg_freshVar_le q.val h.val 6 7 (by decide) (by decide))
          (by decide)).mp hc_eq
        have e2 := (PAZFTerm.eqFormula_holds_iff _ (.var 5) 10 v'
          (pzPackCfg_freshVar_le q'.val h' 8 9 (by decide) (by decide))
          (by decide)).mp hc'_eq
        simp only [PATerm.eval, pzPackCfg_eval, PAZFTerm.eval, eval_ofNat,
          hv4, hv5, hv6, hv7, hv8, hv9] at e1 e2 hn8 hn7
        let L := decodeHalf n6
        let R' := decodeHalf n9
        let R := R'.cons hFin
        have hL_enc : encodeHalf L = n6 := encodeHalf_decodeHalf n6
        have hR_enc : encodeHalf R = n7 := by
          simp [R, R', hFin, hn7]
        let c : Cfg states 2 := ⟨q, ⟨h, L, R⟩⟩
        let c' : Cfg states 2 := ⟨q', ⟨hFin, L.cons w, R'⟩⟩
        refine ⟨c, c', ?_, ?_, ?_⟩
        · simp [encodeCfg, c, hL_enc, hR_enc, e1]
        · have hLw : encodeHalf (L.cons w) = n8 := by simp [L, hn8]
          simp [encodeCfg, c', R', hFin, hLw, e2]
        · simp [step, c, c', htr, Tape.write, Tape.move, R]
  · rintro ⟨⟨q, ⟨h, L, R⟩⟩, c', hv4, hv5, hstep⟩
    simp only [step] at hstep
    cases htr : M.transition q h with
    | none => simp [htr] at hstep
    | some val =>
      rcases val with ⟨w, d, q'⟩
      rw [htr, Option.map_some, Option.some.injEq] at hstep
      subst hstep
      cases d with
      | left =>
        let h' := L.head.val
        have hh'mem : h' ∈ ([0, 1] : List ℕ) := by
          have := L.head.isLt
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          omega
        let φ := PAFormula.ex 6 (.ex 7 (.ex 8 (.ex 9
          (.and ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10)
            (.and ((pzPackCfg q'.val h' (.var 8) (.var 9)).eqFormula (.var 5) 10)
              (.and (.eq (.var 6) (.add (.mul (.ofNat 2) (.var 8)) (.ofNat h')))
                (.eq (.var 9) (.add (.mul (.ofNat 2) (.var 7)) (.ofNat w.val)))))))))
        refine ⟨φ, ⟨q, List.mem_finRange q, h, List.mem_finRange h, ?_⟩, ?_⟩
        · rw [htr, List.mem_map]
          exact ⟨h', hh'mem, rfl⟩
        · simp only [φ, PAFormula.Holds]
          refine ⟨encodeHalf L, encodeHalf R, encodeHalf L.tail, encodeHalf (R.cons w), ?_⟩
          set v' := Function.update (Function.update (Function.update
            (Function.update v 6 (encodeHalf L)) 7 (encodeHalf R))
            8 (encodeHalf L.tail)) 9 (encodeHalf (R.cons w))
          have hv4' : v' 4 = v 4 := by simp [v']
          have hv5' : v' 5 = v 5 := by simp [v']
          have hv6' : v' 6 = encodeHalf L := by simp [v']
          have hv7' : v' 7 = encodeHalf R := by simp [v']
          have hv8' : v' 8 = encodeHalf L.tail := by simp [v']
          have hv9' : v' 9 = encodeHalf (R.cons w) := by simp [v']
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [PAZFTerm.eqFormula_holds_iff _ (.var 4) 10 v'
              (pzPackCfg_freshVar_le q.val h.val 6 7 (by decide) (by decide)) (by decide)]
            simp [PATerm.eval, pzPackCfg_eval, PAZFTerm.eval, hv4', hv6', hv7', hv4, encodeCfg]
          · rw [PAZFTerm.eqFormula_holds_iff _ (.var 5) 10 v'
              (pzPackCfg_freshVar_le q'.val h' 8 9 (by decide) (by decide)) (by decide)]
            simp [PATerm.eval, pzPackCfg_eval, PAZFTerm.eval, hv5', hv8', hv9', hv5, encodeCfg,
              Tape.write, Tape.move, h']
          · simp only [PATerm.eval, eval_ofNat, hv6', hv8', h']
            exact encodeHalf_eq_tail_head L
          · simp only [PATerm.eval, eval_ofNat, hv7', hv9']
            exact encodeHalf_cons R w
      | right =>
        let h' := R.head.val
        have hh'mem : h' ∈ ([0, 1] : List ℕ) := by
          have := R.head.isLt
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          omega
        let φ := PAFormula.ex 6 (.ex 7 (.ex 8 (.ex 9
          (.and ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10)
            (.and ((pzPackCfg q'.val h' (.var 8) (.var 9)).eqFormula (.var 5) 10)
              (.and (.eq (.var 8) (.add (.mul (.ofNat 2) (.var 6)) (.ofNat w.val)))
                (.eq (.var 7) (.add (.mul (.ofNat 2) (.var 9)) (.ofNat h')))))))))
        refine ⟨φ, ⟨q, List.mem_finRange q, h, List.mem_finRange h, ?_⟩, ?_⟩
        · rw [htr, List.mem_map]
          exact ⟨h', hh'mem, rfl⟩
        · simp only [φ, PAFormula.Holds]
          refine ⟨encodeHalf L, encodeHalf R, encodeHalf (L.cons w), encodeHalf R.tail, ?_⟩
          set v' := Function.update (Function.update (Function.update
            (Function.update v 6 (encodeHalf L)) 7 (encodeHalf R))
            8 (encodeHalf (L.cons w))) 9 (encodeHalf R.tail)
          have hv4' : v' 4 = v 4 := by simp [v']
          have hv5' : v' 5 = v 5 := by simp [v']
          have hv6' : v' 6 = encodeHalf L := by simp [v']
          have hv7' : v' 7 = encodeHalf R := by simp [v']
          have hv8' : v' 8 = encodeHalf (L.cons w) := by simp [v']
          have hv9' : v' 9 = encodeHalf R.tail := by simp [v']
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [PAZFTerm.eqFormula_holds_iff _ (.var 4) 10 v'
              (pzPackCfg_freshVar_le q.val h.val 6 7 (by decide) (by decide)) (by decide)]
            simp [PATerm.eval, pzPackCfg_eval, PAZFTerm.eval, hv4', hv6', hv7', hv4, encodeCfg]
          · rw [PAZFTerm.eqFormula_holds_iff _ (.var 5) 10 v'
              (pzPackCfg_freshVar_le q'.val h' 8 9 (by decide) (by decide)) (by decide)]
            simp [PATerm.eval, pzPackCfg_eval, PAZFTerm.eval, hv5', hv8', hv9', hv5, encodeCfg,
              Tape.write, Tape.move, h']
          · simp only [PATerm.eval, eval_ofNat, hv6', hv8']
            exact encodeHalf_cons L w
          · simp only [PATerm.eval, eval_ofNat, hv7', hv9', h']
            exact encodeHalf_eq_tail_head R

theorem paHalted_holds_iff {states : ℕ} (M : Machine states 2) (v : ℕ → ℕ) :
    (paHalted M).Holds v ↔ ∃ c : Cfg states 2, v 4 = encodeCfg c ∧ step M c = none := by
  unfold paHalted
  rw [paDisjList_holds_iff]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨φ, ⟨q, _, h, _, hmem⟩, hholds⟩
    cases htr : M.transition q h with
    | some _ => rw [htr] at hmem; cases hmem
    | none =>
      rw [htr, List.mem_singleton] at hmem
      subst hmem
      simp only [PAFormula.Holds] at hholds
      rcases hholds with ⟨n6, n7, heq⟩
      set v' := Function.update (Function.update v 6 n6) 7 n7
      have e1 := (PAZFTerm.eqFormula_holds_iff _ (.var 4) 10 v'
        (pzPackCfg_freshVar_le q.val h.val 6 7 (by decide) (by decide)) (by decide)).mp heq
      have hv4 : v' 4 = v 4 := by simp [v']
      have hv6 : v' 6 = n6 := by simp [v']
      have hv7 : v' 7 = n7 := by simp [v']
      simp only [PATerm.eval, pzPackCfg_eval, PAZFTerm.eval, hv4, hv6, hv7] at e1
      refine ⟨⟨q, ⟨h, decodeHalf n6, decodeHalf n7⟩⟩, ?_, ?_⟩
      · simp [encodeCfg, e1]
      · simp [step, htr]
  · rintro ⟨⟨q, ⟨h, L, R⟩⟩, hv4, hstep⟩
    simp only [step, Option.map_eq_none_iff] at hstep
    let φ := PAFormula.ex 6
      (.ex 7 ((pzPackCfg q.val h.val (.var 6) (.var 7)).eqFormula (.var 4) 10))
    refine ⟨φ, ⟨q, List.mem_finRange q, h, List.mem_finRange h, ?_⟩, ?_⟩
    · simp [hstep, φ]
    · simp only [φ, PAFormula.Holds]
      refine ⟨encodeHalf L, encodeHalf R, ?_⟩
      set v' := Function.update (Function.update v 6 (encodeHalf L)) 7 (encodeHalf R)
      rw [PAZFTerm.eqFormula_holds_iff _ (.var 4) 10 v'
        (pzPackCfg_freshVar_le q.val h.val 6 7 (by decide) (by decide)) (by decide)]
      have hv4' : v' 4 = v 4 := by simp [v']
      have hv6' : v' 6 = encodeHalf L := by simp [v']
      have hv7' : v' 7 = encodeHalf R := by simp [v']
      simp [PATerm.eval, pzPackCfg_eval, PAZFTerm.eval, hv4', hv6', hv7', hv4, encodeCfg]

private theorem reaches_to_trace {σ : Type*} {f : σ → Option σ} {a b : σ}
    (h : StateTransition.Reaches f a b) :
    ∃ (n : ℕ) (tr : ℕ → σ), tr 0 = a ∧ (∀ i < n, f (tr i) = some (tr (i + 1))) ∧ tr n = b := by
  induction h with
  | refl => exact ⟨0, fun _ ↦ a, rfl, fun _ hi ↦ absurd hi (Nat.not_lt_zero _), rfl⟩
  | @tail x y _ hxy ih =>
    rcases ih with ⟨n, tr, h0, hstep, hn⟩
    refine ⟨n + 1, fun i ↦ if i == n + 1 then y else tr i, ?_, ?_, ?_⟩
    · simp [h0]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · have hne1 : (i == n + 1) = false := beq_eq_false_iff_ne.mpr (by omega)
        have hne2 : (i + 1 == n + 1) = false := beq_eq_false_iff_ne.mpr (by omega)
        simp only [hne1, hne2, Bool.false_eq_true, ↓reduceIte]
        exact hstep i hlt
      · have hne1 : (i == i + 1) = false := beq_eq_false_iff_ne.mpr (by omega)
        simp only [hne1, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, hn]
        exact Option.mem_def.mp hxy
    · simp

/-- Standard-model adequacy of `paHalts`: `(paHalts M).Holds v` holds in `ℕ` if and only if `M`
halts from `init` (proved constructively without `Classical.choice`). -/
theorem paHalts_holds_iff_halts {states : ℕ} [NeZero states] (M : Machine states 2)
    (v : ℕ → ℕ) : (paHalts M).Holds v ↔ ConjectureMachines.Halts M := by
  unfold paHalts ConjectureMachines.Halts
  simp only [PAFormula.Holds]
  constructor
  · rintro ⟨n, c, d, h0, hsteps, hhalt⟩
    set v2 := Function.update (Function.update (Function.update v 0 n) 1 c) 2 d
    have hb0 : c % (1 + d) = 0 := by
      have := (paBetaEq_holds_iff v2 (.var 1) (.var 2) .zero .zero).mp h0
      simpa [v2, PATerm.eval] using this
    have hreach : ∀ i ≤ n, ∃ cfg : Cfg states 2,
        c % (1 + (i + 1) * d) = encodeCfg cfg ∧ StateTransition.Reaches (step M) init cfg := by
      intro i
      induction i with
      | zero =>
        intro _
        refine ⟨init, ?_, Relation.ReflTransGen.refl⟩
        simpa [encodeCfg_init] using hb0
      | succ i ih =>
        intro hle
        obtain ⟨cfg₀, hcfg₀, hr₀⟩ := ih (Nat.le_of_succ_le hle)
        have hilt : (paLt (.var 3) (.var 0)).Holds (Function.update v2 3 i) := by
          rw [paLt_holds_iff]
          simp [v2, PATerm.eval]
          omega
        obtain ⟨x4, x5, hb_i, hb_i1, hst⟩ := hsteps i hilt
        set v5 := Function.update (Function.update (Function.update v2 3 i) 4 x4) 5 x5
        have hx4 : c % (1 + (i + 1) * d) = x4 := by
          have := (paBetaEq_holds_iff v5 (.var 1) (.var 2) (.var 3) (.var 4)).mp hb_i
          simpa [v5, v2, PATerm.eval] using this
        have hx5 : c % (1 + (i + 1 + 1) * d) = x5 := by
          have := (paBetaEq_holds_iff v5 (.var 1) (.var 2) (.succ (.var 3)) (.var 5)).mp hb_i1
          simpa [v5, v2, PATerm.eval] using this
        obtain ⟨c₁, c₂, hc₁, hc₂, hstep⟩ := (paStep_holds_iff M v5).mp hst
        simp only [v5, Function.update_self,
          Function.update_of_ne (by decide : (4 : ℕ) ≠ 5)] at hc₁ hc₂
        have heq₀ : cfg₀ = c₁ := encodeCfg_injective (by rw [← hcfg₀, hx4, hc₁])
        subst heq₀
        exact ⟨c₂, by rw [hx5, hc₂], Relation.ReflTransGen.tail hr₀ hstep⟩
    obtain ⟨cfg_n, hcfg_n, hr_n⟩ := hreach n (Nat.le_refl n)
    rcases hhalt with ⟨x4, hb_n, hhalted⟩
    set v4 := Function.update v2 4 x4
    have hx4 : c % (1 + (n + 1) * d) = x4 := by
      have := (paBetaEq_holds_iff v4 (.var 1) (.var 2) (.var 0) (.var 4)).mp hb_n
      simpa [v4, v2, PATerm.eval] using this
    obtain ⟨cfg_f, hcfg_f, hnone⟩ := (paHalted_holds_iff M v4).mp hhalted
    simp only [v4, Function.update_self] at hcfg_f
    have heq_f : cfg_n = cfg_f := encodeCfg_injective (by rw [← hcfg_n, hx4, hcfg_f])
    subst heq_f
    have hmem : cfg_n ∈ StateTransition.eval (step M) init :=
      mem_eval'.mpr ⟨hr_n, hnone⟩
    exact hmem.fst
  · intro hdom
    have hmem : (StateTransition.eval (step M) init).get hdom ∈
        StateTransition.eval (step M) init := ⟨hdom, rfl⟩
    obtain ⟨hreach, hnone⟩ := mem_eval'.mp hmem
    obtain ⟨n, tr, htr0, htr_step, htr_n⟩ := reaches_to_trace hreach
    let codes : List ℕ := (List.range (n + 1)).map fun i ↦ encodeCfg (tr i)
    obtain ⟨c, d, hbeta⟩ := exists_beta_nat codes
    have hcode : ∀ i ≤ n, c % (1 + (i + 1) * d) = encodeCfg (tr i) := by
      intro i hi
      have hlen : codes.length = n + 1 := by simp [codes]
      have hbi := hbeta i (by omega)
      simpa [codes] using hbi
    refine ⟨n, c, d, ?_⟩
    set v2 := Function.update (Function.update (Function.update v 0 n) 1 c) 2 d
    refine ⟨?_, ?_, ?_⟩
    · rw [paBetaEq_holds_iff]
      simpa [v2, PATerm.eval, htr0, encodeCfg_init] using hcode 0 (Nat.zero_le n)
    · intro i hilt
      rw [paLt_holds_iff] at hilt
      have hi_lt : i < n := by simpa [v2, PATerm.eval] using hilt
      refine ⟨encodeCfg (tr i), encodeCfg (tr (i + 1)), ?_⟩
      set v5 := Function.update (Function.update
        (Function.update v2 3 i) 4 (encodeCfg (tr i))) 5 (encodeCfg (tr (i + 1)))
      refine ⟨?_, ?_, ?_⟩
      · rw [paBetaEq_holds_iff]
        simpa [v5, v2, PATerm.eval] using hcode i (Nat.le_of_lt hi_lt)
      · rw [paBetaEq_holds_iff]
        simpa [v5, v2, PATerm.eval] using hcode (i + 1) hi_lt
      · rw [paStep_holds_iff]
        exact ⟨tr i, tr (i + 1), by simp [v5], by simp [v5], htr_step i hi_lt⟩
    · refine ⟨encodeCfg (tr n), ?_⟩
      set v4 := Function.update v2 4 (encodeCfg (tr n))
      refine ⟨?_, ?_⟩
      · rw [paBetaEq_holds_iff]
        simpa [v4, v2, PATerm.eval] using hcode n (Nat.le_refl n)
      · rw [paHalted_holds_iff]
        exact ⟨tr n, by simp [v4], htr_n ▸ hnone⟩

/-! ## Section 5: Standard-Model Adequacy of `paZFInconsistent` -/

private theorem pzEq_eval (v : ℕ → ℕ) (x y : PAZFTerm) :
    (pzEq x y).eval v = zfEq (x.eval v) (y.eval v) := rfl
private theorem pzMem_eval (v : ℕ → ℕ) (x y : PAZFTerm) :
    (pzMem x y).eval v = zfMem (x.eval v) (y.eval v) := rfl
private theorem pzImp_eval (v : ℕ → ℕ) (φ ψ : PAZFTerm) :
    (pzImp φ ψ).eval v = zfImp (φ.eval v) (ψ.eval v) := rfl
private theorem pzNot_eval (v : ℕ → ℕ) (φ : PAZFTerm) :
    (pzNot φ).eval v = zfNot (φ.eval v) := rfl
private theorem pzAll_eval (v : ℕ → ℕ) (x φ : PAZFTerm) :
    (pzAll x φ).eval v = zfAll (x.eval v) (φ.eval v) := rfl
private theorem pzEx_eval (v : ℕ → ℕ) (x φ : PAZFTerm) :
    (pzEx x φ).eval v = zfEx (x.eval v) (φ.eval v) := rfl
private theorem pzAnd_eval (v : ℕ → ℕ) (φ ψ : PAZFTerm) :
    (pzAnd φ ψ).eval v = zfAnd (φ.eval v) (ψ.eval v) := rfl

private theorem pzB1_eval (v : ℕ → ℕ) (φ ψ χ : PAZFTerm) :
    (pzB1 φ ψ χ).eval v = axB1 (φ.eval v) (ψ.eval v) (χ.eval v) := by
  simp only [pzB1, axB1, pzImp_eval]
private theorem pzB2_eval (v : ℕ → ℕ) (φ : PAZFTerm) :
    (pzB2 φ).eval v = axB2 (φ.eval v) := by
  simp only [pzB2, axB2, pzImp_eval, pzNot_eval]
private theorem pzB3_eval (v : ℕ → ℕ) (φ ψ : PAZFTerm) :
    (pzB3 φ ψ).eval v = axB3 (φ.eval v) (ψ.eval v) := by
  simp only [pzB3, axB3, pzImp_eval, pzNot_eval]
private theorem pzB4_eval (v : ℕ → ℕ) (x φ ψ : PAZFTerm) :
    (pzB4 x φ ψ).eval v = axB4 (x.eval v) (φ.eval v) (ψ.eval v) := by
  simp only [pzB4, axB4, pzImp_eval, pzAll_eval]
private theorem pzB6a_eval (v : ℕ → ℕ) (x y z : PAZFTerm) :
    (pzB6a x y z).eval v = axB6a (x.eval v) (y.eval v) (z.eval v) := by
  simp only [pzB6a, axB6a, pzAnd_eval, pzImp_eval, pzAll_eval, pzEq_eval, pzMem_eval]
private theorem pzB6b_eval (v : ℕ → ℕ) (x y φ : PAZFTerm) :
    (pzB6b x y φ).eval v = axB6b (x.eval v) (y.eval v) (φ.eval v) := by
  simp only [pzB6b, axB6b, pzImp_eval, pzAll_eval]
private theorem pzB6c_eval (v : ℕ → ℕ) (x φ : PAZFTerm) :
    (pzB6c x φ).eval v = axB6c (x.eval v) (φ.eval v) := by
  simp only [pzB6c, axB6c, pzImp_eval, pzEx_eval, pzAll_eval]
private theorem pzB7_eval (v : ℕ → ℕ) (x y : PAZFTerm) :
    (pzB7 x y).eval v = axB7 (x.eval v) (y.eval v) := by
  simp only [pzB7, axB7, pzEx_eval, pzEq_eval]
private theorem pzB8a_eval (v : ℕ → ℕ) (x y z : PAZFTerm) :
    (pzB8a x y z).eval v = axB8a (x.eval v) (y.eval v) (z.eval v) := by
  simp only [pzB8a, axB8a, pzImp_eval, pzEq_eval]
private theorem pzB8b_eval (v : ℕ → ℕ) (x y z : PAZFTerm) :
    (pzB8b x y z).eval v = axB8b (x.eval v) (y.eval v) (z.eval v) := by
  simp only [pzB8b, axB8b, pzImp_eval, pzEq_eval, pzMem_eval]
private theorem pzB8c_eval (v : ℕ → ℕ) (x y z : PAZFTerm) :
    (pzB8c x y z).eval v = axB8c (x.eval v) (y.eval v) (z.eval v) := by
  simp only [pzB8c, axB8c, pzImp_eval, pzEq_eval, pzMem_eval]
private theorem pzExt_eval (v : ℕ → ℕ) : pzExt.eval v = axExt := by
  simp only [pzExt, axExt, pzImp_eval, pzAll_eval, pzAnd_eval, pzMem_eval, pzEq_eval,
    PAZFTerm.eval]
private theorem pzRep_eval (v : ℕ → ℕ) (φ : PAZFTerm) :
    (pzRep φ).eval v = axRep (φ.eval v) := by
  simp only [pzRep, pzRepRhs, axRep, axRepRhs, pzImp_eval, pzAll_eval, pzEx_eval, pzAnd_eval,
    pzMem_eval, pzEq_eval, PAZFTerm.eval]
private theorem pzPow_eval (v : ℕ → ℕ) : pzPow.eval v = axPow := by
  simp only [pzPow, axPow, pzEx_eval, pzAll_eval, pzImp_eval, pzMem_eval, PAZFTerm.eval]
private theorem pzUni_eval (v : ℕ → ℕ) : pzUni.eval v = axUni := by
  simp only [pzUni, axUni, pzEx_eval, pzAll_eval, pzImp_eval, pzEx_eval, pzAnd_eval, pzMem_eval,
    PAZFTerm.eval]
private theorem pzInf_eval (v : ℕ → ℕ) : pzInf.eval v = axInf := by
  simp only [pzInf, pzInfSingleton, axInf, axInfSingleton, pzEx_eval, pzAnd_eval, pzAll_eval,
    pzImp_eval, pzMem_eval, pzEq_eval, PAZFTerm.eval]

/-- Whether formula code `w` is an axiom instance of `ZFProvable` (any constructor except `mp` and
`gen`). -/
private def IsZFAxiom (w : ℕ) : Prop :=
  w = zfEq 0 0 ∨
  (∃ φ ψ χ, w = axB1 φ ψ χ) ∨
  (∃ φ, w = axB2 φ) ∨
  (∃ φ ψ, w = axB3 φ ψ) ∨
  (∃ x φ ψ, w = axB4 x φ ψ) ∨
  (∃ x y z, x ≠ z ∧ z ≠ y ∧ w = axB6a x y z) ∨
  (∃ x y φ, w = axB6b x y φ) ∨
  (∃ x φ, w = axB6c x φ) ∨
  (∃ x y, w = axB7 x y) ∨
  (∃ x y z, w = axB8a x y z) ∨
  (∃ x y z, w = axB8b x y z) ∨
  (∃ x y z, w = axB8c x y z) ∨
  w = axExt ∨
  (∃ φ, w = axRep φ) ∨
  w = axPow ∨
  w = axUni ∨
  w = axInf

private theorem zfProvable_of_axiom {w : ℕ} (h : IsZFAxiom w) : ZFProvable w := by
  rcases h with rfl | ⟨φ, ψ, χ, rfl⟩ | ⟨φ, rfl⟩ | ⟨φ, ψ, rfl⟩ | ⟨x, φ, ψ, rfl⟩ |
    ⟨x, y, z, hxz, hzy, rfl⟩ | ⟨x, y, φ, rfl⟩ | ⟨x, φ, rfl⟩ | ⟨x, y, rfl⟩ |
    ⟨x, y, z, rfl⟩ | ⟨x, y, z, rfl⟩ | ⟨x, y, z, rfl⟩ | rfl | ⟨φ, rfl⟩ | rfl | rfl | rfl
  · exact .moot
  · exact .b1 φ ψ χ
  · exact .b2 φ
  · exact .b3 φ ψ
  · exact .b4 x φ ψ
  · exact .b6a x y z hxz hzy
  · exact .b6b x y φ
  · exact .b6c x φ
  · exact .b7 x y
  · exact .b8a x y z
  · exact .b8b x y z
  · exact .b8c x y z
  · exact .ext
  · exact .rep φ
  · exact .pow
  · exact .uni
  · exact .inf

private theorem paIsZFStep_holds_iff (v : ℕ → ℕ) :
    paIsZFStep.Holds v ↔
      IsZFAxiom (v 4) ∨
      (∃ φ χ j₁ j₂, j₁ < v 3 ∧ j₂ < v 3 ∧
        v 1 % (1 + (j₁ + 1) * v 2) = φ ∧
        v 1 % (1 + (j₂ + 1) * v 2) = χ ∧
        χ = zfImp φ (v 4)) ∨
      (∃ x φ j, j < v 3 ∧ v 1 % (1 + (j + 1) * v 2) = φ ∧ v 4 = zfAll x φ) := by
  unfold paIsZFStep IsZFAxiom
  rw [paDisjList_holds_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  have eq_iff : ∀ (e : PAZFTerm) (out : PATerm) (u : ℕ → ℕ),
      e.freshVar ≤ 10 → out.freshVar ≤ 10 →
      ((e.eqFormula out 10).Holds u ↔ out.eval u = e.eval u) :=
    fun e out u he ho ↦ PAZFTerm.eqFormula_holds_iff e out 10 u he ho
  constructor
  · rintro (h0 | hmp | hgen | hb1 | hb2 | hb3 | hb4 | hb6a | hb6b | hb6c | hb7 |
      hb8a | hb8b | hb8c | hext | hrep | hpow | huni | hinf)
    · rw [eq_iff _ _ _ (by decide) (by decide)] at h0
      exact Or.inl (Or.inl (by simpa [PATerm.eval, pzEq_eval, PAZFTerm.eval] using h0))
    · simp only [PAFormula.Holds] at hmp
      rcases hmp with ⟨n5, n6, n8, n9, h8, h9, hb8, hb9, himp⟩
      set u := Function.update (Function.update
        (Function.update (Function.update v 5 n5) 6 n6) 8 n8) 9 n9
      rw [paLt_holds_iff] at h8 h9
      rw [paBetaEq_holds_iff] at hb8 hb9
      rw [eq_iff _ _ _ (by decide) (by decide)] at himp
      refine Or.inr (Or.inl ⟨n5, n6, n8, n9, ?_, ?_, ?_, ?_, ?_⟩)
      · simpa [u, PATerm.eval] using h8
      · simpa [u, PATerm.eval] using h9
      · simpa [u, PATerm.eval] using hb8
      · simpa [u, PATerm.eval] using hb9
      · simpa [u, PATerm.eval, pzImp_eval, PAZFTerm.eval] using himp
    · simp only [PAFormula.Holds] at hgen
      rcases hgen with ⟨n5, n6, n8, h8, hb8, hall⟩
      set u := Function.update (Function.update (Function.update v 5 n5) 6 n6) 8 n8
      rw [paLt_holds_iff] at h8
      rw [paBetaEq_holds_iff] at hb8
      rw [eq_iff _ _ _ (by decide) (by decide)] at hall
      refine Or.inr (Or.inr ⟨n5, n6, n8, ?_, ?_, ?_⟩)
      · simpa [u, PATerm.eval] using h8
      · simpa [u, PATerm.eval] using hb8
      · simpa [u, PATerm.eval, pzAll_eval, PAZFTerm.eval] using hall
    · simp only [PAFormula.Holds] at hb1
      rcases hb1 with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inl ⟨n5, n6, n7,
        by simpa [PATerm.eval, pzB1_eval, PAZFTerm.eval] using h⟩))
    · simp only [PAFormula.Holds] at hb2
      rcases hb2 with ⟨n5, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inl ⟨n5,
        by simpa [PATerm.eval, pzB2_eval, PAZFTerm.eval] using h⟩)))
    · simp only [PAFormula.Holds] at hb3
      rcases hb3 with ⟨n5, n6, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨n5, n6,
        by simpa [PATerm.eval, pzB3_eval, PAZFTerm.eval] using h⟩))))
    · simp only [PAFormula.Holds] at hb4
      rcases hb4 with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n5, n6, n7,
        by simpa [PATerm.eval, pzB4_eval, PAZFTerm.eval] using h⟩)))))
    · simp only [PAFormula.Holds] at hb6a
      rcases hb6a with ⟨n5, n6, n7, hne1, hne2, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n5, n6, n7, by simpa [PATerm.eval] using hne1,
          by simpa [PATerm.eval] using hne2,
          by simpa [PATerm.eval, pzB6a_eval, PAZFTerm.eval] using h⟩))))))
    · simp only [PAFormula.Holds] at hb6b
      rcases hb6b with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n5, n6, n7,
        by simpa [PATerm.eval, pzB6b_eval, PAZFTerm.eval] using h⟩)))))))
    · simp only [PAFormula.Holds] at hb6c
      rcases hb6c with ⟨n5, n6, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n5, n6,
        by simpa [PATerm.eval, pzB6c_eval, PAZFTerm.eval] using h⟩))))))))
    · simp only [PAFormula.Holds] at hb7
      rcases hb7 with ⟨n5, n6, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n5, n6, by simpa [PATerm.eval, pzB7_eval, PAZFTerm.eval] using h⟩)))))))))
    · simp only [PAFormula.Holds] at hb8a
      rcases hb8a with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨n5, n6, n7, by simpa [PATerm.eval, pzB8a_eval, PAZFTerm.eval] using h⟩))))))))))
    · simp only [PAFormula.Holds] at hb8b
      rcases hb8b with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨n5, n6, n7,
          by simpa [PATerm.eval, pzB8b_eval, PAZFTerm.eval] using h⟩)))))))))))
    · simp only [PAFormula.Holds] at hb8c
      rcases hb8c with ⟨n5, n6, n7, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨n5, n6, n7,
          by simpa [PATerm.eval, pzB8c_eval, PAZFTerm.eval] using h⟩))))))))))))
    · rw [eq_iff _ _ _ (by decide) (by decide)] at hext
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl
          (by simpa [PATerm.eval, pzExt_eval] using hext))))))))))))))
    · simp only [PAFormula.Holds] at hrep
      rcases hrep with ⟨n5, h⟩
      rw [eq_iff _ _ _ (by decide) (by decide)] at h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n5,
          by simpa [PATerm.eval, pzRep_eval, PAZFTerm.eval] using h⟩))))))))))))))
    · rw [eq_iff _ _ _ (by decide) (by decide)] at hpow
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (by simpa [PATerm.eval, pzPow_eval] using hpow))))))))))))))))
    · rw [eq_iff _ _ _ (by decide) (by decide)] at huni
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (by simpa [PATerm.eval, pzUni_eval] using huni)))))))))))))))))
    · rw [eq_iff _ _ _ (by decide) (by decide)] at hinf
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (by simpa [PATerm.eval, pzInf_eval] using hinf)))))))))))))))))
  · rintro (hax | ⟨φ, χ, j₁, j₂, hj₁, hj₂, hb₁, hb₂, hχ⟩ | ⟨x, φ, j, hj, hbj, hall⟩)
    · rcases hax with h0 | ⟨a, b, c, h⟩ | ⟨a, h⟩ | ⟨a, b, h⟩ | ⟨a, b, c, h⟩ |
        ⟨a, b, c, hac, hcb, h⟩ | ⟨a, b, c, h⟩ | ⟨a, b, h⟩ | ⟨a, b, h⟩ |
        ⟨a, b, c, h⟩ | ⟨a, b, c, h⟩ | ⟨a, b, c, h⟩ | hext | ⟨a, h⟩ | hpow | huni | hinf
      · refine Or.inl ?_
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzEq_eval, PAZFTerm.eval] using h0
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, ?_⟩)))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzB1_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ?_⟩))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzB2_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ?_⟩)))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzB3_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, ?_⟩))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzB4_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨a, b, c, ?_, ?_, ?_⟩)))))))
        · simpa [PAFormula.Holds, PATerm.eval] using hac
        · simpa [PAFormula.Holds, PATerm.eval] using hcb
        · rw [eq_iff _ _ _ (by decide) (by decide)]
          simpa [PATerm.eval, pzB6a_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨a, b, c, ?_⟩))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzB6b_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨a, b, ?_⟩)))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzB6c_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl ⟨a, b, ?_⟩))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzB7_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, ?_⟩)))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzB8a_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, ?_⟩))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzB8b_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, ?_⟩)))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzB8c_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzExt_eval] using hext
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ?_⟩)))))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzRep_eval, PAZFTerm.eval] using h
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ?_))))))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzPow_eval] using hpow
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl ?_)))))))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzUni_eval] using huni
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr ?_)))))))))))))))))
        rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzInf_eval] using hinf
    · refine Or.inr (Or.inl ⟨φ, χ, j₁, j₂, ?_, ?_, ?_, ?_, ?_⟩)
      · rw [paLt_holds_iff]; simpa [PATerm.eval] using hj₁
      · rw [paLt_holds_iff]; simpa [PATerm.eval] using hj₂
      · rw [paBetaEq_holds_iff]; simpa [PATerm.eval] using hb₁
      · rw [paBetaEq_holds_iff]; simpa [PATerm.eval] using hb₂
      · rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzImp_eval, PAZFTerm.eval] using hχ
    · refine Or.inr (Or.inr (Or.inl ⟨x, φ, j, ?_, ?_, ?_⟩))
      · rw [paLt_holds_iff]; simpa [PATerm.eval] using hj
      · rw [paBetaEq_holds_iff]; simpa [PATerm.eval] using hbj
      · rw [eq_iff _ _ _ (by decide) (by decide)]
        simpa [PATerm.eval, pzAll_eval, PAZFTerm.eval] using hall

private def ValidZFDeriv (L : List ℕ) : Prop :=
  ∀ (i : ℕ) (hi : i < L.length),
    IsZFAxiom L[i] ∨
    (∃ (j₁ j₂ : ℕ) (hj₁ : j₁ < i) (hj₂ : j₂ < i),
      L[j₂]'(lt_trans hj₂ hi) = zfImp (L[j₁]'(lt_trans hj₁ hi)) L[i]) ∨
    (∃ (x j : ℕ) (hj : j < i), L[i] = zfAll x (L[j]'(lt_trans hj hi)))

private theorem validZFDeriv_append {L₁ L₂ : List ℕ} (h₁ : ValidZFDeriv L₁)
    (h₂ : ValidZFDeriv L₂) : ValidZFDeriv (L₁ ++ L₂) := by
  intro i hi
  rw [List.length_append] at hi
  rcases Nat.lt_or_ge i L₁.length with hlt | hge
  · rw [List.getElem_append_left hlt]
    rcases h₁ i hlt with hax | ⟨j₁, j₂, hj₁, hj₂, hmp⟩ | ⟨x, j, hj, hgen⟩
    · exact Or.inl hax
    · refine Or.inr (Or.inl ⟨j₁, j₂, hj₁, hj₂, ?_⟩)
      rwa [List.getElem_append_left (lt_trans hj₁ hlt),
        List.getElem_append_left (lt_trans hj₂ hlt)]
    · refine Or.inr (Or.inr ⟨x, j, hj, ?_⟩)
      rwa [List.getElem_append_left (lt_trans hj hlt)]
  · let k := i - L₁.length
    have hk : k < L₂.length := by omega
    have hik : i = L₁.length + k := by omega
    have hget : ∀ (m : ℕ) (hm : m < L₂.length) (hm' : L₁.length + m < (L₁ ++ L₂).length),
        (L₁ ++ L₂)[L₁.length + m]'hm' = L₂[m]'hm := by
      intro m hm hm'
      simp
    have hi_eq : (L₁ ++ L₂)[i] = L₂[k] := by
      simp [hik]
    rw [hi_eq]
    rcases h₂ k hk with hax | ⟨j₁, j₂, hj₁, hj₂, hmp⟩ | ⟨x, j, hj, hgen⟩
    · exact Or.inl hax
    · refine Or.inr (Or.inl ⟨L₁.length + j₁, L₁.length + j₂, by omega, by omega, ?_⟩)
      rw [hget j₁ (lt_trans hj₁ hk), hget j₂ (lt_trans hj₂ hk)]
      exact hmp
    · refine Or.inr (Or.inr ⟨x, L₁.length + j, by omega, ?_⟩)
      rw [hget j (lt_trans hj hk)]
      exact hgen

private theorem exists_validZFDeriv {φ : ℕ} (h : ZFProvable φ) :
    ∃ (L : List ℕ) (hne : L ≠ []), ValidZFDeriv L ∧ L[L.length - 1]'(by
      exact Nat.sub_lt (List.length_pos_of_ne_nil hne) Nat.one_pos) = φ := by
  have single_ax : ∀ {w : ℕ}, IsZFAxiom w →
      ∃ (L : List ℕ) (hne : L ≠ []), ValidZFDeriv L ∧ L[L.length - 1]'(by
        exact Nat.sub_lt (List.length_pos_of_ne_nil hne) Nat.one_pos) = w := by
    intro w hw
    refine ⟨[w], List.cons_ne_nil _ _, ?_, rfl⟩
    intro i hi
    have hi0 : i = 0 := by
      simp only [List.length_singleton] at hi
      omega
    subst hi0
    exact Or.inl hw
  induction h with
  | moot => exact single_ax (Or.inl rfl)
  | b1 a b c => exact single_ax (Or.inr (Or.inl ⟨a, b, c, rfl⟩))
  | b2 a => exact single_ax (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩)))
  | b3 a b => exact single_ax (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))))
  | b4 a b c => exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, rfl⟩)))))
  | b6a a b c hac hcb =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, hac, hcb, rfl⟩))))))
  | b6b a b c =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, rfl⟩)))))))
  | b6c a b =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨a, b, rfl⟩))))))))
  | b7 a b =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨a, b, rfl⟩)))))))))
  | b8a a b c =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨a, b, c, rfl⟩))))))))))
  | b8b a b c =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨a, b, c, rfl⟩)))))))))))
  | b8c a b c =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨a, b, c, rfl⟩))))))))))))
  | ext =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))
  | rep a =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩))))))))))))))
  | pow =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))
  | uni =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))
  | inf =>
    exact single_ax (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))))))))))
  | @mp φ ψ _ _ ih₁ ih₂ =>
    rcases ih₁ with ⟨L₁, hne₁, hv₁, hlast₁⟩
    rcases ih₂ with ⟨L₂, hne₂, hv₂, hlast₂⟩
    have hp₁ : 0 < L₁.length := List.length_pos_of_ne_nil hne₁
    have hp₂ : 0 < L₂.length := List.length_pos_of_ne_nil hne₂
    let L₁₂ := L₁ ++ L₂
    have hv₁₂ : ValidZFDeriv L₁₂ := validZFDeriv_append hv₁ hv₂
    let L := L₁₂ ++ [ψ]
    have hne : L ≠ [] := List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    refine ⟨L, hne, ?_, ?_⟩
    · intro i hi
      simp only [L, L₁₂, List.length_append, List.length_singleton] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · have hlt' : i < L₁₂.length := by
          simp only [L₁₂, List.length_append]
          exact hlt
        simp only [L, List.getElem_append_left hlt']
        rcases hv₁₂ i hlt' with hax | ⟨j₁, j₂, hj₁, hj₂, hmp⟩ | ⟨x, j, hj, hgen⟩
        · exact Or.inl hax
        · refine Or.inr (Or.inl ⟨j₁, j₂, hj₁, hj₂, ?_⟩)
          simpa only [List.getElem_append_left (lt_trans hj₁ hlt'),
            List.getElem_append_left (lt_trans hj₂ hlt')] using hmp
        · refine Or.inr (Or.inr ⟨x, j, hj, ?_⟩)
          simpa only [List.getElem_append_left (lt_trans hj hlt')] using hgen
      · refine Or.inr (Or.inl ⟨L₁.length - 1, L₁.length + L₂.length - 1,
          by omega, by omega, ?_⟩)
        have hget_end : L[L₁.length + L₂.length] = ψ := by
          simp [L, L₁₂]
        have hget1 : L[L₁.length - 1]'(by simp [L, L₁₂]; omega) = φ := by
          rw [List.getElem_append_left (by simp [L₁₂]; omega)]
          rw [List.getElem_append_left (by omega)]
          exact hlast₁
        have hget2 : L[L₁.length + L₂.length - 1]'(by simp [L, L₁₂]; omega) = zfImp φ ψ := by
          rw [List.getElem_append_left (by simp [L₁₂]; omega)]
          have hidx : L₁.length + L₂.length - 1 = L₁.length + (L₂.length - 1) := by omega
          simp only [L₁₂, hidx, List.getElem_append_right (Nat.le_add_right _ _),
            Nat.add_sub_cancel_left]
          exact hlast₂
        rw [hget_end, hget1, hget2]
    · simp [L, L₁₂]
  | @gen x φ _ ih =>
    rcases ih with ⟨L₁, hne₁, hv₁, hlast₁⟩
    have hp₁ : 0 < L₁.length := List.length_pos_of_ne_nil hne₁
    let L := L₁ ++ [zfAll x φ]
    have hne : L ≠ [] := List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    refine ⟨L, hne, ?_, ?_⟩
    · intro i hi
      simp only [L, List.length_append, List.length_singleton] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · simp only [L, List.getElem_append_left hlt]
        rcases hv₁ i hlt with hax | ⟨j₁, j₂, hj₁, hj₂, hmp⟩ | ⟨y, j, hj, hgen⟩
        · exact Or.inl hax
        · refine Or.inr (Or.inl ⟨j₁, j₂, hj₁, hj₂, ?_⟩)
          simpa only [List.getElem_append_left (lt_trans hj₁ hlt),
            List.getElem_append_left (lt_trans hj₂ hlt)] using hmp
        · refine Or.inr (Or.inr ⟨y, j, hj, ?_⟩)
          simpa only [List.getElem_append_left (lt_trans hj hlt)] using hgen
      · refine Or.inr (Or.inr ⟨x, L₁.length - 1, by omega, ?_⟩)
        have hget_end : L[L₁.length] = zfAll x φ := by simp [L]
        have hget1 : L[L₁.length - 1]'(by simp [L]) = φ := by
          rw [List.getElem_append_left (by omega)]
          exact hlast₁
        rw [hget_end, hget1]
    · simp [L]

/-- Standard-model adequacy of `paZFInconsistent`: `paZFInconsistent.Holds v` holds in `ℕ` if and
only if `ZFInconsistent` holds (proved constructively without `Classical.choice`). -/
theorem paZFInconsistent_holds_iff_zfInconsistent (v : ℕ → ℕ) :
    paZFInconsistent.Holds v ↔ ZFInconsistent := by
  unfold paZFInconsistent ZFInconsistent
  simp only [PAFormula.Holds]
  constructor
  · rintro ⟨n, c, d, hsteps, hfinal⟩
    set v2 := Function.update (Function.update (Function.update v 0 n) 1 c) 2 d
    have hprov : ∀ i ≤ n, ZFProvable (c % (1 + (i + 1) * d)) := by
      intro i
      induction i using Nat.strongRecOn with
      | ind i ih =>
        intro hle
        have hle_holds : (paLe (.var 3) (.var 0)).Holds (Function.update v2 3 i) := by
          rw [paLe_holds_iff]
          simp [v2, PATerm.eval, hle]
        obtain ⟨w, hbw, hst⟩ := hsteps i hle_holds
        set v4 := Function.update (Function.update v2 3 i) 4 w
        have hw_eq : c % (1 + (i + 1) * d) = w := by
          have := (paBetaEq_holds_iff v4 (.var 1) (.var 2) (.var 3) (.var 4)).mp hbw
          simpa [v4, v2, PATerm.eval] using this
        rw [hw_eq]
        have hst' := (paIsZFStep_holds_iff v4).mp hst
        simp only [v4, v2, Function.update_self,
          Function.update_of_ne (by decide : (3 : ℕ) ≠ 4),
          Function.update_of_ne (by decide : (1 : ℕ) ≠ 4),
          Function.update_of_ne (by decide : (1 : ℕ) ≠ 3),
          Function.update_of_ne (by decide : (1 : ℕ) ≠ 2),
          Function.update_of_ne (by decide : (2 : ℕ) ≠ 4),
          Function.update_of_ne (by decide : (2 : ℕ) ≠ 3)] at hst'
        rcases hst' with hax | ⟨φ, χ, j₁, j₂, hj₁, hj₂, hb₁, hb₂, hχ⟩ | ⟨x, φ, j, hj, hbj, hall⟩
        · exact zfProvable_of_axiom hax
        · have p₁ : ZFProvable φ := by
            rw [← hb₁]
            exact ih j₁ hj₁ (by omega)
          have p₂ : ZFProvable (zfImp φ w) := by
            rw [← hχ, ← hb₂]
            exact ih j₂ hj₂ (by omega)
          exact .mp p₁ p₂
        · rw [hall]
          refine .gen x ?_
          rw [← hbj]
          exact ih j hj (by omega)
    rcases hfinal with ⟨w, hbw, hmem⟩
    set v4 := Function.update v2 4 w
    have hw_eq : c % (1 + (n + 1) * d) = w := by
      have := (paBetaEq_holds_iff v4 (.var 1) (.var 2) (.var 0) (.var 4)).mp hbw
      simpa [v4, v2, PATerm.eval] using this
    have hw_mem : w = zfMem 0 0 := by
      have := (PAZFTerm.eqFormula_holds_iff (pzMem (.const 0) (.const 0)) (.var 4) 10 v4
        (by decide) (by decide)).mp hmem
      simpa [v4, PATerm.eval, pzMem_eval, PAZFTerm.eval] using this
    rw [← hw_mem, ← hw_eq]
    exact hprov n (Nat.le_refl n)
  · intro hinc
    obtain ⟨L, hne, hvalid, hlast⟩ := exists_validZFDeriv hinc
    have hpos : 0 < L.length := List.length_pos_of_ne_nil hne
    let n := L.length - 1
    obtain ⟨c, d, hbeta⟩ := exists_beta_nat L
    refine ⟨n, c, d, ?_⟩
    set v2 := Function.update (Function.update (Function.update v 0 n) 1 c) 2 d
    refine ⟨?_, ?_⟩
    · intro i hle
      rw [paLe_holds_iff] at hle
      have hi_le : i ≤ n := by simpa [v2, PATerm.eval] using hle
      have hi_lt : i < L.length := by omega
      refine ⟨L[i], ?_⟩
      set v4 := Function.update (Function.update v2 3 i) 4 L[i]
      refine ⟨?_, ?_⟩
      · rw [paBetaEq_holds_iff]
        simpa [v4, v2, PATerm.eval] using hbeta i hi_lt
      · rw [paIsZFStep_holds_iff]
        simp only [v4, v2, Function.update_self,
          Function.update_of_ne (by decide : (3 : ℕ) ≠ 4),
          Function.update_of_ne (by decide : (1 : ℕ) ≠ 4),
          Function.update_of_ne (by decide : (1 : ℕ) ≠ 3),
          Function.update_of_ne (by decide : (1 : ℕ) ≠ 2),
          Function.update_of_ne (by decide : (2 : ℕ) ≠ 4),
          Function.update_of_ne (by decide : (2 : ℕ) ≠ 3)]
        rcases hvalid i hi_lt with hax | ⟨j₁, j₂, hj₁, hj₂, hmp⟩ | ⟨x, j, hj, hgen⟩
        · exact Or.inl hax
        · exact Or.inr (Or.inl ⟨L[j₁]'(lt_trans hj₁ hi_lt), L[j₂]'(lt_trans hj₂ hi_lt),
            j₁, j₂, hj₁, hj₂, hbeta j₁ (lt_trans hj₁ hi_lt),
            hbeta j₂ (lt_trans hj₂ hi_lt), hmp⟩)
        · exact Or.inr (Or.inr ⟨x, L[j]'(lt_trans hj hi_lt), j, hj,
            hbeta j (lt_trans hj hi_lt), hgen⟩)
    · refine ⟨zfMem 0 0, ?_⟩
      set v4 := Function.update v2 4 (zfMem 0 0)
      refine ⟨?_, ?_⟩
      · rw [paBetaEq_holds_iff]
        have hbn := hbeta n (by omega)
        rw [hlast] at hbn
        simpa [v4, v2, PATerm.eval] using hbn
      · rw [PAZFTerm.eqFormula_holds_iff _ (.var 4) 10 v4 (by decide) (by decide)]
        simp [v4, PATerm.eval, pzMem_eval, PAZFTerm.eval]

end ConjectureMachines.Semantics.PA
