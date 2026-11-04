/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Riemann120.Backend
public import Cryptids.Semantics.Riemann.Gadgets
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Layer 2: 63-Node Control DAG, 5-Register Machine & Arithmetic Invariants (`riemann121`)

This module formalizes Layer 2 for the 121-state canonical predecessor machine `canon121`
(`riemann121`) of Shunia's 120-state Riemann Hypothesis counterexample search machine:

1. **63-Node Control DAG & Call-Stack Dispatcher**:
   - `walkInternal`, `walkTape`, `outcomeToInstr`, `evalStack`: call-stack decision tree
     dispatcher rooted at `State 27` (`main.0`) over `ConjectureMachines.Riemann120.rh121Trans`.
   - Exhaustive `decide` verification across all valid control words and reachable call stacks
     from `State 27` that `bits.length ≤ 18` and `[1, 1, 0] ++ bits ++ [1, 0]` contains
     no four consecutive zeros (`hasNoFourZeros`).

2. **5-Register Abstract Machine (`RhRegCfg`, `rhRegStep`, `rhRegNSteps`, `RhRegHalts`)**:
   - Operates on `[m, j, x, f, v]` (`c.regs : List ℕ`) and `c.stack : List (Fin 2)` starting
     from `rhRegInit = ⟨[], [0, 0, 0, 0, 0]⟩`.
   - Also provides equivalence with the dummy-zero-appending tape-register semantics
     (`RhRegTapeHalts`).

3. **Shunia's Pure Mathematical Quantities & Self-Sieving Identity**:
   - `primorial`, `shuniaProd` ($A_n = n! \prod_{p \le n} p$), `offsetDigits`,
     `shuniaDeficit` ($\Delta_n$), `quarterClock` ($q_n$), and `ShuniaCounterexample`.
   - Self-sieving theorem (`prime_iff_not_dvd_shuniaProd` and `shuniaProd_step`, Lemma 2.1 of
     `rhtm.tex`).

4. **Subroutine Verification (`SubEval`) & Main Loop Halting Equivalence**:
   - Complete functional specifications for `move`, `dec_f`, `seed_deficit`, `fold`,
     `transform`, `twice`, `divide`, `product_step`, `product`, `digits`, `halve(j)`,
     `halve(f)`, `width`, `compare`, and `main`, culminating in
     `rhRegHalts_iff_exists_shuniaCounterexample`.
-/

@[expose] public section

namespace ConjectureMachines.Riemann120.Layer2

open Turing (Dir)
open StateTransition
open ConjectureMachines.Riemann120
  (rh121Trans isPrimeBool primorial shuniaProd offsetDigits shuniaDeficit quarterClock
   ShuniaCounterexample)

set_option linter.style.setOption false
set_option linter.flexible false
set_option maxRecDepth 200000

/-! ## Section 1: Control DAG & Leaf Classification of `riemann121` (`canon121`) -/

/-- Enumerates all exact length-`n` internal DAG paths starting at state `q`. -/
def dagExactPaths : ℕ → Fin 121 → List (List (Fin 2))
  | 0, q => if isInternalNode q then [[]] else []
  | n + 1, q =>
    if isInternalNode q then
      ([0, 1] : List (Fin 2)).flatMap fun b =>
        match rh121Trans q b with
        | some (w, .right, q') =>
          if w == b && isInternalNode q' then
            (dagExactPaths n q').map (b :: ·)
          else []
        | _ => []
    else []

theorem mem_dagExactPaths_of_walkInternal {P : List (Fin 2)} {q q' : Fin 121}
    (h : walkInternal q P = some q') :
    P ∈ dagExactPaths P.length q := by
  induction P generalizing q with
  | nil =>
    simp only [walkInternal] at h
    by_cases hi : isInternalNode q = true
    · simp [dagExactPaths, hi]
    · simp [hi] at h
  | cons b bs ih =>
    simp only [walkInternal] at h
    by_cases hi : isInternalNode q = true
    · simp only [hi, ↓reduceIte] at h
      rcases htr : rh121Trans q b with _ | ⟨w, d, q₁⟩
      · simp [htr] at h
      · cases d with
        | left => simp [htr] at h
        | right =>
          simp only [htr] at h
          by_cases hcond : (w == b && isInternalNode q₁) = true
          · simp only [hcond, ↓reduceIte] at h
            have hmem := ih h
            simp only [List.length_cons, dagExactPaths, hi, ↓reduceIte, List.mem_flatMap]
            refine ⟨b, ?_, ?_⟩
            · rcases ConjectureMachines.Semantics.Riemann.Layer1.fin2_cases b with rfl | rfl <;>
                simp
            · simp [htr, hcond, hmem]
          · simp [hcond] at h
    · simp [hi] at h

theorem dagExactPaths_15_eq_nil (q : Fin 121) : dagExactPaths 15 q = [] := by
  revert q; decide

theorem walkInternal_take_of_some {k : ℕ} {P : List (Fin 2)} {q q' : Fin 121}
    (h : walkInternal q P = some q') :
    ∃ qk, walkInternal q (P.take k) = some qk := by
  induction k generalizing P q with
  | zero =>
    simp only [List.take_zero, walkInternal]
    cases P with
    | nil =>
      simp only [walkInternal] at h
      by_cases hi : isInternalNode q = true
      · exact ⟨q, by simp [hi]⟩
      · simp [hi] at h
    | cons b bs =>
      simp only [walkInternal] at h
      by_cases hi : isInternalNode q = true
      · exact ⟨q, by simp [hi]⟩
      · simp [hi] at h
  | succ k ih =>
    cases P with
    | nil =>
      simp only [List.take_nil, walkInternal]
      simp only [walkInternal] at h
      by_cases hi : isInternalNode q = true
      · exact ⟨q, by simp [hi]⟩
      · simp [hi] at h
    | cons b bs =>
      simp only [walkInternal] at h
      by_cases hi : isInternalNode q = true
      · simp only [hi, ↓reduceIte] at h
        rcases htr : rh121Trans q b with _ | ⟨w, d, q₁⟩
        · simp [htr] at h
        · cases d with
          | left => simp [htr] at h
          | right =>
            simp only [htr] at h
            by_cases hcond : (w == b && isInternalNode q₁) = true
            · simp only [hcond, ↓reduceIte] at h
              obtain ⟨qk, hqk⟩ := ih h
              refine ⟨qk, ?_⟩
              simp [List.take_succ_cons, walkInternal, hi, htr, hcond, hqk]
            · simp [hcond] at h
      · simp [hi] at h

theorem walkInternal_length_le_14 {P : List (Fin 2)} {q q' : Fin 121}
    (h : walkInternal q P = some q') : P.length ≤ 14 := by
  if hle : P.length ≤ 14 then
    exact hle
  else
    exfalso
    have h15 : 15 ≤ P.length := by omega
    obtain ⟨q15, hq15⟩ := walkInternal_take_of_some (k := 15) h
    have hmem := mem_dagExactPaths_of_walkInternal hq15
    have hlen : (P.take 15).length = 15 := by simp; omega
    rw [hlen, dagExactPaths_15_eq_nil q] at hmem
    cases hmem

/-- All 120 valid internal control prefixes `P` reachable from `State 27` (`main.0`). -/
def allControlPrefixes : List (List (Fin 2)) :=
  (List.range 15).flatMap fun n => dagExactPaths n 27

theorem mem_allControlPrefixes_of_walkInternal {P : List (Fin 2)} {q : Fin 121}
    (h : walkInternal 27 P = some q) :
    P ∈ allControlPrefixes := by
  have hle := walkInternal_length_le_14 h
  have hmem := mem_dagExactPaths_of_walkInternal h
  simp only [allControlPrefixes, List.mem_flatMap, List.mem_range]
  exact ⟨P.length, by omega, hmem⟩

/-- Every valid control prefix `bits` from `State 27` has length `≤ 18` and no `0000` run
in `[1, 1, 0] ++ bits ++ [1, 0]`. -/
theorem controlPrefix_bounds_and_noFourZeros :
    ∀ bits ∈ allControlPrefixes,
      bits.length ≤ 18 ∧ hasNoFourZeros ([1, 1, 0] ++ bits ++ [1, 0]) = true := by
  decide

/-- All 121 terminal control words `P ++ [b]` leaving the internal DAG from `State 27`. -/
def allTerminalWords : List (List (Fin 2)) :=
  allControlPrefixes.flatMap fun P =>
    match walkInternal 27 P with
    | some q =>
      ([0, 1] : List (Fin 2)).filterMap fun b =>
        match rh121Trans q b with
        | some (_, .right, q') => if isInternalNode q' then none else some (P ++ [b])
        | _ => some (P ++ [b])
    | none => []

/-- Every terminal control word `bits` leaving `State 27` has length `≤ 18` and no `0000` run
in `[1, 1, 0] ++ bits ++ [1, 0]`. -/
theorem terminalWord_bounds_and_noFourZeros :
    ∀ bits ∈ allTerminalWords,
      bits.length ≤ 18 ∧ hasNoFourZeros ([1, 1, 0] ++ bits ++ [1, 0]) = true := by
  decide

theorem rhRegNSteps_stack_valid_and_noFourZeros {n : ℕ} {c : RhRegCfg}
    (hn : rhRegNSteps n rhRegInit = some c) :
    isValidStack c.stack = true ∧
    c.stack.length ≤ 18 ∧
    hasNoFourZeros ([1, 1, 0] ++ c.stack ++ [1, 0]) = true := by
  have hvalid : ∀ m {c₀ c₁ : RhRegCfg},
      isValidStack c₀.stack = true → rhRegNSteps m c₀ = some c₁ →
      isValidStack c₁.stack = true := by
    intro m
    induction m with
    | zero =>
      intro c₀ c₁ hv hm
      injection hm with h_eq; subst h_eq; exact hv
    | succ m ih =>
      intro c₀ c₁ hv hm
      unfold rhRegNSteps at hm
      rcases hs : rhRegStep c₀ with _ | cm
      · simp [hs] at hm
      · rw [hs, Option.bind_some] at hm
        exact ih (rhRegStep_preserves_isValidStack hv hs) hm
  have hv := hvalid n isValidStack_nil hn
  have hmem : c.stack ∈ allValidStacks := List.contains_iff_mem.mp hv
  have hprops := isValidStack_closed_and_noFourZeros c.stack hmem
  exact ⟨hv, hprops.1, hprops.2.1⟩

/-- Tape-faithful variant of `rhRegStep` appending a dummy `0` register on `decnz > 0`. -/
def rhRegTapeStep (c : RhRegCfg) : Option RhRegCfg :=
  match evalStack c.stack with
  | .halt => none
  | .jump stack' => some ⟨stack', c.regs⟩
  | .inc r stack_succ =>
    some ⟨stack_succ, c.regs.set r (c.regs.getD r 0 + 1)⟩
  | .decnz r stack_succ stack_fail =>
    if c.regs.getD r 0 == 0 then
      some ⟨stack_fail, c.regs⟩
    else
      some ⟨stack_succ, c.regs.set r (c.regs.getD r 0 - 1) ++ [0]⟩

def rhRegTapeNSteps : ℕ → RhRegCfg → Option RhRegCfg
  | 0, c => some c
  | n + 1, c => (rhRegTapeStep c).bind (rhRegTapeNSteps n)

def RhRegTapeHalts : Prop :=
  (StateTransition.eval rhRegTapeStep rhRegInit).Dom

def RhRegSim (c₁ c₂ : RhRegCfg) : Prop :=
  c₁.stack = c₂.stack ∧ 5 ≤ c₁.regs.length ∧ 5 ≤ c₂.regs.length ∧
    c₁.regs.take 5 = c₂.regs.take 5

theorem evalStack_reg_lt_5 (bits : List (Fin 2)) :
    match evalStack bits with
    | .inc r _ => r < 5
    | .decnz r _ _ => r < 5
    | _ => True := by
  unfold evalStack outcomeToInstr
  rcases walkTape 27 [] (bits ++ List.replicate 18 0) with _ | ⟨q', _, _⟩ | ⟨q', _, _⟩ | _
  · trivial
  · dsimp only
    split <;> try trivial
    all_goals (split at * <;> contradiction)
  · by_cases h : isLeafInc q' = true <;> simp [h, leafReg_lt_5 q']
  · trivial

theorem getD_eq_of_take_5 {r₁ r₂ : List ℕ} {k : ℕ} (hk : k < 5)
    (h : r₁.take 5 = r₂.take 5) :
    r₁.getD k 0 = r₂.getD k 0 := by
  have h1 : r₁.getD k 0 = (r₁.take 5).getD k 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
  have h2 : r₂.getD k 0 = (r₂.take 5).getD k 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
  rw [h1, h2, h]

theorem rhRegTapeStep_sim {c₁ c₂ : RhRegCfg} (hsim : RhRegSim c₁ c₂) :
    match rhRegTapeStep c₁, rhRegStep c₂ with
    | none, none => True
    | some c₁', some c₂' => RhRegSim c₁' c₂'
    | _, _ => False := by
  rcases hsim with ⟨hstack, hlen₁, hlen₂, htake⟩
  have hr_lt := evalStack_reg_lt_5 c₁.stack
  unfold rhRegTapeStep rhRegStep
  rw [← hstack]
  rcases hev : evalStack c₁.stack with _ | stack' | ⟨r, stack_succ⟩ | ⟨r, stack_succ, stack_fail⟩
  · trivial
  · exact ⟨rfl, hlen₁, hlen₂, htake⟩
  · rw [hev] at hr_lt
    have hget := getD_eq_of_take_5 hr_lt htake
    refine ⟨rfl, by simp [hlen₁], by simp [hlen₂], ?_⟩
    rw [List.take_set, List.take_set, hget, htake]
  · rw [hev] at hr_lt
    have hget := getD_eq_of_take_5 hr_lt htake
    dsimp only
    rw [hget]
    by_cases hz : (c₂.regs.getD r 0 == 0) = true
    · simp only [hz, ↓reduceIte]
      exact ⟨rfl, hlen₁, hlen₂, htake⟩
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      refine ⟨rfl, by simp; omega, by simp [hlen₂], ?_⟩
      dsimp only
      have hle₁ : 5 ≤ (c₁.regs.set r (c₂.regs.getD r 0 - 1)).length := by simp [hlen₁]
      rw [List.take_append_of_le_length hle₁, List.take_set, List.take_set, htake]

/-! ## Section 4: Pure Mathematical Quantities & Self-Sieving Identity (`rhtm.tex`) -/

theorem primorial_pos (n : ℕ) : 0 < primorial n := by
  induction n with
  | zero => decide
  | succ n ih =>
    unfold primorial
    cases isPrimeBool (n + 1) <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ih
    · exact Nat.mul_pos (Nat.succ_pos n) ih

theorem shuniaProd_pos (n : ℕ) : 0 < shuniaProd n :=
  Nat.mul_pos (Nat.factorial_pos n) (primorial_pos n)

private theorem isPrimeBool_two_le {p : ℕ} (hp : isPrimeBool p = true) : 2 ≤ p := by
  simp only [isPrimeBool, Bool.and_eq_true, decide_eq_true_eq] at hp
  exact hp.1

private theorem isPrimeBool_not_dvd {p d : ℕ} (hp : isPrimeBool p = true)
    (hd2 : 2 ≤ d) (hdp : d < p) : ¬ (d ∣ p) := by
  simp only [isPrimeBool, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq, ← Nat.dvd_iff_mod_eq_zero] at hp
  rcases hp.2 d hdp with hlt | hndvd
  · omega
  · exact hndvd

private theorem isPrimeBool_dvd_mul {p a b : ℕ} (hp : isPrimeBool p = true)
    (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  have hp2 := isPrimeBool_two_le hp
  let g := Nat.gcd p a
  have hgp : g ∣ p := Nat.gcd_dvd_left p a
  have hga : g ∣ a := Nat.gcd_dvd_right p a
  have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hgp (by omega)
  have hg_le : g ≤ p := Nat.le_of_dvd (by omega) hgp
  by_cases hg1 : g = 1
  · exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left hg1 h)
  · by_cases hgp_eq : g = p
    · exact Or.inl (hgp_eq ▸ hga)
    · exfalso
      exact isPrimeBool_not_dvd hp (by omega) (by omega) hgp

private theorem exists_of_all_false : ∀ (l : List ℕ) (f : ℕ → Bool),
    l.all f = false → ∃ x ∈ l, f x = false
  | [], _, h => by cases h
  | x :: xs, f, h => by
    simp only [List.all_cons] at h
    cases hfx : f x
    · exact ⟨x, List.mem_cons_self, hfx⟩
    · rw [hfx, Bool.true_and] at h
      obtain ⟨y, hy, hfy⟩ := exists_of_all_false xs f h
      exact ⟨y, List.mem_cons_of_mem x hy, hfy⟩

theorem prime_le_of_dvd_primorial {p m : ℕ} (hp : isPrimeBool p = true) :
    p ∣ primorial m → p ≤ m := by
  have hp2 := isPrimeBool_two_le hp
  induction m with
  | zero =>
    intro h
    have h1 : p = 1 := Nat.eq_one_of_dvd_one h
    omega
  | succ m ih =>
    unfold primorial
    cases isPrimeBool (m + 1) <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact fun h => Nat.le_succ_of_le (ih h)
    · intro h
      rcases isPrimeBool_dvd_mul hp h with h1 | h2
      · exact Nat.le_of_dvd (by omega) h1
      · exact Nat.le_succ_of_le (ih h2)

theorem prime_le_of_dvd_factorial {p m : ℕ} (hp : isPrimeBool p = true) :
    p ∣ m.factorial → p ≤ m := by
  have hp2 := isPrimeBool_two_le hp
  induction m with
  | zero =>
    intro h
    have h1 : p = 1 := Nat.eq_one_of_dvd_one h
    omega
  | succ m ih =>
    rw [Nat.factorial_succ]
    intro h
    rcases isPrimeBool_dvd_mul hp h with h1 | h2
    · exact Nat.le_of_dvd (by omega) h1
    · exact Nat.le_succ_of_le (ih h2)

theorem mul_dvd_factorial_of_lt {a b n : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbn : b ≤ n) :
    a * b ∣ n.factorial := by
  have hb_fac : b.factorial = b * (b - 1).factorial := by
    cases b with
    | zero => omega
    | succ b' => simp [Nat.factorial_succ]
  have ha_dvd : a ∣ (b - 1).factorial := Nat.dvd_factorial ha (by omega)
  have hab_dvd : a * b ∣ b.factorial := by
    rw [hb_fac, mul_comm]
    exact Nat.mul_dvd_mul_left b ha_dvd
  exact dvd_trans hab_dvd (Nat.factorial_dvd_factorial hbn)

/-- Lemma 2.1 of `rhtm.tex`: $J \ge 2$ is prime iff $J \nmid A_{J - 1}$. -/
theorem prime_iff_not_dvd_shuniaProd {J : ℕ} (hJ : 2 ≤ J) :
    isPrimeBool J = true ↔ ¬ (J ∣ shuniaProd (J - 1)) := by
  constructor
  · intro hprime hdvd
    unfold shuniaProd at hdvd
    rcases isPrimeBool_dvd_mul hprime hdvd with hfac | hprim
    · have hle := prime_le_of_dvd_factorial hprime hfac
      omega
    · have hle := prime_le_of_dvd_primorial hprime hprim
      omega
  · intro hnotdvd
    cases hpb : isPrimeBool J
    · exfalso
      apply hnotdvd
      by_cases hJ4 : J = 4
      · subst hJ4; decide
      · have hall_false :
            ((List.range J).all fun d => decide (d < 2) || (J % d != 0)) = false := by
          unfold isPrimeBool at hpb
          rw [decide_eq_true hJ, Bool.true_and] at hpb
          exact hpb
        obtain ⟨d, hd_mem, hd_false⟩ := exists_of_all_false _ _ hall_false
        have hd_lt : d < J := List.mem_range.mp hd_mem
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, bne_eq_false_iff_eq] at hd_false
        have hd_ge2 : 2 ≤ d := by omega
        have hd_dvd : d ∣ J := Nat.dvd_of_mod_eq_zero hd_false.2
        have hfac_dvd : J ∣ (J - 1).factorial := by
          let q := J / d
          have hdq : d * q = J := Nat.mul_div_cancel' hd_dvd
          have hq_lt : q < J := Nat.div_lt_self (by omega) (by omega)
          have hq_ge1 : 1 ≤ q := by
            rcases q with _ | _
            · simp at hdq; omega
            · omega
          by_cases heq_dq : d = q
          · rw [← heq_dq] at hdq
            have hd_ne2 : d ≠ 2 := by
              intro h2
              rw [h2] at hdq
              omega
            have hd_ge3 : 3 ≤ d := by omega
            have h2d_lt : 2 * d < d * d := Nat.mul_lt_mul_of_pos_right hd_ge3 (by omega)
            have h2d_le : 2 * d ≤ J - 1 := by omega
            have hmul := mul_dvd_factorial_of_lt (a := d) (b := 2 * d) (by omega) (by omega) h2d_le
            have h2J : d * (2 * d) = 2 * J := by rw [← hdq, Nat.mul_left_comm]
            rw [h2J] at hmul
            exact dvd_trans (dvd_mul_left J 2) hmul
          · rcases lt_or_gt_of_ne heq_dq with hlt | hgt
            · rw [← hdq]
              exact mul_dvd_factorial_of_lt (by omega) hlt (by omega)
            · have hmul : q * d ∣ (J - 1).factorial :=
                mul_dvd_factorial_of_lt hq_ge1 hgt (by omega : d ≤ J - 1)
              rwa [mul_comm, hdq] at hmul
        exact dvd_mul_of_dvd_left hfac_dvd (primorial (J - 1))
    · rfl

theorem primorial_step {J : ℕ} (hJ : 2 ≤ J) :
    primorial J = if isPrimeBool J then J * primorial (J - 1) else primorial (J - 1) := by
  rcases J with _ | n
  · omega
  · rfl

/-- Self-sieving recurrence for $A_J$:
$A_J = J \cdot A_{J-1}$ if $J \mid A_{J-1}$, else $J^2 \cdot A_{J-1}$. -/
theorem shuniaProd_step {J : ℕ} (hJ : 2 ≤ J) :
    shuniaProd J =
      if J ∣ shuniaProd (J - 1) then J * shuniaProd (J - 1)
      else J ^ 2 * shuniaProd (J - 1) := by
  have hfac : J.factorial = J * (J - 1).factorial := by
    cases J with
    | zero => omega
    | succ J' => simp [Nat.factorial_succ]
  have hp_iff := prime_iff_not_dvd_shuniaProd hJ
  by_cases hdvd : J ∣ shuniaProd (J - 1)
  · have hnotp : ¬ isPrimeBool J = true := fun hp => (hp_iff.mp hp) hdvd
    simp only [hdvd, ↓reduceIte]
    simp only [shuniaProd, hfac, primorial_step hJ, hnotp]
    exact Nat.mul_assoc _ _ _
  · have hp : isPrimeBool J = true := hp_iff.mpr hdvd
    simp only [hdvd, ↓reduceIte]
    simp only [shuniaProd, hfac, primorial_step hJ, hp, ↓reduceIte]
    rw [Nat.pow_two, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm (J - 1).factorial J]

/-! ## Section 5: Subroutine Specification (`SubEval`) & Combinators -/

@[simp] theorem retStack_append_zero (P : List (Fin 2)) :
    retStack (P ++ [0]) = P ++ [1] := by simp [retStack, popBreakRev]

@[simp] theorem retStack_append_one (P : List (Fin 2)) :
    retStack (P ++ [1]) = retStack P := by simp [retStack, popBreakRev]

@[simp] theorem trimZeros_append_zero (P : List (Fin 2)) :
    trimZeros (P ++ [0]) = trimZeros P := by simp [trimZeros, dropLeadingZeros]

@[simp] theorem trimZeros_append_one (P : List (Fin 2)) :
    trimZeros (P ++ [1]) = P ++ [1] := by simp [trimZeros, dropLeadingZeros]

theorem popContinueRev_zero_eq_dropLeadingZeros (rev : List (Fin 2)) :
    popContinueRev 0 rev = dropLeadingZeros rev := by
  induction rev with
  | nil => rfl
  | cons b rest ih =>
    rcases ConjectureMachines.Semantics.Riemann.Layer1.fin2_cases b with rfl | rfl
    · simp [popContinueRev, dropLeadingZeros, ih]
    · rfl

theorem walkTape_of_walkInternal {q q' : Fin 121} {P : List (Fin 2)}
    (h : walkInternal q P = some q') (walked rem : List (Fin 2)) :
    walkTape q walked (P ++ rem) = walkTape q' (walked ++ P) rem := by
  induction P generalizing q walked with
  | nil =>
    simp only [walkInternal] at h
    by_cases hi : isInternalNode q = true
    · simp [hi] at h; subst h; simp
    · simp [hi] at h
  | cons b bs ih =>
    simp only [walkInternal] at h
    by_cases hi : isInternalNode q = true
    · simp only [hi, ↓reduceIte] at h
      rcases htr : rh121Trans q b with _ | ⟨w, d, q₁⟩
      · simp [htr] at h
      · cases d with
        | left => simp [htr] at h
        | right =>
          simp only [htr] at h
          by_cases hcond : (w == b && isInternalNode q₁) = true
          · simp only [hcond, ↓reduceIte] at h
            rw [Bool.and_eq_true] at hcond
            have hw : w = b := beq_iff_eq.mp hcond.1
            subst hw
            have hnotleaf := isLeafState_false_of_isInternalNode q₁ hcond.2
            have hstep := ih h (walked ++ [w])
            simpa [walkTape, htr, hnotleaf, List.append_assoc] using hstep
          · simp [hcond] at h
    · simp [hi] at h

theorem walkInternal_snoc {q q_mid q_end : Fin 121} {P : List (Fin 2)} {b : Fin 2}
    (hP : walkInternal q P = some q_mid)
    (htr : rh121Trans q_mid b = some (b, .right, q_end))
    (hq_end : isInternalNode q_end = true) :
    walkInternal q (P ++ [b]) = some q_end := by
  induction P generalizing q with
  | nil =>
    simp only [walkInternal] at hP
    by_cases hi : isInternalNode q = true
    · simp [hi] at hP; subst hP
      simp [walkInternal, hi, htr, hq_end]
    · simp [hi] at hP
  | cons x xs ih =>
    simp only [List.cons_append, walkInternal] at hP ⊢
    by_cases hi : isInternalNode q = true
    · simp only [hi, ↓reduceIte] at hP ⊢
      rcases htr_q : rh121Trans q x with _ | ⟨w, d, q₁⟩
      · simp [htr_q] at hP
      · cases d with
        | left => simp [htr_q] at hP
        | right =>
          simp only [htr_q] at hP ⊢
          by_cases hc : (w == x && isInternalNode q₁) = true
          · simp only [hc, ↓reduceIte] at hP ⊢
            exact ih hP
          · simp [hc] at hP
    · simp [hi] at hP

theorem evalStack_trimZeros_all :
    ∀ P ∈ allControlPrefixes, evalStack (trimZeros P) = evalStack P := by
  decide

theorem evalStack_trimZeros_of_walkInternal {P : List (Fin 2)} {q : Fin 121}
    (h : walkInternal 27 P = some q) :
    evalStack (trimZeros P) = evalStack P :=
  evalStack_trimZeros_all P (mem_allControlPrefixes_of_walkInternal h)

theorem padTo_of_le {bits : List (Fin 2)} {pos : ℕ} (h : bits.length ≤ pos) :
    padTo bits pos = bits ++ List.replicate (pos - bits.length) 0 := by
  unfold padTo
  rw [List.take_of_length_le]
  simp; omega

theorem padTo_of_ge {bits : List (Fin 2)} {pos : ℕ} (h : pos ≤ bits.length) :
    padTo bits pos = bits.take pos := by
  unfold padTo
  have hsub : pos - bits.length = 0 := by omega
  rw [hsub, List.replicate_zero, List.append_nil]

theorem evalStack_leaf0_of_walkInternal {P : List (Fin 2)} {q q' : Fin 121}
    (h : walkInternal 27 P = some q)
    (htr : rh121Trans q 0 = some (0, .right, q'))
    (hleaf : isLeafState q' = true) :
    evalStack P =
      if isLeafInc q' then
        .inc (leafReg q') (P ++ [1])
      else
        .decnz (leafReg q') (P ++ [1]) (retStack P) := by
  have hwalk : walkTape 27 [] (P ++ List.replicate 18 0) =
      .regLeaf q' (P ++ [0]) (List.replicate 17 0) := by
    rw [walkTape_of_walkInternal h [] (List.replicate 18 0), List.nil_append]
    change walkTape q P (0 :: List.replicate 17 0) = _
    simp [walkTape, htr, hleaf]
  have hpad : padTo P (P.length + 1) = P ++ [0] := by
    rw [padTo_of_le (by omega)]; simp
  have hbrk0 : applyBreak P (P.length + 1) 0 = P ++ [1] := by
    simp [applyBreak, hpad, popBreakRev]
  have hbrk1 : applyBreak P (P.length + 1) 1 = retStack P := by
    simp [applyBreak, hpad, retStack, popBreakRev]
  unfold evalStack
  rw [hwalk]
  simp [outcomeToInstr, hbrk0, hbrk1]

theorem evalStack_leaf1_inc_of_walkInternal {P : List (Fin 2)} {q q' : Fin 121}
    (h : walkInternal 27 P = some q)
    (htr : rh121Trans q 1 = some (1, .right, q'))
    (hleaf : isLeafState q' = true) (hinc : isLeafInc q' = true) :
    evalStack (P ++ [1]) = .inc (leafReg q') (retStack P) := by
  have hwalk : walkTape 27 [] ((P ++ [1]) ++ List.replicate 18 0) =
      .regLeaf q' (P ++ [1]) (List.replicate 18 0) := by
    rw [List.append_assoc, walkTape_of_walkInternal h [] ([1] ++ List.replicate 18 0),
      List.nil_append]
    change walkTape q P (1 :: List.replicate 18 0) = _
    simp [walkTape, htr, hleaf]
  have hpad : padTo (P ++ [1]) (P.length + 1) = P ++ [1] := by
    rw [padTo_of_le (by simp)]; simp
  have hbrk0 : applyBreak (P ++ [1]) (P.length + 1) 0 = retStack P := by
    simp [applyBreak, hpad, retStack, popBreakRev]
  unfold evalStack
  rw [hwalk]
  simp [outcomeToInstr, hinc, hbrk0]

theorem evalStack_break1_of_walkInternal {P : List (Fin 2)} {q q' : Fin 121} {k : ℕ}
    (h : walkInternal 27 P = some q)
    (htr : rh121Trans q 1 = some (0, .left, q'))
    (hq' : (q'.val = 19 ∧ k = 0) ∨ (q'.val = 91 ∧ k = 1)) :
    evalStack (P ++ [1]) = .jump (popBreakRev k P.reverse).reverse := by
  have hwalk : walkTape 27 [] ((P ++ [1]) ++ List.replicate 18 0) =
      .jumpLeft q' P (List.replicate 18 0) := by
    rw [List.append_assoc, walkTape_of_walkInternal h [] ([1] ++ List.replicate 18 0),
      List.nil_append]
    change walkTape q P (1 :: List.replicate 18 0) = _
    simp [walkTape, htr]
  have hpad : padTo (P ++ [1]) P.length = P := by
    rw [padTo_of_ge (by simp)]; simp
  unfold evalStack
  rw [hwalk]
  rcases hq' with ⟨hqv, rfl⟩ | ⟨hqv, rfl⟩
  · simp [outcomeToInstr, hqv, applyBreak, hpad]
  · simp [outcomeToInstr, hqv, applyBreak, hpad]

theorem evalStack_continue1_of_walkInternal {P : List (Fin 2)} {q q' : Fin 121} {k : ℕ}
    (h : walkInternal 27 P = some q)
    (htr : rh121Trans q 1 = some (0, .left, q'))
    (hq' : (q'.val = 10 ∧ k = 0) ∨ (q'.val = 37 ∧ k = 1) ∨ (q'.val = 97 ∧ k = 2)) :
    evalStack (P ++ [1]) = .jump (popContinueRev k P.reverse).reverse := by
  have hwalk : walkTape 27 [] ((P ++ [1]) ++ List.replicate 18 0) =
      .jumpLeft q' P (List.replicate 18 0) := by
    rw [List.append_assoc, walkTape_of_walkInternal h [] ([1] ++ List.replicate 18 0),
      List.nil_append]
    change walkTape q P (1 :: List.replicate 18 0) = _
    simp [walkTape, htr]
  have hpad : padTo (P ++ [1]) P.length = P := by
    rw [padTo_of_ge (by simp)]; simp
  unfold evalStack
  rw [hwalk]
  rcases hq' with ⟨hqv, rfl⟩ | ⟨hqv, rfl⟩ | ⟨hqv, rfl⟩
  · simp [outcomeToInstr, hqv, applyContinue, hpad]
  · simp [outcomeToInstr, hqv, applyContinue, hpad]
  · simp [outcomeToInstr, hqv, applyContinue, hpad]

@[simp] theorem rhRegNSteps_zero (c : RhRegCfg) : rhRegNSteps 0 c = some c := rfl

@[simp] theorem rhRegNSteps_succ (n : ℕ) (c : RhRegCfg) :
    rhRegNSteps (n + 1) c = (rhRegStep c).bind (rhRegNSteps n) := rfl

theorem rhRegStep_one {c c' : RhRegCfg} (h : rhRegStep c = some c') :
    rhRegNSteps 1 c = some c' := by simp [rhRegNSteps, h]

theorem step_rhRegNSteps {n : ℕ} {c₁ c₂ c₃ : RhRegCfg}
    (h1 : rhRegStep c₁ = some c₂) (h2 : rhRegNSteps n c₂ = some c₃) :
    rhRegNSteps (n + 1) c₁ = some c₃ := by simp [rhRegNSteps, h1, h2]

theorem rhRegNSteps_add (m n : ℕ) (c : RhRegCfg) :
    rhRegNSteps (m + n) c = (rhRegNSteps m c).bind (rhRegNSteps n) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    simp only [Nat.succ_add, rhRegNSteps_succ]
    cases rhRegStep c <;> simp [ih]

theorem rhRegNSteps_bind_eq {m n : ℕ} {c₁ c₂ c₃ : RhRegCfg}
    (h1 : rhRegNSteps m c₁ = some c₂) (h2 : rhRegNSteps n c₂ = some c₃) :
    rhRegNSteps (m + n) c₁ = some c₃ := by
  rw [rhRegNSteps_add, h1, Option.bind_some, h2]

theorem rhRegStep_of_jump {s s' : List (Fin 2)} {regs : List ℕ}
    (h : evalStack s = .jump s') :
    rhRegStep ⟨s, regs⟩ = some ⟨s', regs⟩ := by simp [rhRegStep, h]

theorem rhRegStep_of_inc {s s' : List (Fin 2)} {r : ℕ} {regs : List ℕ}
    (h : evalStack s = .inc r s') :
    rhRegStep ⟨s, regs⟩ = some ⟨s', regs.set r (regs.getD r 0 + 1)⟩ := by
  simp [rhRegStep, h]

theorem rhRegStep_of_decnz_zero {s s_succ s_fail : List (Fin 2)} {r : ℕ} {regs : List ℕ}
    (h : evalStack s = .decnz r s_succ s_fail) (hz : regs.getD r 0 = 0) :
    rhRegStep ⟨s, regs⟩ = some ⟨s_fail, regs⟩ := by
  unfold rhRegStep; rw [h]; dsimp only; rw [hz]; rfl

theorem rhRegStep_of_decnz_succ {s s_succ s_fail : List (Fin 2)} {r v : ℕ} {regs : List ℕ}
    (h : evalStack s = .decnz r s_succ s_fail) (hv : regs.getD r 0 = v + 1) :
    rhRegStep ⟨s, regs⟩ = some ⟨s_succ, regs.set r v⟩ := by
  unfold rhRegStep; rw [h]; dsimp only; rw [hv]; rfl

/-- Universal specification of subroutine node `q` in the 63-node control DAG:
for any prefix `P` with `walkInternal 27 P = some q` and 5-register vector `regs`,
`rhRegNSteps` steps from `⟨trimZeros P, regs⟩` to `⟨retStack P, f regs⟩`. -/
def SubEval (q : Fin 121) (f : List ℕ → List ℕ) : Prop :=
  ∀ (P : List (Fin 2)),
    walkInternal 27 P = some q →
    ∀ (regs : List ℕ), regs.length = 5 →
      ∃ s ≥ 1, rhRegNSteps s ⟨trimZeros P, regs⟩ = some ⟨retStack P, f regs⟩ ∧
        (f regs).length = 5

theorem SubEval.congr {q : Fin 121} {f g : List ℕ → List ℕ}
    (h : SubEval q f) (heq : ∀ regs, regs.length = 5 → f regs = g regs) :
    SubEval q g := by
  intro P hP regs hlen
  obtain ⟨s, hs, hsteps, hflen⟩ := h P hP regs hlen
  rw [heq regs hlen] at hsteps hflen
  exact ⟨s, hs, hsteps, hflen⟩

theorem subEval_seq {q q₀ q₁ : Fin 121} {f₀ f₁ : List ℕ → List ℕ}
    (htr0 : rh121Trans q 0 = some (0, .right, q₀)) (hq₀ : isInternalNode q₀ = true)
    (htr1 : rh121Trans q 1 = some (1, .right, q₁)) (hq₁ : isInternalNode q₁ = true)
    (h0 : SubEval q₀ f₀) (h1 : SubEval q₁ f₁) :
    SubEval q (fun regs => f₁ (f₀ regs)) := by
  intro P hP regs hlen
  have hP0 := walkInternal_snoc hP htr0 hq₀
  have hP1 := walkInternal_snoc hP htr1 hq₁
  obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := h0 (P ++ [0]) hP0 regs hlen
  rw [trimZeros_append_zero, retStack_append_zero] at hsteps₀
  obtain ⟨s₁, hs₁, hsteps₁, hlen₁⟩ := h1 (P ++ [1]) hP1 (f₀ regs) hlen₀
  rw [trimZeros_append_one, retStack_append_one] at hsteps₁
  exact ⟨s₀ + s₁, by omega, rhRegNSteps_bind_eq hsteps₀ hsteps₁, hlen₁⟩

theorem subEval_inc_seq {q q₀ q₁ : Fin 121} {f₁ : List ℕ → List ℕ}
    (htr0 : rh121Trans q 0 = some (0, .right, q₀))
    (hleaf : isLeafState q₀ = true) (hinc : isLeafInc q₀ = true)
    (htr1 : rh121Trans q 1 = some (1, .right, q₁)) (hq₁ : isInternalNode q₁ = true)
    (h1 : SubEval q₁ f₁) :
    SubEval q (fun regs =>
      f₁ (regs.set (leafReg q₀) (regs.getD (leafReg q₀) 0 + 1))) := by
  intro P hP regs hlen
  have hev0 : evalStack (trimZeros P) = .inc (leafReg q₀) (P ++ [1]) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 hleaf]
    simp [hinc]
  let r₀ := regs.set (leafReg q₀) (regs.getD (leafReg q₀) 0 + 1)
  have hstep0 : rhRegStep ⟨trimZeros P, regs⟩ = some ⟨P ++ [1], r₀⟩ :=
    rhRegStep_of_inc hev0
  have hP1 := walkInternal_snoc hP htr1 hq₁
  obtain ⟨s₁, hs₁, hsteps₁, hlen₁⟩ := h1 (P ++ [1]) hP1 r₀ (by simp [r₀, hlen])
  rw [trimZeros_append_one, retStack_append_one] at hsteps₁
  exact ⟨s₁ + 1, by omega, step_rhRegNSteps hstep0 hsteps₁, hlen₁⟩

theorem subEval_seq_inc {q q₀ q₁ : Fin 121} {f₀ : List ℕ → List ℕ}
    (htr0 : rh121Trans q 0 = some (0, .right, q₀)) (hq₀ : isInternalNode q₀ = true)
    (htr1 : rh121Trans q 1 = some (1, .right, q₁))
    (hleaf : isLeafState q₁ = true) (hinc : isLeafInc q₁ = true)
    (h0 : SubEval q₀ f₀) :
    SubEval q (fun regs =>
      let r := f₀ regs
      r.set (leafReg q₁) (r.getD (leafReg q₁) 0 + 1)) := by
  intro P hP regs hlen
  have hP0 := walkInternal_snoc hP htr0 hq₀
  obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := h0 (P ++ [0]) hP0 regs hlen
  rw [trimZeros_append_zero, retStack_append_zero] at hsteps₀
  have hev1 := evalStack_leaf1_inc_of_walkInternal hP htr1 hleaf hinc
  have hstep1 := rhRegStep_of_inc (regs := f₀ regs) hev1
  refine ⟨s₀ + 1, by omega, rhRegNSteps_bind_eq hsteps₀ (rhRegStep_one hstep1), ?_⟩
  simp [hlen₀]

theorem subEval_inc_inc {q q₀ q₁ : Fin 121}
    (htr0 : rh121Trans q 0 = some (0, .right, q₀))
    (hleaf0 : isLeafState q₀ = true) (hinc0 : isLeafInc q₀ = true)
    (htr1 : rh121Trans q 1 = some (1, .right, q₁))
    (hleaf1 : isLeafState q₁ = true) (hinc1 : isLeafInc q₁ = true) :
    SubEval q (fun regs =>
      let r₁ := regs.set (leafReg q₀) (regs.getD (leafReg q₀) 0 + 1)
      r₁.set (leafReg q₁) (r₁.getD (leafReg q₁) 0 + 1)) := by
  intro P hP regs hlen
  have hev0 : evalStack (trimZeros P) = .inc (leafReg q₀) (P ++ [1]) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 hleaf0]
    simp [hinc0]
  have hstep0 := rhRegStep_of_inc (regs := regs) hev0
  have hev1 := evalStack_leaf1_inc_of_walkInternal hP htr1 hleaf1 hinc1
  let r₁ := regs.set (leafReg q₀) (regs.getD (leafReg q₀) 0 + 1)
  have hstep1 := rhRegStep_of_inc (regs := r₁) hev1
  refine ⟨2, by omega, step_rhRegNSteps hstep0 (rhRegStep_one hstep1), ?_⟩
  simp [hlen]

theorem subEval_decnz_inc {q q₀ q₁ : Fin 121}
    (htr0 : rh121Trans q 0 = some (0, .right, q₀))
    (hleaf0 : isLeafState q₀ = true) (hdec0 : isLeafInc q₀ = false)
    (htr1 : rh121Trans q 1 = some (1, .right, q₁))
    (hleaf1 : isLeafState q₁ = true) (hinc1 : isLeafInc q₁ = true) :
    SubEval q (fun regs =>
      if regs.getD (leafReg q₀) 0 = 0 then regs
      else
        let r₁ := regs.set (leafReg q₀) (regs.getD (leafReg q₀) 0 - 1)
        r₁.set (leafReg q₁) (r₁.getD (leafReg q₁) 0 + 1)) := by
  intro P hP regs hlen
  have hev0 : evalStack (trimZeros P) = .decnz (leafReg q₀) (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 hleaf0]
    simp [hdec0]
  rcases hv : regs.getD (leafReg q₀) 0 with _ | v
  · have hstep0 := rhRegStep_of_decnz_zero hev0 hv
    refine ⟨1, le_refl 1, ?_, ?_⟩
    · dsimp only; rw [hv]; simp only [↓reduceIte]; exact rhRegStep_one hstep0
    · dsimp only; rw [hv]; simp [hlen]
  · have hstep0 := rhRegStep_of_decnz_succ hev0 hv
    have hev1 := evalStack_leaf1_inc_of_walkInternal hP htr1 hleaf1 hinc1
    have hstep1 := rhRegStep_of_inc (regs := regs.set (leafReg q₀) v) hev1
    refine ⟨2, by omega, ?_, ?_⟩
    · dsimp only; rw [hv]; simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact step_rhRegNSteps hstep0 (rhRegStep_one hstep1)
    · dsimp only; rw [hv]; simp [hlen]

theorem subEval_decnz_seq {q q₀ q₁ : Fin 121} {f₁ : List ℕ → List ℕ}
    (htr0 : rh121Trans q 0 = some (0, .right, q₀))
    (hleaf0 : isLeafState q₀ = true) (hdec0 : isLeafInc q₀ = false)
    (htr1 : rh121Trans q 1 = some (1, .right, q₁)) (hq₁ : isInternalNode q₁ = true)
    (h1 : SubEval q₁ f₁) :
    SubEval q (fun regs =>
      if regs.getD (leafReg q₀) 0 = 0 then regs
      else f₁ (regs.set (leafReg q₀) (regs.getD (leafReg q₀) 0 - 1))) := by
  intro P hP regs hlen
  have hev0 : evalStack (trimZeros P) = .decnz (leafReg q₀) (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 hleaf0]
    simp [hdec0]
  rcases hv : regs.getD (leafReg q₀) 0 with _ | v
  · have hstep0 := rhRegStep_of_decnz_zero hev0 hv
    refine ⟨1, le_refl 1, ?_, ?_⟩
    · dsimp only; rw [hv]; simp only [↓reduceIte]; exact rhRegStep_one hstep0
    · dsimp only; rw [hv]; simp [hlen]
  · have hstep0 := rhRegStep_of_decnz_succ hev0 hv
    have hP1 := walkInternal_snoc hP htr1 hq₁
    obtain ⟨s₁, hs₁, hsteps₁, hlen₁⟩ := h1 (P ++ [1]) hP1 (regs.set (leafReg q₀) v) (by simp [hlen])
    rw [trimZeros_append_one, retStack_append_one] at hsteps₁
    refine ⟨s₁ + 1, by omega, ?_, ?_⟩
    · dsimp only; rw [hv]; simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact step_rhRegNSteps hstep0 hsteps₁
    · dsimp only; rw [hv]; simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact hlen₁

/-- Generic `while_decnz(r, body)` loop combinator (`continue` via `37 = 6.continue.1`). -/
theorem subEval_while_body {q q_dec q_cont q_body : Fin 121}
    (r : ℕ)
    (htr0 : rh121Trans q 0 = some (0, .right, q_dec))
    (hleaf : isLeafState q_dec = true) (hdec : isLeafInc q_dec = false)
    (hlr : leafReg q_dec = r)
    (htr1 : rh121Trans q 1 = some (1, .right, q_cont))
    (hcont : isInternalNode q_cont = true)
    (htr10 : rh121Trans q_cont 0 = some (0, .right, q_body))
    (hbody : isInternalNode q_body = true)
    (htr11 : rh121Trans q_cont 1 = some (0, .left, 37))
    {body : List ℕ → List ℕ} (hSub : SubEval q_body body)
    (g : List ℕ → List ℕ)
    (hg_len : ∀ (regs : List ℕ), regs.length = 5 → (g regs).length = 5)
    (hg_zero : ∀ (regs : List ℕ), regs.length = 5 → regs.getD r 0 = 0 → g regs = regs)
    (hg_step : ∀ (regs : List ℕ) (v : ℕ), regs.length = 5 → regs.getD r 0 = v + 1 →
      g (body (regs.set r v)) = g regs)
    (hmeasure : ∀ (regs : List ℕ) (v : ℕ), regs.length = 5 → regs.getD r 0 = v + 1 →
      (body (regs.set r v)).getD r 0 ≤ v) :
    SubEval q g := by
  intro P hP
  have hP1 := walkInternal_snoc hP htr1 hcont
  have hP10 := walkInternal_snoc hP1 htr10 hbody
  have hev0 : evalStack (trimZeros P) = .decnz r (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 hleaf]
    simp [hdec, hlr]
  have hev11 : evalStack (P ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1]) (k := 1) hP1 htr11
      (Or.inr (Or.inl ⟨rfl, rfl⟩))
    simpa [popContinueRev, popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (k : ℕ) (regs : List ℕ), regs.length = 5 → regs.getD r 0 = k →
      ∃ s ≥ 1, rhRegNSteps s ⟨trimZeros P, regs⟩ = some ⟨retStack P, g regs⟩ ∧
        (g regs).length = 5 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro regs hlen hk
      rcases k with _ | v
      · have hstep := rhRegStep_of_decnz_zero hev0 hk
        rw [hg_zero regs hlen hk]
        exact ⟨1, le_refl 1, rhRegStep_one hstep, hlen⟩
      · have hstep1 := rhRegStep_of_decnz_succ hev0 hk
        obtain ⟨sb, hsb, hsteps_b, hlen_b⟩ :=
          hSub (P ++ [1] ++ [0]) hP10 (regs.set r v) (by simp [hlen])
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_b
        have hstep3 := rhRegStep_of_jump (regs := body (regs.set r v)) hev11
        have hlt : (body (regs.set r v)).getD r 0 < v + 1 :=
          Nat.lt_succ_of_le (hmeasure regs v hlen hk)
        obtain ⟨s, hs, hsteps_s, _⟩ := ih _ hlt (body (regs.set r v)) hlen_b rfl
        rw [hg_step regs v hlen hk] at hsteps_s
        have hc1 := step_rhRegNSteps hstep1 hsteps_b
        have hc2 := rhRegNSteps_bind_eq hc1 (step_rhRegNSteps hstep3 hsteps_s)
        exact ⟨(sb + 1) + (s + 1), by omega, hc2, hg_len regs hlen⟩
  intro regs hlen
  exact hloop (regs.getD r 0) regs hlen rfl

/-- Generic two-stage `while_decnz(r, body₀; body₁)` loop combinator (`continue` via `97`). -/
theorem subEval_while_body2 {q q_dec q_c1 q_c2 : Fin 121}
    (r : ℕ)
    (htr0 : rh121Trans q 0 = some (0, .right, q_dec))
    (hleaf : isLeafState q_dec = true) (hdec : isLeafInc q_dec = false)
    (hlr : leafReg q_dec = r)
    (htr1 : rh121Trans q 1 = some (1, .right, q_c1))
    (hc1 : isInternalNode q_c1 = true)
    (htr11 : rh121Trans q_c1 1 = some (1, .right, q_c2))
    (hc2 : isInternalNode q_c2 = true)
    {body : List ℕ → List ℕ}
    (hBody : ∀ (P : List (Fin 2)), walkInternal 27 P = some q_c1 →
      ∀ (regs : List ℕ), regs.length = 5 →
        ∃ sb ≥ 1, rhRegNSteps sb ⟨trimZeros P, regs⟩ =
          some ⟨P ++ [1] ++ [1], body regs⟩ ∧ (body regs).length = 5)
    (htr_cont : rh121Trans q_c2 1 = some (0, .left, 97))
    (g : List ℕ → List ℕ)
    (hg_len : ∀ (regs : List ℕ), regs.length = 5 → (g regs).length = 5)
    (hg_zero : ∀ (regs : List ℕ), regs.length = 5 → regs.getD r 0 = 0 → g regs = regs)
    (hg_step : ∀ (regs : List ℕ) (v : ℕ), regs.length = 5 → regs.getD r 0 = v + 1 →
      g (body (regs.set r v)) = g regs)
    (hmeasure : ∀ (regs : List ℕ) (v : ℕ), regs.length = 5 → regs.getD r 0 = v + 1 →
      (body (regs.set r v)).getD r 0 ≤ v) :
    SubEval q g := by
  intro P hP
  have hP1 := walkInternal_snoc hP htr1 hc1
  have hP11 := walkInternal_snoc hP1 htr11 hc2
  have hev0 : evalStack (trimZeros P) = .decnz r (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 hleaf]
    simp [hdec, hlr]
  have hev_cont : evalStack (P ++ [1] ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1] ++ [1]) (k := 2) hP11 htr_cont
      (Or.inr (Or.inr ⟨rfl, rfl⟩))
    simpa [popContinueRev, popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (k : ℕ) (regs : List ℕ), regs.length = 5 → regs.getD r 0 = k →
      ∃ s ≥ 1, rhRegNSteps s ⟨trimZeros P, regs⟩ = some ⟨retStack P, g regs⟩ ∧
        (g regs).length = 5 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro regs hlen hk
      rcases k with _ | v
      · have hstep := rhRegStep_of_decnz_zero hev0 hk
        rw [hg_zero regs hlen hk]
        exact ⟨1, le_refl 1, rhRegStep_one hstep, hlen⟩
      · have hstep1 := rhRegStep_of_decnz_succ hev0 hk
        obtain ⟨sb, hsb, hsteps_b, hlen_b⟩ := hBody (P ++ [1]) hP1 (regs.set r v) (by simp [hlen])
        rw [trimZeros_append_one] at hsteps_b
        have hstep_c := rhRegStep_of_jump (regs := body (regs.set r v)) hev_cont
        have hlt : (body (regs.set r v)).getD r 0 < v + 1 :=
          Nat.lt_succ_of_le (hmeasure regs v hlen hk)
        obtain ⟨s, hs, hsteps_s, _⟩ := ih _ hlt (body (regs.set r v)) hlen_b rfl
        rw [hg_step regs v hlen hk] at hsteps_s
        have hc_a := step_rhRegNSteps hstep1 hsteps_b
        have hc_b := rhRegNSteps_bind_eq hc_a (step_rhRegNSteps hstep_c hsteps_s)
        exact ⟨(sb + 1) + (s + 1), by omega, hc_b, hg_len regs hlen⟩
  intro regs hlen
  exact hloop (regs.getD r 0) regs hlen rfl

/-- Generic `while_decnz(r₁, r₂.inc)` move combinator (`continue` via `37 = 6.continue.1`). -/
theorem subEval_move {q q_dec q₁ q_inc : Fin 121} (r₁ r₂ : ℕ)
    (hr₁ : r₁ < 5) (hr₂ : r₂ < 5) (hne : r₁ ≠ r₂)
    (htr0 : rh121Trans q 0 = some (0, .right, q_dec))
    (hleaf_dec : isLeafState q_dec = true) (hdec : isLeafInc q_dec = false)
    (hlr1 : leafReg q_dec = r₁)
    (htr1 : rh121Trans q 1 = some (1, .right, q₁)) (hq₁ : isInternalNode q₁ = true)
    (htr10 : rh121Trans q₁ 0 = some (0, .right, q_inc))
    (hleaf_inc : isLeafState q_inc = true) (hinc : isLeafInc q_inc = true)
    (hlr2 : leafReg q_inc = r₂)
    (htr11 : rh121Trans q₁ 1 = some (0, .left, 37)) :
    SubEval q (fun regs => (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + regs.getD r₁ 0)) := by
  intro P hP
  have hP1 := walkInternal_snoc hP htr1 hq₁
  have hev0 : evalStack (trimZeros P) = .decnz r₁ (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 hleaf_dec]
    simp [hdec, hlr1]
  have hev10 : evalStack (P ++ [1]) = .inc r₂ (P ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hP1 htr10 hleaf_inc
    simpa [hinc, hlr2] using h
  have hev11 : evalStack (P ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1]) (k := 1) hP1 htr11
      (Or.inr (Or.inl ⟨rfl, rfl⟩))
    simpa [popContinueRev, popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (v : ℕ) (regs : List ℕ), regs.length = 5 → regs.getD r₁ 0 = v →
      ∃ s ≥ 1, rhRegNSteps s ⟨trimZeros P, regs⟩ =
        some ⟨retStack P, (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)⟩ ∧
        ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)).length = 5 := by
    have hr₁' : r₁ = 0 ∨ r₁ = 1 ∨ r₁ = 2 ∨ r₁ = 3 ∨ r₁ = 4 := by omega
    have hr₂' : r₂ = 0 ∨ r₂ = 1 ∨ r₂ = 2 ∨ r₂ = 3 ∨ r₂ = 4 := by omega
    intro v
    induction v with
    | zero =>
      intro regs hlen hv
      rcases regs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | _⟩⟩⟩⟩⟩ <;>
        try simp at hlen
      have hstep := rhRegStep_of_decnz_zero hev0 hv
      rcases hr₁' with rfl | rfl | rfl | rfl | rfl <;>
        rcases hr₂' with rfl | rfl | rfl | rfl | rfl <;>
        simp at hne hv ⊢ <;>
        exact ⟨1, le_refl 1, by simpa [hv] using rhRegStep_one hstep⟩
    | succ v ih =>
      intro regs hlen hv
      rcases regs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | _⟩⟩⟩⟩⟩ <;>
        try simp at hlen
      let regs₁ := ([a0, a1, a2, a3, a4].set r₁ v).set r₂ ([a0, a1, a2, a3, a4].getD r₂ 0 + 1)
      have hstep1 := rhRegStep_of_decnz_succ hev0 hv
      have hstep2 : rhRegStep ⟨P ++ [1], [a0, a1, a2, a3, a4].set r₁ v⟩ =
          some ⟨P ++ [1] ++ [1], regs₁⟩ := by
        rw [rhRegStep_of_inc hev10]
        congr 2
        rcases hr₁' with rfl | rfl | rfl | rfl | rfl <;>
          rcases hr₂' with rfl | rfl | rfl | rfl | rfl <;>
          simp at hne <;> rfl
      have hstep3 := rhRegStep_of_jump (regs := regs₁) hev11
      have hv₁ : regs₁.getD r₁ 0 = v := by
        rcases hr₁' with rfl | rfl | rfl | rfl | rfl <;>
          rcases hr₂' with rfl | rfl | rfl | rfl | rfl <;>
          simp [regs₁] at hne ⊢
      obtain ⟨s, hs, hsteps, _⟩ := ih regs₁ (by simp [regs₁]) hv₁
      have heq : (regs₁.set r₁ 0).set r₂ (regs₁.getD r₂ 0 + v) =
          ([a0, a1, a2, a3, a4].set r₁ 0).set r₂
            ([a0, a1, a2, a3, a4].getD r₂ 0 + (v + 1)) := by
        rcases hr₁' with rfl | rfl | rfl | rfl | rfl <;>
          rcases hr₂' with rfl | rfl | rfl | rfl | rfl <;>
          simp [regs₁] at hne ⊢ <;> omega
      rw [heq] at hsteps
      exact ⟨s + 3, by omega,
        step_rhRegNSteps hstep1 (step_rhRegNSteps hstep2 (step_rhRegNSteps hstep3 hsteps)),
        by simp⟩
  intro regs hlen
  exact hloop (regs.getD r₁ 0) regs hlen rfl

/-! ## Section 6: Verification of All Subroutines & Main Loop of `riemann121` -/

/-- `move(m, f)` (State `29`): `(m, j, x, f, v) ↦ (0, j, x, f + m, v)`. -/
theorem subEval_move_m_f :
    SubEval 29 (fun regs => [0, regs.getD 1 0, regs.getD 2 0, regs.getD 3 0 + regs.getD 0 0,
      regs.getD 4 0]) := by
  refine (subEval_move 0 3 (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl).congr ?_
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> simp at hlen ⊢

/-- `move(j, v)` (State `65`): `(m, j, x, f, v) ↦ (m, 0, x, f, v + j)`. -/
theorem subEval_move_j_v :
    SubEval 65 (fun regs => [regs.getD 0 0, 0, regs.getD 2 0, regs.getD 3 0,
      regs.getD 4 0 + regs.getD 1 0]) := by
  refine (subEval_move 1 4 (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl).congr ?_
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> simp at hlen ⊢

/-- `move(x, m)` (State `81`): `(m, j, x, f, v) ↦ (m + x, j, 0, f, v)`. -/
theorem subEval_move_x_m :
    SubEval 81 (fun regs => [regs.getD 0 0 + regs.getD 2 0, regs.getD 1 0, 0, regs.getD 3 0,
      regs.getD 4 0]) := by
  refine (subEval_move 2 0 (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl).congr ?_
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> simp at hlen ⊢

/-- `move(v, j)` (State `60`): `(m, j, x, f, v) ↦ (m, j + v, x, f, 0)`. -/
theorem subEval_move_v_j :
    SubEval 60 (fun regs => [regs.getD 0 0, regs.getD 1 0 + regs.getD 4 0, regs.getD 2 0,
      regs.getD 3 0, 0]) := by
  refine (subEval_move 4 1 (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl).congr ?_
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> simp at hlen ⊢

/-- `move(v, f)` (State `116`): `(m, j, x, f, v) ↦ (m, j, x, f + v, 0)`. -/
theorem subEval_move_v_f :
    SubEval 116 (fun regs => [regs.getD 0 0, regs.getD 1 0, regs.getD 2 0,
      regs.getD 3 0 + regs.getD 4 0, 0]) := by
  refine (subEval_move 4 3 (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl).congr ?_
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> simp at hlen ⊢

/-- `seed_deficit` (State `40`): `(m, j, x, f, v) ↦ (m, 0, x, f + j, v + j)`. -/
theorem subEval_seed_deficit :
    SubEval 40 (fun regs => [regs.getD 0 0, 0, regs.getD 2 0,
      regs.getD 3 0 + regs.getD 1 0, regs.getD 4 0 + regs.getD 1 0]) := by
  have h58 := subEval_inc_inc (q := 58) (q₀ := 70) (q₁ := 36) rfl rfl rfl rfl rfl rfl
  refine subEval_while_body 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl h58
    (fun regs => [regs.getD 0 0, 0, regs.getD 2 0,
      regs.getD 3 0 + regs.getD 1 0, regs.getD 4 0 + regs.getD 1 0])
    (fun _ _ => by simp)
    (fun regs hlen hj => by
      obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hj
      subst hj
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero])
    (fun regs k hlen hj => by
      obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
      rw [show leafReg 70 = 4 from rfl, show leafReg 36 = 3 from rfl]
      simp only [List.set_cons_zero, List.set_cons_succ,
        List.getD_cons_zero, List.getD_cons_succ] at hj ⊢
      subst hj
      simp only [Nat.add_assoc, Nat.add_comm 1 k])
    (fun regs k hlen hj => by
      obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
      rw [show leafReg 70 = 4 from rfl, show leafReg 36 = 3 from rfl]
      simp only [List.set_cons_zero, List.set_cons_succ,
        List.getD_cons_zero, List.getD_cons_succ] at hj ⊢
      omega)

/-- `dec_f` (State `96`): saturating decrement of register `f` (`regs[3]`). -/
theorem subEval_dec_f :
    SubEval 96 (fun regs => [regs.getD 0 0, regs.getD 1 0, regs.getD 2 0,
      regs.getD 3 0 - 1, regs.getD 4 0]) := by
  intro P hP regs hlen
  have hev0 : evalStack (trimZeros P) = .decnz 3 (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP (q' := 46) rfl rfl]
    simp [isLeafInc, leafReg]
  have hev1 : evalStack (P ++ [1]) = .jump (retStack P) := by
    have h := evalStack_break1_of_walkInternal (q' := 19) (k := 0) hP rfl (Or.inl ⟨rfl, rfl⟩)
    simpa [retStack] using h
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> try simp at hlen
  rcases f with _ | f'
  · have hstep := rhRegStep_of_decnz_zero (regs := [m, j, x, 0, v]) hev0 rfl
    exact ⟨1, le_refl 1, rhRegStep_one hstep, rfl⟩
  · have hstep0 := rhRegStep_of_decnz_succ (regs := [m, j, x, f' + 1, v]) hev0 rfl
    have hstep1 := rhRegStep_of_jump (regs := [m, j, x, f', v]) hev1
    exact ⟨2, by omega, step_rhRegNSteps hstep0 (rhRegStep_one hstep1), rfl⟩

/-- `fold` inner loop (State `109`): `(m, j, x, f, v) ↦ (m, 0, x + j, f, v + j)`. -/
theorem subEval_fold_loop :
    SubEval 109 (fun regs => [regs.getD 0 0, 0, regs.getD 2 0 + regs.getD 1 0,
      regs.getD 3 0, regs.getD 4 0 + regs.getD 1 0]) := by
  refine subEval_while_body2 1 rfl rfl rfl rfl rfl rfl rfl rfl
    (body := fun regs =>
      let r1 := regs.set 4 (regs.getD 4 0 + 1)
      r1.set 2 (r1.getD 2 0 + 1))
    (fun P hP regs hlen => by
      have hP1 := walkInternal_snoc hP (b := 1) (q_end := 89) rfl rfl
      have hev0 : evalStack (trimZeros P) = .inc 4 (P ++ [1]) := by
        rw [evalStack_trimZeros_of_walkInternal hP,
          evalStack_leaf0_of_walkInternal hP (q' := 70) rfl rfl]
        simp [isLeafInc, leafReg]
      have hev1 : evalStack (P ++ [1]) = .inc 2 (P ++ [1] ++ [1]) := by
        rw [evalStack_leaf0_of_walkInternal hP1 (q' := 99) rfl rfl]
        simp [isLeafInc, leafReg]
      let r1 := regs.set 4 (regs.getD 4 0 + 1)
      have s0 := rhRegStep_of_inc (regs := regs) hev0
      have s1 := rhRegStep_of_inc (regs := r1) hev1
      exact ⟨2, by omega, step_rhRegNSteps s0 (rhRegStep_one s1), by simp [hlen]⟩)
    rfl
    (fun regs => [regs.getD 0 0, 0, regs.getD 2 0 + regs.getD 1 0,
      regs.getD 3 0, regs.getD 4 0 + regs.getD 1 0])
    (fun _ _ => by simp)
    (fun regs hlen hj => by
      obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hj
      subst hj
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero])
    (fun regs k hlen hj => by
      obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
      simp only [List.set_cons_zero, List.set_cons_succ,
        List.getD_cons_zero, List.getD_cons_succ] at hj ⊢
      subst hj
      congr 1; congr 1
      · congr 1
        · omega
        · congr 1; congr 1; omega)
    (fun regs k hlen hj => by
      obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
      simp only [List.set_cons_zero, List.set_cons_succ,
        List.getD_cons_zero, List.getD_cons_succ] at hj ⊢
      omega)

/-- `fold` (State `102`): `(m, j, x, f, v) ↦ (m, j + v, x + j, f, 0)`. -/
theorem subEval_fold :
    SubEval 102 (fun regs => [regs.getD 0 0, regs.getD 1 0 + regs.getD 4 0,
      regs.getD 2 0 + regs.getD 1 0, regs.getD 3 0, 0]) := by
  refine (subEval_seq (q := 102) (q₀ := 109) (q₁ := 60) rfl rfl rfl rfl
    subEval_fold_loop subEval_move_v_j).congr ?_
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
    (simp at hlen ⊢; try omega)

/-- Post-tested loop inside `transform` (State `95`):
`(m, j, x, f, v) ↦ (0, j + v, x + m * (j + v + 1) + j, f, 0)`. -/
theorem subEval_transform_loop :
    SubEval 95 (fun regs =>
      let J := regs.getD 1 0 + regs.getD 4 0 + 1
      [0, regs.getD 1 0 + regs.getD 4 0,
        regs.getD 2 0 + regs.getD 0 0 * J + regs.getD 1 0, regs.getD 3 0, 0]) := by
  intro P hP
  have hP0 := walkInternal_snoc hP (b := 0) (q_end := 102) rfl rfl
  have hP1 := walkInternal_snoc hP (b := 1) (q_end := 103) rfl rfl
  have hP11 := walkInternal_snoc hP1 (b := 1) (q_end := 89) rfl rfl
  have hev_m : evalStack (P ++ [1]) = .decnz 0 (P ++ [1] ++ [1]) (retStack P) := by
    rw [evalStack_leaf0_of_walkInternal hP1 (q' := 31) rfl rfl]
    simp [isLeafInc, leafReg, retStack_append_one]
  have hev_x : evalStack (P ++ [1] ++ [1]) = .inc 2 (P ++ [1] ++ [1] ++ [1]) := by
    rw [evalStack_leaf0_of_walkInternal hP11 (q' := 99) rfl rfl]
    simp [isLeafInc, leafReg]
  have hev_cont : evalStack (P ++ [1] ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1] ++ [1]) (k := 2) hP11 rfl
      (Or.inr (Or.inr ⟨rfl, rfl⟩))
    simpa [popContinueRev, popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (k : ℕ) (j x f v : ℕ),
      ∃ s ≥ 1, rhRegNSteps s ⟨trimZeros P, [k, j, x, f, v]⟩ =
        some ⟨retStack P, [0, j + v, x + k * (j + v + 1) + j, f, 0]⟩ := by
    intro k
    induction k with
    | zero =>
      intro j x f v
      obtain ⟨sf, hsf, hsteps_f, _⟩ := subEval_fold (P ++ [0]) hP0 [0, j, x, f, v] rfl
      rw [trimZeros_append_zero, retStack_append_zero] at hsteps_f
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hsteps_f
      have hs_m := rhRegStep_of_decnz_zero (regs := [0, j + v, x + j, f, 0]) hev_m rfl
      simp only [Nat.zero_mul, Nat.add_zero]
      exact ⟨sf + 1, by omega, rhRegNSteps_bind_eq hsteps_f (rhRegStep_one hs_m)⟩
    | succ k ih =>
      intro j x f v
      obtain ⟨sf, hsf, hsteps_f, _⟩ := subEval_fold (P ++ [0]) hP0 [k + 1, j, x, f, v] rfl
      rw [trimZeros_append_zero, retStack_append_zero] at hsteps_f
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hsteps_f
      have hs_m := rhRegStep_of_decnz_succ (regs := [k + 1, j + v, x + j, f, 0]) hev_m rfl
      have hs_x := rhRegStep_of_inc (regs := [k, j + v, x + j, f, 0]) hev_x
      have hs_c := rhRegStep_of_jump (regs := [k, j + v, x + j + 1, f, 0]) hev_cont
      obtain ⟨sk, hsk, hsteps_k⟩ := ih (j + v) (x + j + 1) f 0
      have h1 : j + v + 0 = j + v := by omega
      have h2 : x + j + 1 + k * (j + v + 0 + 1) + (j + v) =
          x + (k + 1) * (j + v + 1) + j := by
        rw [h1, Nat.succ_mul]; omega
      rw [h1] at h2 hsteps_k
      rw [h2] at hsteps_k
      have tail := step_rhRegNSteps hs_m (step_rhRegNSteps hs_x (step_rhRegNSteps hs_c hsteps_k))
      exact ⟨sf + (sk + 3), by omega, rhRegNSteps_bind_eq hsteps_f tail⟩
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> try simp at hlen
  obtain ⟨s, hs, hsteps⟩ := hloop m j x f v
  exact ⟨s, hs, hsteps, rfl⟩

/-- `transform` (State `84`): `(m, j, x, f, v) ↦ (0, j + v, (m + x)*(j + v + 1) + j, f, 0)`. -/
theorem subEval_transform :
    SubEval 84 (fun regs =>
      let J := regs.getD 1 0 + regs.getD 4 0 + 1
      [0, regs.getD 1 0 + regs.getD 4 0,
        (regs.getD 0 0 + regs.getD 2 0) * J + regs.getD 1 0, regs.getD 3 0, 0]) := by
  refine (subEval_seq (q := 84) (q₀ := 81) (q₁ := 95) rfl rfl rfl rfl
    subEval_move_x_m subEval_transform_loop).congr ?_
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> simp at hlen ⊢

/-- `twice` (State `68`): sequential composition of two `transform` calls. -/
theorem subEval_twice :
    SubEval 68 (fun regs =>
      let J := regs.getD 1 0 + regs.getD 4 0 + 1
      let x₁ := (regs.getD 0 0 + regs.getD 2 0) * J + regs.getD 1 0
      [0, J - 1, x₁ * J + (J - 1), regs.getD 3 0, 0]) := by
  refine (subEval_seq (q := 68) (q₀ := 84) (q₁ := 84) rfl rfl rfl rfl
    subEval_transform subEval_transform).congr ?_
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> simp at hlen ⊢

/-- `tick` step of `divide` (State `101`): advances Euclidean remainder/quotient by 1 unit. -/
theorem subEval_tick :
    SubEval 101 (fun regs =>
      if regs.getD 4 0 = 0 then
        [regs.getD 0 0, 0, regs.getD 2 0 + 1, regs.getD 3 0, regs.getD 1 0]
      else
        [regs.getD 0 0, regs.getD 1 0 + 1, regs.getD 2 0, regs.getD 3 0, regs.getD 4 0 - 1]) := by
  have h108 : SubEval 108 (fun regs => [regs.getD 0 0, 0, regs.getD 2 0 + 1,
      regs.getD 3 0, regs.getD 4 0 + regs.getD 1 0]) := by
    refine (subEval_seq_inc (q := 108) (q₀ := 65) (q₁ := 99) rfl rfl rfl rfl rfl
      subEval_move_j_v).congr ?_
    intro regs hlen
    rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
      simp [leafReg] at hlen ⊢
  intro P hP regs hlen
  have hP0 := walkInternal_snoc hP (b := 0) (q_end := 107) rfl rfl
  have hP1 := walkInternal_snoc hP (b := 1) (q_end := 108) rfl rfl
  have hP01 := walkInternal_snoc hP0 (b := 1) (q_end := 112) rfl rfl
  have hev0 : evalStack (trimZeros P) = .decnz 4 (P ++ [0] ++ [1]) (P ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hP0 (q' := 73) rfl rfl
    have htz := evalStack_trimZeros_of_walkInternal hP0
    rw [trimZeros_append_zero] at htz
    rw [← htz, retStack_append_zero] at h
    simpa [isLeafInc, leafReg] using h
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> try simp at hlen
  rcases v with _ | v'
  · have hs0 := rhRegStep_of_decnz_zero (regs := [m, j, x, f, 0]) hev0 rfl
    obtain ⟨s1, hs1, hsteps1, _⟩ := h108 (P ++ [1]) hP1 [m, j, x, f, 0] rfl
    rw [trimZeros_append_one, retStack_append_one] at hsteps1
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add, ↓reduceIte] at hsteps1 ⊢
    exact ⟨s1 + 1, by omega, step_rhRegNSteps hs0 hsteps1, rfl⟩
  · have hs0 := rhRegStep_of_decnz_succ (regs := [m, j, x, f, v' + 1]) hev0 rfl
    have hev_inc : evalStack (P ++ [0] ++ [1]) = .inc 1 (P ++ [0] ++ [1] ++ [1]) := by
      rw [evalStack_leaf0_of_walkInternal hP01 (q' := 44) rfl rfl]
      simp [isLeafInc, leafReg]
    have hev_brk : evalStack (P ++ [0] ++ [1] ++ [1]) = .jump (retStack P) := by
      have h := evalStack_break1_of_walkInternal (P := P ++ [0] ++ [1]) (q' := 91) (k := 1)
        hP01 rfl (Or.inr ⟨rfl, rfl⟩)
      simpa [retStack, popBreakRev] using h
    have hs1 := rhRegStep_of_inc (regs := [m, j, x, f, v']) hev_inc
    have hs2 := rhRegStep_of_jump (regs := [m, j + 1, x, f, v']) hev_brk
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.succ_ne_zero, ↓reduceIte,
      Nat.add_sub_cancel]
    exact ⟨3, by omega, step_rhRegNSteps hs0 (step_rhRegNSteps hs1 (rhRegStep_one hs2)), rfl⟩

/-- `while_decnz(m, tick)` loop inside `divide` (State `82`). -/
theorem subEval_divide_loop :
    SubEval 82 (fun regs =>
      let J := regs.getD 1 0 + regs.getD 4 0 + 1
      let N := regs.getD 2 0 * J + regs.getD 1 0 + regs.getD 0 0
      [0, N % J, N / J, regs.getD 3 0, J - 1 - N % J]) := by
  refine subEval_while_body 0 rfl rfl rfl rfl rfl rfl rfl rfl rfl subEval_tick
    (fun regs =>
      let J := regs.getD 1 0 + regs.getD 4 0 + 1
      let N := regs.getD 2 0 * J + regs.getD 1 0 + regs.getD 0 0
      [0, N % J, N / J, regs.getD 3 0, J - 1 - N % J])
    (fun _ _ => by simp)
    (fun regs hlen hm => by
      rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
        try simp at hlen hm
      subst hm
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
      have hj_lt : j < j + v + 1 := by omega
      have hdiv : (x * (j + v + 1) + j) / (j + v + 1) = x := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj_lt, Nat.add_zero]
      have hmod : (x * (j + v + 1) + j) % (j + v + 1) = j := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj_lt]
      simp [hdiv, hmod])
    (fun regs k hlen hm => by
      rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
        try simp at hlen hm
      subst hm
      rcases v with _ | v'
      · simp only [List.set, List.getD_cons_zero, List.getD_cons_succ, ↓reduceIte,
          Nat.zero_add, Nat.add_zero]
        have hN : (x + 1) * (j + 1) + k = x * (j + 1) + j + (k + 1) := by
          rw [Nat.succ_mul]; omega
        rw [hN]
      · simp only [List.set, List.getD_cons_zero, List.getD_cons_succ, Nat.succ_ne_zero,
          ↓reduceIte, Nat.add_sub_cancel]
        have hJ : j + 1 + v' + 1 = j + (v' + 1) + 1 := by omega
        have hJ2 : j + 1 + v' = j + (v' + 1) := by omega
        have hN : x * (j + (v' + 1) + 1) + (j + 1) + k =
            x * (j + (v' + 1) + 1) + j + (k + 1) := by omega
        rw [hJ, hJ2, hN])
    (fun regs k hlen hm => by
      rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
        try simp at hlen hm
      subst hm
      rcases v with _ | v' <;> simp)

/-- `divide` (State `54`): divides $B = m + x$ by $J = j + v + 1$, returning
`[0, B % J, B / J, regs.getD 3 0, J - 1 - B % J]`. -/
theorem subEval_divide :
    SubEval 54 (fun regs =>
      let J := regs.getD 1 0 + regs.getD 4 0 + 1
      let B := regs.getD 0 0 + regs.getD 2 0
      [0, B % J, B / J, regs.getD 3 0, J - 1 - B % J]) := by
  have h66 := subEval_seq (q := 66) (q₀ := 81) (q₁ := 82) rfl rfl rfl rfl
    subEval_move_x_m subEval_divide_loop
  refine (subEval_seq (q := 54) (q₀ := 65) (q₁ := 66) rfl rfl rfl rfl
    subEval_move_j_v h66).congr ?_
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> try simp at hlen
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add, Nat.add_zero]
  have h1 : m + x = x + m := Nat.add_comm m x
  have h2 : j + v + 1 - 1 = j + v := by omega
  have h3 : v + j = j + v := by omega
  simp [h1, h2, h3]

/-- `product_step` (State `38`): advances `[0, K - 2, A_{K-1} - 1, f, 0]` ($K \ge 2$) to
`[0, K - 1, A_K - 1, f, 0]`. -/
theorem subEval_product_step :
    SubEval 38 (fun regs =>
      let J := regs.getD 1 0 + 1 + regs.getD 4 0 + 1
      let B := regs.getD 0 0 + regs.getD 2 0
      let r := B % J
      let q := B / J
      let v := J - 1 - r
      let x_mid := if v = 0 then q else q * J + r
      let x₁ := x_mid * J + (J - 1)
      [0, J - 1, x₁ * J + (J - 1), regs.getD 3 0, 0]) := by
  have h83 : SubEval 83 (fun regs =>
      let J := regs.getD 1 0 + (regs.getD 4 0 + 1) + 1
      [0, regs.getD 1 0 + (regs.getD 4 0 + 1),
        (regs.getD 0 0 + regs.getD 2 0) * J + regs.getD 1 0, regs.getD 3 0, 0]) := by
    refine (subEval_inc_seq (q := 83) (q₀ := 70) (q₁ := 84) rfl rfl rfl rfl rfl
      subEval_transform).congr ?_
    intro regs hlen
    rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
      simp [leafReg] at hlen ⊢
  have h67 : SubEval 67 (fun regs =>
      if regs.getD 4 0 = 0 then regs
      else
        let J := regs.getD 1 0 + regs.getD 4 0 + 1
        [0, regs.getD 1 0 + regs.getD 4 0,
          (regs.getD 0 0 + regs.getD 2 0) * J + regs.getD 1 0, regs.getD 3 0, 0]) := by
    refine (subEval_decnz_seq (q := 67) (q₀ := 73) (q₁ := 83) rfl rfl rfl rfl rfl h83).congr ?_
    intro regs hlen
    rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
      try simp at hlen
    rcases v with _ | v' <;> simp [leafReg]
  have h55 := subEval_seq (q := 55) (q₀ := 67) (q₁ := 68) rfl rfl rfl rfl h67 subEval_twice
  have h45 := subEval_seq (q := 45) (q₀ := 54) (q₁ := 55) rfl rfl rfl rfl subEval_divide h55
  refine (subEval_inc_seq (q := 38) (q₀ := 44) (q₁ := 45) rfl rfl rfl rfl rfl h45).congr ?_
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> try simp at hlen
  simp only [leafReg, List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add]
  have hr_lt : (m + x) % (j + 1 + v + 1) < j + 1 + v + 1 := Nat.mod_lt (m + x) (by omega)
  by_cases hv0 : j + 1 + v - (m + x) % (j + 1 + v + 1) = 0
  · have hr_eq : (m + x) % (j + 1 + v + 1) = j + 1 + v := by omega
    simp [hr_eq]
  · have hjv : (m + x) % (j + 1 + v + 1) + (j + 1 + v - (m + x) % (j + 1 + v + 1)) =
        j + 1 + v := by omega
    simp [hv0, hjv]

theorem product_step_shuniaProd {K : ℕ} (hK : 2 ≤ K) (f : ℕ) :
    let regs := [0, K - 2, shuniaProd (K - 1) - 1, f, 0]
    let J := regs.getD 1 0 + 1 + regs.getD 4 0 + 1
    let B := regs.getD 0 0 + regs.getD 2 0
    let r := B % J
    let q := B / J
    let v := J - 1 - r
    let x_mid := if v = 0 then q else q * J + r
    let x₁ := x_mid * J + (J - 1)
    [0, J - 1, x₁ * J + (J - 1), regs.getD 3 0, 0] =
      [0, K - 1, shuniaProd K - 1, f, 0] := by
  dsimp only
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add, Nat.add_zero]
  have hJ : K - 2 + 1 + 1 = K := by omega
  simp only [hJ]
  rw [shuniaProd_step hK]
  set A := shuniaProd (K - 1)
  have hA_pos : 1 ≤ A := shuniaProd_pos (K - 1)
  set B := A - 1
  have hBA : B + 1 = A := by omega
  have hdiv_mod : K * (B / K) + B % K = B := Nat.div_add_mod B K
  have hr_lt : B % K < K := Nat.mod_lt B (by omega)
  have hK1 : (K - 1) + 1 = K := by omega
  by_cases hdvd : K ∣ A
  · rw [ite_eq_left hdvd]
    obtain ⟨m, hm⟩ := hdvd
    rcases m with _ | m'
    · simp at hm; omega
    · have hm' : B + 1 = m' * K + K := by rw [hBA, hm, Nat.mul_succ, Nat.mul_comm]
      have hB_eq : B = (K - 1) + m' * K := by omega
      have hdiv : B / K = m' := by
        rw [hB_eq, Nat.add_mul_div_right _ _ (by omega),
          Nat.div_eq_of_lt (by omega : K - 1 < K), Nat.zero_add]
      have hK_mul_div : B / K * K + (K - 1) = B := by rw [hdiv, hB_eq, Nat.add_comm]
      have hr_eq : B % K = K - 1 := by
        rw [hB_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hv0 : K - 1 - B % K = 0 := by omega
      rw [ite_eq_left hv0, hK_mul_div]
      have hfin : B * K + (K - 1) = K * A - 1 := by
        have h1 : B * K + (K - 1) + 1 = K * A := by
          calc B * K + (K - 1) + 1
            _ = B * K + K := by omega
            _ = (B + 1) * K := (Nat.succ_mul B K).symm
            _ = K * A := by rw [hBA, Nat.mul_comm]
        omega
      rw [hfin]
  · rw [ite_eq_right hdvd]
    have hv_ne : K - 1 - B % K ≠ 0 := by
      intro hv0
      have hr_eq : B % K = K - 1 := by omega
      apply hdvd
      refine ⟨B / K + 1, ?_⟩
      calc A = B + 1 := hBA.symm
        _ = K * (B / K) + B % K + 1 := by rw [hdiv_mod]
        _ = K * (B / K) + K := by omega
        _ = K * (B / K + 1) := (Nat.mul_succ K (B / K)).symm
    have hqK : B / K * K + B % K = B := by rw [Nat.mul_comm]; exact hdiv_mod
    rw [ite_eq_right hv_ne, hqK]
    have hfin : (B * K + (K - 1)) * K + (K - 1) = K ^ 2 * A - 1 := by
      have h1 : (B * K + (K - 1)) * K + (K - 1) + 1 = K ^ 2 * A := by
        calc (B * K + (K - 1)) * K + (K - 1) + 1
          _ = (B * K + (K - 1)) * K + K := by omega
          _ = (B * K + (K - 1) + 1) * K := (Nat.succ_mul _ K).symm
          _ = (B * K + K) * K := by rw [Nat.add_assoc, hK1]
          _ = (B + 1) * K * K := by rw [← Nat.succ_mul B K]
          _ = K ^ 2 * A := by rw [hBA, Nat.pow_two, Nat.mul_assoc, Nat.mul_comm A (K * K)]
      omega
    rw [hfin]

/-- `product` loop (State `33`): runs `product_step` $M + 1$ times to reach
`[0, M + 1, shuniaProd (M + 2) - 1, 0, 0]`. -/
theorem product_loop_eval {P : List (Fin 2)} (hP : walkInternal 27 P = some 33) (M : ℕ) :
    ∃ s ≥ 1, rhRegNSteps s ⟨trimZeros P, [0, 0, 0, M, 0]⟩ =
      some ⟨retStack P, [0, M + 1, shuniaProd (M + 2) - 1, 0, 0]⟩ := by
  have hP0 := walkInternal_snoc hP (b := 0) (q_end := 38) rfl rfl
  have hP1 := walkInternal_snoc hP (b := 1) (q_end := 39) rfl rfl
  have hev_f : evalStack (P ++ [1]) = .decnz 3 (P ++ [1] ++ [1]) (retStack P) := by
    rw [evalStack_leaf0_of_walkInternal hP1 (q' := 46) rfl rfl]
    simp [isLeafInc, leafReg, retStack_append_one]
  have hev_cont : evalStack (P ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1]) (k := 1) hP1 rfl
      (Or.inr (Or.inl ⟨rfl, rfl⟩))
    simpa [popContinueRev, popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hiter : ∀ (rem K : ℕ), 2 ≤ K →
      ∃ s ≥ 1, rhRegNSteps s ⟨trimZeros P, [0, K - 2, shuniaProd (K - 1) - 1, rem, 0]⟩ =
        some ⟨retStack P, [0, K + rem - 1, shuniaProd (K + rem) - 1, 0, 0]⟩ := by
    intro rem
    induction rem with
    | zero =>
      intro K hK
      obtain ⟨sp, hsp, hsteps_p, _⟩ :=
        subEval_product_step (P ++ [0]) hP0 [0, K - 2, shuniaProd (K - 1) - 1, 0, 0] rfl
      dsimp only at hsteps_p
      rw [trimZeros_append_zero, retStack_append_zero, product_step_shuniaProd hK 0] at hsteps_p
      have hs_f := rhRegStep_of_decnz_zero (regs := [0, K - 1, shuniaProd K - 1, 0, 0]) hev_f rfl
      exact ⟨sp + 1, by omega, rhRegNSteps_bind_eq hsteps_p (rhRegStep_one hs_f)⟩
    | succ rem ih =>
      intro K hK
      obtain ⟨sp, hsp, hsteps_p, _⟩ :=
        subEval_product_step (P ++ [0]) hP0 [0, K - 2, shuniaProd (K - 1) - 1, rem + 1, 0] rfl
      dsimp only at hsteps_p
      rw [trimZeros_append_zero, retStack_append_zero,
        product_step_shuniaProd hK (rem + 1)] at hsteps_p
      have hs_f := rhRegStep_of_decnz_succ
        (regs := [0, K - 1, shuniaProd K - 1, rem + 1, 0]) hev_f rfl
      have hs_c := rhRegStep_of_jump (regs := [0, K - 1, shuniaProd K - 1, rem, 0]) hev_cont
      have hK' : 2 ≤ K + 1 := by omega
      obtain ⟨sr, hsr, hsteps_r⟩ := ih (K + 1) hK'
      have h_in : [0, K + 1 - 2, shuniaProd (K + 1 - 1) - 1, rem, 0] =
          [0, K - 1, shuniaProd K - 1, rem, 0] := rfl
      have h_out : [0, K + 1 + rem - 1, shuniaProd (K + 1 + rem) - 1, 0, 0] =
          [0, K + (rem + 1) - 1, shuniaProd (K + (rem + 1)) - 1, 0, 0] := by
        have hadd : K + 1 + rem = K + (rem + 1) := by omega
        rw [hadd]
      rw [h_in] at hsteps_r
      rw [h_out] at hsteps_r
      have tail := step_rhRegNSteps hs_f (step_rhRegNSteps hs_c hsteps_r)
      exact ⟨sp + (sr + 2), by omega, rhRegNSteps_bind_eq hsteps_p tail⟩
  have h1 : shuniaProd 1 = 1 := by decide
  have h2 : 2 + M = M + 2 := by omega
  obtain ⟨s, hs, hsteps⟩ := hiter M 2 (by omega)
  rw [h1, h2] at hsteps
  exact ⟨s, hs, hsteps⟩

/-- `digits` (State `49`): consumes `B` via offset base-$J$ division ($J = j + v + 1 \ge 2$)
and recovers `j + v` in `regs[1]`. -/
theorem digits_eval {P : List (Fin 2)} (hP : walkInternal 27 P = some 49)
    {j B f v : ℕ} (hJ : 2 ≤ j + v + 1) :
    ∃ s ≥ 1, rhRegNSteps s ⟨trimZeros P, [0, j, B, f, v]⟩ =
      some ⟨retStack P, [0, j + v, 0, f - offsetDigits (j + v + 1) B, 0]⟩ := by
  have hP0 := walkInternal_snoc hP (b := 0) (q_end := 59) rfl rfl
  have hP1 := walkInternal_snoc hP (b := 1) (q_end := 60) rfl rfl
  have hP01 := walkInternal_snoc hP0 (b := 1) (q_end := 72) rfl rfl
  have hP010 := walkInternal_snoc hP01 (b := 0) (q_end := 54) rfl rfl
  have hP011 := walkInternal_snoc hP01 (b := 1) (q_end := 86) rfl rfl
  have hP0110 := walkInternal_snoc hP011 (b := 0) (q_end := 96) rfl rfl
  have hev_x : evalStack (trimZeros P) = .decnz 2 (P ++ [0] ++ [1]) (P ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hP0 (q' := 71) rfl rfl
    have htz := evalStack_trimZeros_of_walkInternal hP0
    rw [trimZeros_append_zero] at htz
    rw [← htz, retStack_append_zero] at h
    simpa [isLeafInc, leafReg] using h
  have hev_cont : evalStack (P ++ [0] ++ [1] ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [0] ++ [1] ++ [1]) (k := 2)
      hP011 rfl (Or.inr (Or.inr ⟨rfl, rfl⟩))
    simpa [popContinueRev, popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  set J := j + v + 1
  have hloop : ∀ (x : ℕ) (ja fa va : ℕ), ja + va + 1 = J →
      ∃ s ≥ 1, rhRegNSteps s ⟨trimZeros P, [0, ja, x, fa, va]⟩ =
        some ⟨retStack P, [0, J - 1, 0, fa - offsetDigits J x, 0]⟩ := by
    intro x
    induction x using Nat.strong_induction_on with
    | h x ih =>
      intro ja fa va hja
      rcases x with _ | x'
      · have hs_x := rhRegStep_of_decnz_zero (regs := [0, ja, 0, fa, va]) hev_x rfl
        obtain ⟨sm, hsm, hsteps_m, _⟩ := subEval_move_v_j (P ++ [1]) hP1 [0, ja, 0, fa, va] rfl
        rw [trimZeros_append_one, retStack_append_one] at hsteps_m
        have heq_j : ja + va = J - 1 := by omega
        have hoff : offsetDigits J 0 = 0 := by simp [offsetDigits]
        simp only [List.getD_cons_zero, List.getD_cons_succ, heq_j, hoff,
          Nat.sub_zero] at hsteps_m ⊢
        exact ⟨sm + 1, by omega, step_rhRegNSteps hs_x hsteps_m⟩
      · have hs_x := rhRegStep_of_decnz_succ (regs := [0, ja, x' + 1, fa, va]) hev_x rfl
        obtain ⟨sd, hsd, hsteps_d, _⟩ :=
          subEval_divide (P ++ [0] ++ [1] ++ [0]) hP010 [0, ja, x', fa, va] rfl
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_d
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add] at hsteps_d
        rw [hja] at hsteps_d
        obtain ⟨sf, hsf, hsteps_f, _⟩ :=
          subEval_dec_f (P ++ [0] ++ [1] ++ [1] ++ [0]) hP0110
            [0, x' % J, x' / J, fa, J - 1 - x' % J] rfl
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_f
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hsteps_f
        have hs_c := rhRegStep_of_jump
          (regs := [0, x' % J, x' / J, fa - 1, J - 1 - x' % J]) hev_cont
        have hr_lt : x' % J < J := Nat.mod_lt x' (by omega)
        have hja' : x' % J + (J - 1 - x' % J) + 1 = J := by omega
        have hlt_x : x' / J < x' + 1 := Nat.lt_succ_of_le (Nat.div_le_self x' J)
        obtain ⟨si, hsi, hsteps_i⟩ :=
          ih (x' / J) hlt_x (x' % J) (fa - 1) (J - 1 - x' % J) hja'
        have hoff : fa - 1 - offsetDigits J (x' / J) = fa - offsetDigits J (x' + 1) := by
          simp [offsetDigits, hJ]; omega
        rw [hoff] at hsteps_i
        have c1 := step_rhRegNSteps hs_x hsteps_d
        have c2 := rhRegNSteps_bind_eq c1 hsteps_f
        have c3 := rhRegNSteps_bind_eq c2 (step_rhRegNSteps hs_c hsteps_i)
        exact ⟨((sd + 1) + sf) + (si + 1), by omega, c3⟩
  have hstart : j + v + 1 = J := rfl
  obtain ⟨s, hs, hsteps⟩ := hloop B j f v hstart
  exact ⟨s, hs, by simpa [J] using hsteps⟩

/-- `halve(j)` (State `104`): `(m, j, x, f, v) ↦ (m + (j + 1)/2, v + j/2, x, f, 0)`. -/
theorem subEval_halve_j :
    SubEval 104 (fun regs => [regs.getD 0 0 + (regs.getD 1 0 + 1) / 2,
      regs.getD 4 0 + regs.getD 1 0 / 2, regs.getD 2 0, regs.getD 3 0, 0]) := by
  have h119 := subEval_decnz_inc (q := 119) (q₀ := 47) (q₁ := 70) rfl rfl rfl rfl rfl rfl
  have h117 := subEval_inc_seq (q := 117) (q₀ := 4) (q₁ := 119) rfl rfl rfl rfl rfl h119
  have h110 : SubEval 110 (fun regs => [regs.getD 0 0 + (regs.getD 1 0 + 1) / 2,
      0, regs.getD 2 0, regs.getD 3 0, regs.getD 4 0 + regs.getD 1 0 / 2]) := by
    refine subEval_while_body 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl h117
      (fun regs => [regs.getD 0 0 + (regs.getD 1 0 + 1) / 2,
        0, regs.getD 2 0, regs.getD 3 0, regs.getD 4 0 + regs.getD 1 0 / 2])
      (fun _ _ => by simp)
      (fun regs hlen hj => by
        obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hj
        subst hj
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero,
          Nat.zero_add, Nat.div_eq_of_lt (by decide : 1 < 2)])
      (fun regs k hlen hj => by
        obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
        rw [show leafReg 4 = 0 from rfl, show leafReg 47 = 1 from rfl,
          show leafReg 70 = 4 from rfl]
        simp only [List.set_cons_zero, List.set_cons_succ,
          List.getD_cons_zero, List.getD_cons_succ] at hj ⊢
        subst hj
        rcases k with _ | k'
        · simp only [↓reduceIte, List.getD_cons_zero, List.getD_cons_succ]
        · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
            List.getD_cons_zero, List.getD_cons_succ]
          have h1 : m + 1 + (k' + 1) / 2 = m + (k' + 1 + 1 + 1) / 2 := by omega
          have h2 : v + 1 + k' / 2 = v + (k' + 1 + 1) / 2 := by omega
          rw [h1, h2])
      (fun regs k hlen hj => by
        obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
        rw [show leafReg 4 = 0 from rfl, show leafReg 47 = 1 from rfl,
          show leafReg 70 = 4 from rfl]
        simp only [List.set_cons_zero, List.set_cons_succ,
          List.getD_cons_zero, List.getD_cons_succ] at hj ⊢
        subst hj
        rcases k with _ | k' <;>
          (simp only [↓reduceIte, Nat.succ_ne_zero, Nat.add_sub_cancel,
             List.getD_cons_zero, List.getD_cons_succ]
           omega))
  refine (subEval_seq (q := 104) (q₀ := 110) (q₁ := 60) rfl rfl rfl rfl
    h110 subEval_move_v_j).congr ?_
  intro regs hlen
  obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add]

/-- `halve(f)` (State `111`): `(m, j, x, f, v) ↦ (m, j, x, v + f/2, 0)`. -/
theorem subEval_halve_f :
    SubEval 111 (fun regs => [regs.getD 0 0, regs.getD 1 0, regs.getD 2 0,
      regs.getD 4 0 + regs.getD 3 0 / 2, 0]) := by
  have h120 := subEval_decnz_inc (q := 120) (q₀ := 46) (q₁ := 70) rfl rfl rfl rfl rfl rfl
  have h115 : SubEval 115 (fun regs => [regs.getD 0 0, regs.getD 1 0, regs.getD 2 0,
      0, regs.getD 4 0 + regs.getD 3 0 / 2]) := by
    refine subEval_while_body 3 rfl rfl rfl rfl rfl rfl rfl rfl rfl h120
      (fun regs => [regs.getD 0 0, regs.getD 1 0, regs.getD 2 0,
        0, regs.getD 4 0 + regs.getD 3 0 / 2])
      (fun _ _ => by simp)
      (fun regs hlen hf => by
        obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hf
        subst hf
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_div, Nat.add_zero])
      (fun regs k hlen hf => by
        obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
        rw [show leafReg 46 = 3 from rfl, show leafReg 70 = 4 from rfl]
        simp only [List.set_cons_zero, List.set_cons_succ,
          List.getD_cons_zero, List.getD_cons_succ] at hf ⊢
        subst hf
        rcases k with _ | k'
        · simp only [↓reduceIte, List.getD_cons_zero, List.getD_cons_succ]
        · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
            List.getD_cons_zero, List.getD_cons_succ]
          have h1 : v + 1 + k' / 2 = v + (k' + 1 + 1) / 2 := by omega
          rw [h1])
      (fun regs k hlen hf => by
        obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
        rw [show leafReg 46 = 3 from rfl, show leafReg 70 = 4 from rfl]
        simp only [List.set_cons_zero, List.set_cons_succ,
          List.getD_cons_zero, List.getD_cons_succ] at hf ⊢
        subst hf
        rcases k with _ | k' <;>
          (simp only [↓reduceIte, Nat.succ_ne_zero, Nat.add_sub_cancel,
             List.getD_cons_zero, List.getD_cons_succ]
           omega))
  refine (subEval_seq (q := 111) (q₀ := 115) (q₁ := 116) rfl rfl rfl rfl
    h115 subEval_move_v_f).congr ?_
  intro regs hlen
  obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add]

/-- Scaling loop inside `width` (State `61`): when `v = 0`, scales `j` by 4 each tick,
conserving `m + j`, counting `q = quarterClock j` in `x`, and dividing `f` by $2^q$. -/
theorem width_loop_eval {P : List (Fin 2)} (hP : walkInternal 27 P = some 61)
    (m j x f : ℕ) :
    let q := quarterClock j
    ∃ s ≥ 1, rhRegNSteps s ⟨trimZeros P, [m, j, x, f, 0]⟩ =
      some ⟨retStack P, [m + j, 0, x + q, f / 2 ^ q, 0]⟩ := by
  have h105 := subEval_seq (q := 105) (q₀ := 104) (q₁ := 111) rfl rfl rfl rfl
    subEval_halve_j subEval_halve_f
  have h98 := subEval_seq (q := 98) (q₀ := 104) (q₁ := 105) rfl rfl rfl rfl subEval_halve_j h105
  have h88 : SubEval 88 (fun regs =>
      let m₁ := regs.getD 0 0 + 1 + (regs.getD 1 0 + 1) / 2
      let j₁ := regs.getD 4 0 + regs.getD 1 0 / 2
      [m₁ + (j₁ + 1) / 2, j₁ / 2, regs.getD 2 0, regs.getD 3 0 / 2, 0]) := by
    refine (subEval_inc_seq (q := 88) (q₀ := 4) (q₁ := 98) rfl rfl rfl rfl rfl h98).congr ?_
    intro regs hlen
    rcases regs with _ | ⟨m0, _ | ⟨j0, _ | ⟨x0, _ | ⟨f0, _ | ⟨v0, _ | _⟩⟩⟩⟩⟩ <;>
      simp [leafReg] at hlen ⊢
  have hP1 := walkInternal_snoc hP (b := 1) (q_end := 75) rfl rfl
  have hP10 := walkInternal_snoc hP1 (b := 0) (q_end := 88) rfl rfl
  have hP11 := walkInternal_snoc hP1 (b := 1) (q_end := 89) rfl rfl
  have hev0 : evalStack (trimZeros P) = .decnz 1 (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP (q' := 47) rfl rfl]
    simp [isLeafInc, leafReg]
  have hev_x : evalStack (P ++ [1] ++ [1]) = .inc 2 (P ++ [1] ++ [1] ++ [1]) := by
    rw [evalStack_leaf0_of_walkInternal hP11 (q' := 99) rfl rfl]
    simp [isLeafInc, leafReg]
  have hev_c : evalStack (P ++ [1] ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1] ++ [1]) (k := 2) hP11 rfl
      (Or.inr (Or.inr ⟨rfl, rfl⟩))
    simpa [popContinueRev, popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (ja : ℕ) (ma xa fa : ℕ),
      ∃ s ≥ 1, rhRegNSteps s ⟨trimZeros P, [ma, ja, xa, fa, 0]⟩ =
        some ⟨retStack P, [ma + ja, 0, xa + quarterClock ja, fa / 2 ^ quarterClock ja, 0]⟩ := by
    intro ja
    induction ja using Nat.strong_induction_on with
    | h ja ih =>
      intro ma xa fa
      rcases ja with _ | z
      · have hs := rhRegStep_of_decnz_zero (regs := [ma, 0, xa, fa, 0]) hev0 rfl
        have hq0 : quarterClock 0 = 0 := by simp [quarterClock]
        simp only [hq0, Nat.add_zero, pow_zero, Nat.div_one]
        exact ⟨1, le_refl 1, rhRegStep_one hs⟩
      · have hs0 := rhRegStep_of_decnz_succ (regs := [ma, z + 1, xa, fa, 0]) hev0 rfl
        obtain ⟨sb, hsb, hsteps_b, _⟩ := h88 (P ++ [1] ++ [0]) hP10 [ma, z, xa, fa, 0] rfl
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_b
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add] at hsteps_b
        have hs_x := rhRegStep_of_inc (regs := [ma + 1 + (z + 1) / 2 + (z / 2 + 1) / 2,
          z / 2 / 2, xa, fa / 2, 0]) hev_x
        have hs_c := rhRegStep_of_jump (regs := [ma + 1 + (z + 1) / 2 + (z / 2 + 1) / 2,
          z / 2 / 2, xa + 1, fa / 2, 0]) hev_c
        have hz_lt : z / 2 / 2 < z + 1 := by omega
        obtain ⟨si, hsi, hsteps_i⟩ :=
          ih (z / 2 / 2) hz_lt (ma + 1 + (z + 1) / 2 + (z / 2 + 1) / 2) (xa + 1) (fa / 2)
        have hdiv4 : z / 2 / 2 = z / 4 := by omega
        have hm_sum : ma + 1 + (z + 1) / 2 + (z / 2 + 1) / 2 + z / 2 / 2 = ma + (z + 1) := by
          omega
        have hq_succ : quarterClock (z + 1) = 1 + quarterClock (z / 4) := by simp [quarterClock]
        have hx_sum : xa + 1 + quarterClock (z / 2 / 2) = xa + quarterClock (z + 1) := by
          rw [hdiv4, hq_succ]; omega
        have hf_div : fa / 2 / 2 ^ quarterClock (z / 2 / 2) = fa / 2 ^ quarterClock (z + 1) := by
          rw [hdiv4, hq_succ, pow_add, pow_one, Nat.div_div_eq_div_mul]
        rw [hm_sum, hx_sum, hf_div] at hsteps_i
        have c1 := step_rhRegNSteps hs0 hsteps_b
        have c2 := rhRegNSteps_bind_eq c1 (step_rhRegNSteps hs_x (step_rhRegNSteps hs_c hsteps_i))
        exact ⟨(sb + 1) + (si + 2), by omega, c2⟩
  exact hloop j m x f

/-- Subtraction loop inside `compare` (State `76`): `[m, j, x, f, v] ↦ [m, j, 0, f - x, v]`. -/
theorem subEval_compare_sub :
    SubEval 76 (fun regs => [regs.getD 0 0, regs.getD 1 0, 0,
      regs.getD 3 0 - regs.getD 2 0, regs.getD 4 0]) := by
  refine subEval_while_body 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl subEval_dec_f
    (fun regs => [regs.getD 0 0, regs.getD 1 0, 0,
      regs.getD 3 0 - regs.getD 2 0, regs.getD 4 0])
    (fun _ _ => by simp)
    (fun regs hlen hx => by
      obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hx
      subst hx
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero])
    (fun regs k hlen hx => by
      obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
      simp only [List.set_cons_zero, List.set_cons_succ,
        List.getD_cons_zero, List.getD_cons_succ] at hx ⊢
      subst hx
      congr 1; congr 1; congr 1; congr 1; omega)
    (fun regs k hlen hx => by
      obtain ⟨m, j, x, f, v, rfl⟩ := list_length_five regs hlen
      simp only [List.set_cons_zero, List.set_cons_succ,
        List.getD_cons_zero, List.getD_cons_succ] at hx ⊢
      omega)

theorem shuniaCounterexample_iff_sub_pos (n : ℕ) :
    ShuniaCounterexample n ↔
      0 < shuniaDeficit n / 2 ^ quarterClock (n - 1) - quarterClock (n - 1) := by
  unfold ShuniaCounterexample
  set q := quarterClock (n - 1)
  have hpow : 0 < 2 ^ q := Nat.pow_pos (by decide)
  rw [← Nat.le_div_iff_mul_le hpow]
  constructor <;> intro h <;> omega

/-- Full `compare` subroutine at State `62` (`[1, 1, 1, 1, 1]`): subtracts `x` from `f`,
then returns to `[]` if `f - x = 0`, or halts at State `77` (`[1^7]`) if `0 < f - x`. -/
theorem compare_eval (m x f : ℕ) :
    (f - x = 0 →
      ∃ s ≥ 1, rhRegNSteps s ⟨[1, 1, 1, 1, 1], [m, 0, x, f, 0]⟩ =
        some ⟨[], [m, 0, 0, 0, 0]⟩) ∧
    (0 < f - x →
      ∃ s c, rhRegNSteps s ⟨[1, 1, 1, 1, 1], [m, 0, x, f, 0]⟩ = some c ∧
        rhRegStep c = none) := by
  obtain ⟨s₆, hs₆, h₆, _⟩ := subEval_compare_sub [1, 1, 1, 1, 1, 0] rfl [m, 0, x, f, 0] rfl
  have h₆' : rhRegNSteps s₆ ⟨[1, 1, 1, 1, 1], [m, 0, x, f, 0]⟩ =
      some ⟨[1, 1, 1, 1, 1, 1], [m, 0, 0, f - x, 0]⟩ := by
    simpa [trimZeros, dropLeadingZeros, retStack, popBreakRev] using h₆
  have hev_chk : evalStack [1, 1, 1, 1, 1, 1] = .decnz 3 [1, 1, 1, 1, 1, 1, 1] [] := rfl
  constructor
  · intro hz
    have hs₇ : rhRegStep ⟨[1, 1, 1, 1, 1, 1], [m, 0, 0, f - x, 0]⟩ =
        some ⟨[], [m, 0, 0, 0, 0]⟩ := by
      rw [hz]; exact rhRegStep_of_decnz_zero hev_chk rfl
    exact ⟨s₆ + 1, by omega, rhRegNSteps_bind_eq h₆' (rhRegStep_one hs₇)⟩
  · intro hpos
    have hsucc : f - x = (f - x - 1) + 1 := by omega
    have hs₇ : rhRegStep ⟨[1, 1, 1, 1, 1, 1], [m, 0, 0, f - x, 0]⟩ =
        some ⟨[1, 1, 1, 1, 1, 1, 1], [m, 0, 0, f - x - 1, 0]⟩ :=
      rhRegStep_of_decnz_succ hev_chk hsucc
    have hhalt : rhRegStep ⟨[1, 1, 1, 1, 1, 1, 1], [m, 0, 0, f - x - 1, 0]⟩ = none := rfl
    exact ⟨s₆ + 1, _, rhRegNSteps_bind_eq h₆' (rhRegStep_one hs₇), hhalt⟩

/-- Full `width` tail at State `50` (`[1, 1, 1, 1]`): computes `q = quarterClock j`,
divides `f` by `2 ^ q`, and runs `compare`. -/
theorem width_eval (j f : ℕ) :
    let q := quarterClock j
    (f / 2 ^ q - q = 0 →
      ∃ s ≥ 1, rhRegNSteps s ⟨[1, 1, 1, 1], [0, j, 0, f, 0]⟩ =
        some ⟨[], [j, 0, 0, 0, 0]⟩) ∧
    (0 < f / 2 ^ q - q →
      ∃ s c, rhRegNSteps s ⟨[1, 1, 1, 1], [0, j, 0, f, 0]⟩ = some c ∧
        rhRegStep c = none) := by
  obtain ⟨s₅, hs₅, h₅⟩ := width_loop_eval (P := [1, 1, 1, 1, 0]) rfl 0 j 0 f
  set q := quarterClock j
  have h₅' : rhRegNSteps s₅ ⟨[1, 1, 1, 1], [0, j, 0, f, 0]⟩ =
      some ⟨[1, 1, 1, 1, 1], [j, 0, q, f / 2 ^ q, 0]⟩ := by
    simpa [trimZeros, dropLeadingZeros, retStack, popBreakRev, q] using h₅
  have hcmp := compare_eval j q (f / 2 ^ q)
  constructor
  · intro hz
    obtain ⟨sc, hsc, hc⟩ := hcmp.1 hz
    exact ⟨s₅ + sc, by omega, rhRegNSteps_bind_eq h₅' hc⟩
  · intro hpos
    obtain ⟨sc, c, hc, hnone⟩ := hcmp.2 hpos
    exact ⟨s₅ + sc, c, rhRegNSteps_bind_eq h₅' hc, hnone⟩

/-- Deterministic execution of one full stage $n = M + 2$ (`main` at State `27`, stack `[]`):
- If `¬ ShuniaCounterexample (M + 2)`, reaches `⟨[], [M + 1, 0, 0, 0, 0]⟩` in $s \ge 1$ steps.
- If `ShuniaCounterexample (M + 2)`, reaches a halting configuration (`rhRegStep c = none`). -/
theorem main_stage_step (M : ℕ) :
    (¬ ShuniaCounterexample (M + 2) →
      ∃ s ≥ 1, rhRegNSteps s ⟨[], [M, 0, 0, 0, 0]⟩ =
        some ⟨[], [M + 1, 0, 0, 0, 0]⟩) ∧
    (ShuniaCounterexample (M + 2) →
      ∃ s c, rhRegNSteps s ⟨[], [M, 0, 0, 0, 0]⟩ = some c ∧ rhRegStep c = none) := by
  -- 1. `move(m, f)` at `[0]` (State `29`):
  obtain ⟨s₁, hs₁, h₁, _⟩ := subEval_move_m_f [0] rfl [M, 0, 0, 0, 0] rfl
  have h₁' : rhRegNSteps s₁ ⟨[], [M, 0, 0, 0, 0]⟩ = some ⟨[1], [0, 0, 0, M, 0]⟩ := by
    simpa [trimZeros, dropLeadingZeros, retStack, popBreakRev] using h₁
  -- 2. `product` at `[1, 0]` (State `33`):
  obtain ⟨s₂, hs₂, h₂⟩ := product_loop_eval (P := [1, 0]) rfl M
  have h₂' : rhRegNSteps s₂ ⟨[1], [0, 0, 0, M, 0]⟩ =
      some ⟨[1, 1], [0, M + 1, shuniaProd (M + 2) - 1, 0, 0]⟩ := by
    simpa [trimZeros, dropLeadingZeros, retStack, popBreakRev] using h₂
  -- 3. `seed_deficit` at `[1, 1, 0]` (State `40`):
  obtain ⟨s₃, hs₃, h₃, _⟩ :=
    subEval_seed_deficit [1, 1, 0] rfl [0, M + 1, shuniaProd (M + 2) - 1, 0, 0] rfl
  have h₃' : rhRegNSteps s₃ ⟨[1, 1], [0, M + 1, shuniaProd (M + 2) - 1, 0, 0]⟩ =
      some ⟨[1, 1, 1], [0, 0, shuniaProd (M + 2) - 1, M + 1, M + 1]⟩ := by
    simpa [trimZeros, dropLeadingZeros, retStack, popBreakRev] using h₃
  -- 4. `digits` at `[1, 1, 1, 0]` (State `49`):
  obtain ⟨s₄, hs₄, h₄⟩ := digits_eval (P := [1, 1, 1, 0]) rfl
    (j := 0) (B := shuniaProd (M + 2) - 1) (f := M + 1) (v := M + 1) (by omega)
  have h₄' : rhRegNSteps s₄ ⟨[1, 1, 1], [0, 0, shuniaProd (M + 2) - 1, M + 1, M + 1]⟩ =
      some ⟨[1, 1, 1, 1], [0, M + 1, 0, shuniaDeficit (M + 2), 0]⟩ := by
    have hdef : M + 1 - offsetDigits (M + 1 + 1) (shuniaProd (M + 2) - 1) =
        shuniaDeficit (M + 2) := rfl
    simpa [trimZeros, dropLeadingZeros, retStack, popBreakRev, hdef] using h₄
  have hpre := rhRegNSteps_bind_eq (rhRegNSteps_bind_eq (rhRegNSteps_bind_eq h₁' h₂') h₃') h₄'
  have hw := width_eval (M + 1) (shuniaDeficit (M + 2))
  constructor
  · intro hnot
    have hrem0 : shuniaDeficit (M + 2) / 2 ^ quarterClock (M + 1) - quarterClock (M + 1) = 0 := by
      have hpos := mt (shuniaCounterexample_iff_sub_pos (M + 2)).mpr hnot
      change ¬ 0 < shuniaDeficit (M + 2) / 2 ^ quarterClock (M + 1) - quarterClock (M + 1) at hpos
      omega
    obtain ⟨sw, hsw, hw_steps⟩ := hw.1 hrem0
    exact ⟨_, by omega, rhRegNSteps_bind_eq hpre hw_steps⟩
  · intro hce
    have hpos : 0 < shuniaDeficit (M + 2) / 2 ^ quarterClock (M + 1) - quarterClock (M + 1) :=
      (shuniaCounterexample_iff_sub_pos (M + 2)).mp hce
    obtain ⟨sw, c, hw_steps, hhalt⟩ := hw.2 hpos
    exact ⟨_, c, rhRegNSteps_bind_eq hpre hw_steps, hhalt⟩

/-- Main Layer 2 Theorem: the 5-register machine for `riemann121` halts if and only if
there exists an integer $n \ge 2$ satisfying `ShuniaCounterexample n`. -/
theorem rhRegHalts_iff_exists_shuniaCounterexample :
    RhRegHalts ↔ ∃ n ≥ 2, ShuniaCounterexample n := by
  rw [rhRegHalts_iff_exists_rhRegNSteps]
  have findBelow : ∀ B : ℕ,
      (∀ m < B, ¬ ShuniaCounterexample (m + 2)) ∨
        ∃ K < B, ShuniaCounterexample (K + 2) ∧ ∀ m < K, ¬ ShuniaCounterexample (m + 2) := by
    intro B
    induction B with
    | zero => exact Or.inl (fun _ hm => absurd hm (Nat.not_lt_zero _))
    | succ B ih =>
      rcases ih with hnone | ⟨K, hKB, hK, hmin⟩
      · if hB : ShuniaCounterexample (B + 2) then
          exact Or.inr ⟨B, Nat.lt_succ_self B, hB, hnone⟩
        else
          exact Or.inl (fun m hm => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
            · exact hnone m hlt
            · exact hB)
      · exact Or.inr ⟨K, Nat.lt_succ_of_lt hKB, hK, hmin⟩
  have hreach_upto : ∀ K : ℕ, (∀ m < K, ¬ ShuniaCounterexample (m + 2)) →
      ∃ T ≥ K, rhRegNSteps T rhRegInit = some ⟨[], [K, 0, 0, 0, 0]⟩ := by
    intro K
    induction K with
    | zero => intro _; exact ⟨0, le_refl 0, rfl⟩
    | succ K ih =>
      intro hnone
      obtain ⟨T, hT, hsteps_T⟩ := ih (fun m hm => hnone m (by omega))
      obtain ⟨s, hs, hstep_s⟩ := (main_stage_step K).1 (hnone K (by omega))
      exact ⟨T + s, by omega, rhRegNSteps_bind_eq hsteps_T hstep_s⟩
  constructor
  · rintro ⟨N, ch, hN, hnone⟩
    rcases findBelow (N + 1) with hsafe | ⟨K, _, hK, _⟩
    · obtain ⟨T, hT_ge, hT_steps⟩ := hreach_upto (N + 1) hsafe
      have hsplit : T = N + (T - N) := by omega
      have hrem_pos : T - N = (T - N - 1) + 1 := by omega
      rw [hsplit, rhRegNSteps_add, hN, Option.bind_some, hrem_pos, rhRegNSteps_succ,
        hnone] at hT_steps
      cases hT_steps
    · exact ⟨K + 2, by omega, hK⟩
  · rintro ⟨n, hn, hce⟩
    have hce' : ShuniaCounterexample ((n - 2) + 2) := by convert hce; omega
    rcases findBelow (n - 1) with hsafe | ⟨K, _, hK, hall⟩
    · exact False.elim (hsafe (n - 2) (by omega) hce')
    · obtain ⟨T, _, hT⟩ := hreach_upto K hall
      obtain ⟨s, ch, hs, hnone⟩ := (main_stage_step K).2 hK
      exact ⟨T + s, ch, rhRegNSteps_bind_eq hT hs, hnone⟩

end ConjectureMachines.Riemann120.Layer2

end
