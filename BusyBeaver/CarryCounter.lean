module

public import BusyBeaver.Defs
public import BusyBeaver.Counter
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Shared Mealy Carry-Counter Certificates (`BusyBeaver.CarryCounter`)

Generalizes `BusyBeaver.Counter.CarryIncrementSpec` and `IsOdometerCryptid` to
arbitrary finite-state Mealy carry-transducer counters (`CarryCounterSpec`,
`MealyCarrySpec`, `MealyCarryTMSpec`) for proving `IsDoesNotHalt` on
fixed-width, mixed-radix, multi-carry, and run-compressed counter holdouts.

All declarations live in `namespace BusyBeaver.CarryCounter` with `@[scoped simp]`
attributes so importing `BusyBeaver.Basic` or `BusyBeaver.Import` never alters
default `simp` sets in existing proofs.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.CarryCounter

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- ============================================================================
-- 1. Abstract Valuation-Guided Carry Counter (`CarryCounterSpec`)
-- ============================================================================

section AbstractCarryCounter

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/--
Abstract certificate for a counter machine `M` over stack/state space `Stack`:
- `ValidStack : Stack → Prop` restricts closure to reachable valid counter states
  (Design Principle 1: invariant-relative closure).
- `inc : Stack → Stack` is the macro-increment operator preserving `ValidStack`.
- `val : Stack → ℕ` is a strict natural-number valuation satisfying
  `val (inc s) = val s + 1` on all valid stacks (certifying genuine `+1`
  odometer progression rather than a finite state cycle).
- `step_inc` witnesses `(evalCounter s) [M]⊢⁺ evalCounter (inc s)` on valid stacks.
-/
structure CarryCounterSpec (M : Machine Γ Λ) (Stack : Type*) where
  ValidStack : Stack → Prop
  evalCounter : Stack → Cfg Γ Λ
  inc : Stack → Stack
  val : Stack → ℕ
  s₀ : Stack
  init_reaches : (init []) [M]⊢* evalCounter s₀
  valid_init : ValidStack s₀
  inc_valid : ∀ s, ValidStack s → ValidStack (inc s)
  val_inc : ∀ s, ValidStack s → val (inc s) = val s + 1
  step_inc : ∀ s, ValidStack s → (evalCounter s) [M]⊢⁺ evalCounter (inc s)

/-- `n`-fold macro-increment from a starting counter stack `s`. -/
def CarryCounterSpec.iter {M : Machine Γ Λ} {Stack : Type*}
    (spec : CarryCounterSpec M Stack) : ℕ → Stack → Stack
  | 0, s => s
  | n + 1, s => spec.iter n (spec.inc s)

@[scoped simp]
theorem CarryCounterSpec.iter_zero {M : Machine Γ Λ} {Stack : Type*}
    (spec : CarryCounterSpec M Stack) (s : Stack) :
    spec.iter 0 s = s := rfl

@[scoped simp]
theorem CarryCounterSpec.iter_succ {M : Machine Γ Λ} {Stack : Type*}
    (spec : CarryCounterSpec M Stack) (n : ℕ) (s : Stack) :
    spec.iter (n + 1) s = spec.iter n (spec.inc s) := rfl

theorem CarryCounterSpec.iter_valid {M : Machine Γ Λ} {Stack : Type*}
    (spec : CarryCounterSpec M Stack) (n : ℕ) {s : Stack} (hs : spec.ValidStack s) :
    spec.ValidStack (spec.iter n s) := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih (spec.inc_valid s hs)

theorem CarryCounterSpec.iter_val {M : Machine Γ Λ} {Stack : Type*}
    (spec : CarryCounterSpec M Stack) (n : ℕ) {s : Stack} (hs : spec.ValidStack s) :
    spec.val (spec.iter n s) = spec.val s + n := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [CarryCounterSpec.iter_succ, ih (spec.inc_valid s hs), spec.val_inc s hs]
    omega

theorem CarryCounterSpec.iter_reachesStar {M : Machine Γ Λ} {Stack : Type*}
    (spec : CarryCounterSpec M Stack) (n : ℕ) {s : Stack} (hs : spec.ValidStack s) :
    (spec.evalCounter s) [M]⊢* spec.evalCounter (spec.iter n s) := by
  induction n generalizing s with
  | zero => exact Counter.stepStar_refl M (spec.evalCounter s)
  | succ n ih =>
    exact Counter.stepStar_trans
      (Counter.stepPlus_stepStar (spec.step_inc s hs))
      (ih (spec.inc_valid s hs))

/-- Valuation growth forces all macro-iterates `spec.iter n spec.s₀` to be pairwise distinct
    (ruling out finite periodic attractors). -/
theorem CarryCounterSpec.iter_injective {M : Machine Γ Λ} {Stack : Type*}
    (spec : CarryCounterSpec M Stack) :
    Function.Injective (fun n => spec.iter n spec.s₀) := by
  intro m n hmn
  dsimp only at hmn
  have hm := spec.iter_val m spec.valid_init
  have hn := spec.iter_val n spec.valid_init
  rw [hmn] at hm
  omega

/-- Every valid `CarryCounterSpec` certifies `IsDoesNotHalt M`. -/
theorem does_not_halt_of_carry_counter {M : Machine Γ Λ} {Stack : Type*}
    (spec : CarryCounterSpec M Stack) :
    IsDoesNotHalt M := by
  refine Counter.does_not_halt_of_invariant
    (fun cfg => ∃ s, spec.ValidStack s ∧ cfg = spec.evalCounter s) ?_ ?_
  · exact ⟨spec.evalCounter spec.s₀, spec.init_reaches, spec.s₀, spec.valid_init, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨spec.evalCounter (spec.inc s), spec.step_inc s hs, spec.inc s, spec.inc_valid s hs, rfl⟩

end AbstractCarryCounter

-- ============================================================================
-- 2. Finite-State Mealy Carry-Transducer Algebra (`MealyCarrySpec`)
-- ============================================================================

section MealyCarryAlgebra

/-- LSB-first mixed-radix positional valuation `∑ᵢ dᵢ · ∏_{j < i} radix(dⱼ)`. -/
def evalMixedRadix {Digit : Type*} (radix digitVal : Digit → ℕ) : List Digit → ℕ
  | [] => 0
  | d :: ds => digitVal d + radix d * evalMixedRadix radix digitVal ds

@[scoped simp]
theorem evalMixedRadix_nil {Digit : Type*} (radix digitVal : Digit → ℕ) :
    evalMixedRadix radix digitVal [] = 0 := rfl

@[scoped simp]
theorem evalMixedRadix_cons {Digit : Type*} (radix digitVal : Digit → ℕ)
    (d : Digit) (ds : List Digit) :
    evalMixedRadix radix digitVal (d :: ds) =
      digitVal d + radix d * evalMixedRadix radix digitVal ds := rfl

/--
Finite-state Mealy carry-transducer specification over digit alphabet `Digit` and
non-zero carry state alphabet `Carry`:
- Each digit `d` has local base `radix d ≥ 2` and value `digitVal d < radix d`.
- Each carry state `c : Carry` carries positive integer weight `carryVal c ≥ 1`,
  with initial increment carry `carryVal c₀ = 1`.
- `stepDigit c d` either:
  * absorbs the carry (`(d', none)`), preserving `radix` and satisfying
    `digitVal d + carryVal c = digitVal d'`, or
  * propagates a carry `c'` (`(d', some c')`), preserving `radix` and satisfying
    `digitVal d + carryVal c = digitVal d' + radix d * carryVal c'`.
- `overflow c` extends the MSB end at `[]` with digits of total value `carryVal c`.
-/
structure MealyCarrySpec (Digit Carry : Type*) where
  radix : Digit → ℕ
  digitVal : Digit → ℕ
  carryVal : Carry → ℕ
  c₀ : Carry
  stepDigit : Carry → Digit → Digit × Option Carry
  overflow : Carry → List Digit
  radix_ge_two : ∀ d, 2 ≤ radix d
  digitVal_lt : ∀ d, digitVal d < radix d
  carryVal_pos : ∀ c, 1 ≤ carryVal c
  carryVal_init : carryVal c₀ = 1
  stepDigit_absorb : ∀ c d d',
    stepDigit c d = (d', none) →
      radix d' = radix d ∧ digitVal d + carryVal c = digitVal d'
  stepDigit_prop : ∀ c d d' c',
    stepDigit c d = (d', some c') →
      radix d' = radix d ∧ digitVal d + carryVal c = digitVal d' + radix d * carryVal c'
  overflow_val : ∀ c, evalMixedRadix radix digitVal (overflow c) = carryVal c
  overflow_nonempty : ∀ c, overflow c ≠ []

/-- Runs the Mealy carry transducer from carry `c` across digit stack `ds`. -/
def runMealyCarry {Digit Carry : Type*} (spec : MealyCarrySpec Digit Carry) :
    Carry → List Digit → List Digit
  | c, [] => spec.overflow c
  | c, d :: ds =>
      match spec.stepDigit c d with
      | (d', none) => d' :: ds
      | (d', some c') => d' :: runMealyCarry spec c' ds

/-- Full `+1` Mealy increment on `List Digit` starting from initial carry `spec.c₀`. -/
def mealyInc {Digit Carry : Type*} (spec : MealyCarrySpec Digit Carry)
    (ds : List Digit) : List Digit :=
  runMealyCarry spec spec.c₀ ds

@[scoped simp]
theorem runMealyCarry_nil {Digit Carry : Type*} (spec : MealyCarrySpec Digit Carry) (c : Carry) :
    runMealyCarry spec c [] = spec.overflow c := rfl

/-- Universal Mealy carry-conservation law: running carry `c` adds `carryVal c` to
    `evalMixedRadix` on every digit list `ds`. -/
theorem evalMixedRadix_runMealyCarry {Digit Carry : Type*}
    (spec : MealyCarrySpec Digit Carry) (c : Carry) (ds : List Digit) :
    evalMixedRadix spec.radix spec.digitVal (runMealyCarry spec c ds) =
      evalMixedRadix spec.radix spec.digitVal ds + spec.carryVal c := by
  induction ds generalizing c with
  | nil =>
    simp [runMealyCarry, spec.overflow_val]
  | cons d tail ih =>
    unfold runMealyCarry
    cases hstep : spec.stepDigit c d with
    | mk d' optC =>
      cases optC with
      | none =>
        rcases spec.stepDigit_absorb c d d' hstep with ⟨hrad, hval⟩
        simp only [evalMixedRadix_cons, hrad]
        linarith
      | some c' =>
        rcases spec.stepDigit_prop c d d' c' hstep with ⟨hrad, hval⟩
        simp only [evalMixedRadix_cons, hrad, ih c']
        ring_nf
        linarith

/-- Universal Mealy increment theorem: `mealyInc` strictly increments `evalMixedRadix` by `1`
    for **every** digit stack `ds : List Digit`. -/
theorem evalMixedRadix_mealyInc {Digit Carry : Type*}
    (spec : MealyCarrySpec Digit Carry) (ds : List Digit) :
    evalMixedRadix spec.radix spec.digitVal (mealyInc spec ds) =
      evalMixedRadix spec.radix spec.digitVal ds + 1 := by
  unfold mealyInc
  rw [evalMixedRadix_runMealyCarry, spec.carryVal_init]

/-- Monotonicity of stack length under `runMealyCarry` (length either stays fixed on
    absorption or grows by `(overflow c').length ≥ 1` on full-stack overflow). -/
theorem length_le_runMealyCarry {Digit Carry : Type*}
    (spec : MealyCarrySpec Digit Carry) (c : Carry) (ds : List Digit) :
    ds.length ≤ (runMealyCarry spec c ds).length := by
  induction ds generalizing c with
  | nil => simp
  | cons d tail ih =>
    unfold runMealyCarry
    cases hstep : spec.stepDigit c d with
    | mk d' optC =>
      cases optC with
      | none => simp
      | some c' =>
        simp only [List.length_cons]
        exact Nat.succ_le_succ (ih c')

/-- Convenience constructor for standard fixed-base `B ≥ 2` single-carry (`Carry = Unit`)
    odometers (binary `B = 2`, ternary `B = 3`, quaternary `B = 4`, etc.). -/
def fixedBaseCarrySpec {Digit : Type*} (B : ℕ) (hB : 2 ≤ B)
    (digitVal : Digit → ℕ) (h_lt : ∀ d, digitVal d < B)
    (incDigit : Digit → Digit × Bool)
    (d_one : Digit) (h_one : digitVal d_one = 1)
    (h_absorb : ∀ d d', incDigit d = (d', false) → digitVal d + 1 = digitVal d')
    (h_prop : ∀ d d', incDigit d = (d', true) → digitVal d + 1 = B ∧ digitVal d' = 0) :
    MealyCarrySpec Digit Unit where
  radix := fun _ => B
  digitVal := digitVal
  carryVal := fun _ => 1
  c₀ := ()
  stepDigit := fun _ d =>
    match incDigit d with
    | (d', false) => (d', none)
    | (d', true) => (d', some ())
  overflow := fun _ => [d_one]
  radix_ge_two := fun _ => hB
  digitVal_lt := h_lt
  carryVal_pos := fun _ => le_rfl
  carryVal_init := rfl
  stepDigit_absorb := by
    intro _ d d' h
    cases h_inc : incDigit d with
    | mk d₁ b =>
      rw [h_inc] at h
      cases b with
      | false =>
        injection h with hd _
        subst hd
        exact ⟨rfl, h_absorb d d₁ h_inc⟩
      | true => nomatch h
  stepDigit_prop := by
    intro _ d d' _ h
    cases h_inc : incDigit d with
    | mk d₁ b =>
      rw [h_inc] at h
      cases b with
      | false => nomatch h
      | true =>
        injection h with hd _
        subst hd
        rcases h_prop d d₁ h_inc with ⟨h1, h0⟩
        exact ⟨rfl, by omega⟩
  overflow_val := by
    intro _
    simp [evalMixedRadix, h_one]
  overflow_nonempty := fun _ => List.cons_ne_nil d_one []

end MealyCarryAlgebra

-- ============================================================================
-- 3. TM Execution Bridge for Mealy Carry Counters (`MealyCarryTMSpec`)
-- ============================================================================

section MealyCarryTMBridge

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Tail-recursive reverse-append (`revAppend scanned rem = scanned.reverse ++ rem`),
    representing the full digit stack when the TM head sits between `scanned` (LSB side,
    reversed) and `rem` (MSB side). -/
def revAppend {α : Type*} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => revAppend xs (x :: ys)

@[scoped simp]
theorem revAppend_nil {α : Type*} (ys : List α) : revAppend [] ys = ys := rfl

@[scoped simp]
theorem revAppend_cons {α : Type*} (x : α) (xs ys : List α) :
    revAppend (x :: xs) ys = revAppend xs (x :: ys) := rfl

/--
Connects a `MealyCarrySpec Digit Carry` to a Post-Turing machine `M`:
- `ValidSuffix scanned rem` is an optional regular/structural invariant on the split
  stack `(scanned, rem)` (use `fun _ _ => True` when all `List Digit` stacks are valid!).
- `hubCfg ds` is the canonical counter hub configuration for stack `ds : List Digit`.
- `carryCfg c scanned rem` is the inward carry-propagation configuration with active
  carry `c`, reversed LSB prefix `scanned`, and remaining MSB suffix `rem`.
- `retCfg scanned rem` is the outward return-sweep configuration walking back across
  `scanned` to `hubCfg`.
- `enter_carry`, `step_prop`, `step_ret`, `exit_ret` require only `[M]⊢*` (`0` or more
  steps), while carry termination (`step_absorb`, `step_overflow`) requires `[M]⊢⁺`
  (`≥ 1` step), so both 1-phase and 2-phase counter hubs fit without dummy steps.
-/
structure MealyCarryTMSpec (M : Machine Γ Λ) (Digit Carry : Type*) where
  mealy : MealyCarrySpec Digit Carry
  ValidDigits : List Digit → Prop := fun _ => True
  ValidSplit : List Digit → List Digit → Prop := fun _ _ => True
  ValidRet : List Digit → List Digit → Prop := fun _ _ => True
  hubCfg : List Digit → Cfg Γ Λ
  carryCfg : Carry → List Digit → List Digit → Cfg Γ Λ
  retCfg : List Digit → List Digit → Cfg Γ Λ
  ds₀ : List Digit
  init_reaches : (init []) [M]⊢* hubCfg ds₀
  valid_init : ValidDigits ds₀
  enter_valid : ∀ ds, ValidDigits ds → ValidSplit [] ds
  absorb_valid : ∀ c scanned d rem d',
    ValidSplit scanned (d :: rem) →
    mealy.stepDigit c d = (d', none) →
    ValidRet scanned (d' :: rem)
  prop_valid : ∀ c scanned d rem d' c',
    ValidSplit scanned (d :: rem) →
    mealy.stepDigit c d = (d', some c') →
    ValidSplit (d' :: scanned) rem
  overflow_valid : ∀ c scanned,
    ValidSplit scanned [] →
    ValidRet scanned (mealy.overflow c)
  ret_step_valid : ∀ d scanned rem,
    ValidRet (d :: scanned) rem →
    ValidRet scanned (d :: rem)
  ret_exit_valid : ∀ ds,
    ValidRet [] ds →
    ValidDigits ds
  enter_carry : ∀ ds, ValidDigits ds → (hubCfg ds) [M]⊢* carryCfg mealy.c₀ [] ds
  step_absorb : ∀ c scanned d rem d',
    ValidSplit scanned (d :: rem) →
    mealy.stepDigit c d = (d', none) →
    (carryCfg c scanned (d :: rem)) [M]⊢⁺ retCfg scanned (d' :: rem)
  step_prop : ∀ c scanned d rem d' c',
    ValidSplit scanned (d :: rem) →
    mealy.stepDigit c d = (d', some c') →
    (carryCfg c scanned (d :: rem)) [M]⊢* carryCfg c' (d' :: scanned) rem
  step_overflow : ∀ c scanned,
    ValidSplit scanned [] →
    (carryCfg c scanned []) [M]⊢⁺ retCfg scanned (mealy.overflow c)
  step_ret : ∀ d scanned rem,
    ValidRet (d :: scanned) rem →
    (retCfg (d :: scanned) rem) [M]⊢* retCfg scanned (d :: rem)
  exit_ret : ∀ ds,
    ValidRet [] ds →
    (retCfg [] ds) [M]⊢* hubCfg ds

/-- Outward return sweep from `retCfg scanned rem` back to `hubCfg (revAppend scanned rem)`. -/
theorem MealyCarryTMSpec.ret_sweep {M : Machine Γ Λ} {Digit Carry : Type*}
    (spec : MealyCarryTMSpec M Digit Carry) :
    ∀ (scanned rem : List Digit),
      spec.ValidRet scanned rem →
      spec.ValidDigits (revAppend scanned rem) ∧
        ((spec.retCfg scanned rem) [M]⊢* spec.hubCfg (revAppend scanned rem))
  | [], rem, hret => ⟨spec.ret_exit_valid rem hret, spec.exit_ret rem hret⟩
  | d :: scanned, rem, hret => by
      have h1 := spec.step_ret d scanned rem hret
      rcases spec.ret_sweep scanned (d :: rem) (spec.ret_step_valid d scanned rem hret) with
        ⟨hvalid, h2⟩
      exact ⟨hvalid, Counter.stepStar_trans h1 h2⟩

/-- Inward Mealy carry cascade + outward return sweep preserves `ValidDigits` and advances
    in `[M]⊢⁺` (`≥ 1` raw TM step). -/
theorem MealyCarryTMSpec.carry_sweep {M : Machine Γ Λ} {Digit Carry : Type*}
    (spec : MealyCarryTMSpec M Digit Carry) :
    ∀ (c : Carry) (scanned rem : List Digit),
      spec.ValidSplit scanned rem →
      spec.ValidDigits (revAppend scanned (runMealyCarry spec.mealy c rem)) ∧
        ((spec.carryCfg c scanned rem) [M]⊢⁺
          spec.hubCfg (revAppend scanned (runMealyCarry spec.mealy c rem)))
  | c, scanned, [], hsplit => by
      have h1 := spec.step_overflow c scanned hsplit
      rcases spec.ret_sweep scanned (spec.mealy.overflow c) (spec.overflow_valid c scanned hsplit)
        with ⟨hvalid, h2⟩
      exact ⟨hvalid, Counter.stepPlus_stepStar_stepPlus h1 h2⟩
  | c, scanned, d :: rem, hsplit => by
      unfold runMealyCarry
      cases hstep : spec.mealy.stepDigit c d with
      | mk d' optC =>
        cases optC with
        | none =>
          have h1 := spec.step_absorb c scanned d rem d' hsplit hstep
          rcases spec.ret_sweep scanned (d' :: rem)
            (spec.absorb_valid c scanned d rem d' hsplit hstep) with ⟨hvalid, h2⟩
          exact ⟨hvalid, Counter.stepPlus_stepStar_stepPlus h1 h2⟩
        | some c' =>
          have hsplit' := spec.prop_valid c scanned d rem d' c' hsplit hstep
          have h1 := spec.step_prop c scanned d rem d' c' hsplit hstep
          rcases spec.carry_sweep c' (d' :: scanned) rem hsplit' with ⟨hvalid, h2⟩
          exact ⟨hvalid, Counter.stepStar_stepPlus_stepPlus h1 h2⟩

/-- Full Mealy increment cycle `(hubCfg ds) [M]⊢⁺ hubCfg (mealyInc spec.mealy ds)`. -/
theorem MealyCarryTMSpec.hub_inc {M : Machine Γ Λ} {Digit Carry : Type*}
    (spec : MealyCarryTMSpec M Digit Carry) (ds : List Digit) (hds : spec.ValidDigits ds) :
    spec.ValidDigits (mealyInc spec.mealy ds) ∧
      ((spec.hubCfg ds) [M]⊢⁺ spec.hubCfg (mealyInc spec.mealy ds)) := by
  have h_enter := spec.enter_carry ds hds
  have h_split := spec.enter_valid ds hds
  rcases spec.carry_sweep spec.mealy.c₀ [] ds h_split with ⟨hvalid, h_sweep⟩
  exact ⟨hvalid, Counter.stepStar_stepPlus_stepPlus h_enter h_sweep⟩

/-- Embeds any `MealyCarryTMSpec` into `CarryCounterSpec` with valuation `evalMixedRadix`. -/
def MealyCarryTMSpec.toCarryCounterSpec {M : Machine Γ Λ} {Digit Carry : Type*}
    (spec : MealyCarryTMSpec M Digit Carry) :
    CarryCounterSpec M (List Digit) where
  ValidStack := spec.ValidDigits
  evalCounter := spec.hubCfg
  inc := mealyInc spec.mealy
  val := evalMixedRadix spec.mealy.radix spec.mealy.digitVal
  s₀ := spec.ds₀
  init_reaches := spec.init_reaches
  valid_init := spec.valid_init
  inc_valid := fun ds hds => (spec.hub_inc ds hds).1
  val_inc := fun ds _ => evalMixedRadix_mealyInc spec.mealy ds
  step_inc := fun ds hds => (spec.hub_inc ds hds).2

/-- Master non-halting theorem for finite-state Mealy carry-transducer Turing machines. -/
theorem does_not_halt_of_mealy_counter {M : Machine Γ Λ} {Digit Carry : Type*}
    (spec : MealyCarryTMSpec M Digit Carry) :
    IsDoesNotHalt M :=
  does_not_halt_of_carry_counter spec.toCarryCounterSpec

end MealyCarryTMBridge

-- ============================================================================
-- 4. Concrete Instantiation: 4-State Binary Odometer Turing Machine
-- ============================================================================


end BusyBeaver.CarryCounter
