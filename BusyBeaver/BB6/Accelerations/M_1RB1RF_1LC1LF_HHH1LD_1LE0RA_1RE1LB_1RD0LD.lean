/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD`.

Each digit stack $S = [s_0, s_1, \dots]$ encodes unary blocks $1^{s_i + 1} 0$ outward from the tape
head (`encStack`). Starting from `init []`, the machine reaches $EL(1, [], 1, [])$ in 5 raw steps,
where:
- $EL(a, L, d, R)$ has state `<E` between `encStack (a :: L)` and `encStack (d :: R)`.
- $E_0(L, R)$ has state `E>` reading `0` between `encStack L` and `encStack (0 :: R)`.

## Accelerated Transition Rules

```text
peelEL(0, R)           = R
peelEL(k + 1, R)       = peelEL(k, 0 :: bumpHead (bumpHead R))

runF(L, [])            = EL(a, L1, 0, [])          where (a, L1) = bumpNE L
runF(L, [0])           = EL(a, L1, 2, [])          where (a, L1) = bumpNE L
runF(L, 0 :: e :: R)   = EL(a, L1, 0, e :: R)      where (a, L1) = bumpNE L
runF(L, 1 :: R)        = runF(0 :: bumpHead L, R)
runF(L, 2 :: R)        = EL(a, L1, d, R1)
                         where (a, L1) = bumpNE (bumpHead (bumpHead L)),
                               (d, R1) = bumpNE (bumpHead R)
runF(L, (d + 3) :: R)  = E0(bumpHead L, d :: R)

runE0([], R)           = runF([0, 0], R)
runE0([0], R)          = runF([0, 1, 0], R)
runE0(0 :: a :: L, R)  = EL(a, L, 0, 1 :: R)
runE0(1 :: L, R)       = runE0(L, 1 :: R)
runE0((a + 2) :: L, R) = EL(a, L, 0, 1 :: R)

E0(L, R)               -> runE0(L, R)
EL(4k, [], d, R)       -> Halt
EL(4k, [0], d, R)      -> EL(1, [], d1 + 2, R2)
EL(4k, 0 :: b :: L, d, R) -> EL(b, L, d1 + 3, R2)
EL(4k, [1], d, R)      -> E0([], d1 :: R2)
EL(4k, 1 :: c :: L, d, R) -> runF(0 :: (c + 1) :: L, d1 :: R2)
EL(4k, (b + 2) :: L, d, R) -> E0(b :: L, d1 :: R2)
  (where R1 = peelEL(k, d :: R) and (d1, R2) = bumpNE R1)
EL(4k + 1, L, d, R)    -> runF(L, bumpHead (bumpHead R1))
EL(4k + 2, [], d, R)   -> E0([], bumpHead (bumpHead R1))
EL(4k + 2, b :: L, d, R) -> EL(b, L, 0, bumpHead (bumpHead R1))
EL(4k + 3, L, d, R)    -> E0(L, bumpHead (bumpHead R1))

Start: EL(1, [], 1, []), reached after 5 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Increment the head digit of `s` and return the non-empty `(head, tail)` decomposition. -/
def bumpNE (s : List ℕ) : ℕ × List ℕ :=
  List.casesOn s (0, []) fun a xs => (a + 1, xs)

/-- Apply `k` stride-4 `<E` peels `R ↦ 0 :: bumpHead (bumpHead R)`. -/
def peelEL (k : ℕ) (R : List ℕ) : List ℕ :=
  ((fun s => 0 :: bumpHead (bumpHead s))^[k]) R

/-- Symbolic state space for the accelerated transition system of `target`. -/
inductive State where
  /-- Left-moving `<E` configuration between `encStack (a :: L)` and `encStack (d :: R)`. -/
  | EL (a : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ)
  /-- Separator `E>` configuration reading `0` between `encStack L` and `encStack (0 :: R)`. -/
  | E0 (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Sweep state `F` across right-stack ones until returning to `EL` or `E0`. -/
def runF : List ℕ → List ℕ → State
  | L, [] =>
    let p := bumpNE L
    .EL p.1 p.2 0 []
  | L, [0] =>
    let p := bumpNE L
    .EL p.1 p.2 2 []
  | L, 0 :: e :: R =>
    let p := bumpNE L
    .EL p.1 p.2 0 (e :: R)
  | L, 1 :: R => runF (0 :: bumpHead L) R
  | L, 2 :: R =>
    let pL := bumpNE (bumpHead (bumpHead L))
    let pR := bumpNE (bumpHead R)
    .EL pL.1 pL.2 pR.1 pR.2
  | L, (d + 3) :: R => .E0 (bumpHead L) (d :: R)

/-- Sweep state `E0` across left-stack ones until returning to `EL` or `runF`. -/
def runE0 : List ℕ → List ℕ → State
  | [], R => runF [0, 0] R
  | [0], R => runF [0, 1, 0] R
  | 0 :: a :: L, R => .EL a L 0 (1 :: R)
  | 1 :: L, R => runE0 L (1 :: R)
  | (a + 2) :: L, R => .EL a L 0 (1 :: R)

/-- Initial symbolic state `EL(1, [], 1, [])`, reached from `init []` in 5 raw steps. -/
def start : State := .EL 1 [] 1 []

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .EL a L d R => Cfg.headLeft E (encStack (a :: L)) (encStack (d :: R))
  | .E0 L R => Cfg.headRight E (encStack L) (ListBlank.cons 0 (encStack (0 :: R)))

/-- Accelerated transition function (`none` indicates halting, reached at `EL(4k, [], d, R)`). -/
def next : State → Option State
  | .E0 L R => some (runE0 L R)
  | .EL a L d R =>
    let R₁ := peelEL (a / 4) (d :: R)
    if a % 4 = 0 then
      match L with
      | [] => none
      | [0] =>
        let p := bumpNE R₁
        some (.EL 1 [] (p.1 + 2) p.2)
      | 0 :: b :: L' =>
        let p := bumpNE R₁
        some (.EL b L' (p.1 + 3) p.2)
      | [1] =>
        let p := bumpNE R₁
        some (.E0 [] (p.1 :: p.2))
      | 1 :: c :: L' =>
        let p := bumpNE R₁
        some (runF (0 :: (c + 1) :: L') (p.1 :: p.2))
      | (b + 2) :: L' =>
        let p := bumpNE R₁
        some (.E0 (b :: L') (p.1 :: p.2))
    else if a % 4 = 1 then
      some (runF L (bumpHead (bumpHead R₁)))
    else if a % 4 = 2 then
      let R₂ := bumpHead (bumpHead R₁)
      List.casesOn L (some (.E0 [] R₂)) fun b L' => some (.EL b L' 0 R₂)
    else
      some (.E0 L (bumpHead (bumpHead R₁)))

/-! ## Stack Encoding Helpers and Intermediate Configurations -/

private theorem encStack_cons_one (s : List ℕ) :
    ListBlank.cons 1 (encStack s) = encStack (bumpHead s) := by
  cases s with
  | nil => simp [bumpHead, encStack]
  | cons a s' => rfl

private theorem cons_bumpNE (s : List ℕ) : (bumpNE s).1 :: (bumpNE s).2 = bumpHead s := by
  cases s <;> rfl

private def cfgEL (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encStack L) <{{E}} (encStack R)

private def cfgE (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgF (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F (encStack L) (ListBlank.cons 0 (encStack R))

/-! ## `runF` and `runE0` Sweep Simulations -/

private theorem rule_F_nil (L : List ℕ) :
    (cfgF L []) [target]⊢⁺ encode (.EL (bumpNE L).1 (bumpNE L).2 0 []) := by
  cases L <;>
    simp only [cfgF, encode, bumpNE, encStack, list_pow_succ, list_pow_zero,
      ListBlank.cons_zero_default] <;>
    bb_steps

private theorem rule_F_zero_nil (L : List ℕ) :
    (cfgF L [0]) [target]⊢⁺ encode (.EL (bumpNE L).1 (bumpNE L).2 2 []) := by
  cases L <;>
    simp only [cfgF, encode, bumpNE, encStack, list_pow_succ, list_pow_zero,
      ListBlank.cons_zero_default] <;>
    bb_steps

private theorem rule_F_zero_cons (L : List ℕ) (e : ℕ) (R : List ℕ) :
    (cfgF L (0 :: e :: R)) [target]⊢⁺ encode (.EL (bumpNE L).1 (bumpNE L).2 0 (e :: R)) := by
  unfold cfgF
  simp only [encode, cons_bumpNE]
  rw [← encStack_cons_one]
  simp only [encStack, list_pow_succ, list_pow_zero]
  bb_steps

private theorem rule_F_one (L R : List ℕ) :
    (cfgF L (1 :: R)) [target]⊢⁺ cfgF (0 :: bumpHead L) R := by
  unfold cfgF
  simp only [encStack, list_pow_succ, list_pow_zero]
  rw [← encStack_cons_one]
  bb_steps

private theorem rule_F_two (L R : List ℕ) :
    (cfgF L (2 :: R)) [target]⊢⁺
      encode (.EL (bumpNE (bumpHead (bumpHead L))).1 (bumpNE (bumpHead (bumpHead L))).2
        (bumpNE (bumpHead R)).1 (bumpNE (bumpHead R)).2) := by
  have h1 :
      (cfgF L (2 :: R)) [target]⊢⁺
        cfgE (bumpHead L) (bumpHead (bumpHead (bumpHead R))) := by
    unfold cfgF cfgE
    simp only [encStack, list_pow_succ, list_pow_zero]
    rw [← encStack_cons_one, ← encStack_cons_one, ← encStack_cons_one, ← encStack_cons_one]
    bb_steps
  have h2 :
      (cfgE (bumpHead L) (bumpHead (bumpHead (bumpHead R)))) [target]⊢⁺
        encode (.EL (bumpNE (bumpHead (bumpHead L))).1 (bumpNE (bumpHead (bumpHead L))).2
          (bumpNE (bumpHead R)).1 (bumpNE (bumpHead R)).2) := by
    cases L <;> cases R <;>
      simp only [cfgE, encode, bumpNE, bumpHead, encStack, list_pow_succ, list_pow_zero,
        ListBlank.cons_zero_default] <;>
      bb_steps
  exact h1.trans h2

private theorem rule_F_ge3 (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfgF L ((d + 3) :: R)) [target]⊢⁺ encode (.E0 (bumpHead L) (d :: R)) := by
  unfold cfgF encode
  simp only [encStack]
  have hd : d + 3 + 1 = 3 + (d + 1) := by omega
  rw [hd, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (d + 1), ← encStack_cons_one]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem reaches_runF :
    ∀ (L R : List ℕ), (cfgF L R) [target]⊢⁺ encode (runF L R)
  | L, [] => rule_F_nil L
  | L, [0] => rule_F_zero_nil L
  | L, 0 :: e :: R => rule_F_zero_cons L e R
  | L, 1 :: R => (rule_F_one L R).trans (reaches_runF (0 :: bumpHead L) R)
  | L, 2 :: R => rule_F_two L R
  | L, (d + 3) :: R => rule_F_ge3 L d R

private theorem rule_E0_nil (R : List ℕ) :
    (encode (.E0 [] R)) [target]⊢⁺ cfgF [0, 0] R := by
  have h1 : (encode (.E0 [] R)) [target]⊢⁺ cfgF [] (1 :: R) := by
    unfold encode cfgF
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  exact h1.trans (rule_F_one [] R)

private theorem rule_E0_zero_nil (R : List ℕ) :
    (encode (.E0 [0] R)) [target]⊢⁺ cfgF [0, 1, 0] R := by
  have h1 : (encode (.E0 [0] R)) [target]⊢⁺ encode (.E0 [] (1 :: R)) := by
    unfold encode
    simp only [encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default]
    bb_steps
  exact (h1.trans (rule_E0_nil (1 :: R))).trans (rule_F_one [0, 0] R)

private theorem rule_E0_zero_cons (a : ℕ) (L R : List ℕ) :
    (encode (.E0 (0 :: a :: L) R)) [target]⊢⁺ encode (.EL a L 0 (1 :: R)) := by
  unfold encode
  simp only [encStack, list_pow_succ, list_pow_zero]
  bb_steps

private theorem rule_E0_one (L R : List ℕ) :
    (encode (.E0 (1 :: L) R)) [target]⊢⁺ encode (.E0 L (1 :: R)) := by
  unfold encode
  simp only [encStack, list_pow_succ, list_pow_zero]
  bb_steps

private theorem rule_E0_ge2 (a : ℕ) (L R : List ℕ) :
    (encode (.E0 ((a + 2) :: L) R)) [target]⊢⁺ encode (.EL a L 0 (1 :: R)) := by
  unfold encode
  simp only [encStack]
  have ha : a + 2 + 1 = 2 + (a + 1) := by omega
  rw [ha, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (a + 1)]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem reaches_runE0 :
    ∀ (L R : List ℕ), (encode (.E0 L R)) [target]⊢⁺ encode (runE0 L R)
  | [], R => (rule_E0_nil R).trans (reaches_runF [0, 0] R)
  | [0], R => (rule_E0_zero_nil R).trans (reaches_runF [0, 1, 0] R)
  | 0 :: a :: L, R => rule_E0_zero_cons a L R
  | 1 :: L, R => (rule_E0_one L R).trans (reaches_runE0 L (1 :: R))
  | (a + 2) :: L, R => rule_E0_ge2 a L R

/-! ## `<E` Stride-4 Peel and Remainder Dispatch -/

private theorem rule_EL_add_four (a : ℕ) (L R : List ℕ) :
    (cfgEL ((a + 4) :: L) R) [target]⊢⁺ cfgEL (a :: L) (0 :: bumpHead (bumpHead R)) := by
  unfold cfgEL
  simp only [encStack]
  have ha : a + 4 + 1 = 4 + (a + 1) := by omega
  rw [ha, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 (a + 1),
    ← encStack_cons_one, ← encStack_cons_one]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem peel_EL_four (k r₀ : ℕ) (L R : List ℕ) :
    (cfgEL ((4 * k + r₀) :: L) R) [target]⊢* cfgEL (r₀ :: L) (peelEL k R) := by
  induction k generalizing R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, peelEL]
    bb_refl
  | succ k ih =>
    have hk : 4 * (k + 1) + r₀ = (4 * k + r₀) + 4 := by omega
    rw [hk]
    exact (rule_EL_add_four (4 * k + r₀) L R).to_star.trans (ih (0 :: bumpHead (bumpHead R)))

private theorem halt_EL_zero_nil (R₁ : List ℕ) :
    ∃ cfg', ((cfgEL [0] R₁) [target]⊢* cfg') ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headLeft C default ([1, 1] +> encStack R₁), ?_, by bb_halt⟩
  unfold cfgEL
  simp only [encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default]
  bb_steps

private theorem step_EL_zero_zero_nil (R₁ : List ℕ) :
    (cfgEL [0, 0] R₁) [target]⊢⁺ encode (.EL 1 [] ((bumpNE R₁).1 + 2) (bumpNE R₁).2) := by
  have h1 :
      (cfgEL [0, 0] R₁) [target]⊢⁺
        cfgE [] (((bumpNE R₁).1 + 3) :: (bumpNE R₁).2) := by
    unfold cfgEL cfgE
    have hR : bumpHead (bumpHead (bumpHead (bumpHead R₁))) =
        ((bumpNE R₁).1 + 3) :: (bumpNE R₁).2 := by
      rw [← cons_bumpNE R₁]
      rfl
    rw [← hR, ← encStack_cons_one, ← encStack_cons_one, ← encStack_cons_one, ← encStack_cons_one]
    simp only [encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default]
    bb_steps
  have h2 :
      (cfgE [] (((bumpNE R₁).1 + 3) :: (bumpNE R₁).2)) [target]⊢⁺
        encode (.EL 1 [] ((bumpNE R₁).1 + 2) (bumpNE R₁).2) := by
    unfold cfgE
    simp only [encode, encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default]
    bb_steps
  exact h1.trans h2

private theorem step_EL_zero_zero_cons (b : ℕ) (L' R₁ : List ℕ) :
    (cfgEL (0 :: 0 :: b :: L') R₁) [target]⊢⁺
      encode (.EL b L' ((bumpNE R₁).1 + 3) (bumpNE R₁).2) := by
  unfold cfgEL
  simp only [encode]
  have hR : bumpHead (bumpHead (bumpHead (bumpHead R₁))) =
      ((bumpNE R₁).1 + 3) :: (bumpNE R₁).2 := by
    rw [← cons_bumpNE R₁]
    rfl
  rw [← hR, ← encStack_cons_one, ← encStack_cons_one, ← encStack_cons_one, ← encStack_cons_one]
  simp only [encStack, list_pow_succ, list_pow_zero]
  bb_steps

private theorem step_EL_zero_one_nil (R₁ : List ℕ) :
    (cfgEL [0, 1] R₁) [target]⊢⁺ encode (.E0 [] ((bumpNE R₁).1 :: (bumpNE R₁).2)) := by
  unfold cfgEL
  simp only [encode, cons_bumpNE]
  cases R₁ <;>
    simp only [bumpHead, encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default] <;>
    bb_steps

private theorem step_EL_zero_one_cons (c : ℕ) (L' R₁ : List ℕ) :
    (cfgEL (0 :: 1 :: c :: L') R₁) [target]⊢⁺
      encode (runF (0 :: (c + 1) :: L') ((bumpNE R₁).1 :: (bumpNE R₁).2)) := by
  have h1 :
      (cfgEL (0 :: 1 :: c :: L') R₁) [target]⊢⁺
        cfgF (c :: L') (1 :: (bumpNE R₁).1 :: (bumpNE R₁).2) := by
    unfold cfgEL cfgF
    rw [cons_bumpNE]
    cases R₁ <;>
      simp only [bumpHead, encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default] <;>
      bb_steps
  exact (h1.trans (rule_F_one (c :: L') ((bumpNE R₁).1 :: (bumpNE R₁).2))).trans
    (reaches_runF (0 :: (c + 1) :: L') ((bumpNE R₁).1 :: (bumpNE R₁).2))

private theorem step_EL_zero_ge2 (b : ℕ) (L' R₁ : List ℕ) :
    (cfgEL (0 :: (b + 2) :: L') R₁) [target]⊢⁺
      encode (.E0 (b :: L') ((bumpNE R₁).1 :: (bumpNE R₁).2)) := by
  unfold cfgEL
  simp only [encode, cons_bumpNE]
  have hb : b + 2 + 1 = 2 + (b + 1) := by omega
  cases R₁ <;>
    simp only [bumpHead, encStack] <;>
    rw [hb, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (b + 1)] <;>
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil, ListBlank.cons_zero_default] <;>
    bb_steps

private theorem step_EL_one (L R₁ : List ℕ) :
    (cfgEL (1 :: L) R₁) [target]⊢⁺ encode (runF L (bumpHead (bumpHead R₁))) := by
  have h1 : (cfgEL (1 :: L) R₁) [target]⊢⁺ cfgF L (bumpHead (bumpHead R₁)) := by
    unfold cfgEL cfgF
    simp only [encStack, list_pow_succ, list_pow_zero]
    rw [← encStack_cons_one, ← encStack_cons_one]
    bb_steps
  exact h1.trans (reaches_runF L (bumpHead (bumpHead R₁)))

private theorem step_EL_two_nil (R₁ : List ℕ) :
    (cfgEL [2] R₁) [target]⊢⁺ encode (.E0 [] (bumpHead (bumpHead R₁))) := by
  unfold cfgEL
  simp only [encode, encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default]
  rw [← encStack_cons_one, ← encStack_cons_one]
  bb_steps

private theorem step_EL_two_cons (b : ℕ) (L' R₁ : List ℕ) :
    (cfgEL (2 :: b :: L') R₁) [target]⊢⁺ encode (.EL b L' 0 (bumpHead (bumpHead R₁))) := by
  unfold cfgEL
  simp only [encode, encStack, list_pow_succ, list_pow_zero]
  rw [← encStack_cons_one, ← encStack_cons_one]
  bb_steps

private theorem step_EL_three (L R₁ : List ℕ) :
    (cfgEL (3 :: L) R₁) [target]⊢⁺ encode (.E0 L (bumpHead (bumpHead R₁))) := by
  unfold cfgEL
  simp only [encode, encStack, list_pow_succ, list_pow_zero]
  rw [← encStack_cons_one, ← encStack_cons_one]
  bb_steps

private theorem init_reaches_start : (init []) [target]⊢* encode start := by
  simp only [start, encode, encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default]
  bb_steps

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start (fun s => ?_)
  rcases s with ⟨a, L, d, R⟩ | ⟨L, R⟩
  · let R₁ := peelEL (a / 4) (d :: R)
    by_cases h0 : a % 4 = 0
    · have ha : a = 4 * (a / 4) + 0 := by omega
      have hpeel : (encode (.EL a L d R)) [target]⊢* cfgEL (0 :: L) R₁ := by
        simpa [encode, cfgEL, ← ha, R₁] using peel_EL_four (a / 4) 0 L (d :: R)
      rcases L with _ | ⟨_ | _ | b, L'⟩
      · simp only [next, h0, ↓reduceIte]
        obtain ⟨cfg', hstar, hnone⟩ := halt_EL_zero_nil R₁
        exact ⟨cfg', hpeel.trans hstar, hnone⟩
      · rcases L' with _ | ⟨b, L''⟩
        · simp only [next, h0, ↓reduceIte]
          exact hpeel.trans_plus (step_EL_zero_zero_nil R₁)
        · simp only [next, h0, ↓reduceIte]
          exact hpeel.trans_plus (step_EL_zero_zero_cons b L'' R₁)
      · rcases L' with _ | ⟨c, L''⟩
        · simp only [next, h0, ↓reduceIte]
          exact hpeel.trans_plus (step_EL_zero_one_nil R₁)
        · simp only [next, h0, ↓reduceIte]
          exact hpeel.trans_plus (step_EL_zero_one_cons c L'' R₁)
      · simp only [next, h0, ↓reduceIte]
        exact hpeel.trans_plus (step_EL_zero_ge2 b L' R₁)
    · by_cases h1 : a % 4 = 1
      · have ha : a = 4 * (a / 4) + 1 := by omega
        have hpeel : (encode (.EL a L d R)) [target]⊢* cfgEL (1 :: L) R₁ := by
          simpa [encode, cfgEL, ← ha, R₁] using peel_EL_four (a / 4) 1 L (d :: R)
        simp only [next, h1, ↓reduceIte]
        exact hpeel.trans_plus (step_EL_one L R₁)
      · by_cases h2 : a % 4 = 2
        · have ha : a = 4 * (a / 4) + 2 := by omega
          have hpeel : (encode (.EL a L d R)) [target]⊢* cfgEL (2 :: L) R₁ := by
            simpa [encode, cfgEL, ← ha, R₁] using peel_EL_four (a / 4) 2 L (d :: R)
          rcases L with _ | ⟨b, L'⟩
          · simp only [next, h2, ↓reduceIte]
            exact hpeel.trans_plus (step_EL_two_nil R₁)
          · simp only [next, h2, ↓reduceIte]
            exact hpeel.trans_plus (step_EL_two_cons b L' R₁)
        · have ha : a = 4 * (a / 4) + 3 := by omega
          have hpeel : (encode (.EL a L d R)) [target]⊢* cfgEL (3 :: L) R₁ := by
            simpa [encode, cfgEL, ← ha, R₁] using peel_EL_four (a / 4) 3 L (d :: R)
          simp only [next, h0, h1, h2, ↓reduceIte]
          exact hpeel.trans_plus (step_EL_three L R₁)
  · simp only [next]
    exact reaches_runE0 L R

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD
