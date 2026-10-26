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

Eliminating the auxiliary mode $E_0$ and contracting the `runF`/$E_0$ bounce loop yields a
single-mode transition system $EL_{\mathrm{HL}}(a, L, d, R) := EL(a, L, d, R)$ starting at
$EL_{\mathrm{HL}}(1, [], 1, [])$.
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

/-! ## High-Level Acceleration -/

/-- Reduced single-mode state space $EL_{\mathrm{HL}}(a, L, d, R) := EL(a, L, d, R)$ obtained by
eliminating $E_0$. -/
inductive HighLevelState where
  /-- Left-moving `<E` configuration between `encStack (a :: L)` and `encStack (d :: R)`. -/
  | EL (a : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level state $EL_{\mathrm{HL}}(1, [], 1, [])$, equal to `start`. -/
def highLevelStart : HighLevelState := .EL 1 [] 1 []

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .EL a L d R => .EL a L d R

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Strip all leading `1` digits from `L`, returning `(count, remainder)`. -/
def countOnes (L : List ℕ) : ℕ × List ℕ :=
  List.rec (motive := fun _ => ℕ × List ℕ) (0, [])
    (fun x xs p => if x = 1 then (p.1 + 1, p.2) else (0, x :: xs)) L

/-- Apply `L ↦ 0 :: bumpHead L` `k` times. -/
def pushZeroBump (k : ℕ) (L : List ℕ) : List ℕ :=
  ((fun s => 0 :: bumpHead s)^[k]) L

/-- Contract one non-empty head `r` of `runF L (r :: R')` given `ih = fun L' => runFHL L' R'`. -/
def stepFHead (R' : List ℕ) (ih : List ℕ → HighLevelState) : ℕ → List ℕ → HighLevelState
  | 0, L =>
    let p := bumpNE L
    List.casesOn (motive := fun _ => HighLevelState) R' (.EL p.1 p.2 2 []) fun e R'' =>
      .EL p.1 p.2 0 (e :: R'')
  | 1, L => ih (0 :: bumpHead L)
  | 2, L =>
    let pL := bumpNE (bumpHead (bumpHead L))
    let pR := bumpNE (bumpHead R')
    .EL pL.1 pL.2 pR.1 pR.2
  | d + 3, L =>
    let c := countOnes (bumpHead L)
    List.casesOn (motive := fun _ => HighLevelState) c.2
      (stepFHead R' ih d (pushZeroBump c.1 [0, 0])) fun x Lt =>
        if x = 0 then
          List.casesOn (motive := fun _ => HighLevelState) Lt
            (stepFHead R' ih d (pushZeroBump c.1 [0, 1, 0])) fun a Lt' =>
              .EL a Lt' 0 (1 :: (List.replicate c.1 1 ++ (d :: R')))
        else
          .EL (x - 2) Lt 0 (1 :: (List.replicate c.1 1 ++ (d :: R')))

/-- Contract `runF` together with any subsequent $E_0$/`runF` bounces until reaching `EL`. -/
def runFHL (L R : List ℕ) : HighLevelState :=
  List.rec (motive := fun _ => List ℕ → HighLevelState)
    (fun L =>
      let p := bumpNE L
      .EL p.1 p.2 0 [])
    (fun r R' ih L => stepFHead R' ih r L)
    R L

/-- Contract `runE0` together with any subsequent `runF`/$E_0$ bounces until reaching `EL`. -/
def runE0HL (L R : List ℕ) : HighLevelState :=
  let c := countOnes L
  List.casesOn (motive := fun _ => HighLevelState) c.2
    (runFHL (pushZeroBump c.1 [0, 0]) R) fun x Lt =>
      if x = 0 then
        List.casesOn (motive := fun _ => HighLevelState) Lt
          (runFHL (pushZeroBump c.1 [0, 1, 0]) R) fun a Lt' =>
            .EL a Lt' 0 (1 :: (List.replicate c.1 1 ++ R))
      else
        .EL (x - 2) Lt 0 (1 :: (List.replicate c.1 1 ++ R))

/-- High-level single-mode accelerated transition function on $EL_{\mathrm{HL}}(a, L, d, R)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .EL a L d R =>
    let R₁ := peelEL (a / 4) (d :: R)
    if a % 4 = 0 then
      List.casesOn (motive := fun _ => Option HighLevelState) L none fun b Lp =>
        let p := bumpNE R₁
        if b = 0 then
          List.casesOn (motive := fun _ => Option HighLevelState) Lp
            (some (.EL 1 [] (p.1 + 2) p.2)) fun b' L'' =>
              some (.EL b' L'' (p.1 + 3) p.2)
        else if b = 1 then
          List.casesOn (motive := fun _ => Option HighLevelState) Lp
            (some (runE0HL [] (p.1 :: p.2))) fun c L'' =>
              some (runFHL (0 :: (c + 1) :: L'') (p.1 :: p.2))
        else
          some (runE0HL ((b - 2) :: Lp) (p.1 :: p.2))
    else
      let R₂ := bumpHead (bumpHead R₁)
      if a % 4 = 1 then
        some (runFHL L R₂)
      else if a % 4 = 2 then
        List.casesOn (motive := fun _ => Option HighLevelState) L
          (some (runE0HL [] R₂)) fun b L' =>
            some (.EL b L' 0 R₂)
      else
        some (runE0HL L R₂)

private theorem countOnes_eq (L : List ℕ) :
    List.replicate (countOnes L).1 1 ++ (countOnes L).2 = L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [countOnes]
    split_ifs with hx
    · subst hx
      exact congrArg (1 :: ·) ih
    · rfl

private theorem countOnes_head_ne_one (L : List ℕ) {x : ℕ} {Lt : List ℕ}
    (h : (countOnes L).2 = x :: Lt) : x ≠ 1 := by
  induction L with
  | nil => simp [countOnes] at h
  | cons y ys ih =>
    simp only [countOnes] at h
    split_ifs at h with hy
    · exact ih h
    · injection h with hxy _
      rintro rfl
      exact hy hxy

private theorem runE0_replicate_ones (k : ℕ) (Lrem R : List ℕ) :
    runE0 (List.replicate k 1 ++ Lrem) R = runE0 Lrem (List.replicate k 1 ++ R) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    conv_lhs => rw [List.replicate_succ, List.cons_append, runE0, ih]
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]

private theorem runF_replicate_ones (k : ℕ) (L R : List ℕ) :
    runF L (List.replicate k 1 ++ R) = runF (pushZeroBump k L) R := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, runF, ih]
    rfl

private theorem reachesPlus_E0_of_runF (L₀ R₀ : List ℕ)
    (hF : ∀ L', CollatzReachesStar next (runF L' R₀) (toState (runFHL L' R₀))) :
    CollatzReachesPlus next (.E0 L₀ R₀) (toState (runE0HL L₀ R₀)) := by
  have hstep : next (.E0 L₀ R₀) = some (runE0 L₀ R₀) := rfl
  have hpeel : runE0 L₀ R₀ =
      runE0 (countOnes L₀).2 (List.replicate (countOnes L₀).1 1 ++ R₀) := by
    conv_lhs => rw [← countOnes_eq L₀]
    exact runE0_replicate_ones (countOnes L₀).1 (countOnes L₀).2 R₀
  rw [hpeel] at hstep
  dsimp only [runE0HL]
  rcases hc : (countOnes L₀).2 with _ | ⟨x, Lt⟩
  · rw [hc, runE0, runF_replicate_ones] at hstep
    exact CollatzReachesPlus.head hstep (hF _)
  · have hx1 : x ≠ 1 := countOnes_head_ne_one L₀ hc
    dsimp only
    rw [hc] at hstep
    split_ifs with hx0
    · subst hx0
      rcases Lt with _ | ⟨a, Lt'⟩
      · rw [runE0, runF_replicate_ones] at hstep
        exact CollatzReachesPlus.head hstep (hF _)
      · rw [runE0] at hstep
        exact CollatzReachesPlus.single hstep
    · have hx2 : x = (x - 2) + 2 := by omega
      rw [hx2, runE0] at hstep
      exact CollatzReachesPlus.single hstep

private theorem reachesStar_runFHL (L R : List ℕ) :
    CollatzReachesStar next (runF L R) (toState (runFHL L R)) := by
  induction R generalizing L with
  | nil => exact CollatzReachesStar.refl next _
  | cons r R' ih_R =>
    induction r using Nat.strong_induction_on generalizing L with
    | h r ih_r =>
      rcases r with _ | _ | _ | d
      · rcases R' with _ | ⟨e, R''⟩ <;> exact CollatzReachesStar.refl next _
      · exact ih_R (0 :: bumpHead L)
      · exact CollatzReachesStar.refl next _
      · conv_lhs => rw [runF]
        exact (reachesPlus_E0_of_runF (bumpHead L) (d :: R') fun L' =>
          ih_r d (by omega) L').to_star

private theorem reachesPlus_E0 (L R : List ℕ) :
    CollatzReachesPlus next (.E0 L R) (toState (runE0HL L R)) :=
  reachesPlus_E0_of_runF L R fun L' => reachesStar_runFHL L' R

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid acceleration of
`target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState)
    (CollatzReachesStar.refl next start) ?_
  rintro ⟨a, L, d, R⟩
  dsimp only [toState, highLevelNext]
  split_ifs with h0 h1 h2
  · rcases L with _ | ⟨b, Lp⟩
    · exact CollatzStepsTo.of_eq (by simp [next, h0])
    · dsimp only
      split_ifs with hb0 hb1
      · subst hb0
        rcases Lp with _ | ⟨b', L''⟩
        · exact CollatzStepsTo.of_eq (by simp [next, h0, toState])
        · exact CollatzStepsTo.of_eq (by simp [next, h0, toState])
      · subst hb1
        rcases Lp with _ | ⟨c, L''⟩
        · exact CollatzReachesPlus.head (by simp [next, h0])
            (reachesPlus_E0 [] _).to_star
        · exact CollatzReachesPlus.head (by simp [next, h0])
            (reachesStar_runFHL (0 :: (c + 1) :: L'') _)
      · have hb2 : b = (b - 2) + 2 := by omega
        refine CollatzReachesPlus.head ?_
          (reachesPlus_E0 ((b - 2) :: Lp) _).to_star
        rw [hb2]
        simp [next, h0]
  · exact CollatzReachesPlus.head (by simp [next, h1])
      (reachesStar_runFHL L _)
  · rcases L with _ | ⟨b, L'⟩
    · exact CollatzReachesPlus.head (by simp [next, h2])
        (reachesPlus_E0 [] _).to_star
    · exact CollatzStepsTo.of_eq (by simp [next, h2, toState])
  · exact CollatzReachesPlus.head (by simp [next, h0, h1, h2])
      (reachesPlus_E0 L _).to_star

/-- `target` halts from the blank tape iff `highLevelNext` halts from `highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- The initial acceleration `next` halts from `start` iff `highLevelNext` halts from
`highLevelStart`. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD
