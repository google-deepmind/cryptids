/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC`.

Each digit stack $S = [s_0, s_1, \dots]$ encodes unary blocks $1^{s_i + 1} 0$ outward from the tape
head (`encStack`). Starting from `init []`, the machine reaches $B([0], 0, [])$ in 8 raw steps,
where
$$B(L, d, R) := \mathrm{encStack}(L)\,\mathrm{B}{>}\,0\,\mathrm{encStack}(d :: R).$$

## Accelerated Transition Rules

```text
cSweepTail([], 2k, R)           = 0^k ++ R
cSweepTail([], 2k + 1, R)       = bump2 (0^k ++ R)
cSweepTail(a1 :: Lp, 2k, R)     = cSweepTail(Lp, a1, bump2 (0^k ++ R))
cSweepTail(a1 :: Lp, 2k + 1, R) = cSweepTail(Lp, a1 + 1, bump2 (0^k ++ R))

runCR1(b, L, [])                = B([], 0, cSweepTail(L, b, [1]))
runCR1(b, L, 0 :: R)            = B((b + 1) :: L, d2, R2)   where (d2, R2) = bump2NE R
runCR1(b, L, 1 :: R)            = runCR1(1, b :: L, R)
runCR1(b, L, [2])               = Halt
runCR1(b, L, 2 :: e :: R)       = B(0 :: 1 :: b :: L, e, R)
runCR1(b, L, (d + 3) :: R)      = B(2 :: b :: L, d, R)

B(L, 3k, R):                    (let L1 = add3 k L)
  L1 = []                       -> B([0], d2, R2)           where (d2, R2) = bump2NE R
  L1 = a0 :: Lp                 -> B([], 0, cSweepTail(Lp, a0, bump2 R))
B(L, 3k + 1, R)                 -> runCR1(b, Lt, R)         where (b, Lt) = bump2NE (add3 k L)
B(L, 3k + 2, [])                -> Halt
B(L, 3k + 2, e :: R')           -> B(0 :: bump2 (add3 k L), e, R')

Start: B([0], 0, []), reached after 8 raw TM steps
```

Restricting to the Poincaré return section $L = [] \land d = 0$ eliminates both the left stack and
the separator counter, yielding a single-stack transition system $B_{\mathrm{HL}}(R) := B([], 0, R)$
starting at $B_{\mathrm{HL}}([1])$.
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_HHH1LC

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Add `2` to the head digit of a stack, or push `1` onto an empty stack. -/
def bump2 (s : List ℕ) : List ℕ :=
  List.casesOn s [1] fun a xs => (a + 2) :: xs

/-- Add `2` to the head digit of `s` and return the non-empty `(head, tail)` decomposition. -/
def bump2NE (s : List ℕ) : ℕ × List ℕ :=
  List.casesOn s (1, []) fun a xs => (a + 2, xs)

/-- Apply `k` stride-3 right-stack peels `L ↦ bumpHead (bumpHead (bumpHead L))`. -/
def add3 (k : ℕ) (L : List ℕ) : List ℕ :=
  ((fun s => bumpHead (bumpHead (bumpHead s)))^[k]) L

/-- Sweep state `C` across `a₀ :: Lp` onto `R`, returning the tail after the leading `0` of `R'`. -/
def cSweepTail : List ℕ → ℕ → List ℕ → List ℕ
  | [], a₀, R =>
    let R₁ := List.replicate (a₀ / 2) 0 ++ R
    if a₀ % 2 = 0 then R₁ else bump2 R₁
  | a₁ :: Lp, a₀, R =>
    let R₂ := bump2 (List.replicate (a₀ / 2) 0 ++ R)
    cSweepTail Lp (if a₀ % 2 = 0 then a₁ else a₁ + 1) R₂

/-- Symbolic state space for the accelerated transition system of `target`. -/
inductive State where
  /-- Separator configuration `B(L, d, R)`: `B>` on `0` between `encStack L` and
  `encStack (d :: R)`. -/
  | B (L : List ℕ) (d : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

/-- Sweep `C>` across right-stack ones from `0 :: b :: L` until returning to `B` or halting. -/
def runCR1 (b : ℕ) (L : List ℕ) : List ℕ → Option State
  | [] => some (.B [] 0 (cSweepTail L b [1]))
  | 0 :: R =>
    let p := bump2NE R
    some (.B ((b + 1) :: L) p.1 p.2)
  | 1 :: R => runCR1 1 (b :: L) R
  | [2] => none
  | 2 :: e :: R => some (.B (0 :: 1 :: b :: L) e R)
  | (d + 3) :: R => some (.B (2 :: b :: L) d R)

/-- Initial symbolic state `B([0], 0, [])`, reached from `init []` in 8 raw steps. -/
def start : State := .B [0] 0 []

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .B L d R => Cfg.headRight B (encStack L) (ListBlank.cons 0 (encStack (d :: R)))

/-- Accelerated transition function (`none` indicates halting via `F0 -> ---`). -/
def next : State → Option State
  | .B L d R =>
    let L₁ := add3 (d / 3) L
    if d % 3 = 0 then
      List.casesOn L₁
        (let p := bump2NE R; some (.B [0] p.1 p.2))
        fun a₀ Lp => some (.B [] 0 (cSweepTail Lp a₀ (bump2 R)))
    else if d % 3 = 1 then
      let p := bump2NE L₁
      runCR1 p.1 p.2 R
    else
      List.casesOn R none fun e R' => some (.B (0 :: bump2 L₁) e R')

/-! ## Stack Encoding Helpers and Intermediate Configurations -/

private theorem encStack_cons_one (s : List ℕ) :
    ListBlank.cons 1 (encStack s) = encStack (bumpHead s) := by
  cases s with
  | nil => simp [bumpHead, encStack]
  | cons a s' => rfl

private theorem bumpHead_bumpHead (s : List ℕ) :
    bumpHead (bumpHead s) = bump2 s := by
  cases s <;> rfl

private theorem cons_bump2NE (s : List ℕ) :
    (bump2NE s).1 :: (bump2NE s).2 = bump2 s := by
  cases s <;> rfl

private def cfgB (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgC (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgCR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encStack L) {{C}}> (encStack R)

private def stepsOrHalts (cfg : Cfg (Fin 2) (Fin 6)) : Option State → Prop
  | some s' => cfg [target]⊢⁺ encode s'
  | none => ∃ cfg', (cfg [target]⊢* cfg') ∧ (step target cfg').isNone

private theorem stepsOrHalts_trans {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {res : Option State}
    (h₁ : c₁ [target]⊢⁺ c₂) (h₂ : stepsOrHalts c₂ res) : stepsOrHalts c₁ res := by
  rcases res with _ | s'
  · obtain ⟨cfg', hstar, hnone⟩ := h₂
    exact ⟨cfg', h₁.to_star.trans hstar, hnone⟩
  · exact h₁.trans h₂

private theorem stepsOrHalts_of_star {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {res : Option State}
    (h₁ : c₁ [target]⊢* c₂) (h₂ : stepsOrHalts c₂ res) : stepsOrHalts c₁ res := by
  rcases res with _ | s'
  · obtain ⟨cfg', hstar, hnone⟩ := h₂
    exact ⟨cfg', h₁.trans hstar, hnone⟩
  · exact h₁.trans_plus h₂

/-! ## `C`-Sweep (`cSweepTail`) Simulation -/

private theorem rule_C_add_two (a : ℕ) (Lp R : List ℕ) :
    (cfgC ((a + 2) :: Lp) R) [target]⊢⁺ cfgC (a :: Lp) (0 :: R) := by
  unfold cfgC
  simp only [encStack]
  have ha : a + 2 + 1 = 2 + (a + 1) := by omega
  rw [ha, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (a + 1)]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem peel_C_two (k r₀ : ℕ) (Lp R : List ℕ) :
    (cfgC ((2 * k + r₀) :: Lp) R) [target]⊢* cfgC (r₀ :: Lp) (List.replicate k 0 ++ R) := by
  induction k generalizing R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, List.replicate, List.nil_append]
    bb_refl
  | succ k ih =>
    have hk : 2 * (k + 1) + r₀ = (2 * k + r₀) + 2 := by omega
    have hrep : List.replicate (k + 1) 0 ++ R = List.replicate k 0 ++ (0 :: R) := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [hk, hrep]
    exact (rule_C_add_two (2 * k + r₀) Lp R).to_star.trans (ih (0 :: R))

private theorem rule_C_zero_nil (R : List ℕ) :
    (cfgC [0] R) [target]⊢⁺ encode (.B [] 0 R) := by
  unfold cfgC
  simp only [encode, encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default]
  bb_steps

private theorem rule_C_one_nil (R : List ℕ) :
    (cfgC [1] R) [target]⊢⁺ encode (.B [] 0 (bump2 R)) := by
  unfold cfgC
  simp only [encode, ← bumpHead_bumpHead, encStack, list_pow_succ, list_pow_zero,
    ListBlank.cons_zero_default]
  rw [← encStack_cons_one, ← encStack_cons_one]
  bb_steps

private theorem rule_C_zero_cons (a₁ : ℕ) (Lp R : List ℕ) :
    (cfgC (0 :: a₁ :: Lp) R) [target]⊢⁺ cfgC (a₁ :: Lp) (bump2 R) := by
  unfold cfgC
  simp only [← bumpHead_bumpHead, encStack, list_pow_succ, list_pow_zero]
  rw [← encStack_cons_one, ← encStack_cons_one]
  bb_steps

private theorem rule_C_one_cons (a₁ : ℕ) (Lp R : List ℕ) :
    (cfgC (1 :: a₁ :: Lp) R) [target]⊢⁺ cfgC ((a₁ + 1) :: Lp) (bump2 R) := by
  unfold cfgC
  simp only [← bumpHead_bumpHead, encStack, list_pow_succ, list_pow_zero]
  rw [← encStack_cons_one, ← encStack_cons_one]
  bb_steps

private theorem reaches_cSweepTail :
    ∀ (Lp : List ℕ) (a₀ : ℕ) (R : List ℕ),
      (cfgC (a₀ :: Lp) R) [target]⊢⁺ encode (.B [] 0 (cSweepTail Lp a₀ R))
  | [], a₀, R => by
    let R₁ := List.replicate (a₀ / 2) 0 ++ R
    by_cases hev : a₀ % 2 = 0
    · simp only [cSweepTail, hev, ↓reduceIte]
      have ha : a₀ = 2 * (a₀ / 2) + 0 := by omega
      have hpeel := peel_C_two (a₀ / 2) 0 [] R
      rw [← ha] at hpeel
      exact hpeel.trans_plus (rule_C_zero_nil R₁)
    · simp only [cSweepTail, hev, ↓reduceIte]
      have ha : a₀ = 2 * (a₀ / 2) + 1 := by omega
      have hpeel := peel_C_two (a₀ / 2) 1 [] R
      rw [← ha] at hpeel
      exact hpeel.trans_plus (rule_C_one_nil R₁)
  | a₁ :: Lp, a₀, R => by
    let R₁ := List.replicate (a₀ / 2) 0 ++ R
    by_cases hev : a₀ % 2 = 0
    · simp only [cSweepTail, hev, ↓reduceIte]
      have ha : a₀ = 2 * (a₀ / 2) + 0 := by omega
      have hpeel := peel_C_two (a₀ / 2) 0 (a₁ :: Lp) R
      rw [← ha] at hpeel
      exact hpeel.trans_plus
        ((rule_C_zero_cons a₁ Lp R₁).trans (reaches_cSweepTail Lp a₁ (bump2 R₁)))
    · simp only [cSweepTail, hev, ↓reduceIte]
      have ha : a₀ = 2 * (a₀ / 2) + 1 := by omega
      have hpeel := peel_C_two (a₀ / 2) 1 (a₁ :: Lp) R
      rw [← ha] at hpeel
      exact hpeel.trans_plus
        ((rule_C_one_cons a₁ Lp R₁).trans (reaches_cSweepTail Lp (a₁ + 1) (bump2 R₁)))

/-! ## `runCR1` and `B` Stride-3 Peel Simulations -/

private theorem sim_runCR1 :
    ∀ (b : ℕ) (L R : List ℕ),
      stepsOrHalts (cfgCR (0 :: b :: L) R) (runCR1 b L R)
  | b, L, [] => by
    change (cfgCR (0 :: b :: L) []) [target]⊢⁺ encode (.B [] 0 (cSweepTail L b [1]))
    have h0 : cfgCR (0 :: b :: L) [] = cfgC (0 :: b :: L) [] := by
      unfold cfgCR cfgC encStack
      simp only [ListBlank.cons_zero_default]
    rw [h0]
    exact (rule_C_zero_cons b L []).trans (reaches_cSweepTail L b [1])
  | b, L, 0 :: R => by
    change (cfgCR (0 :: b :: L) (0 :: R)) [target]⊢⁺
      encode (.B ((b + 1) :: L) (bump2NE R).1 (bump2NE R).2)
    unfold cfgCR
    simp only [encode, cons_bump2NE, ← bumpHead_bumpHead]
    rw [← encStack_cons_one, ← encStack_cons_one]
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  | b, L, 1 :: R => by
    unfold runCR1
    have h1 :
        (cfgCR (0 :: b :: L) (1 :: R)) [target]⊢⁺ cfgCR (0 :: 1 :: b :: L) R := by
      unfold cfgCR
      cases R <;>
        simp only [encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default] <;>
        bb_steps
    exact stepsOrHalts_trans h1 (sim_runCR1 1 (b :: L) R)
  | b, L, [2] => by
    unfold runCR1 stepsOrHalts
    refine ⟨Cfg.headRight F ([0, 0, 0] +> encStack (1 :: b :: L)) default, ?_, by bb_halt⟩
    unfold cfgCR
    simp only [encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default]
    bb_steps
  | b, L, 2 :: e :: R => by
    change (cfgCR (0 :: b :: L) (2 :: e :: R)) [target]⊢⁺
      encode (.B (0 :: 1 :: b :: L) e R)
    unfold cfgCR
    simp only [encode, encStack, list_pow_succ, list_pow_zero]
    bb_steps
  | b, L, (d + 3) :: R => by
    change (cfgCR (0 :: b :: L) ((d + 3) :: R)) [target]⊢⁺
      encode (.B (2 :: b :: L) d R)
    unfold cfgCR
    simp only [encode, encStack]
    have hd : d + 3 + 1 = 4 + d := by omega
    have hd1 : d + 1 = 1 + d := by omega
    rw [hd, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 d,
      hd1, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 d]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps

private theorem rule_B_add_three (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfgB L ((d + 3) :: R)) [target]⊢⁺
      cfgB (bumpHead (bumpHead (bumpHead L))) (d :: R) := by
  unfold cfgB
  simp only [encStack]
  have hd : d + 3 + 1 = 4 + d := by omega
  have hd1 : d + 1 = 1 + d := by omega
  rw [hd, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 d,
    hd1, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 d,
    ← encStack_cons_one, ← encStack_cons_one, ← encStack_cons_one]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem peel_B_three (k r₀ : ℕ) (L R : List ℕ) :
    (cfgB L ((3 * k + r₀) :: R)) [target]⊢* cfgB (add3 k L) (r₀ :: R) := by
  induction k generalizing L with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, add3]
    bb_refl
  | succ k ih =>
    have hk : 3 * (k + 1) + r₀ = (3 * k + r₀) + 3 := by omega
    rw [hk]
    exact (rule_B_add_three L (3 * k + r₀) R).to_star.trans
      (ih (bumpHead (bumpHead (bumpHead L))))

private theorem init_reaches_start : (init []) [target]⊢* encode start := by
  simp only [start, encode, encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default]
  bb_steps

private theorem sim_next (s : State) : stepsOrHalts (encode s) (next s) := by
  rcases s with ⟨L, d, R⟩
  let L₁ := add3 (d / 3) L
  by_cases h0 : d % 3 = 0
  · have hd : d = 3 * (d / 3) + 0 := by omega
    have hpeel : (encode (.B L d R)) [target]⊢* cfgB L₁ (0 :: R) := by
      simpa [encode, cfgB, ← hd, L₁] using peel_B_three (d / 3) 0 L R
    rcases hL₁ : L₁ with _ | ⟨a₀, Lp⟩
    · simp only [next, h0, ↓reduceIte, L₁, hL₁]
      rw [hL₁] at hpeel
      have h1 : (cfgB [] (0 :: R)) [target]⊢⁺ encode (.B [0] (bump2NE R).1 (bump2NE R).2) := by
        unfold cfgB
        simp only [encode, cons_bump2NE, ← bumpHead_bumpHead]
        rw [← encStack_cons_one, ← encStack_cons_one]
        simp only [encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default]
        bb_steps
      exact hpeel.trans_plus h1
    · simp only [next, h0, ↓reduceIte, L₁, hL₁]
      rw [hL₁] at hpeel
      have h1 : (cfgB (a₀ :: Lp) (0 :: R)) [target]⊢⁺ cfgC (a₀ :: Lp) (bump2 R) := by
        unfold cfgB cfgC
        simp only [← bumpHead_bumpHead, encStack, list_pow_succ, list_pow_zero]
        rw [← encStack_cons_one, ← encStack_cons_one]
        bb_steps
      exact hpeel.trans_plus (h1.trans (reaches_cSweepTail Lp a₀ (bump2 R)))
  · by_cases h1 : d % 3 = 1
    · have hd : d = 3 * (d / 3) + 1 := by omega
      have hpeel : (encode (.B L d R)) [target]⊢* cfgB L₁ (1 :: R) := by
        simpa [encode, cfgB, ← hd, L₁] using peel_B_three (d / 3) 1 L R
      simp only [next, h1, ↓reduceIte]
      have hstep :
          (cfgB L₁ (1 :: R)) [target]⊢⁺ cfgCR (0 :: (bump2NE L₁).1 :: (bump2NE L₁).2) R := by
        unfold cfgB cfgCR
        rw [cons_bump2NE, ← bumpHead_bumpHead]
        cases R <;>
          simp only [encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default] <;>
          rw [← encStack_cons_one, ← encStack_cons_one] <;>
          bb_steps
      exact stepsOrHalts_of_star hpeel (stepsOrHalts_trans hstep (sim_runCR1 _ _ R))
    · have hd : d = 3 * (d / 3) + 2 := by omega
      have hpeel : (encode (.B L d R)) [target]⊢* cfgB L₁ (2 :: R) := by
        simpa [encode, cfgB, ← hd, L₁] using peel_B_three (d / 3) 2 L R
      rcases R with _ | ⟨e, R'⟩
      · simp only [next, h0, h1, ↓reduceIte]
        have hhalt :
            (cfgB L₁ [2]) [target]⊢⁺
              Cfg.headRight F ([0, 0, 0] +> encStack (bump2 L₁)) default := by
          unfold cfgB
          simp only [← bumpHead_bumpHead]
          rw [← encStack_cons_one, ← encStack_cons_one]
          simp only [encStack, list_pow_succ, list_pow_zero, ListBlank.cons_zero_default]
          bb_steps
        exact ⟨Cfg.headRight F ([0, 0, 0] +> encStack (bump2 L₁)) default,
          hpeel.trans hhalt.to_star, by bb_halt⟩
      · simp only [next, h0, h1, ↓reduceIte]
        have hstep :
            (cfgB L₁ (2 :: e :: R')) [target]⊢⁺ encode (.B (0 :: bump2 L₁) e R') := by
          unfold cfgB
          simp only [encode, ← bumpHead_bumpHead, encStack, list_pow_succ, list_pow_zero]
          rw [← encStack_cons_one, ← encStack_cons_one]
          bb_steps
        exact hpeel.trans_plus hstep

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start (fun s => ?_)
  have hs := sim_next s
  rcases h : next s with _ | s' <;> simpa [stepsOrHalts, h] using hs

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Acceleration -/

/-- Reduced single-stack state space $B_{\mathrm{HL}}(R) := B([], 0, R)$ on the
$L = [] \land d = 0$ Poincaré return section. -/
inductive HighLevelState where
  /-- Right-stack configuration $B([], 0, R)$ with empty left stack and zero counter. -/
  | B (R : List ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level state $B_{\mathrm{HL}}([1])$, reached in 1 `next` step from `start`. -/
def highLevelStart : HighLevelState := .B [1]

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .B R => .B [] 0 R

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Contract non-empty-left-stack `B(a :: Lp, d, R)` (`inCR1 = false`) and `runCR1 a Lp R`
(`inCR1 = true`) excursions until returning to $B([], 0, \cdot)$ or halting. -/
def scanHL : Bool → ℕ → List ℕ → ℕ → List ℕ → Option HighLevelState
  | true, a, Lp, _, [] => some (.B (cSweepTail Lp a [1]))
  | true, a, Lp, _, r :: R' =>
    if r = 0 then
      if R' = [] then scanHL false (a + 1) Lp 1 []
      else scanHL false (a + 1) Lp (R'.headD 0 + 2) R'.tail
    else if r = 1 then
      scanHL true 1 (a :: Lp) 0 R'
    else if r = 2 then
      if R' = [] then none
      else scanHL false 0 (1 :: a :: Lp) (R'.headD 0) R'.tail
    else
      scanHL false 2 (a :: Lp) (r - 3) R'
  | false, a, Lp, d, R =>
    let a₁ := a + 3 * (d / 3)
    if d % 3 = 0 then
      some (.B (cSweepTail Lp a₁ (bump2 R)))
    else if d % 3 = 1 then
      scanHL true (a₁ + 2) Lp 0 R
    else if R = [] then
      none
    else
      scanHL false 0 ((a₁ + 2) :: Lp) (R.headD 0) R.tail
termination_by inCR1 _ _ _ R => (R.length, if inCR1 then 0 else 1)
decreasing_by
  all_goals simp_wf
  · apply Prod.Lex.left
    omega
  · cases R' with
    | nil => contradiction
    | cons _ _ =>
      apply Prod.Lex.left
      simp only [List.length_cons]
      omega
  · apply Prod.Lex.left
    omega
  · cases R' with
    | nil => contradiction
    | cons _ _ =>
      apply Prod.Lex.left
      simp only [List.length_cons]
      omega
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    omega
  · cases R with
    | nil => contradiction
    | cons _ _ =>
      apply Prod.Lex.left
      simp only [List.length_cons]
      omega

/-- High-level single-stack accelerated transition function on $B_{\mathrm{HL}}(R)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .B R =>
    let p := bump2NE R
    scanHL false 0 [] p.1 p.2

private theorem add3_cons (k a : ℕ) (Lp : List ℕ) :
    add3 k (a :: Lp) = (a + 3 * k) :: Lp := by
  induction k generalizing a with
  | zero => simp [add3]
  | succ k ih =>
    rw [add3, Function.iterate_succ_apply]
    change ((fun s => bumpHead (bumpHead (bumpHead s)))^[k]) ((a + 3) :: Lp) = _
    rw [← add3, ih (a + 3)]
    congr 1
    omega

private theorem scanHL_spec (n : ℕ) :
    ∀ (inCR1 : Bool) (a : ℕ) (Lp : List ℕ) (d : ℕ) (R : List ℕ),
      2 * R.length + (if inCR1 then 0 else 1) = n →
      if inCR1 then
        ∀ s₀ : State, next s₀ = runCR1 a Lp R →
          CollatzStepsTo next s₀ ((scanHL true a Lp d R).map toState)
      else
        CollatzStepsTo next (.B (a :: Lp) d R) ((scanHL false a Lp d R).map toState) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro inCR1 a Lp d R hn
    cases inCR1 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hn ⊢
      rw [scanHL.eq_def]
      dsimp only
      have hL₁ : add3 (d / 3) (a :: Lp) = (a + 3 * (d / 3)) :: Lp := add3_cons (d / 3) a Lp
      split_ifs with h0 h1 hRnil
      · refine CollatzStepsTo.of_eq ?_
        simp [next, hL₁, h0, toState]
      · refine ih (2 * R.length) (by omega) true (a + 3 * (d / 3) + 2) Lp 0 R
          (by simp) (.B (a :: Lp) d R) ?_
        simp [next, hL₁, h1, bump2NE]
      · subst hRnil
        refine CollatzStepsTo.of_eq ?_
        simp [next, h0, h1]
      · rcases R with _ | ⟨e, R'⟩
        · contradiction
        · simp only [List.headD_cons, List.tail_cons]
          have hstep :
              next (.B (a :: Lp) d (e :: R')) =
                some (.B (0 :: (a + 3 * (d / 3) + 2) :: Lp) e R') := by
            simp [next, hL₁, h0, h1, bump2]
          exact CollatzStepsTo.head hstep
            (ih (2 * R'.length + 1) (by simp at hn; omega)
              false 0 ((a + 3 * (d / 3) + 2) :: Lp) e R' rfl)
    | true =>
      simp only [↓reduceIte] at hn ⊢
      intro s₀ hs₀
      rcases R with _ | ⟨r, R'⟩
      · rw [scanHL.eq_def]
        exact CollatzStepsTo.of_eq hs₀
      · rw [scanHL.eq_def]
        dsimp only
        by_cases hr0 : r = 0
        · subst hr0
          simp only [↓reduceIte]
          rcases R' with _ | ⟨x, xs⟩
          · simp only [↓reduceIte]
            exact CollatzStepsTo.head hs₀
              (ih 1 (by simp at hn; omega) false (a + 1) Lp 1 [] rfl)
          · simp only [reduceCtorEq, ↓reduceIte, List.headD_cons, List.tail_cons]
            exact CollatzStepsTo.head hs₀
              (ih (2 * xs.length + 1) (by simp at hn; omega) false (a + 1) Lp (x + 2) xs rfl)
        · simp only [hr0, ↓reduceIte]
          by_cases hr1 : r = 1
          · subst hr1
            simp only [↓reduceIte]
            exact ih (2 * R'.length) (by simp at hn; omega) true 1 (a :: Lp) 0 R' rfl s₀ hs₀
          · simp only [hr1, ↓reduceIte]
            by_cases hr2 : r = 2
            · subst hr2
              simp only [↓reduceIte]
              rcases R' with _ | ⟨e, R''⟩
              · simp only [↓reduceIte]
                exact CollatzStepsTo.of_eq hs₀
              · simp only [reduceCtorEq, ↓reduceIte, List.headD_cons, List.tail_cons]
                exact CollatzStepsTo.head hs₀
                  (ih (2 * R''.length + 1) (by simp at hn; omega) false 0 (1 :: a :: Lp) e R'' rfl)
            · simp only [hr2, ↓reduceIte]
              have hr3 : r = (r - 3) + 3 := by omega
              rw [hr3] at hs₀
              exact CollatzStepsTo.head hs₀
                (ih (2 * R'.length + 1) (by simp at hn; omega) false 2 (a :: Lp) (r - 3) R' rfl)

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid acceleration of
`target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState)
    (CollatzReachesStar.single rfl) ?_
  rintro ⟨R⟩
  exact CollatzStepsTo.head rfl
    (scanHL_spec (2 * (bump2NE R).2.length + 1) false 0 [] (bump2NE R).1 (bump2NE R).2 rfl)

/-- `target` halts from the blank tape iff `highLevelNext` halts from `highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- The initial acceleration `next` halts from `start` iff `highLevelNext` halts from
`highLevelStart`. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_HHH1LC
