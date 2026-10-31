/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB`.

Along the trajectory from step 3 onward, the machine returns to separator configurations
$$D(L, R) := \mathrm{encLeft}(L)\,\mathrm{D}{>}\,0\,\mathrm{encRight}(R)$$
where each left entry $(a, b) \in \mathbb{N} \times \mathrm{Bool}$ encodes $1^{a + 1} 0$
(`b = false`) or $1^{a + 1} 00$ (`b = true`), and each right entry $(d, c) \in \mathbb{N} \times
\mathrm{Fin}\,3$ encodes $1^{d + 1} 0^{c + 1}$ outward from the head. Starting from `init []`, the
machine reaches $D([], [(1, 0)])$ in 3 raw steps.

## Accelerated Transition Rules

```text
runB(z, a, b, L', R):       (let R1 = (1, 1) :: R if z else bump2R R)
  a = 0, L' = []            -> D([], R1)
  a = 0, b = F, p :: L''    -> D(p :: L'', R1)
  a = 0, b = T, (a2,b2)::L''-> D((a2 + 1, b2) :: L'', (0, z ? 2 : 0) :: R)
  a = 1, L' = []            -> D([], bump2R R1)
  a = 1, b = F, (a2,b2)::L''-> runB(F, a2 + 1, b2, L'', R1)
  a = 1, b = T, p :: L''    -> D(p :: L'', bump2R R1)
  a = 2, L' = [] or b = T   -> Halt
  a = 2, b = F, (a2,b2)::L''-> runB(T, a2, b2, L'', R1)
  a = 3, L' = []            -> D([], bump2R R1)
  a = 3, b = F, (a2,b2)::L''-> D((a2 + 1, b2) :: L'', (0, 0) :: R1)
  a = 3, b = T, p :: L''    -> D((0, F) :: p :: L'', (0, 0) :: R1)
  a + 4, b, L'              -> D((a, b) :: L', bump2R R1)

runBR(k, Lr, d1, c1, R'):   (let L = prepend00 k (push01 Lr))
  d1 = 0, R' = []           -> runB(F, 0, F, L, [])
  d1 = 0, (d2, c2) :: R''   -> runBR(k + 1, Lr, d2, c2, R'')          (c1 = 0)
                            -> runB(F, 0, F, L, (d2, c2) :: R'')      (c1 = 1)
                            -> D(L, (1, 0) :: (d2, c2) :: R'')        (c1 = 2)
  d1 = 1, R' = []           -> runB(F, 0, T, L, [])
  d1 = 1, (d2, c2) :: R''   -> runBR(0, L, d2, c2, R'')               (c1 = 0)
                            -> runB(F, 0, T, L, (d2, c2) :: R'')      (c1 = 1)
                            -> D(bumpHeadL L, (0, 1) :: (d2,c2)::R'') (c1 = 2)
  d1 = 2, R' = []           -> D(L, [(0, 0)])
  d1 = 2, (d2, c2) :: R''   -> D(L, (0, 1) :: (d2, c2) :: R'')        (c1 = 0)
                            -> D(L, (0, 2) :: (d2, c2) :: R'')        (c1 = 1)
                            -> D(prepend00 k (push01 (bumpHeadL Lr)),
                                 (1, 1) :: (d2, c2) :: R'')           (c1 = 2)
  d1 + 3, c1, R'            -> D(L, (0, 0) :: (d1, c1) :: R')

D([], [])                   -> D([(0, F)], [(1, 0)])
D([], (d1, c1) :: R')       -> runBR(0, [], d1 + 1, c1, R')
D((4k + r, b) :: L', R)     -> dispatch on r in {0, 1, 2, 3} with R1 = (2, 0)^k ++ R

Start: D([], [(1, 0)]), reached after 3 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Encode the right-stack zero separator (`0`, `00`, or `000`) for `c : Fin 3`. -/
def sepRight : Fin 3 → List (Fin 2)
  | 0 => [0]
  | 1 => [0, 0]
  | 2 => [0, 0, 0]

/-- Encode a left pair stack `L` as `1^{a + 1} 0` (`false`) or `1^{a + 1} 00` (`true`). -/
def encLeft : List (ℕ × Bool) → ListBlank (Fin 2)
  | [] => default
  | (a, false) :: L =>
    ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (ListBlank.cons 0 (encLeft L))
  | (a, true) :: L =>
    ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (ListBlank.append [0, 0] (encLeft L))

/-- Encode a right pair stack `R` as `1^{d + 1} 0^{c + 1} ...` from the tape head outward. -/
def encRight : List (ℕ × Fin 3) → ListBlank (Fin 2)
  | [] => default
  | (d, c) :: R =>
    ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) (ListBlank.append (sepRight c) (encRight R))

/-- Increment the head width of a left stack, or push `(0, false)` onto `[]`. -/
def bumpHeadL (s : List (ℕ × Bool)) : List (ℕ × Bool) :=
  List.casesOn s [(0, false)] fun p L => (p.1 + 1, p.2) :: L

/-- Add `2` to the head width of a right stack, or push `(1, 0)` onto `[]`. -/
def bump2R : List (ℕ × Fin 3) → List (ℕ × Fin 3)
  | [] => [(1, 0)]
  | (d, c) :: R => (d + 2, c) :: R

/-- Push a `100` block (`(0, true)`, normalized to `(0, false)` on `[]`) onto a left stack. -/
def push01 (s : List (ℕ × Bool)) : List (ℕ × Bool) :=
  List.casesOn s [(0, false)] fun p L => (0, true) :: (p.1, p.2) :: L

/-- Prepend `k` copies of `(0, false)` onto a left stack. -/
def prepend00 : ℕ → List (ℕ × Bool) → List (ℕ × Bool)
  | 0, L => L
  | k + 1, L => (0, false) :: prepend00 k L

/-- Symbolic state space for the accelerated transition system of `target`. -/
inductive State where
  /-- Separator configuration `D(L, R)`: state `D>` reading `0` between `encLeft L` and
  `encRight R`. -/
  | D (L : List (ℕ × Bool)) (R : List (ℕ × Fin 3))
  deriving DecidableEq, Repr

/-- Sweep `B>` reading `0` (`twoZeros = false`) or `000` (`twoZeros = true`) across `(a, b) :: L'`
until returning to `D` or halting (`none`). -/
def runB (twoZeros : Bool) :
    ℕ → Bool → List (ℕ × Bool) → List (ℕ × Fin 3) → Option State
  | 0, _, [], R =>
    some (.D [] (if twoZeros then (1, 1) :: R else bump2R R))
  | 0, false, p :: L', R =>
    some (.D (p :: L') (if twoZeros then (1, 1) :: R else bump2R R))
  | 0, true, (a₂, b₂) :: L', R =>
    some (.D ((a₂ + 1, b₂) :: L') ((0, if twoZeros then 2 else 0) :: R))
  | 1, _, [], R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D [] (bump2R R₁))
  | 1, false, (a₂, b₂) :: L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    runB false (a₂ + 1) b₂ L' R₁
  | 1, true, p :: L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D (p :: L') (bump2R R₁))
  | 2, _, [], _ => none
  | 2, false, (a₂, b₂) :: L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    runB true a₂ b₂ L' R₁
  | 2, true, _ :: _, _ => none
  | 3, _, [], R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D [] (bump2R R₁))
  | 3, false, (a₂, b₂) :: L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D ((a₂ + 1, b₂) :: L') ((0, 0) :: R₁))
  | 3, true, p :: L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D ((0, false) :: p :: L') ((0, 0) :: R₁))
  | a + 4, b, L', R =>
    let R₁ := if twoZeros then (1, 1) :: R else bump2R R
    some (.D ((a, b) :: L') (bump2R R₁))

/-- Sweep `B>` across right stack `(d₁, c₁) :: R'` with left stack `prepend00 k (push01 Lrest)`. -/
def runBR (k : ℕ) (Lrest : List (ℕ × Bool)) :
    ℕ → Fin 3 → List (ℕ × Fin 3) → Option State
  | 0, _, [] => runB false 0 false (prepend00 k (push01 Lrest)) []
  | 0, c₁, (d₂, c₂) :: R' =>
    if c₁ = 0 then
      runBR (k + 1) Lrest d₂ c₂ R'
    else if c₁ = 1 then
      runB false 0 false (prepend00 k (push01 Lrest)) ((d₂, c₂) :: R')
    else
      some (.D (prepend00 k (push01 Lrest)) ((1, 0) :: (d₂, c₂) :: R'))
  | 1, _, [] => runB false 0 true (prepend00 k (push01 Lrest)) []
  | 1, c₁, (d₂, c₂) :: R' =>
    let L := prepend00 k (push01 Lrest)
    if c₁ = 0 then
      runBR 0 L d₂ c₂ R'
    else if c₁ = 1 then
      runB false 0 true L ((d₂, c₂) :: R')
    else
      some (.D (bumpHeadL L) ((0, 1) :: (d₂, c₂) :: R'))
  | 2, _, [] => some (.D (prepend00 k (push01 Lrest)) [(0, 0)])
  | 2, c₁, (d₂, c₂) :: R' =>
    let L := prepend00 k (push01 Lrest)
    if c₁ = 0 then
      some (.D L ((0, 1) :: (d₂, c₂) :: R'))
    else if c₁ = 1 then
      some (.D L ((0, 2) :: (d₂, c₂) :: R'))
    else
      some (.D (prepend00 k (push01 (bumpHeadL Lrest))) ((1, 1) :: (d₂, c₂) :: R'))
  | d₁ + 3, c₁, R' =>
    some (.D (prepend00 k (push01 Lrest)) ((0, 0) :: (d₁, c₁) :: R'))

/-- Initial symbolic state `D([], [(1, 0)])`, reached from `init []` in 3 raw steps. -/
def start : State := .D [] [(1, 0)]

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .D L R => Cfg.headRight D (encLeft L) (ListBlank.cons 0 (encRight R))

/-- Accelerated transition function (`none` indicates halting via `C0 -> ---`). -/
def next : State → Option State
  | .D [] [] => some (.D [(0, false)] [(1, 0)])
  | .D [] ((d₁, c₁) :: R') => runBR 0 [] (d₁ + 1) c₁ R'
  | .D ((a, b) :: L') R =>
    let R₁ := List.replicate (a / 4) (2, (0 : Fin 3)) ++ R
    if a % 4 = 0 then
      match L', b with
      | [], _ => some (.D [] ((0, 0) :: R₁))
      | p :: L'', false => some (.D (p :: L'') ((0, 0) :: R₁))
      | (a₂, b₂) :: L'', true =>
        let Lnext := (a₂ + 1, b₂) :: L''
        match R₁ with
        | [] => runB false 0 true Lnext []
        | (d₁, c₁) :: R₁' => runBR 0 Lnext d₁ c₁ R₁'
    else if a % 4 = 1 then
      match L', b with
      | [], _ => some (.D [] ((2, 0) :: R₁))
      | (a₂, b₂) :: L'', false => runB false (a₂ + 1) b₂ L'' ((0, 0) :: R₁)
      | p :: L'', true => some (.D (p :: L'') ((2, 0) :: R₁))
    else if a % 4 = 2 then
      match L', b with
      | [], _ => none
      | (a₂, b₂) :: L'', false => runB true a₂ b₂ L'' ((0, 0) :: R₁)
      | _ :: _, true => none
    else
      match L', b with
      | [], _ => some (.D [] ((2, 0) :: R₁))
      | (a₂, b₂) :: L'', false => some (.D ((a₂ + 1, b₂) :: L'') ((0, 0) :: (0, 0) :: R₁))
      | p :: L'', true => some (.D ((0, false) :: p :: L'') ((0, 0) :: (0, 0) :: R₁))

/-! ## Pair-Stack Encoding Helpers and Shift Lemmas -/

private theorem encLeft_singleton (a : ℕ) (b : Bool) :
    encLeft [(a, b)] = ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default := by
  cases b <;> simp [encLeft, ListBlank.cons_zero_default]

private theorem encLeft_cons_succ (a : ℕ) (b : Bool) (L : List (ℕ × Bool)) :
    encLeft ((a + 1, b) :: L) = ListBlank.cons 1 (encLeft ((a, b) :: L)) := by
  cases b <;> simp only [encLeft, ListBlank.append_pow_succ, ListBlank.append_cons,
    ListBlank.append_nil]

private theorem encLeft_cons_one (L : List (ℕ × Bool)) :
    ListBlank.cons 1 (encLeft L) = encLeft (bumpHeadL L) := by
  rcases L with _ | ⟨⟨a, b⟩, L'⟩
  · simp [bumpHeadL, encLeft]
  · exact (encLeft_cons_succ a b L').symm

private theorem encLeft_push01 (L : List (ℕ × Bool)) :
    encLeft (push01 L) = [1, 0, 0] +> encLeft L := by
  rcases L with _ | ⟨⟨a, b⟩, L'⟩
  · simp [push01, encLeft]
  · simp [push01, encLeft]

private theorem push01_prepend00_push01 (k : ℕ) (L : List (ℕ × Bool)) :
    (0, true) :: prepend00 k (push01 L) = push01 (prepend00 k (push01 L)) := by
  cases k <;> cases L <;> rfl

private theorem sepRight_append_default (c : Fin 3) :
    ListBlank.append (sepRight c) default = default := by
  rcases c with ⟨_ | _ | _ | c, hc⟩
  · simp [sepRight]
  · simp [sepRight]
  · simp [sepRight]
  · omega

private theorem encRight_singleton (d : ℕ) (c : Fin 3) :
    encRight [(d, c)] = ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default := by
  simp [encRight, sepRight_append_default]

private theorem encRight_cons_succ (d : ℕ) (c : Fin 3) (R : List (ℕ × Fin 3)) :
    encRight ((d + 1, c) :: R) = ListBlank.cons 1 (encRight ((d, c) :: R)) := by
  simp only [encRight, ListBlank.append_pow_succ, ListBlank.append_cons, ListBlank.append_nil]

private theorem encRight_bump2R (R : List (ℕ × Fin 3)) :
    encRight (bump2R R) = [1, 1] +> encRight R := by
  rcases R with _ | ⟨⟨d, c⟩, R'⟩
  · simp [bump2R, encRight, sepRight, list_pow_succ, list_pow_zero]
  · simp only [bump2R]
    rw [encRight_cons_succ (d + 1) c R', encRight_cons_succ d c R']
    rfl

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

private theorem d_shift_00 (k : ℕ) (L : List (ℕ × Bool)) (r : ListBlank (Fin 2)) :
    (Cfg.headRight D (encLeft (prepend00 k L)) (ListBlank.cons 0 r)) [target]⊢*
      Cfg.headRight D (encLeft L) (ListBlank.cons 0 ((([1, 0] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing r with
  | zero =>
    simp only [prepend00, list_pow_zero, ListBlank.append_nil]
    bb_refl
  | succ k ih =>
    have h1 :
        (Cfg.headRight D (encLeft (prepend00 (k + 1) L)) (ListBlank.cons 0 r)) [target]⊢⁺
          Cfg.headRight D (encLeft (prepend00 k L)) (ListBlank.cons 0 ([1, 0] +> r)) := by
      simp only [prepend00, encLeft, list_pow_succ, list_pow_zero]
      bb_steps
    have h2 := ih ([1, 0] +> r)
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

private theorem d_bounce_push01 (Lrest : List (ℕ × Bool)) (r : ListBlank (Fin 2)) :
    (Cfg.headRight D (encLeft (push01 Lrest)) (ListBlank.cons 0 r)) [target]⊢⁺
      ((encLeft (push01 (bumpHeadL Lrest))) {{B}}> r) := by
  rw [encLeft_push01 Lrest, encLeft_push01 (bumpHeadL Lrest), ← encLeft_cons_one Lrest]
  bb_steps

private theorem prepend00_comm_00 (m : ℕ) (L : List (ℕ × Bool)) :
    prepend00 m ((0, false) :: L) = (0, false) :: prepend00 m L := by
  induction m with
  | zero => rfl
  | succ m ih => simp [prepend00, ih]

private theorem b_shift_10 (k : ℕ) (L : List (ℕ × Bool)) (r : ListBlank (Fin 2)) :
    ((encLeft L) {{B}}> ((([1, 0] : List (Fin 2)) ^ k) +> r)) [target]⊢*
      ((encLeft (prepend00 k L)) {{B}}> r) := by
  induction k generalizing L with
  | zero =>
    simp only [prepend00, list_pow_zero, ListBlank.append_nil]
    bb_refl
  | succ k ih =>
    have h1 :
        ((encLeft L) {{B}}> ((([1, 0] : List (Fin 2)) ^ (k + 1)) +> r)) [target]⊢⁺
          ((encLeft ((0, false) :: L)) {{B}}> ((([1, 0] : List (Fin 2)) ^ k) +> r)) := by
      rw [ListBlank.append_pow_succ]
      simp only [encLeft, list_pow_succ, list_pow_zero]
      bb_steps
    have h2 := ih ((0, false) :: L)
    rw [prepend00_comm_00] at h2
    exact (h1.trans_star h2).to_star

/-! ## `runB` and `runBR` Sweep Simulations -/

private def cfgB (twoZeros : Bool) (L : List (ℕ × Bool)) (R : List (ℕ × Fin 3)) :
    Cfg (Fin 2) (Fin 6) :=
  if twoZeros then
    Cfg.headRight B (encLeft L) ([0, 0, 0] +> encRight R)
  else
    Cfg.headRight B (encLeft L) (ListBlank.cons 0 (encRight R))

private def cfgBR (L : List (ℕ × Bool)) (R : List (ℕ × Fin 3)) : Cfg (Fin 2) (Fin 6) :=
  (encLeft L) {{B}}> (encRight R)

private theorem sim_runB :
    ∀ (twoZeros : Bool) (a : ℕ) (b : Bool) (L' : List (ℕ × Bool)) (R : List (ℕ × Fin 3)),
      stepsOrHalts (cfgB twoZeros ((a, b) :: L') R) (runB twoZeros a b L' R)
  | twoZeros, 0, b, [], R => by
    unfold runB stepsOrHalts cfgB
    rw [encLeft_singleton 0 b]
    cases twoZeros <;>
      simp only [↓reduceIte, Bool.false_eq_true, encode, encLeft, encRight, sepRight,
        encRight_bump2R, list_pow_succ, list_pow_zero] <;>
      bb_steps
  | twoZeros, 0, false, p :: L', R => by
    unfold runB stepsOrHalts cfgB
    cases twoZeros <;>
      simp only [↓reduceIte, Bool.false_eq_true, encode, encLeft, encRight, sepRight,
        encRight_bump2R, list_pow_succ, list_pow_zero] <;>
      bb_steps
  | twoZeros, 0, true, (a₂, b₂) :: L', R => by
    unfold runB stepsOrHalts cfgB
    cases twoZeros <;>
      simp only [↓reduceIte, Bool.false_eq_true, encode, encLeft, encRight, sepRight,
        encLeft_cons_succ a₂ b₂ L', list_pow_succ, list_pow_zero] <;>
      bb_steps
  | twoZeros, 1, b, [], R => by
    unfold runB stepsOrHalts cfgB
    rw [encLeft_singleton 1 b]
    cases twoZeros <;>
      simp only [↓reduceIte, Bool.false_eq_true, encode, encLeft, encRight, sepRight,
        encRight_bump2R, list_pow_succ, list_pow_zero] <;>
      bb_steps
  | twoZeros, 1, false, (a₂, b₂) :: L', R => by
    unfold runB
    have hstep :
        (cfgB twoZeros ((1, false) :: (a₂, b₂) :: L') R) [target]⊢⁺
          cfgB false ((a₂ + 1, b₂) :: L') (if twoZeros then (1, 1) :: R else bump2R R) := by
      unfold cfgB
      cases twoZeros <;>
        simp only [↓reduceIte, Bool.false_eq_true, encLeft, encRight, sepRight, encRight_bump2R,
          encLeft_cons_succ a₂ b₂ L', list_pow_succ, list_pow_zero] <;>
        bb_steps
    exact stepsOrHalts_trans hstep
      (sim_runB false (a₂ + 1) b₂ L' (if twoZeros then (1, 1) :: R else bump2R R))
  | twoZeros, 1, true, p :: L', R => by
    unfold runB stepsOrHalts cfgB
    cases twoZeros <;>
      simp only [↓reduceIte, Bool.false_eq_true, encode, encLeft, encRight, sepRight,
        encRight_bump2R, list_pow_succ, list_pow_zero] <;>
      bb_steps
  | twoZeros, 2, b, [], R => by
    unfold runB stepsOrHalts cfgB
    rw [encLeft_singleton 2 b]
    cases twoZeros
    · refine ⟨Cfg.headLeft C default ([1, 0, 0, 1, 1] +> encRight R), ?_, by bb_halt⟩
      simp only [Bool.false_eq_true, ↓reduceIte, list_pow_succ, list_pow_zero]
      bb_steps
    · refine ⟨Cfg.headLeft C default ([1, 0, 0, 1, 1, 0, 0] +> encRight R), ?_, by bb_halt⟩
      simp only [↓reduceIte, list_pow_succ, list_pow_zero]
      bb_steps
  | twoZeros, 2, false, (a₂, b₂) :: L', R => by
    unfold runB
    have hstep :
        (cfgB twoZeros ((2, false) :: (a₂, b₂) :: L') R) [target]⊢⁺
          cfgB true ((a₂, b₂) :: L') (if twoZeros then (1, 1) :: R else bump2R R) := by
      unfold cfgB
      cases twoZeros <;>
        simp only [↓reduceIte, Bool.false_eq_true, encLeft, encRight, sepRight, encRight_bump2R,
          list_pow_succ, list_pow_zero] <;>
        bb_steps
    exact stepsOrHalts_trans hstep
      (sim_runB true a₂ b₂ L' (if twoZeros then (1, 1) :: R else bump2R R))
  | twoZeros, 2, true, p :: L', R => by
    unfold runB stepsOrHalts cfgB
    cases twoZeros
    · refine ⟨Cfg.headLeft C ([0] +> encLeft (p :: L')) ([1, 0, 0, 1, 1] +> encRight R),
        ?_, by bb_halt⟩
      simp only [Bool.false_eq_true, ↓reduceIte, encLeft, list_pow_succ, list_pow_zero]
      bb_steps
    · refine ⟨Cfg.headLeft C ([0] +> encLeft (p :: L')) ([1, 0, 0, 1, 1, 0, 0] +> encRight R),
        ?_, by bb_halt⟩
      simp only [↓reduceIte, encLeft, list_pow_succ, list_pow_zero]
      bb_steps
  | twoZeros, 3, b, [], R => by
    unfold runB stepsOrHalts cfgB
    rw [encLeft_singleton 3 b]
    cases twoZeros <;>
      simp only [↓reduceIte, Bool.false_eq_true, encode, encLeft, encRight, sepRight,
        encRight_bump2R, list_pow_succ, list_pow_zero] <;>
      bb_steps
  | twoZeros, 3, false, (a₂, b₂) :: L', R => by
    unfold runB stepsOrHalts cfgB
    cases twoZeros <;>
      simp only [↓reduceIte, Bool.false_eq_true, encode, encLeft, encRight, sepRight,
        encRight_bump2R, encLeft_cons_succ a₂ b₂ L', list_pow_succ, list_pow_zero] <;>
      bb_steps
  | twoZeros, 3, true, p :: L', R => by
    unfold runB stepsOrHalts cfgB
    cases twoZeros <;>
      simp only [↓reduceIte, Bool.false_eq_true, encode, encLeft, encRight, sepRight,
        encRight_bump2R, list_pow_succ, list_pow_zero] <;>
      bb_steps
  | twoZeros, a + 4, b, L', R => by
    unfold runB stepsOrHalts cfgB
    rw [encLeft_cons_succ (a + 3) b L', encLeft_cons_succ (a + 2) b L',
      encLeft_cons_succ (a + 1) b L', encLeft_cons_succ a b L']
    cases twoZeros <;>
      simp only [↓reduceIte, Bool.false_eq_true, encode, encRight, sepRight, encRight_bump2R,
        list_pow_succ, list_pow_zero] <;>
      bb_steps

private theorem sim_runBR :
    ∀ (k : ℕ) (Lrest : List (ℕ × Bool)) (d₁ : ℕ) (c₁ : Fin 3) (R' : List (ℕ × Fin 3)),
      stepsOrHalts (cfgBR (prepend00 k (push01 Lrest)) ((d₁, c₁) :: R'))
        (runBR k Lrest d₁ c₁ R')
  | k, Lrest, 0, c₁, [] => by
    unfold runBR
    have h1 :
        (cfgBR (prepend00 k (push01 Lrest)) [(0, c₁)]) [target]⊢⁺
          cfgB false ((0, false) :: prepend00 k (push01 Lrest)) [] := by
      unfold cfgBR cfgB
      rw [encRight_singleton 0 c₁]
      simp only [Bool.false_eq_true, ↓reduceIte, encLeft, encRight, list_pow_succ, list_pow_zero]
      bb_steps
    exact stepsOrHalts_trans h1 (sim_runB false 0 false (prepend00 k (push01 Lrest)) [])
  | k, Lrest, 0, c₁, (d₂, c₂) :: R' => by
    rcases c₁ with ⟨_ | _ | _ | c₁, hc₁⟩
    · simp only [runBR]
      have h1 :
          (cfgBR (prepend00 k (push01 Lrest)) ((0, 0) :: (d₂, c₂) :: R')) [target]⊢⁺
            cfgBR (prepend00 (k + 1) (push01 Lrest)) ((d₂, c₂) :: R') := by
        unfold cfgBR
        simp only [prepend00, encLeft, encRight, sepRight, list_pow_succ, list_pow_zero]
        bb_steps
      exact stepsOrHalts_trans h1 (sim_runBR (k + 1) Lrest d₂ c₂ R')
    · change stepsOrHalts (cfgBR (prepend00 k (push01 Lrest)) ((0, 1) :: (d₂, c₂) :: R'))
        (runB false 0 false (prepend00 k (push01 Lrest)) ((d₂, c₂) :: R'))
      have h1 :
          (cfgBR (prepend00 k (push01 Lrest)) ((0, 1) :: (d₂, c₂) :: R')) [target]⊢⁺
            cfgB false ((0, false) :: prepend00 k (push01 Lrest)) ((d₂, c₂) :: R') := by
        unfold cfgBR cfgB
        simp only [Bool.false_eq_true, ↓reduceIte, encLeft, encRight, sepRight,
          list_pow_succ, list_pow_zero]
        bb_steps
      exact stepsOrHalts_trans h1
        (sim_runB false 0 false (prepend00 k (push01 Lrest)) ((d₂, c₂) :: R'))
    · change (cfgBR (prepend00 k (push01 Lrest)) ((0, 2) :: (d₂, c₂) :: R')) [target]⊢⁺
        encode (.D (prepend00 k (push01 Lrest)) ((1, 0) :: (d₂, c₂) :: R'))
      unfold cfgBR
      simp only [encode, encRight, sepRight, list_pow_succ, list_pow_zero]
      bb_steps
    · omega
  | k, Lrest, 1, c₁, [] => by
    unfold runBR
    have h1 :
        (cfgBR (prepend00 k (push01 Lrest)) [(1, c₁)]) [target]⊢⁺
          cfgB false ((0, true) :: prepend00 k (push01 Lrest)) [] := by
      unfold cfgBR cfgB
      rw [encRight_singleton 1 c₁]
      simp only [Bool.false_eq_true, ↓reduceIte, encLeft, encRight, list_pow_succ, list_pow_zero]
      bb_steps
    exact stepsOrHalts_trans h1 (sim_runB false 0 true (prepend00 k (push01 Lrest)) [])
  | k, Lrest, 1, c₁, (d₂, c₂) :: R' => by
    let L := prepend00 k (push01 Lrest)
    rcases c₁ with ⟨_ | _ | _ | c₁, hc₁⟩
    · change stepsOrHalts (cfgBR L ((1, 0) :: (d₂, c₂) :: R')) (runBR 0 L d₂ c₂ R')
      have h1 :
          (cfgBR L ((1, 0) :: (d₂, c₂) :: R')) [target]⊢⁺
            cfgBR (prepend00 0 (push01 L)) ((d₂, c₂) :: R') := by
        unfold cfgBR
        simp only [prepend00, L, ← push01_prepend00_push01 k Lrest, encLeft, encRight, sepRight,
          list_pow_succ, list_pow_zero]
        bb_steps
      exact stepsOrHalts_trans h1 (sim_runBR 0 L d₂ c₂ R')
    · change stepsOrHalts (cfgBR L ((1, 1) :: (d₂, c₂) :: R'))
        (runB false 0 true L ((d₂, c₂) :: R'))
      have h1 :
          (cfgBR L ((1, 1) :: (d₂, c₂) :: R')) [target]⊢⁺
            cfgB false ((0, true) :: L) ((d₂, c₂) :: R') := by
        unfold cfgBR cfgB
        simp only [Bool.false_eq_true, ↓reduceIte, encLeft, encRight, sepRight,
          list_pow_succ, list_pow_zero]
        bb_steps
      exact stepsOrHalts_trans h1 (sim_runB false 0 true L ((d₂, c₂) :: R'))
    · change (cfgBR L ((1, 2) :: (d₂, c₂) :: R')) [target]⊢⁺
        encode (.D (bumpHeadL L) ((0, 1) :: (d₂, c₂) :: R'))
      unfold cfgBR
      simp only [encode, encRight, sepRight, list_pow_succ, list_pow_zero]
      rw [← encLeft_cons_one L]
      bb_steps
    · omega
  | k, Lrest, 2, c₁, [] => by
    change (cfgBR (prepend00 k (push01 Lrest)) [(2, c₁)]) [target]⊢⁺
      encode (.D (prepend00 k (push01 Lrest)) [(0, 0)])
    unfold cfgBR
    simp only [encode]
    rw [encRight_singleton 2 c₁, encRight_singleton 0 0]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  | k, Lrest, 2, c₁, (d₂, c₂) :: R' => by
    let L := prepend00 k (push01 Lrest)
    rcases c₁ with ⟨_ | _ | _ | c₁, hc₁⟩
    · change (cfgBR L ((2, 0) :: (d₂, c₂) :: R')) [target]⊢⁺
        encode (.D L ((0, 1) :: (d₂, c₂) :: R'))
      unfold cfgBR
      simp only [encode, encRight, sepRight, list_pow_succ, list_pow_zero]
      bb_steps
    · change (cfgBR L ((2, 1) :: (d₂, c₂) :: R')) [target]⊢⁺
        encode (.D L ((0, 2) :: (d₂, c₂) :: R'))
      unfold cfgBR
      simp only [encode, encRight, sepRight, list_pow_succ, list_pow_zero]
      bb_steps
    · change (cfgBR L ((2, 2) :: (d₂, c₂) :: R')) [target]⊢⁺
        encode (.D (prepend00 k (push01 (bumpHeadL Lrest))) ((1, 1) :: (d₂, c₂) :: R'))
      let rtail := [1, 0, 0, 0, 0] +> encRight ((d₂, c₂) :: R')
      have h1 :
          (cfgBR L ((2, 2) :: (d₂, c₂) :: R')) [target]⊢⁺
            Cfg.headRight D (encLeft L) (ListBlank.cons 0 rtail) := by
        unfold cfgBR
        simp only [encRight, sepRight, list_pow_succ, list_pow_zero, rtail]
        bb_steps
      have h2 := d_shift_00 k (push01 Lrest) rtail
      have h3 := d_bounce_push01 Lrest ((([1, 0] : List (Fin 2)) ^ k) +> rtail)
      have h4 := b_shift_10 k (push01 (bumpHeadL Lrest)) rtail
      have h5 :
          ((encLeft (prepend00 k (push01 (bumpHeadL Lrest)))) {{B}}> rtail) [target]⊢⁺
            encode (.D (prepend00 k (push01 (bumpHeadL Lrest))) ((1, 1) :: (d₂, c₂) :: R')) := by
        simp only [encode, encRight, sepRight, list_pow_succ, list_pow_zero, rtail]
        bb_steps
      exact ((h1.trans_star h2).trans (h3.trans_star h4)).trans h5
    · omega
  | k, Lrest, d₁ + 3, c₁, R' => by
    unfold runBR stepsOrHalts cfgBR
    simp only [encode]
    rw [encRight_cons_succ (d₁ + 2) c₁ R', encRight_cons_succ (d₁ + 1) c₁ R',
      encRight_cons_succ d₁ c₁ R']
    simp only [encRight, sepRight, list_pow_succ, list_pow_zero]
    bb_steps

/-! ## `D` Stride-4 Peel and Top-Level Dispatch -/

private theorem rule_D_add_four (a : ℕ) (b : Bool) (L' : List (ℕ × Bool))
    (R : List (ℕ × Fin 3)) :
    (encode (.D ((a + 4, b) :: L') R)) [target]⊢⁺
      encode (.D ((a, b) :: L') ((2, 0) :: R)) := by
  simp only [encode]
  rw [encLeft_cons_succ (a + 3) b L', encLeft_cons_succ (a + 2) b L',
    encLeft_cons_succ (a + 1) b L', encLeft_cons_succ a b L']
  simp only [encRight, sepRight, list_pow_succ, list_pow_zero]
  bb_steps

private theorem peel_D_four (k r₀ : ℕ) (b : Bool) (L' : List (ℕ × Bool))
    (R : List (ℕ × Fin 3)) :
    (encode (.D ((4 * k + r₀, b) :: L') R)) [target]⊢*
      encode (.D ((r₀, b) :: L') (List.replicate k (2, (0 : Fin 3)) ++ R)) := by
  induction k generalizing R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, List.replicate, List.nil_append]
    bb_refl
  | succ k ih =>
    have hk : 4 * (k + 1) + r₀ = (4 * k + r₀) + 4 := by omega
    have hrep :
        List.replicate (k + 1) (2, (0 : Fin 3)) ++ R =
          List.replicate k (2, (0 : Fin 3)) ++ ((2, 0) :: R) := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [hk, hrep]
    exact (rule_D_add_four (4 * k + r₀) b L' R).to_star.trans (ih ((2, 0) :: R))

private theorem init_reaches_start : (init []) [target]⊢* encode start := by
  simp only [start, encode, encLeft, encRight, sepRight, list_pow_succ, list_pow_zero]
  bb_steps

private theorem sim_D_rem (r₀ : ℕ) (hr₀ : r₀ < 4) (b : Bool) (L' : List (ℕ × Bool))
    (R₁ : List (ℕ × Fin 3)) :
    stepsOrHalts (encode (.D ((r₀, b) :: L') R₁))
      (if r₀ = 0 then
        match L', b with
        | [], _ => some (.D [] ((0, 0) :: R₁))
        | p :: L'', false => some (.D (p :: L'') ((0, 0) :: R₁))
        | (a₂, b₂) :: L'', true =>
          let Lnext := (a₂ + 1, b₂) :: L''
          match R₁ with
          | [] => runB false 0 true Lnext []
          | (d₁, c₁) :: R₁' => runBR 0 Lnext d₁ c₁ R₁'
      else if r₀ = 1 then
        match L', b with
        | [], _ => some (.D [] ((2, 0) :: R₁))
        | (a₂, b₂) :: L'', false => runB false (a₂ + 1) b₂ L'' ((0, 0) :: R₁)
        | p :: L'', true => some (.D (p :: L'') ((2, 0) :: R₁))
      else if r₀ = 2 then
        match L', b with
        | [], _ => none
        | (a₂, b₂) :: L'', false => runB true a₂ b₂ L'' ((0, 0) :: R₁)
        | _ :: _, true => none
      else
        match L', b with
        | [], _ => some (.D [] ((2, 0) :: R₁))
        | (a₂, b₂) :: L'', false => some (.D ((a₂ + 1, b₂) :: L'') ((0, 0) :: (0, 0) :: R₁))
        | p :: L'', true => some (.D ((0, false) :: p :: L'') ((0, 0) :: (0, 0) :: R₁))) := by
  rcases r₀ with _ | _ | _ | _ | r₀
  · simp only [↓reduceIte]
    rcases L' with _ | ⟨⟨a₂, b₂⟩, L''⟩
    · change (encode (.D [(0, b)] R₁)) [target]⊢⁺ encode (.D [] ((0, 0) :: R₁))
      simp only [encode]
      rw [encLeft_singleton 0 b]
      simp only [encLeft, encRight, sepRight, list_pow_succ, list_pow_zero]
      bb_steps
    · cases b
      · change (encode (.D ((0, false) :: (a₂, b₂) :: L'') R₁)) [target]⊢⁺
          encode (.D ((a₂, b₂) :: L'') ((0, 0) :: R₁))
        simp only [encode, encLeft, encRight, sepRight, list_pow_succ, list_pow_zero]
        bb_steps
      · rcases R₁ with _ | ⟨⟨d₁, c₁⟩, R₁'⟩
        · have h1 :
              (encode (.D ((0, true) :: (a₂, b₂) :: L'') [])) [target]⊢⁺
                cfgB false ((0, true) :: (a₂ + 1, b₂) :: L'') [] := by
            unfold cfgB
            simp only [Bool.false_eq_true, ↓reduceIte, encode, encLeft, encRight,
              encLeft_cons_succ a₂ b₂ L'', list_pow_succ, list_pow_zero]
            bb_steps
          exact stepsOrHalts_trans h1 (sim_runB false 0 true ((a₂ + 1, b₂) :: L'') [])
        · have h1 :
              (encode (.D ((0, true) :: (a₂, b₂) :: L'') ((d₁, c₁) :: R₁'))) [target]⊢⁺
                cfgBR (prepend00 0 (push01 ((a₂ + 1, b₂) :: L''))) ((d₁, c₁) :: R₁') := by
            unfold cfgBR
            simp only [prepend00, push01, encode, encLeft, encLeft_cons_succ a₂ b₂ L'',
              list_pow_succ, list_pow_zero]
            bb_steps
          exact stepsOrHalts_trans h1 (sim_runBR 0 ((a₂ + 1, b₂) :: L'') d₁ c₁ R₁')
  · simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false]
    rcases L' with _ | ⟨⟨a₂, b₂⟩, L''⟩
    · change (encode (.D [(1, b)] R₁)) [target]⊢⁺ encode (.D [] ((2, 0) :: R₁))
      simp only [encode]
      rw [encLeft_singleton 1 b]
      simp only [encLeft, encRight, sepRight, list_pow_succ, list_pow_zero]
      bb_steps
    · cases b
      · have h1 :
            (encode (.D ((1, false) :: (a₂, b₂) :: L'') R₁)) [target]⊢⁺
              cfgB false ((a₂ + 1, b₂) :: L'') ((0, 0) :: R₁) := by
          unfold cfgB
          simp only [Bool.false_eq_true, ↓reduceIte, encode, encLeft, encRight, sepRight,
            encLeft_cons_succ a₂ b₂ L'', list_pow_succ, list_pow_zero]
          bb_steps
        exact stepsOrHalts_trans h1 (sim_runB false (a₂ + 1) b₂ L'' ((0, 0) :: R₁))
      · change (encode (.D ((1, true) :: (a₂, b₂) :: L'') R₁)) [target]⊢⁺
          encode (.D ((a₂, b₂) :: L'') ((2, 0) :: R₁))
        simp only [encode, encLeft, encRight, sepRight, list_pow_succ, list_pow_zero]
        bb_steps
  · simp only [↓reduceIte, Nat.reduceEqDiff]
    rcases L' with _ | ⟨⟨a₂, b₂⟩, L''⟩
    · refine ⟨Cfg.headLeft C default ([1, 0, 0, 1, 0] +> encRight R₁), ?_, by bb_halt⟩
      simp only [encode]
      rw [encLeft_singleton 2 b]
      simp only [list_pow_succ, list_pow_zero]
      bb_steps
    · cases b
      · have h1 :
            (encode (.D ((2, false) :: (a₂, b₂) :: L'') R₁)) [target]⊢⁺
              cfgB true ((a₂, b₂) :: L'') ((0, 0) :: R₁) := by
          unfold cfgB
          simp only [↓reduceIte, encode, encLeft, encRight, sepRight, list_pow_succ, list_pow_zero]
          bb_steps
        exact stepsOrHalts_trans h1 (sim_runB true a₂ b₂ L'' ((0, 0) :: R₁))
      · refine ⟨Cfg.headLeft C ([0] +> encLeft ((a₂, b₂) :: L''))
          ([1, 0, 0, 1, 0] +> encRight R₁), ?_, by bb_halt⟩
        simp only [encode, encLeft, list_pow_succ, list_pow_zero]
        bb_steps
  · simp only [↓reduceIte, Nat.reduceEqDiff]
    rcases L' with _ | ⟨⟨a₂, b₂⟩, L''⟩
    · change (encode (.D [(3, b)] R₁)) [target]⊢⁺ encode (.D [] ((2, 0) :: R₁))
      simp only [encode]
      rw [encLeft_singleton 3 b]
      simp only [encLeft, encRight, sepRight, list_pow_succ, list_pow_zero]
      bb_steps
    · cases b
      · change (encode (.D ((3, false) :: (a₂, b₂) :: L'') R₁)) [target]⊢⁺
          encode (.D ((a₂ + 1, b₂) :: L'') ((0, 0) :: (0, 0) :: R₁))
        simp only [encode, encLeft, encRight, sepRight, encLeft_cons_succ a₂ b₂ L'',
          list_pow_succ, list_pow_zero]
        bb_steps
      · change (encode (.D ((3, true) :: (a₂, b₂) :: L'') R₁)) [target]⊢⁺
          encode (.D ((0, false) :: (a₂, b₂) :: L'') ((0, 0) :: (0, 0) :: R₁))
        simp only [encode, encLeft, encRight, sepRight, list_pow_succ, list_pow_zero]
        bb_steps
  · omega

private theorem sim_next (s : State) : stepsOrHalts (encode s) (next s) := by
  rcases s with ⟨_ | ⟨⟨a, b⟩, L'⟩, R⟩
  · rcases R with _ | ⟨⟨d₁, c₁⟩, R'⟩
    · change (encode (.D [] [])) [target]⊢⁺ encode (.D [(0, false)] [(1, 0)])
      simp only [encode, encLeft, encRight, sepRight, list_pow_succ, list_pow_zero]
      bb_steps
    · simp only [next]
      have h1 :
          (encode (.D [] ((d₁, c₁) :: R'))) [target]⊢⁺
            cfgBR (prepend00 0 (push01 [])) ((d₁ + 1, c₁) :: R') := by
        unfold cfgBR
        simp only [prepend00, push01, encode, encLeft, encRight_cons_succ d₁ c₁ R',
          list_pow_succ, list_pow_zero]
        bb_steps
      exact stepsOrHalts_trans h1 (sim_runBR 0 [] (d₁ + 1) c₁ R')
  · simp only [next]
    have ha : a = 4 * (a / 4) + a % 4 := by omega
    have hpeel := peel_D_four (a / 4) (a % 4) b L' R
    rw [← ha] at hpeel
    exact stepsOrHalts_of_star hpeel
      (sim_D_rem (a % 4) (Nat.mod_lt a (by decide)) b L'
        (List.replicate (a / 4) (2, (0 : Fin 3)) ++ R))

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start (fun s => ?_)
  have hs := sim_next s
  rcases h : next s with _ | s' <;> simpa [stepsOrHalts, h] using hs

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB
