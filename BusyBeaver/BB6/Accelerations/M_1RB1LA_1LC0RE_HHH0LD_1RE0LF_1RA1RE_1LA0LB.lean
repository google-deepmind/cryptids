/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB`.

Left-stack digits $L = [a_0, a_1, \dots]$ encode unary blocks $1^{a_i + 1}$ separated by single
zeros (`encStack`), and right-stack digits $R = [d_0, d_1, \dots]$ encode unary blocks
$1^{d_i + 1}$ separated by `000` (`encRight`), both ordered from the tape head outward. Every
reachable `B` stack is non-empty and has no interior zeros (`toLeft pre bot` maps `(pre, bot)` to
`(p_0 + 1) :: \dots :: [bot]`). Starting from `init []`, the machine reaches $B([], 0, [])$ in 1
raw step.

## Accelerated Transition Rules

```text
toLeft([], bot)        = [bot]
toLeft(p :: pre, bot)  = (p + 1) :: toLeft(pre, bot)

drainPos(a, pre, bot, [])      = B((a + 2) :: pre, bot, [])
drainPos(a, pre, bot, r :: R)  = drainPos(r, a :: pre', bot', R)
                                 where (pre', bot') = bumpPosBy(1, pre, bot)

peelOnes(1 :: pre, bot, d, R)  = peelOnes(pre, bot, 0, d :: R)
peelOnes([], 2, d, R)          = Halt
peelOnes([], 0, d, R)          = drainPos(d, [], 0, R)
peelOnes([], 1, d, R)          = B([d, 0], 0, R) if d < 2 else drainPos(d - 2, [0], 0, R)
peelOnes([], b + 3, d + 1, R)  = drainPos(d, [b], 0, R)
peelOnes([], b + 3, 0, R)      = stride-2 countdown by m = b / 2, then exit / drainPos
peelOnes(0 :: pre, bot, d, R)  = C(1) exit on cOneTail(pre, bot) (via drainPos if d >= 2)
peelOnes((b+2) :: pre, bot, ..)= drainPos if d >= 1, else stride-2 countdown by m = b / 2

B(pre, bot, [])      -> peelOnes(pre, bot, 0, [])
B(pre, bot, r :: R)  -> peelOnes(pre, bot, r + 1, R)

Start: B([], 0, []), reached after 1 raw TM step
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Encode a right digit stack `s` as `1^{d+1} 000 ...` from the tape head outward. -/
def encRight (s : List ℕ) : ListBlank (Fin 2) :=
  List.rec default
    (fun d _ ih =>
      ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) (ListBlank.append [0, 0, 0] ih))
    s

/-- Reconstruct a non-empty shielded-zero left stack from positive prefix `pre` and bottom `bot`. -/
def toLeft : List ℕ → ℕ → List ℕ
  | [], bot => [bot]
  | p :: pre, bot => (p + 1) :: toLeft pre bot

/-- Add `k` to the top digit of `toLeft pre bot` in `(pre, bot)` coordinates. -/
def bumpPosBy (k : ℕ) : List ℕ → ℕ → List ℕ × ℕ
  | [], bot => ([], bot + k)
  | p :: pre, bot => ((p + k) :: pre, bot)

/-- Tail update `(headDigit L + 1) :: bumpHead L.tail` for `L = toLeft pre bot`. -/
def cOneTail : List ℕ → ℕ → List ℕ × ℕ
  | [], bot => ([bot + 1], 0)
  | p :: pre, bot =>
    let (pre', bot') := bumpPosBy 1 pre bot
    ((p + 2) :: pre', bot')

/-- Symbolic state space for the accelerated stack transition system of `target`. -/
inductive State where
  /-- Configuration `B(pre, bot, R)`: state `B` on `0` between `toLeft pre bot` and `R`. -/
  | B (pre : List ℕ) (bot : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

/-- Sweep all digits of `R` into `B((a + 3) :: toLeft pre bot, R)` until the right stack is `[]`. -/
def drainPos (a : ℕ) (pre : List ℕ) (bot : ℕ) (R : List ℕ) : State :=
  let t := R.foldl
    (fun t r => let p := bumpPosBy 1 t.2.1 t.2.2; (r, t.1 :: p.1, p.2))
    (a, pre, bot)
  .B ((t.1 + 2) :: t.2.1) t.2.2 []

/-- Peel leading `2`s (`1`s in `pre`) in `C` and contract the countdown / return sweep. -/
def peelOnes : List ℕ → ℕ → ℕ → List ℕ → Option State
  | [], 2, _, _ => none
  | [], 0, d, R => some (drainPos d [] 0 R)
  | [], 1, 0, R => some (.B [0, 0] 0 R)
  | [], 1, 1, R => some (.B [1, 0] 0 R)
  | [], 1, d + 2, R => some (drainPos d [0] 0 R)
  | [], b + 3, d + 1, R => some (drainPos d [b] 0 R)
  | [], b + 3, 0, R =>
    let m := b / 2
    let R₂ := bumpHeadBy m R
    if b % 2 = 1 then
      some (.B [1, 1] m R₂)
    else
      List.casesOn R₂ (some (.B [1, 0] m [])) fun r₂ R₂' => some (drainPos r₂ [m + 3] 1 R₂')
  | 0 :: pre, bot, 0, R =>
    let (pre₁, bot₁) := cOneTail pre bot
    some (.B (0 :: pre₁) bot₁ R)
  | 0 :: pre, bot, 1, R =>
    let (pre₁, bot₁) := cOneTail pre bot
    some (.B (1 :: pre₁) bot₁ R)
  | 0 :: pre, bot, d + 2, R =>
    let (pre₁, bot₁) := cOneTail pre bot
    some (drainPos d pre₁ bot₁ R)
  | 1 :: pre, bot, d, R => peelOnes pre bot 0 (d :: R)
  | (b + 2) :: pre, bot, d + 1, R =>
    let (pre₁, bot₁) := bumpPosBy 1 pre bot
    some (drainPos d (b :: pre₁) bot₁ R)
  | (b + 2) :: pre, bot, 0, R =>
    let m := b / 2
    let (pre₂, bot₂) := bumpPosBy m pre bot
    let R₂ := bumpHeadBy m R
    if b % 2 = 1 then
      let (pre₃, bot₃) := bumpPosBy 1 pre₂ bot₂
      some (.B (1 :: 1 :: pre₃) bot₃ R₂)
    else
      List.casesOn R₂
        (let (pre₃, bot₃) := bumpPosBy 1 pre₂ bot₂; some (.B (1 :: 0 :: pre₃) bot₃ []))
        fun r₂ R₂' =>
          some (List.casesOn pre₂ (drainPos r₂ [bot₂ + 4] 1 R₂') fun q qs =>
            let (pre₃, bot₃) := bumpPosBy 2 qs bot₂
            drainPos r₂ ((q + 5) :: pre₃) bot₃ R₂')

/-- Initial symbolic state `B([], 0, [])`, reached from `init []` in 1 raw step. -/
def start : State := .B [] 0 []

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .B pre bot R => Cfg.headRight B (encStack (toLeft pre bot)) (ListBlank.cons 0 (encRight R))

/-- Accelerated transition function (`none` indicates halting, reached when all digits are `2`). -/
def next : State → Option State
  | .B pre bot [] => peelOnes pre bot 0 []
  | .B pre bot (r :: R) => peelOnes pre bot (r + 1) R

/-! ## Coordinate Identities and Stack Encoding Helpers -/

private def headDigit : List ℕ → ℕ
  | [] => 0
  | a :: _ => a + 1

private theorem bumpHead_eq (s : List ℕ) : bumpHead s = headDigit s :: s.tail := by
  cases s <;> rfl

private theorem bumpHeadBy_cons (k x : ℕ) (xs : List ℕ) :
    bumpHeadBy k (x :: xs) = (x + k) :: xs := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [bumpHeadBy, bumpHead]
    rw [ih, show x + 1 + k = x + (k + 1) by omega]

private theorem bumpHead_bumpHeadBy_nil (m : ℕ) : bumpHead (bumpHeadBy m []) = [m] := by
  rcases m with _ | m
  · rfl
  · simp only [bumpHeadBy, bumpHead, bumpHeadBy_cons, Nat.zero_add]

private theorem toLeft_bumpPosBy (k : ℕ) (pre : List ℕ) (bot : ℕ) :
    toLeft (bumpPosBy k pre bot).1 (bumpPosBy k pre bot).2 = bumpHeadBy k (toLeft pre bot) := by
  rcases pre with _ | ⟨p, qs⟩
  · rcases k with _ | k
    · simp [bumpPosBy, bumpHeadBy, toLeft]
    · simp only [bumpPosBy, toLeft, bumpHeadBy, bumpHead, bumpHeadBy_cons]
      rw [show bot + 1 + k = bot + (k + 1) by omega]
  · simp only [bumpPosBy, toLeft, bumpHeadBy_cons]
    rw [show p + k + 1 = p + 1 + k by omega]

private theorem toLeft_cOneTail (pre : List ℕ) (bot : ℕ) :
    toLeft (cOneTail pre bot).1 (cOneTail pre bot).2 =
      (headDigit (toLeft pre bot) + 1) :: bumpHead (toLeft pre bot).tail := by
  rcases pre with _ | ⟨p, qs⟩
  · rfl
  · simp only [cOneTail, toLeft, headDigit, List.tail]
    have h1 := toLeft_bumpPosBy 1 qs bot
    simp only [bumpHeadBy] at h1
    rw [h1]

private theorem encStack_cons_one (L : List ℕ) :
    ListBlank.cons 1 (encStack L) = encStack (bumpHead L) := by
  cases L with
  | nil => simp [bumpHead, encStack, list_pow_one]
  | cons a L' =>
    simp only [bumpHead, encStack]
    rw [ListBlank.append_pow_succ]
    rfl

private theorem encRight_nil : encRight [] = default := rfl

private theorem encRight_cons (d : ℕ) (s : List ℕ) :
    encRight (d :: s) =
      ListBlank.append (([1] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [0, 0, 0] (encRight s)) := rfl

private theorem encRight_cons_one (R : List ℕ) :
    ListBlank.cons 1 (encRight R) = encRight (bumpHead R) := by
  cases R with
  | nil => simp [bumpHead, encRight_nil, encRight_cons, list_pow_one]
  | cons d R' =>
    simp only [bumpHead, encRight_cons]
    rw [ListBlank.append_pow_succ]
    rfl

private theorem walk_A_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ k)) <{{A}} r) [target]⊢*
      (l <{{A}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => bb_refl
  | succ k ih =>
    have h1 :
        ((l <+ (([1] : List (Fin 2)) ^ (k + 1))) <{{A}} r) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ k)) <{{A}} ([1] +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l ([1] +> r)
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

private theorem walk_E_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{E}}> ((([1] : List (Fin 2)) ^ k) +> r)) [target]⊢*
      ((l <+ (([1] : List (Fin 2)) ^ k)) {{E}}> r) := by
  induction k generalizing l r with
  | zero => bb_refl
  | succ k ih =>
    have h1 :
        (l {{E}}> ((([1] : List (Fin 2)) ^ (k + 1)) +> r)) [target]⊢⁺
          (([1] +> l) {{E}}> ((([1] : List (Fin 2)) ^ k) +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih ([1] +> l) r
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

/-! ## Intermediate Configurations and Local Rules -/

private def cfgB (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B (encStack L) (ListBlank.cons 0 (encRight R))

private def cfgC (L : List ℕ) (d : ℕ) (R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft C (encStack L) (encRight (d :: R))

private theorem rule_B_to_C (L R : List ℕ) :
    (cfgB L R) [target]⊢⁺ (cfgC L (headDigit R) R.tail) := by
  unfold cfgB cfgC
  rw [← bumpHead_eq R, ← encRight_cons_one]
  bb_steps

private theorem halt_C_nil (d : ℕ) (R : List ℕ) :
    ∃ cfg', ReachesStar target (cfgC [] d R) cfg' ∧ (step target cfg').isNone := by
  refine ⟨cfgC [] d R, ReachesStar.refl _ _, ?_⟩
  unfold cfgC
  simp only [encStack]
  bb_halt

private theorem encStack_zero (L : List ℕ) :
    encStack (0 :: L) = ListBlank.cons 1 (ListBlank.cons 0 (encStack L)) := by
  simp [encStack, list_pow_one]

private theorem encStack_succ (a : ℕ) (L : List ℕ) :
    encStack ((a + 1) :: L) = ListBlank.cons 1 (encStack (a :: L)) := by
  simp only [encStack]
  rw [ListBlank.append_pow_succ]
  rfl

private theorem finish_E_to_B (d : ℕ) (L R : List ℕ) :
    ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ d)) {{E}}>
      (ListBlank.append [0, 0, 0] (encRight R))) [target]⊢⁺
      (cfgB ((d + 1) :: L) R) := by
  unfold cfgB
  rw [encStack_succ d L]
  simp only [encStack]
  rw [ListBlank.append_pow_succ]
  bb_steps

private theorem rule_C_zero_nil (d : ℕ) (R : List ℕ) :
    (cfgC [0] d R) [target]⊢⁺ (cfgB [d + 3, 0] R) := by
  unfold cfgC
  have h_pre :
      (Cfg.headLeft C (encStack [0]) (encRight (d :: R))) [target]⊢⁺
        ((((encStack []).cons 0) <+ (([1] : List (Fin 2)) ^ 2)) <{{A}}
          ((([1] : List (Fin 2)) ^ (d + 1)) +> (ListBlank.append [0, 0, 0] (encRight R)))) := by
    rw [encStack_zero]
    simp only [encStack, encRight_cons]
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) 1, list_pow_one,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
    bb_steps
  have h_a := walk_A_left 2 ((encStack []).cons 0)
    ((([1] : List (Fin 2)) ^ (d + 1)) +> (ListBlank.append [0, 0, 0] (encRight R)))
  have h_sum :
      ((([1] : List (Fin 2)) ^ 2) +>
        ((([1] : List (Fin 2)) ^ (d + 1)) +> (ListBlank.append [0, 0, 0] (encRight R)))) =
        ListBlank.cons 1 ((([1] : List (Fin 2)) ^ (d + 2)) +>
          (ListBlank.append [0, 0, 0] (encRight R))) := by
    rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (d + 1),
      show 2 + (d + 1) = (d + 2) + 1 by omega,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) (d + 2)]
    rfl
  have h12 := h_pre.trans_star h_a
  rw [h_sum] at h12
  have h_mid :
      (((encStack []).cons 0) <{{A}}
        (ListBlank.cons 1 ((([1] : List (Fin 2)) ^ (d + 2)) +>
          (ListBlank.append [0, 0, 0] (encRight R))))) [target]⊢⁺
        (((encStack [0]).cons 0) {{E}}>
          ((([1] : List (Fin 2)) ^ (d + 2)) +> (ListBlank.append [0, 0, 0] (encRight R)))) := by
    rw [encStack_zero]
    simp only [encStack]
    bb_steps
  have h_e := walk_E_right (d + 2) ((encStack [0]).cons 0)
    (ListBlank.append [0, 0, 0] (encRight R))
  exact ((h12.trans h_mid).trans_star h_e).trans (finish_E_to_B (d + 2) [0] R)

private theorem encStack_decomp (L : List ℕ) :
    encStack L = (((encStack L.tail).cons 0) <+ (([1] : List (Fin 2)) ^ headDigit L)) := by
  cases L with
  | nil => simp [encStack, headDigit]
  | cons a L' => rfl

private theorem rule_C_one (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfgC (1 :: L) d R) [target]⊢⁺
      (cfgB ((d + 1) :: (headDigit L + 1) :: bumpHead L.tail) R) := by
  unfold cfgC
  have h_pre :
      (Cfg.headLeft C (encStack (1 :: L)) (encRight (d :: R))) [target]⊢⁺
        ((((encStack L.tail).cons 0) <+ (([1] : List (Fin 2)) ^ headDigit L)) <{{A}}
          (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 0 (encRight (d :: R)))))) := by
    rw [encStack_succ 0 L, encStack_zero L, ← encStack_decomp L]
    bb_steps
  have h_a := walk_A_left (headDigit L) ((encStack L.tail).cons 0)
    (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 0 (encRight (d :: R)))))
  have h_ones :
      ((([1] : List (Fin 2)) ^ headDigit L) +>
        (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 0 (encRight (d :: R)))))) =
        ListBlank.cons 1 ((([1] : List (Fin 2)) ^ headDigit L) +>
          (ListBlank.cons 0 (ListBlank.cons 0 (encRight (d :: R))))) := by
    change ((([1] : List (Fin 2)) ^ headDigit L) +>
        (([1] : List (Fin 2)) +> (ListBlank.cons 0 (ListBlank.cons 0 (encRight (d :: R)))))) = _
    rw [ListBlank.append_pow_comm]
    rfl
  have h12 := h_pre.trans_star h_a
  rw [h_ones] at h12
  have h_mid1 :
      (((encStack L.tail).cons 0) <{{A}}
        (ListBlank.cons 1 ((([1] : List (Fin 2)) ^ headDigit L) +>
          (ListBlank.cons 0 (ListBlank.cons 0 (encRight (d :: R))))))) [target]⊢⁺
        (((encStack (bumpHead L.tail)).cons 0) {{E}}>
          ((([1] : List (Fin 2)) ^ headDigit L) +>
            (ListBlank.cons 0 (ListBlank.cons 0 (encRight (d :: R)))))) := by
    rw [← encStack_cons_one]
    bb_steps
  have h_e1 := walk_E_right (headDigit L) ((encStack (bumpHead L.tail)).cons 0)
    (ListBlank.cons 0 (ListBlank.cons 0 (encRight (d :: R))))
  have h_mid2 :
      ((((encStack (bumpHead L.tail)).cons 0) <+ (([1] : List (Fin 2)) ^ headDigit L)) {{E}}>
        (ListBlank.cons 0 (ListBlank.cons 0 (encRight (d :: R))))) [target]⊢⁺
        (((encStack ((headDigit L + 1) :: bumpHead L.tail)).cons 0) {{E}}>
          ((([1] : List (Fin 2)) ^ d) +> (ListBlank.append [0, 0, 0] (encRight R)))) := by
    rw [encStack_succ (headDigit L) (bumpHead L.tail)]
    simp only [encStack, encRight_cons]
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (headDigit L),
      ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
    bb_steps
  have h_e2 := walk_E_right d ((encStack ((headDigit L + 1) :: bumpHead L.tail)).cons 0)
    (ListBlank.append [0, 0, 0] (encRight R))
  exact ((((h12.trans h_mid1).trans_star h_e1).trans h_mid2).trans_star h_e2).trans
    (finish_E_to_B d ((headDigit L + 1) :: bumpHead L.tail) R)

private theorem rule_C_two (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfgC (2 :: L) d R) [target]⊢⁺ (cfgC L 0 (d :: R)) := by
  unfold cfgC
  rw [encStack_succ 1 L, encStack_succ 0 L, encStack_zero L]
  simp only [encRight_cons]
  rw [list_pow_one]
  bb_steps

private theorem rule_C_three (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfgC (3 :: L) d R) [target]⊢⁺ (cfgB ((d + 2) :: 1 :: bumpHead L) R) := by
  unfold cfgC
  have h_pre :
      (Cfg.headLeft C (encStack (3 :: L)) (encRight (d :: R))) [target]⊢⁺
        (((encStack (1 :: bumpHead L)).cons 0) {{E}}> (encRight (d :: R))) := by
    rw [encStack_succ 2 L, encStack_succ 1 L, encStack_succ 0 L, encStack_zero L,
      encStack_succ 0 (bumpHead L), encStack_zero (bumpHead L), ← encStack_cons_one]
    bb_steps
  have h_e :
      (((encStack (1 :: bumpHead L)).cons 0) {{E}}> (encRight (d :: R))) [target]⊢*
        ((((encStack (1 :: bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ (d + 1))) {{E}}>
          (ListBlank.append [0, 0, 0] (encRight R))) := by
    simp only [encRight_cons]
    exact walk_E_right (d + 1) ((encStack (1 :: bumpHead L)).cons 0)
      (ListBlank.append [0, 0, 0] (encRight R))
  exact (h_pre.trans_star h_e).trans (finish_E_to_B (d + 1) (1 :: bumpHead L) R)

private theorem rule_C_ge4 (a : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfgC ((a + 4) :: L) d R) [target]⊢⁺ (cfgB (1 :: a :: L) (d :: R)) := by
  unfold cfgC cfgB
  rw [encStack_succ (a + 3) L, encStack_succ (a + 2) L, encStack_succ (a + 1) L, encStack_succ a L,
    encStack_succ 0 (a :: L), encStack_zero (a :: L)]
  bb_steps

/-! ## Countdown, Odd-Drain, and `drainPos` Contractions -/

private theorem rule_C_ge4_contract (a : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfgC ((a + 4) :: L) d R) [target]⊢⁺ (cfgB ((d + 2) :: (a + 2) :: bumpHead L) R) := by
  have h1 := rule_C_ge4 a L d R
  have h2 := rule_B_to_C (1 :: a :: L) (d :: R)
  simp only [headDigit, List.tail] at h2
  have h3 := rule_C_one (a :: L) (d + 1) R
  simp only [headDigit, List.tail] at h3
  exact (h1.trans h2).trans h3

private theorem rule_C_ge3_pos (b : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfgC ((b + 3) :: L) (d + 1) R) [target]⊢⁺
      (cfgB ((d + 3) :: (b + 1) :: bumpHead L) R) := by
  rcases b with _ | b'
  · exact rule_C_three L (d + 1) R
  · rw [show b' + 1 + 3 = b' + 4 by omega]
    exact rule_C_ge4_contract b' L (d + 1) R

private theorem countdown_step (a : ℕ) (L R : List ℕ) :
    (cfgC ((a + 4) :: L) 0 R) [target]⊢⁺ (cfgC ((a + 2) :: bumpHead L) 0 (bumpHead R)) := by
  have h1 := rule_C_ge4_contract a L 0 R
  have h2 := rule_B_to_C (2 :: (a + 2) :: bumpHead L) R
  have h3 := rule_C_two ((a + 2) :: bumpHead L) (headDigit R) R.tail
  rw [← bumpHead_eq R] at h3
  exact (h1.trans h2).trans h3

private theorem countdown_loop (m a : ℕ) (L R : List ℕ) :
    (cfgC ((a + 2 * m + 2) :: L) 0 R) [target]⊢*
      (cfgC ((a + 2) :: bumpHeadBy m L) 0 (bumpHeadBy m R)) := by
  induction m generalizing L R with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, bumpHeadBy]
    bb_refl
  | succ m ih =>
    rw [show a + 2 * (m + 1) + 2 = (a + 2 * m) + 4 by omega, bumpHeadBy, bumpHeadBy]
    exact ((countdown_step (a + 2 * m) L R).trans_star (ih (bumpHead L) (bumpHead R))).to_star

private theorem rule_C_three_zero_contract (L R : List ℕ) :
    (cfgC (3 :: L) 0 R) [target]⊢⁺ (cfgC (1 :: bumpHead L) 0 (bumpHead R)) := by
  have h1 := rule_C_three L 0 R
  have h2 := rule_B_to_C (2 :: 1 :: bumpHead L) R
  have h3 := rule_C_two (1 :: bumpHead L) (headDigit R) R.tail
  rw [← bumpHead_eq R] at h3
  exact (h1.trans h2).trans h3

private theorem b_ge3_step (a : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ) :
    (cfgB ((a + 3) :: L) (r :: R)) [target]⊢⁺ (cfgB ((r + 3) :: (a + 1) :: bumpHead L) R) := by
  have h1 := rule_B_to_C ((a + 3) :: L) (r :: R)
  simp only [headDigit, List.tail] at h1
  exact h1.trans (rule_C_ge3_pos a L r R)

private theorem reaches_drainPos (a : ℕ) (pre : List ℕ) (bot : ℕ) (R : List ℕ) :
    (cfgB ((a + 3) :: toLeft pre bot) R) [target]⊢* (encode (drainPos a pre bot R)) := by
  induction R generalizing a pre bot with
  | nil =>
    simp only [drainPos, List.foldl_nil, encode, cfgB, toLeft]
    bb_refl
  | cons r R ih =>
    have h1 := b_ge3_step a (toLeft pre bot) r R
    have h_tl := toLeft_bumpPosBy 1 pre bot
    simp only [bumpHeadBy] at h_tl
    have h2 := ih r (a :: (bumpPosBy 1 pre bot).1) (bumpPosBy 1 pre bot).2
    simp only [toLeft] at h2
    rw [h_tl] at h2
    exact (h1.trans_star h2).to_star

private theorem c_three_odd_singleton (m r₂ : ℕ) (R₂' : List ℕ) :
    (cfgC (3 :: bumpHeadBy m []) 0 (r₂ :: R₂')) [target]⊢⁺
      (encode (drainPos r₂ [m + 3] 1 R₂')) := by
  have h1 := rule_C_three_zero_contract (bumpHeadBy m []) (r₂ :: R₂')
  rw [bumpHead_bumpHeadBy_nil] at h1
  simp only [bumpHead] at h1
  have h2 := rule_C_one [m] 0 ((r₂ + 1) :: R₂')
  simp only [headDigit, List.tail, bumpHead] at h2
  have h3 := rule_B_to_C [1, m + 2, 0] ((r₂ + 1) :: R₂')
  simp only [headDigit, List.tail] at h3
  have h4 := rule_C_one [m + 2, 0] (r₂ + 2) R₂'
  simp only [headDigit, List.tail, bumpHead] at h4
  have h_pre := ((h1.trans h2).trans h3).trans h4
  have h_dr := reaches_drainPos r₂ [m + 3] 1 R₂'
  simp only [toLeft] at h_dr
  rw [show m + 2 + 1 + 1 = m + 4 by omega] at h_pre
  exact h_pre.trans_star h_dr

private theorem c_three_odd_cons (pre₂ : List ℕ) (bot₂ r₂ : ℕ) (R₂' : List ℕ) :
    (cfgC (3 :: toLeft pre₂ bot₂) 0 (r₂ :: R₂')) [target]⊢⁺
      (encode (List.casesOn pre₂ (drainPos r₂ [bot₂ + 4] 1 R₂') fun q qs =>
        let (pre₃, bot₃) := bumpPosBy 2 qs bot₂
        drainPos r₂ ((q + 5) :: pre₃) bot₃ R₂')) := by
  rcases pre₂ with _ | ⟨q, qs⟩
  · simp only [toLeft]
    have h1 := rule_C_three_zero_contract [bot₂] (r₂ :: R₂')
    simp only [bumpHead] at h1
    have h2 := rule_C_one [bot₂ + 1] 0 ((r₂ + 1) :: R₂')
    simp only [headDigit, List.tail, bumpHead] at h2
    have h3 := rule_B_to_C [1, bot₂ + 3, 0] ((r₂ + 1) :: R₂')
    simp only [headDigit, List.tail] at h3
    have h4 := rule_C_one [bot₂ + 3, 0] (r₂ + 2) R₂'
    simp only [headDigit, List.tail, bumpHead] at h4
    have h_pre := ((h1.trans h2).trans h3).trans h4
    have h_dr := reaches_drainPos r₂ [bot₂ + 4] 1 R₂'
    simp only [toLeft] at h_dr
    rw [show bot₂ + 3 + 1 + 1 = bot₂ + 5 by omega] at h_pre
    exact h_pre.trans_star h_dr
  · simp only [toLeft]
    have h1 := rule_C_three_zero_contract ((q + 1) :: toLeft qs bot₂) (r₂ :: R₂')
    simp only [bumpHead] at h1
    have h2 := rule_C_one ((q + 2) :: toLeft qs bot₂) 0 ((r₂ + 1) :: R₂')
    simp only [headDigit, List.tail] at h2
    have h3 := rule_B_to_C (1 :: (q + 4) :: bumpHead (toLeft qs bot₂)) ((r₂ + 1) :: R₂')
    simp only [headDigit, List.tail] at h3
    have h4 := rule_C_one ((q + 4) :: bumpHead (toLeft qs bot₂)) (r₂ + 2) R₂'
    simp only [headDigit, List.tail] at h4
    have h_pre := ((h1.trans h2).trans h3).trans h4
    have h_dr := reaches_drainPos r₂ ((q + 5) :: (bumpPosBy 2 qs bot₂).1)
      (bumpPosBy 2 qs bot₂).2 R₂'
    have h_tl := toLeft_bumpPosBy 2 qs bot₂
    simp only [bumpHeadBy] at h_tl
    simp only [toLeft] at h_dr
    rw [h_tl] at h_dr
    rw [show q + 4 + 1 + 1 = q + 6 by omega] at h_pre
    exact h_pre.trans_star h_dr

/-! ## Accelerated Step Verification -/

private theorem reaches_peelOnes (pre : List ℕ) (bot d : ℕ) (R : List ℕ) :
    match peelOnes pre bot d R with
    | some s' => ReachesPlus target (cfgC (toLeft pre bot) d R) (encode s')
    | none => ∃ cfg', ReachesStar target (cfgC (toLeft pre bot) d R) cfg' ∧
        (step target cfg').isNone := by
  induction pre generalizing d R with
  | nil =>
    rcases bot with _ | _ | _ | b
    · simp only [peelOnes, toLeft]
      have h1 := rule_C_zero_nil d R
      have h2 := reaches_drainPos d [] 0 R
      simp only [toLeft] at h2
      exact h1.trans_star h2
    · rcases d with _ | _ | d'
      · simp only [peelOnes, toLeft]
        have h1 := rule_C_one [] 0 R
        simpa [headDigit, List.tail, bumpHead, encode, cfgB, toLeft] using h1
      · simp only [peelOnes, toLeft]
        have h1 := rule_C_one [] 1 R
        simpa [headDigit, List.tail, bumpHead, encode, cfgB, toLeft] using h1
      · simp only [peelOnes, toLeft]
        have h1 := rule_C_one [] (d' + 2) R
        simp only [headDigit, List.tail, bumpHead] at h1
        have h2 := reaches_drainPos d' [0] 0 R
        simp only [toLeft] at h2
        exact h1.trans_star h2
    · simp only [peelOnes, toLeft]
      have h1 := rule_C_two [] d R
      obtain ⟨cfg', hstar, hnone⟩ := halt_C_nil 0 (d :: R)
      exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
    · rcases d with _ | d'
      · have h_par : b % 2 = 1 ∨ b % 2 = 0 := by omega
        rcases h_par with hodd | heven
        · simp only [peelOnes, hodd, ↓reduceIte, toLeft]
          have hb : b + 3 = 2 + 2 * (b / 2) + 2 := by omega
          rw [hb]
          have h1 := countdown_loop (b / 2) 2 [] R
          have h2 := rule_C_ge4_contract 0 (bumpHeadBy (b / 2) []) 0 (bumpHeadBy (b / 2) R)
          rw [bumpHead_bumpHeadBy_nil] at h2
          exact h1.trans_plus h2
        · have hb : b + 3 = 1 + 2 * (b / 2) + 2 := by omega
          have h1 := countdown_loop (b / 2) 1 [] R
          rw [← hb] at h1
          rcases hR₂ : bumpHeadBy (b / 2) R with _ | ⟨r₂, R₂'⟩
          · simp only [peelOnes, heven, hR₂, toLeft]
            rw [hR₂] at h1
            have h2 := rule_C_three (bumpHeadBy (b / 2) []) 0 []
            rw [bumpHead_bumpHeadBy_nil] at h2
            exact h1.trans_plus h2
          · simp only [peelOnes, heven, hR₂, toLeft]
            rw [hR₂] at h1
            exact h1.trans_plus (c_three_odd_singleton (b / 2) r₂ R₂')
      · simp only [peelOnes, toLeft]
        have h1 := rule_C_ge3_pos b [] d' R
        simp only [bumpHead] at h1
        have h2 := reaches_drainPos d' [b] 0 R
        simp only [toLeft] at h2
        exact h1.trans_star h2
  | cons p pre ih =>
    rcases p with _ | _ | b
    · rcases d with _ | _ | d'
      · simp only [peelOnes, toLeft]
        have h1 := rule_C_one (toLeft pre bot) 0 R
        rw [← toLeft_cOneTail] at h1
        exact h1
      · simp only [peelOnes, toLeft]
        have h1 := rule_C_one (toLeft pre bot) 1 R
        rw [← toLeft_cOneTail] at h1
        exact h1
      · simp only [peelOnes, toLeft]
        have h1 := rule_C_one (toLeft pre bot) (d' + 2) R
        rw [← toLeft_cOneTail] at h1
        exact h1.trans_star (reaches_drainPos d' (cOneTail pre bot).1 (cOneTail pre bot).2 R)
    · simp only [peelOnes, toLeft]
      have h1 := rule_C_two (toLeft pre bot) d R
      have h2 := ih 0 (d :: R)
      rcases h : peelOnes pre bot 0 (d :: R) with _ | s'
      · rw [h] at h2
        obtain ⟨cfg', hstar, hnone⟩ := h2
        exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
      · rw [h] at h2
        exact h1.trans h2
    · rcases d with _ | d'
      · have h_par : b % 2 = 1 ∨ b % 2 = 0 := by omega
        rcases h_par with hodd | heven
        · simp only [peelOnes, hodd, ↓reduceIte, toLeft]
          have hb : b + 2 + 1 = 2 + 2 * (b / 2) + 2 := by omega
          rw [hb]
          have h1 := countdown_loop (b / 2) 2 (toLeft pre bot) R
          rw [← toLeft_bumpPosBy] at h1
          have h2 := rule_C_ge4_contract 0
            (toLeft (bumpPosBy (b / 2) pre bot).1 (bumpPosBy (b / 2) pre bot).2) 0
            (bumpHeadBy (b / 2) R)
          have h_tl := toLeft_bumpPosBy 1 (bumpPosBy (b / 2) pre bot).1
            (bumpPosBy (b / 2) pre bot).2
          simp only [bumpHeadBy] at h_tl
          rw [← h_tl] at h2
          exact h1.trans_plus h2
        · have hb : b + 2 + 1 = 1 + 2 * (b / 2) + 2 := by omega
          have h1 := countdown_loop (b / 2) 1 (toLeft pre bot) R
          rw [← hb, ← toLeft_bumpPosBy] at h1
          rcases hR₂ : bumpHeadBy (b / 2) R with _ | ⟨r₂, R₂'⟩
          · simp only [peelOnes, heven, hR₂, toLeft]
            rw [hR₂] at h1
            have h2 := rule_C_three
              (toLeft (bumpPosBy (b / 2) pre bot).1 (bumpPosBy (b / 2) pre bot).2) 0 []
            have h_tl := toLeft_bumpPosBy 1 (bumpPosBy (b / 2) pre bot).1
              (bumpPosBy (b / 2) pre bot).2
            simp only [bumpHeadBy] at h_tl
            rw [← h_tl] at h2
            exact h1.trans_plus h2
          · simp only [peelOnes, heven, hR₂, toLeft]
            rw [hR₂] at h1
            exact h1.trans_plus
              (c_three_odd_cons (bumpPosBy (b / 2) pre bot).1 (bumpPosBy (b / 2) pre bot).2
                r₂ R₂')
      · simp only [peelOnes, toLeft]
        have h1 := rule_C_ge3_pos b (toLeft pre bot) d' R
        have h_tl := toLeft_bumpPosBy 1 pre bot
        simp only [bumpHeadBy] at h_tl
        rw [← h_tl] at h1
        have h2 := reaches_drainPos d' (b :: (bumpPosBy 1 pre bot).1) (bumpPosBy 1 pre bot).2 R
        simp only [toLeft] at h2
        exact h1.trans_star h2

private theorem init_reaches_start : (init []) [target]⊢* (encode start) := by
  have h : (init []) [target]⊢⁺ (encode start) := by
    simp only [start, encode, toLeft]
    rw [encStack_zero]
    simp only [encStack, encRight_nil]
    bb_steps
  exact h.to_star

private theorem step_accel (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨pre, bot, _ | ⟨r, R⟩⟩
  · simp only [next]
    have h1 := rule_B_to_C (toLeft pre bot) []
    simp only [headDigit, List.tail] at h1
    have h2 := reaches_peelOnes pre bot 0 []
    rcases h : peelOnes pre bot 0 [] with _ | s'
    · rw [h] at h2
      obtain ⟨cfg', hstar, hnone⟩ := h2
      exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
    · rw [h] at h2
      exact h1.trans h2
  · simp only [next]
    have h1 := rule_B_to_C (toLeft pre bot) (r :: R)
    simp only [headDigit, List.tail] at h1
    have h2 := reaches_peelOnes pre bot (r + 1) R
    rcases h : peelOnes pre bot (r + 1) R with _ | s'
    · rw [h] at h2
      obtain ⟨cfg', hstar, hnone⟩ := h2
      exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
    · rw [h] at h2
      exact h1.trans h2

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next :=
  IsValidAcceleration.of_step init_reaches_start fun s => by
    cases h : next s <;> simpa [h] using step_accel s

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB
