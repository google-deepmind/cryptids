/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA`
(BMO base-3 holdout (#68, `suspect_48`), see
<https://wiki.bbchallenge.org/wiki/1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA>).

Starting from the blank tape (`init []`), the trajectory reaches the five-pattern configuration
system (`P`, `Q`, `R`, `U`, `T`):
$$\begin{aligned}
P(b, k, c) &:= 0^\infty\,1111\,0^b\,\mathrm{F}{>}\,(111)^k\,0\,1^c\,011\,0^\infty, \\
Q(m) &:= 0^\infty\,\mathrm{F}{>}\,(111)^m\,1^9\,011\,0^\infty, \\
R(m) &:= 0^\infty\,\mathrm{F}{>}\,(111)^m\,1^{12}\,0^\infty, \\
U(m) &:= 0^\infty\,1111\,\mathrm{F}{>}\,(111)^m\,1^9\,011\,0^\infty, \\
T(m) &:= 0^\infty\,1111\,0^{12}\,(000)^m\,\mathrm{F}{>}\,01111\,0^\infty
\end{aligned}$$
at $P(4, 0, 11)$ in 233 steps, and every member configuration advances in `ReachesPlus` either to
another member configuration or to a halting configuration.

## Collatz-like Acceleration Rules

```text
Consider:
P(b, k, c) = 0^inf 1111 0^b F> (111)^k 0 1^c 011 0^inf
Q(m)       = 0^inf F> (111)^m 1^9 011 0^inf
R(m)       = 0^inf F> (111)^m 1^12 0^inf
U(m)       = 0^inf 1111 F> (111)^m 1^9 011 0^inf
T(m)       = 0^inf 1111 0^12 (000)^m F> 01111 0^inf

P(0, k, c)     -> P(3k+3, 0, c+2)
P(b+1, k, c+2) -> P(b, k+1, c)
P(b+2, k, 0)   -> P(b, 0, 3k+5)
P(b+2, k, 1)   -> P(b, 0, 3k+8)
P(1, k, 0)     -> Q(k)
P(1, k, 1)     -> Q(k+1)

Q(m)           -> R(m)
R(m)           -> U(m)
U(m)           -> T(m)
T(2)           -> P(7, 2, 18)
T(m)           -> Halt if m != 2

Start: P(4, 0, 11), reached after 233 raw TM steps
```

Composing transitions through $Q(m) \to R(m) \to U(m) \to T(m)$ collapses the system to the single
canonical family $P(b, k, c)$:

```text
Consider:
P(b, k, c) = 0^inf 1111 0^b F> (111)^k 0 1^c 011 0^inf

P(0, k, c)     -> P(3k+3, 0, c+2)
P(b+1, k, c+2) -> P(b, k+1, c)
P(b+2, k, 0)   -> P(b, 0, 3k+5)
P(b+2, k, 1)   -> P(b, 0, 3k+8)
P(1, 2, 0)     -> P(7, 2, 18)
P(1, k, 0)     -> Halt if k != 2
P(1, 1, 1)     -> P(7, 2, 18)
P(1, k, 1)     -> Halt if k != 1

Start: P(4, 0, 11), reached after 233 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Finite Prefix Simulator for Bounded Concrete Traces -/

private structure PState where
  q : Option (Fin 6)
  h : Fin 2
  l : List (Fin 2)
  r : List (Fin 2)
  deriving DecidableEq

private def toCfg (s : PState) (l_tail : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨s.q, ⟨s.h, ListBlank.append s.l l_tail, ListBlank.append s.r default⟩⟩

private def stepPState (s : PState) : Option PState :=
  match s.q with
  | none => none
  | some q =>
    match target q s.h with
    | none => none
    | some (q', Stmt.write w Dir.right) =>
      match s.r with
      | [] => some ⟨q', 0, w :: s.l, []⟩
      | h' :: r_rest => some ⟨q', h', w :: s.l, r_rest⟩
    | some (q', Stmt.write w Dir.left) =>
      match s.l with
      | [] => none
      | h' :: l_rest => some ⟨q', h', l_rest, w :: s.r⟩

private def runPState : ℕ → PState → Option PState
  | 0, s => some s
  | n + 1, s => (stepPState s).bind (runPState n)

private def runPStateChunk (chunk : ℕ) : ℕ → PState → Option PState
  | 0, s => some s
  | k + 1, s => (runPState chunk s).bind (runPStateChunk chunk k)

private def runPStateFast (chunk k rem : ℕ) (s : PState) : Option PState :=
  (runPStateChunk chunk k s).bind (runPState rem)

private theorem stepPState_sound (s s' : PState) (l_tail : ListBlank (Fin 2))
    (h : stepPState s = some s') :
    step target (toCfg s l_tail) = some (toCfg s' l_tail) := by
  rcases s with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q, hq⟩, ⟨_ | _ | h_sym, hh⟩,
    _ | ⟨lh, lt⟩, _ | ⟨rh, rt⟩⟩ <;>
    (try omega) <;>
    (try {
      dsimp [stepPState, target, machine, ConjectureMachines.Machine.toBB,
        ConjectureMachines.Machine.ofRows, ConjectureMachines.listGetD] at h
      cases h }) <;>
    (try {
      dsimp [stepPState, target, machine, ConjectureMachines.Machine.toBB,
        ConjectureMachines.Machine.ofRows, ConjectureMachines.listGetD] at h
      cases h
      simp [toCfg, step, target, machine, ConjectureMachines.Machine.toBB,
        ConjectureMachines.Machine.ofRows, ConjectureMachines.listGetD, Tape.write, Tape.move] })

private theorem runPState_sound (n : ℕ) (s s' : PState) (l_tail : ListBlank (Fin 2))
    (h : runPState n s = some s') :
    multiStep target (toCfg s l_tail) n = some (toCfg s' l_tail) := by
  induction n generalizing s with
  | zero =>
    injection h with h_eq
    subst h_eq
    rfl
  | succ n ih =>
    dsimp [runPState] at h
    rcases hs : stepPState s with _ | s₁
    · rw [hs] at h
      contradiction
    · rw [hs, Option.bind_some] at h
      rw [multiStep_of_step (stepPState_sound s s₁ l_tail hs)]
      exact ih s₁ h

private theorem runPStateChunk_sound (chunk k : ℕ) (s s' : PState)
    (l_tail : ListBlank (Fin 2))
    (h : runPStateChunk chunk k s = some s') :
    multiStep target (toCfg s l_tail) (chunk * k) = some (toCfg s' l_tail) := by
  induction k generalizing s with
  | zero =>
    injection h with h_eq
    subst h_eq
    simp
  | succ k ih =>
    dsimp [runPStateChunk] at h
    rcases hs : runPState chunk s with _ | s₁
    · rw [hs] at h
      contradiction
    · rw [hs, Option.bind_some] at h
      rw [Nat.mul_succ, Nat.add_comm]
      exact multiStep_trans (runPState_sound chunk s s₁ l_tail hs) (ih s₁ h)

private theorem runPStateFast_sound (chunk k rem : ℕ) (s s' : PState)
    (l_tail : ListBlank (Fin 2))
    (h : runPStateFast chunk k rem s = some s') :
    multiStep target (toCfg s l_tail) (chunk * k + rem) = some (toCfg s' l_tail) := by
  dsimp [runPStateFast] at h
  rcases hs : runPStateChunk chunk k s with _ | s₁
  · rw [hs] at h
    contradiction
  · rw [hs, Option.bind_some] at h
    exact multiStep_trans (runPStateChunk_sound chunk k s s₁ l_tail hs)
      (runPState_sound rem s₁ s' l_tail h)

private theorem runPStateFast_halt (chunk k rem : ℕ) (h_pos : chunk * k + rem > 0)
    (s s' : PState) (l_tail : ListBlank (Fin 2))
    (h_run : runPStateFast chunk k rem s = some s')
    (h_q : s'.q = some E) (h_h : s'.h = 1) :
    ∃ cfg', ReachesPlus target (toCfg s l_tail) cfg' ∧ (step target cfg').isNone := by
  refine ⟨toCfg s' l_tail,
    ⟨chunk * k + rem, h_pos, runPStateFast_sound chunk k rem s s' l_tail h_run⟩, ?_⟩
  simp [toCfg, step, h_q, h_h, target, machine, ConjectureMachines.Machine.toBB,
    ConjectureMachines.Machine.ofRows, ConjectureMachines.listGetD]

private theorem checkHalt_sound (chunk k rem : ℕ) (h_pos : chunk * k + rem > 0)
    (s : PState) (l_tail : ListBlank (Fin 2))
    (h : (match runPStateFast chunk k rem s with
      | some s' => decide (s'.q = some E ∧ s'.h = 1)
      | none => false) = true) :
    ∃ cfg', ReachesPlus target (toCfg s l_tail) cfg' ∧ (step target cfg').isNone := by
  rcases h_run : runPStateFast chunk k rem s with _ | s'
  · rw [h_run] at h
    contradiction
  · rw [h_run, decide_eq_true_eq] at h
    exact runPStateFast_halt chunk k rem h_pos s s' l_tail h_run h.1 h.2

/-! ## Shift, Turnaround, and Bounce Lemmas -/

private theorem zero_pow_three_mul (k : ℕ) :
    ([0, 0, 0] : List (Fin 2)) ^ k = ([0] : List (Fin 2)) ^ (3 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, list_pow_add, ih, list_pow_add]
    rfl

private theorem one_pow_three_mul (k : ℕ) :
    ([1, 1, 1] : List (Fin 2)) ^ k = ([1] : List (Fin 2)) ^ (3 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, list_pow_add, ih, list_pow_add]
    rfl

private theorem ones_comm_111 (k : ℕ) (l : ListBlank (Fin 2)) :
    ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] l) =
      ListBlank.append [1] (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) l) := by
  rw [one_pow_three_mul, ListBlank.append_pow_comm]

private theorem zero_pow_default (n : ℕ) :
    ListBlank.append (([0] : List (Fin 2)) ^ n) (default : ListBlank (Fin 2)) = default := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ListBlank.append_pow_succ, ih]
    exact ListBlank.cons_zero_default

/-- Rightward shift across `(111)^k` in state `B`. -/
private theorem shift_B_111 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B l (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight B (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight B l (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight B (ListBlank.append [1, 1, 1] l)
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1, 1] l) =
          ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Rightward shift across `(111)^k` in state `D`, writing `(000)^k`. -/
private theorem shift_D_111 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight D l (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight D (ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight D l (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight D (ListBlank.append [0, 0, 0] l)
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [0, 0, 0] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ k) (ListBlank.append [0, 0, 0] l) =
          ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward shift across `(111)^k` in state `E` over `01`. -/
private theorem shift_E_111 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [0, 1] r))
      (Cfg.headRight E l
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E
            (ListBlank.append [1, 1, 1]
              (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [0, 1] r))
          (Cfg.headRight E
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [0, 1] (ListBlank.append [1, 1, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 1, 1] (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1, 1] r) =
          ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

private theorem step_F_zero (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight F (ListBlank.append [0] l) r)
      (Cfg.headRight B (ListBlank.append [1] l) r) := by
  have hr : r = ListBlank.cons r.head r.tail := (ListBlank.cons_head_tail r).symm
  rw [hr]
  rcases r.head with ⟨_ | _ | v, hv⟩ <;> (try omega) <;> bb_steps

private theorem step_F_to_A (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight F (ListBlank.append [1] l) r)
      (Cfg.headRight A l (ListBlank.append [1] r)) := by
  have hr : r = ListBlank.cons r.head r.tail := (ListBlank.cons_head_tail r).symm
  rw [hr]
  rcases r.head with ⟨_ | _ | v, hv⟩ <;> (try omega) <;> bb_steps

private theorem turnaround_b0_from_A (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append [1, 1, 1] default) (ListBlank.append [1] r))
      (Cfg.headRight D
        (ListBlank.append [0, 0, 0, 0, 0] (ListBlank.append [1, 1, 1, 1] default)) r) := by
  bb_steps

private theorem turnaround_b0 (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight F (ListBlank.append [1, 1, 1, 1] default) r)
      (Cfg.headRight D
        (ListBlank.append [0, 0, 0, 0, 0] (ListBlank.append [1, 1, 1, 1] default)) r) := by
  have h1 := step_F_to_A (ListBlank.append [1, 1, 1] default) r
  exact h1.trans (turnaround_b0_from_A r)

private theorem turnaround_c0 (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight B (ListBlank.append [1] l)
        (ListBlank.append [0, 0, 1, 1] default))
      (Cfg.headRight E l
        (ListBlank.append [0, 1] (ListBlank.append [1, 1, 1, 0, 1, 1] default))) := by
  bb_steps

private theorem turnaround_c1 (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight B (ListBlank.append [1] l)
        (ListBlank.append [0, 1, 0, 1, 1] default))
      (Cfg.headRight E l
        (ListBlank.append [0, 1]
          (ListBlank.append [1, 1, 1, 1, 1, 1, 0, 1, 1] default))) := by
  bb_steps

private theorem step_bounce_111 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight F (ListBlank.append [0] l)
        (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0, 1, 1] r)))
      (Cfg.headRight F l
        (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1))
          (ListBlank.append [0] r))) := by
  have h1 := step_F_zero l
    (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1, 1] r))
  have h2 := shift_B_111 k (ListBlank.append [1] l) (ListBlank.append [0, 1, 1] r)
  have h3 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] l))
          (ListBlank.append [0, 1, 1] r))
        (Cfg.headRight E
          (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] l))
          (ListBlank.append [0, 1] (ListBlank.append [0] r))) := by
    bb_steps
  have h4 := shift_E_111 k (ListBlank.append [1] l) (ListBlank.append [0] r)
  have h5 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append [1] l)
          (ListBlank.append [0, 1]
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append [0] r))))
        (Cfg.headRight F l
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append [0] r)))) := by
    bb_steps
  have h_all := (((h1.trans_star h2).trans h3).trans_star h4).trans h5
  rwa [← ListBlank.append_pow_succ] at h_all

private theorem bounce_b0_left_eq (k : ℕ) (L0 : ListBlank (Fin 2)) :
    ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ k)
      (ListBlank.append [0, 0, 0, 0, 0] L0) =
    ListBlank.append [0, 0]
      (ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ k)
        (ListBlank.append [0, 0, 0] L0)) := by
  rw [ListBlank.append_append, ListBlank.append_append, ListBlank.append_append]
  congr 1
  rw [zero_pow_three_mul]
  change ([0] : List (Fin 2)) ^ (3 * k) ++ ([0] : List (Fin 2)) ^ 5 =
    ([0] : List (Fin 2)) ^ 2 ++ (([0] : List (Fin 2)) ^ (3 * k) ++ ([0] : List (Fin 2)) ^ 3)
  rw [← list_pow_add, ← list_pow_add, ← list_pow_add]
  congr 1
  omega

private theorem step_bounce_b0 (k : ℕ) (s : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight F (ListBlank.append [1, 1, 1, 1] default)
        (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) (ListBlank.append [0] s)))
      (Cfg.headRight F
        (ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ k)
          (ListBlank.append [0, 0, 0] (ListBlank.append [1, 1, 1, 1] default)))
        (ListBlank.append [0, 1, 1] s)) := by
  let L0 := ListBlank.append [1, 1, 1, 1] (default : ListBlank (Fin 2))
  have h1 := turnaround_b0
    (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) (ListBlank.append [0] s))
  have h2 := shift_D_111 k (ListBlank.append [0, 0, 0, 0, 0] L0) (ListBlank.append [0] s)
  rw [bounce_b0_left_eq k L0] at h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append [0, 0]
            (ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ k)
              (ListBlank.append [0, 0, 0] L0)))
          (ListBlank.append [0] s))
        (Cfg.headRight F
          (ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ k)
            (ListBlank.append [0, 0, 0] L0))
          (ListBlank.append [0, 1, 1] s)) := by
    bb_steps
  exact (h1.trans_star h2).trans h3

private theorem step_bounce_c (k : ℕ) (l tail_c r_after : ListBlank (Fin 2))
    (h_turn : ∀ l' : ListBlank (Fin 2),
      ReachesPlus target
        (Cfg.headRight B (ListBlank.append [1] l') tail_c)
        (Cfg.headRight E l' (ListBlank.append [0, 1] r_after))) :
    ReachesPlus target
      (Cfg.headRight F (ListBlank.append [0] (ListBlank.append [0] l))
        (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) tail_c))
      (Cfg.headRight F l
        (ListBlank.append [0, 1, 1]
          (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) r_after))) := by
  have h1 := step_F_zero (ListBlank.append [0] l)
    (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) tail_c)
  have h2 := shift_B_111 k (ListBlank.append [1] (ListBlank.append [0] l)) tail_c
  rw [ones_comm_111 k (ListBlank.append [0] l)] at h2
  have h3 := h_turn
    (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) (ListBlank.append [0] l))
  have h4 := shift_E_111 k (ListBlank.append [0] l) r_after
  have h5 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append [0] l)
          (ListBlank.append [0, 1]
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) r_after)))
        (Cfg.headRight F l
          (ListBlank.append [0, 1, 1]
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) r_after))) := by
    bb_steps
  exact (((h1.trans_star h2).trans h3).trans_star h4).trans h5

private theorem step_bounce_b1_c (k : ℕ) (tail_c r_after : ListBlank (Fin 2))
    (h_turn : ∀ l' : ListBlank (Fin 2),
      ReachesPlus target
        (Cfg.headRight B (ListBlank.append [1] l') tail_c)
        (Cfg.headRight E l' (ListBlank.append [0, 1] r_after))) :
    ReachesPlus target
      (Cfg.headRight F (ListBlank.append [0] (ListBlank.append [1, 1, 1, 1] default))
        (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) tail_c))
      (Cfg.headRight F default
        (ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1)) r_after))) := by
  have h1 := step_F_zero (ListBlank.append [1, 1, 1, 1] default)
    (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k) tail_c)
  have h_eq :
      ListBlank.append [1] (ListBlank.append [1, 1, 1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append [1]
          (ListBlank.append [1, 1, 1] (ListBlank.append [1] default)) := rfl
  rw [h_eq] at h1
  have h2 := shift_B_111 k
    (ListBlank.append [1] (ListBlank.append [1, 1, 1] (ListBlank.append [1] default)))
    tail_c
  rw [ones_comm_111 k (ListBlank.append [1, 1, 1] (ListBlank.append [1] default))] at h2
  have h_pow :
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [1, 1, 1] (ListBlank.append [1] (default : ListBlank (Fin 2)))) =
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1))
        (ListBlank.append [1] default) := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rw [h_pow] at h2
  have h3 := h_turn
    (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [1] default))
  have h4 := shift_E_111 (k + 1) (ListBlank.append [1] default) r_after
  have h5 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append [1] default)
          (ListBlank.append [0, 1]
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1)) r_after)))
        (Cfg.headRight F default
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1)) r_after))) := by
    bb_steps
  exact (((h1.trans_star h2).trans h3).trans_star h4).trans h5

/-! ## Canonical Pattern Set (Level A) -/

/-- Pattern $P(b, k, c) := 0^\infty\,1111\,0^b\,\mathrm{F}{>}\,(111)^k\,0\,1^c\,011\,0^\infty$. -/
def pat_P : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default))))
    head := some F
    right := .rep [1, 1, 1] 1 (.sym 0 (.rep [1] 2 (.sym 0 (.sym 1 (.sym 1 .default))))) }

/-- Pattern $Q(m) := 0^\infty\,\mathrm{F}{>}\,(111)^m\,1^9\,011\,0^\infty$. -/
def pat_Q : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some F
    right := .rep [1, 1, 1] 0
      (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
        (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 .default)))))))))))) }

/-- Pattern $R(m) := 0^\infty\,\mathrm{F}{>}\,(111)^m\,1^{12}\,0^\infty$. -/
def pat_R : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some F
    right := .rep [1, 1, 1] 0
      (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
        (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))))))))))) }

/-- Pattern $U(m) := 0^\infty\,1111\,\mathrm{F}{>}\,(111)^m\,1^9\,011\,0^\infty$. -/
def pat_U : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))
    head := some F
    right := .rep [1, 1, 1] 0
      (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
        (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 .default)))))))))))) }

/-- Pattern $T(m) := 0^\infty\,1111\,0^{12}\,(000)^m\,\mathrm{F}{>}\,01111\,0^\infty$. -/
def pat_T : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 0, 0] 0
      (.sym 0 (.sym 0 (.sym 0 (.sym 0 (.sym 0 (.sym 0
        (.sym 0 (.sym 0 (.sym 0 (.sym 0 (.sym 0 (.sym 0
          (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default))))))))))))))))
    head := some F
    right := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))) }

/-- Closed pattern set for `1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P, .true), (pat_Q, .true), (pat_R, .true), (pat_U, .true), (pat_T, .true)]

private def cfg_P (b k c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F
    (ListBlank.append (([0] : List (Fin 2)) ^ b)
      (ListBlank.append [1, 1, 1, 1] default))
    (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ c)
          (ListBlank.append [0, 1, 1] default))))

private def cfg_Q (m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F default
    (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ m)
      (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1] default))

private def cfg_R (m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F default
    (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ m)
      (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] default))

private def cfg_U (m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F (ListBlank.append [1, 1, 1, 1] default)
    (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ m)
      (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1] default))

private def cfg_T (m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F
    (ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ m)
      (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        (ListBlank.append [1, 1, 1, 1] default)))
    (ListBlank.append [0, 1, 1, 1, 1] default)

private theorem in_ps_P (b k c : ℕ) : IsInPatternSet ps (cfg_P b k c) :=
  ⟨(pat_P, .true), by simp [ps], fun | 0 => b | 1 => k | _ => c, rfl, trivial⟩

private theorem in_ps_Q (m : ℕ) : IsInPatternSet ps (cfg_Q m) :=
  ⟨(pat_Q, .true), by simp [ps], fun _ => m, rfl, trivial⟩

private theorem in_ps_R (m : ℕ) : IsInPatternSet ps (cfg_R m) :=
  ⟨(pat_R, .true), by simp [ps], fun _ => m, rfl, trivial⟩

private theorem in_ps_U (m : ℕ) : IsInPatternSet ps (cfg_U m) :=
  ⟨(pat_U, .true), by simp [ps], fun _ => m, rfl, trivial⟩

private theorem in_ps_T (m : ℕ) : IsInPatternSet ps (cfg_T m) :=
  ⟨(pat_T, .true), by simp [ps], fun _ => m, rfl, trivial⟩

/-! ## Macro-Step Transitions -/

private def s_init : PState := ⟨some A, 0, ([0] : List (Fin 2)) ^ 15, []⟩

private def s_233 : PState :=
  ⟨some F, 0, [0, 0, 0, 0, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1]⟩

private theorem init_reaches_P : ReachesStar target (init []) (cfg_P 4 0 11) := by
  have h_run : runPState 233 s_init = some s_233 := by decide
  have h_ms := runPState_sound 233 s_init s_233 default h_run
  have h_init : toCfg s_init default = init [] := by
    unfold toCfg s_init init
    rw [zero_pow_default]
    rfl
  rw [h_init] at h_ms
  exact ⟨233, h_ms⟩

private theorem step_P_b0 (k c : ℕ) :
    ReachesPlus target (cfg_P 0 k c) (cfg_P (3 * k + 3) 0 (c + 2)) := by
  have h := step_bounce_b0 k
    (ListBlank.append (([1] : List (Fin 2)) ^ c) (ListBlank.append [0, 1, 1] default))
  have hl :
      ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ k)
        (ListBlank.append [0, 0, 0]
          (ListBlank.append [1, 1, 1, 1] (default : ListBlank (Fin 2)))) =
      ListBlank.append (([0] : List (Fin 2)) ^ (3 * k + 3))
        (ListBlank.append [1, 1, 1, 1] default) := by
    rw [ListBlank.append_append, zero_pow_three_mul, list_pow_add]
    rfl
  rwa [hl] at h

private theorem step_P_b_pos_c_ge2 (b k c : ℕ) :
    ReachesPlus target (cfg_P (b + 1) k (c + 2)) (cfg_P b (k + 1) c) := by
  have h := step_bounce_111 k
    (ListBlank.append (([0] : List (Fin 2)) ^ b) (ListBlank.append [1, 1, 1, 1] default))
    (ListBlank.append (([1] : List (Fin 2)) ^ c) (ListBlank.append [0, 1, 1] default))
  have hl :
      ListBlank.append [0]
        (ListBlank.append (([0] : List (Fin 2)) ^ b)
          (ListBlank.append [1, 1, 1, 1] (default : ListBlank (Fin 2)))) =
      ListBlank.append (([0] : List (Fin 2)) ^ (b + 1))
        (ListBlank.append [1, 1, 1, 1] default) := by
    rw [← ListBlank.append_pow_succ]
  rwa [hl] at h

private theorem right_tape_c0 (k : ℕ) :
    ListBlank.append [0, 1, 1]
      (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [1, 1, 1, 0, 1, 1] (default : ListBlank (Fin 2)))) =
    ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ (3 * k + 5))
        (ListBlank.append [0, 1, 1] default)) := by
  have h1 :
      ([1] : List (Fin 2)) ^ (3 * k + 5) =
        ([1, 1] : List (Fin 2)) ++
          (([1, 1, 1] : List (Fin 2)) ^ k ++ ([1, 1, 1] : List (Fin 2))) := by
    have ha : 3 * k + 5 = 2 + (3 * k + 3) := by omega
    rw [ha, list_pow_add, list_pow_add, ← one_pow_three_mul]
    rfl
  rw [h1]
  simp only [List.cons_append, List.nil_append, ListBlank.append_cons, ListBlank.append_nil,
    ← ListBlank.append_append]

private theorem step_P_b_ge2_c0 (b k : ℕ) :
    ReachesPlus target (cfg_P (b + 2) k 0) (cfg_P b 0 (3 * k + 5)) := by
  have h := step_bounce_c k
    (ListBlank.append (([0] : List (Fin 2)) ^ b) (ListBlank.append [1, 1, 1, 1] default))
    (ListBlank.append [0, 0, 1, 1] default)
    (ListBlank.append [1, 1, 1, 0, 1, 1] default)
    turnaround_c0
  have hl :
      ListBlank.append [0]
        (ListBlank.append [0]
          (ListBlank.append (([0] : List (Fin 2)) ^ b)
            (ListBlank.append [1, 1, 1, 1] (default : ListBlank (Fin 2))))) =
      ListBlank.append (([0] : List (Fin 2)) ^ (b + 2))
        (ListBlank.append [1, 1, 1, 1] default) := by
    rw [← ListBlank.append_pow_succ, ← ListBlank.append_pow_succ]
  rwa [hl, right_tape_c0 k] at h

private theorem right_tape_c1 (k : ℕ) :
    ListBlank.append [0, 1, 1]
      (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [1, 1, 1, 1, 1, 1, 0, 1, 1] (default : ListBlank (Fin 2)))) =
    ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ (3 * k + 8))
        (ListBlank.append [0, 1, 1] default)) := by
  have h1 :
      ([1] : List (Fin 2)) ^ (3 * k + 8) =
        ([1, 1] : List (Fin 2)) ++
          (([1, 1, 1] : List (Fin 2)) ^ k ++ ([1, 1, 1, 1, 1, 1] : List (Fin 2))) := by
    have ha : 3 * k + 8 = 2 + (3 * k + 6) := by omega
    rw [ha, list_pow_add, list_pow_add, ← one_pow_three_mul]
    rfl
  rw [h1]
  simp only [List.cons_append, List.nil_append, ListBlank.append_cons, ListBlank.append_nil,
    ← ListBlank.append_append]

private theorem step_P_b_ge2_c1 (b k : ℕ) :
    ReachesPlus target (cfg_P (b + 2) k 1) (cfg_P b 0 (3 * k + 8)) := by
  have h := step_bounce_c k
    (ListBlank.append (([0] : List (Fin 2)) ^ b) (ListBlank.append [1, 1, 1, 1] default))
    (ListBlank.append [0, 1, 0, 1, 1] default)
    (ListBlank.append [1, 1, 1, 1, 1, 1, 0, 1, 1] default)
    turnaround_c1
  have hl :
      ListBlank.append [0]
        (ListBlank.append [0]
          (ListBlank.append (([0] : List (Fin 2)) ^ b)
            (ListBlank.append [1, 1, 1, 1] (default : ListBlank (Fin 2))))) =
      ListBlank.append (([0] : List (Fin 2)) ^ (b + 2))
        (ListBlank.append [1, 1, 1, 1] default) := by
    rw [← ListBlank.append_pow_succ, ← ListBlank.append_pow_succ]
  rwa [hl, right_tape_c1 k] at h

private theorem step_P_b1_c0 (k : ℕ) :
    ReachesPlus target (cfg_P 1 k 0) (cfg_Q k) := by
  have h := step_bounce_b1_c k
    (ListBlank.append [0, 0, 1, 1] default)
    (ListBlank.append [1, 1, 1, 0, 1, 1] default)
    turnaround_c0
  have hr :
      ListBlank.append [1, 1, 1]
        (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1))
          (ListBlank.append [1, 1, 1, 0, 1, 1] (default : ListBlank (Fin 2)))) =
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1] default) := by
    rw [← ListBlank.append_pow_succ, list_pow_add ([1, 1, 1] : List (Fin 2)) k 2]
    simp only [← ListBlank.append_append]
    rfl
  rwa [hr] at h

private theorem step_P_b1_c1 (k : ℕ) :
    ReachesPlus target (cfg_P 1 k 1) (cfg_Q (k + 1)) := by
  have h := step_bounce_b1_c k
    (ListBlank.append [0, 1, 0, 1, 1] default)
    (ListBlank.append [1, 1, 1, 1, 1, 1, 0, 1, 1] default)
    turnaround_c1
  have hr :
      ListBlank.append [1, 1, 1]
        (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1))
          (ListBlank.append [1, 1, 1, 1, 1, 1, 0, 1, 1] (default : ListBlank (Fin 2)))) =
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (k + 1))
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1] default) := by
    rw [← ListBlank.append_pow_succ, list_pow_add ([1, 1, 1] : List (Fin 2)) (k + 1) 1]
    simp only [← ListBlank.append_append]
    rfl
  rwa [hr] at h

private theorem step_Q (m : ℕ) : ReachesPlus target (cfg_Q m) (cfg_R m) := by
  have h := step_bounce_111 (m + 3) default default
  have hl : ListBlank.append [0] (default : ListBlank (Fin 2)) = default :=
    ListBlank.cons_zero_default
  have hr1 :
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 3))
        (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2))) =
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ m)
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1] default) := by
    rw [list_pow_add ([1, 1, 1] : List (Fin 2)) m 3, ← ListBlank.append_append]
    rfl
  have hr2 :
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 3 + 1))
        (default : ListBlank (Fin 2)) =
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ m)
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] default) := by
    rw [list_pow_add ([1, 1, 1] : List (Fin 2)) m 4, ← ListBlank.append_append]
    rfl
  rwa [hl, hr1, hr2] at h

private theorem step_R_left_eq (m : ℕ) (L0 : ListBlank (Fin 2)) :
    ListBlank.append [1, 1, 1, 1, 1]
      (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 2)) L0) =
    ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 2))
      (ListBlank.append [1] (ListBlank.append [1, 1, 1, 1] L0)) := by
  rw [ListBlank.append_append, ListBlank.append_append, ListBlank.append_append]
  congr 1
  rw [one_pow_three_mul]
  change ([1] : List (Fin 2)) ^ 5 ++ ([1] : List (Fin 2)) ^ (3 * (m + 2)) =
    ([1] : List (Fin 2)) ^ (3 * (m + 2)) ++ ([1] : List (Fin 2)) ^ 1 ++ ([1] : List (Fin 2)) ^ 4
  rw [← list_pow_add, ← list_pow_add, ← list_pow_add]
  congr 1
  omega

private theorem step_R (m : ℕ) : ReachesPlus target (cfg_R m) (cfg_U m) := by
  have hr_start :
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ m)
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
          (default : ListBlank (Fin 2))) =
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 2))
        (ListBlank.append [1, 1, 1, 1, 1, 1] default) := by
    rw [list_pow_add ([1, 1, 1] : List (Fin 2)) m 2, ← ListBlank.append_append]
    rfl
  have h1 :
      ReachesPlus target (cfg_R m)
        (Cfg.headRight B (ListBlank.append [1] default)
          (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 2))
            (ListBlank.append [1, 1, 1, 1, 1, 1] default))) := by
    unfold cfg_R
    rw [hr_start]
    have h_f := step_F_zero default
      (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 2))
        (ListBlank.append [1, 1, 1, 1, 1, 1] default))
    simpa using h_f
  have h2 := shift_B_111 (m + 2) (ListBlank.append [1] default)
    (ListBlank.append [1, 1, 1, 1, 1, 1] default)
  rw [ones_comm_111 (m + 2) default] at h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append [1]
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 2)) default))
          (ListBlank.append [1, 1, 1, 1, 1, 1] default))
        (Cfg.headRight E
          (ListBlank.append [1, 1, 1, 1, 1]
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 2)) default))
          (ListBlank.append [0, 1] (ListBlank.append [0, 1, 1] default))) := by
    bb_steps
  rw [step_R_left_eq m default] at h3
  have h4 := shift_E_111 (m + 2)
    (ListBlank.append [1] (ListBlank.append [1, 1, 1, 1] default))
    (ListBlank.append [0, 1, 1] default)
  have h5 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1] (ListBlank.append [1, 1, 1, 1] default))
          (ListBlank.append [0, 1]
            (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 2))
              (ListBlank.append [0, 1, 1] default))))
        (cfg_U m) := by
    have hr_end :
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 2))
            (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2)))) =
        ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1] default) := by
      rw [← ListBlank.append_pow_succ, list_pow_add ([1, 1, 1] : List (Fin 2)) m 3,
        ← ListBlank.append_append]
      rfl
    unfold cfg_U
    rw [← hr_end]
    bb_steps
  exact (((h1.trans_star h2).trans h3).trans_star h4).trans h5

private theorem step_U_left_eq (m : ℕ) (L0 : ListBlank (Fin 2)) :
    ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ (m + 3))
      (ListBlank.append [0, 0, 0] L0) =
    ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ m)
      (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] L0) := by
  rw [ListBlank.append_append, ListBlank.append_append]
  congr 1
  change ([0, 0, 0] : List (Fin 2)) ^ (m + 3) ++ ([0, 0, 0] : List (Fin 2)) ^ 1 =
    ([0, 0, 0] : List (Fin 2)) ^ m ++ ([0, 0, 0] : List (Fin 2)) ^ 4
  rw [← list_pow_add, ← list_pow_add]

private theorem step_U (m : ℕ) : ReachesPlus target (cfg_U m) (cfg_T m) := by
  have h := step_bounce_b0 (m + 3) (ListBlank.append [1, 1] default)
  have hr_u :
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ (m + 3))
        (ListBlank.append [0] (ListBlank.append [1, 1] (default : ListBlank (Fin 2)))) =
      ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ m)
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1] default) := by
    rw [list_pow_add ([1, 1, 1] : List (Fin 2)) m 3, ← ListBlank.append_append]
    rfl
  rwa [hr_u, step_U_left_eq m (ListBlank.append [1, 1, 1, 1] default)] at h

private def s_T (n_zeros pad : ℕ) : PState :=
  ⟨some F, 0,
   ([0] : List (Fin 2)) ^ n_zeros ++ [1, 1, 1, 1] ++ ([0] : List (Fin 2)) ^ pad,
   [1, 1, 1, 1]⟩

private def s_T5_start : PState :=
  ⟨some F, 0, ([0] : List (Fin 2)) ^ 27, [1, 1, 1, 1]⟩

private def s_T2_end : PState :=
  ⟨some F, 1, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1]⟩

private theorem step_T0 :
    ∃ cfg', ReachesPlus target (cfg_T 0) cfg' ∧ (step target cfg').isNone := by
  have h := checkHalt_sound 100 32 29 (by decide) (s_T 12 20) default (by decide)
  have heq : toCfg (s_T 12 20) default = cfg_T 0 := by
    unfold toCfg s_T cfg_T
    rw [← ListBlank.append_append, zero_pow_default]
    rfl
  rwa [heq] at h

private theorem step_T1 :
    ∃ cfg', ReachesPlus target (cfg_T 1) cfg' ∧ (step target cfg').isNone := by
  have h := checkHalt_sound 100 33 13 (by decide) (s_T 15 25) default (by decide)
  have heq : toCfg (s_T 15 25) default = cfg_T 1 := by
    unfold toCfg s_T cfg_T
    rw [← ListBlank.append_append, zero_pow_default]
    rfl
  rwa [heq] at h

private theorem step_T2 : ReachesPlus target (cfg_T 2) (cfg_P 7 2 18) := by
  have h_run : runPStateFast 100 7 2 (s_T 18 5) = some s_T2_end := by decide
  have h_ms := runPStateFast_sound 100 7 2 (s_T 18 5) s_T2_end default h_run
  have heq1 : toCfg (s_T 18 5) default = cfg_T 2 := by
    unfold toCfg s_T cfg_T
    rw [← ListBlank.append_append, zero_pow_default]
    rfl
  have heq2 : toCfg s_T2_end default = cfg_P 7 2 18 := rfl
  rw [heq1, heq2] at h_ms
  exact ⟨702, by decide, h_ms⟩

private theorem step_T3 :
    ∃ cfg', ReachesPlus target (cfg_T 3) cfg' ∧ (step target cfg').isNone := by
  have h := checkHalt_sound 100 4 36 (by decide) (s_T 21 0) default (by decide)
  have heq : toCfg (s_T 21 0) default = cfg_T 3 := by
    unfold toCfg s_T cfg_T
    rw [← ListBlank.append_append, zero_pow_default]
    rfl
  rwa [heq] at h

private theorem step_T4 :
    ∃ cfg', ReachesPlus target (cfg_T 4) cfg' ∧ (step target cfg').isNone := by
  have h := checkHalt_sound 100 18 18 (by decide) (s_T 24 5) default (by decide)
  have heq : toCfg (s_T 24 5) default = cfg_T 4 := by
    unfold toCfg s_T cfg_T
    rw [← ListBlank.append_append, zero_pow_default]
    rfl
  rwa [heq] at h

private theorem step_T_ge5_left_eq (d : ℕ) (L0 : ListBlank (Fin 2)) :
    ListBlank.append (([0, 0, 0] : List (Fin 2)) ^ (d + 5))
      (ListBlank.append [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] L0) =
    ListBlank.append (([0] : List (Fin 2)) ^ 27)
      (ListBlank.append (([0] : List (Fin 2)) ^ (3 * d)) L0) := by
  rw [ListBlank.append_append, ListBlank.append_append, zero_pow_three_mul]
  congr 1
  change ([0] : List (Fin 2)) ^ (3 * (d + 5)) ++ ([0] : List (Fin 2)) ^ 12 =
    ([0] : List (Fin 2)) ^ 27 ++ ([0] : List (Fin 2)) ^ (3 * d)
  rw [← list_pow_add, ← list_pow_add]
  congr 1
  omega

private theorem step_T_ge5 (d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_T (d + 5)) cfg' ∧ (step target cfg').isNone := by
  let l_tail :=
    ListBlank.append (([0] : List (Fin 2)) ^ (3 * d))
      (ListBlank.append [1, 1, 1, 1] default)
  have h_halt := checkHalt_sound 100 17 80 (by decide) s_T5_start l_tail (by decide)
  have h_eq : toCfg s_T5_start l_tail = cfg_T (d + 5) := by
    unfold toCfg s_T5_start cfg_T
    rw [step_T_ge5_left_eq d (ListBlank.append [1, 1, 1, 1] default)]
    rfl
  rwa [h_eq] at h_halt

private theorem step_T_halt_ne2 (m : ℕ) (hm : m ≠ 2) :
    ∃ cfg', ReachesPlus target (cfg_T m) cfg' ∧ (step target cfg').isNone := by
  rcases m with _ | _ | _ | _ | _ | d
  · exact step_T0
  · exact step_T1
  · exact False.elim (hm rfl)
  · exact step_T3
  · exact step_T4
  · exact step_T_ge5 d

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_P 4 0 11, init_reaches_P, in_ps_P 4 0 11⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl | rfl | rfl | rfl
  · have h_eq : evalTapePattern (pat_P, VarCond.true).1 vars = cfg_P (vars 0) (vars 1) (vars 2) :=
      rfl
    rw [h_eq]
    rcases vars 0 with _ | _ | b'
    · exact ⟨cfg_P (3 * vars 1 + 3) 0 (vars 2 + 2),
        step_P_b0 (vars 1) (vars 2), Or.inl (in_ps_P _ _ _)⟩
    · rcases vars 2 with _ | _ | c'
      · exact ⟨cfg_Q (vars 1), step_P_b1_c0 (vars 1), Or.inl (in_ps_Q _)⟩
      · exact ⟨cfg_Q (vars 1 + 1), step_P_b1_c1 (vars 1), Or.inl (in_ps_Q _)⟩
      · exact ⟨cfg_P 0 (vars 1 + 1) c',
          step_P_b_pos_c_ge2 0 (vars 1) c', Or.inl (in_ps_P _ _ _)⟩
    · rcases vars 2 with _ | _ | c'
      · exact ⟨cfg_P b' 0 (3 * vars 1 + 5),
          step_P_b_ge2_c0 b' (vars 1), Or.inl (in_ps_P _ _ _)⟩
      · exact ⟨cfg_P b' 0 (3 * vars 1 + 8),
          step_P_b_ge2_c1 b' (vars 1), Or.inl (in_ps_P _ _ _)⟩
      · exact ⟨cfg_P (b' + 1) (vars 1 + 1) c',
          step_P_b_pos_c_ge2 (b' + 1) (vars 1) c', Or.inl (in_ps_P _ _ _)⟩
  · exact ⟨cfg_R (vars 0), step_Q (vars 0), Or.inl (in_ps_R _)⟩
  · exact ⟨cfg_U (vars 0), step_R (vars 0), Or.inl (in_ps_U _)⟩
  · exact ⟨cfg_T (vars 0), step_U (vars 0), Or.inl (in_ps_T _)⟩
  · have h_eq : evalTapePattern (pat_T, VarCond.true).1 vars = cfg_T (vars 0) := rfl
    rw [h_eq]
    rcases vars 0 with _ | _ | _ | _ | _ | d
    · obtain ⟨cfg', h1, h2⟩ := step_T0
      exact ⟨cfg', h1, Or.inr h2⟩
    · obtain ⟨cfg', h1, h2⟩ := step_T1
      exact ⟨cfg', h1, Or.inr h2⟩
    · exact ⟨cfg_P 7 2 18, step_T2, Or.inl (in_ps_P 7 2 18)⟩
    · obtain ⟨cfg', h1, h2⟩ := step_T3
      exact ⟨cfg', h1, Or.inr h2⟩
    · obtain ⟨cfg', h1, h2⟩ := step_T4
      exact ⟨cfg', h1, Or.inr h2⟩
    · obtain ⟨cfg', h1, h2⟩ := step_T_ge5 d
      exact ⟨cfg', h1, Or.inr h2⟩

/-- `1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA`. -/
inductive State where
  /-- $P(b, k, c) := 0^\infty\,1111\,0^b\,\mathrm{F}{>}\,(111)^k\,0\,1^c\,011\,0^\infty$. -/
  | P (b k c : ℕ)

/-- Initial symbolic state $P(4, 0, 11)$, reached after 233 raw TM steps. -/
def start : State := .P 4 0 11

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .P b k c =>
    Cfg.headRight SixState.F
      (ListBlank.append (([0] : List (Fin 2)) ^ b)
        (ListBlank.append [1, 1, 1, 1] default))
      (ListBlank.append (([1, 1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ c)
            (ListBlank.append [0, 1, 1] default))))

/-- Accelerated Collatz-like transition function (collapsing $Q, R, U, T$ into $P$). -/
def next : State → Option State
  | .P 0 k c => some (.P (3 * k + 3) 0 (c + 2))
  | .P 1 k 0 => if k = 2 then some (.P 7 2 18) else none
  | .P 1 k 1 => if k = 1 then some (.P 7 2 18) else none
  | .P 1 k (c + 2) => some (.P 0 (k + 1) c)
  | .P (b + 2) k 0 => some (.P b 0 (3 * k + 5))
  | .P (b + 2) k 1 => some (.P b 0 (3 * k + 8))
  | .P (b + 2) k (c + 2) => some (.P (b + 1) (k + 1) c)

private theorem step_state (b k c : ℕ) :
    match next (.P b k c) with
    | some s' => ReachesPlus target (encode (.P b k c)) (encode s')
    | none => ∃ cfg', ReachesPlus target (encode (.P b k c)) cfg' ∧ (step target cfg').isNone := by
  rcases b with _ | _ | b'
  · exact step_P_b0 k c
  · rcases c with _ | _ | c'
    · have h_to_T : ReachesPlus target (cfg_P 1 k 0) (cfg_T k) :=
        (((step_P_b1_c0 k).trans (step_Q k)).trans (step_R k)).trans (step_U k)
      rcases k with _ | _ | _ | k'
      · obtain ⟨cfg', h_halt, h_none⟩ := step_T0
        exact ⟨cfg', h_to_T.trans h_halt, h_none⟩
      · obtain ⟨cfg', h_halt, h_none⟩ := step_T1
        exact ⟨cfg', h_to_T.trans h_halt, h_none⟩
      · exact h_to_T.trans step_T2
      · obtain ⟨cfg', h_halt, h_none⟩ := step_T_halt_ne2 (k' + 3) (by omega)
        exact ⟨cfg', h_to_T.trans h_halt, h_none⟩
    · have h_to_T : ReachesPlus target (cfg_P 1 k 1) (cfg_T (k + 1)) :=
        (((step_P_b1_c1 k).trans (step_Q (k + 1))).trans (step_R (k + 1))).trans (step_U (k + 1))
      rcases k with _ | _ | k'
      · obtain ⟨cfg', h_halt, h_none⟩ := step_T1
        exact ⟨cfg', h_to_T.trans h_halt, h_none⟩
      · exact h_to_T.trans step_T2
      · dsimp [next]
        obtain ⟨cfg', h_halt, h_none⟩ := step_T_halt_ne2 (k' + 3) (by omega)
        exact ⟨cfg', h_to_T.trans h_halt, h_none⟩
    · dsimp [next]
      exact step_P_b_pos_c_ge2 0 k c'
  · rcases c with _ | _ | c'
    · exact step_P_b_ge2_c0 b' k
    · exact step_P_b_ge2_c1 b' k
    · exact step_P_b_pos_c_ge2 (b' + 1) k c'

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_P
  step_some := by
    rintro ⟨b, k, c⟩ s' hnext
    have h := step_state b k c
    rwa [hnext] at h
  step_none := by
    rintro ⟨b, k, c⟩ hnext
    have h := step_state b k c
    rw [hnext] at h
    obtain ⟨cfg', hp, hh⟩ := h
    exact ⟨cfg', hp.to_star, hh⟩

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## Countdown, 2-Parameter Slice, and Base-3 ($3^n$) Exponential Macro-Transitions -/

/-- Countdown acceleration of `step_P_b_pos_c_ge2`:
$P(b + j, k, c + 2j) \vdash^* P(b, k + j, c)$ in $j$ sweeps. -/
theorem countdown_P : ∀ j b k c : ℕ,
    ReachesStar target (encode (.P (b + j) k (c + 2 * j))) (encode (.P b (k + j) c))
  | 0, _, _, _ => ReachesStar.refl _ _
  | j + 1, b, k, c => by
    have h1 : b + (j + 1) = (b + j) + 1 := by omega
    have h2 : c + 2 * (j + 1) = (c + 2 * j) + 2 := by omega
    have h3 : (k + 1) + j = k + (j + 1) := by omega
    rw [h1, h2, ← h3]
    exact (step_P_b_pos_c_ge2 (b + j) k (c + 2 * j)).to_star.trans (countdown_P j b (k + 1) c)

/-- 1-cycle tripling step on the 2-parameter canonical slice $P(b, 0, c)$:
$P(b, 0, c + 2b) \vdash^+ P(3b + 3, 0, c + 2)$. -/
theorem triple_P (b c : ℕ) :
    ReachesPlus target (encode (.P b 0 (c + 2 * b))) (encode (.P (3 * b + 3) 0 (c + 2))) := by
  have h1 := countdown_P b 0 0 c
  simp only [Nat.zero_add] at h1
  exact h1.trans_plus (step_P_b0 b c)

/-- Accelerated slice transition for $b \ge m + 2$, even $c = 2m$:
$P(b + m + 2, 0, 2m) \vdash^+ P(b, 0, 3m + 5)$. -/
theorem accel_P_even (b m : ℕ) :
    ReachesPlus target (encode (.P (b + m + 2) 0 (2 * m))) (encode (.P b 0 (3 * m + 5))) := by
  have h_b : b + m + 2 = (b + 2) + m := by omega
  rw [h_b]
  have h1 := countdown_P m (b + 2) 0 0
  simp only [Nat.zero_add] at h1
  exact h1.trans_plus (step_P_b_ge2_c0 b m)

/-- Accelerated slice transition for $b \ge m + 2$, odd $c = 2m + 1$:
$P(b + m + 2, 0, 2m + 1) \vdash^+ P(b, 0, 3m + 8)$. -/
theorem accel_P_odd (b m : ℕ) :
    ReachesPlus target (encode (.P (b + m + 2) 0 (2 * m + 1))) (encode (.P b 0 (3 * m + 8))) := by
  have h_b : b + m + 2 = (b + 2) + m := by omega
  have h_c : 2 * m + 1 = 1 + 2 * m := by omega
  rw [h_b, h_c]
  have h1 := countdown_P m (b + 2) 0 1
  simp only [Nat.zero_add] at h1
  exact h1.trans_plus (step_P_b_ge2_c1 b m)

private def ExpRelP (b c_cost b_out : ℕ) : Prop :=
  b_out ≥ 1 ∧ ∀ c : ℕ,
    ReachesStar target (encode (.P (b + 1) 0 (c + c_cost + 2))) (encode (.P b_out 0 (c + 2)))

private theorem ExpRelP_zero (b : ℕ) : ExpRelP b 0 (b + 1) := by
  refine ⟨by omega, fun c => ?_⟩
  rw [Nat.add_zero]

private theorem ExpRelP_succ {b c_cost b_out : ℕ} (h : ExpRelP b c_cost b_out) :
    ExpRelP b (c_cost + (2 * b_out - 2)) (3 * b_out + 3) := by
  rcases h with ⟨hb_pos, h_step⟩
  refine ⟨by omega, fun c => ?_⟩
  have h_eq1 : c + (c_cost + (2 * b_out - 2)) + 2 = (c + (2 * b_out - 2)) + c_cost + 2 := by omega
  have h_eq2 : (c + (2 * b_out - 2)) + 2 = c + 2 * b_out := by omega
  rw [h_eq1]
  have h1 := h_step (c + (2 * b_out - 2))
  rw [h_eq2] at h1
  exact h1.trans (triple_P b_out c).to_star

private theorem mul_pow3_ge (b n : ℕ) : (2 * b + 5) * 3 ^ n ≥ 2 * b + 10 * n + 5 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    omega

private theorem mul_pow3_mod2 (b n : ℕ) : ((2 * b + 5) * 3 ^ n) % 2 = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    omega

private theorem ExpRelP_pow3 (n b : ℕ) :
    ExpRelP b (((2 * b + 5) * 3 ^ n - 2 * b - 10 * n - 5) / 2)
      (((2 * b + 5) * 3 ^ n - 3) / 2) := by
  induction n with
  | zero =>
    have h1 : ((2 * b + 5) * 3 ^ 0 - 2 * b - 10 * 0 - 5) / 2 = 0 := by omega
    have h2 : ((2 * b + 5) * 3 ^ 0 - 3) / 2 = b + 1 := by omega
    rw [h1, h2]
    exact ExpRelP_zero b
  | succ n ih =>
    have h_ge := mul_pow3_ge b n
    have h_mod := mul_pow3_mod2 b n
    have h_pow : (2 * b + 5) * 3 ^ (n + 1) = ((2 * b + 5) * 3 ^ n) * 3 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
    have h_step := ExpRelP_succ ih
    have h1 :
        ((2 * b + 5) * 3 ^ n - 2 * b - 10 * n - 5) / 2 +
          (2 * (((2 * b + 5) * 3 ^ n - 3) / 2) - 2) =
        ((2 * b + 5) * 3 ^ (n + 1) - 2 * b - 10 * (n + 1) - 5) / 2 := by
      rw [h_pow]
      omega
    have h2 :
        3 * (((2 * b + 5) * 3 ^ n - 3) / 2) + 3 =
          ((2 * b + 5) * 3 ^ (n + 1) - 3) / 2 := by
      rw [h_pow]
      omega
    rw [h1, h2] at h_step
    exact h_step

/-- Base-3 ($3^n$) exponential macro-transition on $P(b + 1, 0, c)$:
$$P\!\left(b + 1,\; 0,\; c + \frac{(2b + 5) \cdot 3^n - 2b - 10n - 5}{2} + 2\right)
  \;\vdash^*\; P\!\left(\frac{(2b + 5) \cdot 3^n - 3}{2},\; 0,\; c + 2\right).$$ -/
theorem exp3_step_P (n b c : ℕ) :
    ReachesStar target
      (encode (.P (b + 1) 0 (c + (((2 * b + 5) * 3 ^ n - 2 * b - 10 * n - 5) / 2) + 2)))
      (encode (.P (((2 * b + 5) * 3 ^ n - 3) / 2) 0 (c + 2))) :=
  (ExpRelP_pow3 n b).2 c

end BusyBeaver.M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA
