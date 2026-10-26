/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC`

Formal Collatz-like transducer acceleration (`IsValidAcceleration`) for the 6-state, 2-symbol
Busy Beaver holdout `1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC`.

Both half-tapes are represented as `(2, 2)` zero-stacks `List (ℕ × Bool)` via `encStack`, where
each entry `(a, b)` encodes `0^{a+1} 1` (`b = false`) or `0^{a+1} 11` (`b = true`):
$$
E(L, R) := \mathrm{tail}(\mathrm{encStack}(L))\,\mathrm{E}{>}\,\mathrm{tail}(\mathrm{encStack}(R)).
$$
Starting from the blank tape (`init []`), the machine reaches
`start = .E [(1, false)] [(0, false)]` after 4 raw Turing machine steps. Halting (`D1 -> ---`)
occurs only during a right-excursion in `bounceR` when the head encounters `(3, b)`.

## Accelerated Transition Rules

```text
encStack []              = 0^inf
encStack ((a, false)::S) = 0^{a+1} 1  ++ encStack S
encStack ((a, true) ::S) = 0^{a+1} 11 ++ encStack S

E(L, [])             -> closeRet L (r11, [])
E(L, (0, b) :: R1)   -> stepZero L b R1
E(L, (d+1, b) :: R1) -> closeRet L <$> bounceR ((d, b) :: R1)
  where bounceR ((3, _) :: _) = Halt

Start: E([(1, false)], [(0, false)]), reached after 4 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Encode a `(2, 2)` zero-stack `List (ℕ × Bool)` into a `ListBlank (Fin 2)` half-tape. -/
def encStack : List (ℕ × Bool) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: xs =>
    ListBlank.append (([0] : List (Fin 2)) ^ (a + 1))
      (ListBlank.append (if b then [1, 1] else [1]) (encStack xs))

/-- Increment the leading zero-run count of a non-empty stack (no-op on `[]`). -/
def incHead : List (ℕ × Bool) → List (ℕ × Bool)
  | [] => []
  | (a, b) :: xs => (a + 1, b) :: xs

/-- Return carry modes produced by a right-excursion across `encStack R`. -/
inductive RetMode where
  | r01
  | r10
  | r11
  | r21
  deriving DecidableEq, Repr

/-- Unwind a `01` left-context frame after a recursive right-excursion. -/
def unwind01 : RetMode × List (ℕ × Bool) → RetMode × List (ℕ × Bool)
  | (.r01, R') => (.r01, (0, false) :: R')
  | (.r10, R') => (.r10, (0, false) :: R')
  | (.r11, R') => (.r10, (0, true) :: R')
  | (.r21, R') => (.r11, (0, false) :: incHead R')

/-- Unwind a `111` left-context frame after a recursive right-excursion. -/
def unwind111 : RetMode × List (ℕ × Bool) → RetMode × List (ℕ × Bool)
  | (.r01, R') => (.r01, (0, true) :: R')
  | (.r10, R') => (.r11, (0, false) :: R')
  | (.r11, R') => (.r11, (0, true) :: R')
  | (.r21, R') => (.r21, (0, true) :: R')

/-- Unwind a `11` left-context frame after a recursive right-excursion. -/
def unwind11 : RetMode × List (ℕ × Bool) → RetMode × List (ℕ × Bool)
  | (.r01, R') => (.r21, R')
  | (.r10, R') => (.r01, (0, false) :: R')
  | (.r11, R') => (.r01, (0, true) :: R')
  | (.r21, R') => (.r11, (0, true) :: R')

/-- Right-excursion transducer across `encStack R`; halts (`none`) on `(3, _) :: _`. -/
def bounceR : List (ℕ × Bool) → Option (RetMode × List (ℕ × Bool))
  | [] => some (.r11, [])
  | (0, false) :: R₁ => unwind01 <$> bounceR R₁
  | (0, true) :: R₁ => some (.r01, incHead R₁)
  | (1, false) :: R₁ => unwind111 <$> bounceR R₁
  | (1, true) :: R₁ => some (.r01, (0, false) :: R₁)
  | (2, false) :: R₁ => (fun p => unwind11 (unwind01 p)) <$> bounceR R₁
  | (2, true) :: R₁ => some (.r21, incHead R₁)
  | (3, _) :: _ => none
  | (d + 4, b) :: R₁ => some (.r11, (d + 1, b) :: R₁)

/-- Symbolic configuration state `E(L, R)` over `(2, 2)` zero-stacks. -/
inductive State where
  | E (L R : List (ℕ × Bool))
  deriving DecidableEq, Repr

/-- Merge a right-excursion return carry `(m, R')` with the left stack `L`. -/
def closeRet : List (ℕ × Bool) → RetMode × List (ℕ × Bool) → State
  | L, (.r01, R') => .E L ((0, true) :: R')
  | [], (.r10, R') => .E [(0, false)] ((0, false) :: R')
  | (0, false) :: L₁, (.r10, R') => .E ((0, true) :: L₁) ((0, false) :: R')
  | (0, true) :: L₁, (.r10, R') => .E (incHead L₁) ((0, true) :: (0, false) :: R')
  | (a + 1, bL) :: L₁, (.r10, R') => .E ((0, false) :: (a, bL) :: L₁) ((0, false) :: R')
  | [], (.r11, R') => .E [(0, false)] ((0, true) :: R')
  | (0, false) :: L₁, (.r11, R') => .E ((0, true) :: L₁) ((0, true) :: R')
  | (0, true) :: L₁, (.r11, R') => .E (incHead L₁) ((0, true) :: (0, true) :: R')
  | (a + 1, bL) :: L₁, (.r11, R') => .E ((0, false) :: (a, bL) :: L₁) ((0, true) :: R')
  | [], (.r21, R') => .E [(0, true)] ((0, true) :: R')
  | (0, false) :: L₁, (.r21, R') => .E (incHead L₁) ((0, true) :: (0, true) :: R')
  | (0, true) :: L₁, (.r21, R') => .E ((0, false) :: L₁) ((0, true) :: (0, true) :: R')
  | (a + 1, bL) :: L₁, (.r21, R') => .E ((0, true) :: (a, bL) :: L₁) ((0, true) :: R')

/-- Direct transition when the leading right-stack item has `d = 0`. -/
def stepZero : List (ℕ × Bool) → Bool → List (ℕ × Bool) → State
  | [], false, R₁ => .E [] ((1, false) :: incHead R₁)
  | [], true, R₁ => .E [] ((1, false) :: (0, false) :: R₁)
  | (0, false) :: L₁, b, R₁ => .E L₁ ((0, false) :: (0, b) :: R₁)
  | (0, true) :: L₁, b, R₁ => .E L₁ ((1, false) :: (0, b) :: R₁)
  | (1, false) :: L₁, false, R₁ => .E (incHead L₁) ((0, true) :: incHead R₁)
  | (1, false) :: L₁, true, R₁ => .E (incHead L₁) ((0, true) :: (0, false) :: R₁)
  | (1, true) :: L₁, false, R₁ => .E ((0, false) :: L₁) ((0, true) :: incHead R₁)
  | (1, true) :: L₁, true, R₁ => .E ((0, false) :: L₁) ((0, true) :: (0, false) :: R₁)
  | (a + 2, bL) :: L₁, false, R₁ => .E ((a, bL) :: L₁) ((1, false) :: incHead R₁)
  | (a + 2, bL) :: L₁, true, R₁ => .E ((a, bL) :: L₁) ((1, false) :: (0, false) :: R₁)

/-- Initial accelerated state, reached after 4 raw Turing machine steps from `init []`. -/
def start : State := .E [(1, false)] [(0, false)]

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .E L R => Cfg.headRight SixState.E (encStack L).tail (encStack R).tail

/-- Accelerated transition function (`none` indicates halting). -/
def next : State → Option State
  | .E L [] => some (closeRet L (.r11, []))
  | .E L ((0, b) :: R₁) => some (stepZero L b R₁)
  | .E L ((d + 1, b) :: R₁) => closeRet L <$> bounceR ((d, b) :: R₁)

/-! ## Stack Encoding Lemmas -/

private theorem encStack_zero_false (S : List (ℕ × Bool)) :
    encStack ((0, false) :: S) = ListBlank.cons 0 (ListBlank.cons 1 (encStack S)) :=
  rfl

private theorem encStack_zero_true (S : List (ℕ × Bool)) :
    encStack ((0, true) :: S) =
      ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 1 (encStack S))) :=
  rfl

private theorem encStack_succ (a : ℕ) (b : Bool) (S : List (ℕ × Bool)) :
    encStack ((a + 1, b) :: S) = ListBlank.cons 0 (encStack ((a, b) :: S)) := by
  simp only [encStack, ListBlank.append_pow_succ, ListBlank.append_cons, ListBlank.append_nil]

private theorem zero_cons_encStack (S : List (ℕ × Bool)) :
    ListBlank.cons 0 (encStack S) = encStack (incHead S) := by
  rcases S with _ | ⟨⟨a, b⟩, S'⟩
  · simp [encStack, incHead]
  · exact (encStack_succ a b S').symm

private theorem encStack_head (S : List (ℕ × Bool)) : (encStack S).head = 0 := by
  rcases S with _ | ⟨⟨a, b⟩, S'⟩
  · rfl
  · simp only [encStack, ListBlank.append_pow_succ, ListBlank.append_cons,
      ListBlank.append_nil, ListBlank.head_cons]

private theorem encStack_eq_zero_cons_tail (S : List (ℕ × Bool)) :
    encStack S = ListBlank.cons 0 (encStack S).tail := by
  nth_rw 1 [← ListBlank.cons_head_tail (encStack S)]
  rw [encStack_head]

private theorem encStack_tail_zero_false (S : List (ℕ × Bool)) :
    (encStack ((0, false) :: S)).tail = ListBlank.cons 1 (encStack S) := by
  rw [encStack_zero_false, ListBlank.tail_cons]

private theorem encStack_tail_zero_true (S : List (ℕ × Bool)) :
    (encStack ((0, true) :: S)).tail = ListBlank.cons 1 (ListBlank.cons 1 (encStack S)) := by
  rw [encStack_zero_true, ListBlank.tail_cons]

private theorem encStack_tail_succ (a : ℕ) (b : Bool) (S : List (ℕ × Bool)) :
    (encStack ((a + 1, b) :: S)).tail = encStack ((a, b) :: S) := by
  rw [encStack_succ, ListBlank.tail_cons]

private theorem encStack_incHead_tail (S : List (ℕ × Bool)) :
    (encStack (incHead S)).tail = encStack S := by
  rcases S with _ | ⟨⟨a, b⟩, S'⟩
  · rfl
  · exact encStack_tail_succ a b S'

/-! ## Right-Excursion Micro-Step Lemmas -/

private def retCfg (W : ListBlank (Fin 2)) : RetMode × List (ℕ × Bool) → Cfg (Fin 2) (Fin 6)
  | (.r01, R') => Cfg.headRight E W (ListBlank.cons 1 (ListBlank.cons 1 (encStack R')))
  | (.r10, R') =>
    Cfg.headRight E (ListBlank.cons 1 W) (ListBlank.cons 1 (encStack R'))
  | (.r11, R') =>
    Cfg.headRight E (ListBlank.cons 1 W) (ListBlank.cons 1 (ListBlank.cons 1 (encStack R')))
  | (.r21, R') =>
    Cfg.headRight E (ListBlank.cons 1 (ListBlank.cons 1 W))
      (ListBlank.cons 1 (ListBlank.cons 1 (encStack R')))

private theorem raw_base_five_zeros (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E W (ListBlank.append [0, 0, 0, 0, 0] Z))
      (Cfg.headRight E (ListBlank.cons 1 W) (ListBlank.append [1, 1, 0, 0] Z)) := by
  bb_steps

private theorem raw_base_0_1 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E W (ListBlank.append [0, 1, 1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [1, 1, 0, 0] Z)) := by
  bb_steps

private theorem raw_base_1_1 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E W (ListBlank.append [0, 0, 1, 1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [1, 1, 0, 1, 0] Z)) := by
  bb_steps

private theorem raw_base_2_1 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E W (ListBlank.append [0, 0, 0, 1, 1, 0] Z))
      (Cfg.headRight E (ListBlank.append [1, 1] W) (ListBlank.append [1, 1, 0, 0] Z)) := by
  bb_steps

private theorem raw_halt_3 (W Z : ListBlank (Fin 2)) :
    ∃ cfg', ReachesStar target
      (Cfg.headRight E W (ListBlank.append [0, 0, 0, 0, 1] Z)) cfg' ∧
      (step target cfg').isNone := by
  refine ⟨Cfg.headRight D (ListBlank.append [1, 0, 1, 1] W) (ListBlank.cons 1 Z), ?_, by bb_halt⟩
  exact (by bb_steps : ReachesPlus target _ _).to_star

private theorem raw_step_0_0 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E W (ListBlank.append [0, 1] Z))
      (Cfg.headRight E (ListBlank.append [0, 1] W) Z) := by
  bb_steps

private theorem raw_step_1_0 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E W (ListBlank.append [0, 0, 1] Z))
      (Cfg.headRight E (ListBlank.append [1, 1, 1] W) Z) := by
  bb_steps

private theorem raw_step_2_0 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E W (ListBlank.append [0, 0, 0, 1] Z))
      (Cfg.headRight E (ListBlank.append [0, 1, 1, 1] W) Z) := by
  bb_steps

private theorem raw_u01_r01 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [0, 1] W) (ListBlank.append [1, 1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [1, 1, 0, 1, 0] Z)) := by
  bb_steps

private theorem raw_u01_r10 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 0, 1] W) (ListBlank.append [1, 0] Z))
      (Cfg.headRight E (ListBlank.cons 1 W) (ListBlank.append [1, 0, 1, 0] Z)) := by
  bb_steps

private theorem raw_u01_r11 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 0, 1] W) (ListBlank.append [1, 1, 0] Z))
      (Cfg.headRight E (ListBlank.cons 1 W) (ListBlank.append [1, 0, 1, 1, 0] Z)) := by
  bb_steps

private theorem raw_u01_r21 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 1, 0, 1] W) (ListBlank.append [1, 1, 0] Z))
      (Cfg.headRight E (ListBlank.cons 1 W) (ListBlank.append [1, 1, 0, 1, 0, 0] Z)) := by
  bb_steps

private theorem raw_u111_r01 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 1, 1] W) (ListBlank.append [1, 1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [1, 1, 0, 1, 1, 0] Z)) := by
  bb_steps

private theorem raw_u111_r10 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 1, 1, 1] W) (ListBlank.append [1, 0] Z))
      (Cfg.headRight E (ListBlank.cons 1 W) (ListBlank.append [1, 1, 0, 1, 0] Z)) := by
  bb_steps

private theorem raw_u111_r11 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 1, 1, 1] W) (ListBlank.append [1, 1, 0] Z))
      (Cfg.headRight E (ListBlank.cons 1 W) (ListBlank.append [1, 1, 0, 1, 1, 0] Z)) := by
  bb_steps

private theorem raw_u111_r21 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 1, 1, 1, 1] W) (ListBlank.append [1, 1, 0] Z))
      (Cfg.headRight E (ListBlank.append [1, 1] W) (ListBlank.append [1, 1, 0, 1, 1, 0] Z)) := by
  bb_steps

private theorem raw_u11_r10 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 1, 1] W) (ListBlank.append [1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [1, 1, 0, 1, 0] Z)) := by
  bb_steps

private theorem unwind01_spec (W : ListBlank (Fin 2)) (p : RetMode × List (ℕ × Bool)) :
    ReachesPlus target
      (retCfg (ListBlank.append [0, 1] W) p)
      (retCfg W (unwind01 p)) := by
  rcases p with ⟨m, R'⟩
  cases m with
  | r01 =>
    dsimp only [unwind01, retCfg]
    rw [encStack_zero_false, encStack_eq_zero_cons_tail R']
    exact raw_u01_r01 W (encStack R').tail
  | r10 =>
    dsimp only [unwind01, retCfg]
    rw [encStack_zero_false, encStack_eq_zero_cons_tail R']
    exact raw_u01_r10 W (encStack R').tail
  | r11 =>
    dsimp only [unwind01, retCfg]
    rw [encStack_zero_true, encStack_eq_zero_cons_tail R']
    exact raw_u01_r11 W (encStack R').tail
  | r21 =>
    dsimp only [unwind01, retCfg]
    rw [encStack_zero_false, ← zero_cons_encStack R', encStack_eq_zero_cons_tail R']
    exact raw_u01_r21 W (encStack R').tail

private theorem unwind111_spec (W : ListBlank (Fin 2)) (p : RetMode × List (ℕ × Bool)) :
    ReachesPlus target
      (retCfg (ListBlank.append [1, 1, 1] W) p)
      (retCfg W (unwind111 p)) := by
  rcases p with ⟨m, R'⟩
  cases m with
  | r01 =>
    dsimp only [unwind111, retCfg]
    rw [encStack_zero_true, encStack_eq_zero_cons_tail R']
    exact raw_u111_r01 W (encStack R').tail
  | r10 =>
    dsimp only [unwind111, retCfg]
    rw [encStack_zero_false, encStack_eq_zero_cons_tail R']
    exact raw_u111_r10 W (encStack R').tail
  | r11 =>
    dsimp only [unwind111, retCfg]
    rw [encStack_zero_true, encStack_eq_zero_cons_tail R']
    exact raw_u111_r11 W (encStack R').tail
  | r21 =>
    dsimp only [unwind111, retCfg]
    rw [encStack_zero_true, encStack_eq_zero_cons_tail R']
    exact raw_u111_r21 W (encStack R').tail

private theorem unwind11_spec (W : ListBlank (Fin 2)) (p : RetMode × List (ℕ × Bool)) :
    ReachesStar target
      (retCfg (ListBlank.append [1, 1] W) p)
      (retCfg W (unwind11 p)) := by
  rcases p with ⟨m, R'⟩
  cases m with
  | r01 =>
    dsimp only [unwind11, retCfg]
    bb_refl
  | r10 =>
    dsimp only [unwind11, retCfg]
    rw [encStack_zero_false, encStack_eq_zero_cons_tail R']
    exact (raw_u11_r10 W (encStack R').tail).to_star
  | r11 =>
    dsimp only [unwind11, retCfg]
    rw [encStack_zero_true, encStack_eq_zero_cons_tail R']
    exact (raw_u111_r01 W (encStack R').tail).to_star
  | r21 =>
    dsimp only [unwind11, retCfg]
    rw [encStack_zero_true, encStack_eq_zero_cons_tail R']
    exact (raw_u111_r11 W (encStack R').tail).to_star

private theorem bounceR_spec (R : List (ℕ × Bool)) (W : ListBlank (Fin 2)) :
    match bounceR R with
    | some p => ReachesPlus target (Cfg.headRight E W (encStack R)) (retCfg W p)
    | none =>
      ∃ cfg', ReachesStar target (Cfg.headRight E W (encStack R)) cfg' ∧
        (step target cfg').isNone := by
  induction R generalizing W with
  | nil =>
    dsimp only [bounceR, retCfg, encStack]
    simpa using raw_base_five_zeros W default
  | cons hd R₁ ih =>
    rcases hd with ⟨_ | _ | _ | _ | d, b⟩
    · cases b with
      | false =>
        dsimp only [bounceR]
        have hstep : ReachesPlus target
            (Cfg.headRight E W (encStack ((0, false) :: R₁)))
            (Cfg.headRight E (ListBlank.append [0, 1] W) (encStack R₁)) := by
          rw [encStack_zero_false]
          exact raw_step_0_0 W (encStack R₁)
        have ihW := ih (ListBlank.append [0, 1] W)
        rcases hres : bounceR R₁ with _ | p
        · rw [hres] at ihW
          obtain ⟨cfg', hstar, hhalt⟩ := ihW
          exact ⟨cfg', hstep.to_star.trans hstar, hhalt⟩
        · rw [hres] at ihW
          exact (hstep.trans ihW).trans (unwind01_spec W p)
      | true =>
        dsimp only [bounceR, retCfg]
        rw [encStack_zero_true, ← zero_cons_encStack R₁, encStack_eq_zero_cons_tail R₁]
        exact raw_base_0_1 W (encStack R₁).tail
    · cases b with
      | false =>
        dsimp only [bounceR]
        have hstep : ReachesPlus target
            (Cfg.headRight E W (encStack ((1, false) :: R₁)))
            (Cfg.headRight E (ListBlank.append [1, 1, 1] W) (encStack R₁)) := by
          rw [encStack_succ, encStack_zero_false]
          exact raw_step_1_0 W (encStack R₁)
        have ihW := ih (ListBlank.append [1, 1, 1] W)
        rcases hres : bounceR R₁ with _ | p
        · rw [hres] at ihW
          obtain ⟨cfg', hstar, hhalt⟩ := ihW
          exact ⟨cfg', hstep.to_star.trans hstar, hhalt⟩
        · rw [hres] at ihW
          exact (hstep.trans ihW).trans (unwind111_spec W p)
      | true =>
        dsimp only [bounceR, retCfg]
        rw [encStack_succ, encStack_zero_true, encStack_zero_false, encStack_eq_zero_cons_tail R₁]
        exact raw_base_1_1 W (encStack R₁).tail
    · cases b with
      | false =>
        dsimp only [bounceR]
        have hstep : ReachesPlus target
            (Cfg.headRight E W (encStack ((2, false) :: R₁)))
            (Cfg.headRight E (ListBlank.append [0, 1, 1, 1] W) (encStack R₁)) := by
          rw [encStack_succ, encStack_succ, encStack_zero_false]
          exact raw_step_2_0 W (encStack R₁)
        have ihW := ih (ListBlank.append [0, 1, 1, 1] W)
        rcases hres : bounceR R₁ with _ | p
        · rw [hres] at ihW
          obtain ⟨cfg', hstar, hhalt⟩ := ihW
          exact ⟨cfg', hstep.to_star.trans hstar, hhalt⟩
        · rw [hres] at ihW
          have hu1 := unwind01_spec (ListBlank.append [1, 1] W) p
          have hu2 := unwind11_spec W (unwind01 p)
          exact ((hstep.trans ihW).trans hu1).trans_star hu2
      | true =>
        dsimp only [bounceR, retCfg]
        rw [encStack_succ, encStack_succ, encStack_zero_true, ← zero_cons_encStack R₁,
          encStack_eq_zero_cons_tail R₁]
        exact raw_base_2_1 W (encStack R₁).tail
    · dsimp only [bounceR]
      cases b with
      | false =>
        rw [encStack_succ, encStack_succ, encStack_succ, encStack_zero_false]
        exact raw_halt_3 W (encStack R₁)
      | true =>
        rw [encStack_succ, encStack_succ, encStack_succ, encStack_zero_true]
        exact raw_halt_3 W (ListBlank.cons 1 (encStack R₁))
    · dsimp only [bounceR, retCfg]
      rw [encStack_succ (d + 3), encStack_succ (d + 2), encStack_succ (d + 1), encStack_succ d,
        encStack_eq_zero_cons_tail ((d, b) :: R₁)]
      exact raw_base_five_zeros W (encStack ((d, b) :: R₁)).tail

/-! ## Left-Stack Return & Direct `d = 0` Lemmas -/

private theorem closeRet_spec (L : List (ℕ × Bool)) (p : RetMode × List (ℕ × Bool)) :
    ReachesStar target (retCfg (encStack L).tail p) (encode (closeRet L p)) := by
  rcases p with ⟨m, R'⟩
  cases m with
  | r01 =>
    dsimp only [closeRet, retCfg, encode]
    rw [encStack_tail_zero_true]
  | r10 =>
    rcases L with _ | ⟨⟨_ | a, bL⟩, L₁⟩
    · dsimp only [closeRet, retCfg, encode]
      rw [encStack_tail_zero_false, encStack_tail_zero_false]
      simp only [encStack, ListBlank.tail_default]
      bb_refl
    · cases bL with
      | false =>
        dsimp only [closeRet, retCfg, encode]
        rw [encStack_tail_zero_false, encStack_tail_zero_true, encStack_tail_zero_false]
      | true =>
        dsimp only [closeRet, retCfg, encode]
        rw [encStack_tail_zero_true, encStack_incHead_tail, encStack_tail_zero_true,
          encStack_zero_false, encStack_eq_zero_cons_tail R']
        exact (raw_u11_r10 (encStack L₁) (encStack R').tail).to_star
    · dsimp only [closeRet, retCfg, encode]
      rw [encStack_tail_succ, encStack_tail_zero_false, encStack_tail_zero_false]
  | r11 =>
    rcases L with _ | ⟨⟨_ | a, bL⟩, L₁⟩
    · dsimp only [closeRet, retCfg, encode]
      rw [encStack_tail_zero_false, encStack_tail_zero_true]
      simp only [encStack, ListBlank.tail_default]
      bb_refl
    · cases bL with
      | false =>
        dsimp only [closeRet, retCfg, encode]
        rw [encStack_tail_zero_false, encStack_tail_zero_true, encStack_tail_zero_true]
      | true =>
        dsimp only [closeRet, retCfg, encode]
        rw [encStack_tail_zero_true, encStack_incHead_tail, encStack_tail_zero_true,
          encStack_zero_true, encStack_eq_zero_cons_tail R']
        exact (raw_u111_r01 (encStack L₁) (encStack R').tail).to_star
    · dsimp only [closeRet, retCfg, encode]
      rw [encStack_tail_succ, encStack_tail_zero_false, encStack_tail_zero_true]
  | r21 =>
    rcases L with _ | ⟨⟨_ | a, bL⟩, L₁⟩
    · dsimp only [closeRet, retCfg, encode]
      rw [encStack_tail_zero_true, encStack_tail_zero_true]
      simp only [encStack, ListBlank.tail_default]
      bb_refl
    · cases bL with
      | false =>
        dsimp only [closeRet, retCfg, encode]
        rw [encStack_tail_zero_false, encStack_incHead_tail, encStack_tail_zero_true,
          encStack_zero_true, encStack_eq_zero_cons_tail R']
        exact (raw_u111_r01 (encStack L₁) (encStack R').tail).to_star
      | true =>
        dsimp only [closeRet, retCfg, encode]
        rw [encStack_tail_zero_true, encStack_tail_zero_false, encStack_tail_zero_true,
          encStack_zero_true, encStack_eq_zero_cons_tail R']
        exact (raw_u111_r11 (encStack L₁) (encStack R').tail).to_star
    · dsimp only [closeRet, retCfg, encode]
      rw [encStack_tail_succ, encStack_tail_zero_true, encStack_tail_zero_true]

private theorem raw_d0_L00 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [0, 0] W) (ListBlank.append [1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [0, 1, 0, 0] Z)) := by
  bb_steps

private theorem raw_d0_b1_L00 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [0, 0] W) (ListBlank.append [1, 1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [0, 1, 0, 1, 0] Z)) := by
  bb_steps

private theorem raw_d0_L01 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [0, 1] W) (ListBlank.append [1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [1, 1, 0, 0] Z)) := by
  bb_steps

private theorem raw_d0_b1_L01 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [0, 1] W) (ListBlank.append [1, 1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [1, 1, 0, 1, 0] Z)) := by
  bb_steps

private theorem raw_d0_L10 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 0] W) (ListBlank.append [1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [1, 0, 1, 0] Z)) := by
  bb_steps

private theorem raw_d0_b1_L10 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 0] W) (ListBlank.append [1, 1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [1, 0, 1, 1, 0] Z)) := by
  bb_steps

private theorem raw_d0_L110 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 1, 0] W) (ListBlank.append [1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [0, 1, 0, 1, 0] Z)) := by
  bb_steps

private theorem raw_d0_b1_L110 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E (ListBlank.append [1, 1, 0] W) (ListBlank.append [1, 1, 0] Z))
      (Cfg.headRight E W (ListBlank.append [0, 1, 0, 1, 1, 0] Z)) := by
  bb_steps

private theorem stepZero_spec (L : List (ℕ × Bool)) (b : Bool) (R₁ : List (ℕ × Bool)) :
    ReachesPlus target (encode (.E L ((0, b) :: R₁))) (encode (stepZero L b R₁)) := by
  rcases L with _ | ⟨⟨_ | _ | a, bL⟩, L₁⟩
  · cases b with
    | false =>
      dsimp only [stepZero, encode]
      rw [encStack_tail_zero_false, encStack_tail_succ, encStack_zero_false,
        ← zero_cons_encStack R₁, encStack_eq_zero_cons_tail R₁]
      simpa [encStack] using raw_d0_L00 default (encStack R₁).tail
    | true =>
      dsimp only [stepZero, encode]
      rw [encStack_tail_zero_true, encStack_tail_succ, encStack_zero_false, encStack_zero_false,
        encStack_eq_zero_cons_tail R₁]
      simpa [encStack] using raw_d0_b1_L00 default (encStack R₁).tail
  · cases bL with
    | false =>
      cases b with
      | false =>
        dsimp only [stepZero, encode]
        rw [encStack_tail_zero_false, encStack_eq_zero_cons_tail L₁, ListBlank.tail_cons,
          encStack_tail_zero_false, encStack_tail_zero_false, encStack_zero_false,
          encStack_eq_zero_cons_tail R₁]
        exact raw_d0_L10 (encStack L₁).tail (encStack R₁).tail
      | true =>
        dsimp only [stepZero, encode]
        rw [encStack_tail_zero_false, encStack_eq_zero_cons_tail L₁, ListBlank.tail_cons,
          encStack_tail_zero_true, encStack_tail_zero_false, encStack_zero_true,
          encStack_eq_zero_cons_tail R₁]
        exact raw_d0_b1_L10 (encStack L₁).tail (encStack R₁).tail
    | true =>
      cases b with
      | false =>
        dsimp only [stepZero, encode]
        rw [encStack_tail_zero_true, encStack_eq_zero_cons_tail L₁, ListBlank.tail_cons,
          encStack_tail_zero_false, encStack_tail_succ, encStack_zero_false, encStack_zero_false,
          encStack_eq_zero_cons_tail R₁]
        exact raw_d0_L110 (encStack L₁).tail (encStack R₁).tail
      | true =>
        dsimp only [stepZero, encode]
        rw [encStack_tail_zero_true, encStack_eq_zero_cons_tail L₁, ListBlank.tail_cons,
          encStack_tail_zero_true, encStack_tail_succ, encStack_zero_false, encStack_zero_true,
          encStack_eq_zero_cons_tail R₁]
        exact raw_d0_b1_L110 (encStack L₁).tail (encStack R₁).tail
  · cases bL with
    | false =>
      cases b with
      | false =>
        dsimp only [stepZero, encode]
        rw [encStack_tail_succ, encStack_zero_false, encStack_incHead_tail,
          encStack_tail_zero_false, encStack_tail_zero_true, ← zero_cons_encStack R₁,
          encStack_eq_zero_cons_tail R₁]
        exact raw_d0_L01 (encStack L₁) (encStack R₁).tail
      | true =>
        dsimp only [stepZero, encode]
        rw [encStack_tail_succ, encStack_zero_false, encStack_incHead_tail,
          encStack_tail_zero_true, encStack_tail_zero_true, encStack_zero_false,
          encStack_eq_zero_cons_tail R₁]
        exact raw_d0_b1_L01 (encStack L₁) (encStack R₁).tail
    | true =>
      cases b with
      | false =>
        dsimp only [stepZero, encode]
        rw [encStack_tail_succ, encStack_zero_true, encStack_tail_zero_false,
          encStack_tail_zero_false, encStack_tail_zero_true, ← zero_cons_encStack R₁,
          encStack_eq_zero_cons_tail R₁]
        exact raw_d0_L01 (ListBlank.cons 1 (encStack L₁)) (encStack R₁).tail
      | true =>
        dsimp only [stepZero, encode]
        rw [encStack_tail_succ, encStack_zero_true, encStack_tail_zero_false,
          encStack_tail_zero_true, encStack_tail_zero_true, encStack_zero_false,
          encStack_eq_zero_cons_tail R₁]
        exact raw_d0_b1_L01 (ListBlank.cons 1 (encStack L₁)) (encStack R₁).tail
  · cases b with
    | false =>
      dsimp only [stepZero, encode]
      rw [encStack_tail_succ (a + 1), encStack_succ a, encStack_eq_zero_cons_tail ((a, bL) :: L₁),
        ListBlank.tail_cons, encStack_tail_zero_false, encStack_tail_succ, encStack_zero_false,
        ← zero_cons_encStack R₁, encStack_eq_zero_cons_tail R₁]
      exact raw_d0_L00 (encStack ((a, bL) :: L₁)).tail (encStack R₁).tail
    | true =>
      dsimp only [stepZero, encode]
      rw [encStack_tail_succ (a + 1), encStack_succ a, encStack_eq_zero_cons_tail ((a, bL) :: L₁),
        ListBlank.tail_cons, encStack_tail_zero_true, encStack_tail_succ, encStack_zero_false,
        encStack_zero_false, encStack_eq_zero_cons_tail R₁]
      exact raw_d0_b1_L00 (encStack ((a, bL) :: L₁)).tail (encStack R₁).tail

/-! ## Acceleration Validity -/

private theorem init_reaches_start : ReachesStar target (init []) (encode start) := by
  refine (?_ : ReachesPlus target (init []) (encode start)).to_star
  dsimp only [start, encode]
  rw [encStack_tail_succ, encStack_zero_false, ListBlank.tail_cons]
  simp only [encStack]
  bb_steps

private theorem step_all (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨L, _ | ⟨⟨_ | d, b⟩, R₁⟩⟩
  · dsimp only [next]
    have hb := bounceR_spec [] (encStack L).tail
    dsimp only [bounceR] at hb
    have hcl := closeRet_spec L (.r11, [])
    have heq : encode (.E L []) = Cfg.headRight E (encStack L).tail (encStack []) := by
      simp [encode, encStack]
    rw [heq]
    exact hb.trans_star hcl
  · dsimp only [next]
    exact stepZero_spec L b R₁
  · dsimp only [next]
    have heq : encode (.E L ((d + 1, b) :: R₁)) =
        Cfg.headRight E (encStack L).tail (encStack ((d, b) :: R₁)) := by
      dsimp only [encode]
      rw [encStack_tail_succ]
    rw [heq]
    have hb := bounceR_spec ((d, b) :: R₁) (encStack L).tail
    rcases hres : bounceR ((d, b) :: R₁) with _ | p
    · rw [hres] at hb
      exact hb
    · rw [hres] at hb
      exact hb.trans_star (closeRet_spec L p)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some s s' h := by
    have hs := step_all s
    rw [h] at hs
    exact hs
  step_none s h := by
    have hs := step_all s
    rw [h] at hs
    exact hs

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC
