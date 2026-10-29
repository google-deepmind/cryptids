/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF`

Formal `HasStackReduction` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF` (Halving Tower family).

Each half-tape stack encodes unary blocks $1^{a + 1}$ separated by single zeros (`encStack`),
ordered from the tape head outward. Starting from `init []`, the machine enters a closed 3-mode
(`C`, `D`, `D00`) 2nd-order digit-stack system in 5 raw steps, where

* `C(L, R)` has state `C` reading the `0` separator between `encStack L` and `encStack R`,
* `D(L, R)` has state `D` reading the `0` separator between `encStack L` and `encStack R`,
* `D00(L, R)` has state `D` reading `0` between `encStack L` and `0 · encStack R`.

## Accelerated Transition Rules

With `β = bumpHead` (increment the head digit, or push `0` onto an empty stack):

```text
C(L, [])                 -> D(β L, [])
C(L, [0])                -> C(1 :: β L, [])
C(L, 0 :: (e + 1) :: R)  -> D00(β (β L), e :: R)
C(L, 0 :: 0 :: R)        -> D00₀(β (β L), [] | R)      (double-zero sub-system, see below)
C(L, (d + 1) :: R)       -> C(d :: β L, R)

D([], [])                -> C([0, 0], [])
D([], d :: R)            -> C([d + 1, 0], R)
D(0 :: L, R)             -> Halt (state E)
D(1 :: L, R)             -> D00(β L, β R)
D(2 :: L, [])            -> C(2 :: β L, [])
D(2 :: L, d :: R)        -> C((d + 3) :: β L, R)
D((a + 3) :: L, R)       -> D((a + 1) :: β L, β R)

D00([], R)               -> C([0, 0], R)
D00(0 :: L, R)           -> Halt (state E)
D00(1 :: L, R)           -> D00(β L, 0 :: R)
D00(2 :: L, R)           -> C(2 :: β L, R)
D00((a + 3) :: L, R)     -> D((a + 1) :: β L, 0 :: R)

Start: D([2], []), reached after 5 raw TM steps
```

The double-zero case `C(L, 0 :: 0 :: R)` is closed through an inner sub-system `C₀`, `D₀`, `D00₀`
whose right half-tape is `encRight0 R S`: the digit stack `S` encoded as usual but sealed by
`0 · encStack R` instead of the blank tape. Its rules mirror the `C`/`D`/`D00` rules
(`C₀(L, [] | R) -> D(β L, R)` re-enters the main system, `D00₀([1], S | R)` halts), and a
strong induction on the head digit shows that every inner configuration with all entries of `S`
positive either halts or returns to the main system (`rule_C_zero_zero_cons`).

<!-- hardness:begin -->
## Hardness

*Hardness class:* Problem S4 — trigger **POW**, growth mass-conserving sandpile, shield partial.

*Verdict (heuristic, from exact accelerated simulation of the certified rules):* probviously
non-halting.

*Hazard:* as #660; E3 macro twin of #659

*Simulated horizon:* family-level

*Why it is hard:* see #660

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RC_1LC0LE_1RD1RC_1LB0RA_HHH0LF_1RD1LF

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Digit-Stack Encodings and Walk Helpers -/

@[simp]
private theorem encStack_nil : encStack [] = default :=
  rfl

private theorem encStack_cons (a : ℕ) (s : List ℕ) :
    encStack (a :: s) = ((encStack s).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1)) :=
  rfl

@[simp]
private theorem encStack_cons_one (s : List ℕ) :
    (1 : Fin 2) >> encStack s = encStack (bumpHead s) := by
  cases s with
  | nil => simp [bumpHead, encStack]
  | cons a s' => rfl

local macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  simp only [Cfg.headRight, Cfg.headLeft, ListBlank.append_cons, ListBlank.append_nil,
    ListBlank.cons_zero_default, encStack_nil, encStack_cons_one,
    ListBlank.head_cons, ListBlank.tail_cons, multiStep_zero]
  try rfl))

local macro "step" : tactic => `(tactic| (
  try refine ReachesPlus.to_star ?_
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons,
    ListBlank.head_default_fin, ListBlank.tail_cons, ListBlank.tail_default,
    ListBlank.cons_zero_default]
  apply ReachesPlus.head (by rfl)
  simp only [Cfg.headRight, Cfg.headLeft, Tape.move, Tape.write,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]))

local macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  try finish))

/-- Right-sweep separator configuration: state `C` reading `0` between `L` and `R`. -/
private def cfg_C (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨0, encStack L, encStack R⟩⟩

/-- Left-split separator configuration: state `D` reading `0` between `L` and `R`. -/
private def cfg_D (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨0, encStack L, encStack R⟩⟩

/-- Double-zero separator configuration: state `D` reading `0` between `L` and `0 >> encStack R`.
-/
private def cfg_D00 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨0, encStack L, (encStack R).cons 0⟩⟩

/-- Modes of the 2nd-order digit-stack configuration family. -/
private inductive StackMode
  | C
  | D
  | D00

private def evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .C, L, R => cfg_C L R
  | .D, L, R => cfg_D L R
  | .D00, L, R => cfg_D00 L R

private def IsInStackSystem1 (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg1 m L R

/-- State `C` walks right across `1^k` (`C, 1 -> 1RC`). -/
private theorem c_walk_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{C}}> ((([1] : List (Fin 2)) ^ k) +> r)) [target]⊢*
      ((l <+ (([1] : List (Fin 2)) ^ k)) {{C}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : k + 1 = 1 + k := by omega
    rw [h_split, list_pow_add, ListBlank.append_assoc]
    have h1 :
        (l {{C}}> (([1] : List (Fin 2)) ^ 1 +> (([1] : List (Fin 2)) ^ k +> r))) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ 1)) {{C}}> (([1] : List (Fin 2)) ^ k +> r)) := by
      simp only [list_pow_one]
      execute 1
    refine h1.to_star.trans ?_
    refine (ih (l <+ (([1] : List (Fin 2)) ^ 1)) r).trans ?_
    rw [← ListBlank.append_assoc, list_pow_add_comm]

/-- State `F` walks left across `1^k` (`F, 1 -> 1LF`). -/
private theorem f_walk_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ k)) <{{F}} r) [target]⊢*
      (l <{{F}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : k + 1 = 1 + k := by omega
    rw [h_split, list_pow_add, ListBlank.append_assoc]
    have h1 :
        (((l <+ (([1] : List (Fin 2)) ^ k)) <+ (([1] : List (Fin 2)) ^ 1)) <{{F}} r) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ k)) <{{F}} (([1] : List (Fin 2)) ^ 1 +> r)) := by
      simp only [list_pow_one]
      execute 1
    refine h1.to_star.trans ?_
    refine (ih l (([1] : List (Fin 2)) ^ 1 +> r)).trans ?_
    rw [← ListBlank.append_assoc, list_pow_add_comm]

/-! ## Mode `C` Rules -/

private theorem rule_C_nil (L : List ℕ) :
    (cfg_C L []) [target]⊢⁺ (cfg_D (bumpHead L) []) := by
  unfold cfg_C cfg_D
  rw [encStack_nil]
  execute 1

private theorem rule_C_zero_nil (L : List ℕ) :
    (cfg_C L [0]) [target]⊢⁺ (cfg_C (1 :: bumpHead L) []) := by
  unfold cfg_C
  rw [encStack_cons 0 [], encStack_nil, encStack_cons 1 (bumpHead L)]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 6

private theorem rule_C_zero_succ_cons (L R : List ℕ) (e : ℕ) :
    (cfg_C L (0 :: (e + 1) :: R)) [target]⊢⁺ (cfg_D00 (bumpHead (bumpHead L)) (e :: R)) := by
  unfold cfg_C cfg_D00
  rw [encStack_cons 0 ((e + 1) :: R), encStack_cons (e + 1) R, encStack_cons e R]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 6

private theorem rule_C_succ_cons (L R : List ℕ) (d : ℕ) :
    (cfg_C L ((d + 1) :: R)) [target]⊢⁺ (cfg_C (d :: bumpHead L) R) := by
  unfold cfg_C
  rw [encStack_cons (d + 1) R]
  have h_split : d + 1 + 1 = 2 + d := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some C, ⟨0, encStack L,
        (([1] : List (Fin 2)) ^ 2) +>
          ((([1] : List (Fin 2)) ^ d) +> (encStack R).cons 0)⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) {{C}}>
          ((([1] : List (Fin 2)) ^ d) +> (encStack R).cons 0)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 3
  refine h_pre.trans_star ?_
  refine (c_walk_right d (((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    ((encStack R).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons d (bumpHead L)]
  finish

/-! ## Mode `D` Rules -/

private theorem rule_D_nil_nil :
    (cfg_D [] []) [target]⊢⁺ (cfg_C [0, 0] []) := by
  unfold cfg_D cfg_C
  rw [encStack_nil, encStack_cons 0 [0], encStack_cons 0 [], encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 5

private theorem rule_D_nil_cons (R : List ℕ) (d : ℕ) :
    (cfg_D [] (d :: R)) [target]⊢⁺ (cfg_C ((d + 1) :: [0]) R) := by
  unfold cfg_D cfg_C
  rw [encStack_nil, encStack_cons d R]
  have h_pre :
      (⟨some D, ⟨0, default,
        (([1] : List (Fin 2)) ^ (d + 1)) +> (encStack R).cons 0⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack [0]).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) {{C}}>
          ((([1] : List (Fin 2)) ^ (d + 1)) +> (encStack R).cons 0)) := by
    rw [encStack_cons 0 [], encStack_nil]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 5
  refine h_pre.trans_star ?_
  refine (c_walk_right (d + 1) (((encStack [0]).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    ((encStack R).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons (d + 1) [0]]
  finish

private def cfg_Halt_D (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, encStack L, (0 : Fin 2) >> encStack (bumpHead R)⟩⟩

private theorem rule_D_zero (L R : List ℕ) :
    ((cfg_D (0 :: L) R) [target]⊢⁺ (cfg_Halt_D L R)) ∧
      (step target (cfg_Halt_D L R)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_D cfg_Halt_D
  rw [encStack_cons 0 L]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 2

private theorem rule_D_one (L R : List ℕ) :
    (cfg_D (1 :: L) R) [target]⊢⁺ (cfg_D00 (bumpHead L) (bumpHead R)) := by
  unfold cfg_D cfg_D00
  rw [encStack_cons 1 L]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 4

private theorem rule_D_two_nil (L : List ℕ) :
    (cfg_D (2 :: L) []) [target]⊢⁺ (cfg_C (2 :: bumpHead L) []) := by
  unfold cfg_D cfg_C
  rw [encStack_cons 2 L, encStack_cons 2 (bumpHead L), encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 11

private theorem rule_D_two_cons (L R : List ℕ) (d : ℕ) :
    (cfg_D (2 :: L) (d :: R)) [target]⊢⁺ (cfg_C ((d + 3) :: bumpHead L) R) := by
  unfold cfg_D cfg_C
  rw [encStack_cons 2 L, encStack_cons d R]
  have h_pre :
      (⟨some D, ⟨0, ((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 3),
        (([1] : List (Fin 2)) ^ (d + 1)) +> (encStack R).cons 0⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 3)) {{C}}>
          ((([1] : List (Fin 2)) ^ (d + 1)) +> (encStack R).cons 0)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 11
  refine h_pre.trans_star ?_
  refine (c_walk_right (d + 1) (((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 3))
    ((encStack R).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons (d + 3) (bumpHead L)]
  finish

private theorem rule_D_ge3 (L R : List ℕ) (a : ℕ) :
    (cfg_D ((a + 3) :: L) R) [target]⊢⁺ (cfg_D ((a + 1) :: bumpHead L) (bumpHead R)) := by
  unfold cfg_D
  rw [encStack_cons (a + 3) L]
  have h_split : a + 3 + 1 = 2 + (a + 1 + 1) := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some D, ⟨0, (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1 + 1))) <+
        (([1] : List (Fin 2)) ^ 2), encStack R⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1 + 1))) <{{F}}
          (((encStack (bumpHead R)).cons 0).cons 0)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 3
  refine h_pre.trans_star ?_
  rw [list_pow_add, ListBlank.append_assoc]
  refine (f_walk_left (a + 1) (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    (((encStack (bumpHead R)).cons 0).cons 0)).trans ?_
  have h_split3 : a + 1 = 1 + a := by omega
  rw [h_split3, list_pow_add, ListBlank.append_assoc]
  have h_mid :
      ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) <{{F}}
        ((([1] : List (Fin 2)) ^ 1) +>
          ((([1] : List (Fin 2)) ^ a) +> (((encStack (bumpHead R)).cons 0).cons 0))))
        [target]⊢⁺
        ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) {{C}}>
          ((([1] : List (Fin 2)) ^ a) +> (((encStack (bumpHead R)).cons 0).cons 0))) := by
    simp only [list_pow_one]
    execute 4
  refine h_mid.to_star.trans ?_
  refine (c_walk_right a (((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    (((encStack (bumpHead R)).cons 0).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons a (bumpHead L)]
  have h_post :
      ((encStack (a :: bumpHead L)) {{C}}> (((encStack (bumpHead R)).cons 0).cons 0))
        [target]⊢⁺
        (⟨some D, ⟨0, encStack ((a + 1) :: bumpHead L), encStack (bumpHead R)⟩⟩ :
          Cfg (Fin 2) (Fin 6)) := by
    execute 1
  rw [Nat.add_comm 1 a]
  exact h_post.to_star

/-! ## Mode `D00` Rules -/

private theorem rule_D00_nil (R : List ℕ) :
    (cfg_D00 [] R) [target]⊢⁺ (cfg_C [0, 0] R) := by
  unfold cfg_D00 cfg_C
  rw [encStack_nil, encStack_cons 0 [0], encStack_cons 0 [], encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 5

private def cfg_Halt_D00 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, encStack L, (0 : Fin 2) >> (1 : Fin 2) >> (encStack R).cons 0⟩⟩

private theorem rule_D00_zero (L R : List ℕ) :
    ((cfg_D00 (0 :: L) R) [target]⊢⁺ (cfg_Halt_D00 L R)) ∧
      (step target (cfg_Halt_D00 L R)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_D00 cfg_Halt_D00
  rw [encStack_cons 0 L]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 2

private theorem rule_D00_one (L R : List ℕ) :
    (cfg_D00 (1 :: L) R) [target]⊢⁺ (cfg_D00 (bumpHead L) (0 :: R)) := by
  unfold cfg_D00
  rw [encStack_cons 1 L, encStack_cons 0 R]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 4

private theorem rule_D00_two (L R : List ℕ) :
    (cfg_D00 (2 :: L) R) [target]⊢⁺ (cfg_C (2 :: bumpHead L) R) := by
  unfold cfg_D00 cfg_C
  rw [encStack_cons 2 L, encStack_cons 2 (bumpHead L)]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 11

private theorem rule_D00_ge3 (L R : List ℕ) (a : ℕ) :
    (cfg_D00 ((a + 3) :: L) R) [target]⊢⁺ (cfg_D ((a + 1) :: bumpHead L) (0 :: R)) := by
  unfold cfg_D00 cfg_D
  rw [encStack_cons (a + 3) L]
  have h_split : a + 3 + 1 = 2 + (a + 1 + 1) := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some D, ⟨0, (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1 + 1))) <+
        (([1] : List (Fin 2)) ^ 2), (encStack R).cons 0⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1 + 1))) <{{F}}
          (((encStack (0 :: R)).cons 0).cons 0)) := by
    rw [encStack_cons 0 R]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 3
  refine h_pre.trans_star ?_
  rw [list_pow_add, ListBlank.append_assoc]
  refine (f_walk_left (a + 1) (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    (((encStack (0 :: R)).cons 0).cons 0)).trans ?_
  have h_split3 : a + 1 = 1 + a := by omega
  rw [h_split3, list_pow_add, ListBlank.append_assoc]
  have h_mid :
      ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) <{{F}}
        ((([1] : List (Fin 2)) ^ 1) +>
          ((([1] : List (Fin 2)) ^ a) +> (((encStack (0 :: R)).cons 0).cons 0))))
        [target]⊢⁺
        ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) {{C}}>
          ((([1] : List (Fin 2)) ^ a) +> (((encStack (0 :: R)).cons 0).cons 0))) := by
    simp only [list_pow_one]
    execute 4
  refine h_mid.to_star.trans ?_
  refine (c_walk_right a (((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    (((encStack (0 :: R)).cons 0).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons a (bumpHead L)]
  have h_post :
      ((encStack (a :: bumpHead L)) {{C}}> (((encStack (0 :: R)).cons 0).cons 0))
        [target]⊢⁺
        (⟨some D, ⟨0, encStack ((a + 1) :: bumpHead L), encStack (0 :: R)⟩⟩ :
          Cfg (Fin 2) (Fin 6)) := by
    execute 1
  rw [Nat.add_comm 1 a]
  exact h_post.to_star

/-! ## Double-Zero Sub-System (`C(L, 0 :: 0 :: R)`) -/

/-- Right half-tape of the inner sub-system: the digit stack `R_act` encoded as `encStack`, but
sealed by `0 >> encStack R` instead of the blank tape. -/
private def encRight0 (R : List ℕ) : List ℕ → ListBlank (Fin 2)
  | [] => (encStack R).cons 0
  | d :: R_act => (([1] : List (Fin 2)) ^ (d + 1)) +> ((encRight0 R R_act).cons 0)

private theorem encRight0_nil (R : List ℕ) : encRight0 R [] = (encStack R).cons 0 :=
  rfl

private theorem encRight0_cons (R : List ℕ) (d : ℕ) (R_act : List ℕ) :
    encRight0 R (d :: R_act) = (([1] : List (Fin 2)) ^ (d + 1)) +> ((encRight0 R R_act).cons 0) :=
  rfl

/-- Inner right-sweep configuration: state `C` reading `0` between `L` and `encRight0 R R_act`. -/
private def cfg_C0 (R L R_act : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨0, encStack L, encRight0 R R_act⟩⟩

/-- Inner left-split configuration: state `D` reading `0` between `L` and `encRight0 R R_act`. -/
private def cfg_D0 (R L R_act : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨0, encStack L, encRight0 R R_act⟩⟩

/-- Inner double-zero configuration: state `D` reading `0` between `L` and
`0 >> encRight0 R R_act`. -/
private def cfg_D00_0 (R L R_act : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨0, encStack L, (encRight0 R R_act).cons 0⟩⟩

private theorem rule_C_zero_zero_to_D00_0 (L R : List ℕ) :
    (cfg_C L (0 :: 0 :: R)) [target]⊢⁺ (cfg_D00_0 R (bumpHead (bumpHead L)) []) := by
  unfold cfg_C cfg_D00_0
  rw [encStack_cons 0 (0 :: R), encStack_cons 0 R, encRight0_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 6

private def cfg_Halt_D00_0 (R R_act : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, default,
    (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (encRight0 R R_act).cons 0⟩⟩

private theorem rule_D00_0_one_nil_halt (R R_act : List ℕ) :
    ((cfg_D00_0 R [1] R_act) [target]⊢⁺ (cfg_Halt_D00_0 R R_act)) ∧
      (step target (cfg_Halt_D00_0 R R_act)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_D00_0 cfg_Halt_D00_0
  rw [encStack_cons 1 [], encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 6

private theorem rule_C0_nil (R L : List ℕ) :
    (cfg_C0 R L []) [target]⊢⁺ (cfg_D (bumpHead L) R) := by
  unfold cfg_C0 cfg_D
  rw [encRight0_nil]
  execute 1

private theorem rule_C0_succ_cons (R L R_act : List ℕ) (d : ℕ) :
    (cfg_C0 R L ((d + 1) :: R_act)) [target]⊢⁺ (cfg_C0 R (d :: bumpHead L) R_act) := by
  unfold cfg_C0
  rw [encRight0_cons R (d + 1) R_act]
  have h_split : d + 1 + 1 = 2 + d := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some C, ⟨0, encStack L,
        (([1] : List (Fin 2)) ^ 2) +>
          ((([1] : List (Fin 2)) ^ d) +> (encRight0 R R_act).cons 0)⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) {{C}}>
          ((([1] : List (Fin 2)) ^ d) +> (encRight0 R R_act).cons 0)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 3
  refine h_pre.trans_star ?_
  refine (c_walk_right d (((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    ((encRight0 R R_act).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons d (bumpHead L)]
  finish

private theorem rule_D00_0_two (R L R_act : List ℕ) :
    (cfg_D00_0 R (2 :: L) R_act) [target]⊢⁺ (cfg_C0 R (2 :: bumpHead L) R_act) := by
  unfold cfg_D00_0 cfg_C0
  rw [encStack_cons 2 L, encStack_cons 2 (bumpHead L)]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 11

private theorem rule_D00_0_ge3 (R L R_act : List ℕ) (a : ℕ) :
    (cfg_D00_0 R ((a + 3) :: L) R_act) [target]⊢⁺
      (cfg_D0 R ((a + 1) :: bumpHead L) (0 :: R_act)) := by
  unfold cfg_D00_0 cfg_D0
  rw [encStack_cons (a + 3) L]
  have h_split : a + 3 + 1 = 2 + (a + 1 + 1) := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some D, ⟨0, (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1 + 1))) <+
        (([1] : List (Fin 2)) ^ 2), (encRight0 R R_act).cons 0⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1 + 1))) <{{F}}
          (((encRight0 R (0 :: R_act)).cons 0).cons 0)) := by
    rw [encRight0_cons R 0 R_act]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 3
  refine h_pre.trans_star ?_
  rw [list_pow_add, ListBlank.append_assoc]
  refine (f_walk_left (a + 1) (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    (((encRight0 R (0 :: R_act)).cons 0).cons 0)).trans ?_
  have h_split3 : a + 1 = 1 + a := by omega
  rw [h_split3, list_pow_add, ListBlank.append_assoc]
  have h_mid :
      ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) <{{F}}
        ((([1] : List (Fin 2)) ^ 1) +>
          ((([1] : List (Fin 2)) ^ a) +> (((encRight0 R (0 :: R_act)).cons 0).cons 0))))
        [target]⊢⁺
        ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) {{C}}>
          ((([1] : List (Fin 2)) ^ a) +> (((encRight0 R (0 :: R_act)).cons 0).cons 0))) := by
    simp only [list_pow_one]
    execute 4
  refine h_mid.to_star.trans ?_
  refine (c_walk_right a (((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    (((encRight0 R (0 :: R_act)).cons 0).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons a (bumpHead L)]
  have h_post :
      ((encStack (a :: bumpHead L)) {{C}}> (((encRight0 R (0 :: R_act)).cons 0).cons 0))
        [target]⊢⁺
        (⟨some D, ⟨0, encStack ((a + 1) :: bumpHead L), encRight0 R (0 :: R_act)⟩⟩ :
          Cfg (Fin 2) (Fin 6)) := by
    execute 1
  rw [Nat.add_comm 1 a]
  exact h_post.to_star

private theorem rule_D0_one_cons (R L R_act : List ℕ) (d : ℕ) :
    (cfg_D0 R (1 :: L) (d :: R_act)) [target]⊢⁺
      (cfg_D00_0 R (bumpHead L) ((d + 1) :: R_act)) := by
  unfold cfg_D0 cfg_D00_0
  rw [encStack_cons 1 L, encRight0_cons R d R_act, encRight0_cons R (d + 1) R_act]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 4

private theorem rule_D0_two_cons (R L R_act : List ℕ) (d : ℕ) :
    (cfg_D0 R (2 :: L) (d :: R_act)) [target]⊢⁺ (cfg_C0 R ((d + 3) :: bumpHead L) R_act) := by
  unfold cfg_D0 cfg_C0
  rw [encStack_cons 2 L, encRight0_cons R d R_act]
  have h_pre :
      (⟨some D, ⟨0, ((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 3),
        (([1] : List (Fin 2)) ^ (d + 1)) +> (encRight0 R R_act).cons 0⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 3)) {{C}}>
          ((([1] : List (Fin 2)) ^ (d + 1)) +> (encRight0 R R_act).cons 0)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 11
  refine h_pre.trans_star ?_
  refine (c_walk_right (d + 1) (((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 3))
    ((encRight0 R R_act).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons (d + 3) (bumpHead L)]
  finish

private theorem rule_D0_ge3_cons (R L R_act : List ℕ) (a d : ℕ) :
    (cfg_D0 R ((a + 3) :: L) (d :: R_act)) [target]⊢⁺
      (cfg_D0 R ((a + 1) :: bumpHead L) ((d + 1) :: R_act)) := by
  unfold cfg_D0
  rw [encStack_cons (a + 3) L]
  have h_split : a + 3 + 1 = 2 + (a + 1 + 1) := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some D, ⟨0, (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1 + 1))) <+
        (([1] : List (Fin 2)) ^ 2), encRight0 R (d :: R_act)⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1 + 1))) <{{F}}
          (((encRight0 R ((d + 1) :: R_act)).cons 0).cons 0)) := by
    rw [encRight0_cons R d R_act, encRight0_cons R (d + 1) R_act]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 3
  refine h_pre.trans_star ?_
  rw [list_pow_add, ListBlank.append_assoc]
  refine (f_walk_left (a + 1) (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    (((encRight0 R ((d + 1) :: R_act)).cons 0).cons 0)).trans ?_
  have h_split3 : a + 1 = 1 + a := by omega
  rw [h_split3, list_pow_add, ListBlank.append_assoc]
  have h_mid :
      ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) <{{F}}
        ((([1] : List (Fin 2)) ^ 1) +>
          ((([1] : List (Fin 2)) ^ a) +> (((encRight0 R ((d + 1) :: R_act)).cons 0).cons 0))))
        [target]⊢⁺
        ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) {{C}}>
          ((([1] : List (Fin 2)) ^ a) +> (((encRight0 R ((d + 1) :: R_act)).cons 0).cons 0))) := by
    simp only [list_pow_one]
    execute 4
  refine h_mid.to_star.trans ?_
  refine (c_walk_right a (((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    (((encRight0 R ((d + 1) :: R_act)).cons 0).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons a (bumpHead L)]
  have h_post :
      ((encStack (a :: bumpHead L)) {{C}}> (((encRight0 R ((d + 1) :: R_act)).cons 0).cons 0))
        [target]⊢⁺
        (⟨some D, ⟨0, encStack ((a + 1) :: bumpHead L), encRight0 R ((d + 1) :: R_act)⟩⟩ :
          Cfg (Fin 2) (Fin 6)) := by
    execute 1
  rw [Nat.add_comm 1 a]
  exact h_post.to_star

/-- `cfg` reaches (in `≥ 1` steps) a stack configuration or a halting configuration. -/
private abbrev Closes (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ cfg', (cfg [target]⊢⁺ cfg') ∧ (IsInStackSystem1 cfg' ∨ (step target cfg').isNone)

private theorem Closes_step {c₁ c₂ : Cfg (Fin 2) (Fin 6)} (h₁ : c₁ [target]⊢⁺ c₂)
    (h₂ : Closes c₂) : Closes c₁ := by
  rcases h₂ with ⟨cfg', h_rest, h_end⟩
  exact ⟨cfg', h₁.trans h_rest, h_end⟩

/-- An inner `C₀` sweep across a right stack of positive digits re-enters the main system. -/
private theorem c0_sweep_pos_to_D (R R_pos L : List ℕ) :
    Closes (cfg_C0 R L (List.map (· + 1) R_pos)) := by
  induction R_pos generalizing L with
  | nil => exact ⟨cfg_D (bumpHead L) R, rule_C0_nil R L, Or.inl ⟨.D, bumpHead L, R, rfl⟩⟩
  | cons d R_pos' ih =>
    exact Closes_step (rule_C0_succ_cons R L (List.map (· + 1) R_pos') d) (ih (d :: bumpHead L))

/-- Peeling the head digit `a + 1` of an inner `D₀` configuration either closes or returns to an
inner `D00₀` configuration with a smaller second digit bound. -/
private theorem d0_peel_gen (R : List ℕ) (a : ℕ) :
    ∀ (b₀ : ℕ) (L'' : List ℕ) (d : ℕ) (R_pos : List ℕ),
      Closes (cfg_D0 R ((a + 1) :: (b₀ + 1) :: L'') (d :: List.map (· + 1) R_pos)) ∨
      (∃ b₁ d₁, b₁ ≤ b₀ + a / 2 ∧
        (cfg_D0 R ((a + 1) :: (b₀ + 1) :: L'') (d :: List.map (· + 1) R_pos)) [target]⊢⁺
          (cfg_D00_0 R ((b₁ + 2) :: L'') (List.map (· + 1) (d₁ :: R_pos)))) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b₀ L'' d R_pos
    rcases a with _ | _ | a'
    · refine Or.inr ⟨b₀, d, by omega, ?_⟩
      simpa [bumpHead] using rule_D0_one_cons R ((b₀ + 1) :: L'') (List.map (· + 1) R_pos) d
    · refine Or.inl (Closes_step ?_ (c0_sweep_pos_to_D R R_pos ((d + 3) :: (b₀ + 2) :: L'')))
      simpa [bumpHead] using rule_D0_two_cons R ((b₀ + 1) :: L'') (List.map (· + 1) R_pos) d
    · have h_step :
          (cfg_D0 R ((a' + 2 + 1) :: (b₀ + 1) :: L'') (d :: List.map (· + 1) R_pos)) [target]⊢⁺
            (cfg_D0 R ((a' + 1) :: (b₀ + 2) :: L'') ((d + 1) :: List.map (· + 1) R_pos)) := by
        simpa [bumpHead] using
          rule_D0_ge3_cons R ((b₀ + 1) :: L'') (List.map (· + 1) R_pos) a' d
      rcases ih a' (by omega) (b₀ + 1) L'' (d + 1) R_pos with h_close | ⟨b₁, d₁, hb₁, h_rest⟩
      · exact Or.inl (Closes_step h_step h_close)
      · exact Or.inr ⟨b₁, d₁, by omega, h_step.trans h_rest⟩

/-- Every inner `D00₀` configuration with a single left digit `a + 2` closes. -/
private theorem d00_single_closed (R : List ℕ) (a : ℕ) :
    ∀ (R_pos : List ℕ), Closes (cfg_D00_0 R [a + 2] (List.map (· + 1) R_pos)) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro R_pos
    rcases a with _ | _ | _ | a'
    · refine Closes_step ?_ (c0_sweep_pos_to_D R R_pos [2, 0])
      simpa [bumpHead] using rule_D00_0_two R [] (List.map (· + 1) R_pos)
    · have h1 : (cfg_D00_0 R [3] (List.map (· + 1) R_pos)) [target]⊢⁺
          (cfg_D0 R [1, 0] (0 :: List.map (· + 1) R_pos)) := by
        simpa [bumpHead] using rule_D00_0_ge3 R [] (List.map (· + 1) R_pos) 0
      have h2 : (cfg_D0 R [1, 0] (0 :: List.map (· + 1) R_pos)) [target]⊢⁺
          (cfg_D00_0 R [1] (1 :: List.map (· + 1) R_pos)) := by
        simpa [bumpHead] using rule_D0_one_cons R [0] (List.map (· + 1) R_pos) 0
      obtain ⟨h3, hnone⟩ := rule_D00_0_one_nil_halt R (1 :: List.map (· + 1) R_pos)
      exact ⟨_, (h1.trans h2).trans h3, Or.inr hnone⟩
    · have h1 : (cfg_D00_0 R [4] (List.map (· + 1) R_pos)) [target]⊢⁺
          (cfg_D0 R [2, 0] (0 :: List.map (· + 1) R_pos)) := by
        simpa [bumpHead] using rule_D00_0_ge3 R [] (List.map (· + 1) R_pos) 1
      have h2 : (cfg_D0 R [2, 0] (0 :: List.map (· + 1) R_pos)) [target]⊢⁺
          (cfg_C0 R [3, 1] (List.map (· + 1) R_pos)) := by
        simpa [bumpHead] using rule_D0_two_cons R [0] (List.map (· + 1) R_pos) 0
      exact Closes_step (h1.trans h2) (c0_sweep_pos_to_D R R_pos [3, 1])
    · have h1 : (cfg_D00_0 R [a' + 3 + 2] (List.map (· + 1) R_pos)) [target]⊢⁺
          (cfg_D0 R ((a' + 3) :: [0]) (0 :: List.map (· + 1) R_pos)) := by
        simpa [bumpHead] using rule_D00_0_ge3 R [] (List.map (· + 1) R_pos) (a' + 2)
      have h2 : (cfg_D0 R ((a' + 3) :: [0]) (0 :: List.map (· + 1) R_pos)) [target]⊢⁺
          (cfg_D0 R ((a' + 1) :: [1]) (1 :: List.map (· + 1) R_pos)) := by
        simpa [bumpHead] using rule_D0_ge3_cons R [0] (List.map (· + 1) R_pos) a' 0
      rcases d0_peel_gen R a' 0 [] 1 R_pos with h_close | ⟨b₁, d₁, hb₁, h_rest⟩
      · exact Closes_step (h1.trans h2) h_close
      · exact Closes_step ((h1.trans h2).trans h_rest) (ih b₁ (by omega) (d₁ :: R_pos))

/-- Every inner `D00₀` configuration with head left digit `a + 2` closes. -/
private theorem d00_list_closed (R L_tail : List ℕ) :
    ∀ (a : ℕ) (R_pos : List ℕ),
      Closes (cfg_D00_0 R ((a + 2) :: L_tail) (List.map (· + 1) R_pos)) := by
  induction L_tail with
  | nil =>
    intro a R_pos
    exact d00_single_closed R a R_pos
  | cons b L'' ih =>
    intro a R_pos
    rcases a with _ | a'
    · refine Closes_step ?_ (c0_sweep_pos_to_D R R_pos (2 :: (b + 1) :: L''))
      simpa [bumpHead] using rule_D00_0_two R (b :: L'') (List.map (· + 1) R_pos)
    · have h1 : (cfg_D00_0 R ((a' + 1 + 2) :: b :: L'') (List.map (· + 1) R_pos)) [target]⊢⁺
          (cfg_D0 R ((a' + 1) :: (b + 1) :: L'') (0 :: List.map (· + 1) R_pos)) := by
        simpa [bumpHead] using rule_D00_0_ge3 R (b :: L'') (List.map (· + 1) R_pos) a'
      rcases d0_peel_gen R a' b L'' 0 R_pos with h_close | ⟨b₁, d₁, _, h_rest⟩
      · exact Closes_step h1 h_close
      · exact Closes_step (h1.trans h_rest) (ih b₁ (d₁ :: R_pos))

private theorem rule_C_zero_zero_cons (L R : List ℕ) :
    Closes (cfg_C L (0 :: 0 :: R)) := by
  refine Closes_step (rule_C_zero_zero_to_D00_0 L R) ?_
  cases L with
  | nil =>
    obtain ⟨hstep, hnone⟩ := rule_D00_0_one_nil_halt R []
    exact ⟨_, hstep, Or.inr hnone⟩
  | cons a L_tail =>
    exact d00_list_closed R L_tail a []

/-! ## Initial Reachability and Stack Reduction Closure -/

private theorem init_to_cfg_D :
    (init []) [target]⊢⁺ (cfg_D [2] []) := by
  unfold cfg_D
  rw [encStack_cons 2 [], encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 5

private theorem init_reaches_nontrivial :
    (init []) [target]⊢⁺ evalStackCfg1 .D [1, 1] [0] :=
  init_to_cfg_D
    |>.trans (rule_D_two_nil [])
    |>.trans (rule_C_nil [2, 0])
    |>.trans (rule_D_ge3 [0] [] 0)

private theorem stack_system_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : IsInStackSystem1 cfg) :
    ∃ cfg', (cfg [target]⊢⁺ cfg') ∧
      (IsInStackSystem1 cfg' ∨ (step target cfg').isNone) := by
  rcases h with ⟨m, L, R, rfl⟩
  cases m with
  | C =>
    cases R with
    | nil =>
      exact ⟨cfg_D (bumpHead L) [], rule_C_nil L, Or.inl ⟨.D, bumpHead L, [], rfl⟩⟩
    | cons d R' =>
      rcases d with _ | d
      · cases R' with
        | nil =>
          exact ⟨cfg_C (1 :: bumpHead L) [], rule_C_zero_nil L,
            Or.inl ⟨.C, 1 :: bumpHead L, [], rfl⟩⟩
        | cons e R'' =>
          rcases e with _ | e
          · exact rule_C_zero_zero_cons L R''
          · exact ⟨cfg_D00 (bumpHead (bumpHead L)) (e :: R''), rule_C_zero_succ_cons L R'' e,
              Or.inl ⟨.D00, bumpHead (bumpHead L), e :: R'', rfl⟩⟩
      · exact ⟨cfg_C (d :: bumpHead L) R', rule_C_succ_cons L R' d,
          Or.inl ⟨.C, d :: bumpHead L, R', rfl⟩⟩
  | D =>
    cases L with
    | nil =>
      cases R with
      | nil =>
        exact ⟨cfg_C [0, 0] [], rule_D_nil_nil, Or.inl ⟨.C, [0, 0], [], rfl⟩⟩
      | cons d R' =>
        exact ⟨cfg_C ((d + 1) :: [0]) R', rule_D_nil_cons R' d,
          Or.inl ⟨.C, (d + 1) :: [0], R', rfl⟩⟩
    | cons a L' =>
      rcases a with _ | _ | _ | a
      · obtain ⟨hstep, hnone⟩ := rule_D_zero L' R
        exact ⟨cfg_Halt_D L' R, hstep, Or.inr hnone⟩
      · exact ⟨cfg_D00 (bumpHead L') (bumpHead R), rule_D_one L' R,
          Or.inl ⟨.D00, bumpHead L', bumpHead R, rfl⟩⟩
      · cases R with
        | nil =>
          exact ⟨cfg_C (2 :: bumpHead L') [], rule_D_two_nil L',
            Or.inl ⟨.C, 2 :: bumpHead L', [], rfl⟩⟩
        | cons d R' =>
          exact ⟨cfg_C ((d + 3) :: bumpHead L') R', rule_D_two_cons L' R' d,
            Or.inl ⟨.C, (d + 3) :: bumpHead L', R', rfl⟩⟩
      · exact ⟨cfg_D ((a + 1) :: bumpHead L') (bumpHead R), rule_D_ge3 L' R a,
          Or.inl ⟨.D, (a + 1) :: bumpHead L', bumpHead R, rfl⟩⟩
  | D00 =>
    cases L with
    | nil =>
      exact ⟨cfg_C [0, 0] R, rule_D00_nil R, Or.inl ⟨.C, [0, 0], R, rfl⟩⟩
    | cons a L' =>
      rcases a with _ | _ | _ | a
      · obtain ⟨hstep, hnone⟩ := rule_D00_zero L' R
        exact ⟨cfg_Halt_D00 L' R, hstep, Or.inr hnone⟩
      · exact ⟨cfg_D00 (bumpHead L') (0 :: R), rule_D00_one L' R,
          Or.inl ⟨.D00, bumpHead L', 0 :: R, rfl⟩⟩
      · exact ⟨cfg_C (2 :: bumpHead L') R, rule_D00_two L' R,
          Or.inl ⟨.C, 2 :: bumpHead L', R, rfl⟩⟩
      · exact ⟨cfg_D ((a + 1) :: bumpHead L') (0 :: R), rule_D00_ge3 L' R a,
          Or.inl ⟨.D, (a + 1) :: bumpHead L', 0 :: R, rfl⟩⟩

private theorem encStack_head (a : ℕ) (s : List ℕ) : (encStack (a :: s)).head = 1 := by
  simp [encStack, list_pow_succ]

private theorem encStack_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ s : List ℕ, encStack s ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default, rfl, ?_⟩
  intro s h
  rcases s with _ | ⟨_ | a, rest⟩
  · have h1 := congrArg ListBlank.head h
    simp [encStack] at h1
  · rcases rest with _ | ⟨b, s'⟩
    · have h1 := congrArg (fun x => x.tail.tail.tail.head) h
      simp [encStack, list_pow_succ, list_pow_zero] at h1
    · have h1 := congrArg (fun x => x.tail.tail.head) h
      simp [encStack, list_pow_succ, list_pow_zero] at h1
  · have h1 := congrArg (fun x => x.tail.head) h
    simp [encStack, list_pow_succ] at h1

private theorem block_encoding :
    ∃ strideL offsetL sepL strideR offsetR sepR : ℕ,
      strideL > 0 ∧ offsetL > 0 ∧ sepL > 0 ∧
      strideR > 0 ∧ offsetR > 0 ∧ sepR > 0 ∧
      (∀ a L, encStack (a :: L) =
        ListBlank.append (([1] : List (Fin 2)) ^ (strideL * a + offsetL))
          (ListBlank.append (([0] : List (Fin 2)) ^ sepL) (encStack L))) ∧
      (∀ d R, encStack (d :: R) =
        ListBlank.append (([1] : List (Fin 2)) ^ (strideR * d + offsetR))
          (ListBlank.append (([0] : List (Fin 2)) ^ sepR) (encStack R))) := by
  refine ⟨1, 1, 1, 1, 1, 1,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro a L
    simp [encStack]
  · intro d R
    simp [encStack]

private theorem modes_bounded :
    ∃ modes : List StackMode, modes.length ≤ 6 ∧ ∀ m : StackMode, m ∈ modes := by
  refine ⟨[.C, .D, .D00], by decide, ?_⟩
  intro m
  cases m <;> simp

private theorem valid_stack_modes : IsValidStackModes encStack encStack evalStackCfg1 := by
  intro m
  cases m with
  | C => exact ⟨C, .id [], .id [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩
  | D => exact ⟨D, .id [], .id [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩
  | D00 => exact ⟨D, .id [], .id [0], by decide, by decide, Or.inl (fun _ _ => rfl)⟩

/-- `target` reduces to a closed 2nd-order digit-stack system (`HasStackReduction`). -/
theorem has_stack_reduction : HasStackReduction target :=
  HasStackReduction.of_oneDigit target StackMode encStack encStack evalStackCfg1 IsInStackSystem1
    ⟨rfl, rfl, encStack_head, encStack_head,
      encStack_not_surjective, encStack_not_surjective,
      block_encoding, modes_bounded, valid_stack_modes,
      fun _ => Iff.rfl, fun m L R => ⟨m, L, R, rfl⟩,
      ⟨.D, [1, 1], [0], init_reaches_nontrivial, by decide, ⟨1, by decide, by decide⟩⟩,
      Or.inl ⟨.D00, .D00, 1, (· + 1), (0 :: ·),
        fun _ => Nat.le_succ _, fun z L R => rule_D00_one (z :: L) R⟩,
      stack_system_closed⟩

end BusyBeaver.M_1RB1RC_1LC0LE_1RD1RC_1LB0RA_HHH0LF_1RD1LF
