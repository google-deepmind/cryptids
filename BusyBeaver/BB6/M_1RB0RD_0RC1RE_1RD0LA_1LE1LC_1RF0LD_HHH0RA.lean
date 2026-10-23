/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA` (Lucy's Moonlight)

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA`
(see <https://wiki.bbchallenge.org/wiki/Lucy%27s_Moonlight>)
(**Lucy's Moonlight**, `cryptid_5`, holdout `#750`, `suspect_86`).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$C(c, b, a, d) := 0^\infty\,(10)^d\,(1110)^a\,1^b\,10\,(10)^c\,\mathrm{C}{>}\,0^\infty$$
at $C(0, 0, 0, 0)$ in 2 steps, and every $C(c, b, a, d)$ advances in `ReachesPlus` either to
another $C(c', b', a', d')$ or to a halting configuration.

## Collatz-like Acceleration Rules

```text
Consider:
C(c, b, a, d) = 0^inf (10)^d (1110)^a 1^b 10 (10)^c C> 0^inf

C(c, b+3, a, d) -> C(c+4, b, a, d)
C(c, 2, a+1, d) -> C(0, 2c+8, a, d)
C(c, 2, 0, d+1) -> C(0, 2c+6, 0, d)
C(c, 2, 0, 0)   -> C(0, 2c+5, 0, 0)
C(c, 1, a+1, d) -> C(c+3, 0, a+1, d)
C(c, 1, 0, d+1) -> C(c+3, 0, 0, d+1)
C(c, 1, 0, 0)   -> C(0, 2c+5, 0, 0)
C(c, 0, a+2, d) -> C(0, 2c+10, a, d)
C(c, 0, 1, d+1) -> C(0, 2c+8, 0, d)
C(c, 0, 1, 0)   -> C(0, 2c+7, 0, 0)
C(c, 0, 0, d)   -> C(0, 0, (c+d)/2+1, 1)  if (c+d) % 2 = 0
C(c, 0, 0, d)   -> Halt                   if (c+d) % 2 = 1

Start: C(0, 0, 0, 0), reached after 2 raw TM steps
```

## High-Level Collatz-like Acceleration

Eliminating $c$ (via base-$3$ reduction of $b$) and draining $a$ to $0$ reduces the 4-counter
dynamics $C(c, b, a, d)$ to a single counter $b \in \mathbb{N}$ plus a parity bit
$p \in \mathrm{Bool}$ representing
$L(p, b) := C(0, b, 0, \text{if } p \text{ then } 1 \text{ else } 0)$, starting at
$L(\mathrm{false}, 0)$:
- `drainA` collapses the $a \ge 1$ cascade from $C(0, b, a, d)$ ($d \in \{0, 1\}$) until $a = 0$.
- `highLevelNext` advances $L(p, b)$ directly to the next $L(p', b')$ or halts when
  $p = \mathrm{true}$ and $b \equiv 0 \pmod{3}$.
-/

@[expose] public section

namespace BusyBeaver.M_1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_HHH0RA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Sweep Lemmas -/

private theorem append_pow_succ_right (u : List (Fin 2)) (k : ℕ) (b : ListBlank (Fin 2)) :
    ListBlank.append (u ^ k) (ListBlank.append u b) =
      ListBlank.append (u ^ (k + 1)) b := by
  rw [ListBlank.append_append, ← list_pow_succ']

/-- Leftward shift across `(01)^k` in state `E`. -/
private theorem shift_E_01 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight E l
        (ListBlank.append [1] (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l)
            (ListBlank.append [1] r))
          (Cfg.headRight E (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] (ListBlank.append [1, 0] r))) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l (ListBlank.append [1, 0] r)
    rw [append_pow_succ_right [1, 0] k r] at h2
    exact (h1.trans_star h2).to_star

private theorem sweep_C_to_E (k : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) default)
      (Cfg.headRight E l
        (ListBlank.append [1, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) default)
        (Cfg.headRight E (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
          (ListBlank.append [1] (ListBlank.append [1] default))) := by
    bb_steps
  have h2 := shift_E_01 k l (ListBlank.append [1] default)
  rw [append_10_pow_one k default] at h2
  exact h1.trans_star h2

/-- Rightward shift across `(01)^k` in state `D`. -/
private theorem shift_D_01 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight D (ListBlank.append [0] l)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight D
        (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight D (ListBlank.append [0] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight D (ListBlank.append [0] (ListBlank.append [0, 1] l))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [0, 1] l) r
    rw [append_pow_succ_right [0, 1] k l] at h2
    exact (h1.trans_star h2).to_star

private theorem sweep_D_to_C (k : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D (ListBlank.append [0] l)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
      (Cfg.headRight C (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2)) l) default) := by
  have h1 := shift_D_01 k l default
  have h2 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append [0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l))
          default)
        (Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 2)) l)
          default) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (k + 1),
      ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k]
    bb_steps
  exact h1.trans_plus h2

/-- Rightward shift across `(01)^k` in state `C` with prefix `11`. -/
private theorem shift_C_01 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C (ListBlank.append [0] l)
        (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)))
      (Cfg.headRight C
        (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
        (ListBlank.append [1, 1] r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C (ListBlank.append [0] l)
            (ListBlank.append [1, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r)))
          (Cfg.headRight C (ListBlank.append [0] (ListBlank.append [1, 1] l))
            (ListBlank.append [1, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    rw [append_pow_succ_right [1, 1] k l] at h2
    exact (h1.trans_star h2).to_star

private theorem sweep_C_1101 (k : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C (ListBlank.append [0] l)
        (ListBlank.append [1, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default)))
      (Cfg.headRight C
        (ListBlank.append [0, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) l))
        default) := by
  have h1 := shift_C_01 k l default
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
          (ListBlank.append [1, 1] default))
        (Cfg.headRight C
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) l))
          default) := by
    rw [one_pow_two_mul k, ListBlank.append_pow_succ ([1] : List (Fin 2)) (2 * k)]
    bb_steps
  exact h1.trans_plus h2

/-- Rightward shift across `(01)^(2k)` in state `A`. -/
private theorem shift_A_0101 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * k)) r))
      (Cfg.headRight A (ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * (k + 1))) r))
          (Cfg.headRight A (ListBlank.append [0, 1, 1, 1] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * k)) r)) := by
      rw [Nat.mul_succ, ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (2 * k + 1),
        ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (2 * k)]
      bb_steps
    have h2 := ih (ListBlank.append [0, 1, 1, 1] l) r
    rw [append_pow_succ_right [0, 1, 1, 1] k l] at h2
    exact (h1.trans_star h2).to_star

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$C(c, b, a, d) := 0^\infty\,(10)^d\,(1110)^a\,1^b\,10\,(10)^c\,\mathrm{C}{>}\,0^\infty$. -/
def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left :=
      .rep [0, 1] 0
        (.sym 0 (.sym 1 (.rep [1] 1 (.rep [0, 1, 1, 1] 2 (.rep [0, 1] 3 .default)))))
    head := some C
    right := .default }

/-- Closed pattern set for `1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

/-- Configuration $C(c, b, a, d)$. -/
private def cfg_C (c b a d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
      (ListBlank.append [0, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ b)
          (ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ a)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default)))))
    default

/-- Intermediate configuration with $b = 0$ and $(01)^m$ at the head. -/
private def pure_C (m a d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ m)
      (ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ a)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default)))
    default

private theorem eval_pat_C (vars : ℕ → ℕ) :
    evalTapePattern pat_C vars = cfg_C (vars 0) (vars 1) (vars 2) (vars 3) :=
  rfl

private theorem in_ps_C (c b a d : ℕ) : IsInPatternSet ps (cfg_C c b a d) :=
  ⟨(pat_C, .true), List.Mem.head _,
    fun i => match i with | 0 => c | 1 => b | 2 => a | 3 => d | _ => 0, rfl, trivial⟩

/-! ## Accelerated Transition Rules -/

private theorem step_C_b_ge3 (c b a d : ℕ) :
    ReachesPlus target (cfg_C c (b + 3) a d) (cfg_C (c + 4) b a d) := by
  unfold cfg_C
  rw [append_pow_succ_right [0, 1] c, append_pow_succ_right [0, 1] (c + 4)]
  set tail :=
    ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ a)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default)
  set rest := ListBlank.append (([1] : List (Fin 2)) ^ b) tail
  have h_b :
      ListBlank.append (([1] : List (Fin 2)) ^ (b + 3)) tail =
        ListBlank.append [1, 1, 1] rest := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (b + 2),
      ListBlank.append_pow_succ ([1] : List (Fin 2)) (b + 1),
      ListBlank.append_pow_succ ([1] : List (Fin 2)) b]
    rfl
  rw [h_b]
  have h1 := sweep_C_to_E (c + 1) (ListBlank.append [1, 1, 1] rest)
  have h2 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append [1, 1, 1] rest)
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 1)) default)))
        (Cfg.headRight D (ListBlank.append [0] rest)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 3)) default)) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (c + 2),
      ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (c + 1),
      ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) c]
    bb_steps
  have h3 := sweep_D_to_C (c + 3) rest
  exact (h1.trans h2).trans h3

private theorem step_b1_01 (c : ℕ) (tail : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
          (ListBlank.append [0, 1] (ListBlank.append [1, 0, 1] tail)))
        default)
      (Cfg.headRight C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 3))
          (ListBlank.append [0, 1] (ListBlank.append [0, 1] tail)))
        default) := by
  rw [append_pow_succ_right [0, 1] c, ← append_pow_succ_right [0, 1] (c + 2)]
  have h1 := sweep_C_to_E (c + 1) (ListBlank.append [1, 0, 1] tail)
  have h2 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append [1, 0, 1] tail)
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 1)) default)))
        (Cfg.headRight D
          (ListBlank.append [0] (ListBlank.append [0, 1, 0, 1, 0, 1] tail))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) c]
    bb_steps
  have h3 := sweep_D_to_C c (ListBlank.append [0, 1, 0, 1, 0, 1] tail)
  have h_eq :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 2))
        (ListBlank.append [0, 1, 0, 1, 0, 1] tail) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 2))
          (ListBlank.append [0, 1]
            (ListBlank.append [0, 1] (ListBlank.append [0, 1] tail))) :=
    rfl
  rw [h_eq] at h3
  exact (h1.trans h2).trans h3

private theorem step_C_b1_a_succ (c a d : ℕ) :
    ReachesPlus target (cfg_C c 1 (a + 1) d) (cfg_C (c + 3) 0 (a + 1) d) := by
  unfold cfg_C
  rw [list_pow_one, list_pow_zero, ListBlank.append_nil,
    ListBlank.append_pow_succ ([0, 1, 1, 1] : List (Fin 2)) a]
  exact step_b1_01 c
    (ListBlank.append [1, 1]
      (ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ a)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default)))

private theorem step_C_b1_d_succ (c d : ℕ) :
    ReachesPlus target (cfg_C c 1 0 (d + 1)) (cfg_C (c + 3) 0 0 (d + 1)) := by
  unfold cfg_C
  rw [list_pow_one, list_pow_zero, ListBlank.append_nil,
    ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) d]
  exact step_b1_01 c (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default)

private theorem step_C_b1_00 (c : ℕ) :
    ReachesPlus target (cfg_C c 1 0 0) (cfg_C 0 (2 * c + 5) 0 0) := by
  unfold cfg_C
  rw [append_pow_succ_right [0, 1] c, list_pow_one, list_pow_zero, ListBlank.append_nil]
  have h1 := sweep_C_to_E (c + 1) (ListBlank.append [1] default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append [1] default)
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 1)) default)))
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append [1, 1] default))
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 1)) default))) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) c]
    bb_steps
  have h3 := sweep_C_1101 (c + 1) (ListBlank.append [1, 1] default)
  have h_comb :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (c + 1) + 1))
        (ListBlank.append [1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * c + 5)) default := by
    have h_2 : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
    rw [h_2, ← ListBlank.append_pow_add]
    exact congrArg (fun n => ListBlank.append (([1] : List (Fin 2)) ^ n) default) (by omega)
  rw [h_comb] at h3
  exact (h1.trans h2).trans h3

private theorem cfg_C_b0_eq_pure_C (c a d : ℕ) :
    cfg_C c 0 a d = pure_C (c + 1) a d := by
  unfold cfg_C pure_C
  rw [list_pow_zero, ListBlank.append_nil, append_pow_succ_right [0, 1] c]

private theorem cfg_C_b2_eq_pure_C (c a d : ℕ) :
    cfg_C c 2 a d = pure_C c (a + 1) d := by
  unfold cfg_C pure_C
  rw [ListBlank.append_pow_succ ([0, 1, 1, 1] : List (Fin 2)) a]
  rfl

private theorem step_pure_C_0 (m : ℕ) (tail : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [0, 1, 1, 1, 0] tail))
        default)
      (Cfg.headRight C
        (ListBlank.append [0, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 5)) tail))
        default) := by
  have h1 := sweep_C_to_E m (ListBlank.append [0, 1, 1, 1, 0] tail)
  have h2 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append [0, 1, 1, 1, 0] tail)
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ m) default)))
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append [1, 1] tail))
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 1)) default))) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m]
    bb_steps
  have h3 := sweep_C_1101 (m + 1) (ListBlank.append [1, 1] tail)
  have h_comb :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (m + 1) + 1))
        (ListBlank.append [1, 1] tail) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 5)) tail := by
    have h_2 : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
    rw [h_2, ← ListBlank.append_pow_add]
    exact congrArg (fun n => ListBlank.append (([1] : List (Fin 2)) ^ n) tail) (by omega)
  rw [h_comb] at h3
  exact (h1.trans h2).trans h3

private theorem step_pure_C_a_ge2 (m a d : ℕ) :
    ReachesPlus target (pure_C m (a + 2) d) (cfg_C 0 (2 * m + 8) a d) := by
  unfold pure_C cfg_C
  rw [list_pow_zero, ListBlank.append_nil]
  set rest :=
    ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ a)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default)
  have h_a :
      ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ (a + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default) =
        ListBlank.append [0, 1, 1, 1, 0] (ListBlank.append [1, 1, 1] rest) := by
    rw [ListBlank.append_pow_succ ([0, 1, 1, 1] : List (Fin 2)) (a + 1),
      ListBlank.append_pow_succ ([0, 1, 1, 1] : List (Fin 2)) a]
    rfl
  rw [h_a]
  have h1 := step_pure_C_0 m (ListBlank.append [1, 1, 1] rest)
  have h_comb :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 5))
        (ListBlank.append [1, 1, 1] rest) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 8)) rest := by
    have h_3 : ([1, 1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 3 := rfl
    rw [h_3, ← ListBlank.append_pow_add]
  rwa [h_comb] at h1

private theorem step_pure_C_a1_d0 (m : ℕ) :
    ReachesPlus target (pure_C m 1 0) (cfg_C 0 (2 * m + 5) 0 0) := by
  unfold pure_C cfg_C
  rw [list_pow_one, list_pow_zero, ListBlank.append_nil]
  have h_def :
      ListBlank.append [0, 1, 1, 1] (default : ListBlank (Fin 2)) =
        ListBlank.append [0, 1, 1, 1, 0] default := by
    simp
  rw [h_def]
  exact step_pure_C_0 m default

private theorem step_pure_C_a1_d_succ (m d : ℕ) :
    ReachesPlus target (pure_C m 1 (d + 1)) (cfg_C 0 (2 * m + 6) 0 d) := by
  unfold pure_C cfg_C
  rw [list_pow_one, list_pow_zero, ListBlank.append_nil,
    ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) d]
  set rest := ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default
  have h1 := step_pure_C_0 m (ListBlank.append [1] rest)
  rw [append_pow_succ_right [1] (2 * m + 5) rest] at h1
  exact h1

private theorem step_pure_C_a0_to_A (m : ℕ) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 1)) default) default)
      (Cfg.headRight A (ListBlank.append [0, 1] default)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 2)) default)) := by
  have h1 := sweep_C_to_E (m + 1) default
  have h2 :
      ReachesPlus target
        (Cfg.headRight E default
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 1)) default)))
        (Cfg.headRight A (ListBlank.append [0, 1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 2)) default)) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (m + 1),
      ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m]
    bb_steps
  exact h1.trans h2

private theorem step_pure_C_a0_odd (k : ℕ) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * k + 1)) default) default)
      (cfg_C 0 0 (k + 1) 1) := by
  have h1 := step_pure_C_a0_to_A (2 * k)
  have h2 := shift_A_0101 (k + 1) (ListBlank.append [0, 1] default) default
  have h3 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append [0, 1] default))
          default)
        (cfg_C 0 0 (k + 1) 1) := by
    unfold cfg_C
    rw [list_pow_zero, list_pow_one, ListBlank.append_nil]
    bb_steps
  exact (h1.trans_star h2).trans h3

private theorem step_pure_C_a0_even (k : ℕ) :
    ∃ cfg',
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (2 * k + 2)) default) default)
        cfg' ∧
      (step target cfg').isNone := by
  have h1 := step_pure_C_a0_to_A (2 * k + 1)
  have h2 :=
    shift_A_0101 (k + 1) (ListBlank.append [0, 1] default) (ListBlank.append [0, 1] default)
  rw [append_pow_succ_right [0, 1] (2 * (k + 1)) default] at h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append [0, 1] default))
          (ListBlank.append [0, 1] default))
        (Cfg.headRight F
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ (k + 1))
              (ListBlank.append [0, 1] default)))
          default) := by
    bb_steps
  refine ⟨_, (h1.trans_star h2).trans h3, ?_⟩
  bb_halt

/-! ## Closure of `ps` (Level A) -/

private theorem pure_C_a0_eq (m d : ℕ) :
    pure_C m 0 d =
      Cfg.headRight C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + d)) default) default := by
  unfold pure_C
  rw [list_pow_zero, ListBlank.append_nil, ← ListBlank.append_pow_add]

private theorem step_pure_C (m a d : ℕ) (hm_pos : m + a ≥ 1) :
    ∃ cfg', ReachesPlus target (pure_C m a d) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases a with _ | _ | a
  · rw [pure_C_a0_eq]
    obtain ⟨k, hk_odd | hk_even⟩ : ∃ k, m + d = 2 * k + 1 ∨ m + d = 2 * k + 2 :=
      ⟨(m + d - 1) / 2, by omega⟩
    · rw [hk_odd]
      exact ⟨cfg_C 0 0 (k + 1) 1, step_pure_C_a0_odd k, Or.inl (in_ps_C 0 0 (k + 1) 1)⟩
    · rw [hk_even]
      obtain ⟨cfg', hstep, hhalt⟩ := step_pure_C_a0_even k
      exact ⟨cfg', hstep, Or.inr hhalt⟩
  · rcases d with _ | d
    · exact ⟨cfg_C 0 (2 * m + 5) 0 0, step_pure_C_a1_d0 m,
        Or.inl (in_ps_C 0 (2 * m + 5) 0 0)⟩
    · exact ⟨cfg_C 0 (2 * m + 6) 0 d, step_pure_C_a1_d_succ m d,
        Or.inl (in_ps_C 0 (2 * m + 6) 0 d)⟩
  · exact ⟨cfg_C 0 (2 * m + 8) a d, step_pure_C_a_ge2 m a d,
      Or.inl (in_ps_C 0 (2 * m + 8) a d)⟩

private theorem step_C (c b a d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C c b a d) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | _ | b
  · rw [cfg_C_b0_eq_pure_C]
    exact step_pure_C (c + 1) a d (by omega)
  · rcases a with _ | a
    · rcases d with _ | d
      · exact ⟨cfg_C 0 (2 * c + 5) 0 0, step_C_b1_00 c,
          Or.inl (in_ps_C 0 (2 * c + 5) 0 0)⟩
      · exact ⟨cfg_C (c + 3) 0 0 (d + 1), step_C_b1_d_succ c d,
          Or.inl (in_ps_C (c + 3) 0 0 (d + 1))⟩
    · exact ⟨cfg_C (c + 3) 0 (a + 1) d, step_C_b1_a_succ c a d,
        Or.inl (in_ps_C (c + 3) 0 (a + 1) d)⟩
  · rw [cfg_C_b2_eq_pure_C]
    exact step_pure_C c (a + 1) d (by omega)
  · exact ⟨cfg_C (c + 4) b a d, step_C_b_ge3 c b a d,
      Or.inl (in_ps_C (c + 4) b a d)⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_C 0 0 0 0) := by
  have h_init : ReachesPlus target (init []) (cfg_C 0 0 0 0) := by
    unfold cfg_C
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_C 0 0 0 0, init_reaches_start, in_ps_C 0 0 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_C]
  exact step_C (vars 0) (vars 1) (vars 2) (vars 3)

/-- `1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA`. -/
inductive State where
  /-- $C(c, b, a, d) := 0^\infty\,(10)^d\,(1110)^a\,1^b\,10\,(10)^c\,\mathrm{C}{>}\,0^\infty$. -/
  | C (c b a d : ℕ)

/-- Initial symbolic state $C(0, 0, 0, 0)$, reached after 2 raw TM steps. -/
def start : State := .C 0 0 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C c b a d =>
    Cfg.headRight SixState.C
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
        (ListBlank.append [0, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ b)
            (ListBlank.append (([0, 1, 1, 1] : List (Fin 2)) ^ a)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ d) default)))))
      default

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .C c 0 0 d =>
    if (c + d) % 2 = 0 then
      some (.C 0 0 ((c + d) / 2 + 1) 1)
    else
      none
  | .C c 0 1 0 => some (.C 0 (2 * (c + 1) + 5) 0 0)
  | .C c 0 1 (d + 1) => some (.C 0 (2 * (c + 1) + 6) 0 d)
  | .C c 0 (a + 2) d => some (.C 0 (2 * (c + 1) + 8) a d)
  | .C c 1 0 0 => some (.C 0 (2 * c + 5) 0 0)
  | .C c 1 0 (d + 1) => some (.C (c + 3) 0 0 (d + 1))
  | .C c 1 (a + 1) d => some (.C (c + 3) 0 (a + 1) d)
  | .C c 2 0 0 => some (.C 0 (2 * c + 5) 0 0)
  | .C c 2 0 (d + 1) => some (.C 0 (2 * c + 6) 0 d)
  | .C c 2 (a + 1) d => some (.C 0 (2 * c + 8) a d)
  | .C c (b + 3) a d => some (.C (c + 4) b a d)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨c, b, a, d⟩ s' hnext
    rcases b with _ | _ | _ | b
    · rcases a with _ | _ | a
      · simp only [next] at hnext
        split_ifs at hnext with h_even
        simp only [Option.some.injEq] at hnext
        subst hnext
        change ReachesPlus target (cfg_C c 0 0 d) (cfg_C 0 0 ((c + d) / 2 + 1) 1)
        rw [cfg_C_b0_eq_pure_C, pure_C_a0_eq]
        have h_odd : c + 1 + d = 2 * ((c + d) / 2) + 1 := by omega
        rw [h_odd]
        exact step_pure_C_a0_odd ((c + d) / 2)
      · rcases d with _ | d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          change ReachesPlus target (cfg_C c 0 1 0) (cfg_C 0 (2 * (c + 1) + 5) 0 0)
          rw [cfg_C_b0_eq_pure_C]
          exact step_pure_C_a1_d0 (c + 1)
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          change ReachesPlus target (cfg_C c 0 1 (d + 1)) (cfg_C 0 (2 * (c + 1) + 6) 0 d)
          rw [cfg_C_b0_eq_pure_C]
          exact step_pure_C_a1_d_succ (c + 1) d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        change ReachesPlus target (cfg_C c 0 (a + 2) d) (cfg_C 0 (2 * (c + 1) + 8) a d)
        rw [cfg_C_b0_eq_pure_C]
        exact step_pure_C_a_ge2 (c + 1) a d
    · rcases a with _ | a
      · rcases d with _ | d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_b1_00 c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_b1_d_succ c d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C_b1_a_succ c a d
    · rcases a with _ | a
      · rcases d with _ | d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          change ReachesPlus target (cfg_C c 2 0 0) (cfg_C 0 (2 * c + 5) 0 0)
          rw [cfg_C_b2_eq_pure_C]
          exact step_pure_C_a1_d0 c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          change ReachesPlus target (cfg_C c 2 0 (d + 1)) (cfg_C 0 (2 * c + 6) 0 d)
          rw [cfg_C_b2_eq_pure_C]
          exact step_pure_C_a1_d_succ c d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        change ReachesPlus target (cfg_C c 2 (a + 1) d) (cfg_C 0 (2 * c + 8) a d)
        rw [cfg_C_b2_eq_pure_C]
        exact step_pure_C_a_ge2 c a d
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact step_C_b_ge3 c b a d
  step_none := by
    rintro ⟨c, b, a, d⟩ hnext
    rcases b with _ | _ | _ | b
    · rcases a with _ | _ | a
      · simp only [next] at hnext
        split_ifs at hnext with h_even
        change ∃ cfg', ReachesStar target (cfg_C c 0 0 d) cfg' ∧ (step target cfg').isNone
        rw [cfg_C_b0_eq_pure_C, pure_C_a0_eq]
        have h_even' : c + 1 + d = 2 * ((c + d) / 2) + 2 := by omega
        rw [h_even']
        obtain ⟨cfg', hp, hh⟩ := step_pure_C_a0_even ((c + d) / 2)
        exact ⟨cfg', hp.to_star, hh⟩
      · rcases d with _ | d <;> simp [next] at hnext
      · simp [next] at hnext
    · rcases a with _ | a
      · rcases d with _ | d <;> simp [next] at hnext
      · simp [next] at hnext
    · rcases a with _ | a
      · rcases d with _ | d <;> simp [next] at hnext
      · simp [next] at hnext
    · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-like Acceleration -/

/-- One-counter-plus-bit symbolic state space for the high-level Collatz-like acceleration of
`1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA` (Lucy's Moonlight), corresponding to
$C(0, b, 0, d)$ with $d \in \{0, 1\}$. -/
inductive HighLevelState where
  /-- $L(p, b) := C(0, b, 0, \text{if } p \text{ then } 1 \text{ else } 0)$. -/
  | L (p : Bool) (b : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $L(\mathrm{false}, 0) = C(0, 0, 0, 0)$. -/
def highLevelStart : HighLevelState := .L false 0

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .L p b => .C 0 b 0 (if p then 1 else 0)

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Drain the counter $a$ starting from $C(0, b, a, \text{if } p \text{ then } 1 \text{ else } 0)$
until $a = 0$, collapsing each base-$3$ reduction of $b$ into a single step. -/
def drainA (b a : ℕ) (p : Bool) : HighLevelState :=
  if a = 0 then
    .L p b
  else if a = 1 then
    let q := b / 3
    if b % 3 = 0 then .L false (8 * q + if p then 8 else 7)
    else if b % 3 = 1 then .L false (8 * q + if p then 14 else 13)
    else .L p (8 * q + 8)
  else
    let q := b / 3
    let b' := if b % 3 = 0 then 8 * q + 10 else if b % 3 = 1 then 8 * q + 16 else 8 * q + 8
    drainA b' (a - (2 - b % 3 / 2)) p
termination_by a
decreasing_by omega

/-- High-level accelerated Collatz-like transition function on $L(p, b)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .L false b =>
    let q := b / 3
    if b % 3 = 0 then some (drainA 0 (2 * q + 1) true)
    else some (.L false (8 * q + 5))
  | .L true b =>
    let q := b / 3
    if b % 3 = 0 then none
    else if b % 3 = 1 then some (drainA 0 (2 * q + 3) true)
    else some (.L false (8 * q + 6))

private theorem reachesStar_trans {s₁ s₂ s₃ : State}
    (h₁ : CollatzReachesStar next s₁ s₂) (h₂ : CollatzReachesStar next s₂ s₃) :
    CollatzReachesStar next s₁ s₃ := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  refine ⟨m + n, ?_⟩
  unfold CollatzReachesIn at *
  rw [Nat.add_comm, Function.iterate_add_apply, hm, hn]

private theorem reaches_drain_b (q : ℕ) : ∀ (c r a d : ℕ),
    CollatzReachesStar next (.C c (3 * q + r) a d) (.C (c + 4 * q) r a d) := by
  induction q with
  | zero =>
    intro c r a d
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ q ih =>
    intro c r a d
    have hstep : next (.C c (3 * (q + 1) + r) a d) = some (.C (c + 4) (3 * q + r) a d) := by
      rw [show 3 * (q + 1) + r = (3 * q + r) + 3 by omega]
      rfl
    have ih' := ih (c + 4) r a d
    rw [show c + 4 + 4 * q = c + 4 * (q + 1) by omega] at ih'
    exact CollatzReachesStar.head hstep ih'

private theorem reaches_drainA (a : ℕ) : ∀ (b : ℕ) (p : Bool),
    CollatzReachesStar next (.C 0 b a (if p then 1 else 0)) (toState (drainA b a p)) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b p
    rw [drainA]
    rcases eq_or_ne a 0 with rfl | ha0
    · simp only [↓reduceIte, toState]
      exact CollatzReachesStar.refl next _
    · have hb := reaches_drain_b (b / 3) 0 (b % 3) a (if p then 1 else 0)
      rw [Nat.div_add_mod, Nat.zero_add] at hb
      refine reachesStar_trans hb ?_
      rcases eq_or_ne a 1 with rfl | ha1
      · simp only [ha0, ↓reduceIte]
        by_cases hr0 : b % 3 = 0
        · rw [hr0]
          simp only [↓reduceIte]
          cases p
          · simp only [↓reduceIte, Bool.false_eq_true, toState]
            refine CollatzReachesStar.single ?_
            change some (State.C 0 (2 * (4 * (b / 3) + 1) + 5) 0 0) = _
            congr 2; omega
          · simp only [↓reduceIte, toState]
            refine CollatzReachesStar.single ?_
            change some (State.C 0 (2 * (4 * (b / 3) + 1) + 6) 0 0) = _
            congr 2; omega
        · by_cases hr1 : b % 3 = 1
          · rw [hr1]
            simp only [Nat.one_ne_zero, ↓reduceIte]
            have h1 : next (.C (4 * (b / 3)) 1 1 (if p then 1 else 0)) =
                some (.C (4 * (b / 3) + 3) 0 1 (if p then 1 else 0)) := by
              cases p <;> rfl
            refine CollatzReachesStar.head h1 ?_
            cases p
            · simp only [↓reduceIte, Bool.false_eq_true, toState]
              refine CollatzReachesStar.single ?_
              change some (State.C 0 (2 * (4 * (b / 3) + 3 + 1) + 5) 0 0) = _
              congr 2; omega
            · simp only [↓reduceIte, toState]
              refine CollatzReachesStar.single ?_
              change some (State.C 0 (2 * (4 * (b / 3) + 3 + 1) + 6) 0 0) = _
              congr 2; omega
          · have hr2 : b % 3 = 2 := by omega
            simp only [hr0, hr1, ↓reduceIte, toState]
            rw [hr2]
            refine CollatzReachesStar.single ?_
            change some (State.C 0 (2 * (4 * (b / 3)) + 8) 0 (if p then 1 else 0)) = _
            congr 2; omega
      · simp only [ha0, ha1, ↓reduceIte]
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
        by_cases hr0 : b % 3 = 0
        · rw [hr0]
          simp only [↓reduceIte, Nat.zero_div, Nat.sub_zero, Nat.add_sub_cancel]
          have hstep : next (.C (4 * (b / 3)) 0 (a' + 2) (if p then 1 else 0)) =
              some (.C 0 (8 * (b / 3) + 10) a' (if p then 1 else 0)) := by
            change some (State.C 0 (2 * (4 * (b / 3) + 1) + 8) a' (if p then 1 else 0)) = _
            congr 2; omega
          exact CollatzReachesStar.head hstep (ih a' (by omega) (8 * (b / 3) + 10) p)
        · by_cases hr1 : b % 3 = 1
          · rw [hr1]
            have h1div : 1 / 2 = 0 := rfl
            simp only [Nat.one_ne_zero, ↓reduceIte, h1div, Nat.sub_zero, Nat.add_sub_cancel]
            have h1 : next (.C (4 * (b / 3)) 1 (a' + 2) (if p then 1 else 0)) =
                some (.C (4 * (b / 3) + 3) 0 (a' + 2) (if p then 1 else 0)) := rfl
            have h2 : next (.C (4 * (b / 3) + 3) 0 (a' + 2) (if p then 1 else 0)) =
                some (.C 0 (8 * (b / 3) + 16) a' (if p then 1 else 0)) := by
              change some (State.C 0 (2 * (4 * (b / 3) + 3 + 1) + 8) a' (if p then 1 else 0)) = _
              congr 2; omega
            exact CollatzReachesStar.head h1
              (CollatzReachesStar.head h2 (ih a' (by omega) (8 * (b / 3) + 16) p))
          · have hr2 : b % 3 = 2 := by omega
            simp only [hr0, hr1, ↓reduceIte]
            rw [hr2]
            have hsub : a' + 2 - (2 - 2 / 2) = a' + 1 := by omega
            rw [hsub]
            have h1 : next (.C (4 * (b / 3)) 2 ((a' + 1) + 1) (if p then 1 else 0)) =
                some (.C 0 (8 * (b / 3) + 8) (a' + 1) (if p then 1 else 0)) := by
              change some (State.C 0 (2 * (4 * (b / 3)) + 8) (a' + 1) (if p then 1 else 0)) = _
              congr 2; omega
            exact CollatzReachesStar.head h1 (ih (a' + 1) (by omega) (8 * (b / 3) + 8) p)

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState) (CollatzReachesStar.refl next start) ?_
  rintro ⟨p, b⟩
  have hb := reaches_drain_b (b / 3) 0 (b % 3) 0 (if p then 1 else 0)
  rw [Nat.div_add_mod, Nat.zero_add] at hb
  refine CollatzStepsTo.of_reachesStar hb ?_
  cases p
  · by_cases hr0 : b % 3 = 0
    · simp only [highLevelNext, hr0, ↓reduceIte, Option.map_some]
      have hev : (4 * (b / 3) + 0) % 2 = 0 := by omega
      have hdiv : (4 * (b / 3) + 0) / 2 + 1 = 2 * (b / 3) + 1 := by omega
      have h1 : next (.C (4 * (b / 3)) 0 0 0) = some (.C 0 0 (2 * (b / 3) + 1) 1) := by
        simp only [next, hev, ↓reduceIte, hdiv]
      exact CollatzReachesPlus.head h1 (reaches_drainA (2 * (b / 3) + 1) 0 true)
    · simp only [highLevelNext, hr0, ↓reduceIte, Option.map_some, toState]
      have hrem : b % 3 = 1 ∨ b % 3 = 2 := by omega
      rcases hrem with hr | hr
      · rw [hr]
        refine CollatzStepsTo.of_eq ?_
        change some (State.C 0 (2 * (4 * (b / 3)) + 5) 0 0) = _
        congr 2; omega
      · rw [hr]
        refine CollatzStepsTo.of_eq ?_
        change some (State.C 0 (2 * (4 * (b / 3)) + 5) 0 0) = _
        congr 2; omega
  · by_cases hr0 : b % 3 = 0
    · simp only [highLevelNext, hr0, ↓reduceIte, Option.map_none]
      have hodd : (4 * (b / 3) + 1) % 2 ≠ 0 := by omega
      exact CollatzStepsTo.of_eq (by simp only [next, hodd, ↓reduceIte])
    · by_cases hr1 : b % 3 = 1
      · have hhl : highLevelNext (.L true b) = some (drainA 0 (2 * (b / 3) + 3) true) := by
          dsimp only [highLevelNext]
          rw [hr1]
          rfl
        rw [hhl, Option.map_some, hr1]
        have h1 : next (.C (4 * (b / 3)) 1 0 1) = some (.C (4 * (b / 3) + 3) 0 0 1) := rfl
        have hev : (4 * (b / 3) + 3 + 1) % 2 = 0 := by omega
        have hdiv : (4 * (b / 3) + 3 + 1) / 2 + 1 = 2 * (b / 3) + 3 := by omega
        have h2 : next (.C (4 * (b / 3) + 3) 0 0 1) = some (.C 0 0 (2 * (b / 3) + 3) 1) := by
          simp only [next, hev, ↓reduceIte, hdiv]
        exact CollatzReachesPlus.head h1
          (CollatzReachesStar.head h2 (reaches_drainA (2 * (b / 3) + 3) 0 true))
      · have hr2 : b % 3 = 2 := by omega
        have hhl : highLevelNext (.L true b) = some (.L false (8 * (b / 3) + 6)) := by
          dsimp only [highLevelNext]
          rw [hr2]
          rfl
        rw [hhl, Option.map_some, toState, hr2]
        refine CollatzStepsTo.of_eq ?_
        change some (State.C 0 (2 * (4 * (b / 3)) + 6) 0 0) = _
        congr 2; omega

/-- `target` halts from the blank tape if and only if the high-level acceleration `highLevelNext`
halts from `highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- The initial acceleration `next` halts from `start` if and only if the high-level acceleration
`highLevelNext` halts from `highLevelStart`. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_HHH0RA
