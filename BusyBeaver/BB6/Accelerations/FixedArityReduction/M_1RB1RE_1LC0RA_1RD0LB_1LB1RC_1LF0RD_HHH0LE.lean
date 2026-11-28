/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE`
(see <https://wiki.bbchallenge.org/wiki/1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE>)
(holdout #421, `suspect_13`, redirects to **BMO5**).

Starting from the blank tape (`init []`), the trajectory reaches the three-family canonical
configuration system
$$\begin{aligned}
C_1(a) &:= 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,0^\infty, \\
D(a, b, c) &:= 0^\infty\,1^b\,(10)^{a+1}\,\mathrm{D}{>}\,(01)^{c+1}\,0^\infty, \\
C_2(a, b) &:= 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,1101\,(01)^b\,0^\infty
\end{aligned}$$
at $C_1(3)$ in 8 steps, and every configuration in $\{C_1, D, C_2\}$ advances in `ReachesPlus`
either to another configuration in $\{C_1, D, C_2\}$ or to a halting configuration.

## Collatz-like Acceleration Rules

```text
Consider:
C1(a)       = 0^inf 1^{a+1} C> 0^inf
D(a, b, c)  = 0^inf 1^b (10)^{a+1} D> (01)^{c+1} 0^inf
C2(a, b)    = 0^inf 1^{a+1} C> 1101 (01)^b 0^inf

C1(0)             -> Halt
C1(1)             -> C2(1, 0)
C1(a + 2)         -> D(0, a, 1)

C2(0, b)          -> C1(2b + 7)
C2(1, b)          -> C1(2b + 9)
C2(a + 2, b)      -> C2(a, b + 2)

D(a, 0, 0)        -> C2(2a + 1, 1)
D(a, 1, 0)        -> C2(2a + 3, 0)
D(a, 2, 0)        -> C2(2a + 5, 0)
D(a, 3, 0)        -> Halt
D(a, 4, 0)        -> Halt
D(a, 5, 0)        -> C2(1, a + 3)
D(a, b + 6, 0)    -> D(0, b, a + 4)
D(a, 0, c + 1)    -> C2(2a + 3, c)
D(a, 1, c + 1)    -> D(a + 1, 0, c)
D(a, b + 2, c + 1)-> D(a + 2, b, c)

Start: C1(3), reached after 8 raw TM steps
```

## High-Level Collatz-like Acceleration

Contracting the $C_2(a, b) \to^* C_1(2a + 2b + 7)$ sweep and evaluating the $D(a, b, c)$ diagonal
drain $k = \min(\lfloor b/2 \rfloor, c)$ across cycles $D(a, b + 6, 0) \to D(0, b, a + 4)$
(which strictly decrease $b$) reduces the entire three-family system to a **single-counter**
Collatz-like map on $C(a) := C_1(a)$ starting at $C(3)$:
- $C(0) \to \text{Halt}$, $C(1) \to C(9)$, and $C(a + 2) \to \mathrm{evalD0}(a, 1)$.
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Sweep Lemmas -/

/-- Rightward shift across `(01)^k` in state `A`. -/
private theorem shift_A_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight A (ListBlank.append [0, 1] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [0, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Rightward shift across `(01)^k` in state `C`, producing `(11)^k` on the left. -/
private theorem shift_C_right_pair (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight C (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight C (ListBlank.append [1, 1] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Rightward shift across `(01)^k` in state `C`, producing `1^{2k}` on the left. -/
private theorem shift_C_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight C (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) r) := by
  rw [← one_pow_two_mul]
  exact shift_C_right_pair k l r

/-- Leftward shift across `(10)^k` in state `C` with `11` under the head. -/
private theorem shift_C_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1, 1] r))
      (Cfg.headRight C l
        (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1, 1] r))
          (Cfg.headRight C
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 1] (ListBlank.append [0, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [0, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Leftward shift across `(10)^k` in state `F` with `11` under the head. -/
private theorem shift_F_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1, 1] r))
      (Cfg.headRight F l
        (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight F
            (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1, 1] r))
          (Cfg.headRight F
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 1] (ListBlank.append [0, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [0, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern $C_1(a) := 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,0^\infty$. -/
def pat_C1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .default }

/-- Canonical tape pattern
$D(a, b, c) := 0^\infty\,1^b\,(10)^{a+1}\,\mathrm{D}{>}\,(01)^{c+1}\,0^\infty$. -/
def pat_D : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.rep [1] 1 .default)))
    head := some D
    right := .sym 0 (.sym 1 (.rep [0, 1] 2 .default)) }

/-- Canonical tape pattern
$C_2(a, b) := 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,1101\,(01)^b\,0^\infty$. -/
def pat_C2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default)))) }

/-- Closed pattern set for `1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C1, .true), (pat_D, .true), (pat_C2, .true)]

/-- Configuration $C_1(a)$. -/
def cfg_C1 (a : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    default

/-- Configuration $D(a, b, c)$. -/
def cfg_D (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D
    (ListBlank.append [0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
        (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
    (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))

/-- Configuration $C_2(a, b)$. -/
def cfg_C2 (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [1, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default))

private theorem eval_pat_C1 (vars : ℕ → ℕ) :
    evalTapePattern pat_C1 vars = cfg_C1 (vars 0) :=
  rfl

private theorem eval_pat_D (vars : ℕ → ℕ) :
    evalTapePattern pat_D vars = cfg_D (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem eval_pat_C2 (vars : ℕ → ℕ) :
    evalTapePattern pat_C2 vars = cfg_C2 (vars 0) (vars 1) :=
  rfl

private theorem in_ps_C1 (a : ℕ) : IsInPatternSet ps (cfg_C1 a) :=
  ⟨(pat_C1, .true), List.Mem.head _,
    fun i => match i with | 0 => a | _ => 0, rfl, trivial⟩

private theorem in_ps_D (a b c : ℕ) : IsInPatternSet ps (cfg_D a b c) :=
  ⟨(pat_D, .true), List.Mem.tail _ (List.Mem.head _),
    fun i => match i with | 0 => a | 1 => b | 2 => c | _ => 0, rfl, trivial⟩

private theorem in_ps_C2 (a b : ℕ) : IsInPatternSet ps (cfg_C2 a b) :=
  ⟨(pat_C2, .true), List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
    fun i => match i with | 0 => a | 1 => b | _ => 0, rfl, trivial⟩

/-! ## Accelerated Transition Rules for `C1` -/

private theorem step_C1_0 :
    ∃ cfg', ReachesPlus target (cfg_C1 0) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F default (ListBlank.append [0, 1, 0, 1, 0, 1] default), ?_, ?_⟩
  · unfold cfg_C1
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  · bb_halt

private theorem step_C1_1 :
    ReachesPlus target (cfg_C1 1) (cfg_C2 1 0) := by
  unfold cfg_C1 cfg_C2
  rw [list_pow_one, list_pow_zero, ListBlank.append_nil]
  bb_steps

private theorem step_C1_ge2 (a : ℕ) :
    ReachesPlus target (cfg_C1 (a + 2)) (cfg_D 0 a 1) := by
  unfold cfg_C1 cfg_D
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    have h_add : a + 2 = 2 + a := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_l, list_pow_zero, list_pow_one, ListBlank.append_nil]
  bb_steps

private theorem step_C1 (a : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C1 a) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases a with _ | _ | a'
  · obtain ⟨cfg', h1, h2⟩ := step_C1_0
    exact ⟨cfg', h1, Or.inr h2⟩
  · exact ⟨cfg_C2 1 0, step_C1_1, Or.inl (in_ps_C2 1 0)⟩
  · exact ⟨cfg_D 0 a' 1, step_C1_ge2 a', Or.inl (in_ps_D 0 a' 1)⟩

/-! ## Accelerated Transition Rules for `C2` -/

private theorem sweep_C2_base (l : ListBlank (Fin 2)) (b : ℕ) :
    ReachesPlus target
      (Cfg.headRight C (ListBlank.append [1] l)
        (ListBlank.append [1, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default)))
      (Cfg.headRight C (ListBlank.append [0] l)
        (ListBlank.append [1, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [1] l)
          (ListBlank.append [1, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default)))
        (Cfg.headRight A (ListBlank.append [0] l)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default)) := by
    have h_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [0, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default) := by
      have h_add : b + 2 = 2 + b := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  have h2 := shift_A_right (b + 2) (ListBlank.append [0] l) default
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) (ListBlank.append [0] l))
          default)
        (Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) (ListBlank.append [0] l))
          (ListBlank.append [1, 1] default)) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_C_left (b + 2) (ListBlank.append [0] l) default
  exact h123.trans_star h4

private theorem step_C2_0 (b : ℕ) :
    ReachesPlus target (cfg_C2 0 b) (cfg_C1 (2 * b + 7)) := by
  unfold cfg_C2
  rw [list_pow_zero, ListBlank.append_nil]
  have h1 := sweep_C2_base default b
  have h2 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [0] default)
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default)))
        (Cfg.headRight C default
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 4)) default)) := by
    have h_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [0, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default) := by
      have h_add : b + 4 = 2 + (b + 2) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_right (b + 4) default default
  have h123 := h12.trans_star h3
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (b + 4))) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * b + 7)) default) := by
    have h_eq : 2 * (b + 4) = (2 * b + 7) + 1 := by omega
    rw [h_eq, ListBlank.append_pow_succ]
  unfold cfg_C1
  rwa [h_l] at h123

private theorem step_C2_1 (b : ℕ) :
    ReachesPlus target (cfg_C2 1 b) (cfg_C1 (2 * b + 9)) := by
  unfold cfg_C2
  rw [list_pow_one]
  have h1 := sweep_C2_base (ListBlank.append [1] default) b
  have h2 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [0] (ListBlank.append [1] default))
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default)))
        (Cfg.headRight C default
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 5)) default)) := by
    have h_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 5)) (default : ListBlank (Fin 2)) =
          ListBlank.append [0, 1, 0, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default) := by
      have h_add : b + 5 = 3 + (b + 2) := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_right (b + 5) default default
  have h123 := h12.trans_star h3
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (b + 5))) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * b + 9)) default) := by
    have h_eq : 2 * (b + 5) = (2 * b + 9) + 1 := by omega
    rw [h_eq, ListBlank.append_pow_succ]
  unfold cfg_C1
  rwa [h_l] at h123

private theorem step_C2_ge2 (a b : ℕ) :
    ReachesPlus target (cfg_C2 (a + 2) b) (cfg_C2 a (b + 2)) := by
  unfold cfg_C2
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    have h_add : a + 2 = 2 + a := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_l]
  have h1 := sweep_C2_base
    (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)) b
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0]
            (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default)))
        (Cfg.headRight C
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          (ListBlank.append [1, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default))) := by
    bb_steps
  exact h1.trans h2

private theorem step_C2 (a b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C2 a b) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases a with _ | _ | a'
  · exact ⟨cfg_C1 (2 * b + 7), step_C2_0 b, Or.inl (in_ps_C1 (2 * b + 7))⟩
  · exact ⟨cfg_C1 (2 * b + 9), step_C2_1 b, Or.inl (in_ps_C1 (2 * b + 9))⟩
  · exact ⟨cfg_C2 a' (b + 2), step_C2_ge2 a' b, Or.inl (in_ps_C2 a' (b + 2))⟩

/-! ## Accelerated Transition Rules for `D` -/

private theorem drain_D_left (a : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D
        (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) l))
        (ListBlank.append [0, 1] r))
      (Cfg.headRight C l
        (ListBlank.append [1, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] r)))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) l))
          (ListBlank.append [0, 1] r))
        (Cfg.headRight C (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) l)
          (ListBlank.append [1, 1] (ListBlank.append [1, 1] r))) := by
    bb_steps
  have h2 := shift_C_left a l (ListBlank.append [1, 1] r)
  exact h1.trans_star h2

private theorem sweep_D_b0 (a : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D
        (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
        (ListBlank.append [0, 1] r))
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (a + 2))) default)
        (ListBlank.append [1, 1] r)) := by
  have h1 := drain_D_left a default r
  have h2 :
      ReachesPlus target
        (Cfg.headRight C default
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] r))))
        (Cfg.headRight C default
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 2))
            (ListBlank.append [1, 1] r))) := by
    have h_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 2)) (ListBlank.append [1, 1] r) =
          ListBlank.append [0, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] r)) := by
      have h_add : a + 2 = 2 + a := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_r]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_right (a + 2) default (ListBlank.append [1, 1] r)
  exact h12.trans_star h3

private theorem step_D_b0_c0 (a : ℕ) :
    ReachesPlus target (cfg_D a 0 0) (cfg_C2 (2 * a + 1) 1) := by
  unfold cfg_D
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := sweep_D_b0 a default
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (a + 2))) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 1)) default) := by
    have h_eq : 2 * (a + 2) = 3 + (2 * a + 1) := by omega
    rw [h_eq, ListBlank.append_pow_add]
    rfl
  rw [h_l] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 1)) default))
          (ListBlank.append [1, 1] default))
        (cfg_C2 (2 * a + 1) 1) := by
    unfold cfg_C2
    rw [list_pow_one]
    bb_steps
  exact h1.trans h2

private theorem step_D_b0_csucc (a c : ℕ) :
    ReachesPlus target (cfg_D a 0 (c + 1)) (cfg_C2 (2 * a + 3) c) := by
  unfold cfg_D
  rw [list_pow_zero, ListBlank.append_nil, ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) c]
  have h1 := sweep_D_b0 a
    (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (a + 2))) (default : ListBlank (Fin 2)) =
        ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 3)) default) := by
    have h_eq : 2 * (a + 2) = (2 * a + 3) + 1 := by omega
    rw [h_eq, ListBlank.append_pow_succ]
  unfold cfg_C2
  rwa [h_l] at h1

private theorem bounce_D_succ (a : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D
        (ListBlank.append [0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append [1] l)))
        (ListBlank.append [0, 1] r))
      (Cfg.headRight D
        (ListBlank.append [0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) (ListBlank.append [0] l)))
        r) := by
  have h1 := drain_D_left a (ListBlank.append [1] l) r
  have h2 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [1] l)
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] r))))
        (Cfg.headRight A (ListBlank.append [0] l)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1))
            (ListBlank.append [1, 1] r))) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_A_right (a + 1) (ListBlank.append [0] l) (ListBlank.append [1, 1] r)
  have h123 := h12.trans_star h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) (ListBlank.append [0] l))
          (ListBlank.append [1, 1] r))
        (Cfg.headRight D
          (ListBlank.append [0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) (ListBlank.append [0] l)))
          r) := by
    bb_steps
  exact h123.trans h4

private theorem step_D_b1_csucc (a c : ℕ) :
    ReachesPlus target (cfg_D a 1 (c + 1)) (cfg_D (a + 1) 0 c) := by
  unfold cfg_D
  rw [list_pow_one, list_pow_zero, ListBlank.append_nil,
    ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) c]
  have h := bounce_D_succ a default
    (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))
  have h_def : ListBlank.append [0] (default : ListBlank (Fin 2)) = default := by simp
  rwa [h_def] at h

private theorem step_D_b_ge2_csucc (a b c : ℕ) :
    ReachesPlus target (cfg_D a (b + 2) (c + 1)) (cfg_D (a + 2) b c) := by
  unfold cfg_D
  have h_b :
      ListBlank.append (([1] : List (Fin 2)) ^ (b + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1]
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)) := by
    have h_add : b + 2 = 2 + b := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_b, ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) c]
  have h := bounce_D_succ a
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
    (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))
  have h_l :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1))
        (ListBlank.append [0]
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ b) (default : ListBlank (Fin 2))))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 2))
          (ListBlank.append (([1] : List (Fin 2)) ^ b) default) := by
    have h_01 :
        ListBlank.append [0]
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ b) (default : ListBlank (Fin 2)))) =
          ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default) := rfl
    rw [h_01, ListBlank.append_append, ← list_pow_succ']
  rwa [h_l] at h

private theorem finish_D_empty_default (k : ℕ) :
    ReachesPlus target
      (Cfg.headRight D
        (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
        default)
      (cfg_C2 (2 * k + 1) 0) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
          default)
        (Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default)
          (ListBlank.append [1, 1] (ListBlank.append [1] default))) := by
    bb_steps
  have h2 := shift_C_left k default (ListBlank.append [1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C default
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] default))))
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append [1] default))) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_C_right (k + 1) (ListBlank.append [1, 1] default) (ListBlank.append [1] default)
  have h1234 := h123.trans_star h4
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1)))
        (ListBlank.append [1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default) := by
    have h_11 :
        ListBlank.append [1, 1] (default : ListBlank (Fin 2)) =
          ListBlank.append (([1] : List (Fin 2)) ^ 2) default := rfl
    rw [h_11, ListBlank.append_append, ← list_pow_add]
    have h_eq : 2 * (k + 1) + 2 = 3 + (2 * k + 1) := by omega
    rw [h_eq, ListBlank.append_pow_add]
    rfl
  rw [h_l] at h1234
  have h5 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) default))
          (ListBlank.append [1] default))
        (cfg_C2 (2 * k + 1) 0) := by
    unfold cfg_C2
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h1234.trans h5

private theorem step_D_b1_c0 (a : ℕ) :
    ReachesPlus target (cfg_D a 1 0) (cfg_C2 (2 * a + 3) 0) := by
  unfold cfg_D
  rw [list_pow_one, list_pow_zero, ListBlank.append_nil]
  have h1 := bounce_D_succ a default default
  have h_def : ListBlank.append [0] (default : ListBlank (Fin 2)) = default := by simp
  rw [h_def] at h1
  have h2 := finish_D_empty_default (a + 1)
  have h_eq : 2 * (a + 1) + 1 = 2 * a + 3 := by omega
  rw [h_eq] at h2
  exact h1.trans h2

private theorem step_D_b2_c0 (a : ℕ) :
    ReachesPlus target (cfg_D a 2 0) (cfg_C2 (2 * a + 5) 0) := by
  unfold cfg_D
  have h_2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [h_2, list_pow_zero, ListBlank.append_nil]
  have h1 := bounce_D_succ a (ListBlank.append [1] default) default
  have h_l :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1))
        (ListBlank.append [0] (ListBlank.append [1] (default : ListBlank (Fin 2)))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 2)) default := by
    have h_01 :
        ListBlank.append [0] (ListBlank.append [1] (default : ListBlank (Fin 2))) =
          ListBlank.append [0, 1] default := rfl
    rw [h_01, ListBlank.append_append, ← list_pow_succ']
  rw [h_l] at h1
  have h2 := finish_D_empty_default (a + 2)
  have h_eq : 2 * (a + 2) + 1 = 2 * a + 5 := by omega
  rw [h_eq] at h2
  exact h1.trans h2

private theorem finish_D_empty_succ (k : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D
        (ListBlank.append [0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] l)))
        default)
      (Cfg.headRight F (ListBlank.append [0] l)
        (ListBlank.append [1, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) default))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append [0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] l)))
          default)
        (Cfg.headRight C
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] l))
          (ListBlank.append [1, 1] (ListBlank.append [1] default))) := by
    bb_steps
  have h2 := shift_C_left k (ListBlank.append [1] l) (ListBlank.append [1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C (ListBlank.append [1] l)
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] default))))
        (Cfg.headRight A (ListBlank.append [0] l)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append [1] default))) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_A_right (k + 1) (ListBlank.append [0] l) (ListBlank.append [1] default)
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [0] l))
          (ListBlank.append [1] default))
        (Cfg.headRight F
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [0] l))
          (ListBlank.append [1, 1] default)) := by
    bb_steps
  have h12345 := h1234.trans h5
  have h6 := shift_F_left (k + 1) (ListBlank.append [0] l) default
  exact h12345.trans_star h6

private theorem sweep_D_ge3_c0 (a : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D
        (ListBlank.append [0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append [1, 1, 1] l)))
        (ListBlank.append [0, 1] default))
      (Cfg.headRight F (ListBlank.append [0] l)
        (ListBlank.append [1, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 3)) default))) := by
  have h1 := bounce_D_succ a (ListBlank.append [1, 1] l) default
  have h_l :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1))
        (ListBlank.append [0] (ListBlank.append [1, 1] l)) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 2)) (ListBlank.append [1] l) := by
    have h_01 :
        ListBlank.append [0] (ListBlank.append [1, 1] l) =
          ListBlank.append [0, 1] (ListBlank.append [1] l) := rfl
    rw [h_01, ListBlank.append_append, ← list_pow_succ']
  rw [h_l] at h1
  have h2 := finish_D_empty_succ (a + 2) l
  exact h1.trans h2

private theorem step_D_b3_c0 (a : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_D a 3 0) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F default
    (ListBlank.append [0, 1, 0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 3)) default)), ?_, ?_⟩
  · unfold cfg_D
    have h_3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [h_3, list_pow_zero, ListBlank.append_nil]
    have h1 := sweep_D_ge3_c0 a default
    have h2 :
        ReachesPlus target
          (Cfg.headRight F (ListBlank.append [0] default)
            (ListBlank.append [1, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 3)) default)))
          (Cfg.headRight F default
            (ListBlank.append [0, 1, 0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 3)) default))) := by
      bb_steps
    exact h1.trans h2
  · bb_halt

private theorem step_D_b4_c0 (a : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_D a 4 0) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F default
    (ListBlank.append [0, 1, 0, 1, 0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 3)) default)), ?_, ?_⟩
  · unfold cfg_D
    have h_4 :
        ListBlank.append (([1] : List (Fin 2)) ^ 4) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1] (ListBlank.append [1] default) := rfl
    rw [h_4, list_pow_zero, ListBlank.append_nil]
    have h1 := sweep_D_ge3_c0 a (ListBlank.append [1] default)
    have h2 :
        ReachesPlus target
          (Cfg.headRight F (ListBlank.append [0] (ListBlank.append [1] default))
            (ListBlank.append [1, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 3)) default)))
          (Cfg.headRight F default
            (ListBlank.append [0, 1, 0, 1, 0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 3)) default))) := by
      bb_steps
    exact h1.trans h2
  · bb_halt

private theorem step_D_b5_c0 (a : ℕ) :
    ReachesPlus target (cfg_D a 5 0) (cfg_C2 1 (a + 3)) := by
  unfold cfg_D
  have h_5 :
      ListBlank.append (([1] : List (Fin 2)) ^ 5) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1] (ListBlank.append [1, 1] default) := rfl
  rw [h_5, list_pow_zero, ListBlank.append_nil]
  have h1 := sweep_D_ge3_c0 a (ListBlank.append [1, 1] default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight F (ListBlank.append [0] (ListBlank.append [1, 1] default))
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 3)) default)))
        (cfg_C2 1 (a + 3)) := by
    unfold cfg_C2
    rw [list_pow_one]
    bb_steps
  exact h1.trans h2

private theorem step_D_b_ge6_c0 (a b : ℕ) :
    ReachesPlus target (cfg_D a (b + 6) 0) (cfg_D 0 b (a + 4)) := by
  unfold cfg_D
  have h_6 :
      ListBlank.append (([1] : List (Fin 2)) ^ (b + 6)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)) := by
    have h_add : b + 6 = 6 + b := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_6, list_pow_zero, ListBlank.append_nil]
  have h1 := sweep_D_ge3_c0 a
    (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
  have h2 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [0]
            (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 3)) default)))
        (Cfg.headRight D
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
          (ListBlank.append [0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 4)) default))) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (a + 3)]
    bb_steps
  exact h1.trans h2

private theorem step_D (a b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_D a b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases c with _ | c'
  · rcases b with _ | _ | _ | _ | _ | _ | b'
    · exact ⟨cfg_C2 (2 * a + 1) 1, step_D_b0_c0 a, Or.inl (in_ps_C2 (2 * a + 1) 1)⟩
    · exact ⟨cfg_C2 (2 * a + 3) 0, step_D_b1_c0 a, Or.inl (in_ps_C2 (2 * a + 3) 0)⟩
    · exact ⟨cfg_C2 (2 * a + 5) 0, step_D_b2_c0 a, Or.inl (in_ps_C2 (2 * a + 5) 0)⟩
    · obtain ⟨cfg', h1, h2⟩ := step_D_b3_c0 a
      exact ⟨cfg', h1, Or.inr h2⟩
    · obtain ⟨cfg', h1, h2⟩ := step_D_b4_c0 a
      exact ⟨cfg', h1, Or.inr h2⟩
    · exact ⟨cfg_C2 1 (a + 3), step_D_b5_c0 a, Or.inl (in_ps_C2 1 (a + 3))⟩
    · exact ⟨cfg_D 0 b' (a + 4), step_D_b_ge6_c0 a b', Or.inl (in_ps_D 0 b' (a + 4))⟩
  · rcases b with _ | _ | b'
    · exact ⟨cfg_C2 (2 * a + 3) c', step_D_b0_csucc a c', Or.inl (in_ps_C2 (2 * a + 3) c')⟩
    · exact ⟨cfg_D (a + 1) 0 c', step_D_b1_csucc a c', Or.inl (in_ps_D (a + 1) 0 c')⟩
    · exact ⟨cfg_D (a + 2) b' c', step_D_b_ge2_csucc a b' c', Or.inl (in_ps_D (a + 2) b' c')⟩

/-! ## Level A: Closed Pattern Set -/

private theorem init_reaches_start : ReachesStar target (init []) (cfg_C1 3) := by
  have h_init : ReachesPlus target (init []) (cfg_C1 3) := by
    unfold cfg_C1
    have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [h3]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_C1 3, init_reaches_start, in_ps_C1 3⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl | rfl
  · rw [eval_pat_C1]
    exact step_C1 (vars 0)
  · rw [eval_pat_D]
    exact step_D (vars 0) (vars 1) (vars 2)
  · rw [eval_pat_C2]
    exact step_C2 (vars 0) (vars 1)

/-- `1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE`. -/
inductive State where
  /-- $C_1(a) := 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,0^\infty$. -/
  | C1 (a : ℕ)
  /-- $D(a, b, c) := 0^\infty\,1^b\,(10)^{a+1}\,\mathrm{D}{>}\,(01)^{c+1}\,0^\infty$. -/
  | D (a b c : ℕ)
  /-- $C_2(a, b) := 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,1101\,(01)^b\,0^\infty$. -/
  | C2 (a b : ℕ)

/-- Initial symbolic state $C_1(3)$, reached after 8 raw TM steps. -/
def start : State := .C1 3

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C1 a => cfg_C1 a
  | .D a b c => cfg_D a b c
  | .C2 a b => cfg_C2 a b

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .C1 0 => none
  | .C1 1 => some (.C2 1 0)
  | .C1 (a + 2) => some (.D 0 a 1)
  | .C2 0 b => some (.C1 (2 * b + 7))
  | .C2 1 b => some (.C1 (2 * b + 9))
  | .C2 (a + 2) b => some (.C2 a (b + 2))
  | .D a 0 0 => some (.C2 (2 * a + 1) 1)
  | .D a 1 0 => some (.C2 (2 * a + 3) 0)
  | .D a 2 0 => some (.C2 (2 * a + 5) 0)
  | .D _ 3 0 => none
  | .D _ 4 0 => none
  | .D a 5 0 => some (.C2 1 (a + 3))
  | .D a (b + 6) 0 => some (.D 0 b (a + 4))
  | .D a 0 (c + 1) => some (.C2 (2 * a + 3) c)
  | .D a 1 (c + 1) => some (.D (a + 1) 0 c)
  | .D a (b + 2) (c + 1) => some (.D (a + 2) b c)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro (⟨a⟩ | ⟨a, b, c⟩ | ⟨a, b⟩) s' hnext
    · rcases a with _ | _ | a'
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C1_1
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C1_ge2 a'
    · rcases c with _ | c'
      · rcases b with _ | _ | _ | _ | _ | _ | b'
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b0_c0 a
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b1_c0 a
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b2_c0 a
        · simp [next] at hnext
        · simp [next] at hnext
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b5_c0 a
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b_ge6_c0 a b'
      · rcases b with _ | _ | b'
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b0_csucc a c'
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b1_csucc a c'
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_D_b_ge2_csucc a b' c'
    · rcases a with _ | _ | a'
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C2_0 b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C2_1 b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C2_ge2 a' b
  step_none := by
    rintro (⟨a⟩ | ⟨a, b, c⟩ | ⟨a, b⟩) hnext
    · rcases a with _ | _ | a'
      · obtain ⟨cfg', hp, hh⟩ := step_C1_0
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
      · simp [next] at hnext
    · rcases c with _ | c'
      · rcases b with _ | _ | _ | _ | _ | _ | b'
        · simp [next] at hnext
        · simp [next] at hnext
        · simp [next] at hnext
        · obtain ⟨cfg', hp, hh⟩ := step_D_b3_c0 a
          exact ⟨cfg', hp.to_star, hh⟩
        · obtain ⟨cfg', hp, hh⟩ := step_D_b4_c0 a
          exact ⟨cfg', hp.to_star, hh⟩
        · simp [next] at hnext
        · simp [next] at hnext
      · rcases b with _ | _ | b' <;> simp [next] at hnext
    · rcases a with _ | _ | a' <;> simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-like Acceleration -/

/-- High-level symbolic state $C(a) := C_1(a)$ on a single counter $a$. -/
inductive HighLevelState where
  | C (a : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $C(3)$. -/
def highLevelStart : HighLevelState := .C 3

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .C a => .C1 a

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Evaluate $D(0, b, c)$ across the diagonal $(b, c)$ sweep and any subsequent $b \ge 6$ cycles
until returning to $C_1$ or halting. -/
def evalD0 (b c : ℕ) : Option HighLevelState :=
  let k := min (b / 2) c
  let a1 := 2 * k
  let b1 := b - 2 * k
  let c1 := c - k
  if c1 > 0 then
    if b1 = 0 then some (.C (4 * a1 + 2 * c1 + 11))
    else if c1 = 1 then some (.C (4 * a1 + 15))
    else some (.C (4 * a1 + 2 * c1 + 13))
  else if b1 = 0 then some (.C (4 * a1 + 11))
  else if b1 = 1 then some (.C (4 * a1 + 13))
  else if b1 = 2 then some (.C (4 * a1 + 17))
  else if b1 = 3 ∨ b1 = 4 then none
  else if b1 = 5 then some (.C (2 * a1 + 15))
  else evalD0 (b1 - 6) (a1 + 4)
termination_by b
decreasing_by omega

/-- High-level single-counter Collatz-like transition function on $C(a)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .C 0 => none
  | .C 1 => some (.C 9)
  | .C (a + 2) => evalD0 a 1

private theorem reaches_C2_even (j : ℕ) (r b : ℕ) :
    CollatzReachesStar next (.C2 (2 * j + r) b) (.C2 r (b + 2 * j)) := by
  induction j generalizing b with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ j ih =>
    have h_step : next (.C2 (2 * (j + 1) + r) b) = some (.C2 (2 * j + r) (b + 2)) := by
      have ha : 2 * (j + 1) + r = (2 * j + r) + 2 := by omega
      rw [ha]
      rfl
    have ih' := ih (b + 2)
    have hb : b + 2 + 2 * j = b + 2 * (j + 1) := by omega
    rw [hb] at ih'
    exact CollatzReachesStar.head h_step ih'

private theorem stepsTo_C2 (a b : ℕ) :
    CollatzStepsTo next (.C2 a b) (some (.C1 (2 * a + 2 * b + 7))) := by
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 2 ∧ a = 2 * j + r :=
    ⟨a / 2, a % 2, Nat.mod_lt _ (by omega), (Nat.div_add_mod a 2).symm⟩
  refine CollatzStepsTo.of_reachesStar (reaches_C2_even j r b) ?_
  interval_cases r
  · have h : 2 * (b + 2 * j) + 7 = 2 * (2 * j + 0) + 2 * b + 7 := by omega
    rw [← h]
    exact CollatzStepsTo.of_eq rfl
  · have h : 2 * (b + 2 * j) + 9 = 2 * (2 * j + 1) + 2 * b + 7 := by omega
    rw [← h]
    exact CollatzStepsTo.of_eq rfl

private theorem reaches_D_diag (k : ℕ) (a b c : ℕ) :
    CollatzReachesStar next (.D a (b + 2 * k) (c + k)) (.D (a + 2 * k) b c) := by
  induction k generalizing a with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    have h_step : next (.D a (b + 2 * (k + 1)) (c + (k + 1))) =
        some (.D (a + 2) (b + 2 * k) (c + k)) := by
      have hb : b + 2 * (k + 1) = (b + 2 * k) + 2 := by omega
      have hc : c + (k + 1) = (c + k) + 1 := by omega
      rw [hb, hc]
      simp [next]
    have ih' := ih (a + 2)
    have ha : a + 2 + 2 * k = a + 2 * (k + 1) := by omega
    rw [ha] at ih'
    exact CollatzReachesStar.head h_step ih'

private theorem stepsTo_evalD0 (b c : ℕ) :
    CollatzStepsTo next (.D 0 b c) ((evalD0 b c).map toState) := by
  induction b using Nat.strongRecOn generalizing c with
  | ind b ih =>
    let k := min (b / 2) c
    have h_diag := reaches_D_diag k 0 (b - 2 * k) (c - k)
    have hb_eq : b - 2 * k + 2 * k = b := by omega
    have hc_eq : c - k + k = c := by omega
    rw [Nat.zero_add, hb_eq, hc_eq] at h_diag
    refine CollatzStepsTo.of_reachesStar h_diag ?_
    rw [evalD0]
    set a1 := 2 * k
    set b1 := b - 2 * k
    set c1 := c - k
    by_cases hc1 : c1 > 0
    · simp only [hc1, ↓reduceIte]
      have hb1_lt : b1 < 2 := by omega
      obtain ⟨c1', hc1'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : c1 ≠ 0)
      interval_cases b1
      · simp only [↓reduceIte, Option.map, toState]
        rw [hc1']
        refine CollatzStepsTo.head rfl ?_
        have h_c2 := stepsTo_C2 (2 * a1 + 3) c1'
        have h_eq : 2 * (2 * a1 + 3) + 2 * c1' + 7 = 4 * a1 + 2 * (c1' + 1) + 11 := by omega
        rwa [h_eq] at h_c2
      · simp only [one_ne_zero, ↓reduceIte]
        rw [hc1']
        rcases c1' with _ | c2
        · simp only [↓reduceIte, Option.map, toState]
          refine CollatzStepsTo.head rfl (CollatzStepsTo.head rfl ?_)
          have h_c2 := stepsTo_C2 (2 * (a1 + 1) + 1) 1
          have h_eq : 2 * (2 * (a1 + 1) + 1) + 2 * 1 + 7 = 4 * a1 + 15 := by omega
          rwa [h_eq] at h_c2
        · simp only [Option.map, toState]
          refine CollatzStepsTo.head rfl (CollatzStepsTo.head rfl ?_)
          have h_c2 := stepsTo_C2 (2 * (a1 + 1) + 3) c2
          have h_eq : 2 * (2 * (a1 + 1) + 3) + 2 * c2 + 7 =
              4 * a1 + 2 * (c2 + 1 + 1) + 13 := by omega
          rwa [h_eq] at h_c2
    · simp only [hc1, ↓reduceIte]
      have hc1_zero : c1 = 0 := by omega
      rw [hc1_zero]
      rcases b1 with _ | _ | _ | _ | _ | _ | b2
      · simp only [↓reduceIte, Option.map, toState]
        refine CollatzStepsTo.head rfl ?_
        have h_c2 := stepsTo_C2 (2 * a1 + 1) 1
        have h_eq : 2 * (2 * a1 + 1) + 2 * 1 + 7 = 4 * a1 + 11 := by omega
        rwa [h_eq] at h_c2
      · simp only [↓reduceIte, Option.map, toState]
        refine CollatzStepsTo.head rfl ?_
        have h_c2 := stepsTo_C2 (2 * a1 + 3) 0
        have h_eq : 2 * (2 * a1 + 3) + 2 * 0 + 7 = 4 * a1 + 13 := by omega
        rwa [h_eq] at h_c2
      · simp only [↓reduceIte, Option.map, toState]
        refine CollatzStepsTo.head rfl ?_
        have h_c2 := stepsTo_C2 (2 * a1 + 5) 0
        have h_eq : 2 * (2 * a1 + 5) + 2 * 0 + 7 = 4 * a1 + 17 := by omega
        rwa [h_eq] at h_c2
      · simp only [Nat.reduceEqDiff, true_or, ↓reduceIte, Option.map]
        exact CollatzStepsTo.of_eq rfl
      · simp only [Nat.reduceEqDiff, or_true, ↓reduceIte, Option.map]
        exact CollatzStepsTo.of_eq rfl
      · simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, Option.map, toState]
        refine CollatzStepsTo.head rfl ?_
        have h_c2 := stepsTo_C2 1 (a1 + 3)
        have h_eq : 2 * 1 + 2 * (a1 + 3) + 7 = 2 * a1 + 15 := by omega
        rwa [h_eq] at h_c2
      · have hne0 : b2 + 6 ≠ 0 := by omega
        have hne1 : b2 + 6 ≠ 1 := by omega
        have hne2 : b2 + 6 ≠ 2 := by omega
        have hne34 : ¬ (b2 + 6 = 3 ∨ b2 + 6 = 4) := by omega
        have hne5 : b2 + 6 ≠ 5 := by omega
        have hsub : b2 + 6 - 6 = b2 := by omega
        simp only [hne0, hne1, hne2, hne34, hne5, ↓reduceIte, hsub]
        exact CollatzStepsTo.head rfl (ih b2 (by omega) (a1 + 4))

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState) (CollatzReachesStar.refl next _) ?_
  rintro ⟨a⟩
  rcases a with _ | _ | a
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
  · exact CollatzStepsTo.head rfl (stepsTo_evalD0 a 1)

/-- `target` halts from the blank tape if and only if `highLevelNext` halts from
`highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- Equivalence between the low-level and high-level Collatz-like accelerations. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE
