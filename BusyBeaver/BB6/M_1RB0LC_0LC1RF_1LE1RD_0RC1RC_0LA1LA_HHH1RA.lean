/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA`

We define the configuration for $p \in \{0, 1\}$ (representing `false` and `true`) and $k, c \ge 0$:

$$
E(p, k, c) := 0^\infty \ 1^{3 + p} \ \mathrm{A}{>} \ 0 \ (11)^k \ 0 \ 1^c \ 0^\infty.
$$

Starting from $E(0, 0, 2)$ (i.e., $0^\infty \ 1^3 \ \mathrm{A}{>} \ 0 \ 0 \ 1^2 \ 0^\infty$,
reached after 23 steps from the blank tape), every return to the $E$-family after draining the
intermediate $k = 1$ / even-$c$ accumulation phases lands back in $a \in \{3, 4\}$
($p \in \{0, 1\}$), following the closed-form map $T$:

$$
T(E(p, k, c)) = \begin{cases}
  E(1 - p,\ 3\lfloor k / 2 \rfloor + 2,\ c)
    & \text{if } c \equiv 1 \pmod 2,\ k \equiv 0 \pmod 2, \\
  \text{Halt}
    & \text{if } c = 1,\ k \equiv 1 \pmod 2, \\
  E(0,\ 0,\ 6\lfloor k / 2 \rfloor + 10 + p)
    & \text{if } c = 3,\ k \equiv 1 \pmod 2, \\
  E(p,\ 3\lfloor k / 2 \rfloor + 5 + p,\ c - 5)
    & \text{if } c \ge 5,\ c \equiv 1 \pmod 2,\ k \equiv 1 \pmod 2, \\
  E(0,\ 0,\ 6k + 5 + p)
    & \text{if } c \equiv 0 \pmod 2,\ c = 2k, \\
  E(0,\ 0,\ 6k + 2 + p)
    & \text{if } c \equiv 0 \pmod 2,\ 2k = c + 2, \\
  E(1 - p,\ 3(c / 2) + 3,\ 2k - c - 3)
    & \text{if } c \equiv 0 \pmod 2,\ 2k \ge c + 4, \\
  E(1 - p,\ 3,\ c - 2)
    & \text{if } c \equiv 0 \pmod 2,\ c \ge 2,\ k = 0, \\
  E(p,\ 3k + 1 + p,\ c - 2k - 1)
    & \text{if } c \equiv 0 \pmod 2,\ c \ge 2k + 2,\ k \ge 1.
\end{cases}
$$

<!-- hardness:begin -->
## Hardness

*Hardness class:* Problem 5 — trigger **EQ (rebound trap)**, growth exponential
($\gamma\approx1.9538$ per era), shield none.

*Verdict (heuristic, from exact accelerated simulation of the certified rules):* probviously
non-halting.

*Hazard:* $P(\text{halt}) \approx 10^{-380.6}$

*Simulated horizon:* $> 3.22\times10^{762}$ TM steps

*Why it is hard:* odd-$c$ Antihydra rounds $k\mapsto\tfrac32 k+2$ ((3/2)^{\nu_2(k+4)} 2-adic bursts,
the expanding dual of Tao's Syracuse step) alternating with even-$c$ subtraction drains; halts iff
$c_j - 2k_j \in \lbrace -4,+2 \rbrace$

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Rightward shift across `(11)^k` in state `C`. -/
private theorem shift_C_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C l (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight C (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C l (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight C (ListBlank.append [1, 1] l)
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward shift of `1^k` across `1 0 C> 0`. -/
private theorem shift_L1 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C
        (ListBlank.append [0] (ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ k) l)))
        (ListBlank.append [0] r))
      (Cfg.headRight C
        (ListBlank.append [0] (ListBlank.append [1] l))
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [0] (ListBlank.append [1]
              (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))))
            (ListBlank.append [0] r))
          (Cfg.headRight C
            (ListBlank.append [0] (ListBlank.append [1]
              (ListBlank.append (([1] : List (Fin 2)) ^ k) l)))
            (ListBlank.append [0] (ListBlank.append [1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Leftward shift of `(11)^k` across `1 C> 0 0`. -/
private theorem shift_L2 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C
        (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
        (ListBlank.append [0, 0] r))
      (Cfg.headRight C
        (ListBlank.append [1] l)
        (ListBlank.append [0, 0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [1] (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)))
            (ListBlank.append [0, 0] r))
          (Cfg.headRight C
            (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [0, 0] (ListBlank.append [1, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] r) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Right-end bounce for `z = 2`. -/
private theorem bounce_z2 (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append [0] (ListBlank.append [1] l))
        (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))
      (Cfg.headRight C
        (ListBlank.append [1] l)
        (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))) := by
  rw [list_pow_succ, list_pow_one]
  bb_steps

/-- Right-end bounce for odd `z = 2 * j + 1`. -/
private theorem bounce_odd (l : ListBlank (Fin 2)) (j : ℕ) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append [0] (ListBlank.append [1] l))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default))
      (Cfg.headRight C
        (ListBlank.append [1] l)
        (ListBlank.append [0, 0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default))))) := by
  have h_split :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ j) (ListBlank.append [1] default) := by
    rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * j) 1, ← one_pow_two_mul, list_pow_one]
  rw [h_split]
  have h1 := shift_C_11 j (ListBlank.append [0] (ListBlank.append [1] l))
    (ListBlank.append [1] default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ j)
            (ListBlank.append [0] (ListBlank.append [1] l)))
          (ListBlank.append [1] default))
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j))
              (ListBlank.append [0] (ListBlank.append [1] l)))))
          (ListBlank.append [0] default)) := by
    rw [one_pow_two_mul]
    bb_steps
  have h12 := h1.trans_plus h2
  have h3 := shift_L1 (2 * j) (ListBlank.append [0] (ListBlank.append [1] l)) default
  have h123 := h12.trans_star h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append [1]
            (ListBlank.append [0] (ListBlank.append [1] l))))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j)) default)))
        (Cfg.headRight C
          (ListBlank.append [1] l)
          (ListBlank.append [0, 0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
            (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ j)
              (ListBlank.append [1] default)))))) := by
    have h_r :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ j) (ListBlank.append [1] default) =
          ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j)) default) := by
      rw [← h_split, Nat.add_comm (2 * j) 1,
        ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * j), list_pow_one]
    rw [h_r, list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h123.trans_star h4.to_star

/-- Right-end bounce for even `z = 2 * j + 4`. -/
private theorem bounce_even4 (l : ListBlank (Fin 2)) (j : ℕ) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append [0] (ListBlank.append [1] l))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 4)) default))
      (Cfg.headRight C
        (ListBlank.append [1] l)
        (ListBlank.append [0, 0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 2)) default))))) := by
  have h_split :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 4)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 1))
          (ListBlank.append (([1] : List (Fin 2)) ^ 2) default) := by
    have h_eq : 2 * j + 4 = 2 * (j + 1) + 2 := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (j + 1)) 2, ← one_pow_two_mul]
  rw [h_split]
  have h1 := shift_C_11 (j + 1) (ListBlank.append [0] (ListBlank.append [1] l))
    (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 1))
            (ListBlank.append [0] (ListBlank.append [1] l)))
          (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))
        (Cfg.headRight C
          (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ j)
            (ListBlank.append [1] (ListBlank.append [0] (ListBlank.append [1] l)))))
          (ListBlank.append [0, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))) := by
    have h_l :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 1))
          (ListBlank.append [0] (ListBlank.append [1] l)) =
          ListBlank.append [1] (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ j)
              (ListBlank.append [0] (ListBlank.append [1] l)))) := by
      rw [ListBlank.append_pow_succ]
      rfl
    have h_l2 :
        ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ j)
          (ListBlank.append [1] (ListBlank.append [0] (ListBlank.append [1] l)))) =
          ListBlank.append [1] (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ j)
              (ListBlank.append [0] (ListBlank.append [1] l)))) := by
      rw [swap_1_11_pow j (ListBlank.append [0] (ListBlank.append [1] l))]
    rw [h_l, h_l2, list_pow_succ, list_pow_one]
    bb_steps
  have h12 := h1.trans_plus h2
  have h3 := shift_L2 j (ListBlank.append [1] (ListBlank.append [0] (ListBlank.append [1] l)))
    (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)
  have h123 := h12.trans_star h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1] (ListBlank.append [1]
            (ListBlank.append [0] (ListBlank.append [1] l))))
          (ListBlank.append [0, 0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ j)
            (ListBlank.append (([1] : List (Fin 2)) ^ 2) default))))
        (Cfg.headRight C
          (ListBlank.append [1] l)
          (ListBlank.append [0, 0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 2)) default))))) := by
    have h_r :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ j)
          (ListBlank.append (([1] : List (Fin 2)) ^ 2) default) =
          ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 2)) default := by
      rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * j) 2, ← one_pow_two_mul]
    rw [h_r, list_pow_one]
    bb_steps
  exact h123.trans_star h4.to_star

/-- Leftward sweep across odd block `(11)^k 1` preceded by `0`. -/
private theorem sweep_L2_odd (a k : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))))
        (ListBlank.append [0, 0] r))
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
        (ListBlank.append [0, 1, 1, 0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))) := by
  have h1 := shift_L2 k
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)) r
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1]
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
          (ListBlank.append [0, 0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r)))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
          (ListBlank.append [0, 1, 1, 0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))) := by
    bb_steps
  exact h1.trans_plus h2

/-- Leftward sweep across even block `(11)^(m + 1)` at left blank boundary. -/
private theorem sweep_L2_even (m : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ m) default))
        (ListBlank.append [0, 0] r))
      (Cfg.headRight A
        (ListBlank.append [1] default)
        (ListBlank.append [0, 1, 1, 0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1)) r))) := by
  have h_l :
      ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ m) (default : ListBlank (Fin 2))) =
        ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [1] default)) := by
    rw [swap_1_11_pow m default]
    rfl
  rw [h_l]
  have h1 := shift_L2 m (ListBlank.append [1] default) r
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1] (ListBlank.append [1] default))
          (ListBlank.append [0, 0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ m) r)))
        (Cfg.headRight A
          (ListBlank.append [1] default)
          (ListBlank.append [0, 1, 1, 0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1)) r))) := by
    rw [ListBlank.append_pow_succ]
    bb_steps
  exact h1.trans_plus h2

/-- Canonical tape pattern
$E(a, k, c) := 0^\infty\,1^a\,\mathrm{A}{>}\,0\,(11)^k\,0\,1^c\,0^\infty$. -/
private abbrev pat_E : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some A
    right := .sym 0 (.rep [1, 1] 1 (.sym 0 (.rep [1] 2 .default))) }

/-- Closed pattern set for `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` (Level A). -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .rep [1] 0 .default
      head := some SixState.A
      right := .sym 0 (.rep [1, 1] 1 (.sym 0 (.rep [1] 2 .default))) }, .true)]

/-- Configuration $E(a, k, c)$. -/
private def cfg_E (a k c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
    (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))

private theorem eval_pat_E (vars : ℕ → ℕ) :
    evalTapePattern pat_E vars = cfg_E (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_E (a k c : ℕ) : IsInPatternSet ps (cfg_E a k c) :=
  ⟨(pat_E, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => k | 2 => c | _ => 0, rfl, trivial⟩

private theorem finish_A_0110 (a m d : ℕ) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
        (ListBlank.append [0, 1, 1, 0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))))
      (cfg_E (a + 3) m d) := by
  unfold cfg_E
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    rw [Nat.add_comm a 3, ListBlank.append_pow_add]
    rfl
  rw [h_l]
  bb_steps

private theorem eq_cfg_E_a_1 (a k d : ℕ) :
    Cfg.headRight A
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
      (ListBlank.append [0, 1, 1, 0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) =
      cfg_E a 1 (2 * k + d) := by
  unfold cfg_E
  rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) d, ← one_pow_two_mul, list_pow_one]
  rfl

private def cfg_M1 (a kp z : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append [0] (ListBlank.append [1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ kp)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))))
    (ListBlank.append (([1] : List (Fin 2)) ^ z) default)

private theorem step_M1_odd (a kp j : ℕ) :
    ReachesPlus target (cfg_M1 a kp (2 * j + 1)) (cfg_E (a + 3) kp (2 * j + 1)) := by
  have h1 := bounce_odd
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ kp)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))) j
  have h2 := sweep_L2_odd a kp
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default)))
  have h12 := h1.trans h2
  simp only [list_pow_zero, ListBlank.append_nil] at h12
  exact h12.trans (finish_A_0110 a kp (2 * j + 1))

private theorem step_M1_z2 (a kp : ℕ) :
    ReachesPlus target (cfg_M1 a kp 2) (cfg_E a 1 (2 * kp + 2)) := by
  have h1 := bounce_z2
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ kp)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
  have h2 := sweep_L2_odd a kp (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)
  have h12 := h1.trans h2
  rwa [eq_cfg_E_a_1 a kp 2] at h12

private theorem step_M1_even4 (a kp j : ℕ) :
    ReachesPlus target (cfg_M1 a kp (2 * j + 4)) (cfg_E (a + 3) (kp + 1) (2 * j + 2)) := by
  unfold cfg_M1
  have h1 := bounce_even4
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ kp)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))) j
  have h2 := sweep_L2_odd a kp
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 2)) default)))
  have h12 := h1.trans h2
  have h_merge :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ kp)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 2)) default))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (kp + 1))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 2)) default)) := by
    rw [← ListBlank.append_pow_add ([1, 1] : List (Fin 2)) kp 1]
  rw [h_merge] at h12
  exact h12.trans (finish_A_0110 a (kp + 1) (2 * j + 2))

private theorem step_M1 (a kp d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_M1 a kp (d + 1)) cfg' ∧ IsInPatternSet ps cfg' := by
  rcases nat_even_or_odd_two_mul d with ⟨j, rfl⟩ | ⟨m, rfl⟩
  · exact ⟨cfg_E (a + 3) kp (2 * j + 1), step_M1_odd a kp j, in_ps_E (a + 3) kp (2 * j + 1)⟩
  · rcases m with _ | j
    · exact ⟨cfg_E a 1 (2 * kp + 2), step_M1_z2 a kp, in_ps_E a 1 (2 * kp + 2)⟩
    · have h_eq : 2 * (j + 1) + 1 + 1 = 2 * j + 4 := by omega
      rw [h_eq]
      exact ⟨cfg_E (a + 3) (kp + 1) (2 * j + 2), step_M1_even4 a kp j,
        in_ps_E (a + 3) (kp + 1) (2 * j + 2)⟩

private def cfg_M0 (n z : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append [0] (ListBlank.append [1]
      (ListBlank.append (([1] : List (Fin 2)) ^ n) default)))
    (ListBlank.append (([1] : List (Fin 2)) ^ z) default)

private theorem cfg_M0_even_eq_M1 (m z : ℕ) :
    cfg_M0 (2 * m) z = cfg_M1 0 m z := by
  unfold cfg_M0 cfg_M1
  have h0 :
      ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ 0) (default : ListBlank (Fin 2))) = default := by
    simp
  rw [h0, one_pow_two_mul]

private theorem step_M0_z0 (n : ℕ) :
    ReachesPlus target (cfg_M0 n 0) (cfg_E 3 0 (n + 2)) := by
  have h1 :
      ReachesStar target
        (cfg_M0 n 0)
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append [1] default))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ n) default))) := by
    unfold cfg_M0
    have h_def :
        ListBlank.append (([1] : List (Fin 2)) ^ 0) (default : ListBlank (Fin 2)) =
          ListBlank.append [0] default := by
      simp
    rw [h_def]
    exact shift_L1 n default default
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append [1] default))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ n) default)))
        (cfg_E 3 0 (n + 2)) := by
    unfold cfg_E
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (n + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ n) default) := by
      rw [Nat.add_comm n 2, ListBlank.append_pow_add]
      rfl
    have h_l : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [h_r, h_l, list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h1.trans_plus h2

private theorem step_M0_odd_odd (m j : ℕ) :
    ReachesPlus target (cfg_M0 (2 * m + 1) (2 * j + 1)) (cfg_E 4 (m + 1) (2 * j + 1)) := by
  have h_l_odd :
      ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 1))
          (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ m) default) := by
    rw [Nat.add_comm (2 * m) 1, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * m),
      ← one_pow_two_mul, list_pow_one]
    rfl
  unfold cfg_M0
  rw [h_l_odd]
  have h1 := bounce_odd (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 1)) default) j
  rw [h_l_odd] at h1
  have h2 := sweep_L2_even m
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 1)) default)))
  have h12 := h1.trans h2
  simp only [list_pow_zero, ListBlank.append_nil] at h12
  have h_def1 :
      ListBlank.append [1] (default : ListBlank (Fin 2)) =
        ListBlank.append (([1] : List (Fin 2)) ^ 1) default := by
    rw [list_pow_one]
  rw [h_def1] at h12
  exact h12.trans (finish_A_0110 1 (m + 1) (2 * j + 1))

private theorem step_M0_odd_z2 (m : ℕ) :
    ReachesPlus target (cfg_M0 (2 * m + 1) 2) (cfg_E 1 1 (2 * (m + 1) + 2)) := by
  have h_l_odd :
      ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 1))
          (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ m) default) := by
    rw [Nat.add_comm (2 * m) 1, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * m),
      ← one_pow_two_mul, list_pow_one]
    rfl
  unfold cfg_M0
  rw [h_l_odd]
  have h1 := bounce_z2 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 1)) default)
  rw [h_l_odd] at h1
  have h2 := sweep_L2_even m (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)
  have h12 := h1.trans h2
  have h_def1 :
      ListBlank.append [1] (default : ListBlank (Fin 2)) =
        ListBlank.append (([1] : List (Fin 2)) ^ 1) default := by
    rw [list_pow_one]
  rwa [h_def1, eq_cfg_E_a_1 1 (m + 1) 2] at h12

private theorem step_M0_odd_even4 (m j : ℕ) :
    ReachesPlus target (cfg_M0 (2 * m + 1) (2 * j + 4)) (cfg_E 4 (m + 2) (2 * j + 2)) := by
  have h_l_odd :
      ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 1))
          (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ m) default) := by
    rw [Nat.add_comm (2 * m) 1, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * m),
      ← one_pow_two_mul, list_pow_one]
    rfl
  unfold cfg_M0
  rw [h_l_odd]
  have h1 := bounce_even4
    (ListBlank.append (([1] : List (Fin 2)) ^ (2 * m + 1)) default) j
  rw [h_l_odd] at h1
  have h2 := sweep_L2_even m
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 2)) default)))
  have h12 := h1.trans h2
  have h_merge :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1))
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 2)) default))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 2))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 2)) default)) := by
    rw [← ListBlank.append_pow_add ([1, 1] : List (Fin 2)) (m + 1) 1]
  have h_def1 :
      ListBlank.append [1] (default : ListBlank (Fin 2)) =
        ListBlank.append (([1] : List (Fin 2)) ^ 1) default := by
    rw [list_pow_one]
  rw [h_merge, h_def1] at h12
  exact h12.trans (finish_A_0110 1 (m + 2) (2 * j + 2))

private theorem step_M0 (n z : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_M0 n z) cfg' ∧ IsInPatternSet ps cfg' := by
  rcases z with _ | d
  · exact ⟨cfg_E 3 0 (n + 2), step_M0_z0 n, in_ps_E 3 0 (n + 2)⟩
  · rcases nat_even_or_odd_two_mul n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [cfg_M0_even_eq_M1 m (d + 1)]
      exact step_M1 0 m d
    · rcases nat_even_or_odd_two_mul d with ⟨j, rfl⟩ | ⟨m', rfl⟩
      · exact ⟨cfg_E 4 (m + 1) (2 * j + 1), step_M0_odd_odd m j, in_ps_E 4 (m + 1) (2 * j + 1)⟩
      · rcases m' with _ | j
        · exact ⟨cfg_E 1 1 (2 * (m + 1) + 2), step_M0_odd_z2 m,
            in_ps_E 1 1 (2 * (m + 1) + 2)⟩
        · have h_eq : 2 * (j + 1) + 1 + 1 = 2 * j + 4 := by omega
          rw [h_eq]
          exact ⟨cfg_E 4 (m + 2) (2 * j + 2), step_M0_odd_even4 m j,
            in_ps_E 4 (m + 2) (2 * j + 2)⟩

private theorem step_E_k0 (a c : ℕ) :
    ReachesPlus target (cfg_E a 0 c) (cfg_M0 a c) := by
  unfold cfg_E cfg_M0
  rw [list_pow_zero, ListBlank.append_nil]
  bb_steps

private theorem step_E_k1_even (a m : ℕ) :
    ReachesPlus target (cfg_E a 1 (2 * m)) (cfg_E (a + 3) m 0) := by
  have h_eq :
      cfg_E a 1 (2 * m) =
        Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
          (ListBlank.append [0, 1, 1, 0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ m)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)))) := by
    unfold cfg_E
    rw [← one_pow_two_mul]
    simp
  rw [h_eq]
  exact finish_A_0110 a m 0

private theorem step_E_k1_c1 (a : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_E a 1 1) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F (ListBlank.append (([1] : List (Fin 2)) ^ (a + 5)) default) default,
    ?_, rfl⟩
  unfold cfg_E
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (a + 5)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    rw [Nat.add_comm a 5, ListBlank.append_pow_add]
    rfl
  rw [h_l, list_pow_one]
  bb_steps

private theorem step_E_k1_odd3 (a j : ℕ) :
    ReachesPlus target (cfg_E a 1 (2 * j + 3)) (cfg_M0 (a + 5) (2 * j)) := by
  unfold cfg_E cfg_M0
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (a + 5)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    rw [Nat.add_comm a 5, ListBlank.append_pow_add]
    rfl
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j)) default) := by
    rw [Nat.add_comm (2 * j) 3, ListBlank.append_pow_add]
    rfl
  rw [h_l, h_r, list_pow_one]
  bb_steps

private theorem step_E_k2_c0 (a kp : ℕ) :
    ReachesPlus target (cfg_E a (kp + 2) 0) (cfg_M0 (a + 2) (2 * kp + 1)) := by
  unfold cfg_E cfg_M0
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    rw [Nat.add_comm a 2, ListBlank.append_pow_add]
    rfl
  have h_r1 :
      (([1, 1] : List (Fin 2)) ^ (kp + 2)) =
        ([1, 1, 1, 1] : List (Fin 2)) ++ ([1] : List (Fin 2)) ^ (2 * kp) := by
    rw [Nat.add_comm kp 2, list_pow_add, one_pow_two_mul kp]
    rfl
  have h_r2 :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * kp + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * kp)) default) := by
    rw [Nat.add_comm (2 * kp) 1, ListBlank.append_pow_add, list_pow_one]
  rw [h_l, h_r1, ListBlank.append_assoc, h_r2, list_pow_zero, ListBlank.append_nil]
  bb_steps

private theorem step_E_k2_succ (a kp d : ℕ) :
    ReachesPlus target (cfg_E a (kp + 2) (d + 1)) (cfg_M1 (a + 3) kp (d + 1)) := by
  have h1 :
      ReachesPlus target
        (cfg_E a (kp + 2) (d + 1))
        (Cfg.headRight C
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ kp)
            (ListBlank.append [1, 0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)))) := by
    unfold cfg_E
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
      rw [Nat.add_comm a 3, ListBlank.append_pow_add]
      rfl
    have h_r :
        (([1, 1] : List (Fin 2)) ^ (kp + 2)) =
          ([1, 1, 1] : List (Fin 2)) ++ (([1, 1] : List (Fin 2)) ^ kp ++ [1]) := by
      have h_eq : ([1, 1] : List (Fin 2)) ^ kp ++ [1] = [1] ++ ([1, 1] : List (Fin 2)) ^ kp := by
        induction kp with
        | zero => rfl
        | succ k ih => rw [list_pow_succ, List.append_assoc, ih, ← List.append_assoc]; rfl
      rw [h_eq, ← List.append_assoc, Nat.add_comm kp 2, list_pow_add]
      rfl
    rw [h_l, h_r, ListBlank.append_assoc, ListBlank.append_assoc]
    bb_steps
  have h2 := shift_C_11 kp
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))
    (ListBlank.append [1, 0] (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ kp)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
          (ListBlank.append [1, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)))
        (cfg_M1 (a + 3) kp (d + 1)) := by
    unfold cfg_M1
    bb_steps
  exact h12.trans h3

private theorem step_E (a k c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_E a k c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases k with _ | _ | kp
  · obtain ⟨cfg', h_step, h_in⟩ := step_M0 a c
    exact ⟨cfg', (step_E_k0 a c).trans h_step, Or.inl h_in⟩
  · rcases nat_even_or_odd_two_mul c with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨cfg_E (a + 3) m 0, step_E_k1_even a m, Or.inl (in_ps_E (a + 3) m 0)⟩
    · rcases m with _ | j
      · obtain ⟨cfg', h_step, h_halt⟩ := step_E_k1_c1 a
        exact ⟨cfg', h_step, Or.inr h_halt⟩
      · have h_eq : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
        rw [h_eq]
        obtain ⟨cfg', h_step, h_in⟩ := step_M0 (a + 5) (2 * j)
        exact ⟨cfg', (step_E_k1_odd3 a j).trans h_step, Or.inl h_in⟩
  · rcases c with _ | d
    · obtain ⟨cfg', h_step, h_in⟩ := step_M0 (a + 2) (2 * kp + 1)
      exact ⟨cfg', (step_E_k2_c0 a kp).trans h_step, Or.inl h_in⟩
    · obtain ⟨cfg', h_step, h_in⟩ := step_M1 (a + 3) kp d
      exact ⟨cfg', (step_E_k2_succ a kp d).trans h_step, Or.inl h_in⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_E 3 0 2) := by
  have h_init : ReachesPlus target (init []) (cfg_E 3 0 2) := by
    unfold cfg_E
    have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [h3, h2, list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_E 3 0 2, init_reaches_start, in_ps_E 3 0 2⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  exact step_E (vars 0) (vars 1) (vars 2)

/-- `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B, Box 1) -/

/-- Symbolic configuration state space for `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA`. -/
inductive State where
  /-- $E(a, k, c) := 0^\infty\,1^a\,\mathrm{A}{>}\,0\,(11)^k\,0\,1^c\,0^\infty$. -/
  | E (a k c : ℕ)
  /-- $M_1(a, k, d+1) := 0^\infty\,1^a\,0\,(11)^k\,1\,0\,\mathrm{C}{>}\,1^{d+1}\,0^\infty$. -/
  | M_1 (a k d : ℕ)
  /-- $M_0(n, z) := 0^\infty\,1^n\,1\,0\,\mathrm{C}{>}\,1^z\,0^\infty$. -/
  | M_0 (n z : ℕ)

/-- Initial symbolic state $E(3, 0, 2)$. -/
def start : State := .E 3 0 2

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .E a k c =>
    Cfg.headRight SixState.A
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
      (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))
  | .M_1 a k d =>
    Cfg.headRight SixState.C
      (ListBlank.append [0] (ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))))
      (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
  | .M_0 n z =>
    Cfg.headRight SixState.C
      (ListBlank.append [0] (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ n) default)))
      (ListBlank.append (([1] : List (Fin 2)) ^ z) default)

/-- Accelerated Collatz-like transition function (Box 1). -/
def next : State → Option State
  | .E a 0 c => some (.M_0 a c)
  | .E a 1 c =>
    if c % 2 = 0 then some (.E (a + 3) (c / 2) 0)
    else if c = 1 then none
    else some (.M_0 (a + 5) (c - 3))
  | .E a (k + 2) 0 => some (.M_0 (a + 2) (2 * k + 1))
  | .E a (k + 2) (d + 1) => some (.M_1 (a + 3) k d)
  | .M_1 a k d =>
    if d % 2 = 0 then some (.E (a + 3) k (d + 1))
    else if d = 1 then some (.E a 1 (2 * k + 2))
    else some (.E (a + 3) (k + 1) (d - 1))
  | .M_0 n 0 => some (.E 3 0 (n + 2))
  | .M_0 n (d + 1) =>
    if d % 2 = 0 then
      if n % 2 = 0 then some (.E 3 (n / 2) (d + 1))
      else some (.E 4 (n / 2 + 1) (d + 1))
    else if d = 1 then
      if n % 2 = 0 then some (.E 0 1 (n + 2))
      else some (.E 1 1 (n + 3))
    else
      if n % 2 = 0 then some (.E 3 (n / 2 + 1) (d - 1))
      else some (.E 4 (n / 2 + 2) (d - 1))

private theorem encode_E (a k c : ℕ) : encode (.E a k c) = cfg_E a k c := rfl
private theorem encode_M1 (a k d : ℕ) : encode (.M_1 a k d) = cfg_M1 a k (d + 1) := rfl
private theorem encode_M0 (n z : ℕ) : encode (.M_0 n z) = cfg_M0 n z := rfl

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro (⟨a, k, c⟩ | ⟨a, k, d⟩ | ⟨n, z⟩) s' hnext
    · rcases k with _ | _ | k
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_E_k0 a c
      · rcases nat_even_or_odd_two_mul c with ⟨m, rfl⟩ | ⟨m, rfl⟩
        · have hmod : (2 * m) % 2 = 0 := by omega
          have hdiv : (2 * m) / 2 = m := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          exact step_E_k1_even a m
        · rcases m with _ | j
          · simp [next] at hnext
          · have hmod : (2 * (j + 1) + 1) % 2 ≠ 0 := by omega
            have hne1 : 2 * (j + 1) + 1 ≠ 1 := by omega
            have hsub : 2 * (j + 1) + 1 - 3 = 2 * j := by omega
            have h_eq : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
            simp only [next, hmod, ↓reduceIte, hne1, hsub, Option.some.injEq] at hnext
            subst hnext
            rw [encode_E, h_eq]
            exact step_E_k1_odd3 a j
      · rcases c with _ | d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_E_k2_c0 a k
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_E_k2_succ a k d
    · rcases nat_even_or_odd_two_mul d with ⟨j, rfl⟩ | ⟨m, rfl⟩
      · have hmod : (2 * j) % 2 = 0 := by omega
        simp only [next, hmod, ↓reduceIte, Option.some.injEq] at hnext
        subst hnext
        exact step_M1_odd a k j
      · rcases m with _ | j
        · change next (.M_1 a k 1) = some s' at hnext
          simp only [next, Nat.reduceMod, Nat.one_ne_zero, ↓reduceIte, Option.some.injEq] at hnext
          subst hnext
          exact step_M1_z2 a k
        · have hmod : (2 * (j + 1) + 1) % 2 ≠ 0 := by omega
          have hne1 : 2 * (j + 1) + 1 ≠ 1 := by omega
          have hsub : 2 * (j + 1) + 1 - 1 = 2 * j + 2 := by omega
          have h_eq : 2 * (j + 1) + 1 + 1 = 2 * j + 4 := by omega
          simp only [next, hmod, ↓reduceIte, hne1, hsub, Option.some.injEq] at hnext
          subst hnext
          rw [encode_M1, h_eq]
          exact step_M1_even4 a k j
    · rcases z with _ | d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_M0_z0 n
      · rcases nat_even_or_odd_two_mul n with ⟨m, rfl⟩ | ⟨m, rfl⟩
        · have hnmod : (2 * m) % 2 = 0 := by omega
          have hndiv : (2 * m) / 2 = m := by omega
          rcases nat_even_or_odd_two_mul d with ⟨j, rfl⟩ | ⟨m', rfl⟩
          · have hdmod : (2 * j) % 2 = 0 := by omega
            simp only [next, hdmod, ↓reduceIte, hnmod, hndiv, Option.some.injEq] at hnext
            subst hnext
            rw [encode_M0, cfg_M0_even_eq_M1]
            exact step_M1_odd 0 m j
          · rcases m' with _ | j
            · change next (.M_0 (2 * m) 2) = some s' at hnext
              simp only [next, Nat.reduceMod, Nat.one_ne_zero, ↓reduceIte, hnmod,
                Option.some.injEq] at hnext
              subst hnext
              rw [encode_M0, cfg_M0_even_eq_M1]
              exact step_M1_z2 0 m
            · have hdmod : (2 * (j + 1) + 1) % 2 ≠ 0 := by omega
              have hdne1 : 2 * (j + 1) + 1 ≠ 1 := by omega
              have hdsub : 2 * (j + 1) + 1 - 1 = 2 * j + 2 := by omega
              have h_eq : 2 * (j + 1) + 1 + 1 = 2 * j + 4 := by omega
              simp only [next, hdmod, ↓reduceIte, hdne1, hnmod, hndiv, hdsub,
                Option.some.injEq] at hnext
              subst hnext
              rw [encode_M0, cfg_M0_even_eq_M1, h_eq]
              exact step_M1_even4 0 m j
        · have hnmod : (2 * m + 1) % 2 ≠ 0 := by omega
          have hndiv : (2 * m + 1) / 2 = m := by omega
          rcases nat_even_or_odd_two_mul d with ⟨j, rfl⟩ | ⟨m', rfl⟩
          · have hdmod : (2 * j) % 2 = 0 := by omega
            simp only [next, hdmod, ↓reduceIte, hnmod, hndiv, Option.some.injEq] at hnext
            subst hnext
            exact step_M0_odd_odd m j
          · rcases m' with _ | j
            · have h_add : 2 * m + 1 + 3 = 2 * (m + 1) + 2 := by omega
              change next (.M_0 (2 * m + 1) 2) = some s' at hnext
              simp only [next, Nat.reduceMod, Nat.one_ne_zero, ↓reduceIte, hnmod, h_add,
                Option.some.injEq] at hnext
              subst hnext
              exact step_M0_odd_z2 m
            · have hdmod : (2 * (j + 1) + 1) % 2 ≠ 0 := by omega
              have hdne1 : 2 * (j + 1) + 1 ≠ 1 := by omega
              have hdsub : 2 * (j + 1) + 1 - 1 = 2 * j + 2 := by omega
              have h_eq : 2 * (j + 1) + 1 + 1 = 2 * j + 4 := by omega
              simp only [next, hdmod, ↓reduceIte, hdne1, hnmod, hndiv, hdsub,
                Option.some.injEq] at hnext
              subst hnext
              rw [encode_M0, h_eq]
              exact step_M0_odd_even4 m j
  step_none := by
    rintro (⟨a, k, c⟩ | ⟨a, k, d⟩ | ⟨n, z⟩) hnext
    · rcases k with _ | _ | k
      · simp [next] at hnext
      · simp only [next] at hnext
        split_ifs at hnext with h1 h2
        subst h2
        obtain ⟨cfg', h_plus, h_halt⟩ := step_E_k1_c1 a
        exact ⟨cfg', h_plus.to_star, h_halt⟩
      · rcases c with _ | d <;> simp [next] at hnext
    · simp only [next] at hnext
      split_ifs at hnext
    · rcases z with _ | d
      · simp [next] at hnext
      · simp only [next] at hnext
        split_ifs at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-Like Acceleration -/

private inductive PrevState where
  | E (a k c : ℕ)

private def prevStart : PrevState := .E 3 0 2

private def prevToState : PrevState → State
  | .E a k c => .E a k c

private def prevEncode (s : PrevState) : Cfg (Fin 2) (Fin 6) :=
  encode (prevToState s)

private def prevNext : PrevState → Option PrevState
  | .E a 0 0 => some (.E 3 0 (a + 2))
  | .E a 0 (d + 1) =>
    if d % 2 = 0 then
      if a % 2 = 0 then some (.E 3 (a / 2) (d + 1))
      else some (.E 4 (a / 2 + 1) (d + 1))
    else if d = 1 then
      if a % 2 = 0 then some (.E 0 1 (a + 2))
      else some (.E 1 1 (a + 3))
    else
      if a % 2 = 0 then some (.E 3 (a / 2 + 1) (d - 1))
      else some (.E 4 (a / 2 + 2) (d - 1))
  | .E a 1 c =>
    if c % 2 = 0 then some (.E (a + 3) (c / 2) 0)
    else if c = 1 then none
    else if c = 3 then some (.E 3 0 (a + 7))
    else if c = 5 then
      if (a + 5) % 2 = 0 then some (.E 0 1 (a + 7))
      else some (.E 1 1 (a + 8))
    else
      if (a + 5) % 2 = 0 then some (.E 3 ((a + 5) / 2 + 1) (c - 5))
      else some (.E 4 ((a + 5) / 2 + 2) (c - 5))
  | .E a (k + 2) 0 =>
    if (a + 2) % 2 = 0 then some (.E 3 ((a + 2) / 2) (2 * k + 1))
    else some (.E 4 ((a + 2) / 2 + 1) (2 * k + 1))
  | .E a (k + 2) (d + 1) =>
    if d % 2 = 0 then some (.E (a + 6 * (k / 2 + 1)) (k % 2) (d + 1))
    else if d = 1 then some (.E (a + 3) 1 (2 * k + 2))
    else
      let m := min (k + 1) (d / 2)
      some (.E (a + 6 * m) (k + 2 - m) (d + 1 - 2 * m))

private theorem reaches_E_even_step (m : ℕ) (a k d : ℕ) (hd : d % 2 = 0) :
    CollatzReachesStar next (.E a (k + 2 * m) (d + 1)) (.E (a + 6 * m) k (d + 1)) := by
  induction m generalizing a with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ m ih =>
    have h1 : next (.E a (k + 2 * (m + 1)) (d + 1)) =
        some (.M_1 (a + 3) (k + 2 * m) d) := by
      have hk : k + 2 * (m + 1) = (k + 2 * m) + 2 := by omega
      rw [hk]
      rfl
    have h2 : next (.M_1 (a + 3) (k + 2 * m) d) =
        some (.E (a + 6) (k + 2 * m) (d + 1)) := by
      simp [next, hd]
    have ih' := ih (a + 6)
    have ha : a + 6 + 6 * m = a + 6 * (m + 1) := by omega
    rw [ha] at ih'
    exact CollatzReachesStar.head h1 (CollatzReachesStar.head h2 ih')

private theorem reaches_E_even_drain (a k d : ℕ) (hd : d % 2 = 0) :
    CollatzStepsTo next (.E a (k + 2) (d + 1))
      (some (.E (a + 6 * (k / 2 + 1)) (k % 2) (d + 1))) := by
  have h1 : next (.E a (k + 2) (d + 1)) = some (.M_1 (a + 3) k d) := rfl
  have h2 : next (.M_1 (a + 3) k d) = some (.E (a + 6) k (d + 1)) := by simp [next, hd]
  have h_star := reaches_E_even_step (k / 2) (a + 6) (k % 2) d hd
  have hk : k % 2 + 2 * (k / 2) = k := by omega
  have ha : a + 6 + 6 * (k / 2) = a + 6 * (k / 2 + 1) := by omega
  rw [hk, ha] at h_star
  exact CollatzReachesPlus.head h1 (CollatzReachesStar.head h2 h_star)

private theorem reaches_E_odd_diag (m : ℕ) (a k d : ℕ) (hd : d % 2 ≠ 0) :
    CollatzReachesStar next (.E a (k + m + 1) (d + 2 * m + 1))
      (.E (a + 6 * m) (k + 1) (d + 1)) := by
  induction m generalizing a with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ m ih =>
    have h1 : next (.E a (k + (m + 1) + 1) (d + 2 * (m + 1) + 1)) =
        some (.M_1 (a + 3) (k + m) (d + 2 * (m + 1))) := by
      have hk : k + (m + 1) + 1 = (k + m) + 2 := by omega
      have hd' : d + 2 * (m + 1) + 1 = (d + 2 * (m + 1)) + 1 := by omega
      rw [hk, hd']
      rfl
    have h2 : next (.M_1 (a + 3) (k + m) (d + 2 * (m + 1))) =
        some (.E (a + 6) (k + m + 1) (d + 2 * m + 1)) := by
      have hmod : d % 2 = 1 := by omega
      have hne1 : d + 2 * (m + 1) ≠ 1 := by omega
      have hsub : d + 2 * (m + 1) - 1 = d + 2 * m + 1 := by omega
      simp [next, hmod, hne1, hsub]
    have ih' := ih (a + 6)
    have ha : a + 6 + 6 * m = a + 6 * (m + 1) := by omega
    rw [ha] at ih'
    exact CollatzReachesStar.head h1 (CollatzReachesStar.head h2 ih')

private theorem reaches_E_odd_drain (a k d : ℕ) (hd : d % 2 ≠ 0) (hd1 : d ≠ 1) :
    CollatzStepsTo next (.E a (k + 2) (d + 1))
      (some (.E (a + 6 * min (k + 1) (d / 2))
        (k + 2 - min (k + 1) (d / 2))
        (d + 1 - 2 * min (k + 1) (d / 2)))) := by
  let m := min (k + 1) (d / 2)
  have hm_pos : 0 < m := by omega
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm_pos)
  have h1 : next (.E a (k + 2) (d + 1)) = some (.M_1 (a + 3) k d) := rfl
  have h2 : next (.M_1 (a + 3) k d) = some (.E (a + 6) (k + 1) (d - 1)) := by
    simp [next, hd, hd1]
  have hd_sub_odd : (d - 2 * m) % 2 ≠ 0 := by omega
  have h_star := reaches_E_odd_diag m' (a + 6) (k + 1 - m) (d - 2 * m) hd_sub_odd
  have hk1 : k + 1 - m + m' + 1 = k + 1 := by omega
  have hd1' : d - 2 * m + 2 * m' + 1 = d - 1 := by omega
  have ha : a + 6 + 6 * m' = a + 6 * m := by omega
  have hk2 : k + 1 - m + 1 = k + 2 - m := by omega
  have hd2 : d - 2 * m + 1 = d + 1 - 2 * m := by omega
  rw [hk1, hd1', ha, hk2, hd2] at h_star
  exact CollatzReachesPlus.head h1 (CollatzReachesStar.head h2 h_star)

private theorem is_valid_prev_acceleration :
    IsValidAcceleration target prevStart prevEncode prevNext := by
  refine is_valid_acceleration.of_collatz (embed := prevToState)
    (CollatzReachesStar.refl next start) ?_
  rintro ⟨a, k, c⟩
  rcases k with _ | _ | k
  · rcases c with _ | d
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · dsimp [prevNext]
      split_ifs <;>
        exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq (by simp [next, prevToState, *]))
  · by_cases hc2 : c % 2 = 0
    · simp only [prevNext, hc2, ↓reduceIte]
      exact CollatzStepsTo.of_eq (by simp [next, prevToState, hc2])
    · by_cases hc1 : c = 1
      · subst hc1
        exact CollatzStepsTo.of_eq rfl
      · by_cases hc3 : c = 3
        · subst hc3
          exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
        · by_cases hc5 : c = 5
          · subst hc5
            dsimp [prevNext]
            split_ifs with ha
            · exact CollatzStepsTo.head rfl
                (CollatzStepsTo.of_eq (by simp [next, prevToState, ha]))
            · exact CollatzStepsTo.head rfl
                (CollatzStepsTo.of_eq (by simp [next, prevToState, ha]))
          · have h_sub : c - 3 = (c - 4) + 1 := by omega
            have h_mod : (c - 4) % 2 ≠ 0 := by omega
            have h_ne1 : c - 4 ≠ 1 := by omega
            have h_sub2 : c - 4 - 1 = c - 5 := by omega
            have h_step1 : next (.E a 1 c) = some (.M_0 (a + 5) ((c - 4) + 1)) := by
              simp [next, hc2, hc1, h_sub]
            simp only [prevNext, hc2, hc1, hc3, hc5, ↓reduceIte]
            split_ifs with ha
            · exact CollatzStepsTo.head h_step1
                (CollatzStepsTo.of_eq (by simp [next, prevToState, h_mod, h_ne1, ha, h_sub2]))
            · exact CollatzStepsTo.head h_step1
                (CollatzStepsTo.of_eq (by simp [next, prevToState, h_mod, h_ne1, ha, h_sub2]))
  · rcases c with _ | d
    · have hd_mod : (2 * k) % 2 = 0 := by omega
      have h_step1 : next (.E a (k + 2) 0) = some (.M_0 (a + 2) (2 * k + 1)) := rfl
      dsimp [prevNext]
      split_ifs with ha
      · have ha' : a % 2 = 0 := by omega
        exact CollatzStepsTo.head h_step1
          (CollatzStepsTo.of_eq (by simp [next, prevToState, hd_mod, ha']))
      · have ha' : a % 2 ≠ 0 := by omega
        exact CollatzStepsTo.head h_step1
          (CollatzStepsTo.of_eq (by simp [next, prevToState, hd_mod, ha']))
    · by_cases hd : d % 2 = 0
      · have h_eq : Option.map prevToState (prevNext (.E a (k + 2) (d + 1))) =
            some (.E (a + 6 * (k / 2 + 1)) (k % 2) (d + 1)) := by
          dsimp [prevNext]; split_ifs; rfl
        rw [h_eq]
        exact reaches_E_even_drain a k d hd
      · by_cases hd1 : d = 1
        · subst hd1
          exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
        · have h_eq : Option.map prevToState (prevNext (.E a (k + 2) (d + 1))) =
              some (.E (a + 6 * min (k + 1) (d / 2))
                (k + 2 - min (k + 1) (d / 2))
                (d + 1 - 2 * min (k + 1) (d / 2))) := by
            dsimp [prevNext]; split_ifs; rfl
          rw [h_eq]
          exact reaches_E_odd_drain a k d hd hd1

/-- Reduced high-level symbolic configuration state space for
`1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA`, restricting $a$ to $\{3, 4\}$ via `p : Bool`. -/
inductive HighLevelState where
  /-- $E(p, k, c) := 0^\infty\,1^{3 + p}\,\mathrm{A}{>}\,0\,(11)^k\,0\,1^c\,0^\infty$ where
  `p = false` encodes $a = 3$ and `p = true` encodes $a = 4$. -/
  | E (p : Bool) (k c : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $E(\mathrm{false}, 0, 2) = E(3, 0, 2)$. -/
def highLevelStart : HighLevelState := .E false 0 2

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .E p k c => .E (if p then 4 else 3) k c

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Closed-form high-level accelerated transition function on $E(p, k, c)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .E p k c =>
    if c % 2 = 1 then
      if k % 2 = 0 then some (.E (!p) (3 * (k / 2) + 2) c)
      else if c = 1 then none
      else if c = 3 then some (.E false 0 (6 * (k / 2) + (if p then 11 else 10)))
      else some (.E p (3 * (k / 2) + (if p then 6 else 5)) (c - 5))
    else if c = 2 * k then
      some (.E false 0 (6 * k + (if p then 6 else 5)))
    else if 2 * k = c + 2 then
      some (.E false 0 (6 * k + (if p then 3 else 2)))
    else if 2 * k ≥ c + 4 then
      some (.E (!p) (3 * (c / 2) + 3) (2 * k - c - 3))
    else if k = 0 then
      some (.E (!p) 3 (c - 2))
    else
      some (.E p (3 * k + (if p then 2 else 1)) (c - 2 * k - 1))

private def toPrev : HighLevelState → PrevState
  | .E p k c => .E (if p then 4 else 3) k c

local macro "some_E_omega" : tactic =>
  `(tactic| (rw [Option.some.injEq, PrevState.E.injEq]; refine ⟨by omega, by omega, by omega⟩))

local macro "prev_eq" : tactic =>
  `(tactic|
    (simp only [prevNext]; split_ifs <;> first | rfl | contradiction | omega | some_E_omega))

local macro "hl_eq" : tactic =>
  `(tactic| (unfold highLevelNext; split_ifs <;>
    first | rfl | contradiction | omega | (dsimp only [Option.map, toPrev, Bool.not]; split_ifs <;>
      first | rfl | contradiction | some_E_omega)))

private theorem stepsTo_odd_c (p : Bool) (k c : ℕ) (hc_odd : c % 2 = 1) :
    CollatzStepsTo prevNext (toPrev (.E p k c)) ((highLevelNext (.E p k c)).map toPrev) := by
  have hc_pos : c = (c - 1) + 1 := by omega
  by_cases hk_even : k % 2 = 0
  · have hrhs : ((highLevelNext (.E p k c)).map toPrev) =
        some (.E (if !p then 4 else 3) (3 * (k / 2) + 2) c) := by cases p <;> hl_eq
    rw [hrhs]
    rcases k with _ | _ | kp
    · rw [hc_pos]
      cases p <;> (dsimp only [toPrev, Bool.not]; exact CollatzStepsTo.of_eq (by prev_eq))
    · omega
    · rw [hc_pos]
      cases p <;> dsimp only [toPrev, Bool.not]
      · have s1 : prevNext (.E 3 (kp + 2) ((c - 1) + 1)) =
            some (.E (3 + 6 * (kp / 2 + 1)) 0 ((c - 1) + 1)) := by prev_eq
        exact CollatzStepsTo.head s1 (CollatzStepsTo.of_eq (by prev_eq))
      · have s1 : prevNext (.E 4 (kp + 2) ((c - 1) + 1)) =
            some (.E (4 + 6 * (kp / 2 + 1)) 0 ((c - 1) + 1)) := by prev_eq
        exact CollatzStepsTo.head s1 (CollatzStepsTo.of_eq (by prev_eq))
  · have h1 : ∀ (a0 q : ℕ),
        (a0 = 3 ∧ p = false ∨ a0 = 4 ∧ p = true) →
        CollatzStepsTo prevNext (.E (a0 + 6 * q) 1 c)
          (if c = 1 then none
           else if c = 3 then some (.E 3 0 (6 * q + (if p then 11 else 10)))
           else some (.E a0 (3 * q + (if p then 6 else 5)) (c - 5))) := by
      rintro a0 q (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · by_cases hc1 : c = 1
        · subst hc1; exact CollatzStepsTo.of_eq rfl
        · by_cases hc3 : c = 3
          · subst hc3
            rw [show (if 3 = 1 then none else if 3 = 3 then _ else _) =
              some (PrevState.E 3 0 (6 * q + 10)) by rfl]
            exact CollatzStepsTo.of_eq (by prev_eq)
          · have hr : (if c = 1 then none
                else if c = 3 then some (PrevState.E 3 0 (6 * q + (if false then 11 else 10)))
                else some (PrevState.E 3 (3 * q + (if false then 6 else 5)) (c - 5))) =
                some (.E 3 (3 * q + 5) (c - 5)) := by
              split_ifs <;> first | rfl | contradiction
            rw [hr]
            by_cases hc5 : c = 5
            · subst hc5
              have s1 : prevNext (.E (3 + 6 * q) 1 5) = some (.E 0 1 (10 + 6 * q)) := by prev_eq
              exact CollatzStepsTo.head s1 (CollatzStepsTo.of_eq (by prev_eq))
            · exact CollatzStepsTo.of_eq (by prev_eq)
      · by_cases hc1 : c = 1
        · subst hc1; exact CollatzStepsTo.of_eq rfl
        · by_cases hc3 : c = 3
          · subst hc3
            rw [show (if 3 = 1 then none else if 3 = 3 then _ else _) =
              some (PrevState.E 3 0 (6 * q + 11)) by rfl]
            exact CollatzStepsTo.of_eq (by prev_eq)
          · have hr : (if c = 1 then none
                else if c = 3 then some (PrevState.E 3 0 (6 * q + (if true then 11 else 10)))
                else some (PrevState.E 4 (3 * q + (if true then 6 else 5)) (c - 5))) =
                some (.E 4 (3 * q + 6) (c - 5)) := by
              split_ifs <;> first | rfl | contradiction
            rw [hr]
            by_cases hc5 : c = 5
            · subst hc5
              have s1 : prevNext (.E (4 + 6 * q) 1 5) = some (.E 1 1 (12 + 6 * q)) := by prev_eq
              exact CollatzStepsTo.head s1 (CollatzStepsTo.of_eq (by prev_eq))
            · exact CollatzStepsTo.of_eq (by prev_eq)
    have hrhs : ((highLevelNext (.E p k c)).map toPrev) =
        (if c = 1 then none
         else if c = 3 then some (.E 3 0 (6 * (k / 2) + (if p then 11 else 10)))
         else some (.E (if p then 4 else 3) (3 * (k / 2) + (if p then 6 else 5)) (c - 5))) := by
      cases p <;> hl_eq
    rw [hrhs]
    rcases k with _ | _ | kp
    · omega
    · have h0 : (if p then 4 else 3) = (if p then 4 else 3) + 6 * (1 / 2) := by omega
      dsimp only [toPrev]
      rw [h0]
      exact h1 (if p then 4 else 3) (1 / 2) (by cases p <;> simp)
    · have s1 : prevNext (.E (if p then 4 else 3) (kp + 2) ((c - 1) + 1)) =
          some (.E ((if p then 4 else 3) + 6 * ((kp + 2) / 2)) 1 ((c - 1) + 1)) := by
        cases p <;> prev_eq
      rw [← hc_pos] at s1
      exact CollatzStepsTo.head s1
        (h1 (if p then 4 else 3) ((kp + 2) / 2) (by cases p <;> simp))

private theorem stepsTo_even_near (p : Bool) (k c : ℕ) (hc_odd : ¬c % 2 = 1)
    (hnear : c = 2 * k ∨ 2 * k = c + 2) :
    CollatzStepsTo prevNext (toPrev (.E p k c)) ((highLevelNext (.E p k c)).map toPrev) := by
  by_cases hc_eq_2k : c = 2 * k
  · have hrhs : ((highLevelNext (.E p k c)).map toPrev) =
        some (.E 3 0 (6 * k + (if p then 6 else 5))) := by cases p <;> hl_eq
    rw [hrhs]
    subst hc_eq_2k
    rcases k with _ | _ | kp
    · cases p <;> exact CollatzStepsTo.of_eq rfl
    · cases p <;>
        exact CollatzStepsTo.head rfl (CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl))
    · cases p <;> dsimp only [toPrev]
      · have s1 : prevNext (.E 3 (kp + 2) ((2 * kp + 3) + 1)) =
            some (.E (3 + 6 * (kp + 1)) 1 2) := by prev_eq
        rw [show (2 * kp + 3) + 1 = 2 * (kp + 2) by omega] at s1
        have s2 : prevNext (.E (3 + 6 * (kp + 1)) 1 2) =
            some (.E (6 + 6 * (kp + 1)) 1 0) := by prev_eq
        have s3 : prevNext (.E (6 + 6 * (kp + 1)) 1 0) =
            some (.E (9 + 6 * (kp + 1)) 0 0) := by prev_eq
        exact CollatzStepsTo.head s1 (CollatzStepsTo.head s2
          (CollatzStepsTo.head s3 (CollatzStepsTo.of_eq (by prev_eq))))
      · have s1 : prevNext (.E 4 (kp + 2) ((2 * kp + 3) + 1)) =
            some (.E (4 + 6 * (kp + 1)) 1 2) := by prev_eq
        rw [show (2 * kp + 3) + 1 = 2 * (kp + 2) by omega] at s1
        have s2 : prevNext (.E (4 + 6 * (kp + 1)) 1 2) =
            some (.E (7 + 6 * (kp + 1)) 1 0) := by prev_eq
        have s3 : prevNext (.E (7 + 6 * (kp + 1)) 1 0) =
            some (.E (10 + 6 * (kp + 1)) 0 0) := by prev_eq
        exact CollatzStepsTo.head s1 (CollatzStepsTo.head s2
          (CollatzStepsTo.head s3 (CollatzStepsTo.of_eq (by prev_eq))))
  · have h2k_eq_c2 : 2 * k = c + 2 := by omega
    have hrhs : ((highLevelNext (.E p k c)).map toPrev) =
        some (.E 3 0 (6 * k + (if p then 3 else 2))) := by cases p <;> hl_eq
    rw [hrhs]
    rcases k with _ | _ | _ | kp
    · omega
    · have hc0 : c = 0 := by omega
      subst hc0
      cases p <;> exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · have hc2 : c = 2 := by omega
      subst hc2
      cases p <;> exact CollatzStepsTo.head rfl (CollatzStepsTo.head rfl
        (CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)))
    · have hc_eq : c = (2 * kp + 3) + 1 := by omega
      rw [hc_eq]
      cases p <;> dsimp only [toPrev]
      · have s1 : prevNext (.E 3 (kp + 3) ((2 * kp + 3) + 1)) =
            some (.E (3 + 6 * (kp + 1)) 2 2) := by prev_eq
        have s2 : prevNext (.E (3 + 6 * (kp + 1)) 2 2) =
            some (.E (6 + 6 * (kp + 1)) 1 2) := by prev_eq
        have s3 : prevNext (.E (6 + 6 * (kp + 1)) 1 2) =
            some (.E (9 + 6 * (kp + 1)) 1 0) := by prev_eq
        have s4 : prevNext (.E (9 + 6 * (kp + 1)) 1 0) =
            some (.E (12 + 6 * (kp + 1)) 0 0) := by prev_eq
        exact CollatzStepsTo.head s1 (CollatzStepsTo.head s2
          (CollatzStepsTo.head s3 (CollatzStepsTo.head s4 (CollatzStepsTo.of_eq (by prev_eq)))))
      · have s1 : prevNext (.E 4 (kp + 3) ((2 * kp + 3) + 1)) =
            some (.E (4 + 6 * (kp + 1)) 2 2) := by prev_eq
        have s2 : prevNext (.E (4 + 6 * (kp + 1)) 2 2) =
            some (.E (7 + 6 * (kp + 1)) 1 2) := by prev_eq
        have s3 : prevNext (.E (7 + 6 * (kp + 1)) 1 2) =
            some (.E (10 + 6 * (kp + 1)) 1 0) := by prev_eq
        have s4 : prevNext (.E (10 + 6 * (kp + 1)) 1 0) =
            some (.E (13 + 6 * (kp + 1)) 0 0) := by prev_eq
        exact CollatzStepsTo.head s1 (CollatzStepsTo.head s2
          (CollatzStepsTo.head s3 (CollatzStepsTo.head s4 (CollatzStepsTo.of_eq (by prev_eq)))))

private theorem stepsTo_even_ge (p : Bool) (k c : ℕ) (hc_odd : ¬c % 2 = 1)
    (hc_eq_2k : ¬c = 2 * k) (h2k_eq_c2 : ¬2 * k = c + 2) (h2k_ge : 2 * k ≥ c + 4) :
    CollatzStepsTo prevNext (toPrev (.E p k c)) ((highLevelNext (.E p k c)).map toPrev) := by
  have hrhs : ((highLevelNext (.E p k c)).map toPrev) =
      some (.E (if !p then 4 else 3) (3 * (c / 2) + 3) (2 * k - c - 3)) := by
    cases p <;> hl_eq
  rw [hrhs]
  rcases k with _ | _ | kp
  · omega
  · omega
  · by_cases hc0 : c = 0
    · subst hc0
      cases p <;> (dsimp only [toPrev, Bool.not]; exact CollatzStepsTo.of_eq (by prev_eq))
    · by_cases hc2 : c = 2
      · subst hc2
        cases p <;> dsimp only [toPrev, Bool.not]
        · have s1 : prevNext (.E 3 (kp + 2) 2) = some (.E 6 1 (2 * kp + 2)) := rfl
          have s2 : prevNext (.E 6 1 (2 * kp + 2)) =
              some (.E 9 ((kp - 1) + 2) 0) := by prev_eq
          exact CollatzStepsTo.head s1
            (CollatzStepsTo.head s2 (CollatzStepsTo.of_eq (by prev_eq)))
        · have s1 : prevNext (.E 4 (kp + 2) 2) = some (.E 7 1 (2 * kp + 2)) := rfl
          have s2 : prevNext (.E 7 1 (2 * kp + 2)) =
              some (.E 10 ((kp - 1) + 2) 0) := by prev_eq
          exact CollatzStepsTo.head s1
            (CollatzStepsTo.head s2 (CollatzStepsTo.of_eq (by prev_eq)))
      · have hc_eq : c = (c - 1) + 1 := by omega
        cases p <;> dsimp only [toPrev, Bool.not]
        · have s1 : prevNext (.E 3 (kp + 2) c) =
              some (.E (3 + 6 * (c / 2 - 1)) ((kp + 1 - c / 2) + 2) 2) := by
            rw [hc_eq]; prev_eq
          have s2 : prevNext (.E (3 + 6 * (c / 2 - 1)) ((kp + 1 - c / 2) + 2) 2) =
              some (.E (6 + 6 * (c / 2 - 1)) 1 (2 * (kp + 1 - c / 2) + 2)) := by prev_eq
          have s3 : prevNext (.E (6 + 6 * (c / 2 - 1)) 1 (2 * (kp + 1 - c / 2) + 2)) =
              some (.E (3 + 6 * (c / 2)) ((kp - c / 2) + 2) 0) := by prev_eq
          exact CollatzStepsTo.head s1 (CollatzStepsTo.head s2
            (CollatzStepsTo.head s3 (CollatzStepsTo.of_eq (by prev_eq))))
        · have s1 : prevNext (.E 4 (kp + 2) c) =
              some (.E (4 + 6 * (c / 2 - 1)) ((kp + 1 - c / 2) + 2) 2) := by
            rw [hc_eq]; prev_eq
          have s2 : prevNext (.E (4 + 6 * (c / 2 - 1)) ((kp + 1 - c / 2) + 2) 2) =
              some (.E (7 + 6 * (c / 2 - 1)) 1 (2 * (kp + 1 - c / 2) + 2)) := by prev_eq
          have s3 : prevNext (.E (7 + 6 * (c / 2 - 1)) 1 (2 * (kp + 1 - c / 2) + 2)) =
              some (.E (4 + 6 * (c / 2)) ((kp - c / 2) + 2) 0) := by prev_eq
          exact CollatzStepsTo.head s1 (CollatzStepsTo.head s2
            (CollatzStepsTo.head s3 (CollatzStepsTo.of_eq (by prev_eq))))

private theorem stepsTo_even_lt (p : Bool) (k c : ℕ) (hc_odd : ¬c % 2 = 1)
    (hc_eq_2k : ¬c = 2 * k) (h2k_eq_c2 : ¬2 * k = c + 2) (h2k_ge : ¬2 * k ≥ c + 4) :
    CollatzStepsTo prevNext (toPrev (.E p k c)) ((highLevelNext (.E p k c)).map toPrev) := by
  by_cases hk0 : k = 0
  · have hrhs : ((highLevelNext (.E p k c)).map toPrev) =
        some (.E (if !p then 4 else 3) 3 (c - 2)) := by cases p <;> hl_eq
    rw [hrhs]
    subst hk0
    by_cases hc2 : c = 2
    · subst hc2
      cases p <;> exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · have hc_eq : c = (c - 1) + 1 := by omega
      rw [hc_eq]
      cases p <;> (dsimp only [toPrev, Bool.not]; exact CollatzStepsTo.of_eq (by prev_eq))
  · have hrhs : ((highLevelNext (.E p k c)).map toPrev) =
        some (.E (if p then 4 else 3) (3 * k + (if p then 2 else 1))
          (c - 2 * k - 1)) := by cases p <;> hl_eq
    rw [hrhs]
    rcases k with _ | _ | kp
    · omega
    · cases p <;> dsimp only [toPrev]
      · have s1 : prevNext (.E 3 1 c) = some (.E 6 ((c / 2 - 2) + 2) 0) := by prev_eq
        exact CollatzStepsTo.head s1 (CollatzStepsTo.of_eq (by prev_eq))
      · have s1 : prevNext (.E 4 1 c) = some (.E 7 ((c / 2 - 2) + 2) 0) := by prev_eq
        exact CollatzStepsTo.head s1 (CollatzStepsTo.of_eq (by prev_eq))
    · have hc_eq : c = (c - 1) + 1 := by omega
      rw [hc_eq]
      cases p <;> dsimp only [toPrev]
      · have s1 : prevNext (.E 3 (kp + 2) ((c - 1) + 1)) =
            some (.E (3 + 6 * (kp + 1)) 1 (c - 2 * kp - 2)) := by prev_eq
        have s2 : prevNext (.E (3 + 6 * (kp + 1)) 1 (c - 2 * kp - 2)) =
            some (.E (6 + 6 * (kp + 1)) ((c / 2 - kp - 3) + 2) 0) := by prev_eq
        exact CollatzStepsTo.head s1
          (CollatzStepsTo.head s2 (CollatzStepsTo.of_eq (by prev_eq)))
      · have s1 : prevNext (.E 4 (kp + 2) ((c - 1) + 1)) =
            some (.E (4 + 6 * (kp + 1)) 1 (c - 2 * kp - 2)) := by prev_eq
        have s2 : prevNext (.E (4 + 6 * (kp + 1)) 1 (c - 2 * kp - 2)) =
            some (.E (7 + 6 * (kp + 1)) ((c / 2 - kp - 3) + 2) 0) := by prev_eq
        exact CollatzStepsTo.head s1
          (CollatzStepsTo.head s2 (CollatzStepsTo.of_eq (by prev_eq)))

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  have h_enc : highLevelEncode = fun u => prevEncode (toPrev u) := by
    funext ⟨_, _, _⟩
    rfl
  rw [h_enc]
  refine is_valid_prev_acceleration.of_collatz (embed := toPrev)
    (CollatzReachesStar.refl prevNext prevStart) ?_
  rintro ⟨p, k, c⟩
  by_cases hc_odd : c % 2 = 1
  · exact stepsTo_odd_c p k c hc_odd
  · by_cases hc_eq_2k : c = 2 * k
    · exact stepsTo_even_near p k c hc_odd (Or.inl hc_eq_2k)
    · by_cases h2k_eq_c2 : 2 * k = c + 2
      · exact stepsTo_even_near p k c hc_odd (Or.inr h2k_eq_c2)
      · by_cases h2k_ge : 2 * k ≥ c + 4
        · exact stepsTo_even_ge p k c hc_odd hc_eq_2k h2k_eq_c2 h2k_ge
        · exact stepsTo_even_lt p k c hc_odd hc_eq_2k h2k_eq_c2 h2k_ge

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

end BusyBeaver.M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA
