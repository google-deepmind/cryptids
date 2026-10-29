/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`

We define the configuration for $a \ge 0$, $b \ge 6$:

$$
C(a, b) := 0^\infty \ 110 \ \mathrm{A}{>} \ (11)^a \ 0 \ 1^b \ 0^\infty.
$$

Starting from $C(0, 9)$ (reached after 74 steps from the blank tape), the machine follows the map
$T$:

$$
T(C(a, b)) = \begin{cases}
  C(k+1, 9) & \text{if } a = 0,\ b = 2k+6, \\
  C(a-k+3, 6k+12) & \text{if } a \ge 1,\ b = 2k+6,\ k \le a+2, \\
  \text{Halt} & \text{if } a \ge 1,\ b = 2k+6,\ k \in \lbrace a+3, a+4 \rbrace, \\
  C(k-a-4, 6a+33) & \text{if } a \ge 1,\ b = 2k+6,\ k \ge a+5, \\
  C(k-a, 6a+6) & \text{if } b = 2k+1,\ k > a, \\
  \text{Halt} & \text{if } b = 2k+1,\ a \in \lbrace k, k+1 \rbrace, \\
  C(a-k-1, 6k+9) & \text{if } b = 2k+1,\ a \ge k+2.
\end{cases}
$$

<!-- hardness:begin -->
## Hardness

*Hardness class:* Problem 4 — trigger **EQ (2-wide window at turnaround)**, growth exponential
($\gamma\approx1.4246$ per era, base 3), shield none.

*Verdict (heuristic, from exact accelerated simulation of the certified rules):* probviously
non-halting.

*Hazard:* $P(\text{halt}) \approx 1.6\times10^{-31}$ after 200 eras, geometric tail

*Simulated horizon:* 200 eras (exact)

*Why it is hard:* base-3 `exp3_step_C_odd/even` cascade coupled to the Euclidean-like reflection
$(a,b)\mapsto(b-a,3a)$; sits between Baker–Wüstholz and $\times2,\times3$ rigidity

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private theorem shift_R (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append [0] l))
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)))
        r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append [0, 1, 1] (ListBlank.append [0] l))
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight A
            (ListBlank.append [0, 1, 1] (ListBlank.append [0]
              (ListBlank.append [1, 1] l)))
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

private theorem shift_L_A (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight A l
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight A
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] (ListBlank.append [1, 1] r))) := by
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

private theorem shift_L_F (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1, 1] r))
      (Cfg.headRight F l
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight F
            (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1, 1] r))
          (Cfg.headRight F
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 1] (ListBlank.append [1, 1] r))) := by
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

private theorem shift_R_block (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] l)
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r)))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l)))
        r) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] l)
          (ListBlank.append [0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r)))
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] (ListBlank.append [0]
            (ListBlank.append [1, 1] l)))
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r)) := by
    rw [ListBlank.append_pow_succ]
    bb_steps
  have h2 := shift_R k (ListBlank.append [1, 1] l) r
  have h3 := h1.trans_star h2
  have h_pow :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rwa [h_pow] at h3

private theorem shift_L_even (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0] l)))
        (ListBlank.append [1] r))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] l)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0, 1] r))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0] l)))
          (ListBlank.append [1] r))
        (Cfg.headRight F
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0] l))
          (ListBlank.append [1, 1] (ListBlank.append [0, 1] r))) := by
    bb_steps
  have h2 := shift_L_F k (ListBlank.append [0] l) (ListBlank.append [0, 1] r)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [0] l)
          (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0, 1] r))))
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] l)
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0, 1] r))) := by
    bb_steps
  exact h12.trans h3

private theorem shift_L_odd (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0] l)))
        (ListBlank.append [1] r))
      (Cfg.headRight F l
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0, 1] r)))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0] l)))
          (ListBlank.append [1] r))
        (Cfg.headRight A
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0] l))
          (ListBlank.append [1] (ListBlank.append [0, 1] r))) := by
    bb_steps
  have h2 := shift_L_A k (ListBlank.append [0] l) (ListBlank.append [0, 1] r)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0] l)
          (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0, 1] r))))
        (Cfg.headRight F l
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0, 1] r)))) := by
    bb_steps
  exact h12.trans h3

private theorem shift_R_0 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] l)
        (ListBlank.append [0, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r)))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
        (ListBlank.append [0, 1] r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append [0, 1, 1] l)
            (ListBlank.append [0, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r)))
          (Cfg.headRight A
            (ListBlank.append [0, 1, 1] (ListBlank.append [1, 1] l))
            (ListBlank.append [0, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem even_end (m : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append [0] l))
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 2)) default)))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] l)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [0, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ 4) default)))) := by
  have h1 := shift_R_block (m + 1) (ListBlank.append [0] l) default
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 2)) (ListBlank.append [0] l) =
        ListBlank.append [1, 1] (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ m) (ListBlank.append [0] l))) := by
    rw [ListBlank.append_pow_succ, ListBlank.append_pow_succ]
  rw [h_l] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] (ListBlank.append [0]
            (ListBlank.append [1, 1] (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ m)
                (ListBlank.append [0] l))))))
          default)
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ m)
            (ListBlank.append [0] l)))
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ 4) default))) := by
    have h4 : (([1, 1] : List (Fin 2)) ^ 4) = [1, 1, 1, 1, 1, 1, 1, 1] := rfl
    rw [h4]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_L_even m l (ListBlank.append (([1, 1] : List (Fin 2)) ^ 4) default)
  exact h12.trans h3

private theorem sweep_L_odd_default (k : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) default))
        (ListBlank.append [1] r))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1))
          (ListBlank.append [0, 1] r))) := by
  have h0 : (default : ListBlank (Fin 2)) = ListBlank.append [0] default := by
    simp
  have h1 := shift_L_odd k default r
  rw [← h0] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight F default
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0, 1] r))))
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] default)
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append [0, 1] r))) := by
    rw [ListBlank.append_pow_succ]
    bb_steps
  exact h1.trans h2

private theorem odd_collapse (a c k : ℕ) (h_k : c + a = k + 1) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
          (ListBlank.append [0] r))))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 6) r)))) := by
  have h1 := shift_R_0 c (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)
    (ListBlank.append [0] r)
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) default) := by
    rw [← ListBlank.append_pow_add, h_k, ListBlank.append_pow_succ]
  rw [h_l] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) default)))
          (ListBlank.append [0, 1] (ListBlank.append [0] r)))
        (Cfg.headRight A
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) default))
          (ListBlank.append [1] (ListBlank.append [1, 1, 1, 1, 1] r))) := by
    bb_steps
  have h12 := h1.trans_plus h2
  have h3 := sweep_L_odd_default k (ListBlank.append [1, 1, 1, 1, 1] r)
  have h6 :
      ListBlank.append [0, 1] (ListBlank.append [1, 1, 1, 1, 1] r) =
        ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 6) r) := rfl
  rw [h6] at h3
  exact h12.trans h3

private theorem sweep_L_odd_even (a k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
            (ListBlank.append [0] l)))))
        (ListBlank.append [1] r))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] l)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0, 1] r))))) := by
  have h1 := shift_L_odd k
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) (ListBlank.append [0] l)) r
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) (ListBlank.append [0] l) =
        ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [0] l)) := by
    rw [ListBlank.append_pow_succ]
  rw [h_l] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
            (ListBlank.append [0] l)))
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0, 1] r))))
        (Cfg.headRight F
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [0] l))
          (ListBlank.append [1, 1] (ListBlank.append [0, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append [0, 1] r))))) := by
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_L_F a (ListBlank.append [0] l)
    (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
      (ListBlank.append [0, 1] r)))
  have h123 := h12.trans_star h3
  have h4 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [0] l)
          (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
            (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append [0, 1] r))))))
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] l)
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
            (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append [0, 1] r))))) := by
    bb_steps
  exact h123.trans h4

private theorem odd_step (b c : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append [0] l))
        (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
            (ListBlank.append [0] r))))))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] l)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 6) r)))))) := by
  have h1 := shift_R_block b (ListBlank.append [0] l)
    (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
      (ListBlank.append [0] r)))
  have h2 := shift_R_0 (c + 1)
    (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
      (ListBlank.append [0] l)))
    (ListBlank.append [0] r)
  have h12 := h1.trans_star h2
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
        (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
          (ListBlank.append [0] l))) =
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
          (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
            (ListBlank.append [0] l)))) := by
    rw [ListBlank.append_pow_succ]
  rw [h_l] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
              (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
                (ListBlank.append [0] l))))))
          (ListBlank.append [0, 1] (ListBlank.append [0] r)))
        (Cfg.headRight A
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
            (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1))
              (ListBlank.append [0] l)))))
          (ListBlank.append [1] (ListBlank.append [1, 1, 1, 1, 1] r))) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := sweep_L_odd_even b c l (ListBlank.append [1, 1, 1, 1, 1] r)
  have h6 :
      ListBlank.append [0, 1] (ListBlank.append [1, 1, 1, 1, 1] r) =
        ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 6) r) := rfl
  rw [h6] at h4
  exact h123.trans h4

private theorem unit_step (a b : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
            (ListBlank.append [0] l))))
        (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 2))
          (ListBlank.append [0, 1, 0] r))))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] l)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 9) r)))))) := by
  have h1 := shift_R_block (b + 1)
    (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
      (ListBlank.append [0] l)))
    (ListBlank.append [0, 1, 0] r)
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 2))
        (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
          (ListBlank.append [0] l))) =
        ListBlank.append [1, 1] (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
            (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
              (ListBlank.append [0] l))))) := by
    rw [ListBlank.append_pow_succ, ListBlank.append_pow_succ]
  rw [h_l] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] (ListBlank.append [0]
            (ListBlank.append [1, 1] (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
                (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
                  (ListBlank.append [0] l))))))))
          (ListBlank.append [0, 1, 0] r))
        (Cfg.headRight A
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
            (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
              (ListBlank.append [0] l)))))
          (ListBlank.append [1] (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1] r))) := by
    bb_steps
  have h12 := h1.trans h2
  have h3 := sweep_L_odd_even a b l (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1] r)
  have h9 :
      ListBlank.append [0, 1] (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1] r) =
        ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 9) r) := rfl
  rw [h9] at h3
  exact h12.trans h3

private theorem unit_collapse_default (a : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] default)
        (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 2))
          (ListBlank.append [0, 1, 0] r))))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 9) r)))) := by
  have h1 := shift_R_block (a + 1) default (ListBlank.append [0, 1, 0] r)
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)) := by
    rw [ListBlank.append_pow_succ, ListBlank.append_pow_succ]
  rw [h_l] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] (ListBlank.append [0]
            (ListBlank.append [1, 1] (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)))))
          (ListBlank.append [0, 1, 0] r))
        (Cfg.headRight A
          (ListBlank.append [0, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
          (ListBlank.append [1] (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1] r))) := by
    bb_steps
  have h12 := h1.trans h2
  have h3 := sweep_L_odd_default a (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1] r)
  have h9 :
      ListBlank.append [0, 1] (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1] r) =
        ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 9) r) := rfl
  rw [h9] at h3
  exact h12.trans h3

private theorem unit_b1_succ (a : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 2)) default)))
        (ListBlank.append [0, 1, 1, 0, 1, 0] r))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 12) r)))) := by
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)) := by
    rw [ListBlank.append_pow_succ, ListBlank.append_pow_succ]
  rw [h_l]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] (ListBlank.append [0]
            (ListBlank.append [1, 1] (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)))))
          (ListBlank.append [0, 1, 1, 0, 1, 0] r))
        (Cfg.headRight A
          (ListBlank.append [0, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
          (ListBlank.append [1]
            (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] r))) := by
    bb_steps
  have h2 := sweep_L_odd_default a (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] r)
  have h12_eq :
      ListBlank.append [0, 1] (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] r) =
        ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 12) r) := rfl
  rw [h12_eq] at h2
  exact h1.trans h2

private theorem bounce_0 (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append [0, 1, 1] default) (ListBlank.append [1] r))
      (Cfg.headRight A (ListBlank.append [0, 1, 1] default) (ListBlank.append [0, 1] r)) := by
  bb_steps

private theorem bounce_succ (a : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default))
        (ListBlank.append [1] r))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default)))
        (ListBlank.append [0, 1] r)) := by
  have h0 : (default : ListBlank (Fin 2)) = ListBlank.append [0] default := by
    simp
  have h1 := shift_L_even (a + 1) default r
  rw [← h0] at h1
  have h_r :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) (ListBlank.append [0, 1] r) =
        ListBlank.append [1] (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [0, 1] r))) := by
    rw [ListBlank.append_pow_succ]
    rfl
  rw [h_r] at h1
  have h2 := bounce_0
    (ListBlank.append [1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [0, 1] r)))
  have h12 := h1.trans h2
  have h_r2 :
      ListBlank.append [0, 1] (ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [0, 1] r))) =
        ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
            (ListBlank.append [0, 1] r)) := by
    rw [ListBlank.append_pow_succ]
    rfl
  rw [h_r2] at h12
  have h3 := shift_R_block a default (ListBlank.append [0, 1] r)
  exact h12.trans h3

private theorem bounce_0_block (a : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) r))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] default)
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) r))) := by
  have h_r :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) r =
        ListBlank.append [1] (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) r)) := by
    rw [ListBlank.append_pow_succ]
    rfl
  rw [h_r]
  have h1 := bounce_0 (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) r))
  have h_r2 :
      ListBlank.append [0, 1] (ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) r)) =
        ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) r) := by
    rw [ListBlank.append_pow_succ]
    rfl
  rwa [h_r2] at h1

private theorem bounce_succ_block (a b : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default))
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1)) r))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default)))
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1)) r))) := by
  have h_r :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1)) r =
        ListBlank.append [1] (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ b) r)) := by
    rw [ListBlank.append_pow_succ]
    rfl
  rw [h_r]
  have h1 := bounce_succ a
    (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ b) r))
  have h_r2 :
      ListBlank.append [0, 1] (ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ b) r)) =
        ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (b + 1)) r) := by
    rw [ListBlank.append_pow_succ]
    rfl
  rwa [h_r2] at h1

private theorem halt_M3_0 (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append [0, 1, 1] default) (ListBlank.append [0, 1, 0] r))
      (Cfg.headRight E default (ListBlank.append [0, 1, 1, 1, 1, 1, 1, 1] r)) := by
  bb_steps

private theorem halt_M3_1 (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] default)
        (ListBlank.append [0, 1, 1, 0, 1, 0] r))
      (Cfg.headRight E default
        (ListBlank.append [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] r)) := by
  bb_steps

private theorem halt_M4_0 (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [0, 1, 1] (ListBlank.append [0] (ListBlank.append [1, 1] default)))
        (ListBlank.append [0, 1, 1, 0, 1, 0] r))
      (Cfg.headRight E default
        (ListBlank.append [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] r)) := by
  bb_steps

private theorem isNone_E_zero (r : ListBlank (Fin 2)) :
    (step target (Cfg.headRight E default (ListBlank.append [0] r))).isNone := by
  bb_halt

/-- Canonical tape pattern $C(a, b) := 0^\infty\,110\,\mathrm{A}{>}\,(11)^a\,0\,1^b\,0^\infty$. -/
def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 .default))
    head := some A
    right := .rep [1, 1] 0 (.sym 0 (.rep [1] 1 .default)) }

/-- Configuration $C(a, b)$. -/
private def cfg_C (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 1] default)
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))

private theorem eval_pat_C (vars : ℕ → ℕ) :
    evalTapePattern pat_C vars = cfg_C (vars 0) (vars 1) :=
  rfl

/-- Closed pattern set for `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) := [(pat_C, .ge_const 1 6)]

private theorem in_ps_C (a b : ℕ) (h : b ≥ 6) : IsInPatternSet ps (cfg_C a b) :=
  ⟨(pat_C, .ge_const 1 6), List.Mem.head _,
    fun k => match k with | 0 => a | 1 => b | _ => 0, rfl, h⟩

private def cfg_M3 (a c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 1] default)
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
      (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))))

private def cfg_M4 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default))
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
      (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))))

private theorem M3_reaches (c a d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_M3 a c d) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction c generalizing a d with
  | zero =>
    rcases a with _ | _ | a
    · refine ⟨_, halt_M3_0 (ListBlank.append (([1] : List (Fin 2)) ^ d) default),
        Or.inr (isNone_E_zero _)⟩
    · have h1 := bounce_0_block 0
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
      have h2 := halt_M3_1 (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
      refine ⟨_, h1.trans h2, Or.inr (isNone_E_zero _)⟩
    · have h1 := bounce_0_block (a + 1)
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
      have h2 := unit_collapse_default a (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
      rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 9 d default] at h2
      exact ⟨cfg_C (a + 1) (9 + d), h1.trans h2,
        Or.inl (in_ps_C (a + 1) (9 + d) (by omega))⟩
  | succ c ih =>
    rcases a with _ | a
    · have h1 :
          cfg_M3 0 (c + 1) d =
            Cfg.headRight A
              (ListBlank.append [0, 1, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0) default))
              (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))) :=
        rfl
      rw [h1]
      have h2 := odd_collapse 0 (c + 1) c (by omega)
        (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
      rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 6 d default] at h2
      exact ⟨cfg_C (c + 1) (6 + d), h2, Or.inl (in_ps_C (c + 1) (6 + d) (by omega))⟩
    · have h1 := bounce_0_block a
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
      have h0 : (default : ListBlank (Fin 2)) = ListBlank.append [0] default := by
        simp
      have h2 := odd_step a c default (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
      rw [← h0, ← ListBlank.append_pow_add ([1] : List (Fin 2)) 6 d default] at h2
      have h12 : ReachesPlus target (cfg_M3 (a + 1) (c + 1) d) (cfg_M3 a c (6 + d)) :=
        h1.trans h2
      rcases ih a (6 + d) with ⟨cfg', h3, h_end⟩
      exact ⟨cfg', h12.trans h3, h_end⟩

private theorem M4_reaches (c a b d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_M4 a b c d) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction c generalizing a b d with
  | zero =>
    rcases b with _ | _ | b
    · have h1 := odd_collapse (a + 1) 0 a (by omega)
        (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
      rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 6 d default] at h1
      exact ⟨cfg_C (a + 1) (6 + d), h1, Or.inl (in_ps_C (a + 1) (6 + d) (by omega))⟩
    · have h1 := bounce_succ_block a 0
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
      rcases a with _ | a
      · have h2 := halt_M4_0 (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
        refine ⟨_, h1.trans h2, Or.inr (isNone_E_zero _)⟩
      · have h2 := unit_b1_succ a (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
        rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 12 d default] at h2
        exact ⟨cfg_C (a + 1) (12 + d), h1.trans h2,
          Or.inl (in_ps_C (a + 1) (12 + d) (by omega))⟩
    · have h1 := bounce_succ_block a (b + 1)
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
      have h0 : (default : ListBlank (Fin 2)) = ListBlank.append [0] default := by
        simp
      have h2 := unit_step a b default (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
      rw [← h0, ← ListBlank.append_pow_add ([1] : List (Fin 2)) 9 d default] at h2
      have h12 : ReachesPlus target (cfg_M4 a (b + 2) 0 d) (cfg_M3 a b (9 + d)) :=
        h1.trans h2
      rcases M3_reaches b a (9 + d) with ⟨cfg', h3, h_end⟩
      exact ⟨cfg', h12.trans h3, h_end⟩
  | succ c ih =>
    rcases b with _ | b
    · have h1 := odd_collapse (a + 1) (c + 1) (c + a + 1) (by omega)
        (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
      rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 6 d default] at h1
      exact ⟨cfg_C (c + a + 2) (6 + d), h1,
        Or.inl (in_ps_C (c + a + 2) (6 + d) (by omega))⟩
    · have h1 := bounce_succ_block a b
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
      have h2 := odd_step b c
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default)
        (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
      rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 6 d default] at h2
      have h12 : ReachesPlus target (cfg_M4 a (b + 1) (c + 1) d) (cfg_M4 a b c (6 + d)) :=
        h1.trans h2
      rcases ih a b (6 + d) with ⟨cfg', h3, h_end⟩
      exact ⟨cfg', h12.trans h3, h_end⟩

private theorem cfg_C_odd_eq_M3 (a c : ℕ) :
    cfg_C a (2 * c + 1) = cfg_M3 a c 0 := by
  unfold cfg_C cfg_M3
  have h1 :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * c + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c) default) := by
    rw [Nat.add_comm (2 * c) 1, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * c),
      ← one_pow_two_mul, list_pow_one]
  have h0 :
      ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ 0) (default : ListBlank (Fin 2))) = default := by
    simp
  rw [h1, h0]
  rfl

private theorem step_closed (a b : ℕ) (h_b : b ≥ 6) :
    ∃ cfg', ReachesPlus target (cfg_C a b) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases nat_even_or_odd_two_mul b with ⟨k, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    have h_eq :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (m + 3))) (default : ListBlank (Fin 2)) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1 + 2)) default := by
      rw [one_pow_two_mul]
    have h_r9 :
        ListBlank.append [0, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ 4) (default : ListBlank (Fin 2))) =
          ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 9) default) :=
      rfl
    rcases a with _ | a
    · unfold cfg_C
      rw [h_eq]
      have h0 : (default : ListBlank (Fin 2)) = ListBlank.append [0] default := by
        simp
      have h1 := even_end (m + 1) default
      rw [← h0, h_r9] at h1
      exact ⟨cfg_C (m + 1) 9, h1, Or.inl (in_ps_C (m + 1) 9 (by decide))⟩
    · unfold cfg_C
      rw [h_eq]
      have h1 := bounce_0_block a
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1 + 2)) default))
      have h2 := shift_R_block a default
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1 + 2)) default))
      have h12 := h1.trans h2
      have h3 := even_end (m + 1)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default)
      have h123 := h12.trans h3
      have h_m4 :
          Cfg.headRight A
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default))
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1))
              (ListBlank.append [0, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ 4) default))) =
            cfg_M4 a (m + 1) 4 0 := by
        unfold cfg_M4
        have h0 :
            ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 0) (default : ListBlank (Fin 2))) =
              default := by
          simp
        rw [h0]
      rw [h_m4] at h123
      rcases M4_reaches 4 a (m + 1) 0 with ⟨cfg', h4, h_end⟩
      exact ⟨cfg', h123.trans h4, h_end⟩
  · rw [cfg_C_odd_eq_M3]
    exact M3_reaches c a 0

private theorem init_reaches_pat_C : ReachesStar target (init []) (cfg_C 0 9) := by
  have h1 :
      ReachesPlus target
        (init [])
        (Cfg.headRight A
          (ListBlank.append [0, 1, 1] default)
          (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 2) default))) := by
    have h2_pow : (([1, 1] : List (Fin 2)) ^ 2) = [1, 1, 1, 1] := rfl
    rw [h2_pow]
    bb_steps
  have h0 : (default : ListBlank (Fin 2)) = ListBlank.append [0] default := by
    simp
  have h2 := even_end 0 default
  have h_r9 :
      ListBlank.append [0, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ 4) (default : ListBlank (Fin 2))) =
        ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 9) default) :=
    rfl
  rw [← h0, h_r9] at h2
  exact (h1.trans h2).to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_C 0 9, init_reaches_pat_C, in_ps_C 0 9 (by decide)⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  subst h_mem
  rw [eval_pat_C]
  exact step_closed (vars 0) (vars 1) h_cond

/-- `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`. -/
inductive State where
  /-- $C(a, b + 6) := 0^\infty\,110\,\mathrm{A}{>}\,(11)^a\,0\,1^{b+6}\,0^\infty$. -/
  | C (a b : ℕ)
  /-- $M_3(a, c, d) := 0^\infty\,110\,\mathrm{A}{>}\,(11)^a\,01\,(11)^c\,0\,1^d\,0^\infty$. -/
  | M_3 (a c d : ℕ)
  /-- $M_4(a, b, c, d) :=
    0^\infty\,(11)^{a+1}\,110\,\mathrm{A}{>}\,(11)^b\,01\,(11)^c\,0\,1^d\,0^\infty$. -/
  | M_4 (a b c d : ℕ)

/-- Initial symbolic state $C(0, 9)$, reached after 74 raw TM steps. -/
def start : State := .C 0 3

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b =>
    Cfg.headRight SixState.A
      (ListBlank.append [0, 1, 1] default)
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (b + 6)) default)))
  | .M_3 a c d =>
    Cfg.headRight SixState.A
      (ListBlank.append [0, 1, 1] default)
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))))
  | .M_4 a b c d =>
    Cfg.headRight SixState.A
      (ListBlank.append [0, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default))
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .C 0 b =>
    if b % 2 = 0 then some (.C (b / 2 + 1) 3)
    else some (.C (b / 2 + 3) 0)
  | .C (a + 1) b =>
    if b % 2 = 0 then some (.M_4 a (b / 2 + 1) 4 0)
    else some (.M_3 a (b / 2 + 2) 6)
  | .M_3 0 0 _ => none
  | .M_3 1 0 _ => none
  | .M_3 (a + 2) 0 d => some (.C (a + 1) (d + 3))
  | .M_3 0 (c + 1) d => some (.C (c + 1) d)
  | .M_3 (a + 1) (c + 1) d => some (.M_3 a c (d + 6))
  | .M_4 a 0 c d => some (.C (a + c + 1) d)
  | .M_4 0 1 0 _ => none
  | .M_4 (a + 1) 1 0 d => some (.C (a + 1) (d + 6))
  | .M_4 a (b + 2) 0 d => some (.M_3 a b (d + 9))
  | .M_4 a (b + 1) (c + 1) d => some (.M_4 a b c (d + 6))

private theorem encode_C (a b : ℕ) : encode (.C a b) = cfg_C a (b + 6) := rfl
private theorem encode_M3 (a c d : ℕ) : encode (.M_3 a c d) = cfg_M3 a c d := rfl
private theorem encode_M4 (a b c d : ℕ) : encode (.M_4 a b c d) = cfg_M4 a b c d := rfl

private theorem step_M3_succ_zero (c d : ℕ) :
    ReachesPlus target (cfg_M3 0 (c + 1) d) (cfg_C (c + 1) (d + 6)) := by
  have h1 :
      cfg_M3 0 (c + 1) d =
        Cfg.headRight A
          (ListBlank.append [0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0) default))
          (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))) :=
    rfl
  rw [h1]
  have h2 := odd_collapse 0 (c + 1) c (by omega)
    (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
  rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 6 d default, Nat.add_comm 6 d] at h2
  exact h2

private theorem step_M3_succ_succ (a c d : ℕ) :
    ReachesPlus target (cfg_M3 (a + 1) (c + 1) d) (cfg_M3 a c (d + 6)) := by
  have h1 := bounce_0_block a
    (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
  have h0 : (default : ListBlank (Fin 2)) = ListBlank.append [0] default := by simp
  have h2 := odd_step a c default (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
  rw [← h0, ← ListBlank.append_pow_add ([1] : List (Fin 2)) 6 d default,
    Nat.add_comm 6 d] at h2
  exact h1.trans h2

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_pat_C
  step_some := by
    rintro (⟨a, b⟩ | ⟨a, c, d⟩ | ⟨a, b, c, d⟩) s' hnext
    · rcases nat_even_or_odd_two_mul b with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hmod : (2 * k) % 2 = 0 := by omega
        have hdiv : (2 * k) / 2 = k := by omega
        have h_eq :
            ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 6))
              (default : ListBlank (Fin 2)) =
              ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1 + 2)) default := by
          have hk : 2 * k + 6 = 2 * (k + 1 + 2) := by omega
          rw [hk, one_pow_two_mul]
        rcases a with _ | a
        · simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          rw [encode_C, encode_C]
          unfold cfg_C
          rw [h_eq]
          have h0 : (default : ListBlank (Fin 2)) = ListBlank.append [0] default := by simp
          have h1 := even_end (k + 1) default
          have h_r9 :
              ListBlank.append [0, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ 4) (default : ListBlank (Fin 2))) =
                ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 9) default) :=
            rfl
          rw [← h0, h_r9] at h1
          exact h1
        · simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          rw [encode_C, encode_M4]
          unfold cfg_C
          rw [h_eq]
          have h1 := bounce_0_block a
            (ListBlank.append [0]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1 + 2)) default))
          have h2 := shift_R_block a default
            (ListBlank.append [0]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1 + 2)) default))
          have h12 := h1.trans h2
          have h3 := even_end (k + 1)
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default)
          have h123 := h12.trans h3
          have h_m4 :
              Cfg.headRight A
                (ListBlank.append [0, 1, 1]
                  (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default))
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1))
                  (ListBlank.append [0, 1]
                    (ListBlank.append (([1, 1] : List (Fin 2)) ^ 4) default))) =
                cfg_M4 a (k + 1) 4 0 := by
            unfold cfg_M4
            have h0 :
                ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ 0)
                    (default : ListBlank (Fin 2))) = default := by
              simp
            rw [h0]
          rwa [h_m4] at h123
      · have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
        have hdiv : (2 * k + 1) / 2 = k := by omega
        have h_odd : 2 * k + 1 + 6 = 2 * (k + 3) + 1 := by omega
        rcases a with _ | a
        · simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          rw [encode_C, encode_C, h_odd, cfg_C_odd_eq_M3]
          exact step_M3_succ_zero (k + 2) 0
        · simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          rw [encode_C, encode_M3, h_odd, cfg_C_odd_eq_M3]
          exact step_M3_succ_succ a (k + 2) 0
    · rcases c with _ | c
      · rcases a with _ | _ | a
        · simp [next] at hnext
        · simp [next] at hnext
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          rw [encode_M3, encode_C]
          have h1 := bounce_0_block (a + 1)
            (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
              (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
          have h2 := unit_collapse_default a (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
          have h9 : 9 + d = d + 3 + 6 := by omega
          rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 9 d default, h9] at h2
          exact h1.trans h2
      · rcases a with _ | a
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_M3_succ_zero c d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_M3_succ_succ a c d
    · rcases b with _ | b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        rw [encode_M4, encode_C]
        have h1 := odd_collapse (a + 1) c (a + c) (by omega)
          (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
        rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 6 d default, Nat.add_comm 6 d] at h1
        exact h1
      · rcases c with _ | c
        · rcases b with _ | b
          · rcases a with _ | a
            · simp [next] at hnext
            · simp only [next, Option.some.injEq] at hnext
              subst hnext
              rw [encode_M4, encode_C]
              have h1 := bounce_succ_block (a + 1) 0
                (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
                  (ListBlank.append [0]
                    (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
              have h2 := unit_b1_succ a (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
              have h12 : 12 + d = d + 6 + 6 := by omega
              rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 12 d default, h12] at h2
              exact h1.trans h2
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            rw [encode_M4, encode_M3]
            have h1 := bounce_succ_block a (b + 1)
              (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
            have h0 : (default : ListBlank (Fin 2)) = ListBlank.append [0] default := by simp
            have h2 := unit_step a b default (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
            rw [← h0, ← ListBlank.append_pow_add ([1] : List (Fin 2)) 9 d default,
              Nat.add_comm 9 d] at h2
            exact h1.trans h2
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          rw [encode_M4, encode_M4]
          have h1 := bounce_succ_block a b
            (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 1))
              (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
          have h2 := odd_step b c
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default)
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
          rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 6 d default,
            Nat.add_comm 6 d] at h2
          exact h1.trans h2
  step_none := by
    rintro (⟨a, b⟩ | ⟨a, c, d⟩ | ⟨a, b, c, d⟩) hnext
    · rcases a with _ | a <;> (simp only [next] at hnext; split_ifs at hnext)
    · rcases c with _ | c
      · rcases a with _ | _ | a
        · exact ⟨_, (halt_M3_0 (ListBlank.append (([1] : List (Fin 2)) ^ d) default)).to_star,
            isNone_E_zero _⟩
        · have h1 := bounce_0_block 0
            (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
              (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
          have h2 := halt_M3_1 (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
          exact ⟨_, (h1.trans h2).to_star, isNone_E_zero _⟩
        · simp [next] at hnext
      · rcases a with _ | a <;> simp [next] at hnext
    · rcases b with _ | b
      · simp [next] at hnext
      · rcases c with _ | c
        · rcases b with _ | b
          · rcases a with _ | a
            · have h1 := bounce_succ_block 0 0
                (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
                  (ListBlank.append [0]
                    (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
              have h2 := halt_M4_0 (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
              exact ⟨_, (h1.trans h2).to_star, isNone_E_zero _⟩
            · simp [next] at hnext
          · simp [next] at hnext
        · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-Like Acceleration -/

/-- Single-family high-level symbolic configuration state space for
`1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`. -/
inductive HighLevelState where
  /-- $C(a, b + 6) := 0^\infty\,110\,\mathrm{A}{>}\,(11)^a\,0\,1^{b+6}\,0^\infty$. -/
  | C (a b : ℕ)

/-- Initial high-level symbolic state `.C 0 3`, encoding $C(0, 9)$. -/
def highLevelStart : HighLevelState := .C 0 3

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .C a b => .C a b

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- High-level accelerated transition function on $C(a, b + 6)$, obtained by composing transitions
through $M_3$ and $M_4$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .C 0 b =>
    if b % 2 = 0 then some (.C (b / 2 + 1) 3)
    else some (.C (b / 2 + 3) 0)
  | .C (a + 1) b =>
    if b % 2 = 0 then
      let k := b / 2
      if k ≤ a + 3 then some (.C (a + 4 - k) (6 * k + 6))
      else if k ≤ a + 5 then none
      else some (.C (k - a - 5) (6 * a + 33))
    else
      let k := b / 2 + 2
      if k > a then some (.C (k - a) (6 * a + 6))
      else if a ≤ k + 1 then none
      else some (.C (a - k - 1) (6 * k + 9))

private theorem next_M3_succ (a c d : ℕ) :
    next (.M_3 (a + 1) (c + 1) d) = some (.M_3 a c (d + 6)) := by
  simp [next]

private theorem next_M4_zero (a c d : ℕ) :
    next (.M_4 a 0 c d) = some (.C (a + c + 1) d) := by
  simp [next]

private theorem next_M4_ge2_zero (a b d : ℕ) :
    next (.M_4 a (b + 2) 0 d) = some (.M_3 a b (d + 9)) := by
  simp [next]

private theorem next_M4_succ (a b c d : ℕ) :
    next (.M_4 a (b + 1) (c + 1) d) = some (.M_4 a b c (d + 6)) := by
  simp [next]

private def evalM3 (a c d : ℕ) : Option HighLevelState :=
  if c > a then some (.C (c - a) (d + 6 * a))
  else if a ≤ c + 1 then none
  else some (.C (a - c - 1) (d + 6 * c + 3))

private theorem stepsTo_M3 : ∀ (a c d : ℕ),
    CollatzStepsTo next (.M_3 a c d) ((evalM3 a c d).map toState)
  | 0, 0, _d => by
    dsimp [evalM3]
    exact CollatzStepsTo.of_eq rfl
  | 1, 0, _d => by
    dsimp [evalM3]
    exact CollatzStepsTo.of_eq rfl
  | a + 2, 0, d => by
    have h1 : ¬ (0 > a + 2) := by omega
    have h2 : ¬ (a + 2 ≤ 0 + 1) := by omega
    simp only [evalM3, h1, h2, ↓reduceIte, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
    exact CollatzStepsTo.of_eq rfl
  | 0, c + 1, d => by
    have h1 : c + 1 > 0 := by omega
    simp only [evalM3, h1, ↓reduceIte, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
    exact CollatzStepsTo.of_eq rfl
  | a + 1, c + 1, d => by
    have ih := stepsTo_M3 a c (d + 6)
    have heq : evalM3 (a + 1) (c + 1) d = evalM3 a c (d + 6) := by
      dsimp [evalM3]
      split_ifs <;> first | rfl | omega | (congr 1; congr 1 <;> omega)
    rw [heq]
    exact CollatzStepsTo.head (next_M3_succ a c d) ih

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState)
    (CollatzReachesStar.refl next start) ?_
  rintro ⟨a, b⟩
  rcases a with _ | a
  · dsimp [highLevelNext]
    split_ifs with hb
    · exact CollatzStepsTo.of_eq (by simp [next, toState, hb])
    · exact CollatzStepsTo.of_eq (by simp [next, toState, hb])
  · by_cases hb : b % 2 = 0
    · simp only [highLevelNext, hb, ↓reduceIte]
      have h_step0 : next (.C (a + 1) b) = some (.M_4 a (b / 2 + 1) 4 0) := by simp [next, hb]
      generalize b / 2 = k at h_step0 ⊢
      rcases k with _ | _ | _ | _ | _ | u
      · exact CollatzStepsTo.head h_step0
          (CollatzStepsTo.head (next_M4_succ a 0 3 0)
            (CollatzStepsTo.of_eq (next_M4_zero a 3 6)))
      · have hle : 1 ≤ a + 3 := by omega
        have ha : a + 4 - 1 = a + 2 + 1 := by omega
        simp only [hle, ↓reduceIte, ha]
        exact CollatzStepsTo.head h_step0
          (CollatzStepsTo.head (next_M4_succ a 1 3 0)
            (CollatzStepsTo.head (next_M4_succ a 0 2 6)
              (CollatzStepsTo.of_eq (next_M4_zero a 2 12))))
      · have hle : 2 ≤ a + 3 := by omega
        have ha : a + 4 - 2 = a + 1 + 1 := by omega
        simp only [hle, ↓reduceIte, ha]
        exact CollatzStepsTo.head h_step0
          (CollatzStepsTo.head (next_M4_succ a 2 3 0)
            (CollatzStepsTo.head (next_M4_succ a 1 2 6)
              (CollatzStepsTo.head (next_M4_succ a 0 1 12)
                (CollatzStepsTo.of_eq (next_M4_zero a 1 18)))))
      · have hle : 3 ≤ a + 3 := by omega
        have ha : a + 4 - 3 = a + 0 + 1 := by omega
        simp only [hle, ↓reduceIte, ha]
        exact CollatzStepsTo.head h_step0
          (CollatzStepsTo.head (next_M4_succ a 3 3 0)
            (CollatzStepsTo.head (next_M4_succ a 2 2 6)
              (CollatzStepsTo.head (next_M4_succ a 1 1 12)
                (CollatzStepsTo.head (next_M4_succ a 0 0 18)
                  (CollatzStepsTo.of_eq (next_M4_zero a 0 24))))))
      · rcases a with _ | a'
        · exact CollatzStepsTo.head h_step0
            (CollatzStepsTo.head (next_M4_succ 0 4 3 0)
              (CollatzStepsTo.head (next_M4_succ 0 3 2 6)
                (CollatzStepsTo.head (next_M4_succ 0 2 1 12)
                  (CollatzStepsTo.head (next_M4_succ 0 1 0 18)
                    (CollatzStepsTo.of_eq rfl)))))
        · have hle : 4 ≤ a' + 1 + 3 := by omega
          have ha : a' + 1 + 4 - 4 = a' + 1 := by omega
          simp only [hle, ↓reduceIte, ha]
          exact CollatzStepsTo.head h_step0
            (CollatzStepsTo.head (next_M4_succ (a' + 1) 4 3 0)
              (CollatzStepsTo.head (next_M4_succ (a' + 1) 3 2 6)
                (CollatzStepsTo.head (next_M4_succ (a' + 1) 2 1 12)
                  (CollatzStepsTo.head (next_M4_succ (a' + 1) 1 0 18)
                    (CollatzStepsTo.of_eq rfl)))))
      · have h_m3 := stepsTo_M3 a u 33
        have heq :
            (if u + 5 ≤ a + 3 then some (.C (a + 4 - (u + 5)) (6 * (u + 5) + 6))
             else if u + 5 ≤ a + 5 then none
             else some (.C (u + 5 - a - 5) (6 * a + 33))) = evalM3 a u 33 := by
          dsimp [evalM3]
          split_ifs <;> first | rfl | omega | (congr 1; congr 1 <;> omega)
        rw [heq]
        exact CollatzStepsTo.head h_step0
          (CollatzStepsTo.head (next_M4_succ a (u + 5) 3 0)
            (CollatzStepsTo.head (next_M4_succ a (u + 4) 2 6)
              (CollatzStepsTo.head (next_M4_succ a (u + 3) 1 12)
                (CollatzStepsTo.head (next_M4_succ a (u + 2) 0 18)
                  (CollatzStepsTo.head (next_M4_ge2_zero a u 24) h_m3)))))
    · simp only [highLevelNext, hb, ↓reduceIte]
      have h_step0 : next (.C (a + 1) b) = some (.M_3 a (b / 2 + 2) 6) := by simp [next, hb]
      have h_m3 := stepsTo_M3 a (b / 2 + 2) 6
      have heq :
          (if b / 2 + 2 > a then some (.C (b / 2 + 2 - a) (6 * a + 6))
           else if a ≤ b / 2 + 2 + 1 then none
           else some (.C (a - (b / 2 + 2) - 1) (6 * (b / 2 + 2) + 9))) =
            evalM3 a (b / 2 + 2) 6 := by
        dsimp [evalM3]
        split_ifs <;> first | rfl | omega | (congr 1; congr 1; omega)
      rw [heq]
      exact CollatzStepsTo.head h_step0 h_m3

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

end BusyBeaver.M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA
