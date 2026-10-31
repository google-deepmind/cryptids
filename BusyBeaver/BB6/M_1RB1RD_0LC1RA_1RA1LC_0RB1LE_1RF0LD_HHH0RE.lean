/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE`

We define the configuration for $p \in \lbrace 0, 1 \rbrace$ and $a, w \ge 0$ (restricting
$0^\infty \ (10)^a \ 1^{2j+3} \ \mathrm{D}{>} \ 1 \ 1^w \ 0^\infty$ to its closed invariant
$j \in \lbrace 0, 1 \rbrace$):

$$
D_p(a, w) := 0^\infty \ (10)^a \ 1^{2p+3} \ \mathrm{D}{>} \ 1 \ 1^w \ 0^\infty.
$$

Starting from $D_0(0, 3)$ (reached after 38 steps from the blank tape), with
$m = \lfloor w / 2 \rfloor$, the machine follows the map $T$:

$$
\begin{aligned}
T(D_0(a, w)) &= \begin{cases}
  D_0(a - m - 2, 2w + 5) & \text{if } a \ge m + 2, \\
  D_1(1, 2w + 1) & \text{if } a = m + 1, \\
  D_1(1, 2w) & \text{if } a = m, \\
  \text{Halt} & \text{if } w = 2a + 2, \\
  D_0(2a + 2, 2w - 4a - 5) & \text{if } 2a + 3 \le w \le 2a + 5, \\
  J_1(2a + 3, w - 2a - 6) & \text{if } w \ge 2a + 6,
\end{cases} \\
T(D_1(a, w)) &= J_1(a, w),
\end{aligned}
$$

where $J_1(a, w)$ (`drainJ1`) contracts $w \ge 2a + 6$ drain chains from $D_1(a, w)$:

$$
J_1(a, w) = \begin{cases}
  D_0(a - m - 2, 2w + 7) & \text{if } a \ge m + 2, \\
  D_1(1, 2w + 3) & \text{if } a = m + 1, \\
  D_1(1, 2w + 2) & \text{if } a = m, \\
  \text{Halt} & \text{if } w = 2a + 2, \\
  D_0(2a + 3, 2w - 4a - 5) & \text{if } 2a + 3 \le w \le 2a + 5, \\
  J_1(2a + 4, w - 2a - 6) & \text{if } w \ge 2a + 6.
\end{cases}
$$

<!-- hardness:begin -->
## Hardness

*Hardness class:* Problem 2 — trigger **EQ with leaky parity shield**, growth linear ($2^n$ fuel
bursts, intermittent resets), shield leaky.

*Verdict (heuristic, from exact accelerated simulation of the certified rules):* probviously
non-halting.

*Hazard:* $P(\text{halt}) \approx 1.2\times10^{-4}$ ($\propto 1/T$)

*Simulated horizon:* $10^{16}$ TM steps

*Why it is hard:* structural sibling of #183 on `D1(a, b, w)`; boundary coincidence
$w_{\text{rem}} = 2a+7$ in the even-source branch

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Leftward shift across `(11)^k` in state `E`, writing `(10)^k`. -/
private theorem shift_E_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft E (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft E l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft E
            (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            r)
          (Cfg.headLeft E
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 0] r)) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 0] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1, 0] r) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Rightward shift across `(10)^k` in state `B`, writing `(11)^k`. -/
private theorem shift_B_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r))
      (Cfg.headRight B (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight B l
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight B (ListBlank.append [1, 1] l)
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward shift across `1^k` in state `C`. -/
private theorem shift_C_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft C (ListBlank.append (([1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft C l (ListBlank.append (([1] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft C
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
            r)
          (Cfg.headLeft C
            (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] r)) := by
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

/-- Rightward shift across `(10)^k` in state `F`, preserving `(10)^k`. -/
private theorem shift_F_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r))
      (Cfg.headRight F (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight F l
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight F (ListBlank.append [1, 0] l)
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 0] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1, 0] l) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Rightward shift across `(01)^k` in state `A`, writing `(11)^k`. -/
private theorem shift_A_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight A (ListBlank.append [1, 1] l)
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

/-- Canonical tape pattern $P_1(c) := 0^\infty\,\mathrm{C}{>}\,0\,1^c\,0^\infty$. -/
private abbrev pat_1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.rep [1] 0 .default) }

/-- Canonical tape pattern $P_2(a, c) := 0^\infty\,(10)^a\,1\,\mathrm{C}{>}\,0\,1^c\,0^\infty$. -/
private abbrev pat_2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [0, 1] 0 .default)
    head := some C
    right := .sym 0 (.rep [1] 1 .default) }

/-- Closed pattern set for `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE` (Level A). -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .default
      head := some SixState.C
      right := .sym 0 (.rep [1] 0 .default) }, .ge_const 0 1),
   ({ left := .sym 1 (.rep [0, 1] 0 .default)
      head := some SixState.C
      right := .sym 0 (.rep [1] 1 .default) }, .ge_const 1 1)]

/-- Configuration $P_1(c)$. -/
private def cfg_P1 (c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C default
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

/-- Configuration $P_2(a, c)$. -/
private def cfg_P2 (a c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

private theorem eval_pat_1 (vars : ℕ → ℕ) :
    evalTapePattern pat_1 vars = cfg_P1 (vars 0) :=
  rfl

private theorem eval_pat_2 (vars : ℕ → ℕ) :
    evalTapePattern pat_2 vars = cfg_P2 (vars 0) (vars 1) :=
  rfl

private theorem in_ps_P1 (c : ℕ) (hc : c ≥ 1) : IsInPatternSet ps (cfg_P1 c) :=
  ⟨(pat_1, .ge_const 0 1), List.Mem.head _,
    fun _ => c, rfl, hc⟩

private theorem in_ps_P2 (a c : ℕ) (hc : c ≥ 1) : IsInPatternSet ps (cfg_P2 a c) :=
  ⟨(pat_2, .ge_const 1 1), List.Mem.tail _ (List.Mem.head _),
    fun i => match i with | 0 => a | 1 => c | _ => 0, rfl, hc⟩

/-- Intermediate configuration
$D_1(a, b, w) := 0^\infty\,(10)^a\,1^b\,\mathrm{D}{>}\,1\,1^w\,0^\infty$. -/
private def cfg_D1 (a b w : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D
    (ListBlank.append (([1] : List (Fin 2)) ^ b)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))

private theorem headLeft_C_default_eq_P1 (m : ℕ) :
    Cfg.headLeft C default (ListBlank.append (([1] : List (Fin 2)) ^ m) default) = cfg_P1 m := by
  simp [cfg_P1, Cfg.headLeft, Cfg.headRight]

private theorem headLeft_C_succ_eq_P2 (a m : ℕ) :
    Cfg.headLeft C
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default)
      (ListBlank.append (([1] : List (Fin 2)) ^ m) default) = cfg_P2 a m := by
  unfold cfg_P2
  rw [ListBlank.append_pow_succ]
  simp [Cfg.headLeft, Cfg.headRight]

/-! ## Transitions from $P_1$ and $P_2$ -/

private theorem step_P1_c1 : ReachesPlus target (cfg_P1 1) (cfg_P1 4) := by
  unfold cfg_P1
  have h1 : (([1] : List (Fin 2)) ^ 1) = [1] := rfl
  have h4 : (([1] : List (Fin 2)) ^ 4) = [1, 1, 1, 1] := rfl
  rw [h1, h4]
  bb_steps

private theorem step_P1_ge2 (w : ℕ) :
    ReachesPlus target (cfg_P1 (w + 2)) (cfg_D1 0 2 w) := by
  unfold cfg_P1 cfg_D1
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default) := by
    rw [Nat.add_comm w 2, ListBlank.append_pow_add]
    rfl
  have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [h_r, h2, list_pow_zero, ListBlank.append_nil]
  bb_steps

private theorem step_P2_a0_c1 : ReachesPlus target (cfg_P2 0 1) (cfg_P1 5) := by
  unfold cfg_P2 cfg_P1
  have h1 : (([1] : List (Fin 2)) ^ 1) = [1] := rfl
  have h5 : (([1] : List (Fin 2)) ^ 5) = [1, 1, 1, 1, 1] := rfl
  rw [h1, h5, list_pow_zero, ListBlank.append_nil]
  bb_steps

private theorem step_P2_succ_c1 (a : ℕ) :
    ReachesPlus target (cfg_P2 (a + 1) 1) (cfg_P2 a 5) := by
  unfold cfg_P2
  have h1 : (([1] : List (Fin 2)) ^ 1) = [1] := rfl
  have h5 : (([1] : List (Fin 2)) ^ 5) = [1, 1, 1, 1, 1] := rfl
  rw [ListBlank.append_pow_succ, h1, h5]
  bb_steps

private theorem step_P2_ge2 (a w : ℕ) :
    ReachesPlus target (cfg_P2 a (w + 2)) (cfg_D1 a 3 w) := by
  unfold cfg_P2 cfg_D1
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default) := by
    rw [Nat.add_comm w 2, ListBlank.append_pow_add]
    rfl
  have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
  rw [h_r, h3]
  bb_steps

/-! ## Case 1: $D_1(0, 2k+1, w)$ -/

private theorem sweep_case1 (k w : ℕ) :
    ReachesPlus target
      (cfg_D1 0 (2 * k + 1) w)
      (Cfg.headRight B
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))) := by
  unfold cfg_D1
  rw [list_pow_zero, ListBlank.append_nil]
  have h_l1 :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] default) := by
    rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 1, ← one_pow_two_mul, list_pow_one]
  rw [h_l1]
  set r := ListBlank.append (([1] : List (Fin 2)) ^ w) default
  have h1 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] default))
          (ListBlank.append [1] r))
        (Cfg.headLeft E
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] default))
          (ListBlank.append [1] r)) := by
    bb_steps
  have h2 := shift_E_left k (ListBlank.append [1] default) (ListBlank.append [1] r)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append [1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] r)))
        (Cfg.headRight B
          (ListBlank.append [1, 1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] r))) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_B_right k (ListBlank.append [1, 1] default) (ListBlank.append [1] r)
  have h1234 := h123.trans_star h4
  have h_l2 :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default := by
    rw [one_pow_two_mul, ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 2]
    rfl
  rwa [h_l2] at h1234

private theorem step_D1_case1_ge2 (k w : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 1) (w + 2)) (cfg_D1 0 (2 * (k + 1) + 2) w) := by
  have h1 := sweep_case1 k (w + 2)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) default)))
        (cfg_D1 0 (2 * (k + 1) + 2) w) := by
    unfold cfg_D1
    rw [list_pow_zero, ListBlank.append_nil]
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default) := by
      rw [Nat.add_comm w 2, ListBlank.append_pow_add]
      rfl
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1) + 2))
          (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default) := by
      have h_eq : 2 * (k + 1) + 2 = 2 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_r, h_l]
    bb_steps
  exact h1.trans h2

private theorem step_D1_case1_w0 (k : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 1) 0) (cfg_P1 (2 * k + 4)) := by
  have h1 := sweep_case1 k 0
  rw [list_pow_zero, ListBlank.append_nil] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)
          (ListBlank.append [1] default))
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 4)) default)
          default) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default) := by
      have h_eq : 2 * k + 4 = 2 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_l]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_left (2 * k + 4) default default
  have h123 := h12.trans_star h3
  rwa [headLeft_C_default_eq_P1] at h123

private theorem step_D1_case1_w1 (k : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 1) 1) (cfg_P1 (2 * k + 6)) := by
  have h1 := sweep_case1 k 1
  rw [list_pow_one] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)
          (ListBlank.append [1] (ListBlank.append [1] default)))
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 6)) default)
          default) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 6)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default) := by
      have h_eq : 2 * k + 6 = 4 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_l]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_left (2 * k + 6) default default
  have h123 := h12.trans_star h3
  rwa [headLeft_C_default_eq_P1] at h123

/-! ## Case 2: $D_1(0, 2k+2, w)$ -/

private theorem sweep_case2 (k w : ℕ) :
    ReachesPlus target
      (cfg_D1 0 (2 * k + 2) w)
      (Cfg.headRight F
        (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))) := by
  unfold cfg_D1
  rw [list_pow_zero, ListBlank.append_nil]
  have h_l1 :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) default := by
    have h_eq : 2 * k + 2 = 2 * (k + 1) := by omega
    rw [h_eq, ← one_pow_two_mul]
  rw [h_l1]
  set r := ListBlank.append (([1] : List (Fin 2)) ^ w) default
  have h1 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) default)
          (ListBlank.append [1] r))
        (Cfg.headLeft E
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) default)
          (ListBlank.append [1] r)) := by
    bb_steps
  have h2 := shift_E_left (k + 1) default (ListBlank.append [1] r)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft E default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [1] r)))
        (Cfg.headRight F
          (ListBlank.append [1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [1] r))) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_F_right (k + 1) (ListBlank.append [1] default) (ListBlank.append [1] r)
  have h1234 := h123.trans_star h4
  have h_l2 :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1))
        (ListBlank.append [1] (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default) := by
    rw [ListBlank.append_pow_succ, append_10_pow_one]
    rfl
  rwa [h_l2] at h1234

private theorem step_D1_case2_w0 (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_D1 0 (2 * k + 2) 0) cfg' ∧ (step target cfg').isNone := by
  have h1 := sweep_case2 k 0
  rw [list_pow_zero, ListBlank.append_nil] at h1
  refine ⟨Cfg.headRight F
    (ListBlank.append [1, 0, 1, 0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
    default, ?_, ?_⟩
  · have h2 :
        ReachesPlus target
          (Cfg.headRight F
            (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
            (ListBlank.append [1] default))
          (Cfg.headRight F
            (ListBlank.append [1, 0, 1, 0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
            default) := by
      bb_steps
    exact h1.trans h2
  · bb_halt

private theorem step_D1_case2_w1 (k : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 2) 1) (cfg_P2 k 3) := by
  have h1 := sweep_case2 k 1
  rw [list_pow_one] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
          (ListBlank.append [1] (ListBlank.append [1] default)))
        (cfg_P2 k 3) := by
    unfold cfg_P2
    have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [h3]
    bb_steps
  exact h1.trans h2

private theorem step_D1_case2_w2 (k : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 2) 2) (cfg_P2 k 5) := by
  have h1 := sweep_case2 k 2
  have h_w2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [h_w2] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
          (ListBlank.append [1] (ListBlank.append [1, 1] default)))
        (cfg_P2 k 5) := by
    unfold cfg_P2
    have h5 : (([1] : List (Fin 2)) ^ 5) = [1, 1, 1, 1, 1] := rfl
    rw [h5]
    bb_steps
  exact h1.trans h2

private theorem step_D1_case2_w3 (k : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 2) 3) (cfg_P2 k 7) := by
  have h1 := sweep_case2 k 3
  have h_w3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
  rw [h_w3] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
          (ListBlank.append [1] (ListBlank.append [1, 1, 1] default)))
        (cfg_P2 k 7) := by
    unfold cfg_P2
    have h7 : (([1] : List (Fin 2)) ^ 7) = [1, 1, 1, 1, 1, 1, 1] := rfl
    rw [h7]
    bb_steps
  exact h1.trans h2

private theorem step_D1_case2_ge4 (k w : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 2) (w + 4)) (cfg_D1 (k + 1) (2 * 2 + 1) w) := by
  have h1 := sweep_case2 k (w + 4)
  have h2 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (w + 4)) default)))
        (cfg_D1 (k + 1) (2 * 2 + 1) w) := by
    unfold cfg_D1
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (w + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ w) default) := by
      rw [Nat.add_comm w 4, ListBlank.append_pow_add]
      rfl
    have h5 : (([1] : List (Fin 2)) ^ (2 * 2 + 1)) = [1, 1, 1, 1, 1] := rfl
    rw [h_r, h5, ListBlank.append_pow_succ]
    bb_steps
  exact h1.trans h2

/-! ## Case 3: $D_1(a+1, 2k+1, w)$ -/

private theorem sweep_case3 (a k w : ℕ) :
    ReachesPlus target
      (cfg_D1 (a + 1) (2 * k + 1) w)
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
        (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))) := by
  unfold cfg_D1
  set l := ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default
  set r := ListBlank.append (([1] : List (Fin 2)) ^ w) default
  have h_l1 :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 0, 1] l) := by
    rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 1, ← one_pow_two_mul,
      list_pow_one, ListBlank.append_pow_succ]
    rfl
  rw [h_l1]
  have h1 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 0, 1] l))
          (ListBlank.append [1] r))
        (Cfg.headLeft E
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 0, 1] l))
          (ListBlank.append [1] r)) := by
    bb_steps
  have h2 := shift_E_left k (ListBlank.append [1, 0, 1] l) (ListBlank.append [1] r)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append [1, 0, 1] l)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] r)))
        (Cfg.headRight A
          (ListBlank.append [1, 1] l)
          (ListBlank.append [0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] r)))) := by
    bb_steps
  have h123 := h12.trans h3
  rw [append_zero_10_pow_one] at h123
  have h4 := shift_A_right k (ListBlank.append [1, 1] l) (ListBlank.append [0, 1] r)
  have h1234 := h123.trans_star h4
  have h_l2 :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l := by
    rw [one_pow_two_mul, ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 2]
    rfl
  rwa [h_l2] at h1234

private theorem step_D1_case3_ge2 (a k w : ℕ) :
    ReachesPlus target (cfg_D1 (a + 1) (2 * k + 1) (w + 2)) (cfg_D1 a (2 * (k + 2) + 1) w) := by
  have h1 := sweep_case3 a k (w + 2)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) default)))
        (cfg_D1 a (2 * (k + 2) + 1) w) := by
    unfold cfg_D1
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default) := by
      rw [Nat.add_comm w 2, ListBlank.append_pow_add]
      rfl
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 2) + 1))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)) := by
      have h_eq : 2 * (k + 2) + 1 = 3 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_r, h_l]
    bb_steps
  exact h1.trans h2

private theorem step_D1_case3_w0 (a k : ℕ) :
    ReachesPlus target
      (cfg_D1 (a + 1) (2 * k + 1) 0)
      (Cfg.headLeft C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 5)) default)) := by
  have h1 := sweep_case3 a k 0
  rw [list_pow_zero, ListBlank.append_nil] at h1
  set l := ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l)
          (ListBlank.append [0, 1] default))
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 5)) l)
          default) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 5)) l =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l) := by
      have h_eq : 2 * k + 5 = 3 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_l]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_left (2 * k + 5) l default
  exact h12.trans_star h3

private theorem step_D1_case3_w1 (a k : ℕ) :
    ReachesPlus target
      (cfg_D1 (a + 1) (2 * k + 1) 1)
      (Cfg.headLeft C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 7)) default)) := by
  have h1 := sweep_case3 a k 1
  rw [list_pow_one] at h1
  set l := ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l)
          (ListBlank.append [0, 1] (ListBlank.append [1] default)))
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 7)) l)
          default) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 7)) l =
          ListBlank.append [1, 1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l) := by
      have h_eq : 2 * k + 7 = 5 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_l]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_left (2 * k + 7) l default
  exact h12.trans_star h3

/-! ## Strong Induction on $w$ and `HasCollatzReduction` -/

private def IH_Prop (w : ℕ) : Prop :=
  (∀ k, StepsToClosed target ps (cfg_D1 0 (2 * k + 1) w)) ∧
  (∀ k, StepsToClosed target ps (cfg_D1 0 (2 * k + 2) w)) ∧
  (∀ a k, StepsToClosed target ps (cfg_D1 (a + 1) (2 * k + 1) w))

private theorem d1_closed_case1 (w k : ℕ) (ih : ∀ m < w, IH_Prop m) :
    StepsToClosed target ps (cfg_D1 0 (2 * k + 1) w) := by
  rcases w with _ | _ | w'
  · exact ⟨cfg_P1 (2 * k + 4), step_D1_case1_w0 k, Or.inl (in_ps_P1 (2 * k + 4) (by omega))⟩
  · exact ⟨cfg_P1 (2 * k + 6), step_D1_case1_w1 k, Or.inl (in_ps_P1 (2 * k + 6) (by omega))⟩
  · exact StepsToClosed.of_reachesPlus (step_D1_case1_ge2 k w')
      ((ih w' (by omega)).2.1 (k + 1))

private theorem d1_closed_case2 (w k : ℕ) (ih : ∀ m < w, IH_Prop m) :
    StepsToClosed target ps (cfg_D1 0 (2 * k + 2) w) := by
  rcases w with _ | _ | _ | _ | w'
  · obtain ⟨cfg', h_step, h_halt⟩ := step_D1_case2_w0 k
    exact ⟨cfg', h_step, Or.inr h_halt⟩
  · exact ⟨cfg_P2 k 3, step_D1_case2_w1 k, Or.inl (in_ps_P2 k 3 (by decide))⟩
  · exact ⟨cfg_P2 k 5, step_D1_case2_w2 k, Or.inl (in_ps_P2 k 5 (by decide))⟩
  · exact ⟨cfg_P2 k 7, step_D1_case2_w3 k, Or.inl (in_ps_P2 k 7 (by decide))⟩
  · exact StepsToClosed.of_reachesPlus (step_D1_case2_ge4 k w')
      ((ih w' (by omega)).2.2 k 2)

private theorem d1_closed_case3 (w a k : ℕ) (ih : ∀ m < w, IH_Prop m) :
    StepsToClosed target ps (cfg_D1 (a + 1) (2 * k + 1) w) := by
  rcases w with _ | _ | w'
  · have h_step := step_D1_case3_w0 a k
    rcases a with _ | a'
    · rw [list_pow_zero, ListBlank.append_nil, headLeft_C_default_eq_P1] at h_step
      exact ⟨cfg_P1 (2 * k + 5), h_step, Or.inl (in_ps_P1 (2 * k + 5) (by omega))⟩
    · rw [headLeft_C_succ_eq_P2] at h_step
      exact ⟨cfg_P2 a' (2 * k + 5), h_step, Or.inl (in_ps_P2 a' (2 * k + 5) (by omega))⟩
  · have h_step := step_D1_case3_w1 a k
    rcases a with _ | a'
    · rw [list_pow_zero, ListBlank.append_nil, headLeft_C_default_eq_P1] at h_step
      exact ⟨cfg_P1 (2 * k + 7), h_step, Or.inl (in_ps_P1 (2 * k + 7) (by omega))⟩
    · rw [headLeft_C_succ_eq_P2] at h_step
      exact ⟨cfg_P2 a' (2 * k + 7), h_step, Or.inl (in_ps_P2 a' (2 * k + 7) (by omega))⟩
  · have h_step := step_D1_case3_ge2 a k w'
    rcases a with _ | a'
    · exact StepsToClosed.of_reachesPlus h_step ((ih w' (by omega)).1 (k + 2))
    · exact StepsToClosed.of_reachesPlus h_step ((ih w' (by omega)).2.2 a' (k + 2))

private theorem d1_closed (w : ℕ) : IH_Prop w := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    exact ⟨fun k => d1_closed_case1 w k ih,
      fun k => d1_closed_case2 w k ih,
      fun a k => d1_closed_case3 w a k ih⟩

private theorem step_P1_closed (c : ℕ) (hc : c ≥ 1) : StepsToClosed target ps (cfg_P1 c) := by
  rcases c with _ | _ | w
  · omega
  · exact ⟨cfg_P1 4, step_P1_c1, Or.inl (in_ps_P1 4 (by decide))⟩
  · exact StepsToClosed.of_reachesPlus (step_P1_ge2 w) ((d1_closed w).2.1 0)

private theorem step_P2_closed (a c : ℕ) (hc : c ≥ 1) : StepsToClosed target ps (cfg_P2 a c) := by
  rcases c with _ | _ | w
  · omega
  · rcases a with _ | a'
    · exact ⟨cfg_P1 5, step_P2_a0_c1, Or.inl (in_ps_P1 5 (by decide))⟩
    · exact ⟨cfg_P2 a' 5, step_P2_succ_c1 a', Or.inl (in_ps_P2 a' 5 (by decide))⟩
  · rcases a with _ | a'
    · exact StepsToClosed.of_reachesPlus (step_P2_ge2 0 w) ((d1_closed w).1 1)
    · exact StepsToClosed.of_reachesPlus (step_P2_ge2 (a' + 1) w) ((d1_closed w).2.2 a' 1)

private theorem init_reaches_start : ReachesStar target (init []) (cfg_P1 1) := by
  have h_init : ReachesPlus target (init []) (cfg_P1 1) := by
    unfold cfg_P1
    have h1 : (([1] : List (Fin 2)) ^ 1) = [1] := rfl
    rw [h1]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_P1 1, init_reaches_start, in_ps_P1 1 (by decide)⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl
  · exact step_P1_closed (vars 0) h_cond
  · exact step_P2_closed (vars 0) (vars 1) h_cond

/-- `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B, Box 1) -/

/-- Symbolic configuration state space for `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE`. -/
inductive State where
  /-- $P_1(c + 1) := 0^\infty\,\mathrm{C}{>}\,0\,1^{c+1}\,0^\infty$. -/
  | P_1 (c : ℕ)
  /-- $P_2(a, c + 1) := 0^\infty\,(10)^a\,1\,\mathrm{C}{>}\,0\,1^{c+1}\,0^\infty$. -/
  | P_2 (a c : ℕ)
  /-- $D_1(0, 2k + 1, w) := 0^\infty\,1^{2k+1}\,\mathrm{D}{>}\,1\,1^w\,0^\infty$. -/
  | D_1_0_odd (k w : ℕ)
  /-- $D_1(0, 2k + 2, w) := 0^\infty\,1^{2k+2}\,\mathrm{D}{>}\,1\,1^w\,0^\infty$. -/
  | D_1_0_even (k w : ℕ)
  /-- $D_1(a + 1, 2k + 1, w) :=
    0^\infty\,(10)^{a+1}\,1^{2k+1}\,\mathrm{D}{>}\,1\,1^w\,0^\infty$. -/
  | D_1_succ_odd (a k w : ℕ)

/-- Initial symbolic state $P_1(1)$, reached after 3 raw TM steps. -/
def start : State := .P_1 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 c =>
    Cfg.headRight SixState.C default
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .P_2 a c =>
    Cfg.headRight SixState.C
      (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .D_1_0_odd k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_1_0_even k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_1_succ_odd a k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))

/-- Accelerated Collatz-like transition function (Box 1). -/
def next : State → Option State
  | .P_1 0 => some (.P_1 3)
  | .P_1 (w + 1) => some (.D_1_0_even 0 w)
  | .P_2 0 0 => some (.P_1 4)
  | .P_2 (a + 1) 0 => some (.P_2 a 4)
  | .P_2 0 (w + 1) => some (.D_1_0_odd 1 w)
  | .P_2 (a + 1) (w + 1) => some (.D_1_succ_odd a 1 w)
  | .D_1_0_odd k 0 => some (.P_1 (2 * k + 3))
  | .D_1_0_odd k 1 => some (.P_1 (2 * k + 5))
  | .D_1_0_odd k (w + 2) => some (.D_1_0_even (k + 1) w)
  | .D_1_0_even _ 0 => none
  | .D_1_0_even k 1 => some (.P_2 k 2)
  | .D_1_0_even k 2 => some (.P_2 k 4)
  | .D_1_0_even k 3 => some (.P_2 k 6)
  | .D_1_0_even k (w + 4) => some (.D_1_succ_odd k 2 w)
  | .D_1_succ_odd 0 k 0 => some (.P_1 (2 * k + 4))
  | .D_1_succ_odd 0 k 1 => some (.P_1 (2 * k + 6))
  | .D_1_succ_odd (a + 1) k 0 => some (.P_2 a (2 * k + 4))
  | .D_1_succ_odd (a + 1) k 1 => some (.P_2 a (2 * k + 6))
  | .D_1_succ_odd 0 k (w + 2) => some (.D_1_0_odd (k + 2) w)
  | .D_1_succ_odd (a + 1) k (w + 2) => some (.D_1_succ_odd a (k + 2) w)

private theorem step_state : ∀ s : State,
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesPlus target (encode s) cfg' ∧ (step target cfg').isNone
  | .P_1 0 => step_P1_c1
  | .P_1 (w + 1) => step_P1_ge2 w
  | .P_2 0 0 => step_P2_a0_c1
  | .P_2 (a + 1) 0 => step_P2_succ_c1 a
  | .P_2 0 (w + 1) => step_P2_ge2 0 w
  | .P_2 (a + 1) (w + 1) => step_P2_ge2 (a + 1) w
  | .D_1_0_odd k 0 => step_D1_case1_w0 k
  | .D_1_0_odd k 1 => step_D1_case1_w1 k
  | .D_1_0_odd k (w + 2) => step_D1_case1_ge2 k w
  | .D_1_0_even k 0 => step_D1_case2_w0 k
  | .D_1_0_even k 1 => step_D1_case2_w1 k
  | .D_1_0_even k 2 => step_D1_case2_w2 k
  | .D_1_0_even k 3 => step_D1_case2_w3 k
  | .D_1_0_even k (w + 4) => step_D1_case2_ge4 k w
  | .D_1_succ_odd 0 k 0 => by
    have h := step_D1_case3_w0 0 k
    rwa [list_pow_zero, ListBlank.append_nil, headLeft_C_default_eq_P1] at h
  | .D_1_succ_odd 0 k 1 => by
    have h := step_D1_case3_w1 0 k
    rwa [list_pow_zero, ListBlank.append_nil, headLeft_C_default_eq_P1] at h
  | .D_1_succ_odd (a + 1) k 0 => by
    have h := step_D1_case3_w0 (a + 1) k
    rwa [headLeft_C_succ_eq_P2] at h
  | .D_1_succ_odd (a + 1) k 1 => by
    have h := step_D1_case3_w1 (a + 1) k
    rwa [headLeft_C_succ_eq_P2] at h
  | .D_1_succ_odd 0 k (w + 2) => step_D1_case3_ge2 0 k w
  | .D_1_succ_odd (a + 1) k (w + 2) => step_D1_case3_ge2 (a + 1) k w

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := fun s s' hnext => by
    have h := step_state s
    rwa [hnext] at h
  step_none := fun s hnext => by
    have h := step_state s
    rw [hnext] at h
    obtain ⟨cfg', hp, hh⟩ := h
    exact ⟨cfg', hp.to_star, hh⟩

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## Intermediate Collatz-Like Acceleration on $D_1(a, z, w)$ -/

private inductive MidState where
  /-- $D_1(0, 2k + 1, w) := 0^\infty\,1^{2k+1}\,\mathrm{D}{>}\,1\,1^w\,0^\infty$. -/
  | D_1_0_odd (k w : ℕ)
  /-- $D_1(0, 2k + 2, w) := 0^\infty\,1^{2k+2}\,\mathrm{D}{>}\,1\,1^w\,0^\infty$. -/
  | D_1_0_even (k w : ℕ)
  /-- $D_1(a + 1, 2k + 1, w) :=
    0^\infty\,(10)^{a+1}\,1^{2k+1}\,\mathrm{D}{>}\,1\,1^w\,0^\infty$. -/
  | D_1_succ_odd (a k w : ℕ)

private def midStart : MidState := .D_1_0_even 0 2

private def midToState : MidState → State
  | .D_1_0_odd k w => .D_1_0_odd k w
  | .D_1_0_even k w => .D_1_0_even k w
  | .D_1_succ_odd a k w => .D_1_succ_odd a k w

private def midEncode (s : MidState) : Cfg (Fin 2) (Fin 6) :=
  encode (midToState s)

private def midNext : MidState → Option MidState
  | .D_1_0_odd k 0 => some (.D_1_0_even 0 (2 * k + 2))
  | .D_1_0_odd k 1 => some (.D_1_0_even 0 (2 * k + 4))
  | .D_1_0_odd k (w + 2) => some (.D_1_0_even (k + 1) w)
  | .D_1_0_even _ 0 => none
  | .D_1_0_even 0 1 => some (.D_1_0_odd 1 1)
  | .D_1_0_even (k + 1) 1 => some (.D_1_succ_odd k 1 1)
  | .D_1_0_even 0 2 => some (.D_1_0_odd 1 3)
  | .D_1_0_even (k + 1) 2 => some (.D_1_succ_odd k 1 3)
  | .D_1_0_even 0 3 => some (.D_1_0_odd 1 5)
  | .D_1_0_even (k + 1) 3 => some (.D_1_succ_odd k 1 5)
  | .D_1_0_even k (w + 4) => some (.D_1_succ_odd k 2 w)
  | .D_1_succ_odd 0 k 0 => some (.D_1_0_even 0 (2 * k + 3))
  | .D_1_succ_odd 0 k 1 => some (.D_1_0_even 0 (2 * k + 5))
  | .D_1_succ_odd 1 k 0 => some (.D_1_0_odd 1 (2 * k + 3))
  | .D_1_succ_odd 1 k 1 => some (.D_1_0_odd 1 (2 * k + 5))
  | .D_1_succ_odd (a + 2) k 0 => some (.D_1_succ_odd a 1 (2 * k + 3))
  | .D_1_succ_odd (a + 2) k 1 => some (.D_1_succ_odd a 1 (2 * k + 5))
  | .D_1_succ_odd a k (w + 2) =>
    let m := (w + 2) / 2
    if a + 1 ≤ m then
      some (.D_1_0_odd (k + 2 * (a + 1)) (w - 2 * a))
    else
      some (.D_1_succ_odd (a - m) (k + 2 * m) (w + 2 - 2 * m))

private theorem reaches_D_1_succ_odd_diag (m : ℕ) (a k w : ℕ) :
    CollatzReachesStar next
      (.D_1_succ_odd (a + m) k (w + 2 * m))
      (.D_1_succ_odd a (k + 2 * m) w) := by
  induction m generalizing k with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ m ih =>
    have h_next : next (.D_1_succ_odd (a + (m + 1)) k (w + 2 * (m + 1))) =
        some (.D_1_succ_odd (a + m) (k + 2) (w + 2 * m)) := by
      have h1 : a + (m + 1) = (a + m) + 1 := by omega
      have h2 : w + 2 * (m + 1) = (w + 2 * m) + 2 := by omega
      rw [h1, h2]
      simp [next]
    have ih' := ih (k + 2)
    have hk : k + 2 + 2 * m = k + 2 * (m + 1) := by omega
    rw [hk] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem reaches_D_1_succ_odd_drain_le (a k w : ℕ) (h : a + 1 ≤ (w + 2) / 2) :
    CollatzStepsTo next (.D_1_succ_odd a k (w + 2))
      (some (.D_1_0_odd (k + 2 * (a + 1)) (w - 2 * a))) := by
  have h_star := reaches_D_1_succ_odd_diag a 0 k (w - 2 * a + 2)
  have ha : 0 + a = a := by omega
  have hw : w - 2 * a + 2 + 2 * a = w + 2 := by omega
  rw [ha, hw] at h_star
  have h_last : next (.D_1_succ_odd 0 (k + 2 * a) (w - 2 * a + 2)) =
      some (.D_1_0_odd (k + 2 * (a + 1)) (w - 2 * a)) := by
    have hk : k + 2 * a + 2 = k + 2 * (a + 1) := by omega
    simp [next, hk]
  exact CollatzStepsTo.of_reachesStar h_star (CollatzStepsTo.of_eq h_last)

private theorem reaches_D_1_succ_odd_drain_gt (a k w : ℕ) (h : ¬ a + 1 ≤ (w + 2) / 2) :
    CollatzStepsTo next (.D_1_succ_odd a k (w + 2))
      (some (.D_1_succ_odd (a - (w + 2) / 2) (k + 2 * ((w + 2) / 2))
        (w + 2 - 2 * ((w + 2) / 2)))) := by
  let m := (w + 2) / 2
  have hm_pos : 0 < m := by omega
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm_pos)
  have h_head : next (.D_1_succ_odd a k (w + 2)) =
      some (.D_1_succ_odd (a - 1) (k + 2) w) := by
    have ha1 : a = (a - 1) + 1 := by omega
    rw [ha1]
    simp [next]
  have h_star := reaches_D_1_succ_odd_diag m' (a - m) (k + 2) (w + 2 - 2 * m)
  have ha : a - m + m' = a - 1 := by omega
  have hk : k + 2 + 2 * m' = k + 2 * m := by omega
  have hw : w + 2 - 2 * m + 2 * m' = w := by omega
  rw [ha, hk, hw] at h_star
  exact CollatzReachesPlus.head h_head h_star

private theorem is_valid_mid_acceleration :
    IsValidAcceleration target midStart midEncode midNext := by
  refine is_valid_acceleration.of_collatz (embed := midToState)
    (.head (s₂ := .P_1 3) rfl (.single rfl)) ?_
  rintro (⟨k, w⟩ | ⟨k, w⟩ | ⟨a, k, w⟩)
  · rcases w with _ | _ | w
    · exact CollatzStepsTo.head (s₂ := .P_1 (2 * k + 3)) rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.head (s₂ := .P_1 (2 * k + 5)) rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.of_eq rfl
  · rcases k with _ | k <;> rcases w with _ | _ | _ | _ | w
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.of_eq rfl
  · rcases w with _ | _ | w
    · rcases a with _ | _ | a
      · exact CollatzStepsTo.head (s₂ := .P_1 (2 * k + 4)) rfl (CollatzStepsTo.of_eq rfl)
      · exact CollatzStepsTo.head (s₂ := .P_2 0 (2 * k + 4)) rfl (CollatzStepsTo.of_eq rfl)
      · exact CollatzStepsTo.head (s₂ := .P_2 (a + 1) (2 * k + 4)) rfl (CollatzStepsTo.of_eq rfl)
    · rcases a with _ | _ | a
      · exact CollatzStepsTo.head (s₂ := .P_1 (2 * k + 6)) rfl (CollatzStepsTo.of_eq rfl)
      · exact CollatzStepsTo.head (s₂ := .P_2 0 (2 * k + 6)) rfl (CollatzStepsTo.of_eq rfl)
      · exact CollatzStepsTo.head (s₂ := .P_2 (a + 1) (2 * k + 6)) rfl (CollatzStepsTo.of_eq rfl)
    · by_cases h : a + 1 ≤ (w + 2) / 2
      · have h_eq : Option.map midToState
            (midNext (MidState.D_1_succ_odd a k (w + 2))) =
          some (.D_1_0_odd (k + 2 * (a + 1)) (w - 2 * a)) := by
          rcases a with _ | _ | a
          · dsimp [midNext]; split_ifs
            · rfl
            · omega
          · dsimp [midNext]; split_ifs
            · rfl
            · omega
          · dsimp [midNext]; split_ifs; rfl
        rw [h_eq]
        exact reaches_D_1_succ_odd_drain_le a k w h
      · have h_eq : Option.map midToState
            (midNext (MidState.D_1_succ_odd a k (w + 2))) =
          some (.D_1_succ_odd (a - (w + 2) / 2) (k + 2 * ((w + 2) / 2))
            (w + 2 - 2 * ((w + 2) / 2))) := by
          rcases a with _ | _ | a
          · omega
          · dsimp [midNext]; split_ifs
            · omega
            · rfl
          · dsimp [midNext]; split_ifs; rfl
        rw [h_eq]
        exact reaches_D_1_succ_odd_drain_gt a k w h

/-! ## Intermediate Acceleration on $D(a, j, w)$ -/

private inductive PrevState where
  | D (a j w : ℕ)

private def prevStart : PrevState := .D 0 0 3

private def prevToState : PrevState → State
  | .D 0 j w => .D_1_0_odd (j + 1) w
  | .D (a + 1) j w => .D_1_succ_odd a (j + 1) w

private def prevEncode (s : PrevState) : Cfg (Fin 2) (Fin 6) :=
  encode (prevToState s)

private def prevToMid : PrevState → MidState
  | .D 0 j w => .D_1_0_odd (j + 1) w
  | .D (a + 1) j w => .D_1_succ_odd a (j + 1) w

private def prevNext : PrevState → Option PrevState
  | .D a j w =>
    let m := w / 2
    if a ≥ m + 2 then some (.D (a - m - 2) 0 (2 * j + 2 * w + 5))
    else if a = m + 1 then some (.D 1 1 (2 * j + 2 * w + 1))
    else if a = m then some (.D 1 1 (2 * j + 2 * w))
    else if w = 2 * a + 2 then none
    else if w ≤ 2 * a + 5 then some (.D (j + 2 * a + 2) 0 (2 * w - 4 * a - 5))
    else some (.D (j + 2 * a + 3) 1 (w - 2 * a - 6))

private theorem steps_zero (j w : ℕ) :
    CollatzStepsTo midNext (.D_1_0_odd (j + 1) w) ((prevNext (.D 0 j w)).map prevToMid) := by
  rcases w with _ | _ | _ | _ | _ | _ | w <;>
    refine CollatzStepsTo.head rfl (CollatzStepsTo.of_eq ?_) <;> simp only [prevNext] <;>
    split_ifs <;> first | contradiction | omega | rfl

private theorem steps_succ_small (a j w : ℕ) (hw : w ≤ 1) :
    CollatzStepsTo midNext (.D_1_succ_odd a (j + 1) w)
      ((prevNext (.D (a + 1) j w)).map prevToMid) := by
  rcases w with _ | _ | w
  · rcases a with _ | _ | a
    · refine CollatzStepsTo.head rfl (CollatzStepsTo.of_eq ?_)
      simp only [prevNext]
      split_ifs <;> first | contradiction | omega | rfl
    · refine CollatzStepsTo.of_eq ?_
      simp only [prevNext]
      split_ifs <;> first | contradiction | omega | rfl
    · refine CollatzStepsTo.of_eq ?_
      simp only [prevNext]
      split_ifs <;> first | contradiction | omega | rfl
  · rcases a with _ | _ | a
    · refine CollatzStepsTo.head rfl (CollatzStepsTo.of_eq ?_)
      simp only [prevNext]
      split_ifs <;> first | contradiction | omega | rfl
    · refine CollatzStepsTo.of_eq ?_
      simp only [prevNext]
      split_ifs <;> first | contradiction | omega | rfl
    · refine CollatzStepsTo.of_eq ?_
      simp only [prevNext]
      split_ifs <;> first | contradiction | omega | rfl
  · omega

private theorem is_valid_prev_acceleration :
    IsValidAcceleration target prevStart prevEncode prevNext := by
  have he : (fun u => midEncode (prevToMid u)) = prevEncode := by
    funext u
    rcases u with ⟨_ | a, j, w⟩ <;> rfl
  rw [← he]
  refine is_valid_mid_acceleration.of_collatz (embed := prevToMid)
    (CollatzReachesStar.single rfl) ?_
  rintro ⟨_ | a, j, w⟩
  · exact steps_zero j w
  · rcases w with _ | _ | w
    · exact steps_succ_small a j 0 (by omega)
    · exact steps_succ_small a j 1 (by omega)
    · by_cases h : a + 1 ≤ (w + 2) / 2
      · have h1 : midNext (.D_1_succ_odd a (j + 1) (w + 2)) =
            some (.D_1_0_odd (j + 2 * (a + 1) + 1) (w - 2 * a)) := by
          simp only [midNext, h, ↓reduceIte, Option.some.injEq, MidState.D_1_0_odd.injEq,
            and_true]
          omega
        have h2 : prevNext (.D (a + 1) j (w + 2)) =
            prevNext (.D 0 (j + 2 * (a + 1)) (w - 2 * a)) := by
          simp only [prevNext]
          split_ifs <;> simp_all <;> omega
        rw [h2]
        exact CollatzStepsTo.head h1 (steps_zero _ _)
      · have h1 : midNext (.D_1_succ_odd a (j + 1) (w + 2)) =
            some (.D_1_succ_odd (a - (w + 2) / 2) (j + 2 * ((w + 2) / 2) + 1)
              (w + 2 - 2 * ((w + 2) / 2))) := by
          simp only [midNext, h, ↓reduceIte, Option.some.injEq, MidState.D_1_succ_odd.injEq,
            true_and, and_true]
          omega
        have h2 : prevNext (.D (a + 1) j (w + 2)) =
            prevNext (.D (a - (w + 2) / 2 + 1) (j + 2 * ((w + 2) / 2))
              (w + 2 - 2 * ((w + 2) / 2))) := by
          simp only [prevNext]
          split_ifs <;>
            (try simp only [Option.some.injEq, PrevState.D.injEq, reduceCtorEq,
              true_and]) <;>
            omega
        rw [h2]
        exact CollatzStepsTo.head h1 (steps_succ_small _ _ _ (by omega))

/-! ## High-Level Collatz-Like Acceleration -/

/-- High-level symbolic configuration state space for
`1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE`. -/
inductive HighLevelState where
  /-- $D_p(a, w) := 0^\infty\,(10)^a\,1^{2p+3}\,\mathrm{D}{>}\,1\,1^w\,0^\infty$ for
  $p \in \{0, 1\}$. -/
  | D (p : Bool) (a w : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $D_0(0, 3)$. -/
def highLevelStart : HighLevelState := .D false 0 3

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .D p 0 w => .D_1_0_odd (if p then 2 else 1) w
  | .D p (a + 1) w => .D_1_succ_odd a (if p then 2 else 1) w

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Evaluate the $j = 1$ state $0^\infty\,(10)^a\,1^5\,\mathrm{D}{>}\,1\,1^w\,0^\infty$ across any
chain of $w \ge 2a + 6$ drain steps. -/
def drainJ1 (a w : ℕ) : Option HighLevelState :=
  let m := w / 2
  if a ≥ m + 2 then some (.D false (a - m - 2) (2 * w + 7))
  else if a = m + 1 then some (.D true 1 (2 * w + 3))
  else if a = m then some (.D true 1 (2 * w + 2))
  else if w = 2 * a + 2 then none
  else if w ≤ 2 * a + 5 then some (.D false (2 * a + 3) (2 * w - 4 * a - 5))
  else drainJ1 (2 * a + 4) (w - 2 * a - 6)
termination_by w
decreasing_by omega

/-- High-level accelerated transition function on $D_p(a, w)$, restricting $j$ to its closed bit
$p \in \{0, 1\}$ and contracting $w \ge 2a + 6$ drain chains via `drainJ1`. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .D false a w =>
    let m := w / 2
    if a ≥ m + 2 then some (.D false (a - m - 2) (2 * w + 5))
    else if a = m + 1 then some (.D true 1 (2 * w + 1))
    else if a = m then some (.D true 1 (2 * w))
    else if w = 2 * a + 2 then none
    else if w ≤ 2 * a + 5 then some (.D false (2 * a + 2) (2 * w - 4 * a - 5))
    else drainJ1 (2 * a + 3) (w - 2 * a - 6)
  | .D true a w => drainJ1 a w

private def toPrev : HighLevelState → PrevState
  | .D false a w => .D a 0 w
  | .D true a w => .D a 1 w

private theorem steps_drainJ1 (a w : ℕ) :
    CollatzStepsTo prevNext (.D a 1 w) ((drainJ1 a w).map toPrev) := by
  induction w using Nat.strong_induction_on generalizing a with
  | h w ih =>
    rw [drainJ1]
    by_cases h1 : a ≥ w / 2 + 2
    · rw [ite_eq_left h1]
      refine CollatzStepsTo.of_eq ?_
      dsimp only [prevNext, Option.map, toPrev]
      rw [ite_eq_left h1, Option.some.injEq, PrevState.D.injEq]
      omega
    · rw [ite_eq_right h1]
      by_cases h2 : a = w / 2 + 1
      · rw [ite_eq_left h2]
        refine CollatzStepsTo.of_eq ?_
        dsimp only [prevNext, Option.map, toPrev]
        rw [ite_eq_right h1, ite_eq_left h2, Option.some.injEq, PrevState.D.injEq]
        omega
      · rw [ite_eq_right h2]
        by_cases h3 : a = w / 2
        · rw [ite_eq_left h3]
          refine CollatzStepsTo.of_eq ?_
          dsimp only [prevNext, Option.map, toPrev]
          rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, Option.some.injEq,
            PrevState.D.injEq]
          omega
        · rw [ite_eq_right h3]
          by_cases h4 : w = 2 * a + 2
          · rw [ite_eq_left h4]
            refine CollatzStepsTo.of_eq ?_
            dsimp only [prevNext, Option.map]
            rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
          · rw [ite_eq_right h4]
            by_cases h5 : w ≤ 2 * a + 5
            · rw [ite_eq_left h5]
              refine CollatzStepsTo.of_eq ?_
              dsimp only [prevNext, Option.map, toPrev]
              rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                ite_eq_left h5, Option.some.injEq, PrevState.D.injEq]
              omega
            · rw [ite_eq_right h5]
              have hstep : prevNext (.D a 1 w) = some (.D (2 * a + 4) 1 (w - 2 * a - 6)) := by
                dsimp only [prevNext]
                rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                  ite_eq_right h5, Option.some.injEq, PrevState.D.injEq]
                omega
              exact CollatzStepsTo.head hstep (ih (w - 2 * a - 6) (by omega) (2 * a + 4))

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  have he : (fun u => prevEncode (toPrev u)) = highLevelEncode := by
    funext u
    rcases u with ⟨_ | _, _ | a, w⟩ <;> rfl
  rw [← he]
  refine is_valid_prev_acceleration.of_collatz (embed := toPrev)
    (CollatzReachesStar.refl prevNext _) ?_
  rintro ⟨_ | _, a, w⟩
  · dsimp only [toPrev, highLevelNext]
    by_cases h1 : a ≥ w / 2 + 2
    · rw [ite_eq_left h1]
      refine CollatzStepsTo.of_eq ?_
      dsimp only [prevNext, Option.map, toPrev]
      rw [ite_eq_left h1, Option.some.injEq, PrevState.D.injEq]
      omega
    · rw [ite_eq_right h1]
      by_cases h2 : a = w / 2 + 1
      · rw [ite_eq_left h2]
        refine CollatzStepsTo.of_eq ?_
        dsimp only [prevNext, Option.map, toPrev]
        rw [ite_eq_right h1, ite_eq_left h2, Option.some.injEq, PrevState.D.injEq]
        omega
      · rw [ite_eq_right h2]
        by_cases h3 : a = w / 2
        · rw [ite_eq_left h3]
          refine CollatzStepsTo.of_eq ?_
          dsimp only [prevNext, Option.map, toPrev]
          rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, Option.some.injEq,
            PrevState.D.injEq]
          omega
        · rw [ite_eq_right h3]
          by_cases h4 : w = 2 * a + 2
          · rw [ite_eq_left h4]
            refine CollatzStepsTo.of_eq ?_
            dsimp only [prevNext, Option.map]
            rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
          · rw [ite_eq_right h4]
            by_cases h5 : w ≤ 2 * a + 5
            · rw [ite_eq_left h5]
              refine CollatzStepsTo.of_eq ?_
              dsimp only [prevNext, Option.map, toPrev]
              rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                ite_eq_left h5, Option.some.injEq, PrevState.D.injEq]
              omega
            · rw [ite_eq_right h5]
              have hstep : prevNext (.D a 0 w) = some (.D (2 * a + 3) 1 (w - 2 * a - 6)) := by
                dsimp only [prevNext]
                rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                  ite_eq_right h5, Option.some.injEq, PrevState.D.injEq]
                omega
              exact CollatzStepsTo.head hstep (steps_drainJ1 (2 * a + 3) (w - 2 * a - 6))
  · exact steps_drainJ1 a w

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

end BusyBeaver.M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE
