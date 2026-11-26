/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC`

We define the configuration for $a, k, d, c \ge 0$:

$$
C(a, k, d, c) := 0^\infty \ (10)^a \ (11)^k \ \mathrm{C}{>} \ (11)^d \ (10)^c \ 1111 \ 0^\infty.
$$

Starting from $C(0, 0, 0, 1)$ (reached after 27 steps from the blank tape), the machine visits only
configurations in which $k$ and $d$ are not both nonzero. Writing
$D(a, d, c) := C(a, 0, d, c)$ and $K(a, k, c) := C(a, k + 1, 0, c)$, the intermediate map $T$ is:

$$
\begin{aligned}
T(K(a, k, c)) &= \begin{cases}
  K(a, k - c, 2c + 1) & \text{if } c \le k, \\
  D(a, 2k + 2, c - k - 1) & \text{if } c > k,
\end{cases} \\
T(D(a, d, c)) &= \begin{cases}
  K(a - 1, d + 1, 0) & \text{if } a \ge 1,\ c = 0, \\
  K(a - 1, d + 2 - c, 2c - 1) & \text{if } a \ge 1,\ 1 \le c \le d + 2, \\
  D(a - 1, 2d + 4, c - d - 3) & \text{if } a \ge 1,\ c \ge d + 3, \\
  D(d + 1, 0, c) & \text{if } a = 0,\ c \ge 1, \\
  \text{Halt} & \text{if } a = 0,\ c = 0.
\end{cases}
\end{aligned}
$$

Contracting the terminating $K(a, k, c)$ loop via `evalK` (which preserves $a$ and returns the
resulting $(d', c')$ of $D(a, d', c')$) and iterating the strictly decreasing $a$-drain via
`drainD` until $a = 0$ restricts the dynamics (`HighLevelState`, `highLevelNext`) to the
two-counter Poincaré section $D(a, c) := C(a, 0, 0, c)$, starting at `highLevelStart = .D 0 1` with
`highLevelNext (.D a c) = drainD a 0 c`.
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift Lemmas -/

private theorem shift_A_11 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{A}}> (([1, 1] : List (Fin 2))^k +> r)) [target]⊢*
    ((l <+ ([1, 1] : List (Fin 2))^k) {{A}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : (l {{A}}> (([1, 1] : List (Fin 2))^(k + 1) +> r)) [target]⊢⁺
        ((l <+ ([1, 1] : List (Fin 2))) {{A}}> (([1, 1] : List (Fin 2))^k +> r)) := by
      rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) k r]
      bb_steps
    have h2 := ih (l <+ ([1, 1] : List (Fin 2))) r
    have h3 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_pow : ((l <+ ([1, 1] : List (Fin 2))) <+ ([1, 1] : List (Fin 2))^k) =
        (l <+ ([1, 1] : List (Fin 2))^(k + 1)) := by
      rw [← ListBlank.append_assoc, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem shift_B_11 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{B}}> (([1, 1] : List (Fin 2))^k +> r)) [target]⊢*
    ((l <+ ([1, 0] : List (Fin 2))^k) {{B}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : (l {{B}}> (([1, 1] : List (Fin 2))^(k + 1) +> r)) [target]⊢⁺
        ((l <+ ([1, 0] : List (Fin 2))) {{B}}> (([1, 1] : List (Fin 2))^k +> r)) := by
      rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) k r]
      bb_steps
    have h2 := ih (l <+ ([1, 0] : List (Fin 2))) r
    have h3 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_pow : ((l <+ ([1, 0] : List (Fin 2))) <+ ([1, 0] : List (Fin 2))^k) =
        (l <+ ([1, 0] : List (Fin 2))^(k + 1)) := by
      rw [← ListBlank.append_assoc, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem shift_E_11 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (([1, 1] : List (Fin 2))^k +> r)) [target]⊢*
    ((l <+ ([0, 1] : List (Fin 2))^k) {{E}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : (l {{E}}> (([1, 1] : List (Fin 2))^(k + 1) +> r)) [target]⊢⁺
        ((l <+ ([0, 1] : List (Fin 2))) {{E}}> (([1, 1] : List (Fin 2))^k +> r)) := by
      rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) k r]
      bb_steps
    have h2 := ih (l <+ ([0, 1] : List (Fin 2))) r
    have h3 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_pow : ((l <+ ([0, 1] : List (Fin 2))) <+ ([0, 1] : List (Fin 2))^k) =
        (l <+ ([0, 1] : List (Fin 2))^(k + 1)) := by
      rw [← ListBlank.append_assoc, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem shift_C_left_01 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2))^k) {{C}}> ((0 : Fin 2) >> r)) [target]⊢*
    (l {{C}}> ((0 : Fin 2) >> (([1, 1] : List (Fin 2))^k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h_pow_l : (l <+ ([1, 0] : List (Fin 2))^(k + 1)) =
        ((l <+ ([1, 0] : List (Fin 2))^k) <+ ([1, 0] : List (Fin 2))) := by
      rw [← ListBlank.append_assoc]; rfl
    rw [h_pow_l]
    have h1 : (((l <+ ([1, 0] : List (Fin 2))^k) <+ ([1,
      0] : List (Fin 2))) {{C}}> ((0 : Fin 2) >> r))
        [target]⊢⁺
        ((l <+ ([1, 0] : List (Fin 2))^k) {{C}}> ((0 : Fin 2) >> (([1,
      1] : List (Fin 2)) +> r))) := by
      bb_steps
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    have h3 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_pow_r : (([1, 1] : List (Fin 2))^k +> (([1, 1] : List (Fin 2)) +> r)) =
        (([1, 1] : List (Fin 2))^(k + 1) +> r) := by
      rw [← ListBlank.append_assoc, ← list_pow_succ']
    rwa [h_pow_r] at h3

private theorem shift_C_left_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2))^k) {{C}}> ((1 : Fin 2) >> r)) [target]⊢*
    (l {{C}}> (([1, 0] : List (Fin 2))^k +> ((1 : Fin 2) >> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    have h_pow_l : (l <+ ([1, 0] : List (Fin 2))^(k + 1)) =
        ((l <+ ([1, 0] : List (Fin 2))^k) <+ ([1, 0] : List (Fin 2))) := by
      rw [← ListBlank.append_assoc]; rfl
    rw [h_pow_l]
    have h1 : (((l <+ ([1, 0] : List (Fin 2))^k) <+ ([1,
      0] : List (Fin 2))) {{C}}> ((1 : Fin 2) >> r))
        [target]⊢⁺
        ((l <+ ([1, 0] : List (Fin 2))^k) {{C}}> (([1,
      0] : List (Fin 2)) +> ((1 : Fin 2) >> r))) := by
      bb_steps
    have h2 : ((l <+ ([1, 0] : List (Fin 2))^k) {{C}}> (([1,
      0] : List (Fin 2)) +> ((1 : Fin 2) >> r)))
        [target]⊢*
        (l {{C}}> (([1, 0] : List (Fin 2))^k +> (([1,
      0] : List (Fin 2)) +> ((1 : Fin 2) >> r)))) := by
      simpa [List.cons_append, ListBlank.append_cons, ListBlank.append_nil] using
        ih l ((0 : Fin 2) >> ((1 : Fin 2) >> r))
    have h3 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_pow_r : (([1, 0] : List (Fin 2))^k +> (([1, 0] : List (Fin 2)) +> ((1 : Fin 2) >> r))) =
        (([1, 0] : List (Fin 2))^(k + 1) +> ((1 : Fin 2) >> r)) := by
      rw [← ListBlank.append_assoc, ← list_pow_succ']
    rwa [h_pow_r] at h3

private theorem step_C_11_to_B (d : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) [target]⊢⁺
    ((l <+ [1, 1]) {{B}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) := by
  cases d with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  | succ d =>
    rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) d]
    bb_steps

private theorem step_C_default_to_E (d : Nat) (r : ListBlank (Fin 2)) :
    (default {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) [target]⊢⁺
    ((default <+ [0, 1]) {{E}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) := by
  cases d with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  | succ d =>
    rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) d]
    bb_steps

private theorem step_C_01_to_A (d : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) [target]⊢⁺
    (l {{A}}> (([1, 1] : List (Fin 2))^d +> ([1, 1] +> ((1 : Fin 2) >> r)))) := by
  have h1 : ((l <+ [0, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) [target]⊢⁺
      (l {{A}}> ([1, 1] +> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r)))) := by
    cases d with
    | zero =>
      simp only [list_pow_zero, ListBlank.append_cons, ListBlank.append_nil]
      bb_steps
    | succ d =>
      rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) d]
      bb_steps
  have h_comm : ([1, 1] +> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) =
      (([1, 1] : List (Fin 2))^d +> ([1, 1] +> ((1 : Fin 2) >> r))) := by
    rw [← ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) d]
    rw [ListBlank.append_pow_add ([1, 1] : List (Fin 2)) d 1]
    rfl
  rwa [h_comm] at h1

/-! ## Canonical Pattern Set -/

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1, 1] 1 (.rep [0, 1] 0 .default)
    head  := some C
    right := .rep [1, 1] 2 (.rep [1, 0] 3 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default))))) }

def ps : TapePatternSet (Fin 2) (Fin 6) := [(pat_A, .true)]

private def cfg_A (a k d c : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((([0, 1] : List (Fin 2))^a +> default) <+ ([1, 1] : List (Fin 2))^k) {{C}}>
    (([1, 1] : List (Fin 2))^d +> (([1, 0] : List (Fin 2))^c +> ([1, 1, 1, 1] +> default)))

private theorem eval_pat_A (vars : Nat -> Nat) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) (vars 2) (vars 3) := rfl

private theorem in_ps_A (a k d c : Nat) : IsInPatternSet ps (cfg_A a k d c) := by
  refine ⟨(pat_A, .true), List.Mem.head _,
      (fun i => match i with | 0 => a | 1 => k | 2 => d | 3 => c | _ => 0), ?_, trivial⟩
  exact (eval_pat_A (fun i => match i with | 0 => a | 1 => k | 2 => d | 3 => c | _ => 0)).symm

/-! ## Accelerated Transition Rules -/

private theorem rule_1 (a k d c : Nat) :
    (cfg_A a (k + 1) d (c + 1)) [target]⊢⁺ (cfg_A a k (d + 2) c) := by
  let L := ((([0, 1] : List (Fin 2))^a +> default) <+ ([1, 1] : List (Fin 2))^k)
  let R_tail := (([1, 0] : List (Fin 2))^c +> ([1, 1, 1, 1] +> default))
  have h_start : cfg_A a (k + 1) d (c + 1) =
      ((L <+ [1, 1]) {{C}}> (([1,
      1] : List (Fin 2))^d +> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail)))) := by
    unfold cfg_A
    rw [ListBlank.append_pow_add_rev _ ([1, 1] : List (Fin 2)) k 1]
    rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) c]
    rfl
  rw [h_start]
  have h1 := step_C_11_to_B d L ((0 : Fin 2) >> R_tail)
  have h2 := shift_B_11 d (L <+ [1, 1]) ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (((L <+ [1, 1]) <+ ([1,
      0] : List (Fin 2))^d) {{B}}> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail)))
      [target]⊢⁺
      (((L <+ [1, 1]) <+ ([1,
      0] : List (Fin 2))^d) {{C}}> ((0 : Fin 2) >> ((1 : Fin 2) >> R_tail))) := by
    bb_steps
  have h123 := ReachesPlus.trans h12 h3
  have h4 := shift_C_left_01 d (L <+ [1, 1]) ((1 : Fin 2) >> R_tail)
  have h1234 := ReachesPlus.trans_star h123 h4
  have h5 : ((L <+ [1, 1]) {{C}}> ((0 : Fin 2) >> (([1,
      1] : List (Fin 2))^d +> ((1 : Fin 2) >> R_tail))))
      [target]⊢⁺
      (L {{C}}> ([1, 1, 1] +> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> R_tail)))) := by
    bb_steps
  have h12345 := ReachesPlus.trans h1234 h5
  have h_end : (L {{C}}> ([1, 1, 1] +> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> R_tail)))) =
      cfg_A a k (d + 2) c := by
    rw [show (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> R_tail)) =
        ((1 : Fin 2) >> (([1, 1] : List (Fin 2))^d +> R_tail)) from swap_1_11_pow d R_tail]
    unfold cfg_A
    have h_d : d + 2 = 2 + d := by omega
    rw [h_d, ListBlank.append_pow_add ([1, 1] : List (Fin 2)) 2 d]
    rfl
  rwa [h_end] at h12345

private theorem rule_2 (a k d : Nat) :
    (cfg_A a (k + 1) d 0) [target]⊢⁺ (cfg_A a (k + 1) 0 (d + 1)) := by
  let L := ((([0, 1] : List (Fin 2))^a +> default) <+ ([1, 1] : List (Fin 2))^k)
  have h_start : cfg_A a (k + 1) d 0 =
      ((L <+ [1, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ([1, 1,
      1] +> default)))) := by
    unfold cfg_A
    rw [ListBlank.append_pow_add_rev _ ([1, 1] : List (Fin 2)) k 1]
    rfl
  rw [h_start]
  have h1 := step_C_11_to_B d L ([1, 1, 1] +> default)
  have h2 := shift_B_11 d (L <+ [1, 1]) ((1 : Fin 2) >> ([1, 1, 1] +> default))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (((L <+ [1, 1]) <+ ([1, 0] : List (Fin 2))^d) {{B}}> ((1 : Fin 2) >> ([1, 1,
      1] +> default)))
      [target]⊢⁺
      ((((L <+ [1, 1]) <+ ([1, 0] : List (Fin 2))^d) <+ [1, 0]) {{C}}> ((1 : Fin 2) >> ([1, 1,
      1] +> default))) := by
    bb_steps
  have h123 := ReachesPlus.trans h12 h3
  have h_pow : (((L <+ [1, 1]) <+ ([1, 0] : List (Fin 2))^d) <+ [1, 0]) =
      ((L <+ [1, 1]) <+ ([1, 0] : List (Fin 2))^(d + 1)) := by
    rw [← ListBlank.append_assoc]; rfl
  rw [h_pow] at h123
  have h4 := shift_C_left_10 (d + 1) (L <+ [1, 1]) ([1, 1, 1] +> default)
  have h1234 := ReachesPlus.trans_star h123 h4
  have h_end : ((L <+ [1, 1]) {{C}}> (([1, 0] : List (Fin 2))^(d + 1) +> ((1 : Fin 2) >> ([1,
      1, 1] +> default)))) =
      cfg_A a (k + 1) 0 (d + 1) := by
    unfold cfg_A
    rw [ListBlank.append_pow_add_rev _ ([1, 1] : List (Fin 2)) k 1]
    rfl
  rwa [h_end] at h1234

private theorem rule_3 (d : Nat) :
    ∃ cfg', ((cfg_A 0 0 d 0) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  refine ⟨(default {{F}}> ((0 : Fin 2) >> ((1 : Fin 2) >> (([1,
      1] : List (Fin 2))^(d + 3) +> ([1] +> default))))), ?_,
    by bb_halt⟩
  have h_start : cfg_A 0 0 d 0 =
      (default {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ([1, 1, 1] +> default)))) := rfl
  rw [h_start]
  have h1 := step_C_default_to_E d ([1, 1, 1] +> default)
  have h2 := shift_E_11 d (default <+ [0, 1]) ((1 : Fin 2) >> ([1, 1, 1] +> default))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (((default <+ [0, 1]) <+ ([0, 1] : List (Fin 2))^d) {{E}}> ((1 : Fin 2) >> ([1, 1,
      1] +> default)))
      [target]⊢⁺
      (((((default <+ [0, 1]) <+ ([0, 1] : List (Fin 2))^d) <+ [0, 1]) <+ [0,
      1]) {{E}}> default) := by
    bb_steps
  have h123 := ReachesPlus.trans h12 h3
  have h_l : ((((default <+ [0, 1]) <+ ([0, 1] : List (Fin 2))^d) <+ [0, 1]) <+ [0, 1]) =
      ((0 : Fin 2) >> (default <+ ([1, 0] : List (Fin 2))^(d + 3))) := by
    have h_merge : ((((default <+ [0, 1]) <+ ([0, 1] : List (Fin 2))^d) <+ [0, 1]) <+ [0, 1]) =
        ((([0, 1] : List (Fin 2))^(d + 3) +> default)) := by
      have h_d : d + 3 = ((1 + d) + 1) + 1 := by omega
      rw [h_d]
      rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) ((1 + d) + 1) 1]
      rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) (1 + d) 1]
      rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) 1 d]
      rfl
    rw [h_merge, default_append_01_pow (d + 3)]
  rw [h_l] at h123
  have h4 : (((0 : Fin 2) >> (default <+ ([1, 0] : List (Fin 2))^(d + 3))) {{E}}> default)
      [target]⊢⁺
      ((default <+ ([1, 0] : List (Fin 2))^(d + 3)) {{C}}> ((0 : Fin 2) >> ([1] +> default))) := by
    bb_steps
  have h1234 := ReachesPlus.trans h123 h4
  have h5 := shift_C_left_01 (d + 3) default ([1] +> default)
  have h12345 := ReachesPlus.trans_star h1234 h5
  have h6 : (default {{C}}> ((0 : Fin 2) >> (([1, 1] : List (Fin 2))^(d + 3) +> ([1] +> default))))
      [target]⊢⁺
      (default {{F}}> ((0 : Fin 2) >> ((1 : Fin 2) >> (([1,
      1] : List (Fin 2))^(d + 3) +> ([1] +> default))))) := by
    bb_steps
  exact ReachesPlus.trans h12345 h6

private theorem rule_4 (d c : Nat) :
    (cfg_A 0 0 d (c + 1)) [target]⊢⁺ (cfg_A (d + 1) 0 0 (c + 1)) := by
  let R_tail := (([1, 0] : List (Fin 2))^c +> ([1, 1, 1, 1] +> default))
  have h_start : cfg_A 0 0 d (c + 1) =
      (default {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail)))) := by
    unfold cfg_A
    rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) c]
    rfl
  rw [h_start]
  have h1 := step_C_default_to_E d ((0 : Fin 2) >> R_tail)
  have h2 := shift_E_11 d (default <+ [0, 1]) ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (((default <+ [0, 1]) <+ ([0,
      1] : List (Fin 2))^d) {{E}}> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail)))
      [target]⊢⁺
      (((default <+ [0, 1]) <+ ([0,
      1] : List (Fin 2))^d) {{C}}> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail))) := by
    bb_steps
  have h123 := ReachesPlus.trans h12 h3
  have h_end : (((default <+ [0, 1]) <+ ([0,
      1] : List (Fin 2))^d) {{C}}> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail))) =
      cfg_A (d + 1) 0 0 (c + 1) := by
    unfold cfg_A
    have h_d : d + 1 = 1 + d := by omega
    rw [h_d, ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) 1 d]
    rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) c]
    rfl
  rwa [h_end] at h123

private theorem rule_5 (a d : Nat) :
    (cfg_A (a + 1) 0 d 0) [target]⊢⁺ (cfg_A a (d + 2) 0 0) := by
  let L := (([0, 1] : List (Fin 2))^a +> default)
  have h_start : cfg_A (a + 1) 0 d 0 =
      ((L <+ [0, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ([1, 1,
      1] +> default)))) := by
    unfold cfg_A
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a]
    rfl
  rw [h_start]
  have h1 := step_C_01_to_A d L ([1, 1, 1] +> default)
  have h2 := shift_A_11 d L ([1, 1] +> ((1 : Fin 2) >> ([1, 1, 1] +> default)))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : ((L <+ ([1, 1] : List (Fin 2))^d) {{A}}> ([1, 1] +> ((1 : Fin 2) >> ([1, 1,
      1] +> default))))
      [target]⊢⁺
      ((((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) <+ [1, 1]) {{C}}> ([1, 1, 1,
      1] +> default)) := by
    bb_steps
  have h123 := ReachesPlus.trans h12 h3
  have h_end : ((((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) <+ [1, 1]) {{C}}> ([1, 1, 1,
      1] +> default)) =
      cfg_A a (d + 2) 0 0 := by
    unfold cfg_A
    rw [ListBlank.append_pow_add_rev L ([1, 1] : List (Fin 2)) (d + 1) 1]
    rw [ListBlank.append_pow_add_rev L ([1, 1] : List (Fin 2)) d 1]
    rfl
  rwa [h_end] at h123

private theorem rule_6 (a d : Nat) :
    (cfg_A (a + 1) 0 d 1) [target]⊢⁺ (cfg_A a (d + 2) 0 1) := by
  let L := (([0, 1] : List (Fin 2))^a +> default)
  have h_start : cfg_A (a + 1) 0 d 1 =
      ((L <+ [0, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ([0, 1, 1, 1,
      1] +> default)))) := by
    unfold cfg_A
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a]
    rfl
  rw [h_start]
  have h1 := step_C_01_to_A d L ([0, 1, 1, 1, 1] +> default)
  have h2 := shift_A_11 d L ([1, 1] +> ((1 : Fin 2) >> ([0, 1, 1, 1, 1] +> default)))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : ((L <+ ([1, 1] : List (Fin 2))^d) {{A}}> ([1, 1] +> ((1 : Fin 2) >> ([0, 1, 1, 1,
      1] +> default))))
      [target]⊢⁺
      ((((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) <+ [1, 1]) {{C}}> (([1,
      0] : List (Fin 2))^1 +> ([1, 1, 1, 1] +> default))) := by
    bb_steps
  have h123 := ReachesPlus.trans h12 h3
  have h_end : ((((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) <+ [1, 1]) {{C}}> (([1,
      0] : List (Fin 2))^1 +> ([1, 1, 1, 1] +> default))) =
      cfg_A a (d + 2) 0 1 := by
    unfold cfg_A
    rw [ListBlank.append_pow_add_rev L ([1, 1] : List (Fin 2)) (d + 1) 1]
    rw [ListBlank.append_pow_add_rev L ([1, 1] : List (Fin 2)) d 1]
    rfl
  rwa [h_end] at h123

private theorem rule_7 (a d c : Nat) :
    (cfg_A (a + 1) 0 d (c + 2)) [target]⊢⁺ (cfg_A a (d + 1) 2 c) := by
  let L := (([0, 1] : List (Fin 2))^a +> default)
  let R_tail := (([1, 0] : List (Fin 2))^c +> ([1, 1, 1, 1] +> default))
  have h_start : cfg_A (a + 1) 0 d (c + 2) =
      ((L <+ [0, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ([0, 1,
      0] +> R_tail)))) := by
    unfold cfg_A
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a]
    have h_c : c + 2 = 2 + c := by omega
    rw [h_c, ListBlank.append_pow_add ([1, 0] : List (Fin 2)) 2 c]
    rfl
  rw [h_start]
  have h1 := step_C_01_to_A d L ([0, 1, 0] +> R_tail)
  have h2 := shift_A_11 d L ([1, 1] +> ((1 : Fin 2) >> ([0, 1, 0] +> R_tail)))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : ((L <+ ([1, 1] : List (Fin 2))^d) {{A}}> ([1, 1] +> ((1 : Fin 2) >> ([0, 1,
      0] +> R_tail))))
      [target]⊢⁺
      (((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) {{C}}> (([1,
      1] : List (Fin 2))^2 +> R_tail)) := by
    simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h123 := ReachesPlus.trans h12 h3
  have h_end : (((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) {{C}}> (([1,
      1] : List (Fin 2))^2 +> R_tail)) =
      cfg_A a (d + 1) 2 c := by
    unfold cfg_A
    rw [ListBlank.append_pow_add_rev L ([1, 1] : List (Fin 2)) d 1]
    rfl
  rwa [h_end] at h123

private theorem init_reaches_A : (init []) [target]⊢* (cfg_A 0 0 0 1) := by
  refine ReachesPlus.to_star ?_
  unfold init cfg_A
  bb_steps

private theorem step_A_all (a k d c : Nat) :
    ∃ cfg', ((cfg_A a k d c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases k with _ | k'
  · rcases a with _ | a'
    · rcases c with _ | c'
      · obtain ⟨cfg', h_step, h_halt⟩ := rule_3 d
        exact ⟨cfg', h_step, Or.inr h_halt⟩
      · exact ⟨cfg_A (d + 1) 0 0 (c' + 1), rule_4 d c', Or.inl (in_ps_A (d + 1) 0 0 (c' + 1))⟩
    · rcases c with _ | _ | c'
      · exact ⟨cfg_A a' (d + 2) 0 0, rule_5 a' d, Or.inl (in_ps_A a' (d + 2) 0 0)⟩
      · exact ⟨cfg_A a' (d + 2) 0 1, rule_6 a' d, Or.inl (in_ps_A a' (d + 2) 0 1)⟩
      · exact ⟨cfg_A a' (d + 1) 2 c', rule_7 a' d c', Or.inl (in_ps_A a' (d + 1) 2 c')⟩
  · rcases c with _ | c'
    · exact ⟨cfg_A a (k' + 1) 0 (d + 1), rule_2 a k' d, Or.inl (in_ps_A a (k' + 1) 0 (d + 1))⟩
    · exact ⟨cfg_A a k' (d + 2) c', rule_1 a k' d c', Or.inl (in_ps_A a k' (d + 2) c')⟩

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 0 0 0 1, init_reaches_A, in_ps_A 0 0 0 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · rw [eval_pat_A]
    exact step_A_all (vars 0) (vars 1) (vars 2) (vars 3)
  · nomatch h_mem

/-- `1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

inductive State where
  /-- $A(a, k, d, c) := 0^\infty\,(10)^a\,(11)^k\,\mathrm{C}{>}\,(11)^d\,(10)^c\,1111\,0^\infty$. -/
  | mk (a k d c : ℕ)

def start : State := .mk 0 0 0 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .mk a k d c => evalTapePattern pat_A fun i =>
      if i = 0 then a else if i = 1 then k else if i = 2 then d else if i = 3 then c else 0

def next : State → Option State
  | .mk a (k + 1) d (c + 1) => some (.mk a k (d + 2) c)
  | .mk a (k + 1) d 0       => some (.mk a (k + 1) 0 (d + 1))
  | .mk (a + 1) 0 d (c + 2) => some (.mk a (d + 1) 2 c)
  | .mk (a + 1) 0 d 1       => some (.mk a (d + 2) 0 1)
  | .mk (a + 1) 0 d 0       => some (.mk a (d + 2) 0 0)
  | .mk 0 0 d (c + 1)       => some (.mk (d + 1) 0 0 (c + 1))
  | .mk 0 0 _ 0             => none

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine ⟨init_reaches_A, ?_, ?_⟩
  · intro s s' hnext
    match s with
    | .mk 0 0 d (c' + 1) => injection hnext with h; subst h; exact rule_4 d c'
    | .mk (a' + 1) 0 d 0 => injection hnext with h; subst h; exact rule_5 a' d
    | .mk (a' + 1) 0 d 1 => injection hnext with h; subst h; exact rule_6 a' d
    | .mk (a' + 1) 0 d (c' + 2) => injection hnext with h; subst h; exact rule_7 a' d c'
    | .mk a (k' + 1) d 0 => injection hnext with h; subst h; exact rule_2 a k' d
    | .mk a (k' + 1) d (c' + 1) => injection hnext with h; subst h; exact rule_1 a k' d c'
    | .mk 0 0 d 0 => nomatch hnext
  · intro s hnext
    match s with
    | .mk 0 0 d 0             => exact ⟨_, ReachesPlus.to_star (rule_3 d).choose_spec.1,
      (rule_3 d).choose_spec.2⟩
    | .mk a (k + 1) d (c + 1) => nomatch hnext
    | .mk a (k + 1) d 0       => nomatch hnext
    | .mk (a + 1) 0 d (c + 2) => nomatch hnext
    | .mk (a + 1) 0 d 1       => nomatch hnext
    | .mk (a + 1) 0 d 0       => nomatch hnext
    | .mk 0 0 d (c + 1)       => nomatch hnext

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-Like Acceleration -/

private inductive PrevState where
  | D (a d c : ℕ)
  | K (a k c : ℕ)

private def prevStart : PrevState := .D 0 0 1

private def prevToState : PrevState → State
  | .D a d c => .mk a 0 d c
  | .K a k c => .mk a (k + 1) 0 c

private def prevEncode (s : PrevState) : Cfg (Fin 2) (Fin 6) :=
  encode (prevToState s)

private def prevNext : PrevState → Option PrevState
  | .K a k c =>
    if c ≤ k then some (.K a (k - c) (2 * c + 1)) else some (.D a (2 * k + 2) (c - k - 1))
  | .D (a + 1) d 0 => some (.K a (d + 1) 0)
  | .D (a + 1) d (c + 1) =>
    if c ≤ d + 1 then some (.K a (d + 1 - c) (2 * c + 1))
    else some (.D a (2 * d + 4) (c - d - 2))
  | .D 0 d (c + 1) => some (.D (d + 1) 0 (c + 1))
  | .D 0 _ 0 => none

private theorem reaches_drain (a : ℕ) : ∀ (k c d : ℕ),
    CollatzReachesPlus next (.mk a (k + 1) d c)
      (if k + 1 > c then .mk a (k + 1 - c) 0 (d + 2 * c + 1)
       else .mk a 0 (d + 2 * (k + 1)) (c - (k + 1)))
  | k, 0, d => by
    simp only [Nat.succ_pos', ↓reduceIte, Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
    exact .single rfl
  | 0, c + 1, d => by
    have h : ¬ (1 > c + 1) := by omega
    have hsub : c + 1 - 1 = c := by omega
    simp only [h, ↓reduceIte, hsub]
    exact .single rfl
  | k + 1, c + 1, d => by
    have ih := reaches_drain a k c (d + 2)
    refine CollatzReachesPlus.head (s₂ := .mk a (k + 1) (d + 2) c) rfl ?_
    by_cases h : k + 1 > c
    · have h' : k + 2 > c + 1 := by omega
      have h1 : k + 2 - (c + 1) = k + 1 - c := by omega
      have h2 : d + 2 * (c + 1) + 1 = d + 2 + 2 * c + 1 := by omega
      simp only [h, ↓reduceIte] at ih
      simp only [h', ↓reduceIte, h1, h2]
      exact ih.to_star
    · have h' : ¬ (k + 2 > c + 1) := by omega
      have h1 : d + 2 * (k + 2) = d + 2 + 2 * (k + 1) := by omega
      have h2 : c + 1 - (k + 2) = c - (k + 1) := by omega
      simp only [h, ↓reduceIte] at ih
      simp only [h', ↓reduceIte, h1, h2]
      exact ih.to_star

private theorem is_valid_prev_acceleration :
    IsValidAcceleration target prevStart prevEncode prevNext := by
  refine is_valid_acceleration.of_collatz (embed := prevToState)
    (CollatzReachesStar.refl next start) ?_
  rintro (⟨a, d, c⟩ | ⟨a, k, c⟩)
  · rcases a with _ | a <;> rcases c with _ | _ | c
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
    · refine CollatzStepsTo.of_eq ?_
      simp only [prevNext, Nat.zero_le, ↓reduceIte, Nat.sub_zero, Option.map_some]
      rfl
    · have h := reaches_drain a d c 2
      refine CollatzStepsTo.head (s₂ := .mk a (d + 1) 2 c) rfl ?_
      by_cases hc : c ≤ d
      · have hg : d + 1 > c := by omega
        have hc' : c + 1 ≤ d + 1 := by omega
        simp only [hg, ↓reduceIte] at h
        simp only [prevNext, hc', ↓reduceIte, Option.map_some, prevToState]
        rw [show d + 1 - (c + 1) + 1 = d + 1 - c by omega,
          show 2 * (c + 1) + 1 = 2 + 2 * c + 1 by omega]
        exact h
      · have hg : ¬ d + 1 > c := by omega
        have hc' : ¬ c + 1 ≤ d + 1 := by omega
        simp only [hg, ↓reduceIte] at h
        simp only [prevNext, hc', ↓reduceIte, Option.map_some, prevToState]
        rw [show 2 * d + 4 = 2 + 2 * (d + 1) by omega, show c + 1 - d - 2 = c - (d + 1) by omega]
        exact h
  · have h := reaches_drain a k c 0
    by_cases hc : c ≤ k
    · have hg : k + 1 > c := by omega
      simp only [hg, ↓reduceIte] at h
      simp only [prevNext, hc, ↓reduceIte, Option.map_some, prevToState]
      rw [show k - c + 1 = k + 1 - c by omega, show 2 * c + 1 = 0 + 2 * c + 1 by omega]
      exact h
    · have hg : ¬ k + 1 > c := by omega
      simp only [hg, ↓reduceIte] at h
      simp only [prevNext, hc, ↓reduceIte, Option.map_some, prevToState]
      rw [show 2 * k + 2 = 0 + 2 * (k + 1) by omega, show c - k - 1 = c - (k + 1) by omega]
      exact h

/-- High-level symbolic configuration state space for
`1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC`: the two-counter Poincaré section $d = 0$, $k = 0$. -/
inductive HighLevelState where
  /-- $D(a, c) := A(a, 0, 0, c) = 0^\infty\,(10)^a\,\mathrm{C}{>}\,(10)^c\,1111\,0^\infty$. -/
  | D (a c : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $D(0, 1) = A(0, 0, 0, 1)$. -/
def highLevelStart : HighLevelState := .D 0 1

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .D a c => .mk a 0 0 c

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Contract the $K(a, k, c)$ loop until it exits to $D(a, d', c')$, returning $(d', c')$. -/
def evalK (k c : ℕ) : ℕ × ℕ :=
  let c1 := max c 1
  if c1 ≤ k then evalK (k - c1) (2 * c1 + 1)
  else (2 * k + 2, c1 - k - 1)
termination_by k
decreasing_by omega

/-- Contract the $D(a, d, c)$ reduction on $a$ until $a = 0$ and the state returns to $d = 0$
(or halts when $a = 0$ and $c = 0$). -/
def drainD (a d c : ℕ) : Option HighLevelState :=
  if a = 0 then
    if c = 0 then none else some (.D (d + 1) c)
  else
    let nextDC :=
      if c = 0 then evalK (d + 1) 0
      else if c - 1 ≤ d + 1 then evalK (d + 1 - (c - 1)) (2 * (c - 1) + 1)
      else (2 * d + 4, c - 1 - d - 2)
    drainD (a - 1) nextDC.1 nextDC.2
termination_by a
decreasing_by omega

/-- High-level accelerated transition function on $D(a, c)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .D a c => drainD a 0 c

private def toPrev : HighLevelState → PrevState
  | .D a c => .D a 0 c

private theorem reaches_evalK_pos (a : ℕ) :
    ∀ k, ∀ c, c ≠ 0 →
      CollatzReachesPlus prevNext (.K a k c) (.D a (evalK k c).1 (evalK k c).2) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro c hc
    rw [evalK.eq_def]
    have hmax : max c 1 = c := by omega
    simp only [hmax]
    by_cases hck : c ≤ k
    · simp only [hck, ↓reduceIte]
      have h_step : prevNext (.K a k c) = some (.K a (k - c) (2 * c + 1)) := by
        simp [prevNext, hck]
      have h_lt : k - c < k := by omega
      have h_rec := ih (k - c) h_lt (2 * c + 1) (by omega)
      exact CollatzReachesPlus.head h_step h_rec.to_star
    · simp only [hck, ↓reduceIte]
      have h_step : prevNext (.K a k c) = some (.D a (2 * k + 2) (c - k - 1)) := by
        simp [prevNext, hck]
      exact CollatzReachesPlus.single h_step

private theorem reaches_evalK (a k c : ℕ) :
    CollatzReachesPlus prevNext (.K a k c) (.D a (evalK k c).1 (evalK k c).2) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have h_step : prevNext (.K a k 0) = some (.K a k 1) := by
      simp [prevNext]
    have h_eq : evalK k 0 = evalK k 1 := by
      rw [evalK.eq_def, evalK.eq_def]
      simp
    rw [h_eq]
    exact CollatzReachesPlus.head h_step (reaches_evalK_pos a k 1 (by omega)).to_star
  · exact reaches_evalK_pos a k c (Nat.pos_iff_ne_zero.mp hc)

private theorem stepsTo_drainD : ∀ (a d c : ℕ),
    CollatzStepsTo prevNext (.D a d c) ((drainD a d c).map toPrev)
  | 0, d, 0 => by
    rw [drainD.eq_def]
    simp only [↓reduceIte, Option.map_none]
    exact CollatzStepsTo.of_eq rfl
  | 0, d, c + 1 => by
    rw [drainD.eq_def]
    simp only [↓reduceIte, Nat.add_one_ne_zero, Option.map_some, toPrev]
    exact CollatzStepsTo.of_eq rfl
  | a + 1, d, 0 => by
    rw [drainD.eq_def]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have h1 : prevNext (.D (a + 1) d 0) = some (.K a (d + 1) 0) := rfl
    have h2 := reaches_evalK a (d + 1) 0
    have h3 := stepsTo_drainD a (evalK (d + 1) 0).1 (evalK (d + 1) 0).2
    exact CollatzStepsTo.head h1 (CollatzStepsTo.of_reachesStar h2.to_star h3)
  | a + 1, d, c + 1 => by
    rw [drainD.eq_def]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    by_cases hc : c ≤ d + 1
    · simp only [hc, ↓reduceIte]
      have h1 : prevNext (.D (a + 1) d (c + 1)) = some (.K a (d + 1 - c) (2 * c + 1)) := by
        simp [prevNext, hc]
      have h2 := reaches_evalK a (d + 1 - c) (2 * c + 1)
      have h3 := stepsTo_drainD a (evalK (d + 1 - c) (2 * c + 1)).1
        (evalK (d + 1 - c) (2 * c + 1)).2
      exact CollatzStepsTo.head h1 (CollatzStepsTo.of_reachesStar h2.to_star h3)
    · simp only [hc, ↓reduceIte]
      have h1 : prevNext (.D (a + 1) d (c + 1)) = some (.D a (2 * d + 4) (c - d - 2)) := by
        simp [prevNext, hc]
      have h3 := stepsTo_drainD a (2 * d + 4) (c - d - 2)
      exact CollatzStepsTo.head h1 h3

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  have h_enc : (fun u => prevEncode (toPrev u)) = highLevelEncode :=
    funext fun ⟨_, _⟩ => rfl
  rw [← h_enc]
  refine is_valid_prev_acceleration.of_collatz (embed := toPrev)
    (CollatzReachesStar.refl prevNext prevStart) ?_
  rintro ⟨a, c⟩
  exact stepsTo_drainD a 0 c

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

end BusyBeaver.M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC
