/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`

We define the configuration for $a, c \ge 0$:

$$
C(a, c) := 0^\infty \ 1^{a+2} \ \mathrm{E}{>} \ 110 \ 1^{2c+2} \ 0^\infty.
$$

Starting from $C(8, 1)$ (reached after 167 steps from the blank tape), with
$k = \lfloor a / 2 \rfloor$,
the machine follows the map $T$:

$$
T(C(a, c)) = \begin{cases}
  \text{Halt} & \text{if } c = 0, \\
  C(2, k + 3) & \text{if } c = 1 \text{ and } a \text{ is odd}, \\
  C(14, 0) & \text{if } a = 0 \text{ and } c = 1, \\
  C(17, k - 1) & \text{if } a \ge 2 \text{ is even and } c = 1, \\
  C(3a + 20, d - k - 3) & \text{if } c = d + 2 \text{ and } k + 3 \le d, \\
  C(6d + 3(a \bmod 2) + 5, k + 2 - d) & \text{if } c = d + 2 \text{ and } d \le k + 2.
\end{cases}
$$
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Rightward shift across `(11)^k` in state `D`. -/
private theorem shift_D_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight D l (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight D (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight D l (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight D (ListBlank.append [1, 1] l)
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

/-- Rightward shift across `(11)^k` in state `F`. -/
private theorem shift_F_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F l (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight F (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight F l (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight F (ListBlank.append [1, 1] l)
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

/-- Leftward shift of `(11)^k` across `B> 1 1 0 1 1`. -/
private theorem shift_B_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1, 1, 0, 1, 1] r))
      (Cfg.headRight B l
        (ListBlank.append [1, 1, 0, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight B
            (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1, 1, 0, 1, 1] r))
          (Cfg.headRight B
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 1, 0, 1, 1] (ListBlank.append [1, 1] r))) := by
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

/-- Canonical even-left tape pattern
$E_{\mathrm{even}}(a, b, c) :=$
$0^\infty\,(11)^{a+1}\,\mathrm{E}{>}\,(11)^{b+1}\,0\,(11)^{c+1}\,0^\infty$. -/
private abbrev pat_Even : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some E
    right := .sym 1 (.sym 1 (.rep [1, 1] 1 (.sym 0 (.sym 1 (.sym 1 (.rep [1, 1] 2 .default)))))) }

/-- Canonical odd-left tape pattern
$E_{\mathrm{odd}}(a, b, c) :=$
$0^\infty\,(11)^a\,111\,\mathrm{E}{>}\,(11)^{b+1}\,0\,(11)^{c+1}\,0^\infty$. -/
private abbrev pat_Odd : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some E
    right := .sym 1 (.sym 1 (.rep [1, 1] 1 (.sym 0 (.sym 1 (.sym 1 (.rep [1, 1] 2 .default)))))) }

/-- Closed pattern set for `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` (Level A). -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
      head := some SixState.E
      right := .sym 1 (.sym 1 (.rep [1, 1] 1 (.sym 0 (.sym 1 (.sym 1
        (.rep [1, 1] 2 .default)))))) }, .true),
   ({ left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
      head := some SixState.E
      right := .sym 1 (.sym 1 (.rep [1, 1] 1 (.sym 0 (.sym 1 (.sym 1
        (.rep [1, 1] 2 .default)))))) }, .true)]

/-- Configuration $E_{\mathrm{even}}(a, b, c)$. -/
private def cfg_Even (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append [1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [0, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ c) default))))

/-- Configuration $E_{\mathrm{odd}}(a, b, c)$. -/
private def cfg_Odd (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append [1, 1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [0, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ c) default))))

private theorem eval_pat_Even (vars : ℕ → ℕ) :
    evalTapePattern pat_Even vars = cfg_Even (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem eval_pat_Odd (vars : ℕ → ℕ) :
    evalTapePattern pat_Odd vars = cfg_Odd (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_Even (a b c : ℕ) : IsInPatternSet ps (cfg_Even a b c) :=
  ⟨(pat_Even, .true), by simp [ps], fun | 0 => a | 1 => b | _ => c, rfl, trivial⟩

private theorem in_ps_Odd (a b c : ℕ) : IsInPatternSet ps (cfg_Odd a b c) :=
  ⟨(pat_Odd, .true), by simp [ps], fun | 0 => a | 1 => b | _ => c, rfl, trivial⟩

private theorem ones_odd_eq (a : ℕ) (l : ListBlank (Fin 2)) :
    ListBlank.append [1, 1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l) =
      ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1] l)) := by
  change ListBlank.append [1, 1]
    (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l)) = _
  rw [← swap_1_11_pow]

/-- Right-end turnaround from `F> 1 1 0^∞` to `B> 1 1 0 1 1 0^∞`. -/
private theorem step_F_end (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight F l (ListBlank.append [1, 1] default))
      (Cfg.headRight B l (ListBlank.append [1, 1, 0, 1, 1] default)) := by
  bb_steps

/-- Right-end turnaround from `1 D> 1 1 0^∞` to `B> 1 1 0 1 1 0^∞`. -/
private theorem step_D_end (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D (ListBlank.append [1] l) (ListBlank.append [1, 1] default))
      (Cfg.headRight B l (ListBlank.append [1, 1, 0, 1, 1] default)) := by
  bb_steps

/-- Halting transition when `b = 0, c = 0`. -/
private theorem step_b0_c0_halt (l : ListBlank (Fin 2)) :
    ∃ cfg', ReachesPlus target
      (Cfg.headRight E l
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0) default))))) cfg' ∧
      (step target cfg').isNone := by
  refine ⟨Cfg.headRight E (ListBlank.append [1, 1, 1, 1, 1, 1] l) default, ?_, by bb_halt⟩
  simp only [list_pow_zero, ListBlank.append_nil]
  bb_steps

/-- Common prefix when `b = 0, c = 1`: reaches `B> 1 1 0 1 1 0^∞` after prepending `(11)^2`
to the left tape. -/
private theorem step_b0_c1_to_B (a : ℕ) (l_base : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base))
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1) default)))))
      (Cfg.headRight B l_base
        (ListBlank.append [1, 1, 0, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 3)) default))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base))
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
              (ListBlank.append [0, 1, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1) default)))))
        (Cfg.headRight B
          (ListBlank.append [1, 1, 1, 1]
            (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base)))
          (ListBlank.append [1, 1, 0, 1, 1] default)) := by
    simp only [list_pow_zero, list_pow_one, ListBlank.append_nil]
    bb_steps
  have h_l :
      ListBlank.append [1, 1, 1, 1]
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base)) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 3)) l_base := by
    change ListBlank.append (([1, 1] : List (Fin 2)) ^ 2)
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base)) = _
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add]
    have h_add : 2 + 1 + a = a + 3 := by omega
    rw [h_add]
  rw [h_l] at h1
  exact h1.trans_star (shift_B_11 (a + 3) l_base default)

private theorem step_Even_b0_c1 (a : ℕ) :
    ReachesPlus target (cfg_Even a 0 1) (cfg_Odd 2 2 (a + 1)) := by
  have h1 := step_b0_c1_to_B a default
  have h_split :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
            (ListBlank.append [1, 1] default)) := by
    have h_eq : a + 3 = 1 + (a + 1) + 1 := by omega
    rw [h_eq, ListBlank.append_pow_add, ListBlank.append_pow_add, list_pow_one]
  rw [h_split] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight B default
          (ListBlank.append [1, 1, 0, 1, 1]
            (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
                (ListBlank.append [1, 1] default)))))
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1, 1, 1, 1, 1, 1] default)
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
            (ListBlank.append [1, 1] default))) := by
    bb_steps
  have h3 := shift_F_11 (a + 1)
    (ListBlank.append [1, 0, 1, 1, 1, 1, 1, 1] default)
    (ListBlank.append [1, 1] default)
  have h4 := step_F_end
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1))
      (ListBlank.append [1, 0, 1, 1, 1, 1, 1, 1] default))
  have h5 := shift_B_11 (a + 1)
    (ListBlank.append [1, 0, 1, 1, 1, 1, 1, 1] default) default
  have h6 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append [1, 0, 1, 1, 1, 1, 1, 1] default)
          (ListBlank.append [1, 1, 0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default)))
        (cfg_Odd 2 2 (a + 1)) := by
    unfold cfg_Odd
    have h_p2 : (([1, 1] : List (Fin 2)) ^ 2) = [1, 1, 1, 1] := rfl
    rw [h_p2]
    bb_steps
  exact (((h1.trans h2).trans_star h3).trans h4).trans_star h5 |>.trans h6

private theorem step_Odd_b0_c1 (a : ℕ) :
    ReachesPlus target (cfg_Odd a 0 1) (cfg_Even 1 0 (a + 3)) := by
  unfold cfg_Odd
  rw [ones_odd_eq]
  have h1 := step_b0_c1_to_B a (ListBlank.append [1] default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B (ListBlank.append [1] default)
          (ListBlank.append [1, 1, 0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 3)) default)))
        (cfg_Even 1 0 (a + 3)) := by
    unfold cfg_Even
    simp only [list_pow_one, list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h1.trans h2

/-- Common prefix when `b = 0, c = d + 2`: sweeps the right block and returns to `B>` at
`l_base`. -/
private theorem step_b0_c2_to_B (a d : ℕ) (l_base : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base))
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ (d + 2)) default)))))
      (Cfg.headRight B l_base
        (ListBlank.append [1, 1, 0, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 3))
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) default))))) := by
  have h_r :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (d + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [1, 1] default)) := by
    have h_eq : d + 2 = 1 + d + 1 := by omega
    rw [h_eq, ListBlank.append_pow_add, ListBlank.append_pow_add, list_pow_one]
  rw [h_r]
  have h1 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base))
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
              (ListBlank.append [0, 1, 1]
                (ListBlank.append [1, 1]
                  (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
                    (ListBlank.append [1, 1] default)))))))
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1, 1, 1, 1, 1]
            (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base)))
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [1, 1] default))) := by
    simp only [list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := shift_F_11 d
    (ListBlank.append [1, 0, 1, 1, 1, 1, 1]
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base)))
    (ListBlank.append [1, 1] default)
  have h3 := step_F_end
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
      (ListBlank.append [1, 0, 1, 1, 1, 1, 1]
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base))))
  have h4 := shift_B_11 d
    (ListBlank.append [1, 0, 1, 1, 1, 1, 1]
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base)))
    default
  have h5 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append [1, 0, 1, 1, 1, 1, 1]
            (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base)))
          (ListBlank.append [1, 1, 0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) default)))
        (Cfg.headRight B
          (ListBlank.append [1, 1, 1, 1]
            (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base)))
          (ListBlank.append [1, 1, 0, 1, 1]
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) default)))) := by
    bb_steps
  have h_l :
      ListBlank.append [1, 1, 1, 1]
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base)) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 3)) l_base := by
    change ListBlank.append (([1, 1] : List (Fin 2)) ^ 2)
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) l_base)) = _
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add]
    have h_add : 2 + 1 + a = a + 3 := by omega
    rw [h_add]
  rw [h_l] at h5
  have h6 := shift_B_11 (a + 3) l_base
    (ListBlank.append [0, 1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) default))
  exact (((h1.trans_star h2).trans h3).trans_star h4).trans h5 |>.trans_star h6

private theorem step_Even_b0_c2 (a d : ℕ) :
    ReachesPlus target (cfg_Even a 0 (d + 2)) (cfg_Even 1 (a + 3) d) := by
  have h1 := step_b0_c2_to_B a d default
  have h2 :
      ReachesPlus target
        (Cfg.headRight B default
          (ListBlank.append [1, 1, 0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 3))
              (ListBlank.append [0, 1, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) default)))))
        (cfg_Even 1 (a + 3) d) := by
    unfold cfg_Even
    rw [list_pow_one]
    bb_steps
  exact h1.trans h2

private theorem step_Odd_b0_c2 (a d : ℕ) :
    ReachesPlus target (cfg_Odd a 0 (d + 2)) (cfg_Odd 2 (a + 3) d) := by
  unfold cfg_Odd
  rw [ones_odd_eq]
  have h1 := step_b0_c2_to_B a d (ListBlank.append [1] default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B (ListBlank.append [1] default)
          (ListBlank.append [1, 1, 0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 3))
              (ListBlank.append [0, 1, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) default)))))
        (Cfg.headRight E
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ 2)
              (ListBlank.append [1] default)))
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 3))
              (ListBlank.append [0, 1, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) default))))) := by
    have h_p2 : (([1, 1] : List (Fin 2)) ^ 2) = [1, 1, 1, 1] := rfl
    rw [h_p2]
    bb_steps
  exact h1.trans h2

/-- Common transition when `b = bp + 1, c = 0`: transfers `(11)^bp` across the separator and
appends `111` to `l`. -/
private theorem step_b1_c0_gen (bp : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E l
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (bp + 1))
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0) default)))))
      (Cfg.headRight E
        (ListBlank.append [1, 1, 1] l)
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp) default))))) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight E l
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (bp + 1))
              (ListBlank.append [0, 1, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0) default)))))
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1, 1] l)
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
            (ListBlank.append [0, 1, 1] default))) := by
    rw [ListBlank.append_pow_succ]
    simp only [list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := shift_F_11 bp
    (ListBlank.append [1, 0, 1, 1] l)
    (ListBlank.append [0, 1, 1] default)
  have h12 := h1.trans_star h2
  have h_swap :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
        (ListBlank.append [1, 0, 1, 1] l) =
        ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
            (ListBlank.append [0, 1, 1] l)) := by
    change ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
      (ListBlank.append [1] (ListBlank.append [0, 1, 1] l)) = _
    rw [swap_1_11_pow]
  rw [h_swap] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
              (ListBlank.append [0, 1, 1] l)))
          (ListBlank.append [0, 1, 1] default))
        (Cfg.headRight B
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
            (ListBlank.append [0, 1, 1] l))
          (ListBlank.append [1, 1, 0, 1, 1] default)) := by
    bb_steps
  have h4 := shift_B_11 bp (ListBlank.append [0, 1, 1] l) default
  have h5 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append [0, 1, 1] l)
          (ListBlank.append [1, 1, 0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp) default)))
        (Cfg.headRight E
          (ListBlank.append [1, 1, 1] l)
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
              (ListBlank.append [0, 1, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp) default))))) := by
    simp only [list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact ((h12.trans h3).trans_star h4).trans h5

private theorem step_Even_b1_c0 (a bp : ℕ) :
    ReachesPlus target (cfg_Even a (bp + 1) 0) (cfg_Odd (a + 1) 0 bp) := by
  have h := step_b1_c0_gen bp
    (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
  unfold cfg_Even cfg_Odd
  rwa [ListBlank.append_pow_succ]

private theorem step_Odd_b1_c0 (a bp : ℕ) :
    ReachesPlus target (cfg_Odd a (bp + 1) 0) (cfg_Even (a + 2) 0 bp) := by
  have h := step_b1_c0_gen bp
    (ListBlank.append [1, 1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
  have h_l :
      ListBlank.append [1, 1, 1]
        (ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (default : ListBlank (Fin 2)))) =
        ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 2)) default) := by
    change ListBlank.append [1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ 2)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)) = _
    rw [← ListBlank.append_pow_add, Nat.add_comm]
  unfold cfg_Odd cfg_Even
  rwa [h_l] at h

/-- Common diagonal transition when `b = bp + 1, c = cp + 1`: prepends `(11)^3` to `l` and
decrements both `b` and `c`. -/
private theorem step_b1_c1_gen (bp cp : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E l
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (bp + 1))
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ (cp + 1)) default)))))
      (Cfg.headRight E
        (ListBlank.append [1, 1, 1, 1, 1, 1] l)
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ cp) default))))) := by
  have h_r :
      ListBlank.append [0, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (cp + 1)) (default : ListBlank (Fin 2))) =
        ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (cp + 1))
            (ListBlank.append [1, 1] default)) := by
    change ListBlank.append [0]
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (cp + 1)) default)) = _
    rw [← ListBlank.append_pow_succ, ListBlank.append_pow_add, list_pow_one]
  rw [h_r]
  have h1 :
      ReachesPlus target
        (Cfg.headRight E l
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (bp + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ (cp + 1))
                  (ListBlank.append [1, 1] default))))))
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1, 1] l)
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
            (ListBlank.append [0]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ (cp + 1))
                (ListBlank.append [1, 1] default))))) := by
    rw [ListBlank.append_pow_succ]
    bb_steps
  have h2 := shift_F_11 bp
    (ListBlank.append [1, 0, 1, 1] l)
    (ListBlank.append [0]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ (cp + 1))
        (ListBlank.append [1, 1] default)))
  have h3 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
            (ListBlank.append [1, 0, 1, 1] l))
          (ListBlank.append [0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (cp + 1))
              (ListBlank.append [1, 1] default))))
        (Cfg.headRight D
          (ListBlank.append [0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
              (ListBlank.append [1, 0, 1, 1] l)))
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (cp + 1))
            (ListBlank.append [1, 1] default))) := by
    bb_steps
  have h4 := shift_D_11 (cp + 1)
    (ListBlank.append [0]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
        (ListBlank.append [1, 0, 1, 1] l)))
    (ListBlank.append [1, 1] default)
  have h1234 := ((h1.trans_star h2).trans h3).trans_star h4
  have h_l_cp :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (cp + 1))
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
            (ListBlank.append [1, 0, 1, 1] l))) =
        ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ cp)
            (ListBlank.append [1, 0]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
                (ListBlank.append [1, 0, 1, 1] l)))) := by
    rw [ListBlank.append_pow_succ]
    change ListBlank.append [1]
      (ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ cp)
          (ListBlank.append [0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
              (ListBlank.append [1, 0, 1, 1] l))))) = _
    rw [← swap_1_11_pow]
    rfl
  rw [h_l_cp] at h1234
  have h5 := step_D_end
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ cp)
      (ListBlank.append [1, 0]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
          (ListBlank.append [1, 0, 1, 1] l))))
  have h6 := shift_B_11 cp
    (ListBlank.append [1, 0]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
        (ListBlank.append [1, 0, 1, 1] l)))
    default
  have h123456 := (h1234.trans h5).trans_star h6
  have h_l_bp :
      ListBlank.append [1, 0]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
          (ListBlank.append [1, 0, 1, 1] l)) =
        ListBlank.append [1, 0, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
            (ListBlank.append [0, 1, 1] l)) := by
    change ListBlank.append [1, 0]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
        (ListBlank.append [1] (ListBlank.append [0, 1, 1] l))) = _
    rw [swap_1_11_pow]
    rfl
  rw [h_l_bp] at h123456
  have h7 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append [1, 0, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
              (ListBlank.append [0, 1, 1] l)))
          (ListBlank.append [1, 1, 0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ cp) default)))
        (Cfg.headRight B
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
            (ListBlank.append [0, 1, 1] l))
          (ListBlank.append [1, 1, 0, 1, 1]
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ cp) default)))) := by
    bb_steps
  have h8 := shift_B_11 bp
    (ListBlank.append [0, 1, 1] l)
    (ListBlank.append [0, 1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ cp) default))
  have h9 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append [0, 1, 1] l)
          (ListBlank.append [1, 1, 0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
              (ListBlank.append [0, 1, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ cp) default)))))
        (Cfg.headRight E
          (ListBlank.append [1, 1, 1, 1, 1, 1] l)
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ bp)
              (ListBlank.append [0, 1, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ cp) default))))) := by
    bb_steps
  exact ((h123456.trans h7).trans_star h8).trans h9

private theorem step_Even_b1_c1 (a bp cp : ℕ) :
    ReachesPlus target (cfg_Even a (bp + 1) (cp + 1)) (cfg_Even (a + 3) bp cp) := by
  have h := step_b1_c1_gen bp cp
    (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
  have h_l :
      ListBlank.append [1, 1, 1, 1, 1, 1]
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (default : ListBlank (Fin 2)))) =
        ListBlank.append [1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 3)) default) := by
    change ListBlank.append [1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ 3)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)) = _
    rw [← ListBlank.append_pow_add, Nat.add_comm]
  unfold cfg_Even
  rwa [h_l] at h

private theorem step_Odd_b1_c1 (a bp cp : ℕ) :
    ReachesPlus target (cfg_Odd a (bp + 1) (cp + 1)) (cfg_Odd (a + 3) bp cp) := by
  have h := step_b1_c1_gen bp cp
    (ListBlank.append [1, 1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
  have h_l :
      ListBlank.append [1, 1, 1, 1, 1, 1]
        (ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (default : ListBlank (Fin 2)))) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 3)) default) := by
    change ListBlank.append [1, 1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ 3)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)) = _
    rw [← ListBlank.append_pow_add, Nat.add_comm]
  unfold cfg_Odd
  rwa [h_l] at h

private theorem step_Even (a b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_Even a b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | bp
  · rcases c with _ | _ | d
    · obtain ⟨cfg', h_step, h_halt⟩ := step_b0_c0_halt
        (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
      exact ⟨cfg', h_step, Or.inr h_halt⟩
    · exact ⟨cfg_Odd 2 2 (a + 1), step_Even_b0_c1 a, Or.inl (in_ps_Odd 2 2 (a + 1))⟩
    · exact ⟨cfg_Even 1 (a + 3) d, step_Even_b0_c2 a d, Or.inl (in_ps_Even 1 (a + 3) d)⟩
  · rcases c with _ | cp
    · exact ⟨cfg_Odd (a + 1) 0 bp, step_Even_b1_c0 a bp, Or.inl (in_ps_Odd (a + 1) 0 bp)⟩
    · exact ⟨cfg_Even (a + 3) bp cp, step_Even_b1_c1 a bp cp,
        Or.inl (in_ps_Even (a + 3) bp cp)⟩

private theorem step_Odd (a b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_Odd a b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | bp
  · rcases c with _ | _ | d
    · obtain ⟨cfg', h_step, h_halt⟩ := step_b0_c0_halt
        (ListBlank.append [1, 1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
      exact ⟨cfg', h_step, Or.inr h_halt⟩
    · exact ⟨cfg_Even 1 0 (a + 3), step_Odd_b0_c1 a, Or.inl (in_ps_Even 1 0 (a + 3))⟩
    · exact ⟨cfg_Odd 2 (a + 3) d, step_Odd_b0_c2 a d, Or.inl (in_ps_Odd 2 (a + 3) d)⟩
  · rcases c with _ | cp
    · exact ⟨cfg_Even (a + 2) 0 bp, step_Odd_b1_c0 a bp, Or.inl (in_ps_Even (a + 2) 0 bp)⟩
    · exact ⟨cfg_Odd (a + 3) bp cp, step_Odd_b1_c1 a bp cp,
        Or.inl (in_ps_Odd (a + 3) bp cp)⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_Odd 2 2 0) := by
  have h_mid :
      ReachesPlus target (init [])
        (Cfg.headRight E
          (ListBlank.append [1, 1, 1, 1] default)
          (ListBlank.append [1, 1, 1, 1, 1, 1] default)) := by
    bb_steps
  have h_end :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1, 1, 1, 1] default)
          (ListBlank.append [1, 1, 1, 1, 1, 1] default))
        (cfg_Odd 2 2 0) := by
    unfold cfg_Odd
    have h_p2 : (([1, 1] : List (Fin 2)) ^ 2) = [1, 1, 1, 1] := rfl
    rw [h_p2, list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact (h_mid.trans h_end).to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_Odd 2 2 0, init_reaches_start, in_ps_Odd 2 2 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl
  · exact step_Even (vars 0) (vars 1) (vars 2)
  · exact step_Odd (vars 0) (vars 1) (vars 2)

/-- `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B, Box 1) -/

/-- Symbolic configuration state space for `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`. -/
inductive State where
  /-- $C_0(a, b, c) :=
    0^\infty\,(11)^{a+1}\,\mathrm{E}{>}\,(11)^{b+1}\,0\,(11)^{c+1}\,0^\infty$. -/
  | C_0 (a b c : ℕ)
  /-- $C_1(a, b, c) :=
    0^\infty\,(11)^a\,111\,\mathrm{E}{>}\,(11)^{b+1}\,0\,(11)^{c+1}\,0^\infty$. -/
  | C_1 (a b c : ℕ)

/-- Initial symbolic state $C_1(2, 2, 0)$. -/
def start : State := .C_1 2 2 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C_0 a b c =>
    Cfg.headRight SixState.E
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
          (ListBlank.append [0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ c) default))))
  | .C_1 a b c =>
    Cfg.headRight SixState.E
      (ListBlank.append [1, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
          (ListBlank.append [0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ c) default))))

/-- Accelerated Collatz-like transition function (Box 1). -/
def next : State → Option State
  | .C_0 _ 0 0 => none
  | .C_0 a 0 1 => some (.C_1 2 2 (a + 1))
  | .C_0 a 0 (d + 2) => some (.C_0 1 (a + 3) d)
  | .C_0 a (b + 1) 0 => some (.C_1 (a + 1) 0 b)
  | .C_0 a (b + 1) (c + 1) => some (.C_0 (a + 3) b c)
  | .C_1 _ 0 0 => none
  | .C_1 a 0 1 => some (.C_0 1 0 (a + 3))
  | .C_1 a 0 (d + 2) => some (.C_1 2 (a + 3) d)
  | .C_1 a (b + 1) 0 => some (.C_0 (a + 2) 0 b)
  | .C_1 a (b + 1) (c + 1) => some (.C_1 (a + 3) b c)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro (⟨a, b, c⟩ | ⟨a, b, c⟩) s' hnext
    · rcases b with _ | b
      · rcases c with _ | _ | d
        · simp [next] at hnext
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_Even_b0_c1 a
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_Even_b0_c2 a d
      · rcases c with _ | c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_Even_b1_c0 a b
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_Even_b1_c1 a b c
    · rcases b with _ | b
      · rcases c with _ | _ | d
        · simp [next] at hnext
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_Odd_b0_c1 a
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_Odd_b0_c2 a d
      · rcases c with _ | c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_Odd_b1_c0 a b
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_Odd_b1_c1 a b c
  step_none := by
    rintro (⟨a, b, c⟩ | ⟨a, b, c⟩) hnext
    · rcases b with _ | b
      · rcases c with _ | _ | d
        · obtain ⟨cfg', h_plus, h_halt⟩ := step_b0_c0_halt
            (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
          exact ⟨cfg', h_plus.to_star, h_halt⟩
        · simp [next] at hnext
        · simp [next] at hnext
      · rcases c with _ | c <;> simp [next] at hnext
    · rcases b with _ | b
      · rcases c with _ | _ | d
        · obtain ⟨cfg', h_plus, h_halt⟩ := step_b0_c0_halt
            (ListBlank.append [1, 1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
          exact ⟨cfg', h_plus.to_star, h_halt⟩
        · simp [next] at hnext
        · simp [next] at hnext
      · rcases c with _ | c <;> simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-Like Acceleration -/

private inductive MidState where
  | C (a b c : ℕ)

private def midStart : MidState := .C 5 2 0

private def midToState : MidState → State
  | .C a b c => if a % 2 = 0 then .C_0 (a / 2) b c else .C_1 (a / 2) b c

private def midEncode (s : MidState) : Cfg (Fin 2) (Fin 6) :=
  encode (midToState s)

private def midNext : MidState → Option MidState
  | .C _ 0 0 => none
  | .C a 0 1 =>
    if a % 2 = 0 then some (.C 5 2 (a / 2 + 1))
    else some (.C 2 0 (a / 2 + 3))
  | .C a 0 (d + 2) =>
    if a % 2 = 0 then some (.C 2 (a / 2 + 3) d)
    else some (.C 5 (a / 2 + 3) d)
  | .C a (b + 1) c =>
    if b + 1 ≤ c then some (.C (a + 6 * (b + 1)) 0 (c - (b + 1)))
    else some (.C (a + 6 * c + 3) 0 (b - c))

private theorem reaches_C0_diag (k : ℕ) (a b c : ℕ) :
    CollatzReachesStar next (.C_0 a (b + k) (c + k)) (.C_0 (a + 3 * k) b c) := by
  induction k generalizing a with
  | zero =>
    simp only [Nat.add_zero, Nat.mul_zero]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    have h_next : next (.C_0 a (b + (k + 1)) (c + (k + 1))) =
        some (.C_0 (a + 3) (b + k) (c + k)) := rfl
    have ih' := ih (a + 3)
    have h_arith : a + 3 + 3 * k = a + 3 * (k + 1) := by omega
    rw [h_arith] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem reaches_C1_diag (k : ℕ) (a b c : ℕ) :
    CollatzReachesStar next (.C_1 a (b + k) (c + k)) (.C_1 (a + 3 * k) b c) := by
  induction k generalizing a with
  | zero =>
    simp only [Nat.add_zero, Nat.mul_zero]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    have h_next : next (.C_1 a (b + (k + 1)) (c + (k + 1))) =
        some (.C_1 (a + 3) (b + k) (c + k)) := rfl
    have ih' := ih (a + 3)
    have h_arith : a + 3 + 3 * k = a + 3 * (k + 1) := by omega
    rw [h_arith] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem reaches_C0_drain_le (b : ℕ) (a c : ℕ) (hbc : b + 1 ≤ c) :
    CollatzReachesPlus next (.C_0 a (b + 1) c) (.C_0 (a + 3 * (b + 1)) 0 (c - (b + 1))) := by
  have h_head : next (.C_0 a (b + 1) c) = some (.C_0 (a + 3) b (c - 1)) := by
    rcases c with _ | c
    · omega
    · rfl
  have h_star := reaches_C0_diag b (a + 3) 0 (c - (b + 1))
  have h_b : 0 + b = b := by omega
  have h_c : c - (b + 1) + b = c - 1 := by omega
  have h_a : a + 3 + 3 * b = a + 3 * (b + 1) := by omega
  rw [h_b, h_c, h_a] at h_star
  exact CollatzReachesPlus.head h_head h_star

private theorem reaches_C1_drain_le (b : ℕ) (a c : ℕ) (hbc : b + 1 ≤ c) :
    CollatzReachesPlus next (.C_1 a (b + 1) c) (.C_1 (a + 3 * (b + 1)) 0 (c - (b + 1))) := by
  have h_head : next (.C_1 a (b + 1) c) = some (.C_1 (a + 3) b (c - 1)) := by
    rcases c with _ | c
    · omega
    · rfl
  have h_star := reaches_C1_diag b (a + 3) 0 (c - (b + 1))
  have h_b : 0 + b = b := by omega
  have h_c : c - (b + 1) + b = c - 1 := by omega
  have h_a : a + 3 + 3 * b = a + 3 * (b + 1) := by omega
  rw [h_b, h_c, h_a] at h_star
  exact CollatzReachesPlus.head h_head h_star

private theorem reaches_C0_drain_gt (b c : ℕ) (a : ℕ) (hbc : ¬(b + 1 ≤ c)) :
    CollatzReachesPlus next (.C_0 a (b + 1) c) (.C_1 (a + 3 * c + 1) 0 (b - c)) := by
  have h_star := reaches_C0_diag c a (b + 1 - c) 0
  have h_b : b + 1 - c + c = b + 1 := by omega
  have h_c : 0 + c = c := by omega
  rw [h_b, h_c] at h_star
  have h_step : next (.C_0 (a + 3 * c) (b + 1 - c) 0) =
      some (.C_1 (a + 3 * c + 1) 0 (b - c)) := by
    have : b + 1 - c = (b - c) + 1 := by omega
    rw [this]
    rfl
  exact CollatzStepsTo.of_reachesStar h_star (CollatzStepsTo.of_eq h_step)

private theorem reaches_C1_drain_gt (b c : ℕ) (a : ℕ) (hbc : ¬(b + 1 ≤ c)) :
    CollatzReachesPlus next (.C_1 a (b + 1) c) (.C_0 (a + 3 * c + 2) 0 (b - c)) := by
  have h_star := reaches_C1_diag c a (b + 1 - c) 0
  have h_b : b + 1 - c + c = b + 1 := by omega
  have h_c : 0 + c = c := by omega
  rw [h_b, h_c] at h_star
  have h_step : next (.C_1 (a + 3 * c) (b + 1 - c) 0) =
      some (.C_0 (a + 3 * c + 2) 0 (b - c)) := by
    have : b + 1 - c = (b - c) + 1 := by omega
    rw [this]
    rfl
  exact CollatzStepsTo.of_reachesStar h_star (CollatzStepsTo.of_eq h_step)

private theorem is_valid_mid_acceleration :
    IsValidAcceleration target midStart midEncode midNext := by
  refine is_valid_acceleration.of_collatz (embed := midToState)
    (CollatzReachesStar.refl next start) ?_
  rintro ⟨a, b, c⟩
  by_cases ha : a % 2 = 0
  · rcases b with _ | b
    · rcases c with _ | _ | d
      · exact CollatzStepsTo.of_eq (by simp [midToState, midNext, ha, next])
      · exact CollatzStepsTo.of_eq (by simp [midToState, midNext, ha, next])
      · exact CollatzStepsTo.of_eq (by simp [midToState, midNext, ha, next])
    · by_cases hbc : b + 1 ≤ c
      · have h_step := reaches_C0_drain_le b (a / 2) c hbc
        have hmod : (a + 6 * (b + 1)) % 2 = 0 := by omega
        have hdiv : (a + 6 * (b + 1)) / 2 = a / 2 + 3 * (b + 1) := by omega
        dsimp [midNext]
        split_ifs
        simp only [Option.map_some, midToState]
        split_ifs
        rw [hdiv]
        exact h_step
      · have h_step := reaches_C0_drain_gt b c (a / 2) hbc
        have hmod : (a + 6 * c + 3) % 2 ≠ 0 := by omega
        have hdiv : (a + 6 * c + 3) / 2 = a / 2 + 3 * c + 1 := by omega
        dsimp [midNext]
        split_ifs
        simp only [Option.map_some, midToState]
        split_ifs
        rw [hdiv]
        exact h_step
  · rcases b with _ | b
    · rcases c with _ | _ | d
      · exact CollatzStepsTo.of_eq (by simp [midToState, midNext, ha, next])
      · exact CollatzStepsTo.of_eq (by simp [midToState, midNext, ha, next])
      · exact CollatzStepsTo.of_eq (by simp [midToState, midNext, ha, next])
    · by_cases hbc : b + 1 ≤ c
      · have h_step := reaches_C1_drain_le b (a / 2) c hbc
        have hmod : (a + 6 * (b + 1)) % 2 ≠ 0 := by omega
        have hdiv : (a + 6 * (b + 1)) / 2 = a / 2 + 3 * (b + 1) := by omega
        dsimp [midNext]
        split_ifs
        simp only [Option.map_some, midToState]
        split_ifs
        rw [hdiv]
        exact h_step
      · have h_step := reaches_C1_drain_gt b c (a / 2) hbc
        have hmod : (a + 6 * c + 3) % 2 = 0 := by omega
        have hdiv : (a + 6 * c + 3) / 2 = a / 2 + 3 * c + 2 := by omega
        dsimp [midNext]
        split_ifs
        simp only [Option.map_some, midToState]
        split_ifs
        rw [hdiv]
        exact h_step

/-- Single-family high-level symbolic configuration state space for
`1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`. -/
inductive HighLevelState where
  /-- $C(a, c) := 0^\infty\,1^{a+2}\,\mathrm{E}{>}\,110\,1^{2c+2}\,0^\infty$. -/
  | C (a c : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $C(8, 1)$. -/
def highLevelStart : HighLevelState := .C 8 1

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .C a c => if a % 2 = 0 then .C_0 (a / 2) 0 c else .C_1 (a / 2) 0 c

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

private def toMid : HighLevelState → MidState
  | .C a c => .C a 0 c

/-- High-level accelerated transition function on $C(a, c)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .C _ 0 => none
  | .C a 1 =>
    if a % 2 = 1 then some (.C 2 (a / 2 + 3))
    else if a = 0 then some (.C 14 0)
    else some (.C 17 (a / 2 - 1))
  | .C a (d + 2) =>
    let k := a / 2
    if k + 3 ≤ d then some (.C (3 * a + 20) (d - k - 3))
    else some (.C (6 * d + 3 * (a % 2) + 5) (k + 2 - d))

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  have h_init : CollatzReachesStar midNext midStart (toMid highLevelStart) :=
    CollatzReachesStar.head rfl (CollatzReachesStar.refl midNext _)
  refine is_valid_mid_acceleration.of_collatz (embed := toMid) h_init ?_
  rintro ⟨a, c⟩
  rcases c with _ | _ | d
  · exact CollatzStepsTo.of_eq rfl
  · dsimp [toMid, highLevelNext]
    split_ifs with h1 h2
    · have h0 : ¬ (a % 2 = 0) := by omega
      exact CollatzStepsTo.of_eq (by simp [midNext, h0, toMid])
    · subst h2
      exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · have h0 : a % 2 = 0 := by omega
      have h_step1 : midNext (.C a 0 1) = some (.C 5 2 (a / 2 + 1)) := by simp [midNext, h0]
      have h_step2 : midNext (.C 5 2 (a / 2 + 1)) = some (.C 17 0 (a / 2 - 1)) := by
        simp [midNext]
        omega
      exact CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq h_step2)
  · dsimp [toMid, highLevelNext]
    by_cases ha : a % 2 = 0
    · have h_step1 : midNext (.C a 0 (d + 2)) = some (.C 2 ((a / 2 + 2) + 1) d) := by
        simp [midNext, ha]
      split_ifs with hk
      · have h_step2 : midNext (.C 2 ((a / 2 + 2) + 1) d) =
            some (.C (3 * a + 20) 0 (d - a / 2 - 3)) := by
          dsimp only [midNext]
          split_ifs <;> (try simp only [Option.some.injEq, MidState.C.injEq, true_and])
            <;> omega
        exact CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq h_step2)
      · have h_step2 : midNext (.C 2 ((a / 2 + 2) + 1) d) =
            some (.C (6 * d + 3 * (a % 2) + 5) 0 (a / 2 + 2 - d)) := by
          dsimp only [midNext]
          split_ifs <;> (try simp only [Option.some.injEq, MidState.C.injEq, true_and,
            and_true]) <;> omega
        exact CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq h_step2)
    · have h_step1 : midNext (.C a 0 (d + 2)) = some (.C 5 ((a / 2 + 2) + 1) d) := by
        simp [midNext, ha]
      split_ifs with hk
      · have h_step2 : midNext (.C 5 ((a / 2 + 2) + 1) d) =
            some (.C (3 * a + 20) 0 (d - a / 2 - 3)) := by
          dsimp only [midNext]
          split_ifs <;> (try simp only [Option.some.injEq, MidState.C.injEq, true_and])
            <;> omega
        exact CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq h_step2)
      · have h_step2 : midNext (.C 5 ((a / 2 + 2) + 1) d) =
            some (.C (6 * d + 3 * (a % 2) + 5) 0 (a / 2 + 2 - d)) := by
          dsimp only [midNext]
          split_ifs <;> (try simp only [Option.some.injEq, MidState.C.injEq, true_and,
            and_true]) <;> omega
        exact CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq h_step2)

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

end BusyBeaver.M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD
