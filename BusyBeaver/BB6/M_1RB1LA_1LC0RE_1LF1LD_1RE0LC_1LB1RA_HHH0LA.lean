/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`

We define the configuration for $r \in \lbrace 0, 1 \rbrace$, $b, c \ge 0$, and
$d \in \lbrace 3, 6 \rbrace$:

$$
C_d(r, b, c) := 0^\infty \ 1^{r+1} \ \mathrm{C}{>} \ 00 \ 1^{b+4} \ (01)^c \ 1^d \ 011 \ 0^\infty.
$$

Starting from $C_3(0, 6, 0)$ (reached after 200 steps from the blank tape), writing $s = b + r$ and
$k = \lfloor b / 2 \rfloor$, the intermediate map $T$ is:

$$
\begin{aligned}
T(C_3(r, b, 0)) &= \begin{cases}
  C_3(r, 0, k + 3) & \text{if } b \text{ is even}, \\
  C_3(0, 12, k) & \text{if } b \text{ is odd and } r = 1, \\
  \text{Halt} & \text{if } b \text{ is odd and } r = 0,
\end{cases} \\
T(C_3(r, b, 1)) &= \begin{cases}
  C_6(r, 0, k + 3) & \text{if } b \text{ is odd}, \\
  \text{Halt} & \text{if } b \text{ is even and } r = 0, \\
  C_3(0, 9, 3) & \text{if } b = 0 \text{ and } r = 1, \\
  C_6(0, 12, k - 1) & \text{if } b \ge 2 \text{ is even and } r = 1,
\end{cases} \\
T(C_3(r, b, c + 2)) &= C_3(s \bmod 2, 3\lfloor s / 2 \rfloor + 9, c), \\
T(C_6(r, b, 0)) &= \begin{cases}
  C_3(r, 0, k + 5) & \text{if } b \text{ is odd}, \\
  C_3(0, 12, k + 1) & \text{if } b \text{ is even and } r = 1, \\
  \text{Halt} & \text{if } b \text{ is even and } r = 0,
\end{cases} \\
T(C_6(r, b, 1)) &= C_3(s \bmod 2, 3\lfloor s / 2 \rfloor + 6, 3), \\
T(C_6(r, b, c + 2)) &= C_6(s \bmod 2, 3\lfloor s / 2 \rfloor + 9, c).
\end{aligned}
$$

Contracting the $\lfloor c / 2 \rfloor$-step Syracuse scan $(r, b) \mapsto (s \bmod 2,
3\lfloor s / 2 \rfloor + 9)$ via `syracuseScan` and resolving the terminal $c \bmod 2 \in \{0, 1\}$
step via `finishC3` / `finishC6` (including $C_3(1, 0, 1) \to C_3(0, 9, 3) \to C_3(1, 21, 1) \to
C_6(1, 0, 13)$) restricts the dynamics to a single `ℕ` counter $c$ on the $b \in \{0, 12\}$
Poincaré section (`HighLevelState`: `C3_0 r c`, `C3_12 c`, `C6_0 r c`, `C6_12 c`), starting from
`highLevelStart = .C3_0 false 6`.
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Leftward shift across `1^k` in state `A`. -/
private theorem shift_A_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight A l
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight A
            (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] (ListBlank.append [1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1] : List (Fin 2)) ^ k)
          (ListBlank.append [1] (ListBlank.append [1] r)) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [1] r) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Leftward sweep across `0 1^k` in state `A`. -/
private theorem sweep_A_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [0] l))
        (ListBlank.append [1] r))
      (Cfg.headRight A l
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))) := by
  have h1 := shift_A_left k (ListBlank.append [0] l) r
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0] l)
          (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r)))
        (Cfg.headRight A l
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))) := by
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r) =
          ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r) :=
      ListBlank.append_pow_comm [1] k r
    rw [h_pow, ListBlank.append_pow_succ]
    bb_steps
  exact h1.trans_plus h2

/-- Rightward shift loop across `1^k` behind `011` in state `A`. -/
private theorem shift_A_right_loop (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l
        (ListBlank.append [0, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [0, 1, 1] r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r)))
          (Cfg.headRight A
            (ListBlank.append [1] l)
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ k) r))) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Rightward sweep across `0 1^(k + 2)` in state `A`. -/
private theorem sweep_A_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A l
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) r)))
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l)))
        r) := by
  have h_split :
      ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) r) =
        ListBlank.append [0, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r) := by
    rw [Nat.add_comm k 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 k r]
    rfl
  rw [h_split]
  have h1 := shift_A_right_loop k l r
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
          (ListBlank.append [0, 1, 1] r))
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l)))
          r) := by
    rw [ListBlank.append_pow_succ]
    bb_steps
  exact h1.trans_plus h2

/-- Rightward sweep across `0 1^(k + 2)` starting with `01` on the left. -/
private theorem sweep_A_right_from_01 (k : ℕ) (l₀ r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append [0] l₀))
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) r)))
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) (ListBlank.append [0] l₀))))
        r) := by
  have h1 := sweep_A_right k (ListBlank.append [1] (ListBlank.append [0] l₀)) r
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (k + 1))
        (ListBlank.append [1] (ListBlank.append [0] l₀)) =
        ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) (ListBlank.append [0] l₀) := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rwa [h_l] at h1

/-- Leftward shift across `1^(2 * k)` in state `C`, producing `(01)^k` on the right. -/
private theorem shift_C_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)
        (ListBlank.append [1] r))
      (Cfg.headRight C l
        (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) l =
          ListBlank.append [1] (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)) := by
      have h_eq : 2 * (k + 1) = 2 + 2 * k := by omega
      rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * k) l]
      rfl
    rw [h_l]
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [1] (ListBlank.append [1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)))
            (ListBlank.append [1] r))
          (Cfg.headRight C
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)
            (ListBlank.append [1] (ListBlank.append [0, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [0, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_r] at h3

/-- Full left-right sweep from state `C` reading `00` across `1^m 0 1^(c + 3)`. -/
private theorem sweep_C_00 (m c : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (c + 3))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))
        (ListBlank.append [0, 0] r))
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default)
        (ListBlank.append [0, 0, 1, 1, 1] r)) := by
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (c + 3))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ m) (default : ListBlank (Fin 2)))) =
        ListBlank.append [1] (ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))) := by
    have h_eq : c + 3 = 2 + (c + 1) := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (c + 1)]
    rfl
  rw [h_l]
  have h1 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1] (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))))
          (ListBlank.append [0, 0] r))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))
          (ListBlank.append [1] (ListBlank.append [0, 1, 0] r))) := by
    bb_steps
  have h2 := sweep_A_left (c + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ m) default)
    (ListBlank.append [0, 1, 0] r)
  have h12 := h1.trans h2
  have h3 := sweep_A_right c
    (ListBlank.append (([1] : List (Fin 2)) ^ m) default)
    (ListBlank.append [0, 1, 0] r)
  have h123 := h12.trans h3
  have h_comb :
      ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
        (ListBlank.append (([1] : List (Fin 2)) ^ m) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default := by
    have h_eq : c + 1 + m = m + c + 1 := by omega
    rw [← ListBlank.append_pow_add, h_eq]
  rw [h_comb] at h123
  have h4 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default)))
          (ListBlank.append [0, 1, 0] r))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default)
          (ListBlank.append [0, 0, 1, 1, 1] r)) := by
    bb_steps
  exact h123.trans h4

/-- First canonical tape pattern ($h = 3$):
$C(a, f, g, 3) := 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,00\,1^{f+4}\,(01)^g\,1^3\,011\,0^\infty$. -/
private abbrev pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .sym 1 (.rep [1] 0 .default)
    head  := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
              (.rep [1] 1 (.rep [0, 1] 2
                (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 .default))))))))))))) }

/-- Second canonical tape pattern ($h = 6$):
$C(a, f, g, 6) := 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,00\,1^{f+4}\,(01)^g\,1^6\,011\,0^\infty$. -/
private abbrev pat_B : TapePattern (Fin 2) (Fin 6) :=
  { left  := .sym 1 (.rep [1] 0 .default)
    head  := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
              (.rep [1] 1 (.rep [0, 1] 2
                (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
                  (.sym 0 (.sym 1 (.sym 1 .default)))))))))))))))) }

/-- Closed pattern set for `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` (Level A). -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left  := .sym 1 (.rep [1] 0 .default)
      head  := some SixState.C
      right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
                (.rep [1] 1 (.rep [0, 1] 2
                  (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 .default))))))))))))) }, .true),
   ({ left  := .sym 1 (.rep [1] 0 .default)
      head  := some SixState.C
      right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
                (.rep [1] 1 (.rep [0, 1] 2
                  (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
                    (.sym 0 (.sym 1 (.sym 1 .default)))))))))))))))) }, .true)]

/-- Configuration $C(a, f, g, h)$. -/
private def cfg_C (a f g h : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append [0, 0]
      (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
          (ListBlank.append (([1] : List (Fin 2)) ^ h)
            (ListBlank.append [0, 1, 1] default)))))

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = cfg_C (vars 0) (vars 1) (vars 2) 3 := by
  unfold pat_A cfg_C
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (vars 0) default,
    Nat.add_comm (vars 1) 4, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 (vars 1)]
  rfl

private theorem eval_pat_B (vars : ℕ → ℕ) :
    evalTapePattern pat_B vars = cfg_C (vars 0) (vars 1) (vars 2) 6 := by
  unfold pat_B cfg_C
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (vars 0) default,
    Nat.add_comm (vars 1) 4, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 (vars 1)]
  rfl

private theorem in_ps_A (a f g : ℕ) : IsInPatternSet ps (cfg_C a f g 3) := by
  refine ⟨(pat_A, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => f | 2 => g | _ => 0, ?_, trivial⟩
  rw [eval_pat_A]
  rfl

private theorem in_ps_B (a f g : ℕ) : IsInPatternSet ps (cfg_C a f g 6) := by
  refine ⟨(pat_B, .true), List.Mem.tail _ (List.Mem.head _),
    fun i => match i with | 0 => a | 1 => f | 2 => g | _ => 0, ?_, trivial⟩
  rw [eval_pat_B]
  rfl

private theorem cfg_C_g0_h6 (a f : ℕ) : cfg_C a f 0 6 = cfg_C a (f + 3) 0 3 := by
  unfold cfg_C
  simp only [list_pow_zero, ListBlank.append_nil]
  have h_eq : f + 3 + 4 = (f + 4) + 3 := by omega
  have h_6 :
      ListBlank.append (([1] : List (Fin 2)) ^ 6)
        (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append (([1] : List (Fin 2)) ^ 3)
            (ListBlank.append [0, 1, 1] default)) := by
    rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 3 3]
  rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) (f + 4) 3, h_6]

private theorem rule_dec_a (a f g h : ℕ) :
    ReachesPlus target (cfg_C (a + 2) f g h) (cfg_C a (f + 3) g h) := by
  unfold cfg_C
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (a + 2 + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([1] : List (Fin 2)) ^ (a + 3))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)) := by
    simp
  have h_r2 :
      ListBlank.append [0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (f + 3 + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
            (ListBlank.append (([1] : List (Fin 2)) ^ h)
              (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2)))))) =
        ListBlank.append [0, 0, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default)))) := by
    have h_f : f + 3 + 4 = 3 + (f + 4) := by omega
    rw [h_f, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (f + 4)]
    rfl
  rw [h_l, h_r2]
  have h_step := sweep_C_00 0 a
    (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
        (ListBlank.append (([1] : List (Fin 2)) ^ h)
          (ListBlank.append [0, 1, 1] default))))
  have h_add : 0 + a + 1 = a + 1 := by omega
  rwa [h_add] at h_step

private def cfg_M (a f g h : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [1] (ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
    (ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
          (ListBlank.append (([1] : List (Fin 2)) ^ h)
            (ListBlank.append [0, 1, 1] default)))))

private theorem step_C_a0_to_M (f g h : ℕ) :
    ReachesPlus target (cfg_C 0 f g h) (cfg_M 0 f g h) := by
  unfold cfg_C cfg_M
  bb_steps

private theorem step_C_a1_to_M (f g h : ℕ) :
    ReachesPlus target (cfg_C 1 f g h) (cfg_M 1 f g h) := by
  unfold cfg_C cfg_M
  bb_steps

private theorem step_M_g2 (a f g h : ℕ) :
    ReachesPlus target (cfg_M a f (g + 2) h) (cfg_C (f + 4 + a) 3 g h) := by
  unfold cfg_M
  have h1 := sweep_A_right_from_01 (f + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (g + 2))
      (ListBlank.append (([1] : List (Fin 2)) ^ h)
        (ListBlank.append [0, 1, 1] default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (g + 2))
            (ListBlank.append (([1] : List (Fin 2)) ^ h)
              (ListBlank.append [0, 1, 1] default))))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1 + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
          (ListBlank.append [0, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 4)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
                (ListBlank.append (([1] : List (Fin 2)) ^ h)
                  (ListBlank.append [0, 1, 1] default)))))) := by
    have h_g :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (g + 2))
          (ListBlank.append (([1] : List (Fin 2)) ^ h)
            (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2)))) =
          ListBlank.append [0, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default))) := by
      rw [Nat.add_comm g 2, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 g]
      rfl
    have h_f :
        ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
      have h_eq : f + 4 = 3 + (f + 1) := by omega
      rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (f + 1)]
      rfl
    rw [h_g, h_f]
    bb_steps
  have h12 := h1.trans h2
  have h3 := sweep_C_00 (a + 3) (f + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ 4)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
        (ListBlank.append (([1] : List (Fin 2)) ^ h)
          (ListBlank.append [0, 1, 1] default))))
  have h123 := h12.trans h3
  have h_end :
      Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3 + (f + 1) + 1)) default)
        (ListBlank.append [0, 0, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ 4)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default))))) =
        cfg_C (f + 4 + a) 3 g h := by
    unfold cfg_C
    have h_a : a + 3 + (f + 1) + 1 = f + 4 + a + 1 := by omega
    rw [h_a]
    rfl
  rwa [h_end] at h123

private theorem step_M_g1_h6 (a f : ℕ) :
    ReachesPlus target (cfg_M a f 1 6) (cfg_C (f + 4 + a) 0 3 3) := by
  unfold cfg_M
  have h1 := sweep_A_right_from_01 (f + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
      (ListBlank.append (([1] : List (Fin 2)) ^ 6)
        (ListBlank.append [0, 1, 1] default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([1] : List (Fin 2)) ^ 6)
              (ListBlank.append [0, 1, 1] default))))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1 + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
          (ListBlank.append [0, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ 3)
                (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                  (ListBlank.append [0, 1, 1] default)))))) := by
    have h_f :
        ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
      have h_eq : f + 4 = 3 + (f + 1) := by omega
      rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (f + 1)]
      rfl
    rw [h_f]
    bb_steps
  have h12 := h1.trans h2
  have h3 := sweep_C_00 (a + 3) (f + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ 3)
        (ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append [0, 1, 1] default))))
  have h123 := h12.trans h3
  have h_end :
      Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3 + (f + 1) + 1)) default)
        (ListBlank.append [0, 0, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 3)
              (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                (ListBlank.append [0, 1, 1] default))))) =
        cfg_C (f + 4 + a) 0 3 3 := by
    unfold cfg_C
    have h_a : a + 3 + (f + 1) + 1 = f + 4 + a + 1 := by omega
    rw [h_a]
    rfl
  rwa [h_end] at h123

private def cfg_L (a m h : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append (([1] : List (Fin 2)) ^ (m + 6))
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
    (ListBlank.append [1]
      (ListBlank.append (([1] : List (Fin 2)) ^ h)
        (ListBlank.append [0, 1, 1] default)))

private theorem step_M_g0_h3 (a f : ℕ) :
    ReachesPlus target (cfg_M a f 0 3) (cfg_L a (f + 1) 3) := by
  have h_eq :
      cfg_M a f 0 3 =
        Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 5 + 2))
              (ListBlank.append [0, 1, 1] default))) := by
    unfold cfg_M
    simp only [list_pow_zero, ListBlank.append_nil]
    have h_f : f + 5 + 2 = (f + 4) + 3 := by omega
    rw [h_f, ListBlank.append_pow_add ([1] : List (Fin 2)) (f + 4) 3]
  rw [h_eq]
  have h1 := sweep_A_right_from_01 (f + 5)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
    (ListBlank.append [0, 1, 1] default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 5 + 2))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))))
          (ListBlank.append [0, 1, 1] default))
        (cfg_L a (f + 1) 3) := by
    unfold cfg_L
    have h_f :
        ListBlank.append (([1] : List (Fin 2)) ^ (f + 5 + 2))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
      have h_add : f + 5 + 2 = 6 + (f + 1) := by omega
      rw [h_add, ListBlank.append_pow_add ([1] : List (Fin 2)) 6 (f + 1)]
      rfl
    rw [h_f]
    bb_steps
  exact h1.trans h2

private theorem step_M_g1_h3 (a f : ℕ) :
    ReachesPlus target (cfg_M a f 1 3) (cfg_L a f 6) := by
  unfold cfg_M
  have h1 := sweep_A_right_from_01 (f + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
      (ListBlank.append (([1] : List (Fin 2)) ^ 3)
        (ListBlank.append [0, 1, 1] default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append [0, 1, 1] default))))
        (cfg_L a f 6) := by
    unfold cfg_L
    have h_l1 :
        ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ f)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
      rw [Nat.add_comm f 4, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 f]
      rfl
    have h_l2 :
        ListBlank.append (([1] : List (Fin 2)) ^ (f + 6))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ f)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
      rw [Nat.add_comm f 6, ListBlank.append_pow_add ([1] : List (Fin 2)) 6 f]
      rfl
    rw [h_l1, h_l2]
    bb_steps
  exact h1.trans h2

private theorem step_L_odd (a k h : ℕ) :
    ReachesPlus target (cfg_L a (2 * k + 1) h) (cfg_C a 0 (k + 3) h) := by
  unfold cfg_L
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1 + 6))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 3)))
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
    have h_eq : 2 * k + 1 + 6 = 2 * (k + 3) + 1 := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (k + 3)) 1]
  rw [h_l]
  have h1 := shift_C_left (k + 3)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
    (ListBlank.append (([1] : List (Fin 2)) ^ h) (ListBlank.append [0, 1, 1] default))
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3))
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default)))))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)))
          (ListBlank.append [0, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3))
                (ListBlank.append (([1] : List (Fin 2)) ^ h)
                  (ListBlank.append [0, 1, 1] default)))))) := by
    simp only [list_pow_zero, list_pow_one, ListBlank.append_nil, ListBlank.append_cons,
      ListBlank.cons_zero_default]
    bb_steps
  have h12 := h1.trans_plus h2
  have h3 := sweep_C_00 0 a
    (ListBlank.append (([1] : List (Fin 2)) ^ 1)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3))
        (ListBlank.append (([1] : List (Fin 2)) ^ h)
          (ListBlank.append [0, 1, 1] default))))
  have h123 := h12.trans h3
  have h_end :
      Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (0 + a + 1)) default)
        (ListBlank.append [0, 0, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3))
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default))))) =
        cfg_C a 0 (k + 3) h := by
    unfold cfg_C
    have h_a : 0 + a + 1 = a + 1 := by omega
    rw [h_a]
    rfl
  rwa [h_end] at h123

private theorem step_L_even_a0_halt (k h : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_L 0 (2 * k) h) cfg' ∧ (step target cfg').isNone := by
  unfold cfg_L
  have h_eq : 2 * k + 6 = 2 * (k + 3) := by omega
  rw [h_eq]
  have h1 := shift_C_left (k + 3)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 3) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ h) (ListBlank.append [0, 1, 1] default))
  have h_k :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3))
        (ListBlank.append (([1] : List (Fin 2)) ^ h)
          (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2)))) =
        ListBlank.append [0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ h)
              (ListBlank.append [0, 1, 1] default))) := by
    have h_add : k + 3 = 2 + (k + 1) := by omega
    rw [h_add, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 (k + 1)]
    rfl
  rw [h_k] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 3) default))
          (ListBlank.append [1]
            (ListBlank.append [0, 1, 0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
                (ListBlank.append (([1] : List (Fin 2)) ^ h)
                  (ListBlank.append [0, 1, 1] default))))))
        (Cfg.headRight F default
          (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default))))) := by
    bb_steps
  refine ⟨_, h1.trans_plus h2, ?_⟩
  bb_halt

private theorem step_L_even_a1_zero :
    ReachesPlus target (cfg_L 1 0 6) (cfg_C 6 0 3 3) := by
  unfold cfg_L cfg_C
  bb_steps

private theorem step_L_even_a1_succ (j h : ℕ) :
    ReachesPlus target (cfg_L 1 (2 * (j + 1)) h) (cfg_C 6 3 j h) := by
  unfold cfg_L
  have h_eq : 2 * (j + 1) + 6 = 2 * (j + 4) := by omega
  rw [h_eq]
  have h1 := shift_C_left (j + 4)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 4) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ h) (ListBlank.append [0, 1, 1] default))
  have h_j :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 4))
        (ListBlank.append (([1] : List (Fin 2)) ^ h)
          (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2)))) =
        ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append (([1] : List (Fin 2)) ^ h)
              (ListBlank.append [0, 1, 1] default))) := by
    rw [Nat.add_comm j 4, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 4 j]
    rfl
  rw [h_j] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 4) default))
          (ListBlank.append [1]
            (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ j)
                (ListBlank.append (([1] : List (Fin 2)) ^ h)
                  (ListBlank.append [0, 1, 1] default))))))
        (cfg_C 6 3 j h) := by
    unfold cfg_C
    have h4 : (([1] : List (Fin 2)) ^ 4) = [1, 1, 1, 1] := rfl
    have h7 : (([1] : List (Fin 2)) ^ 7) = [1, 1, 1, 1, 1, 1, 1] := rfl
    rw [h4, h7]
    bb_steps
  exact h1.trans_plus h2

private theorem step_C_h3 (a f g : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C a f g 3) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases a with _ | _ | a'
  · have h0 := step_C_a0_to_M f g 3
    rcases g with _ | _ | g'
    · have h1 := h0.trans (step_M_g0_h3 0 f)
      rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨cfg_C 0 0 (k + 3) 3, h1.trans (step_L_odd 0 k 3),
          Or.inl (in_ps_A 0 0 (k + 3))⟩
      · have h_eq : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
        rw [h_eq] at h1
        obtain ⟨cfg', h2, h_halt⟩ := step_L_even_a0_halt (k + 1) 3
        exact ⟨cfg', h1.trans h2, Or.inr h_halt⟩
    · have h1 := h0.trans (step_M_g1_h3 0 f)
      rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · obtain ⟨cfg', h2, h_halt⟩ := step_L_even_a0_halt k 6
        exact ⟨cfg', h1.trans h2, Or.inr h_halt⟩
      · exact ⟨cfg_C 0 0 (k + 3) 6, h1.trans (step_L_odd 0 k 6),
          Or.inl (in_ps_B 0 0 (k + 3))⟩
    · exact ⟨cfg_C (f + 4 + 0) 3 g' 3, h0.trans (step_M_g2 0 f g' 3),
        Or.inl (in_ps_A (f + 4 + 0) 3 g')⟩
  · have h0 := step_C_a1_to_M f g 3
    rcases g with _ | _ | g'
    · have h1 := h0.trans (step_M_g0_h3 1 f)
      rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨cfg_C 1 0 (k + 3) 3, h1.trans (step_L_odd 1 k 3),
          Or.inl (in_ps_A 1 0 (k + 3))⟩
      · have h_eq : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
        rw [h_eq] at h1
        exact ⟨cfg_C 6 3 k 3, h1.trans (step_L_even_a1_succ k 3),
          Or.inl (in_ps_A 6 3 k)⟩
    · have h1 := h0.trans (step_M_g1_h3 1 f)
      rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rcases k with _ | j
        · exact ⟨cfg_C 6 0 3 3, h1.trans step_L_even_a1_zero,
            Or.inl (in_ps_A 6 0 3)⟩
        · exact ⟨cfg_C 6 3 j 6, h1.trans (step_L_even_a1_succ j 6),
            Or.inl (in_ps_B 6 3 j)⟩
      · exact ⟨cfg_C 1 0 (k + 3) 6, h1.trans (step_L_odd 1 k 6),
          Or.inl (in_ps_B 1 0 (k + 3))⟩
    · exact ⟨cfg_C (f + 4 + 1) 3 g' 3, h0.trans (step_M_g2 1 f g' 3),
        Or.inl (in_ps_A (f + 4 + 1) 3 g')⟩
  · exact ⟨cfg_C a' (f + 3) g 3, rule_dec_a a' f g 3,
      Or.inl (in_ps_A a' (f + 3) g)⟩

private theorem step_C_h6 (a f g : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C a f g 6) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases g with _ | _ | g'
  · rw [cfg_C_g0_h6 a f]
    exact step_C_h3 a (f + 3) 0
  · rcases a with _ | _ | a'
    · exact ⟨cfg_C (f + 4 + 0) 0 3 3,
        (step_C_a0_to_M f 1 6).trans (step_M_g1_h6 0 f),
        Or.inl (in_ps_A (f + 4 + 0) 0 3)⟩
    · exact ⟨cfg_C (f + 4 + 1) 0 3 3,
        (step_C_a1_to_M f 1 6).trans (step_M_g1_h6 1 f),
        Or.inl (in_ps_A (f + 4 + 1) 0 3)⟩
    · exact ⟨cfg_C a' (f + 3) 1 6, rule_dec_a a' f 1 6,
        Or.inl (in_ps_B a' (f + 3) 1)⟩
  · rcases a with _ | _ | a'
    · exact ⟨cfg_C (f + 4 + 0) 3 g' 6,
        (step_C_a0_to_M f (g' + 2) 6).trans (step_M_g2 0 f g' 6),
        Or.inl (in_ps_B (f + 4 + 0) 3 g')⟩
    · exact ⟨cfg_C (f + 4 + 1) 3 g' 6,
        (step_C_a1_to_M f (g' + 2) 6).trans (step_M_g2 1 f g' 6),
        Or.inl (in_ps_B (f + 4 + 1) 3 g')⟩
    · exact ⟨cfg_C a' (f + 3) (g' + 2) 6, rule_dec_a a' f (g' + 2) 6,
        Or.inl (in_ps_B a' (f + 3) (g' + 2))⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_C 4 0 0 3) := by
  have h_init : ReachesPlus target (init []) (cfg_C 4 0 0 3) := by
    unfold cfg_C
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_C 4 0 0 3, init_reaches_start, in_ps_A 4 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl
  · rw [eval_pat_A]
    exact step_C_h3 (vars 0) (vars 1) (vars 2)
  · rw [eval_pat_B]
    exact step_C_h6 (vars 0) (vars 1) (vars 2)

/-- `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B, Box 1) -/

/-- Symbolic configuration state space for `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`. -/
inductive State where
  /-- $C(a, b, c, 3) :=
    0^\infty\,1^{a+1}\,\mathrm{C}{>}\,00\,1^{b+4}\,(01)^c\,1^3\,011\,0^\infty$. -/
  | C_3 (a b c : ℕ)
  /-- $C(a, b, c, 6) :=
    0^\infty\,1^{a+1}\,\mathrm{C}{>}\,00\,1^{b+4}\,(01)^c\,1^6\,011\,0^\infty$. -/
  | C_6 (a b c : ℕ)
  /-- $M(a, b, c, 3)$ for $a \in \{0, 1\}$. -/
  | M_3 (a : Bool) (b c : ℕ)
  /-- $M(a, b, c + 1, 6)$ for $a \in \{0, 1\}$. -/
  | M_6_pos (a : Bool) (b c : ℕ)
  /-- $L(a, b + 1, 3)$ for $a \in \{0, 1\}$. -/
  | L_3 (a : Bool) (b : ℕ)
  /-- $L(a, b, 6)$ for $a \in \{0, 1\}$. -/
  | L_6 (a : Bool) (b : ℕ)

/-- Initial symbolic state $C(4, 0, 0, 3)$, reached after 162 raw TM steps. -/
def start : State := .C_3 4 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C_3 a b c =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
      (ListBlank.append [0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append [0, 1, 1] default)))))
  | .C_6 a b c =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
      (ListBlank.append [0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append (([1] : List (Fin 2)) ^ 6)
              (ListBlank.append [0, 1, 1] default)))))
  | .M_3 a b c =>
    Cfg.headRight SixState.A
      (ListBlank.append [1] (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append [0, 1, 1] default)))))
  | .M_6_pos a b c =>
    Cfg.headRight SixState.A
      (ListBlank.append [1] (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ 6)
              (ListBlank.append [0, 1, 1] default)))))
  | .L_3 a b =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ ((b + 1) + 6))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append [0, 1, 1] default)))
  | .L_6 a b =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ (b + 6))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ 6)
          (ListBlank.append [0, 1, 1] default)))

/-- Accelerated Collatz-like transition function (Box 1). -/
def next : State → Option State
  | .C_3 0 b c => some (.M_3 false b c)
  | .C_3 1 b c => some (.M_3 true b c)
  | .C_3 (a + 2) b c => some (.C_3 a (b + 3) c)
  | .C_6 0 b 0 => some (.M_3 false (b + 3) 0)
  | .C_6 1 b 0 => some (.M_3 true (b + 3) 0)
  | .C_6 0 b (c + 1) => some (.M_6_pos false b c)
  | .C_6 1 b (c + 1) => some (.M_6_pos true b c)
  | .C_6 (a + 2) b c => some (.C_6 a (b + 3) c)
  | .M_3 a b 0 => some (.L_3 a b)
  | .M_3 a b 1 => some (.L_6 a b)
  | .M_3 a b (c + 2) => some (.C_3 (b + 4 + if a then 1 else 0) 3 c)
  | .M_6_pos a b 0 => some (.C_3 (b + 4 + if a then 1 else 0) 0 3)
  | .M_6_pos a b (c + 1) => some (.C_6 (b + 4 + if a then 1 else 0) 3 c)
  | .L_3 a b =>
    if b % 2 = 0 then some (.C_3 (if a then 1 else 0) 0 (b / 2 + 3))
    else if a then some (.C_3 6 3 (b / 2))
    else none
  | .L_6 a b =>
    if b % 2 = 1 then some (.C_6 (if a then 1 else 0) 0 (b / 2 + 3))
    else if !a then none
    else if b = 0 then some (.C_3 6 0 3)
    else some (.C_6 6 3 (b / 2 - 1))

private theorem encode_C_6 (a b c : ℕ) : encode (.C_6 a b c) = cfg_C a b c 6 := rfl
private theorem encode_L_3 (a : Bool) (b : ℕ) :
    encode (.L_3 a b) = cfg_L (if a then 1 else 0) (b + 1) 3 := rfl
private theorem encode_L_6 (a : Bool) (b : ℕ) :
    encode (.L_6 a b) = cfg_L (if a then 1 else 0) b 6 := rfl

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro (⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b⟩ | ⟨a, b⟩) s' hnext
    · rcases a with _ | _ | a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C_a0_to_M b c 3
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C_a1_to_M b c 3
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_dec_a a b c 3
    · rcases a with _ | _ | a
      · rcases c with _ | c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          rw [encode_C_6, cfg_C_g0_h6]
          exact step_C_a0_to_M (b + 3) 0 3
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_a0_to_M b (c + 1) 6
      · rcases c with _ | c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          rw [encode_C_6, cfg_C_g0_h6]
          exact step_C_a1_to_M (b + 3) 0 3
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_a1_to_M b (c + 1) 6
      · rcases c with _ | c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_dec_a a b 0 6
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_dec_a a b (c + 1) 6
    · rcases c with _ | _ | c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_M_g0_h3 (if a then 1 else 0) b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_M_g1_h3 (if a then 1 else 0) b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_M_g2 (if a then 1 else 0) b c 3
    · rcases c with _ | c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_M_g1_h6 (if a then 1 else 0) b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_M_g2 (if a then 1 else 0) b c 6
    · rcases nat_even_or_odd_two_mul b with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hmod : (2 * k) % 2 = 0 := by omega
        have hdiv : (2 * k) / 2 = k := by omega
        simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
        subst hnext
        exact step_L_odd (if a then 1 else 0) k 3
      · have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
        have hdiv : (2 * k + 1) / 2 = k := by omega
        rcases a with _ | _
        · simp [next] at hnext
        · simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          rw [encode_L_3]
          have h_eq : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
          rw [h_eq]
          exact step_L_even_a1_succ k 3
    · rcases nat_even_or_odd_two_mul b with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hmod : (2 * k) % 2 ≠ 1 := by omega
        rcases a with _ | _
        · simp [next] at hnext
        · rcases k with _ | j
          · have hs : s' = .C_3 6 0 3 := by
              change some (.C_3 6 0 3) = some s' at hnext
              exact (Option.some.inj hnext).symm
            subst hs
            exact step_L_even_a1_zero
          · have hne0 : 2 * (j + 1) ≠ 0 := by omega
            have hdiv : 2 * (j + 1) / 2 - 1 = j := by omega
            simp only [next, hmod, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              hne0, hdiv, Option.some.injEq] at hnext
            subst hnext
            exact step_L_even_a1_succ j 6
      · have hmod : (2 * k + 1) % 2 = 1 := by omega
        have hdiv : (2 * k + 1) / 2 = k := by omega
        simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
        subst hnext
        exact step_L_odd (if a then 1 else 0) k 6
  step_none := by
    rintro (⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b⟩ | ⟨a, b⟩) hnext
    · rcases a with _ | _ | a <;> simp [next] at hnext
    · rcases a with _ | _ | a <;> rcases c with _ | c <;> simp [next] at hnext
    · rcases c with _ | _ | c <;> simp [next] at hnext
    · rcases c with _ | c <;> simp [next] at hnext
    · rcases nat_even_or_odd_two_mul b with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have hmod : (2 * k) % 2 = 0 := by omega
        simp [next, hmod] at hnext
      · rcases a with _ | _
        · rw [encode_L_3]
          have h_eq : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
          rw [h_eq]
          obtain ⟨cfg', hp, hh⟩ := step_L_even_a0_halt (k + 1) 3
          exact ⟨cfg', hp.to_star, hh⟩
        · simp [next] at hnext
    · rcases nat_even_or_odd_two_mul b with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rcases a with _ | _
        · rw [encode_L_6]
          obtain ⟨cfg', hp, hh⟩ := step_L_even_a0_halt k 6
          exact ⟨cfg', hp.to_star, hh⟩
        · have hmod : (2 * k) % 2 ≠ 1 := by omega
          simp only [next, hmod, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hnext
          split_ifs at hnext
      · have hmod : (2 * k + 1) % 2 = 1 := by omega
        simp [next, hmod] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-Like Acceleration -/

private inductive PrevState where
  | C_3 (r : Bool) (b c : ℕ)
  | C_6 (r : Bool) (b c : ℕ)

private def prevStart : PrevState := .C_3 false 6 0

private def prevToState : PrevState → State
  | .C_3 r b c => .C_3 (if r then 1 else 0) b c
  | .C_6 r b c => .C_6 (if r then 1 else 0) b c

private def prevEncode (s : PrevState) : Cfg (Fin 2) (Fin 6) :=
  encode (prevToState s)

private def prevNext : PrevState → Option PrevState
  | .C_3 r b 0 =>
    if b % 2 = 0 then some (.C_3 r 0 (b / 2 + 3))
    else if r then some (.C_3 false 12 (b / 2))
    else none
  | .C_3 r b 1 =>
    if b % 2 = 1 then some (.C_6 r 0 (b / 2 + 3))
    else if !r then none
    else if b = 0 then some (.C_3 false 9 3)
    else some (.C_6 false 12 (b / 2 - 1))
  | .C_3 r b (c + 2) =>
    let s := b + if r then 1 else 0
    some (.C_3 (decide (s % 2 = 1)) (3 * (s / 2) + 9) c)
  | .C_6 r b 0 =>
    if b % 2 = 1 then some (.C_3 r 0 (b / 2 + 5))
    else if r then some (.C_3 false 12 (b / 2 + 1))
    else none
  | .C_6 r b 1 =>
    let s := b + if r then 1 else 0
    some (.C_3 (decide (s % 2 = 1)) (3 * (s / 2) + 6) 3)
  | .C_6 r b (c + 2) =>
    let s := b + if r then 1 else 0
    some (.C_6 (decide (s % 2 = 1)) (3 * (s / 2) + 9) c)

private theorem reaches_C3_drain (k : ℕ) (a b c : ℕ) :
    CollatzReachesStar next (.C_3 (2 * k + a) b c) (.C_3 a (b + 3 * k) c) := by
  induction k generalizing b with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    have h_next : next (.C_3 (2 * (k + 1) + a) b c) = some (.C_3 (2 * k + a) (b + 3) c) := by
      have : 2 * (k + 1) + a = (2 * k + a) + 2 := by omega
      rw [this]
      rfl
    have ih' := ih (b + 3)
    have h_arith : b + 3 + 3 * k = b + 3 * (k + 1) := by omega
    rw [h_arith] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem reaches_C6_drain (k : ℕ) (a b c : ℕ) :
    CollatzReachesStar next (.C_6 (2 * k + a) b c) (.C_6 a (b + 3 * k) c) := by
  induction k generalizing b with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    have h_next : next (.C_6 (2 * (k + 1) + a) b c) = some (.C_6 (2 * k + a) (b + 3) c) := by
      have : 2 * (k + 1) + a = (2 * k + a) + 2 := by omega
      rw [this]
      rfl
    have ih' := ih (b + 3)
    have h_arith : b + 3 + 3 * k = b + 3 * (k + 1) := by omega
    rw [h_arith] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem drain_C3 {a b c b' : ℕ} {r : Bool} (hr : (if r then 1 else 0) = a % 2)
    (hb : b' = b + 3 * (a / 2)) :
    CollatzReachesStar next (.C_3 a b c) (prevToState (.C_3 r b' c)) := by
  have h := reaches_C3_drain (a / 2) (a % 2) b c
  rw [Nat.div_add_mod, ← hb, ← hr] at h
  exact h

private theorem drain_C6 {a b c b' : ℕ} {r : Bool} (hr : (if r then 1 else 0) = a % 2)
    (hb : b' = b + 3 * (a / 2)) :
    CollatzReachesStar next (.C_6 a b c) (prevToState (.C_6 r b' c)) := by
  have h := reaches_C6_drain (a / 2) (a % 2) b c
  rw [Nat.div_add_mod, ← hb, ← hr] at h
  exact h

private theorem is_valid_prev_acceleration :
    IsValidAcceleration target prevStart prevEncode prevNext := by
  have h_init : CollatzReachesStar next start (prevToState prevStart) :=
    CollatzReachesStar.head rfl (CollatzReachesStar.head rfl (CollatzReachesStar.refl next _))
  refine is_valid_acceleration.of_collatz (embed := prevToState) h_init ?_
  rintro (⟨r, b, c⟩ | ⟨r, b, c⟩)
  · have h1 (c : ℕ) : next (prevToState (.C_3 r b c)) = some (.M_3 r b c) := by cases r <;> rfl
    match c with
    | 0 =>
      have h2 : next (.M_3 r b 0) = some (.L_3 r b) := rfl
      by_cases hb : b % 2 = 0
      · have h3 : next (.L_3 r b) = some (prevToState (.C_3 r 0 (b / 2 + 3))) := by
          simp [next, hb, prevToState]
        have h4 : prevNext (.C_3 r b 0) = some (.C_3 r 0 (b / 2 + 3)) := by
          simp [prevNext, hb]
        rw [h4]
        exact CollatzStepsTo.head (h1 0) (CollatzStepsTo.head h2 (CollatzStepsTo.of_eq h3))
      · cases r
        · have h3 : next (.L_3 false b) = none := by simp [next, hb]
          have h4 : prevNext (.C_3 false b 0) = none := by simp [prevNext, hb]
          rw [h4]
          exact CollatzStepsTo.head (h1 0) (CollatzStepsTo.head h2 (CollatzStepsTo.of_eq h3))
        · have h3 : next (.L_3 true b) = some (.C_3 6 3 (b / 2)) := by simp [next, hb]
          have h4 : prevNext (.C_3 true b 0) = some (.C_3 false 12 (b / 2)) := by
            simp [prevNext, hb]
          rw [h4]
          exact CollatzReachesPlus.head (h1 0)
            (CollatzReachesStar.head h2 (CollatzReachesStar.head h3 (drain_C3 rfl rfl)))
    | 1 =>
      have h2 : next (.M_3 r b 1) = some (.L_6 r b) := rfl
      by_cases hb : b % 2 = 1
      · have h3 : next (.L_6 r b) = some (prevToState (.C_6 r 0 (b / 2 + 3))) := by
          simp [next, hb, prevToState]
        have h4 : prevNext (.C_3 r b 1) = some (.C_6 r 0 (b / 2 + 3)) := by
          simp [prevNext, hb]
        rw [h4]
        exact CollatzStepsTo.head (h1 1) (CollatzStepsTo.head h2 (CollatzStepsTo.of_eq h3))
      · cases r
        · have h3 : next (.L_6 false b) = none := by simp [next, hb]
          have h4 : prevNext (.C_3 false b 1) = none := by simp [prevNext, hb]
          rw [h4]
          exact CollatzStepsTo.head (h1 1) (CollatzStepsTo.head h2 (CollatzStepsTo.of_eq h3))
        · rcases Nat.eq_zero_or_pos b with rfl | hpos
          · exact CollatzReachesPlus.head (h1 1)
              (CollatzReachesStar.head h2 (CollatzReachesStar.head rfl (drain_C3 rfl rfl)))
          · have h3 : next (.L_6 true b) = some (.C_6 6 3 (b / 2 - 1)) := by
              simp [next, hb, Nat.pos_iff_ne_zero.mp hpos]
            have h4 : prevNext (.C_3 true b 1) = some (.C_6 false 12 (b / 2 - 1)) := by
              simp [prevNext, hb, Nat.pos_iff_ne_zero.mp hpos]
            rw [h4]
            exact CollatzReachesPlus.head (h1 1)
              (CollatzReachesStar.head h2 (CollatzReachesStar.head h3 (drain_C6 rfl rfl)))
    | c + 2 =>
      have h2 : next (.M_3 r b (c + 2)) = some (.C_3 (b + 4 + if r then 1 else 0) 3 c) := rfl
      exact CollatzReachesPlus.head (h1 (c + 2)) (CollatzReachesStar.head h2
        (drain_C3 (by cases r <;> dsimp [prevNext] <;> simp only [decide_eq_true_eq] <;>
            split_ifs <;> omega)
          (by cases r <;> dsimp [prevNext] <;> omega)))
  · match c with
    | 0 =>
      have h1 : next (prevToState (.C_6 r b 0)) = some (.M_3 r (b + 3) 0) := by cases r <;> rfl
      have h2 : next (.M_3 r (b + 3) 0) = some (.L_3 r (b + 3)) := rfl
      by_cases hb : b % 2 = 1
      · have e1 : (b + 3) % 2 = 0 := by omega
        have e2 : (b + 3) / 2 + 3 = b / 2 + 5 := by omega
        have h3 : next (.L_3 r (b + 3)) = some (prevToState (.C_3 r 0 (b / 2 + 5))) := by
          simp [next, e1, e2, prevToState]
        have h4 : prevNext (.C_6 r b 0) = some (.C_3 r 0 (b / 2 + 5)) := by
          simp [prevNext, hb]
        rw [h4]
        exact CollatzStepsTo.head h1 (CollatzStepsTo.head h2 (CollatzStepsTo.of_eq h3))
      · have e1 : ¬(b + 3) % 2 = 0 := by omega
        cases r
        · have h3 : next (.L_3 false (b + 3)) = none := by simp [next, e1]
          have h4 : prevNext (.C_6 false b 0) = none := by simp [prevNext, hb]
          rw [h4]
          exact CollatzStepsTo.head h1 (CollatzStepsTo.head h2 (CollatzStepsTo.of_eq h3))
        · have e2 : (b + 3) / 2 = b / 2 + 1 := by omega
          have h3 : next (.L_3 true (b + 3)) = some (.C_3 6 3 (b / 2 + 1)) := by
            simp [next, e1, e2]
          have h4 : prevNext (.C_6 true b 0) = some (.C_3 false 12 (b / 2 + 1)) := by
            simp [prevNext, hb]
          rw [h4]
          exact CollatzReachesPlus.head h1
            (CollatzReachesStar.head h2 (CollatzReachesStar.head h3 (drain_C3 rfl rfl)))
    | 1 =>
      have h1 : next (prevToState (.C_6 r b 1)) = some (.M_6_pos r b 0) := by cases r <;> rfl
      have h2 : next (.M_6_pos r b 0) = some (.C_3 (b + 4 + if r then 1 else 0) 0 3) := rfl
      exact CollatzReachesPlus.head h1 (CollatzReachesStar.head h2
        (drain_C3 (by cases r <;> dsimp [prevNext] <;> simp only [decide_eq_true_eq] <;>
            split_ifs <;> omega)
          (by cases r <;> dsimp [prevNext] <;> omega)))
    | c + 2 =>
      have h1 : next (prevToState (.C_6 r b (c + 2))) = some (.M_6_pos r b (c + 1)) := by
        cases r <;> rfl
      have h2 : next (.M_6_pos r b (c + 1)) = some (.C_6 (b + 4 + if r then 1 else 0) 3 c) := rfl
      exact CollatzReachesPlus.head h1 (CollatzReachesStar.head h2
        (drain_C6 (by cases r <;> dsimp [prevNext] <;> simp only [decide_eq_true_eq] <;>
            split_ifs <;> omega)
          (by cases r <;> dsimp [prevNext] <;> omega)))

/-- High-level symbolic configuration state space for
`1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`: the single-counter $b \in \{0, 12\}$ Poincaré
section. -/
inductive HighLevelState where
  /-- $C(r, 0, c, 3)$ for $r \in \{0, 1\}$. -/
  | C3_0 (r : Bool) (c : ℕ)
  /-- $C(0, 12, c, 3)$. -/
  | C3_12 (c : ℕ)
  /-- $C(r, 0, c, 6)$ for $r \in \{0, 1\}$. -/
  | C6_0 (r : Bool) (c : ℕ)
  /-- $C(0, 12, c, 6)$. -/
  | C6_12 (c : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $C(0, 0, 6, 3)$. -/
def highLevelStart : HighLevelState := .C3_0 false 6

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .C3_0 r c => .C_3 (if r then 1 else 0) 0 c
  | .C3_12 c => .C_3 0 12 c
  | .C6_0 r c => .C_6 (if r then 1 else 0) 0 c
  | .C6_12 c => .C_6 0 12 c

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Contract $k$ Syracuse-like pairs $c + 2 \mapsto c$ on $(r, b)$ via
$(r, b) \mapsto ((b + r) \bmod 2, 3\lfloor (b + r)/2 \rfloor + 9)$. -/
def syracuseScan (r : Bool) (b k : ℕ) : Bool × ℕ :=
  if k = 0 then (r, b)
  else
    let s := b + if r then 1 else 0
    syracuseScan (decide (s % 2 = 1)) (3 * (s / 2) + 9) (k - 1)
termination_by k
decreasing_by omega

/-- Resolve the terminal $c \in \{0, 1\}$ case of $C_3(r, b, c)$ back onto the $b \in \{0, 12\}$
Poincaré section. -/
def finishC3 (r : Bool) (b rem : ℕ) : Option HighLevelState :=
  if rem = 0 then
    if b % 2 = 0 then some (.C3_0 r (b / 2 + 3))
    else if r then some (.C3_12 (b / 2))
    else none
  else
    if b % 2 = 1 then some (.C6_0 r (b / 2 + 3))
    else if !r then none
    else if b = 0 then some (.C6_0 true 13)
    else some (.C6_12 (b / 2 - 1))

/-- Resolve the terminal $c \in \{0, 1\}$ case of $C_6(r, b, c)$ back onto the $b \in \{0, 12\}$
Poincaré section. -/
def finishC6 (r : Bool) (b rem : ℕ) : Option HighLevelState :=
  if rem = 0 then
    if b % 2 = 1 then some (.C3_0 r (b / 2 + 5))
    else if r then some (.C3_12 (b / 2 + 1))
    else none
  else
    let s := b + if r then 1 else 0
    let s1 := (3 * (s / 2) + 6) + if s % 2 = 1 then 1 else 0
    finishC3 (decide (s1 % 2 = 1)) (3 * (s1 / 2) + 9) 1

/-- High-level accelerated transition function on the single-counter $b \in \{0, 12\}$ Poincaré
section, contracting the Syracuse scan over $\lfloor c / 2 \rfloor$ steps into a single step. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .C3_0 r c => let p := syracuseScan r 0 (c / 2); finishC3 p.1 p.2 (c % 2)
  | .C3_12 c => let p := syracuseScan false 12 (c / 2); finishC3 p.1 p.2 (c % 2)
  | .C6_0 r c => let p := syracuseScan r 0 (c / 2); finishC6 p.1 p.2 (c % 2)
  | .C6_12 c => let p := syracuseScan false 12 (c / 2); finishC6 p.1 p.2 (c % 2)

private def toPrev : HighLevelState → PrevState
  | .C3_0 r c => .C_3 r 0 c
  | .C3_12 c => .C_3 false 12 c
  | .C6_0 r c => .C_6 r 0 c
  | .C6_12 c => .C_6 false 12 c

private theorem reaches_scan_C3 (k : ℕ) (r : Bool) (b rem : ℕ) :
    CollatzReachesStar prevNext (.C_3 r b (2 * k + rem))
      (.C_3 (syracuseScan r b k).1 (syracuseScan r b k).2 rem) := by
  induction k generalizing r b with
  | zero =>
    rw [syracuseScan.eq_def]
    simp only [Nat.mul_zero, Nat.zero_add, ↓reduceIte]
    exact CollatzReachesStar.refl prevNext _
  | succ k ih =>
    rw [syracuseScan.eq_def]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have hc : 2 * (k + 1) + rem = (2 * k + rem) + 2 := by omega
    rw [hc]
    exact CollatzReachesStar.head rfl (ih _ _)

private theorem reaches_scan_C6 (k : ℕ) (r : Bool) (b rem : ℕ) :
    CollatzReachesStar prevNext (.C_6 r b (2 * k + rem))
      (.C_6 (syracuseScan r b k).1 (syracuseScan r b k).2 rem) := by
  induction k generalizing r b with
  | zero =>
    rw [syracuseScan.eq_def]
    simp only [Nat.mul_zero, Nat.zero_add, ↓reduceIte]
    exact CollatzReachesStar.refl prevNext _
  | succ k ih =>
    rw [syracuseScan.eq_def]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have hc : 2 * (k + 1) + rem = (2 * k + rem) + 2 := by omega
    rw [hc]
    exact CollatzReachesStar.head rfl (ih _ _)

private theorem stepsTo_finishC3_0 (r : Bool) (b : ℕ) :
    CollatzStepsTo prevNext (.C_3 r b 0) ((finishC3 r b 0).map toPrev) := by
  by_cases hb : b % 2 = 0
  · simp only [finishC3, hb, ↓reduceIte, Option.map_some, toPrev]
    exact CollatzStepsTo.of_eq (by simp only [prevNext, hb, ↓reduceIte])
  · cases r
    · simp only [finishC3, hb, Bool.false_eq_true, ↓reduceIte, Option.map_none]
      exact CollatzStepsTo.of_eq (by simp only [prevNext, hb, Bool.false_eq_true, ↓reduceIte])
    · simp only [finishC3, hb, ↓reduceIte, Option.map_some, toPrev]
      exact CollatzStepsTo.of_eq (by simp only [prevNext, hb, ↓reduceIte])

private theorem stepsTo_finishC3_1 (r : Bool) (b : ℕ) :
    CollatzStepsTo prevNext (.C_3 r b 1) ((finishC3 r b 1).map toPrev) := by
  by_cases hb : b % 2 = 1
  · simp only [finishC3, Nat.one_ne_zero, hb, ↓reduceIte, Option.map_some, toPrev]
    exact CollatzStepsTo.of_eq (by simp only [prevNext, hb, ↓reduceIte])
  · cases r
    · simp only [finishC3, Nat.one_ne_zero, hb, Bool.not_false, ↓reduceIte, Option.map_none]
      exact CollatzStepsTo.of_eq (by simp only [prevNext, hb, Bool.not_false, ↓reduceIte])
    · rcases Nat.eq_zero_or_pos b with rfl | hpos
      · simp only [finishC3, Nat.one_ne_zero, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          Option.map_some, toPrev]
        exact CollatzStepsTo.head rfl (CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl))
      · have hne : b ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
        simp only [finishC3, Nat.one_ne_zero, hb, Bool.not_true, Bool.false_eq_true, hne,
          ↓reduceIte, Option.map_some, toPrev]
        exact CollatzStepsTo.of_eq
          (by simp only [prevNext, hb, Bool.not_true, Bool.false_eq_true, hne, ↓reduceIte])

private theorem stepsTo_scan_C3 (r : Bool) (b c : ℕ) :
    CollatzStepsTo prevNext (.C_3 r b c)
      ((let p := syracuseScan r b (c / 2); finishC3 p.1 p.2 (c % 2)).map toPrev) := by
  have h_scan := reaches_scan_C3 (c / 2) r b (c % 2)
  rw [Nat.div_add_mod] at h_scan
  have h_mod : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases h_mod with hm | hm
  · rw [hm] at h_scan ⊢
    exact CollatzStepsTo.of_reachesStar h_scan (stepsTo_finishC3_0 _ _)
  · rw [hm] at h_scan ⊢
    exact CollatzStepsTo.of_reachesStar h_scan (stepsTo_finishC3_1 _ _)

private theorem stepsTo_finishC6_0 (r : Bool) (b : ℕ) :
    CollatzStepsTo prevNext (.C_6 r b 0) ((finishC6 r b 0).map toPrev) := by
  by_cases hb : b % 2 = 1
  · simp only [finishC6, hb, ↓reduceIte, Option.map_some, toPrev]
    exact CollatzStepsTo.of_eq (by simp only [prevNext, hb, ↓reduceIte])
  · cases r
    · simp only [finishC6, hb, Bool.false_eq_true, ↓reduceIte, Option.map_none]
      exact CollatzStepsTo.of_eq (by simp only [prevNext, hb, Bool.false_eq_true, ↓reduceIte])
    · simp only [finishC6, hb, ↓reduceIte, Option.map_some, toPrev]
      exact CollatzStepsTo.of_eq (by simp only [prevNext, hb, ↓reduceIte])

private theorem stepsTo_finishC6_1 (r : Bool) (b : ℕ) :
    CollatzStepsTo prevNext (.C_6 r b 1) ((finishC6 r b 1).map toPrev) := by
  let s := b + if r then 1 else 0
  let s1 := (3 * (s / 2) + 6) + if s % 2 = 1 then 1 else 0
  have h1 : prevNext (.C_6 r b 1) = some (.C_3 (decide (s % 2 = 1)) (3 * (s / 2) + 6) 3) := rfl
  have h2 : prevNext (.C_3 (decide (s % 2 = 1)) (3 * (s / 2) + 6) 3) =
      some (.C_3 (decide (s1 % 2 = 1)) (3 * (s1 / 2) + 9) 1) := by
    simp only [prevNext, decide_eq_true_eq, s1]
  have h_fin : finishC6 r b 1 = finishC3 (decide (s1 % 2 = 1)) (3 * (s1 / 2) + 9) 1 := by
    simp only [finishC6, Nat.one_ne_zero, ↓reduceIte, s, s1]
  rw [h_fin]
  exact CollatzStepsTo.head h1 (CollatzStepsTo.head h2 (stepsTo_finishC3_1 _ _))

private theorem stepsTo_scan_C6 (r : Bool) (b c : ℕ) :
    CollatzStepsTo prevNext (.C_6 r b c)
      ((let p := syracuseScan r b (c / 2); finishC6 p.1 p.2 (c % 2)).map toPrev) := by
  have h_scan := reaches_scan_C6 (c / 2) r b (c % 2)
  rw [Nat.div_add_mod] at h_scan
  have h_mod : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases h_mod with hm | hm
  · rw [hm] at h_scan ⊢
    exact CollatzStepsTo.of_reachesStar h_scan (stepsTo_finishC6_0 _ _)
  · rw [hm] at h_scan ⊢
    exact CollatzStepsTo.of_reachesStar h_scan (stepsTo_finishC6_1 _ _)

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  have h_enc : (fun u => prevEncode (toPrev u)) = highLevelEncode :=
    funext fun u => by cases u <;> rfl
  rw [← h_enc]
  refine is_valid_prev_acceleration.of_collatz (embed := toPrev)
    (CollatzReachesStar.single rfl) ?_
  rintro (⟨r, c⟩ | ⟨c⟩ | ⟨r, c⟩ | ⟨c⟩)
  · exact stepsTo_scan_C3 r 0 c
  · exact stepsTo_scan_C3 false 12 c
  · exact stepsTo_scan_C6 r 0 c
  · exact stepsTo_scan_C6 false 12 c

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

end BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA
