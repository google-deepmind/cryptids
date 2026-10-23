/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD`
([bbchallenge Wiki](https://wiki.bbchallenge.org/wiki/1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD),
holdout #130, `suspect_122`, analyzed by Polygon).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$E(q, a, b, c) := 0^\infty\,\mathrm{E}{>}\,0\,0^q\,1^a\,0\,1^b\,0\,1^c\,0^\infty \quad (q < 2)$$
at $E(1, 3, 0, 0)$ in 12 steps, and every $E(q, a, b, c)$ with $q \in \{0, 1\}$ advances in
`ReachesPlus` either to another $E(q', a', b', c')$ with $q' \in \{0, 1\}$ or to a halting
configuration (via the intermediate right-sweep family
$F(d, a, b, c) := 0^\infty\,1^{d+1}\,\mathrm{F}{>}\,1^a\,0\,1^b\,0\,1^c\,0^\infty$).

## Collatz-like Acceleration Rules

```text
Consider:
E(q, a, b, c) = 0^inf E> 0 0^q 1^a 0 1^b 0 1^c 0^inf   (q in {0, 1})
F(d, a, b, c) = 0^inf 1^(d+1) F> 1^a 0 1^b 0 1^c 0^inf

E(0, a, b, c)         -> F(0, a, b, c)
E(1, a+1, b, c)       -> F(1, a+1, b, c)
E(1, 0, b+1, c)       -> F(2, b+1, c, 0)
E(1, 0, 0, c+1)       -> E((c+2) % 2, c+2, 3, 0)
E(1, 0, 0, 0)         -> Halt

F(d, 2k+4, b, c)      -> F(d+1, 2k, b+3, c)
F(d, 0, b+1, c)       -> F(d+1, b+1, c, 0)
F(d, 0, 0, c+1)       -> F(d+1, 0, c+1, 0)
F(d, 0, 0, 0)         -> E((d+1) % 2, d+1, 3, 0)
F(d, 1, b, c)         -> Halt
F(0, 2, b, c)         -> E((b+2) % 2, b+2, c+3, 0)
F(1, 2, b, c)         -> E(1, b+4, c, 0)
F(d+2, 2, b, c)       -> E((d+1) % 2, d+1, b+4, c)
F(d, 3, b, c)         -> E((d+b+2) % 2, d+b+2, c+3, 0)
F(0, 2k+5, b, c)      -> Halt
F(1, 2k+5, b, c)      -> E(1, 2k+3, b+6, c)
F(d, 2k+5, b, 0)      -> E((d+1) % 2, d+1, 2k+1, b+3)

Start: E(1, 3, 0, 0), reached after 12 raw TM steps
```

## High-Level Collatz-like Acceleration

Restricting to canonical parity $q = a \bmod 2$ (`E(a, b, c) := E(a \bmod 2, a, b, c)`),
contracting the odd-$a$ drain $E(1, 2k + 5, b, c) \to E(1, 2k + 3, b + 6, c)$ in closed form, and
eliminating the even-block $F$-sweeps via `evalF0`, `evalF1`, and `evalFGe2` yields a
single-family, 3-counter map $T$ on $E(a, b, c)$ starting at $E(3, 0, 0)$:

$$
T(E(a, b, c)) = \begin{cases}
  F_0(\lfloor a / 2 \rfloor, b, c) & \text{if } a \text{ is even}, \\
  \text{Halt} & \text{if } a = 1, \\
  E(b + 3a - 6, c + 3, 0) & \text{if } a \ge 3 \text{ is odd},
\end{cases}
$$

where $F_0(k, b, c)$, $F_1(k, b, c)$, and $F_{\ge 2}(d, k, b, c)$ (corresponding to
$F(0, 2k, b, c)$, $F(1, 2k, b, c)$, and $F(d + 2, 2k, b, c)$) evaluate to $E(a', b', c')$ or
$\text{Halt}$ with termination measure $5k + 3b + 4c$ on $F_{\ge 2}$.
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Sweep Lemmas -/

/-- Rightward shift across `1^k` in state `B` with a trailing `0` on the left tape. -/
private theorem shift_B_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B (ListBlank.append [0] l)
        (ListBlank.append (([1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight B
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ k) l)) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight B (ListBlank.append [0] l)
            (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight B (ListBlank.append [0] (ListBlank.append [1] l))
            (ListBlank.append (([1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward shift across `(11)^k` in state `E`. -/
private theorem shift_E_left_pair (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft E (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft E l (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h_l :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l =
          ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) := by
      rw [ListBlank.append_pow_succ]
    rw [h_l]
    have h1 :
        ReachesPlus target
          (Cfg.headLeft E
            (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)) r)
          (Cfg.headLeft E
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 1] r)) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_r :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] r) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_r] at h3

/-- Leftward shift across `1^(2k)` in state `E`. -/
private theorem shift_E_left_even (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft E (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) r)
      (Cfg.headLeft E l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)) := by
  rw [← one_pow_two_mul k]
  exact shift_E_left_pair k l r

private theorem bounce_B_110 (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight B (ListBlank.append [0] l) (ListBlank.append [1, 1, 0] r))
      (Cfg.headLeft E l (ListBlank.append [0, 1, 1, 1] r)) := by
  bb_steps

private theorem sweep_B_right_bounce (m : ℕ) (l s : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight B (ListBlank.append [0] l)
        (ListBlank.append (([1] : List (Fin 2)) ^ (m + 2)) (ListBlank.append [0] s)))
      (Cfg.headLeft E (ListBlank.append (([1] : List (Fin 2)) ^ m) l)
        (ListBlank.append [0, 1, 1, 1] s)) := by
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (m + 2)) (ListBlank.append [0] s) =
        ListBlank.append (([1] : List (Fin 2)) ^ m) (ListBlank.append [1, 1, 0] s) := by
    rw [ListBlank.append_pow_add ([1] : List (Fin 2)) m 2 (ListBlank.append [0] s)]
    rfl
  rw [h_r]
  have h1 := shift_B_right m l (ListBlank.append [1, 1, 0] s)
  have h2 := bounce_B_110 (ListBlank.append (([1] : List (Fin 2)) ^ m) l) s
  exact h1.trans_plus h2

private theorem turn_E_zero_to_F (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headLeft E (ListBlank.append [0] l) r)
      (Cfg.headRight F (ListBlank.append [1] l) r) := by
  bb_steps

private theorem turn_E_01_to_E (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headLeft E (ListBlank.append [1] (ListBlank.append [0] l)) r)
      (Cfg.headLeft E l (ListBlank.append [0, 1] r)) := by
  bb_steps

private theorem turn_E_default_1_to_E (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headLeft E (ListBlank.append [1] default) r)
      (Cfg.headRight E default (ListBlank.append [0, 0, 1] r)) := by
  bb_steps

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$E(q, a, b, c) := 0^\infty\,\mathrm{E}{>}\,0\,0^q\,1^a\,0\,1^b\,0\,1^c\,0^\infty$. -/
def pat_E : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 0 (.rep [0] 0 (.rep [1] 1 (.sym 0 (.rep [1] 2 (.sym 0 (.rep [1] 3 .default)))))) }

/-- Closed pattern set for `1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_E, .not (.ge_const 0 2))]

/-- Canonical hub configuration $E(q, a, b, c)$. -/
private def cfg_E (q a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E default
    (ListBlank.append [0]
      (ListBlank.append (([0] : List (Fin 2)) ^ q)
        (ListBlank.append (([1] : List (Fin 2)) ^ a)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ b)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))))))

/-- Intermediate right-sweep configuration $F(d, a, b, c)$. -/
private def cfg_F (d a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight F
    (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ a)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ b)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))))

/-- Intermediate right-bounce configuration $B(d, m, n, p)$. -/
private def cfg_B (d m n p : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B
    (ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ m)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ n)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ p) default)))))

private theorem eval_pat_E (vars : ℕ → ℕ) :
    evalTapePattern pat_E vars = cfg_E (vars 0) (vars 1) (vars 2) (vars 3) :=
  rfl

private theorem in_ps_E (q a b c : ℕ) (hq : ¬ (q ≥ 2)) :
    IsInPatternSet ps (cfg_E q a b c) :=
  ⟨(pat_E, .not (.ge_const 0 2)), List.Mem.head _,
    fun i => match i with | 0 => q | 1 => a | 2 => b | 3 => c | _ => 0, rfl, hq⟩

/-! ## Exact Macro-Transition Lemmas -/

/-- Exact left-sweep completion into canonical hub `cfg_E`. -/
private theorem finish_left_E_exact {cfg : Cfg (Fin 2) (Fin 6)} (n b c : ℕ)
    (h : ReachesPlus target cfg
      (Cfg.headLeft E
        (ListBlank.append (([1] : List (Fin 2)) ^ (n + 1)) default)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ b)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))))) :
    ReachesPlus target cfg (cfg_E ((n + 1) % 2) (n + 1) b c) := by
  let r_tail :=
    ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ b)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))
  rcases nat_even_or_odd_two_mul n with ⟨j, hn⟩ | ⟨j, hn⟩
  · have hn1 : n + 1 = 2 * j + 1 := by omega
    have hmod : (n + 1) % 2 = 1 := by omega
    rw [hn1, ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * j) 1 default] at h
    have h2 := shift_E_left_even j
      (ListBlank.append (([1] : List (Fin 2)) ^ 1) default) r_tail
    have h3 := turn_E_default_1_to_E
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j)) r_tail)
    rw [list_pow_one] at h2
    have h123 := (h.trans_star h2).trans h3
    have h_end :
        Cfg.headRight E default
          (ListBlank.append [0, 0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j)) r_tail)) =
          cfg_E 1 (2 * j + 1) b c := by
      unfold cfg_E
      have h_pow : 2 * j + 1 = 1 + 2 * j := by omega
      rw [h_pow, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * j) r_tail]
      rfl
    rw [h_end] at h123
    rw [hmod, hn1]
    exact h123
  · have hn1 : n + 1 = 2 * (j + 1) := by omega
    have hmod : (n + 1) % 2 = 0 := by omega
    rw [hn1] at h
    have h2 := shift_E_left_even (j + 1) default r_tail
    have h12 := h.trans_star h2
    have h_end :
        Cfg.headLeft E default
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (j + 1))) r_tail) =
          cfg_E 0 (2 * (j + 1)) b c := by
      simp [cfg_E, Cfg.headLeft, Cfg.headRight, r_tail]
    rw [h_end] at h12
    rw [hmod, hn1]
    exact h12

/-- Exact transition from `cfg_B d (m' + 2) n p` to canonical hub `cfg_E`. -/
private theorem step_B_ge2_to_E (d m' n p : ℕ) :
    ReachesPlus target (cfg_B d (m' + 2) n p)
      (cfg_E ((d + m' + 1) % 2) (d + m' + 1) (n + 3) p) := by
  unfold cfg_B
  let s :=
    ListBlank.append (([1] : List (Fin 2)) ^ n)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ p) default))
  have h1 := sweep_B_right_bounce m'
    (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default) s
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ m')
        (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ ((d + m') + 1)) default := by
    rw [← ListBlank.append_pow_add]
    exact congrArg (fun k => ListBlank.append (([1] : List (Fin 2)) ^ k) default) (by omega)
  have h_r :
      ListBlank.append [0, 1, 1, 1] s =
        ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (n + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ p) default))) := by
    have hn3 : n + 3 = 3 + n := by omega
    rw [hn3, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 n]
    rfl
  rw [h_l, h_r] at h1
  exact finish_left_E_exact (d + m') (n + 3) p h1

/-- Halting from `cfg_F d 1 b c`. -/
private theorem halt_F_a1 (d b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_F d 1 b c) cfg' ∧ (step target cfg').isNone := by
  have h1 :
      ReachesPlus target (cfg_F d 1 b c)
        (Cfg.headRight D
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ b)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))) := by
    unfold cfg_F
    rw [list_pow_one]
    bb_steps
  refine ⟨_, h1, ?_⟩
  bb_halt

/-- Exact exit from `cfg_F d 3 b c`. -/
private theorem step_F_a3_to_E (d b c : ℕ) :
    ReachesPlus target (cfg_F d 3 b c)
      (cfg_E ((d + b + 2) % 2) (d + b + 2) (c + 3) 0) := by
  have h1 : ReachesPlus target (cfg_F d 3 b c) (cfg_B d (b + 1 + 2) c 0) := by
    unfold cfg_F cfg_B
    have hb : b + 1 + 2 = 3 + b := by omega
    have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [hb, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 b, h3, list_pow_zero,
      ListBlank.append_nil]
    bb_steps
  have h2 := step_B_ge2_to_E d (b + 1) c 0
  have hd : d + (b + 1) + 1 = d + b + 2 := by omega
  rw [hd] at h2
  exact h1.trans h2

/-- Exact exit from `cfg_F 0 2 b c`. -/
private theorem step_F_a2_d0_to_E (b c : ℕ) :
    ReachesPlus target (cfg_F 0 2 b c)
      (cfg_E ((b + 2) % 2) (b + 2) (c + 3) 0) := by
  have h1 : ReachesPlus target (cfg_F 0 2 b c) (cfg_B 0 (b + 1 + 2) c 0) := by
    unfold cfg_F cfg_B
    have hb : b + 1 + 2 = 3 + b := by omega
    have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [hb, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 b, list_pow_one, h2, h3,
      list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := step_B_ge2_to_E 0 (b + 1) c 0
  have hd : 0 + (b + 1) + 1 = b + 2 := by omega
  rw [hd] at h2
  exact h1.trans h2

/-- Exact exit from `cfg_F 1 2 b c`. -/
private theorem step_F_a2_d1_to_E (b c : ℕ) :
    ReachesPlus target (cfg_F 1 2 b c) (cfg_E 1 (b + 4) c 0) := by
  unfold cfg_F cfg_E
  have hb : b + 4 = 4 + b := by omega
  have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  have h4 : (([1] : List (Fin 2)) ^ 4) = [1, 1, 1, 1] := rfl
  rw [hb, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 b, h2, h4, list_pow_one, list_pow_zero,
    ListBlank.append_nil]
  bb_steps

/-- Exact exit from `cfg_F (d + 2) 2 b c`. -/
private theorem step_F_a2_dge2_to_E (d b c : ℕ) :
    ReachesPlus target (cfg_F (d + 2) 2 b c)
      (cfg_E ((d + 1) % 2) (d + 1) (b + 4) c) := by
  have h1 :
      ReachesPlus target (cfg_F (d + 2) 2 b c)
        (Cfg.headLeft E
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))) := by
    unfold cfg_F
    have hd : d + 2 + 1 = 2 + (d + 1) := by omega
    have hb : b + 4 = 4 + b := by omega
    have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    have h4 : (([1] : List (Fin 2)) ^ 4) = [1, 1, 1, 1] := rfl
    rw [hd, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (d + 1) default,
      hb, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 b, h2, h4]
    bb_steps
  exact finish_left_E_exact d (b + 4) c h1

/-- Shift rule from `cfg_F d 0 (b + 1) c` to `cfg_F (d + 1) (b + 1) c 0`. -/
private theorem rule_F_a0_bsucc (d b c : ℕ) :
    ReachesPlus target (cfg_F d 0 (b + 1) c) (cfg_F (d + 1) (b + 1) c 0) := by
  unfold cfg_F
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (d + 1) default]
  repeat rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) b]
  rw [list_pow_zero, ListBlank.append_nil]
  bb_steps

/-- Shift rule from `cfg_F d 0 0 (c + 1)` to `cfg_F (d + 1) 0 (c + 1) 0`. -/
private theorem rule_F_a0_b0_csucc (d c : ℕ) :
    ReachesPlus target (cfg_F d 0 0 (c + 1)) (cfg_F (d + 1) 0 (c + 1) 0) := by
  unfold cfg_F
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (d + 1) default]
  repeat rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c]
  rw [list_pow_zero, ListBlank.append_nil]
  bb_steps

/-- Exact exit from `cfg_F d 0 0 0`. -/
private theorem step_F_a0_b0_c0_to_E (d : ℕ) :
    ReachesPlus target (cfg_F d 0 0 0) (cfg_E ((d + 1) % 2) (d + 1) 3 0) := by
  have h1 :
      ReachesPlus target (cfg_F d 0 0 0)
        (Cfg.headLeft E
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ 0) default))))) := by
    unfold cfg_F
    have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d default, h3, list_pow_zero,
      ListBlank.append_nil]
    bb_steps
  exact finish_left_E_exact d 3 0 h1

private theorem step_F_to_B2 (d m b c : ℕ) :
    ReachesPlus target (cfg_F d (m + 2) b c)
      (Cfg.headRight B
        (ListBlank.append [0]
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)))
        (ListBlank.append (([1] : List (Fin 2)) ^ m)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ b)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))))) := by
  unfold cfg_F
  have hm : m + 2 = 2 + m := by omega
  have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [hm, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 m, h2]
  bb_steps

/-- Even-block reduction `cfg_F d (2k + 4) b c ⊢⁺ cfg_F (d + 1) (2k) (b + 3) c`. -/
private theorem rule_F_even_ge4 (d k b c : ℕ) :
    ReachesPlus target (cfg_F d (2 * k + 4) b c) (cfg_F (d + 1) (2 * k) (b + 3) c) := by
  let l_0 := ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) (default : ListBlank (Fin 2))
  let s :=
    ListBlank.append (([1] : List (Fin 2)) ^ b)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ c) default))
  have h1 := step_F_to_B2 d (2 * k + 2) b c
  have h2 := sweep_B_right_bounce (2 * k) (ListBlank.append [0] l_0) s
  have h12 := h1.trans h2
  have h3 := shift_E_left_even k (ListBlank.append [0] l_0) (ListBlank.append [0, 1, 1, 1] s)
  have h123 := h12.trans_star h3
  have h4 := turn_E_zero_to_F l_0
    (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) (ListBlank.append [0, 1, 1, 1] s))
  have h1234 := h123.trans h4
  have h_end :
      Cfg.headRight F (ListBlank.append [1] l_0)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [0, 1, 1, 1] s)) =
        cfg_F (d + 1) (2 * k) (b + 3) c := by
    unfold cfg_F
    rw [← ListBlank.append_pow_succ ([1] : List (Fin 2)) (d + 1) default]
    have hb3 : b + 3 = 3 + b := by omega
    rw [hb3, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 b]
    rfl
  rwa [h_end] at h1234

private theorem sweep_F_odd_to_E (d k b c : ℕ) :
    ReachesPlus target (cfg_F d (2 * k + 5) b c)
      (Cfg.headLeft E
        (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (b + 3))
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))))) := by
  let l_0 := ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) (default : ListBlank (Fin 2))
  let s :=
    ListBlank.append (([1] : List (Fin 2)) ^ b)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ c) default))
  have h1 := step_F_to_B2 d (2 * k + 3) b c
  have h2 := sweep_B_right_bounce (2 * k + 1) (ListBlank.append [0] l_0) s
  have h12 := h1.trans h2
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) (ListBlank.append [0] l_0) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.append [0] l_0)) := by
    rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 1 (ListBlank.append [0] l_0),
      list_pow_one]
  rw [h_l] at h12
  have h3 := shift_E_left_even k
    (ListBlank.append [1] (ListBlank.append [0] l_0))
    (ListBlank.append [0, 1, 1, 1] s)
  have h123 := h12.trans_star h3
  have h4 := turn_E_01_to_E l_0
    (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) (ListBlank.append [0, 1, 1, 1] s))
  have h1234 := h123.trans h4
  have h_r :
      ListBlank.append [0, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [0, 1, 1, 1] s)) =
        ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (b + 3))
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))) := by
    have hk : 2 * k + 1 = 1 + 2 * k := by omega
    have hb3 : b + 3 = 3 + b := by omega
    rw [hk, ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * k),
      hb3, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 b]
    rfl
  rwa [h_r] at h1234

/-- Exact exit from `cfg_F d (2k + 5) b 0`. -/
private theorem step_F_odd_c0_to_E (d k b : ℕ) :
    ReachesPlus target (cfg_F d (2 * k + 5) b 0)
      (cfg_E ((d + 1) % 2) (d + 1) (2 * k + 1) (b + 3)) := by
  have h1 := sweep_F_odd_to_E d k b 0
  have h_r :
      ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (b + 3))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ 0)
                  (default : ListBlank (Fin 2))))))) =
        ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (b + 3)) default))) := by
    simp
  rw [h_r] at h1
  exact finish_left_E_exact d (2 * k + 1) (b + 3) h1

/-- Halting from `cfg_F 0 (2k + 5) b c`. -/
private theorem halt_F_odd_d0 (k b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_F 0 (2 * k + 5) b c) cfg' ∧
      (step target cfg').isNone := by
  have h1 := sweep_F_odd_to_E 0 k b c
  let r_tail :=
    ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 3))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))
  have h2 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
          (ListBlank.append [0] r_tail))
        (Cfg.headRight D
          (ListBlank.append [0] (ListBlank.append [1, 1] default))
          (ListBlank.append [0] r_tail)) := by
    rw [list_pow_one]
    bb_steps
  refine ⟨_, h1.trans h2, ?_⟩
  bb_halt

/-- Exact transition from `cfg_F 1 (2k + 5) b c` to canonical hub `cfg_E`. -/
private theorem step_F_odd_d1_to_E (k b c : ℕ) :
    ReachesPlus target (cfg_F 1 (2 * k + 5) b c)
      (cfg_E 1 (2 * k + 3) (b + 6) c) := by
  have h1 := sweep_F_odd_to_E 1 k b c
  have h2 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (b + 3))
                  (ListBlank.append [0]
                    (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))))))
        (cfg_B 0 ((2 * k + 2) + 2) (b + 3) c) := by
    unfold cfg_B
    have hk : (2 * k + 2) + 2 = 3 + (2 * k + 1) := by omega
    have h2' : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    have h3' : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [hk, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (2 * k + 1), h2', h3', list_pow_one]
    bb_steps
  have h3 := step_B_ge2_to_E 0 (2 * k + 2) (b + 3) c
  have hmod : (0 + (2 * k + 2) + 1) % 2 = 1 := by omega
  have ha : 0 + (2 * k + 2) + 1 = 2 * k + 3 := by omega
  have hb : (b + 3) + 3 = b + 6 := by omega
  rw [hmod, ha, hb] at h3
  exact (h1.trans h2).trans h3

/-- Entry transition `cfg_E 0 a b c ⊢⁺ cfg_F 0 a b c`. -/
private theorem step_E_q0_to_F (a b c : ℕ) :
    ReachesPlus target (cfg_E 0 a b c) (cfg_F 0 a b c) := by
  unfold cfg_E cfg_F
  rw [list_pow_zero, list_pow_one, ListBlank.append_nil]
  bb_steps

/-- Entry transition `cfg_E 1 (a + 1) b c ⊢⁺ cfg_F 1 (a + 1) b c`. -/
private theorem step_E_q1_asucc_to_F (a b c : ℕ) :
    ReachesPlus target (cfg_E 1 (a + 1) b c) (cfg_F 1 (a + 1) b c) := by
  unfold cfg_E cfg_F
  have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) a, list_pow_one, h2]
  bb_steps

/-- Entry transition `cfg_E 1 0 (b + 1) c ⊢⁺ cfg_F 2 (b + 1) c 0`. -/
private theorem step_E_q1_a0_bsucc_to_F (b c : ℕ) :
    ReachesPlus target (cfg_E 1 0 (b + 1) c) (cfg_F 2 (b + 1) c 0) := by
  unfold cfg_E cfg_F
  have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
  repeat rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) b]
  rw [list_pow_one, list_pow_zero, h3, ListBlank.append_nil]
  bb_steps

/-- Hub-to-hub transition `cfg_E 1 0 0 (c + 1) ⊢⁺ cfg_E ((c + 2) % 2) (c + 2) 3 0`. -/
private theorem accel_E_q1_a0_b0_csucc (c : ℕ) :
    ReachesPlus target (cfg_E 1 0 0 (c + 1))
      (cfg_E ((c + 2) % 2) (c + 2) 3 0) := by
  have h1 : ReachesPlus target (cfg_E 1 0 0 (c + 1)) (cfg_B 1 (c + 2) 0 0) := by
    unfold cfg_E cfg_B
    have hc : c + 2 = 2 + c := by omega
    have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c, hc,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 2 c, h2, list_pow_one, list_pow_zero,
      ListBlank.append_nil]
    bb_steps
  have h2 := step_B_ge2_to_E 1 c 0 0
  have hd : 1 + c + 1 = c + 2 := by omega
  rw [hd] at h2
  exact h1.trans h2

/-- Halting from `cfg_E 1 0 0 0`. -/
private theorem halt_E_q1_a0_b0_c0 :
    ∃ cfg', ReachesPlus target (cfg_E 1 0 0 0) cfg' ∧ (step target cfg').isNone := by
  have h1 :
      ReachesPlus target (cfg_E 1 0 0 0)
        (Cfg.headRight D
          (ListBlank.append [0] (ListBlank.append [1, 1] default))
          (ListBlank.append [0] (ListBlank.append [1, 1, 1] default))) := by
    unfold cfg_E
    rw [list_pow_one, list_pow_zero, ListBlank.append_nil]
    bb_steps
  refine ⟨_, h1, ?_⟩
  bb_halt

private theorem init_reaches_start : ReachesStar target (init []) (cfg_E 1 3 0 0) := by
  have h_init : ReachesPlus target (init []) (cfg_E 1 3 0 0) := by
    unfold cfg_E
    have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [list_pow_one, list_pow_zero, h3, ListBlank.append_nil]
    bb_steps
  exact h_init.to_star

/-! ## Collatz-Like Acceleration (Level B) and Pattern Closure (Level A) -/

/-- Symbolic configuration state space for `1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD`. -/
inductive State where
  /-- Canonical hub configuration
  $E(q, a, b, c) := 0^\infty\,\mathrm{E}{>}\,0\,0^q\,1^a\,0\,1^b\,0\,1^c\,0^\infty$
  with $q \in \{0, 1\}$. -/
  | E (q : Bool) (a b c : ℕ)
  /-- Even-block right-sweep configuration
  $F(d, 2k, b, c) := 0^\infty\,1^{d+1}\,\mathrm{F}{>}\,1^{2k}\,0\,1^b\,0\,1^c\,0^\infty$. -/
  | F_even (d k b c : ℕ)

/-- Initial symbolic state $E(1, 3, 0, 0)$, reached after 12 raw TM steps. -/
def start : State := .E true 3 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .E q a b c =>
    Cfg.headRight SixState.E default
      (ListBlank.append [0]
        (ListBlank.append (([0] : List (Fin 2)) ^ (if q then 1 else 0))
          (ListBlank.append (([1] : List (Fin 2)) ^ a)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ b)
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))))))
  | .F_even d k b c =>
    Cfg.headRight SixState.F
      (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ b)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ c) default)))))

/-- Construct a canonical hub state $E(m \bmod 2, m, b, c)$. -/
def mkE (m b c : ℕ) : State :=
  .E (decide (m % 2 = 1)) m b c

private theorem encode_mkE (m b c : ℕ) :
    encode (mkE m b c) = cfg_E (m % 2) m b c := by
  unfold mkE encode cfg_E
  dsimp only
  have h : (if decide (m % 2 = 1) = true then 1 else 0) = m % 2 := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
  rw [h]

/-- Dispatch from $F(0, a, b, c)$ into `State` or halting (`none`). -/
def enterF_d0 (a b c : ℕ) : Option State :=
  if a % 2 = 0 then
    some (.F_even 0 (a / 2) b c)
  else if a = 1 then
    none
  else if a = 3 then
    some (mkE (b + 2) (c + 3) 0)
  else
    none

/-- Dispatch from $F(1, a, b, c)$ into `State` or halting (`none`). -/
def enterF_d1 (a b c : ℕ) : Option State :=
  if a % 2 = 0 then
    some (.F_even 1 (a / 2) b c)
  else if a = 1 then
    none
  else if a = 3 then
    some (mkE (b + 3) (c + 3) 0)
  else
    some (.E true (a - 2) (b + 6) c)

/-- Dispatch from $F(d, a, b, 0)$ into `State` or halting (`none`). -/
def enterF_c0 (d a b : ℕ) : Option State :=
  if a % 2 = 0 then
    some (.F_even d (a / 2) b 0)
  else if a = 1 then
    none
  else if a = 3 then
    some (mkE (d + b + 2) 3 0)
  else
    some (mkE (d + 1) (a - 4) (b + 3))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .E false a b c => enterF_d0 a b c
  | .E true 0 0 0 => none
  | .E true 0 0 (c + 1) => some (mkE (c + 2) 3 0)
  | .E true 0 (b + 1) c => enterF_c0 2 (b + 1) c
  | .E true (a + 1) b c => enterF_d1 (a + 1) b c
  | .F_even d 0 0 0 => some (mkE (d + 1) 3 0)
  | .F_even d 0 0 (c + 1) => some (.F_even (d + 1) 0 (c + 1) 0)
  | .F_even d 0 (b + 1) c => enterF_c0 (d + 1) (b + 1) c
  | .F_even 0 1 b c => some (mkE (b + 2) (c + 3) 0)
  | .F_even 1 1 b c => some (.E true (b + 4) c 0)
  | .F_even (d + 2) 1 b c => some (mkE (d + 1) (b + 4) c)
  | .F_even d (k + 2) b c => some (.F_even (d + 1) k (b + 3) c)

private theorem enterF_d0_some {cfg : Cfg (Fin 2) (Fin 6)} {a b c : ℕ} {s' : State}
    (hreach : ReachesPlus target cfg (cfg_F 0 a b c))
    (hnext : enterF_d0 a b c = some s') :
    ReachesPlus target cfg (encode s') := by
  unfold enterF_d0 at hnext
  split_ifs at hnext with heven ha1 ha3
  · simp only [Option.some.injEq] at hnext
    subst hnext
    change ReachesPlus target cfg (cfg_F 0 (2 * (a / 2)) b c)
    have ha : 2 * (a / 2) = a := by omega
    rwa [ha]
  · simp only [Option.some.injEq] at hnext
    subst hnext
    subst ha3
    rw [encode_mkE]
    have h2 := step_F_a3_to_E 0 b c
    have hd : 0 + b + 2 = b + 2 := by omega
    rw [hd] at h2
    exact hreach.trans h2

private theorem enterF_d0_none {cfg : Cfg (Fin 2) (Fin 6)} {a b c : ℕ}
    (hreach : ReachesPlus target cfg (cfg_F 0 a b c))
    (hnext : enterF_d0 a b c = none) :
    HaltsFrom target cfg := by
  unfold enterF_d0 at hnext
  split_ifs at hnext with heven ha1 ha3
  · subst ha1
    obtain ⟨cfg', hp, hh⟩ := halt_F_a1 0 b c
    exact ⟨cfg', (hreach.trans hp).to_star, hh⟩
  · have ha : a = 2 * ((a - 5) / 2) + 5 := by omega
    rw [ha] at hreach
    obtain ⟨cfg', hp, hh⟩ := halt_F_odd_d0 ((a - 5) / 2) b c
    exact ⟨cfg', (hreach.trans hp).to_star, hh⟩

private theorem enterF_d1_some {cfg : Cfg (Fin 2) (Fin 6)} {a b c : ℕ} {s' : State}
    (hreach : ReachesPlus target cfg (cfg_F 1 a b c))
    (hnext : enterF_d1 a b c = some s') :
    ReachesPlus target cfg (encode s') := by
  unfold enterF_d1 at hnext
  split_ifs at hnext with heven ha1 ha3
  · simp only [Option.some.injEq] at hnext
    subst hnext
    change ReachesPlus target cfg (cfg_F 1 (2 * (a / 2)) b c)
    have ha : 2 * (a / 2) = a := by omega
    rwa [ha]
  · simp only [Option.some.injEq] at hnext
    subst hnext
    subst ha3
    rw [encode_mkE]
    have h2 := step_F_a3_to_E 1 b c
    have hd : 1 + b + 2 = b + 3 := by omega
    rw [hd] at h2
    exact hreach.trans h2
  · simp only [Option.some.injEq] at hnext
    subst hnext
    change ReachesPlus target cfg (cfg_E 1 (a - 2) (b + 6) c)
    have ha5 : a = 2 * ((a - 5) / 2) + 5 := by omega
    have ha3' : a - 2 = 2 * ((a - 5) / 2) + 3 := by omega
    rw [ha5] at hreach
    rw [ha3']
    exact hreach.trans (step_F_odd_d1_to_E ((a - 5) / 2) b c)

private theorem enterF_d1_none {cfg : Cfg (Fin 2) (Fin 6)} {a b c : ℕ}
    (hreach : ReachesPlus target cfg (cfg_F 1 a b c))
    (hnext : enterF_d1 a b c = none) :
    HaltsFrom target cfg := by
  unfold enterF_d1 at hnext
  split_ifs at hnext with heven ha1 ha3
  subst ha1
  obtain ⟨cfg', hp, hh⟩ := halt_F_a1 1 b c
  exact ⟨cfg', (hreach.trans hp).to_star, hh⟩

private theorem enterF_c0_some {cfg : Cfg (Fin 2) (Fin 6)} {d a b : ℕ} {s' : State}
    (hreach : ReachesPlus target cfg (cfg_F d a b 0))
    (hnext : enterF_c0 d a b = some s') :
    ReachesPlus target cfg (encode s') := by
  unfold enterF_c0 at hnext
  split_ifs at hnext with heven ha1 ha3
  · simp only [Option.some.injEq] at hnext
    subst hnext
    change ReachesPlus target cfg (cfg_F d (2 * (a / 2)) b 0)
    have ha : 2 * (a / 2) = a := by omega
    rwa [ha]
  · simp only [Option.some.injEq] at hnext
    subst hnext
    subst ha3
    rw [encode_mkE]
    exact hreach.trans (step_F_a3_to_E d b 0)
  · simp only [Option.some.injEq] at hnext
    subst hnext
    rw [encode_mkE]
    have ha5 : a = 2 * ((a - 5) / 2) + 5 := by omega
    have ha1' : a - 4 = 2 * ((a - 5) / 2) + 1 := by omega
    rw [ha5] at hreach
    rw [ha1']
    exact hreach.trans (step_F_odd_c0_to_E d ((a - 5) / 2) b)

private theorem enterF_c0_none {cfg : Cfg (Fin 2) (Fin 6)} {d a b : ℕ}
    (hreach : ReachesPlus target cfg (cfg_F d a b 0))
    (hnext : enterF_c0 d a b = none) :
    HaltsFrom target cfg := by
  unfold enterF_c0 at hnext
  split_ifs at hnext with heven ha1 ha3
  subst ha1
  obtain ⟨cfg', hp, hh⟩ := halt_F_a1 d b 0
  exact ⟨cfg', (hreach.trans hp).to_star, hh⟩

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro (⟨q, a, b, c⟩ | ⟨d, k, b, c⟩) s' hnext
    · rcases q with _ | _
      · exact enterF_d0_some (step_E_q0_to_F a b c) hnext
      · rcases a with _ | a'
        · rcases b with _ | b'
          · rcases c with _ | c'
            · simp [next] at hnext
            · simp only [next, Option.some.injEq] at hnext
              subst hnext
              rw [encode_mkE]
              exact accel_E_q1_a0_b0_csucc c'
          · exact enterF_c0_some (step_E_q1_a0_bsucc_to_F b' c) hnext
        · exact enterF_d1_some (step_E_q1_asucc_to_F a' b c) hnext
    · rcases k with _ | _ | k'
      · rcases b with _ | b'
        · rcases c with _ | c'
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            rw [encode_mkE]
            exact step_F_a0_b0_c0_to_E d
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            exact rule_F_a0_b0_csucc d c'
        · exact enterF_c0_some (rule_F_a0_bsucc d b' c) hnext
      · rcases d with _ | _ | d'
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          rw [encode_mkE]
          exact step_F_a2_d0_to_E b c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_F_a2_d1_to_E b c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          rw [encode_mkE]
          exact step_F_a2_dge2_to_E d' b c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_F_even_ge4 d k' b c
  step_none := by
    rintro (⟨q, a, b, c⟩ | ⟨d, k, b, c⟩) hnext
    · rcases q with _ | _
      · exact enterF_d0_none (step_E_q0_to_F a b c) hnext
      · rcases a with _ | a'
        · rcases b with _ | b'
          · rcases c with _ | c'
            · obtain ⟨cfg', hp, hh⟩ := halt_E_q1_a0_b0_c0
              exact ⟨cfg', hp.to_star, hh⟩
            · simp [next] at hnext
          · exact enterF_c0_none (step_E_q1_a0_bsucc_to_F b' c) hnext
        · exact enterF_d1_none (step_E_q1_asucc_to_F a' b c) hnext
    · rcases k with _ | _ | k'
      · rcases b with _ | b'
        · rcases c with _ | c' <;> simp [next] at hnext
        · exact enterF_c0_none (rule_F_a0_bsucc d b' c) hnext
      · rcases d with _ | _ | d' <;> simp [next] at hnext
      · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## Pattern Closure Proof (Level A) -/

private theorem stepsToClosed_of_E {cfg : Cfg (Fin 2) (Fin 6)} (q a b c : ℕ) (hq : ¬ (q ≥ 2))
    (h : ReachesPlus target cfg (cfg_E q a b c)) :
    StepsToClosed target ps cfg :=
  ⟨cfg_E q a b c, h, Or.inl (in_ps_E q a b c hq)⟩

private theorem stepsToClosed_F_a2 (d b c : ℕ) :
    StepsToClosed target ps (cfg_F d 2 b c) := by
  rcases d with _ | _ | d'
  · exact stepsToClosed_of_E _ _ _ _ (by omega) (step_F_a2_d0_to_E b c)
  · exact stepsToClosed_of_E _ _ _ _ (by omega) (step_F_a2_d1_to_E b c)
  · exact stepsToClosed_of_E _ _ _ _ (by omega) (step_F_a2_dge2_to_E d' b c)

private theorem stepsToClosed_F_c0_all (M : ℕ) :
    ∀ a b, 4 * a + 5 * b ≤ M → ∀ d, StepsToClosed target ps (cfg_F d a b 0) := by
  induction M with
  | zero =>
    intro a b hM d
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    exact stepsToClosed_of_E _ _ _ _ (by omega) (step_F_a0_b0_c0_to_E d)
  | succ M ih =>
    intro a b hM d
    rcases Nat.of_le_succ hM with hle | heq
    · exact ih a b hle d
    · rcases nat_even_or_odd_two_mul a with ⟨k, ha⟩ | ⟨k, ha⟩
      · rcases k with _ | _ | k'
        · have ha0 : a = 0 := by omega
          subst ha0
          rcases b with _ | b'
          · exact stepsToClosed_of_E _ _ _ _ (by omega) (step_F_a0_b0_c0_to_E d)
          · exact StepsToClosed.of_reachesPlus (rule_F_a0_bsucc d b' 0)
              (ih (b' + 1) 0 (by omega) (d + 1))
        · have ha2 : a = 2 := by omega
          subst ha2
          exact stepsToClosed_F_a2 d b 0
        · have ha4 : a = 2 * k' + 4 := by omega
          subst ha4
          exact StepsToClosed.of_reachesPlus (rule_F_even_ge4 d k' b 0)
            (ih (2 * k') (b + 3) (by omega) (d + 1))
      · rcases k with _ | _ | k'
        · have ha1 : a = 1 := by omega
          subst ha1
          obtain ⟨cfg', hp, hh⟩ := halt_F_a1 d b 0
          exact ⟨cfg', hp, Or.inr hh⟩
        · have ha3 : a = 3 := by omega
          subst ha3
          exact stepsToClosed_of_E _ _ _ _ (by omega) (step_F_a3_to_E d b 0)
        · have ha5 : a = 2 * k' + 5 := by omega
          subst ha5
          exact stepsToClosed_of_E _ _ _ _ (by omega) (step_F_odd_c0_to_E d k' b)

private theorem stepsToClosed_F_c0 (d a b : ℕ) :
    StepsToClosed target ps (cfg_F d a b 0) :=
  stepsToClosed_F_c0_all (4 * a + 5 * b) a b (Nat.le_refl _) d

private theorem stepsToClosed_F_even_all (K : ℕ) :
    ∀ k ≤ K, ∀ d b c, StepsToClosed target ps (cfg_F d (2 * k) b c) := by
  induction K with
  | zero =>
    intro k hk d b c
    have hk0 : k = 0 := by omega
    subst hk0
    change StepsToClosed target ps (cfg_F d 0 b c)
    rcases b with _ | b'
    · rcases c with _ | c'
      · exact stepsToClosed_of_E _ _ _ _ (by omega) (step_F_a0_b0_c0_to_E d)
      · exact StepsToClosed.of_reachesPlus (rule_F_a0_b0_csucc d c')
          (stepsToClosed_F_c0 (d + 1) 0 (c' + 1))
    · exact StepsToClosed.of_reachesPlus (rule_F_a0_bsucc d b' c)
        (stepsToClosed_F_c0 (d + 1) (b' + 1) c)
  | succ K ih =>
    intro k hk d b c
    rcases Nat.of_le_succ hk with hle | rfl
    · exact ih k hle d b c
    · rcases K with _ | K'
      · exact stepsToClosed_F_a2 d b c
      · have h2k : 2 * (K' + 1 + 1) = 2 * K' + 4 := by omega
        rw [h2k]
        exact StepsToClosed.of_reachesPlus (rule_F_even_ge4 d K' b c)
          (ih K' (by omega) (d + 1) (b + 3) c)

private theorem stepsToClosed_F_d0 (a b c : ℕ) :
    StepsToClosed target ps (cfg_F 0 a b c) := by
  rcases nat_even_or_odd_two_mul a with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact stepsToClosed_F_even_all k k (Nat.le_refl k) 0 b c
  · rcases k with _ | _ | k'
    · obtain ⟨cfg', hp, hh⟩ := halt_F_a1 0 b c
      exact ⟨cfg', hp, Or.inr hh⟩
    · exact stepsToClosed_of_E _ _ _ _ (by omega) (step_F_a3_to_E 0 b c)
    · have ha5 : 2 * (k' + 1 + 1) + 1 = 2 * k' + 5 := by omega
      rw [ha5]
      obtain ⟨cfg', hp, hh⟩ := halt_F_odd_d0 k' b c
      exact ⟨cfg', hp, Or.inr hh⟩

private theorem stepsToClosed_F_d1 (a b c : ℕ) :
    StepsToClosed target ps (cfg_F 1 a b c) := by
  rcases nat_even_or_odd_two_mul a with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact stepsToClosed_F_even_all k k (Nat.le_refl k) 1 b c
  · rcases k with _ | _ | k'
    · obtain ⟨cfg', hp, hh⟩ := halt_F_a1 1 b c
      exact ⟨cfg', hp, Or.inr hh⟩
    · exact stepsToClosed_of_E _ _ _ _ (by omega) (step_F_a3_to_E 1 b c)
    · have ha5 : 2 * (k' + 1 + 1) + 1 = 2 * k' + 5 := by omega
      rw [ha5]
      exact stepsToClosed_of_E _ _ _ _ (by omega) (step_F_odd_d1_to_E k' b c)

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_E 1 3 0 0, init_reaches_start, in_ps_E 1 3 0 0 (by omega)⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, hcond⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_E]
  change ¬ (vars 0 ≥ 2) at hcond
  have hq : vars 0 = 0 ∨ vars 0 = 1 := by omega
  rcases hq with hq0 | hq1
  · rw [hq0]
    exact StepsToClosed.of_reachesPlus
      (step_E_q0_to_F (vars 1) (vars 2) (vars 3))
      (stepsToClosed_F_d0 (vars 1) (vars 2) (vars 3))
  · rw [hq1]
    rcases vars 1 with _ | a'
    · rcases vars 2 with _ | b'
      · rcases vars 3 with _ | c'
        · obtain ⟨cfg', hp, hh⟩ := halt_E_q1_a0_b0_c0
          exact ⟨cfg', hp, Or.inr hh⟩
        · exact stepsToClosed_of_E _ _ _ _ (by omega) (accel_E_q1_a0_b0_csucc c')
      · exact StepsToClosed.of_reachesPlus
          (step_E_q1_a0_bsucc_to_F b' (vars 3))
          (stepsToClosed_F_c0 2 (b' + 1) (vars 3))
    · exact StepsToClosed.of_reachesPlus
        (step_E_q1_asucc_to_F a' (vars 2) (vars 3))
        (stepsToClosed_F_d1 (a' + 1) (vars 2) (vars 3))

/-- `1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## High-Level Collatz-like Acceleration -/

/-- Single-family high-level symbolic configuration state space
$E(a, b, c) := 0^\infty\,\mathrm{E}{>}\,0\,0^{a \bmod 2}\,1^a\,0\,1^b\,0\,1^c\,0^\infty$
for `1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD`. -/
inductive HighLevelState where
  /-- $E(a, b, c) := 0^\infty\,\mathrm{E}{>}\,0\,0^{a \bmod 2}\,1^a\,0\,1^b\,0\,1^c\,0^\infty$. -/
  | E (a b c : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $E(3, 0, 0)$, corresponding to $E(1, 3, 0, 0)$. -/
def highLevelStart : HighLevelState := .E 3 0 0

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .E a b c => mkE a b c

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Outcome of $F(d + 2, 2k, b, c)$ when run until returning to $E$ or halting. -/
def evalFGe2 (d k b c : ℕ) : Option HighLevelState :=
  if k = 0 then
    if b = 0 then
      if c = 0 then some (.E (d + 3) 3 0)
      else evalFGe2 (d + 1) 0 c 0
    else if b % 2 = 0 then evalFGe2 (d + 1) (b / 2) c 0
    else if b = 1 then none
    else if b = 3 then some (.E (d + c + 5) 3 0)
    else some (.E (d + 4) (b - 4) (c + 3))
  else if k = 1 then
    some (.E (d + 1) (b + 4) c)
  else
    evalFGe2 (d + 1) (k - 2) (b + 3) c
termination_by 5 * k + 3 * b + 4 * c
decreasing_by all_goals omega

/-- Outcome of $F(1, 2k, b, c)$ when run until returning to $E$ or halting. -/
def evalF1 (k b c : ℕ) : Option HighLevelState :=
  if k = 0 then
    if b = 0 then
      if c = 0 then some (.E 2 3 0)
      else evalFGe2 0 0 c 0
    else if b % 2 = 0 then evalFGe2 0 (b / 2) c 0
    else if b = 1 then none
    else if b = 3 then some (.E (c + 4) 3 0)
    else some (.E 3 (b - 4) (c + 3))
  else if k = 1 then
    if b % 2 = 1 then some (.E (b + 4) c 0)
    else evalFGe2 0 (b / 2) (c + 3) 0
  else
    evalFGe2 0 (k - 2) (b + 3) c

/-- Outcome of $F(0, 2k, b, c)$ when run until returning to $E$ or halting. -/
def evalF0 (k b c : ℕ) : Option HighLevelState :=
  if k = 0 then
    if b = 0 then
      if c = 0 then some (.E 1 3 0)
      else evalF1 0 c 0
    else if b % 2 = 0 then evalF1 (b / 2) c 0
    else if b = 1 then none
    else if b = 3 then some (.E (c + 3) 3 0)
    else some (.E 2 (b - 4) (c + 3))
  else if k = 1 then
    some (.E (b + 2) (c + 3) 0)
  else
    evalF1 (k - 2) (b + 3) c

/-- High-level accelerated Collatz-like transition function on $E(a, b, c)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .E a b c =>
    if a % 2 = 0 then evalF0 (a / 2) b c
    else if a = 1 then none
    else some (.E (b + 3 * a - 6) (c + 3) 0)

private theorem stepsTo_evalFGe2_aux (M : ℕ) :
    ∀ d k b c, 5 * k + 3 * b + 4 * c = M →
      CollatzStepsTo next (.F_even (d + 2) k b c) ((evalFGe2 d k b c).map toState) := by
  induction M using Nat.strongRecOn with
  | ind M ih =>
    intro d k b c hM
    rw [evalFGe2]
    split_ifs with hk0 hb0 hc0 hb_even hb1 hb3 hk1
    · subst hk0 hb0 hc0
      exact CollatzStepsTo.of_eq rfl
    · subst hk0 hb0
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      exact CollatzStepsTo.head rfl
        (ih (5 * 0 + 3 * (c' + 1) + 4 * 0) (by omega) (d + 1) 0 (c' + 1) 0 rfl)
    · subst hk0
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have h1 :
          next (.F_even (d + 2) 0 (b' + 1) c) =
            some (.F_even ((d + 1) + 2) ((b' + 1) / 2) c 0) := by
        simp [next, enterF_c0, hb_even]
      exact CollatzStepsTo.head h1
        (ih (5 * ((b' + 1) / 2) + 3 * c + 4 * 0) (by omega)
          (d + 1) ((b' + 1) / 2) c 0 rfl)
    · subst hk0 hb1
      exact CollatzStepsTo.of_eq rfl
    · subst hk0 hb3
      refine CollatzStepsTo.of_eq ?_
      change some (mkE (d + 2 + 1 + c + 2) 3 0) = some (mkE (d + c + 5) 3 0)
      exact congrArg (fun m => some (mkE m 3 0)) (by omega)
    · subst hk0
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 5 := ⟨b - 5, by omega⟩
      refine CollatzStepsTo.of_eq ?_
      simp [next, enterF_c0, hb_even, toState]
    · subst hk1
      exact CollatzStepsTo.of_eq rfl
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      exact CollatzStepsTo.head rfl
        (ih (5 * k' + 3 * (b + 3) + 4 * c) (by omega) (d + 1) k' (b + 3) c rfl)

private theorem stepsTo_evalFGe2 (d k b c : ℕ) :
    CollatzStepsTo next (.F_even (d + 2) k b c) ((evalFGe2 d k b c).map toState) :=
  stepsTo_evalFGe2_aux (5 * k + 3 * b + 4 * c) d k b c rfl

private theorem stepsTo_evalF1 (k b c : ℕ) :
    CollatzStepsTo next (.F_even 1 k b c) ((evalF1 k b c).map toState) := by
  unfold evalF1
  split_ifs with hk0 hb0 hc0 hb_even hb1 hb3 hk1 hb_odd
  · subst hk0 hb0 hc0
    exact CollatzStepsTo.of_eq rfl
  · subst hk0 hb0
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    exact CollatzStepsTo.head rfl (stepsTo_evalFGe2 0 0 (c' + 1) 0)
  · subst hk0
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have h1 :
        next (.F_even 1 0 (b' + 1) c) =
          some (.F_even 2 ((b' + 1) / 2) c 0) := by
      simp [next, enterF_c0, hb_even]
    exact CollatzStepsTo.head h1 (stepsTo_evalFGe2 0 ((b' + 1) / 2) c 0)
  · subst hk0 hb1
    exact CollatzStepsTo.of_eq rfl
  · subst hk0 hb3
    refine CollatzStepsTo.of_eq ?_
    change some (mkE (1 + 1 + c + 2) 3 0) = some (mkE (c + 4) 3 0)
    exact congrArg (fun m => some (mkE m 3 0)) (by omega)
  · subst hk0
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 5 := ⟨b - 5, by omega⟩
    refine CollatzStepsTo.of_eq ?_
    simp [next, enterF_c0, hb_even, toState]
  · subst hk1
    have hpar : (b + 4) % 2 = 1 := by omega
    refine CollatzStepsTo.of_eq ?_
    simp [next, toState, mkE, hpar]
  · subst hk1
    have h1 : next (.F_even 1 1 b c) = some (.E true ((b + 3) + 1) c 0) := rfl
    have hb4_even : (b + 4) % 2 = 0 := by omega
    have h2 : next (.E true ((b + 3) + 1) c 0) = some (.F_even 1 (b / 2 + 2) c 0) := by
      change enterF_d1 (b + 4) c 0 = _
      simp only [enterF_d1, hb4_even, ite_true, Option.some.injEq, State.F_even.injEq,
        true_and, and_true]
      omega
    have h3 : next (.F_even 1 (b / 2 + 2) c 0) = some (.F_even 2 (b / 2) (c + 3) 0) := rfl
    exact CollatzStepsTo.head h1
      (CollatzStepsTo.head h2
        (CollatzStepsTo.head h3 (stepsTo_evalFGe2 0 (b / 2) (c + 3) 0)))
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    exact CollatzStepsTo.head rfl (stepsTo_evalFGe2 0 k' (b + 3) c)

private theorem stepsTo_evalF0 (k b c : ℕ) :
    CollatzStepsTo next (.F_even 0 k b c) ((evalF0 k b c).map toState) := by
  unfold evalF0
  split_ifs with hk0 hb0 hc0 hb_even hb1 hb3 hk1
  · subst hk0 hb0 hc0
    exact CollatzStepsTo.of_eq rfl
  · subst hk0 hb0
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    exact CollatzStepsTo.head rfl (stepsTo_evalF1 0 (c' + 1) 0)
  · subst hk0
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have h1 :
        next (.F_even 0 0 (b' + 1) c) =
          some (.F_even 1 ((b' + 1) / 2) c 0) := by
      simp [next, enterF_c0, hb_even]
    exact CollatzStepsTo.head h1 (stepsTo_evalF1 ((b' + 1) / 2) c 0)
  · subst hk0 hb1
    exact CollatzStepsTo.of_eq rfl
  · subst hk0 hb3
    refine CollatzStepsTo.of_eq ?_
    change some (mkE (0 + 1 + c + 2) 3 0) = some (mkE (c + 3) 3 0)
    exact congrArg (fun m => some (mkE m 3 0)) (by omega)
  · subst hk0
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 5 := ⟨b - 5, by omega⟩
    refine CollatzStepsTo.of_eq ?_
    simp [next, enterF_c0, hb_even, toState]
  · subst hk1
    exact CollatzStepsTo.of_eq rfl
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    exact CollatzStepsTo.head rfl (stepsTo_evalF1 k' (b + 3) c)

private theorem reaches_E_odd_drain : ∀ (m b c : ℕ),
    CollatzReachesStar next (.E true (2 * m + 3) b c) (.E true 3 (b + 6 * m) c)
  | 0, b, c => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | m + 1, b, c => by
    have h1 : next (.E true (2 * (m + 1) + 3) b c) =
        some (.E true (2 * m + 3) (b + 6) c) := by
      have ha : 2 * (m + 1) + 3 = (2 * m + 4) + 1 := by omega
      have hodd : (2 * m + 5) % 2 = 1 := by omega
      rw [ha]
      change enterF_d1 (2 * m + 5) b c = _
      simp only [enterF_d1, hodd, one_ne_zero, ite_false]
      split_ifs with h1' h3'
      · omega
      · omega
      · exact congrArg (fun x => some (State.E true x (b + 6) c)) (by omega)
    have ih := reaches_E_odd_drain m (b + 6) c
    have hb : b + 6 + 6 * m = b + 6 * (m + 1) := by omega
    rw [hb] at ih
    exact CollatzReachesStar.head h1 ih

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState)
    (CollatzReachesStar.refl next start) ?_
  rintro ⟨a, b, c⟩
  dsimp only [highLevelNext]
  split_ifs with ha_even ha1
  · have hmk : toState (.E a b c) = .E false a b c := by
      simp [toState, mkE, ha_even]
    rw [hmk]
    have h1 : next (.E false a b c) = some (.F_even 0 (a / 2) b c) := by
      simp [next, enterF_d0, ha_even]
    exact CollatzStepsTo.head h1 (stepsTo_evalF0 (a / 2) b c)
  · subst ha1
    exact CollatzStepsTo.of_eq rfl
  · obtain ⟨m, rfl⟩ : ∃ m, a = 2 * m + 3 := ⟨(a - 3) / 2, by omega⟩
    have hodd : (2 * m + 3) % 2 = 1 := by omega
    have hmk : toState (.E (2 * m + 3) b c) = .E true (2 * m + 3) b c := by
      simp [toState, mkE, hodd]
    rw [hmk]
    refine CollatzStepsTo.of_reachesStar (reaches_E_odd_drain m b c) ?_
    refine CollatzStepsTo.of_eq ?_
    change some (mkE (b + 6 * m + 3) (c + 3) 0) =
      some (mkE (b + 3 * (2 * m + 3) - 6) (c + 3) 0)
    exact congrArg (fun x => some (mkE x (c + 3) 0)) (by omega)

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

end BusyBeaver.M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD
