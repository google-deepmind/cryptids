/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE`
(holdout #116 (`suspect_99`, listed on
[`User:RobinCodes/Next_Steps`](https://wiki.bbchallenge.org/wiki/User:RobinCodes/Next_Steps))).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$C(a, b, c, d) := 0^\infty\,1^d\,(10)^c\,1^b\,\mathrm{C}{>}\,110\,(10)^a\,1\,0^\infty$$
at $C(0, 3, 0, 0)$ in 33 steps, and every $C(a, b, c, d)$ advances in `ReachesPlus` either to
another $C(a', b', c', d')$ or to a halting configuration.

## Collatz-like Acceleration Rules

```text
Consider:
C(a, b, c, d)    = 0^inf 1^d (10)^c 1^b C> 110 (10)^a 1 0^inf
W(k, b, c, d)    = 0^inf 1^d (10)^c 1^b E> 11110 (10)^k 1 0^inf
M(k, u, b, c, d) = 0^inf 1^d (10)^c 1^{b+1} (01)^u 10 E> 01110 (10)^k 1 0^inf
S(a, b, c, d)    = 0^inf 1^d (10)^c 1^{b+1} 0 A> 111 (11)^a 0^inf
R(a, b, c, d)    = 0^inf 1^d (10)^c 1^{b+1} 0 A> 1111 (11)^a 0^inf

C(a, 0, 0, d+1)    = C(a, d+1, 0, 0)
C(0, 0, c, d)     -> C(0, 3, c, d)              if c >= 1 or d = 0
C(1, 0, c, d)     -> S(0, 1, c, d)              if c >= 1 or d = 0
C(k+2, 0, c, d)   -> W(k, 2, c, d)              if c >= 1 or d = 0
C(0, 1, c, 0)     -> Halt
C(0, 1, c, d+1)   -> C(c+2, d, 0, 0)
C(0, b+2, c, d)   -> C(2, b, c, d)
C(1, b+1, c, d)   -> S(0, b+2, c, d)
C(k+2, b+1, c, d) -> M(k, 0, b, c, d)

W(0, b, c, d)     -> C(2, b, c, d)
W(1, b, c, d)     -> S(0, b+3, c, d)
W(k+2, b, c, d)   -> M(k, 0, b+1, c, d)

M(0, u, b, c, d)         -> S(u+2, b, c, d)
M(1, u, 0, c, 0)         -> C(0, 0, u+c+5, 1)
M(2, u, 0, c, 0)         -> C(0, 3, u+c+5, 1)
M(3, u, 0, c, 0)         -> C(0, 4, u+c+5, 1)
M(k+4, u, 0, c, 0)       -> W(k, 2, u+c+5, 1)
M(k+1, u, 0, c, 1)       -> W(k, 2(u+c)+6, 0, 0)
M(k+1, u, 0, c, d+2)     -> M(k, u+c+2, d, 0, 0)
M(k+1, u, 1, 0, 0)       -> W(k, 2u+6, 0, 0)
M(k+1, u, 1, 0, d+1)     -> M(k, u+2, d, 0, 0)
M(k+1, u, 1, c+1, d)     -> W(k, 2u+6, c+1, d)
M(k+1, u, b+2, c, d)     -> M(k, u+2, b, c, d)

S(a, 0, c, 0)     -> C(a+c+2, 0, 0, 0)
S(a, 0, c, 1)     -> C(0, 2(a+c)+4, 0, 0)
S(a, 0, c, d+2)   -> R(a+c+1, d, 0, 0)
S(a, 1, 0, 0)     -> C(0, 2a+4, 0, 0)
S(a, 1, 0, d+1)   -> R(a+1, d, 0, 0)
S(a, 1, c+1, d)   -> C(0, 2a+4, c+1, d)
S(a, b+2, c, d)   -> R(a+1, b, c, d)

R(a, 0, c, 0)     -> C(0, 2(a+c)+7, 0, 0)
R(a, 0, c, 1)     -> C(0, 2(a+c)+5, 0, 0)
R(a, 0, c, 2)     -> Halt
R(a, 0, c, d+3)   -> C(a+c+3, d, 0, 0)
R(a, 1, 0, 0)     -> C(0, 2a+5, 0, 0)
R(a, 1, 0, 1)     -> Halt
R(a, 1, 0, d+2)   -> C(a+3, d, 0, 0)
R(a, 1, c+1, d)   -> C(0, 2a+5, c+1, d)
R(a, 2, c, 0)     -> Halt
R(a, 2, c, d+1)   -> C(a+c+3, d, 0, 0)
R(a, b+3, c, d)   -> C(a+3, b, c, d)

Start: C(0, 3, 0, 0), reached after 33 raw TM steps
```

## High-Level Collatz-like Acceleration

Along the trajectory from $C(0, 3, 0, 0)$, every canonical return configuration has either
$c = d = 0$ or $d = 1$. Eliminating the transient families $W$, $M$, $S$, and $R$ (via `evalW`, the
recursive loop `evalM` decreasing in $k$, `evalS`, and `evalR`) yields a high-level Collatz-like
acceleration `highLevelNext` on the two canonical families
$$C_0(a, b) := C(a, b, 0, 0), \qquad C_1(a, b, c) := C(a, b, c, 1),$$
starting from $C_0(0, 3)$.
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private theorem target_A_0 : target A 0 = some (some B, Stmt.write 1 Dir.right) := rfl
private theorem target_A_1 : target A 1 = some (some F, Stmt.write 1 Dir.left) := rfl
private theorem target_B_0 : target B 0 = some (some C, Stmt.write 1 Dir.right) := rfl
private theorem target_B_1 : target B 1 = some (some F, Stmt.write 1 Dir.right) := rfl
private theorem target_C_0 : target C 0 = some (some D, Stmt.write 0 Dir.left) := rfl
private theorem target_C_1 : target C 1 = some (some E, Stmt.write 1 Dir.right) := rfl
private theorem target_D_0 : target D 0 = none := rfl
private theorem target_D_1 : target D 1 = some (some C, Stmt.write 1 Dir.left) := rfl
private theorem target_E_0 : target E 0 = some (some B, Stmt.write 0 Dir.right) := rfl
private theorem target_E_1 : target E 1 = some (some E, Stmt.write 1 Dir.right) := rfl
private theorem target_F_0 : target F 0 = some (some A, Stmt.write 1 Dir.left) := rfl
private theorem target_F_1 : target F 1 = some (some E, Stmt.write 0 Dir.left) := rfl

/-! ## Tape Construction Helpers and Block Identities -/

/-- Left-tape helper encoding $0^\infty\,1^d\,(10)^c\,1^b$. -/
abbrev left_bcd (b c d : ℕ) : ListBlank (Fin 2) :=
  ListBlank.append (([1] : List (Fin 2)) ^ b)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
      (ListBlank.append (([1] : List (Fin 2)) ^ d) default))

private theorem append_10_pow_cons_one (k : ℕ) (s : ListBlank (Fin 2)) :
    ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.cons 1 s) =
      ListBlank.cons 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) s) := by
  simpa using append_10_pow_one k s

private theorem left_bcd_zero_zero (d : ℕ) :
    left_bcd 0 0 d = left_bcd d 0 0 := by
  simp [left_bcd]

private theorem left_bcd_one_zero (d : ℕ) :
    left_bcd 1 0 d = left_bcd (d + 1) 0 0 := by
  unfold left_bcd
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 1 d default, Nat.add_comm 1 d]

private theorem cons_one_left_bcd_zero (c d : ℕ) :
    ListBlank.cons 1 (left_bcd 0 c d) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ c)
        (ListBlank.cons 1 (left_bcd d 0 0)) := by
  unfold left_bcd
  simp only [list_pow_zero, ListBlank.append_nil]
  exact (append_10_pow_cons_one c (ListBlank.append (([1] : List (Fin 2)) ^ d) default)).symm

private theorem append_0_cons_1_left_bcd_zero (c d : ℕ) :
    ListBlank.append (([1, 0] : List (Fin 2)) ^ 0)
      (ListBlank.cons 1 (left_bcd 0 c d)) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ c)
        (ListBlank.cons 1 (left_bcd d 0 0)) := by
  rw [list_pow_zero, ListBlank.append_nil]
  exact cons_one_left_bcd_zero c d

/-- Canonical tape pattern
$C(a, b, c, d) := 0^\infty\,1^d\,(10)^c\,1^b\,\mathrm{C}{>}\,110\,(10)^a\,1\,0^\infty$. -/
def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 1 (.rep [0, 1] 2 (.rep [1] 3 .default))
    head := some C
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))) }

/-- Closed pattern set for `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE` (Level A). -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

/-- Canonical configuration $C(a, b, c, d)$. -/
def cfg_C (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C (left_bcd b c d)
    (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
        (ListBlank.cons 1 default)))))

private theorem eval_pat_C (vars : ℕ → ℕ) :
    evalTapePattern pat_C vars = cfg_C (vars 0) (vars 1) (vars 2) (vars 3) :=
  rfl

private theorem in_ps_C (a b c d : ℕ) : IsInPatternSet ps (cfg_C a b c d) :=
  ⟨(pat_C, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0, rfl, trivial⟩

private def cfg_0 (a : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
    (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 default)))

private def cfg_21 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E (left_bcd b c d)
    (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))))

private def cfg_51 (a u b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D
    (ListBlank.cons 0 (ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
      (ListBlank.cons 1 (left_bcd b c d))))
    (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 0
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
        (ListBlank.cons 1 default))))))

private def cfg_31 (a u b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.cons 1 (ListBlank.cons 0
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
        (ListBlank.cons 1 (left_bcd b c d)))))
    (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))))

/-- Intermediate configuration family $R$ (with shift parameter `u`). -/
def cfg_8 (a u b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.cons 0 (ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
      (ListBlank.cons 1 (left_bcd b c d))))
    (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)))))

private def cfg_99 (a u b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.cons 1 (ListBlank.cons 0
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
        (ListBlank.cons 1 (left_bcd b c d)))))
    (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)))))

/-- Intermediate configuration family $S$ (with shift parameter `u`). -/
def cfg_57 (a u b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.cons 0 (ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
      (ListBlank.cons 1 (left_bcd b c d))))
    (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))))

/-- Intermediate configuration family $W$ (with shift parameter `a`). -/
def cfg_89 (a k b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E (left_bcd b c d)
    (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.cons 1 (ListBlank.cons 0
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
            (ListBlank.cons 1 default))))))))

/-- Intermediate configuration family $M$ (with shift parameter `a`). -/
def cfg_101 (a k u b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.cons 1 (ListBlank.cons 0
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
        (ListBlank.cons 1 (left_bcd b c d)))))
    (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.cons 1 (ListBlank.cons 0
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
            (ListBlank.cons 1 default))))))))

private def cfg_65 (a k u b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.cons 0 (ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
      (ListBlank.cons 1 (left_bcd b c d))))
    (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.cons 1 (ListBlank.cons 0
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ k)
            (ListBlank.cons 1 default)))))))))

private def cfg_65_sweep (a k u : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.cons 1 (ListBlank.cons 0
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ u)
        (ListBlank.cons 1 (ListBlank.cons 1 default)))))
    (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default)))))))))

private theorem reachesPlus_of_multiStep (n : ℕ) (hn : n > 0) {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : multiStep target c₁ n = some c₂) : ReachesPlus target c₁ c₂ :=
  ⟨n, hn, h⟩

local macro "sim_steps" : tactic =>
  `(tactic| (
    dsimp only [cfg_0, cfg_C, cfg_21, cfg_51, cfg_31, cfg_8, cfg_99, cfg_57,
      cfg_89, cfg_101, cfg_65, cfg_65_sweep, left_bcd]
    simp only [multiStep_succ', multiStep_zero, Option.bind, step,
      target_A_0, target_A_1, target_B_0, target_B_1, target_C_0, target_C_1,
      target_D_0, target_D_1, target_E_0, target_E_1, target_F_0, target_F_1,
      Cfg.headRight, list_pow_zero, list_pow_succ, List.cons_append,
      List.singleton_append, List.nil_append, Tape.write, Tape.move,
      ListBlank.append_nil, ListBlank.append_cons, ListBlank.head_cons,
      ListBlank.tail_cons, ListBlank.cons_zero_default, ListBlank.head_default_fin,
      ListBlank.tail_default, Option.map]))

/-! ## Shift Loops and Accelerated Transitions -/

private theorem reach_21 (a : ℕ) : ∀ b c d,
    ReachesPlus target (cfg_21 a b c d) (cfg_C 0 (b + 2 * a + 1) c d) := by
  induction a with
  | zero =>
    intro b c d
    have h : b + 2 * 0 + 1 = b + 1 := by omega
    rw [h]
    refine reachesPlus_of_multiStep 9 (by decide) ?_
    sim_steps
  | succ a ih =>
    intro b c d
    have h1 : ReachesPlus target (cfg_21 (a + 1) b c d) (cfg_21 a (b + 2) c d) := by
      refine reachesPlus_of_multiStep 2 (by decide) ?_
      sim_steps
    have h_eq : b + 2 * (a + 1) + 1 = (b + 2) + 2 * a + 1 := by omega
    rw [h_eq]
    exact h1.trans (ih (b + 2) c d)

private theorem shift_51_step (u : ℕ) : ∀ a b c d,
    ReachesStar target (cfg_51 a u b c d) (cfg_51 (a + u) 0 b c d) := by
  induction u with
  | zero =>
    intro a b c d
    rw [Nat.add_zero]
  | succ u ih =>
    intro a b c d
    have h1 : ReachesPlus target (cfg_51 a (u + 1) b c d) (cfg_51 (a + 1) u b c d) := by
      refine reachesPlus_of_multiStep 2 (by decide) ?_
      sim_steps
    have h_eq : a + (u + 1) = (a + 1) + u := by omega
    rw [h_eq]
    exact (h1.trans_star (ih (a + 1) b c d)).to_star

private theorem step_51_succ (a b c d : ℕ) :
    ReachesPlus target (cfg_51 a 0 (b + 1) c d) (cfg_C (a + 2) b c d) := by
  refine reachesPlus_of_multiStep 3 (by decide) ?_
  sim_steps

private theorem step_51_halt (a : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_51 a 0 0 0 0) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight D default
    (ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 0
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 2))
        (ListBlank.cons 1 default)))))),
    reachesPlus_of_multiStep 4 (by decide) ?_, by bb_halt⟩
  sim_steps

private theorem reach_51_succ (a u b c d : ℕ) :
    ReachesPlus target (cfg_51 a u (b + 1) c d) (cfg_C (a + u + 2) b c d) :=
  (shift_51_step u a (b + 1) c d).trans_plus (step_51_succ (a + u) b c d)

private theorem reach_51_b0_succ (a u c d : ℕ) :
    ReachesPlus target (cfg_51 a u 0 c (d + 1)) (cfg_C (a + u + c + 2) d 0 0) := by
  have h1 := shift_51_step u a 0 c (d + 1)
  have h_eq : cfg_51 (a + u) 0 0 c (d + 1) = cfg_51 (a + u) c (d + 1) 0 0 := by
    unfold cfg_51
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq] at h1
  exact h1.trans_plus (reach_51_succ (a + u) c d 0 0)

private theorem reach_51_b0_halt (a u c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_51 a u 0 c 0) cfg' ∧ (step target cfg').isNone := by
  have h1 := shift_51_step u a 0 c 0
  have h_eq : cfg_51 (a + u) 0 0 c 0 = cfg_51 (a + u) c 0 0 0 := by
    unfold cfg_51
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq] at h1
  have h2 := h1.trans (shift_51_step c (a + u) 0 0 0)
  obtain ⟨cfg', hp, hh⟩ := step_51_halt (a + u + c)
  exact ⟨cfg', h2.trans_plus hp, hh⟩

private theorem shift_31 (a : ℕ) : ∀ u b c d,
    ReachesPlus target (cfg_31 a u b c d) (cfg_51 0 (u + a) b c d) := by
  induction a with
  | zero =>
    intro u b c d
    rw [Nat.add_zero]
    refine reachesPlus_of_multiStep 11 (by decide) ?_
    sim_steps
  | succ a ih =>
    intro u b c d
    have h1 : ReachesPlus target (cfg_31 (a + 1) u b c d) (cfg_31 a (u + 1) b c d) := by
      refine reachesPlus_of_multiStep 4 (by decide) ?_
      sim_steps
    have h_eq : u + (a + 1) = (u + 1) + a := by omega
    rw [h_eq]
    exact h1.trans (ih (u + 1) b c d)

private theorem reach_31_succ (a u b c d : ℕ) :
    ReachesPlus target (cfg_31 a u (b + 1) c d) (cfg_C (u + a + 2) b c d) := by
  have h := (shift_31 a u (b + 1) c d).trans (reach_51_succ 0 (u + a) b c d)
  rwa [Nat.zero_add] at h

private theorem reach_31_b0_succ (a u c d : ℕ) :
    ReachesPlus target (cfg_31 a u 0 c (d + 1)) (cfg_C (u + a + c + 2) d 0 0) := by
  have h := (shift_31 a u 0 c (d + 1)).trans (reach_51_b0_succ 0 (u + a) c d)
  rwa [Nat.zero_add] at h

private theorem reach_31_b0_halt (a u c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_31 a u 0 c 0) cfg' ∧ (step target cfg').isNone := by
  obtain ⟨cfg', hp, hh⟩ := reach_51_b0_halt 0 (u + a) c
  exact ⟨cfg', (shift_31 a u 0 c 0).trans hp, hh⟩

private theorem shift_8_step (u : ℕ) : ∀ a b c d,
    ReachesStar target (cfg_8 a u b c d) (cfg_8 (a + u) 0 b c d) := by
  induction u with
  | zero =>
    intro a b c d
    rw [Nat.add_zero]
  | succ u ih =>
    intro a b c d
    have h1 : ReachesPlus target (cfg_8 a (u + 1) b c d) (cfg_8 (a + 1) u b c d) := by
      refine reachesPlus_of_multiStep 2 (by decide) ?_
      sim_steps
    have h_eq : a + (u + 1) = (a + 1) + u := by omega
    rw [h_eq]
    exact (h1.trans_star (ih (a + 1) b c d)).to_star

private theorem shift_99 (a : ℕ) : ∀ u b c d,
    ReachesPlus target (cfg_99 a u b c d) (cfg_8 (u + a + 1) 0 b c d) := by
  induction a with
  | zero =>
    intro u b c d
    rw [Nat.add_zero]
    have h1 : ReachesPlus target (cfg_99 0 u b c d) (cfg_8 0 (u + 1) b c d) := by
      refine reachesPlus_of_multiStep 9 (by decide) ?_
      sim_steps
    have h2 := shift_8_step (u + 1) 0 b c d
    rw [Nat.zero_add] at h2
    exact h1.trans_star h2
  | succ a ih =>
    intro u b c d
    have h1 : ReachesPlus target (cfg_99 (a + 1) u b c d) (cfg_99 a (u + 1) b c d) := by
      refine reachesPlus_of_multiStep 4 (by decide) ?_
      sim_steps
    have h_eq : u + (a + 1) + 1 = (u + 1) + a + 1 := by omega
    rw [h_eq]
    exact h1.trans (ih (u + 1) b c d)

private theorem step_8_ge2 (a b c d : ℕ) :
    ReachesPlus target (cfg_8 a 0 (b + 2) c d) (cfg_31 (a + 1) 0 b c d) := by
  refine reachesPlus_of_multiStep 9 (by decide) ?_
  sim_steps

private theorem reach_8_ge3 (a b c d : ℕ) :
    ReachesPlus target (cfg_8 a 0 (b + 3) c d) (cfg_C (a + 3) b c d) := by
  have h := (step_8_ge2 a (b + 1) c d).trans (reach_31_succ (a + 1) 0 b c d)
  rwa [Nat.zero_add] at h

private theorem reach_8_b2_succ (a c d : ℕ) :
    ReachesPlus target (cfg_8 a 0 2 c (d + 1)) (cfg_C (a + c + 3) d 0 0) := by
  have h := (step_8_ge2 a 0 c (d + 1)).trans (reach_31_b0_succ (a + 1) 0 c d)
  have h_eq : 0 + (a + 1) + c + 2 = a + c + 3 := by omega
  rwa [h_eq] at h

private theorem reach_8_b2_halt (a c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_8 a 0 2 c 0) cfg' ∧ (step target cfg').isNone := by
  obtain ⟨cfg', hp, hh⟩ := reach_31_b0_halt (a + 1) 0 c
  exact ⟨cfg', (step_8_ge2 a 0 c 0).trans hp, hh⟩

private theorem reach_8_b1_c_succ (a c d : ℕ) :
    ReachesPlus target (cfg_8 a 0 1 (c + 1) d) (cfg_C 0 (2 * a + 5) (c + 1) d) := by
  have h1 : ReachesPlus target (cfg_8 a 0 1 (c + 1) d)
      (cfg_21 (a + 1) 2 (c + 1) d) := by
    refine reachesPlus_of_multiStep 7 (by decide) ?_
    sim_steps
  have h2 := reach_21 (a + 1) 2 (c + 1) d
  have h_eq : 2 + 2 * (a + 1) + 1 = 2 * a + 5 := by omega
  rw [h_eq] at h2
  exact h1.trans h2

private theorem reach_8_b1_c0_d0 (a : ℕ) :
    ReachesPlus target (cfg_8 a 0 1 0 0) (cfg_C 0 (2 * a + 5) 0 0) := by
  have h1 : ReachesPlus target (cfg_8 a 0 1 0 0) (cfg_21 (a + 1) 2 0 0) := by
    refine reachesPlus_of_multiStep 7 (by decide) ?_
    sim_steps
  have h2 := reach_21 (a + 1) 2 0 0
  have h_eq : 2 + 2 * (a + 1) + 1 = 2 * a + 5 := by omega
  rw [h_eq] at h2
  exact h1.trans h2

private theorem reach_8_b1_c0_halt (a : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_8 a 0 1 0 1) cfg' ∧ (step target cfg').isNone := by
  have h_eq : cfg_8 a 0 1 0 1 = cfg_8 a 0 2 0 0 := by
    unfold cfg_8
    rw [left_bcd_one_zero]
  rw [h_eq]
  exact reach_8_b2_halt a 0

private theorem reach_8_b1_c0_ge2 (a d : ℕ) :
    ReachesPlus target (cfg_8 a 0 1 0 (d + 2)) (cfg_C (a + 3) d 0 0) := by
  have h_eq : cfg_8 a 0 1 0 (d + 2) = cfg_8 a 0 (d + 3) 0 0 := by
    unfold cfg_8
    rw [left_bcd_one_zero]
  rw [h_eq]
  exact reach_8_ge3 a d 0 0

private theorem reach_8_b0_d0 (a c : ℕ) :
    ReachesPlus target (cfg_8 a 0 0 c 0) (cfg_C 0 (2 * (a + c) + 7) 0 0) := by
  have h_eq : cfg_8 a 0 0 c 0 = cfg_8 a c 0 0 0 := by
    unfold cfg_8
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq]
  have h1 := shift_8_step c a 0 0 0
  have h2 : ReachesPlus target (cfg_8 (a + c) 0 0 0 0) (cfg_99 (a + c) 0 1 0 0) := by
    refine reachesPlus_of_multiStep 12 (by decide) ?_
    sim_steps
  have h3 := shift_99 (a + c) 0 1 0 0
  rw [Nat.zero_add] at h3
  have h4 := reach_8_b1_c0_d0 (a + c + 1)
  have h_idx : 2 * (a + c + 1) + 5 = 2 * (a + c) + 7 := by omega
  rw [h_idx] at h4
  exact (h1.trans_plus h2).trans (h3.trans h4)

private theorem reach_8_b0_d1 (a c : ℕ) :
    ReachesPlus target (cfg_8 a 0 0 c 1) (cfg_C 0 (2 * (a + c) + 5) 0 0) := by
  have h_eq : cfg_8 a 0 0 c 1 = cfg_8 a c 1 0 0 := by
    unfold cfg_8
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq]
  exact (shift_8_step c a 1 0 0).trans_plus (reach_8_b1_c0_d0 (a + c))

private theorem reach_8_b0_d2_halt (a c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_8 a 0 0 c 2) cfg' ∧ (step target cfg').isNone := by
  have h_eq : cfg_8 a 0 0 c 2 = cfg_8 a c 2 0 0 := by
    unfold cfg_8
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq]
  obtain ⟨cfg', hp, hh⟩ := reach_8_b2_halt (a + c) 0
  exact ⟨cfg', (shift_8_step c a 2 0 0).trans_plus hp, hh⟩

private theorem reach_8_b0_ge3 (a c d : ℕ) :
    ReachesPlus target (cfg_8 a 0 0 c (d + 3)) (cfg_C (a + c + 3) d 0 0) := by
  have h_eq : cfg_8 a 0 0 c (d + 3) = cfg_8 a c (d + 3) 0 0 := by
    unfold cfg_8
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq]
  exact (shift_8_step c a (d + 3) 0 0).trans_plus (reach_8_ge3 (a + c) d 0 0)

private theorem shift_57_step (u : ℕ) : ∀ a b c d,
    ReachesStar target (cfg_57 a u b c d) (cfg_57 (a + u) 0 b c d) := by
  induction u with
  | zero =>
    intro a b c d
    rw [Nat.add_zero]
  | succ u ih =>
    intro a b c d
    have h1 : ReachesPlus target (cfg_57 a (u + 1) b c d) (cfg_57 (a + 1) u b c d) := by
      refine reachesPlus_of_multiStep 2 (by decide) ?_
      sim_steps
    have h_eq : a + (u + 1) = (a + 1) + u := by omega
    rw [h_eq]
    exact (h1.trans_star (ih (a + 1) b c d)).to_star

private theorem reach_57_ge2 (a b c d : ℕ) :
    ReachesPlus target (cfg_57 a 0 (b + 2) c d) (cfg_8 (a + 1) 0 b c d) := by
  have h1 : ReachesPlus target (cfg_57 a 0 (b + 2) c d) (cfg_99 a 0 b c d) := by
    refine reachesPlus_of_multiStep 9 (by decide) ?_
    sim_steps
  have h2 := shift_99 a 0 b c d
  rw [Nat.zero_add] at h2
  exact h1.trans h2

private theorem reach_57_b1_c_succ (a c d : ℕ) :
    ReachesPlus target (cfg_57 a 0 1 (c + 1) d) (cfg_C 0 (2 * a + 4) (c + 1) d) := by
  have h1 : ReachesPlus target (cfg_57 a 0 1 (c + 1) d) (cfg_21 a 3 (c + 1) d) := by
    refine reachesPlus_of_multiStep 8 (by decide) ?_
    sim_steps
  have h2 := reach_21 a 3 (c + 1) d
  have h_eq : 3 + 2 * a + 1 = 2 * a + 4 := by omega
  rw [h_eq] at h2
  exact h1.trans h2

private theorem reach_57_b1_c0_d0 (a : ℕ) :
    ReachesPlus target (cfg_57 a 0 1 0 0) (cfg_C 0 (2 * a + 4) 0 0) := by
  have h1 : ReachesPlus target (cfg_57 a 0 1 0 0) (cfg_21 a 3 0 0) := by
    refine reachesPlus_of_multiStep 8 (by decide) ?_
    sim_steps
  have h2 := reach_21 a 3 0 0
  have h_eq : 3 + 2 * a + 1 = 2 * a + 4 := by omega
  rw [h_eq] at h2
  exact h1.trans h2

private theorem reach_57_b1_c0_succ (a d : ℕ) :
    ReachesPlus target (cfg_57 a 0 1 0 (d + 1)) (cfg_8 (a + 1) 0 d 0 0) := by
  have h_eq : cfg_57 a 0 1 0 (d + 1) = cfg_57 a 0 (d + 2) 0 0 := by
    unfold cfg_57
    rw [left_bcd_one_zero]
  rw [h_eq]
  exact reach_57_ge2 a d 0 0

private theorem reach_57_b0_d0 (a c : ℕ) :
    ReachesPlus target (cfg_57 a 0 0 c 0) (cfg_C (a + c + 2) 0 0 0) := by
  have h_eq : cfg_57 a 0 0 c 0 = cfg_57 a c 0 0 0 := by
    unfold cfg_57
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq]
  have h1 := shift_57_step c a 0 0 0
  have h2 : ReachesPlus target (cfg_57 (a + c) 0 0 0 0) (cfg_31 (a + c) 0 1 0 0) := by
    refine reachesPlus_of_multiStep 12 (by decide) ?_
    sim_steps
  have h3 := reach_31_succ (a + c) 0 0 0 0
  have h_idx : 0 + (a + c) + 2 = a + c + 2 := by omega
  rw [h_idx] at h3
  exact (h1.trans_plus h2).trans h3

private theorem reach_57_b0_d1 (a c : ℕ) :
    ReachesPlus target (cfg_57 a 0 0 c 1) (cfg_C 0 (2 * (a + c) + 4) 0 0) := by
  have h_eq : cfg_57 a 0 0 c 1 = cfg_57 a c 1 0 0 := by
    unfold cfg_57
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq]
  exact (shift_57_step c a 1 0 0).trans_plus (reach_57_b1_c0_d0 (a + c))

private theorem reach_57_b0_ge2 (a c d : ℕ) :
    ReachesPlus target (cfg_57 a 0 0 c (d + 2)) (cfg_8 (a + c + 1) 0 d 0 0) := by
  have h_eq : cfg_57 a 0 0 c (d + 2) = cfg_57 a c (d + 2) 0 0 := by
    unfold cfg_57
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq]
  exact (shift_57_step c a (d + 2) 0 0).trans_plus (reach_57_ge2 (a + c) d 0 0)

private theorem shift_89_step (a : ℕ) : ∀ k b c d,
    ReachesStar target (cfg_89 a k b c d) (cfg_89 0 k (b + 2 * a) c d) := by
  induction a with
  | zero =>
    intro k b c d
    have h : b + 2 * 0 = b := by omega
    rw [h]
  | succ a ih =>
    intro k b c d
    have h1 : ReachesPlus target (cfg_89 (a + 1) k b c d) (cfg_89 a k (b + 2) c d) := by
      refine reachesPlus_of_multiStep 2 (by decide) ?_
      sim_steps
    have h_eq : b + 2 * (a + 1) = (b + 2) + 2 * a := by omega
    rw [h_eq]
    exact (h1.trans_star (ih k (b + 2) c d)).to_star

private theorem reach_89_k0 (b c d : ℕ) :
    ReachesPlus target (cfg_89 0 0 b c d) (cfg_C 2 b c d) := by
  have h1 : ReachesPlus target (cfg_89 0 0 b c d) (cfg_31 0 0 (b + 1) c d) := by
    refine reachesPlus_of_multiStep 16 (by decide) ?_
    sim_steps
  exact h1.trans (reach_31_succ 0 0 b c d)

private theorem reach_89_k1 (b c d : ℕ) :
    ReachesPlus target (cfg_89 0 1 b c d) (cfg_57 0 0 (b + 3) c d) := by
  refine reachesPlus_of_multiStep 7 (by decide) ?_
  sim_steps

private theorem reach_89_ge2 (k b c d : ℕ) :
    ReachesPlus target (cfg_89 0 (k + 2) b c d) (cfg_101 0 k 0 (b + 1) c d) := by
  refine reachesPlus_of_multiStep 16 (by decide) ?_
  sim_steps

private theorem shift_65_sweep_step (a : ℕ) : ∀ k u,
    ReachesStar target (cfg_65_sweep a k u) (cfg_65_sweep 0 k (u + a)) := by
  induction a with
  | zero =>
    intro k u
    rw [Nat.add_zero]
  | succ a ih =>
    intro k u
    have h1 : ReachesPlus target (cfg_65_sweep (a + 1) k u)
        (cfg_65_sweep a k (u + 1)) := by
      refine reachesPlus_of_multiStep 4 (by decide) ?_
      sim_steps
    have h_eq : u + (a + 1) = (u + 1) + a := by omega
    rw [h_eq]
    exact (h1.trans_star (ih k (u + 1))).to_star

private theorem reach_65_sweep_k0 (u : ℕ) :
    ReachesPlus target (cfg_65_sweep 0 0 u) (cfg_C 0 0 (u + 4) 1) := by
  refine reachesPlus_of_multiStep 17 (by decide) ?_
  sim_steps
  rw [append_10_pow_cons_one]

private theorem reach_65_sweep_k1 (u : ℕ) :
    ReachesPlus target (cfg_65_sweep 0 1 u) (cfg_C 0 3 (u + 4) 1) := by
  have h1 : ReachesPlus target (cfg_65_sweep 0 1 u) (cfg_21 0 2 (u + 4) 1) := by
    refine reachesPlus_of_multiStep 21 (by decide) ?_
    sim_steps
    rw [append_10_pow_cons_one]
  exact h1.trans (reach_21 0 2 (u + 4) 1)

private theorem reach_65_sweep_k2 (u : ℕ) :
    ReachesPlus target (cfg_65_sweep 0 2 u) (cfg_C 0 4 (u + 4) 1) := by
  refine reachesPlus_of_multiStep 31 (by decide) ?_
  sim_steps
  rw [append_10_pow_cons_one]

private theorem reach_65_sweep_ge3 (k u : ℕ) :
    ReachesPlus target (cfg_65_sweep 0 (k + 3) u) (cfg_89 0 k 2 (u + 4) 1) := by
  refine reachesPlus_of_multiStep 21 (by decide) ?_
  sim_steps
  rw [append_10_pow_cons_one, append_10_pow_cons_one]

private theorem shift_101_step (a : ℕ) : ∀ k u b c d,
    ReachesStar target (cfg_101 a k u b c d) (cfg_101 0 k (u + a) b c d) := by
  induction a with
  | zero =>
    intro k u b c d
    rw [Nat.add_zero]
  | succ a ih =>
    intro k u b c d
    have h1 : ReachesPlus target (cfg_101 (a + 1) k u b c d)
        (cfg_101 a k (u + 1) b c d) := by
      refine reachesPlus_of_multiStep 4 (by decide) ?_
      sim_steps
    have h_eq : u + (a + 1) = (u + 1) + a := by omega
    rw [h_eq]
    exact (h1.trans_star (ih k (u + 1) b c d)).to_star

private theorem shift_65_step (u : ℕ) : ∀ a k b c d,
    ReachesStar target (cfg_65 a k u b c d) (cfg_65 (a + u) k 0 b c d) := by
  induction u with
  | zero =>
    intro a k b c d
    rw [Nat.add_zero]
  | succ u ih =>
    intro a k b c d
    have h1 : ReachesPlus target (cfg_65 a k (u + 1) b c d)
        (cfg_65 (a + 1) k u b c d) := by
      refine reachesPlus_of_multiStep 2 (by decide) ?_
      sim_steps
    have h_eq : a + (u + 1) = (a + 1) + u := by omega
    rw [h_eq]
    exact (h1.trans_star (ih (a + 1) k b c d)).to_star

private theorem reach_101_k0 (u b c d : ℕ) :
    ReachesPlus target (cfg_101 0 0 u b c d) (cfg_57 (u + 2) 0 b c d) := by
  have h1 : ReachesPlus target (cfg_101 0 0 u b c d) (cfg_57 0 (u + 2) b c d) := by
    refine reachesPlus_of_multiStep 7 (by decide) ?_
    sim_steps
  have h2 := shift_57_step (u + 2) 0 b c d
  rw [Nat.zero_add] at h2
  exact h1.trans_star h2

private theorem step_101_to_65 (k u b c d : ℕ) :
    ReachesPlus target (cfg_101 0 (k + 1) u b c d) (cfg_65 (u + 1) k 0 b c d) := by
  have h1 : ReachesPlus target (cfg_101 0 (k + 1) u b c d)
      (cfg_65 0 k (u + 1) b c d) := by
    refine reachesPlus_of_multiStep 9 (by decide) ?_
    sim_steps
  have h2 := shift_65_step (u + 1) 0 k b c d
  rw [Nat.zero_add] at h2
  exact h1.trans_star h2

private theorem step_65_ge2 (a k b c d : ℕ) :
    ReachesPlus target (cfg_65 a k 0 (b + 2) c d) (cfg_101 0 k (a + 1) b c d) := by
  have h1 : ReachesPlus target (cfg_65 a k 0 (b + 2) c d)
      (cfg_101 (a + 1) k 0 b c d) := by
    refine reachesPlus_of_multiStep 9 (by decide) ?_
    sim_steps
  have h2 := shift_101_step (a + 1) k 0 b c d
  rw [Nat.zero_add] at h2
  exact h1.trans_star h2

private theorem step_65_b1_c_succ (a k c d : ℕ) :
    ReachesPlus target (cfg_65 a k 0 1 (c + 1) d)
      (cfg_89 0 k (2 * a + 4) (c + 1) d) := by
  have h1 : ReachesPlus target (cfg_65 a k 0 1 (c + 1) d)
      (cfg_89 (a + 1) k 2 (c + 1) d) := by
    refine reachesPlus_of_multiStep 7 (by decide) ?_
    sim_steps
  have h2 := shift_89_step (a + 1) k 2 (c + 1) d
  have h_eq : 2 + 2 * (a + 1) = 2 * a + 4 := by omega
  rw [h_eq] at h2
  exact h1.trans_star h2

private theorem step_65_b1_c0_d0 (a k : ℕ) :
    ReachesPlus target (cfg_65 a k 0 1 0 0) (cfg_89 0 k (2 * a + 4) 0 0) := by
  have h1 : ReachesPlus target (cfg_65 a k 0 1 0 0) (cfg_89 (a + 1) k 2 0 0) := by
    refine reachesPlus_of_multiStep 7 (by decide) ?_
    sim_steps
  have h2 := shift_89_step (a + 1) k 2 0 0
  have h_eq : 2 + 2 * (a + 1) = 2 * a + 4 := by omega
  rw [h_eq] at h2
  exact h1.trans_star h2

private theorem step_65_b0_d0_to_sweep (a k c : ℕ) :
    ReachesPlus target (cfg_65 a k 0 0 c 0) (cfg_65_sweep 0 k (a + c)) := by
  have h_eq : cfg_65 a k 0 0 c 0 = cfg_65 a k c 0 0 0 := by
    unfold cfg_65
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq]
  have h1 := shift_65_step c a k 0 0 0
  have h2 : ReachesPlus target (cfg_65 (a + c) k 0 0 0 0)
      (cfg_65_sweep (a + c) k 0) := by
    refine reachesPlus_of_multiStep 12 (by decide) ?_
    sim_steps
    rw [append_10_pow_cons_one]
  have h3 := shift_65_sweep_step (a + c) k 0
  rw [Nat.zero_add] at h3
  exact (h1.trans_plus h2).trans_star h3

private theorem reach_101_succ_ge2 (k u b c d : ℕ) :
    ReachesPlus target (cfg_101 0 (k + 1) u (b + 2) c d)
      (cfg_101 0 k (u + 2) b c d) :=
  (step_101_to_65 k u (b + 2) c d).trans (step_65_ge2 (u + 1) k b c d)

private theorem reach_101_succ_b1_c_succ (k u c d : ℕ) :
    ReachesPlus target (cfg_101 0 (k + 1) u 1 (c + 1) d)
      (cfg_89 0 k (2 * u + 6) (c + 1) d) := by
  have h := (step_101_to_65 k u 1 (c + 1) d).trans (step_65_b1_c_succ (u + 1) k c d)
  have h_eq : 2 * (u + 1) + 4 = 2 * u + 6 := by omega
  rwa [h_eq] at h

private theorem reach_101_succ_b1_c0_d0 (k u : ℕ) :
    ReachesPlus target (cfg_101 0 (k + 1) u 1 0 0)
      (cfg_89 0 k (2 * u + 6) 0 0) := by
  have h := (step_101_to_65 k u 1 0 0).trans (step_65_b1_c0_d0 (u + 1) k)
  have h_eq : 2 * (u + 1) + 4 = 2 * u + 6 := by omega
  rwa [h_eq] at h

private theorem reach_101_succ_b1_c0_succ (k u d : ℕ) :
    ReachesPlus target (cfg_101 0 (k + 1) u 1 0 (d + 1))
      (cfg_101 0 k (u + 2) d 0 0) := by
  have h_eq : cfg_101 0 (k + 1) u 1 0 (d + 1) = cfg_101 0 (k + 1) u (d + 2) 0 0 := by
    unfold cfg_101
    rw [left_bcd_one_zero]
  rw [h_eq]
  exact reach_101_succ_ge2 k u d 0 0

private theorem reach_101_succ_b0_ge2 (k u c d : ℕ) :
    ReachesPlus target (cfg_101 0 (k + 1) u 0 c (d + 2))
      (cfg_101 0 k (u + c + 2) d 0 0) := by
  have h1 := step_101_to_65 k u 0 c (d + 2)
  have h_eq : cfg_65 (u + 1) k 0 0 c (d + 2) = cfg_65 (u + 1) k c (d + 2) 0 0 := by
    unfold cfg_65
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq] at h1
  have h2 := h1.trans_star (shift_65_step c (u + 1) k (d + 2) 0 0)
  have h3 := h2.trans (step_65_ge2 (u + 1 + c) k d 0 0)
  have h_idx : u + 1 + c + 1 = u + c + 2 := by omega
  rwa [h_idx] at h3

private theorem reach_101_succ_b0_d1 (k u c : ℕ) :
    ReachesPlus target (cfg_101 0 (k + 1) u 0 c 1)
      (cfg_89 0 k (2 * (u + c) + 6) 0 0) := by
  have h1 := step_101_to_65 k u 0 c 1
  have h_eq : cfg_65 (u + 1) k 0 0 c 1 = cfg_65 (u + 1) k c 1 0 0 := by
    unfold cfg_65
    rw [append_0_cons_1_left_bcd_zero]
  rw [h_eq] at h1
  have h2 := h1.trans_star (shift_65_step c (u + 1) k 1 0 0)
  have h3 := h2.trans (step_65_b1_c0_d0 (u + 1 + c) k)
  have h_idx : 2 * (u + 1 + c) + 4 = 2 * (u + c) + 6 := by omega
  rwa [h_idx] at h3

private theorem reach_101_succ_b0_d0_k0 (u c : ℕ) :
    ReachesPlus target (cfg_101 0 1 u 0 c 0) (cfg_C 0 0 (u + c + 5) 1) := by
  have h := ((step_101_to_65 0 u 0 c 0).trans
    (step_65_b0_d0_to_sweep (u + 1) 0 c)).trans (reach_65_sweep_k0 (u + 1 + c))
  have h_idx : u + 1 + c + 4 = u + c + 5 := by omega
  rwa [h_idx] at h

private theorem reach_101_succ_b0_d0_k1 (u c : ℕ) :
    ReachesPlus target (cfg_101 0 2 u 0 c 0) (cfg_C 0 3 (u + c + 5) 1) := by
  have h := ((step_101_to_65 1 u 0 c 0).trans
    (step_65_b0_d0_to_sweep (u + 1) 1 c)).trans (reach_65_sweep_k1 (u + 1 + c))
  have h_idx : u + 1 + c + 4 = u + c + 5 := by omega
  rwa [h_idx] at h

private theorem reach_101_succ_b0_d0_k2 (u c : ℕ) :
    ReachesPlus target (cfg_101 0 3 u 0 c 0) (cfg_C 0 4 (u + c + 5) 1) := by
  have h := ((step_101_to_65 2 u 0 c 0).trans
    (step_65_b0_d0_to_sweep (u + 1) 2 c)).trans (reach_65_sweep_k2 (u + 1 + c))
  have h_idx : u + 1 + c + 4 = u + c + 5 := by omega
  rwa [h_idx] at h

private theorem reach_101_succ_b0_d0_ge3 (k u c : ℕ) :
    ReachesPlus target (cfg_101 0 (k + 4) u 0 c 0)
      (cfg_89 0 k 2 (u + c + 5) 1) := by
  have h := ((step_101_to_65 (k + 3) u 0 c 0).trans
    (step_65_b0_d0_to_sweep (u + 1) (k + 3) c)).trans (reach_65_sweep_ge3 k (u + 1 + c))
  have h_idx : u + 1 + c + 4 = u + c + 5 := by omega
  rwa [h_idx] at h

private theorem step_C_a0_succ (b c d : ℕ) :
    ReachesPlus target (cfg_C 0 (b + 1) c d) (cfg_31 0 0 b c d) := by
  refine reachesPlus_of_multiStep 14 (by decide) ?_
  sim_steps

private theorem reach_C_a0_b1_halt (c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C 0 1 c 0) cfg' ∧ (step target cfg').isNone := by
  obtain ⟨cfg', hp, hh⟩ := reach_31_b0_halt 0 0 c
  exact ⟨cfg', (step_C_a0_succ 0 c 0).trans hp, hh⟩

private theorem reach_C_a0_b1_succ (c d : ℕ) :
    ReachesPlus target (cfg_C 0 1 c (d + 1)) (cfg_C (c + 2) d 0 0) := by
  have h := (step_C_a0_succ 0 c (d + 1)).trans (reach_31_b0_succ 0 0 c d)
  have h_eq : 0 + 0 + c + 2 = c + 2 := by omega
  rwa [h_eq] at h

private theorem reach_C_a0_ge2 (b c d : ℕ) :
    ReachesPlus target (cfg_C 0 (b + 2) c d) (cfg_C 2 b c d) :=
  (step_C_a0_succ (b + 1) c d).trans (reach_31_succ 0 0 b c d)

private theorem reach_C_a1_succ (b c d : ℕ) :
    ReachesPlus target (cfg_C 1 (b + 1) c d) (cfg_57 0 0 (b + 2) c d) := by
  refine reachesPlus_of_multiStep 5 (by decide) ?_
  sim_steps

private theorem reach_C_ge2_succ (k b c d : ℕ) :
    ReachesPlus target (cfg_C (k + 2) (b + 1) c d) (cfg_101 0 k 0 b c d) := by
  refine reachesPlus_of_multiStep 14 (by decide) ?_
  sim_steps

private theorem reach_C_a0_b0_c_succ (c d : ℕ) :
    ReachesPlus target (cfg_C 0 0 (c + 1) d) (cfg_C 0 3 (c + 1) d) := by
  have h1 : ReachesPlus target (cfg_C 0 0 (c + 1) d) (cfg_21 0 2 (c + 1) d) := by
    refine reachesPlus_of_multiStep 12 (by decide) ?_
    sim_steps
  exact h1.trans (reach_21 0 2 (c + 1) d)

private theorem reach_C_a1_b0_c_succ (c d : ℕ) :
    ReachesPlus target (cfg_C 1 0 (c + 1) d) (cfg_57 0 0 1 (c + 1) d) := by
  refine reachesPlus_of_multiStep 5 (by decide) ?_
  sim_steps

private theorem reach_C_ge2_b0_c_succ (k c d : ℕ) :
    ReachesPlus target (cfg_C (k + 2) 0 (c + 1) d) (cfg_89 0 k 2 (c + 1) d) := by
  refine reachesPlus_of_multiStep 12 (by decide) ?_
  sim_steps

private theorem reach_C_a0_b0_c0_d0 :
    ReachesPlus target (cfg_C 0 0 0 0) (cfg_C 0 3 0 0) := by
  have h1 : ReachesPlus target (cfg_C 0 0 0 0) (cfg_21 0 2 0 0) := by
    refine reachesPlus_of_multiStep 12 (by decide) ?_
    sim_steps
  exact h1.trans (reach_21 0 2 0 0)

private theorem reach_C_a1_b0_c0_d0 :
    ReachesPlus target (cfg_C 1 0 0 0) (cfg_57 0 0 1 0 0) := by
  refine reachesPlus_of_multiStep 5 (by decide) ?_
  sim_steps

private theorem reach_C_ge2_b0_c0_d0 (k : ℕ) :
    ReachesPlus target (cfg_C (k + 2) 0 0 0) (cfg_89 0 k 2 0 0) := by
  refine reachesPlus_of_multiStep 12 (by decide) ?_
  sim_steps

private theorem init_reaches_start : ReachesStar target (init []) (cfg_C 0 3 0 0) := by
  have h1 : multiStep target (init []) 13 = some (cfg_0 1) := by
    have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = Cfg.headRight A default default := rfl
    rw [h_init]
    sim_steps
  have h2 : multiStep target (cfg_0 1) 20 = some (cfg_C 0 3 0 0) := by
    sim_steps
  exact ⟨33, multiStep_trans h1 h2⟩

/-! ## Level A: Closed Pattern Set (`IsClosedPatternSet`) -/

private theorem closed_8 (a b c d : ℕ) :
    StepsToClosed target ps (cfg_8 a 0 b c d) := by
  rcases b with _ | _ | _ | b
  · rcases d with _ | _ | _ | d
    · exact ⟨_, reach_8_b0_d0 a c, Or.inl (in_ps_C 0 (2 * (a + c) + 7) 0 0)⟩
    · exact ⟨_, reach_8_b0_d1 a c, Or.inl (in_ps_C 0 (2 * (a + c) + 5) 0 0)⟩
    · obtain ⟨cfg', hp, hh⟩ := reach_8_b0_d2_halt a c
      exact ⟨cfg', hp, Or.inr hh⟩
    · exact ⟨_, reach_8_b0_ge3 a c d, Or.inl (in_ps_C (a + c + 3) d 0 0)⟩
  · rcases c with _ | c
    · rcases d with _ | _ | d
      · exact ⟨_, reach_8_b1_c0_d0 a, Or.inl (in_ps_C 0 (2 * a + 5) 0 0)⟩
      · obtain ⟨cfg', hp, hh⟩ := reach_8_b1_c0_halt a
        exact ⟨cfg', hp, Or.inr hh⟩
      · exact ⟨_, reach_8_b1_c0_ge2 a d, Or.inl (in_ps_C (a + 3) d 0 0)⟩
    · exact ⟨_, reach_8_b1_c_succ a c d, Or.inl (in_ps_C 0 (2 * a + 5) (c + 1) d)⟩
  · rcases d with _ | d
    · obtain ⟨cfg', hp, hh⟩ := reach_8_b2_halt a c
      exact ⟨cfg', hp, Or.inr hh⟩
    · exact ⟨_, reach_8_b2_succ a c d, Or.inl (in_ps_C (a + c + 3) d 0 0)⟩
  · exact ⟨_, reach_8_ge3 a b c d, Or.inl (in_ps_C (a + 3) b c d)⟩

private theorem closed_57 (a b c d : ℕ) :
    StepsToClosed target ps (cfg_57 a 0 b c d) := by
  rcases b with _ | _ | b
  · rcases d with _ | _ | d
    · exact ⟨_, reach_57_b0_d0 a c, Or.inl (in_ps_C (a + c + 2) 0 0 0)⟩
    · exact ⟨_, reach_57_b0_d1 a c, Or.inl (in_ps_C 0 (2 * (a + c) + 4) 0 0)⟩
    · exact StepsToClosed.of_reachesPlus (reach_57_b0_ge2 a c d) (closed_8 (a + c + 1) d 0 0)
  · rcases c with _ | c
    · rcases d with _ | d
      · exact ⟨_, reach_57_b1_c0_d0 a, Or.inl (in_ps_C 0 (2 * a + 4) 0 0)⟩
      · exact StepsToClosed.of_reachesPlus (reach_57_b1_c0_succ a d) (closed_8 (a + 1) d 0 0)
    · exact ⟨_, reach_57_b1_c_succ a c d, Or.inl (in_ps_C 0 (2 * a + 4) (c + 1) d)⟩
  · exact StepsToClosed.of_reachesPlus (reach_57_ge2 a b c d) (closed_8 (a + 1) b c d)

private theorem closed_89_aux (k b c d : ℕ)
    (ih : ∀ m < k, ∀ u b' c' d', StepsToClosed target ps (cfg_101 0 m u b' c' d')) :
    StepsToClosed target ps (cfg_89 0 k b c d) := by
  rcases k with _ | _ | k
  · exact ⟨_, reach_89_k0 b c d, Or.inl (in_ps_C 2 b c d)⟩
  · exact StepsToClosed.of_reachesPlus (reach_89_k1 b c d) (closed_57 0 (b + 3) c d)
  · exact StepsToClosed.of_reachesPlus (reach_89_ge2 k b c d)
      (ih k (by omega) 0 (b + 1) c d)

private theorem closed_101 (k u b c d : ℕ) :
    StepsToClosed target ps (cfg_101 0 k u b c d) := by
  induction k using Nat.strongRecOn generalizing u b c d with
  | ind k ih =>
    rcases k with _ | k
    · exact StepsToClosed.of_reachesPlus (reach_101_k0 u b c d) (closed_57 (u + 2) b c d)
    · rcases b with _ | _ | b
      · rcases d with _ | _ | d
        · rcases k with _ | _ | _ | k
          · exact ⟨_, reach_101_succ_b0_d0_k0 u c, Or.inl (in_ps_C 0 0 (u + c + 5) 1)⟩
          · exact ⟨_, reach_101_succ_b0_d0_k1 u c, Or.inl (in_ps_C 0 3 (u + c + 5) 1)⟩
          · exact ⟨_, reach_101_succ_b0_d0_k2 u c, Or.inl (in_ps_C 0 4 (u + c + 5) 1)⟩
          · exact StepsToClosed.of_reachesPlus (reach_101_succ_b0_d0_ge3 k u c)
              (closed_89_aux k 2 (u + c + 5) 1 (fun m hm => ih m (by omega)))
        · exact StepsToClosed.of_reachesPlus (reach_101_succ_b0_d1 k u c)
            (closed_89_aux k (2 * (u + c) + 6) 0 0 (fun m hm => ih m (by omega)))
        · exact StepsToClosed.of_reachesPlus (reach_101_succ_b0_ge2 k u c d)
            (ih k (by omega) (u + c + 2) d 0 0)
      · rcases c with _ | c
        · rcases d with _ | d
          · exact StepsToClosed.of_reachesPlus (reach_101_succ_b1_c0_d0 k u)
              (closed_89_aux k (2 * u + 6) 0 0 (fun m hm => ih m (by omega)))
          · exact StepsToClosed.of_reachesPlus (reach_101_succ_b1_c0_succ k u d)
              (ih k (by omega) (u + 2) d 0 0)
        · exact StepsToClosed.of_reachesPlus (reach_101_succ_b1_c_succ k u c d)
            (closed_89_aux k (2 * u + 6) (c + 1) d (fun m hm => ih m (by omega)))
      · exact StepsToClosed.of_reachesPlus (reach_101_succ_ge2 k u b c d)
          (ih k (by omega) (u + 2) b c d)

private theorem closed_89 (k b c d : ℕ) :
    StepsToClosed target ps (cfg_89 0 k b c d) :=
  closed_89_aux k b c d (fun m _ => closed_101 m)

private theorem closed_C_pos (a b c d : ℕ) :
    StepsToClosed target ps (cfg_C a (b + 1) c d) := by
  rcases a with _ | _ | k
  · rcases b with _ | b
    · rcases d with _ | d
      · obtain ⟨cfg', hp, hh⟩ := reach_C_a0_b1_halt c
        exact ⟨cfg', hp, Or.inr hh⟩
      · exact ⟨_, reach_C_a0_b1_succ c d, Or.inl (in_ps_C (c + 2) d 0 0)⟩
    · exact ⟨_, reach_C_a0_ge2 b c d, Or.inl (in_ps_C 2 b c d)⟩
  · exact StepsToClosed.of_reachesPlus (reach_C_a1_succ b c d) (closed_57 0 (b + 2) c d)
  · exact StepsToClosed.of_reachesPlus (reach_C_ge2_succ k b c d) (closed_101 k 0 b c d)

private theorem closed_C (a b c d : ℕ) :
    StepsToClosed target ps (cfg_C a b c d) := by
  rcases b with _ | b
  · rcases c with _ | c
    · rcases d with _ | d
      · rcases a with _ | _ | k
        · exact ⟨_, reach_C_a0_b0_c0_d0, Or.inl (in_ps_C 0 3 0 0)⟩
        · exact StepsToClosed.of_reachesPlus reach_C_a1_b0_c0_d0 (closed_57 0 1 0 0)
        · exact StepsToClosed.of_reachesPlus (reach_C_ge2_b0_c0_d0 k) (closed_89 k 2 0 0)
      · have h_eq : cfg_C a 0 0 (d + 1) = cfg_C a (d + 1) 0 0 := by
          unfold cfg_C
          rw [left_bcd_zero_zero]
        rw [h_eq]
        exact closed_C_pos a d 0 0
    · rcases a with _ | _ | k
      · exact ⟨_, reach_C_a0_b0_c_succ c d, Or.inl (in_ps_C 0 3 (c + 1) d)⟩
      · exact StepsToClosed.of_reachesPlus (reach_C_a1_b0_c_succ c d)
          (closed_57 0 1 (c + 1) d)
      · exact StepsToClosed.of_reachesPlus (reach_C_ge2_b0_c_succ k c d)
          (closed_89 k 2 (c + 1) d)
  · exact closed_C_pos a b c d

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_C 0 3 0 0, init_reaches_start, in_ps_C 0 3 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_C]
  exact closed_C (vars 0) (vars 1) (vars 2) (vars 3)

/-- `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Level B: Collatz-Like Acceleration (`IsValidAcceleration`) -/

/-- Symbolic configuration state space for `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE`. -/
inductive State where
  /-- $C(a, b, c, d) := 0^\infty\,1^d\,(10)^c\,1^b\,\mathrm{C}{>}\,110\,(10)^a\,1\,0^\infty$. -/
  | C (a b c d : ℕ)
  /-- $W(k, b, c, d) := 0^\infty\,1^d\,(10)^c\,1^b\,\mathrm{E}{>}\,11110\,(10)^k\,1\,0^\infty$. -/
  | W (k b c d : ℕ)
  /-- $M(k, u, b, c, d) :=
    0^\infty\,1^d\,(10)^c\,1^{b+1}\,(01)^u\,10\,\mathrm{E}{>}\,01110\,(10)^k\,1\,0^\infty$. -/
  | M (k u b c d : ℕ)
  /-- $S(a, b, c, d) := 0^\infty\,1^d\,(10)^c\,1^{b+1}\,0\,\mathrm{A}{>}\,111\,(11)^a\,0^\infty$. -/
  | S (a b c d : ℕ)
  /-- $R(a, b, c, d) :=
    0^\infty\,1^d\,(10)^c\,1^{b+1}\,0\,\mathrm{A}{>}\,1111\,(11)^a\,0^\infty$. -/
  | R (a b c d : ℕ)

/-- Initial symbolic state $C(0, 3, 0, 0)$, reached after 33 raw TM steps. -/
def start : State := .C 0 3 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b c d => cfg_C a b c d
  | .W k b c d => cfg_89 0 k b c d
  | .M k u b c d => cfg_101 0 k u b c d
  | .S a b c d => cfg_57 a 0 b c d
  | .R a b c d => cfg_8 a 0 b c d

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .C 0 0 0 0 => some (.C 0 3 0 0)
  | .C 1 0 0 0 => some (.S 0 1 0 0)
  | .C (k + 2) 0 0 0 => some (.W k 2 0 0)
  | .C 0 0 0 1 => none
  | .C 0 0 0 (d + 2) => some (.C 2 d 0 0)
  | .C 1 0 0 (d + 1) => some (.S 0 (d + 2) 0 0)
  | .C (k + 2) 0 0 (d + 1) => some (.M k 0 d 0 0)
  | .C 0 0 (c + 1) d => some (.C 0 3 (c + 1) d)
  | .C 1 0 (c + 1) d => some (.S 0 1 (c + 1) d)
  | .C (k + 2) 0 (c + 1) d => some (.W k 2 (c + 1) d)
  | .C 0 1 _ 0 => none
  | .C 0 1 c (d + 1) => some (.C (c + 2) d 0 0)
  | .C 0 (b + 2) c d => some (.C 2 b c d)
  | .C 1 (b + 1) c d => some (.S 0 (b + 2) c d)
  | .C (k + 2) (b + 1) c d => some (.M k 0 b c d)
  | .W 0 b c d => some (.C 2 b c d)
  | .W 1 b c d => some (.S 0 (b + 3) c d)
  | .W (k + 2) b c d => some (.M k 0 (b + 1) c d)
  | .M 0 u b c d => some (.S (u + 2) b c d)
  | .M 1 u 0 c 0 => some (.C 0 0 (u + c + 5) 1)
  | .M 2 u 0 c 0 => some (.C 0 3 (u + c + 5) 1)
  | .M 3 u 0 c 0 => some (.C 0 4 (u + c + 5) 1)
  | .M (k + 4) u 0 c 0 => some (.W k 2 (u + c + 5) 1)
  | .M (k + 1) u 0 c 1 => some (.W k (2 * (u + c) + 6) 0 0)
  | .M (k + 1) u 0 c (d + 2) => some (.M k (u + c + 2) d 0 0)
  | .M (k + 1) u 1 0 0 => some (.W k (2 * u + 6) 0 0)
  | .M (k + 1) u 1 0 (d + 1) => some (.M k (u + 2) d 0 0)
  | .M (k + 1) u 1 (c + 1) d => some (.W k (2 * u + 6) (c + 1) d)
  | .M (k + 1) u (b + 2) c d => some (.M k (u + 2) b c d)
  | .S a 0 c 0 => some (.C (a + c + 2) 0 0 0)
  | .S a 0 c 1 => some (.C 0 (2 * (a + c) + 4) 0 0)
  | .S a 0 c (d + 2) => some (.R (a + c + 1) d 0 0)
  | .S a 1 0 0 => some (.C 0 (2 * a + 4) 0 0)
  | .S a 1 0 (d + 1) => some (.R (a + 1) d 0 0)
  | .S a 1 (c + 1) d => some (.C 0 (2 * a + 4) (c + 1) d)
  | .S a (b + 2) c d => some (.R (a + 1) b c d)
  | .R a 0 c 0 => some (.C 0 (2 * (a + c) + 7) 0 0)
  | .R a 0 c 1 => some (.C 0 (2 * (a + c) + 5) 0 0)
  | .R _ 0 _ 2 => none
  | .R a 0 c (d + 3) => some (.C (a + c + 3) d 0 0)
  | .R a 1 0 0 => some (.C 0 (2 * a + 5) 0 0)
  | .R _ 1 0 1 => none
  | .R a 1 0 (d + 2) => some (.C (a + 3) d 0 0)
  | .R a 1 (c + 1) d => some (.C 0 (2 * a + 5) (c + 1) d)
  | .R _ 2 _ 0 => none
  | .R a 2 c (d + 1) => some (.C (a + c + 3) d 0 0)
  | .R a (b + 3) c d => some (.C (a + 3) b c d)

private theorem step_some_C (a b c d : ℕ) (s' : State)
    (hnext : next (.C a b c d) = some s') :
    ReachesPlus target (encode (.C a b c d)) (encode s') := by
  rcases b with _ | b
  · rcases c with _ | c
    · rcases d with _ | d
      · rcases a with _ | _ | k
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_C_a0_b0_c0_d0
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_C_a1_b0_c0_d0
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_C_ge2_b0_c0_d0 k
      · have h_eq : encode (.C a 0 0 (d + 1)) = cfg_C a (d + 1) 0 0 := by
          dsimp only [encode]
          unfold cfg_C
          rw [left_bcd_zero_zero]
        rw [h_eq]
        rcases a with _ | _ | k
        · rcases d with _ | d
          · simp [next] at hnext
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            exact reach_C_a0_ge2 d 0 0
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_C_a1_succ d 0 0
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_C_ge2_succ k d 0 0
    · rcases a with _ | _ | k
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact reach_C_a0_b0_c_succ c d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact reach_C_a1_b0_c_succ c d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact reach_C_ge2_b0_c_succ k c d
  · rcases a with _ | _ | k
    · rcases b with _ | b
      · rcases d with _ | d
        · simp [next] at hnext
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_C_a0_b1_succ c d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact reach_C_a0_ge2 b c d
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_C_a1_succ b c d
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_C_ge2_succ k b c d

private theorem step_some_W (k b c d : ℕ) (s' : State)
    (hnext : next (.W k b c d) = some s') :
    ReachesPlus target (encode (.W k b c d)) (encode s') := by
  rcases k with _ | _ | k
  · simp only [next, Option.some.injEq] at hnext
    subst hnext
    exact reach_89_k0 b c d
  · simp only [next, Option.some.injEq] at hnext
    subst hnext
    exact reach_89_k1 b c d
  · simp only [next, Option.some.injEq] at hnext
    subst hnext
    exact reach_89_ge2 k b c d

private theorem step_some_M (k u b c d : ℕ) (s' : State)
    (hnext : next (.M k u b c d) = some s') :
    ReachesPlus target (encode (.M k u b c d)) (encode s') := by
  rcases k with _ | k
  · simp only [next, Option.some.injEq] at hnext
    subst hnext
    exact reach_101_k0 u b c d
  · rcases b with _ | _ | b
    · rcases d with _ | _ | d
      · rcases k with _ | _ | _ | k
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_101_succ_b0_d0_k0 u c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_101_succ_b0_d0_k1 u c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_101_succ_b0_d0_k2 u c
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_101_succ_b0_d0_ge3 k u c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact reach_101_succ_b0_d1 k u c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact reach_101_succ_b0_ge2 k u c d
    · rcases c with _ | c
      · rcases d with _ | d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_101_succ_b1_c0_d0 k u
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact reach_101_succ_b1_c0_succ k u d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact reach_101_succ_b1_c_succ k u c d
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_101_succ_ge2 k u b c d

private theorem step_some_S (a b c d : ℕ) (s' : State)
    (hnext : next (.S a b c d) = some s') :
    ReachesPlus target (encode (.S a b c d)) (encode s') := by
  rcases b with _ | _ | b
  · rcases d with _ | _ | d
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_57_b0_d0 a c
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_57_b0_d1 a c
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_57_b0_ge2 a c d
  · rcases c with _ | c
    · rcases d with _ | d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact reach_57_b1_c0_d0 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact reach_57_b1_c0_succ a d
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_57_b1_c_succ a c d
  · simp only [next, Option.some.injEq] at hnext
    subst hnext
    exact reach_57_ge2 a b c d

private theorem step_some_R (a b c d : ℕ) (s' : State)
    (hnext : next (.R a b c d) = some s') :
    ReachesPlus target (encode (.R a b c d)) (encode s') := by
  rcases b with _ | _ | _ | b
  · rcases d with _ | _ | _ | d
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_8_b0_d0 a c
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_8_b0_d1 a c
    · simp [next] at hnext
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_8_b0_ge3 a c d
  · rcases c with _ | c
    · rcases d with _ | _ | d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact reach_8_b1_c0_d0 a
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact reach_8_b1_c0_ge2 a d
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_8_b1_c_succ a c d
  · rcases d with _ | d
    · simp [next] at hnext
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact reach_8_b2_succ a c d
  · simp only [next, Option.some.injEq] at hnext
    subst hnext
    exact reach_8_ge3 a b c d

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro (⟨a, b, c, d⟩ | ⟨k, b, c, d⟩ | ⟨k, u, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩) s' hnext
    · exact step_some_C a b c d s' hnext
    · exact step_some_W k b c d s' hnext
    · exact step_some_M k u b c d s' hnext
    · exact step_some_S a b c d s' hnext
    · exact step_some_R a b c d s' hnext
  step_none := by
    rintro (⟨a, b, c, d⟩ | ⟨k, b, c, d⟩ | ⟨k, u, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩) hnext
    · rcases b with _ | b
      · rcases c with _ | c
        · rcases d with _ | _ | d
          · rcases a with _ | _ | k <;> simp [next] at hnext
          · rcases a with _ | _ | k
            · have h_eq : encode (.C 0 0 0 1) = cfg_C 0 1 0 0 := by
                dsimp only [encode]
                unfold cfg_C
                rw [left_bcd_zero_zero]
              rw [h_eq]
              obtain ⟨cfg', hp, hh⟩ := reach_C_a0_b1_halt 0
              exact ⟨cfg', hp.to_star, hh⟩
            · simp [next] at hnext
            · simp [next] at hnext
          · rcases a with _ | _ | k <;> simp [next] at hnext
        · rcases a with _ | _ | k <;> simp [next] at hnext
      · rcases a with _ | _ | k
        · rcases b with _ | b
          · rcases d with _ | d
            · obtain ⟨cfg', hp, hh⟩ := reach_C_a0_b1_halt c
              exact ⟨cfg', hp.to_star, hh⟩
            · simp [next] at hnext
          · simp [next] at hnext
        · simp [next] at hnext
        · simp [next] at hnext
    · rcases k with _ | _ | k <;> simp [next] at hnext
    · rcases k with _ | k
      · simp [next] at hnext
      · rcases b with _ | _ | b
        · rcases d with _ | _ | d
          · rcases k with _ | _ | _ | k <;> simp [next] at hnext
          · simp [next] at hnext
          · simp [next] at hnext
        · rcases c with _ | c
          · rcases d with _ | d <;> simp [next] at hnext
          · simp [next] at hnext
        · simp [next] at hnext
    · rcases b with _ | _ | b
      · rcases d with _ | _ | d <;> simp [next] at hnext
      · rcases c with _ | c
        · rcases d with _ | d <;> simp [next] at hnext
        · simp [next] at hnext
      · simp [next] at hnext
    · rcases b with _ | _ | _ | b
      · rcases d with _ | _ | _ | d
        · simp [next] at hnext
        · simp [next] at hnext
        · obtain ⟨cfg', hp, hh⟩ := reach_8_b0_d2_halt a c
          exact ⟨cfg', hp.to_star, hh⟩
        · simp [next] at hnext
      · rcases c with _ | c
        · rcases d with _ | _ | d
          · simp [next] at hnext
          · obtain ⟨cfg', hp, hh⟩ := reach_8_b1_c0_halt a
            exact ⟨cfg', hp.to_star, hh⟩
          · simp [next] at hnext
        · simp [next] at hnext
      · rcases d with _ | d
        · obtain ⟨cfg', hp, hh⟩ := reach_8_b2_halt a c
          exact ⟨cfg', hp.to_star, hh⟩
        · simp [next] at hnext
      · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-like Acceleration -/

/-- Canonical high-level state space eliminating the transient families `W`, `M`, `S`, and `R`. -/
inductive HighLevelState where
  /-- $C_0(a, b) := C(a, b, 0, 0) = 0^\infty\,1^b\,\mathrm{C}{>}\,110\,(10)^a\,1\,0^\infty$. -/
  | C0 (a b : ℕ)
  /-- $C_1(a, b, c) := C(a, b, c, 1) =
    0^\infty\,1\,(10)^c\,1^b\,\mathrm{C}{>}\,110\,(10)^a\,1\,0^\infty$. -/
  | C1 (a b c : ℕ)
  deriving DecidableEq, Repr

/-- Initial state $C_0(0, 3)$ for the high-level Collatz-like acceleration. -/
def highLevelStart : HighLevelState := .C0 0 3

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .C0 a b => .C a b 0 0
  | .C1 a b c => .C a b c 1

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Outcome of `State.R a b (if d1 then c else 0) (if d1 then 1 else 0)`. -/
def evalR (a b c : ℕ) (d1 : Bool) : Option HighLevelState :=
  if b = 0 then
    if !d1 then some (.C0 0 (2 * a + 7))
    else some (.C0 0 (2 * (a + c) + 5))
  else if b = 1 then
    if !d1 then some (.C0 0 (2 * a + 5))
    else if c = 0 then none
    else some (.C1 0 (2 * a + 5) c)
  else if b = 2 then
    if !d1 then none
    else some (.C0 (a + c + 3) 0)
  else
    if !d1 then some (.C0 (a + 3) (b - 3))
    else some (.C1 (a + 3) (b - 3) c)

/-- Outcome of `State.S a b (if d1 then c else 0) (if d1 then 1 else 0)`. -/
def evalS (a b c : ℕ) (d1 : Bool) : Option HighLevelState :=
  if b = 0 then
    if !d1 then some (.C0 (a + 2) 0)
    else some (.C0 0 (2 * (a + c) + 4))
  else if b = 1 then
    if !d1 then some (.C0 0 (2 * a + 4))
    else if c = 0 then evalR (a + 1) 0 0 false
    else some (.C1 0 (2 * a + 4) c)
  else
    evalR (a + 1) (b - 2) c d1

/-- Outcome of `State.M k u b (if d1 then c else 0) (if d1 then 1 else 0)`, decreasing in `k`. -/
def evalM (k u b c : ℕ) (d1 : Bool) : Option HighLevelState :=
  if k = 0 then
    evalS (u + 2) b c d1
  else
    let k' := k - 1
    if b = 0 then
      if !d1 then
        if k = 1 then some (.C1 0 0 (u + 5))
        else if k = 2 then some (.C1 0 3 (u + 5))
        else if k = 3 then some (.C1 0 4 (u + 5))
        else if k = 4 then some (.C1 2 2 (u + 5))
        else if k = 5 then evalS 0 5 (u + 5) true
        else evalM (k - 6) 0 3 (u + 5) true
      else
        if k' = 0 then some (.C0 2 (2 * (u + c) + 6))
        else if k' = 1 then evalS 0 (2 * (u + c) + 9) 0 false
        else evalM (k' - 2) 0 (2 * (u + c) + 7) 0 false
    else if b = 1 then
      if !d1 then
        if k' = 0 then some (.C0 2 (2 * u + 6))
        else if k' = 1 then evalS 0 (2 * u + 9) 0 false
        else evalM (k' - 2) 0 (2 * u + 7) 0 false
      else if c = 0 then
        evalM k' (u + 2) 0 0 false
      else
        if k' = 0 then some (.C1 2 (2 * u + 6) c)
        else if k' = 1 then evalS 0 (2 * u + 9) c true
        else evalM (k' - 2) 0 (2 * u + 7) c true
    else
      evalM k' (u + 2) (b - 2) c d1
termination_by k
decreasing_by all_goals omega

/-- Outcome of `State.W k b (if d1 then c else 0) (if d1 then 1 else 0)`. -/
def evalW (k b c : ℕ) (d1 : Bool) : Option HighLevelState :=
  if k = 0 then
    if d1 then some (.C1 2 b c) else some (.C0 2 b)
  else if k = 1 then
    evalS 0 (b + 3) c d1
  else
    evalM (k - 2) 0 (b + 1) c d1

/-- Outcome of `State.C a b (if d1 then c else 0) (if d1 then 1 else 0)` for `a ≥ 1`. -/
def evalCPos (a b c : ℕ) (d1 : Bool) : Option HighLevelState :=
  if b = 0 then
    if d1 && c == 0 then
      if a = 1 then evalS 0 2 0 false
      else evalM (a - 2) 0 0 0 false
    else
      if a = 1 then evalS 0 1 c d1
      else evalW (a - 2) 2 c d1
  else
    if a = 1 then evalS 0 (b + 1) c d1
    else evalM (a - 2) 0 (b - 1) c d1

/-- High-level accelerated Collatz-like transition function on `C0` and `C1`. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .C0 a b =>
    if a = 0 then
      if b = 0 then evalCPos 2 1 0 false
      else if b = 1 then none
      else evalCPos 2 (b - 2) 0 false
    else
      evalCPos a b 0 false
  | .C1 a b c =>
    if a = 0 then
      if b = 0 then
        if c = 0 then none
        else evalCPos 2 1 c true
      else if b = 1 then
        some (.C0 (c + 2) 0)
      else
        evalCPos 2 (b - 2) c true
    else
      evalCPos a b c true

private def cOf (c : ℕ) (d1 : Bool) : ℕ := if d1 then c else 0

private def dOf (d1 : Bool) : ℕ := if d1 then 1 else 0

private theorem stepsTo_R (a b c : ℕ) (d1 : Bool) :
    CollatzStepsTo next (.R a b (cOf c d1) (dOf d1)) ((evalR a b c d1).map toState) := by
  cases d1 <;> rcases b with _ | _ | _ | b'
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.of_eq rfl
  · rcases c with _ | c' <;> exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.of_eq rfl

private theorem stepsTo_S (a b c : ℕ) (d1 : Bool) :
    CollatzStepsTo next (.S a b (cOf c d1) (dOf d1)) ((evalS a b c d1).map toState) := by
  cases d1 <;> rcases b with _ | _ | b'
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.head rfl (stepsTo_R (a + 1) b' c false)
  · exact CollatzStepsTo.of_eq rfl
  · rcases c with _ | c'
    · exact CollatzStepsTo.head rfl (stepsTo_R (a + 1) 0 0 false)
    · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.head rfl (stepsTo_R (a + 1) b' c true)

private theorem stepsTo_M (k : ℕ) :
    ∀ (u b c : ℕ) (d1 : Bool),
      CollatzStepsTo next (.M k u b (cOf c d1) (dOf d1)) ((evalM k u b c d1).map toState) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro u b c d1
    rw [evalM]
    rcases k with _ | k'
    · exact CollatzStepsTo.head rfl (stepsTo_S (u + 2) b c d1)
    · rcases b with _ | _ | b'
      · cases d1
        · rcases k' with _ | _ | _ | _ | _ | k''
          · exact CollatzStepsTo.of_eq rfl
          · exact CollatzStepsTo.of_eq rfl
          · exact CollatzStepsTo.of_eq rfl
          · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
          · exact CollatzStepsTo.head rfl (CollatzStepsTo.head rfl (stepsTo_S 0 5 (u + 5) true))
          · exact CollatzStepsTo.head (s₂ := .W (k'' + 2) 2 (u + 5) 1) rfl
              (CollatzStepsTo.head rfl (ih k'' (by omega) 0 3 (u + 5) true))
        · refine CollatzStepsTo.head (s₂ := .W k' (2 * (u + c) + 6) 0 0)
            (by simp [next, cOf, dOf]) ?_
          rcases k' with _ | _ | k''
          · exact CollatzStepsTo.of_eq rfl
          · exact CollatzStepsTo.head rfl (stepsTo_S 0 (2 * (u + c) + 9) 0 false)
          · exact CollatzStepsTo.head rfl (ih k'' (by omega) 0 (2 * (u + c) + 7) 0 false)
      · cases d1
        · refine CollatzStepsTo.head (s₂ := .W k' (2 * u + 6) 0 0) (by simp [next, cOf, dOf]) ?_
          rcases k' with _ | _ | k''
          · exact CollatzStepsTo.of_eq rfl
          · exact CollatzStepsTo.head rfl (stepsTo_S 0 (2 * u + 9) 0 false)
          · exact CollatzStepsTo.head rfl (ih k'' (by omega) 0 (2 * u + 7) 0 false)
        · rcases c with _ | c'
          · exact CollatzStepsTo.head (by simp [next, cOf, dOf])
              (ih k' (by omega) (u + 2) 0 0 false)
          · refine CollatzStepsTo.head (s₂ := .W k' (2 * u + 6) (c' + 1) 1)
              (by simp [next, cOf, dOf]) ?_
            rcases k' with _ | _ | k''
            · exact CollatzStepsTo.of_eq rfl
            · exact CollatzStepsTo.head rfl (stepsTo_S 0 (2 * u + 9) (c' + 1) true)
            · exact CollatzStepsTo.head rfl (ih k'' (by omega) 0 (2 * u + 7) (c' + 1) true)
      · exact CollatzStepsTo.head (by simp [next]) (ih k' (by omega) (u + 2) b' c d1)

private theorem stepsTo_W (k b c : ℕ) (d1 : Bool) :
    CollatzStepsTo next (.W k b (cOf c d1) (dOf d1)) ((evalW k b c d1).map toState) := by
  rcases k with _ | _ | k'
  · cases d1 <;> exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.head rfl (stepsTo_S 0 (b + 3) c d1)
  · exact CollatzStepsTo.head rfl (stepsTo_M k' 0 (b + 1) c d1)

private theorem stepsTo_CPos (a' b c : ℕ) (d1 : Bool) :
    CollatzStepsTo next (.C (a' + 1) b (cOf c d1) (dOf d1))
      ((evalCPos (a' + 1) b c d1).map toState) := by
  rcases b with _ | b'
  · cases d1
    · rcases a' with _ | k
      · exact CollatzStepsTo.head rfl (stepsTo_S 0 1 c false)
      · exact CollatzStepsTo.head rfl (stepsTo_W k 2 c false)
    · rcases c with _ | c'
      · rcases a' with _ | k
        · exact CollatzStepsTo.head rfl (stepsTo_S 0 2 0 false)
        · exact CollatzStepsTo.head rfl (stepsTo_M k 0 0 0 false)
      · rcases a' with _ | k
        · exact CollatzStepsTo.head rfl (stepsTo_S 0 1 (c' + 1) true)
        · exact CollatzStepsTo.head rfl (stepsTo_W k 2 (c' + 1) true)
  · rcases a' with _ | k
    · exact CollatzStepsTo.head rfl (stepsTo_S 0 (b' + 2) c d1)
    · exact CollatzStepsTo.head rfl (stepsTo_M k 0 b' c d1)

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState)
    (CollatzReachesStar.refl next start) ?_
  rintro (⟨a, b⟩ | ⟨a, b, c⟩)
  · rcases a with _ | a'
    · rcases b with _ | _ | b'
      · exact CollatzStepsTo.head rfl (CollatzStepsTo.head rfl (stepsTo_CPos 1 1 0 false))
      · exact CollatzStepsTo.of_eq rfl
      · exact CollatzStepsTo.head rfl (stepsTo_CPos 1 b' 0 false)
    · exact stepsTo_CPos a' b 0 false
  · rcases a with _ | a'
    · rcases b with _ | _ | b'
      · rcases c with _ | c'
        · exact CollatzStepsTo.of_eq rfl
        · exact CollatzStepsTo.head rfl
            (CollatzStepsTo.head rfl (stepsTo_CPos 1 1 (c' + 1) true))
      · exact CollatzStepsTo.of_eq rfl
      · exact CollatzStepsTo.head rfl (stepsTo_CPos 1 b' c true)
    · exact stepsTo_CPos a' b c true

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

end BusyBeaver.M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE
