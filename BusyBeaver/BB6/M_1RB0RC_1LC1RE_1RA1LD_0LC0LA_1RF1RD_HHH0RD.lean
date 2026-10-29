/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD`

We define the configuration for $p \in \lbrace 0, 1 \rbrace$ and $k, c \ge 0$:

$$
S(p, k, c) := 0^\infty \ (1110)^p \ 1^k \ \mathrm{D}{>} \ 11 \ 1^c \ 0^\infty.
$$

Starting from $S(0, 2, 0)$ (reached after 10 steps from the blank tape), the machine follows the
map $T$, writing $k = 3q + r$ with $r \in \lbrace 0, 1, 2 \rbrace$ and $d = c - q$:

- If $c < q$: $T(S(p, k, c)) = S(p, k - 3c - 2, 4c + 5)$.
- If $c \ge q$ and $r = 0$:
  $$
  T(S(p, 3q, c)) = \begin{cases}
    S(0, 2, 3) & \text{if } p = 0,\ q = 0,\text{ and } c = 0, \\
    S(0, 4, c - 1) & \text{if } p = 0,\ q = 0,\text{ and } c \ge 1, \\
    S(1, 4q, 1) & \text{if } p = 0,\ q \ge 1,\text{ and } d = 0, \\
    S(1, 4q - 1, d) & \text{if } p = 0,\ q \ge 1,\text{ and } d \ge 1, \\
    S(0, 2, c + 2) & \text{if } p = 1 \text{ and } q = 0, \\
    S(0, 4, 4q + 5) & \text{if } p = 1,\ q \ge 1,\text{ and } d = 0, \\
    S(0, 1, 4q + 9) & \text{if } p = 1,\ q \ge 1,\text{ and } d = 1, \\
    S(1, 4q + 8, 1) & \text{if } p = 1,\ q \ge 1,\text{ and } d = 2, \\
    S(1, 4q + 7, d - 2) & \text{if } p = 1,\ q \ge 1,\text{ and } d \ge 3.
  \end{cases}
  $$
- If $c \ge q$ and $r = 1$:
  $$
  T(S(p, 3q + 1, c)) = \begin{cases}
    S(0, 0, 4q + 3) & \text{if } p = 0 \text{ and } d = 0, \\
    S(0, 8, 4q + 1) & \text{if } p = 1 \text{ and } d = 0, \\
    S(0, 4q + 3p + 4, 1) & \text{if } d = 1, \\
    S(0, 4q + 3p + 3, d - 1) & \text{if } d \ge 2.
  \end{cases}
  $$
- If $c \ge q$ and $r = 2$:
  $$
  T(S(p, 3q + 2, c)) = \begin{cases}
    S(p, 0, 4q + 5) & \text{if } d = 0, \\
    S(0, 0, 4q + 9) & \text{if } p = 1 \text{ and } d = 1, \\
    \text{Halt} & \text{if } d = p + 1, \\
    S(0, 4q + 4p + 6, 0) & \text{if } d = p + 2, \\
    S(0, 4q + 4p + 6, 3) & \text{if } d = p + 3, \\
    S(0, 4q + 4p + 8, d - p - 4) & \text{if } d \ge p + 4.
  \end{cases}
  $$

<!-- hardness:begin -->
## Hardness

*Hardness class:* Cascade — trigger **EQ**, growth exponential ($4^n$ inner cascades, $(4/3)^k$
sweeps), shield partial (odd-$a$ invariant kills 2 of 4 halting rules and 12 of 34 rules).

*Verdict (heuristic, from exact accelerated simulation of the certified rules):* probviously
non-halting.

*Hazard:* $P(\text{halt}) \lesssim 10^{-5}$ per era

*Simulated horizon:* exact rule simulation (see dossier)

*Why it is hard:* remaining halts `rule_4/12_halt` need $c_{\text{rem}}=1$: a $(4/3)^k$ Mahler-type
residue problem

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift Lemmas -/

private theorem shift_C_right (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{C}}> (([0, 1] : List (Fin 2)) ^ k +> r)) [target]⊢*
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    have h1 : (l {{C}}> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ k +> r)))
        [target]⊢*
        ((l <+ [0, 1]) {{C}}> (([0, 1] : List (Fin 2)) ^ k +> r)) := by
      bb_steps
    have h2 := ih (l <+ [0, 1]) r
    rw [ListBlank.append_pow_succ'] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_DC_left (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{D}}> ([0] +> r)) [target]⊢*
    (l {{D}}> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [list_pow_succ, ← ListBlank.append_append]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) {{D}}> ([0] +> r))
        [target]⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{D}}> ([0] +> ([1, 0] +> r))) := by
      bb_steps
    have h2 := ih l (([1, 0] : List (Fin 2)) +> r)
    rw [ListBlank.append_pow_succ'] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_C_left_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{C}}> ([1] +> r)) [target]⊢*
    (l {{C}}> ([1] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [list_pow_succ, ← ListBlank.append_append]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) {{C}}> ([1] +> r))
        [target]⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{C}}> ([1] +> ([1, 1] +> r))) := by
      bb_steps
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    rw [ListBlank.append_pow_succ'] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_E_0101 (m : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)) [target]⊢*
    ((l <+ ([1, 1, 1, 1] : List (Fin 2)) ^ m) {{E}}> r) := by
  induction m generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ m ih =>
    rw [ListBlank.append_pow_succ]
    have h1 : (l {{E}}> ([0, 1, 0, 1] +> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)))
        [target]⊢*
        ((l <+ [1, 1, 1, 1]) {{E}}> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)) := by
      bb_steps
    have h2 := ih (l <+ [1, 1, 1, 1]) r
    rw [ListBlank.append_pow_succ'] at h2
    exact ReachesStar.trans h1 h2

private theorem one_pow_four_mul (k : ℕ) :
    ([1, 1, 1, 1] : List (Fin 2)) ^ k = ([1] : List (Fin 2)) ^ (4 * k) :=
  (list_pow_mul [1] 4 k).symm

private theorem zero_one_pow_two_mul (m : ℕ) :
    ([0, 1] : List (Fin 2)) ^ (2 * m) = ([0, 1, 0, 1] : List (Fin 2)) ^ m :=
  list_pow_mul [0, 1] 2 m

/-! ## Canonical Pattern Set -/

private def cfg_D (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  (default : ListBlank (Fin 2)) {{D}}> (([0, 1] : List (Fin 2)) ^ a +> (([1] : List (Fin 2)) ^ b +>
      default))

abbrev cfg_A (l : ListBlank (Fin 2)) (k j c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (l <+ ([1] : List (Fin 2)) ^ k) {{D}}>
    ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> (([1] : List (Fin 2)) ^ c +> default)))

abbrev l_hat : ListBlank (Fin 2) :=
  ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]

abbrev l_ones3 : ListBlank (Fin 2) :=
  (default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3

abbrev cfg_C001 (l : ListBlank (Fin 2)) (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  l {{C}}> ([0, 0, 1] +> (([0, 1] : List (Fin 2)) ^ a +> (([1] : List (Fin 2)) ^ b +> default)))

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1] 0 (.rep [0, 1, 1, 1] 1 .default)
    head  := some D
    right := .sym 1 (.sym 1 (.rep [0, 1] 2 (.rep [1] 3 .default))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .not (.ge_const 1 2))]

private theorem eval_pat_A (vars : Nat -> Nat) :
    evalTapePattern pat_A vars =
    cfg_A (default <+ ([0, 1, 1, 1] : List (Fin 2)) ^ (vars 1)) (vars 0) (vars 2) (vars 3) := rfl

private theorem in_ps_S_def (k j c : Nat) : IsInPatternSet ps (cfg_A default k j c) := by
  refine ⟨(pat_A, .not (.ge_const 1 2)), List.Mem.head _,
    fun i => match i with | 0 => k | 1 => 0 | 2 => j | 3 => c | _ => 0, rfl, ?_⟩
  simp [evalVarCond]

private theorem in_ps_S_hat (k j c : Nat) : IsInPatternSet ps (cfg_A l_hat k j c) := by
  refine ⟨(pat_A, .not (.ge_const 1 2)), List.Mem.head _,
    fun i => match i with | 0 => k | 1 => 1 | 2 => j | 3 => c | _ => 0, rfl, ?_⟩
  simp [evalVarCond]

private theorem in_ps_S_ones3 (k j c : Nat) :
    IsInPatternSet ps (cfg_A (default <+ ([1] : List (Fin 2)) ^ 3) k j c) := by
  unfold cfg_A
  rw [← ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 k]
  exact in_ps_S_def (3 + k) j c

/-! ## Accelerated Transition Rules -/

private theorem step_C001_even_to_E (l : ListBlank (Fin 2)) (m : Nat) (r : ListBlank (Fin 2)) :
    (l {{C}}> ([0, 0, 1] +> (([0, 1] : List (Fin 2)) ^ (2 * m) +> r))) [target]⊢⁺
    ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}> r) := by
  rw [zero_one_pow_two_mul m]
  have h1 : (l {{C}}> ([0, 0, 1] +> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ 3) {{E}}> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  have h2 := shift_E_0101 m (l <+ ([1] : List (Fin 2)) ^ 3) r
  rw [one_pow_four_mul m, ← ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) 3 (4 * m)] at h2
  have hm : 3 + 4 * m = 4 * m + 3 := by omega
  rw [hm] at h2
  exact ReachesPlus.trans_star h1 h2

private theorem step_C001_even_b0_halt (l : ListBlank (Fin 2)) (m : Nat) :
    ∃ cfg', ((cfg_C001 l (2 * m) 0) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  refine ⟨(((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ [1]) {{F}}> default), ?_,
    by rfl⟩
  unfold cfg_C001
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := step_C001_even_to_E l m default
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}> default)
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ [1]) {{F}}> default) := by
    bb_steps
  exact ReachesPlus.trans h1 h2

private theorem step_C001_even_b1 (l : ListBlank (Fin 2)) (m : Nat) :
    (cfg_C001 l (2 * m) 1) [target]⊢⁺ (cfg_A l (4 * m + 2) 0 0) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := step_C001_even_to_E l m (([1] : List (Fin 2)) ^ 1 +> default)
  have hm : 4 * m + 3 = (4 * m + 2) + 1 := by omega
  rw [hm, ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (4 * m + 2) 1] at h1
  have h2 : (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) <+ ([1] : List (Fin 2)) ^ 1) {{E}}>
      (([1] : List (Fin 2)) ^ 1 +> default))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) {{D}}> ([1, 1] +> default)) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  exact ReachesPlus.trans h1 h2

private theorem step_C001_even_b2 (l : ListBlank (Fin 2)) (m : Nat) :
    (cfg_C001 l (2 * m) 2) [target]⊢⁺ (cfg_A l (4 * m + 2) 0 3) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := step_C001_even_to_E l m (([1] : List (Fin 2)) ^ 2 +> default)
  have hm : 4 * m + 3 = (4 * m + 2) + 1 := by omega
  rw [hm, ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (4 * m + 2) 1] at h1
  have h2 : (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) <+ ([1] : List (Fin 2)) ^ 1) {{E}}>
      (([1] : List (Fin 2)) ^ 2 +> default))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  exact ReachesPlus.trans h1 h2

private theorem step_C001_even_b3 (l : ListBlank (Fin 2)) (m c : Nat) :
    (cfg_C001 l (2 * m) (c + 3)) [target]⊢⁺ (cfg_A l (4 * m + 4) 0 c) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have hc : c + 3 = 3 + c := by omega
  rw [hc, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 c default]
  have h1 := step_C001_even_to_E l m (([1] : List (Fin 2)) ^ 3 +> (([1] : List (Fin 2)) ^ c +>
      default))
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}>
      (([1] : List (Fin 2)) ^ 3 +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ c +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (4 * m + 3) 1] at h2
  have hm : (4 * m + 3) + 1 = 4 * m + 4 := by omega
  rw [hm] at h2
  exact ReachesPlus.trans h1 h2

private theorem step_C001_odd_b0 (l : ListBlank (Fin 2)) (m : Nat) :
    (cfg_C001 l (2 * m + 1) 0) [target]⊢⁺ (cfg_A l (4 * m + 4) 0 1) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_add ([0, 1] : List (Fin 2)) (2 * m) 1 default]
  have h1 := step_C001_even_to_E l m (([0, 1] : List (Fin 2)) ^ 1 +> default)
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}> (([0, 1] : List (Fin 2)) ^ 1 +>
      default))
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (4 * m + 3) 1] at h2
  have hm : (4 * m + 3) + 1 = 4 * m + 4 := by omega
  rw [hm] at h2
  exact ReachesPlus.trans h1 h2

private theorem step_C001_odd_b1 (l : ListBlank (Fin 2)) (m c : Nat) :
    (cfg_C001 l (2 * m + 1) (c + 1)) [target]⊢⁺ (cfg_A l (4 * m + 3) 0 (c + 1)) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_add ([0, 1] : List (Fin 2)) (2 * m) 1 (([1] : List (Fin 2)) ^ (c + 1) +>
    default),
    ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 := step_C001_even_to_E l m (([0, 1] : List (Fin 2)) ^ 1 +> ([1] +>
      (([1] : List (Fin 2)) ^ c +> default)))
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}>
      (([0, 1] : List (Fin 2)) ^ 1 +> ([1] +> (([1] : List (Fin 2)) ^ c +> default))))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{D}}>
        ([1, 1] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  exact ReachesPlus.trans h1 h2

private theorem step_C001_all (l : ListBlank (Fin 2))
    (hl : ∀ k j c, IsInPatternSet ps (cfg_A l k j c)) (a b : Nat) :
    ∃ cfg', ((cfg_C001 l a b) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have ha : ∃ m, a = 2 * m ∨ a = 2 * m + 1 := ⟨a / 2, by omega⟩
  rcases ha with ⟨m, rfl | rfl⟩
  · rcases b with _ | _ | _ | c
    · obtain ⟨cfg', h_plus, h_halt⟩ := step_C001_even_b0_halt l m
      exact ⟨cfg', h_plus, Or.inr h_halt⟩
    · exact ⟨_, step_C001_even_b1 l m, Or.inl (hl (4 * m + 2) 0 0)⟩
    · exact ⟨_, step_C001_even_b2 l m, Or.inl (hl (4 * m + 2) 0 3)⟩
    · exact ⟨_, step_C001_even_b3 l m c, Or.inl (hl (4 * m + 4) 0 c)⟩
  · rcases b with _ | c
    · exact ⟨_, step_C001_odd_b0 l m, Or.inl (hl (4 * m + 4) 0 1)⟩
    · exact ⟨_, step_C001_odd_b1 l m c, Or.inl (hl (4 * m + 3) 0 (c + 1))⟩

private theorem step_D_succ_to_cfg_C001 (a b : Nat) :
    (cfg_D (a + 1) b) [target]⊢⁺ (cfg_C001 default a b) := by
  unfold cfg_D cfg_C001
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a (([1] : List (Fin 2)) ^ b +> default)]
  bb_steps

private theorem step_S_def_k0_jsucc_to_cfg_C001 (j c : Nat) :
    (cfg_A default 0 (j + 1) c) [target]⊢⁺ (cfg_C001 l_hat j c) := by
  unfold cfg_A cfg_C001 l_hat
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j (([1] : List (Fin 2)) ^ c +> default)]
  dsimp [ListBlank.append, list_pow_succ]
  bb_steps

private theorem step_S_hat_k0_jsucc (j c : Nat) :
    (cfg_A l_hat 0 (j + 1) c) [target]⊢⁺ (cfg_A default 6 (j + 1) c) := by
  unfold cfg_A l_hat
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j (([1] : List (Fin 2)) ^ c +> default)]
  dsimp [ListBlank.append, list_pow_succ]
  bb_steps

private theorem step_S_hat_k1_c0 (j : Nat) :
    (cfg_A l_hat 1 j 0) [target]⊢⁺ (cfg_A default 1 1 (2 * j + 5)) := by
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 : ((l_hat <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default)))
      [target]⊢⁺
      ((l_hat <+ [0]) {{C}}> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j default] at h1
  have h2 := shift_C_right (j + 1) (l_hat <+ [0]) default
  rw [append_01_pow_zero (j + 1) l_hat] at h2
  have h3 : (((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}> default)
      [target]⊢⁺
      ((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    bb_steps
  have h4 := shift_C_left_10 (j + 1) l_hat (([1] : List (Fin 2)) ^ 3 +> default)
  rw [one_pow_two_mul (j + 1),
    ← ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (j + 1)) 3 default] at h4
  have hj : 2 * (j + 1) + 3 = 2 * j + 5 := by omega
  rw [hj] at h4
  have h5 : (l_hat {{C}}> ([1] +> (([1] : List (Fin 2)) ^ (2 * j + 5) +> default)))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([0, 1] : List (Fin 2)) ^ 1 +> (([1] : List (Fin 2)) ^ (2 * j + 5) +>
      default)))) := by
    unfold l_hat
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_S_hat_k1_csucc_to_cfg_C001 (j c : Nat) :
    (cfg_A l_hat 1 j (c + 1)) [target]⊢⁺
    (cfg_C001 (default <+ ([1] : List (Fin 2)) ^ 3) (j + 1) c) := by
  unfold cfg_A cfg_C001
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 : ((l_hat <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      [target]⊢⁺
      ((l_hat <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1) (l_hat <+ [0])
      ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_01_pow_zero (j + 1) l_hat] at h2
  have h3 : (((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      ((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    bb_steps
  have h4 := shift_DC_left (j + 1) l_hat ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_10_pow_one (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : (l_hat {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      [target]⊢⁺
      ((default <+ ([1] : List (Fin 2)) ^ 3) {{C}}>
        ([0, 0, 1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))) := by
    unfold l_hat
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_SL_stride3 (l : ListBlank (Fin 2)) (k j c : Nat) :
    (cfg_A l (k + 3) j (c + 1)) [target]⊢⁺ (cfg_A l k (j + 2) c) := by
  unfold cfg_A
  have hk : k + 3 = (k + 2) + 1 := by omega
  rw [hk, ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (k + 2) 1,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 : (((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1) ((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ [0])
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_01_pow_zero (j + 1) (l <+ ([1] : List (Fin 2)) ^ (k + 2))] at h2
  have h3 : ((((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    bb_steps
  have h4 := shift_DC_left (j + 1) (l <+ ([1] : List (Fin 2)) ^ (k + 2))
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_10_pow_one (j + 1) (([1] : List (Fin 2)) ^ c +> default),
    ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) k 2] at h4
  have h5 : (((l <+ ([1] : List (Fin 2)) ^ k) <+ ([1] : List (Fin 2)) ^ 2) {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ k) {{D}}>
        ([1, 1] +> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (j + 1) (([1] : List (Fin 2)) ^ c +>
    default)] at h5
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_SL_c0_k2 (l : ListBlank (Fin 2)) (k j : Nat) :
    (cfg_A l (k + 2) j 0) [target]⊢⁺ (cfg_A l k 0 (2 * j + 5)) := by
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have hk : k + 2 = (k + 1) + 1 := by omega
  rw [hk, ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (k + 1) 1]
  have h1 : (((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default)))
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j default] at h1
  have h2 := shift_C_right (j + 1) ((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ [0]) default
  rw [append_01_pow_zero (j + 1) (l <+ ([1] : List (Fin 2)) ^ (k + 1))] at h2
  have h3 : ((((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}> default)
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    bb_steps
  have h4 := shift_C_left_10 (j + 1) (l <+ ([1] : List (Fin 2)) ^ (k + 1))
      (([1] : List (Fin 2)) ^ 3 +> default)
  rw [one_pow_two_mul (j + 1),
    ← ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (j + 1)) 3 default,
    ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) k 1] at h4
  have hj : 2 * (j + 1) + 3 = 2 * j + 5 := by omega
  rw [hj] at h4
  have h5 : (((l <+ ([1] : List (Fin 2)) ^ k) <+ ([1] : List (Fin 2)) ^ 1) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * j + 5) +> default)))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ k) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ (2 * j + 5) +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_S_k1_c0 (j : Nat) :
    (cfg_A default 1 j 0) [target]⊢⁺ (cfg_A default 0 0 (2 * j + 3)) := by
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default)))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{C}}> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +>
      default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j default] at h1
  have h2 := shift_C_right (j + 1) default default
  have h12 := ReachesPlus.trans_star h1 h2
  have hj1 : j + 1 = 1 + j := by omega
  rw [hj1, ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) 1 j] at h12
  change (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default))) [target]⊢⁺
      ((((default <+ ([1] : List (Fin 2)) ^ 1) <+ [0]) <+ ([0,
      1] : List (Fin 2)) ^ j) {{C}}> default) at h12
  rw [append_01_pow_zero j (default <+ ([1] : List (Fin 2)) ^ 1)] at h12
  have h3 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ j) <+ [0]) {{C}}> default)
      [target]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ j) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    bb_steps
  have h4 := shift_C_left_10 j ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1)
      (([1] : List (Fin 2)) ^ 3 +> default)
  rw [one_pow_two_mul j,
    ← ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * j) 3 default] at h4
  have h5 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * j + 3) +> default)))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ (2 * j + 3) +> default))) := by
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans h12 h3) h4) h5

private theorem step_S_k1_csucc (j c : Nat) :
    (cfg_A default 1 j (c + 1)) [target]⊢⁺ (cfg_D (j + 2) c) := by
  unfold cfg_A cfg_D
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1) default ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [default_append_01_pow (j + 1)] at h2
  have h3 : ((((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    bb_steps
  have h4 := shift_DC_left (j + 1) default ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_10_pow_one (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : ([0] : List (Fin 2)) +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +>
      (([1] : List (Fin 2)) ^ c +> default))) =
      ([0, 1] : List (Fin 2)) ^ (j + 2) +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (j + 1)]
    rfl
  rw [h5] at h4
  exact ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3) h4

private theorem step_S_k2_csucc (j c : Nat) :
    (cfg_A default 2 j (c + 1)) [target]⊢⁺ (cfg_D (j + 3) c) := by
  unfold cfg_A cfg_D
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      [target]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1)
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ [0])
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_01_pow_zero (j + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1)]
    at h2
  have h3 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    bb_steps
  have h4 := shift_DC_left (j + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1)
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_10_pow_one (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}>
        (([0, 1] : List (Fin 2)) ^ 2 +> (([0, 1] : List (Fin 2)) ^ (j + 1) +>
      (([1] : List (Fin 2)) ^ c +> default)))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 (j + 1) (([1] : List (Fin 2)) ^ c +>
    default)] at h5
  have hj : 2 + (j + 1) = j + 3 := by omega
  rw [hj] at h5
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_S_k0_j0 (c : Nat) :
    (cfg_A default 0 0 c) [target]⊢⁺ (cfg_D 1 (c + 2)) := by
  unfold cfg_A cfg_D
  rw [Nat.add_comm c 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 c default]
  dsimp [ListBlank.append, list_pow_succ]
  bb_steps

private theorem step_SL_hat_k2_csucc (j c : Nat) :
    (cfg_A l_hat 2 j (c + 1)) [target]⊢⁺ (cfg_A default 1 (j + 3) c) := by
  unfold cfg_A l_hat
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List
      (Fin 2)) ^ 2) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      [target]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin
      2)) ^ 1) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1)
    (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin 2))
      ^ 1) <+ [0])
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_01_pow_zero (j + 1)
    ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+
      ([1] : List (Fin 2)) ^ 1)] at h2
  have h3 : ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List
      (Fin 2)) ^ 1) <+
      ([1, 0] : List (Fin 2)) ^ (j + 1) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin
      2)) ^ 1) <+
        ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    bb_steps
  have h4 := shift_DC_left (j + 1)
    ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin 2)) ^
      1)
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_10_pow_one (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List
      (Fin 2)) ^ 1) {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([0, 1] : List (Fin 2)) ^ 2 +> (([0, 1] : List (Fin 2)) ^ (j + 1) +>
      (([1] : List (Fin 2)) ^ c +> default))))) := by
    bb_steps
  rw [← ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 (j + 1) (([1] : List (Fin 2)) ^ c +>
    default)] at h5
  have hj : 2 + (j + 1) = j + 3 := by omega
  rw [hj] at h5
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_SL_hat_k0_j0 (c : Nat) :
    (cfg_A l_hat 0 0 c) [target]⊢⁺ (cfg_A default 2 0 (c + 2)) := by
  unfold cfg_A l_hat
  rw [Nat.add_comm c 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 c default]
  dsimp [ListBlank.append, list_pow_succ]
  bb_steps

/-! ## Blank-Tape Entry and Closure -/

private theorem init_to_cfg_D : (init []) [target]⊢⁺ (cfg_D 1 1) := by
  unfold init cfg_D
  simp only [Tape.mk₁]
  bb_steps

private theorem init_reaches_S : (init []) [target]⊢* (cfg_A default 2 0 0) :=
  ReachesPlus.to_star
    (ReachesPlus.trans (ReachesPlus.trans init_to_cfg_D (step_D_succ_to_cfg_C001 0 1))
      (step_C001_even_b1 default 0))

private theorem step_S_def_all (k j c : Nat) :
    ∃ cfg', ((cfg_A default k j c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases k with _ | _ | _ | k'
  · rcases j with _ | j'
    · have h12 := ReachesPlus.trans (step_S_k0_j0 c) (step_D_succ_to_cfg_C001 0 (c + 2))
      obtain ⟨cfg', h3, h_end⟩ := step_C001_all default in_ps_S_def 0 (c + 2)
      exact ⟨cfg', ReachesPlus.trans h12 h3, h_end⟩
    · have h1 := step_S_def_k0_jsucc_to_cfg_C001 j' c
      obtain ⟨cfg', h2, h_end⟩ := step_C001_all l_hat in_ps_S_hat j' c
      exact ⟨cfg', ReachesPlus.trans h1 h2, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_S_k1_c0 j, Or.inl (in_ps_S_def 0 0 (2 * j + 3))⟩
    · have h12 := ReachesPlus.trans (step_S_k1_csucc j c') (step_D_succ_to_cfg_C001 (j + 1) c')
      obtain ⟨cfg', h3, h_end⟩ := step_C001_all default in_ps_S_def (j + 1) c'
      exact ⟨cfg', ReachesPlus.trans h12 h3, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 default 0 j, Or.inl (in_ps_S_def 0 0 (2 * j + 5))⟩
    · have h12 := ReachesPlus.trans (step_S_k2_csucc j c') (step_D_succ_to_cfg_C001 (j + 2) c')
      obtain ⟨cfg', h3, h_end⟩ := step_C001_all default in_ps_S_def (j + 2) c'
      exact ⟨cfg', ReachesPlus.trans h12 h3, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 default (k' + 1) j, Or.inl (in_ps_S_def (k' + 1) 0 (2 * j + 5))⟩
    · exact ⟨_, step_SL_stride3 default k' j c', Or.inl (in_ps_S_def k' (j + 2) c')⟩

private theorem step_S_hat_all (k j c : Nat) :
    ∃ cfg', ((cfg_A l_hat k j c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases k with _ | _ | _ | k'
  · rcases j with _ | j'
    · exact ⟨_, step_SL_hat_k0_j0 c, Or.inl (in_ps_S_def 2 0 (c + 2))⟩
    · exact ⟨_, step_S_hat_k0_jsucc j' c, Or.inl (in_ps_S_def 6 (j' + 1) c)⟩
  · rcases c with _ | c'
    · exact ⟨_, step_S_hat_k1_c0 j, Or.inl (in_ps_S_def 1 1 (2 * j + 5))⟩
    · have h1 := step_S_hat_k1_csucc_to_cfg_C001 j c'
      obtain ⟨cfg', h2,
      h_end⟩ := step_C001_all (default <+ ([1] : List (Fin 2)) ^ 3) in_ps_S_ones3 (j + 1) c'
      exact ⟨cfg', ReachesPlus.trans h1 h2, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 l_hat 0 j, Or.inl (in_ps_S_hat 0 0 (2 * j + 5))⟩
    · exact ⟨_, step_SL_hat_k2_csucc j c', Or.inl (in_ps_S_def 1 (j + 3) c')⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 l_hat (k' + 1) j, Or.inl (in_ps_S_hat (k' + 1) 0 (2 * j + 5))⟩
    · exact ⟨_, step_SL_stride3 l_hat k' j c', Or.inl (in_ps_S_hat k' (j + 2) c')⟩

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A default 2 0 0, init_reaches_S, in_ps_S_def 2 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · rw [eval_pat_A]
    change ¬ (vars 1 >= 2) at h_cond
    have hp : vars 1 = 0 ∨ vars 1 = 1 := by omega
    rcases hp with h0 | h1
    · rw [h0]
      exact step_S_def_all (vars 0) (vars 2) (vars 3)
    · rw [h1]
      exact step_S_hat_all (vars 0) (vars 2) (vars 3)
  · nomatch h_mem

/-- `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

private theorem cfg_A_ones3_eq (k j c : Nat) :
    cfg_A l_ones3 k j c = cfg_A default (3 + k) j c := by
  unfold cfg_A l_ones3
  rw [← ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 k]

inductive State where
  | S_def (k j c : ℕ)
  | S_hat (k j c : ℕ)
  | C_def (a b : ℕ)
  | C_hat (a b : ℕ)
  | C_ones3 (a b : ℕ)

def start : State := .S_def 2 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .S_def k j c => cfg_A default k j c
  | .S_hat k j c => cfg_A l_hat k j c
  | .C_def a b => cfg_C001 default a b
  | .C_hat a b => cfg_C001 l_hat a b
  | .C_ones3 a b => cfg_C001 l_ones3 a b

def next : State → Option State
  | .S_def 0 0 c => some (.C_def 0 (c + 2))
  | .S_def 0 (j + 1) c => some (.C_hat j c)
  | .S_def 1 j 0 => some (.S_def 0 0 (2 * j + 3))
  | .S_def 1 j (c + 1) => some (.C_def (j + 1) c)
  | .S_def 2 j 0 => some (.S_def 0 0 (2 * j + 5))
  | .S_def 2 j (c + 1) => some (.C_def (j + 2) c)
  | .S_def (k + 3) j 0 => some (.S_def (k + 1) 0 (2 * j + 5))
  | .S_def (k + 3) j (c + 1) => some (.S_def k (j + 2) c)
  | .S_hat 0 0 c => some (.S_def 2 0 (c + 2))
  | .S_hat 0 (j + 1) c => some (.S_def 6 (j + 1) c)
  | .S_hat 1 j 0 => some (.S_def 1 1 (2 * j + 5))
  | .S_hat 1 j (c + 1) => some (.C_ones3 (j + 1) c)
  | .S_hat 2 j 0 => some (.S_hat 0 0 (2 * j + 5))
  | .S_hat 2 j (c + 1) => some (.S_def 1 (j + 3) c)
  | .S_hat (k + 3) j 0 => some (.S_hat (k + 1) 0 (2 * j + 5))
  | .S_hat (k + 3) j (c + 1) => some (.S_hat k (j + 2) c)
  | .C_def a b =>
    if a % 2 = 0 then
      Nat.casesOn b none fun b =>
      Nat.casesOn b (some (.S_def (4 * (a / 2) + 2) 0 0)) fun b =>
      Nat.casesOn b (some (.S_def (4 * (a / 2) + 2) 0 3)) fun c =>
      some (.S_def (4 * (a / 2) + 4) 0 c)
    else
      Nat.casesOn b (some (.S_def (4 * (a / 2) + 4) 0 1)) fun c =>
      some (.S_def (4 * (a / 2) + 3) 0 (c + 1))
  | .C_hat a b =>
    if a % 2 = 0 then
      Nat.casesOn b none fun b =>
      Nat.casesOn b (some (.S_hat (4 * (a / 2) + 2) 0 0)) fun b =>
      Nat.casesOn b (some (.S_hat (4 * (a / 2) + 2) 0 3)) fun c =>
      some (.S_hat (4 * (a / 2) + 4) 0 c)
    else
      Nat.casesOn b (some (.S_hat (4 * (a / 2) + 4) 0 1)) fun c =>
      some (.S_hat (4 * (a / 2) + 3) 0 (c + 1))
  | .C_ones3 a b =>
    if a % 2 = 0 then
      Nat.casesOn b none fun b =>
      Nat.casesOn b (some (.S_def (3 + (4 * (a / 2) + 2)) 0 0)) fun b =>
      Nat.casesOn b (some (.S_def (3 + (4 * (a / 2) + 2)) 0 3)) fun c =>
      some (.S_def (3 + (4 * (a / 2) + 4)) 0 c)
    else
      Nat.casesOn b (some (.S_def (3 + (4 * (a / 2) + 4)) 0 1)) fun c =>
      some (.S_def (3 + (4 * (a / 2) + 3)) 0 (c + 1))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_S ?_
  intro s
  cases s with
  | S_def k j c =>
    rcases k with _ | _ | _ | k
    · rcases j with _ | j
      · exact ReachesPlus.trans (step_S_k0_j0 c) (step_D_succ_to_cfg_C001 0 (c + 2))
      · exact step_S_def_k0_jsucc_to_cfg_C001 j c
    · rcases c with _ | c
      · exact step_S_k1_c0 j
      · exact ReachesPlus.trans (step_S_k1_csucc j c) (step_D_succ_to_cfg_C001 (j + 1) c)
    · rcases c with _ | c
      · exact step_SL_c0_k2 default 0 j
      · exact ReachesPlus.trans (step_S_k2_csucc j c) (step_D_succ_to_cfg_C001 (j + 2) c)
    · rcases c with _ | c
      · exact step_SL_c0_k2 default (k + 1) j
      · exact step_SL_stride3 default k j c
  | S_hat k j c =>
    rcases k with _ | _ | _ | k
    · rcases j with _ | j
      · exact step_SL_hat_k0_j0 c
      · exact step_S_hat_k0_jsucc j c
    · rcases c with _ | c
      · exact step_S_hat_k1_c0 j
      · exact step_S_hat_k1_csucc_to_cfg_C001 j c
    · rcases c with _ | c
      · exact step_SL_c0_k2 l_hat 0 j
      · exact step_SL_hat_k2_csucc j c
    · rcases c with _ | c
      · exact step_SL_c0_k2 l_hat (k + 1) j
      · exact step_SL_stride3 l_hat k j c
  | C_def a b =>
    by_cases h : a % 2 = 0
    · have ha : a = 2 * (a / 2) := by omega
      rcases b with _ | _ | _ | c
      · simp only [next, h, ↓reduceIte, encode]
        rw [ha]
        obtain ⟨cfg', h_plus, h_halt⟩ := step_C001_even_b0_halt default (a / 2)
        exact ⟨cfg', ReachesPlus.to_star h_plus, h_halt⟩
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b1 default (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b2 default (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b3 default (a / 2) c
        rwa [← ha] at hstep
    · have ha : a = 2 * (a / 2) + 1 := by omega
      rcases b with _ | c
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_odd_b0 default (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_odd_b1 default (a / 2) c
        rwa [← ha] at hstep
  | C_hat a b =>
    by_cases h : a % 2 = 0
    · have ha : a = 2 * (a / 2) := by omega
      rcases b with _ | _ | _ | c
      · simp only [next, h, ↓reduceIte, encode]
        rw [ha]
        obtain ⟨cfg', h_plus, h_halt⟩ := step_C001_even_b0_halt l_hat (a / 2)
        exact ⟨cfg', ReachesPlus.to_star h_plus, h_halt⟩
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b1 l_hat (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b2 l_hat (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b3 l_hat (a / 2) c
        rwa [← ha] at hstep
    · have ha : a = 2 * (a / 2) + 1 := by omega
      rcases b with _ | c
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_odd_b0 l_hat (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_odd_b1 l_hat (a / 2) c
        rwa [← ha] at hstep
  | C_ones3 a b =>
    by_cases h : a % 2 = 0
    · have ha : a = 2 * (a / 2) := by omega
      rcases b with _ | _ | _ | c
      · simp only [next, h, ↓reduceIte, encode]
        rw [ha]
        obtain ⟨cfg', h_plus, h_halt⟩ := step_C001_even_b0_halt l_ones3 (a / 2)
        exact ⟨cfg', ReachesPlus.to_star h_plus, h_halt⟩
      · simp only [next, h, ↓reduceIte, encode, ← cfg_A_ones3_eq]
        have hstep := step_C001_even_b1 l_ones3 (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode, ← cfg_A_ones3_eq]
        have hstep := step_C001_even_b2 l_ones3 (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode, ← cfg_A_ones3_eq]
        have hstep := step_C001_even_b3 l_ones3 (a / 2) c
        rwa [← ha] at hstep
    · have ha : a = 2 * (a / 2) + 1 := by omega
      rcases b with _ | c
      · simp only [next, h, ↓reduceIte, encode, ← cfg_A_ones3_eq]
        have hstep := step_C001_odd_b0 l_ones3 (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode, ← cfg_A_ones3_eq]
        have hstep := step_C001_odd_b1 l_ones3 (a / 2) c
        rwa [← ha] at hstep

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-Like Acceleration -/

private inductive MidState where
  | S_def (k j c : ℕ)
  | S_hat (k j c : ℕ)

private def midStart : MidState := .S_def 2 0 0

private def midToState : MidState → State
  | .S_def k j c => .S_def k j c
  | .S_hat k j c => .S_hat k j c

private def midEncode (s : MidState) : Cfg (Fin 2) (Fin 6) :=
  encode (midToState s)

private def midEvalC (mk : ℕ → ℕ → ℕ → MidState) (a b : ℕ) : Option MidState :=
  if a % 2 = 0 then
    Nat.casesOn b none fun b =>
    Nat.casesOn b (some (mk (4 * (a / 2) + 2) 0 0)) fun b =>
    Nat.casesOn b (some (mk (4 * (a / 2) + 2) 0 3)) fun c =>
    some (mk (4 * (a / 2) + 4) 0 c)
  else
    Nat.casesOn b (some (mk (4 * (a / 2) + 4) 0 1)) fun c =>
    some (mk (4 * (a / 2) + 3) 0 (c + 1))

private def midNext : MidState → Option MidState
  | .S_def 0 0 c => midEvalC .S_def 0 (c + 2)
  | .S_def 0 (j + 1) c => midEvalC .S_hat j c
  | .S_def 1 j 0 => some (.S_def 0 0 (2 * j + 3))
  | .S_def 1 j (c + 1) => midEvalC .S_def (j + 1) c
  | .S_def 2 j 0 => some (.S_def 0 0 (2 * j + 5))
  | .S_def 2 j (c + 1) => midEvalC .S_def (j + 2) c
  | .S_def (k + 3) j 0 => some (.S_def (k + 1) 0 (2 * j + 5))
  | .S_def (k + 3) j (c + 1) =>
    let m := min ((k + 3) / 3) (c + 1)
    some (.S_def (k + 3 - 3 * m) (j + 2 * m) (c + 1 - m))
  | .S_hat 0 0 c => some (.S_def 2 0 (c + 2))
  | .S_hat 0 (j + 1) c => some (.S_def 6 (j + 1) c)
  | .S_hat 1 j 0 => some (.S_def 1 1 (2 * j + 5))
  | .S_hat 1 j (c + 1) => midEvalC (fun k j' c' => .S_def (3 + k) j' c') (j + 1) c
  | .S_hat 2 j 0 => some (.S_hat 0 0 (2 * j + 5))
  | .S_hat 2 j (c + 1) => some (.S_def 1 (j + 3) c)
  | .S_hat (k + 3) j 0 => some (.S_hat (k + 1) 0 (2 * j + 5))
  | .S_hat (k + 3) j (c + 1) =>
    let m := min ((k + 3) / 3) (c + 1)
    some (.S_hat (k + 3 - 3 * m) (j + 2 * m) (c + 1 - m))

private theorem reaches_S_def_diag (m : ℕ) (k j c : ℕ) :
    CollatzReachesStar next
      (.S_def (k + 3 * m) j (c + m))
      (.S_def k (j + 2 * m) c) := by
  induction m generalizing j with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ m ih =>
    have h_next : next (.S_def (k + 3 * (m + 1)) j (c + (m + 1))) =
        some (.S_def (k + 3 * m) (j + 2) (c + m)) := by
      have h1 : k + 3 * (m + 1) = (k + 3 * m) + 3 := by omega
      have h2 : c + (m + 1) = (c + m) + 1 := by omega
      rw [h1, h2]
      simp [next]
    have ih' := ih (j + 2)
    have hj : j + 2 + 2 * m = j + 2 * (m + 1) := by omega
    rw [hj] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem reaches_S_def_drain (k j c : ℕ) :
    CollatzStepsTo next (.S_def (k + 3) j (c + 1))
      (some (.S_def (k + 3 - 3 * min ((k + 3) / 3) (c + 1))
        (j + 2 * min ((k + 3) / 3) (c + 1))
        (c + 1 - min ((k + 3) / 3) (c + 1)))) := by
  let m := min ((k + 3) / 3) (c + 1)
  have hm_pos : 0 < m := by
    dsimp [m]
    have : 0 < (k + 3) / 3 := by omega
    have : 0 < c + 1 := Nat.succ_pos c
    exact Nat.lt_min.mpr ⟨‹_›, ‹_›⟩
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm_pos)
  have h_head : next (.S_def (k + 3) j (c + 1)) =
      some (.S_def k (j + 2) c) := by simp [next]
  have h_star := reaches_S_def_diag m' (k + 3 - 3 * m) (j + 2) (c + 1 - m)
  have hk : k + 3 - 3 * m + 3 * m' = k := by omega
  have hj : j + 2 + 2 * m' = j + 2 * m := by omega
  have hc : c + 1 - m + m' = c := by omega
  rw [hk, hj, hc] at h_star
  exact CollatzReachesPlus.head h_head h_star

private theorem reaches_S_hat_diag (m : ℕ) (k j c : ℕ) :
    CollatzReachesStar next
      (.S_hat (k + 3 * m) j (c + m))
      (.S_hat k (j + 2 * m) c) := by
  induction m generalizing j with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ m ih =>
    have h_next : next (.S_hat (k + 3 * (m + 1)) j (c + (m + 1))) =
        some (.S_hat (k + 3 * m) (j + 2) (c + m)) := by
      have h1 : k + 3 * (m + 1) = (k + 3 * m) + 3 := by omega
      have h2 : c + (m + 1) = (c + m) + 1 := by omega
      rw [h1, h2]
      simp [next]
    have ih' := ih (j + 2)
    have hj : j + 2 + 2 * m = j + 2 * (m + 1) := by omega
    rw [hj] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem reaches_S_hat_drain (k j c : ℕ) :
    CollatzStepsTo next (.S_hat (k + 3) j (c + 1))
      (some (.S_hat (k + 3 - 3 * min ((k + 3) / 3) (c + 1))
        (j + 2 * min ((k + 3) / 3) (c + 1))
        (c + 1 - min ((k + 3) / 3) (c + 1)))) := by
  let m := min ((k + 3) / 3) (c + 1)
  have hm_pos : 0 < m := by
    dsimp [m]
    have : 0 < (k + 3) / 3 := by omega
    have : 0 < c + 1 := Nat.succ_pos c
    exact Nat.lt_min.mpr ⟨‹_›, ‹_›⟩
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm_pos)
  have h_head : next (.S_hat (k + 3) j (c + 1)) =
      some (.S_hat k (j + 2) c) := by simp [next]
  have h_star := reaches_S_hat_diag m' (k + 3 - 3 * m) (j + 2) (c + 1 - m)
  have hk : k + 3 - 3 * m + 3 * m' = k := by omega
  have hj : j + 2 + 2 * m' = j + 2 * m := by omega
  have hc : c + 1 - m + m' = c := by omega
  rw [hk, hj, hc] at h_star
  exact CollatzReachesPlus.head h_head h_star

private theorem stepsTo_C_def (a b : ℕ) :
    CollatzStepsTo next (.C_def a b) ((midEvalC .S_def a b).map midToState) := by
  dsimp [midEvalC]
  split_ifs with ha
  · rcases b with _ | _ | _ | c <;> exact CollatzStepsTo.of_eq (by simp [next, midToState, ha])
  · rcases b with _ | c <;> exact CollatzStepsTo.of_eq (by simp [next, midToState, ha])

private theorem stepsTo_C_hat (a b : ℕ) :
    CollatzStepsTo next (.C_hat a b) ((midEvalC .S_hat a b).map midToState) := by
  dsimp [midEvalC]
  split_ifs with ha
  · rcases b with _ | _ | _ | c <;> exact CollatzStepsTo.of_eq (by simp [next, midToState, ha])
  · rcases b with _ | c <;> exact CollatzStepsTo.of_eq (by simp [next, midToState, ha])

private theorem stepsTo_C_ones3 (a b : ℕ) :
    CollatzStepsTo next (.C_ones3 a b)
      ((midEvalC (fun k j' c' => .S_def (3 + k) j' c') a b).map midToState) := by
  dsimp [midEvalC]
  split_ifs with ha
  · rcases b with _ | _ | _ | c <;> exact CollatzStepsTo.of_eq (by simp [next, midToState, ha])
  · rcases b with _ | c <;> exact CollatzStepsTo.of_eq (by simp [next, midToState, ha])

private theorem is_valid_mid_acceleration :
    IsValidAcceleration target midStart midEncode midNext := by
  refine is_valid_acceleration.of_collatz (embed := midToState)
    (CollatzReachesStar.refl next start) ?_
  rintro (⟨k, j, c⟩ | ⟨k, j, c⟩)
  · rcases k with _ | _ | _ | k
    · rcases j with _ | j
      · exact CollatzStepsTo.head rfl (stepsTo_C_def 0 (c + 2))
      · exact CollatzStepsTo.head rfl (stepsTo_C_hat j c)
    · rcases c with _ | c
      · exact CollatzStepsTo.of_eq rfl
      · exact CollatzStepsTo.head rfl (stepsTo_C_def (j + 1) c)
    · rcases c with _ | c
      · exact CollatzStepsTo.of_eq rfl
      · exact CollatzStepsTo.head rfl (stepsTo_C_def (j + 2) c)
    · rcases c with _ | c
      · exact CollatzStepsTo.of_eq rfl
      · have h_eq : Option.map midToState
              (midNext (MidState.S_def (k + 3) j (c + 1))) =
            some (.S_def (k + 3 - 3 * min ((k + 3) / 3) (c + 1))
              (j + 2 * min ((k + 3) / 3) (c + 1))
              (c + 1 - min ((k + 3) / 3) (c + 1))) := rfl
        rw [h_eq]
        exact reaches_S_def_drain k j c
  · rcases k with _ | _ | _ | k
    · rcases j with _ | j <;> exact CollatzStepsTo.of_eq rfl
    · rcases c with _ | c
      · exact CollatzStepsTo.of_eq rfl
      · exact CollatzStepsTo.head rfl (stepsTo_C_ones3 (j + 1) c)
    · rcases c with _ | c <;> exact CollatzStepsTo.of_eq rfl
    · rcases c with _ | c
      · exact CollatzStepsTo.of_eq rfl
      · have h_eq : Option.map midToState
              (midNext (MidState.S_hat (k + 3) j (c + 1))) =
            some (.S_hat (k + 3 - 3 * min ((k + 3) / 3) (c + 1))
              (j + 2 * min ((k + 3) / 3) (c + 1))
              (c + 1 - min ((k + 3) / 3) (c + 1))) := rfl
        rw [h_eq]
        exact reaches_S_hat_drain k j c

/-- High-level symbolic configuration state space for `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD`,
parameterizing $S(p, k, c) := 0^\infty\,(1110)^p\,1^k\,\mathrm{D}{>}\,11\,1^c\,0^\infty$
for $p \in \{0, 1\}$. -/
inductive HighLevelState where
  /-- $S(p, k, c) := 0^\infty\,(1110)^p\,1^k\,\mathrm{D}{>}\,11\,1^c\,0^\infty$. -/
  | S (p : Bool) (k c : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $S(0, 2, 0)$. -/
def highLevelStart : HighLevelState := .S false 2 0

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .S false k c => .S_def k 0 c
  | .S true k c => .S_hat k 0 c

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

private def toMid : HighLevelState → MidState
  | .S false k c => .S_def k 0 c
  | .S true k c => .S_hat k 0 c

/-- High-level accelerated transition function on $S(p, k, c)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .S p k c =>
    let q := k / 3
    let r := k % 3
    if c < q then some (.S p (k - 3 * c - 2) (4 * c + 5))
    else
      let d := c - q
      if p then
        if r = 0 then
          if q = 0 then some (.S false 2 (c + 2))
          else if d = 0 then some (.S false 4 (4 * q + 5))
          else if d = 1 then some (.S false 1 (4 * q + 9))
          else if d = 2 then some (.S true (4 * q + 8) 1)
          else some (.S true (4 * q + 7) (d - 2))
        else if r = 1 then
          if d = 0 then some (.S false 8 (4 * q + 1))
          else if d = 1 then some (.S false (4 * q + 7) 1)
          else some (.S false (4 * q + 6) (d - 1))
        else
          if d = 0 then some (.S true 0 (4 * q + 5))
          else if d = 1 then some (.S false 0 (4 * q + 9))
          else if d = 2 then none
          else if d = 3 then some (.S false (4 * q + 10) 0)
          else if d = 4 then some (.S false (4 * q + 10) 3)
          else some (.S false (4 * q + 12) (d - 5))
      else
        if r = 0 then
          if q = 0 then
            if c = 0 then some (.S false 2 3) else some (.S false 4 (c - 1))
          else if d = 0 then some (.S true (4 * q) 1)
          else some (.S true (4 * q - 1) d)
        else if r = 1 then
          if d = 0 then some (.S false 0 (4 * q + 3))
          else if d = 1 then some (.S false (4 * q + 4) 1)
          else some (.S false (4 * q + 3) (d - 1))
        else
          if d = 0 then some (.S false 0 (4 * q + 5))
          else if d = 1 then none
          else if d = 2 then some (.S false (4 * q + 6) 0)
          else if d = 3 then some (.S false (4 * q + 6) 3)
          else some (.S false (4 * q + 8) (d - 4))

private theorem mid_drain_def {k j c k' j' c' : ℕ}
    (hk : k' = k + 3 - 3 * min ((k + 3) / 3) (c + 1))
    (hj : j' = j + 2 * min ((k + 3) / 3) (c + 1))
    (hc : c' = c + 1 - min ((k + 3) / 3) (c + 1)) :
    midNext (.S_def (k + 3) j (c + 1)) = some (.S_def k' j' c') := by
  subst hk hj hc
  rfl

private theorem mid_drain_hat {k j c k' j' c' : ℕ}
    (hk : k' = k + 3 - 3 * min ((k + 3) / 3) (c + 1))
    (hj : j' = j + 2 * min ((k + 3) / 3) (c + 1))
    (hc : c' = c + 1 - min ((k + 3) / 3) (c + 1)) :
    midNext (.S_hat (k + 3) j (c + 1)) = some (.S_hat k' j' c') := by
  subst hk hj hc
  rfl

private theorem midEvalC_even_0 (mk : ℕ → ℕ → ℕ → MidState) (m : ℕ) :
    midEvalC mk (2 * m) 0 = none := by
  have h1 : (2 * m) % 2 = 0 := by omega
  simp only [midEvalC, h1, ↓reduceIte]
  rfl

private theorem midEvalC_even_1 (mk : ℕ → ℕ → ℕ → MidState) (m k : ℕ) (hk : k = 4 * m + 2) :
    midEvalC mk (2 * m) 1 = some (mk k 0 0) := by
  subst hk
  have h1 : (2 * m) % 2 = 0 := by omega
  have h2 : (2 * m) / 2 = m := by omega
  simp only [midEvalC, h1, ↓reduceIte, h2]
  rfl

private theorem midEvalC_even_2 (mk : ℕ → ℕ → ℕ → MidState) (m k : ℕ) (hk : k = 4 * m + 2) :
    midEvalC mk (2 * m) 2 = some (mk k 0 3) := by
  subst hk
  have h1 : (2 * m) % 2 = 0 := by omega
  have h2 : (2 * m) / 2 = m := by omega
  simp only [midEvalC, h1, ↓reduceIte, h2]
  rfl

private theorem midEvalC_even_3 (mk : ℕ → ℕ → ℕ → MidState) (m c k : ℕ) (hk : k = 4 * m + 4) :
    midEvalC mk (2 * m) (c + 3) = some (mk k 0 c) := by
  subst hk
  have h1 : (2 * m) % 2 = 0 := by omega
  have h2 : (2 * m) / 2 = m := by omega
  simp only [midEvalC, h1, ↓reduceIte, h2]

private theorem midEvalC_odd_0 (mk : ℕ → ℕ → ℕ → MidState) (m k : ℕ) (hk : k = 4 * m + 4) :
    midEvalC mk (2 * m + 1) 0 = some (mk k 0 1) := by
  subst hk
  have h1 : ¬ (2 * m + 1) % 2 = 0 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  simp only [midEvalC, h1, ↓reduceIte, h2]
  rfl

private theorem midEvalC_odd_1 (mk : ℕ → ℕ → ℕ → MidState) (m c k : ℕ) (hk : k = 4 * m + 3) :
    midEvalC mk (2 * m + 1) (c + 1) = some (mk k 0 (c + 1)) := by
  subst hk
  have h1 : ¬ (2 * m + 1) % 2 = 0 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  simp only [midEvalC, h1, ↓reduceIte, h2]

private theorem reaches_drain_def (q r d : ℕ) (hr : r < 3) :
    CollatzReachesStar midNext (.S_def (3 * q + r) 0 (q + d)) (.S_def r (2 * q) d) := by
  rcases q with _ | q
  · simp only [Nat.mul_zero, Nat.zero_add]
    exact CollatzReachesStar.refl midNext _
  · have h_eq1 : 3 * (q + 1) + r = (3 * q + r) + 3 := by omega
    have h_eq2 : q + 1 + d = (q + d) + 1 := by omega
    rw [h_eq1, h_eq2]
    exact CollatzReachesStar.head
      (mid_drain_def (by omega) (by omega) (by omega))
      (CollatzReachesStar.refl midNext _)

private theorem reaches_drain_hat (q r d : ℕ) (hr : r < 3) :
    CollatzReachesStar midNext (.S_hat (3 * q + r) 0 (q + d)) (.S_hat r (2 * q) d) := by
  rcases q with _ | q
  · simp only [Nat.mul_zero, Nat.zero_add]
    exact CollatzReachesStar.refl midNext _
  · have h_eq1 : 3 * (q + 1) + r = (3 * q + r) + 3 := by omega
    have h_eq2 : q + 1 + d = (q + d) + 1 := by omega
    rw [h_eq1, h_eq2]
    exact CollatzReachesStar.head
      (mid_drain_hat (by omega) (by omega) (by omega))
      (CollatzReachesStar.refl midNext _)

private theorem stepsTo_lt_def (k c k' c' : ℕ) (hc : c < k / 3)
    (hk' : k' = k - 3 * c - 2) (hc' : c' = 4 * c + 5) :
    CollatzStepsTo midNext (.S_def k 0 c) (some (.S_def k' 0 c')) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ k = 3 * q + r := ⟨k / 3, k % 3, by omega, by omega⟩
  rcases c with _ | c
  · obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have h1 : 3 * (q + 1) + r = (3 * q + r) + 3 := by omega
    obtain rfl : k' = 3 * q + r + 1 := by omega
    obtain rfl : c' = 5 := by omega
    rw [h1]
    exact CollatzStepsTo.of_eq rfl
  · obtain ⟨t, rfl⟩ : ∃ t, q = c + 2 + t := ⟨q - c - 2, by omega⟩
    have h1 : 3 * (c + 2 + t) + r = (3 * (c + 1 + t) + r) + 3 := by omega
    obtain rfl : k' = 3 * t + r + 1 := by omega
    obtain rfl : c' = 2 * (2 * (c + 1)) + 5 := by omega
    rw [h1]
    exact CollatzStepsTo.head
      (mid_drain_def (k' := (3 * t + r) + 3) (j' := 2 * (c + 1)) (c' := 0)
        (by omega) (by omega) (by omega))
      (CollatzStepsTo.of_eq rfl)

private theorem stepsTo_lt_hat (k c k' c' : ℕ) (hc : c < k / 3)
    (hk' : k' = k - 3 * c - 2) (hc' : c' = 4 * c + 5) :
    CollatzStepsTo midNext (.S_hat k 0 c) (some (.S_hat k' 0 c')) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ k = 3 * q + r := ⟨k / 3, k % 3, by omega, by omega⟩
  rcases c with _ | c
  · obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have h1 : 3 * (q + 1) + r = (3 * q + r) + 3 := by omega
    obtain rfl : k' = 3 * q + r + 1 := by omega
    obtain rfl : c' = 5 := by omega
    rw [h1]
    exact CollatzStepsTo.of_eq rfl
  · obtain ⟨t, rfl⟩ : ∃ t, q = c + 2 + t := ⟨q - c - 2, by omega⟩
    have h1 : 3 * (c + 2 + t) + r = (3 * (c + 1 + t) + r) + 3 := by omega
    obtain rfl : k' = 3 * t + r + 1 := by omega
    obtain rfl : c' = 2 * (2 * (c + 1)) + 5 := by omega
    rw [h1]
    exact CollatzStepsTo.head
      (mid_drain_hat (k' := (3 * t + r) + 3) (j' := 2 * (c + 1)) (c' := 0)
        (by omega) (by omega) (by omega))
      (CollatzStepsTo.of_eq rfl)

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  have he : (fun s => midEncode (toMid s)) = highLevelEncode := by
    funext ⟨p, k, c⟩
    cases p <;> rfl
  rw [← he]
  refine is_valid_mid_acceleration.of_collatz (embed := toMid)
    (CollatzReachesStar.refl midNext _) ?_
  rintro ⟨p, k, c⟩
  cases p
  · simp only [highLevelNext, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · exact stepsTo_lt_def k c _ _ (by omega) rfl rfl
    · obtain rfl : k = 0 := by omega
      obtain rfl : c = 0 := by omega
      exact CollatzStepsTo.of_eq (midEvalC_even_2 .S_def 0 2 rfl)
    · obtain rfl : k = 0 := by omega
      obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      exact CollatzStepsTo.of_eq (midEvalC_even_3 .S_def 0 d 4 (by omega))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * (q + 1) + 0 := ⟨k / 3 - 1, by omega⟩
      obtain rfl : c = (q + 1) + 0 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_def (q + 1) 0 0 (by omega)) ?_
      have hj : 2 * (q + 1) = (2 * q + 1) + 1 := by omega
      rw [hj]
      exact CollatzStepsTo.of_eq (midEvalC_odd_0 .S_hat q _ (by omega))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * (q + 1) + 0 := ⟨k / 3 - 1, by omega⟩
      obtain ⟨d, rfl⟩ : ∃ d, c = (q + 1) + (d + 1) := ⟨c - (q + 1) - 1, by omega⟩
      refine CollatzStepsTo.of_reachesStar (reaches_drain_def (q + 1) 0 (d + 1) (by omega)) ?_
      have hj : 2 * (q + 1) = (2 * q + 1) + 1 := by omega
      rw [hj]
      exact CollatzStepsTo.of_eq ((midEvalC_odd_1 .S_hat q d _ rfl).trans (by
        simp only [Option.map_some, toMid, Option.some.injEq, MidState.S_hat.injEq]
        exact ⟨by omega, trivial, by omega⟩))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 1 := ⟨k / 3, by omega⟩
      have hc : c = q + 0 := by omega
      rw [hc]
      refine CollatzStepsTo.of_reachesStar (reaches_drain_def q 1 0 (by omega)) ?_
      exact CollatzStepsTo.of_eq (by
        simp only [midNext, Option.map_some, toMid, Option.some.injEq, MidState.S_def.injEq,
          true_and]
        omega)
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 1 := ⟨k / 3, by omega⟩
      obtain rfl : c = q + 1 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_def q 1 1 (by omega)) ?_
      exact CollatzStepsTo.of_eq (midEvalC_odd_0 .S_def q _ (by omega))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 1 := ⟨k / 3, by omega⟩
      obtain ⟨d, rfl⟩ : ∃ d, c = q + (d + 2) := ⟨c - q - 2, by omega⟩
      refine CollatzStepsTo.of_reachesStar (reaches_drain_def q 1 (d + 2) (by omega)) ?_
      exact CollatzStepsTo.of_eq ((midEvalC_odd_1 .S_def q d _ rfl).trans (by
        simp only [Option.map_some, toMid, Option.some.injEq, MidState.S_def.injEq]
        exact ⟨by omega, trivial, by omega⟩))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      have hc : c = q + 0 := by omega
      rw [hc]
      refine CollatzStepsTo.of_reachesStar (reaches_drain_def q 2 0 (by omega)) ?_
      exact CollatzStepsTo.of_eq (by
        simp only [midNext, Option.map_some, toMid, Option.some.injEq, MidState.S_def.injEq,
          true_and]
        omega)
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      obtain rfl : c = q + 1 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_def q 2 1 (by omega)) ?_
      have hj : 2 * q + 2 = 2 * (q + 1) := by omega
      exact CollatzStepsTo.of_eq (by dsimp [midNext]; rw [hj]; exact midEvalC_even_0 .S_def (q + 1))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      obtain rfl : c = q + 2 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_def q 2 2 (by omega)) ?_
      have hj : 2 * q + 2 = 2 * (q + 1) := by omega
      exact CollatzStepsTo.of_eq
        (by dsimp [midNext]; rw [hj]; exact midEvalC_even_1 .S_def (q + 1) _ (by omega))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      obtain rfl : c = q + 3 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_def q 2 3 (by omega)) ?_
      have hj : 2 * q + 2 = 2 * (q + 1) := by omega
      exact CollatzStepsTo.of_eq
        (by dsimp [midNext]; rw [hj]; exact midEvalC_even_2 .S_def (q + 1) _ (by omega))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      obtain ⟨d, rfl⟩ : ∃ d, c = q + (d + 4) := ⟨c - q - 4, by omega⟩
      refine CollatzStepsTo.of_reachesStar (reaches_drain_def q 2 (d + 4) (by omega)) ?_
      have hj : 2 * q + 2 = 2 * (q + 1) := by omega
      exact CollatzStepsTo.of_eq (by
        dsimp [midNext]; rw [hj, midEvalC_even_3 .S_def (q + 1) d _ rfl]
        simp only [toMid, Option.some.injEq, MidState.S_def.injEq]
        exact ⟨by omega, trivial, by omega⟩)
  · simp only [highLevelNext, ↓reduceIte]
    split_ifs
    · exact stepsTo_lt_hat k c _ _ (by omega) rfl rfl
    · obtain rfl : k = 0 := by omega
      exact CollatzStepsTo.of_eq rfl
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * (q + 1) + 0 := ⟨k / 3 - 1, by omega⟩
      obtain rfl : c = (q + 1) + 0 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat (q + 1) 0 0 (by omega)) ?_
      have hj : 2 * (q + 1) = (2 * q + 1) + 1 := by omega
      have h1 : midNext (.S_hat 0 (2 * (q + 1)) 0) = some (.S_def 6 (2 * (q + 1)) 0) := by
        rw [hj]; rfl
      exact CollatzStepsTo.head h1 (CollatzStepsTo.of_eq (by
        simp only [midNext, Option.map_some, toMid, Option.some.injEq, MidState.S_def.injEq,
          true_and]
        omega))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * (q + 1) + 0 := ⟨k / 3 - 1, by omega⟩
      obtain rfl : c = (q + 1) + 1 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat (q + 1) 0 1 (by omega)) ?_
      have hj : 2 * (q + 1) = (2 * q + 1) + 1 := by omega
      have h1 : midNext (.S_hat 0 (2 * (q + 1)) 1) = some (.S_def 6 (2 * (q + 1)) 1) := by
        rw [hj]; rfl
      exact CollatzStepsTo.head h1 (CollatzStepsTo.head
        (mid_drain_def (k' := 3) (j' := 2 * (q + 1) + 2) (c' := 0)
          (by omega) (by omega) (by omega))
        (CollatzStepsTo.of_eq (by
          simp only [midNext, Option.map_some, toMid, Option.some.injEq, MidState.S_def.injEq,
            true_and]
          omega)))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * (q + 1) + 0 := ⟨k / 3 - 1, by omega⟩
      obtain rfl : c = (q + 1) + 2 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat (q + 1) 0 2 (by omega)) ?_
      have hj : 2 * (q + 1) = (2 * q + 1) + 1 := by omega
      have h1 : midNext (.S_hat 0 (2 * (q + 1)) 2) = some (.S_def 6 (2 * (q + 1)) 2) := by
        rw [hj]; rfl
      exact CollatzStepsTo.head h1 (CollatzStepsTo.head
        (mid_drain_def (k' := 0) (j' := (2 * (q + 2) + 1) + 1) (c' := 0)
          (by omega) (by omega) (by omega))
        (CollatzStepsTo.of_eq (by
          dsimp [midNext]; exact midEvalC_odd_0 .S_hat (q + 2) _ (by omega))))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * (q + 1) + 0 := ⟨k / 3 - 1, by omega⟩
      obtain ⟨d, rfl⟩ : ∃ d, c = (q + 1) + (d + 3) := ⟨c - (q + 1) - 3, by omega⟩
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat (q + 1) 0 (d + 3) (by omega)) ?_
      have hj : 2 * (q + 1) = (2 * q + 1) + 1 := by omega
      have h1 : midNext (.S_hat 0 (2 * (q + 1)) (d + 3)) =
          some (.S_def 6 (2 * (q + 1)) (d + 3)) := by rw [hj]; rfl
      exact CollatzStepsTo.head h1 (CollatzStepsTo.head
        (mid_drain_def (k' := 0) (j' := (2 * (q + 2) + 1) + 1) (c' := d + 1)
          (by omega) (by omega) (by omega))
        (CollatzStepsTo.of_eq (by
          dsimp [midNext]; rw [midEvalC_odd_1 .S_hat (q + 2) d _ rfl]
          simp only [toMid, Option.some.injEq, MidState.S_hat.injEq]
          exact ⟨by omega, trivial, by omega⟩)))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 1 := ⟨k / 3, by omega⟩
      have hc : c = q + 0 := by omega
      rw [hc]
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat q 1 0 (by omega)) ?_
      have h1 : midNext (.S_hat 1 (2 * q) 0) = some (.S_def 1 1 ((4 * q + 1) + 3 + 1)) := by
        simp only [midNext, Option.some.injEq, MidState.S_def.injEq, true_and]
        omega
      exact CollatzStepsTo.head h1 (CollatzStepsTo.of_eq (by
        dsimp [midNext]; rw [midEvalC_even_3 .S_def 1 (4 * q + 1) 8 rfl]
        simp only [toMid, Option.some.injEq, MidState.S_def.injEq, true_and]
        omega))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 1 := ⟨k / 3, by omega⟩
      obtain rfl : c = q + 1 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat q 1 1 (by omega)) ?_
      exact CollatzStepsTo.of_eq (by
        dsimp [midNext]; rw [midEvalC_odd_0 (fun k j' c' => .S_def (3 + k) j' c') q _ rfl]
        simp only [toMid, Option.some.injEq, MidState.S_def.injEq, and_true]
        omega)
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 1 := ⟨k / 3, by omega⟩
      obtain ⟨d, rfl⟩ : ∃ d, c = q + (d + 2) := ⟨c - q - 2, by omega⟩
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat q 1 (d + 2) (by omega)) ?_
      exact CollatzStepsTo.of_eq (by
        dsimp [midNext]; rw [midEvalC_odd_1 (fun k j' c' => .S_def (3 + k) j' c') q d _ rfl]
        simp only [toMid, Option.some.injEq, MidState.S_def.injEq]
        exact ⟨by omega, trivial, by omega⟩)
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      have hc : c = q + 0 := by omega
      rw [hc]
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat q 2 0 (by omega)) ?_
      exact CollatzStepsTo.of_eq (by
        simp only [midNext, Option.map_some, toMid, Option.some.injEq, MidState.S_hat.injEq,
          true_and]
        omega)
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      obtain rfl : c = q + 1 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat q 2 1 (by omega)) ?_
      exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq (by
        simp only [midNext, Option.map_some, toMid, Option.some.injEq, MidState.S_def.injEq,
          true_and]
        omega))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      obtain rfl : c = q + 2 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat q 2 2 (by omega)) ?_
      have h1 : midNext (.S_hat 2 (2 * q) 2) = some (.S_def 1 (2 * q + 3) 1) := rfl
      have hj : (2 * q + 3) + 1 = 2 * (q + 2) := by omega
      exact CollatzStepsTo.head h1 (CollatzStepsTo.of_eq
        (by dsimp [midNext]; rw [hj]; exact midEvalC_even_0 .S_def (q + 2)))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      obtain rfl : c = q + 3 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat q 2 3 (by omega)) ?_
      have h1 : midNext (.S_hat 2 (2 * q) 3) = some (.S_def 1 (2 * q + 3) 2) := rfl
      have hj : (2 * q + 3) + 1 = 2 * (q + 2) := by omega
      exact CollatzStepsTo.head h1 (CollatzStepsTo.of_eq
        (by dsimp [midNext]; rw [hj]; exact midEvalC_even_1 .S_def (q + 2) _ (by omega)))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      obtain rfl : c = q + 4 := by omega
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat q 2 4 (by omega)) ?_
      have h1 : midNext (.S_hat 2 (2 * q) 4) = some (.S_def 1 (2 * q + 3) 3) := rfl
      have hj : (2 * q + 3) + 1 = 2 * (q + 2) := by omega
      exact CollatzStepsTo.head h1 (CollatzStepsTo.of_eq
        (by dsimp [midNext]; rw [hj]; exact midEvalC_even_2 .S_def (q + 2) _ (by omega)))
    · obtain ⟨q, rfl⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      obtain ⟨d, rfl⟩ : ∃ d, c = q + (d + 5) := ⟨c - q - 5, by omega⟩
      refine CollatzStepsTo.of_reachesStar (reaches_drain_hat q 2 (d + 5) (by omega)) ?_
      have h1 : midNext (.S_hat 2 (2 * q) (d + 5)) = some (.S_def 1 (2 * q + 3) (d + 4)) := rfl
      have hj : (2 * q + 3) + 1 = 2 * (q + 2) := by omega
      exact CollatzStepsTo.head h1 (CollatzStepsTo.of_eq (by
        dsimp [midNext]; rw [hj, midEvalC_even_3 .S_def (q + 2) d _ rfl]
        simp only [toMid, Option.some.injEq, MidState.S_def.injEq]
        exact ⟨by omega, trivial, by omega⟩))

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

end BusyBeaver.M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD
