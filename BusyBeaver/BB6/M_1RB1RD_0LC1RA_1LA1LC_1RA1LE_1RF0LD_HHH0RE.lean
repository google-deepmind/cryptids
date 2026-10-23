/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`

We define the configuration for $a, c \ge 0$:

$$
P_1(a, c) := 0^\infty \ 1^a \ \mathrm{A}{>} \ 1^c \ 0^\infty.
$$

Starting from $P_1(2, 1)$ (reached after 6 steps from the blank tape), the machine follows the map
$T$:

$$
T(P_1(a, c)) = \begin{cases}
  P_1(2, a+1) & \text{if } c = 0, \\
  P_1(a+2, 0) & \text{if } c = 1, \\
  P_1(a+3, c-2) & \text{if } c \ge 2 \text{ and } a \text{ is even}, \\
  \text{Halt} & \text{if } c = 2 \text{ and } a \text{ is odd}, \\
  G(\lfloor a/2 \rfloor, 1) & \text{if } c = 3 \text{ and } a \text{ is odd}, \\
  G(\lfloor a/2 \rfloor + 1, c-2) & \text{if } c \ge 4 \text{ and } a \text{ is odd},
\end{cases}
$$

where $G(k, c)$ (the outcome of the countdown configuration $P_2(k, 0, c)$, with its diagonal
drain $P_2(k+1, m, c+2) \to P_2(k, m+2, c)$ collapsed) is defined recursively by:

$$
G(k, c) = \begin{cases}
  P_1(0, 2c+3) & \text{if } 2k \le c \le 2k+1, \\
  P_1(4k+4, c-2k-2) & \text{if } c \ge 2k+2, \\
  G(k - \lfloor c/2 \rfloor - 1, 2c+3) & \text{if } c < 2k.
\end{cases}
$$
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift Lemmas -/

/-- `C>` scanning `1` shifts leftward over `1^k`, preserving `1^k` on the right. -/
private theorem shift_C_left (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1] : List (Fin 2))^k) {{C}}> (([1] : List (Fin 2)) +> r)) [target]⊢*
    (l {{C}}> (([1] : List (Fin 2))^k +> (([1] : List (Fin 2)) +> r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h_split : (l <+ ([1] : List (Fin 2))^(k + 1)) =
        ((l <+ ([1] : List (Fin 2))^k) <+ ([1] : List (Fin 2))) := by
      rw [ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) k 1]; rfl
    rw [h_split]
    have h1 : (((l <+ ([1] : List (Fin 2))^k)
      <+ ([1] : List (Fin 2))) {{C}}> (([1] : List (Fin 2)) +> r))
        [target]⊢⁺
        ((l <+ ([1] : List (Fin 2))^k) {{C}}> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))
          +> r))) := by
      bb_steps
    have h2 := ih l (([1] : List (Fin 2)) +> r)
    have h12 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_comb : (([1] : List (Fin 2))^k +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))
      +> r))) =
        (([1] : List (Fin 2))^(k + 1) +> (([1] : List (Fin 2)) +> r)) := by
      rw [ListBlank.append_pow_add ([1] : List (Fin 2)) k 1 (([1] : List (Fin 2)) +> r)]
      rfl
    rwa [h_comb] at h12

/-- `E>` scanning `1` shifts leftward over `(11)^k`,
  turning each `(11)` into `(10)` on the right. -/
private theorem shift_ED_left (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 1] : List (Fin 2))^k) {{E}}> (([1] : List (Fin 2)) +> r)) [target]⊢*
    (l {{E}}> (([1] : List (Fin 2)) +> (([1, 0] : List (Fin 2))^k +> r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h_split : (l <+ ([1, 1] : List (Fin 2))^(k + 1)) =
        ((l <+ ([1, 1] : List (Fin 2))^k) <+ ([1, 1] : List (Fin 2))) := by
      rw [ListBlank.append_pow_add_rev l ([1, 1] : List (Fin 2)) k 1]; rfl
    rw [h_split]
    have h1 : (((l <+ ([1, 1] : List (Fin 2))^k) <+ ([1,
      1] : List (Fin 2))) {{E}}> (([1] : List (Fin 2)) +> r))
        [target]⊢⁺
        ((l <+ ([1, 1] : List (Fin 2))^k) {{E}}> (([1] : List (Fin 2)) +> (([1,
          0] : List (Fin 2)) +> r))) := by
      bb_steps
    have h2 := ih l (([1, 0] : List (Fin 2)) +> r)
    have h12 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_comb : (([1, 0] : List (Fin 2))^k +> (([1, 0] : List (Fin 2)) +> r)) =
        (([1, 0] : List (Fin 2))^(k + 1) +> r) := by
      rw [ListBlank.append_pow_add ([1, 0] : List (Fin 2)) k 1 r]; rfl
    rwa [h_comb] at h12

/-- `A>` shifts rightward over `(01)^k`, writing `(11)^k` on the left. -/
private theorem shift_AB_right (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{A}}> (([0, 1] : List (Fin 2))^k +> r)) [target]⊢*
    ((l <+ ([1, 1] : List (Fin 2))^k) {{A}}> r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h_split := ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k r
    rw [h_split]
    have h1 : (l {{A}}> (([0, 1] : List (Fin 2)) +> (([0, 1] : List (Fin 2))^k +> r)))
        [target]⊢⁺
        ((l <+ ([1, 1] : List (Fin 2))) {{A}}> (([0, 1] : List (Fin 2))^k +> r)) := by
      bb_steps
    have h2 := ih (l <+ ([1, 1] : List (Fin 2))) r
    have h12 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_comb : ((l <+ ([1, 1] : List (Fin 2))) <+ ([1, 1] : List (Fin 2))^k) =
        (l <+ ([1, 1] : List (Fin 2))^(k + 1)) := by
      have h_eq : k + 1 = 1 + k := by omega
      rw [h_eq, ListBlank.append_pow_add_rev l ([1, 1] : List (Fin 2)) 1 k]; rfl
    rwa [h_comb] at h12

/-- `F>` shifts rightward over `(10)^k`, writing `(01)^k` (`[1, 0]^k` on the left stack). -/
private theorem shift_FE_right (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{F}}> (([1, 0] : List (Fin 2))^k +> r)) [target]⊢*
    ((l <+ ([1, 0] : List (Fin 2))^k) {{F}}> r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h_split := ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) k r
    rw [h_split]
    have h1 : (l {{F}}> (([1, 0] : List (Fin 2)) +> (([1, 0] : List (Fin 2))^k +> r)))
        [target]⊢⁺
        ((l <+ ([1, 0] : List (Fin 2))) {{F}}> (([1, 0] : List (Fin 2))^k +> r)) := by
      bb_steps
    have h2 := ih (l <+ ([1, 0] : List (Fin 2))) r
    have h12 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_comb : ((l <+ ([1, 0] : List (Fin 2))) <+ ([1, 0] : List (Fin 2))^k) =
        (l <+ ([1, 0] : List (Fin 2))^(k + 1)) := by
      have h_eq : k + 1 = 1 + k := by omega
      rw [h_eq, ListBlank.append_pow_add_rev l ([1, 0] : List (Fin 2)) 1 k]; rfl
    rwa [h_comb] at h12

/-! ## Canonical Pattern Set and Accelerated Transition Rules -/

/-- Hub Pattern 1: `P1(a, c) := 0^∞ 1^a A> 1^c 0^∞` (`a, c ∈ ℕ`). -/
def pat_P1 : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1] 0 .default
    head  := some A
    right := .rep [1] 1 .default }

/-- Hub Pattern 2: `P2(k, m, c) := 0^∞ (10)^(k+1) (11)^m A> 1^c 0^∞` (`k, m, c ∈ ℕ`). -/
def pat_P2 : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1, 1] 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head  := some A
    right := .rep [1] 2 .default }

/-- The closed 2-hub pattern set `ps`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P1, .true), (pat_P2, .true)]

private def cfg_P1 (a c : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((default <+ ([1] : List (Fin 2))^a) {{A}}> (([1] : List (Fin 2))^c +> default))

private def cfg_P2 (k m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((((default <+ ([0, 1] : List (Fin 2))^k) << 1) << 0) <+ ([1, 1] : List (Fin 2))^m) {{A}}>
   (([1] : List (Fin 2))^c +> default))

private theorem eval_pat_P1 (vars : Nat → Nat) :
    evalTapePattern pat_P1 vars = cfg_P1 (vars 0) (vars 1) := rfl

private theorem eval_pat_P2 (vars : Nat → Nat) :
    evalTapePattern pat_P2 vars = cfg_P2 (vars 0) (vars 1) (vars 2) := rfl

private theorem in_ps_P1 (a c : Nat) : IsInPatternSet ps (cfg_P1 a c) := by
  refine ⟨(pat_P1, .true), List.Mem.head _, (fun i => match i with | 0 => a | _ => c), rfl, trivial⟩

private theorem in_ps_P2 (k m c : Nat) : IsInPatternSet ps (cfg_P2 k m c) := by
  refine ⟨(pat_P2, .true), List.Mem.tail _ (List.Mem.head _),
    (fun i => match i with | 0 => k | 1 => m | _ => c), rfl, trivial⟩

/-- Rule 1 (`P1, c = 0`): `P1(a, 0) -> P1(2, a + 1)` in `a + 6` steps. -/
private theorem rule_1 (a : Nat) :
    (cfg_P1 a 0) [target]⊢⁺ (cfg_P1 2 (a + 1)) := by
  have h1 : (cfg_P1 a 0) [target]⊢⁺
      ((default <+ ([1] : List (Fin 2))^a) {{C}}> (([1] : List (Fin 2)) +> default)) := by
    unfold cfg_P1
    simp only [list_pow_zero, ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := shift_C_left a default default
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (default {{C}}> (([1] : List (Fin 2))^a +> (([1] : List (Fin 2)) +> default)))
      [target]⊢⁺ (cfg_P1 2 (a + 1)) := by
    unfold cfg_P1
    have h_r : (([1] : List (Fin 2))^a +> (([1] : List (Fin 2)) +> (default : ListBlank (Fin 2)))) =
        (([1] : List (Fin 2))^(a + 1) +> default) := by
      rw [ListBlank.append_pow_add ([1] : List (Fin 2)) a 1 default]; rfl
    rw [h_r]
    simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  exact ReachesPlus.trans h12 h3

/-- Rule 2 (`P1, c = 1`): `P1(a, 1) -> P1(a + 2, 0)` in `2` steps. -/
private theorem rule_2 (a : Nat) :
    (cfg_P1 a 1) [target]⊢⁺ (cfg_P1 (a + 2) 0) := by
  unfold cfg_P1
  rw [ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) a 2]
  bb_steps

/-- Rule 3 (`P1, a = 2m, c = d + 2`): `P1(2m, d + 2) -> P1(2m + 3, d)` in `4m + 6` steps. -/
private theorem rule_3 (m d : Nat) :
    (cfg_P1 (2 * m) (d + 2)) [target]⊢⁺ (cfg_P1 (2 * m + 3) d) := by
  have h1 : (cfg_P1 (2 * m) (d + 2)) [target]⊢⁺
      ((default <+ ([1,
        1] : List (Fin 2))^m) {{E}}> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))
        +> (([1] : List (Fin 2))^d +> default)))) := by
    unfold cfg_P1
    rw [← one_pow_two_mul m]
    have h_eq : d + 2 = 2 + d := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 d default]
    simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := shift_ED_left m default (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (default {{E}}> (([1] : List (Fin 2)) +> (([1,
    0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default)))))
      [target]⊢⁺
      ((default << 1) {{A}}> (([0] : List (Fin 2)) +> (([1,
        0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d
        +> default))))) := by
    bb_steps
  have h123 := ReachesPlus.trans h12 h3
  rw [append_zero_10_pow_one_succ m (([1] : List (Fin 2))^d +> default)] at h123
  have h4 := shift_AB_right (m + 1) (default << 1) (([1] : List (Fin 2))^d +> default)
  have h1234 := ReachesPlus.trans_star h123 h4
  have h_l : ((default << 1) <+ ([1, 1] : List (Fin 2))^(m + 1)) =
      (default <+ ([1] : List (Fin 2))^(2 * m + 3)) := by
    rw [one_pow_two_mul (m + 1)]
    have h_d : ((default : ListBlank (Fin 2)) << (1 : Fin 2)) = default
      <+ ([1] : List (Fin 2))^1 := rfl
    rw [h_d, ← ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 1 (2 * (m + 1))]
    have h_eq : 1 + 2 * (m + 1) = 2 * m + 3 := by omega
    rw [h_eq]
  unfold cfg_P1
  rwa [h_l] at h1234

/-- Common prefix for Rules 4, 5, 6 (`a = 2m + 1, c = d + 2`): reaches `E>` in `4m + 8` steps. -/
private theorem odd_P1_to_E (m d : Nat) :
    (cfg_P1 (2 * m + 1) (d + 2)) [target]⊢⁺
    ((default <+ ([0, 1] : List (Fin 2))^(m + 2)) {{E}}> (([1] : List (Fin 2))^d +> default)) := by
  have h_l0 : (default <+ ([1] : List (Fin 2))^(2 * m + 1)) =
      ((default << 1) <+ ([1, 1] : List (Fin 2))^m) := by
    have h_eq : 2 * m + 1 = 1 + 2 * m := by omega
    rw [h_eq, ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 1 (2 * m)]
    rw [← one_pow_two_mul m]
    rfl
  have h1 : (cfg_P1 (2 * m + 1) (d + 2)) [target]⊢⁺
      (((default << 1) <+ ([1,
        1] : List (Fin 2))^m) {{E}}> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))
        +> (([1] : List (Fin 2))^d +> default)))) := by
    unfold cfg_P1
    rw [h_l0]
    have h_eq : d + 2 = 2 + d := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 d default]
    simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := shift_ED_left m (default << 1) (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d
    +> default))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : ((default << 1) {{E}}> (([1] : List (Fin 2)) +> (([1,
    0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default)))))
      [target]⊢⁺
      ((default << 1) {{F}}> (([1,
        0] : List (Fin 2))^(m + 1) +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d
        +> default)))) := by
    rw [ListBlank.append_pow_succ ([1,
      0] : List (Fin 2)) m (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default))]
    bb_steps
  have h123 := ReachesPlus.trans h12 h3
  have h4 := shift_FE_right (m + 1) (default << 1) (([1] : List (Fin 2))
    +> (([1] : List (Fin 2))^d +> default))
  have h1234 := ReachesPlus.trans_star h123 h4
  rw [show (((default : ListBlank (Fin 2)) << 1) <+ ([1, 0] : List (Fin 2))^(m + 1)) =
      (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2))^(m + 1)) << 1) from
    append_10_pow_one (m + 1) default] at h1234
  have h5 : (((default <+ ([0,
    1] : List (Fin 2))^(m + 1)) << 1) {{F}}> (([1] : List (Fin 2))
    +> (([1] : List (Fin 2))^d +> default)))
      [target]⊢⁺
      ((default <+ ([0,
        1] : List (Fin 2))^(m + 2)) {{E}}> (([1] : List (Fin 2))^d +> default)) := by
    rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) (m + 1) 1]
    bb_steps
  exact ReachesPlus.trans h1234 h5

/-- Rule 4 (`P1, a = 2m + 1, c = 2`): `P1(2m + 1, 2)` halts in `4m + 9` steps. -/
private theorem rule_4_halt (m : Nat) :
    ∃ cfg', ((cfg_P1 (2 * m + 1) 2) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  refine ⟨(((default <+ ([0, 1] : List (Fin 2))^(m + 2)) << 1) {{F}}> default), ?_, rfl⟩
  have h1 := odd_P1_to_E m 0
  have h2 : ((default <+ ([0,
    1] : List (Fin 2))^(m + 2)) {{E}}> (([1] : List (Fin 2))^0 +> default))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^(m + 2)) << 1) {{F}}> default) := by
    bb_steps
  exact ReachesPlus.trans h1 h2

/-- Rule 5 (`P1, a = 2m + 1, c = 3`): `P1(2m + 1, 3) -> P2(m, 1, 0)` in `4m + 10` steps. -/
private theorem rule_5 (m : Nat) :
    (cfg_P1 (2 * m + 1) 3) [target]⊢⁺ (cfg_P2 m 1 0) := by
  have h1 := odd_P1_to_E m 1
  have h2 : ((default <+ ([0,
    1] : List (Fin 2))^(m + 2)) {{E}}> (([1] : List (Fin 2))^1 +> default))
      [target]⊢⁺ (cfg_P2 m 1 0) := by
    unfold cfg_P2
    rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) (m + 1) 1]
    rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) m 1]
    simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  exact ReachesPlus.trans h1 h2

/-- Rule 6 (`P1, a = 2m + 1, c = d + 4`): `P1(2m + 1, d + 4) -> P2(m, 2, d)` in `4m + 12` steps. -/
private theorem rule_6 (m d : Nat) :
    (cfg_P1 (2 * m + 1) (d + 4)) [target]⊢⁺ (cfg_P2 m 2 d) := by
  have h1 := odd_P1_to_E m (d + 2)
  have h2 : ((default <+ ([0,
    1] : List (Fin 2))^(m + 2)) {{E}}> (([1] : List (Fin 2))^(d + 2) +> default))
      [target]⊢⁺ (cfg_P2 m 2 d) := by
    unfold cfg_P2
    rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) (m + 1) 1]
    rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) m 1]
    have h_eq : d + 2 = 2 + d := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 d default]
    simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  exact ReachesPlus.trans h1 h2

/-- Common helper for Rules 7 and 8 (`P2, c = 0`): `(((l << 1) << 0) <+ [1,
  1]^m) A> default -> l A> ([1]^(2m + 3) +> default)`. -/
private theorem rule_P2_c0 (l : ListBlank (Fin 2)) (m : Nat) :
    (((((l << 1) << 0) <+ ([1, 1] : List (Fin 2))^m) {{A}}> default)) [target]⊢⁺
    (l {{A}}> (([1] : List (Fin 2))^(2 * m + 3) +> default)) := by
  have h1 : (((((l << 1) << 0) <+ ([1, 1] : List (Fin 2))^m) {{A}}> default)) [target]⊢⁺
      ((((l << 1) << 0) <+ ([1] : List (Fin 2))^(2 * m)) {{C}}> (([1] : List (Fin 2))
        +> default)) := by
    rw [← one_pow_two_mul m]
    bb_steps
  have h2 := shift_C_left (2 * m) ((l << 1) << 0) default
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (((l << 1) << 0) {{C}}> (([1] : List (Fin 2))^(2 * m) +> (([1] : List (Fin 2))
    +> default)))
      [target]⊢⁺
      (l {{A}}> (([1] : List (Fin 2))^(2 * m + 3) +> default)) := by
    have h_r1 : (([1] : List (Fin 2))^(2 * m) +> (([1] : List (Fin 2))
      +> (default : ListBlank (Fin 2)))) =
        (([1] : List (Fin 2))^(2 * m + 1) +> default) := by
      rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * m) 1 default]; rfl
    have h_r2 : (([1] : List (Fin 2))^(2 * m + 3) +> (default : ListBlank (Fin 2))) =
        (([1] : List (Fin 2))^2 +> (([1] : List (Fin 2))^(2 * m + 1) +> default)) := by
      have h_eq : 2 * m + 3 = 2 + (2 * m + 1) := by omega
      rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * m + 1) default]
    rw [h_r1, h_r2]
    simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  exact ReachesPlus.trans h12 h3

/-- Rule 7 (`P2, k = 0, c = 0`): `P2(0, m, 0) -> P1(0, 2m + 3)` in `2m + 4` steps. -/
private theorem rule_7 (m : Nat) :
    (cfg_P2 0 m 0) [target]⊢⁺ (cfg_P1 0 (2 * m + 3)) := by
  unfold cfg_P2 cfg_P1
  simp only [list_pow_zero, ListBlank.append_nil]
  exact rule_P2_c0 default m

/-- Rule 8 (`P2, k = k' + 1, c = 0`): `P2(k' + 1, m, 0) -> P2(k', 0, 2m + 3)` in `2m + 4` steps. -/
private theorem rule_8 (k' m : Nat) :
    (cfg_P2 (k' + 1) m 0) [target]⊢⁺ (cfg_P2 k' 0 (2 * m + 3)) := by
  unfold cfg_P2
  rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) k' 1]
  simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons,
    ListBlank.append_nil]
  exact rule_P2_c0 (((default <+ ([0, 1] : List (Fin 2))^k') << 1) << 0) m

/-- Rule 9 (`P2, c = 1`): `P2(k, m, 1) -> P2(k, m + 1, 0)` in `2` steps. -/
private theorem rule_9 (k m : Nat) :
    (cfg_P2 k m 1) [target]⊢⁺ (cfg_P2 k (m + 1) 0) := by
  unfold cfg_P2
  rw [ListBlank.append_pow_add_rev (((default <+ ([0, 1] : List (Fin 2))^k) << 1) << 0) ([1,
    1] : List (Fin 2)) m 1]
  bb_steps

/-- Common helper for Rules 10 and 11 (`P2, c = d + 2`): `(((l << 1) << 0) <+ [1,
  1]^m) A> ([1]^(d + 2) +> default) -> (l <+ [1, 1]^(m + 2)) A> ([1]^d +> default)`. -/
private theorem rule_P2_c2 (l : ListBlank (Fin 2)) (m d : Nat) :
    (((((l << 1) << 0) <+ ([1,
      1] : List (Fin 2))^m) {{A}}> (([1] : List (Fin 2))^(d + 2) +> default))) [target]⊢⁺
    ((l <+ ([1, 1] : List (Fin 2))^(m + 2)) {{A}}> (([1] : List (Fin 2))^d +> default)) := by
  have h1 : (((((l << 1) << 0) <+ ([1,
    1] : List (Fin 2))^m) {{A}}> (([1] : List (Fin 2))^(d + 2) +> default))) [target]⊢⁺
      ((((l << 1) << 0) <+ ([1,
        1] : List (Fin 2))^m) {{E}}> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))
        +> (([1] : List (Fin 2))^d +> default)))) := by
    have h_eq : d + 2 = 2 + d := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 d default]
    simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h2 := shift_ED_left m ((l << 1) << 0) (([1] : List (Fin 2))
    +> (([1] : List (Fin 2))^d +> default))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (((l << 1) << 0) {{E}}> (([1] : List (Fin 2)) +> (([1,
    0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default)))))
      [target]⊢⁺
      ((l <+ ([1, 1] : List (Fin 2))) {{A}}> (([0] : List (Fin 2)) +> (([1,
        0] : List (Fin 2))^m +> (([1] : List (Fin 2)) +> (([1] : List (Fin 2))^d
        +> default))))) := by
    bb_steps
  have h123 := ReachesPlus.trans h12 h3
  rw [append_zero_10_pow_one_succ m (([1] : List (Fin 2))^d +> default)] at h123
  have h4 := shift_AB_right (m + 1) (l <+ ([1,
    1] : List (Fin 2))) (([1] : List (Fin 2))^d +> default)
  have h1234 := ReachesPlus.trans_star h123 h4
  have h_l : ((l <+ ([1, 1] : List (Fin 2))) <+ ([1, 1] : List (Fin 2))^(m + 1)) =
      (l <+ ([1, 1] : List (Fin 2))^(m + 2)) := by
    have h_eq : m + 2 = 1 + (m + 1) := by omega
    rw [h_eq, ListBlank.append_pow_add_rev l ([1, 1] : List (Fin 2)) 1 (m + 1)]; rfl
  rwa [h_l] at h1234

/-- Rule 10 (`P2, k = 0, c = d + 2`): `P2(0, m, d + 2) -> P1(2m + 4, d)` in `4m + 6` steps. -/
private theorem rule_10 (m d : Nat) :
    (cfg_P2 0 m (d + 2)) [target]⊢⁺ (cfg_P1 (2 * m + 4) d) := by
  unfold cfg_P2 cfg_P1
  simp only [list_pow_zero, ListBlank.append_nil]
  have h := rule_P2_c2 default m d
  have h_eq : 2 * m + 4 = 2 * (m + 2) := by omega
  rw [h_eq, ← one_pow_two_mul (m + 2)]
  exact h

/-- Rule 11 (`P2, k = k' + 1, c = d + 2`): `P2(k' + 1, m, d + 2) -> P2(k', m + 2,
  d)` in `4m + 6` steps. -/
private theorem rule_11 (k' m d : Nat) :
    (cfg_P2 (k' + 1) m (d + 2)) [target]⊢⁺ (cfg_P2 k' (m + 2) d) := by
  unfold cfg_P2
  rw [ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) k' 1]
  simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons,
    ListBlank.append_nil]
  exact rule_P2_c2 (((default <+ ([0, 1] : List (Fin 2))^k') << 1) << 0) m d

/-! ## Blank-Tape Entry and Closure -/

/-- Blank initial tape `init []` is `cfg_P1 0 0` and reaches `cfg_P1 2 1` in 6 steps. -/
private theorem init_reaches_P1 : (init []) [target]⊢* (cfg_P1 2 1) := by
  have h : (init [] : Cfg (Fin 2) (Fin 6)) = cfg_P1 0 0 := by
    unfold init cfg_P1
    simp only [list_pow_zero, ListBlank.append_nil]
    rfl
  rw [h]
  exact ReachesPlus.to_star (rule_1 0)

/-- Complete closure of Hub 1 (`cfg_P1 a c`) across all `(a, c) ∈ ℕ²` (Rules 1–6). -/
private theorem step_P1_all (a c : Nat) :
    ∃ cfg', ((cfg_P1 a c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases c with _ | c1
  · -- c = 0: Rule 1
    exact ⟨cfg_P1 2 (a + 1), rule_1 a, Or.inl (in_ps_P1 2 (a + 1))⟩
  · rcases c1 with _ | d
    · -- c = 1: Rule 2
      exact ⟨cfg_P1 (a + 2) 0, rule_2 a, Or.inl (in_ps_P1 (a + 2) 0)⟩
    · -- c = d + 2
      rcases nat_even_or_odd_two_mul a with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · -- a = 2 * m, c = d + 2: Rule 3
        exact ⟨cfg_P1 (2 * m + 3) d, rule_3 m d, Or.inl (in_ps_P1 (2 * m + 3) d)⟩
      · -- a = 2 * m + 1, c = d + 2
        rcases d with _ | d1
        · -- c = 2: Rule 4 (Halt)
          obtain ⟨cfg', h_plus, h_halt⟩ := rule_4_halt m
          exact ⟨cfg', h_plus, Or.inr h_halt⟩
        · rcases d1 with _ | d2
          · -- c = 3: Rule 5
            exact ⟨cfg_P2 m 1 0, rule_5 m, Or.inl (in_ps_P2 m 1 0)⟩
          · -- c = d2 + 4: Rule 6
            exact ⟨cfg_P2 m 2 d2, rule_6 m d2, Or.inl (in_ps_P2 m 2 d2)⟩

/-- Complete closure of Hub 2 (`cfg_P2 k m c`) across all `(k, m, c) ∈ ℕ³` (Rules 7–11). -/
private theorem step_P2_all (k m c : Nat) :
    ∃ cfg', ((cfg_P2 k m c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases c with _ | c1
  · -- c = 0
    rcases k with _ | k'
    · -- k = 0, c = 0: Rule 7
      exact ⟨cfg_P1 0 (2 * m + 3), rule_7 m, Or.inl (in_ps_P1 0 (2 * m + 3))⟩
    · -- k = k' + 1, c = 0: Rule 8
      exact ⟨cfg_P2 k' 0 (2 * m + 3), rule_8 k' m, Or.inl (in_ps_P2 k' 0 (2 * m + 3))⟩
  · rcases c1 with _ | d
    · -- c = 1: Rule 9
      exact ⟨cfg_P2 k (m + 1) 0, rule_9 k m, Or.inl (in_ps_P2 k (m + 1) 0)⟩
    · -- c = d + 2
      rcases k with _ | k'
      · -- k = 0, c = d + 2: Rule 10
        exact ⟨cfg_P1 (2 * m + 4) d, rule_10 m d, Or.inl (in_ps_P1 (2 * m + 4) d)⟩
      · -- k = k' + 1, c = d + 2: Rule 11
        exact ⟨cfg_P2 k' (m + 2) d, rule_11 k' m d, Or.inl (in_ps_P2 k' (m + 2) d)⟩

/-! ## Countdown and Exponential Macro-Transitions

Additional accelerated transitions on `P2` (not needed for the closure theorems below). -/

/-! ## Closed Pattern Set (Level A) -/

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_P1 2 1, init_reaches_P1, in_ps_P1 2 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  rcases h_mem with ⟨⟩ | ⟨_, ⟨⟩ | ⟨_, h_mem⟩⟩
  · rw [eval_pat_P1]
    exact step_P1_all (vars 0) (vars 1)
  · rw [eval_pat_P2]
    exact step_P2_all (vars 0) (vars 1) (vars 2)
  · nomatch h_mem

/-- `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

inductive State
  | P_1 (a c : Nat)
  | P_2 (k m c : Nat)

def start : State := .P_1 2 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 a c => evalTapePattern pat_P1 (fun i => if i = 0 then a else if i = 1 then c else 0)
  | .P_2 k m c => evalTapePattern pat_P2
      (fun i => if i = 0 then k else if i = 1 then m else if i = 2 then c else 0)

def next : State → Option State
  | .P_1 a 0 => some (.P_1 2 (a + 1))
  | .P_1 a 1 => some (.P_1 (a + 2) 0)
  | .P_1 a (c + 2) =>
    if a % 2 = 0 then some (.P_1 (a + 3) c)
    else
      Nat.casesOn c none fun c =>
      Nat.casesOn c (some (.P_2 (a / 2) 1 0)) fun d =>
      some (.P_2 (a / 2) 2 d)
  | .P_2 k m 1 => some (.P_2 k (m + 1) 0)
  | .P_2 0 m 0 => some (.P_1 0 (2 * m + 3))
  | .P_2 (k + 1) m 0 => some (.P_2 k 0 (2 * m + 3))
  | .P_2 0 m (d + 2) => some (.P_1 (2 * m + 4) d)
  | .P_2 (k + 1) m (d + 2) => some (.P_2 k (m + 2) d)

private theorem step_state : ∀ s : State,
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone = true
  | .P_1 a 0 => rule_1 a
  | .P_1 a 1 => rule_2 a
  | .P_1 a (c + 2) => by
    have ha : (∃ m, a = 2 * m) ∨ (∃ m, a = 2 * m + 1) := nat_even_or_odd_two_mul a
    cases ha with
    | inl h =>
      rcases h with ⟨m, rfl⟩
      have h1 : (2 * m) % 2 = 0 := by omega
      simp only [next, h1, ↓reduceIte]
      exact rule_3 m c
    | inr h =>
      rcases h with ⟨m, rfl⟩
      have h1 : (2 * m + 1) % 2 = 1 := by omega
      have h2 : (2 * m + 1) / 2 = m := by omega
      simp only [next, h1, Nat.one_ne_zero, ↓reduceIte, h2]
      cases c with
      | zero =>
        have hh := rule_4_halt m
        rcases hh with ⟨cfg', hp, hd⟩
        exact ⟨cfg', ReachesPlus.to_star hp, hd⟩
      | succ c =>
        cases c with
        | zero => exact rule_5 m
        | succ d => exact rule_6 m d
  | .P_2 k m 1 => rule_9 k m
  | .P_2 0 m 0 => rule_7 m
  | .P_2 (k + 1) m 0 => rule_8 k m
  | .P_2 0 m (d + 2) => rule_10 m d
  | .P_2 (k + 1) m (d + 2) => rule_11 k m d

theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_P1
  step_some := fun s s' hnext => by
    have h := step_state s
    rw [hnext] at h
    exact h
  step_none := fun s hnext => by
    have h := step_state s
    rw [hnext] at h
    exact h

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-Like Acceleration -/

/-- Single-family state space $P_1(a, c) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^c\,0^\infty$ for the
high-level Collatz-like acceleration. -/
inductive HighLevelState where
  /-- $P_1(a, c) := 0^\infty\,1^a\,\mathrm{A}{>}\,1^c\,0^\infty$. -/
  | P_1 (a c : ℕ)

/-- Initial state $P_1(2, 1)$ for the high-level Collatz-like acceleration. -/
def highLevelStart : HighLevelState := .P_1 2 1

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .P_1 a c => .P_1 a c

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Outcome of the countdown family $P_2(k, 0, c)$ when run until it returns to $P_1$: the
diagonal drain $P_2(k + 1, m, c + 2) \to P_2(k, m + 2, c)$ is collapsed into a single step. -/
def evalP2 (k c : ℕ) : HighLevelState :=
  if 2 * k ≤ c then
    if c ≤ 2 * k + 1 then .P_1 0 (2 * c + 3) else .P_1 (4 * k + 4) (c - 2 * k - 2)
  else evalP2 (k - c / 2 - 1) (2 * c + 3)
termination_by k
decreasing_by omega

/-- High-level accelerated Collatz-like transition function on $P_1(a, c)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .P_1 a 0 => some (.P_1 2 (a + 1))
  | .P_1 a 1 => some (.P_1 (a + 2) 0)
  | .P_1 a (c + 2) =>
    if a % 2 = 0 then some (.P_1 (a + 3) c)
    else if c = 0 then none
    else if c = 1 then some (evalP2 (a / 2) 1)
    else some (evalP2 (a / 2 + 1) c)

/-- Outcome of $P_2(k, m, c)$ with the diagonal drain collapsed (general `m`). -/
private def evalP2m (k m c : ℕ) : HighLevelState :=
  if k ≤ c / 2 then
    if c ≤ 2 * k + 1 then .P_1 0 (2 * m + 2 * c + 3)
    else .P_1 (2 * m + 4 * k + 4) (c - 2 * k - 2)
  else evalP2 (k - c / 2 - 1) (2 * m + 2 * c + 3)

private theorem evalP2_eq (k c : ℕ) : evalP2 k c = evalP2m k 0 c := by
  rw [evalP2, evalP2m]
  split_ifs <;> first
    | omega
    | exact congrArg₂ HighLevelState.P_1 (by omega) (by omega)
    | exact congrArg₂ evalP2 (by omega) (by omega)

private theorem evalP2_one_eq (k : ℕ) : evalP2 k 1 = evalP2m k 1 0 := by
  rw [evalP2, evalP2m]
  split_ifs <;> first
    | omega
    | exact congrArg₂ HighLevelState.P_1 (by omega) (by omega)
    | exact congrArg₂ evalP2 (by omega) (by omega)

private theorem evalP2_succ_eq (k c : ℕ) : evalP2 (k + 1) (c + 2) = evalP2m k 2 c := by
  rw [evalP2, evalP2m]
  have h : (c + 2) / 2 = c / 2 + 1 := by omega
  split_ifs <;> first
    | omega
    | exact congrArg₂ HighLevelState.P_1 (by omega) (by omega)
    | exact congrArg₂ evalP2 (by omega) (by omega)

private theorem drain_P2 : ∀ (t k m c : ℕ),
    CollatzReachesStar next (.P_2 (k + t) m (c + 2 * t)) (.P_2 k (m + 2 * t) c)
  | 0, _, _, _ => CollatzReachesStar.refl _ _
  | t + 1, k, m, c => by
    have h : next (.P_2 (k + (t + 1)) m (c + 2 * (t + 1))) =
        some (.P_2 (k + t) (m + 2) (c + 2 * t)) := by
      rw [show c + 2 * (t + 1) = c + 2 * t + 2 by omega]
      rfl
    refine CollatzReachesStar.head h ?_
    rw [show m + 2 * (t + 1) = m + 2 + 2 * t by omega]
    exact drain_P2 t k (m + 2) c

private theorem stepsTo_P2 (k : ℕ) : ∀ (m c : ℕ),
    CollatzStepsTo next (.P_2 k m c) (some (toState (evalP2m k m c))) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m c
    by_cases hk : k ≤ c / 2
    · obtain ⟨e, rfl⟩ : ∃ e, c = e + 2 * k := ⟨c - 2 * k, by omega⟩
      have hd := drain_P2 k 0 m e
      rw [Nat.zero_add] at hd
      refine CollatzStepsTo.of_reachesStar hd ?_
      rcases e with _ | _ | e
      · have hv : evalP2m k m (0 + 2 * k) = .P_1 0 (2 * (m + 2 * k) + 3) := by
          rw [evalP2m]
          split_ifs <;> first
          | omega
          | exact congrArg₂ HighLevelState.P_1 (by omega) (by omega)
        rw [hv]
        exact CollatzStepsTo.of_eq rfl
      · have hv : evalP2m k m (1 + 2 * k) = .P_1 0 (2 * (m + 2 * k + 1) + 3) := by
          rw [evalP2m]
          split_ifs <;> first
          | omega
          | exact congrArg₂ HighLevelState.P_1 (by omega) (by omega)
        rw [hv]
        exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
      · have hv : evalP2m k m (e + 2 + 2 * k) = .P_1 (2 * (m + 2 * k) + 4) e := by
          rw [evalP2m]
          split_ifs <;> first
          | omega
          | exact congrArg₂ HighLevelState.P_1 (by omega) (by omega)
        rw [hv]
        exact CollatzStepsTo.of_eq rfl
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 + c / 2 := ⟨k - 1 - c / 2, by omega⟩
      have hc : c = c % 2 + 2 * (c / 2) := by omega
      have hd := drain_P2 (c / 2) (k' + 1) m (c % 2)
      rw [← hc] at hd
      refine CollatzStepsTo.of_reachesStar hd ?_
      have hr : evalP2m (k' + 1 + c / 2) m c = evalP2m k' 0 (2 * m + 2 * c + 3) := by
        simp only [evalP2m, hk, ↓reduceIte]
        rw [evalP2_eq]
        congr 1
        omega
      rw [hr]
      have ih' := ih k' (by omega) 0 (2 * m + 2 * c + 3)
      rcases Nat.mod_two_eq_zero_or_one c with h2 | h2
      · rw [h2]
        refine CollatzStepsTo.head ?_ ih'
        change some (State.P_2 k' 0 (2 * (m + 2 * (c / 2)) + 3)) = _
        congr 2
        omega
      · rw [h2]
        refine CollatzStepsTo.head rfl (CollatzStepsTo.head ?_ ih')
        change some (State.P_2 k' 0 (2 * (m + 2 * (c / 2) + 1) + 3)) = _
        congr 2
        omega

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState) (CollatzReachesStar.refl next start) ?_
  rintro ⟨a, c⟩
  rcases c with _ | _ | c
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.of_eq rfl
  · by_cases heven : a % 2 = 0
    · exact CollatzStepsTo.of_eq (by simp [highLevelNext, next, toState, heven])
    · rcases c with _ | _ | d
      · exact CollatzStepsTo.of_eq (by simp [highLevelNext, next, toState, heven])
      · have h : highLevelNext (.P_1 a 3) = some (evalP2 (a / 2) 1) := by
          simp [highLevelNext, heven]
        rw [h, Option.map_some, evalP2_one_eq]
        exact CollatzStepsTo.head (by simp [next, toState, heven]) (stepsTo_P2 (a / 2) 1 0)
      · have h : highLevelNext (.P_1 a (d + 4)) = some (evalP2 (a / 2 + 1) (d + 2)) := by
          simp [highLevelNext, heven]
        rw [h, Option.map_some, evalP2_succ_eq]
        exact CollatzStepsTo.head (by simp [next, toState, heven]) (stepsTo_P2 (a / 2) 2 d)

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

end BusyBeaver.M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE
