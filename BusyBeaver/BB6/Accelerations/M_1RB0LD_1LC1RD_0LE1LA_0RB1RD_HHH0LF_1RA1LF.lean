/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`.

Each digit stack $S = [s_0, s_1, \dots]$ encodes unary blocks $1^{s_i + 1}$ separated by single
zeros (`encStack`), ordered from the tape head outward. Starting from `init []`, the machine
reaches $C(0, [0], [1])$ in 19 raw steps, where $C(a, L, R)$ has state `C` reading `0` between
`encStack (a :: L)` and `encStack R`.

## Accelerated Transition Rules

```text
transferD(a, L, [])     = C(a, L, [0])
transferD(a, L, d :: R) = transferD(d, a :: L, R)

C(0, [], R)      -> Halt
C(0, b :: L, R)  -> transferD(b, L, bumpHead (bumpHead R))
C(1, [], R)      -> C(0, [], 0 :: R)
C(1, b :: L, R)  -> C(b + 1, L, 0 :: R)
C(a + 2, L, R)   -> C(a, bumpHead L, bumpHead R)

Start: C(0, [0], [1]), reached after 19 raw TM steps
```

Restricting to the Poincaré return section $R = [0]$ eliminates the right stack completely, yielding
a single-stack transition system $C_{\mathrm{HL}}(a, L) := C(a, L, [0])$ starting at
$C_{\mathrm{HL}}(3, [0])$.
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Symbolic state space for the accelerated sandpile transition system of `target`. -/
inductive State where
  /-- Separator configuration `C(a, L, R)`: state `C` reading `0` between `a :: L` and `R`. -/
  | C (a : ℕ) (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Sweep all digits of `R` onto `a :: L` in state `D` and turn around into `C(..., [0])`. -/
def transferD (a : ℕ) (L R : List ℕ) : State :=
  let p := R.foldl (fun p d => (d, p.1 :: p.2)) (a, L)
  .C p.1 p.2 [0]

/-- Initial symbolic state `C(0, [0], [1])`, reached from `init []` in 19 raw steps. -/
def start : State := .C 0 [0] [1]

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a L R => Cfg.headRight C (encStack (a :: L)) (ListBlank.cons 0 (encStack R))

/-- Accelerated transition function (`none` indicates halting, reached only at `C(0, [], R)`). -/
def next : State → Option State
  | .C 0 [] _ => none
  | .C 0 (b :: L) R => some (transferD b L (bumpHead (bumpHead R)))
  | .C 1 [] R => some (.C 0 [] (0 :: R))
  | .C 1 (b :: L) R => some (.C (b + 1) L (0 :: R))
  | .C (a + 2) L R => some (.C a (bumpHead L) (bumpHead R))

/-! ## Stack Encoding and Sweep Helpers -/

private theorem encStack_cons_one (s : List ℕ) :
    ListBlank.cons 1 (encStack s) = encStack (bumpHead s) := by
  cases s with
  | nil => simp [bumpHead, encStack]
  | cons a s' => rfl

private theorem walk_D (k : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{D}}> ((([1] : List (Fin 2)) ^ k) +> r)) [target]⊢*
      ((l <+ (([1] : List (Fin 2)) ^ k)) {{D}}> r) := by
  induction k generalizing l r with
  | zero => bb_refl
  | succ k ih =>
    have h1 :
        (l {{D}}> ((([1] : List (Fin 2)) ^ (k + 1)) +> r)) [target]⊢⁺
          (([1] +> l) {{D}}> ((([1] : List (Fin 2)) ^ k) +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih ([1] +> l) r
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

private theorem walk_F (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ k)) <{{F}} r) [target]⊢*
      (l <{{F}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => bb_refl
  | succ k ih =>
    have h1 :
        ((l <+ (([1] : List (Fin 2)) ^ (k + 1))) <{{F}} r) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ k)) <{{F}} ([1] +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l ([1] +> r)
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

/-! ## Intermediate Configurations and Local Rules -/

private def cfgC (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgD (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D (encStack L) (ListBlank.cons 0 (encStack R))

private theorem rule_D_nil (a : ℕ) (L : List ℕ) :
    (cfgD (a :: L) []) [target]⊢⁺ (encode (.C a L [0])) := by
  unfold cfgD encode
  simp only [encStack, Nat.zero_add, list_pow_one]
  bb_steps

private theorem rule_D_cons (d : ℕ) (L R : List ℕ) :
    (cfgD L (d :: R)) [target]⊢⁺ (cfgD (d :: L) R) := by
  unfold cfgD
  have h_pre :
      (Cfg.headRight D (encStack L) (ListBlank.cons 0 (encStack (d :: R)))) [target]⊢⁺
        (([1] +> ((encStack L).cons 0)) {{D}}>
          ((([1] : List (Fin 2)) ^ d) +> ((encStack R).cons 0))) := by
    simp only [encStack]
    rw [ListBlank.append_pow_succ]
    bb_steps
  have h_sw := walk_D d ([1] +> ((encStack L).cons 0)) ((encStack R).cons 0)
  rw [ListBlank.append_pow_succ'] at h_sw
  simpa only [encStack] using h_pre.trans_star h_sw

private theorem reaches_transferD (a : ℕ) (L R : List ℕ) :
    (cfgD (a :: L) R) [target]⊢⁺ (encode (transferD a L R)) := by
  induction R generalizing a L with
  | nil => exact rule_D_nil a L
  | cons d R ih => exact (rule_D_cons d (a :: L) R).trans (ih d (a :: L))

private theorem halt_C_zero_nil (R : List ℕ) :
    ∃ cfg', ReachesStar target (encode (.C 0 [] R)) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight E default
    (ListBlank.cons 0 (ListBlank.cons 0 (encStack (bumpHead (bumpHead (bumpHead R)))))), ?_, ?_⟩
  · have h :
        ReachesPlus target (encode (.C 0 [] R))
          (Cfg.headRight E default
            (ListBlank.cons 0
              (ListBlank.cons 0 (encStack (bumpHead (bumpHead (bumpHead R))))))) := by
      simp only [encode, encStack, Nat.zero_add, list_pow_one]
      rw [← encStack_cons_one, ← encStack_cons_one, ← encStack_cons_one]
      bb_steps
    exact h.to_star
  · bb_halt

private theorem rule_C_zero_cons (b : ℕ) (L R : List ℕ) :
    (encode (.C 0 (b :: L) R)) [target]⊢⁺ (cfgD (b :: L) (bumpHead (bumpHead R))) := by
  unfold encode cfgD
  simp only [encStack, Nat.zero_add, list_pow_one]
  rw [ListBlank.append_pow_succ, ← encStack_cons_one, ← encStack_cons_one]
  bb_steps

private theorem rule_C_one (L R : List ℕ) :
    (cfgC (1 :: L) R) [target]⊢⁺ (cfgC (bumpHead L) (0 :: R)) := by
  unfold cfgC
  simp only [encStack, list_pow_succ, list_pow_zero]
  rw [← encStack_cons_one]
  bb_steps

private theorem rule_C_ge2 (a : ℕ) (L R : List ℕ) :
    (encode (.C (a + 2) L R)) [target]⊢⁺ (encode (.C a (bumpHead L) (bumpHead R))) := by
  unfold encode
  have h_pre :
      (Cfg.headRight C (encStack ((a + 2) :: L)) (ListBlank.cons 0 (encStack R))) [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 2))) <{{F}}
          (((encStack R).cons 0).cons 0)) := by
    simp only [encStack]
    rw [ListBlank.append_pow_succ]
    bb_steps
  have h_split :
      (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 2))) =
        (([1] +> ((encStack L).cons 0)) <+ (([1] : List (Fin 2)) ^ (a + 1))) := by
    rw [show a + 2 = (a + 1) + 1 by omega, list_pow_succ', ← ListBlank.append_append]
  rw [h_split] at h_pre
  have h_swF := walk_F (a + 1) ([1] +> ((encStack L).cons 0)) (((encStack R).cons 0).cons 0)
  have h_mid :
      (([1] +> ((encStack L).cons 0)) <{{F}}
        ((([1] : List (Fin 2)) ^ (a + 1)) +> (((encStack R).cons 0).cons 0))) [target]⊢⁺
        (([1] +> ((encStack (bumpHead L)).cons 0)) {{D}}>
          ((([1] : List (Fin 2)) ^ a) +> (((encStack R).cons 0).cons 0))) := by
    rw [ListBlank.append_pow_succ, ← encStack_cons_one]
    bb_steps
  have h_swD := walk_D a ([1] +> ((encStack (bumpHead L)).cons 0)) (((encStack R).cons 0).cons 0)
  rw [ListBlank.append_pow_succ'] at h_swD
  have h_post :
      ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))) {{D}}>
        (((encStack R).cons 0).cons 0)) [target]⊢⁺
        Cfg.headRight C (encStack (a :: bumpHead L))
          (ListBlank.cons 0 (encStack (bumpHead R))) := by
    simp only [encStack]
    rw [← encStack_cons_one R]
    bb_steps
  exact (((h_pre.trans_star h_swF).trans h_mid).trans_star h_swD).trans h_post

/-! ## Accelerated Step Verification -/

private theorem init_reaches_start : ReachesStar target (init []) (encode start) := by
  have h : ReachesPlus target (init []) (encode start) := by
    simp only [start, encode, encStack, list_pow_succ, list_pow_zero]
    bb_steps
  exact h.to_star

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start fun s => ?_
  rcases s with ⟨_ | _ | a, L, R⟩
  · rcases L with _ | ⟨b, L'⟩
    · exact halt_C_zero_nil R
    · simp only [next]
      exact (rule_C_zero_cons b L' R).trans (reaches_transferD b L' (bumpHead (bumpHead R)))
  · rcases L with _ | ⟨b, L'⟩
    · simp only [next, encode]
      exact rule_C_one [] R
    · simp only [next, encode]
      exact rule_C_one (b :: L') R
  · simp only [next]
    exact rule_C_ge2 a L R

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Acceleration -/

/-- Reduced single-stack state space $C_{\mathrm{HL}}(a, L) := C(a, L, [0])$ on the $R = [0]$
Poincaré return section. -/
inductive HighLevelState where
  /-- Separator configuration $C(a, L, [0])$ at the start of an epoch ($R = [0]$). -/
  | C (a : ℕ) (L : List ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level state $C_{\mathrm{HL}}(3, [0])$, reached in 1 `next` step from `start`. -/
def highLevelStart : HighLevelState := .C 3 [0]

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .C a L => .C a L [0]

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Sweep all digits of `R` onto `a :: L` and return to the $R = [0]$ section. -/
def transferHL (a : ℕ) (L R : List ℕ) : HighLevelState :=
  let p := R.foldl (fun p d => (d, p.1 :: p.2)) (a, L)
  .C p.1 p.2

/-- Contract an entire epoch of `next` steps until returning to $R = [0]$ or halting. -/
def stepEpoch (a : ℕ) (L R : List ℕ) : Option HighLevelState :=
  let k := a / 2
  let R₁ := bumpHeadBy k R
  if L = [] then
    if a ≤ 1 then none
    else if a % 2 = 0 then some (transferHL (k - 1) [] (bumpHead (bumpHead R₁)))
    else stepEpoch k [] (0 :: R₁)
  else
    let b := L.headD 0
    let L' := L.tail
    if a % 2 = 0 then some (transferHL (b + k) L' (bumpHead (bumpHead R₁)))
    else stepEpoch (b + k + 1) L' (0 :: R₁)
termination_by (L.length, a)
decreasing_by
  all_goals simp_wf
  · omega
  · cases L with
    | nil => contradiction
    | cons _ _ =>
      apply Prod.Lex.left
      simp +zetaDelta only [List.length_cons]
      omega

/-- High-level single-stack accelerated transition function on $C_{\mathrm{HL}}(a, L)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .C a L => stepEpoch a L [0]

private theorem bumpHeadBy_cons_eq (k b : ℕ) (L : List ℕ) :
    bumpHeadBy k (b :: L) = (b + k) :: L := by
  induction k generalizing b with
  | zero => simp [bumpHeadBy]
  | succ k ih =>
    simp only [bumpHeadBy, bumpHead]
    rw [ih (b + 1)]
    congr 1
    omega

private theorem bumpHeadBy_pos_nil {k : ℕ} (hk : k ≥ 1) :
    bumpHeadBy k [] = [k - 1] := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm 1 m]
  simp only [bumpHeadBy, bumpHead, bumpHeadBy_cons_eq, Nat.zero_add, Nat.add_sub_cancel]

private theorem reaches_mod2 (k r : ℕ) (L R : List ℕ) :
    CollatzReachesStar next (.C (2 * k + r) L R) (.C r (bumpHeadBy k L) (bumpHeadBy k R)) := by
  induction k generalizing L R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, bumpHeadBy]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    have h1 : next (.C (2 * (k + 1) + r) L R) =
        some (.C (2 * k + r) (bumpHead L) (bumpHead R)) := by
      rw [show 2 * (k + 1) + r = (2 * k + r) + 2 by omega]
      rfl
    exact CollatzReachesStar.head h1 (ih (bumpHead L) (bumpHead R))

private theorem stepsTo_stepEpoch_nil (a : ℕ) : ∀ R : List ℕ,
    CollatzStepsTo next (.C a [] R) ((stepEpoch a [] R).map toState) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro R
    rw [stepEpoch]
    simp only [↓reduceIte]
    have ha : 2 * (a / 2) + a % 2 = a := by omega
    have hstar := ha ▸ reaches_mod2 (a / 2) (a % 2) [] R
    refine CollatzStepsTo.of_reachesStar hstar ?_
    split_ifs with hle heven
    · have hk0 : a / 2 = 0 := by omega
      rw [hk0]
      simp only [bumpHeadBy, Option.map_none]
      rcases (show a % 2 = 0 ∨ a % 2 = 1 by omega) with hm0 | hm1
      · rw [hm0]
        exact CollatzStepsTo.of_eq rfl
      · rw [hm1]
        exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · have hk1 : a / 2 ≥ 1 := by omega
      rw [heven, bumpHeadBy_pos_nil hk1]
      exact CollatzStepsTo.of_eq rfl
    · have hk1 : a / 2 ≥ 1 := by omega
      have hmod1 : a % 2 = 1 := by omega
      rw [hmod1, bumpHeadBy_pos_nil hk1]
      have hstep :
          next (.C 1 [a / 2 - 1] (bumpHeadBy (a / 2) R)) =
            some (.C (a / 2) [] (0 :: bumpHeadBy (a / 2) R)) := by
        dsimp only [next]
        congr 2
        omega
      exact CollatzStepsTo.head hstep (ih (a / 2) (by omega) (0 :: bumpHeadBy (a / 2) R))

private theorem stepsTo_stepEpoch (L : List ℕ) : ∀ (a : ℕ) (R : List ℕ),
    CollatzStepsTo next (.C a L R) ((stepEpoch a L R).map toState) := by
  induction L with
  | nil => exact fun a R => stepsTo_stepEpoch_nil a R
  | cons b L' ihL =>
    intro a R
    rw [stepEpoch]
    simp only [reduceCtorEq, ↓reduceIte, List.headD_cons, List.tail_cons]
    have ha : 2 * (a / 2) + a % 2 = a := by omega
    have hstar := ha ▸ reaches_mod2 (a / 2) (a % 2) (b :: L') R
    refine CollatzStepsTo.of_reachesStar hstar ?_
    rw [bumpHeadBy_cons_eq]
    split_ifs with heven
    · rw [heven]
      exact CollatzStepsTo.of_eq rfl
    · have hmod1 : a % 2 = 1 := by omega
      rw [hmod1]
      exact CollatzStepsTo.head rfl (ihL (b + a / 2 + 1) (0 :: bumpHeadBy (a / 2) R))

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid acceleration of
`target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState)
    (CollatzReachesStar.single rfl) ?_
  rintro ⟨a, L⟩
  exact stepsTo_stepEpoch L a [0]

/-- `target` halts from the blank tape iff `highLevelNext` halts from `highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- The initial acceleration `next` halts from `start` iff `highLevelNext` halts from
`highLevelStart`. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF
