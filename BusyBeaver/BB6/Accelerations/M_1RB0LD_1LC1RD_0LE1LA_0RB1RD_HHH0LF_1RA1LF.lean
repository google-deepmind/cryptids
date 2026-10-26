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

end BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF
