/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`.

Along the trajectory from step 4 onward, the machine returns to right-moving configurations
$$B(L, E, c) := \mathrm{encStack}(L)\,\mathrm{B}{>}\,\mathrm{encRight}(E, c)$$
where `encStack L` encodes unary blocks $1^{a_i + 1} 0$ outward on the left and `encRight E c`
encodes even-width blocks $1^{2 e_j + 1} 0$ followed by a bottom block $1^{c + 1}$ on the right.
Starting from `init []`, the machine reaches $B([0], [], 1)$ in 4 raw steps.

## Accelerated Transition Rules

```text
drainD([], E, c)              = B([0], E, c)
drainD((2k + 1) :: Lt, E, c)  = B(bumpHead Lt, 0^(k + 1) ++ E, c)
drainD(2k :: Lt, E, c)        = drainD(Lt, [], c + 2)              if 0^k ++ E = []
                              = drainD(Lt, (e + 1) :: Et, c)       if 0^k ++ E = e :: Et

B(L, [], c)                   -> drainD(bumpHeadBy c L, [], 3)
B(L, [e0], 0)                 -> drainD(bumpHeadBy (2 * e0) L, [], 2)
B(L, [e0], 1)                 -> Halt
B(L, [e0], 2)                 -> B(bumpHead (bumpHeadBy (2 * e0) L), [0, 0], 1)
B(L, [e0], 3)                 -> drainD(bumpHeadBy (2 * e0) L, [1], 0)
B(L, [e0], c + 4)             -> drainD(bumpHeadBy (2 * e0) L, [1, 0], c)
B(L, e0 :: 0 :: E2, c)        -> drainD(bumpHeadBy (2 * e0) L, 1 :: E2, c)
B(L, e0 :: 1 :: E2, c)        -> B(4 :: bumpHeadBy (2 * e0) L, E2, c)
B(L, e0 :: (e1 + 2) :: E2, c) -> drainD(4 :: bumpHeadBy (2 * e0) L, e1 :: E2, c)

Start: B([0], [], 1), reached after 4 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Encode an even-prefix right stack `E` with bottom block `c` as `1^{2e + 1} 0 ... 1^{c + 1}`. -/
def encRight (E : List ℕ) (c : ℕ) : ListBlank (Fin 2) :=
  List.rec (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)
    (fun e _ ih =>
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * e + 1)) (ListBlank.cons 0 ih))
    E

/-- Symbolic state space for the accelerated transition system of `target`. -/
inductive State where
  /-- Right-moving configuration `B(L, E, c)`: `encStack L` with `B>` on `encRight E c`. -/
  | B (L E : List ℕ) (c : ℕ)
  deriving DecidableEq, Repr

/-- Drain a `<D` sweep across `L` onto `(E, c)` until `B>` re-emerges. -/
def drainD : List ℕ → List ℕ → ℕ → State
  | [], E, c => .B [0] E c
  | a :: Lt, E, c =>
    if a % 2 = 1 then
      .B (bumpHead Lt) (List.replicate (a / 2 + 1) 0 ++ E) c
    else
      List.casesOn (List.replicate (a / 2) 0 ++ E) (drainD Lt [] (c + 2))
        fun e Et => drainD Lt ((e + 1) :: Et) c

/-- Initial symbolic state `B([0], [], 1)`, reached from `init []` in 4 raw steps. -/
def start : State := .B [0] [] 1

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .B L E c => Cfg.headRight B (encStack L) (encRight E c)

/-- Accelerated transition function (`none` indicates halting, reached only at `B(L, [e0], 1)`). -/
def next : State → Option State
  | .B L [] c => some (drainD (bumpHeadBy c L) [] 3)
  | .B L [e₀] 0 => some (drainD (bumpHeadBy (2 * e₀) L) [] 2)
  | .B _ [_] 1 => none
  | .B L [e₀] 2 => some (.B (bumpHead (bumpHeadBy (2 * e₀) L)) [0, 0] 1)
  | .B L [e₀] 3 => some (drainD (bumpHeadBy (2 * e₀) L) [1] 0)
  | .B L [e₀] (c + 4) => some (drainD (bumpHeadBy (2 * e₀) L) [1, 0] c)
  | .B L (e₀ :: 0 :: E₂) c => some (drainD (bumpHeadBy (2 * e₀) L) (1 :: E₂) c)
  | .B L (e₀ :: 1 :: E₂) c => some (.B (4 :: bumpHeadBy (2 * e₀) L) E₂ c)
  | .B L (e₀ :: (e₁ + 2) :: E₂) c => some (drainD (4 :: bumpHeadBy (2 * e₀) L) (e₁ :: E₂) c)

/-! ## Stack Encoding and Shift Lemmas -/

private theorem encRight_nil (c : ℕ) :
    encRight [] c = ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default := rfl

private theorem encRight_cons (e : ℕ) (E : List ℕ) (c : ℕ) :
    encRight (e :: E) c =
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * e + 1))
        (ListBlank.cons 0 (encRight E c)) := rfl

private theorem one_cons_encStack (L : List ℕ) :
    ListBlank.cons 1 (encStack L) = encStack (bumpHead L) := by
  cases L with
  | nil => simp [bumpHead, encStack]
  | cons a Lt => rfl

private theorem ones_append_encStack (d : ℕ) (L : List ℕ) :
    ListBlank.append (([1] : List (Fin 2)) ^ d) (encStack L) = encStack (bumpHeadBy d L) := by
  induction d generalizing L with
  | zero => rfl
  | succ d ih =>
    rw [← ListBlank.append_pow_succ']
    change ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 1 (encStack L)) = _
    rw [one_cons_encStack, ih]
    rfl

private theorem step_B_shift (d : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{B}}> ((([1] : List (Fin 2)) ^ (d + 1)) +> ListBlank.cons 0 r)) [target]⊢⁺
      (([1, 0] +> ((([1] : List (Fin 2)) ^ d) +> l)) {{A}}> r) := by
  induction d generalizing l with
  | zero =>
    simp only [Nat.zero_add, list_pow_succ, list_pow_zero]
    bb_steps
  | succ d ih =>
    have h1 :
        (l {{B}}> ((([1] : List (Fin 2)) ^ (d + 2)) +> ListBlank.cons 0 r)) [target]⊢⁺
          (([1] +> l) {{B}}> ((([1] : List (Fin 2)) ^ (d + 1)) +> ListBlank.cons 0 r)) := by
      rw [ListBlank.append_pow_succ, ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih ([1] +> l)
    rw [ListBlank.append_pow_succ'] at h2
    exact h1.trans h2

/-! ## Leftward `<D` Drain Simulation -/

private def cfgD (L E : List ℕ) (c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encStack L) <{{D}} (encRight E c)

private theorem rule_D_nil (E : List ℕ) (c : ℕ) :
    (cfgD [] E c) [target]⊢⁺ encode (.B [0] E c) := by
  unfold cfgD encode
  simp only [encStack, ListBlank.cons_zero_default]
  bb_steps

private theorem rule_D_one (Lt E : List ℕ) (c : ℕ) :
    (cfgD (1 :: Lt) E c) [target]⊢⁺ encode (.B (bumpHead Lt) (0 :: E) c) := by
  unfold cfgD encode
  change (([1, 1, 0] +> encStack Lt) <{{D}} (encRight E c)) [target]⊢⁺
    ((encStack (bumpHead Lt)) {{B}}> ([1, 0] +> encRight E c))
  rw [← one_cons_encStack]
  bb_steps

private theorem rule_D_add_two (a : ℕ) (Lt E : List ℕ) (c : ℕ) :
    (cfgD ((a + 2) :: Lt) E c) [target]⊢⁺ cfgD (a :: Lt) (0 :: E) c := by
  unfold cfgD
  have ha : a + 2 + 1 = 2 + (a + 1) := by omega
  change (((([1] : List (Fin 2)) ^ (a + 2 + 1)) +> ListBlank.cons 0 (encStack Lt)) <{{D}}
      (encRight E c)) [target]⊢⁺
    ((encStack (a :: Lt)) <{{D}} ([1, 0] +> encRight E c))
  rw [ha, ListBlank.append_pow_add]
  change (([1, 1] +> encStack (a :: Lt)) <{{D}} (encRight E c)) [target]⊢⁺ _
  bb_steps

private theorem peel_D_two (k r₀ : ℕ) (Lt E : List ℕ) (c : ℕ) :
    (cfgD ((2 * k + r₀) :: Lt) E c) [target]⊢*
      cfgD (r₀ :: Lt) (List.replicate k 0 ++ E) c := by
  induction k generalizing E with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, List.replicate, List.nil_append]
    bb_refl
  | succ k ih =>
    have hk : 2 * (k + 1) + r₀ = (2 * k + r₀) + 2 := by omega
    have hrep : List.replicate (k + 1) 0 ++ E = List.replicate k 0 ++ (0 :: E) := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [hk, hrep]
    exact (rule_D_add_two (2 * k + r₀) Lt E c).to_star.trans (ih (0 :: E))

private theorem rule_D_zero_raw (l s : ListBlank (Fin 2)) :
    (([1, 0] +> l) <{{D}} ([1] +> s)) [target]⊢⁺ (l <{{D}} ([1, 1, 1] +> s)) := by
  bb_steps

private theorem rule_D_zero_nil (Lt : List ℕ) (c : ℕ) :
    (cfgD (0 :: Lt) [] c) [target]⊢⁺ cfgD Lt [] (c + 2) := by
  unfold cfgD
  rw [encRight_nil, encRight_nil]
  change (([1, 0] +> encStack Lt) <{{D}} ((([1] : List (Fin 2)) ^ (c + 1)) +> default)) [target]⊢⁺
    ((encStack Lt) <{{D}} ((([1] : List (Fin 2)) ^ (c + 2 + 1)) +> default))
  have hc1 : c + 1 = 1 + c := by omega
  have hc2 : c + 2 + 1 = 3 + c := by omega
  rw [hc1, hc2, ListBlank.append_pow_add, ListBlank.append_pow_add]
  exact rule_D_zero_raw (encStack Lt) ((([1] : List (Fin 2)) ^ c) +> default)

private theorem rule_D_zero_cons (Lt : List ℕ) (e : ℕ) (Et : List ℕ) (c : ℕ) :
    (cfgD (0 :: Lt) (e :: Et) c) [target]⊢⁺ cfgD Lt ((e + 1) :: Et) c := by
  unfold cfgD
  rw [encRight_cons, encRight_cons]
  have he1 : 2 * e + 1 = 1 + 2 * e := by omega
  have he2 : 2 * (e + 1) + 1 = 3 + 2 * e := by omega
  rw [he1, he2, ListBlank.append_pow_add, ListBlank.append_pow_add]
  exact rule_D_zero_raw (encStack Lt)
    ((([1] : List (Fin 2)) ^ (2 * e)) +> ListBlank.cons 0 (encRight Et c))

private theorem reaches_drainD :
    ∀ (L E : List ℕ) (c : ℕ), (cfgD L E c) [target]⊢⁺ encode (drainD L E c)
  | [], E, c => rule_D_nil E c
  | a :: Lt, E, c => by
    by_cases hodd : a % 2 = 1
    · simp only [drainD, hodd, ↓reduceIte]
      have ha : a = 2 * (a / 2) + 1 := by omega
      have hpeel := peel_D_two (a / 2) 1 Lt E c
      rw [← ha] at hpeel
      have h1 := hpeel.trans_plus (rule_D_one Lt (List.replicate (a / 2) 0 ++ E) c)
      have hrep : 0 :: (List.replicate (a / 2) 0 ++ E) = List.replicate (a / 2 + 1) 0 ++ E := by
        rw [List.replicate_succ, List.cons_append]
      rwa [← hrep]
    · simp only [drainD, hodd, ↓reduceIte]
      have ha : a = 2 * (a / 2) + 0 := by omega
      have hpeel := peel_D_two (a / 2) 0 Lt E c
      rw [← ha] at hpeel
      rcases hE1 : List.replicate (a / 2) 0 ++ E with _ | ⟨e, Et⟩
      · rw [hE1] at hpeel
        exact hpeel.trans_plus ((rule_D_zero_nil Lt c).trans (reaches_drainD Lt [] (c + 2)))
      · rw [hE1] at hpeel
        exact hpeel.trans_plus
          ((rule_D_zero_cons Lt e Et c).trans (reaches_drainD Lt ((e + 1) :: Et) c))

/-! ## Rightward `B>` Turnaround Rules -/

private theorem init_reaches_start : (init []) [target]⊢* encode start := by
  simp only [start, encode, encStack, encRight_nil, list_pow_succ, list_pow_zero,
    ListBlank.cons_zero_default]
  bb_steps

private theorem step_B_empty (L : List ℕ) (c : ℕ) :
    (encode (.B L [] c)) [target]⊢⁺ encode (drainD (bumpHeadBy c L) [] 3) := by
  have hshift :
      (encode (.B L [] c)) [target]⊢⁺ ((encStack (0 :: bumpHeadBy c L)) {{A}}> default) := by
    simp only [encode, encRight_nil, encStack, Nat.zero_add, list_pow_one]
    conv_lhs => rw [← ListBlank.cons_zero_default]
    have h := step_B_shift c (encStack L) default
    rwa [ones_append_encStack] at h
  have hturn :
      ((encStack (0 :: bumpHeadBy c L)) {{A}}> default) [target]⊢⁺ cfgD (bumpHeadBy c L) [] 3 := by
    unfold cfgD
    simp only [encStack, encRight_nil, list_pow_succ, list_pow_zero]
    bb_steps
  exact (hshift.trans hturn).trans (reaches_drainD (bumpHeadBy c L) [] 3)

private theorem shift_B_cons (L : List ℕ) (e₀ : ℕ) (Et : List ℕ) (c : ℕ) :
    (encode (.B L (e₀ :: Et) c)) [target]⊢⁺
      ((encStack (0 :: bumpHeadBy (2 * e₀) L)) {{A}}> (encRight Et c)) := by
  simp only [encode, encRight_cons, encStack, Nat.zero_add, list_pow_one]
  have h := step_B_shift (2 * e₀) (encStack L) (encRight Et c)
  rwa [ones_append_encStack] at h

private theorem step_B_single_zero (L : List ℕ) (e₀ : ℕ) :
    (encode (.B L [e₀] 0)) [target]⊢⁺ encode (drainD (bumpHeadBy (2 * e₀) L) [] 2) := by
  have hturn :
      ((encStack (0 :: bumpHeadBy (2 * e₀) L)) {{A}}> (encRight [] 0)) [target]⊢⁺
        cfgD (bumpHeadBy (2 * e₀) L) [] 2 := by
    unfold cfgD
    simp only [encStack, encRight_nil, list_pow_succ, list_pow_zero]
    bb_steps
  exact ((shift_B_cons L e₀ [] 0).trans hturn).trans (reaches_drainD (bumpHeadBy (2 * e₀) L) [] 2)

private theorem halt_B_single_one (L : List ℕ) (e₀ : ℕ) :
    ∃ cfg', ((encode (.B L [e₀] 1)) [target]⊢* cfg') ∧ (step target cfg').isNone := by
  let l₁ := encStack (bumpHeadBy (2 * e₀) L)
  refine ⟨([1, 1, 1, 0] +> l₁) {{F}}> default, ?_, by bb_halt⟩
  have hhalt :
      ((encStack (0 :: bumpHeadBy (2 * e₀) L)) {{A}}> (encRight [] 1)) [target]⊢⁺
        (([1, 1, 1, 0] +> l₁) {{F}}> default) := by
    simp only [encStack, encRight_nil, list_pow_succ, list_pow_zero, l₁]
    bb_steps
  exact ((shift_B_cons L e₀ [] 1).trans hhalt).to_star

private theorem step_B_single_two (L : List ℕ) (e₀ : ℕ) :
    (encode (.B L [e₀] 2)) [target]⊢⁺ encode (.B (bumpHead (bumpHeadBy (2 * e₀) L)) [0, 0] 1) := by
  have hturn :
      ((encStack (0 :: bumpHeadBy (2 * e₀) L)) {{A}}> (encRight [] 2)) [target]⊢⁺
        cfgD (3 :: bumpHeadBy (2 * e₀) L) [] 1 := by
    unfold cfgD
    simp only [encStack, encRight_nil, list_pow_succ, list_pow_zero]
    bb_steps
  exact ((shift_B_cons L e₀ [] 2).trans hturn).trans
    (reaches_drainD (3 :: bumpHeadBy (2 * e₀) L) [] 1)

private theorem step_B_single_three (L : List ℕ) (e₀ : ℕ) :
    (encode (.B L [e₀] 3)) [target]⊢⁺ encode (drainD (bumpHeadBy (2 * e₀) L) [1] 0) := by
  have hturn :
      ((encStack (0 :: bumpHeadBy (2 * e₀) L)) {{A}}> (encRight [] 3)) [target]⊢⁺
        cfgD (2 :: bumpHeadBy (2 * e₀) L) [] 0 := by
    unfold cfgD
    simp only [encStack, encRight_nil, list_pow_succ, list_pow_zero]
    bb_steps
  exact ((shift_B_cons L e₀ [] 3).trans hturn).trans
    (reaches_drainD (2 :: bumpHeadBy (2 * e₀) L) [] 0)

private theorem step_B_single_ge4 (L : List ℕ) (e₀ c : ℕ) :
    (encode (.B L [e₀] (c + 4))) [target]⊢⁺ encode (drainD (bumpHeadBy (2 * e₀) L) [1, 0] c) := by
  have hturn :
      ((encStack (0 :: bumpHeadBy (2 * e₀) L)) {{A}}> (encRight [] (c + 4))) [target]⊢⁺
        cfgD (4 :: bumpHeadBy (2 * e₀) L) [] c := by
    unfold cfgD
    simp only [encStack, encRight_nil]
    have hc : c + 4 + 1 = 4 + (c + 1) := by omega
    rw [hc, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 (c + 1),
      ListBlank.append_pow_succ ([1] : List (Fin 2)) c]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    rw [Cfg.headLeft_cons]
    bb_steps
  exact ((shift_B_cons L e₀ [] (c + 4)).trans hturn).trans
    (reaches_drainD (4 :: bumpHeadBy (2 * e₀) L) [] c)

private theorem step_B_cons_zero (L : List ℕ) (e₀ : ℕ) (E₂ : List ℕ) (c : ℕ) :
    (encode (.B L (e₀ :: 0 :: E₂) c)) [target]⊢⁺
      encode (drainD (bumpHeadBy (2 * e₀) L) (1 :: E₂) c) := by
  have hturn :
      ((encStack (0 :: bumpHeadBy (2 * e₀) L)) {{A}}> (encRight (0 :: E₂) c)) [target]⊢⁺
        cfgD (0 :: bumpHeadBy (2 * e₀) L) (0 :: E₂) c := by
    unfold cfgD
    simp only [encStack, encRight_cons, Nat.mul_zero, list_pow_succ, list_pow_zero]
    bb_steps
  exact ((shift_B_cons L e₀ (0 :: E₂) c).trans hturn).trans
    (reaches_drainD (0 :: bumpHeadBy (2 * e₀) L) (0 :: E₂) c)

private theorem step_B_cons_one (L : List ℕ) (e₀ : ℕ) (E₂ : List ℕ) (c : ℕ) :
    (encode (.B L (e₀ :: 1 :: E₂) c)) [target]⊢⁺
      encode (.B (4 :: bumpHeadBy (2 * e₀) L) E₂ c) := by
  have hturn :
      ((encStack (0 :: bumpHeadBy (2 * e₀) L)) {{A}}> (encRight (1 :: E₂) c)) [target]⊢⁺
        encode (.B (4 :: bumpHeadBy (2 * e₀) L) E₂ c) := by
    simp only [encode, encStack, encRight_cons, list_pow_succ, list_pow_zero]
    bb_steps
  exact (shift_B_cons L e₀ (1 :: E₂) c).trans hturn

private theorem step_B_cons_ge2 (L : List ℕ) (e₀ e₁ : ℕ) (E₂ : List ℕ) (c : ℕ) :
    (encode (.B L (e₀ :: (e₁ + 2) :: E₂) c)) [target]⊢⁺
      encode (drainD (4 :: bumpHeadBy (2 * e₀) L) (e₁ :: E₂) c) := by
  have hturn :
      ((encStack (0 :: bumpHeadBy (2 * e₀) L)) {{A}}> (encRight ((e₁ + 2) :: E₂) c)) [target]⊢⁺
        cfgD (4 :: bumpHeadBy (2 * e₀) L) (e₁ :: E₂) c := by
    unfold cfgD
    simp only [encStack, encRight_cons]
    have he : 2 * (e₁ + 2) + 1 = 4 + (2 * e₁ + 1) := by omega
    rw [he, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 (2 * e₁ + 1),
      ListBlank.append_pow_succ ([1] : List (Fin 2)) (2 * e₁)]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
      ListBlank.append_cons, ListBlank.append_nil]
    rw [Cfg.headLeft_cons]
    bb_steps
  exact ((shift_B_cons L e₀ ((e₁ + 2) :: E₂) c).trans hturn).trans
    (reaches_drainD (4 :: bumpHeadBy (2 * e₀) L) (e₁ :: E₂) c)

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start (fun s => ?_)
  rcases s with ⟨L, E, c⟩
  rcases E with _ | ⟨e₀, _ | ⟨_ | _ | e₁, E₂⟩⟩
  · exact step_B_empty L c
  · rcases c with _ | _ | _ | _ | c
    · exact step_B_single_zero L e₀
    · exact halt_B_single_one L e₀
    · exact step_B_single_two L e₀
    · exact step_B_single_three L e₀
    · exact step_B_single_ge4 L e₀ c
  · exact step_B_cons_zero L e₀ E₂ c
  · exact step_B_cons_one L e₀ E₂ c
  · exact step_B_cons_ge2 L e₀ e₁ E₂ c

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD
