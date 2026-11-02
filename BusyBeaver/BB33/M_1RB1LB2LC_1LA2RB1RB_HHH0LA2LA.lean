/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LB2LC_1LA2RB1RB_---0LA2LA` (Holdout #397)

Formal `IsClosedStackPatternSet`, `HasStackedCollatzReduction`, and `IsValidAcceleration` proofs
for the 3-state, 3-symbol Busy Beaver holdout `1RB1LB2LC_1LA2RB1RB_---0LA2LA` (Holdout #397; see
<https://wiki.bbchallenge.org/wiki/1RB1LB2LC_1LA2RB1RB_---0LA2LA>).

Starting from the blank tape (`init []`), the trajectory reaches the right-bounce family
$$W(w) = 0^\infty\,\overline{w}\,\mathrm{B}{>}\,0^\infty
  \quad (w \in \{\mathtt{false}, \mathtt{true}\}^*, \quad
  \overline{\mathtt{false}} = 2, \; \overline{\mathtt{true}} = 1, \quad \text{listed head-first})$$
at $W([\mathtt{true}]) = 0^\infty\,1\,\mathrm{B}{>}\,0^\infty$ in 1 raw Turing machine step (and
$W([\mathtt{false}, \mathtt{false}, \mathtt{false}, \mathtt{true}]) =
  0^\infty\,1\,2\,2\,2\,\mathrm{B}{>}\,0^\infty$
at step 8). Each full sweep from $W(w)$ runs LegionMammal's 6-carry pass transducer `pass .ca w`
across $w$ from right to left (head-first):
- if `pass .ca w = some w'`, the machine returns in `ReachesPlus` to
  $W(\mathtt{false} :: w')$;
- if `pass .ca w = none` (reaching the left-hand blank tape in carry `.cc` or `.ce`, corresponding
  to Turing state `C` reading `0`), the machine halts (`C0 -> ---`).

## Stacked Collatz-like Acceleration Rules

```text
Configuration family (w listed from tape head to left boundary):
  W(w) = 0^inf rev(enc(w)) B> 0^inf   where enc(false) = 2, enc(true) = 1

6-carry pass transducer pass(carry, w):
  ca, 2 :: zs -> 1 :: pass(cc, zs)        ca, [] -> [1]
  ca, 1 :: zs -> 2 :: pass(cb, zs)
  cb, 2 :: zs -> 1 :: zs                  cb, [] -> [2, 1]
  cb, 1 :: zs -> 2 :: zs
  cc, 2 :: zs -> 1 :: pass(ca, zs)        cc, [] -> Halt (C0)
  cc, 1 :: zs -> 2 :: pass(cd, zs)
  cd, 2 :: zs -> 2 :: pass(ce, zs)        cd, [] -> [2, 2, 1]
  cd, 1 :: zs -> 1 :: pass(cf, zs)
  ce, 2 :: zs -> 2 :: pass(ca, zs)        ce, [] -> Halt (C0)
  ce, 1 :: zs -> 1 :: pass(cd, zs)
  cf, 2 :: zs -> 2 :: pass(cd, zs)        cf, [] -> [1, 2, 2, 1]
  cf, 1 :: zs -> 1 :: pass(ca, zs)

Full sweep map:
  W(w) -> W(2 :: pass(ca, w))

Start: W([1]) at step 1 (orbit: 1 -> 2221 -> 21112221 -> 212111112221 -> ...)
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LB2LC_1LA2RB1RB_HHH0LA2LA

open ThreeState Turing

/-- The `(3, 3)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 3 3 :=
  load_rle_machine% "1RB1LB2LC_1LA2RB1RB_---0LA2LA"

/-- The `(3, 3)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 3) (Fin 3) :=
  machine.toBB

/-! ## Level B: Stacked Collatz-like Acceleration (`State`, `start`, `encode`, `next`) -/

/-- Canonical right-bounce configuration family
$W(w) = 0^\infty\,\overline{w}\,\mathrm{B}{>}\,0^\infty$. -/
inductive State where
  | W (w : List Bool)
  deriving DecidableEq, Repr

/-- Six carry states (`a..f`) of LegionMammal's sweep transducer for
`1RB1LB2LC_1LA2RB1RB_---0LA2LA`. -/
inductive Carry where
  | ca
  | cb
  | cc
  | cd
  | ce
  | cf
  deriving DecidableEq, Repr

/-- Head-to-boundary pass transducer across a boolean cell word (`false` = symbol `2`,
`true` = symbol `1`); returns `none` when carry `.cc` or `.ce` reaches the blank boundary
(`C0 -> ---`). -/
def pass : Carry → List Bool → Option (List Bool)
  | .ca, [] => some [true]
  | .ca, false :: zs => List.cons true <$> pass .cc zs
  | .ca, true :: zs => List.cons false <$> pass .cb zs
  | .cb, [] => some [false, true]
  | .cb, false :: zs => some (true :: zs)
  | .cb, true :: zs => some (false :: zs)
  | .cc, [] => none
  | .cc, false :: zs => List.cons true <$> pass .ca zs
  | .cc, true :: zs => List.cons false <$> pass .cd zs
  | .cd, [] => some [false, false, true]
  | .cd, false :: zs => List.cons false <$> pass .ce zs
  | .cd, true :: zs => List.cons true <$> pass .cf zs
  | .ce, [] => none
  | .ce, false :: zs => List.cons false <$> pass .ca zs
  | .ce, true :: zs => List.cons true <$> pass .cd zs
  | .cf, [] => some [true, false, false, true]
  | .cf, false :: zs => List.cons false <$> pass .cd zs
  | .cf, true :: zs => List.cons true <$> pass .ca zs

/-- Initial accelerated state $W([\mathtt{true}])$, reached from `init []` in 1 step. -/
def start : State := .W [true]

/-- Decode an accelerated `State` into its concrete Turing machine configuration. -/
@[simp]
def encode : State → Cfg (Fin 3) (Fin 3)
  | .W w =>
      Cfg.headRight B (ListBlank.append (w.map fun b => if b then 1 else 2) default) default

/-- One full sweep of the accelerated 6-carry transducer (`none` indicates halting). -/
def next : State → Option State
  | .W w => (fun w' => .W (false :: w')) <$> pass .ca w

/-! ## Private Pass Simulation Proof -/

private def encCells (w : List Bool) : List (Fin 3) :=
  w.map fun b => if b then 1 else 2

private def cfgEnter (q : Fin 3) (cells : List Bool) (r : ListBlank (Fin 3)) :
    Cfg (Fin 3) (Fin 3) :=
  ((default <+ encCells cells) <{{q}} r)

private def cfgExit (cells : List Bool) (r : ListBlank (Fin 3)) :
    Cfg (Fin 3) (Fin 3) :=
  ((default <+ encCells cells) {{B}}> r)

private theorem enter_A_nil (r : ListBlank (Fin 3)) :
    (cfgEnter A [] r) [target]⊢⁺ (cfgExit [true] r) := by
  unfold cfgEnter cfgExit encCells
  bb_steps

private theorem enter_B_nil (r : ListBlank (Fin 3)) :
    (cfgEnter B [] r) [target]⊢⁺ (cfgExit [false, true] r) := by
  unfold cfgEnter cfgExit encCells
  bb_steps

private theorem enter_A_true_nil (r : ListBlank (Fin 3)) :
    (cfgEnter A [true] r) [target]⊢⁺ (cfgExit [false, false, true] r) := by
  unfold cfgEnter cfgExit encCells
  bb_steps

private theorem enter_C_false_true_nil (r : ListBlank (Fin 3)) :
    (cfgEnter C [false, true] r) [target]⊢⁺ (cfgExit [true, false, false, true] r) := by
  unfold cfgEnter cfgExit encCells
  bb_steps

private theorem enter_A_false (zs : List Bool) (r : ListBlank (Fin 3)) :
    (cfgEnter A (false :: zs) r) [target]⊢⁺ (cfgEnter C zs ([2] +> r)) := by
  dsimp only [cfgEnter, encCells, List.map]
  bb_steps

private theorem enter_A_true (zs : List Bool) (r : ListBlank (Fin 3)) :
    (cfgEnter A (true :: zs) r) [target]⊢⁺ (cfgEnter B zs ([1] +> r)) := by
  dsimp only [cfgEnter, encCells, List.map]
  bb_steps

private theorem enter_B_false (zs : List Bool) (r : ListBlank (Fin 3)) :
    (cfgEnter B (false :: zs) r) [target]⊢⁺ (cfgExit (true :: zs) r) := by
  dsimp only [cfgEnter, cfgExit, encCells, List.map]
  bb_steps

private theorem enter_B_true (zs : List Bool) (r : ListBlank (Fin 3)) :
    (cfgEnter B (true :: zs) r) [target]⊢⁺ (cfgExit (false :: zs) r) := by
  dsimp only [cfgEnter, cfgExit, encCells, List.map]
  bb_steps

private theorem enter_C_false (zs : List Bool) (r : ListBlank (Fin 3)) :
    (cfgEnter C (false :: zs) r) [target]⊢⁺ (cfgEnter A zs ([2] +> r)) := by
  dsimp only [cfgEnter, encCells, List.map]
  bb_steps

private theorem enter_C_true (zs : List Bool) (r : ListBlank (Fin 3)) :
    (cfgEnter C (true :: zs) r) [target]⊢⁺ (cfgEnter A zs ([0] +> r)) := by
  dsimp only [cfgEnter, encCells, List.map]
  bb_steps

private theorem exit_zero (zs : List Bool) (r : ListBlank (Fin 3)) :
    (cfgExit zs ([0] +> r)) [target]⊢⁺ (cfgEnter A zs ([1] +> r)) := by
  unfold cfgExit cfgEnter
  bb_steps

private theorem exit_one (zs : List Bool) (r : ListBlank (Fin 3)) :
    (cfgExit zs ([1] +> r)) [target]⊢⁺ (cfgExit (false :: zs) r) := by
  unfold cfgExit encCells
  bb_steps

private theorem exit_two (zs : List Bool) (r : ListBlank (Fin 3)) :
    (cfgExit zs ([2] +> r)) [target]⊢⁺ (cfgExit (true :: zs) r) := by
  unfold cfgExit encCells
  bb_steps

private def SimSpec (q : Carry) (cells outCells : List Bool) : Prop :=
  match q with
  | .ca => ∀ r : ListBlank (Fin 3), (cfgEnter A cells r) [target]⊢⁺ (cfgExit outCells r)
  | .cb => ∀ r : ListBlank (Fin 3), (cfgEnter B cells r) [target]⊢⁺ (cfgExit outCells r)
  | .cc => ∀ r : ListBlank (Fin 3), (cfgEnter C cells r) [target]⊢⁺ (cfgExit outCells r)
  | .cd =>
    ∃ mid : List Bool,
      (∀ r1 : ListBlank (Fin 3), (cfgEnter A cells r1) [target]⊢⁺ (cfgExit mid r1)) ∧
      (∀ r2 : ListBlank (Fin 3), (cfgEnter A mid r2) [target]⊢⁺ (cfgExit outCells r2))
  | .ce =>
    ∃ mid : List Bool,
      (∀ r1 : ListBlank (Fin 3), (cfgEnter C cells r1) [target]⊢⁺ (cfgExit mid r1)) ∧
      (∀ r2 : ListBlank (Fin 3), (cfgEnter B mid r2) [target]⊢⁺ (cfgExit outCells r2))
  | .cf =>
    ∃ mid : List Bool,
      (∀ r1 : ListBlank (Fin 3), (cfgEnter B cells r1) [target]⊢⁺ (cfgExit mid r1)) ∧
      (∀ r2 : ListBlank (Fin 3), (cfgEnter C mid r2) [target]⊢⁺ (cfgExit outCells r2))

private theorem boundary_sim (q : Carry) (outCells : List Bool)
    (hp : pass q [] = some outCells) :
    SimSpec q [] outCells := by
  cases q with
  | ca =>
    injection hp with h; subst h
    exact enter_A_nil
  | cb =>
    injection hp with h; subst h
    exact enter_B_nil
  | cc => cases hp
  | cd =>
    injection hp with h; subst h
    exact ⟨[true], enter_A_nil, enter_A_true_nil⟩
  | ce => cases hp
  | cf =>
    injection hp with h; subst h
    exact ⟨[false, true], enter_B_nil, enter_C_false_true_nil⟩

private theorem cell_step_sim (q : Carry) (z : Bool) (zs outCells : List Bool)
    (ih : ∀ (q' : Carry) (out' : List Bool), pass q' zs = some out' → SimSpec q' zs out')
    (hp : pass q (z :: zs) = some outCells) :
    SimSpec q (z :: zs) outCells := by
  cases q with
  | ca =>
    cases z with
    | false =>
      obtain ⟨zs', hps, rfl⟩ := Option.map_eq_some_iff.mp hp
      have hrec := ih .cc zs' hps
      intro r
      exact ((enter_A_false zs r).trans (hrec ([2] +> r))).trans (exit_two zs' r)
    | true =>
      obtain ⟨zs', hps, rfl⟩ := Option.map_eq_some_iff.mp hp
      have hrec := ih .cb zs' hps
      intro r
      exact ((enter_A_true zs r).trans (hrec ([1] +> r))).trans (exit_one zs' r)
  | cb =>
    cases z with
    | false =>
      injection hp with h; subst h
      exact enter_B_false zs
    | true =>
      injection hp with h; subst h
      exact enter_B_true zs
  | cc =>
    cases z with
    | false =>
      obtain ⟨zs', hps, rfl⟩ := Option.map_eq_some_iff.mp hp
      have hrec := ih .ca zs' hps
      intro r
      exact ((enter_C_false zs r).trans (hrec ([2] +> r))).trans (exit_two zs' r)
    | true =>
      obtain ⟨zs', hps, rfl⟩ := Option.map_eq_some_iff.mp hp
      rcases ih .cd zs' hps with ⟨mid, hrec1, hrec2⟩
      intro r
      have p1 := (enter_C_true zs r).trans (hrec1 ([0] +> r))
      have p2 := (exit_zero mid r).trans (hrec2 ([1] +> r))
      exact (p1.trans p2).trans (exit_one zs' r)
  | cd =>
    cases z with
    | false =>
      obtain ⟨zs', hps, rfl⟩ := Option.map_eq_some_iff.mp hp
      rcases ih .ce zs' hps with ⟨mid, hrec1, hrec2⟩
      refine ⟨true :: mid, fun r1 => ?_, fun r2 => ?_⟩
      · exact ((enter_A_false zs r1).trans (hrec1 ([2] +> r1))).trans (exit_two mid r1)
      · exact ((enter_A_true mid r2).trans (hrec2 ([1] +> r2))).trans (exit_one zs' r2)
    | true =>
      obtain ⟨zs', hps, rfl⟩ := Option.map_eq_some_iff.mp hp
      rcases ih .cf zs' hps with ⟨mid, hrec1, hrec2⟩
      refine ⟨false :: mid, fun r1 => ?_, fun r2 => ?_⟩
      · exact ((enter_A_true zs r1).trans (hrec1 ([1] +> r1))).trans (exit_one mid r1)
      · exact ((enter_A_false mid r2).trans (hrec2 ([2] +> r2))).trans (exit_two zs' r2)
  | ce =>
    cases z with
    | false =>
      obtain ⟨zs', hps, rfl⟩ := Option.map_eq_some_iff.mp hp
      have hrec := ih .ca zs' hps
      refine ⟨true :: zs', fun r1 => ?_, enter_B_true zs'⟩
      exact ((enter_C_false zs r1).trans (hrec ([2] +> r1))).trans (exit_two zs' r1)
    | true =>
      obtain ⟨zs', hps, rfl⟩ := Option.map_eq_some_iff.mp hp
      rcases ih .cd zs' hps with ⟨mid, hrec1, hrec2⟩
      refine ⟨false :: zs', fun r1 => ?_, enter_B_false zs'⟩
      have p1 := (enter_C_true zs r1).trans (hrec1 ([0] +> r1))
      have p2 := (exit_zero mid r1).trans (hrec2 ([1] +> r1))
      exact (p1.trans p2).trans (exit_one zs' r1)
  | cf =>
    cases z with
    | false =>
      obtain ⟨zs', hps, rfl⟩ := Option.map_eq_some_iff.mp hp
      rcases ih .cd zs' hps with ⟨mid, hrec1, hrec2⟩
      refine ⟨true :: zs, enter_B_false zs, fun r2 => ?_⟩
      have p1 := (enter_C_true zs r2).trans (hrec1 ([0] +> r2))
      have p2 := (exit_zero mid r2).trans (hrec2 ([1] +> r2))
      exact (p1.trans p2).trans (exit_one zs' r2)
    | true =>
      obtain ⟨zs', hps, rfl⟩ := Option.map_eq_some_iff.mp hp
      have hrec := ih .ca zs' hps
      refine ⟨false :: zs, enter_B_true zs, fun r2 => ?_⟩
      exact ((enter_C_false zs r2).trans (hrec ([2] +> r2))).trans (exit_two zs' r2)

private theorem pass_sim (q : Carry) (cells outCells : List Bool)
    (hp : pass q cells = some outCells) :
    SimSpec q cells outCells := by
  induction cells generalizing q outCells with
  | nil => exact boundary_sim q outCells hp
  | cons z zs ih => exact cell_step_sim q z zs outCells ih hp

private theorem haltsFrom_of_plus {c₁ c₂ : Cfg (Fin 3) (Fin 3)}
    (h₁ : c₁ [target]⊢⁺ c₂) (h₂ : HaltsFrom target c₂) :
    HaltsFrom target c₁ :=
  HaltsFrom.of_reachesStar h₁.to_star h₂

private theorem halt_C_nil (r : ListBlank (Fin 3)) :
    HaltsFrom target (cfgEnter C [] r) :=
  ⟨cfgEnter C [] r, ReachesStar.refl _ _, by unfold cfgEnter encCells; bb_halt⟩

private def HaltSpec (q : Carry) (cells : List Bool) : Prop :=
  match q with
  | .ca => ∀ r : ListBlank (Fin 3), HaltsFrom target (cfgEnter A cells r)
  | .cb => False
  | .cc => ∀ r : ListBlank (Fin 3), HaltsFrom target (cfgEnter C cells r)
  | .cd =>
    (∀ r1 : ListBlank (Fin 3), HaltsFrom target (cfgEnter A cells r1)) ∨
    (∃ mid : List Bool,
      (∀ r1 : ListBlank (Fin 3), (cfgEnter A cells r1) [target]⊢⁺ (cfgExit mid r1)) ∧
      (∀ r2 : ListBlank (Fin 3), HaltsFrom target (cfgEnter A mid r2)))
  | .ce => ∀ r1 : ListBlank (Fin 3), HaltsFrom target (cfgEnter C cells r1)
  | .cf =>
    ∃ mid : List Bool,
      (∀ r1 : ListBlank (Fin 3), (cfgEnter B cells r1) [target]⊢⁺ (cfgExit mid r1)) ∧
      (∀ r2 : ListBlank (Fin 3), HaltsFrom target (cfgEnter C mid r2))

private theorem halt_sim (q : Carry) (cells : List Bool)
    (hp : pass q cells = none) :
    HaltSpec q cells := by
  induction cells generalizing q with
  | nil =>
    cases q with
    | ca => cases hp
    | cb => cases hp
    | cc => exact halt_C_nil
    | cd => cases hp
    | ce => exact halt_C_nil
    | cf => cases hp
  | cons z zs ih =>
    cases q with
    | ca =>
      cases z with
      | false =>
        have hrec := ih .cc (Option.map_eq_none_iff.mp hp)
        intro r
        exact haltsFrom_of_plus (enter_A_false zs r) (hrec ([2] +> r))
      | true =>
        exact False.elim (ih .cb (Option.map_eq_none_iff.mp hp))
    | cb =>
      cases z <;> cases hp
    | cc =>
      cases z with
      | false =>
        have hrec := ih .ca (Option.map_eq_none_iff.mp hp)
        intro r
        exact haltsFrom_of_plus (enter_C_false zs r) (hrec ([2] +> r))
      | true =>
        rcases ih .cd (Option.map_eq_none_iff.mp hp) with hrec1 | ⟨mid, hrec1, hrec2⟩
        · intro r
          exact haltsFrom_of_plus (enter_C_true zs r) (hrec1 ([0] +> r))
        · intro r
          have p1 := ((enter_C_true zs r).trans (hrec1 ([0] +> r))).trans (exit_zero mid r)
          exact haltsFrom_of_plus p1 (hrec2 ([1] +> r))
    | cd =>
      cases z with
      | false =>
        have hrec := ih .ce (Option.map_eq_none_iff.mp hp)
        refine Or.inl fun r1 => ?_
        exact haltsFrom_of_plus (enter_A_false zs r1) (hrec ([2] +> r1))
      | true =>
        rcases ih .cf (Option.map_eq_none_iff.mp hp) with ⟨mid, hrec1, hrec2⟩
        refine Or.inr ⟨false :: mid, fun r1 => ?_, fun r2 => ?_⟩
        · exact ((enter_A_true zs r1).trans (hrec1 ([1] +> r1))).trans (exit_one mid r1)
        · exact haltsFrom_of_plus (enter_A_false mid r2) (hrec2 ([2] +> r2))
    | ce =>
      cases z with
      | false =>
        have hrec := ih .ca (Option.map_eq_none_iff.mp hp)
        intro r1
        exact haltsFrom_of_plus (enter_C_false zs r1) (hrec ([2] +> r1))
      | true =>
        rcases ih .cd (Option.map_eq_none_iff.mp hp) with hrec1 | ⟨mid, hrec1, hrec2⟩
        · intro r1
          exact haltsFrom_of_plus (enter_C_true zs r1) (hrec1 ([0] +> r1))
        · intro r1
          have p1 := ((enter_C_true zs r1).trans (hrec1 ([0] +> r1))).trans (exit_zero mid r1)
          exact haltsFrom_of_plus p1 (hrec2 ([1] +> r1))
    | cf =>
      cases z with
      | false =>
        refine ⟨true :: zs, enter_B_false zs, ?_⟩
        rcases ih .cd (Option.map_eq_none_iff.mp hp) with hrec1 | ⟨mid, hrec1, hrec2⟩
        · intro r2
          exact haltsFrom_of_plus (enter_C_true zs r2) (hrec1 ([0] +> r2))
        · intro r2
          have p1 := ((enter_C_true zs r2).trans (hrec1 ([0] +> r2))).trans (exit_zero mid r2)
          exact haltsFrom_of_plus p1 (hrec2 ([1] +> r2))
      | true =>
        have hrec := ih .ca (Option.map_eq_none_iff.mp hp)
        refine ⟨false :: zs, enter_B_true zs, fun r2 => ?_⟩
        exact haltsFrom_of_plus (enter_C_false zs r2) (hrec ([2] +> r2))

private theorem bounce_enter (w : List Bool) :
    (encode (.W w)) [target]⊢⁺ (cfgEnter A w ([1] +> default)) := by
  unfold encode cfgEnter encCells
  bb_steps

private theorem init_reaches_start :
    (init []) [target]⊢⁺ (encode start) := by
  unfold start encode
  bb_steps

private theorem step_state_plus (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesPlus target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨w⟩
  dsimp only [next]
  cases hp : pass .ca w with
  | some outCells =>
    change (encode (.W w)) [target]⊢⁺ (cfgExit (false :: outCells) default)
    have hpass := pass_sim .ca w outCells hp ([1] +> default)
    exact ((bounce_enter w).trans hpass).trans (exit_one outCells default)
  | none =>
    change ∃ cfg', ((encode (.W w)) [target]⊢⁺ cfg') ∧ (step target cfg').isNone
    obtain ⟨cfg', hstar, hnone⟩ := halt_sim .ca w hp ([1] +> default)
    exact ⟨cfg', (bounce_enter w).trans_star hstar, hnone⟩

/-- `next` is a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start.to_star (fun s => ?_)
  have hs := step_state_plus s
  rcases hnext : next s with _ | s'
  · rw [hnext] at hs
    obtain ⟨cfg', hplus, hnone⟩ := hs
    exact ⟨cfg', hplus.to_star, hnone⟩
  · rw [hnext] at hs
    exact hs

/-- `target` halts iff the accelerated transition function `next` halts from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## Level A: Closed `StackPatternSet` (`HasStackedCollatzReduction`) -/

/-- Stack pattern for $W(w) = 0^\infty\,\overline{w}\,\mathrm{B}{>}\,0^\infty$. -/
def pat_W : StackPattern (Fin 3) (Fin 3) :=
  { left := [.word [[2], [1]] 0]
    head := some B
    right := [] }

/-- Full `StackPatternSet` for `1RB1LB2LC_1LA2RB1RB_---0LA2LA`. -/
def ps : StackPatternSet (Fin 3) (Fin 3) :=
  [(pat_W, .true)]

private theorem evalStackPattern_pat_W (vars : ℕ → ℕ) (stks : ℕ → List ℕ) :
    evalStackPattern pat_W vars stks =
      Cfg.headRight B (evalStackExpr [.word [[2], [1]] 0] vars stks) default :=
  rfl

private theorem mem_encode (s : State) : IsInStackPatternSet ps (encode s) := by
  rcases s with ⟨w⟩
  obtain ⟨vars, stks, h_expr⟩ :=
    (exists_evalStackExpr_single_word_iff (2 : Fin 3) (1 : Fin 3)
      (ListBlank.append (w.map fun b => if b then 1 else 2) default)).mpr ⟨w, rfl⟩
  refine ⟨(pat_W, .true), List.Mem.head _, vars, stks, ?_, trivial⟩
  rw [evalStackPattern_pat_W, ← h_expr]
  rfl

private theorem encode_of_mem (cfg : Cfg (Fin 3) (Fin 3))
    (h : IsInStackPatternSet ps cfg) : ∃ s : State, cfg = encode s := by
  rcases h with ⟨entry, hentry, vars, stks, rfl, _⟩
  rcases List.mem_singleton.mp hentry with rfl
  obtain ⟨w, hw⟩ :=
    (exists_evalStackExpr_single_word_iff (2 : Fin 3) (1 : Fin 3)
      (evalStackExpr [.word [[2], [1]] 0] vars stks)).mp ⟨vars, stks, rfl⟩
  refine ⟨.W w, ?_⟩
  rw [evalStackPattern_pat_W, hw]
  rfl

/-- `ps` is a closed stacked pattern set for `target`. -/
theorem is_closed_stack_pattern_set : IsClosedStackPatternSet target ps := by
  refine is_valid_acceleration.isClosedStackPatternSet mem_encode encode_of_mem (fun s hnext => ?_)
  have hs := step_state_plus s
  rw [hnext] at hs
  exact hs

/-- `target` has a stacked Collatz-like reduction via `ps`. -/
theorem has_stacked_collatz_reduction : HasStackedCollatzReduction target :=
  ⟨ps, is_closed_stack_pattern_set⟩

end BusyBeaver.M_1RB1LB2LC_1LA2RB1RB_HHH0LA2LA
