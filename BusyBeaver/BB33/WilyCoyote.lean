/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Shared Wily Coyote Reduction Engine (`BusyBeaver/BB33/WilyCoyote.lean`)

Shared stacked Collatz-like acceleration (`State`, `WilyMode`, `wilyPass`, `start`, `encode`,
`next`, `pat_W`, `ps`) and generic closure proof (`StepSpec`) for the two 3-state, 3-symbol
**Wily Coyote** holdout machines (Holdouts #531 and #532):
- `1RB2LA1LA_2LA0RA2RC_---0LC2RA` (Holdout #531)
- `1RB2LA1LA_2LA0RA2RC_---1RB2RA` (Holdout #532)

The two machines agree on 7 of the 8 defined transitions and differ only on `(C, 1)` (`0LC` vs.
`1RB`). Along every pass from $W(w) = 0^\infty\,\mathrm{A}{>}\,0\,\overline{w}\,0^\infty$, state
`C` is only entered in mode `.s1` (`(l <+ [2]) {{C}}> r`), where symbol `2` is immediately to the
left of the tape head; consequently `C1 -> 0LC -> C2 -> 2RA -> A0 -> 1RB` (`3` raw steps) and
`C1 -> 1RB` (`1` raw step) both satisfy the same `ReachesPlus` step `enter_s1_true`.
-/

@[expose] public section

namespace BusyBeaver.WilyCoyote

open ThreeState Turing

/-! ## Level B: Stacked Collatz-like Acceleration (`State`, `start`, `encode`, `next`) -/

/-- Canonical left-bounce configuration family
$W(w) = 0^\infty\,\mathrm{A}{>}\,0\,\overline{w}\,0^\infty$. -/
inductive State where
  | W (w : List Bool)
  deriving DecidableEq, Repr

/-- Carry/pass modes of Racheline's left-to-right sweep transducer for Wily Coyote. -/
inductive WilyMode where
  | s0
  | s1
  | s2
  | s3
  deriving DecidableEq, Repr

/-- Left-to-right pass transducer across a boolean cell word (`false` = symbol `2`,
`true` = symbol `1`); returns `none` when mode `.s1` reaches the blank boundary (`C0 -> ---`). -/
def wilyPass : WilyMode → List Bool → Option (List Bool)
  | .s0, [] => some [false]
  | .s0, false :: xs => List.cons true <$> wilyPass .s1 xs
  | .s0, true :: xs => List.cons false <$> wilyPass .s2 xs
  | .s1, [] => none
  | .s1, false :: xs => List.cons true <$> wilyPass .s3 xs
  | .s1, true :: xs => List.cons false <$> wilyPass .s0 xs
  | .s2, [] => some [true, true, false, false]
  | .s2, false :: xs => List.cons false <$> wilyPass .s2 xs
  | .s2, true :: xs => List.cons true <$> wilyPass .s1 xs
  | .s3, [] => some [false, false]
  | .s3, b :: xs => some ((!b) :: xs)

/-- Initial accelerated state $W([\mathtt{false}, \mathtt{false}])$, reached from `init []` in 3
steps. -/
def start : State := .W [false, false]

/-- Decode an accelerated `State` into its concrete Turing machine configuration. -/
@[simp]
def encode : State → Cfg (Fin 3) (Fin 3)
  | .W w =>
      Cfg.headRight A default
        (ListBlank.cons 0 (ListBlank.append (w.map fun b => if b then 1 else 2) default))

/-- One full sweep of the accelerated Wily Coyote transducer (`none` indicates halting). -/
def next : State → Option State
  | .W w => (fun w' => .W (false :: w')) <$> wilyPass .s0 w

/-! ## Level A: Closed `StackPatternSet` (`pat_W`, `ps`) -/

/-- Stack pattern for $W(w) = 0^\infty\,\mathrm{A}{>}\,0\,\overline{w}\,0^\infty$. -/
def pat_W : StackPattern (Fin 3) (Fin 3) :=
  { left := []
    head := some A
    right := [.sym 0, .word [[2], [1]] 0] }

/-- Full `StackPatternSet` for the Wily Coyote holdout pair. -/
def ps : StackPatternSet (Fin 3) (Fin 3) :=
  [(pat_W, .true)]

/-! ## Parametric Pass Simulation (`StepSpec`) -/

/-- Map a boolean word `w` into tape cells (`true ↦ 1`, `false ↦ 2`). -/
def encCells (w : List Bool) : List (Fin 3) :=
  w.map fun b => if b then 1 else 2

/-- Intermediate tape configuration at mode `m` with left half-tape `l` and right half-tape `r`. -/
def modeCfg : WilyMode → ListBlank (Fin 3) → ListBlank (Fin 3) → Cfg (Fin 3) (Fin 3)
  | .s0, l, r => l {{B}}> r
  | .s1, l, r => (l <+ [2]) {{C}}> r
  | .s2, l, r => (l <+ [0]) {{A}}> r
  | .s3, l, r => l {{A}}> r

/-- Left half-tape upon returning in state `<A` from mode `m`. -/
def exitLeft : WilyMode → ListBlank (Fin 3) → ListBlank (Fin 3)
  | .s0, l => l
  | .s1, l => l <+ [2]
  | .s2, l => l <+ [1]
  | .s3, l => l

/-- Bundle of concrete multi-step obligations shared by both Wily Coyote machines. -/
structure StepSpec (M : Machine (Fin 3) (Fin 3)) : Prop where
  /-- Blank tape reaches `encode start` in at least one step. -/
  init_reaches : ReachesPlus M (init []) (encode start)
  /-- Left-boundary bounce entering mode `.s0`. -/
  enter_pass (w : List Bool) :
    (encode (.W w)) [M]⊢⁺ (modeCfg .s0 (default <+ [1]) (encCells w +> default))
  /-- Left-boundary completion returning to `encode (.W (false :: out))`. -/
  exit_pass (out : List Bool) :
    ((default <+ [1]) <{{A}} (encCells out +> default)) [M]⊢⁺ (encode (.W (false :: out)))
  /-- Leftward `<A` sweep across symbol `1` (flips `1 ↦ 2`). -/
  pop_A_false (l r : ListBlank (Fin 3)) :
    ((l <+ [1]) <{{A}} r) [M]⊢⁺ (l <{{A}} (([2] : List (Fin 3)) +> r))
  /-- Leftward `<A` sweep across symbol `2` (flips `2 ↦ 1`). -/
  pop_A_true (l r : ListBlank (Fin 3)) :
    ((l <+ [2]) <{{A}} r) [M]⊢⁺ (l <{{A}} (([1] : List (Fin 3)) +> r))
  /-- Right boundary in mode `.s0`. -/
  bound_s0 (l : ListBlank (Fin 3)) :
    (modeCfg .s0 l default) [M]⊢⁺ (exitLeft .s0 l <{{A}} (encCells [false] +> default))
  /-- Right boundary in mode `.s1` halts immediately (`C0 -> ---`). -/
  bound_s1_halt (l : ListBlank (Fin 3)) :
    (step M (modeCfg .s1 l default)).isNone
  /-- Right boundary in mode `.s2`. -/
  bound_s2 (l : ListBlank (Fin 3)) :
    (modeCfg .s2 l default) [M]⊢⁺
      (exitLeft .s2 l <{{A}} (encCells [true, true, false, false] +> default))
  /-- Right boundary in mode `.s3` on `[]`. -/
  bound_s3_nil (l : ListBlank (Fin 3)) :
    (modeCfg .s3 l default) [M]⊢⁺
      (exitLeft .s3 l <{{A}} (encCells [false, false] +> default))
  /-- Early exit in mode `.s3` on `b :: xs`. -/
  bound_s3_cons (b : Bool) (l : ListBlank (Fin 3)) (xs : List Bool) :
    (modeCfg .s3 l (encCells (b :: xs) +> default)) [M]⊢⁺
      (exitLeft .s3 l <{{A}} (encCells ((!b) :: xs) +> default))
  /-- Mode `.s0` reading `2` (`false`). -/
  enter_s0_false (l r : ListBlank (Fin 3)) :
    (modeCfg .s0 l (([2] : List (Fin 3)) +> r)) [M]⊢⁺ (modeCfg .s1 l r)
  /-- Mode `.s0` reading `1` (`true`). -/
  enter_s0_true (l r : ListBlank (Fin 3)) :
    (modeCfg .s0 l (([1] : List (Fin 3)) +> r)) [M]⊢⁺ (modeCfg .s2 l r)
  /-- Mode `.s1` reading `2` (`false`). -/
  enter_s1_false (l r : ListBlank (Fin 3)) :
    (modeCfg .s1 l (([2] : List (Fin 3)) +> r)) [M]⊢⁺ (modeCfg .s3 ((l <+ [2]) <+ [2]) r)
  /-- Mode `.s1` reading `1` (`true`): takes 3 raw steps on `---0LC2RA` and 1 on `---1RB2RA`. -/
  enter_s1_true (l r : ListBlank (Fin 3)) :
    (modeCfg .s1 l (([1] : List (Fin 3)) +> r)) [M]⊢⁺ (modeCfg .s0 ((l <+ [2]) <+ [1]) r)
  /-- Mode `.s2` reading `2` (`false`). -/
  enter_s2_false (l r : ListBlank (Fin 3)) :
    (modeCfg .s2 l (([2] : List (Fin 3)) +> r)) [M]⊢⁺ (modeCfg .s2 (l <+ [1]) r)
  /-- Mode `.s2` reading `1` (`true`). -/
  enter_s2_true (l r : ListBlank (Fin 3)) :
    (modeCfg .s2 l (([1] : List (Fin 3)) +> r)) [M]⊢⁺ (modeCfg .s1 (l <+ [1]) r)

/-- Discharge all 16 concrete step obligations of `StepSpec` for a Wily Coyote machine. -/
macro "prove_wily_step_spec" : tactic =>
  `(tactic| (
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [start, encode]; bb_steps
    · intro w; dsimp only [encode, modeCfg, encCells]; bb_steps
    · intro out; dsimp only [encode, encCells]; bb_steps
    · intro l r; bb_steps
    · intro l r; bb_steps
    · intro l; dsimp only [modeCfg, exitLeft, encCells]; bb_steps
    · intro l; dsimp only [modeCfg]; bb_halt
    · intro l; dsimp only [modeCfg, exitLeft, encCells]; bb_steps
    · intro l; dsimp only [modeCfg, exitLeft, encCells]; bb_steps
    · intro b l xs
      cases b <;>
        (dsimp only [modeCfg, exitLeft, encCells, List.map, Bool.not_false, Bool.not_true]
         bb_steps)
    · intro l r; dsimp only [modeCfg]; bb_steps
    · intro l r; dsimp only [modeCfg]; bb_steps
    · intro l r; dsimp only [modeCfg]; bb_steps
    · intro l r; dsimp only [modeCfg]; bb_steps
    · intro l r; dsimp only [modeCfg]; bb_steps
    · intro l r; dsimp only [modeCfg]; bb_steps))

private theorem wilyPass_reachesPlus {M : Machine (Fin 3) (Fin 3)} (hs : StepSpec M)
    (m : WilyMode) (l : ListBlank (Fin 3)) (w out : List Bool)
    (h : wilyPass m w = some out) :
    (modeCfg m l (encCells w +> default)) [M]⊢⁺
      (exitLeft m l <{{A}} (encCells out +> default)) := by
  induction w generalizing m l out with
  | nil =>
    cases m with
    | s0 =>
      injection h with h'
      subst h'
      exact hs.bound_s0 l
    | s1 => cases h
    | s2 =>
      injection h with h'
      subst h'
      exact hs.bound_s2 l
    | s3 =>
      injection h with h'
      subst h'
      exact hs.bound_s3_nil l
  | cons b xs ih =>
    cases m with
    | s0 =>
      cases b with
      | false =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s1 xs with
        | none => rw [hp] at h; cases h
        | some ys =>
          rw [hp] at h
          injection h with h'
          subst h'
          exact ((hs.enter_s0_false l _).trans (ih .s1 l ys hp)).trans (hs.pop_A_true l _)
      | true =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s2 xs with
        | none => rw [hp] at h; cases h
        | some ys =>
          rw [hp] at h
          injection h with h'
          subst h'
          exact ((hs.enter_s0_true l _).trans (ih .s2 l ys hp)).trans (hs.pop_A_false l _)
    | s1 =>
      cases b with
      | false =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s3 xs with
        | none => rw [hp] at h; cases h
        | some ys =>
          rw [hp] at h
          injection h with h'
          subst h'
          exact ((hs.enter_s1_false l _).trans
            (ih .s3 ((l <+ [2]) <+ [2]) ys hp)).trans (hs.pop_A_true (l <+ [2]) _)
      | true =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s0 xs with
        | none => rw [hp] at h; cases h
        | some ys =>
          rw [hp] at h
          injection h with h'
          subst h'
          exact ((hs.enter_s1_true l _).trans
            (ih .s0 ((l <+ [2]) <+ [1]) ys hp)).trans (hs.pop_A_false (l <+ [2]) _)
    | s2 =>
      cases b with
      | false =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s2 xs with
        | none => rw [hp] at h; cases h
        | some ys =>
          rw [hp] at h
          injection h with h'
          subst h'
          exact ((hs.enter_s2_false l _).trans
            (ih .s2 (l <+ [1]) ys hp)).trans (hs.pop_A_false (l <+ [1]) _)
      | true =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s1 xs with
        | none => rw [hp] at h; cases h
        | some ys =>
          rw [hp] at h
          injection h with h'
          subst h'
          exact ((hs.enter_s2_true l _).trans
            (ih .s1 (l <+ [1]) ys hp)).trans (hs.pop_A_true (l <+ [1]) _)
    | s3 =>
      dsimp only [wilyPass] at h
      injection h with h'
      subst h'
      exact hs.bound_s3_cons b l xs

private theorem wilyPass_halts {M : Machine (Fin 3) (Fin 3)} (hs : StepSpec M)
    (m : WilyMode) (l : ListBlank (Fin 3)) (w : List Bool)
    (h : wilyPass m w = none) :
    ∃ cfg', ((modeCfg m l (encCells w +> default)) [M]⊢* cfg') ∧
      (step M cfg').isNone := by
  induction w generalizing m l with
  | nil =>
    cases m with
    | s0 => cases h
    | s1 => exact ⟨modeCfg .s1 l default, ReachesStar.refl _ _, hs.bound_s1_halt l⟩
    | s2 => cases h
    | s3 => cases h
  | cons b xs ih =>
    cases m with
    | s0 =>
      cases b with
      | false =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s1 xs with
        | some ys => rw [hp] at h; cases h
        | none =>
          obtain ⟨cfg', hreach, hnone⟩ := ih .s1 l hp
          exact ⟨cfg', (hs.enter_s0_false l _).to_star.trans hreach, hnone⟩
      | true =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s2 xs with
        | some ys => rw [hp] at h; cases h
        | none =>
          obtain ⟨cfg', hreach, hnone⟩ := ih .s2 l hp
          exact ⟨cfg', (hs.enter_s0_true l _).to_star.trans hreach, hnone⟩
    | s1 =>
      cases b with
      | false =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s3 xs with
        | some ys => rw [hp] at h; cases h
        | none =>
          obtain ⟨cfg', hreach, hnone⟩ := ih .s3 ((l <+ [2]) <+ [2]) hp
          exact ⟨cfg', (hs.enter_s1_false l _).to_star.trans hreach, hnone⟩
      | true =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s0 xs with
        | some ys => rw [hp] at h; cases h
        | none =>
          obtain ⟨cfg', hreach, hnone⟩ := ih .s0 ((l <+ [2]) <+ [1]) hp
          exact ⟨cfg', (hs.enter_s1_true l _).to_star.trans hreach, hnone⟩
    | s2 =>
      cases b with
      | false =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s2 xs with
        | some ys => rw [hp] at h; cases h
        | none =>
          obtain ⟨cfg', hreach, hnone⟩ := ih .s2 (l <+ [1]) hp
          exact ⟨cfg', (hs.enter_s2_false l _).to_star.trans hreach, hnone⟩
      | true =>
        dsimp only [wilyPass] at h
        cases hp : wilyPass .s1 xs with
        | some ys => rw [hp] at h; cases h
        | none =>
          obtain ⟨cfg', hreach, hnone⟩ := ih .s1 (l <+ [1]) hp
          exact ⟨cfg', (hs.enter_s2_true l _).to_star.trans hreach, hnone⟩
    | s3 => cases h

private theorem step_state_plus {M : Machine (Fin 3) (Fin 3)} (hs : StepSpec M) (s : State) :
    match next s with
    | some s' => ReachesPlus M (encode s) (encode s')
    | none => ∃ cfg', ReachesPlus M (encode s) cfg' ∧ (step M cfg').isNone := by
  rcases s with ⟨w⟩
  dsimp only [next]
  cases hp : wilyPass .s0 w with
  | some out =>
    exact ((hs.enter_pass w).trans (wilyPass_reachesPlus hs .s0 (default <+ [1]) w out hp)).trans
      (hs.exit_pass out)
  | none =>
    obtain ⟨cfg', hreach, hnone⟩ := wilyPass_halts hs .s0 (default <+ [1]) w hp
    exact ⟨cfg', (hs.enter_pass w).trans_star hreach, hnone⟩

/-- Any machine `M` satisfying `StepSpec M` has `IsValidAcceleration M start encode next`. -/
theorem StepSpec.is_valid_acceleration {M : Machine (Fin 3) (Fin 3)} (hs : StepSpec M) :
    IsValidAcceleration M start encode next := by
  refine IsValidAcceleration.of_step hs.init_reaches.to_star (fun s => ?_)
  have hstep := step_state_plus hs s
  rcases hnext : next s with _ | s'
  · rw [hnext] at hstep
    obtain ⟨cfg', hplus, hnone⟩ := hstep
    exact ⟨cfg', hplus.to_star, hnone⟩
  · rw [hnext] at hstep
    exact hstep

private theorem evalStackPattern_pat_W (vars : ℕ → ℕ) (stks : ℕ → List ℕ) :
    evalStackPattern pat_W vars stks =
      Cfg.headRight A default (ListBlank.cons 0 (evalStackExpr [.word [[2], [1]] 0] vars stks)) :=
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

/-- Any machine `M` satisfying `StepSpec M` has `IsClosedStackPatternSet M ps`. -/
theorem StepSpec.is_closed_stack_pattern_set {M : Machine (Fin 3) (Fin 3)} (hs : StepSpec M) :
    IsClosedStackPatternSet M ps := by
  refine hs.is_valid_acceleration.isClosedStackPatternSet mem_encode encode_of_mem
    (fun s hnext => ?_)
  have hstep := step_state_plus hs s
  rw [hnext] at hstep
  exact hstep

end BusyBeaver.WilyCoyote
