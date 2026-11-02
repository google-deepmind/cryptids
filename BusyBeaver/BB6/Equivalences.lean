/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
public import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC

/-!
# Halting Equivalences between `BB(6)` Holdouts

Machine-level halting equivalences between `BB(6)` holdouts whose certified high-level
Collatz-like accelerations coincide. Each equivalence is a theorem about the two raw Turing
machines (`IsHalt`), obtained by transporting `CollatzHalts` between the two accelerated systems.

## `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC` and `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`

The two transition tables (`#568` and `#623` of the 2026-10-24 holdout list, see
`BusyBeaver.BB6.Hardness`) differ only in the `F1` transition (`1LC` versus `0LA`), and the
`bbchallenge` community merged the first machine into the holdout class of the second (busycoq
[`Eqv_RegularPairs.v`](https://github.com/ccz181078/busycoq/blob/BB6/verify/Eqv_RegularPairs.v)).
The two modules prove, independently of each other, that each machine halts from the blank tape
if and only if its high-level acceleration `highLevelNext` halts from `highLevelStart`
(`isHalt_iff_highLevel_acceleration`), on the $b = 0$ Poincaré section

$$
D(a, d) := 0^\infty \ \mathrm{D}{>} \ (10)^{a+1} \ 0 \ 1^d \ 0^\infty,
$$

and the two accelerated systems (`HighLevelState`, `highLevelStart` $= D(0, 7)$, `evalA`,
`drainB`, `highLevelNext`) are given by literally the same equations on the counters $(a, d)$.
The theorem `isHalt_HHH1LC_iff_HHH0LA` proves that the two copies of `evalA`, `drainB` and
`highLevelNext` agree along the identity of counters $D(a, d) \mapsto D(a, d)$ between the two
state types, transports `CollatzHalts` along it, and combines the two halting equivalences:

$$
\mathrm{IsHalt}(\texttt{---1LC}) \iff \mathrm{CollatzHalts}(T_{\mathrm{HL}}, D(0, 7)) \iff
\mathrm{IsHalt}(\texttt{---0LA}).
$$
-/

@[expose] public section

namespace BusyBeaver.BB6

/-- Iterating `Option.bind` commutes with `Option.map e` when `e` intertwines the two transition
functions. -/
private theorem iterate_bind_map {S T : Type*} {e : S → T} {next : S → Option S}
    {next' : T → Option T} (h : ∀ s, next' (e s) = (next s).map e) (n : ℕ) (o : Option S) :
    (Option.bind · next')^[n] (o.map e) = ((Option.bind · next)^[n] o).map e := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
    have hstep : (o.map e).bind next' = (o.bind next).map e := by
      cases o with
      | none => rfl
      | some s => exact h s
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hstep, ih]

/-- `CollatzHalts` is transported along any map `e` that intertwines the two transition functions
(no injectivity is needed). -/
private theorem collatzHalts_iff_map {S T : Type*} {e : S → T} {next : S → Option S}
    {next' : T → Option T} (h : ∀ s, next' (e s) = (next s).map e) (s : S) :
    CollatzHalts next s ↔ CollatzHalts next' (e s) := by
  unfold CollatzHalts
  refine exists_congr fun n => ?_
  rw [show some (e s) = (some s).map e from rfl, iterate_bind_map h, Option.isNone_map]

/-- The identity of counters $D(a, d) \mapsto D(a, d)$ between the two high-level state spaces. -/
private def embed : M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.HighLevelState →
    M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.HighLevelState
  | .D a d => .D a d

/-- The two copies of `evalA` agree. -/
private theorem evalA_eq (a : ℕ) : ∀ k m : ℕ,
    M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.evalA a k m =
      M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.evalA a k m := by
  induction a with
  | zero =>
    intro k m
    rw [M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.evalA,
      M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.evalA]
    simp only [↓reduceIte]
  | succ a ih =>
    intro k m
    rw [M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.evalA,
      M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.evalA]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel, ih]

/-- The two copies of `drainB` agree, up to `embed`. -/
private theorem drainB_eq (b : ℕ) : ∀ a d : ℕ,
    M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.drainB a b d =
      (M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.drainB a b d).map embed := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro a d
    rw [M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.drainB,
      M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.drainB, ← evalA_eq]
    split_ifs
    · rfl
    · cases M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.evalA a (b - 1) (d + 2 * b + 3) with
      | none => rfl
      | some p =>
        simp only [Option.bind_some]
        split_ifs with hlt
        · exact ih p.2.1 hlt p.1 p.2.2
        · rfl

/-- The two copies of `highLevelNext` agree, up to `embed`. -/
private theorem highLevelNext_embed
    (s : M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.HighLevelState) :
    M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.highLevelNext (embed s) =
      (M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.highLevelNext s).map embed := by
  obtain ⟨a, d⟩ := s
  dsimp only [embed, M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.highLevelNext,
    M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.highLevelNext]
  split_ifs
  · exact drainB_eq _ _ _
  · rfl
  · exact drainB_eq _ _ _
  · exact drainB_eq _ _ _
  · rfl
  · exact drainB_eq _ _ _
  · exact drainB_eq _ _ _
  · rw [← evalA_eq]
    cases M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.evalA (d + 1 - a) a (2 * a + 5) with
    | none => rfl
    | some p => exact drainB_eq _ _ _

/-- `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC` halts from the blank tape if and only if
`1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA` does: both are equivalent to the halting of the same
high-level Collatz-like acceleration `highLevelNext` from $D(0, 7)$. -/
theorem isHalt_HHH1LC_iff_HHH0LA :
    IsHalt M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.target ↔
      IsHalt M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.target := by
  rw [M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.isHalt_iff_highLevel_acceleration,
    M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.isHalt_iff_highLevel_acceleration]
  exact collatzHalts_iff_map highLevelNext_embed _

end BusyBeaver.BB6
