# Busy Beaver (3, 3) Holdouts (`BusyBeaver/BB33/`)

This directory contains formal Lean 4 specifications and kernel-verified Collatz-like and stacked Collatz-like reductions (`is_closed_pattern_set`, `has_collatz_reduction` or `is_closed_stack_pattern_set`, `has_stacked_collatz_reduction`, together with `is_valid_acceleration` and `isHalt_iff_acceleration`) for all 6 remaining unsolved [3-state 3-symbol Busy Beaver (`BB(3, 3)`)](https://wiki.bbchallenge.org/wiki/BB(3,3)) holdout Turing machines, spanning 4 distinct dynamical equivalence classes.

## Formalized `BB(3, 3)` Holdout Machines

| Machine (`bbchallenge` RLE) | States | Symbols | Proved Properties | Wiki / Notes | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `1RB0LB0RC_2LC2LA1RA_1RA1LC---` | `3` | `3` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LB0RC_2LC2LA1RA_1RA1LC---) (Holdout #153, conjugate of holdout #758; shares exact 2-counter map `next` with `1RB2LC1RC_2LC---2RB_2LA0LB0RA`) | [`M_1RB0LB0RC_2LC2LA1RA_1RA1LCHHH.lean`](./M_1RB0LB0RC_2LC2LA1RA_1RA1LCHHH.lean) |
| `1RB1LB2LC_1LA2RB1RB_---0LA2LA` | `3` | `3` | `IsClosedStackPatternSet`, `HasStackedCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LB2LC_1LA2RB1RB_---0LA2LA) (Holdout #397; 6-carry pass transducer discovered by `@LegionMammal978`, similar to Wily Coyote) | [`M_1RB1LB2LC_1LA2RB1RB_HHH0LA2LA.lean`](./M_1RB1LB2LC_1LA2RB1RB_HHH0LA2LA.lean) |
| `1RB2LA1LA_2LA0RA2RC_---0LC2RA` | `3` | `3` | `IsClosedStackPatternSet`, `HasStackedCollatzReduction`, `IsValidAcceleration` | [Wiki (`Wily Coyote`)](https://wiki.bbchallenge.org/wiki/Wily_Coyote) (*Wily Coyote* / Holdout #531; 4-mode pass transducer discovered by Racheline) | [`M_1RB2LA1LA_2LA0RA2RC_HHH0LC2RA.lean`](./M_1RB2LA1LA_2LA0RA2RC_HHH0LC2RA.lean) |
| `1RB2LA1LA_2LA0RA2RC_---1RB2RA` | `3` | `3` | `IsClosedStackPatternSet`, `HasStackedCollatzReduction`, `IsValidAcceleration` | [Wiki (`Wily Coyote`)](https://wiki.bbchallenge.org/wiki/Wily_Coyote) (*Wily Coyote* twin / Holdout #532; identical macro-step `W(w)` trajectory to holdout #531) | [`M_1RB2LA1LA_2LA0RA2RC_HHH1RB2RA.lean`](./M_1RB2LA1LA_2LA0RA2RC_HHH1RB2RA.lean) |
| `1RB2LC1RC_2LC---2RB_2LA0LB0RA` | `3` | `3` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB2LC1RC_2LC---2RB_2LA0LB0RA) (Holdout #758, probvious champion / halter; 2-counter contraction of `@dyuan01` & `@LegionMammal978`'s rules) | [`M_1RB2LC1RC_2LCHHH2RB_2LA0LB0RA.lean`](./M_1RB2LC1RC_2LCHHH2RB_2LA0LB0RA.lean) |
| `1RB2RA1LC_2LC1RB2RB_---2LA1LA` | `3` | `3` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki (`Bigfoot`)](https://wiki.bbchallenge.org/wiki/Bigfoot), [Shawn Ligocki (2023)](https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html) (*Bigfoot* / Holdout #829; 7-rule mod-6 map discovered by Ligocki & `@savask`) | [`M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA.lean`](./M_1RB2RA1LC_2LC1RB2RB_HHH2LA1LA.lean) |

## Summary of Certified Reductions

### 1. *Bigfoot* (`1RB2RA1LC_2LC1RB2RB_---2LA1LA`, Holdout #829) — Base-6 Collatz Cryptid
Discovered and analyzed by Shawn Ligocki and `@savask` in October 2023 ([*BB(3, 3) is Hard*](https://www.sligocki.com/2023/10/16/bb-3-3-is-hard.html); [Wiki](https://wiki.bbchallenge.org/wiki/Bigfoot)).
- **Closed Pattern Family (`ps`)**: `A(a, b, c) := 0^∞ (12)^a 1^(2b+2) <A 1^(2c+4) 0^∞` for `a, b, c : ℕ` (related to the Wiki's `A_Wiki(a, b', c') = 0^∞ (12)^a (11)^b' <A (11)^c' 0^∞` with `b' ≥ 1, c' ≥ 2` by `b' = b + 1, c' = c + 2`).
- **Entry**: Reached from the blank tape in 69 steps at `start = .A 2 0 0` (`A_Wiki(2, 1, 2)`).
- **Certified Acceleration (`next`)**: The exact 7-rule mod-6 piecewise-affine map on `(a, b, c)` from Ligocki & `@savask`'s analysis, halting (`none`) if and only if `b ≡ 1 (mod 6)` and `a = 0`.

### 2. Holdout #758 / #153 Pair (`1RB2LC1RC_2LC---2RB_2LA0LB0RA` and `1RB0LB0RC_2LC2LA1RA_1RA1LC---`) — 2-Counter Contraction (Probvious Champion / Halter)
Analyzed by `@dyuan01` (11-rule 3-counter map) and `@LegionMammal978` (10-rule 2-counter map on `A(a, c)`) on the `bbchallenge` Discord and [Wiki: `1RB2LC1RC_2LC---2RB_2LA0LB0RA`](https://wiki.bbchallenge.org/wiki/1RB2LC1RC_2LC---2RB_2LA0LB0RA).
- **Closed Pattern Families (`ps`)**:
  - For `1RB2LC1RC_2LC---2RB_2LA0LB0RA` (Holdout #758): `A(a, c) := 0^∞ 1 2^a <C (20)^c 0^∞` (entered at `start = .A 0 1` in 2 steps).
  - For `1RB0LB0RC_2LC2LA1RA_1RA1LC---` (Holdout #153): `A(a, c) := 0^∞ (01)^c A> 1^a 2 0^∞` (entered at `start = .A 1 1` in 4 steps), obtained via state/symbol/direction conjugation (`A ↔ C`, `1 ↔ 2`, `L ↔ R`).
- **Certified Acceleration (`next`)**: Both machines share `@LegionMammal978`'s exact 10-rule 2-counter transition function `next` on `State.A (a c : ℕ)`, which contracts `@dyuan01`'s 3-counter rules into a single map on `ℕ²` halting (`none`) only when `a ≤ c` with `a, c` both even, when `a = c + 1` with `c` odd, or when `a = c + 3` with `c ≡ 3 (mod 4)`.

### 3. *Wily Coyote* Pair (`1RB2LA1LA_2LA0RA2RC_---0LC2RA` and `1RB2LA1LA_2LA0RA2RC_---1RB2RA`, Holdouts #531 & #532) — 4-Mode Stacked Transducer
Analyzed by Racheline on [Wiki: Wily Coyote](https://wiki.bbchallenge.org/wiki/Wily_Coyote). The two machines differ only on the `(C, 1)` transition (`0LC` vs. `1RB`): because `(C, 1)` is always entered with `2` immediately to the left of the tape head, `C1 → 0LC → C2 → 2RA → A0 → 1RB` (`3` raw steps) has the exact same net effect as `C1 → 1RB` (`1` raw step), yielding identical macro-step `W(w)` trajectories.
- **Closed Stacked Pattern Family (`ps`)**: `0^∞ A> 0 w 0^∞` for an arbitrary finite word `w ∈ {1, 2}*` (represented by a `StackPattern` with `.word [[2], [1]] 0`).
- **Entry**: Reached from the blank tape in 3 steps at `start = .W [false, false]` (`w = 22`).
- **Certified Acceleration (`next`)**: Racheline's 4-mode left-to-right sweep transducer (`s0..s3`) with boundary extensions (`s0 ↦ 2`, `s1 ↦ HALT`, `s2 ↦ 1122`, `s3 ↦ 22`), prepending `2` (`false`) at the left boundary on each pass.

### 4. Holdout #397 (`1RB1LB2LC_1LA2RB1RB_---0LA2LA`) — 6-Carry Stacked Transducer
Analyzed by `@LegionMammal978` on [Wiki: `1RB1LB2LC_1LA2RB1RB_---0LA2LA`](https://wiki.bbchallenge.org/wiki/1RB1LB2LC_1LA2RB1RB_---0LA2LA).
- **Closed Stacked Pattern Family (`ps`)**: `0^∞ w^R B> 0 0^∞` for a head-facing word `w ∈ {1, 2}*` (represented by a `StackPattern` with `.word [[2], [1]] 0`).
- **Entry**: Reached from the blank tape in 1 step at `start = .W [true]` (`w = 1`, which steps on the first pass to `.W [false, false, false, true]`, i.e. `w = 2221`, at step 8).
- **Certified Acceleration (`next`)**: `@LegionMammal978`'s 6-carry sweep transducer (`ca..cf`, with early exit on `(cb, 2)` and `(cb, 1)` and boundary rules `ca ↦ 1`, `cb ↦ 21`, `cc ↦ HALT`, `cd ↦ 221`, `ce ↦ HALT`, `cf ↦ 1221`), prepending `2` (`false`) at the head boundary after each sweep.
