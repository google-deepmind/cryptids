# 15-state Weak Collatz machine (`weak_collatz_15`)

This binary Turing machine has **15 states**, **29 defined transitions** (all 29 visited by step
`93` on the blank tape—`100%` active cell utilization, `0` unused transitions, and `15/15`
Hopcroft equivalence classes), and a single halting transition (`14/ZERO`, state `14` reading `0`).
Starting in state `0` on the all-blank tape, Lean 4 constructively proves that it halts if and only
if there exist `x ≥ 3` and `1 ≤ j ≤ x` with `terras^[j] x = x`
(`halts_weakCollatz15_iff_bounded_cycle`), and hence if and only if the 16-state machine
`weak_collatz_16`, the 17-state machine `weak_collatz_17`, the 27-state machine `weak_collatz_27`,
the 41-state machine `weak_collatz_41`, and the 75-state baseline `weak_collatz_75` halt
(`candidate_equivalent`, `16 → 15` states, `-1` state / `-6.25%`;
`75 → 41 → 27 → 17 → 16 → 15` overall, `-60` states / `-80.00%`) and **Tao's Weak Collatz
Conjecture** is false (`halts_candidate_iff_not_weakCollatz`).

## Computability Context: Why Weak Collatz Is the Exact $\Sigma_1^0$ Half of Collatz

The full Collatz Conjecture asserts both **no divergent trajectories** ($\forall x \ge 1,\; \exists
k,\; T^k(x) = 1$) and **no nontrivial cycles** ($\forall x \ge 1,\; \forall k \ge 1,\; T^k(x) = x
\Rightarrow x \in \{1, 2\}$):
- Existence of a divergent trajectory ($\exists x \ge 1,\; \forall k,\; T^k(x) \neq 1$) is strictly
  $\Sigma_2^0$ and cannot be semi-decided by blank-tape Turing machine halting without an oracle.
- Existence of a nontrivial positive cycle ($\exists x \ge 3,\; \exists k \ge 1,\; T^k(x) = x$)—the
  negation of **Weak Collatz** (Steiner 1977; Böhm & Sontacchi 1978; Eliahou 1993; Tao 2019;
  `ccchallenge.org`)—is $\Sigma_1^0$, making it the exact half of the Collatz Conjecture reducible
  to standard `(Q, 2)` blank-tape halting.

## Compression Architecture (`75 → 41 → 27 → 17 → 16 → 15` states)

[`weak_collatz_16`](../weak_collatz_16/README.md) proved locally minimal under single-state deletion
because its inward parity-squeeze loop (`1^d 0 1^y`) required both an even-exit right-shift sweeper
(`EV_SR`) and a 2-step odd decrement (`P1`, `P2`) to undo the squeeze before computing `3k + 2`.
`weak_collatz_15` breaks out of that local minimum with a completely new **Parity-Back +
Left-to-Right Pair-Eater** architecture under the shifted conservation law `d + n = x - 1`
(`n = y - 1`, `0^∞ 1^d 0 1^n 0^∞`):

1. **Shifted Unary Conservation Law (`n = y - 1`, `d + n = x - 1`) & Zero-State `y = 2` Abort**:
   Representing `y ≥ 2` by `n = y - 1` makes even `y = 2k` correspond to odd `n = 2k - 1` and odd
   `y = 2k + 1` correspond to even `n = 2k`. Because every `terras` step from `y ≥ 3` lands in
   `y' ≥ 2` (`terras (2k) = k ≥ 2` for `k ≥ 2`, `terras (2k + 1) = 3k + 2 ≥ 5`), aborting
   immediately at `y = 2` (`n = 1`) makes `y = 1` unreachable. Under `n = y - 1`, `y = 2` (`n = 1`)
   is the unique configuration where the even-loop shift state `L1` (state `1`) reads `0`, jumping
   directly into `GT_SW` (`1(0) = 1R12`) with zero dedicated abort-detection state.
2. **Parity-Back Sweep (`states 5, 6`)**: Instead of a dedicated left-sweeper (`HALT_SW`) plus
   squeeze-parity detector (`T2`, `ODD0`), states `5` (`PAR_E`) and `6` (`PAR_O`) alternate while
   sweeping left across `1^n` at the end of every step, simultaneously returning to the separator
   `0` and branching on `n mod 2` (`PAR_O(0)` checks `d = 0` via `HALT_CHK` for even `z = x`
   cycle halting and otherwise dispatches to the even loop; `PAR_E(0)` dispatches to the odd loop).
3. **Left-to-Right Pair-Eater & 1-Step Odd Decrement (`O_P1`, state `10`)**:
   - **Even loop (`states 0–4`, `L += 1, M += 1, R -= 2`)**: eats pairs of `1`s from the right of
     `1^n` and leaves `1^(d + k) 0 1^(k - 1)` directly in place with zero shift-back cleanup
     (eliminating `EV_SR`).
   - **Odd loop (`states 7–11`, `L -= 1, M += 3, R -= 2`)**: because `0` is not first shifted right
     by `k + 1`, `terras (2k + 1) = 3k + 2` shifts `0` left by only `1` per pair of `1`s (`1`
     decrement state `O_P1` instead of `P1 + P2`), with the `+1` odd offset performed cleanly at
     entry (`5 → 7 → 8 → 10 → 11 → 7`) using the same loop transitions.
4. **6-Step Blank-Tape Boot (`29/29` Active Transitions Visited by Step `93`)**: Starting in state
   `0` (`L_SW`, `1R1 1L0`) on the all-blank tape reaches `stageCfg 4` (`0^∞ 0 [1] 1 1 0^∞` in state
   `3`) in **`6` steps** (`0 → 1 → 12 → 13 → 13 → 13 → 3`) and visits all `29/29` active
   transitions by step `93`.

As a one-line table in the `bbchallenge` format (`0`–`14` written `A`–`O`):

```
1RB1LA_1RM0RC_1RD1RC_0LF1RE_0LE0LA_0LH1LG_0LO1LF_0LF1RI_0LK0LJ_1LK1LJ_1RM0RL_1RH1RL_1LN1RM_0RD1LN_---1RN
```

Eliminating the shift-back pass and redundant pre-odd squeeze also delivers a **`~2.0x` speedup**
over `weak_collatz_16`: `weak_collatz_15` reaches `stageCfg 16` at step **`808`** and `stageCfg 18`
at step **`1,005`** (vs. `1,605` / `1,955` in `weak_collatz_16`, `2,706` in `weak_collatz_17`,
`12,238` in `weak_collatz_27`, `70,573` in `weak_collatz_41`, and `235,850` in `weak_collatz_75`
for `x = 17`), and reaches `stageCfg 24` at step **`2,338`** and `stageCfg 26` at step **`2,809`**
(vs. `4,821` / `5,663` in `weak_collatz_16`, and `677,770` for `x = 25` in `weak_collatz_75`—up to
**`~240x–290x`** faster than `weak_collatz_75`).

## Review Entry Points

- [`machine.txt`](machine.txt): Canonical 15-state transition table.
- [`WeakCollatz15.lean`](../../Cryptids/WeakCollatz15.lean):
  `halts_weakCollatz15_iff_bounded_cycle`, `candidate_equivalent`, and `candidate_fewer_states`
  (`zero_axioms` and `constructive`).
- [`Semantics/WeakCollatz15.lean`](../../Cryptids/Semantics/WeakCollatz15.lean):
  `halts_candidate_iff_exists_cycle`, `halts_candidate_iff_bohmSontacchi` (`constructive`), and
  `halts_candidate_iff_not_weakCollatz` (`all`).

## Verification

```sh
lake build Cryptids.WeakCollatz15 Cryptids.Semantics.WeakCollatz15 Challenge
lake comparator --config comparator/weak_collatz_15_reduction.json
lake comparator --config comparator/weak_collatz_15.json
python3 verify.py
```
