# 16-state Weak Collatz machine (`weak_collatz_16`)

This binary Turing machine has **16 states**, **31 defined transitions** (all 31 visited by step
`1,576` on the blank tape—`100%` active cell utilization, `0` unused transitions, and `16/16`
Hopcroft equivalence classes), and a single halting transition (`15/ZERO`, state `15` reading `0`).
Starting in state `0` on the all-blank tape, Lean 4 constructively proves that it halts if and only
if there exist `x ≥ 3` and `1 ≤ j ≤ x` with `terras^[j] x = x`
(`halts_weakCollatz16_iff_bounded_cycle`), and hence if and only if the 17-state machine
`weak_collatz_17`, the 27-state machine `weak_collatz_27`, the 41-state machine `weak_collatz_41`,
and the 75-state baseline `weak_collatz_75` halt (`candidate_equivalent`, `17 → 16` states, `-1`
state / `-5.88%`; `75 → 41 → 27 → 17 → 16` overall, `-59` states / `-78.67%`) and **Tao's Weak
Collatz Conjecture** is false (`halts_candidate_iff_not_weakCollatz`).

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

## Compression Architecture (`75 → 41 → 27 → 17 → 16` states)

In [`weak_collatz_17`](../weak_collatz_17/README.md), advancing the candidate maximum by `+1`
(`x ↦ x + 1`) required a dedicated trim/entry state `GTD_OIN` (state `9` of `weak_collatz_17`) to
erase the temporary `+1` written by `O_SL` before `GT_SW` filled the separator `0` on `z > x`
aborts. `weak_collatz_16` eliminates that state completely by exploiting **parity of cycle maxima**:

1. **Every Nontrivial Cycle Maximum Is Even (`even_of_stageHalts`, constructive)**: If a nontrivial
   `terras` cycle `C` outside `{1, 2}` had an odd maximum `M = 2m + 1 ≥ 3`, its immediate successor
   would satisfy `terras(2m + 1) = 3m + 2 > 2m + 1 = M`, contradicting `M = max C` (indeed `M ≡ 2
   (mod 6)` since its cycle predecessor must be odd). Consequently, testing **only even candidate
   maxima** `x = 2m` (`x = 2, 4, 6, 8, ...`, incrementing `x ↦ x + 2` on stage abort) is both sound
   and complete.
2. **Trim-Free `+2` Stage Advance (`-1` state vs. `weak_collatz_17`)**: Under the popcount
   conservation law `d + y = x` at `roundCfg d y` (`0^∞ 1^d [0] 1^y 0^∞` in state `1`):
   - **On `z > x` abort (`L = 0` at state `10` or `L = 1` at state `11`)**: `O_SL` (state `9`) has
     already increased the tape popcount from `x` to `x + 1`; jumping directly to `GT_SW` (state
     `3`, `1L1 1R3`) without trimming fills the single separator `0` with `1`, merging the blocks
     directly into `1^(x + 2)` (`stageCfg (x + 2)`)!
   - **On `y = 1` abort**: `ODD0` (state `8`) bounces left through `EV_SR → EC → O_SL → P1 → GT_SW`
     (`8 → 7 → 5 → 9 → 10 → 3 → 1`), prepending `1` on the left (`O_SL`) and appending `1` on the
     right (`GT_SW`) to advance `1^x ↦ 1^(x + 2)` using the exact same states.
3. **Zero-State Blank-Tape Boot (`31/31` Active Transitions Visited)**: Starting in state `0` (`T2`,
   `0R8 1R4`) on the all-blank tape traverses `0 → 8 → 7 → 5 → 9 → 10 → 3 → 1`, reaching
   `stageCfg 2` at **`t = 9`** and `stageCfg 4` at **`t = 39`** with zero dedicated boot states.

As a one-line table in the `bbchallenge` format (`0`–`15` written `A`–`P`):

```
0RI1RE_1RC1LB_1RH0RA_1LB1RD_1LF1RE_0LJ0LG_0RC1LO_0LF1RH_0LH1LF_1LK1LJ_0RD1LL_0RD0RM_1RN1RM_0LF0LJ_0LP1LO_---1RB
```

Skipping all odd candidate stages also yields an additional **`~1.5x` speedup** over
`weak_collatz_17` (`1,605` steps to reach `x = 16` and `1,955` steps to reach `x = 18`, vs. `2,706`
steps in `weak_collatz_17`, `12,238` in `weak_collatz_27`, `70,573` in `weak_collatz_41`, and
`235,850` in `weak_collatz_75` to reach `x = 17`; `4,821` steps to `x = 24` and `5,663` steps to
`x = 26`, vs. `7,920`, `36,226`, `174,497`, and `677,770` steps to `x = 25`—up to **`120x–140x`**
faster than `weak_collatz_75`).

## Review Entry Points

- [`machine.txt`](machine.txt): Canonical 16-state transition table.
- [`WeakCollatz16.lean`](../../Cryptids/WeakCollatz16.lean): `halts_weakCollatz16_iff_bounded_cycle`,
  `candidate_equivalent`, and `candidate_fewer_states` (`zero_axioms` and `constructive`).
- [`Semantics/WeakCollatz16.lean`](../../Cryptids/Semantics/WeakCollatz16.lean):
  `halts_candidate_iff_exists_cycle`, `halts_candidate_iff_bohmSontacchi` (`constructive`), and
  `halts_candidate_iff_not_weakCollatz` (`all`).

## Verification

```sh
lake build Cryptids.WeakCollatz16 Cryptids.Semantics.WeakCollatz16 Challenge
lake comparator --config comparator/weak_collatz_16_reduction.json
lake comparator --config comparator/weak_collatz_16.json
python3 verify.py
```
