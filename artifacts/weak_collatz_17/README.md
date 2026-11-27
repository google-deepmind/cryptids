# 17-state Weak Collatz machine (`weak_collatz_17`)

> [!NOTE]
> Superseded as the smallest Weak Collatz machine in this repository by the 16-state machine
> [`weak_collatz_16`](../weak_collatz_16/README.md) (`17 → 16` states, `-1` state / `-5.88%`),
> retained here as the `+1`-stage popcount-conservation step in the `75 → 41 → 27 → 17 → 16` chain.

This binary Turing machine has **17 states**, **33 defined transitions** (all 33 visited by step
`238` on the blank tape—`100%` active cell utilization, `0` unused transitions, and `17/17`
Hopcroft equivalence classes), and a single halting transition (`16/ZERO`, state `16` reading `0`).
Starting in state `0` on the all-blank tape, Lean 4 constructively proves that it halts if and only
if there exist `x ≥ 3` and `1 ≤ j ≤ x` with `terras^[j] x = x`
(`halts_weakCollatz17_iff_bounded_cycle`), and hence if and only if the 27-state machine
`weak_collatz_27`, the 41-state machine `weak_collatz_41`, and the 75-state baseline
`weak_collatz_75` halt (`candidate_equivalent`, `27 → 17` states, `-10` states / `-37.04%`;
`75 → 41 → 27 → 17` overall, `-58` states / `-77.33%`) and **Tao's Weak Collatz Conjecture** is
false (`halts_candidate_iff_not_weakCollatz`).

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

## Compression Architecture (`75 → 41 → 27 → 17` states)

Instead of storing two independent unary blocks `1^x 0 1^y` (which required dedicated comparison,
mismatch restoration, and stage-doubling loops totaling 17 states in
[`weak_collatz_27`](../weak_collatz_27/README.md)), `weak_collatz_17` maintains the **popcount
conservation law** `d + y = x` at every round checkpoint `roundCfg d y` (`d = x - y ≥ 0`, `y ≥ 1`),
encoding the pair `(x, y)` as `0^∞  1^d  [0]  1^y  0^∞` in state `1`:

1. **Single-Block Stage Start & 1-Step Blank-Tape Boot (`0` extra states)**: At the start of stage
   `x` (`d = 0`, `y = x`), `roundCfg 0 x` is simply a **single** unary block `0^∞ [0] 1^x 0^∞`!
   Starting in state `0` (`1L1 1R0`) on the blank tape writes `1` and steps left into `roundCfg 0 1`
   at **`t = 1`**, visiting `stageCfg 2` at `t = 8` and `stageCfg 3` at `t = 29` with zero dedicated
   boot or stage-splitting states.
2. **Inward Parity Squeeze (`states 1–7`)**: Each squeeze pass (`sqzCfg d b a`) shifts a left `0`
   one cell right (`d ↦ d + 1`) and carves a right `0` one cell left (`b ↦ b - 2`, `a ↦ a + 1`),
   conserving `d + b + a = x`. For even `y = 2k + 2`, `x - (k + 1) = d + k + 1 ≥ 1` always holds,
   and state `7` shifts `1^(k + 1)` left by one cell into `roundCfg (d + k + 1) (k + 1)`.
3. **Conservation-Preserving Odd Pass, `O(1)`-Write Stage Advance & Cycle-Max Halt (`states 8–16`)**:
   For `y = 1`, states `8 → 5 → 0 → 1` fill the single `0` next to `1^x` with `1`, forming
   `1^(x + 1)` in `7` steps. For odd `y = 2k + 1 ≥ 3` (`z = 3k + 2`), the squeeze leaves
   `0^∞ 1^(d + k + 1) 0 [0] 1^k 0^∞`; each pass (`states 10–14`) peels two `1`s locally from the
   left block and one `1` from `1^k` into the middle block (`(L, r, m) ↦ (L - 2, r + 3, m - 1)`,
   still conserving `L + r + m = x`):
   - **If `L` runs out early (`z > x` abort)**: state `9` trims the temporary `+1` and state `0`
     fills the single `0` between `1^r` and `1^m` with `1`, merging `1^r 1 1^m = 1^(x + 1)` in
     place and sweeping left to `stageCfg (x + 1)`;
   - **When all `k + 1` peels succeed (`z ≤ x`)**: state `15` sweeps left to the separator `0` and
     state `16` inspects the cell to its left—halting (`---`) iff `x - z = 0` (`z = x`; note every
     predecessor `y ≤ M` of a cycle maximum `M = max C ≥ 3` must be odd since `2M > M`), and
     otherwise stepping right into `roundCfg (x - z) z`.

As a one-line table in the `bbchallenge` format (`0`–`16` written `A`–`Q`):

```
1LB1RA_1RC1LB_1RH0RD_0RI1RE_1LF1RE_0LA0LG_0RC1LP_0LF1RH_0LF1LJ_0LK0RA_1LL1LK_0RJ1LM_0RJ0RN_1RO1RN_0LF0LK_0LQ1LP_---1RB
```

This compression also delivers another **`4.5x` speedup** over `weak_collatz_27` (`2,706` vs.
`12,238` steps in `weak_collatz_27`, `70,573` in `weak_collatz_41`, and `235,850` in
`weak_collatz_75` to reach stage `x = 17`—a `4.52x` / `26.08x` / `87.16x` speedup; `7,920` vs.
`36,226`, `174,497`, and `677,770` steps to reach stage `x = 25`—a `4.57x` / `22.03x` / `85.58x`
speedup).

## Review Entry Points

- [`machine.txt`](machine.txt): Canonical 17-state transition table.
- [`WeakCollatz17.lean`](../../Cryptids/WeakCollatz17.lean): `halts_weakCollatz17_iff_bounded_cycle`,
  `candidate_equivalent`, and `candidate_fewer_states` (`zero_axioms` and `constructive`).
- [`Semantics/WeakCollatz17.lean`](../../Cryptids/Semantics/WeakCollatz17.lean):
  `halts_candidate_iff_exists_cycle`, `halts_candidate_iff_bohmSontacchi` (`constructive`), and
  `halts_candidate_iff_not_weakCollatz` (`all`).

## Verification

```sh
lake build Cryptids.WeakCollatz17 Cryptids.Semantics.WeakCollatz17 Challenge
lake comparator --config comparator/weak_collatz_17_reduction.json
lake comparator --config comparator/weak_collatz_17.json
python3 verify.py
```
