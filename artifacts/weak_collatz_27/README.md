# 27-state Weak Collatz machine (`weak_collatz_27`)

> [!NOTE]
> Superseded as the smallest Weak Collatz machine in this repository by the 17-state machine
> [`weak_collatz_17`](../weak_collatz_17/README.md) (`27 → 17` states, `-10` states / `-37.04%`),
> retained here as the intermediate zero-counter reduction step in the `75 → 41 → 27 → 17` chain.

This binary Turing machine has **27 states**, **53 defined transitions** (all 53 visited by step
`507` on the blank tape—`100%` active cell utilization), and a single halting transition
(`18/ZERO`, state `18` reading `0`). Starting in state `0` on the all-blank tape, Lean 4
constructively proves that it halts if and only if there exist `x ≥ 3` and `1 ≤ j ≤ x` with
`terras^[j] x = x` (`halts_weakCollatz27_iff_bounded_cycle`), and hence if and only if the 41-state
machine `weak_collatz_41` and 75-state baseline `weak_collatz_75` halt (`candidate_equivalent`,
`41 → 27` states, `-14` states / `-34.15%`; `75 → 41 → 27` overall, `-48` states / `-64.00%`) and
**Tao's Weak Collatz Conjecture** is false (`halts_candidate_iff_not_weakCollatz`).

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

## Compression Architecture (`75 → 41 → 27` states)

At every stage checkpoint `stageCfg x y` (`x ≥ 1`, `y ≥ 1`), the tape holds **only two unary
blocks** `0^∞  1^x  0  [1] 1^(y - 1)  0^∞` in state `24`, with **no step-counter block `1^c`**:

1. **Zero-Counter Cycle-Maximum Dovetailing (`-14` states vs. `weak_collatz_41`)**: Eliminates both
   the 1-pass triple-builder (`10` states) and the 3-block counter-decrement / stage-erase chains
   (`9` states) of [`weak_collatz_41`](../weak_collatz_41/README.md). Instead of counting down a
   unary budget `c`, stage `x` aborts and advances to `x + 1` whenever `y = 1` (exiting the trivial
   `{1, 2}` cycle) or `terras y > x` (exceeding the candidate cycle maximum):
   - Every nontrivial cycle `C` attains a maximum `M = max C ≥ 3` whose orbit stays inside `[3, M]`
     (`3 ≤ terras^[t] M ≤ M`) and returns in `1 ≤ j ≤ M - 2` steps, so the smallest such cycle
     maximum halts;
   - Conversely, by constructive finite pigeonhole (`not_stayIn_self_of_noStageHalts`), no stage
     `x ≥ 3` can remain inside `[2, x - 1]` for `x` rounds without hitting `1` unless a periodic
     orbit `u ≥ 3` (`u = 2` hits `1` next) lies entirely below `x`, guaranteeing stage termination
     even without assuming absence of divergent Collatz trajectories.
2. **Shared `restCfg` Stage-Advance Splitter (`states 0–6, 22, 23`)**: Both abort paths produce
   `0^∞ [0] 1^(2(x + 1)) 0^∞` in state `5` (`restCfg 0 0 (x + 1)`)—at `y = 1` via the 3-state
   doubler `dblCfg` (`states 0–3`), and at `z > x` by erasing `1^(z - x)` rightward into `0^∞`
   (`state 0`) onto the `1^(2x)` block already constructed during comparison—reusing the mismatch
   restoration loop `restCfg` to split `1^(2(x + 1))` directly into `stageCfg (x + 1) (x + 1)`.
3. **Zero-State Blank-Tape Warm-Up (`53/53` Active Transitions Visited)**: Starting in state `0` on
   the blank tape enters `restCfg 0 0 1` in `5` steps and naturally traverses `stageCfg 1 1`
   (`t = 18`) and `stageCfg 2 2` (`t = 56`, where `2 ↦ 1 ≠ 2` aborts at `y = 1`) into
   `stageCfg 3 3` (`t = 148`) with zero dedicated boot states.

As a one-line table in the style of the `bbchallenge` format (`0`–`25` written `A`–`Z`, `26`
written `a`):

```
1RC0RA_0RF0RA_1LD1RC_0LB1LD_1RW1LE_1RG1RF_0LT1RX_0RY1LH_1LD0RJ_0LK1RJ_0LQ0LL_0RZ1LM_1RI1LM_0Ra0RY_1RZ1RO_0LN1LP_0LS1LR_0LU1LR_---1RT_0RF0LH_0RW0RX_1LZ1RV_0RA0RF_1RV0LE_1RO1RI_1LP1La_1LR0LQ
```

This compression also accelerates simulation (`12,238` vs. `70,573` steps in `weak_collatz_41` and
`235,850` in `weak_collatz_75` to reach stage `x = 17`—a `5.77x` / `19.27x` speedup; `36,226` vs.
`174,497` and `677,770` steps to reach `x = 25`—a `4.82x` / `18.71x` speedup).

## Review Entry Points

- [`machine.txt`](machine.txt): Canonical 27-state transition table.
- [`WeakCollatz27.lean`](../../Cryptids/WeakCollatz27.lean): `halts_weakCollatz27_iff_bounded_cycle`,
  `candidate_equivalent`, and `candidate_fewer_states` (`zero_axioms` and `constructive`).
- [`Semantics/WeakCollatz27.lean`](../../Cryptids/Semantics/WeakCollatz27.lean):
  `halts_candidate_iff_exists_cycle`, `halts_candidate_iff_bohmSontacchi` (`constructive`), and
  `halts_candidate_iff_not_weakCollatz` (`all`).

## Verification

```sh
lake build Cryptids.WeakCollatz27 Cryptids.Semantics.WeakCollatz27 Challenge
lake comparator --config comparator/weak_collatz_27_reduction.json
lake comparator --config comparator/weak_collatz_27.json
python3 verify.py
```
