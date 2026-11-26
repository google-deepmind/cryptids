# 41-state Weak Collatz machine (`weak_collatz_41`)

This binary Turing machine has **41 states**, **81 defined transitions** (all 81 visited within the
first 250,000 steps on the blank tape), and a single halting transition (`25/ZERO`, state `25`
reading `0`). Starting in state `0` on the all-blank tape, Lean 4 constructively proves that it
halts if and only if there exist `x ≥ 3` and `1 ≤ j ≤ x` with `terras^[j] x = x`
(`halts_weakCollatz41_iff_bounded_cycle`), and hence if and only if the 75-state reference machine
`weak_collatz_75` halts (`candidate_equivalent`, `-34` states / `-45.33%`) and **Tao's Weak Collatz
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

## Compression Architecture (`75 → 41` states)

At every stage checkpoint `stageCfg c x y` (`c ≥ 1`, `x ≥ 3`, `y ≥ 1`), the tape holds
`0^∞  1^c  0  1^x  0  [1] 1^(y - 1)  0^∞` in state `12`, separated by **single-cell `0` markers**
with **zero growing blank gaps**:

1. **Outer-Left Counter & Adjacent `1^x 0 1^y` Layout**: Reordering the tape from
   `1^x 00 1^c 0^(g + 2) 1^y` (`weak_collatz_75`) to `1^c 0 1^x 0 1^y` places `1^x` and `1^z`
   directly adjacent across a single `0` and erases `1^c` from its outer left edge into `0^∞`,
   eliminating all variable-width `0^(g + 2)` sweeps (`sweep0R`/`sweep0L`).
2. **In-Place Zero-Gap `terras` Engine (`states 12–22`)**: Shifts a single `0`-hole rightward
   through `1^y` while erasing `1`s from the right end (`evenCfg`). For even `y = 2k + 2`, the
   right suffix vanishes into `0^∞`, leaving `1^(k + 1)` directly in place; for odd `y = 2k + 1`,
   the hole reverses leftward (`oddCfg`), expanding `1^k` into `1^(3k + 2)` without moving the
   left delimiter.
3. **Local `2p` Comparison & Unified Restoration (`states 0, 1, 20, 22, 23–31`)**: Compares
   `1^x 0 1^z` locally as `1^u 0 1^v 0 1^(2p)` (`u + p = x`, `v + p = z`) without ever sweeping
   across `1^c` or `1^(2p)`, halting at `(25, 0)` when `u = v = 0` and otherwise restoring
   `1^x 0 1^z` through a single shared loop (`restCfg`) for both `z < x` and `z > x`.
4. **Right-to-Left 1-Pass Triple-Build & 6-Step Boot (`states 0–11, 34–40`)**: Builds all three
   blocks `1^A 0 1^A 0 1^A` from `1^A` in a single pass (`tripleCfg`) instead of two copy passes,
   uses the sole free `0`-slot `(1, 0)` for a 6-step blank-tape entry into `tripleCfg 0 3`
   (reaching `stageCfg 3 3 3` at step `77`), and pairs all six disjoint `0`-only and `1`-only
   states without context ambiguity.

This compression also accelerates simulation (`70,573` vs. `235,850` steps to reach stage `x = 17`,
a `3.34x` speedup; `174,497` vs. `677,770` steps to reach `x = 25`, a `3.88x` speedup).

## Review Entry Points

- [`machine.txt`](machine.txt): Canonical 41-state transition table.
- [`WeakCollatz41.lean`](../../Cryptids/WeakCollatz41.lean): `halts_weakCollatz41_iff_bounded_cycle`,
  `candidate_equivalent`, and `candidate_fewer_states` (`zero_axioms` and `constructive`).
- [`Semantics/WeakCollatz41.lean`](../../Cryptids/Semantics/WeakCollatz41.lean):
  `halts_candidate_iff_exists_cycle`, `halts_candidate_iff_bohmSontacchi` (`constructive`), and
  `halts_candidate_iff_not_weakCollatz` (`all`).

## Verification

```sh
lake build Cryptids.WeakCollatz41 Cryptids.Semantics.WeakCollatz41 Challenge
lake comparator --config comparator/weak_collatz_41_reduction.json
lake comparator --config comparator/weak_collatz_41.json
python3 verify.py
```
