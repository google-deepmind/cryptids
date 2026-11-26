# 75-state Weak Collatz reference machine (`weak_collatz_75`)

This binary Turing machine has **75 states** and one halting transition (`56/ZERO`, state `56`
reading `0`). Starting in state `0` on the blank tape, Lean 4 constructively proves that it halts
if and only if there exist `x ≥ 3` and `1 ≤ j ≤ x` with `terras^[j] x = x`
(`halts_weakCollatz75_iff_bounded_cycle`), equivalently if and only if `terras` admits a nontrivial
positive cycle (`halts_weakCollatz75_iff_exists_cycle`) or a solution to the Böhm–Sontacchi (1978)
Diophantine cycle equation (`halts_weakCollatz75_iff_bohmSontacchi`), and hence if and only if
**Tao's Weak Collatz Conjecture** is false (`halts_weakCollatz75_iff_not_weakCollatz`).

`weak_collatz_75` improves on the previously published unverified 124-state Weak Collatz machine on
the `bbchallenge` wiki (`124 → 75` states) via constructive finite pigeonhole on the cycle maximum
`M ≥ 3` (`1 ≤ j ≤ M - 2`), and serves as the reference baseline for the 41-state compression
[`weak_collatz_41`](../weak_collatz_41/README.md) (`75 → 41` states).

## Review Entry Points

- [`machine.txt`](machine.txt): Canonical 75-state transition table.
- [`WeakCollatz75.lean`](../../Cryptids/WeakCollatz75.lean): `halts_weakCollatz75_iff_bounded_cycle`.
- [`Semantics/WeakCollatz75.lean`](../../Cryptids/Semantics/WeakCollatz75.lean):
  `bounded_cycle_iff_exists_cycle`, `halts_weakCollatz75_iff_exists_cycle`,
  `halts_weakCollatz75_iff_bohmSontacchi`, and `halts_weakCollatz75_iff_not_weakCollatz`.
