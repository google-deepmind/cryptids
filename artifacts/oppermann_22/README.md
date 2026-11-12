# 22-state Oppermann machine

This binary Turing machine has **22 states** and 43 defined transitions. It halts only in state
`21` (`X`) reading `0`, its one undefined cell. It starts in state `0` (`q12`) on the blank tape.
Lean proves that it halts if and only if Oppermann's conjecture is false, i.e. if some `n ≥ 2` has
no prime strictly between `n^2 - n` and `n^2`, or none strictly between `n^2` and `n^2 + n`.

The machine was designed by Daniel Veljjanoski, with Claude (Anthropic) as assistant. Its
primality test is the one of the Goldbach machines: the anonymous 2016 machine, Andrew Yao and
Yijun Leng's `goldbach_25`, and [`goldbach_21`](../goldbach_21/README.md) by Maxence Faldor and Moritz
Firsching. Sixteen of the 22 states are states of that test, with seven of their cells changed,
and the Lean proof uses the lemmas of [`Goldbach21.lean`](../../Cryptids/Goldbach21.lean).

Earlier machines for the same conjecture, both with Lean proofs:

- Joseph Jabbour and Ralph Razzouk, 28 states ([`ralphrazzouk/busybeaver`](https://github.com/ralphrazzouk/busybeaver/tree/master/problems/oppermann), September
  2026; a 29-state version before it). It counts the numbers left in the interval down and
  rebuilds the count for the next interval by a copy loop.
- Charlie Reams, 45 states ([`calr3/tinycryptids`](https://github.com/calr3/tinycryptids/tree/main/oppermann), November 2026). It tracks the interval
  with a register of cells whose hole moves two cells per number, and a flag set by a prime.

Both walk the intervals between consecutive quarter-squares `⌊j²/4⌋`, whose interiors are
exactly the half-intervals of the conjecture; this machine does the same. Its walker area with a hole that
moves two cells per number and its flag are close to Reams's register; here the area needs no
rebuild between blocks, the start runs through the loop's own states, and the primality test
is a different one.

## How it works

Everything is in unary. The tape holds, left to right, a block of ones for the number under
test, a separator `0`, a flag cell, and a walker area of ones with one hole. The tape left of
the block stays blank; the block grows to the left. States `0`–`21` are
`q12, q16, q0, q3, q4, q6, q7, q9, q11, q13, q14, q15, q20, q22, q23, q24, A1, B, C, C2, Z1, X`,
where `q0`–`q24` are the names of the same states in the Lean proof of `goldbach_21`.

* **Test** (the sixteen `q` states): `q16` reading the blank left of a block of `t` ones writes
  a `1` and enters the trial division of `t` by `2, 3, …`. A prime leaves `q6` on the
  separator; a composite leaves `q6` on the flag cell, through `A1`. The block is restored.
* **Walker** (`B`, `C`, `C2`, `Z1`): after each test `B` runs right to the hole and fills it,
  `C` steps one cell left, `C2` opens a hole on the next cell left, `Z1` runs back, and `q3`,
  `q4`, `q16` return to the left end of the block, where the next number is tested. So the hole
  moves two cells per number. The first prime of a block sets the flag.
* **Blocks**: block `j` is `⌊j²/4⌋, …, ⌊(j+1)²/4⌋ - 1`. Block `2n` is `n^2, …, n^2 + n - 1` and
  block `2n + 1` is `n^2 + n, …, (n + 1)^2 - 1`; the first number of a block is not prime (from
  block `4` on), so the block holds the same primes as the open half-interval of the
  conjecture. It starts with the flag clear and `j - 1` ones in the walker area; the blank
  beyond them is the hole. At the last number of the block the hole would land on the flag
  cell (`j` even) or pass it (`j` odd). With the flag set, the flag is cleared and the walker
  area has `j` ones, the start of block `j + 1`.
* **Halt**: with the flag clear and `j` odd, `C` reads the flag, `X` reads the separator, and
  `X` reading `0` is undefined. With the flag clear and `j` even, the hole moves one cell only
  and the machine halts one number later, at the first number of the next block, which is not
  prime.
* **Start**: `q12` on the blank tape. After 9 steps the machine is at the test of `0` with the
  walker area `0 1 1`, one cell out of step with the blocks. The tests of `0, …, 11` bring it
  into step (at `10` the hole moves one cell only, and `11` is prime): it is then at the start
  of block `7`, the number `12`, with six ones in the walker area. The half-intervals of
  `n = 2, 3` hold the primes `3, 5, 7, 11`. No state is used for the start only.

The design follows `legendre_21`, a 21-state machine for Legendre's conjecture by the same
author (proposed separately in pull request #32 of this repository): the same test and walker,
with one more state (`C2`), four changed cells and another start state. A start without a
further state was found by a computer search over start states and
changed cells; its survivors were checked against a simulator written from the definition.
Searches that merge one state of the 22-state machine and change up to two cells, for every
start state, found no 21-state machine.

In the bbchallenge standard text format (states `0`–`21` written `A`–`V`):

```
1RJ1RA_1RD1LB_0RI1LN_0LB1RE_0LB1RF_0RR0LG_0LE1LN_1RC0LH_1RI0RA_0LK0LM_1LL1LK_1LQ0LO_1LH1LM_0RC0LN_1RP1LO_1RD1RP_0RF1RQ_1LS1RR_0LV1LT_0RT0LU_0LD1LU_---1RF
```

## Review entry points

- [`Oppermann22.lean`](../../Cryptids/Oppermann22.lean): the machine (loaded from `machine.txt`),
  its embedding into the state numbering of `Goldbach21.edited`, the test (`test_eval`), the
  walker and block lemmas, and `halts_oppermann22_iff`.
- [`Semantics/Oppermann22.lean`](../../Cryptids/Semantics/Oppermann22.lean):
  `halts_oppermann22_iff_exists_gap` and `halts_oppermann22_iff_not_oppermann`.

## Verification

`python3 verify.py` simulates the machine on the blank tape and checks the whole tape at every
test event (`q16` reading `0`) against the block, separator, flag and walker area of the proof;
the first events are at steps 9 and 12, and the default `--steps 250000` covers 48 test
events, up to the number 47. It also checks that from prepared tapes at the end of a block in
which no prime was seen the machine halts in state `21` (at once for a block of odd index, one
number later for a block of even index), while with the flag set it goes on to the next block
with the expected tape.
