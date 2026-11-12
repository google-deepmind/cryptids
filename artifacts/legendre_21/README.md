# 21-state Legendre machine

This binary Turing machine has **21 states** and 41 defined transitions. It halts only in state
`20` (`X`) reading `0`, its one undefined cell. It starts in state `0` (`q14`) on the blank tape.
Lean proves that it halts if and only if Legendre's conjecture is false, i.e. if some `n ≥ 1` has
no prime strictly between `n^2` and `(n + 1)^2` (one of Landau's four problems, 1912).

The machine was designed by Daniel Veljjanoski, with Claude (Anthropic) as assistant. Its
primality test is the one of the Goldbach machines: the anonymous 2016 machine, Andrew Yao and
Yijun Leng's `goldbach_25`, and [`goldbach_21`](../goldbach_21/README.md) by Maxence Faldor and Moritz
Firsching. Sixteen of the 21 states are states of that test, with seven of their cells changed,
and the Lean proof uses the lemmas of [`Goldbach21.lean`](../../Cryptids/Goldbach21.lean).

Earlier machines for the same conjecture, both with Lean proofs:

- Joseph Jabbour and Ralph Razzouk, 26 states ([`ralphrazzouk/busybeaver`](https://github.com/ralphrazzouk/busybeaver/tree/master/problems/legendre), September
  2026; a 29-state version before it). Its primality test also comes from the 25-state Goldbach
  machine. It counts the numbers left in the interval down, leaves the interval at its first
  prime, and rebuilds the count for the next interval by a copy loop.
- Charlie Reams, 44 states, with a proof of an equivalent statement
  ([`calr3/tinycryptids`](https://github.com/calr3/tinycryptids/tree/main/legendre), November
  2026). That machine also tracks the interval with a register of cells with a hole and a flag
  set by a prime; here the register needs no rebuild between intervals, and the primality test
  is a different one.

## How it works

Everything is in unary. The tape holds, left to right, a block of ones for the number under
test, a separator `0`, a flag cell, and a walker area of ones with one hole. The tape left of
the block stays blank; the block grows to the left. States `0`–`20` are
`q14, q0, q3, q4, q6, q7, q9, q11, q12, q13, q15, q16, q20, q22, q23, q24, A1, B, C, Z1, X`,
where `q0`–`q24` are the names of the same states in the Lean proof of `goldbach_21`.

* **Test** (the sixteen `q` states): `q16` reading the blank left of a block of `t` ones writes
  a `1` and enters the trial division of `t` by `2, 3, …`. A prime leaves `q6` on the
  separator; a composite leaves `q6` on the flag cell, through `A1`. The block is restored.
* **Walker** (`B`, `C`, `Z1`): after each test `B` runs right to the hole and fills it, `C` opens
  a hole one cell further left, `Z1` runs back, and `q3`, `q4`, `q16` return to the left end of
  the block, where the next number is tested.
* **Intervals**: interval `n` is `n^2, …, n^2 + 2n` (`n^2` is never prime, so it holds the same
  primes as the open interval of the conjecture). It starts with the flag clear and `2n` ones in
  the walker area; the blank beyond them is the hole. The first prime of the interval sets the
  flag, moves the separator one cell left, and is tested once more. When the hole reaches the
  left end with the flag set, it moves into the flag cell: the flag is clear again and the
  walker area has `2n + 2` ones, the start of interval `n + 1`.
* **Halt**: when the hole reaches the left end with the flag clear after a composite, no prime
  was seen in the interval; `C` reads the flag, `X` reads the separator, and `X` reading `0` is
  undefined.
* **Start**: `q14` on the blank tape. After 17 steps the machine is at the test of `1` with the
  walker area `1 0 1`; the number `1` does not move the hole, so interval `1` (`1, 2, 2, 3`)
  ends as every later interval does. No state is used for the start only.

The machine began as a 25-state hand design (the test and eight more states) and was reduced to
21 states by computer searches over merged states, changed cells and start states; the
survivors of each search were then checked against a simulator written from the definition.
Searches that merge one state of the 21-state machine and change up to two cells, for every
start state, and a partial search with three changed cells found no 20-state machine.

In the bbchallenge standard text format (states `0`–`20` written `A`–`U`):

```
1LK1LA_0RH1LN_0LL1RD_0LL1RE_0RR0LF_1RS1LN_1RB0LG_1RH0RI_1RJ1RI_0LA0LM_1LQ0LO_1RC1LL_1LG1LM_0RB0LN_1RP1LO_1RC1RP_0RE1RQ_1LS1RR_1LU0LT_0LC1LT_---0RR
```

## Review entry points

- [`Legendre21.lean`](../../Cryptids/Legendre21.lean): the machine (loaded from `machine.txt`),
  its embedding into the state numbering of `Goldbach21.edited`, the test (`test_eval`), the
  interval lemmas, and `halts_legendre21_iff`.
- [`Semantics/Legendre21.lean`](../../Cryptids/Semantics/Legendre21.lean):
  `halts_legendre21_iff_exists_gap` and `halts_legendre21_iff_not_legendre`.

## Verification

`python3 verify.py` simulates the machine on the blank tape and checks the whole tape at every
test event (`q16` reading `0`) against the block, separator, flag and walker area of the proof;
the first events are at steps 14 and 17, and the default `--steps 250000` covers 50 test
events, up to the number 43. It also checks that from a prepared tape at the end of an interval
in which no prime was seen the machine halts in state `20`, while with the flag set it goes on
to the next interval with the expected tape.
