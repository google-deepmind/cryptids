# 19-state Kurepa machine

This binary Turing machine has **19 states** and 37 defined transitions. It halts only in state
`17` (`K`) reading `0`, its one undefined cell. It starts in state `0` (`G0`) on the blank tape.
Lean proves that it halts if and only if Kurepa's left factorial conjecture is false, i.e. if some
`n > 2` divides the left factorial `!n = 0! + 1! + ... + (n - 1)!` (Đuro Kurepa, *On the left
factorial function !n*, Math. Balkanica 1, 1971; problem B44 in Guy's *Unsolved Problems in Number
Theory*). Equivalently: if some odd prime `p` divides `!p`.

The machine was designed by Daniel Veljjanoski, with Claude (Anthropic) as assistant.

An earlier machine for the same conjecture is Charlie Reams's 38-state machine with a Lean proof
([`calr3/tinycryptids`](https://github.com/calr3/tinycryptids/tree/main/kurepa), October 2026; a 47-state hand design reduced to 38 states by exact SAT
state merging). It tests `n | !n` for every `n >= 3`: the tape holds `n`, the sum `!n + n + 1`,
`n!` and copies of `n!` in unary; a hole walks the sum while a second hole steps cyclically through
the cells of `n`; and filling a marker merges `n!` into the sum. This machine keeps that scheme
(a unary modulus, a running sum, a factorial, the two holes, the merge by a filled marker) and,
like Reams's machine, tests every number without a primality test. What is different:

- It tests `2S | !S` for every `S >= 2`. `2 | !2` is true, so a machine that tests `n | !n` has to
  skip `n = 2`; `4` does not divide `!2 = 2`, so this machine skips nothing, the tape holds half
  factorials, and the first tape is `11 0 11 0 1`.
- The hole of the sum starts on the marker itself, so the test and the merge are one walk.
- The multiplication is the copy loop of [`brocard_27`](../brocard_27/README.md).
- The table was shrunk by a computer search (delete a state, redirect its transitions, change at
  most two cells) from a 21-state loop to an 18-state loop that needs one start state.

## How it works

Everything is in unary. States `0`–`18` are `G0, S1, S2, EC, R1, L0, L1, LNa, LN0, W, W2, EN, TRa,
TRb, BE, TLa, TLb, K, LNf`. At the start of round `S >= 2` the tape holds, left to right, a block
`N` of `S` ones, a separator `0`, a block `A` of `!S/2 + S - 1` ones, a marker `0`, and a block `T`
of `S!/2` ones; `S1` is in `N` or on the separator.

* **Multiply** (`S1`–`LN0`, states `1`–`8`): `S + 1` passes. In each pass `EC` walks a cursor hole
  through `T`, and for every cell a `1` is appended to a block `C` right of `T`. At the end of the
  first pass a new cell is written left of `N`; after each pass a hole opens in `N` one cell
  further right, and the passes end when that hole has passed the last cell of `N`. Then `C` has
  `(S + 1) * S!/2` ones and `N` has `S + 1`.
* **Test** (`W`–`LNf`, states `9`–`18`): `EN` opens a hole on the second cell of `N`. `TRa`, `TRb`
  run right to the first `0` of `A` and fill it; the first time this is the marker, which merges
  `T` into `A`. `BE` opens the next hole one cell to the left, `TLa`, `TLb` run back and fill the
  hole of `N`, and `EN` opens it one cell further right, or on the second cell again when it has
  passed the last cell: the first cell of `N` is never used, so the hole steps cyclically through
  `S` cells. When `A` is used up, `K` reads the last cell of `N`. It is the hole exactly if `S`
  divides `|A| + 1 = !S/2 + S`, i.e. if `2S | !S`: `K` reading `0` is the undefined cell.
  Otherwise `LNf` fills the hole and round `S + 1` starts: `A` now has
  `!S/2 + S - 1 + 1 + S!/2 = !(S + 1)/2 + S` ones, and `C` is the new `T`.
* **Why this is Kurepa's conjecture**: an `S > 2` with `2S | !S` is a counterexample, and `S = 2`
  never passes. Conversely an odd counterexample `n` passes the test itself (`!n` is even), and
  an even one, `n = 2j`, has `j > 2` (`4` does not divide `!4 = 10`) and `j` is a counterexample
  again: `j | n | !n`, and `j` divides `k!` for `k >= j`, so `j | !j`. Repeat until it is odd.
* **Start**: `G0` (state `0`) on the blank tape. `G0`, `EN`, `W`, `W2` write `11 0 11`, and the
  test states write the rest: after 15 steps the tape is `11 0 11 0 1` with `S1` on the
  separator, the start of round `2`. Both cells of `G0`, and `W2` reading `0`, are used for the
  start only.

The search for a smaller machine went on from this one: deleting one more state, redirecting its
transitions and changing up to two cells, for every start state, found no 18-state machine with
this tape layout. That is a statement about this search, not a lower bound.

In the bbchallenge standard text format (states `0`–`18` written `A`–`S`):

```
1LL1RJ_0RC1RB_0RD1RC_0LE0RB_1LF1LH_0LG1LF_1RD1LG_0LI1LH_0RJ1LF_0RK1LJ_1RA1RL_0LJ0RM_0RN1RM_1LO1RN_0LR0LP_0LQ1LP_1RL1LQ_---1LS_1LB1LS
```

## Review entry points

- [`Kurepa19.lean`](../../Cryptids/Kurepa19.lean): the machine (loaded from `machine.txt`), the
  multiply and test lemmas, the round lemmas `round_halt` and `round_next`, and
  `halts_kurepa19_iff`.
- [`Semantics/Kurepa19.lean`](../../Cryptids/Semantics/Kurepa19.lean):
  `halts_kurepa19_iff_exists_dvd`, `halts_kurepa19_iff_exists_prime` and
  `halts_kurepa19_iff_not_kurepa`.

## Verification

`python3 verify.py` simulates the machine on the blank tape, checks that the first round start is
at step 15 with the tape `11 0 11 0 1`, and checks the whole tape at every round start (`S1`
entered from `LNf`) against `S`, `!S/2 + S - 1` and `S!/2` ones (`S = 2, ..., 6` at the default
`--steps 250000`; the rounds `7` and `8` start after 7,441,638 and about 465,000,000 steps). It
also checks that from a prepared round start with `S = 5`, `|A| = 9`, `|T| = 3` (`5` divides `10`)
the machine halts in state `17`, while with `|A| = 10` it reaches the next round start with the
blocks `6`, `14`, `18`.
