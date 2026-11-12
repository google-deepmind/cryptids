# 27-state Brocard machine

This binary Turing machine has **27 states** and 53 defined transitions. It halts only in state
`22` (`M0`) reading `0`, its one undefined cell. It starts in state `0` (`TLx`) on the blank tape.
Lean proves that it halts if and only if Brocard's problem `n! + 1 = m^2` has a solution with
`n > 7`, i.e. beyond the three known solutions `n = 4, 5, 7` (Brocard 1876, Ramanujan 1913;
Erdős conjectured there are no others; none exist for `n ≤ 10^12`).

The machine was designed by Daniel Veljjanoski, with Claude (Anthropic) as assistant. Earlier
machines for the same problem: the 51-state machine of Joseph Jabbour and Ralph Razzouk with a
Lean proof ([`ralphrazzouk/busybeaver`](https://github.com/ralphrazzouk/busybeaver),
September 2026), Charlie Reams's 61-state machine with a Lean proof
([`calr3/tinycryptids`](https://github.com/calr3/tinycryptids), November 2026) and a 43-state table
without a machine-checked proof in Tandi, Gonzalez-Hendrix and Brown, *Measuring Decidability as Related to Busy
Beaver Numbers* ([arXiv:2605.20215](https://arxiv.org/abs/2605.20215)). Improving that 43-state count is
Open Problem 6.2 of William Gasarch's SIGACT News Open Problems Column ([vol. 57, no. 3, September
2026](https://doi.org/10.1145/3848065.3848068)), which reports Jonathan Brown's conjecture that about
30 states may suffice; this machine has 27.

## How it works

Everything is in unary. The tape holds a block `N` of `n` cells, a separator, and a block `B`
that holds `n!/8` cells between rounds (`3` at `n = 4`). `n! + 1` is a square if and only if
`n!/8` is a triangular number `1 + 2 + ... + k` (`m = 2k + 1`), so a round multiplies `B` by
`n + 1`, grows `N` by one cell, and tests `B` by subtracting `1, 2, 3, ...`:

* **Multiply** (states `1`–`10`): a hole walks through `N`; for each cell the template `B` is
  copied once to the right end, cell by cell with a cursor hole. The merge leaves one extra cell.
* **Test** (states `0`, `11`–`18`): a hole walks right through `B`; a block `S` right of `B` holds
  the current chunk size with a hole walking left, and the blank beyond `S` acts as its hole, so
  `S` grows by one cell per wrap for free. At each wrap the machine checks whether `B` is
  exhausted.
* **Fail** (states `19`–`21`): `S` is erased and the last cell of `B` with it, which cancels the
  merge's extra cell.
* **Gate** (states `22`–`26`): a success walks left over `B` counting its ones modulo `4`.
  Residue `0` halts at the separator; residues `2` and `3` return to the next round. Since
  `32` divides `n!` for `n ≥ 8`, every success with `n ≥ 8` has residue `0`, while the known
  solutions have `7!/8 = 630 ≡ 2`, `5!/8 = 15 ≡ 3` and `4!/8 = 3 ≡ 3 (mod 4)` (`n = 6` fails
  the test). Residue `1` never occurs at a success, so `M1` reading `0` is never used; it holds
  the same move as `M2` and `M3` reading `0`.
* **Start**: there is no start state. The machine starts in `TLx` (state `0`), the state that
  begins a test. In the loop `TLx` only ever reads a `1`; reading `0` it writes a `1` and enters
  `LN0`. The loop's own states then build `1111 0 1111` and reach the test of round `4` after
  45 steps. That test succeeds (`4! + 1 = 25`), the gate suppresses it, and 119 steps after the
  start the machine is in `LN1` on the blank left of `1111 0 111`, the configuration every round
  passes through.

The machine is the 28-state machine `brocard_28` of an earlier version of this repository without
its start state `GO`; besides the renumbering, only the two cells `TLx` and `M1` reading `0`
differ. The start was found by a search over the 27 possible start states and the values of the
loop's two unused cells (`TLx` and `M1` reading `0`); it uses only the first. An earlier search
had missed it because it allowed at most 8 ones on the tape before the loop is entered, and
this start reaches 11, during the test of round `4`. Versions with 41 and 34 states, whose gate
counted the cells of `N`, are in the history of pull request 27.

As a one-line table in the style of the bbchallenge standard format, with the states `0`–`25`
written `A`–`Z` and `26` written `a` (the standard format itself covers only 26 states, and the
bbchallenge.org viewer ignores case, so this string is for reading, not for that viewer):

```
1LB0RM_0LC1LB_1RD1LC_0RK0RE_0RJ1RE_0RG1RF_1LH1RG_0LI1LH_1RJ1LI_0LB0RF_1RL1RK_0RA1LL_0RN1RM_1LO1RN_0LP0LQ_0LW1RM_0LR1LQ_1RS1LR_0RT0RM_0RU0RT_0LV0RU_0LV0LB_---1LX_0Ra1LY_0Ra1LZ_0Ra1LW_1RT1Ra
```

## Review entry points

- [`Brocard27.lean`](../../Cryptids/Brocard27.lean): the machine (loaded from `machine.txt`), the
  routine lemmas, and `halts_brocard27_iff_exists_tri`.
- [`Semantics/Brocard27.lean`](../../Cryptids/Semantics/Brocard27.lean):
  `halts_brocard27_iff_exists_square` and `halts_brocard27_iff_not_brocard`.

## Verification

`python3 verify.py` simulates the machine on the blank tape, checks that the 45-step start ends
at the test of round `4`, and checks the tape at every test against `n!/8 + 1` (`n = 4, 5, 6` at
the default `--steps 250000`; the tests for `n = 7` and `n = 8` start after about 360,000 and
23,000,000 steps). It also checks that from a prepared tape a planted triangular number of cells
with residue `0` halts in state `22` while a non-triangular one goes on to the next test with
the expected tape.
