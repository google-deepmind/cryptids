# 34-state Brocard machine

This binary Turing machine has **34 states** and 66 defined transitions. It halts only in state
`30` (`C8`) reading `1`; the other undefined cell (state `33`, `A`, reading `1`) is never reached.
It starts in state `0` (`TLx`) on the blank tape. Lean proves that it halts if and only if
Brocard's problem `n! + 1 = m^2` has a solution with `n > 7`, i.e. beyond the three known
solutions `n = 4, 5, 7` (Brocard 1876, Ramanujan 1913; Erdős conjectured there are no others;
none exist for `n ≤ 10^12`).

The machine was designed by Daniel Veljjanoski, with Claude (Anthropic) as assistant. Earlier
machines for the same problem: Charlie Reams's 61-state machine with a Lean proof
([`calr3/tinycryptids`](https://github.com/calr3/tinycryptids), November 2026) and a 43-state table
without a machine-checked proof in Tandi, Gonzalez-Hendrix and Brown, *Measuring Decidability as Related to Busy
Beaver Numbers* ([arXiv:2605.20215](https://arxiv.org/abs/2605.20215)). Improving that 43-state count is
Open Problem 6.2 of William Gasarch's SIGACT News Open Problems Column ([vol. 57, no. 3, September
2026](https://doi.org/10.1145/3848065.3848068)), which reports Jonathan Brown's conjecture that about
30 states may suffice; 34 improves the count.

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
* **Gate** (states `22`–`32`): a success counts the cells of `N`; fewer than eight (the known
  solutions `n = 5, 7`; `n = 6` fails) returns to the next round, eight halts.
* **Start**: the machine starts in `TLx` (state `0`) on the blank tape. Its never-read `0`-cell
  and those of `C1`–`C5` and `C7` write `1111 0 111` leftward, `A` (state `33`) writes the last
  cell, and the gate's return path (`Ns`, `Bs`, `ER`, `ER2`, `ER3`) brings the head to the end
  of `B`. A first version with 41 states, whose start was written by eight dedicated states, is
  in the history of the pull request.

As a one-line table in the style of the bbchallenge standard format, with the states `0`–`25`
written `A`–`Z` and `26`–`33` written `a`–`h` (the standard format itself covers only 26 states,
and the bbchallenge.org viewer ignores case, so this string is for reading, not for that viewer):

```
1LX0RM_0LC1LB_1RD1LC_0RK0RE_0RJ1RE_0RG1RF_1LH1RG_0LI1LH_1RJ1LI_0LB0RF_1RL1RK_0RA1LL_0RN1RM_1LO1RN_0LP0LQ_0LW1RM_0LR1LQ_1RS1LR_0RT0RM_0RU0RT_0LV0RU_0LV0LB_0LX1LW_1LY1LY_1LZ1LZ_0La1La_1Lb1Lb_1Ld1Lc_0Rf1Ld_1Lh1Le_0Rf---_0Rg1Rf_1RT1Rg_1Rf---
```

## Review entry points

- [`Brocard34.lean`](../../Cryptids/Brocard34.lean): the machine (loaded from `machine.txt`), the
  routine lemmas, and `halts_brocard34_iff_exists_tri`.
- [`Semantics/Brocard34.lean`](../../Cryptids/Semantics/Brocard34.lean):
  `halts_brocard34_iff_exists_square` and `halts_brocard34_iff_not_brocard`.

## Verification

`python3 verify.py` simulates the machine on the blank tape and checks the tape at every test
against `n!/8 + 1` (`n = 5, 6` at the default `--steps 250000`; the tests for `n = 7` and
`n = 8` start after about 360,000 and 23,000,000 steps), and that from a prepared tape a
planted triangular number halts in state `30` while a non-triangular one goes on to the next
test with the expected tape.
