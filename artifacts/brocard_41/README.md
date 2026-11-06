# 41-state Brocard machine

This binary Turing machine has **41 states** and 72 defined transitions. It halts only in state
`38` (`C8`) reading `1`; the other nine undefined cells (the start states `0`–`7` reading `1`,
state `19` (`TLx`) reading `0`) are never reached. It starts in state 0 on the blank tape. Lean proves that it
halts if and only if Brocard's problem `n! + 1 = m^2` has a solution with `n > 7`, i.e. beyond
the three known solutions `n = 4, 5, 7` (Brocard 1876, Ramanujan 1913; Erdős conjectured there
are no others; none exist for `n ≤ 10^12`).

The machine was designed by Daniel Veljjanoski, with Claude (Anthropic) as assistant. Earlier
machines for the same problem: Charlie Reams's 61-state machine with a Lean proof
([`calr3/tinycryptids`](https://github.com/calr3/tinycryptids), November 2026) and a 43-state table
without a machine-checked proof in Tandi, Gonzalez-Hendrix and Brown, *Measuring Decidability as Related to Busy
Beaver Numbers* ([arXiv:2605.20215](https://arxiv.org/abs/2605.20215)).

## How it works

Everything is in unary. The tape holds a block `N` of `n` cells, a separator, and a block `B`
that holds `n!/8` cells between rounds (`3` at `n = 4`). `n! + 1` is a square if and only if
`n!/8` is a triangular number `1 + 2 + ... + k` (`m = 2k + 1`), so a round multiplies `B` by
`n + 1`, grows `N` by one cell, and tests `B` by subtracting `1, 2, 3, ...`:

* **Multiply** (states `8`–`17`): a hole walks through `N`; for each cell the template `B` is
  copied once to the right end, cell by cell with a cursor hole. The merge leaves one extra cell.
* **Test** (states `18`–`26`): a hole walks right through `B`; a block `S` right of `B` holds
  the current chunk size with a hole walking left, and the blank beyond `S` acts as its hole, so
  `S` grows by one cell per wrap for free. At each wrap the machine checks whether `B` is
  exhausted.
* **Fail** (states `27`–`29`): `S` is erased and the last cell of `B` with it, which cancels the
  merge's extra cell.
* **Gate** (states `30`–`40`): a success counts the cells of `N`; fewer than eight (the known
  solutions `n = 5, 7`; `n = 6` fails) returns to the next round, eight halts.
* **Start** (states `0`–`7`): writes `1111 0 111`.

In bbchallenge standard text (states `A`–`Z`, then `a`–`o`):

```
1LB---_1LC---_1LD---_0LE---_1LF---_1LG---_1LH---_1Rn---_0LJ1LI_1RK1LJ_0RR0RL_0RQ1RL_0RN1RM_1LO1RN_0LP1LO_1RQ1LP_0LI0RM_1RS1RR_0RT1LS_---0RU_0RV1RU_1LW1RV_0LX0LY_0Le1RU_0LZ1LY_1Ra1LZ_0Rb0RU_0Rc0Rb_0Ld0Rc_0Ld0LI_0Lf1Le_0Rn1Lg_0Rn1Lh_0Rn1Li_0Rn1Lj_0Rn1Lk_0Rn1Ll_0Rn1Lm_0Rn---_0Ro1Rn_1Rb1Ro
```

## Review entry points

- [`Brocard41.lean`](../../Cryptids/Brocard41.lean): the machine (loaded from `machine.txt`), the
  routine lemmas, and `halts_brocard41_iff_exists_tri`.
- [`Semantics/Brocard41.lean`](../../Cryptids/Semantics/Brocard41.lean):
  `halts_brocard41_iff_exists_square` and `halts_brocard41_iff_not_brocard`.

## Verification

`python3 verify.py` simulates the machine on the blank tape and checks the tape at every test
against `n!/8 + 1` (`n = 5, 6` at the default `--steps 250000`; the tests for `n = 7` and
`n = 8` start after about 360,000 and 23,000,000 steps), and that from a prepared tape a
planted triangular number halts in state `38` while a non-triangular one goes on to the next
test with the expected tape.
