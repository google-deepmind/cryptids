# 28-state Brocard machine

This binary Turing machine has **28 states** and 55 defined transitions. It halts only in state
`23` (`M0`) reading `0`, its one undefined cell. It starts in state `0` (`GO`) on the blank tape.
Lean proves that it halts if and only if Brocard's problem `n! + 1 = m^2` has a solution with
`n > 7`, i.e. beyond the three known solutions `n = 4, 5, 7` (Brocard 1876, Ramanujan 1913;
Erdős conjectured there are no others; none exist for `n ≤ 10^12`).

The machine was designed by Daniel Veljjanoski, with Claude (Anthropic) as assistant. Earlier
machines for the same problem: Charlie Reams's 61-state machine with a Lean proof
([`calr3/tinycryptids`](https://github.com/calr3/tinycryptids), November 2026) and a 43-state table
without a machine-checked proof in Tandi, Gonzalez-Hendrix and Brown, *Measuring Decidability as Related to Busy
Beaver Numbers* ([arXiv:2605.20215](https://arxiv.org/abs/2605.20215)). Improving that 43-state count is
Open Problem 6.2 of William Gasarch's SIGACT News Open Problems Column ([vol. 57, no. 3, September
2026](https://doi.org/10.1145/3848065.3848068)), which reports Jonathan Brown's conjecture that about
30 states may suffice; this machine has 28.

## How it works

Everything is in unary. The tape holds a block `N` of `n` cells, a separator, and a block `B`
that holds `n!/8` cells between rounds (`3` at `n = 4`). `n! + 1` is a square if and only if
`n!/8` is a triangular number `1 + 2 + ... + k` (`m = 2k + 1`), so a round multiplies `B` by
`n + 1`, grows `N` by one cell, and tests `B` by subtracting `1, 2, 3, ...`:

* **Multiply** (states `2`–`11`): a hole walks through `N`; for each cell the template `B` is
  copied once to the right end, cell by cell with a cursor hole. The merge leaves one extra cell.
* **Test** (states `1`, `12`–`19`): a hole walks right through `B`; a block `S` right of `B` holds
  the current chunk size with a hole walking left, and the blank beyond `S` acts as its hole, so
  `S` grows by one cell per wrap for free. At each wrap the machine checks whether `B` is
  exhausted.
* **Fail** (states `20`–`22`): `S` is erased and the last cell of `B` with it, which cancels the
  merge's extra cell.
* **Gate** (states `23`–`27`): a success walks left over `B` counting its ones modulo `4`.
  Residue `0` halts at the separator; residues `2` and `3` return to the next round. Since
  `32` divides `n!` for `n ≥ 8`, every success with `n ≥ 8` has residue `0`, while the known
  solutions have `7!/8 = 630 ≡ 2` and `5!/8 = 15 ≡ 3 (mod 4)` (`n = 6` fails the test).
* **Start**: the machine starts in `GO` (state `0`) on the blank tape. `GO` and the two cells
  that no run of the loop reads (`TLx` and `M1` reading `0`) steer the loop's own states to
  write `1111 0 111` in 46 steps and enter the loop in `LN1` on the blank left of `N`, the
  configuration every round passes through. This start was found by an exhaustive search over
  one-state starts; no start without a new state exists. Earlier versions with 41 and 34
  states, whose gate counted the cells of `N`, are in the history of the pull request.

As a one-line table in the style of the bbchallenge standard format, with the states `0`–`25`
written `A`–`Z` and `26`–`27` written `a`–`b` (the standard format itself covers only 26 states,
and the bbchallenge.org viewer ignores case, so this string is for reading, not for that viewer):

```
1LK1RD_0LK0RN_0LD1LC_1RE1LD_0RL0RF_0RK1RF_0RH1RG_1LI1RH_0LJ1LI_1RK1LJ_0LC0RG_1RM1RL_0RB1LM_0RO1RN_1LP1RO_0LQ0LR_0LX1RN_0LS1LR_1RT1LS_0RU0RN_0RV0RU_0LW0RV_0LW0LC_---1LY_1RA1LZ_0Rb1La_0Rb1LX_1RU1Rb
```

## Review entry points

- [`Brocard28.lean`](../../Cryptids/Brocard28.lean): the machine (loaded from `machine.txt`), the
  routine lemmas, and `halts_brocard28_iff_exists_tri`.
- [`Semantics/Brocard28.lean`](../../Cryptids/Semantics/Brocard28.lean):
  `halts_brocard28_iff_exists_square` and `halts_brocard28_iff_not_brocard`.

## Verification

`python3 verify.py` simulates the machine on the blank tape, checks that the 46-step start
produces `1111 0 111`, and checks the tape at every test against `n!/8 + 1` (`n = 5, 6` at the
default `--steps 250000`; the tests for `n = 7` and `n = 8` start after about 360,000 and
23,000,000 steps). It also checks that from a prepared tape a planted triangular number of cells
with residue `0` halts in state `23` while a non-triangular one goes on to the next test with
the expected tape.
