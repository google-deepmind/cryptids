# Stack Reductions (`StackReduction/`)

Fixed-arity reductions have the same number of blocks from start to finish. Many machines are not like that, and their number of blocks grows with time: this is the case for stack reductions.

The main example is [`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean), which we will use as a guiding example to explain what a stack reduction is and how it can be found.

If we run `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF` from a blank tape, we observe that one shape of configuration keeps coming back:
```
step       34:   0^inf 1 0 1^4 C> 0 1 0^inf
step       84:   0^inf 1 0 1^4 0 1^2 C> 0 1 0^inf
step     2504:   0^inf 1^12 0 1 C> 0 1^13 0 1^8 0 1^6 0 1^4 0 1^2 0^inf
```

The tape is always blocks of `1`s separated by single `0`s, with the head in state C on one of the separating `0`s. The number of blocks changes, so a fixed number of integers cannot describe it. Let's denote it by:
```
C([x1, ..., xm], [y1, ..., yn]) = 0^inf 1^x1 0 ... 0 1^xm C> 0 1^y1 0 ... 0 1^yn 0^inf
```

If we watch closely, we find more and more instances of `C(L, R)`:
```
step        8:   0^inf 1^3 C> 0 1 0^inf = C([3], [1])
step       19:   0^inf 1 0 1 C> 0 1^2 0^inf = C([1, 1], [2])
step       34:   0^inf 1 0 1^4 C> 0 1 0^inf = C([1, 4], [1])
step       47:   0^inf 1^2 0 1^2 C> 0 1^2 0^inf = C([2, 2], [2])
step       55:   0^inf 1^3 C> 0 1 0 1^2 0^inf = C([3], [1, 2])
step       66:   0^inf 1 0 1 C> 0 1^2 0 1^2 0^inf = C([1, 1], [2, 2])
step       84:   0^inf 1 0 1^4 0 1^2 C> 0 1 0^inf = C([1, 4, 2], [1])
step       92:   0^inf 1 0 1^5 C> 0 1 0 1 0^inf = C([1, 5], [1, 1])
```

Compared to fixed-arity reductions, we now have two things to keep track of: the lengths of the blocks, as with `a` and `b`, but also the number of blocks, which is new. Despite this, we can show the same three things:
1. The machine reaches an instance of `C(L, R)`: here, it reaches `C([3], [1])` in 8 steps.
2. Once the machine reaches one instance of `C(L, R)`, it will necessarily either reach a new instance of `C(L, R)` or halt: in other words, the family of configurations `C(L, R)` is closed.
3. To determine the next instance `C(L', R')` from `C(L, R)`, there exist simple rules:
```
Start: C([3], [1])
C([L, b, x + 2], [y, R]) -> C([L, b + 1, x], [y + 1, R])        if x >= 1
C([L, b, 2],     [y, R]) -> C([L, b + 1],    [1, y, R])
C([L, b, 1],     [y, R]) -> C([L, b, y + 2, R], [1])
C([1],           [y, R]) -> halt
```

Here `L` and `R` stand for the remaining blocks, possibly none. If there is no block `b`, then `b + 1` is a new block of length 1.

Once these three facts are proved, we can forget the machine entirely! Its halting problem is strictly equivalent to the halting problem of the `C([3], [1])` trajectory in this system of rules.

The rules only look at the blocks next to the head: they take from the nearest block, give to its neighbours, add or remove a block, and occasionally move all the blocks of one side to the other side. This is why each list is called a stack: like a stack of plates, the machine only ever touches the top.

`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF` is just one example: 166 BB(6) holdouts have been reduced to a problem of this kind, including machines previously studied by the community such as [`1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB`](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/Accelerations/M_1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_HHH0LB.lean) ([bbchallenge Wiki](https://wiki.bbchallenge.org/wiki/1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB)). Note that for most of these 166 machines, our Lean proof (`HasStackReduction`) only checks steps 1 and 2 (that the tape stays in the stack family), while explicit transition rules (step 3) are proved in our acceleration and halting/non-halting proofs. In `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`, the blocks are made of `1`s and are always separated by a single `0`. Other stack reductions swap the roles of `0` and `1`, use longer separators such as `00`, or mix a few separator lengths. In general, the formal definition allows one symbol to repeat arbitrarily many times while restricting the separator to finitely many lengths (at most 4). This restriction is essential: if all symbols could have arbitrary run lengths, then *any* tape could be written as a stack of alternating runs, and the definition would trivially hold for every Turing machine.

Stack reductions have enabled us to prove the halting or non-halting of three previously open machines in this repository: two halting ([`1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA`](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/Halt/M_1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_HHH0RA.lean) and [`1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB`](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/Halt/M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.lean)) and one non-halting ([`1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---`](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/NonHalt/M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH.lean)). For example, for [`1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_---0RA`](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/Halt/M_1RB1LE_1LC1RE_1LE1LD_1LC0LA_1RF0LA_HHH0RA.lean), each configuration at the right edge of the tape is a single stack of `0`-separated blocks of `1`s. After 11,120 stack steps (already past 10^33 raw Turing machine steps), the stack reaches the shape:
```
[1, 6, 6,  5, ..., 5,  3,  5, ..., 5,  3,  5, ..., 5,  ...]
            a0 times        a1 times        a2 times
```
with `a0 = 156,691`, `a1 = 3,931,792`, and `a2 = 19,317,108`. The proof shows that each cycle on this shape subtracts `9` from `a0` and `28` from `a1`. Running `17,410` cycles drains `a0` down to `1`, and two intermediate steps then switch the prefix `[1, 6, 6]` to `[1, 4]`, leaving `a1 = 3,444,302` entries equal to `5` in front. On this new shape, each cycle subtracts `9` from `a1`, so `382,700` cycles drain it down to `2`, at which point the machine directly hits its halting transition (well past 10^80 raw steps).

<!-- In a stacked reduction, both half-tapes organize into unbounded sequences $L, R \in \mathbb{N}^{\ast}$ of variable-length run blocks (such as $1^{a+1} 0^s$), so the machine's state space is an unbounded pair of integer stacks rather than a fixed-dimension tuple in $\mathbb{N}^d$. At each macro-step, the head performs modular arithmetic ($\bmod\ 2$, $\bmod\ 3$, or $\bmod\ 4$) on the active top counters adjacent to the head—incrementing stack tops or pushing fresh zero entries that increase stack depth—and periodically triggers a full-stack transfer sweep ($\tau$, $\sigma_D$, $\Delta$, $\tau_B$) that pours one stack onto the other in reverse order. This couples local Collatz-like residue branching at the head with arbitrarily deep historical memory stored across $L$ and $R$, while halting requires draining an entire stack down to $\varepsilon$ at a specific head residue. Thirteen holdouts in the table below satisfy `HasStackReduction` (nine `bbchallenge` Wiki holdouts, three Halving Tower holdouts, and one interleaved multi-separator pair-stack); the seven open problems below give explicit accelerated maps $(s_0, T)$ in this family.  -->

## Contents

This directory collects all **`28` stacked `BB(6)` holdout machines** (`9` Wiki and `19` novel reductions): `13` structural two-sided digit-stack reductions (`HasStackReduction`), `7` open stacked acceleration problems (`IsValidAcceleration`, `4` with `HighLevelState`), and `8` hard multi-layer stack potential cryptids (`IsStackCryptid`).

## Machines (28 Total: 9 Wiki, 19 Ours)

| Machine (`bbchallenge` RLE) | Origin | Proved Properties | State Space / Notes | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- |
| `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF` | Wiki | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF) | [`M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF.lean`](./M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF.lean) |
| `1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB` | Wiki | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB) | [`M_1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_HHH0LB.lean`](./M_1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_HHH0LB.lean) |
| `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` | Wiki | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA) | [`M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean`](./M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean) |
| `1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---` | Wiki | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---) (redirects to `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`: the same table restarted from its state `C`) | [`M_1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1REHHH.lean`](./M_1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1REHHH.lean) |
| `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` | Wiki | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---) (redirects to `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`: the same table restarted from its state `D`, mirrored) | [`M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean`](./M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean) |
| `1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---` | Wiki | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---) (redirects to `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`: the same table restarted from its state `E`) | [`M_1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RDHHH.lean`](./M_1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RDHHH.lean) |
| `1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB` | Wiki | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB) | [`M_1RB1RA_1LC0RC_HHH0LD_0LE0RF_1RE0RA_0LF1LB.lean`](./M_1RB1RA_1LC0RC_HHH0LD_0LE0RF_1RE0RA_0LF1LB.lean) |
| `1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF` | Wiki | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF) | [`M_1RB0RE_0RCHHH_1LD1LE_1LE1LD_1RF0LC_1RA1RF.lean`](./M_1RB0RE_0RCHHH_1LD1LE_1LE1LD_1RF0LC_1RA1RF.lean) |
| `1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD` | Wiki | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD) | [`M_1RBHHH_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD.lean`](./M_1RBHHH_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD.lean) |
| `1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD` | Ours (Novel) | `HasStackReduction` | — (Halving Tower family, E1 sibling of `1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB`) | [`M_1RB0LC_1LC0RE_1LD1LC_1LA1RD_HHH0RF_0LB0RD.lean`](./M_1RB0LC_1LC0RE_1LD1LC_1LA1RD_HHH0RF_0LB0RD.lean) |
| `1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA` | Ours (Novel) | `HasStackReduction` | — (Interleaved multi-separator pair-stack) | [`M_1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LDHHH_0LB1LA.lean`](./M_1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LDHHH_0LB1LA.lean) |
| `1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF` | Ours (Novel) | `HasStackReduction` | — (Halving Tower family; busycoq `Eqv_Select4_E3E4.v` merges `1RB---_0RC1RF_1RD0LD_1LA1LE_0RA0LB_1RE1LC` into this class) | [`M_1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RAHHH_1RB1LF.lean`](./M_1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RAHHH_1RB1LF.lean) |
| `1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF` | Ours (Novel) | `HasStackReduction` | — (Halving Tower family, E3 macro twin of `1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF`) | [`M_1RB1RC_1LC0LE_1RD1RC_1LB0RA_HHH0LF_1RD1LF.lean`](./M_1RB1RC_1LC0LE_1RD1RC_1LB0RA_HHH0LF_1RD1LF.lean) |
| `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF` | Ours (Novel) | `IsValidAcceleration` (`State`, `HighLevelState`) | $C(a, L, R) \to C_{\mathrm{HL}}(a, L) \in \mathbb{N} \times \mathbb{N}^{\ast}$ (from $C(0, [0], [1])$) | [`M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean`](./M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean) |
| `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB` | Ours (Novel) | `IsValidAcceleration` (`State`, `HighLevelState`) | $C(a, L, R) \to C_{\mathrm{HL}}(a, L, R) \in \mathbb{N} \times \mathbb{N}^{\ast} \times \mathbb{N}^{\ast}$ (from $C(1, \varepsilon, [0, 0])$) | [`M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB.lean`](./M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB.lean) |
| `1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA` | Ours (Novel) | `IsValidAcceleration` (`State`, `HighLevelState`) | $C, F \to F_{\mathrm{HL}}(a, b, L, r, R)$ (from $F(1, 0, \varepsilon, 0, \varepsilon)$) | [`M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.lean`](./M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.lean) |
| `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA` | Ours (Novel) | `IsValidAcceleration` (`State`, `HighLevelState`) | $D, E \to D_{\mathrm{HL}}(a, b, L) \in \mathbb{N}^2 \times \mathbb{N}^{\ast}$ (from $D(1, 0, \varepsilon, \varepsilon)$) | [`M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.lean`](./M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.lean) |
| `1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB` | Ours (Novel) | `IsValidAcceleration` | $B(P, u, R) \in \mathbb{N}^{\ast} \times \mathbb{N} \times \mathbb{N}^{\ast}$ (from $B(\varepsilon, 0, \varepsilon)$) | [`M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB.lean`](./M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB.lean) |
| `1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB` | Ours (Novel) | `IsValidAcceleration` (`State`, `HighLevelState`) | $C(a, L, R) \to C_{\mathrm{HL}}(a, L) \in \mathbb{N} \times \mathbb{N}^{\ast}$ (from $C(3, [0], \varepsilon)$) | [`M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean`](./M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean) |
| `1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA` | Ours (Novel) | `IsValidAcceleration` | $C_R(a, b, L, d, R)$ (from $C_R(0, 0, \varepsilon, 0, \varepsilon)$) | [`M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA.lean`](./M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA.lean) |
| `1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---` | Ours (Novel) | `IsStackCryptid` | Potential cryptid (multi-layer stack) | [`M_1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RBHHH.lean`](./M_1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RBHHH.lean) |
| `1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---` | Ours (Novel) | `IsStackCryptid` | Potential cryptid (multi-layer stack) | [`M_1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0REHHH.lean`](./M_1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0REHHH.lean) |
| `1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---` | Ours (Novel) | `IsStackCryptid` | Potential cryptid (multi-layer stack) | [`M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LBHHH.lean`](./M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LBHHH.lean) |
| `1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LE---` | Ours (Novel) | `IsStackCryptid` | Potential cryptid (multi-layer stack) | [`M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LEHHH.lean`](./M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LEHHH.lean) |
| `1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---` | Ours (Novel) | `IsStackCryptid` | Potential cryptid (multi-layer stack) | [`M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LAHHH.lean`](./M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LAHHH.lean) |
| `1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LC---` | Ours (Novel) | `IsStackCryptid` | Potential cryptid (multi-layer stack) | [`M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LCHHH.lean`](./M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LCHHH.lean) |
| `1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LA---` | Ours (Novel) | `IsStackCryptid` | Potential cryptid (multi-layer stack) | [`M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LAHHH.lean`](./M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LAHHH.lean) |
| `1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---` | Ours (Novel) | `IsStackCryptid` | Potential cryptid (multi-layer stack) | [`M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LEHHH.lean`](./M_1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LEHHH.lean) |

## Stacked Reduction Equations (7 Examples)

### [`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`](./M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean)

Over states $C(a, L, R)$ with $a \in \mathbb{N}$ and $L, R \in \mathbb{N}^{\ast}$, define the right-to-left stack transfer $\tau$ by

$$
\tau(a, L, \varepsilon) = C(a, L, [0]), \qquad \tau(a, L, [d] \cdot R) = \tau(d, [a] \cdot L, R).
$$

Starting from $s_0 = C(0, [0], [1])$ (after 19 TM steps),

$$
T(C(a, L, R)) = \begin{cases}
  \mathrm{Halt} & \text{if } a = 0 \text{ and } L = \varepsilon, \\
  \tau(b, L', \beta_1(\beta_1(R))) & \text{if } a = 0 \text{ and } L = [b] \cdot L', \\
  C(0, \varepsilon, [0] \cdot R) & \text{if } a = 1 \text{ and } L = \varepsilon, \\
  C(b + 1, L', [0] \cdot R) & \text{if } a = 1 \text{ and } L = [b] \cdot L', \\
  C(a - 2, \beta_1(L), \beta_1(R)) & \text{if } a \ge 2.
\end{cases}
$$

**High-level acceleration ($T_{\mathrm{HL}}$):** Restricting to the Poincaré return section $R = [0]$ eliminates the right stack completely over $C_{\mathrm{HL}}(a, L) := C(a, L, [0])$. With $\tau_{\mathrm{HL}}(a, L, \varepsilon) = C_{\mathrm{HL}}(a, L)$ and $\tau_{\mathrm{HL}}(a, L, [d] \cdot R) = \tau_{\mathrm{HL}}(d, [a] \cdot L, R)$, define $\mathcal{E}(a, L, R)$ for $k = \lfloor a/2 \rfloor$ and $R_1 = \beta_1^k(R)$ by

$$
\mathcal{E}(a, L, R) = \begin{cases}
  \mathrm{Halt} & \text{if } L = \varepsilon \text{ and } a \le 1, \\
  \tau_{\mathrm{HL}}(k - 1, \varepsilon, \beta_1^2(R_1)) & \text{if } L = \varepsilon \text{ and } a \ge 2 \text{ is even}, \\
  \mathcal{E}(k, \varepsilon, [0] \cdot R_1) & \text{if } L = \varepsilon \text{ and } a \ge 3 \text{ is odd}, \\
  \tau_{\mathrm{HL}}(b + k, L', \beta_1^2(R_1)) & \text{if } L = [b] \cdot L' \text{ and } a \text{ is even}, \\
  \mathcal{E}(b + k + 1, L', [0] \cdot R_1) & \text{if } L = [b] \cdot L' \text{ and } a \text{ is odd}.
\end{cases}
$$

Starting from $s_{0,\mathrm{HL}} = C_{\mathrm{HL}}(3, [0])$ (1 `next` step from $s_0$), $T_{\mathrm{HL}}(C_{\mathrm{HL}}(a, L)) = \mathcal{E}(a, L, [0])$.

### [`1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`](./M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB.lean)

Over states $C(a, L, R)$ with $a \in \mathbb{N}$ and $L, R \in \mathbb{N}^{\ast}$, define $\delta : \mathbb{N}^{\ast} \to \mathbb{N}^{\ast}$ by

$$
\delta(\varepsilon) = [0], \qquad \delta([d]) = [d + 1], \qquad \delta([d, r] \cdot S) = [r + d + 2] \cdot S,
$$

and write $(b, L') = (1, \varepsilon)$ if $L = \varepsilon$ and $(b, L') = (c + 2, L_1)$ if $L = [c] \cdot L_1$. Starting from $s_0 = C(1, \varepsilon, [0, 0])$ (after 12 TM steps), $T(C(a, L, R)) = \sigma(a, L, R)$, where

$$
\sigma(a, L, R) = \begin{cases}
  \mathrm{Halt} & \text{if } R = \varepsilon, \\
  C(b, L', [a + 2, 0]) & \text{if } R = [0], \\
  C(b, L', [a + r + 3] \cdot \delta(R')) & \text{if } R = [0, r] \cdot R', \\
  \sigma(0, [a] \cdot L, R') & \text{if } R = [1] \cdot R', \\
  C(a + 2, L, [r - 2] \cdot \delta(R')) & \text{if } R = [r] \cdot R' \text{ with } r \ge 2.
\end{cases}
$$

**High-level acceleration ($T_{\mathrm{HL}}$):** Contracting all $k = \lfloor r_0 / 2 \rfloor$ parity-peel steps of $r_0$ together with arbitrary leading $1$-scans defines $\sigma_{\mathrm{HL}}$ on $C_{\mathrm{HL}}(a, L, R) := C(a, L, R)$ from $s_{0,\mathrm{HL}} = C_{\mathrm{HL}}(1, \varepsilon, [0, 0])$ by $T_{\mathrm{HL}}(C_{\mathrm{HL}}(a, L, R)) = \sigma_{\mathrm{HL}}(a, L, R)$, where $\sigma_{\mathrm{HL}}(a, L, \varepsilon) = \mathrm{Halt}$ and, for $R = [r_0] \cdot R'$ with $k = \lfloor r_0 / 2 \rfloor$, $R_k = \delta^k(R')$, and $a_1 = a + 2k$:

$$
\sigma_{\mathrm{HL}}(a, L, [r_0] \cdot R') = \begin{cases}
  C_{\mathrm{HL}}(b, L', [a_1 + 2, 0]) & \text{if } r_0 \text{ is even and } R_k = \varepsilon, \\
  C_{\mathrm{HL}}(b, L', [a_1 + r + 3] \cdot \delta(R'')) & \text{if } r_0 \text{ is even and } R_k = [r] \cdot R'', \\
  \sigma_{\mathrm{HL}}(0, [a_1] \cdot L, R_k) & \text{if } r_0 \text{ is odd}.
\end{cases}
$$

### [`1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA`](./M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.lean)

Over states $C(a, b, L, r, R)$ and $F(a, b, L, r, R)$ with $a, b, r \in \mathbb{N}$ and $L, R \in \mathbb{N}^{\ast}$, write $(c^+, L') = (0, \varepsilon)$ if $L = \varepsilon$ and $(c^+, L') = (c + 1, L_1)$ if $L = [c] \cdot L_1$. Starting from $s_0 = F(1, 0, \varepsilon, 0, \varepsilon)$ (after 16 TM steps),

$$
\begin{aligned}
  T(C(a, b, L, r, R)) &= \begin{cases}
    \mathrm{Halt} & \text{if } a = 0 \text{ and } b = 0, \\
    F(b + 2, c^+, L', r, R) & \text{if } a = 0,\ b \ge 1 \text{ is odd}, \\
    C(b - 2, c^+, L', 0, [r + 1] \cdot R) & \text{if } a = 0,\ b \ge 2 \text{ is even}, \\
    F(a - 1, b, L, 0, [r] \cdot R) & \text{if } a \ge 1,
  \end{cases} \\
  T(F(a, b, L, r, R)) &= \begin{cases}
    C(a' + 2, b, L, 0, \varepsilon) & \text{if } r \text{ is even and } R = \varepsilon, \\
    F(0, b + 1, L, a', \varepsilon) & \text{if } r \text{ is even and } R = [0], \\
    F(a' + 3, b + 1, L, e, R') & \text{if } r \text{ is even},\ R = [0, e] \cdot R',\ a' \text{ even}, \\
    C(a' - 1, b + 1, L, 0, [e + 1] \cdot R') & \text{if } r \text{ is even},\ R = [0, e] \cdot R',\ a' \text{ odd}, \\
    F(0, b + 1, L, a', [d] \cdot R') & \text{if } r \text{ is even and } R = [d + 1] \cdot R', \\
    C(a', b, L, 0, [0]) & \text{if } r \text{ is odd and } R = \varepsilon, \\
    F(0, a' + 1, [b] \cdot L, e, R') & \text{if } r \text{ is odd and } R = [e] \cdot R',
  \end{cases}
\end{aligned}
$$

where $a' = a + 2\lfloor r/2 \rfloor$.

**High-level acceleration ($T_{\mathrm{HL}}$):** Eliminating $C$ yields a single-constructor system on $F_{\mathrm{HL}}(a, b, L, r, R) := F(a, b, L, r, R)$ starting from $s_{0,\mathrm{HL}} = F_{\mathrm{HL}}(1, 0, \varepsilon, 0, \varepsilon)$, where every $C(u, v, L, r, R)$ transition in $T(F(\dots))$ is contracted via

$$
\Xi(u, v, L, r, R) = \begin{cases}
  F_{\mathrm{HL}}(u - 1, v, L, 0, [r] \cdot R) & \text{if } u \ge 1, \\
  \mathrm{Halt} & \text{if } u = 0 \text{ and } (v = 0 \text{ or } (v = 2 \text{ and } L = \varepsilon)), \\
  F_{\mathrm{HL}}(v + 2, c^+, L', r, R) & \text{if } u = 0 \text{ and } v \ge 1 \text{ is odd}, \\
  \Xi(0, c + 1, L_1, 0, [r + 1] \cdot R) & \text{if } u = 0,\ v = 2,\ L = [c] \cdot L_1, \\
  F_{\mathrm{HL}}(v - 3, c^+, L', 0, [0, r + 1] \cdot R) & \text{if } u = 0 \text{ and } v \ge 4 \text{ is even}.
\end{cases}
$$

### [`1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA`](./M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.lean)

Over states $D(a, b, L, R)$ and $E(a, L, R)$ with $a, b \in \mathbb{N}$ and $L, R \in \mathbb{N}^{\ast}$, define

$$
\sigma_D(a, b, L, \varepsilon) = D(a, b, L, \varepsilon), \qquad \sigma_D(a, b, L, [d] \cdot R) = \sigma_D(d, a, [b] \cdot L, R).
$$

Starting from $s_0 = D(1, 0, \varepsilon, \varepsilon)$ (after 7 TM steps), with $k = \lfloor a/2 \rfloor$:

$$
\begin{aligned}
  T(D(a, b, L, R)) &= \begin{cases}
    E(b + k, L, [k]) & \text{if } a \text{ is even and } R = \varepsilon, \\
    E(b + k, L, [d + k + 1] \cdot R') & \text{if } a \text{ is even and } R = [d] \cdot R', \\
    D(k, b + k + 2, \beta_1(L), \varepsilon) & \text{if } a \text{ is odd and } R = \varepsilon, \\
    \sigma_D(d + k + 1, b + k + 2, \beta_1(L), R') & \text{if } a \text{ is odd and } R = [d] \cdot R',
  \end{cases} \\
  T(E(a, L, R)) &= \begin{cases}
    \mathrm{Halt} & \text{if } a = 0 \text{ and } L = \varepsilon, \\
    E(b, L', [0] \cdot R) & \text{if } a = 0 \text{ and } L = [b] \cdot L', \\
    \sigma_D(0, 1, [0], R) & \text{if } a = 1 \text{ and } L = \varepsilon, \\
    \sigma_D(0, b + 2, \beta_1(L'), R) & \text{if } a = 1 \text{ and } L = [b] \cdot L', \\
    D(a - 2, 0, \varepsilon, [0] \cdot R) & \text{if } a \ge 2 \text{ and } L = \varepsilon, \\
    D(a - 2, b + 1, L', [0] \cdot R) & \text{if } a \ge 2 \text{ and } L = [b] \cdot L'.
  \end{cases}
\end{aligned}
$$

**High-level acceleration ($T_{\mathrm{HL}}$):** Restricting to $R = \varepsilon$ eliminates both $E$ and the right stack $R$ on $D_{\mathrm{HL}}(a, b, L) := D(a, b, L, \varepsilon)$. With $\sigma_{D,\mathrm{HL}}(a, b, L, \varepsilon) = D_{\mathrm{HL}}(a, b, L)$ and $\sigma_{D,\mathrm{HL}}(a, b, L, [d] \cdot R) = \sigma_{D,\mathrm{HL}}(d, a, [b] \cdot L, R)$, define $\mathcal{R}_E(a, L, r_0, R')$ (writing $k_2 = \lfloor (a - 2)/2 \rfloor$ when $a \ge 2$) by

$$
\begin{aligned}
  \mathcal{R}_E(a, \varepsilon, r_0, R') &= \begin{cases}
    \mathrm{Halt} & \text{if } a = 0, \\
    \sigma_{D,\mathrm{HL}}(0, 1, [0], [r_0] \cdot R') & \text{if } a = 1, \\
    \sigma_{D,\mathrm{HL}}(k_2 + 1, k_2 + 2, [0], [r_0] \cdot R') & \text{if } a \ge 3 \text{ is odd}, \\
    \mathcal{R}_E(k_2, \varepsilon, k_2 + 1, [r_0] \cdot R') & \text{if } a \ge 2 \text{ is even},
  \end{cases} \\
  \mathcal{R}_E(a, [b] \cdot L', r_0, R') &= \begin{cases}
    \mathcal{R}_E(b, L', 0, [r_0] \cdot R') & \text{if } a = 0, \\
    \sigma_{D,\mathrm{HL}}(0, b + 2, \beta_1(L'), [r_0] \cdot R') & \text{if } a = 1, \\
    \sigma_{D,\mathrm{HL}}(k_2 + 1, b + k_2 + 3, \beta_1(L'), [r_0] \cdot R') & \text{if } a \ge 3 \text{ is odd}, \\
    \mathcal{R}_E(b + k_2 + 1, L', k_2 + 1, [r_0] \cdot R') & \text{if } a \ge 2 \text{ is even}.
  \end{cases}
\end{aligned}
$$

Starting from $s_{0,\mathrm{HL}} = D_{\mathrm{HL}}(1, 0, \varepsilon)$, with $k = \lfloor a/2 \rfloor$, $T_{\mathrm{HL}}(D_{\mathrm{HL}}(a, b, L)) = D_{\mathrm{HL}}(k, b + k + 2, \beta_1(L))$ if $a$ is odd and $\mathcal{R}_E(b + k, L, k, \varepsilon)$ if $a$ is even.

### [`1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB`](./M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB.lean)

Over states $B(P, u, R)$ with $P, R \in \mathbb{N}^{\ast}$ and $u \in \mathbb{N}$ (where $P$ holds strictly positive upper stack entries shifted by $1$ above a bottom register $u$), define the stack-increment and transfer helpers:

$$
\begin{aligned}
  \pi_k(\varepsilon, u) &= (\varepsilon, u + k), & \pi_k([p] \cdot P, u) &= ([p + k] \cdot P, u), \\
  \gamma(\varepsilon, u) &= ([u + 1], 0), & \gamma([p] \cdot P, u) &= ([p + 2] \cdot P', u') \quad \text{where } (P', u') = \pi_1(P, u), \\
  \Delta(a, P, u, \varepsilon) &= B([a + 2] \cdot P, u, \varepsilon), & \Delta(a, P, u, [r] \cdot R) &= \Delta(r, [a] \cdot P', u', R) \quad \text{where } (P', u') = \pi_1(P, u).
\end{aligned}
$$

Starting from $s_0 = B(\varepsilon, 0, \varepsilon)$ (after 1 TM step), $T(B(P, u, \varepsilon)) = \Pi(P, u, 0, \varepsilon)$ and $T(B(P, u, [r] \cdot R)) = \Pi(P, u, r + 1, R)$, where

$$
\begin{aligned}
  \Pi(\varepsilon, u, d, R) &= \begin{cases}
    \Delta(d, \varepsilon, 0, R) & \text{if } u = 0, \\
    B([0, 0], 0, R) & \text{if } u = 1,\ d = 0, \\
    B([1, 0], 0, R) & \text{if } u = 1,\ d = 1, \\
    \Delta(d - 2, [0], 0, R) & \text{if } u = 1,\ d \ge 2, \\
    \mathrm{Halt} & \text{if } u = 2, \\
    \Delta(d - 1, [u - 3], 0, R) & \text{if } u \ge 3,\ d \ge 1, \\
    B([1, 1], m, \beta_1^m(R)) & \text{if } u = 2m + 4,\ d = 0, \\
    B([1, 0], m, \varepsilon) & \text{if } u = 2m + 3,\ d = 0,\ \beta_1^m(R) = \varepsilon, \\
    \Delta(r_2, [m + 3], 1, T_2) & \text{if } u = 2m + 3,\ d = 0,\ \beta_1^m(R) = [r_2] \cdot T_2,
  \end{cases} \\
  \Pi([p] \cdot P, u, d, R) &= \begin{cases}
    B([0] \cdot P_1, u_1, R) & \text{if } p = 0,\ d = 0,\ (P_1, u_1) = \gamma(P, u), \\
    B([1] \cdot P_1, u_1, R) & \text{if } p = 0,\ d = 1,\ (P_1, u_1) = \gamma(P, u), \\
    \Delta(d - 2, P_1, u_1, R) & \text{if } p = 0,\ d \ge 2,\ (P_1, u_1) = \gamma(P, u), \\
    \Pi(P, u, 0, [d] \cdot R) & \text{if } p = 1, \\
    \Delta(d - 1, [b] \cdot P_1, u_1, R) & \text{if } p = b + 2,\ d \ge 1,\ (P_1, u_1) = \pi_1(P, u), \\
    B([1, 1] \cdot P_3, u_3, R_2) & \text{if } p = 2m + 3,\ d = 0, \\
    B([1, 0] \cdot P_3, u_3, \varepsilon) & \text{if } p = 2m + 2,\ d = 0,\ R_2 = \varepsilon, \\
    \Delta(r_2, [u_2 + 4], 1, T_2) & \text{if } p = 2m + 2,\ d = 0,\ R_2 = [r_2] \cdot T_2,\ P_2 = \varepsilon, \\
    \Delta(r_2, [q + 5] \cdot P_4, u_4, T_2) & \text{if } p = 2m + 2,\ d = 0,\ R_2 = [r_2] \cdot T_2,\ P_2 = [q] \cdot Q,
  \end{cases}
\end{aligned}
$$

with $R_2 = \beta_1^m(R)$, $(P_2, u_2) = \pi_m(P, u)$, $(P_3, u_3) = \pi_1(P_2, u_2)$, and $(P_4, u_4) = \pi_2(Q, u_2)$.

### [`1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB`](./M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean)

Over states $C(a, L, R)$ with $a \in \mathbb{N}$ and $L, R \in \mathbb{N}^{\ast}$, define

$$
\tau_B(\varepsilon, \varepsilon) = C(0, \varepsilon, \varepsilon), \qquad \tau_B([a] \cdot L, \varepsilon) = C(a + 1, L, \varepsilon), \qquad \tau_B(L, [d] \cdot R) = \tau_B([d] \cdot \beta_1(L), R).
$$

Write $(r, R') = (0, \varepsilon)$ when $R = \varepsilon$ and $(r, R') = (d, R_1)$ when $R = [d] \cdot R_1$. Starting from $s_0 = C(3, [0], \varepsilon)$ (after 19 TM steps),

$$
T(C(a, L, R)) = \begin{cases}
  \mathrm{Halt} & \text{if } a = 0 \text{ and } L = \varepsilon, \\
  \tau_B([r + 2, 0] \cdot L', R') & \text{if } a = 0 \text{ and } L = [0] \cdot L', \\
  \tau_B([b] \cdot L', [r + 2] \cdot R') & \text{if } a = 0 \text{ and } L = [b + 1] \cdot L', \\
  \tau_B(\beta_1^k(L), [r + k + 2] \cdot R') & \text{if } a = 2k + 1, \\
  C(k, \varepsilon, [0, r + k] \cdot R') & \text{if } a = 2k + 2 \text{ and } L = \varepsilon, \\
  C(b + k + 1, L', [0, r + k] \cdot R') & \text{if } a = 2k + 2 \text{ and } L = [b] \cdot L'.
\end{cases}
$$

**High-level acceleration ($T_{\mathrm{HL}}$):** Restricting to $R = \varepsilon$ eliminates the right stack $R$ on $C_{\mathrm{HL}}(a, L) := C(a, L, \varepsilon)$. With $\tau_{B,\mathrm{HL}}(\varepsilon, \varepsilon) = C_{\mathrm{HL}}(0, \varepsilon)$, $\tau_{B,\mathrm{HL}}([a] \cdot L, \varepsilon) = C_{\mathrm{HL}}(a + 1, L)$, and $\tau_{B,\mathrm{HL}}(L, [d] \cdot R) = \tau_{B,\mathrm{HL}}([d] \cdot \beta_1(L), R)$, define $\mathcal{U}(a, L, R)$ (writing $(r, R') = (0, \varepsilon)$ when $R = \varepsilon$ and $(d, R_1)$ when $R = [d] \cdot R_1$) by replacing $\tau_B$ with $\tau_{B,\mathrm{HL}}$ and the two $C(\dots)$ branches on $a = 2k + 2$ with recursive calls $\mathcal{U}(k, \varepsilon, [0, r + k] \cdot R')$ and $\mathcal{U}(b + k + 1, L', [0, r + k] \cdot R')$. Starting from $s_{0,\mathrm{HL}} = C_{\mathrm{HL}}(3, [0])$, $T_{\mathrm{HL}}(C_{\mathrm{HL}}(a, L)) = \mathcal{U}(a, L, \varepsilon)$.

### [`1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA`](./M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA.lean)

Over states $C_R(a, b, L, d, R)$ with $a, b, d \in \mathbb{N}$ and $L, R \in \mathbb{N}^{\ast}$, define $\hat{\beta}_1(\varepsilon) = (0, \varepsilon)$, $\hat{\beta}_1([r] \cdot S) = (r + 1, S)$, $\hat{\beta}_2(\varepsilon) = (1, \varepsilon)$, and $\hat{\beta}_2([c] \cdot S) = (c + 2, S)$. Let

$$
\begin{aligned}
  \sigma_0(b, d, L, R) &= \begin{cases}
    C_R(d + 1, c, L', r, R') & \text{if } b = 0, \\
    C_R(0, c, L', d + 1, R) & \text{if } b = 1, \\
    C_R(b - 2, c, L', 0, [d] \cdot R) & \text{if } b \ge 2,
  \end{cases} \quad (c, L') = \hat{\beta}_2(L),\ (r, R') = \hat{\beta}_1(R), \\
  \sigma_1(b, L, R) &= \begin{cases}
    C_R(0, b + 5, L, 0, \varepsilon) & \text{if } R = \varepsilon \text{ or } R = [0], \\
    C_R(r_2 + 1, b + 5, L, r, R') & \text{if } R = [0, r_2] \cdot R_3,\ (r, R') = \hat{\beta}_1(R_3), \\
    C_R(e, b + 5, L, r, R') & \text{if } R = [e + 1] \cdot R_2,\ (r, R') = \hat{\beta}_1(R_2).
  \end{cases}
\end{aligned}
$$

Starting from $s_0 = C_R(0, 0, \varepsilon, 0, \varepsilon)$ (after 5 TM steps), with $q = \lfloor a/3 \rfloor$, $b_1 = b + 2q$, and $R_1 = \beta_1^q(R)$:

$$
T(C_R(a, b, L, d, R)) = \begin{cases}
  \sigma_0(b_1, 0, L, R_1) & \text{if } d = 0 \text{ and } a \equiv 0 \pmod{3}, \\
  \sigma_1(b_1, L, R_1) & \text{if } d = 0 \text{ and } a \equiv 1 \pmod{3}, \\
  C_R(0, b_1 + 2, L, r + 1, R') & \text{if } d = 0,\ a \equiv 2 \pmod{3},\ (r, R') = \hat{\beta}_1(R_1), \\
  \sigma_0(b, d, L, R) & \text{if } d \ge 1 \text{ and } a = 0, \\
  \mathrm{Halt} & \text{if } d \ge 1 \text{ and } a = 1, \\
  C_R(d, a - 1, [b] \cdot L, r, R') & \text{if } d \ge 1,\ a \ge 2,\ (r, R') = \hat{\beta}_1(R).
\end{cases}
$$

---
