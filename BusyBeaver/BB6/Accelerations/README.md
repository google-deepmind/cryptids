# `BB(6)` Stacked, Odometer, and Transducer Accelerations (`BusyBeaver/BB6/Accelerations/`)

This directory contains formal Lean 4 specifications and kernel-verified reductions for 29 `BB(6)` (6-state, 2-symbol) holdout Turing machines whose blank-tape dynamics reduce to unbounded digit-stack, mixed-radix odometer, or bidirectional finite-state transducer maps rather than bounded-counter piecewise-affine maps:

1. **9 Community-Documented `bbchallenge` Wiki Machines** formalized under the three structural reduction predicates defined in [`BusyBeaver/Defs.lean`](../../Defs.lean)—`HasStackReduction` (6 machines), `HasOdometerReduction` (2 machines: Beaver Math Olympiad Problems 10 and 11), and `HasTransducerReduction` (1 machine: *Bell eats counter*).
2. **20 Open `BB(6)` Acceleration Problems** certified via `IsValidAcceleration` and `IsHalt target ↔ CollatzHalts next start` (with [`1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`](./M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH.lean) additionally proved under `HasOdometerReduction`). Each open problem below states the exact initial state $s_0$ (`start`) and accelerated transition map $T$ (`next`) verified in Lean 4: the corresponding Turing machine halts from the blank tape if and only if iterating $T$ from $s_0$ eventually reaches $\text{Halt}$ (`none`).

## Structural Reduction Predicates ([`BusyBeaver/Defs.lean`](../../Defs.lean))

| Predicate | Dynamical Family |
| :--- | :--- |
| `HasStackReduction M` | Closed two-sided variable-length digit-stack system (`StackTuple`, `IsValidStackModes`) with non-blank/blank block encodings (`stackDigit`, `stackSepLen`), non-trivial stack reachability, and certified `ReachesPlus` closure from `init []`. |
| `HasOdometerReduction M` | Closed mixed-radix odometer stack + bit-stream system (`evalOdomR` / `evalOdomL`) with certified decrement (`cap (dec stk) = cap stk - 1`), zero-capacity drain (`drain`), reflection, and `ReachesPlus` closure from `init []`. |
| `HasTransducerReduction M` | Closed bidirectional macro-word transducer (`IsValidTransducerModes`, `iterTransducerMacro`) over prefix-free block alphabets (`kraftSum`) with certified left-to-right and right-to-left unbounded sweeps and `ReachesPlus` closure from `init []`. |

## Formalized `bbchallenge` Wiki Machines (9 Machines)

| Machine (`bbchallenge` RLE) | Family | Proved Properties | Wiki Page | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- |
| `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF` | Stacked | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF) | [`M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF.lean`](./M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF.lean) |
| `1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB` | Stacked | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB) | [`M_1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_HHH0LB.lean`](./M_1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_HHH0LB.lean) |
| `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` | Stacked | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA) | [`M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean`](./M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean) |
| `1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB` | Stacked | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RA_1LC0RC_---0LD_0LE0RF_1RE0RA_0LF1LB) | [`M_1RB1RA_1LC0RC_HHH0LD_0LE0RF_1RE0RA_0LF1LB.lean`](./M_1RB1RA_1LC0RC_HHH0LD_0LE0RF_1RE0RA_0LF1LB.lean) |
| `1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF` | Stacked | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF) | [`M_1RB0RE_0RCHHH_1LD1LE_1LE1LD_1RF0LC_1RA1RF.lean`](./M_1RB0RE_0RCHHH_1LD1LE_1LE1LD_1RF0LC_1RA1RF.lean) |
| `1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD` | Stacked | `HasStackReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD) | [`M_1RBHHH_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD.lean`](./M_1RBHHH_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD.lean) |
| `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` | Odometer | `HasOdometerReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---) ([BMO Problem 10](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad)) | [`M_1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RCHHH.lean`](./M_1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RCHHH.lean) |
| `1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB` | Odometer | `HasOdometerReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_0LD---) ([BMO Problem 11](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad), state-relabeled) | [`M_1RB0LD_0RCHHH_1LD0RF_0LE0RA_0RA1LF_0LA1LB.lean`](./M_1RB0LD_0RCHHH_1LD0RF_0LE0RA_0RA1LF_0LA1LB.lean) |
| `1RB0LD_0RC---_0LD0RF_1LE1LD_0LA0RD_0RB1RA` | Transducer | `HasTransducerReduction` | [Wiki (`Bell_eats_counter`)](https://wiki.bbchallenge.org/wiki/Bell_eats_counter) (state-relabeled) | [`M_1RB0LD_0RCHHH_0LD0RF_1LE1LD_0LA0RD_0RB1RA.lean`](./M_1RB0LD_0RCHHH_0LD0RF_1LE1LD_0LA0RD_0RB1RA.lean) |

## Open `BB(6)` Acceleration Problems (20 Machines)

| Machine (`bbchallenge` RLE) | Family | State Space | Initial State $s_0$ | Proved Properties | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF` | Stacked | $C(a, L, R) \in \mathbb{N} \times \mathbb{N}^* \times \mathbb{N}^*$ | $C(0, [0], [1])$ | `IsValidAcceleration` | [`M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean`](./M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean) |
| `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB` | Stacked | $C(a, L, R) \in \mathbb{N} \times \mathbb{N}^* \times \mathbb{N}^*$ | $C(1, [], [0, 0])$ | `IsValidAcceleration` | [`M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB.lean`](./M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB.lean) |
| `1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA` | Stacked | $C(a, b, L, r, R),\ F(a, b, L, r, R)$ | $F(1, 0, [], 0, [])$ | `IsValidAcceleration` | [`M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.lean`](./M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.lean) |
| `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA` | Stacked | $D(a, b, L, R),\ E(a, L, R)$ | $D(1, 0, [], [])$ | `IsValidAcceleration` | [`M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.lean`](./M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.lean) |
| `1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB` | Stacked | $B(P, u, R) \in \mathbb{N}^* \times \mathbb{N} \times \mathbb{N}^*$ | $B([], 0, [])$ | `IsValidAcceleration` | [`M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB.lean`](./M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB.lean) |
| `1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB` | Stacked | $C(a, L, R) \in \mathbb{N} \times \mathbb{N}^* \times \mathbb{N}^*$ | $C(3, [0], [])$ | `IsValidAcceleration` | [`M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean`](./M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean) |
| `1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA` | Stacked | $C_R(a, b, L, d, R)$ | $C_R(0, 0, [], 0, [])$ | `IsValidAcceleration` | [`M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA.lean`](./M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA.lean) |
| `1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA` | Odometer | $B(L, R) \in \mathbb{N}^* \times \mathbb{N}^*$ | $B([], [0, 1])$ | `IsValidAcceleration` | [`M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA.lean`](./M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA.lean) |
| `1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD` | Odometer | $E(a, L, d, R)$ | $E(1, [], 0, [])$ | `IsValidAcceleration` | [`M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD.lean`](./M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD.lean) |
| `1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---` | Odometer | $(L, w) \in \lbrace L_0, L_1, L_2 \rbrace^* \times \lbrace 0, 1 \rbrace^*$ | $([], [])$ | `HasOdometerReduction`, `IsValidAcceleration` | [`M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH.lean`](./M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH.lean) |
| `1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD` | Odometer | $B(L, E, c) \in \mathbb{N}^* \times \mathbb{N}^* \times \mathbb{N}$ | $B([0], [], 1)$ | `IsValidAcceleration` | [`M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD.lean`](./M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD.lean) |
| `1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA` | Odometer | $E(d, R) \in \mathbb{N} \times \mathbb{N}^*$ | $E(0, [0])$ | `IsValidAcceleration` | [`M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA.lean`](./M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA.lean) |
| `1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---` | Odometer | $E(R) \in \mathbb{N}^*$ | $E([])$ | `IsValidAcceleration` | [`M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH.lean`](./M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH.lean) |
| `1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD` | Odometer | $E_L(a, L, d, R),\ E_0(L, R)$ | $E_L(1, [], 1, [])$ | `IsValidAcceleration` | [`M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD.lean`](./M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD.lean) |
| `1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF` | Transducer | $E(L, R) \in \mathbb{N}^* \times \mathbb{N}^*$ | $E([1], [])$ | `IsValidAcceleration` | [`M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF.lean`](./M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF.lean) |
| `1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC` | Transducer | $E(L, R) \in (\mathbb{N} \times \lbrace 0, 1 \rbrace)^* \times (\mathbb{N} \times \lbrace 0, 1 \rbrace)^*$ | $E([(1, 0)], [(0, 0)])$ | `IsValidAcceleration` | [`M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean`](./M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean) |
| `1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC` | Transducer | $B(L, d, R) \in \mathbb{N}^* \times \mathbb{N} \times \mathbb{N}^*$ | $B([0], 0, [])$ | `IsValidAcceleration` | [`M_1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_HHH1LC.lean`](./M_1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_HHH1LC.lean) |
| `1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---` | Transducer | $D(L, R) \in \mathbb{N}^* \times \mathbb{N}^*$ | $D([1], [])$ | `IsValidAcceleration` | [`M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH.lean`](./M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH.lean) |
| `1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB` | Transducer | $D(L, R) \in (\mathbb{N} \times \lbrace 0, 1 \rbrace)^* \times (\mathbb{N} \times \mathbb{Z}_3)^*$ | $D([], [(1, 0)])$ | `IsValidAcceleration` | [`M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean`](./M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean) |
| `1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA` | Transducer | $M_0(L, R) \in (\mathbb{N} \times \lbrace 1, 2, 3, 4 \rbrace)^* \times (\mathbb{N} \times \lbrace 1, 2, 3, 4 \rbrace)^*$ | $M_0([(0, 1), (0, 1)], [(1, 1)])$ | `IsValidAcceleration` | [`M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean`](./M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean) |

---

## Notation

For lists over $\mathbb{N}$ (written $[]$ for empty and $x :: X$ for cons, with $0^k$ denoting $k$ copies of $0$), we write:

$$
\beta_k([]) = [k - 1] \quad (k \ge 1), \qquad \beta_k(x :: X) = (x + k) :: X, \qquad \iota([]) = [], \qquad \iota(x :: X) = (x + 1) :: X,
$$

and $\beta_1^m$ for the $m$-fold iterate of $\beta_1$ (`bumpHead`). On tape encodings, $\mathrm{enc}_1([a_0, \dots, a_{m-1}]) := 1^{a_0+1} 0 \cdots 1^{a_{m-1}+1} 0 \, 0^\infty$ and $\mathrm{enc}_0([k_0, \dots, k_{m-1}]) := 0^{k_0} 1 \cdots 0^{k_{m-1}} 1 \, 0^\infty$.

---

## 1. Stacked Reductions

### 1.1 [`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`](./M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean)

For $a \in \mathbb{N}$ and $L, R \in \mathbb{N}^*$, let $C(a, L, R) := \mathrm{enc}_1(a :: L) \ \mathrm{C}{>} \ 0 \, \mathrm{enc}_1(R)$. Define $\tau(a, L, []) = C(a, L, [0])$ and $\tau(a, L, d :: R) = \tau(d, a :: L, R)$. Starting from $s_0 = C(0, [0], [1])$ (after 11 TM steps),

$$
T(C(a, L, R)) = \begin{cases}
  \text{Halt} & \text{if } a = 0 \text{ and } L = [], \\
  \tau(b, L', \beta_1(\beta_1(R))) & \text{if } a = 0 \text{ and } L = b :: L', \\
  C(0, [], 0 :: R) & \text{if } a = 1 \text{ and } L = [], \\
  C(b + 1, L', 0 :: R) & \text{if } a = 1 \text{ and } L = b :: L', \\
  C(a - 2, \beta_1(L), \beta_1(R)) & \text{if } a \ge 2.
\end{cases}
$$

### 1.2 [`1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`](./M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB.lean)

For $a \in \mathbb{N}$ and $L, R \in \mathbb{N}^*$, let $C(a, L, R)$ encode left $1^{a+1} 00$-blocks and right $1^{d+1} 0$-blocks. Define $\delta([]) = [0]$, $\delta([d]) = [d + 1]$, and $\delta(d :: r :: S) = (r + d + 2) :: S$, and write $(b, L') = (1, [])$ if $L = []$ and $(c + 2, L_1)$ if $L = c :: L_1$. Starting from $s_0 = C(1, [], [0, 0])$ (after 19 TM steps), $T(C(a, L, R)) = \sigma(a, L, R)$, where

$$
\sigma(a, L, R) = \begin{cases}
  \text{Halt} & \text{if } R = [], \\
  C(b, L', [a + 2, 0]) & \text{if } R = [0], \\
  C(b, L', (a + r + 3) :: \delta(R')) & \text{if } R = 0 :: r :: R', \\
  \sigma(0, a :: L, R') & \text{if } R = 1 :: R', \\
  C(a + 2, L, (r - 2) :: \delta(R')) & \text{if } R = r :: R' \text{ with } r \ge 2.
\end{cases}
$$

### 1.3 [`1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA`](./M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.lean)

Over states $C(a, b, L, r, R)$ and $F(a, b, L, r, R)$ ($a, b, r \in \mathbb{N}$, $L, R \in \mathbb{N}^*$), write $(c^+, L') = (0, [])$ if $L = []$ and $(c + 1, L_1)$ if $L = c :: L_1$. Starting from $s_0 = F(1, 0, [], 0, [])$ (after 9 TM steps),

$$
\begin{aligned}
  T(C(a, b, L, r, R)) &= \begin{cases}
    \text{Halt} & \text{if } a = 0 \text{ and } b = 0, \\
    F(b + 2, c^+, L', r, R) & \text{if } a = 0,\ b \ge 1 \text{ is odd}, \\
    C(b - 2, c^+, L', 0, (r + 1) :: R) & \text{if } a = 0,\ b \ge 2 \text{ is even}, \\
    F(a - 1, b, L, 0, r :: R) & \text{if } a \ge 1,
  \end{cases} \\
  T(F(a, b, L, r, R)) &= \begin{cases}
    C(a' + 2, b, L, 0, []) & \text{if } r \text{ is even and } R = [], \\
    F(0, b + 1, L, a', []) & \text{if } r \text{ is even and } R = [0], \\
    F(a' + 3, b + 1, L, e, R') & \text{if } r \text{ is even},\ R = 0 :: e :: R',\ a' \text{ even}, \\
    C(a' - 1, b + 1, L, 0, (e + 1) :: R') & \text{if } r \text{ is even},\ R = 0 :: e :: R',\ a' \text{ odd}, \\
    F(0, b + 1, L, a', d :: R') & \text{if } r \text{ is even and } R = (d + 1) :: R', \\
    C(a', b, L, 0, [0]) & \text{if } r \text{ is odd and } R = [], \\
    F(0, a' + 1, b :: L, e, R') & \text{if } r \text{ is odd and } R = e :: R',
  \end{cases}
\end{aligned}
$$

where $a' = a + 2\lfloor r/2 \rfloor$.

### 1.4 [`1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA`](./M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.lean)

Over states $D(a, b, L, R)$ and $E(a, L, R)$ ($a, b \in \mathbb{N}$, $L, R \in \mathbb{N}^*$), define $\sigma_D(a, b, L, []) = D(a, b, L, [])$ and $\sigma_D(a, b, L, d :: R) = \sigma_D(d, a, b :: L, R)$. Starting from $s_0 = D(1, 0, [], [])$ (after 9 TM steps), with $k = \lfloor a/2 \rfloor$:

$$
\begin{aligned}
  T(D(a, b, L, R)) &= \begin{cases}
    E(b + k, L, [k]) & \text{if } a \text{ is even and } R = [], \\
    E(b + k, L, (d + k + 1) :: R') & \text{if } a \text{ is even and } R = d :: R', \\
    D(k, b + k + 2, \beta_1(L), []) & \text{if } a \text{ is odd and } R = [], \\
    \sigma_D(d + k + 1, b + k + 2, \beta_1(L), R') & \text{if } a \text{ is odd and } R = d :: R',
  \end{cases} \\
  T(E(a, L, R)) &= \begin{cases}
    \text{Halt} & \text{if } a = 0 \text{ and } L = [], \\
    E(b, L', 0 :: R) & \text{if } a = 0 \text{ and } L = b :: L', \\
    \sigma_D(0, 1, [0], R) & \text{if } a = 1 \text{ and } L = [], \\
    \sigma_D(0, b + 2, \beta_1(L'), R) & \text{if } a = 1 \text{ and } L = b :: L', \\
    D(a - 2, 0, [], 0 :: R) & \text{if } a \ge 2 \text{ and } L = [], \\
    D(a - 2, b + 1, L', 0 :: R) & \text{if } a \ge 2 \text{ and } L = b :: L'.
  \end{cases}
\end{aligned}
$$

### 1.5 [`1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB`](./M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB.lean)

States $B(P, u, R)$ ($P, R \in \mathbb{N}^*$, $u \in \mathbb{N}$) encode left stack $\ell(P, u)$ (where $\ell([], u) = [u]$ and $\ell(p :: P, u) = (p + 1) :: \ell(P, u)$, so $0$ occurs only at the bottom $u$) and right $1^{r+1} 000$-stack $R$. Define $\pi_k([], u) = ([], u + k)$, $\pi_k(p :: P, u) = ((p + k) :: P, u)$, $\gamma([], u) = ([u + 1], 0)$, and $\gamma(p :: P, u) = ((p + 2) :: P', u')$ where $(P', u') = \pi_1(P, u)$. Define $\Delta(a, P, u, []) = B((a + 2) :: P, u, [])$ and $\Delta(a, P, u, r :: R) = \Delta(r, a :: P', u', R)$ where $(P', u') = \pi_1(P, u)$. Starting from $s_0 = B([], 0, [])$ (after 3 TM steps), $T(B(P, u, [])) = \Pi(P, u, 0, [])$ and $T(B(P, u, r :: R)) = \Pi(P, u, r + 1, R)$, where

$$
\begin{aligned}
  \Pi([], u, d, R) &= \begin{cases}
    \Delta(d, [], 0, R) & \text{if } u = 0, \\
    B([0, 0], 0, R) & \text{if } u = 1,\ d = 0, \\
    B([1, 0], 0, R) & \text{if } u = 1,\ d = 1, \\
    \Delta(d - 2, [0], 0, R) & \text{if } u = 1,\ d \ge 2, \\
    \text{Halt} & \text{if } u = 2, \\
    \Delta(d - 1, [u - 3], 0, R) & \text{if } u \ge 3,\ d \ge 1, \\
    B([1, 1], m, \beta_1^m(R)) & \text{if } u = b + 3,\ d = 0,\ b = 2m + 1, \\
    B([1, 0], m, []) & \text{if } u = b + 3,\ d = 0,\ b = 2m,\ \beta_1^m(R) = [], \\
    \Delta(r_2, [m + 3], 1, R_2') & \text{if } u = b + 3,\ d = 0,\ b = 2m,\ \beta_1^m(R) = r_2 :: R_2',
  \end{cases} \\
  \Pi(p :: P, u, d, R) &= \begin{cases}
    B(0 :: P_1, u_1, R) & \text{if } p = 0,\ d = 0,\ (P_1, u_1) = \gamma(P, u), \\
    B(1 :: P_1, u_1, R) & \text{if } p = 0,\ d = 1,\ (P_1, u_1) = \gamma(P, u), \\
    \Delta(d - 2, P_1, u_1, R) & \text{if } p = 0,\ d \ge 2,\ (P_1, u_1) = \gamma(P, u), \\
    \Pi(P, u, 0, d :: R) & \text{if } p = 1, \\
    \Delta(d - 1, b :: P_1, u_1, R) & \text{if } p = b + 2,\ d \ge 1,\ (P_1, u_1) = \pi_1(P, u), \\
    B(1 :: 1 :: P_3, u_3, R_2) & \text{if } p = b + 2,\ d = 0,\ b = 2m + 1, \\
    B(1 :: 0 :: P_3, u_3, []) & \text{if } p = b + 2,\ d = 0,\ b = 2m,\ R_2 = [], \\
    \Delta(r_2, [u_2 + 4], 1, R_2') & \text{if } p = b + 2,\ d = 0,\ b = 2m,\ R_2 = r_2 :: R_2',\ P_2 = [], \\
    \Delta(r_2, (q + 5) :: P_4, u_4, R_2') & \text{if } p = b + 2,\ d = 0,\ b = 2m,\ R_2 = r_2 :: R_2',\ P_2 = q :: Q,
  \end{cases}
\end{aligned}
$$

with $R_2 = \beta_1^m(R)$, $(P_2, u_2) = \pi_m(P, u)$, $(P_3, u_3) = \pi_1(P_2, u_2)$, and $(P_4, u_4) = \pi_2(Q, u_2)$.

### 1.6 [`1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB`](./M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean)

For $a \in \mathbb{N}$ and $L, R \in \mathbb{N}^*$, define $\tau_B([], []) = C(0, [], [])$, $\tau_B(a :: L, []) = C(a + 1, L, [])$, and $\tau_B(L, d :: R) = \tau_B(d :: \beta_1(L), R)$. Write $r = 0, R' = []$ when $R = []$ and $r = d, R' = R_1$ when $R = d :: R_1$. Starting from $s_0 = C(3, [0], [])$ (after 11 TM steps),

$$
T(C(a, L, R)) = \begin{cases}
  \text{Halt} & \text{if } a = 0 \text{ and } L = [], \\
  \tau_B((r + 2) :: 0 :: L', R') & \text{if } a = 0 \text{ and } L = 0 :: L', \\
  \tau_B(b :: L', (r + 2) :: R') & \text{if } a = 0 \text{ and } L = (b + 1) :: L', \\
  \tau_B(\beta_1^k(L), (r + k + 2) :: R') & \text{if } a = 2k + 1, \\
  C(k, [], 0 :: (r + k) :: R') & \text{if } a = 2k + 2 \text{ and } L = [], \\
  C(b + k + 1, L', 0 :: (r + k) :: R') & \text{if } a = 2k + 2 \text{ and } L = b :: L'.
\end{cases}
$$

### 1.7 [`1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA`](./M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA.lean)

Over $C_R(a, b, L, d, R)$ ($a, b, d \in \mathbb{N}$, $L, R \in \mathbb{N}^*$), write $\hat{\beta}_1([]) = (0, [])$, $\hat{\beta}_1(r :: S) = (r + 1, S)$, $\hat{\beta}_2([]) = (1, [])$, and $\hat{\beta}_2(c :: S) = (c + 2, S)$. Define

$$
\begin{aligned}
  \sigma_0(b, d, L, R) &= \begin{cases}
    C_R(d + 1, c, L', r, R') & \text{if } b = 0, \\
    C_R(0, c, L', d + 1, R) & \text{if } b = 1, \\
    C_R(b - 2, c, L', 0, d :: R) & \text{if } b \ge 2,
  \end{cases} \quad (c, L') = \hat{\beta}_2(L),\ (r, R') = \hat{\beta}_1(R), \\
  \sigma_1(b, L, R) &= \begin{cases}
    C_R(0, b + 5, L, 0, []) & \text{if } R = [] \text{ or } R = [0], \\
    C_R(r_2 + 1, b + 5, L, r, R') & \text{if } R = 0 :: r_2 :: R_3,\ (r, R') = \hat{\beta}_1(R_3), \\
    C_R(e, b + 5, L, r, R') & \text{if } R = (e + 1) :: R_2,\ (r, R') = \hat{\beta}_1(R_2).
  \end{cases}
\end{aligned}
$$

Starting from $s_0 = C_R(0, 0, [], 0, [])$ (after 5 TM steps), with $q = \lfloor a/3 \rfloor$, $b_1 = b + 2q$, and $R_1 = \beta_1^q(R)$:

$$
T(C_R(a, b, L, d, R)) = \begin{cases}
  \sigma_0(b_1, 0, L, R_1) & \text{if } d = 0 \text{ and } a \equiv 0 \pmod{3}, \\
  \sigma_1(b_1, L, R_1) & \text{if } d = 0 \text{ and } a \equiv 1 \pmod{3}, \\
  C_R(0, b_1 + 2, L, r + 1, R') & \text{if } d = 0,\ a \equiv 2 \pmod{3},\ (r, R') = \hat{\beta}_1(R_1), \\
  \sigma_0(b, d, L, R) & \text{if } d \ge 1 \text{ and } a = 0, \\
  \text{Halt} & \text{if } d \ge 1 \text{ and } a = 1, \\
  C_R(d, a - 1, b :: L, r, R') & \text{if } d \ge 1,\ a \ge 2,\ (r, R') = \hat{\beta}_1(R).
\end{cases}
$$

---

## 2. Odometer Reductions

### 2.1 [`1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA`](./M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA.lean)

Over $B(L, R)$ ($L, R \in \mathbb{N}^*$ encoding odd runs $1^{2a+1} 0$), define $\rho(0, []) = [0, 0]$, $\rho(0, d :: R) = (d + 1) :: R$, and $\rho(b + 1, R) = 0 :: \rho(b, R)$. Define $\zeta(a, L, []) = \text{Halt}$, $\zeta(a, L, [0]) = B([], L^{\mathrm{rev}} \mathbin{+\!\!+} [a + 2, 0])$, $\zeta(a, L, 0 :: 0 :: R) = \zeta(a + 2, L, R)$, $\zeta(a, L, 0 :: (b + 1) :: R) = B((a + 2) :: L, b :: R)$, and $\zeta(a, L, (b + 1) :: R) = B((a + 1) :: L, \rho(b, R))$. Starting from $s_0 = B([], [0, 1])$ (after 11 TM steps),

$$
T(B(L, [])) = B([], L^{\mathrm{rev}} \mathbin{+\!\!+} [0, 0]), \qquad T(B(L, d :: R)) = \zeta(0, 0^d \mathbin{+\!\!+} L, R).
$$

### 2.2 [`1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD`](./M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD.lean)

Over $E(a, L, d, R)$ ($a, d \in \mathbb{N}$, $L, R \in \mathbb{N}^*$), define $\eta(d, []) = \text{Halt}$ if $d$ is odd and $E(0, 0^{d/2+1} \mathbin{+\!\!+} [1], 0, [])$ if $d$ is even; $\eta(d, e :: R) = E(0, 0^{\lfloor d/2 \rfloor} \mathbin{+\!\!+} [1], e, R)$ if $d$ is odd and $\eta(e + d + 4, R)$ if $d$ is even. For mode $m \in \lbrace \mathsf{A}, \mathsf{B}, \mathsf{BR} \rbrace$, define $\Lambda$ by $\Lambda(\mathsf{A}, [], d, R) = \eta(d + 1, R)$, $\Lambda(\mathsf{B}, [], d, R) = \eta(d, R)$, $\Lambda(\mathsf{BR}, [], d, R) = E(1, [], d, R)$, and for non-empty $L$ (with $\mu(x) = \mathsf{A}$ if $x$ is even, $\mathsf{B}$ if $x$ is odd):

$$
\begin{aligned}
  \Lambda(\mathsf{A}, x :: L, d, R) &= \Lambda(\mu(x), L, x + d + 2, R), \\
  \Lambda(\mathsf{B}, 0 :: L, d, R) &= \Lambda(\mathsf{BR}, L, d + 1, R), &
  \Lambda(\mathsf{B}, (x + 1) :: L, d, R) &= \Lambda(\mu(x), L, x, (d + 1) :: R), \\
  \Lambda(\mathsf{BR}, 0 :: L, d, R) &= \Lambda(\mathsf{BR}, L, 0, d :: R), &
  \Lambda(\mathsf{BR}, (x + 1) :: L, d, R) &= \Lambda(\mu(x), L, x, 0 :: d :: R).
\end{aligned}
$$

Starting from $s_0 = E(1, [], 0, [])$ (after 3 TM steps),

$$
T(E(a, L, d, R)) = \begin{cases}
  \Lambda(\mu(a + 3), L, a + 3, [0]) & \text{if } d = 0 \text{ and } R = [], \\
  \Lambda(\mu(a + 1), L, a + e + 4, R') & \text{if } d = 0 \text{ and } R = e :: R', \\
  \text{Halt} & \text{if } d \ge 1 \text{ is odd and } R = [], \\
  E(a + 3, L, e, R') & \text{if } d = 1 \text{ and } R = e :: R', \\
  E(0, 0^{(d-3)/2} \mathbin{+\!\!+} (a + 3) :: L, e, R') & \text{if } d \ge 3 \text{ is odd and } R = e :: R', \\
  \Lambda(\mathsf{A}, 0^{(d-1)/2} \mathbin{+\!\!+} (a + 3) :: L, 0, [0]) & \text{if } d \ge 2 \text{ is even and } R = [], \\
  \Lambda(\mathsf{A}, 0^{(d-1)/2} \mathbin{+\!\!+} (a + 3) :: L, e + 1, R') & \text{if } d \ge 2 \text{ is even and } R = e :: R'.
\end{cases}
$$

### 2.3 [`1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`](./M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH.lean)

Over $(L, w) \in \lbrace L_0, L_1, L_2 \rbrace^* \times \lbrace 0, 1 \rbrace^*$ (identifying $w$ with the zero-padded bit-stream $w \, 0^\infty$), define the mixed-radix capacity $\mathrm{cap}([]) = 0$, $\mathrm{cap}(L_0 :: L) = 2\mathrm{cap}(L) + 1$, $\mathrm{cap}(L_1 :: L) = 2\mathrm{cap}(L)$, and $\mathrm{cap}(L_2 :: L) = \lfloor \mathrm{cap}(L)/2 \rfloor$, odometer decrement $\mathrm{dec}(L_0 :: L) = L_1 :: L$, $\mathrm{dec}(L_1 :: L) = L_0 :: \mathrm{dec}(L)$, and $\mathrm{dec}(L_2 :: L) = L_2 :: \mathrm{dec}(\mathrm{dec}(L))$ (satisfying $\mathrm{cap}(\mathrm{dec}(L)) = \mathrm{cap}(L) - 1$ whenever $\mathrm{cap}(L) \ge 1$), and zero-capacity drain word $\mathrm{drain}([]) = [1, 0]$, $\mathrm{drain}(L_0 :: L) = \mathrm{drain}(L) \mathbin{+\!\!+} [1, 0, 1, 0]$, $\mathrm{drain}(L_1 :: L) = \mathrm{drain}(L) \mathbin{+\!\!+} [1, 0, 1, 0]$, and $\mathrm{drain}(L_2 :: L) = \mathrm{drain}(L) \mathbin{+\!\!+} [0, 0, 0]$ if $\mathrm{cap}(L)$ is even else $\mathrm{drain}(L) \mathbin{+\!\!+} [1, 0, 0]$. Write $\mathcal{L}(L, u) = (\mathrm{dec}(L), u)$ if $\mathrm{cap}(L) \ge 1$ and $([], \mathrm{drain}(L) \mathbin{+\!\!+} u)$ if $\mathrm{cap}(L) = 0$. Starting from $s_0 = ([], [])$ (after 2 TM steps), reading leading bits from $w \, 0^\infty$:

$$
T(L, w) = \begin{cases}
  \mathcal{L}(L, 1 :: w') & \text{if } w \, 0^\infty = 0 \, w' \, 0^\infty, \\
  (L_2 :: L, w') & \text{if } w \, 0^\infty = 100 \, w' \, 0^\infty \text{ or } 110 \, w' \, 0^\infty, \\
  (L_0 :: L, w') & \text{if } w \, 0^\infty = 1010 \, w' \, 0^\infty, \\
  \mathcal{L}(L, 1000 :: w') & \text{if } w \, 0^\infty = 1011 \, w' \, 0^\infty, \\
  \text{Halt} & \text{if } w \, 0^\infty = 111 \, w' \, 0^\infty.
\end{cases}
$$

### 2.4 [`1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`](./M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD.lean)

Over $B(L, E, c)$ ($L, E \in \mathbb{N}^*$, $c \in \mathbb{N}$), define $\Delta([], E, c) = B([0], E, c)$, and for $a :: L'$: if $a$ is odd, $\Delta(a :: L', E, c) = B(\beta_1(L'), 0^{\lfloor a/2 \rfloor + 1} \mathbin{+\!\!+} E, c)$; if $a$ is even, let $E' = 0^{a/2} \mathbin{+\!\!+} E$, setting $\Delta(a :: L', E, c) = \Delta(L', [], c + 2)$ when $E' = []$ and $\Delta(L', (e + 1) :: E_t, c)$ when $E' = e :: E_t$. Starting from $s_0 = B([0], [], 1)$ (after 3 TM steps),

$$
T(B(L, E, c)) = \begin{cases}
  \Delta(\beta_1^c(L), [], 3) & \text{if } E = [], \\
  \Delta(\beta_1^{2e_0}(L), [], 2) & \text{if } E = [e_0],\ c = 0, \\
  \text{Halt} & \text{if } E = [e_0],\ c = 1, \\
  B(\beta_1^{2e_0+1}(L), [0, 0], 1) & \text{if } E = [e_0],\ c = 2, \\
  \Delta(\beta_1^{2e_0}(L), [1], 0) & \text{if } E = [e_0],\ c = 3, \\
  \Delta(\beta_1^{2e_0}(L), [1, 0], c - 4) & \text{if } E = [e_0],\ c \ge 4, \\
  \Delta(\beta_1^{2e_0}(L), 1 :: E_2, c) & \text{if } E = e_0 :: 0 :: E_2, \\
  B(4 :: \beta_1^{2e_0}(L), E_2, c) & \text{if } E = e_0 :: 1 :: E_2, \\
  \Delta(4 :: \beta_1^{2e_0}(L), (e_1 - 2) :: E_2, c) & \text{if } E = e_0 :: e_1 :: E_2 \text{ with } e_1 \ge 2.
\end{cases}
$$

### 2.5 [`1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA`](./M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA.lean)

Over $E(d, R)$ ($d \in \mathbb{N}$, $R \in \mathbb{N}^*$), define $\Omega([], d, R) = E(d + 2, R)$, $\Omega([j], d, R) = E(1, 0^j \mathbin{+\!\!+} (d + 1) :: R)$, $\Omega(0 :: j_2 :: K, d, R) = \Omega(K, 2j_2 + d + 6, R)$, and $\Omega((j_1 + 1) :: j_2 :: K, d, R) = \Omega(K, 2j_2 + 5, 0^{j_1} \mathbin{+\!\!+} (d + 1) :: R)$. Starting from $s_0 = E(0, [0])$ (after 11 TM steps), $T(E(d, R)) = \Sigma([], d, R)$, where

$$
\Sigma(K, d, R) = \begin{cases}
  \text{Halt} & \text{if } R = [] \text{ and } d \text{ is odd}, \\
  E(1, 0^{d/2 + 1}) & \text{if } R = [],\ d \text{ is even, and } K = [], \\
  \Omega(K', 2j_2 + 5, 0^{d/2}) & \text{if } R = [],\ d \text{ is even, and } K = j_2 :: K', \\
  \Sigma(\lfloor d/2 \rfloor :: K, e, R') & \text{if } R = e :: R' \text{ and } d \text{ is odd}, \\
  \Omega(K, d + e + 2, R') & \text{if } R = e :: R' \text{ and } d \text{ is even}.
\end{cases}
$$

### 2.6 [`1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---`](./M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH.lean)

Over $E(R)$ ($R \in \mathbb{N}^*$), define $\phi([]) = \phi([0]) = []$, $\phi(0 :: r_2 :: R) = 0 :: (r_2 + 1) :: R$, and $\phi((r + 1) :: R) = r :: R$. Define the return pass $\rho : \lbrace 0, 1 \rbrace \times \lbrace 0, 1 \rbrace^* \times \mathbb{N}^* \to \mathbb{N}^*$ by

$$
\begin{aligned}
  \rho(0, [], R) &= \phi(\beta_1(R)), & \rho(1, [], R) &= \phi(0 :: \beta_1(R)), \\
  \rho(0, 0 :: B, R) &= \rho(1, B, \beta_1(R)), & \rho(0, 1 :: B, R) &= \rho(1, B, \beta_1(\beta_1(R))), \\
  \rho(1, 0 :: B, R) &= \rho(0, B, 0 :: \beta_1(R)), & \rho(1, [1], R) &= \phi(0 :: 0 :: \beta_1(R)), \\
  \rho(1, 1 :: 0 :: B, R) &= \rho(1, B, 0 :: 0 :: \beta_1(R)), & \rho(1, 1 :: 1 :: B, R) &= \rho(1, B, 1 :: 0 :: \beta_1(R)),
\end{aligned}
$$

and the scan pass $\sigma(m, B, R)$ ($m \in \lbrace 0, 1 \rbrace$, writing $B_0 = B$ if $m = 0$ and $B_0 = 1 :: B$ if $m = 1$) by $\sigma(0, B, []) = \rho(0, B, [0])$, $\sigma(1, B, []) = \rho(1, B, [0, 0])$, $\sigma(m, B, 0 :: R) = \rho(0, B_0' , R)$, $\sigma(m, B, 1 :: R) = \rho(1, B_0', R)$, $\sigma(m, B, 2 :: R) = \sigma(0, 0 :: B_0', R)$, $\sigma(m, B, 3 :: R) = \sigma(1, B_0', R)$ (where $B_0' = 0 :: B$ if $m = 0$ and $1 :: 0 :: B$ if $m = 1$), and $\sigma(m, B, r :: R) = \text{Halt}$ for $r \ge 4$. Starting from $s_0 = E([])$ (after 3 TM steps),

$$
T(E([])) = E([0, 0]), \quad T(E(0 :: R)) = E(\sigma(0, [0, 0], R)), \quad T(E(1 :: R)) = E(\sigma(1, [0], R)), \quad T(E(r :: R)) = \text{Halt}\ (r \ge 2).
$$

### 2.7 [`1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD`](./M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD.lean)

Over $E_L(a, L, d, R)$ and $E_0(L, R)$ ($a, d \in \mathbb{N}$, $L, R \in \mathbb{N}^*$), let $\hat{\beta}_1([]) = (0, [])$, $\hat{\beta}_1(x :: X) = (x + 1, X)$, and $\pi_E(0, R) = R$, $\pi_E(k + 1, R) = \pi_E(k, 0 :: \beta_1(\beta_1(R)))$. Define $\Phi(L, R)$ and $\Psi(L, R)$ by

$$
\begin{aligned}
  \Phi(L, R) &= \begin{cases}
    E_L(p_1, p_2, 0, []) & \text{if } R = [],\ (p_1, p_2) = \hat{\beta}_1(L), \\
    E_L(p_1, p_2, 2, []) & \text{if } R = [0],\ (p_1, p_2) = \hat{\beta}_1(L), \\
    E_L(p_1, p_2, 0, e :: R') & \text{if } R = 0 :: e :: R',\ (p_1, p_2) = \hat{\beta}_1(L), \\
    \Phi(0 :: \beta_1(L), R') & \text{if } R = 1 :: R', \\
    E_L(q_1, q_2, r_1, r_2) & \text{if } R = 2 :: R',\ (q_1, q_2) = \hat{\beta}_1(\beta_1^2(L)),\ (r_1, r_2) = \hat{\beta}_1(\beta_1(R')), \\
    E_0(\beta_1(L), d :: R') & \text{if } R = (d + 3) :: R',
  \end{cases} \\
  \Psi(L, R) &= \begin{cases}
    \Phi([0, 0], R) & \text{if } L = [], \\
    \Phi([0, 1, 0], R) & \text{if } L = [0], \\
    E_L(a, L', 0, 1 :: R) & \text{if } L = 0 :: a :: L', \\
    \Psi(L', 1 :: R) & \text{if } L = 1 :: L', \\
    E_L(a, L', 0, 1 :: R) & \text{if } L = (a + 2) :: L'.
  \end{cases}
\end{aligned}
$$

Starting from $s_0 = E_L(1, [], 1, [])$ (after 9 TM steps), $T(E_0(L, R)) = \Psi(L, R)$, while for $E_L(a, L, d, R)$ with $R_1 = \pi_E(\lfloor a/4 \rfloor, d :: R)$ and $(p_1, p_2) = \hat{\beta}_1(R_1)$:

$$
T(E_L(a, L, d, R)) = \begin{cases}
  \text{Halt} & \text{if } a \equiv 0 \pmod{4} \text{ and } L = [], \\
  E_L(1, [], p_1 + 2, p_2) & \text{if } a \equiv 0 \pmod{4} \text{ and } L = [0], \\
  E_L(b, L', p_1 + 3, p_2) & \text{if } a \equiv 0 \pmod{4} \text{ and } L = 0 :: b :: L', \\
  E_0([], p_1 :: p_2) & \text{if } a \equiv 0 \pmod{4} \text{ and } L = [1], \\
  \Phi(0 :: (c + 1) :: L', p_1 :: p_2) & \text{if } a \equiv 0 \pmod{4} \text{ and } L = 1 :: c :: L', \\
  E_0(b :: L', p_1 :: p_2) & \text{if } a \equiv 0 \pmod{4} \text{ and } L = (b + 2) :: L', \\
  \Phi(L, \beta_1^2(R_1)) & \text{if } a \equiv 1 \pmod{4}, \\
  E_0([], \beta_1^2(R_1)) & \text{if } a \equiv 2 \pmod{4} \text{ and } L = [], \\
  E_L(b, L', 0, \beta_1^2(R_1)) & \text{if } a \equiv 2 \pmod{4} \text{ and } L = b :: L', \\
  E_0(L, \beta_1^2(R_1)) & \text{if } a \equiv 3 \pmod{4}.
\end{cases}
$$

---

## 3. Transducer Reductions

### 3.1 [`1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF`](./M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF.lean)

Over zero-run stacks $E(L, R)$ ($L, R \in \mathbb{N}^*$ via $\mathrm{enc}_0$), define the 3-mode right transducer $\Sigma_R : \lbrace \mathsf{a}, \mathsf{b}, \mathsf{c} \rbrace \times \mathbb{N}^* \times \mathbb{N}^* \to \text{State}$ by $\Sigma_R(\mathsf{a}, L, []) = E(1 :: L, [])$, $\Sigma_R(\mathsf{b}, L, []) = E(\iota(L), [])$, $\Sigma_R(\mathsf{c}, L, []) = E(L, [])$, and $\Sigma_R(m, L, d :: R_t) = \varepsilon_d(m, L, R_t)$, where

$$
\begin{aligned}
  \varepsilon_0(\mathsf{a}, L, R_t) &= E(L, \iota(R_t)), &
  \varepsilon_0(\mathsf{b}, L, R_t) &= \Sigma_R(\mathsf{a}, \iota(L), R_t), &
  \varepsilon_0(\mathsf{c}, L, R_t) &= \Sigma_R(\mathsf{b}, 0 :: L, R_t), \\
  \varepsilon_{d+1}(\mathsf{a}, L, R_t) &= \varepsilon_d(\mathsf{b}, 0 :: L, R_t), &
  \varepsilon_{d+1}(\mathsf{b}, L, R_t) &= \varepsilon_d(\mathsf{c}, \iota(L), R_t), \\
  \varepsilon_1(\mathsf{c}, L, R_t) &= \Sigma_R(\mathsf{b}, 1 :: L, R_t), &
  \varepsilon_{d+2}(\mathsf{c}, L, R_t) &= E(L, (d + 2) :: R_t).
\end{aligned}
$$

Define $\Sigma_L([], R) = \Sigma_R(\mathsf{a}, [], 2 :: R)$, $\Sigma_L(0 :: L_t, R) = \Sigma_L(L_t, 0 :: R)$, $\Sigma_L(1 :: L_t, R) = \Sigma_R(\mathsf{b}, \iota(L_t), 0 :: R)$, $\Sigma_L(2 :: L_t, R) = E(L_t, 2 :: R)$, and $\Sigma_L((a + 3) :: L_t, R) = \Sigma_R(\mathsf{a}, a :: L_t, 2 :: R)$. Starting from $s_0 = E([1], [])$ (after 5 TM steps),

$$
T(E([], R)) = \Sigma_L([], 0 :: R), \qquad T(E(0 :: L_t, R)) = \text{Halt}, \qquad T(E((a + 1) :: L_t, R)) = \Sigma_L(a :: L_t, 0 :: R).
$$

### 3.2 [`1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC`](./M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean)

Over pair stacks $E(L, R)$ with entries $(a, b) \in \mathbb{N} \times \lbrace 0, 1 \rbrace$ (encoding $0^{a+1} 1^{b+1}$), write $\iota_H([]) = []$ and $\iota_H((a, b) :: X) = (a + 1, b) :: X$. Over return modes $\mathcal{M} = \lbrace r_{01}, r_{10}, r_{11}, r_{21} \rbrace$, define $u_{01}, u_{111}, u_{11} : \mathcal{M} \times (\mathbb{N} \times \lbrace 0, 1 \rbrace)^* \to \mathcal{M} \times (\mathbb{N} \times \lbrace 0, 1 \rbrace)^*$ by

$$
\begin{aligned}
  u_{01}(r_{01}, R') &= (r_{01}, (0, 0) :: R'), & u_{01}(r_{10}, R') &= (r_{10}, (0, 0) :: R'), & u_{01}(r_{11}, R') &= (r_{10}, (0, 1) :: R'), & u_{01}(r_{21}, R') &= (r_{11}, (0, 0) :: \iota_H(R')), \\
  u_{111}(r_{01}, R') &= (r_{01}, (0, 1) :: R'), & u_{111}(r_{10}, R') &= (r_{11}, (0, 0) :: R'), & u_{111}(r_{11}, R') &= (r_{11}, (0, 1) :: R'), & u_{111}(r_{21}, R') &= (r_{21}, (0, 1) :: R'), \\
  u_{11}(r_{01}, R') &= (r_{21}, R'), & u_{11}(r_{10}, R') &= (r_{01}, (0, 0) :: R'), & u_{11}(r_{11}, R') &= (r_{01}, (0, 1) :: R'), & u_{11}(r_{21}, R') &= (r_{11}, (0, 1) :: R'),
\end{aligned}
$$

and right bounce $\mathcal{B}([]) = (r_{11}, [])$, $\mathcal{B}((0, 0) :: R_1) = u_{01}(\mathcal{B}(R_1))$, $\mathcal{B}((0, 1) :: R_1) = (r_{01}, \iota_H(R_1))$, $\mathcal{B}((1, 0) :: R_1) = u_{111}(\mathcal{B}(R_1))$, $\mathcal{B}((1, 1) :: R_1) = (r_{01}, (0, 0) :: R_1)$, $\mathcal{B}((2, 0) :: R_1) = u_{11}(u_{01}(\mathcal{B}(R_1)))$, $\mathcal{B}((2, 1) :: R_1) = (r_{21}, \iota_H(R_1))$, $\mathcal{B}((3, \_) :: \_) = \text{Halt}$, and $\mathcal{B}((d + 4, b) :: R_1) = (r_{11}, (d + 1, b) :: R_1)$. Starting from $s_0 = E([(1, 0)], [(0, 0)])$ (after 4 TM steps), $T(E(L, [])) = \kappa(L, (r_{11}, []))$, $T(E(L, (0, b) :: R_1)) = \zeta_0(L, b, R_1)$, and $T(E(L, (d + 1, b) :: R_1)) = \kappa(L, \mathcal{B}((d, b) :: R_1))$, with local boundary maps $\kappa$ (`closeRet`) and $\zeta_0$ (`stepZero`) given in [`M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean`](./M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean).

### 3.3 [`1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC`](./M_1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_HHH1LC.lean)

Over $B(L, d, R)$ ($L, R \in \mathbb{N}^*$, $d \in \mathbb{N}$), define $\chi([], a_0, R) = 0^{\lfloor a_0/2 \rfloor} \mathbin{+\!\!+} R$ if $a_0$ is even and $\beta_2(0^{\lfloor a_0/2 \rfloor} \mathbin{+\!\!+} R)$ if $a_0$ is odd, and $\chi(a_1 :: L_p, a_0, R) = \chi(L_p, a_1 + (a_0 \bmod 2), \beta_2(0^{\lfloor a_0/2 \rfloor} \mathbin{+\!\!+} R))$. Define $\hat{\beta}_2([]) = (1, [])$, $\hat{\beta}_2(a :: S) = (a + 2, S)$, and $\Gamma(b, L, R)$ by

$$
\Gamma(b, L, R) = \begin{cases}
  B([], 0, \chi(L, b, [1])) & \text{if } R = [], \\
  B((b + 1) :: L, p_1, p_2) & \text{if } R = 0 :: R',\ (p_1, p_2) = \hat{\beta}_2(R'), \\
  \Gamma(1, b :: L, R') & \text{if } R = 1 :: R', \\
  \text{Halt} & \text{if } R = [2], \\
  B(0 :: 1 :: b :: L, e, R') & \text{if } R = 2 :: e :: R', \\
  B(2 :: b :: L, r - 3, R') & \text{if } R = r :: R' \text{ with } r \ge 3.
\end{cases}
$$

Starting from $s_0 = B([0], 0, [])$ (after 4 TM steps), let $L_1 = \beta_1^{3\lfloor d/3 \rfloor}(L)$; then

$$
T(B(L, d, R)) = \begin{cases}
  B([0], p_1, p_2) & \text{if } d \equiv 0 \pmod{3},\ L_1 = [],\ (p_1, p_2) = \hat{\beta}_2(R), \\
  B([], 0, \chi(L_p, a_0, \beta_2(R))) & \text{if } d \equiv 0 \pmod{3},\ L_1 = a_0 :: L_p, \\
  \Gamma(q_1, q_2, R) & \text{if } d \equiv 1 \pmod{3},\ (q_1, q_2) = \hat{\beta}_2(L_1), \\
  \text{Halt} & \text{if } d \equiv 2 \pmod{3} \text{ and } R = [], \\
  B(0 :: \beta_2(L_1), e, R') & \text{if } d \equiv 2 \pmod{3} \text{ and } R = e :: R'.
\end{cases}
$$

### 3.4 [`1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---`](./M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH.lean)

Over zero-run stacks $D(L, R)$ ($L, R \in \mathbb{N}^*$ via $\mathrm{enc}_0$), define $\sigma_B(L, []) = D(\iota(L), [])$, $\sigma_B(L, 0 :: R_t) = \sigma_B(\iota(L), R_t)$, $\sigma_B(L, 1 :: R_t) = \sigma_B(0 :: \iota(L), R_t)$, and $\sigma_B(L, (d + 2) :: R_t) = D(\iota(L), (d + 1) :: R_t)$. Starting from $s_0 = D([1], [])$ (after 3 TM steps),

$$
T(D(L, R)) = \begin{cases}
  \sigma_B([0], 1 :: R) & \text{if } L = [], \\
  \sigma_B([], \iota(\iota(R))) & \text{if } L = [0], \\
  \sigma_B(L'', 0 :: \iota(R)) & \text{if } L = 0 :: 0 :: L'', \\
  \sigma_B(k :: L'', \iota(\iota(R))) & \text{if } L = 0 :: (k + 1) :: L'', \\
  D([], 1 :: 0 :: R) & \text{if } L = [1], \\
  \sigma_B(0 :: L'', 0 :: 0 :: R) & \text{if } L = 1 :: 0 :: L'', \\
  D(k :: L'', 1 :: 0 :: R) & \text{if } L = 1 :: (k + 1) :: L'', \\
  \sigma_B([], 2 :: 1 :: R) & \text{if } L = [2], \\
  \text{Halt} & \text{if } L = 2 :: 0 :: L'', \\
  \sigma_B(L'', 0 :: 1 :: 1 :: R) & \text{if } L = 2 :: 1 :: L'', \\
  \sigma_B(k :: L'', 2 :: 1 :: R) & \text{if } L = 2 :: (k + 2) :: L'', \\
  \sigma_B(0 :: k :: L', 1 :: R) & \text{if } L = (k + 3) :: L'.
\end{cases}
$$

### 3.5 [`1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB`](./M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean)

Over asymmetric pair stacks $D(L, R)$ with $L \in (\mathbb{N} \times \lbrace 0, 1 \rbrace)^*$ (encoding $1^{a+1} 0^{b+1}$) and $R \in (\mathbb{N} \times \mathbb{Z}_3)^*$ (encoding $1^{d+1} 0^{c+1}$), starting from $s_0 = D([], [(1, 0)])$ (after 3 TM steps):
- When $L = (a, b) :: L'$, $T$ peels $q = \lfloor a/4 \rfloor$ blocks $(2, 0)^q$ onto $R$ to form $R_1 = (2, 0)^q \mathbin{+\!\!+} R$ and branches on $(a \bmod 4, b)$, halting when $a \equiv 2 \pmod{4}$ and either $L' = []$ or $b = 1$, and otherwise invoking the left cascade `runB` or right cascade `runBR` defined in [`M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean`](./M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean) (`runB` also halts on $(2, \_, [], \_)$ and $(2, 1, \_ :: \_, \_)$).
- When $L = []$, $T(D([], [])) = D([(0, 0)], [(1, 0)])$ and $T(D([], (d_1, c_1) :: R')) = \mathrm{runBR}(0, [], d_1 + 1, c_1, R')$.

### 3.6 [`1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA`](./M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean)

Over $(1, 4)$-separator stacks $M_0(L, R)$ with $L, R \in (\mathbb{N} \times \lbrace 1, 2, 3, 4 \rbrace)^*$ (each $(a, s)$ encoding $1^{a+1} 0^s$), write $\tilde{\tau}([]) = [(0, 1)]$, $\tilde{\tau}(X) = X$ ($X \ne []$), $\pi_s(_, []) = []$, $\pi_1((a, b') :: X) = (a + 1, b') :: X$, and $\pi_{s+1}((a, b') :: X) = (0, s) :: (a, b') :: X$ ($s \in \lbrace 1, 2, 3 \rbrace$). Starting from $s_0 = M_0([(0, 1), (0, 1)], [(1, 1)])$ (after 6 TM steps),

$$
T(M_0(L, R)) = \begin{cases}
  \mathcal{D}(1, L, []) & \text{if } R = [], \\
  \mathcal{D}(1, L, \pi_s(R_t)) & \text{if } R = (0, s) :: R_t, \\
  M_0((0, 1) :: \tilde{\tau}(L), \pi_s(R_t)) & \text{if } R = (1, s) :: R_t, \\
  M_0((0, 2) :: \tilde{\tau}(L), \pi_s(R_t)) & \text{if } R = (2, s) :: R_t, \\
  \text{Halt} & \text{if } R = (a, \_) :: \_ \text{ with } a \ge 3,
\end{cases}
$$

where $\mathcal{D}$ (`stepD`) peels $(0, 1)^2$ pairs on $L$ and, on $(0, 1) :: (1, 4) :: L_2$ ($L_2 \ne []$), invokes the 6-state carry transducer `evalStage3` over $\mathcal{F} = \lbrace f_{00}, \dots, f_{05} \rbrace$ (halting at `stepD` on $(a, \_) :: \_$ with $a \ge 2$, at `evalQ0Aux` on $(a, \_) :: \_$ with $a \ge 2$, and at `stepBit1` on $f_{05}$); see [`M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean`](./M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean) for full definitions.
