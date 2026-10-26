# `BB(6)` Stacked, Odometer, and Transducer Accelerations (`BusyBeaver/BB6/Accelerations/`)

This directory contains formal Lean 4 specifications and kernel-verified reductions for 29 `BB(6)` (6-state, 2-symbol) holdout Turing machines whose blank-tape dynamics evolve over unbounded digit stacks, mixed-radix odometers, or bidirectional finite-state word transducers rather than fixed-dimension counter tuples:

1. **9 Community-Documented `bbchallenge` Wiki Machines** formalized under the three structural reduction predicates defined in [`BusyBeaver/Defs.lean`](../../Defs.lean)—`HasStackReduction` (6 machines), `HasOdometerReduction` (2 machines: Beaver Math Olympiad Problems 10 and 11), and `HasTransducerReduction` (1 machine: *Bell eats counter*).
2. **20 Open `BB(6)` Acceleration Problems** certified via `IsValidAcceleration` and `IsHalt target ↔ CollatzHalts next start` (with [`1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`](./M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH.lean) additionally proved under `HasOdometerReduction`). Each open problem states a self-contained initial state $s_0$ (`start`) and accelerated transition map $T$ (`next`) over finite sequences and non-negative integers: the corresponding Turing machine halts from the blank tape if and only if iterating $T$ from $s_0$ eventually reaches $\mathrm{Halt}$ (`none`).

## Structural Reduction Predicates ([`BusyBeaver/Defs.lean`](../../Defs.lean))

| Predicate | Dynamical Family |
| :--- | :--- |
| `HasStackReduction M` | Closed two-sided variable-length digit-stack system (`StackTuple`, `IsValidStackModes`) with non-blank/blank block encodings (`stackDigit`, `stackSepLen`), non-trivial stack reachability, and certified `ReachesPlus` closure from `init []`. |
| `HasOdometerReduction M` | Closed mixed-radix odometer stack and bit-stream system (`evalOdomR` / `evalOdomL`) with certified decrement (`cap (dec stk) = cap stk - 1`), zero-capacity drain (`drain`), reflection, and `ReachesPlus` closure from `init []`. |
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

## Sequence and Stack Notation

Throughout the table and problem statements below, $\mathbb{N} = \lbrace 0, 1, 2, \dots \rbrace$ denotes the non-negative integers, and we use standard sequence (free-monoid) notation for stacks and words:

- **Finite sequences ($\Sigma^*$):** For any alphabet or entry set $\Sigma$ (such as $\mathbb{N}$, $\lbrace 0, 1 \rbrace$, or $\mathbb{N} \times \lbrace 0, 1 \rbrace$), $\Sigma^*$ denotes the set of finite sequences $[x_1, x_2, \dots, x_m]$ of length $m \ge 0$ with $x_i \in \Sigma$, ordered from the active top/front entry ($x_1$) to the bottom/back entry ($x_m$).
- **Empty sequence ($\varepsilon$):** We write $\varepsilon \in \Sigma^*$ for the empty sequence of length $0$ (written `[]` in Lean). Note that $[0]$ has length $1$ (sole entry $0$), whereas $\varepsilon$ has length $0$.
- **Concatenation, push, and pop ($X \cdot Y$):** For $X, Y \in \Sigma^*$, $X \cdot Y$ denotes sequence concatenation (written `X ++ Y` in Lean), with $\varepsilon \cdot X = X \cdot \varepsilon = X$. In particular:
  - $[x] \cdot X$ pushes/prepends a single entry $x \in \Sigma$ onto the front of $X$ (written `x :: X` in Lean), and $[x, y] \cdot X$ pushes $x$ followed by $y$ (`x :: y :: X` in Lean).
  - Writing $X = [x] \cdot X'$ in a branch condition matches a non-empty sequence $X$ with top entry $x$ and remaining tail $X'$.
- **Repetition and reversal ($[x]^k$, $X^{\mathrm{rev}}$):** For $k \in \mathbb{N}$, $[x]^k$ denotes the sequence $[x, \dots, x]$ of $k$ copies of $x$ (with $[x]^0 = \varepsilon$), and $[x_1, \dots, x_m]^{\mathrm{rev}} = [x_m, \dots, x_1]$.
- **Head-increment operators ($\beta_k$, $\iota$):** On integer stacks $X \in \mathbb{N}^*$, we define:

$$
\beta_k(\varepsilon) = [k - 1] \quad (k \ge 1), \qquad \beta_k([x] \cdot X) = [x + k] \cdot X, \qquad \iota(\varepsilon) = \varepsilon, \qquad \iota([x] \cdot X) = [x + 1] \cdot X,
$$

and write $\beta_1^m$ for the $m$-fold iterate of $\beta_1$ (`bumpHead` in Lean).

## Open `BB(6)` Acceleration Problems (20 Machines)

| Machine (`bbchallenge` RLE) | Family | State Space | Initial State $s_0$ | Proved Properties | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF` | Stacked | $C(a, L, R) \in \mathbb{N} \times \mathbb{N}^* \times \mathbb{N}^*$ | $C(0, [0], [1])$ | `IsValidAcceleration` | [`M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean`](./M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean) |
| `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB` | Stacked | $C(a, L, R) \in \mathbb{N} \times \mathbb{N}^* \times \mathbb{N}^*$ | $C(1, \varepsilon, [0, 0])$ | `IsValidAcceleration` | [`M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB.lean`](./M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB.lean) |
| `1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA` | Stacked | $C(a, b, L, r, R),\ F(a, b, L, r, R)$ | $F(1, 0, \varepsilon, 0, \varepsilon)$ | `IsValidAcceleration` | [`M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.lean`](./M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.lean) |
| `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA` | Stacked | $D(a, b, L, R),\ E(a, L, R)$ | $D(1, 0, \varepsilon, \varepsilon)$ | `IsValidAcceleration` | [`M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.lean`](./M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.lean) |
| `1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB` | Stacked | $B(P, u, R) \in \mathbb{N}^* \times \mathbb{N} \times \mathbb{N}^*$ | $B(\varepsilon, 0, \varepsilon)$ | `IsValidAcceleration` | [`M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB.lean`](./M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB.lean) |
| `1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB` | Stacked | $C(a, L, R) \in \mathbb{N} \times \mathbb{N}^* \times \mathbb{N}^*$ | $C(3, [0], \varepsilon)$ | `IsValidAcceleration` | [`M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean`](./M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean) |
| `1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA` | Stacked | $C_R(a, b, L, d, R)$ | $C_R(0, 0, \varepsilon, 0, \varepsilon)$ | `IsValidAcceleration` | [`M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA.lean`](./M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA.lean) |
| `1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA` | Odometer | $B(L, R) \in \mathbb{N}^* \times \mathbb{N}^*$ | $B(\varepsilon, [0, 1])$ | `IsValidAcceleration` | [`M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA.lean`](./M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA.lean) |
| `1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD` | Odometer | $E(a, L, d, R)$ | $E(1, \varepsilon, 0, \varepsilon)$ | `IsValidAcceleration` | [`M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD.lean`](./M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD.lean) |
| `1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---` | Odometer | $(L, w) \in \lbrace L_0, L_1, L_2 \rbrace^* \times \lbrace 0, 1 \rbrace^*$ | $(\varepsilon, \varepsilon)$ | `HasOdometerReduction`, `IsValidAcceleration` | [`M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH.lean`](./M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH.lean) |
| `1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD` | Odometer | $B(L, E, c) \in \mathbb{N}^* \times \mathbb{N}^* \times \mathbb{N}$ | $B([0], \varepsilon, 1)$ | `IsValidAcceleration` | [`M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD.lean`](./M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD.lean) |
| `1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA` | Odometer | $E(d, R) \in \mathbb{N} \times \mathbb{N}^*$ | $E(0, [0])$ | `IsValidAcceleration` | [`M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA.lean`](./M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA.lean) |
| `1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---` | Odometer | $E(R) \in \mathbb{N}^*$ | $E(\varepsilon)$ | `IsValidAcceleration` | [`M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH.lean`](./M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH.lean) |
| `1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD` | Odometer | $E_L(a, L, d, R),\ E_0(L, R)$ | $E_L(1, \varepsilon, 1, \varepsilon)$ | `IsValidAcceleration` | [`M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD.lean`](./M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD.lean) |
| `1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF` | Transducer | $E(L, R) \in \mathbb{N}^* \times \mathbb{N}^*$ | $E([1], \varepsilon)$ | `IsValidAcceleration` | [`M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF.lean`](./M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF.lean) |
| `1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC` | Transducer | $E(L, R) \in (\mathbb{N} \times \lbrace 0, 1 \rbrace)^* \times (\mathbb{N} \times \lbrace 0, 1 \rbrace)^*$ | $E([(1, 0)], [(0, 0)])$ | `IsValidAcceleration` | [`M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean`](./M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean) |
| `1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC` | Transducer | $B(L, d, R) \in \mathbb{N}^* \times \mathbb{N} \times \mathbb{N}^*$ | $B([0], 0, \varepsilon)$ | `IsValidAcceleration` | [`M_1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_HHH1LC.lean`](./M_1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_HHH1LC.lean) |
| `1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---` | Transducer | $D(L, R) \in \mathbb{N}^* \times \mathbb{N}^*$ | $D([1], \varepsilon)$ | `IsValidAcceleration` | [`M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH.lean`](./M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH.lean) |
| `1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB` | Transducer | $D(L, R) \in (\mathbb{N} \times \lbrace 0, 1 \rbrace)^* \times (\mathbb{N} \times \lbrace 0, 1, 2 \rbrace)^*$ | $D(\varepsilon, [(1, 0)])$ | `IsValidAcceleration` | [`M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean`](./M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean) |
| `1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA` | Transducer | $M_0(L, R) \in (\mathbb{N} \times \lbrace 1, 2, 3, 4 \rbrace)^* \times (\mathbb{N} \times \lbrace 1, 2, 3, 4 \rbrace)^*$ | $M_0([(0, 1), (0, 1)], [(1, 1)])$ | `IsValidAcceleration` | [`M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean`](./M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean) |

---

## 1. Stacked Reductions

In a stacked reduction, both half-tapes organize into unbounded sequences $L, R \in \mathbb{N}^*$ of variable-length run blocks (such as $1^{a+1} 0^s$), so the machine's state space is an unbounded pair of integer stacks rather than a fixed-dimension tuple in $\mathbb{N}^d$. At each macro-step, the head performs modular arithmetic ($\bmod\ 2$, $\bmod\ 3$, or $\bmod\ 4$) on the active top counters adjacent to the head—incrementing stack tops or pushing fresh zero entries that increase stack depth—and periodically triggers a full-stack transfer sweep ($\tau$, $\sigma_D$, $\Delta$, $\tau_B$) that pours one stack onto the other in reverse order. This couples local Collatz-like residue branching at the head with arbitrarily deep historical memory stored across $L$ and $R$, while halting requires draining an entire stack down to $\varepsilon$ at a specific head residue. Six `bbchallenge` Wiki holdouts in the table above satisfy `HasStackReduction`; the seven open problems below give explicit accelerated maps $(s_0, T)$ in this family.

### 1.1 [`1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`](./M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean)

Over states $C(a, L, R)$ with $a \in \mathbb{N}$ and $L, R \in \mathbb{N}^*$, define the right-to-left stack transfer $\tau$ by

$$
\tau(a, L, \varepsilon) = C(a, L, [0]), \qquad \tau(a, L, [d] \cdot R) = \tau(d, [a] \cdot L, R).
$$

Starting from $s_0 = C(0, [0], [1])$ (after 11 TM steps),

$$
T(C(a, L, R)) = \begin{cases}
  \mathrm{Halt} & \text{if } a = 0 \text{ and } L = \varepsilon, \\
  \tau(b, L', \beta_1(\beta_1(R))) & \text{if } a = 0 \text{ and } L = [b] \cdot L', \\
  C(0, \varepsilon, [0] \cdot R) & \text{if } a = 1 \text{ and } L = \varepsilon, \\
  C(b + 1, L', [0] \cdot R) & \text{if } a = 1 \text{ and } L = [b] \cdot L', \\
  C(a - 2, \beta_1(L), \beta_1(R)) & \text{if } a \ge 2.
\end{cases}
$$

### 1.2 [`1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`](./M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB.lean)

Over states $C(a, L, R)$ with $a \in \mathbb{N}$ and $L, R \in \mathbb{N}^*$, define $\delta : \mathbb{N}^* \to \mathbb{N}^*$ by

$$
\delta(\varepsilon) = [0], \qquad \delta([d]) = [d + 1], \qquad \delta([d, r] \cdot S) = [r + d + 2] \cdot S,
$$

and write $(b, L') = (1, \varepsilon)$ if $L = \varepsilon$ and $(b, L') = (c + 2, L_1)$ if $L = [c] \cdot L_1$. Starting from $s_0 = C(1, \varepsilon, [0, 0])$ (after 19 TM steps), $T(C(a, L, R)) = \sigma(a, L, R)$, where

$$
\sigma(a, L, R) = \begin{cases}
  \mathrm{Halt} & \text{if } R = \varepsilon, \\
  C(b, L', [a + 2, 0]) & \text{if } R = [0], \\
  C(b, L', [a + r + 3] \cdot \delta(R')) & \text{if } R = [0, r] \cdot R', \\
  \sigma(0, [a] \cdot L, R') & \text{if } R = [1] \cdot R', \\
  C(a + 2, L, [r - 2] \cdot \delta(R')) & \text{if } R = [r] \cdot R' \text{ with } r \ge 2.
\end{cases}
$$

### 1.3 [`1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA`](./M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.lean)

Over states $C(a, b, L, r, R)$ and $F(a, b, L, r, R)$ with $a, b, r \in \mathbb{N}$ and $L, R \in \mathbb{N}^*$, write $(c^+, L') = (0, \varepsilon)$ if $L = \varepsilon$ and $(c^+, L') = (c + 1, L_1)$ if $L = [c] \cdot L_1$. Starting from $s_0 = F(1, 0, \varepsilon, 0, \varepsilon)$ (after 9 TM steps),

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

### 1.4 [`1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA`](./M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.lean)

Over states $D(a, b, L, R)$ and $E(a, L, R)$ with $a, b \in \mathbb{N}$ and $L, R \in \mathbb{N}^*$, define

$$
\sigma_D(a, b, L, \varepsilon) = D(a, b, L, \varepsilon), \qquad \sigma_D(a, b, L, [d] \cdot R) = \sigma_D(d, a, [b] \cdot L, R).
$$

Starting from $s_0 = D(1, 0, \varepsilon, \varepsilon)$ (after 9 TM steps), with $k = \lfloor a/2 \rfloor$:

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

### 1.5 [`1RB1LA_1LC0RE_---0LD_1RE0LF_1RA1RE_1LA0LB`](./M_1RB1LA_1LC0RE_HHH0LD_1RE0LF_1RA1RE_1LA0LB.lean)

Over states $B(P, u, R)$ with $P, R \in \mathbb{N}^*$ and $u \in \mathbb{N}$ (where $P$ holds strictly positive upper stack entries shifted by $1$ above a bottom register $u$), define the stack-increment and transfer helpers:

$$
\begin{aligned}
  \pi_k(\varepsilon, u) &= (\varepsilon, u + k), & \pi_k([p] \cdot P, u) &= ([p + k] \cdot P, u), \\
  \gamma(\varepsilon, u) &= ([u + 1], 0), & \gamma([p] \cdot P, u) &= ([p + 2] \cdot P', u') \quad \text{where } (P', u') = \pi_1(P, u), \\
  \Delta(a, P, u, \varepsilon) &= B([a + 2] \cdot P, u, \varepsilon), & \Delta(a, P, u, [r] \cdot R) &= \Delta(r, [a] \cdot P', u', R) \quad \text{where } (P', u') = \pi_1(P, u).
\end{aligned}
$$

Starting from $s_0 = B(\varepsilon, 0, \varepsilon)$ (after 3 TM steps), $T(B(P, u, \varepsilon)) = \Pi(P, u, 0, \varepsilon)$ and $T(B(P, u, [r] \cdot R)) = \Pi(P, u, r + 1, R)$, where

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

### 1.6 [`1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB`](./M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean)

Over states $C(a, L, R)$ with $a \in \mathbb{N}$ and $L, R \in \mathbb{N}^*$, define

$$
\tau_B(\varepsilon, \varepsilon) = C(0, \varepsilon, \varepsilon), \qquad \tau_B([a] \cdot L, \varepsilon) = C(a + 1, L, \varepsilon), \qquad \tau_B(L, [d] \cdot R) = \tau_B([d] \cdot \beta_1(L), R).
$$

Write $(r, R') = (0, \varepsilon)$ when $R = \varepsilon$ and $(r, R') = (d, R_1)$ when $R = [d] \cdot R_1$. Starting from $s_0 = C(3, [0], \varepsilon)$ (after 11 TM steps),

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

### 1.7 [`1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA`](./M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA.lean)

Over states $C_R(a, b, L, d, R)$ with $a, b, d \in \mathbb{N}$ and $L, R \in \mathbb{N}^*$, define $\hat{\beta}_1(\varepsilon) = (0, \varepsilon)$, $\hat{\beta}_1([r] \cdot S) = (r + 1, S)$, $\hat{\beta}_2(\varepsilon) = (1, \varepsilon)$, and $\hat{\beta}_2([c] \cdot S) = (c + 2, S)$. Let

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

## 2. Odometer Reductions

In an odometer reduction, one side of the tape acts as a positional or mixed-radix counter stack whose discrete capacity decrements by $1$ via recursive borrow propagation on each reflection from the active head, until reaching zero capacity triggers a global drain/reset sweep across the entire stack. Unlike classical periodic odometers in ergodic theory, each carry-propagation or zero-capacity drain (`drain`, $\Lambda$, $\Omega$, $\rho$) dynamically rewrites the active stream on the opposite half-tape, coupling numeration-system carries with variable-length prefix parsing across exponentially separated timescales. On the `bbchallenge` Wiki this class includes **Beaver Math Olympiad Problems 10 and 11** (formalized under `HasOdometerReduction` above); the seven open problems below include a direct ternary-alphabet odometer sibling (`1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`, also proved under `HasOdometerReduction`) alongside six open carry-and-drain accelerations.

### 2.1 [`1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA`](./M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA.lean)

Over states $B(L, R)$ with $L, R \in \mathbb{N}^*$, define $\rho : \mathbb{N} \times \mathbb{N}^* \to \mathbb{N}^*$ by

$$
\rho(0, \varepsilon) = [0, 0], \qquad \rho(0, [d] \cdot R) = [d + 1] \cdot R, \qquad \rho(b + 1, R) = [0] \cdot \rho(b, R),
$$

and the right-scan map $\zeta$ by

$$
\zeta(a, L, R) = \begin{cases}
  \mathrm{Halt} & \text{if } R = \varepsilon, \\
  B(\varepsilon, L^{\mathrm{rev}} \cdot [a + 2, 0]) & \text{if } R = [0], \\
  \zeta(a + 2, L, R') & \text{if } R = [0, 0] \cdot R', \\
  B([a + 2] \cdot L, [b] \cdot R') & \text{if } R = [0, b + 1] \cdot R', \\
  B([a + 1] \cdot L, \rho(b, R')) & \text{if } R = [b + 1] \cdot R'.
\end{cases}
$$

Starting from $s_0 = B(\varepsilon, [0, 1])$ (after 11 TM steps),

$$
T(B(L, \varepsilon)) = B(\varepsilon, L^{\mathrm{rev}} \cdot [0, 0]), \qquad T(B(L, [d] \cdot R)) = \zeta(0, [0]^d \cdot L, R).
$$

### 2.2 [`1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD`](./M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD.lean)

Over states $E(a, L, d, R)$ with $a, d \in \mathbb{N}$ and $L, R \in \mathbb{N}^*$, define the boundary bounce $\eta$ by

$$
\eta(d, \varepsilon) = \begin{cases}
  \mathrm{Halt} & \text{if } d \text{ is odd}, \\
  E(0, [0]^{d/2 + 1} \cdot [1], 0, \varepsilon) & \text{if } d \text{ is even},
\end{cases} \qquad
\eta(d, [e] \cdot R) = \begin{cases}
  E(0, [0]^{\lfloor d/2 \rfloor} \cdot [1], e, R) & \text{if } d \text{ is odd}, \\
  \eta(e + d + 4, R) & \text{if } d \text{ is even}.
\end{cases}
$$

For mode $m \in \lbrace \mathsf{A}, \mathsf{B}, \mathsf{BR} \rbrace$, write $\mu(x) = \mathsf{A}$ if $x$ is even and $\mu(x) = \mathsf{B}$ if $x$ is odd, and define the left drain $\Lambda$ by $\Lambda(\mathsf{A}, \varepsilon, d, R) = \eta(d + 1, R)$, $\Lambda(\mathsf{B}, \varepsilon, d, R) = \eta(d, R)$, $\Lambda(\mathsf{BR}, \varepsilon, d, R) = E(1, \varepsilon, d, R)$, and

$$
\begin{aligned}
  \Lambda(\mathsf{A}, [x] \cdot L, d, R) &= \Lambda(\mu(x), L, x + d + 2, R), \\
  \Lambda(\mathsf{B}, [0] \cdot L, d, R) &= \Lambda(\mathsf{BR}, L, d + 1, R), &
  \Lambda(\mathsf{B}, [x + 1] \cdot L, d, R) &= \Lambda(\mu(x), L, x, [d + 1] \cdot R), \\
  \Lambda(\mathsf{BR}, [0] \cdot L, d, R) &= \Lambda(\mathsf{BR}, L, 0, [d] \cdot R), &
  \Lambda(\mathsf{BR}, [x + 1] \cdot L, d, R) &= \Lambda(\mu(x), L, x, [0, d] \cdot R).
\end{aligned}
$$

Starting from $s_0 = E(1, \varepsilon, 0, \varepsilon)$ (after 3 TM steps),

$$
T(E(a, L, d, R)) = \begin{cases}
  \Lambda(\mu(a + 3), L, a + 3, [0]) & \text{if } d = 0 \text{ and } R = \varepsilon, \\
  \Lambda(\mu(a + 1), L, a + e + 4, R') & \text{if } d = 0 \text{ and } R = [e] \cdot R', \\
  \mathrm{Halt} & \text{if } d \ge 1 \text{ is odd and } R = \varepsilon, \\
  E(a + 3, L, e, R') & \text{if } d = 1 \text{ and } R = [e] \cdot R', \\
  E(0, [0]^{(d-3)/2} \cdot [a + 3] \cdot L, e, R') & \text{if } d \ge 3 \text{ is odd and } R = [e] \cdot R', \\
  \Lambda(\mathsf{A}, [0]^{(d-1)/2} \cdot [a + 3] \cdot L, 0, [0]) & \text{if } d \ge 2 \text{ is even and } R = \varepsilon, \\
  \Lambda(\mathsf{A}, [0]^{(d-1)/2} \cdot [a + 3] \cdot L, e + 1, R') & \text{if } d \ge 2 \text{ is even and } R = [e] \cdot R'.
\end{cases}
$$

### 2.3 [`1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`](./M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH.lean)

Over $(L, w) \in \lbrace L_0, L_1, L_2 \rbrace^* \times \lbrace 0, 1 \rbrace^*$, define the mixed-radix capacity $\mathrm{cap}$, odometer decrement $\mathrm{dec}$ (satisfying $\mathrm{cap}(\mathrm{dec}(L)) = \mathrm{cap}(L) - 1$ whenever $\mathrm{cap}(L) \ge 1$), and zero-capacity drain word $\mathrm{drain}$ by

$$
\begin{aligned}
  \mathrm{cap}(\varepsilon) &= 0, & \mathrm{cap}([L_0] \cdot L) &= 2\mathrm{cap}(L) + 1, \\
  \mathrm{cap}([L_1] \cdot L) &= 2\mathrm{cap}(L), & \mathrm{cap}([L_2] \cdot L) &= \lfloor \mathrm{cap}(L)/2 \rfloor, \\
  \mathrm{dec}([L_0] \cdot L) &= [L_1] \cdot L, & \mathrm{dec}([L_1] \cdot L) &= [L_0] \cdot \mathrm{dec}(L), \\
  \mathrm{dec}([L_2] \cdot L) &= [L_2] \cdot \mathrm{dec}(\mathrm{dec}(L)), & \mathrm{drain}(\varepsilon) &= [1, 0], \\
  \mathrm{drain}([L_0] \cdot L) &= \mathrm{drain}(L) \cdot [1, 0, 1, 0], & \mathrm{drain}([L_1] \cdot L) &= \mathrm{drain}(L) \cdot [1, 0, 1, 0], \\
  \mathrm{drain}([L_2] \cdot L) &= \begin{cases}
    \mathrm{drain}(L) \cdot [0, 0, 0] & \text{if } \mathrm{cap}(L) \text{ is even}, \\
    \mathrm{drain}(L) \cdot [1, 0, 0] & \text{if } \mathrm{cap}(L) \text{ is odd}.
  \end{cases}
\end{aligned}
$$

Write $\mathcal{L}(L, u) = (\mathrm{dec}(L), u)$ if $\mathrm{cap}(L) \ge 1$ and $\mathcal{L}(L, u) = (\varepsilon, \mathrm{drain}(L) \cdot u)$ if $\mathrm{cap}(L) = 0$. Identifying any finite bit sequence $w \in \lbrace 0, 1 \rbrace^*$ with its zero-padded stream (so missing trailing bits read as $0$, i.e. $\varepsilon$ has leading bit $0$ and remaining tail $\varepsilon$), starting from $s_0 = (\varepsilon, \varepsilon)$ (after 2 TM steps):

$$
T(L, w) = \begin{cases}
  \mathcal{L}(L, [1] \cdot w') & \text{if } w \text{ has leading prefix } [0] \text{ with tail } w', \\
  ([L_2] \cdot L, w') & \text{if } w \text{ has leading prefix } [1, 0, 0] \text{ or } [1, 1, 0] \text{ with tail } w', \\
  ([L_0] \cdot L, w') & \text{if } w \text{ has leading prefix } [1, 0, 1, 0] \text{ with tail } w', \\
  \mathcal{L}(L, [1, 0, 0, 0] \cdot w') & \text{if } w \text{ has leading prefix } [1, 0, 1, 1] \text{ with tail } w', \\
  \mathrm{Halt} & \text{if } w \text{ has leading prefix } [1, 1, 1].
\end{cases}
$$

### 2.4 [`1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`](./M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD.lean)

Over states $B(L, E, c)$ with $L, E \in \mathbb{N}^*$ and $c \in \mathbb{N}$, define the left drain $\Delta$ by $\Delta(\varepsilon, E, c) = B([0], E, c)$ and, for $[a] \cdot L'$:

$$
\Delta([a] \cdot L', E, c) = \begin{cases}
  B(\beta_1(L'), [0]^{\lfloor a/2 \rfloor + 1} \cdot E, c) & \text{if } a \text{ is odd}, \\
  \Delta(L', \varepsilon, c + 2) & \text{if } a \text{ is even and } [0]^{a/2} \cdot E = \varepsilon, \\
  \Delta(L', [e + 1] \cdot E_t, c) & \text{if } a \text{ is even and } [0]^{a/2} \cdot E = [e] \cdot E_t.
\end{cases}
$$

Starting from $s_0 = B([0], \varepsilon, 1)$ (after 3 TM steps),

$$
T(B(L, E, c)) = \begin{cases}
  \Delta(\beta_1^c(L), \varepsilon, 3) & \text{if } E = \varepsilon, \\
  \Delta(\beta_1^{2e_0}(L), \varepsilon, 2) & \text{if } E = [e_0],\ c = 0, \\
  \mathrm{Halt} & \text{if } E = [e_0],\ c = 1, \\
  B(\beta_1^{2e_0+1}(L), [0, 0], 1) & \text{if } E = [e_0],\ c = 2, \\
  \Delta(\beta_1^{2e_0}(L), [1], 0) & \text{if } E = [e_0],\ c = 3, \\
  \Delta(\beta_1^{2e_0}(L), [1, 0], c - 4) & \text{if } E = [e_0],\ c \ge 4, \\
  \Delta(\beta_1^{2e_0}(L), [1] \cdot E_2, c) & \text{if } E = [e_0, 0] \cdot E_2, \\
  B([4] \cdot \beta_1^{2e_0}(L), E_2, c) & \text{if } E = [e_0, 1] \cdot E_2, \\
  \Delta([4] \cdot \beta_1^{2e_0}(L), [e_1 - 2] \cdot E_2, c) & \text{if } E = [e_0, e_1] \cdot E_2 \text{ with } e_1 \ge 2.
\end{cases}
$$

### 2.5 [`1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA`](./M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA.lean)

Over states $E(d, R)$ with $d \in \mathbb{N}$ and $R \in \mathbb{N}^*$, define the return drain $\Omega$ by

$$
\begin{aligned}
  \Omega(\varepsilon, d, R) &= E(d + 2, R), \\
  \Omega([j], d, R) &= E(1, [0]^j \cdot [d + 1] \cdot R), \\
  \Omega([0, j_2] \cdot K, d, R) &= \Omega(K, 2j_2 + d + 6, R), \\
  \Omega([j_1 + 1, j_2] \cdot K, d, R) &= \Omega(K, 2j_2 + 5, [0]^{j_1} \cdot [d + 1] \cdot R).
\end{aligned}
$$

Starting from $s_0 = E(0, [0])$ (after 11 TM steps), $T(E(d, R)) = \Sigma(\varepsilon, d, R)$, where

$$
\Sigma(K, d, R) = \begin{cases}
  \mathrm{Halt} & \text{if } R = \varepsilon \text{ and } d \text{ is odd}, \\
  E(1, [0]^{d/2 + 1}) & \text{if } R = \varepsilon,\ d \text{ is even, and } K = \varepsilon, \\
  \Omega(K', 2j_2 + 5, [0]^{d/2}) & \text{if } R = \varepsilon,\ d \text{ is even, and } K = [j_2] \cdot K', \\
  \Sigma([\lfloor d/2 \rfloor] \cdot K, e, R') & \text{if } R = [e] \cdot R' \text{ and } d \text{ is odd}, \\
  \Omega(K, d + e + 2, R') & \text{if } R = [e] \cdot R' \text{ and } d \text{ is even}.
\end{cases}
$$

### 2.6 [`1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---`](./M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH.lean)

Over states $E(R)$ with $R \in \mathbb{N}^*$, define $\phi(\varepsilon) = \phi([0]) = \varepsilon$, $\phi([0, r_2] \cdot R) = [0, r_2 + 1] \cdot R$, and $\phi([r + 1] \cdot R) = [r] \cdot R$. Define the return pass $\rho : \lbrace 0, 1 \rbrace \times \lbrace 0, 1 \rbrace^* \times \mathbb{N}^* \to \mathbb{N}^*$ by

$$
\begin{aligned}
  \rho(0, \varepsilon, R) &= \phi(\beta_1(R)), & \rho(1, \varepsilon, R) &= \phi([0] \cdot \beta_1(R)), \\
  \rho(0, [0] \cdot B, R) &= \rho(1, B, \beta_1(R)), & \rho(0, [1] \cdot B, R) &= \rho(1, B, \beta_1(\beta_1(R))), \\
  \rho(1, [0] \cdot B, R) &= \rho(0, B, [0] \cdot \beta_1(R)), & \rho(1, [1], R) &= \phi([0, 0] \cdot \beta_1(R)), \\
  \rho(1, [1, 0] \cdot B, R) &= \rho(1, B, [0, 0] \cdot \beta_1(R)), & \rho(1, [1, 1] \cdot B, R) &= \rho(1, B, [1, 0] \cdot \beta_1(R)),
\end{aligned}
$$

and, writing $B_m = [0] \cdot B$ if $m = 0$ and $B_m = [1, 0] \cdot B$ if $m = 1$, define the scan pass $\sigma$ by

$$
\sigma(m, B, R) = \begin{cases}
  E(\rho(0, B, [0])) & \text{if } R = \varepsilon \text{ and } m = 0, \\
  E(\rho(1, B, [0, 0])) & \text{if } R = \varepsilon \text{ and } m = 1, \\
  E(\rho(0, B_m, R')) & \text{if } R = [0] \cdot R', \\
  E(\rho(1, B_m, R')) & \text{if } R = [1] \cdot R', \\
  \sigma(0, [0] \cdot B_m, R') & \text{if } R = [2] \cdot R', \\
  \sigma(1, B_m, R') & \text{if } R = [3] \cdot R', \\
  \mathrm{Halt} & \text{if } R = [r] \cdot R' \text{ with } r \ge 4.
\end{cases}
$$

Starting from $s_0 = E(\varepsilon)$ (after 3 TM steps),

$$
T(E(\varepsilon)) = E([0, 0]), \quad T(E([0] \cdot R)) = \sigma(0, [0, 0], R), \quad T(E([1] \cdot R)) = \sigma(1, [0], R), \quad T(E([r] \cdot R)) = \mathrm{Halt}\ (r \ge 2).
$$

### 2.7 [`1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD`](./M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD.lean)

Over states $E_L(a, L, d, R)$ and $E_0(L, R)$ with $a, d \in \mathbb{N}$ and $L, R \in \mathbb{N}^*$, let $\hat{\beta}_1(\varepsilon) = (0, \varepsilon)$, $\hat{\beta}_1([x] \cdot X) = (x + 1, X)$, $\pi_E(0, R) = R$, and $\pi_E(k + 1, R) = \pi_E(k, [0] \cdot \beta_1(\beta_1(R)))$. Define $\Phi(L, R)$ and $\Psi(L, R)$ by

$$
\begin{aligned}
  \Phi(L, R) &= \begin{cases}
    E_L(p_1, p_2, 0, \varepsilon) & \text{if } R = \varepsilon,\ (p_1, p_2) = \hat{\beta}_1(L), \\
    E_L(p_1, p_2, 2, \varepsilon) & \text{if } R = [0],\ (p_1, p_2) = \hat{\beta}_1(L), \\
    E_L(p_1, p_2, 0, [e] \cdot R') & \text{if } R = [0, e] \cdot R',\ (p_1, p_2) = \hat{\beta}_1(L), \\
    \Phi([0] \cdot \beta_1(L), R') & \text{if } R = [1] \cdot R', \\
    E_L(q_1, q_2, r_1, r_2) & \text{if } R = [2] \cdot R',\ (q_1, q_2) = \hat{\beta}_1(\beta_1^2(L)),\ (r_1, r_2) = \hat{\beta}_1(\beta_1(R')), \\
    E_0(\beta_1(L), [d] \cdot R') & \text{if } R = [d + 3] \cdot R',
  \end{cases} \\
  \Psi(L, R) &= \begin{cases}
    \Phi([0, 0], R) & \text{if } L = \varepsilon, \\
    \Phi([0, 1, 0], R) & \text{if } L = [0], \\
    E_L(a, L', 0, [1] \cdot R) & \text{if } L = [0, a] \cdot L', \\
    \Psi(L', [1] \cdot R) & \text{if } L = [1] \cdot L', \\
    E_L(a, L', 0, [1] \cdot R) & \text{if } L = [a + 2] \cdot L'.
  \end{cases}
\end{aligned}
$$

Starting from $s_0 = E_L(1, \varepsilon, 1, \varepsilon)$ (after 9 TM steps), $T(E_0(L, R)) = \Psi(L, R)$, while for $E_L(a, L, d, R)$ with $R_1 = \pi_E(\lfloor a/4 \rfloor, [d] \cdot R)$ and $(p_1, p_2) = \hat{\beta}_1(R_1)$:

$$
T(E_L(a, L, d, R)) = \begin{cases}
  \mathrm{Halt} & \text{if } a \equiv 0 \pmod{4} \text{ and } L = \varepsilon, \\
  E_L(1, \varepsilon, p_1 + 2, p_2) & \text{if } a \equiv 0 \pmod{4} \text{ and } L = [0], \\
  E_L(b, L', p_1 + 3, p_2) & \text{if } a \equiv 0 \pmod{4} \text{ and } L = [0, b] \cdot L', \\
  E_0(\varepsilon, [p_1] \cdot p_2) & \text{if } a \equiv 0 \pmod{4} \text{ and } L = [1], \\
  \Phi([0, c + 1] \cdot L', [p_1] \cdot p_2) & \text{if } a \equiv 0 \pmod{4} \text{ and } L = [1, c] \cdot L', \\
  E_0([b] \cdot L', [p_1] \cdot p_2) & \text{if } a \equiv 0 \pmod{4} \text{ and } L = [b + 2] \cdot L', \\
  \Phi(L, \beta_1^2(R_1)) & \text{if } a \equiv 1 \pmod{4}, \\
  E_0(\varepsilon, \beta_1^2(R_1)) & \text{if } a \equiv 2 \pmod{4} \text{ and } L = \varepsilon, \\
  E_L(b, L', 0, \beta_1^2(R_1)) & \text{if } a \equiv 2 \pmod{4} \text{ and } L = [b] \cdot L', \\
  E_0(L, \beta_1^2(R_1)) & \text{if } a \equiv 3 \pmod{4}.
\end{cases}
$$

---

## 3. Transducer Reductions

In a transducer reduction, neither half-tape acts as a dominant scalar counter: instead, both half-tapes are words over a finite or run-length block alphabet, and each macro-step sweeps a stateful finite-mode carry head (a sequential Mealy transducer) across an arbitrarily long prefix of blocks, rewriting every block in transit before reflecting at the blank boundary or an interior stop pattern. Halting reduces to the **iterated transducer mortality / forbidden-subword problem**—determining whether repeated bidirectional sweeps from $s_0$ ever synthesize a specific local halting block or carry state (such as a block of height $\ge 3$ or a designated halting carry mode). On the `bbchallenge` Wiki this class is exemplified by *Bell eats counter* (formalized under `HasTransducerReduction` above); the six open problems below capture pure zero-run, pair-block, and multi-separator bidirectional transducers in `BB(6)`.

### 3.1 [`1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF`](./M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF.lean)

Over zero-run stacks $E(L, R)$ with $L, R \in \mathbb{N}^*$, define the 3-mode right transducer $\Sigma_R$ over modes $m \in \lbrace \mathsf{a}, \mathsf{b}, \mathsf{c} \rbrace$ by $\Sigma_R(\mathsf{a}, L, \varepsilon) = E([1] \cdot L, \varepsilon)$, $\Sigma_R(\mathsf{b}, L, \varepsilon) = E(\iota(L), \varepsilon)$, $\Sigma_R(\mathsf{c}, L, \varepsilon) = E(L, \varepsilon)$, and $\Sigma_R(m, L, [d] \cdot R_t) = \psi_d(m, L, R_t)$, where

$$
\begin{aligned}
  \psi_0(\mathsf{a}, L, R_t) &= E(L, \iota(R_t)), &
  \psi_{d+1}(\mathsf{a}, L, R_t) &= \psi_d(\mathsf{b}, [0] \cdot L, R_t), \\
  \psi_0(\mathsf{b}, L, R_t) &= \Sigma_R(\mathsf{a}, \iota(L), R_t), &
  \psi_{d+1}(\mathsf{b}, L, R_t) &= \psi_d(\mathsf{c}, \iota(L), R_t), \\
  \psi_0(\mathsf{c}, L, R_t) &= \Sigma_R(\mathsf{b}, [0] \cdot L, R_t), &
  \psi_1(\mathsf{c}, L, R_t) &= \Sigma_R(\mathsf{b}, [1] \cdot L, R_t), \\
  \psi_{d+2}(\mathsf{c}, L, R_t) &= E(L, [d + 2] \cdot R_t),
\end{aligned}
$$

and define the left sweep $\Sigma_L$ by

$$
\Sigma_L(L, R) = \begin{cases}
  \Sigma_R(\mathsf{a}, \varepsilon, [2] \cdot R) & \text{if } L = \varepsilon, \\
  \Sigma_L(L_t, [0] \cdot R) & \text{if } L = [0] \cdot L_t, \\
  \Sigma_R(\mathsf{b}, \iota(L_t), [0] \cdot R) & \text{if } L = [1] \cdot L_t, \\
  E(L_t, [2] \cdot R) & \text{if } L = [2] \cdot L_t, \\
  \Sigma_R(\mathsf{a}, [a] \cdot L_t, [2] \cdot R) & \text{if } L = [a + 3] \cdot L_t.
\end{cases}
$$

Starting from $s_0 = E([1], \varepsilon)$ (after 5 TM steps),

$$
T(E(\varepsilon, R)) = \Sigma_L(\varepsilon, [0] \cdot R), \qquad T(E([0] \cdot L_t, R)) = \mathrm{Halt}, \qquad T(E([a + 1] \cdot L_t, R)) = \Sigma_L([a] \cdot L_t, [0] \cdot R).
$$

### 3.2 [`1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC`](./M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean)

Over pair stacks $E(L, R)$ with entries $(a, b) \in \mathbb{N} \times \lbrace 0, 1 \rbrace$, write $\iota_H(\varepsilon) = \varepsilon$ and $\iota_H([(a, b)] \cdot X) = [(a + 1, b)] \cdot X$. Over return modes $\mathcal{M} = \lbrace r_{01}, r_{10}, r_{11}, r_{21} \rbrace$, define $u_{01}, u_{111}, u_{11}$ by

$$
\begin{aligned}
  u_{01}(r_{01}, R') &= (r_{01}, [(0, 0)] \cdot R'), & u_{01}(r_{10}, R') &= (r_{10}, [(0, 0)] \cdot R'), \\
  u_{01}(r_{11}, R') &= (r_{10}, [(0, 1)] \cdot R'), & u_{01}(r_{21}, R') &= (r_{11}, [(0, 0)] \cdot \iota_H(R')), \\
  u_{111}(r_{01}, R') &= (r_{01}, [(0, 1)] \cdot R'), & u_{111}(r_{10}, R') &= (r_{11}, [(0, 0)] \cdot R'), \\
  u_{111}(r_{11}, R') &= (r_{11}, [(0, 1)] \cdot R'), & u_{111}(r_{21}, R') &= (r_{21}, [(0, 1)] \cdot R'), \\
  u_{11}(r_{01}, R') &= (r_{21}, R'), & u_{11}(r_{10}, R') &= (r_{01}, [(0, 0)] \cdot R'), \\
  u_{11}(r_{11}, R') &= (r_{01}, [(0, 1)] \cdot R'), & u_{11}(r_{21}, R') &= (r_{11}, [(0, 1)] \cdot R'),
\end{aligned}
$$

and define the right bounce $\mathcal{B}$ on $R \in (\mathbb{N} \times \lbrace 0, 1 \rbrace)^*$ by

$$
\mathcal{B}(R) = \begin{cases}
  (r_{11}, \varepsilon) & \text{if } R = \varepsilon, \\
  u_{01}(\mathcal{B}(R_1)) & \text{if } R = [(0, 0)] \cdot R_1, \\
  (r_{01}, \iota_H(R_1)) & \text{if } R = [(0, 1)] \cdot R_1, \\
  u_{111}(\mathcal{B}(R_1)) & \text{if } R = [(1, 0)] \cdot R_1, \\
  (r_{01}, [(0, 0)] \cdot R_1) & \text{if } R = [(1, 1)] \cdot R_1, \\
  u_{11}(u_{01}(\mathcal{B}(R_1))) & \text{if } R = [(2, 0)] \cdot R_1, \\
  (r_{21}, \iota_H(R_1)) & \text{if } R = [(2, 1)] \cdot R_1, \\
  \mathrm{Halt} & \text{if } R = [(3, b)] \cdot R_1 \text{ for any } b \in \lbrace 0, 1 \rbrace, \\
  (r_{11}, [(d + 1, b)] \cdot R_1) & \text{if } R = [(d + 4, b)] \cdot R_1.
\end{cases}
$$

Starting from $s_0 = E([(1, 0)], [(0, 0)])$ (after 4 TM steps), $T(E(L, \varepsilon)) = \kappa(L, (r_{11}, \varepsilon))$, $T(E(L, [(0, b)] \cdot R_1)) = \zeta_0(L, b, R_1)$, and $T(E(L, [(d + 1, b)] \cdot R_1)) = \kappa(L, \mathcal{B}([(d, b)] \cdot R_1))$ (returning $\mathrm{Halt}$ whenever $\mathcal{B}$ halts), where the finite boundary maps $\kappa$ (`closeRet`) and $\zeta_0$ (`stepZero`) are given in [`M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean`](./M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean).

### 3.3 [`1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC`](./M_1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_HHH1LC.lean)

Over states $B(L, d, R)$ with $L, R \in \mathbb{N}^*$ and $d \in \mathbb{N}$, define the parity-halving sweep $\chi$ by

$$
\begin{aligned}
  \chi(\varepsilon, a_0, R) &= \begin{cases}
    [0]^{a_0 / 2} \cdot R & \text{if } a_0 \text{ is even}, \\
    \beta_2([0]^{\lfloor a_0 / 2 \rfloor} \cdot R) & \text{if } a_0 \text{ is odd},
  \end{cases} \\
  \chi([a_1] \cdot L_p, a_0, R) &= \chi(L_p,\ a_1 + (a_0 \bmod 2),\ \beta_2([0]^{\lfloor a_0 / 2 \rfloor} \cdot R)),
\end{aligned}
$$

and, with $\hat{\beta}_2(\varepsilon) = (1, \varepsilon)$ and $\hat{\beta}_2([a] \cdot S) = (a + 2, S)$, define $\Gamma(b, L, R)$ by

$$
\Gamma(b, L, R) = \begin{cases}
  B(\varepsilon, 0, \chi(L, b, [1])) & \text{if } R = \varepsilon, \\
  B([b + 1] \cdot L, p_1, p_2) & \text{if } R = [0] \cdot R',\ (p_1, p_2) = \hat{\beta}_2(R'), \\
  \Gamma(1, [b] \cdot L, R') & \text{if } R = [1] \cdot R', \\
  \mathrm{Halt} & \text{if } R = [2], \\
  B([0, 1, b] \cdot L, e, R') & \text{if } R = [2, e] \cdot R', \\
  B([2, b] \cdot L, r - 3, R') & \text{if } R = [r] \cdot R' \text{ with } r \ge 3.
\end{cases}
$$

Starting from $s_0 = B([0], 0, \varepsilon)$ (after 4 TM steps), let $L_1 = \beta_1^{3\lfloor d/3 \rfloor}(L)$; then

$$
T(B(L, d, R)) = \begin{cases}
  B([0], p_1, p_2) & \text{if } d \equiv 0 \pmod{3},\ L_1 = \varepsilon,\ (p_1, p_2) = \hat{\beta}_2(R), \\
  B(\varepsilon, 0, \chi(L_p, a_0, \beta_2(R))) & \text{if } d \equiv 0 \pmod{3},\ L_1 = [a_0] \cdot L_p, \\
  \Gamma(q_1, q_2, R) & \text{if } d \equiv 1 \pmod{3},\ (q_1, q_2) = \hat{\beta}_2(L_1), \\
  \mathrm{Halt} & \text{if } d \equiv 2 \pmod{3} \text{ and } R = \varepsilon, \\
  B([0] \cdot \beta_2(L_1), e, R') & \text{if } d \equiv 2 \pmod{3} \text{ and } R = [e] \cdot R'.
\end{cases}
$$

### 3.4 [`1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---`](./M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH.lean)

Over zero-run stacks $D(L, R)$ with $L, R \in \mathbb{N}^*$, define the right sweep $\sigma_B$ by

$$
\begin{aligned}
  \sigma_B(L, \varepsilon) &= D(\iota(L), \varepsilon), &
  \sigma_B(L, [0] \cdot R_t) &= \sigma_B(\iota(L), R_t), \\
  \sigma_B(L, [1] \cdot R_t) &= \sigma_B([0] \cdot \iota(L), R_t), &
  \sigma_B(L, [d + 2] \cdot R_t) &= D(\iota(L), [d + 1] \cdot R_t).
\end{aligned}
$$

Starting from $s_0 = D([1], \varepsilon)$ (after 3 TM steps),

$$
T(D(L, R)) = \begin{cases}
  \sigma_B([0], [1] \cdot R) & \text{if } L = \varepsilon, \\
  \sigma_B(\varepsilon, \iota(\iota(R))) & \text{if } L = [0], \\
  \sigma_B(L'', [0] \cdot \iota(R)) & \text{if } L = [0, 0] \cdot L'', \\
  \sigma_B([k] \cdot L'', \iota(\iota(R))) & \text{if } L = [0, k + 1] \cdot L'', \\
  D(\varepsilon, [1, 0] \cdot R) & \text{if } L = [1], \\
  \sigma_B([0] \cdot L'', [0, 0] \cdot R) & \text{if } L = [1, 0] \cdot L'', \\
  D([k] \cdot L'', [1, 0] \cdot R) & \text{if } L = [1, k + 1] \cdot L'', \\
  \sigma_B(\varepsilon, [2, 1] \cdot R) & \text{if } L = [2], \\
  \mathrm{Halt} & \text{if } L = [2, 0] \cdot L'', \\
  \sigma_B(L'', [0, 1, 1] \cdot R) & \text{if } L = [2, 1] \cdot L'', \\
  \sigma_B([k] \cdot L'', [2, 1] \cdot R) & \text{if } L = [2, k + 2] \cdot L'', \\
  \sigma_B([0, k] \cdot L', [1] \cdot R) & \text{if } L = [k + 3] \cdot L'.
\end{cases}
$$

### 3.5 [`1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB`](./M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean)

Over asymmetric pair stacks $D(L, R)$ with $L \in (\mathbb{N} \times \lbrace 0, 1 \rbrace)^*$ and $R \in (\mathbb{N} \times \lbrace 0, 1, 2 \rbrace)^*$, starting from $s_0 = D(\varepsilon, [(1, 0)])$ (after 3 TM steps):

- When $L = \varepsilon$, $T(D(\varepsilon, \varepsilon)) = D([(0, 0)], [(1, 0)])$ and $T(D(\varepsilon, [(d_1, c_1)] \cdot R')) = \mathrm{runBR}(0, \varepsilon, d_1 + 1, c_1, R')$.
- When $L = [(a, b)] \cdot L'$, $T$ peels $q = \lfloor a/4 \rfloor$ blocks $[(2, 0)]^q$ onto $R$ to form $R_1 = [(2, 0)]^q \cdot R$ and branches on $(a \bmod 4, b)$, halting immediately when $a \equiv 2 \pmod{4}$ and either $L' = \varepsilon$ or $b = 1$, and otherwise invoking the left cascade `runB` or right cascade `runBR` defined in [`M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean`](./M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean) (where `runB` also halts whenever it reaches top residue $a' = 2$ with $L'' = \varepsilon$, or $a' = 2$ and $b' = 1$ with non-empty $L''$).

### 3.6 [`1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA`](./M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean)

Over $(1, 4)$-separator stacks $M_0(L, R)$ with $L, R \in (\mathbb{N} \times \lbrace 1, 2, 3, 4 \rbrace)^*$, define $\tilde{\tau}(\varepsilon) = [(0, 1)]$ and $\tilde{\tau}(X) = X$ for $X \ne \varepsilon$, and for $s \in \lbrace 1, 2, 3, 4 \rbrace$ define $\pi_s$ by

$$
\pi_s(\varepsilon) = \varepsilon, \qquad \pi_1([(a, b')] \cdot X) = [(a + 1, b')] \cdot X, \qquad \pi_{k+1}([(a, b')] \cdot X) = [(0, k), (a, b')] \cdot X \quad (k \in \lbrace 1, 2, 3 \rbrace).
$$

Starting from $s_0 = M_0([(0, 1), (0, 1)], [(1, 1)])$ (after 6 TM steps),

$$
T(M_0(L, R)) = \begin{cases}
  \mathcal{D}(1, L, \varepsilon) & \text{if } R = \varepsilon, \\
  \mathcal{D}(1, L, \pi_s(R_t)) & \text{if } R = [(0, s)] \cdot R_t, \\
  M_0([(0, 1)] \cdot \tilde{\tau}(L), \pi_s(R_t)) & \text{if } R = [(1, s)] \cdot R_t, \\
  M_0([(0, 2)] \cdot \tilde{\tau}(L), \pi_s(R_t)) & \text{if } R = [(2, s)] \cdot R_t, \\
  \mathrm{Halt} & \text{if } R = [(a, s)] \cdot R_t \text{ with } a \ge 3,
\end{cases}
$$

where $\mathcal{D}$ (`stepD`) peels $[(0, 1), (0, 1)]$ pairs on $L$ and, on $[(0, 1), (1, 4)] \cdot L_2$ with $L_2 \ne \varepsilon$, invokes the 6-state carry transducer `evalStage3` over $\mathcal{F} = \lbrace f_{00}, \dots, f_{05} \rbrace$ (halting at `stepD` or `evalQ0Aux` on any head block $[(a, s)] \cdot X$ with $a \ge 2$, and at `stepBit1` on carry state $f_{05}$); see [`M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean`](./M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean) for full definitions.
