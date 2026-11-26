# Odometer Reductions (`OdometerReduction/`)

<!-- TODO (Marco): Expand overview for mixed-radix odometer reductions (`HasOdometerReduction`, `IsOdometerCryptid`, open odometer `IsValidAcceleration`). -->

In an odometer reduction, one side of the tape acts as a positional or mixed-radix counter stack whose discrete capacity decrements by $1$ via recursive borrow propagation on each reflection from the active head, until reaching zero capacity triggers a global drain/reset sweep across the entire stack. Unlike classical periodic odometers in ergodic theory, each carry-propagation or zero-capacity drain (`drain`, $\Lambda$, $\Omega$, $\rho$) dynamically rewrites the active stream on the opposite half-tape, coupling numeration-system carries with variable-length prefix parsing across exponentially separated timescales. On the `bbchallenge` Wiki this class includes **Beaver Math Olympiad Problem 11** (formalized under `HasOdometerReduction` above); the seven open problems below include a direct ternary-alphabet odometer sibling (`1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`, also proved under `HasOdometerReduction`) alongside six open carry-and-drain accelerations.

This directory collects all **`10` odometer `BB(6)` holdout machines** (`1` Wiki and `9` novel reductions): `1` structural `HasOdometerReduction` (*BMO Problem 11* macro twin), `1` combined `HasOdometerReduction` + `IsValidAcceleration` (`HighLevelState`) open problem, `6` open odometer `IsValidAcceleration` problems (`5` with `HighLevelState`), and `2` hard odometer potential cryptids (`IsOdometerCryptid`).

## Machines (10 Total: 1 Wiki, 9 Ours)

| Machine (`bbchallenge` RLE) | Origin | Proved Properties | State Space / Notes | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- |
| `1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB` | Wiki | `HasOdometerReduction` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LD_0LC0RE_1LA0RD_0RB0LC_1RC1RF_0LD---) ([BMO Problem 11](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad), macro-equivalent reflected holdout) | [`M_1RB0LD_0RCHHH_1LD0RF_0LE0RA_0RA1LF_0LA1LB.lean`](./M_1RB0LD_0RCHHH_1LD0RF_0LE0RA_0RA1LF_0LA1LB.lean) |
| `1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA` | Ours (Novel) | `IsValidAcceleration` (`State`, `HighLevelState`) | $B(L, R) \to B_{\mathrm{HL}}(R) \in \mathbb{N}^{\ast}$ (from $B(\varepsilon, [0, 1])$) | [`M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA.lean`](./M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA.lean) |
| `1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD` | Ours (Novel) | `IsValidAcceleration` (`State`, `HighLevelState`) | $E(a, L, d, R) \to E_{\mathrm{HL}}(k, d, R) \in \mathbb{N}^2 \times \mathbb{N}^{\ast}$ (from $E(1, \varepsilon, 0, \varepsilon)$) | [`M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD.lean`](./M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD.lean) |
| `1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---` | Ours (Novel) | `HasOdometerReduction`, `IsValidAcceleration` (`State`, `HighLevelState`) | $(L, w) \to W(w) \in \lbrace 0, 1 \rbrace^{\ast}$ (from $(\varepsilon, \varepsilon)$) | [`M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH.lean`](./M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH.lean) |
| `1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD` | Ours (Novel) | `IsValidAcceleration` (`State`, `HighLevelState`) | $B(L, E, c) \to B_{\mathrm{HL}}(E, c) \in \mathbb{N}^{\ast} \times \mathbb{N}$ (from $B([0], \varepsilon, 1)$) | [`M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD.lean`](./M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD.lean) |
| `1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA` | Ours (Novel) | `IsValidAcceleration` | $E(d, R) \in \mathbb{N} \times \mathbb{N}^{\ast}$ (from $E(0, [0])$) | [`M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA.lean`](./M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA.lean) |
| `1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---` | Ours (Novel) | `IsValidAcceleration` (`State`, `HighLevelState`) | $E(R) \to E_{\mathrm{HL}}(R) \in \mathbb{N}^{\ast}$ (from $E(\varepsilon)$) | [`M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH.lean`](./M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH.lean) |
| `1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD` | Ours (Novel) | `IsValidAcceleration` (`State`, `HighLevelState`) | $E_L, E_0 \to E_{L,\mathrm{HL}}(a, L, d, R)$ (from $E_L(1, \varepsilon, 1, \varepsilon)$) | [`M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD.lean`](./M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD.lean) |
| `1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1RA---` | Ours (Novel) | ``IsOdometerCryptid`` | Potential cryptid (mixed-radix odometer bitstream) | [`M_1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1RAHHH.lean`](./M_1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1RAHHH.lean) |
| `1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA` | Ours (Novel) | ``IsOdometerCryptid`` | Potential cryptid (mixed-radix odometer bitstream) | [`M_1RBHHH_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA.lean`](./M_1RBHHH_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA.lean) |

## Odometer Reduction Equations (7 Examples)

### [`1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA`](./M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA.lean)

Over states $B(L, R)$ with $L, R \in \mathbb{N}^{\ast}$, define $\rho : \mathbb{N} \times \mathbb{N}^{\ast} \to \mathbb{N}^{\ast}$ by

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

Starting from $s_0 = B(\varepsilon, [0, 1])$ (after 16 TM steps),

$$
T(B(L, \varepsilon)) = B(\varepsilon, L^{\mathrm{rev}} \cdot [0, 0]), \qquad T(B(L, [d] \cdot R)) = \zeta(0, [0]^d \cdot L, R).
$$

**High-level acceleration ($T_{\mathrm{HL}}$):** Restricting to the Poincaré return section $L = \varepsilon$ eliminates the left stack completely over $B_{\mathrm{HL}}(R) := B(\varepsilon, R)$. Define $\pi_0(a, [0, 0] \cdot R) = \pi_0(a + 2, R)$ and $\pi_0(a, R) = (a, R)$ when $R$ does not begin with $[0, 0]$, and define $\mathcal{S}(L, \varepsilon) = B_{\mathrm{HL}}(L^{\mathrm{rev}} \cdot [0, 0])$ and, for $L_1 = [0]^d \cdot L$ and $(p_1, p_2) = \pi_0(0, R_1)$,

$$
\mathcal{S}(L, [d] \cdot R_1) = \begin{cases}
  \mathrm{Halt} & \text{if } p_2 = \varepsilon, \\
  B_{\mathrm{HL}}(L_1^{\mathrm{rev}} \cdot [p_1 + 2, 0]) & \text{if } p_2 = [0], \\
  \mathcal{S}([p_1 + 2] \cdot L_1, [e - 1] \cdot R_4) & \text{if } p_2 = [0, e] \cdot R_4 \text{ with } e \ge 1, \\
  \mathcal{S}([p_1 + 1] \cdot L_1, \rho(c - 1, R_3)) & \text{if } p_2 = [c] \cdot R_3 \text{ with } c \ge 1.
\end{cases}
$$

Starting from $s_{0,\mathrm{HL}} = B_{\mathrm{HL}}([0, 1])$, $T_{\mathrm{HL}}(B_{\mathrm{HL}}(R)) = \mathcal{S}(\varepsilon, R)$.

### [`1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD`](./M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD.lean)

Over states $E(a, L, d, R)$ with $a, d \in \mathbb{N}$ and $L, R \in \mathbb{N}^{\ast}$, define the boundary bounce $\eta$ by

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

Starting from $s_0 = E(1, \varepsilon, 0, \varepsilon)$ (after 6 TM steps),

$$
T(E(a, L, d, R)) = \begin{cases}
  \Lambda(\mu(a + 3), L, a + 3, [0]) & \text{if } d = 0 \text{ and } R = \varepsilon, \\
  \Lambda(\mu(a + 1), L, a + e + 4, R') & \text{if } d = 0 \text{ and } R = [e] \cdot R', \\
  \mathrm{Halt} & \text{if } d \ge 1 \text{ is odd and } R = \varepsilon, \\
  E(a + 3, L, e, R') & \text{if } d = 1 \text{ and } R = [e] \cdot R', \\
  E(0, [0]^{(d-3)/2} \cdot [a + 3] \cdot L, e, R') & \text{if } d \ge 3 \text{ is odd and } R = [e] \cdot R', \\
  \Lambda(\mathsf{A}, [0]^{(d-2)/2} \cdot [a + 3] \cdot L, 0, [0]) & \text{if } d \ge 2 \text{ is even and } R = \varepsilon, \\
  \Lambda(\mathsf{A}, [0]^{(d-2)/2} \cdot [a + 3] \cdot L, e + 1, R') & \text{if } d \ge 2 \text{ is even and } R = [e] \cdot R'.
\end{cases}
$$

**High-level acceleration ($T_{\mathrm{HL}}$):** Every left-boundary bounce produces $a = 0$ and $L = [0]^k \cdot [1]$, collapsing the left stack $L$ to a single counter $k \in \mathbb{N}$ over $E_{\mathrm{HL}}(k, d, R) := E(0, [0]^k \cdot [1], d, R)$. Defining $\eta_{\mathrm{HL}}$ identically to $\eta$ with $E(0, [0]^m \cdot [1], d', R')$ replaced by $E_{\mathrm{HL}}(m, d', R')$, $\Lambda_{\mathrm{HL}}$ on prefixes $P$ above the bottom $[1]$ sentinel ($\Lambda_{\mathrm{HL}}(\mathsf{A}, \varepsilon, d, R) = \eta_{\mathrm{HL}}(d + 3, R)$, $\Lambda_{\mathrm{HL}}(\mathsf{B}, \varepsilon, d, R) = E_{\mathrm{HL}}(0, d + 1, R)$, $\Lambda_{\mathrm{HL}}(\mathsf{BR}, \varepsilon, d, R) = E_{\mathrm{HL}}(0, 0, [d] \cdot R)$, and the $\Lambda$ step rules on $[x] \cdot P$), and $\Sigma_R(a, P, d, R)$ by contracting the two odd $d$ right-step branches ($d = 1$ and $d \ge 3$ odd with $R = [e] \cdot R'$) recursively before calling $\Lambda_{\mathrm{HL}}$, we have $T_{\mathrm{HL}}(E_{\mathrm{HL}}(k, d, R)) = \Sigma_R(0, [0]^k, d, R)$ starting from $s_{0,\mathrm{HL}} = E_{\mathrm{HL}}(2, 0, \varepsilon)$ (1 `next` step from $s_0$).

### [`1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---`](./M_1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LDHHH.lean)

Over $(L, w) \in \lbrace L_0, L_1, L_2 \rbrace^{\ast} \times \lbrace 0, 1 \rbrace^{\ast}$, define the mixed-radix capacity $\mathrm{cap}$, odometer decrement $\mathrm{dec}$ (satisfying $\mathrm{cap}(\mathrm{dec}(L)) = \mathrm{cap}(L) - 1$ whenever $\mathrm{cap}(L) \ge 1$), and zero-capacity drain word $\mathrm{drain}$ by

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

Write $\mathcal{L}(L, u) = (\mathrm{dec}(L), u)$ if $\mathrm{cap}(L) \ge 1$ and $\mathcal{L}(L, u) = (\varepsilon, \mathrm{drain}(L) \cdot u)$ if $\mathrm{cap}(L) = 0$. Identifying any finite bit sequence $w \in \lbrace 0, 1 \rbrace^{\ast}$ with its zero-padded stream (so missing trailing bits read as $0$, i.e. $\varepsilon$ has leading bit $0$ and remaining tail $\varepsilon$), starting from $s_0 = (\varepsilon, \varepsilon)$ (after 2 TM steps):

$$
T(L, w) = \begin{cases}
  \mathcal{L}(L, [1] \cdot w') & \text{if } w \text{ has leading prefix } [0] \text{ with tail } w', \\
  ([L_2] \cdot L, w') & \text{if } w \text{ has leading prefix } [1, 0, 0] \text{ or } [1, 1, 0] \text{ with tail } w', \\
  ([L_0] \cdot L, w') & \text{if } w \text{ has leading prefix } [1, 0, 1, 0] \text{ with tail } w', \\
  \mathcal{L}(L, [1, 0, 0, 0] \cdot w') & \text{if } w \text{ has leading prefix } [1, 0, 1, 1] \text{ with tail } w', \\
  \mathrm{Halt} & \text{if } w \text{ has leading prefix } [1, 1, 1].
\end{cases}
$$

**High-level acceleration ($T_{\mathrm{HL}}$):** Restricting to the empty-odometer Poincaré section $L = \varepsilon$ eliminates the mixed-radix odometer stack $L$ completely, yielding a pure binary-word dynamical system on $W(w) := (\varepsilon, w) \in \lbrace 0, 1 \rbrace^{\ast}$ starting from $s_{0,\mathrm{HL}} = W(\varepsilon)$. Define $\mathcal{O}(L, w)$ (again reading missing trailing bits after a leading $1$ as $0$ with tail $\varepsilon$) by

$$
\mathcal{O}(L, w) = \begin{cases}
  W(\mathrm{drain}(L) \cdot [1]) & \text{if } w = \varepsilon \text{ and } \mathrm{cap}(L) = 0, \\
  \mathcal{O}([L_2] \cdot \mathrm{dec}(L), \varepsilon) & \text{if } w = \varepsilon \text{ and } \mathrm{cap}(L) \ge 1, \\
  W(\mathrm{drain}(L) \cdot [1] \cdot w') & \text{if } w = [0] \cdot w' \text{ and } \mathrm{cap}(L) = 0, \\
  \mathcal{O}(\mathrm{dec}(L), [1] \cdot w') & \text{if } w = [0] \cdot w' \text{ and } \mathrm{cap}(L) \ge 1, \\
  \mathcal{O}([L_2] \cdot L, w') & \text{if } w \text{ has leading prefix } [1, 0, 0] \text{ or } [1, 1, 0] \text{ with tail } w', \\
  \mathcal{O}([L_0] \cdot L, w') & \text{if } w \text{ has leading prefix } [1, 0, 1, 0] \text{ with tail } w', \\
  W(\mathrm{drain}(L) \cdot [1, 0, 0, 0] \cdot w') & \text{if } w \text{ has leading prefix } [1, 0, 1, 1] \text{ with tail } w' \text{ and } \mathrm{cap}(L) = 0, \\
  \mathcal{O}(\mathrm{dec}(L), [1, 0, 0, 0] \cdot w') & \text{if } w \text{ has leading prefix } [1, 0, 1, 1] \text{ with tail } w' \text{ and } \mathrm{cap}(L) \ge 1, \\
  \mathrm{Halt} & \text{if } w \text{ has leading prefix } [1, 1, 1],
\end{cases}
$$

with $T_{\mathrm{HL}}(W(w)) = \mathcal{O}(\varepsilon, w)$.

### [`1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD`](./M_1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_HHH1RD.lean)

Over states $B(L, E, c)$ with $L, E \in \mathbb{N}^{\ast}$ and $c \in \mathbb{N}$, define the left drain $\Delta$ by $\Delta(\varepsilon, E, c) = B([0], E, c)$ and, for $[a] \cdot L'$:

$$
\Delta([a] \cdot L', E, c) = \begin{cases}
  B(\beta_1(L'), [0]^{\lfloor a/2 \rfloor + 1} \cdot E, c) & \text{if } a \text{ is odd}, \\
  \Delta(L', \varepsilon, c + 2) & \text{if } a \text{ is even and } [0]^{a/2} \cdot E = \varepsilon, \\
  \Delta(L', [e + 1] \cdot E_t, c) & \text{if } a \text{ is even and } [0]^{a/2} \cdot E = [e] \cdot E_t.
\end{cases}
$$

Starting from $s_0 = B([0], \varepsilon, 1)$ (after 4 TM steps),

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

**High-level acceleration ($T_{\mathrm{HL}}$):** Restricting to $L = [0]$ eliminates the left stack $L$ on $B_{\mathrm{HL}}(E, c) := B([0], E, c)$. Define $\Delta_{\mathrm{ev}}(\varepsilon, E, c) = B_{\mathrm{HL}}(E, c)$, $\Delta_{\mathrm{ev}}([h] \cdot H, E, c) = \Delta_{\mathrm{ev}}(H, \varepsilon, c + 2)$ when $[0]^h \cdot E = \varepsilon$ and $\Delta_{\mathrm{ev}}(H, [e + 1] \cdot E_t, c)$ when $[0]^h \cdot E = [e] \cdot E_t$, together with $\Delta_{\mathrm{odd}}(h_0, \varepsilon, E, c) = B_{\mathrm{HL}}([0]^{h_0 + 1} \cdot E, c)$ and $\Delta_{\mathrm{odd}}(h_0, [h_1] \cdot H, E, c) = \Delta_{\mathrm{odd}}(h_1, H, [1] \cdot [0]^{h_0 - 1} \cdot E, c)$. Defining the pair-peel map $\mathcal{P}(h_0, H, E, c)$ by

$$
\mathcal{P}(h_0, H, E, c) = \begin{cases}
  \Delta_{\mathrm{ev}}([h_0 + c/2] \cdot H, \varepsilon, 3) & \text{if } E = \varepsilon \text{ and } c \text{ is even}, \\
  \Delta_{\mathrm{odd}}(h_0 + \lfloor c/2 \rfloor, H, \varepsilon, 3) & \text{if } E = \varepsilon \text{ and } c \text{ is odd}, \\
  \Delta_{\mathrm{ev}}([h_0 + e_0] \cdot H, \varepsilon, 2) & \text{if } E = [e_0],\ c = 0, \\
  \mathrm{Halt} & \text{if } E = [e_0],\ c = 1, \\
  \Delta_{\mathrm{odd}}(h_0 + e_0, H, [1], 1) & \text{if } E = [e_0],\ c = 2, \\
  \Delta_{\mathrm{ev}}([h_0 + e_0] \cdot H, [1], 0) & \text{if } E = [e_0],\ c = 3, \\
  \Delta_{\mathrm{ev}}([h_0 + e_0] \cdot H, [1, 0], c - 4) & \text{if } E = [e_0],\ c \ge 4, \\
  \Delta_{\mathrm{ev}}([h_0 + e_0] \cdot H, [1] \cdot E_2, c) & \text{if } E = [e_0, 0] \cdot E_2, \\
  \mathcal{P}(2, [h_0 + e_0] \cdot H, E_2, c) & \text{if } E = [e_0, 1] \cdot E_2, \\
  \Delta_{\mathrm{ev}}([2, h_0 + e_0] \cdot H, [e_1 - 2] \cdot E_2, c) & \text{if } E = [e_0, e_1] \cdot E_2 \text{ with } e_1 \ge 2,
\end{cases}
$$

we obtain $T_{\mathrm{HL}}(B_{\mathrm{HL}}(E, c)) = \mathcal{P}(0, \varepsilon, E, c)$ from $s_{0,\mathrm{HL}} = B_{\mathrm{HL}}(\varepsilon, 1)$.

### [`1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA`](./M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA.lean)

Over states $E(d, R)$ with $d \in \mathbb{N}$ and $R \in \mathbb{N}^{\ast}$, define the return drain $\Omega$ by

$$
\begin{aligned}
  \Omega(\varepsilon, d, R) &= E(d + 2, R), \\
  \Omega([j], d, R) &= E(1, [0]^j \cdot [d + 1] \cdot R), \\
  \Omega([0, j_2] \cdot K, d, R) &= \Omega(K, 2j_2 + d + 6, R), \\
  \Omega([j_1 + 1, j_2] \cdot K, d, R) &= \Omega(K, 2j_2 + 5, [0]^{j_1} \cdot [d + 1] \cdot R).
\end{aligned}
$$

Starting from $s_0 = E(0, [0])$ (after 4 TM steps), $T(E(d, R)) = \Sigma(\varepsilon, d, R)$, where

$$
\Sigma(K, d, R) = \begin{cases}
  \mathrm{Halt} & \text{if } R = \varepsilon \text{ and } d \text{ is odd}, \\
  E(1, [0]^{d/2 + 1}) & \text{if } R = \varepsilon,\ d \text{ is even, and } K = \varepsilon, \\
  \Omega(K', 2j_2 + 5, [0]^{d/2}) & \text{if } R = \varepsilon,\ d \text{ is even, and } K = [j_2] \cdot K', \\
  \Sigma([\lfloor d/2 \rfloor] \cdot K, e, R') & \text{if } R = [e] \cdot R' \text{ and } d \text{ is odd}, \\
  \Omega(K, d + e + 2, R') & \text{if } R = [e] \cdot R' \text{ and } d \text{ is even}.
\end{cases}
$$

### [`1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---`](./M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH.lean)

Over states $E(R)$ with $R \in \mathbb{N}^{\ast}$, define $\phi(\varepsilon) = \phi([0]) = \varepsilon$, $\phi([0, r_2] \cdot R) = [0, r_2 + 1] \cdot R$, and $\phi([r + 1] \cdot R) = [r] \cdot R$. Define the return pass $\rho : \lbrace 0, 1 \rbrace \times \lbrace 0, 1 \rbrace^{\ast} \times \mathbb{N}^{\ast} \to \mathbb{N}^{\ast}$ by

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

Starting from $s_0 = E(\varepsilon)$ (after 6 TM steps),

$$
T(E(\varepsilon)) = E([0, 0]), \quad T(E([0] \cdot R)) = \sigma(0, [0, 0], R), \quad T(E([1] \cdot R)) = \sigma(1, [0], R), \quad T(E([r] \cdot R)) = \mathrm{Halt}\ (r \ge 2).
$$

**High-level acceleration ($T_{\mathrm{HL}}$):** Every step from $s_0$ produces a stack with leading entry $0$. Peeling this invariant leading $0$ over $E_{\mathrm{HL}}(R) := E([0] \cdot R)$ from $s_{0,\mathrm{HL}} = E_{\mathrm{HL}}([0])$ (1 `next` step from $s_0$) absorbs both $\phi$ and the trailing $[0, 0]$ bit seed: defining $\rho_{\mathrm{HL}}$ by the same step clauses as $\rho$ except $\rho_{\mathrm{HL}}(0, \varepsilon, R) = \beta_1(\beta_1(R))$, $\rho_{\mathrm{HL}}(1, \varepsilon, R) = [3] \cdot \beta_1(R)$, and $\rho_{\mathrm{HL}}(1, [1], R) = [1, 0] \cdot \beta_1(R)$, and $\sigma_{\mathrm{HL}}$ identically to $\sigma$ (using $\rho_{\mathrm{HL}}$ and $E_{\mathrm{HL}}$), we have $T_{\mathrm{HL}}(E_{\mathrm{HL}}(R)) = \sigma_{\mathrm{HL}}(0, \varepsilon, R)$.

### [`1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD`](./M_1RB1RF_1LC1LF_HHH1LD_1LE0RA_1RE1LB_1RD0LD.lean)

Over states $E_L(a, L, d, R)$ and $E_0(L, R)$ with $a, d \in \mathbb{N}$ and $L, R \in \mathbb{N}^{\ast}$, let $\hat{\beta}_1(\varepsilon) = (0, \varepsilon)$, $\hat{\beta}_1([x] \cdot X) = (x + 1, X)$, $\pi_E(0, R) = R$, and $\pi_E(k + 1, R) = \pi_E(k, [0] \cdot \beta_1(\beta_1(R)))$. Define $\Phi(L, R)$ and $\Psi(L, R)$ by

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

Starting from $s_0 = E_L(1, \varepsilon, 1, \varepsilon)$ (after 5 TM steps), $T(E_0(L, R)) = \Psi(L, R)$, while for $E_L(a, L, d, R)$ with $R_1 = \pi_E(\lfloor a/4 \rfloor, [d] \cdot R)$ and $(p_1, p_2) = \hat{\beta}_1(R_1)$:

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

**High-level acceleration ($T_{\mathrm{HL}}$):** Eliminating $E_0$ yields a single-mode system on $E_{L,\mathrm{HL}}(a, L, d, R) := E_L(a, L, d, R)$ starting from $s_{0,\mathrm{HL}} = E_{L,\mathrm{HL}}(1, \varepsilon, 1, \varepsilon)$. Writing $L = [1]^k \cdot L_{\mathrm{rem}}$ (where $L_{\mathrm{rem}}$ does not begin with $1$) and $\zeta_0^k$ for the $k$-fold iterate of $S \mapsto [0] \cdot \beta_1(S)$, $\Psi_{\mathrm{HL}}(L, R)$ contracts all leading $1$-peels of $\Psi$ in one shot—returning $\Phi_{\mathrm{HL}}(\zeta_0^k([0, 0]), R)$ if $L_{\mathrm{rem}} = \varepsilon$, $\Phi_{\mathrm{HL}}(\zeta_0^k([0, 1, 0]), R)$ if $L_{\mathrm{rem}} = [0]$, $E_{L,\mathrm{HL}}(a, L_t', 0, [1]^{k+1} \cdot R)$ if $L_{\mathrm{rem}} = [0, a] \cdot L_t'$, and $E_{L,\mathrm{HL}}(x - 2, L_t, 0, [1]^{k+1} \cdot R)$ if $L_{\mathrm{rem}} = [x] \cdot L_t$ ($x \ge 2$)—while $\Phi_{\mathrm{HL}}(L, R)$ replaces $E_0(\beta_1(L), [d] \cdot R')$ on $R = [d + 3] \cdot R'$ with $\Psi_{\mathrm{HL}}(\beta_1(L), [d] \cdot R')$, and $T_{\mathrm{HL}}$ replaces every $E_0$ and $\Phi$ branch of $T(E_L(\dots))$ with $\Psi_{\mathrm{HL}}$ and $\Phi_{\mathrm{HL}}$.

---
