# Transducer Reductions (`TransducerReduction/`)

<!-- TODO (Marco): Expand overview for bidirectional word-stack transducer reductions (`IsValidAcceleration`, cf. `HasTransducerReduction`). -->

In a transducer reduction, neither half-tape acts as a dominant scalar counter: instead, both half-tapes are words over a finite or run-length block alphabet, and each macro-step sweeps a stateful finite-mode carry head (a sequential Mealy transducer) across an arbitrarily long prefix of blocks, rewriting every block in transit before reflecting at the blank boundary or an interior stop pattern. Halting reduces to the **iterated transducer mortality / forbidden-subword problem**—determining whether repeated bidirectional sweeps from $s_0$ ever synthesize a specific local halting block or carry state (such as a block of height $\ge 3$ or a designated halting carry mode). The four open problems below capture pure zero-run, pair-block, and multi-separator bidirectional transducers in `BB(6)`.

This directory holds the **`4` transducer `BB(6)` holdout problems** (all novel `IsValidAcceleration` reductions; `#118` belongs to the *BMO Problem 11* odometer family).

## Machines (4 Total)

| Machine (`bbchallenge` RLE) | Origin | Proved Properties | State Space / Notes | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- |
| `1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF` | Ours (Novel) | `IsValidAcceleration` | $E(L, R) \in \mathbb{N}^{\ast} \times \mathbb{N}^{\ast}$ (from $E([1], \varepsilon)$) | [`M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF.lean`](./M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF.lean) |
| `1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC` | Ours (Novel) | `IsValidAcceleration` (`State`, `HighLevelState`) | $E(L, R) \to E_{\mathrm{HL}}(R) \in (\mathbb{N} \times \lbrace 0, 1 \rbrace)^{\ast}$ (from $E([(1, 0)], [(0, 0)])$) | [`M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean`](./M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean) |
| `1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB` | Ours (Novel) | `IsValidAcceleration` | $D(L, R) \in (\mathbb{N} \times \lbrace 0, 1 \rbrace)^{\ast} \times (\mathbb{N} \times \lbrace 0, 1, 2 \rbrace)^{\ast}$ (from $D(\varepsilon, [(1, 0)])$) | [`M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean`](./M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean) |
| `1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA` | Ours (Novel) / [BMO 11](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad) class | `IsValidAcceleration` | $M_0(L, R) \in (\mathbb{N} \times \lbrace 1, 2, 3, 4 \rbrace)^{\ast} \times (\mathbb{N} \times \lbrace 1, 2, 3, 4 \rbrace)^{\ast}$ (from $M_0([(0, 1), (0, 1)], [(1, 1)])$); [BMO 11](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad) odometer equivalence class (`Hardness.lean`) | [`M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean`](./M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean) |

## Transducer Reduction Equations (4 Examples)

### [`1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF`](./M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF.lean)

Over zero-run stacks $E(L, R)$ with $L, R \in \mathbb{N}^{\ast}$, define the 3-mode right transducer $\Sigma_R$ over modes $m \in \lbrace \mathsf{a}, \mathsf{b}, \mathsf{c} \rbrace$ by $\Sigma_R(\mathsf{a}, L, \varepsilon) = E([1] \cdot L, \varepsilon)$, $\Sigma_R(\mathsf{b}, L, \varepsilon) = E(\iota(L), \varepsilon)$, $\Sigma_R(\mathsf{c}, L, \varepsilon) = E(L, \varepsilon)$, and $\Sigma_R(m, L, [d] \cdot R_t) = \psi_d(m, L, R_t)$, where

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

### [`1RB0RE_0RC1RE_1RD1LE_0LE---_1RA1LF_1RF0LC`](./M_1RB0RE_0RC1RE_1RD1LE_0LEHHH_1RA1LF_1RF0LC.lean)

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

and define the right bounce $\mathcal{B}$ on $R \in (\mathbb{N} \times \lbrace 0, 1 \rbrace)^{\ast}$ by

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

**High-level acceleration ($T_{\mathrm{HL}}$):** Restricting to the $L = \varepsilon$ Poincaré return section eliminates both the left stack $L$ and the boundary tables $\kappa, \zeta_0$ on $E_{\mathrm{HL}}(R) := E(\varepsilon, R)$. With $\xi(r_{01}, R') = E_{\mathrm{HL}}([(0, 1)] \cdot R')$, $\xi(r_{10}, R') = E_{\mathrm{HL}}([(0, 0), (0, 0)] \cdot R')$, $\xi(r_{11}, R') = E_{\mathrm{HL}}([(0, 0), (0, 1)] \cdot R')$, and $\xi(r_{21}, R') = E_{\mathrm{HL}}([(1, 0), (0, 1)] \cdot R')$, starting from $s_{0,\mathrm{HL}} = E_{\mathrm{HL}}([(0, 1)])$ (1 `next` step from $s_0$):

$$
T_{\mathrm{HL}}(E_{\mathrm{HL}}(R)) = \begin{cases}
  E_{\mathrm{HL}}([(0, 0), (0, 1)]) & \text{if } R = \varepsilon, \\
  E_{\mathrm{HL}}([(1, 0)] \cdot \iota_H(R_1)) & \text{if } R = [(0, 0)] \cdot R_1, \\
  E_{\mathrm{HL}}([(1, 0), (0, 0)] \cdot R_1) & \text{if } R = [(0, 1)] \cdot R_1, \\
  \xi(\mathcal{B}([(d, b)] \cdot R_1)) & \text{if } R = [(d + 1, b)] \cdot R_1 \text{ (or } \mathrm{Halt} \text{ if } \mathcal{B} \text{ halts)}.
\end{cases}
$$

### [`1RB1RE_1LC0RA_---1LD_1LA0LF_0LB0LC_1RB0LB`](./M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean)

Over asymmetric pair stacks $D(L, R)$ with $L \in (\mathbb{N} \times \lbrace 0, 1 \rbrace)^{\ast}$ and $R \in (\mathbb{N} \times \lbrace 0, 1, 2 \rbrace)^{\ast}$, starting from $s_0 = D(\varepsilon, [(1, 0)])$ (after 3 TM steps):

- When $L = \varepsilon$, $T(D(\varepsilon, \varepsilon)) = D([(0, 0)], [(1, 0)])$ and $T(D(\varepsilon, [(d_1, c_1)] \cdot R')) = \mathrm{runBR}(0, \varepsilon, d_1 + 1, c_1, R')$.
- When $L = [(a, b)] \cdot L'$, $T$ peels $q = \lfloor a/4 \rfloor$ blocks $[(2, 0)]^q$ onto $R$ to form $R_1 = [(2, 0)]^q \cdot R$ and branches on $(a \bmod 4, b)$, halting immediately when $a \equiv 2 \pmod{4}$ and either $L' = \varepsilon$ or $b = 1$, and otherwise invoking the left cascade `runB` or right cascade `runBR` defined in [`M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean`](./M_1RB1RE_1LC0RA_HHH1LD_1LA0LF_0LB0LC_1RB0LB.lean) (where `runB` also halts whenever it reaches top residue $a' = 2$ with $L'' = \varepsilon$, or $a' = 2$ and $b' = 1$ with non-empty $L''$).

### [`1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA`](./M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean)

Over $(1, 4)$-separator stacks $M_0(L, R)$ with $L, R \in (\mathbb{N} \times \lbrace 1, 2, 3, 4 \rbrace)^{\ast}$, define $\tilde{\tau}(\varepsilon) = [(0, 1)]$ and $\tilde{\tau}(X) = X$ for $X \ne \varepsilon$, and for $s \in \lbrace 1, 2, 3, 4 \rbrace$ define $\pi_s$ by

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
