# `BB(6)` Accelerations & Behavioral Reductions (`BusyBeaver/BB6/Accelerations/`)

This directory organizes all **`109` unresolved and acceleration-based `BB(6)` holdout machines** (including potential cryptids and Collatz-like reductions) into five dynamical subdirectories, alongside shared stack helpers in [`Stack.lean`](./Stack.lean). Resolved `IsHalt` and `IsNotHalt` proofs live in [`../Halt/`](../Halt/) and [`../NonHalt/`](../NonHalt/).

| Subdirectory | Dynamical Family & Goal Definitions | Machines | Wiki / Community | Ours (Novel) | Details & Examples |
| :--- | :--- | :---: | :---: | :---: | :--- |
| [`FixedArityReduction/`](./FixedArityReduction/README.md) | Fixed-arity `TapePatternSet` / counter accelerations (`IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration`, `IsCryptid`) | `52` | `33` | `19` | [`FixedArityReduction/README.md`](./FixedArityReduction/README.md) |
| [`StackReduction/`](./StackReduction/README.md) | Unbounded two-sided digit-stack systems (`HasStackReduction`, `IsStackCryptid`, stacked `IsValidAcceleration`) | `28` | `10` | `18` | [`StackReduction/README.md`](./StackReduction/README.md) |
| [`OdometerReduction/`](./OdometerReduction/README.md) | Mixed-radix odometer stack & bitstream systems (`HasOdometerReduction`, `IsOdometerCryptid`, odometer `IsValidAcceleration`) | `10` | `1` | `9` | [`OdometerReduction/README.md`](./OdometerReduction/README.md) |
| [`TransducerReduction/`](./TransducerReduction/README.md) | Bidirectional finite-mode word-stack transducers (`IsValidAcceleration`, cf. `HasTransducerReduction`) | `4` | `0` (`1` BMO11 class) | `4` | [`TransducerReduction/README.md`](./TransducerReduction/README.md) |
| [`SegmentedReduction/`](./SegmentedReduction/README.md) | Partitioned `≤ 3`-region segmented half-tape schemas (`IsClosedSegmentedSystem`, `IsSegmentedCryptid`) | `15` | `0` | `15` | [`SegmentedReduction/README.md`](./SegmentedReduction/README.md) |
| **Total** | | **`109`** | **`44`** | **`65`** | |

## Sequence and Stack Notation

Throughout the table and problem statements below, $\mathbb{N} = \lbrace 0, 1, 2, \dots \rbrace$ denotes the non-negative integers, and we use standard sequence (free-monoid) notation for stacks and words:

- **Finite sequences ($\Sigma^{\ast}$):** For any alphabet or entry set $\Sigma$ (such as $\mathbb{N}$, $\lbrace 0, 1 \rbrace$, or $\mathbb{N} \times \lbrace 0, 1 \rbrace$), $\Sigma^{\ast}$ denotes the set of finite sequences $[x_1, x_2, \dots, x_m]$ of length $m \ge 0$ with $x_i \in \Sigma$, ordered from the active top/front entry ($x_1$) to the bottom/back entry ($x_m$).
- **Empty sequence ($\varepsilon$):** We write $\varepsilon \in \Sigma^{\ast}$ for the empty sequence of length $0$ (written `[]` in Lean). Note that $[0]$ has length $1$ (sole entry $0$), whereas $\varepsilon$ has length $0$.
- **Concatenation, push, and pop ($X \cdot Y$):** For $X, Y \in \Sigma^{\ast}$, $X \cdot Y$ denotes sequence concatenation (written `X ++ Y` in Lean), with $\varepsilon \cdot X = X \cdot \varepsilon = X$. In particular:
  - $[x] \cdot X$ pushes/prepends a single entry $x \in \Sigma$ onto the front of $X$ (written `x :: X` in Lean), and $[x, y] \cdot X$ pushes $x$ followed by $y$ (`x :: y :: X` in Lean).
  - Writing $X = [x] \cdot X'$ in a branch condition matches a non-empty sequence $X$ with top entry $x$ and remaining tail $X'$.
- **Repetition and reversal ($[x]^k$, $X^{\mathrm{rev}}$):** For $k \in \mathbb{N}$, $[x]^k$ denotes the sequence $[x, \dots, x]$ of $k$ copies of $x$ (with $[x]^0 = \varepsilon$), and $[x_1, \dots, x_m]^{\mathrm{rev}} = [x_m, \dots, x_1]$.
- **Head-increment operators ($\beta_k$, $\iota$):** On integer stacks $X \in \mathbb{N}^{\ast}$, we define:

$$
\beta_k(\varepsilon) = [k - 1] \quad (k \ge 1), \qquad \beta_k([x] \cdot X) = [x + k] \cdot X, \qquad \iota(\varepsilon) = \varepsilon, \qquad \iota([x] \cdot X) = [x + 1] \cdot X,
$$

and write $\beta_1^m$ for the $m$-fold iterate of $\beta_1$ (`bumpHead` in Lean).
