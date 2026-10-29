/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic

/-!
# Hardness of the BB(6) Holdouts: the Cryptid Core

This page records *why* the hardest BB(6) holdouts are hard, in the vocabulary the `bbchallenge`
community uses for [Cryptids](https://wiki.bbchallenge.org/wiki/Cryptids) (Antihydra, Space Needle,
Lucy's Moonlight), applied uniformly to the machines formalized in this repository. Every reduction
cited here is kernel-verified (`HasCollatzReduction`, `HasStackReduction`, `IsValidAcceleration`);
every hazard statement is a *heuristic* computed from the certified rules by exact accelerated
simulation and is marked as such. The full dossiers, with reproduction commands, accompany the arXiv
report; this page is the summary.

## 1. The hardness vocabulary

A cryptid's halting condition is decided by a **residue sequence** (parities, base-3 digits, 2-adic
valuations) that passes every statistical test for randomness. Three facts classify a machine:

* **Halting trigger** — how residues become a halting event: **RW** (gambler's ruin: a long run of
  residues must go wrong; Hydra/Antihydra), **RES** (one residue at an era reset; Lucy's Moonlight),
  **EQ**/**POW** (two independently evolving quantities must coincide exactly, or a value must be an
  exact power of two / Mersenne number; Space Needle).
* **Growth regime** — linear, exponential, or tetrational mass; it fixes the decay of the per-test
  hazard $p_t$: geometric (RW), constant (RES), or $\sim m/W_t$ for a target of $m$ values in a
  window of width $W_t$ (EQ/POW).
* **Shield** — an inductive invariant (parity lock, mod-3 head, digit bound) that disables halting
  arms on all (*full*), almost all (*leaky*) or some (*partial*) steps.

The verdict follows the Borel–Cantelli bookkeeping of the community's *probviously*:
$\sum_t p_t < \infty$ gives probviously non-halting with the tail as residual probability;
$\sum_t p_t = \infty$ gives probviously halting; two decided sinks give the *undecided type*. **A
critical ($\sum 1/t$) hazard is a prediction that the machine halts within computational reach** —
see the calibration case below.

## 2. The core

Thirty-three classes of the 2026-10-24 holdout list (623 classes) are hard in this sense: the five
first-order problems of the report, the shielded single-base exponential cascades, and the
Collatz-like stacked cryptids. Eight were known to the community before our campaign; the rest are
new. Problem S1 (`#72`) is listed last because the community has since **proved that it halts**.

Not listed below, but counted as hard by our solvability census, is the base-3 odometer family of
[BMO Problem 11](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad): the holdout
`1RB0LD_0RC---_1LD0RF_0LE0RA_0RA1LF_0LA1LB` (#15, macro-equivalent to the wiki's Problem 11 machine,
[`HasOdometerReduction`](./Accelerations/M_1RB0LD_0RCHHH_1LD0RF_0LE0RA_0RA1LF_0LA1LB.lean)) together
with eleven holdout classes that run the same odometer up to a proof isomorphism (`#14`, `#49`,
`#118`, `#223`, `#278`, `#301`, `#304`, `#313`, `#325`, `#566`, `#652`; `#118` is
[formalized here](./Accelerations/M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.lean)). Their hazard
has not been re-measured with the method of this page, so they carry no verdict here.

### Problems 1-5 (first-order, this campaign)

* `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`
  ([#330](./M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.lean)) (ours): Problem 1; Tetrational
  Hydra-Reset (Racheline / ShiftOv6). Trigger RES + competing sinks; growth tetrational
  ($10 \uparrow\uparrow k$, $N_7 \approx 2.86\times10^{771}$); shield none. undecided type (second
  known after Racheline's #424). Status: `is_cryptid`; `HasCollatzReduction`; open (on the
  2026-10-24 holdout list).
* `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`
  ([#183](./M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean)) (ours): Problem 2; Single-Base
  Exponential Cascade. Trigger EQ (shrinking target) with leaky parity shield; growth linear (mass
  $2k+c$, drift $+2$/cycle); shield leaky (odd-$c$ regime blocks the coincidence). probviously
  non-halting. Status: `is_cryptid`; `HasCollatzReduction`; open (on the 2026-10-24 holdout list).
* `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE`
  ([#352](./M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE.lean)) (ours): Problem 2; Single-Base
  Exponential Cascade. Trigger EQ with leaky parity shield; growth linear ($2^n$ fuel bursts,
  intermittent resets); shield leaky. probviously non-halting. Status: `is_cryptid`;
  `HasCollatzReduction`; open (on the 2026-10-24 holdout list).
* `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`
  ([#530](./M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE.lean)) (ours): Problem 2; Single-Base
  Exponential Cascade. Trigger EQ with leaky parity shield; growth linear; shield leaky. probviously
  non-halting. Status: `is_cryptid`; `HasCollatzReduction`; open (on the 2026-10-24 holdout list).
* `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`
  ([#429](./M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean)) (ours): Problem 3; Single-Base
  Exponential Cascade. Trigger EQ, critical; growth linear ($2v+w \approx 43.66\,T$); shield none
  (parity flips every step). probviously halting, but only at $\sim 10^{110}$ steps. Status:
  `is_cryptid`; `HasCollatzReduction`; open (on the 2026-10-24 holdout list).
* `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`
  ([#184](./M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.lean)) (ours): Problem 4; Single-Base
  Exponential Cascade. Trigger EQ (2-wide window at turnaround); growth exponential
  ($\gamma\approx1.4246$ per era, base 3); shield none. probviously non-halting. Status:
  `is_cryptid`; `HasCollatzReduction`; open (on the 2026-10-24 holdout list).
* `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`
  ([#724](./M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE.lean)) (ours): Problem 4; Single-Base
  Exponential Cascade. Trigger EQ (2-wide window); growth exponential ($\gamma\approx1.4589$ per
  era); shield none. probviously non-halting. Status: `is_cryptid`; `HasCollatzReduction`; open (on
  the 2026-10-24 holdout list).
* `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA`
  ([#73](./M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.lean)) (ours): Problem 5; Tetrational
  Hydra-Reset (Racheline / ShiftOv6). Trigger EQ (rebound trap); growth exponential
  ($\gamma\approx1.9538$ per era); shield none. probviously non-halting. Status: `is_cryptid`;
  `HasCollatzReduction`; open (on the 2026-10-24 holdout list).

### Shielded single-base exponential cascades

* `1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`
  ([#79](./M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.lean)) (ours): Cascade; Single-Base
  Exponential Cascade. Trigger EQ; growth super-exponential (two-stage $2^n$ doubling tower); shield
  none. probviously non-halting. Status: `is_cryptid`; `HasCollatzReduction`; open (on the
  2026-10-24 holdout list).
* `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE`
  ([#116](./M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE.lean)) (wiki): Cascade; Single-Base
  Exponential Cascade. Trigger EQ; growth exponential; shield see family. wiki rediscovery
  (RobinCodes *Next Steps* list). Status: `is_cryptid`, `is_stack_cryptid`; `HasCollatzReduction`;
  open (on the 2026-10-24 holdout list).
* `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD`
  ([#153](./M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD.lean)) (ours): Cascade; Single-Base
  Exponential Cascade. Trigger EQ; growth exponential (two-base: $2^n$ doubling then $4^n$
  quadrupling, $\times2.3917$ per launch); shield none. probviously non-halting. Status:
  `is_cryptid`; `HasCollatzReduction`; open (on the 2026-10-24 holdout list).
* `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD`
  ([#464](./M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD.lean)) (ours): Cascade; Single-Base
  Exponential Cascade. Trigger EQ; growth exponential ($4^n$ inner cascades, $(4/3)^k$ sweeps);
  shield partial (odd-$a$ invariant kills 2 of 4 halting rules and 12 of 34 rules). probviously
  non-halting. Status: `is_cryptid`; `HasCollatzReduction`; open (on the 2026-10-24 holdout list).
* `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`
  ([#590](./M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.lean)) (ours): Cascade; Single-Base
  Exponential Cascade. Trigger EQ; growth super-exponential; shield none. probviously non-halting.
  Status: `is_cryptid`; `HasCollatzReduction`; open (on the 2026-10-24 holdout list).
* `1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB`
  ([#614](./M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB.lean)) (ours): Cascade; Single-Base
  Exponential Cascade. Trigger EQ ($2^n$ remainder coincidence); growth exponential ($\times1.4069$
  per cascade); shield partial ($a\ge1$ kills `rule_1_halt`). probviously non-halting. Status:
  `is_cryptid`; `HasCollatzReduction`; open (on the 2026-10-24 holdout list).
* `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`
  ([#623](./M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean)) (ours): Cascade; Single-Base
  Exponential Cascade. Trigger EQ; growth exponential (4-counter $3^n$ cascade); shield full
  (odd-$a_H$ parity shield blocks every `closes_H_mid` halt). probviously non-halting; strong
  `IsDoesNotHalt` candidate. Status: `is_cryptid`; `HasCollatzReduction`; open (on the 2026-10-24
  holdout list).
* `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`
  ([#644](./M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE.lean)) (ours): Cascade; Single-Base
  Exponential Cascade. Trigger EQ (second-order coincidence); growth exponential ($2^n$ cascade);
  shield partial (even-$c$ parity shield blocks 99.8% of visits). probviously non-halting. Status:
  `is_cryptid`; `HasCollatzReduction`; open (on the 2026-10-24 holdout list).
* `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD`
  ([#688](./M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD.lean)) (wiki): Cascade; Single-Base
  Exponential Cascade. Trigger EQ; growth exponential; shield see family. wiki rediscovery
  (RobinCodes *Next Steps* list). Status: `is_cryptid`, `is_stack_cryptid`; `HasCollatzReduction`;
  open (on the 2026-10-24 holdout list).
* `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`
  ([#693](./M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean)) (ours): Cascade; Single-Base
  Exponential Cascade. Trigger EQ; growth exponential ($\times1.2402$ per step); shield none.
  probviously non-halting. Status: `is_cryptid`; `HasCollatzReduction`; open (on the 2026-10-24
  holdout list).
* `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`
  ([#746](./M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean)) (ours): Cascade; Single-Base
  Exponential Cascade. Trigger EQ; growth exponential ($2^n$ cascade + base-$3/2$ underflow drain);
  shield partial (exact even-$c$ invariant). probviously non-halting. Status: `is_cryptid`;
  `HasCollatzReduction`; open (on the 2026-10-24 holdout list).

### Collatz-like stacked cryptids (S2-S5 and their siblings)

* `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA`
  ([#391](./Accelerations/M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA.lean)) (ours): Problem S2;
  Unary-Binary Bounded Stack Counter. Trigger POW (bottom funnel $x+2 = 2^k$); growth power-law
  regime; shield partial (`ValidStack391`: mode $D$ never halts). probviously non-halting (clean
  race). Status: `is_stack_cryptid`; `Accelerations`; open (on the 2026-10-24 holdout list).
* `1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA`
  ([#129](./Accelerations/M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA.lean)) (ours): Problem S3;
  Halving Tower (2-Adic Stack). Trigger EQ (depth-two gate); growth —; shield partial
  (`ValidStack129` kills $\mathrm{CR}\,[]\,R$ and all $0::0::L$ states). probviously non-halting
  (weak race). Status: `is_stack_cryptid`; `Accelerations`; open (on the 2026-10-24 holdout list).
* `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`
  ([#660](./Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean)) (ours): Problem S4;
  Halving Tower (2-Adic Stack). Trigger POW (power-of-two bottom exposure); growth mass-conserving
  ($\Delta M = 0$), log-depth tower; shield partial (`ValidStack660` kills $C([],R)$). probviously
  non-halting. Status: `is_stack_cryptid`; `Accelerations`; open (on the 2026-10-24 holdout list).
* `1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF`
  ([bbchallenge](https://bbchallenge.org/1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF)) (ours): Problem
  S4; Halving Tower (2-Adic Stack). Trigger POW; growth mass-conserving sandpile; shield partial.
  probviously non-halting. Status: `is_stack_cryptid`; open (on the 2026-10-24 holdout list).
* `1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF`
  ([bbchallenge](https://bbchallenge.org/1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF)) (ours): Problem
  S4; Halving Tower (2-Adic Stack). Trigger POW; growth mass-conserving sandpile; shield partial.
  probviously non-halting. Status: `is_stack_cryptid`; open (on the 2026-10-24 holdout list).
* `1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB`
  ([#680](./Accelerations/M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB.lean)) (ours): Problem S4;
  Halving Tower (2-Adic Stack). Trigger POW; growth mass-conserving sandpile; shield partial
  (`ValidStack680` kills $C([],R)$; strict digit positivity at `mode_C`). probviously non-halting.
  Status: `is_stack_cryptid`; `Accelerations`; open (on the 2026-10-24 holdout list).
* `1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD`
  ([bbchallenge](https://bbchallenge.org/1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD)) (ours): S4
  sibling; Halving Tower (2-Adic Stack). Trigger POW; growth mass-conserving sandpile; shield
  partial (strict digit positivity blocks the sole $d=0$ halt). probviously non-halting. Status:
  `is_stack_cryptid`; open (on the 2026-10-24 holdout list).
* `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`
  ([#549](./Accelerations/M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF.lean)) (wiki): Problem S5;
  Halving Tower (2-Adic Stack). Trigger POW (Mersenne bottom rung $2^k-1$); growth —; shield partial
  (`ValidStack549` kills the empty-stack halt). probviously non-halting, slowly critical. Status:
  `is_stack_cryptid`; `Accelerations`; open (on the 2026-10-24 holdout list).
* `1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA`
  ([#80](./Accelerations/M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA.lean)) (ours): S5 sibling;
  Halving Tower (2-Adic Stack). Trigger POW; growth —; shield partial. probviously non-halting.
  Status: `is_stack_cryptid`; `Accelerations`; open (on the 2026-10-24 holdout list).

### Wiki stack families

* `1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB`
  ([#33](./Accelerations/M_1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_HHH0LB.lean)) (wiki): Wiki stack;
  2nd-Order Stride-k Digit-Stack. Trigger era-recursive (3-case bottom-extension recurrence); growth
  doubly-exponential era lengths ($T_0..T_3 = 1, 2, 8, 256$); shield none closed (all-even $R$ +
  $L.\mathrm{last}=0$ refuted across eras). probviously non-halting (wiki cryptid). Status:
  `is_stack_cryptid`; `Accelerations`; open (on the 2026-10-24 holdout list).
* `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`
  ([#85](./Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean)) (wiki): Wiki stack;
  Unary-Binary Bounded Stack Counter. Trigger RES (a particular sequence of $\approx 107$–$110$
  residues mod 3 must occur while the left side is empty; wiki); growth exponential (the main number
  is multiplied by $8/3$ per era; wiki); shield none (every return to an empty left side is a fresh
  trial). probviously **halting** (wiki, Racheline 2024-11-23: expected halt at
  $\approx 10^{10^{38.1}}$ steps, far beyond any simulation); the wiki treats the four start states
  #85/#285/#490/#500 as one cryptid. Status: `is_stack_cryptid`; `Accelerations`; open (on the
  2026-10-24 holdout list).
* `1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---`
  ([#285](./Accelerations/M_1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1REHHH.lean)) (wiki): Wiki stack;
  Unary-Binary Bounded Stack Counter. Trigger as #85 (same table, started from its state `C`);
  growth as #85; shield as #85. same dynamics as `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` (#85)
  (wiki: "when the TM starts on any starting state, it exhibits the same probviously halting
  behaviour"). Status: `is_stack_cryptid`; `Accelerations`; open (on the 2026-10-24 holdout list).
* `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`
  ([#490](./Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean)) (wiki): Wiki stack;
  Unary-Binary Bounded Stack Counter. Trigger as #85 (same table, started from its state `D`,
  mirrored); growth as #85; shield as #85. same dynamics as
  `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` (#85); this is the start state analysed by @-d on the
  wiki (halting path of length 108, $\approx 235{,}000$ right-side words explored). Status:
  `is_stack_cryptid`; `Accelerations`; open (on the 2026-10-24 holdout list).
* `1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---`
  ([#500](./Accelerations/M_1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RDHHH.lean)) (wiki): Wiki stack;
  Unary-Binary Bounded Stack Counter. Trigger as #85 (same table, started from its state `E`);
  growth as #85; shield as #85. same dynamics as `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` (#85)
  (wiki: the start states `E` and `F` share one trajectory). Status: `is_stack_cryptid`;
  `Accelerations`; open (on the 2026-10-24 holdout list).

### Resolved by the community

* `1RB1LA_0RC1RD_1LC0LA_1LE1RE_0RB0LF_---0LD`
  ([bbchallenge](https://bbchallenge.org/1RB1LA_0RC1RD_1LC0LA_1LE1RE_0RB0LF_---0LD)) (ours): Problem
  S1 (resolved: halts); Unary-Binary Bounded Stack Counter. Trigger POW (Mersenne-minus-2 funnel
  $c+2=2^r$ at $L=[]$); growth power-law ($\propto t^{1/2}$); shield partial (`inv_126_R_shape`).
  **HALTS** — busycoq `CubicMachines.v` (TM49), certified accelerated simulation; our dossier said
  "critical, $0.4$–$0.9$ expected halts per decade". Status: `is_stack_cryptid`; decided HALTING
  (busycoq).

## 3. Per-machine hazard statements

### `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA` (#330, Problem 1)

* **Hazard:** from $S_6(N_7)$: $P(\mathrm{HALT}) = 6.80\%$ vs.
  $P(\text{translated cycler } R_1(n)\mapsto R_1(n+5)) = 93.20\%$, decided at step $\sim 10^{771}$
* **Simulated horizon:** exact trajectory to $N_7$; the deciding residue is a digit of a
  $10^{771}$-digit number
* **Why it is hard / what a proof needs:** base-$31/10$ Erdős–Graham floor recurrence inside a
  tetration tower; not computable, not provable with current tools

### `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE` (#183, Problem 2)

* **Hazard:** $P(\text{halt}) \approx 6\times10^{-5}$, hazard $\propto 1/T$ squared by the shield to
  $\sum t^{-2} < \infty$
* **Simulated horizon:** $7\times10^{16}$ TM steps (exact accelerated rules)
* **Why it is hard / what a proof needs:** intermittent piecewise-Möbius ratio map
  $\rho\mapsto(\rho-1)/2$ or $2\rho/(1-\rho)$; coincidence $c_0-2k_0=6$ only in the rare even-source
  regime

### `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE` (#352, Problem 2)

* **Hazard:** $P(\text{halt}) \approx 1.2\times10^{-4}$ ($\propto 1/T$)
* **Simulated horizon:** $10^{16}$ TM steps
* **Why it is hard / what a proof needs:** structural sibling of #183 on `D1(a, b, w)`; boundary
  coincidence $w_{\text{rem}} = 2a+7$ in the even-source branch

### `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE` (#530, Problem 2)

* **Hazard:** $P(\text{halt}) \approx 1.2\times10^{-4}$ ($\propto 1/T$)
* **Simulated horizon:** $10^{16}$ TM steps
* **Why it is hard / what a proof needs:** third sibling of #183/#352 with reset offset $+2$

### `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` (#429, Problem 3)

* **Hazard:** per-turnaround hazard $q\approx 2.5\times10^{-7}$, $\sum_t 0.00885/t = \infty$
  (divergent Borel–Cantelli boundary); $\approx 2\%$ per decade
* **Simulated horizon:** $2.16\times10^{17}$ TM steps, no halt
* **Why it is hard / what a proof needs:** 1-D harmonic-series shrinking target; halting iff
  $w_t = 2v_t + 8$ at a turnaround

### `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA` (#184, Problem 4)

* **Hazard:** $P(\text{halt}) \approx 1.6\times10^{-31}$ after 200 eras, geometric tail
* **Simulated horizon:** 200 eras (exact)
* **Why it is hard / what a proof needs:** base-3 `exp3_step_C_odd/even` cascade coupled to the
  Euclidean-like reflection $(a,b)\mapsto(b-a,3a)$; sits between Baker–Wüstholz and
  $\times2,\times3$ rigidity

### `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` (#724, Problem 4)

* **Hazard:** $P(\text{halt}) \approx 8.6\times10^{-34}$ after 200 eras
* **Simulated horizon:** 200 eras (exact)
* **Why it is hard / what a proof needs:** the 669-pattern CTL proof collapses to the 4-rule
  2-counter hub `D(a, c)`: structural twin of #184 (different orbit)

### `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` (#73, Problem 5)

* **Hazard:** $P(\text{halt}) \approx 10^{-380.6}$
* **Simulated horizon:** $> 3.22\times10^{762}$ TM steps
* **Why it is hard / what a proof needs:** odd-$c$ Antihydra rounds $k\mapsto\tfrac32 k+2$
  ((3/2)^{\nu_2(k+4)} 2-adic bursts, the expanding dual of Tao's Syracuse step) alternating with
  even-$c$ subtraction drains; halts iff $c_j - 2k_j \in \lbrace -4,+2 \rbrace$

### `1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE` (#79, Cascade)

* **Hazard:** $P(\text{halt}) \ll 10^{-600}$
* **Simulated horizon:** $> 3.46\times10^{1204}$ TM steps in 12 cascades
* **Why it is hard / what a proof needs:** coupled outer `D1` and inner `Modd` $2^n$ cascades; halts
  iff $D_1(2,u,0)$

### `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE` (#116, Cascade)

* **Hazard:** not re-measured in our dossiers
* **Simulated horizon:** —
* **Why it is hard / what a proof needs:** 1st-order collapse of a false stack (`Valid3Counter116`)
* **Wiki:** <https://wiki.bbchallenge.org/wiki/1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE>

### `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD` (#153, Cascade)

* **Hazard:** $P(\text{halt}) \approx 4.4\times10^{-207}$
* **Simulated horizon:** $1.51\times10^{415}$ TM steps
* **Why it is hard / what a proof needs:** halts iff $d_j = b_j + 2$ at $A(0,b_j,0,d_j)$

### `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD` (#464, Cascade)

* **Hazard:** $P(\text{halt}) \lesssim 10^{-5}$ per era
* **Simulated horizon:** exact rule simulation (see dossier)
* **Why it is hard / what a proof needs:** remaining halts `rule_4/12_halt` need $c_{\text{rem}}=1$:
  a $(4/3)^k$ Mahler-type residue problem

### `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC` (#590, Cascade)

* **Hazard:** $P(\text{halt}) \ll 10^{-600}$
* **Simulated horizon:** $> 3.46\times10^{1204}$ TM steps in 12 cascades
* **Why it is hard / what a proof needs:** E1 sibling of #79 with identical rules from $D_1(1,0,0)$
  (candidate exact equivalence)

### `1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB` (#614, Cascade)

* **Hazard:** $P(\text{halt}) \approx 1.7\times10^{-3422}$ after 23,083 cascades
* **Simulated horizon:** 23,083 cascades (exact)
* **Why it is hard / what a proof needs:** `rule_8_halt` requires $P_2(a,0,2)$ at a cascade
  turnaround

### `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA` (#623, Cascade)

* **Hazard:** $P(\text{halt}) < 10^{-73}$; $756/756$ entries into $H_{\text{mid}}$ have odd $a_H$
* **Simulated horizon:** $1.5\times10^{72}$ raw $D$-visits (exact)
* **Why it is hard / what a proof needs:** shares the exact orbit of #568 from $D(11,0,1,0)$;
  busycoq `Eqv_RegularPairs.v` proves #568 ≡ #623

### `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE` (#644, Cascade)

* **Hazard:** $P(\text{halt}) \lesssim 10^{-6}$ (convergent $\sum m^{-2}$ tail)
* **Simulated horizon:** exact rule simulation (see dossier)
* **Why it is hard / what a proof needs:** halting requires both $c = 2b-4$ and
  $c_{\text{odd}} = 2^{k+3}-2k-5$

### `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD` (#688, Cascade)

* **Hazard:** not re-measured in our dossiers
* **Simulated horizon:** —
* **Why it is hard / what a proof needs:** E1 pair of #116
* **Wiki:** <https://wiki.bbchallenge.org/wiki/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD>

### `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` (#693, Cascade)

* **Hazard:** $P(\text{halt}) < 10^{-600}$ (2,001 bits in 6,444 steps)
* **Simulated horizon:** 6,444 macro-steps (exact)
* **Why it is hard / what a proof needs:** alternating parity hubs with diagonal drain
  $\min(v_1,v_2)$; halts iff $|v_1-v_2|\in\lbrace 0,1 \rbrace$ with $v_1\ge v_2$

### `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` (#746, Cascade)

* **Hazard:** $P(\text{halt}) \approx 10^{-294}$ after 1,253 cascades
* **Simulated horizon:** 1,253 cascades (exact)
* **Why it is hard / what a proof needs:** halting iff the $(3/2)^m$ underflow map lands in the
  target set $\lbrace 4\cdot2^n - n - 6 \rbrace$

### `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA` (#391, Problem S2)

* **Hazard:** 318 bottom reaches in $10^7$ steps ($29\to73\to204$ per decade), $x$ spread over
  $10^3$–$10^4$; residual hazard $\approx0.2$; near-misses $251, 513, 514, 61, 132$
* **Simulated horizon:** $10^7$ macro-steps (exact); pumping test: 72 perturbed configurations, 0
  halts in $10^5$ steps
* **Why it is hard / what a proof needs:** rung-by-rung halving with carry on
  $\mathrm{List}(\mathbb N)$

### `1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA` (#129, Problem S3)

* **Hazard:** 232 depth-two visits in $10^7$ steps, $a\in\lbrace 3,4,7,9,11,15 \rbrace$ on 8 of them
  ($a=1$ halts); $\approx2$ expected halts, 0 observed
* **Simulated horizon:** $10^7$ macro-steps (exact)
* **Why it is hard / what a proof needs:** two-mode halving sweeper; halts iff $L$ drains to $[1,0]$
  in $\mathrm{CR}$

### `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF` (#660, Problem S4)

* **Hazard:** 21 exposures in $3\times10^6$ steps ($1292\to646\to323$, $94000\to\dots\to5875$), odd
  parts $\ge323$; negligible residual hazard, no invariant known
* **Simulated horizon:** $3\times10^6$ macro-steps (exact); pumping test: 13 perturbed
  configurations, 0 halts
* **Why it is hard / what a proof needs:** Single-Pass Drainage Law $b_{i+1} = a_{i+1}+q_i+1$,
  $q_{k-1} = 2^m-1$, $u = 2^m$

### `1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF` (#659, Problem S4)

* **Hazard:** as #660 (same sandpile law); E3 macro twin of #209; busycoq `Eqv_*` merges #96 into
  this class
* **Simulated horizon:** family-level
* **Why it is hard / what a proof needs:** see #660

### `1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF` (#209, Problem S4)

* **Hazard:** as #660; E3 macro twin of #659
* **Simulated horizon:** family-level
* **Why it is hard / what a proof needs:** see #660

### `1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB` (#680, Problem S4)

* **Hazard:** as #660
* **Simulated horizon:** family-level
* **Why it is hard / what a proof needs:** E1 pair of #480

### `1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD` (#480, S4 sibling)

* **Hazard:** as #660/#680
* **Simulated horizon:** family-level
* **Why it is hard / what a proof needs:** E1 pair of #680 (different seed)

### `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF` (#549, Problem S5)

* **Hazard:** 846 exposures in $10^7$ steps ($14\to35\to90\to275$ fresh starts per decade),
  $\approx0.05$ expected halts per decade; near-misses $4,13,61,65,252,513,1020,1027$
* **Simulated horizon:** $10^7$ macro-steps (exact)
* **Why it is hard / what a proof needs:** the community's *Sweeper* re-measured; two-mode halving
  sweeper
* **Wiki:** <https://wiki.bbchallenge.org/wiki/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF>

### `1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA` (#80, S5 sibling)

* **Hazard:** E1 Group 39 with #549 (same table, different seed); not separately measured
* **Simulated horizon:** family-level
* **Why it is hard / what a proof needs:** see #549

### `1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB` (#33, Wiki stack)

* **Hazard:** not quantified; perturbed all-even seeds halt in Era 2/3 (`rec_59_bottom_extension`)
* **Simulated horizon:** pumping test: 46 perturbed configurations, 0 halts in $10^5$ steps
* **Why it is hard / what a proof needs:** exact 3-case composition theorem verified on all 1,024
  stacks of weight $\le10$
* **Wiki:** <https://wiki.bbchallenge.org/wiki/1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB>

### `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` (#85, Wiki stack)

* **Hazard:** community estimate, not re-measured here: per empty-left-side reset, probability
  $\approx 3^{-80}$–$3^{-87}$ of entering one of the $2^{13}\cdot 3^{15}$ shortest halting residue
  sequences (length 107–110, Racheline); @-d's breadth-first search over $\approx 235{,}000$
  right-side words found a halting path of length 108 and the halting residue class
  $A(3^{108}k + 1975700577069254261393123959451562008800234946348086, \varepsilon)$
* **Simulated horizon:** community: exhaustive search of the right-side word graph (wiki); here the
  two-sided pair-stack system is certified closed (`HasStackReduction`)
* **Why it is hard / what a proof needs:** the halting mechanism is explicit and the halting set is
  a residue class of positive density, but reaching it needs $\approx 3^{80}$ independent resets:
  the archetype of RES hardness without a shield
* **Wiki:** <https://wiki.bbchallenge.org/wiki/1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA>

### `1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---` (#285, Wiki stack)

* **Hazard:** as #85 (community estimate)
* **Simulated horizon:** as #85
* **Why it is hard / what a proof needs:** the proof is the state relabelling of the #85 proof with
  its own blank-tape entry (12 raw steps)
* **Wiki:** <https://wiki.bbchallenge.org/wiki/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE--->

### `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` (#490, Wiki stack)

* **Hazard:** as #85 (community estimate)
* **Simulated horizon:** as #85
* **Why it is hard / what a proof needs:** the proof is the relabelling and left/right mirror of the
  #85 proof with its own blank-tape entry (7 raw steps)
* **Wiki:** <https://wiki.bbchallenge.org/wiki/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE--->

### `1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---` (#500, Wiki stack)

* **Hazard:** as #85 (community estimate)
* **Simulated horizon:** as #85
* **Why it is hard / what a proof needs:** the proof is the state relabelling of the #85 proof with
  its own blank-tape entry (11 raw steps)
* **Wiki:** <https://wiki.bbchallenge.org/wiki/1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD--->

### `1RB1LA_0RC1RD_1LC0LA_1LE1RE_0RB0LF_---0LD` (#72, Problem S1 (resolved: halts))

* **Hazard:** $3.3\times10^7$ gate visits in $8.4\times10^{14}$ hub steps, 0 hits vs. $\approx6$
  expected; the halt occurs after $5.59\times10^8$ accelerated steps and $2.19\times10^8$
  empty-stack returns ($\approx0.8$ decades beyond the dossier)
* **Simulated horizon:** halt found (see busycoq)
* **Why it is hard / what a proof needs:** calibration case for the hazard model: the only S-problem
  with a divergent hazard is the one that halted
* **busycoq:** CubicMachines.v

## 4. Calibration: the one that halted

`1RB1LA_0RC1RD_1LC0LA_1LE1RE_0RB0LF_---0LD` (#72, Problem S1) was the only stacked problem with a
*critical*, log-divergent hazard ($\approx 0.4$–$0.9$ expected halts per decade of empty-stack
returns after $3.3\times10^7$ returns). The `bbchallenge` community then proved that it halts
(busycoq [`CubicMachines.v`](https://github.com/ccz181078/busycoq/blob/BB6/verify/CubicMachines.v),
module `TM49`, a certified accelerated simulation); re-running their abstract step function, the
halt occurs after $5.59\times10^8$ accelerated steps and $2.19\times10^8$ empty-stack returns, about
$0.8$ decades beyond the dossier's horizon. The taxonomy singled out the right machine; the
procedural lesson is that a machine with an $O(1)$ per-decade hazard must be simulated at least an
order of magnitude further before it is called an open problem.

## 5. What is *not* evidence of hardness

A shield that holds along the simulated trajectory is not a shield. Among machines once described as
"shielded" in our census, `#787`, `#495`, `#767`, `#151`, `#269` and `#334` were later proved
**halting** by the community (busycoq `CubicMachines.v`, `PR_SOMDC23Halt.v`, `SOMDCv10.v`). Only
inductive invariants, closed on all abstract states, count; the pumping test (extend a run of
identical digits, or shift a large digit by the modulus, and see whether the machine halts) is the
cheap way to tell a shape-based shield from a value-dependent survival, and it correctly flags the
exponential stack ladders and halving towers as value-dependent.

-/
