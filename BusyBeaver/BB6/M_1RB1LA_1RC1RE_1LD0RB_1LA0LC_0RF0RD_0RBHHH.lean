/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` (Resolved Non-Halting)

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver machine `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`, known on the
[bbchallenge Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---)
as the **Pomme / Baker machine** (former holdout #613/#529, `suspect_14`).

**Resolution Status (Resolved Non-Halting)**: This machine has been **resolved as non-halting** on
the [bbchallenge Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---)
(November 2025) via Baker's theorem on linear forms in logarithms combined with 2-adic analysis
(mxdys, Pomme, Autumn Pan, vyx7).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$P_{61}(a, c) := 0^\infty\,1^{a+1}\,\mathrm{B}{>}\,1^{c+3}\,01\,0^\infty, \quad
  P_{270}(a, b, c) := 0^\infty\,1^{a+1}\,\mathrm{D}{>}\,110\,(10)^b\,1^{c+3}\,01\,0^\infty$$
at $P_{61}(0, 7)$ in 44 steps, and every configuration in $\{P_{61}(a, c), P_{270}(a, b, c)\}$
steps in `ReachesPlus` either to another configuration in the family or to a halting configuration.

## Collatz-like Acceleration Rules

```text
Consider:
P61(a, c)     = 0^inf 1^{a+1} B> 1^{c+3} 01 0^inf
P270(a, b, c) = 0^inf 1^{a+1} D> 110 (10)^b 1^{c+3} 01 0^inf

P61(a, 0)           -> P61(0, 4a + 4*floor(a/2) + 15)
P61(a, 1)           -> P61(0, 2a + 11)
P61(a, 2)           -> Halt
P61(a, c+3)         -> P270(a, 0, c)

P270(0, b, 0)       -> Halt
P270(1, b, 0)       -> Halt
P270(a+2, b, 0)     -> P61(0, 4a + 4*floor(a/2) + 4b + 35)
P270(0, b, 1)       -> Halt
P270(1, b, 1)       -> Halt
P270(a+2, b, 1)     -> P61(0, 4a + 4*floor(a/2) + 4b + 27)
P270(a, b, 2)       -> P61(0, 2a + 2b + 13)
P270(0, b, c+3)     -> P61(2b + 8, c)
P270(1, b, c+3)     -> P61(2b + 10, c)
P270(a+2, b, 3)     -> Halt
P270(a+2, b, c+4)   -> P270(a, b+3, c)

Start: P61(0, 7), reached after 44 raw TM steps
```

## High-Level Collatz-like Acceleration

Contracting the diagonal sweep $P_{270}(a + 2, b, c + 4) \to P_{270}(a, b + 3, c)$ via
$k = \min(\lfloor a/2 \rfloor, \lfloor c/4 \rfloor)$ eliminates $P_{270}$ in closed form, and
draining any return $P_{61}(a', c')$ with $a' > 0$ (which satisfies $c' \le c - 6 < c$) reduces the
two-family system to a **single-counter** Collatz-like map on $P(c) := P_{61}(0, c)$ starting at
$P(7)$.
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RBHHH

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private theorem target_A_0 : target A 0 = some (some B, Stmt.write 1 Dir.right) := rfl
private theorem target_A_1 : target A 1 = some (some A, Stmt.write 1 Dir.left) := rfl
private theorem target_B_0 : target B 0 = some (some C, Stmt.write 1 Dir.right) := rfl
private theorem target_B_1 : target B 1 = some (some E, Stmt.write 1 Dir.right) := rfl
private theorem target_C_0 : target C 0 = some (some D, Stmt.write 1 Dir.left) := rfl
private theorem target_C_1 : target C 1 = some (some B, Stmt.write 0 Dir.right) := rfl
private theorem target_D_0 : target D 0 = some (some A, Stmt.write 1 Dir.left) := rfl
private theorem target_D_1 : target D 1 = some (some C, Stmt.write 0 Dir.left) := rfl
private theorem target_E_0 : target E 0 = some (some F, Stmt.write 0 Dir.right) := rfl
private theorem target_E_1 : target E 1 = some (some D, Stmt.write 0 Dir.right) := rfl
private theorem target_F_0 : target F 0 = some (some B, Stmt.write 0 Dir.right) := rfl
private theorem target_F_1 : target F 1 = none := rfl

local macro "v1" a:term:arg : term =>
  `(fun k => match k with | 0 => $a | _ => 0)

local macro "v2" a:term:arg b:term:arg : term =>
  `(fun k => match k with | 0 => $a | 1 => $b | _ => 0)

local macro "v3" a:term:arg b:term:arg c:term:arg : term =>
  `(fun k => match k with | 0 => $a | 1 => $b | 2 => $c | _ => 0)

local macro "v4" a:term:arg b:term:arg c:term:arg d:term:arg : term =>
  `(fun k => match k with | 0 => $a | 1 => $b | 2 => $c | 3 => $d | _ => 0)

local macro "pat_step" : tactic =>
  `(tactic| (
    simp only [evalTapePattern, evalTapeExpr,
      evalTapePattern_some, evalTapeExpr_default, evalTapeExpr_sym, evalTapeExpr_rep,
      list_pow_zero, list_pow_succ, List.cons_append, List.singleton_append, List.nil_append,
      ListBlank.append_nil, ListBlank.append_cons, Cfg.headRight, Cfg.headLeft, step,
      target_A_0, target_A_1, target_B_0, target_B_1, target_C_0, target_C_1,
      target_D_0, target_D_1, target_E_0, target_E_1, target_F_0, target_F_1,
      Option.map, Tape.write, Tape.move, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.head_default_fin, ListBlank.tail_default,
      ListBlank.cons_zero_default]
    try rfl))

local macro "var_omega" : tactic =>
  `(tactic| (simp -failIfUnchanged only []; omega))

local macro "congr_vars" : tactic =>
  `(tactic| (
    try (
      refine congrArg _ (funext fun k => ?_)
      rcases k with _ | _ | _ | _ | _ <;>
        first | rfl | (simp -failIfUnchanged only [Nat.add_eq]; omega))))

local macro "congr_cfg" pat:ident : tactic =>
  `(tactic| (
    refine congrArg some (congrArg (evalTapePattern $pat) (funext fun k => ?_))
    rcases k with _ | _ | _ | _ | _ <;>
      first | rfl | (simp -failIfUnchanged only [Nat.add_eq]; omega)))

private def pat_0 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_3 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 .default)))) }

private def pat_4 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))) }

private def pat_5 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))) }

private def pat_6 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))) }

private def pat_7 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 1 .default) }

private def pat_8 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))) }

private def pat_9 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 .default) }

private def pat_10 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default)))) }

private def pat_11 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))) }

private def pat_12 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 .default }

private def pat_13 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 1 .default }

private def pat_14 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))) }

private def pat_15 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default)))) }

private def pat_16 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .default }

private def pat_17 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .default }

private def pat_18 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 1 .default) }

private def pat_19 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default)))) }

private def pat_20 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))) }

private def pat_21 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .default }

private def pat_22 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .default }

private def pat_23 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 1 .default }

private def pat_24 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 .default))) }

private def pat_25 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 0 (.sym 1 .default) }

private def pat_26 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default)))) }

private def pat_27 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 .default) }

private def pat_28 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 .default) }

private def pat_29 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .default }

private def pat_30 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 1 .default) }

private def pat_31 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 .default)))) }

private def pat_32 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 .default)) }

private def pat_33 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))))) }

private def pat_34 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_35 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.sym 1 .default) }

private def pat_36 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_37 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_38 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 1 .default }

private def pat_39 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 .default)))) }

private def pat_40 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 .default)))) }

private def pat_41 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .default }

private def pat_42 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))) }

private def pat_43 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default)))) }

private def pat_44 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default)))) }

private def pat_45 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 .default)))) }

private def pat_46 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some A
    right := .sym 0 (.sym 1 .default) }

private def pat_47 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))) }

private def pat_48 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))))) }

private def pat_49 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 .default))))) }

private def pat_50 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 .default }

private def pat_51 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .default }

private def pat_52 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some F
    right := .default }

private def pat_53 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some B
    right := .default }

private def pat_54 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some C
    right := .default }

private def pat_55 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some D
    right := .sym 1 (.sym 1 .default) }

private def pat_56 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_57 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_58 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 0 (.sym 0 (.sym 1 .default))))) }

private def pat_59 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_60 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 0 (.sym 0 (.sym 1 .default)))))) }

/-- Canonical tape pattern
$P_{61}(a, c) := 0^\infty\,1^{a+1}\,\mathrm{B}{>}\,1^{c+3}\,01\,0^\infty$. -/
def pat_61 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_62 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_63 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_64 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_65 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_66 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 0 (.sym 1 .default))) }

private def pat_67 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))) }

private def pat_68 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_69 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 0 (.sym 1 .default)))) }

private def pat_70 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 0 (.sym 1 .default)))) }

private def pat_71 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_72 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_73 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 0 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_74 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_75 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 0 (.sym 1 .default))))) }

private def pat_76 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 0 (.sym 1 .default)))) }

private def pat_77 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.sym 1 .default)))) }

private def pat_78 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_79 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_80 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_81 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 0 (.sym 0 (.sym 1
               .default))))))))) }

private def pat_82 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_83 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_84 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 0 (.sym 1 .default))))) }

private def pat_85 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_86 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 0 (.sym 1 .default))))) }

private def pat_87 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_88 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_89 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1,
      0] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_90 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))) }

private def pat_91 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1,
      0] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_92 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))) }

private def pat_93 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1,
      0] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_94 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0
               (.sym 1 .default))))))))) }

private def pat_95 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 0 (.sym 0 (.sym 1 .default)))))) }

private def pat_96 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0
               (.sym 1 .default))))))))) }

private def pat_97 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_98 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0
               (.sym 1 .default))))))))) }

private def pat_99 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 0 (.sym 1 .default)))))) }

private def pat_100 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 1 .default) }

private def pat_101 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 0 (.sym 1 .default) }

private def pat_102 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.sym 1 .default)))) }

private def pat_103 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_104 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_105 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_106 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_107 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1
               (.sym 0 (.sym 1 .default)))))))))) }

private def pat_108 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_109 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_110 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_111 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_112 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_113 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_114 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_115 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_116 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_117 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1,
      0] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_118 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_119 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_120 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))) }

private def pat_121 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1,
      0] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_122 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0
               (.sym 1 .default))))))))) }

private def pat_123 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_124 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_125 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_126 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_127 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_128 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0
               (.sym 1 .default))))))))) }

private def pat_129 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.sym 1 .default)))) }

private def pat_130 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .default }

private def pat_131 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_132 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 1 .default }

private def pat_133 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_134 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_135 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .default }

private def pat_136 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_137 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 1 .default) }

private def pat_138 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 0 (.sym 1 .default)))) }

private def pat_139 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_140 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some E
    right := .sym 0 (.sym 1 .default) }

private def pat_141 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some E
    right := .sym 0 (.sym 1 .default) }

private def pat_142 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_143 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_144 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_145 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some E
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_146 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_147 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some E
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_148 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some E
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_149 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_150 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some E
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_151 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_152 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 3 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_153 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_154 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_155 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 1 .default) }

private def pat_156 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))) }

private def pat_157 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .default }

private def pat_158 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_159 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_160 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 1 .default) }

private def pat_161 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 .default) }

private def pat_162 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))) }

private def pat_163 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_164 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_165 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_166 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_167 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))) }

private def pat_168 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1,
      0] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_169 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some F
    right := .sym 1 .default }

private def pat_170 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some F
    right := .sym 1 .default }

private def pat_171 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_172 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))) }

private def pat_173 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1,
      0] 2 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_174 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_175 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0
               (.sym 1 .default))))))))) }

private def pat_176 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some D
    right := .sym 0 (.sym 1 .default) }

private def pat_177 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some D
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_178 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_179 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_180 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 0 (.sym 1 .default) }

private def pat_181 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_182 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_183 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_184 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_185 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default)))))) }

private def pat_186 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 3 (.sym 0
               (.sym 1 .default))))))))) }

private def pat_187 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some A
    right := .sym 0 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_188 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_189 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 .default)) }

private def pat_190 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))) }

private def pat_191 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_192 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_193 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_194 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_195 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_196 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))) }

private def pat_197 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_198 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_199 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 2 .default))) }

private def pat_200 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_201 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_202 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2
               (.sym 0 (.sym 1 .default)))))))))) }

private def pat_203 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 .default)) }

private def pat_204 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 0 (.sym 0 (.sym 0 (.sym 1 .default))) }

private def pat_205 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 .default)))) }

private def pat_206 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))) }

private def pat_207 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_208 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 .default)) }

private def pat_209 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 0 (.sym 1 .default))) }

private def pat_210 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))) }

private def pat_211 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))))) }

private def pat_212 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_213 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_214 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_215 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_216 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_217 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_218 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_219 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_220 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_221 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_222 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 1 (.sym 1 .default) }

private def pat_223 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 0 (.sym 1 .default)))) }

private def pat_224 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_225 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_226 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 1 (.sym 1 .default) }

private def pat_227 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 0 (.sym 1 .default)))) }

private def pat_228 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_229 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_230 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 0 (.sym 1 .default) }

private def pat_231 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_232 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some E
    right := .default }

private def pat_233 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some E
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_234 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some E
    right := .default }

private def pat_235 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some E
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_236 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))) }

private def pat_237 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_238 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_239 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_240 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_241 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))))
    head := some E
    right := .sym 1 .default }

private def pat_242 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 0 (.sym 1 .default))))) }

private def pat_243 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_244 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1
               .default))))))))) }

private def pat_245 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some E
    right := .sym 1 .default }

private def pat_246 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 0 (.sym 1 .default))))) }

private def pat_247 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_248 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1
               .default))))))))) }

private def pat_249 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some F
    right := .sym 1 .default }

private def pat_250 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_251 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some F
    right := .default }

private def pat_252 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some D
    right := .default }

private def pat_253 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_254 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some F
    right := .default }

private def pat_255 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .default }

private def pat_256 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_257 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_258 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_259 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_260 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_261 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_262 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_263 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default))))) }

private def pat_264 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))))
    head := some D
    right := .default }

private def pat_265 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 0 (.sym 1 .default))))) }

private def pat_266 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_267 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1,
      0] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_268 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1,
      0] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_269 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0
               (.sym 1 .default))))))))) }

/-- Canonical tape pattern
$P_{270}(a, b, c) := 0^\infty\,1^{a+1}\,\mathrm{D}{>}\,110\,(10)^b\,1^{c+3}\,01\,0^\infty$. -/
def pat_270 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0
               (.sym 1 .default))))))))) }

private def pat_271 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default)))))))
    head := some D
    right := .default }

private def pat_272 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_273 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_274 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1,
      0] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_275 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1,
      0] 2 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))))) }

private def pat_276 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0
               (.sym 1 .default))))))))) }

private def pat_277 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 3 (.sym 0
               (.sym 1 .default))))))))) }

private def pat_278 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some A
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_279 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))))
    head := some B
    right := .default }

private def pat_280 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some A
    right := .sym 0 (.sym 1 .default) }

private def pat_281 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_282 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some B
    right := .default }

private def pat_283 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some A
    right := .sym 0 (.sym 1 .default) }

private def pat_284 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_285 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_286 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_287 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default)))) }

private def pat_288 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_289 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_290 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default)))))) }

private def pat_291 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))))
    head := some A
    right := .sym 0 (.sym 1 .default) }

private def pat_292 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 0 (.sym 1 .default)))))) }

private def pat_293 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_294 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 1
               (.sym 0 (.sym 1 .default)))))))))) }

private def pat_295 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some A
    right := .sym 0 (.sym 1 .default) }

private def pat_296 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_297 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 0 (.sym 1 .default)))))) }

private def pat_298 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_299 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.sym 1 (.sym 0 (.sym 1
               .default)))))))) }

private def pat_300 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2
               (.sym 0 (.sym 1 .default)))))))))) }

private def pat_301 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 3
               (.sym 0 (.sym 1 .default)))))))))) }

private def pat_302 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some B
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_303 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))))
    head := some C
    right := .default }

private def pat_304 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some B
    right := .sym 1 .default }

private def pat_305 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default)))))))
    head := some C
    right := .default }

private def pat_306 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 1 .default }

private def pat_307 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_308 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_309 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 2 .default)) }

private def pat_310 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default))))) }

private def pat_311 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))))
    head := some B
    right := .sym 1 .default }

private def pat_312 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default)))))))
    head := some B
    right := .sym 1 .default }

private def pat_313 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some E
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_314 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))))
    head := some D
    right := .sym 1 (.sym 1 .default) }

private def pat_315 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))))
    head := some E
    right := .default }

private def pat_316 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some D
    right := .sym 1 (.sym 1 .default) }

private def pat_317 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some E
    right := .default }

private def pat_318 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 .default)
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_319 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))))))
    head := some E
    right := .default }

private def pat_320 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default))))))))
    head := some E
    right := .default }

private def pat_321 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_322 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))))
    head := some F
    right := .default }

private def pat_323 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_324 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default)))))))
    head := some F
    right := .default }

private def pat_325 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0
              .default))))))))
    head := some F
    right := .default }

private def pat_326 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep
              [1] 1 .default)))))))))
    head := some F
    right := .default }

private def pat_327 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_328 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))))))
    head := some B
    right := .default }

private def pat_329 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_330 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default))))))))
    head := some B
    right := .default }

private def pat_331 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0
              .default)))))))))
    head := some B
    right := .default }

private def pat_332 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym
              1 (.rep [1] 1 .default))))))))))
    head := some B
    right := .default }

private def pat_333 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [1] 0 .default))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_334 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0
              .default))))))))
    head := some C
    right := .default }

private def pat_335 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_336 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep
              [1] 1 .default)))))))))
    head := some C
    right := .default }

private def pat_337 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1
              (.rep [1] 0 .default))))))))))
    head := some C
    right := .default }

private def pat_338 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0]
              0 (.sym 1 (.rep [1] 1 .default)))))))))))
    head := some C
    right := .default }

private def pat_339 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))))))
    head := some D
    right := .sym 1 (.sym 1 .default) }

private def pat_340 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some A
    right := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default)))))) }

private def pat_341 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default))))))))
    head := some D
    right := .sym 1 (.sym 1 .default) }

private def pat_342 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0
              .default)))))))))
    head := some D
    right := .sym 1 (.sym 1 .default) }

private def pat_343 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym
              1 (.rep [1] 1 .default))))))))))
    head := some D
    right := .sym 1 (.sym 1 .default) }

private def pat_344 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_345 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some B
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_346 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default)))))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_347 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0
              .default))))))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_348 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep
              [1] 1 .default)))))))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 .default)) }

private def pat_349 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_350 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_351 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some E
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_352 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_353 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))))))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_354 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default))))))))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_355 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_356 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default)))))))
    head := some D
    right := .sym 1 (.sym 0 (.sym 1 .default)) }

private def pat_357 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default)))))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 .default))) }

private def pat_358 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default)))))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_359 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_360 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))))))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_361 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1
              .default)))))))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_362 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_363 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 0 (.sym 1 .default))) }

private def pat_364 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.sym 1 .default)))) }

private def pat_365 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))) }

private def pat_366 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))))) }

private def pat_367 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_368 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 1 (.sym 0 (.sym 1 .default))))) }

private def pat_369 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))))
    head := some A
    right := .sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

private def pat_370 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 0 (.sym 1 .default)))) }

private def pat_371 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 .default)))) }

private def pat_372 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default)))))) }

private def pat_373 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))
    head := some D
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1] 2 (.sym 0 (.sym 1
               .default)))))))) }

/-- Closed pattern set for `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_61, .true), (pat_270, .true)]

private theorem mem_ps_61 : (pat_61, VarCond.true) ∈ ps :=
  .head _

private theorem in_ps_61 (vars : ℕ → ℕ) : IsInPatternSet ps (evalTapePattern pat_61 vars) :=
  ⟨(pat_61, .true), mem_ps_61, vars, rfl, trivial⟩

private theorem mem_ps_270 : (pat_270, VarCond.true) ∈ ps :=
  .tail _ (.head _)

private theorem in_ps_270 (vars : ℕ → ℕ) : IsInPatternSet ps (evalTapePattern pat_270 vars) :=
  ⟨(pat_270, .true), mem_ps_270, vars, rfl, trivial⟩

private def ReachesTarget (ps : TapePatternSet (Fin 2) (Fin 6))
    (c₁ : Cfg (Fin 2) (Fin 6)) (t : Option (Cfg (Fin 2) (Fin 6))) : Prop :=
  match t with
  | some cfg' => ReachesPlus target c₁ cfg' ∧ IsInPatternSet ps cfg'
  | none => ∃ cfg', ReachesPlus target c₁ cfg' ∧ (step target cfg').isNone

private theorem reachesTarget_to_exists {c₁ : Cfg (Fin 2) (Fin 6)}
    {t : Option (Cfg (Fin 2) (Fin 6))} (h : ReachesTarget ps c₁ t) :
    ∃ cfg', ReachesPlus target c₁ cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  cases t with
  | some cfg' => exact ⟨cfg', h.1, Or.inl h.2⟩
  | none =>
    rcases h with ⟨cfg', h₁, h₂⟩
    exact ⟨cfg', h₁, Or.inr h₂⟩

private theorem step_base {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h_step : step target c₁ = some c₂)
    (h_in : IsInPatternSet ps c₂) :
    ReachesTarget ps c₁ (some c₂) :=
  ⟨ReachesPlus.single h_step, h_in⟩

private theorem step_halt {c₁ : Cfg (Fin 2) (Fin 6)} (c₂ : Cfg (Fin 2) (Fin 6))
    (h_step : step target c₁ = some c₂)
    (h_halt : (step target c₂).isNone) :
    ReachesTarget ps c₁ none :=
  ⟨c₂, ReachesPlus.single h_step, h_halt⟩

private theorem step_chain {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h_step : step target c₁ = some c₂)
    {t : Option (Cfg (Fin 2) (Fin 6))}
    (h_next : ReachesTarget ps c₂ t) :
    ReachesTarget ps c₁ t := by
  cases t with
  | some cfg' => exact ⟨(ReachesPlus.single h_step).trans h_next.1, h_next.2⟩
  | none =>
    rcases h_next with ⟨cfg', h₂, h_halt⟩
    exact ⟨cfg', (ReachesPlus.single h_step).trans h₂, h_halt⟩

private theorem step_chain_explicit (c₂ : Cfg (Fin 2) (Fin 6)) {c₁ : Cfg (Fin 2) (Fin 6)}
    (h_step : step target c₁ = some c₂)
    {t : Option (Cfg (Fin 2) (Fin 6))}
    (h_next : ReachesTarget ps c₂ t) :
    ReachesTarget ps c₁ t :=
  step_chain h_step h_next

private theorem cast_target {c₁ : Cfg (Fin 2) (Fin 6)} {t₁ t₂ : Option (Cfg (Fin 2) (Fin 6))}
    (h_eq : t₁ = t₂) (h : ReachesTarget ps c₁ t₁) : ReachesTarget ps c₁ t₂ :=
  h_eq ▸ h

/-- Canonical configuration $P_{61}(a, c)$. -/
private def cfg_P61 (a c : Nat) : Cfg (Fin 2) (Fin 6) :=
  evalTapePattern pat_61 (v2 a c)

/-- Canonical configuration $P_{270}(a, b, c)$. -/
private def cfg_P270 (a b c : Nat) : Cfg (Fin 2) (Fin 6) :=
  evalTapePattern pat_270 (v3 a b c)
private def target_pat_60 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  some (evalTapePattern pat_61 (v2 0 (vars 0)))

private theorem step_pat_60 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_60 vars) (target_pat_60 vars) := by
  refine step_base ?_ (in_ps_61 (v2 0 (vars 0)))
  dsimp only [pat_60, pat_61, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_58 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_60 (v1 0) | u + 1 => target_pat_60 (v1 (u + 1))

private theorem step_pat_58 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_58 vars) (target_pat_58 vars) := by
  rcases h_vr : vars 0 with _ | u
  · simp -failIfUnchanged only [target_pat_58]; rw [h_vr]
    refine step_chain ?_ (step_pat_60 (v1 0))
    dsimp only [pat_58, pat_60, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_58]; rw [h_vr]
    refine step_chain ?_ (step_pat_60 (v1 (u + 1)))
    dsimp only [pat_58, pat_60, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_59 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_58 (v1 (vars 0 + vars 1 + 1))

private theorem step_pat_59 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_59 vars) (target_pat_59 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    rcases h_vr : vars 1 with _ | u
    · have h_eq : target_pat_59 vars = target_pat_58 (v1 1) := by
        simp -failIfUnchanged only [target_pat_59]; rw [h_vl, h_vr]
      rw [h_eq]
      refine step_chain ?_ (step_pat_58 (v1 1))
      dsimp only [pat_59, pat_58, evalTapePattern, evalTapeExpr]; rw [h_vr];
        rw [h_vl]; pat_step
    · have h_eq : target_pat_59 vars = target_pat_58 (v1 ((u + 1) + 1)) := by
        simp -failIfUnchanged only [target_pat_59]; rw [h_vl, h_vr]
        congr_vars
      rw [h_eq]
      refine step_chain ?_ (step_pat_58 (v1 ((u + 1) + 1)))
      dsimp only [pat_59, pat_58, evalTapePattern, evalTapeExpr]; rw [h_vr];
        rw [h_vl]; pat_step
  | succ v ih =>
    rcases h_vr : vars 1 with _ | u
    · have h_eq : target_pat_59 vars = target_pat_59 (v2 v 1) := by
        simp -failIfUnchanged only [target_pat_59]; rw [h_vl, h_vr]
      rw [h_eq]
      refine step_chain ?_ (ih (v2 v 1) rfl)
      dsimp only [pat_59, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl];
        pat_step
    · have h_eq : target_pat_59 vars = target_pat_59 (v2 v ((u + 1) + 1)) := by
        simp -failIfUnchanged only [target_pat_59]; rw [h_vl, h_vr]
        congr_vars
      rw [h_eq]
      refine step_chain ?_ (ih (v2 v ((u + 1) + 1)) rfl)
      dsimp only [pat_59, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl];
        pat_step

private def target_pat_57 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_58 (v1 0) | v + 1 => target_pat_59 (v2 v 0)

private theorem step_pat_57 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_57 vars) (target_pat_57 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_57]; rw [h_vl]
    refine step_chain ?_ (step_pat_58 (v1 0))
    dsimp only [pat_57, pat_58, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_57]; rw [h_vl]
    refine step_chain ?_ (step_pat_59 (v2 v 0))
    dsimp only [pat_57, pat_59, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_56 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_57 (v1 (vars 0))

private theorem step_pat_56 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_56 vars) (target_pat_56 vars) := by
  refine step_chain ?_ (step_pat_57 (v1 (vars 0)))
  dsimp only [pat_56, pat_57, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_55 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_56 (v1 (vars 0))

private theorem step_pat_55 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_55 vars) (target_pat_55 vars) := by
  refine step_chain ?_ (step_pat_56 (v1 (vars 0)))
  dsimp only [pat_55, pat_56, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_54 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_55 (v1 (vars 0))

private theorem step_pat_54 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_54 vars) (target_pat_54 vars) := by
  refine step_chain ?_ (step_pat_55 (v1 (vars 0)))
  dsimp only [pat_54, pat_55, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_53 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_54 (v1 (vars 0))

private theorem step_pat_53 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_53 vars) (target_pat_53 vars) := by
  refine step_chain ?_ (step_pat_54 (v1 (vars 0)))
  dsimp only [pat_53, pat_54, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_52 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_53 (v1 (vars 0))

private theorem step_pat_52 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_52 vars) (target_pat_52 vars) := by
  refine step_chain ?_ (step_pat_53 (v1 (vars 0)))
  dsimp only [pat_52, pat_53, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_51 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_52 (v1 (vars 0))

private theorem step_pat_51 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_51 vars) (target_pat_51 vars) := by
  refine step_chain ?_ (step_pat_52 (v1 (vars 0)))
  dsimp only [pat_51, pat_52, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_50 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_51 (v1 (vars 0 + 1))

private theorem step_pat_50 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_50 vars) (target_pat_50 vars) := by
  refine step_chain ?_ (step_pat_51 (v1 (vars 0 + 1)))
  dsimp only [pat_50, pat_51, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_46 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_50 (v1 (vars 0 + 1))

private theorem step_pat_46 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_46 vars) (target_pat_46 vars) := by
  refine step_chain ?_ (step_pat_50 (v1 (vars 0 + 1)))
  dsimp only [pat_46, pat_50, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_41 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_46 (v1 (vars 0))

private theorem step_pat_41 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_41 vars) (target_pat_41 vars) := by
  refine step_chain ?_ (step_pat_46 (v1 (vars 0)))
  dsimp only [pat_41, pat_46, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_38 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_41 (v1 (vars 0))

private theorem step_pat_38 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_38 vars) (target_pat_38 vars) := by
  refine step_chain ?_ (step_pat_41 (v1 (vars 0)))
  dsimp only [pat_38, pat_41, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_35 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_38 (v1 (vars 0 + 1))

private theorem step_pat_35 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_35 vars) (target_pat_35 vars) := by
  refine step_chain ?_ (step_pat_38 (v1 (vars 0 + 1)))
  dsimp only [pat_35, pat_38, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_32 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_35 (v1 (vars 0 + 1))

private theorem step_pat_32 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_32 vars) (target_pat_32 vars) := by
  refine step_chain ?_ (step_pat_35 (v1 (vars 0 + 1)))
  dsimp only [pat_32, pat_35, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_25 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_32 (v1 (vars 0))

private theorem step_pat_25 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_25 vars) (target_pat_25 vars) := by
  refine step_chain ?_ (step_pat_32 (v1 (vars 0)))
  dsimp only [pat_25, pat_32, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_20 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_25 (v1 (vars 0 + 2 * vars 1))

private theorem step_pat_20 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_20 vars) (target_pat_20 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    have h_eq : target_pat_20 vars = target_pat_25 (v1 (vars 0)) := by
      simp -failIfUnchanged only [target_pat_20]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_25 (v1 (vars 0)))
    dsimp only [pat_20, pat_25, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    have h_eq : target_pat_20 vars = target_pat_20 (v2 ((vars 0 + 1) + 1) u) := by
      simp -failIfUnchanged only [target_pat_20]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_26 (v2 (vars 0) u)) ?_
      (step_chain_explicit (evalTapePattern pat_33 (v2 (vars 0) u)) ?_
        (step_chain_explicit (evalTapePattern pat_15 (v2 (vars 0 + 1) u)) ?_
          (step_chain ?_ (ih (v2 ((vars 0 + 1) + 1) u) rfl))))
    · dsimp only [pat_20, pat_26, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
    · dsimp only [pat_26, pat_33, evalTapePattern, evalTapeExpr]; pat_step
    · dsimp only [pat_33, pat_15, evalTapePattern, evalTapeExpr]; pat_step
    · dsimp only [pat_15, pat_20, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_15 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_20 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_15 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_15 vars) (target_pat_15 vars) := by
  refine step_chain ?_ (step_pat_20 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_15, pat_20, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_11 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_15 (v2 0 (vars 0))

private theorem step_pat_11 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_11 vars) (target_pat_11 vars) := by
  refine step_chain ?_ (step_pat_15 (v2 0 (vars 0)))
  dsimp only [pat_11, pat_15, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_6 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_11 (v1 (vars 0))

private theorem step_pat_6 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_6 vars) (target_pat_6 vars) := by
  refine step_chain ?_ (step_pat_11 (v1 (vars 0)))
  dsimp only [pat_6, pat_11, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_3 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_6 (v1 1)

private theorem step_pat_3 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_3 vars) (target_pat_3 vars) := by
  refine step_chain ?_ (step_pat_6 (v1 1))
  dsimp only [pat_3, pat_6, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_1 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_3 (fun _ => 0)

private theorem step_pat_1 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_1 vars) (target_pat_1 vars) := by
  refine step_chain ?_ (step_pat_3 (fun _ => 0))
  dsimp only [pat_1, pat_3, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_0_zero (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_1 (fun _ => 0) | _v + 1 => none

private theorem step_pat_0_zero (vars : Nat → Nat) (h_c : vars 0 = 0) :
  ReachesTarget ps (evalTapePattern pat_0 vars) (target_pat_0_zero vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_0_zero]; rw [h_vl]
    refine step_chain ?_ (step_pat_1 (fun _ => 0))
    dsimp only [pat_0, pat_1, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · omega
private def target_pat_27_zero (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_0_zero (v1 (vars 0))

private theorem step_pat_27_zero (vars : Nat → Nat) (h_c : vars 0 = 0) :
  ReachesTarget ps (evalTapePattern pat_27 vars) (target_pat_27_zero vars) := by
  refine step_chain ?_ (step_pat_0_zero (v1 (vars 0)) (by var_omega))
  dsimp only [pat_27, pat_0, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_21_zero (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_27_zero (v1 (vars 0))

private theorem step_pat_21_zero (vars : Nat → Nat) (h_c : vars 0 = 0) :
  ReachesTarget ps (evalTapePattern pat_21 vars) (target_pat_21_zero vars) := by
  refine step_chain ?_ (step_pat_27_zero (v1 (vars 0)) (by var_omega))
  dsimp only [pat_21, pat_27, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_16_zero (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_21_zero (v1 (vars 0))

private theorem step_pat_16_zero (vars : Nat → Nat) (h_c : vars 0 = 0) :
  ReachesTarget ps (evalTapePattern pat_16 vars) (target_pat_16_zero vars) := by
  refine step_chain ?_ (step_pat_21_zero (v1 (vars 0)) (by var_omega))
  dsimp only [pat_16, pat_21, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_12_zero (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_16_zero (v1 (vars 0))

private theorem step_pat_12_zero (vars : Nat → Nat) (h_c : vars 0 = 0) :
  ReachesTarget ps (evalTapePattern pat_12 vars) (target_pat_12_zero vars) := by
  refine step_chain ?_ (step_pat_16_zero (v1 (vars 0)) (by var_omega))
  dsimp only [pat_12, pat_16, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_7 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_12_zero (v1 0)

private theorem step_pat_7 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_7 vars) (target_pat_7 vars) := by
  refine step_chain ?_ (step_pat_12_zero (v1 0) rfl)
  dsimp only [pat_7, pat_12, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_34 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  some (evalTapePattern pat_61 (v2 0 (2 * vars 0 + 2 * vars 1 + 9)))

private abbrev Reaches34 (B : Nat) : Prop :=
  ∀ a, ReachesTarget ps (evalTapePattern pat_34 (v2 a B)) (target_pat_34 (v2 a B))

private abbrev Reaches34Lt (N : Nat) : Prop :=
  ∀ b < N, Reaches34 b

private def target_pat_28_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_34 (v2 (vars 0) (vars 1))

private theorem step_pat_28_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_28 vars) (target_pat_28_gen vars) := by
  refine step_chain ?_ (h_34 (vars 0))
  dsimp only [pat_28, pat_34, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_22_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => none | v + 1 => target_pat_28_gen (v2 v (vars 1))

private theorem step_pat_22_pos (vars : Nat → Nat) (h_c : vars 0 ≥ 1) (h_34 : Reaches34 (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_22 vars) (target_pat_22_pos vars) := by
  rcases h_vl : vars 0 with _ | v
  · omega
  · simp -failIfUnchanged only [target_pat_22_pos]; rw [h_vl]
    refine step_chain ?_ (step_pat_28_gen (v2 v (vars 1)) h_34)
    dsimp only [pat_22, pat_28, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_29_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_22_pos (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_29_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_29 vars) (target_pat_29_gen vars) := by
  refine step_chain ?_ (step_pat_22_pos (v2 (vars 0 + 1) (vars 1)) (by var_omega) h_34)
  dsimp only [pat_29, pat_22, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_23_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_29_gen (v2 (vars 0) (vars 1))

private theorem step_pat_23_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_23 vars) (target_pat_23_gen vars) := by
  refine step_chain ?_ (step_pat_29_gen (v2 (vars 0) (vars 1)) h_34)
  dsimp only [pat_23, pat_29, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_18_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_23_gen (v2 1 (vars 0))

private theorem step_pat_18_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_18 vars) (target_pat_18_gen vars) := by
  refine step_chain ?_ (step_pat_23_gen (v2 1 (vars 0)) h_34)
  dsimp only [pat_18, pat_23, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_30_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_23_gen (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_30_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_30 vars) (target_pat_30_gen vars) := by
  refine step_chain ?_ (step_pat_23_gen (v2 (vars 0 + 1) (vars 1)) h_34)
  dsimp only [pat_30, pat_23, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_24_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_30_gen (v2 (vars 2 + vars 0) (vars 1))

private theorem step_pat_24_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_24 vars) (target_pat_24_gen vars) := by
  induction h_vr : vars 2 generalizing vars with
  | zero =>
    have h_eq : target_pat_24_gen vars = target_pat_30_gen (v2 (vars 0) (vars 1)) := by
      simp -failIfUnchanged only [target_pat_24_gen]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_30_gen (v2 (vars 0) (vars 1)) h_34)
    dsimp only [pat_24, pat_30, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    have h_eq : target_pat_24_gen vars = target_pat_24_gen (v3 (vars 0 + 1) (vars 1) u) := by
      simp -failIfUnchanged only [target_pat_24_gen]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_31 (v3 (vars 0) (vars 1) u)) ?_ (step_chain
      ?_ (ih (v3 (vars 0 + 1) (vars 1) u) h_34 rfl))
    · dsimp only [pat_24, pat_31, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
    · dsimp only [pat_31, pat_24, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_19_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_24_gen (v3 1 (vars 0) (vars 1))

private theorem step_pat_19_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_19 vars) (target_pat_19_gen vars) := by
  refine step_chain ?_ (step_pat_24_gen (v3 1 (vars 0) (vars 1)) h_34)
  dsimp only [pat_19, pat_24, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_14_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_18_gen (v1 (vars 0)) | u + 1 => target_pat_19_gen (v2 (vars 0) u)

private theorem step_pat_14_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_14 vars) (target_pat_14_gen vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_14_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_18_gen (v1 (vars 0)) h_34)
    dsimp only [pat_14, pat_18, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_14_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_19_gen (v2 (vars 0) u) h_34)
    dsimp only [pat_14, pat_19, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_10_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_14_gen (v2 (vars 0) (vars 1))

private theorem step_pat_10_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_10 vars) (target_pat_10_gen vars) := by
  refine step_chain ?_ (step_pat_14_gen (v2 (vars 0) (vars 1)) h_34)
  dsimp only [pat_10, pat_14, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_17_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_22_pos (v2 1 (vars 0))

private theorem step_pat_17_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_17 vars) (target_pat_17_gen vars) := by
  refine step_chain ?_ (step_pat_22_pos (v2 1 (vars 0)) (by var_omega) h_34)
  dsimp only [pat_17, pat_22, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_13_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_17_gen (v1 (vars 0))

private theorem step_pat_13_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_13 vars) (target_pat_13_gen vars) := by
  refine step_chain ?_ (step_pat_17_gen (v1 (vars 0)) h_34)
  dsimp only [pat_13, pat_17, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_9_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_13_gen (v1 (vars 0))

private theorem step_pat_9_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_9 vars) (target_pat_9_gen vars) := by
  refine step_chain ?_ (step_pat_13_gen (v1 (vars 0)) h_34)
  dsimp only [pat_9, pat_13, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_5_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_9_gen (v1 (vars 0)) | u + 1 => target_pat_10_gen (v2 (vars 0) u)

private theorem step_pat_5_gen (vars : Nat → Nat) (h_34 : Reaches34 (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_5 vars) (target_pat_5_gen vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_5_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_9_gen (v1 (vars 0)) h_34)
    dsimp only [pat_5, pat_9, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_5_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_10_gen (v2 (vars 0) u) h_34)
    dsimp only [pat_5, pat_10, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_8_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_5_gen (v2 0 (vars 0))

private theorem step_pat_8_gen (vars : Nat → Nat) (h_34 : Reaches34 0) :
  ReachesTarget ps (evalTapePattern pat_8 vars) (target_pat_8_gen vars) := by
  refine step_chain ?_ (step_pat_5_gen (v2 0 (vars 0)) h_34)
  dsimp only [pat_8, pat_5, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_4_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_7 (fun _ => 0) | u + 1 => target_pat_8_gen (v1 u)

private theorem step_pat_4_gen (vars : Nat → Nat) (h_34 : Reaches34 0) :
  ReachesTarget ps (evalTapePattern pat_4 vars) (target_pat_4_gen vars) := by
  rcases h_vr : vars 0 with _ | u
  · simp -failIfUnchanged only [target_pat_4_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_7 (fun _ => 0))
    dsimp only [pat_4, pat_7, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_4_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_8_gen (v1 u) h_34)
    dsimp only [pat_4, pat_8, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_47 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_6 (v1 (vars 0 + 1))

private theorem step_pat_47 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_47 vars) (target_pat_47 vars) := by
  refine step_chain ?_ (step_pat_6 (v1 (vars 0 + 1)))
  dsimp only [pat_47, pat_6, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_42 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_47 (v1 (vars 0))

private theorem step_pat_42 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_42 vars) (target_pat_42 vars) := by
  refine step_chain ?_ (step_pat_47 (v1 (vars 0)))
  dsimp only [pat_42, pat_47, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_43_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_4_gen (v1 (vars 1 + 1)) | v + 1 => target_pat_5_gen (v2 v (vars 1 + 1))

private theorem step_pat_43_gen (vars : Nat → Nat) (h_34 : Reaches34Lt (vars 0 + 1)) :
  ReachesTarget ps (evalTapePattern pat_43 vars) (target_pat_43_gen vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_43_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_4_gen (v1 (vars 1 + 1)) (h_34 0 (by omega)))
    dsimp only [pat_43, pat_4, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_43_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_5_gen (v2 v (vars 1 + 1)) (h_34 v (by omega)))
    dsimp only [pat_43, pat_5, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_48_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_42 (v1 (vars 1 + 1)) | v + 1 => target_pat_43_gen (v2 v (vars 1 + 1))

private theorem step_pat_48_gen (vars : Nat → Nat) (h_34 : Reaches34Lt (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_48 vars) (target_pat_48_gen vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_48_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_42 (v1 (vars 1 + 1)))
    dsimp only [pat_48, pat_42, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_48_gen]; rw [h_vl]
    have h_34_v : Reaches34Lt (v + 1) := by
      intro b hb; exact h_34 b (by omega)
    refine step_chain ?_ (step_pat_43_gen (v2 v (vars 1 + 1)) h_34_v)
    dsimp only [pat_48, pat_43, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_44_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_48_gen (v2 (vars 0) (vars 1))

private theorem step_pat_44_gen (vars : Nat → Nat) (h_34 : Reaches34Lt (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_44 vars) (target_pat_44_gen vars) := by
  refine step_chain ?_ (step_pat_48_gen (v2 (vars 0) (vars 1)) h_34)
  dsimp only [pat_44, pat_48, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_49_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_44_gen (v2 (vars 1) (vars 0 + vars 2 + 1))

private theorem step_pat_49_gen (vars : Nat → Nat) (h_34 : Reaches34Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_49 vars) (target_pat_49_gen vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    have h_eq : target_pat_49_gen vars = target_pat_44_gen (v2 (vars 1) (vars 2 + 1)) := by
      simp -failIfUnchanged only [target_pat_49_gen]; rw [h_vl]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_44_gen (v2 (vars 1) (vars 2 + 1)) h_34)
    dsimp only [pat_49, pat_44, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  | succ v ih =>
    have h_eq : target_pat_49_gen vars = target_pat_49_gen (v3 v (vars 1) (vars 2 + 1)) := by
      simp -failIfUnchanged only [target_pat_49_gen]; rw [h_vl]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_45 (v3 v (vars 1) (vars 2 + 1))) ?_
      (step_chain ?_ (ih (v3 v (vars 1) (vars 2 + 1)) h_34 rfl))
    · dsimp only [pat_49, pat_45, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
    · dsimp only [pat_45, pat_49, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_45_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_49_gen (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_45_gen (vars : Nat → Nat) (h_34 : Reaches34Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_45 vars) (target_pat_45_gen vars) := by
  refine step_chain ?_ (step_pat_49_gen (v3 (vars 0) (vars 1) (vars 2)) h_34)
  dsimp only [pat_45, pat_49, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_40_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_44_gen (v2 (vars 1) 1) | v + 1 => target_pat_45_gen (v3 v (vars 1) 1)

private theorem step_pat_40_gen (vars : Nat → Nat) (h_34 : Reaches34Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_40 vars) (target_pat_40_gen vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_40_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_44_gen (v2 (vars 1) 1) h_34)
    dsimp only [pat_40, pat_44, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_40_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_45_gen (v3 v (vars 1) 1) h_34)
    dsimp only [pat_40, pat_45, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_37_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_40_gen (v2 (vars 0) (vars 1))

private theorem step_pat_37_gen (vars : Nat → Nat) (h_34 : Reaches34Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_37 vars) (target_pat_37_gen vars) := by
  refine step_chain ?_ (step_pat_40_gen (v2 (vars 0) (vars 1)) h_34)
  dsimp only [pat_37, pat_40, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_39_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_42 (v1 1) | v + 1 => target_pat_43_gen (v2 v 1)

private theorem step_pat_39_gen (vars : Nat → Nat) (h_34 : Reaches34Lt (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_39 vars) (target_pat_39_gen vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_39_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_42 (v1 1))
    dsimp only [pat_39, pat_42, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_39_gen]; rw [h_vl]
    have h_34_v : Reaches34Lt (v + 1) := by
      intro b hb; exact h_34 b (by omega)
    refine step_chain ?_ (step_pat_43_gen (v2 v 1) h_34_v)
    dsimp only [pat_39, pat_43, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_36_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_39_gen (v1 (vars 0))

private theorem step_pat_36_gen (vars : Nat → Nat) (h_34 : Reaches34Lt (vars 0)) :
  ReachesTarget ps (evalTapePattern pat_36 vars) (target_pat_36_gen vars) := by
  refine step_chain ?_ (step_pat_39_gen (v1 (vars 0)) h_34)
  dsimp only [pat_36, pat_39, evalTapePattern, evalTapeExpr]; pat_step
private theorem step_pat_34 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_34 vars) (target_pat_34 vars) := by
  induction h_b : vars 1 using Nat.strong_induction_on generalizing vars with
  | h b ih =>
    have h_34 : Reaches34Lt (vars 1) := by
      intro b' hb' a
      exact ih b' (h_b ▸ hb') (v2 a b') rfl
    rcases h_vl : vars 0 with _ | v
    · have h_eq : target_pat_36_gen (v1 (vars 1)) = target_pat_34 vars := by
        simp -failIfUnchanged only [target_pat_34]; rw [h_vl]
        rcases vars 1 with _ | _ | b' <;> (congr_cfg pat_61)
      refine cast_target h_eq (step_chain ?_ (step_pat_36_gen (v1 (vars 1)) h_34))
      dsimp only [pat_34, pat_36, evalTapePattern, evalTapeExpr]; rw [h_vl];
        pat_step
    · have h_eq : target_pat_37_gen (v2 v (vars 1)) = target_pat_34 vars := by
        simp -failIfUnchanged only [target_pat_34]; rw [h_vl]
        rcases v with _ | v' <;> rcases vars 1 with _ | _ | b' <;> (congr_cfg pat_61)
      refine cast_target h_eq (step_chain ?_ (step_pat_37_gen (v2 v (vars 1)) h_34))
      dsimp only [pat_34, pat_37, evalTapePattern, evalTapeExpr]; rw [h_vl];
        pat_step

private theorem all_reaches_34 (B : Nat) : Reaches34 B :=
  fun a => step_pat_34 (v2 a B)

private theorem all_reaches_34_lt (N : Nat) : Reaches34Lt N :=
  fun b _ => all_reaches_34 b

private def target_pat_28 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_28_gen vars
private theorem step_pat_28 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_28 vars) (target_pat_28 vars) := step_pat_28_gen vars (all_reaches_34 _)
private def target_pat_29 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_29_gen vars
private theorem step_pat_29 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_29 vars) (target_pat_29 vars) := step_pat_29_gen vars (all_reaches_34 _)
private def target_pat_23 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_23_gen vars
private theorem step_pat_23 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_23 vars) (target_pat_23 vars) := step_pat_23_gen vars (all_reaches_34 _)
private def target_pat_18 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_18_gen vars
private theorem step_pat_18 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_18 vars) (target_pat_18 vars) := step_pat_18_gen vars (all_reaches_34 _)
private def target_pat_30 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_30_gen vars
private theorem step_pat_30 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_30 vars) (target_pat_30 vars) := step_pat_30_gen vars (all_reaches_34 _)
private def target_pat_24 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_24_gen vars
private theorem step_pat_24 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_24 vars) (target_pat_24 vars) := step_pat_24_gen vars (all_reaches_34 _)
private def target_pat_19 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_19_gen vars
private theorem step_pat_19 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_19 vars) (target_pat_19 vars) := step_pat_19_gen vars (all_reaches_34 _)
private def target_pat_14 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_14_gen vars
private theorem step_pat_14 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_14 vars) (target_pat_14 vars) := step_pat_14_gen vars (all_reaches_34 _)
private def target_pat_10 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_10_gen vars
private theorem step_pat_10 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_10 vars) (target_pat_10 vars) := step_pat_10_gen vars (all_reaches_34 _)
private def target_pat_17 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_17_gen vars
private theorem step_pat_17 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_17 vars) (target_pat_17 vars) := step_pat_17_gen vars (all_reaches_34 _)
private def target_pat_13 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_13_gen vars
private theorem step_pat_13 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_13 vars) (target_pat_13 vars) := step_pat_13_gen vars (all_reaches_34 _)
private def target_pat_9 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) := target_pat_9_gen vars
private theorem step_pat_9 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_9 vars) (target_pat_9 vars) := step_pat_9_gen vars (all_reaches_34 _)
private def target_pat_5 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) := target_pat_5_gen vars
private theorem step_pat_5 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_5 vars) (target_pat_5 vars) := step_pat_5_gen vars (all_reaches_34 _)
private def target_pat_8 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) := target_pat_8_gen vars
private theorem step_pat_8 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_8 vars) (target_pat_8 vars) := step_pat_8_gen vars (all_reaches_34 0)
private def target_pat_4 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) := target_pat_4_gen vars
private theorem step_pat_4 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_4 vars) (target_pat_4 vars) := step_pat_4_gen vars (all_reaches_34 0)
private def target_pat_43 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_43_gen vars
private theorem step_pat_43 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_43 vars) (target_pat_43 vars) := step_pat_43_gen vars (all_reaches_34_lt _)
private def target_pat_48 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_48_gen vars
private theorem step_pat_48 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_48 vars) (target_pat_48 vars) := step_pat_48_gen vars (all_reaches_34_lt _)
private def target_pat_44 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_44_gen vars
private theorem step_pat_44 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_44 vars) (target_pat_44 vars) := step_pat_44_gen vars (all_reaches_34_lt _)
private def target_pat_49 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_49_gen vars
private theorem step_pat_49 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_49 vars) (target_pat_49 vars) := step_pat_49_gen vars (all_reaches_34_lt _)
private def target_pat_45 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_45_gen vars
private theorem step_pat_45 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_45 vars) (target_pat_45 vars) := step_pat_45_gen vars (all_reaches_34_lt _)
private def target_pat_40 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_40_gen vars
private theorem step_pat_40 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_40 vars) (target_pat_40 vars) := step_pat_40_gen vars (all_reaches_34_lt _)
private def target_pat_37 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_37_gen vars
private theorem step_pat_37 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_37 vars) (target_pat_37 vars) := step_pat_37_gen vars (all_reaches_34_lt _)
private def target_pat_39 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_39_gen vars
private theorem step_pat_39 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_39 vars) (target_pat_39 vars) := step_pat_39_gen vars (all_reaches_34_lt _)
private def target_pat_36 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_36_gen vars
private theorem step_pat_36 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_36 vars) (target_pat_36 vars) := step_pat_36_gen vars (all_reaches_34_lt _)

private def target_pat_2 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_4 (v1 1) | v + 1 => target_pat_5 (v2 v 1)

private theorem step_pat_2 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_2 vars) (target_pat_2 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_2]; rw [h_vl]
    refine step_chain ?_ (step_pat_4 (v1 1))
    dsimp only [pat_2, pat_4, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_2]; rw [h_vl]
    refine step_chain ?_ (step_pat_5 (v2 v 1))
    dsimp only [pat_2, pat_5, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_0 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_1 (fun _ => 0) | v + 1 => target_pat_2 (v1 v)

private theorem step_pat_0 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_0 vars) (target_pat_0 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_0]; rw [h_vl]
    refine step_chain ?_ (step_pat_1 (fun _ => 0))
    dsimp only [pat_0, pat_1, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_0]; rw [h_vl]
    refine step_chain ?_ (step_pat_2 (v1 v))
    dsimp only [pat_0, pat_2, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_27 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_0 (v1 (vars 0))

private theorem step_pat_27 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_27 vars) (target_pat_27 vars) := by
  refine step_chain ?_ (step_pat_0 (v1 (vars 0)))
  dsimp only [pat_27, pat_0, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_21 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_27 (v1 (vars 0))

private theorem step_pat_21 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_21 vars) (target_pat_21 vars) := by
  refine step_chain ?_ (step_pat_27 (v1 (vars 0)))
  dsimp only [pat_21, pat_27, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_16 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_21 (v1 (vars 0))

private theorem step_pat_16 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_16 vars) (target_pat_16 vars) := by
  refine step_chain ?_ (step_pat_21 (v1 (vars 0)))
  dsimp only [pat_16, pat_21, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_12 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_16 (v1 (vars 0))

private theorem step_pat_12 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_12 vars) (target_pat_12 vars) := by
  refine step_chain ?_ (step_pat_16 (v1 (vars 0)))
  dsimp only [pat_12, pat_16, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_22 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_27 (v1 (vars 1)) | v + 1 => target_pat_28 (v2 v (vars 1))

private theorem step_pat_22 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_22 vars) (target_pat_22 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_22]; rw [h_vl]
    refine step_chain ?_ (step_pat_27 (v1 (vars 1)))
    dsimp only [pat_22, pat_27, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_22]; rw [h_vl]
    refine step_chain ?_ (step_pat_28 (v2 v (vars 1)))
    dsimp only [pat_22, pat_28, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step

private def target_pat_189 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_35 (v1 0)

private theorem step_pat_189 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_189 vars) (target_pat_189 vars) := by
  refine step_chain ?_ (step_pat_35 (v1 0))
  dsimp only [pat_189, pat_35, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_155 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_189 (fun _ => 0)

private theorem step_pat_155 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_155 vars) (target_pat_155 vars) := by
  refine step_chain ?_ (step_pat_189 (fun _ => 0))
  dsimp only [pat_155, pat_189, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_130 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_155 (fun _ => 0)

private theorem step_pat_130 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_130 vars) (target_pat_130 vars) := by
  refine step_chain ?_ (step_pat_155 (fun _ => 0))
  dsimp only [pat_130, pat_155, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_284 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_25 (v1 (vars 0))

private theorem step_pat_284 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_284 vars) (target_pat_284 vars) := by
  refine step_chain ?_ (step_pat_25 (v1 (vars 0)))
  dsimp only [pat_284, pat_25, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_256 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_284 (v1 (vars 0 + 1))

private theorem step_pat_256 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_256 vars) (target_pat_256 vars) := by
  refine step_chain ?_ (step_pat_284 (v1 (vars 0 + 1)))
  dsimp only [pat_256, pat_284, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_236 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_256 (v1 0)

private theorem step_pat_236 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_236 vars) (target_pat_236 vars) := by
  refine step_chain ?_ (step_pat_256 (v1 0))
  dsimp only [pat_236, pat_256, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_216 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_236 (fun _ => 0)

private theorem step_pat_216 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_216 vars) (target_pat_216 vars) := by
  refine step_chain ?_ (step_pat_236 (fun _ => 0))
  dsimp only [pat_216, pat_236, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_193 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_216 (fun _ => 0)

private theorem step_pat_193 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_193 vars) (target_pat_193 vars) := by
  refine step_chain ?_ (step_pat_216 (fun _ => 0))
  dsimp only [pat_193, pat_216, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_160 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_193 (fun _ => 0)

private theorem step_pat_160 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_160 vars) (target_pat_160 vars) := by
  refine step_chain ?_ (step_pat_193 (fun _ => 0))
  dsimp only [pat_160, pat_193, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_194 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_7 (fun _ => 0)

private theorem step_pat_194 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_194 vars) (target_pat_194 vars) := by
  refine step_chain ?_ (step_pat_7 (fun _ => 0))
  dsimp only [pat_194, pat_7, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_195 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_9 (v1 (vars 0))

private theorem step_pat_195 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_195 vars) (target_pat_195 vars) := by
  refine step_chain ?_ (step_pat_9 (v1 (vars 0)))
  dsimp only [pat_195, pat_9, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_161 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_194 (fun _ => 0) | v + 1 => target_pat_195 (v1 v)

private theorem step_pat_161 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_161 vars) (target_pat_161 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_161]; rw [h_vl]
    refine step_chain ?_ (step_pat_194 (fun _ => 0))
    dsimp only [pat_161, pat_194, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_161]; rw [h_vl]
    refine step_chain ?_ (step_pat_195 (v1 v))
    dsimp only [pat_161, pat_195, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_135 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_160 (fun _ => 0) | v + 1 => target_pat_161 (v1 v)

private theorem step_pat_135 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_135 vars) (target_pat_135 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_135]; rw [h_vl]
    refine step_chain ?_ (step_pat_160 (fun _ => 0))
    dsimp only [pat_135, pat_160, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_135]; rw [h_vl]
    refine step_chain ?_ (step_pat_161 (v1 v))
    dsimp only [pat_135, pat_161, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_114_zero (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_135 (v1 (vars 0)) | _u + 1 => none

private theorem step_pat_114_zero (vars : Nat → Nat) (h_c : vars 1 = 0) :
  ReachesTarget ps (evalTapePattern pat_114 vars) (target_pat_114_zero vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_114_zero]; rw [h_vr]
    refine step_chain ?_ (step_pat_135 (v1 (vars 0)))
    dsimp only [pat_114, pat_135, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · omega
private def target_pat_313 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => none | u + 1 => target_pat_114_zero (v2 (vars 0) u)

private theorem step_pat_313 (vars : Nat → Nat) (h_c : vars 1 = 1) :
  ReachesTarget ps (evalTapePattern pat_313 vars) (target_pat_313 vars) := by
  rcases h_vr : vars 1 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_313]; rw [h_vr]
    refine step_chain ?_ (step_pat_114_zero (v2 (vars 0) u) (by var_omega))
    dsimp only [pat_313, pat_114, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_302 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => none | u + 1 => target_pat_313 (v2 (vars 0 + 1) u)

private theorem step_pat_302 (vars : Nat → Nat) (h_c : vars 1 = 2) :
  ReachesTarget ps (evalTapePattern pat_302 vars) (target_pat_302 vars) := by
  rcases h_vr : vars 1 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_302]; rw [h_vr]
    refine step_chain ?_ (step_pat_313 (v2 (vars 0 + 1) u) (by var_omega))
    dsimp only [pat_302, pat_313, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_278 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_302 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_278 (vars : Nat → Nat) (h_c : vars 1 = 2) :
  ReachesTarget ps (evalTapePattern pat_278 vars) (target_pat_278 vars) := by
  refine step_chain ?_ (step_pat_302 (v2 (vars 0 + 1) (vars 1)) (by var_omega))
  dsimp only [pat_278, pat_302, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_250 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_278 (v2 (vars 0) (vars 1 + 1))

private theorem step_pat_250 (vars : Nat → Nat) (h_c : vars 1 = 1) :
  ReachesTarget ps (evalTapePattern pat_250 vars) (target_pat_250 vars) := by
  refine step_chain ?_ (step_pat_278 (v2 (vars 0) (vars 1 + 1)) (by var_omega))
  dsimp only [pat_250, pat_278, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_231 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_250 (v2 (vars 0) (vars 1))

private theorem step_pat_231 (vars : Nat → Nat) (h_c : vars 1 = 1) :
  ReachesTarget ps (evalTapePattern pat_231 vars) (target_pat_231 vars) := by
  refine step_chain ?_ (step_pat_250 (v2 (vars 0) (vars 1)) (by var_omega))
  dsimp only [pat_231, pat_250, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_213 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_231 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_213 (vars : Nat → Nat) (h_c : vars 1 = 1) :
  ReachesTarget ps (evalTapePattern pat_213 vars) (target_pat_213 vars) := by
  refine step_chain ?_ (step_pat_231 (v2 (vars 0 + 1) (vars 1)) (by var_omega))
  dsimp only [pat_213, pat_231, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_190 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_213 (v2 0 (vars 0))

private theorem step_pat_190 (vars : Nat → Nat) (h_c : vars 0 = 1) :
  ReachesTarget ps (evalTapePattern pat_190 vars) (target_pat_190 vars) := by
  refine step_chain ?_ (step_pat_213 (v2 0 (vars 0)) (by var_omega))
  dsimp only [pat_190, pat_213, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_156 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_190 (v1 (vars 0))

private theorem step_pat_156 (vars : Nat → Nat) (h_c : vars 0 = 1) :
  ReachesTarget ps (evalTapePattern pat_156 vars) (target_pat_156 vars) := by
  refine step_chain ?_ (step_pat_190 (v1 (vars 0)) (by var_omega))
  dsimp only [pat_156, pat_190, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_131 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_156 (v1 (vars 0))

private theorem step_pat_131 (vars : Nat → Nat) (h_c : vars 0 = 1) :
  ReachesTarget ps (evalTapePattern pat_131 vars) (target_pat_131 vars) := by
  refine step_chain ?_ (step_pat_156 (v1 (vars 0)) (by var_omega))
  dsimp only [pat_131, pat_156, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_112 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => none | u + 1 => target_pat_131 (v1 u)

private theorem step_pat_112 (vars : Nat → Nat) (h_c : vars 0 = 2) :
  ReachesTarget ps (evalTapePattern pat_112 vars) (target_pat_112 vars) := by
  rcases h_vr : vars 0 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_112]; rw [h_vr]
    refine step_chain ?_ (step_pat_131 (v1 u) (by var_omega))
    dsimp only [pat_112, pat_131, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_100 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_112 (v1 2)

private theorem step_pat_100 :
  ReachesTarget ps (evalTapePattern pat_100 (v1 0)) (target_pat_100 (v1 0)) := by
  refine step_chain ?_ (step_pat_112 (v1 2) rfl)
  dsimp only [pat_100, pat_112, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_285 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_250 (v2 (vars 0 + 2 * vars 1) (vars 2))

private theorem step_pat_285 (vars : Nat → Nat) (h_c : vars 2 = 1) :
  ReachesTarget ps (evalTapePattern pat_285 vars) (target_pat_285 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    have h_eq : target_pat_285 vars = target_pat_250 (v2 (vars 0) (vars 2)) := by
      simp -failIfUnchanged only [target_pat_285]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_250 (v2 (vars 0) (vars 2)) (by var_omega))
    dsimp only [pat_285, pat_250, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  | succ u ih =>
    have h_eq : target_pat_285 vars = target_pat_285 (v3 ((vars 0 + 1) + 1) u (vars 2)) := by
      simp -failIfUnchanged only [target_pat_285]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_307 (v3 (vars 0) u (vars 2))) ?_
      (step_chain_explicit (evalTapePattern pat_318 (v3 (vars 0) u (vars 2))) ?_
        (step_chain_explicit (evalTapePattern pat_257 (v3 (vars 0 + 1) u (vars 2))) ?_
          (step_chain ?_ (ih (v3 ((vars 0 + 1) + 1) u (vars 2)) h_c rfl))))
    · dsimp only [pat_285, pat_307, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
    · dsimp only [pat_307, pat_318, evalTapePattern, evalTapeExpr]; pat_step
    · dsimp only [pat_318, pat_257, evalTapePattern, evalTapeExpr]; pat_step
    · dsimp only [pat_257, pat_285, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_257 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_285 (v3 (vars 0 + 1) (vars 1) (vars 2))

private theorem step_pat_257 (vars : Nat → Nat) (h_c : vars 2 = 1) :
  ReachesTarget ps (evalTapePattern pat_257 vars) (target_pat_257 vars) := by
  refine step_chain ?_ (step_pat_285 (v3 (vars 0 + 1) (vars 1) (vars 2)) (by var_omega))
  dsimp only [pat_257, pat_285, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_237 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_257 (v3 0 (vars 0) (vars 1))

private theorem step_pat_237 (vars : Nat → Nat) (h_c : vars 1 = 1) :
  ReachesTarget ps (evalTapePattern pat_237 vars) (target_pat_237 vars) := by
  refine step_chain ?_ (step_pat_257 (v3 0 (vars 0) (vars 1)) (by var_omega))
  dsimp only [pat_237, pat_257, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_217 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_237 (v2 (vars 0) (vars 1))

private theorem step_pat_217 (vars : Nat → Nat) (h_c : vars 1 = 1) :
  ReachesTarget ps (evalTapePattern pat_217 vars) (target_pat_217 vars) := by
  refine step_chain ?_ (step_pat_237 (v2 (vars 0) (vars 1)) (by var_omega))
  dsimp only [pat_217, pat_237, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_288 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_217 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_288 (vars : Nat → Nat) (h_c : vars 1 = 1) :
  ReachesTarget ps (evalTapePattern pat_288 vars) (target_pat_288 vars) := by
  refine step_chain ?_ (step_pat_217 (v2 (vars 0 + 1) (vars 1)) (by var_omega))
  dsimp only [pat_288, pat_217, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_260 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_288 (v2 (vars 0) (vars 1))

private theorem step_pat_260 (vars : Nat → Nat) (h_c : vars 1 = 1) :
  ReachesTarget ps (evalTapePattern pat_260 vars) (target_pat_260 vars) := by
  refine step_chain ?_ (step_pat_288 (v2 (vars 0) (vars 1)) (by var_omega))
  dsimp only [pat_260, pat_288, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_196 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_217 (v2 1 (vars 0))

private theorem step_pat_196 (vars : Nat → Nat) (h_c : vars 0 = 1) :
  ReachesTarget ps (evalTapePattern pat_196 vars) (target_pat_196 vars) := by
  refine step_chain ?_ (step_pat_217 (v2 1 (vars 0)) (by var_omega))
  dsimp only [pat_196, pat_217, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_162 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_196 (v1 (vars 0))

private theorem step_pat_162 (vars : Nat → Nat) (h_c : vars 0 = 1) :
  ReachesTarget ps (evalTapePattern pat_162 vars) (target_pat_162 vars) := by
  refine step_chain ?_ (step_pat_196 (v1 (vars 0)) (by var_omega))
  dsimp only [pat_162, pat_196, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_136 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_162 (v1 (vars 1)) | _v + 1 => none

private theorem step_pat_136 (vars : Nat → Nat) (h_c0 : vars 0 = 0) (h_c1 : vars 1 = 1) :
  ReachesTarget ps (evalTapePattern pat_136 vars) (target_pat_136 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_136]; rw [h_vl]
    refine step_chain ?_ (step_pat_162 (v1 (vars 1)) (by var_omega))
    dsimp only [pat_136, pat_162, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · omega
private def target_pat_114 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => none | u + 1 => target_pat_136 (v2 (vars 0) u)

private theorem step_pat_114 (vars : Nat → Nat) (h_c0 : vars 0 = 0) (h_c1 : vars 1 = 2) :
  ReachesTarget ps (evalTapePattern pat_114 vars) (target_pat_114 vars) := by
  rcases h_vr : vars 1 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_114]; rw [h_vr]
    refine step_chain ?_ (step_pat_136 (v2 (vars 0) u) (by var_omega) (by var_omega))
    dsimp only [pat_114, pat_136, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_101 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_114 (v2 (vars 0) 2)

private theorem step_pat_101 (vars : Nat → Nat) (h_c : vars 0 = 0) :
  ReachesTarget ps (evalTapePattern pat_101 vars) (target_pat_101 vars) := by
  refine step_chain ?_ (step_pat_114 (v2 (vars 0) 2) (by var_omega) rfl)
  dsimp only [pat_101, pat_114, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_200 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  some (evalTapePattern pat_61 (v2 (vars 0 + 1) (vars 1)))

private theorem step_pat_200 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_200 vars) (target_pat_200 vars) := by
  refine step_base ?_ (in_ps_61 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_200, pat_61, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_333 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_200 (v2 (vars 0) 0) | u + 1 => target_pat_200 (v2 (vars 0) (u + 1))

private theorem step_pat_333 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_333 vars) (target_pat_333 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_333]; rw [h_vr]
    refine step_chain ?_ (step_pat_200 (v2 (vars 0) 0))
    dsimp only [pat_333, pat_200, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_333]; rw [h_vr]
    refine step_chain ?_ (step_pat_200 (v2 (vars 0) (u + 1)))
    dsimp only [pat_333, pat_200, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_261 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  some (evalTapePattern pat_61 (v2 0 (4 * vars 0 + 4 * (vars 0 / 2) + 4 * vars 1 + 23)))

private abbrev Reaches261Lt (N : Nat) : Prop :=
  ∀ v < N, ∀ b, ReachesTarget ps (evalTapePattern pat_261 (v3 v b 1)) (target_pat_261 (v3 v b 1))

private def target_pat_239_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_260 (v2 1 (vars 1)) | v + 1 => target_pat_261 (v3 v 1 1)

private theorem step_pat_239_gen (vars : Nat → Nat) (h_c : vars 1 = 1) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_239 vars) (target_pat_239_gen vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_239_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_260 (v2 1 (vars 1)) (by var_omega))
    dsimp only [pat_239, pat_260, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_239_gen]; rw [h_vl]
    refine step_chain ?_ (h_261 v (by omega) 1)
    dsimp only [pat_239, pat_261, evalTapePattern, evalTapeExpr]; rw [h_vl, h_c];
      pat_step
private def target_pat_220_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_239_gen (v2 (vars 0) (vars 1))

private theorem step_pat_220_gen (vars : Nat → Nat) (h_c : vars 1 = 1) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_220 vars) (target_pat_220_gen vars) := by
  refine step_chain ?_ (step_pat_239_gen (v2 (vars 0) (vars 1)) (by var_omega) h_261)
  dsimp only [pat_220, pat_239, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_289_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_260 (v2 (vars 1 + 1) (vars 2)) | v + 1 => target_pat_261 (v3 v (vars 1 + 1) 1)

private theorem step_pat_289_gen (vars : Nat → Nat) (h_c : vars 2 = 1) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_289 vars) (target_pat_289_gen vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_289_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_260 (v2 (vars 1 + 1) (vars 2)) (by var_omega))
    dsimp only [pat_289, pat_260, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_289_gen]; rw [h_vl]
    refine step_chain ?_ (h_261 v (by omega) (vars 1 + 1))
    dsimp only [pat_289, pat_261, evalTapePattern, evalTapeExpr]; rw [h_vl, h_c];
      pat_step
private def target_pat_262_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_289_gen (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_262_gen (vars : Nat → Nat) (h_c : vars 2 = 1) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_262 vars) (target_pat_262_gen vars) := by
  refine step_chain ?_ (step_pat_289_gen (v3 (vars 0) (vars 1) (vars 2)) (by var_omega) h_261)
  dsimp only [pat_262, pat_289, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_290_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_262_gen (v3 (vars 1) (vars 0 + vars 2 + 1) (vars 3))

private theorem step_pat_290_gen (vars : Nat → Nat) (h_c : vars 3 = 1) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_290 vars) (target_pat_290_gen vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    have h_eq : target_pat_290_gen vars = target_pat_262_gen (v3 (vars 1) (vars 2 + 1) (vars
      3)) := by
      simp -failIfUnchanged only [target_pat_290_gen]; rw [h_vl]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_262_gen (v3 (vars 1) (vars 2 + 1) (vars 3)) (by var_omega)
      h_261)
    dsimp only [pat_290, pat_262, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  | succ v ih =>
    have h_eq : target_pat_290_gen vars = target_pat_290_gen
      (v4 v (vars 1) (vars 2 + 1) (vars 3)) := by
      simp -failIfUnchanged only [target_pat_290_gen]; rw [h_vl]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_263 (v4 v (vars 1) (vars 2 + 1) (vars 3)))
      ?_ (step_chain ?_ (ih (v4 v (vars 1) (vars 2 + 1) (vars 3)) h_c h_261 rfl))
    · dsimp only [pat_290, pat_263, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
    · dsimp only [pat_263, pat_290, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_263_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_290_gen (v4 (vars 0) (vars 1) (vars 2) (vars 3))

private theorem step_pat_263_gen (vars : Nat → Nat) (h_c : vars 3 = 1) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_263 vars) (target_pat_263_gen vars) := by
  refine step_chain ?_ (step_pat_290_gen
    (v4 (vars 0) (vars 1) (vars 2) (vars 3)) (by var_omega) h_261)
  dsimp only [pat_263, pat_290, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_240_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_262_gen (v3 (vars 1) 1 (vars 2)) | v + 1 => target_pat_263_gen
    (v4 v (vars 1) 1 (vars 2))

private theorem step_pat_240_gen (vars : Nat → Nat) (h_c : vars 2 = 1) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_240 vars) (target_pat_240_gen vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_240_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_262_gen (v3 (vars 1) 1 (vars 2)) (by var_omega) h_261)
    dsimp only [pat_240, pat_262, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_240_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_263_gen (v4 v (vars 1) 1 (vars 2)) (by var_omega) h_261)
    dsimp only [pat_240, pat_263, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_221_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_240_gen (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_221_gen (vars : Nat → Nat) (h_c : vars 2 = 1) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_221 vars) (target_pat_221_gen vars) := by
  refine step_chain ?_ (step_pat_240_gen (v3 (vars 0) (vars 1) (vars 2)) (by var_omega) h_261)
  dsimp only [pat_221, pat_240, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_199_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_220_gen (v2 (vars 1) (vars 2)) | v + 1 => target_pat_221_gen
    (v3 v (vars 1) (vars 2))

private theorem step_pat_199_gen (vars : Nat → Nat) (h_c : vars 2 = 1) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_199 vars) (target_pat_199_gen vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_199_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_220_gen (v2 (vars 1) (vars 2)) (by var_omega) h_261)
    dsimp only [pat_199, pat_220, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_199_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_221_gen (v3 v (vars 1) (vars 2)) (by var_omega) h_261)
    dsimp only [pat_199, pat_221, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_164_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => none | u + 1 => target_pat_199_gen (v3 (vars 0) (vars 1) u)

private theorem step_pat_164_gen (vars : Nat → Nat) (h_c : vars 2 = 2) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_164 vars) (target_pat_164_gen vars) := by
  rcases h_vr : vars 2 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_164_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_199_gen (v3 (vars 0) (vars 1) u) (by var_omega) h_261)
    dsimp only [pat_164, pat_199, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_137_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => none | v + 1 => target_pat_164_gen (v3 v (vars 1) 2)

private theorem step_pat_137_gen (vars : Nat → Nat) (h_c : vars 0 ≥ 1) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_137 vars) (target_pat_137_gen vars) := by
  rcases h_vl : vars 0 with _ | v
  · omega
  · simp -failIfUnchanged only [target_pat_137_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_164_gen (v3 v (vars 1) 2) rfl h_261)
    dsimp only [pat_137, pat_164, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_165_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_137_gen (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_165_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_165 vars) (target_pat_165_gen vars) := by
  refine step_chain ?_ (step_pat_137_gen (v2 (vars 0 + 1) (vars 1)) (by var_omega) h_261)
  dsimp only [pat_165, pat_137, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_138_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_165_gen (v2 (vars 2 + vars 0) (vars 1))

private theorem step_pat_138_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_138 vars) (target_pat_138_gen vars) := by
  induction h_vr : vars 2 generalizing vars with
  | zero =>
    have h_eq : target_pat_138_gen vars = target_pat_165_gen (v2 (vars 0) (vars 1)) := by
      simp -failIfUnchanged only [target_pat_138_gen]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_165_gen (v2 (vars 0) (vars 1)) h_261)
    dsimp only [pat_138, pat_165, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  | succ u ih =>
    have h_eq : target_pat_138_gen vars = target_pat_138_gen (v3 (vars 0 + 1) (vars 1) u) := by
      simp -failIfUnchanged only [target_pat_138_gen]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_166 (v3 (vars 0) (vars 1) u)) ?_ (step_chain
      ?_ (ih (v3 (vars 0 + 1) (vars 1) u) h_261 rfl))
    · dsimp only [pat_138, pat_166, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
    · dsimp only [pat_166, pat_138, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_370_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_138_gen (v3 (vars 0) (vars 1) 1)

private theorem step_pat_370_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_370 vars) (target_pat_370_gen vars) := by
  refine step_chain ?_ (step_pat_138_gen (v3 (vars 0) (vars 1) 1) h_261)
  dsimp only [pat_370, pat_138, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_363_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_370_gen (v2 (vars 0) (vars 1))

private theorem step_pat_363_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_363 vars) (target_pat_363_gen vars) := by
  refine step_chain ?_ (step_pat_370_gen (v2 (vars 0) (vars 1)) h_261)
  dsimp only [pat_363, pat_370, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_356_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_363_gen (v2 (vars 0) (vars 1))

private theorem step_pat_356_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_356 vars) (target_pat_356_gen vars) := by
  refine step_chain ?_ (step_pat_363_gen (v2 (vars 0) (vars 1)) h_261)
  dsimp only [pat_356, pat_363, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_350_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_356_gen (v2 (vars 0) (vars 1))

private theorem step_pat_350_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_350 vars) (target_pat_350_gen vars) := by
  refine step_chain ?_ (step_pat_356_gen (v2 (vars 0) (vars 1)) h_261)
  dsimp only [pat_350, pat_356, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_345_zero (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_350_gen (v2 (vars 0) (vars 1)) | _u + 1 => none

private theorem step_pat_345_zero (vars : Nat → Nat) (h_c : vars 2 = 0) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_345 vars) (target_pat_345_zero vars) := by
  rcases h_vr : vars 2 with _ | u
  · simp -failIfUnchanged only [target_pat_345_zero]; rw [h_vr]
    refine step_chain ?_ (step_pat_350_gen (v2 (vars 0) (vars 1)) h_261)
    dsimp only [pat_345, pat_350, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · omega
private def target_pat_340_zero (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_345_zero (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_340_zero (vars : Nat → Nat) (h_c : vars 2 = 0) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_340 vars) (target_pat_340_zero vars) := by
  refine step_chain ?_ (step_pat_345_zero (v3 (vars 0) (vars 1) (vars 2)) (by var_omega) h_261)
  dsimp only [pat_340, pat_345, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_335_zero (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_340_zero (v3 (vars 0) (vars 1) 0) | _u + 1 => none

private theorem step_pat_335_zero (vars : Nat → Nat) (h_c : vars 2 = 0) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_335 vars) (target_pat_335_zero vars) := by
  rcases h_vr : vars 2 with _ | u
  · simp -failIfUnchanged only [target_pat_335_zero]; rw [h_vr]
    refine step_chain ?_ (step_pat_340_zero (v3 (vars 0) (vars 1) 0) rfl h_261)
    dsimp only [pat_335, pat_340, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · omega
private def target_pat_329_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_333 (v2 (vars 1) 0) | v + 1 => target_pat_335_zero (v3 v (vars 1) 0)

private theorem step_pat_329_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_329 vars) (target_pat_329_gen vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_329_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_333 (v2 (vars 1) 0))
    dsimp only [pat_329, pat_333, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_329_gen]; rw [h_vl]
    refine step_chain ?_ (step_pat_335_zero (v3 v (vars 1) 0) rfl h_261)
    dsimp only [pat_329, pat_335, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_323_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_329_gen (v2 (vars 0) (vars 1))

private theorem step_pat_323_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_323 vars) (target_pat_323_gen vars) := by
  refine step_chain ?_ (step_pat_329_gen (v2 (vars 0) (vars 1)) h_261)
  dsimp only [pat_323, pat_329, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_316_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_323_gen (v2 (vars 0) (vars 1))

private theorem step_pat_316_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_316 vars) (target_pat_316_gen vars) := by
  refine step_chain ?_ (step_pat_323_gen (v2 (vars 0) (vars 1)) h_261)
  dsimp only [pat_316, pat_323, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_305_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_316_gen (v2 (vars 0) (vars 1))

private theorem step_pat_305_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_305 vars) (target_pat_305_gen vars) := by
  refine step_chain ?_ (step_pat_316_gen (v2 (vars 0) (vars 1)) h_261)
  dsimp only [pat_305, pat_316, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_282_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_305_gen (v2 (vars 0) (vars 1))

private theorem step_pat_282_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_282 vars) (target_pat_282_gen vars) := by
  refine step_chain ?_ (step_pat_305_gen (v2 (vars 0) (vars 1)) h_261)
  dsimp only [pat_282, pat_305, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_254_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_282_gen (v2 (vars 0) (vars 1))

private theorem step_pat_254_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_254 vars) (target_pat_254_gen vars) := by
  refine step_chain ?_ (step_pat_282_gen (v2 (vars 0) (vars 1)) h_261)
  dsimp only [pat_254, pat_282, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_234_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_254_gen (v2 (vars 0) (vars 1))

private theorem step_pat_234_gen (vars : Nat → Nat) (h_261 : Reaches261Lt (vars 1)) :
  ReachesTarget ps (evalTapePattern pat_234 vars) (target_pat_234_gen vars) := by
  refine step_chain ?_ (step_pat_254_gen (v2 (vars 0) (vars 1)) h_261)
  dsimp only [pat_234, pat_254, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_215_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_234_gen (v2 1 (vars 0)) | _u + 1 => none

private theorem step_pat_215_gen (vars : Nat → Nat) (h_c : vars 1 = 0) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_215 vars) (target_pat_215_gen vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_215_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_234_gen (v2 1 (vars 0)) h_261)
    dsimp only [pat_215, pat_234, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · omega
private def target_pat_192_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => none | u + 1 => target_pat_215_gen (v2 (vars 0) u)

private theorem step_pat_192_gen (vars : Nat → Nat) (h_c : vars 1 = 1) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_192 vars) (target_pat_192_gen vars) := by
  rcases h_vr : vars 1 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_192_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_215_gen (v2 (vars 0) u) (by var_omega) h_261)
    dsimp only [pat_192, pat_215, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_159_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_192_gen (v2 (vars 0) (vars 1))

private theorem step_pat_159_gen (vars : Nat → Nat) (h_c : vars 1 = 1) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_159 vars) (target_pat_159_gen vars) := by
  refine step_chain ?_ (step_pat_192_gen (v2 (vars 0) (vars 1)) (by var_omega) h_261)
  dsimp only [pat_159, pat_192, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_308_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_234_gen (v2 (vars 0 + 1) (vars 1)) | _u + 1 => none

private theorem step_pat_308_gen (vars : Nat → Nat) (h_c : vars 2 = 0) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_308 vars) (target_pat_308_gen vars) := by
  rcases h_vr : vars 2 with _ | u
  · simp -failIfUnchanged only [target_pat_308_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_234_gen (v2 (vars 0 + 1) (vars 1)) h_261)
    dsimp only [pat_308, pat_234, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · omega
private def target_pat_286_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => none | u + 1 => target_pat_308_gen (v3 (vars 0) (vars 1) u)

private theorem step_pat_286_gen (vars : Nat → Nat) (h_c : vars 2 = 1) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_286 vars) (target_pat_286_gen vars) := by
  rcases h_vr : vars 2 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_286_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_308_gen (v3 (vars 0) (vars 1) u) (by var_omega) h_261)
    dsimp only [pat_286, pat_308, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_258_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_286_gen (v3 1 (vars 0) (vars 1))

private theorem step_pat_258_gen (vars : Nat → Nat) (h_c : vars 1 = 1) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_258 vars) (target_pat_258_gen vars) := by
  refine step_chain ?_ (step_pat_286_gen (v3 1 (vars 0) (vars 1)) (by var_omega) h_261)
  dsimp only [pat_258, pat_286, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_309_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_286_gen (v3 (vars 0 + 1) (vars 1) (vars 2))

private theorem step_pat_309_gen (vars : Nat → Nat) (h_c : vars 2 = 1) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_309 vars) (target_pat_309_gen vars) := by
  refine step_chain ?_ (step_pat_286_gen (v3 (vars 0 + 1) (vars 1) (vars 2)) (by var_omega) h_261)
  dsimp only [pat_309, pat_286, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_287_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_309_gen (v3 (vars 2 + vars 0) (vars 1) (vars 3))

private theorem step_pat_287_gen (vars : Nat → Nat) (h_c : vars 3 = 1) (h_261 : Reaches261Lt (vars
  1)) :
  ReachesTarget ps (evalTapePattern pat_287 vars) (target_pat_287_gen vars) := by
  induction h_vr : vars 2 generalizing vars with
  | zero =>
    have h_eq : target_pat_287_gen vars = target_pat_309_gen (v3 (vars 0) (vars 1) (vars 3)) := by
      simp -failIfUnchanged only [target_pat_287_gen]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_309_gen (v3 (vars 0) (vars 1) (vars 3)) (by var_omega) h_261)
    dsimp only [pat_287, pat_309, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  | succ u ih =>
    have h_eq : target_pat_287_gen vars = target_pat_287_gen
      (v4 (vars 0 + 1) (vars 1) u (vars 3)) := by
      simp -failIfUnchanged only [target_pat_287_gen]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_310 (v4 (vars 0) (vars 1) u (vars 3)))
      ?_ (step_chain ?_ (ih (v4 (vars 0 + 1) (vars 1) u (vars 3)) h_c h_261 rfl))
    · dsimp only [pat_287, pat_310, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
    · dsimp only [pat_310, pat_287, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_259_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_287_gen (v4 1 (vars 0) (vars 1) (vars 2))

private theorem step_pat_259_gen (vars : Nat → Nat) (h_c : vars 2 = 1) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_259 vars) (target_pat_259_gen vars) := by
  refine step_chain ?_ (step_pat_287_gen (v4 1 (vars 0) (vars 1) (vars 2)) (by var_omega) h_261)
  dsimp only [pat_259, pat_287, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_238_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_258_gen (v2 (vars 0) (vars 2)) | u + 1 => target_pat_259_gen
    (v3 (vars 0) u (vars 2))

private theorem step_pat_238_gen (vars : Nat → Nat) (h_c : vars 2 = 1) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_238 vars) (target_pat_238_gen vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_238_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_258_gen (v2 (vars 0) (vars 2)) (by var_omega) h_261)
    dsimp only [pat_238, pat_258, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_238_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_259_gen (v3 (vars 0) u (vars 2)) (by var_omega) h_261)
    dsimp only [pat_238, pat_259, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_219_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_238_gen (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_219_gen (vars : Nat → Nat) (h_c : vars 2 = 1) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_219 vars) (target_pat_219_gen vars) := by
  refine step_chain ?_ (step_pat_238_gen (v3 (vars 0) (vars 1) (vars 2)) (by var_omega) h_261)
  dsimp only [pat_219, pat_238, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_198_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_159_gen (v2 (vars 0) (vars 2)) | u + 1 => target_pat_219_gen
    (v3 (vars 0) u (vars 2))

private theorem step_pat_198_gen (vars : Nat → Nat) (h_c : vars 2 = 1) (h_261 : Reaches261Lt (vars
  0)) :
  ReachesTarget ps (evalTapePattern pat_198 vars) (target_pat_198_gen vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_198_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_159_gen (v2 (vars 0) (vars 2)) (by var_omega) h_261)
    dsimp only [pat_198, pat_159, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_198_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_219_gen (v3 (vars 0) u (vars 2)) (by var_omega) h_261)
    dsimp only [pat_198, pat_219, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_218_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_198_gen (v3 0 (vars 0) (vars 1))

private theorem step_pat_218_gen (vars : Nat → Nat) (h_c : vars 1 = 1) (h_261 : Reaches261Lt 0) :
  ReachesTarget ps (evalTapePattern pat_218 vars) (target_pat_218_gen vars) := by
  refine step_chain ?_ (step_pat_198_gen (v3 0 (vars 0) (vars 1)) (by var_omega) h_261)
  dsimp only [pat_218, pat_198, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_197_gen (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => none | u + 1 => target_pat_218_gen (v2 u (vars 1))

private theorem step_pat_197_gen (vars : Nat → Nat) (h_c0 : vars 0 ≥ 1) (h_c1 : vars 1 = 1) (h_261
  : Reaches261Lt 0) :
  ReachesTarget ps (evalTapePattern pat_197 vars) (target_pat_197_gen vars) := by
  rcases h_vr : vars 0 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_197_gen]; rw [h_vr]
    refine step_chain ?_ (step_pat_218_gen (v2 u (vars 1)) (by var_omega) h_261)
    dsimp only [pat_197, pat_218, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private theorem step_pat_261 (vars : Nat → Nat) (h_c : vars 2 = 1) :
  ReachesTarget ps (evalTapePattern pat_261 vars) (target_pat_261 vars) := by
  induction h_a : vars 0 using Nat.strong_induction_on generalizing vars with
  | h a ih =>
    have h_261 : Reaches261Lt a := by
      intro v hv b
      exact ih v hv (v3 v b 1) rfl rfl
    rcases h_vl : vars 0 with _ | v
    · have h_eq : target_pat_197_gen (v2 (vars 1 + 1) (vars 2)) = target_pat_261 vars := by
        simp -failIfUnchanged only [target_pat_261]; rw [h_vl, h_c]
        rcases vars 1 with _ | _ | b' <;> (congr_cfg pat_61)
      refine cast_target h_eq (step_chain ?_ (step_pat_197_gen
        (v2 (vars 1 + 1) (vars 2)) (by var_omega) (by var_omega) (by intro x hx; omega)))
      dsimp only [pat_261, pat_197, evalTapePattern, evalTapeExpr]; rw [h_vl];
        pat_step
    · have h_261_v : Reaches261Lt v := by
        intro x hx b
        exact h_261 x (by omega) b
      have h_eq : target_pat_198_gen (v3 v (vars 1 + 1) (vars 2)) = target_pat_261 vars := by
        simp -failIfUnchanged only [target_pat_261]; rw [h_vl, h_c]
        rcases v with _ | v' <;> rcases vars 1 with _ | b' <;> (congr_cfg pat_61)
      refine cast_target h_eq (step_chain ?_ (step_pat_198_gen
        (v3 v (vars 1 + 1) (vars 2)) (by var_omega) h_261_v))
      dsimp only [pat_261, pat_198, evalTapePattern, evalTapeExpr]; rw [h_vl];
        pat_step

private theorem all_reaches_261 (N : Nat) : Reaches261Lt N :=
  fun v _ b => step_pat_261 (v3 v b 1) rfl

private def target_pat_137 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_137_gen vars
private theorem step_pat_137 (vars : Nat → Nat) (h_c : vars 0 ≥ 1) : ReachesTarget ps
  (evalTapePattern pat_137 vars) (target_pat_137 vars)
    := step_pat_137_gen vars h_c (all_reaches_261 _)
private def target_pat_165 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_165_gen vars
private theorem step_pat_165 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_165 vars) (target_pat_165 vars) := step_pat_165_gen vars (all_reaches_261 _)
private def target_pat_138 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_138_gen vars
private theorem step_pat_138 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_138 vars) (target_pat_138 vars) := step_pat_138_gen vars (all_reaches_261 _)
private def target_pat_370 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_370_gen vars
private theorem step_pat_370 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_370 vars) (target_pat_370 vars) := step_pat_370_gen vars (all_reaches_261 _)
private def target_pat_363 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_363_gen vars
private theorem step_pat_363 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_363 vars) (target_pat_363 vars) := step_pat_363_gen vars (all_reaches_261 _)
private def target_pat_356 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_356_gen vars
private theorem step_pat_356 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_356 vars) (target_pat_356 vars) := step_pat_356_gen vars (all_reaches_261 _)
private def target_pat_350 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6))
  := target_pat_350_gen vars
private theorem step_pat_350 (vars : Nat → Nat) : ReachesTarget ps
  (evalTapePattern pat_350 vars) (target_pat_350 vars) := step_pat_350_gen vars (all_reaches_261 _)

private def target_pat_115 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_137 (v2 1 (vars 0))

private theorem step_pat_115 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_115 vars) (target_pat_115 vars) := by
  refine step_chain ?_ (step_pat_137 (v2 1 (vars 0)) (by var_omega))
  dsimp only [pat_115, pat_137, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_116 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_138 (v3 1 (vars 0) (vars 1))

private theorem step_pat_116 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_116 vars) (target_pat_116 vars) := by
  refine step_chain ?_ (step_pat_138 (v3 1 (vars 0) (vars 1)))
  dsimp only [pat_116, pat_138, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_102 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_115 (v1 (vars 0)) | u + 1 => target_pat_116 (v2 (vars 0) u)

private theorem step_pat_102 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_102 vars) (target_pat_102 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_102]; rw [h_vr]
    refine step_chain ?_ (step_pat_115 (v1 (vars 0)))
    dsimp only [pat_102, pat_115, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_102]; rw [h_vr]
    refine step_chain ?_ (step_pat_116 (v2 (vars 0) u))
    dsimp only [pat_102, pat_116, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step

private def target_pat_167 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_200 (v2 (vars 0) 0)

private theorem step_pat_167 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_167 vars) (target_pat_167 vars) := by
  refine step_chain ?_ (step_pat_200 (v2 (vars 0) 0))
  dsimp only [pat_167, pat_200, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_139 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_167 (v1 (vars 0 + 2 * vars 1))

private theorem step_pat_139 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_139 vars) (target_pat_139 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    have h_eq : target_pat_139 vars = target_pat_167 (v1 (vars 0)) := by
      simp -failIfUnchanged only [target_pat_139]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_167 (v1 (vars 0)))
    dsimp only [pat_139, pat_167, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  | succ u ih =>
    have h_eq : target_pat_139 vars = target_pat_139 (v2 ((vars 0 + 1) + 1) u) := by
      simp -failIfUnchanged only [target_pat_139]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_168 (v2 (vars 0) u)) ?_
      (step_chain_explicit (evalTapePattern pat_201 (v2 (vars 0) u)) ?_
        (step_chain_explicit (evalTapePattern pat_117 (v2 (vars 0 + 1) u)) ?_
          (step_chain ?_ (ih (v2 ((vars 0 + 1) + 1) u) rfl))))
    · dsimp only [pat_139, pat_168, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
    · dsimp only [pat_168, pat_201, evalTapePattern, evalTapeExpr]; pat_step
    · dsimp only [pat_201, pat_117, evalTapePattern, evalTapeExpr]; pat_step
    · dsimp only [pat_117, pat_139, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_117 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_139 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_117 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_117 vars) (target_pat_117 vars) := by
  refine step_chain ?_ (step_pat_139 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_117, pat_139, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_103 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_117 (v2 0 (vars 0))

private theorem step_pat_103 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_103 vars) (target_pat_103 vars) := by
  refine step_chain ?_ (step_pat_117 (v2 0 (vars 0)))
  dsimp only [pat_103, pat_117, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_140 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  none

private theorem step_pat_140 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_140 vars) (target_pat_140 vars) := by
  refine step_halt (evalTapePattern pat_169 (v1 (vars 0)))
    ?_ (by dsimp only [pat_169, evalTapePattern, evalTapeExpr]; pat_step)
  dsimp only [pat_140, pat_169, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_118 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_140 (v1 (vars 0))

private theorem step_pat_118 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_118 vars) (target_pat_118 vars) := by
  refine step_chain ?_ (step_pat_140 (v1 (vars 0)))
  dsimp only [pat_118, pat_140, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_104 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_118 (v1 (vars 0))

private theorem step_pat_104 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_104 vars) (target_pat_104 vars) := by
  refine step_chain ?_ (step_pat_118 (v1 (vars 0)))
  dsimp only [pat_104, pat_118, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_141 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  none

private theorem step_pat_141 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_141 vars) (target_pat_141 vars) := by
  refine step_halt (evalTapePattern pat_170 (v2 (vars 0) (vars 1)))
    ?_ (by dsimp only [pat_170, evalTapePattern, evalTapeExpr]; pat_step)
  dsimp only [pat_141, pat_170, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_119 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_141 (v2 1 (vars 0))

private theorem step_pat_119 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_119 vars) (target_pat_119 vars) := by
  refine step_chain ?_ (step_pat_141 (v2 1 (vars 0)))
  dsimp only [pat_119, pat_141, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_105 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_119 (v1 (vars 0))

private theorem step_pat_105 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_105 vars) (target_pat_105 vars) := by
  refine step_chain ?_ (step_pat_119 (v1 (vars 0)))
  dsimp only [pat_105, pat_119, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_171 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_141 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_171 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_171 vars) (target_pat_171 vars) := by
  refine step_chain ?_ (step_pat_141 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_171, pat_141, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_142 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_171 (v2 (vars 0) (vars 1))

private theorem step_pat_142 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_142 vars) (target_pat_142 vars) := by
  refine step_chain ?_ (step_pat_171 (v2 (vars 0) (vars 1)))
  dsimp only [pat_142, pat_171, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_120 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_142 (v2 1 (vars 0))

private theorem step_pat_120 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_120 vars) (target_pat_120 vars) := by
  refine step_chain ?_ (step_pat_142 (v2 1 (vars 0)))
  dsimp only [pat_120, pat_142, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_172 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_142 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_172 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_172 vars) (target_pat_172 vars) := by
  refine step_chain ?_ (step_pat_142 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_172, pat_142, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_143 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_172 (v2 (vars 2 + vars 0) (vars 1))

private theorem step_pat_143 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_143 vars) (target_pat_143 vars) := by
  induction h_vr : vars 2 generalizing vars with
  | zero =>
    have h_eq : target_pat_143 vars = target_pat_172 (v2 (vars 0) (vars 1)) := by
      simp -failIfUnchanged only [target_pat_143]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_172 (v2 (vars 0) (vars 1)))
    dsimp only [pat_143, pat_172, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  | succ u ih =>
    have h_eq : target_pat_143 vars = target_pat_143 (v3 (vars 0 + 1) (vars 1) u) := by
      simp -failIfUnchanged only [target_pat_143]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_173 (v3 (vars 0) (vars 1) u)) ?_ (step_chain
      ?_ (ih (v3 (vars 0 + 1) (vars 1) u) rfl))
    · dsimp only [pat_143, pat_173, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
    · dsimp only [pat_173, pat_143, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_121 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_143 (v3 1 (vars 0) (vars 1))

private theorem step_pat_121 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_121 vars) (target_pat_121 vars) := by
  refine step_chain ?_ (step_pat_143 (v3 1 (vars 0) (vars 1)))
  dsimp only [pat_121, pat_143, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_106 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_120 (v1 (vars 0)) | u + 1 => target_pat_121 (v2 (vars 0) u)

private theorem step_pat_106 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_106 vars) (target_pat_106 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_106]; rw [h_vr]
    refine step_chain ?_ (step_pat_120 (v1 (vars 0)))
    dsimp only [pat_106, pat_120, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_106]; rw [h_vr]
    refine step_chain ?_ (step_pat_121 (v2 (vars 0) u))
    dsimp only [pat_106, pat_121, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_174 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_200 (v2 (vars 0) (vars 1 + 1))

private theorem step_pat_174 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_174 vars) (target_pat_174 vars) := by
  refine step_chain ?_ (step_pat_200 (v2 (vars 0) (vars 1 + 1)))
  dsimp only [pat_174, pat_200, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_144 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_174 (v2 (vars 0 + 2 * vars 1) (vars 2))

private theorem step_pat_144 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_144 vars) (target_pat_144 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    have h_eq : target_pat_144 vars = target_pat_174 (v2 (vars 0) (vars 2)) := by
      simp -failIfUnchanged only [target_pat_144]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_174 (v2 (vars 0) (vars 2)))
    dsimp only [pat_144, pat_174, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  | succ u ih =>
    have h_eq : target_pat_144 vars = target_pat_144 (v3 ((vars 0 + 1) + 1) u (vars 2)) := by
      simp -failIfUnchanged only [target_pat_144]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_175 (v3 (vars 0) u (vars 2))) ?_
      (step_chain_explicit (evalTapePattern pat_202 (v3 (vars 0) u (vars 2))) ?_
        (step_chain_explicit (evalTapePattern pat_122 (v3 (vars 0 + 1) u (vars 2))) ?_
          (step_chain ?_ (ih (v3 ((vars 0 + 1) + 1) u (vars 2)) rfl))))
    · dsimp only [pat_144, pat_175, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
    · dsimp only [pat_175, pat_202, evalTapePattern, evalTapeExpr]; pat_step
    · dsimp only [pat_202, pat_122, evalTapePattern, evalTapeExpr]; pat_step
    · dsimp only [pat_122, pat_144, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_122 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_144 (v3 (vars 0 + 1) (vars 1) (vars 2))

private theorem step_pat_122 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_122 vars) (target_pat_122 vars) := by
  refine step_chain ?_ (step_pat_144 (v3 (vars 0 + 1) (vars 1) (vars 2)))
  dsimp only [pat_122, pat_144, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_107 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_122 (v3 0 (vars 0) (vars 1))

private theorem step_pat_107 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_107 vars) (target_pat_107 vars) := by
  refine step_chain ?_ (step_pat_122 (v3 0 (vars 0) (vars 1)))
  dsimp only [pat_107, pat_122, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_362 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_333 (v2 (vars 0) 1) | u + 1 => target_pat_333 (v2 (vars 0) ((u + 1) + 1))

private theorem step_pat_362 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_362 vars) (target_pat_362 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_362]; rw [h_vr]
    refine step_chain ?_ (step_pat_333 (v2 (vars 0) 1))
    dsimp only [pat_362, pat_333, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_362]; rw [h_vr]
    refine step_chain ?_ (step_pat_333 (v2 (vars 0) ((u + 1) + 1)))
    dsimp only [pat_362, pat_333, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_355 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_362 (v2 (vars 0) 1) | u + 1 => target_pat_362 (v2 (vars 0) ((u + 1) + 1))

private theorem step_pat_355 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_355 vars) (target_pat_355 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_355]; rw [h_vr]
    refine step_chain ?_ (step_pat_362 (v2 (vars 0) 1))
    dsimp only [pat_355, pat_362, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_355]; rw [h_vr]
    refine step_chain ?_ (step_pat_362 (v2 (vars 0) ((u + 1) + 1)))
    dsimp only [pat_355, pat_362, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_368 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_355 (v2 (vars 0) 1) | u + 1 => target_pat_355 (v2 (vars 0) ((u + 1) + 1))

private theorem step_pat_368 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_368 vars) (target_pat_368 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_368]; rw [h_vr]
    refine step_chain ?_ (step_pat_355 (v2 (vars 0) 1))
    dsimp only [pat_368, pat_355, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_368]; rw [h_vr]
    refine step_chain ?_ (step_pat_355 (v2 (vars 0) ((u + 1) + 1)))
    dsimp only [pat_368, pat_355, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_360 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_368 (v2 (vars 0) 1) | u + 1 => target_pat_368 (v2 (vars 0) ((u + 1) + 1))

private theorem step_pat_360 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_360 vars) (target_pat_360 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_360]; rw [h_vr]
    refine step_chain ?_ (step_pat_368 (v2 (vars 0) 1))
    dsimp only [pat_360, pat_368, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_360]; rw [h_vr]
    refine step_chain ?_ (step_pat_368 (v2 (vars 0) ((u + 1) + 1)))
    dsimp only [pat_360, pat_368, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_353 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_360 (v2 (vars 0) 0)

private theorem step_pat_353 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_353 vars) (target_pat_353 vars) := by
  refine step_chain ?_ (step_pat_360 (v2 (vars 0) 0))
  dsimp only [pat_353, pat_360, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_347 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_353 (v1 (vars 0))

private theorem step_pat_347 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_347 vars) (target_pat_347 vars) := by
  refine step_chain ?_ (step_pat_353 (v1 (vars 0)))
  dsimp only [pat_347, pat_353, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_342 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_347 (v1 (vars 0))

private theorem step_pat_342 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_342 vars) (target_pat_342 vars) := by
  refine step_chain ?_ (step_pat_347 (v1 (vars 0)))
  dsimp only [pat_342, pat_347, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_337 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_342 (v1 (vars 0))

private theorem step_pat_337 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_337 vars) (target_pat_337 vars) := by
  refine step_chain ?_ (step_pat_342 (v1 (vars 0)))
  dsimp only [pat_337, pat_342, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_331 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_337 (v1 (vars 0))

private theorem step_pat_331 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_331 vars) (target_pat_331 vars) := by
  refine step_chain ?_ (step_pat_337 (v1 (vars 0)))
  dsimp only [pat_331, pat_337, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_325 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_331 (v1 (vars 0))

private theorem step_pat_325 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_325 vars) (target_pat_325 vars) := by
  refine step_chain ?_ (step_pat_331 (v1 (vars 0)))
  dsimp only [pat_325, pat_331, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_319 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_325 (v1 (vars 0))

private theorem step_pat_319 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_319 vars) (target_pat_319 vars) := by
  refine step_chain ?_ (step_pat_325 (v1 (vars 0)))
  dsimp only [pat_319, pat_325, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_311 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_319 (v1 (vars 0))

private theorem step_pat_311 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_311 vars) (target_pat_311 vars) := by
  refine step_chain ?_ (step_pat_319 (v1 (vars 0)))
  dsimp only [pat_311, pat_319, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_291 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_311 (v1 (vars 0))

private theorem step_pat_291 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_291 vars) (target_pat_291 vars) := by
  refine step_chain ?_ (step_pat_311 (v1 (vars 0)))
  dsimp only [pat_291, pat_311, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_264 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_291 (v1 (vars 0))

private theorem step_pat_264 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_264 vars) (target_pat_264 vars) := by
  refine step_chain ?_ (step_pat_291 (v1 (vars 0)))
  dsimp only [pat_264, pat_291, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_241 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_264 (v1 (vars 0))

private theorem step_pat_241 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_241 vars) (target_pat_241 vars) := by
  refine step_chain ?_ (step_pat_264 (v1 (vars 0)))
  dsimp only [pat_241, pat_264, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_222 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_241 (v1 (vars 0))

private theorem step_pat_222 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_222 vars) (target_pat_222 vars) := by
  refine step_chain ?_ (step_pat_241 (v1 (vars 0)))
  dsimp only [pat_222, pat_241, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_203 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_222 (v1 (vars 0))

private theorem step_pat_203 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_203 vars) (target_pat_203 vars) := by
  refine step_chain ?_ (step_pat_222 (v1 (vars 0)))
  dsimp only [pat_203, pat_222, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_176 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_203 (v1 (vars 0))

private theorem step_pat_176 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_176 vars) (target_pat_176 vars) := by
  refine step_chain ?_ (step_pat_203 (v1 (vars 0)))
  dsimp only [pat_176, pat_203, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_145 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_176 (v1 (vars 0))

private theorem step_pat_145 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_145 vars) (target_pat_145 vars) := by
  refine step_chain ?_ (step_pat_176 (v1 (vars 0)))
  dsimp only [pat_145, pat_176, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_123 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_145 (v1 (vars 0))

private theorem step_pat_123 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_123 vars) (target_pat_123 vars) := by
  refine step_chain ?_ (step_pat_145 (v1 (vars 0)))
  dsimp only [pat_123, pat_145, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_230 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  none

private theorem step_pat_230 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_230 vars) (target_pat_230 vars) := by
  refine step_halt (evalTapePattern pat_249 (v1 (vars 0)))
    ?_ (by dsimp only [pat_249, evalTapePattern, evalTapeExpr]; pat_step)
  dsimp only [pat_230, pat_249, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_212 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_230 (v1 (vars 0 + 1))

private theorem step_pat_212 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_212 vars) (target_pat_212 vars) := by
  refine step_chain ?_ (step_pat_230 (v1 (vars 0 + 1)))
  dsimp only [pat_212, pat_230, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_187 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_212 (v1 (vars 0 + 1))

private theorem step_pat_187 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_187 vars) (target_pat_187 vars) := by
  refine step_chain ?_ (step_pat_212 (v1 (vars 0 + 1)))
  dsimp only [pat_187, pat_212, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_153 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_187 (v1 (vars 0))

private theorem step_pat_153 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_153 vars) (target_pat_153 vars) := by
  refine step_chain ?_ (step_pat_187 (v1 (vars 0)))
  dsimp only [pat_153, pat_187, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_129 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_153 (v1 (vars 0 + 2 * vars 1))

private theorem step_pat_129 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_129 vars) (target_pat_129 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    have h_eq : target_pat_129 vars = target_pat_153 (v1 (vars 0)) := by
      simp -failIfUnchanged only [target_pat_129]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_153 (v1 (vars 0)))
    dsimp only [pat_129, pat_153, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  | succ u ih =>
    have h_eq : target_pat_129 vars = target_pat_129 (v2 ((vars 0 + 1) + 1) u) := by
      simp -failIfUnchanged only [target_pat_129]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_154 (v2 (vars 0) u)) ?_
      (step_chain_explicit (evalTapePattern pat_188 (v2 (vars 0) u)) ?_
        (step_chain_explicit (evalTapePattern pat_111 (v2 (vars 0 + 1) u)) ?_
          (step_chain ?_ (ih (v2 ((vars 0 + 1) + 1) u) rfl))))
    · dsimp only [pat_129, pat_154, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
    · dsimp only [pat_154, pat_188, evalTapePattern, evalTapeExpr]; pat_step
    · dsimp only [pat_188, pat_111, evalTapePattern, evalTapeExpr]; pat_step
    · dsimp only [pat_111, pat_129, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_111 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_129 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_111 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_111 vars) (target_pat_111 vars) := by
  refine step_chain ?_ (step_pat_129 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_111, pat_129, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_99 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_111 (v2 0 (vars 0))

private theorem step_pat_99 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_99 vars) (target_pat_99 vars) := by
  refine step_chain ?_ (step_pat_111 (v2 0 (vars 0)))
  dsimp only [pat_99, pat_111, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_84 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_99 (v1 (vars 0))

private theorem step_pat_84 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_84 vars) (target_pat_84 vars) := by
  refine step_chain ?_ (step_pat_99 (v1 (vars 0)))
  dsimp only [pat_84, pat_99, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_292 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_84 (v1 (vars 0 + 1))

private theorem step_pat_292 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_292 vars) (target_pat_292 vars) := by
  refine step_chain ?_ (step_pat_84 (v1 (vars 0 + 1)))
  dsimp only [pat_292, pat_84, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_265 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_292 (v1 (vars 0))

private theorem step_pat_265 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_265 vars) (target_pat_265 vars) := by
  refine step_chain ?_ (step_pat_292 (v1 (vars 0)))
  dsimp only [pat_265, pat_292, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_85 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_100 (fun _ => 0)

private theorem step_pat_85 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_85 vars) (target_pat_85 vars) := by
  refine step_chain ?_ step_pat_100
  dsimp only [pat_85, pat_100, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_87 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_101 (v1 (vars 0))

private theorem step_pat_87 (vars : Nat → Nat) (h_c : vars 0 = 0) :
  ReachesTarget ps (evalTapePattern pat_87 vars) (target_pat_87 vars) := by
  refine step_chain ?_ (step_pat_101 (v1 (vars 0)) (by var_omega))
  dsimp only [pat_87, pat_101, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_88 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_102 (v2 (vars 0) (vars 1))

private theorem step_pat_88 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_88 vars) (target_pat_88 vars) := by
  refine step_chain ?_ (step_pat_102 (v2 (vars 0) (vars 1)))
  dsimp only [pat_88, pat_102, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_77 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_87 (v1 (vars 0)) | u + 1 => target_pat_88 (v2 (vars 0) u)

private theorem step_pat_77 (vars : Nat → Nat) (h_c : vars 0 = 0 ∨ vars 1 ≥ 1) :
  ReachesTarget ps (evalTapePattern pat_77 vars) (target_pat_77 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_77]; rw [h_vr]
    refine step_chain ?_ (step_pat_87 (v1 (vars 0)) (by var_omega))
    dsimp only [pat_77, pat_87, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_77]; rw [h_vr]
    refine step_chain ?_ (step_pat_88 (v2 (vars 0) u))
    dsimp only [pat_77, pat_88, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_86 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_77 (v2 0 (vars 0))

private theorem step_pat_86 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_86 vars) (target_pat_86 vars) := by
  refine step_chain ?_ (step_pat_77 (v2 0 (vars 0)) (Or.inl rfl))
  dsimp only [pat_86, pat_77, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_76 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_85 (fun _ => 0) | u + 1 => target_pat_86 (v1 u)

private theorem step_pat_76 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_76 vars) (target_pat_76 vars) := by
  rcases h_vr : vars 0 with _ | u
  · simp -failIfUnchanged only [target_pat_76]; rw [h_vr]
    refine step_chain ?_ (step_pat_85 (fun _ => 0))
    dsimp only [pat_76, pat_85, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_76]; rw [h_vr]
    refine step_chain ?_ (step_pat_86 (v1 u))
    dsimp only [pat_76, pat_86, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_266 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_76 (v1 (vars 1 + 1)) | v + 1 => target_pat_77 (v2 v (vars 1 + 1))

private theorem step_pat_266 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_266 vars) (target_pat_266 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_266]; rw [h_vl]
    refine step_chain ?_ (step_pat_76 (v1 (vars 1 + 1)))
    dsimp only [pat_266, pat_76, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_266]; rw [h_vl]
    refine step_chain ?_ (step_pat_77 (v2 v (vars 1 + 1)) (by var_omega))
    dsimp only [pat_266, pat_77, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step

private def target_pat_242 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_265 (v1 1) | v + 1 => target_pat_266 (v2 v 1)

private theorem step_pat_242 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_242 vars) (target_pat_242 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_242]; rw [h_vl]
    refine step_chain ?_ (step_pat_265 (v1 1))
    dsimp only [pat_242, pat_265, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_242]; rw [h_vl]
    refine step_chain ?_ (step_pat_266 (v2 v 1))
    dsimp only [pat_242, pat_266, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_223 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_242 (v1 (vars 0))

private theorem step_pat_223 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_223 vars) (target_pat_223 vars) := by
  refine step_chain ?_ (step_pat_242 (v1 (vars 0)))
  dsimp only [pat_223, pat_242, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_204 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_223 (v1 (vars 0))

private theorem step_pat_204 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_204 vars) (target_pat_204 vars) := by
  refine step_chain ?_ (step_pat_223 (v1 (vars 0)))
  dsimp only [pat_204, pat_223, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_177 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_204 (v1 (vars 0))

private theorem step_pat_177 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_177 vars) (target_pat_177 vars) := by
  refine step_chain ?_ (step_pat_204 (v1 (vars 0)))
  dsimp only [pat_177, pat_204, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_146 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_177 (v1 (vars 0))

private theorem step_pat_146 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_146 vars) (target_pat_146 vars) := by
  refine step_chain ?_ (step_pat_177 (v1 (vars 0)))
  dsimp only [pat_146, pat_177, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_205 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_44 (v2 (vars 0) 1)

private theorem step_pat_205 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_205 vars) (target_pat_205 vars) := by
  refine step_chain ?_ (step_pat_44 (v2 (vars 0) 1))
  dsimp only [pat_205, pat_44, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_178 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_205 (v1 (vars 0))

private theorem step_pat_178 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_178 vars) (target_pat_178 vars) := by
  refine step_chain ?_ (step_pat_205 (v1 (vars 0)))
  dsimp only [pat_178, pat_205, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_89 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_103 (v1 (vars 0))

private theorem step_pat_89 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_89 vars) (target_pat_89 vars) := by
  refine step_chain ?_ (step_pat_103 (v1 (vars 0)))
  dsimp only [pat_89, pat_103, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_293 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_89 (v1 (vars 0 + 1))

private theorem step_pat_293 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_293 vars) (target_pat_293 vars) := by
  refine step_chain ?_ (step_pat_89 (v1 (vars 0 + 1)))
  dsimp only [pat_293, pat_89, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_267 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_293 (v1 (vars 0))

private theorem step_pat_267 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_267 vars) (target_pat_267 vars) := by
  refine step_chain ?_ (step_pat_293 (v1 (vars 0)))
  dsimp only [pat_267, pat_293, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_90 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_104 (v1 0)

private theorem step_pat_90 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_90 vars) (target_pat_90 vars) := by
  refine step_chain ?_ (step_pat_104 (v1 0))
  dsimp only [pat_90, pat_104, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_92 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_105 (v1 (vars 0))

private theorem step_pat_92 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_92 vars) (target_pat_92 vars) := by
  refine step_chain ?_ (step_pat_105 (v1 (vars 0)))
  dsimp only [pat_92, pat_105, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_93 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_106 (v2 (vars 0) (vars 1))

private theorem step_pat_93 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_93 vars) (target_pat_93 vars) := by
  refine step_chain ?_ (step_pat_106 (v2 (vars 0) (vars 1)))
  dsimp only [pat_93, pat_106, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_80 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_92 (v1 (vars 0)) | u + 1 => target_pat_93 (v2 (vars 0) u)

private theorem step_pat_80 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_80 vars) (target_pat_80 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_80]; rw [h_vr]
    refine step_chain ?_ (step_pat_92 (v1 (vars 0)))
    dsimp only [pat_80, pat_92, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_80]; rw [h_vr]
    refine step_chain ?_ (step_pat_93 (v2 (vars 0) u))
    dsimp only [pat_80, pat_93, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_91 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_80 (v2 0 (vars 0))

private theorem step_pat_91 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_91 vars) (target_pat_91 vars) := by
  refine step_chain ?_ (step_pat_80 (v2 0 (vars 0)))
  dsimp only [pat_91, pat_80, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_79 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_90 (fun _ => 0) | u + 1 => target_pat_91 (v1 u)

private theorem step_pat_79 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_79 vars) (target_pat_79 vars) := by
  rcases h_vr : vars 0 with _ | u
  · simp -failIfUnchanged only [target_pat_79]; rw [h_vr]
    refine step_chain ?_ (step_pat_90 (fun _ => 0))
    dsimp only [pat_79, pat_90, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_79]; rw [h_vr]
    refine step_chain ?_ (step_pat_91 (v1 u))
    dsimp only [pat_79, pat_91, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_268 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_79 (v1 (vars 1 + 1)) | v + 1 => target_pat_80 (v2 v (vars 1 + 1))

private theorem step_pat_268 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_268 vars) (target_pat_268 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_268]; rw [h_vl]
    refine step_chain ?_ (step_pat_79 (v1 (vars 1 + 1)))
    dsimp only [pat_268, pat_79, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_268]; rw [h_vl]
    refine step_chain ?_ (step_pat_80 (v2 v (vars 1 + 1)))
    dsimp only [pat_268, pat_80, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_243 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_267 (v1 1) | v + 1 => target_pat_268 (v2 v 1)

private theorem step_pat_243 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_243 vars) (target_pat_243 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_243]; rw [h_vl]
    refine step_chain ?_ (step_pat_267 (v1 1))
    dsimp only [pat_243, pat_267, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_243]; rw [h_vl]
    refine step_chain ?_ (step_pat_268 (v2 v 1))
    dsimp only [pat_243, pat_268, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_224 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_243 (v1 (vars 0))

private theorem step_pat_224 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_224 vars) (target_pat_224 vars) := by
  refine step_chain ?_ (step_pat_243 (v1 (vars 0)))
  dsimp only [pat_224, pat_243, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_206 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_224 (v1 (vars 0))

private theorem step_pat_206 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_206 vars) (target_pat_206 vars) := by
  refine step_chain ?_ (step_pat_224 (v1 (vars 0)))
  dsimp only [pat_206, pat_224, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_94 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_107 (v2 (vars 0) (vars 1))

private theorem step_pat_94 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_94 vars) (target_pat_94 vars) := by
  refine step_chain ?_ (step_pat_107 (v2 (vars 0) (vars 1)))
  dsimp only [pat_94, pat_107, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_294 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_94 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_294 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_294 vars) (target_pat_294 vars) := by
  refine step_chain ?_ (step_pat_94 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_294, pat_94, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_269 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_294 (v2 (vars 0) (vars 1))

private theorem step_pat_269 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_269 vars) (target_pat_269 vars) := by
  refine step_chain ?_ (step_pat_294 (v2 (vars 0) (vars 1)))
  dsimp only [pat_269, pat_294, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_244 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_269 (v2 1 (vars 1)) | v + 1 => some (evalTapePattern pat_270 (v3 v 1 (vars 1)))

private theorem step_pat_244 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_244 vars) (target_pat_244 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_244]; rw [h_vl]
    refine step_chain ?_ (step_pat_269 (v2 1 (vars 1)))
    dsimp only [pat_244, pat_269, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_244]; rw [h_vl]
    refine step_base ?_ (in_ps_270 (v3 v 1 (vars 1)))
    dsimp only [pat_244, pat_270, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_225 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_244 (v2 (vars 0) (vars 1))

private theorem step_pat_225 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_225 vars) (target_pat_225 vars) := by
  refine step_chain ?_ (step_pat_244 (v2 (vars 0) (vars 1)))
  dsimp only [pat_225, pat_244, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_207 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_225 (v2 (vars 0) (vars 1))

private theorem step_pat_207 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_207 vars) (target_pat_207 vars) := by
  refine step_chain ?_ (step_pat_225 (v2 (vars 0) (vars 1)))
  dsimp only [pat_207, pat_225, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_179 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_206 (v1 (vars 0)) | u + 1 => target_pat_207 (v2 (vars 0) u)

private theorem step_pat_179 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_179 vars) (target_pat_179 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_179]; rw [h_vr]
    refine step_chain ?_ (step_pat_206 (v1 (vars 0)))
    dsimp only [pat_179, pat_206, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_179]; rw [h_vr]
    refine step_chain ?_ (step_pat_207 (v2 (vars 0) u))
    dsimp only [pat_179, pat_207, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_147 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_178 (v1 (vars 0)) | u + 1 => target_pat_179 (v2 (vars 0) u)

private theorem step_pat_147 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_147 vars) (target_pat_147 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_147]; rw [h_vr]
    refine step_chain ?_ (step_pat_178 (v1 (vars 0)))
    dsimp only [pat_147, pat_178, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_147]; rw [h_vr]
    refine step_chain ?_ (step_pat_179 (v2 (vars 0) u))
    dsimp only [pat_147, pat_179, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_124 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_146 (v1 (vars 0)) | u + 1 => target_pat_147 (v2 (vars 0) u)

private theorem step_pat_124 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_124 vars) (target_pat_124 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_124]; rw [h_vr]
    refine step_chain ?_ (step_pat_146 (v1 (vars 0)))
    dsimp only [pat_124, pat_146, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_124]; rw [h_vr]
    refine step_chain ?_ (step_pat_147 (v2 (vars 0) u))
    dsimp only [pat_124, pat_147, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_108 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_123 (v1 (vars 0)) | u + 1 => target_pat_124 (v2 (vars 0) u)

private theorem step_pat_108 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_108 vars) (target_pat_108 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_108]; rw [h_vr]
    refine step_chain ?_ (step_pat_123 (v1 (vars 0)))
    dsimp only [pat_108, pat_123, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_108]; rw [h_vr]
    refine step_chain ?_ (step_pat_124 (v2 (vars 0) u))
    dsimp only [pat_108, pat_124, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_296 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_265 (v1 (vars 1 + 1)) | v + 1 => target_pat_266 (v2 v (vars 1 + 1))

private theorem step_pat_296 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_296 vars) (target_pat_296 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_296]; rw [h_vl]
    refine step_chain ?_ (step_pat_265 (v1 (vars 1 + 1)))
    dsimp only [pat_296, pat_265, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_296]; rw [h_vl]
    refine step_chain ?_ (step_pat_266 (v2 v (vars 1 + 1)))
    dsimp only [pat_296, pat_266, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_272 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_296 (v2 (vars 0) (vars 1))

private theorem step_pat_272 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_272 vars) (target_pat_272 vars) := by
  refine step_chain ?_ (step_pat_296 (v2 (vars 0) (vars 1)))
  dsimp only [pat_272, pat_296, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_297 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_272 (v2 (vars 1) (vars 0 + vars 2 + 1))

private theorem step_pat_297 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_297 vars) (target_pat_297 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    have h_eq : target_pat_297 vars = target_pat_272 (v2 (vars 1) (vars 2 + 1)) := by
      simp -failIfUnchanged only [target_pat_297]; rw [h_vl]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_272 (v2 (vars 1) (vars 2 + 1)))
    dsimp only [pat_297, pat_272, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  | succ v ih =>
    have h_eq : target_pat_297 vars = target_pat_297 (v3 v (vars 1) (vars 2 + 1)) := by
      simp -failIfUnchanged only [target_pat_297]; rw [h_vl]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_273 (v3 v (vars 1) (vars 2 + 1))) ?_
      (step_chain ?_ (ih (v3 v (vars 1) (vars 2 + 1)) rfl))
    · dsimp only [pat_297, pat_273, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
    · dsimp only [pat_273, pat_297, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_273 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_297 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_273 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_273 vars) (target_pat_273 vars) := by
  refine step_chain ?_ (step_pat_297 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_273, pat_297, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_246 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_272 (v2 (vars 1) 1) | v + 1 => target_pat_273 (v3 v (vars 1) 1)

private theorem step_pat_246 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_246 vars) (target_pat_246 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_246]; rw [h_vl]
    refine step_chain ?_ (step_pat_272 (v2 (vars 1) 1))
    dsimp only [pat_246, pat_272, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_246]; rw [h_vl]
    refine step_chain ?_ (step_pat_273 (v3 v (vars 1) 1))
    dsimp only [pat_246, pat_273, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_227 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_246 (v2 (vars 0) (vars 1))

private theorem step_pat_227 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_227 vars) (target_pat_227 vars) := by
  refine step_chain ?_ (step_pat_246 (v2 (vars 0) (vars 1)))
  dsimp only [pat_227, pat_246, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_209 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_223 (v1 (vars 1)) | v + 1 => target_pat_227 (v2 v (vars 1))

private theorem step_pat_209 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_209 vars) (target_pat_209 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_209]; rw [h_vl]
    refine step_chain ?_ (step_pat_223 (v1 (vars 1)))
    dsimp only [pat_209, pat_223, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_209]; rw [h_vl]
    refine step_chain ?_ (step_pat_227 (v2 v (vars 1)))
    dsimp only [pat_209, pat_227, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_181 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_209 (v2 (vars 0) (vars 1))

private theorem step_pat_181 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_181 vars) (target_pat_181 vars) := by
  refine step_chain ?_ (step_pat_209 (v2 (vars 0) (vars 1)))
  dsimp only [pat_181, pat_209, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_149 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_181 (v2 (vars 0) (vars 1))

private theorem step_pat_149 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_149 vars) (target_pat_149 vars) := by
  refine step_chain ?_ (step_pat_181 (v2 (vars 0) (vars 1)))
  dsimp only [pat_149, pat_181, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_298 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_267 (v1 (vars 1 + 1)) | v + 1 => target_pat_268 (v2 v (vars 1 + 1))

private theorem step_pat_298 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_298 vars) (target_pat_298 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_298]; rw [h_vl]
    refine step_chain ?_ (step_pat_267 (v1 (vars 1 + 1)))
    dsimp only [pat_298, pat_267, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_298]; rw [h_vl]
    refine step_chain ?_ (step_pat_268 (v2 v (vars 1 + 1)))
    dsimp only [pat_298, pat_268, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_274 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_298 (v2 (vars 0) (vars 1))

private theorem step_pat_274 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_274 vars) (target_pat_274 vars) := by
  refine step_chain ?_ (step_pat_298 (v2 (vars 0) (vars 1)))
  dsimp only [pat_274, pat_298, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_299 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_274 (v2 (vars 1) (vars 0 + vars 2 + 1))

private theorem step_pat_299 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_299 vars) (target_pat_299 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    have h_eq : target_pat_299 vars = target_pat_274 (v2 (vars 1) (vars 2 + 1)) := by
      simp -failIfUnchanged only [target_pat_299]; rw [h_vl]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_274 (v2 (vars 1) (vars 2 + 1)))
    dsimp only [pat_299, pat_274, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  | succ v ih =>
    have h_eq : target_pat_299 vars = target_pat_299 (v3 v (vars 1) (vars 2 + 1)) := by
      simp -failIfUnchanged only [target_pat_299]; rw [h_vl]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_275 (v3 v (vars 1) (vars 2 + 1))) ?_
      (step_chain ?_ (ih (v3 v (vars 1) (vars 2 + 1)) rfl))
    · dsimp only [pat_299, pat_275, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
    · dsimp only [pat_275, pat_299, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_275 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_299 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_275 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_275 vars) (target_pat_275 vars) := by
  refine step_chain ?_ (step_pat_299 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_275, pat_299, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_247 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_274 (v2 (vars 1) 1) | v + 1 => target_pat_275 (v3 v (vars 1) 1)

private theorem step_pat_247 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_247 vars) (target_pat_247 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_247]; rw [h_vl]
    refine step_chain ?_ (step_pat_274 (v2 (vars 1) 1))
    dsimp only [pat_247, pat_274, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_247]; rw [h_vl]
    refine step_chain ?_ (step_pat_275 (v3 v (vars 1) 1))
    dsimp only [pat_247, pat_275, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_228 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_247 (v2 (vars 0) (vars 1))

private theorem step_pat_228 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_228 vars) (target_pat_228 vars) := by
  refine step_chain ?_ (step_pat_247 (v2 (vars 0) (vars 1)))
  dsimp only [pat_228, pat_247, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_210 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_224 (v1 (vars 1)) | v + 1 => target_pat_228 (v2 v (vars 1))

private theorem step_pat_210 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_210 vars) (target_pat_210 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_210]; rw [h_vl]
    refine step_chain ?_ (step_pat_224 (v1 (vars 1)))
    dsimp only [pat_210, pat_224, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_210]; rw [h_vl]
    refine step_chain ?_ (step_pat_228 (v2 v (vars 1)))
    dsimp only [pat_210, pat_228, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_300 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_269 (v2 (vars 1 + 1) (vars 2)) | v + 1 => some (evalTapePattern pat_270
    (v3 v (vars 1 + 1) (vars 2)))

private theorem step_pat_300 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_300 vars) (target_pat_300 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_300]; rw [h_vl]
    refine step_chain ?_ (step_pat_269 (v2 (vars 1 + 1) (vars 2)))
    dsimp only [pat_300, pat_269, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_300]; rw [h_vl]
    refine step_base ?_ (in_ps_270 (v3 v (vars 1 + 1) (vars 2)))
    dsimp only [pat_300, pat_270, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_276 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_300 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_276 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_276 vars) (target_pat_276 vars) := by
  refine step_chain ?_ (step_pat_300 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_276, pat_300, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_301 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_276 (v3 (vars 1) (vars 0 + vars 2 + 1) (vars 3))

private theorem step_pat_301 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_301 vars) (target_pat_301 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    have h_eq : target_pat_301 vars = target_pat_276 (v3 (vars 1) (vars 2 + 1) (vars 3)) := by
      simp -failIfUnchanged only [target_pat_301]; rw [h_vl]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_276 (v3 (vars 1) (vars 2 + 1) (vars 3)))
    dsimp only [pat_301, pat_276, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  | succ v ih =>
    have h_eq : target_pat_301 vars = target_pat_301 (v4 v (vars 1) (vars 2 + 1) (vars 3)) := by
      simp -failIfUnchanged only [target_pat_301]; rw [h_vl]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_277 (v4 v (vars 1) (vars 2 + 1) (vars 3)))
      ?_ (step_chain ?_ (ih (v4 v (vars 1) (vars 2 + 1) (vars 3)) rfl))
    · dsimp only [pat_301, pat_277, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
    · dsimp only [pat_277, pat_301, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_277 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_301 (v4 (vars 0) (vars 1) (vars 2) (vars 3))

private theorem step_pat_277 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_277 vars) (target_pat_277 vars) := by
  refine step_chain ?_ (step_pat_301 (v4 (vars 0) (vars 1) (vars 2) (vars 3)))
  dsimp only [pat_277, pat_301, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_248 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_276 (v3 (vars 1) 1 (vars 2)) | v + 1 => target_pat_277
    (v4 v (vars 1) 1 (vars 2))

private theorem step_pat_248 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_248 vars) (target_pat_248 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_248]; rw [h_vl]
    refine step_chain ?_ (step_pat_276 (v3 (vars 1) 1 (vars 2)))
    dsimp only [pat_248, pat_276, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_248]; rw [h_vl]
    refine step_chain ?_ (step_pat_277 (v4 v (vars 1) 1 (vars 2)))
    dsimp only [pat_248, pat_277, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_229 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_248 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_229 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_229 vars) (target_pat_229 vars) := by
  refine step_chain ?_ (step_pat_248 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_229, pat_248, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_211 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_225 (v2 (vars 1) (vars 2)) | v + 1 => target_pat_229 (v3 v (vars 1) (vars 2))

private theorem step_pat_211 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_211 vars) (target_pat_211 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_211]; rw [h_vl]
    refine step_chain ?_ (step_pat_225 (v2 (vars 1) (vars 2)))
    dsimp only [pat_211, pat_225, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
  · simp -failIfUnchanged only [target_pat_211]; rw [h_vl]
    refine step_chain ?_ (step_pat_229 (v3 v (vars 1) (vars 2)))
    dsimp only [pat_211, pat_229, evalTapePattern, evalTapeExpr]; rw [h_vl];
      pat_step
private def target_pat_182 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_210 (v2 (vars 0) (vars 1)) | u + 1 => target_pat_211 (v3 (vars 0) (vars 1) u)

private theorem step_pat_182 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_182 vars) (target_pat_182 vars) := by
  rcases h_vr : vars 2 with _ | u
  · simp -failIfUnchanged only [target_pat_182]; rw [h_vr]
    refine step_chain ?_ (step_pat_210 (v2 (vars 0) (vars 1)))
    dsimp only [pat_182, pat_210, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_182]; rw [h_vr]
    refine step_chain ?_ (step_pat_211 (v3 (vars 0) (vars 1) u))
    dsimp only [pat_182, pat_211, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_150 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_37 (v2 (vars 0) (vars 1)) | u + 1 => target_pat_182 (v3 (vars 0) (vars 1) u)

private theorem step_pat_150 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_150 vars) (target_pat_150 vars) := by
  rcases h_vr : vars 2 with _ | u
  · simp -failIfUnchanged only [target_pat_150]; rw [h_vr]
    refine step_chain ?_ (step_pat_37 (v2 (vars 0) (vars 1)))
    dsimp only [pat_150, pat_37, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_150]; rw [h_vr]
    refine step_chain ?_ (step_pat_182 (v3 (vars 0) (vars 1) u))
    dsimp only [pat_150, pat_182, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_126 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_149 (v2 1 (vars 0)) | u + 1 => target_pat_150 (v3 1 (vars 0) u)

private theorem step_pat_126 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_126 vars) (target_pat_126 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_126]; rw [h_vr]
    refine step_chain ?_ (step_pat_149 (v2 1 (vars 0)))
    dsimp only [pat_126, pat_149, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_126]; rw [h_vr]
    refine step_chain ?_ (step_pat_150 (v3 1 (vars 0) u))
    dsimp only [pat_126, pat_150, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_184 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_149 (v2 (vars 0 + 1) (vars 1)) | u + 1 => target_pat_150
    (v3 (vars 0 + 1) (vars 1) u)

private theorem step_pat_184 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_184 vars) (target_pat_184 vars) := by
  rcases h_vr : vars 2 with _ | u
  · simp -failIfUnchanged only [target_pat_184]; rw [h_vr]
    refine step_chain ?_ (step_pat_149 (v2 (vars 0 + 1) (vars 1)))
    dsimp only [pat_184, pat_149, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_184]; rw [h_vr]
    refine step_chain ?_ (step_pat_150 (v3 (vars 0 + 1) (vars 1) u))
    dsimp only [pat_184, pat_150, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_151_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => none | u + 1 => target_pat_184 (v3 (vars 0) (vars 1) u)

private theorem step_pat_151_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 1) :
  ReachesTarget ps (evalTapePattern pat_151 vars) (target_pat_151_pos vars) := by
  rcases h_vr : vars 2 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_151_pos]; rw [h_vr]
    refine step_chain ?_ (step_pat_184 (v3 (vars 0) (vars 1) u))
    dsimp only [pat_151, pat_184, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_185_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_151_pos (v3 (vars 0 + 1) (vars 1) (vars 2))

private theorem step_pat_185_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 1) :
  ReachesTarget ps (evalTapePattern pat_185 vars) (target_pat_185_pos vars) := by
  refine step_chain ?_ (step_pat_151_pos (v3 (vars 0 + 1) (vars 1) (vars 2)) (by var_omega))
  dsimp only [pat_185, pat_151, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_152_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_185_pos (v3 (vars 2 + vars 0) (vars 1) (vars 3))

private theorem step_pat_152_pos (vars : Nat → Nat) (h_c : vars 3 ≥ 1) :
  ReachesTarget ps (evalTapePattern pat_152 vars) (target_pat_152_pos vars) := by
  induction h_vr : vars 2 generalizing vars with
  | zero =>
    have h_eq : target_pat_152_pos vars = target_pat_185_pos (v3 (vars 0) (vars 1) (vars 3)) := by
      simp -failIfUnchanged only [target_pat_152_pos]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_185_pos (v3 (vars 0) (vars 1) (vars 3)) (by var_omega))
    dsimp only [pat_152, pat_185, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  | succ u ih =>
    have h_eq : target_pat_152_pos vars = target_pat_152_pos
      (v4 (vars 0 + 1) (vars 1) u (vars 3)) := by
      simp -failIfUnchanged only [target_pat_152_pos]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_186 (v4 (vars 0) (vars 1) u (vars 3)))
      ?_ (step_chain ?_ (ih (v4 (vars 0 + 1) (vars 1) u (vars 3)) h_c rfl))
    · dsimp only [pat_152, pat_186, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
    · dsimp only [pat_186, pat_152, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_373_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_152_pos (v4 (vars 0) (vars 1) 1 (vars 2))

private theorem step_pat_373_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 1) :
  ReachesTarget ps (evalTapePattern pat_373 vars) (target_pat_373_pos vars) := by
  refine step_chain ?_ (step_pat_152_pos (v4 (vars 0) (vars 1) 1 (vars 2)) (by var_omega))
  dsimp only [pat_373, pat_152, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_366_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_373_pos (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_366_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 1) :
  ReachesTarget ps (evalTapePattern pat_366 vars) (target_pat_366_pos vars) := by
  refine step_chain ?_ (step_pat_373_pos (v3 (vars 0) (vars 1) (vars 2)) (by var_omega))
  dsimp only [pat_366, pat_373, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_358_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => none | u + 1 => target_pat_366_pos (v3 (vars 0) (vars 1) u)

private theorem step_pat_358_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 2) :
  ReachesTarget ps (evalTapePattern pat_358 vars) (target_pat_358_pos vars) := by
  rcases h_vr : vars 2 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_358_pos]; rw [h_vr]
    refine step_chain ?_ (step_pat_366_pos (v3 (vars 0) (vars 1) u) (by var_omega))
    dsimp only [pat_358, pat_366, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_351_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => none | u + 1 => target_pat_358_pos (v3 (vars 0) (vars 1) u)

private theorem step_pat_351_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 3) :
  ReachesTarget ps (evalTapePattern pat_351 vars) (target_pat_351_pos vars) := by
  rcases h_vr : vars 2 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_351_pos]; rw [h_vr]
    refine step_chain ?_ (step_pat_358_pos (v3 (vars 0) (vars 1) u) (by var_omega))
    dsimp only [pat_351, pat_358, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_345_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => none | u + 1 => target_pat_351_pos (v3 (vars 0) (vars 1) u)

private theorem step_pat_345_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 4) :
  ReachesTarget ps (evalTapePattern pat_345 vars) (target_pat_345_pos vars) := by
  rcases h_vr : vars 2 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_345_pos]; rw [h_vr]
    refine step_chain ?_ (step_pat_351_pos (v3 (vars 0) (vars 1) u) (by var_omega))
    dsimp only [pat_345, pat_351, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_340_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_345_pos (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_340_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 4) :
  ReachesTarget ps (evalTapePattern pat_340 vars) (target_pat_340_pos vars) := by
  refine step_chain ?_ (step_pat_345_pos (v3 (vars 0) (vars 1) (vars 2)) (by var_omega))
  dsimp only [pat_340, pat_345, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_335_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => none | u + 1 => target_pat_340_pos (v3 (vars 0) (vars 1) (u + 1))

private theorem step_pat_335_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 4) :
  ReachesTarget ps (evalTapePattern pat_335 vars) (target_pat_335_pos vars) := by
  rcases h_vr : vars 2 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_335_pos]; rw [h_vr]
    refine step_chain ?_ (step_pat_340_pos (v3 (vars 0) (vars 1) (u + 1)) (by var_omega))
    dsimp only [pat_335, pat_340, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_367_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => none | u + 1 =>
    match vars 0 with
    | 0 => target_pat_333 (v2 (vars 1) ((u + 1) + 1)) | v + 1 => target_pat_335_pos
      (v3 v (vars 1) ((u + 1) + 1))

private theorem step_pat_367_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 3) :
  ReachesTarget ps (evalTapePattern pat_367 vars) (target_pat_367_pos vars) := by
  rcases h_vr : vars 2 with _ | u
  · omega
  · rcases h_vl : vars 0 with _ | v
    · simp -failIfUnchanged only [target_pat_367_pos]; rw [h_vr, h_vl]
      refine step_chain ?_ (step_pat_333 (v2 (vars 1) ((u + 1) + 1)))
      dsimp only [pat_367, pat_333, evalTapePattern, evalTapeExpr]; rw [h_vr];
        rw [h_vl]; pat_step
    · simp -failIfUnchanged only [target_pat_367_pos]; rw [h_vr, h_vl]
      refine step_chain ?_ (step_pat_335_pos (v3 v (vars 1) ((u + 1) + 1)) (by var_omega))
      dsimp only [pat_367, pat_335, evalTapePattern, evalTapeExpr]; rw [h_vr];
        rw [h_vl]; pat_step


private def target_pat_359_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => none | u + 1 => target_pat_367_pos (v3 (vars 0) (vars 1) ((u + 1) + 1))

private theorem step_pat_359_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 2) :
  ReachesTarget ps (evalTapePattern pat_359 vars) (target_pat_359_pos vars) := by
  rcases h_vr : vars 2 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_359_pos]; rw [h_vr]
    refine step_chain ?_ (step_pat_367_pos (v3 (vars 0) (vars 1) ((u + 1) + 1)) (by var_omega))
    dsimp only [pat_359, pat_367, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_369_pos (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => none | u + 1 => target_pat_359_pos (v3 (vars 0) (vars 1) ((u + 1) + 1))

private theorem step_pat_369_pos (vars : Nat → Nat) (h_c : vars 2 ≥ 1) :
  ReachesTarget ps (evalTapePattern pat_369 vars) (target_pat_369_pos vars) := by
  rcases h_vr : vars 2 with _ | u
  · omega
  · simp -failIfUnchanged only [target_pat_369_pos]; rw [h_vr]
    refine step_chain ?_ (step_pat_359_pos (v3 (vars 0) (vars 1) ((u + 1) + 1)) (by var_omega))
    dsimp only [pat_369, pat_359, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_361 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_369_pos (v3 (vars 0) (vars 1) 1) | u + 1 => target_pat_369_pos
    (v3 (vars 0) (vars 1) ((u + 1) + 1))

private theorem step_pat_361 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_361 vars) (target_pat_361 vars) := by
  rcases h_vr : vars 2 with _ | u
  · simp -failIfUnchanged only [target_pat_361]; rw [h_vr]
    refine step_chain ?_ (step_pat_369_pos (v3 (vars 0) (vars 1) 1) (by var_omega))
    dsimp only [pat_361, pat_369, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_361]; rw [h_vr]
    refine step_chain ?_ (step_pat_369_pos (v3 (vars 0) (vars 1) ((u + 1) + 1)) (by var_omega))
    dsimp only [pat_361, pat_369, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step

private def target_pat_354 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_361 (v3 (vars 0) (vars 1) 0)

private theorem step_pat_354 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_354 vars) (target_pat_354 vars) := by
  refine step_chain ?_ (step_pat_361 (v3 (vars 0) (vars 1) 0))
  dsimp only [pat_354, pat_361, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_348 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_354 (v2 (vars 0) (vars 1))

private theorem step_pat_348 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_348 vars) (target_pat_348 vars) := by
  refine step_chain ?_ (step_pat_354 (v2 (vars 0) (vars 1)))
  dsimp only [pat_348, pat_354, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_343 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_348 (v2 (vars 0) (vars 1))

private theorem step_pat_343 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_343 vars) (target_pat_343 vars) := by
  refine step_chain ?_ (step_pat_348 (v2 (vars 0) (vars 1)))
  dsimp only [pat_343, pat_348, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_338 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_343 (v2 (vars 0) (vars 1))

private theorem step_pat_338 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_338 vars) (target_pat_338 vars) := by
  refine step_chain ?_ (step_pat_343 (v2 (vars 0) (vars 1)))
  dsimp only [pat_338, pat_343, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_332 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_338 (v2 (vars 0) (vars 1))

private theorem step_pat_332 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_332 vars) (target_pat_332 vars) := by
  refine step_chain ?_ (step_pat_338 (v2 (vars 0) (vars 1)))
  dsimp only [pat_332, pat_338, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_326 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_332 (v2 (vars 0) (vars 1))

private theorem step_pat_326 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_326 vars) (target_pat_326 vars) := by
  refine step_chain ?_ (step_pat_332 (v2 (vars 0) (vars 1)))
  dsimp only [pat_326, pat_332, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_320 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_326 (v2 (vars 0) (vars 1))

private theorem step_pat_320 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_320 vars) (target_pat_320 vars) := by
  refine step_chain ?_ (step_pat_326 (v2 (vars 0) (vars 1)))
  dsimp only [pat_320, pat_326, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_312 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_320 (v2 (vars 0) (vars 1))

private theorem step_pat_312 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_312 vars) (target_pat_312 vars) := by
  refine step_chain ?_ (step_pat_320 (v2 (vars 0) (vars 1)))
  dsimp only [pat_312, pat_320, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_295 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_312 (v2 (vars 0) (vars 1))

private theorem step_pat_295 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_295 vars) (target_pat_295 vars) := by
  refine step_chain ?_ (step_pat_312 (v2 (vars 0) (vars 1)))
  dsimp only [pat_295, pat_312, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_271 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_295 (v2 (vars 0) (vars 1))

private theorem step_pat_271 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_271 vars) (target_pat_271 vars) := by
  refine step_chain ?_ (step_pat_295 (v2 (vars 0) (vars 1)))
  dsimp only [pat_271, pat_295, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_245 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_271 (v2 (vars 0) (vars 1))

private theorem step_pat_245 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_245 vars) (target_pat_245 vars) := by
  refine step_chain ?_ (step_pat_271 (v2 (vars 0) (vars 1)))
  dsimp only [pat_245, pat_271, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_226 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_245 (v2 (vars 0) (vars 1))

private theorem step_pat_226 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_226 vars) (target_pat_226 vars) := by
  refine step_chain ?_ (step_pat_245 (v2 (vars 0) (vars 1)))
  dsimp only [pat_226, pat_245, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_208 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_226 (v2 (vars 0) (vars 1))

private theorem step_pat_208 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_208 vars) (target_pat_208 vars) := by
  refine step_chain ?_ (step_pat_226 (v2 (vars 0) (vars 1)))
  dsimp only [pat_208, pat_226, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_180 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_208 (v2 (vars 0) (vars 1))

private theorem step_pat_180 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_180 vars) (target_pat_180 vars) := by
  refine step_chain ?_ (step_pat_208 (v2 (vars 0) (vars 1)))
  dsimp only [pat_180, pat_208, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_148 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_180 (v2 (vars 0) (vars 1))

private theorem step_pat_148 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_148 vars) (target_pat_148 vars) := by
  refine step_chain ?_ (step_pat_180 (v2 (vars 0) (vars 1)))
  dsimp only [pat_148, pat_180, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_125 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_148 (v2 1 (vars 0))

private theorem step_pat_125 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_125 vars) (target_pat_125 vars) := by
  refine step_chain ?_ (step_pat_148 (v2 1 (vars 0)))
  dsimp only [pat_125, pat_148, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_109 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_125 (v1 (vars 0)) | u + 1 => target_pat_126 (v2 (vars 0) u)

private theorem step_pat_109 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_109 vars) (target_pat_109 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_109]; rw [h_vr]
    refine step_chain ?_ (step_pat_125 (v1 (vars 0)))
    dsimp only [pat_109, pat_125, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_109]; rw [h_vr]
    refine step_chain ?_ (step_pat_126 (v2 (vars 0) u))
    dsimp only [pat_109, pat_126, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_183 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_148 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_183 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_183 vars) (target_pat_183 vars) := by
  refine step_chain ?_ (step_pat_148 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_183, pat_148, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_151 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_183 (v2 (vars 0) (vars 1)) | u + 1 => target_pat_184 (v3 (vars 0) (vars 1) u)

private theorem step_pat_151 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_151 vars) (target_pat_151 vars) := by
  rcases h_vr : vars 2 with _ | u
  · simp -failIfUnchanged only [target_pat_151]; rw [h_vr]
    refine step_chain ?_ (step_pat_183 (v2 (vars 0) (vars 1)))
    dsimp only [pat_151, pat_183, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_151]; rw [h_vr]
    refine step_chain ?_ (step_pat_184 (v3 (vars 0) (vars 1) u))
    dsimp only [pat_151, pat_184, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
private def target_pat_127 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_151 (v3 1 (vars 0) (vars 1))

private theorem step_pat_127 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_127 vars) (target_pat_127 vars) := by
  refine step_chain ?_ (step_pat_151 (v3 1 (vars 0) (vars 1)))
  dsimp only [pat_127, pat_151, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_185 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_151 (v3 (vars 0 + 1) (vars 1) (vars 2))

private theorem step_pat_185 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_185 vars) (target_pat_185 vars) := by
  refine step_chain ?_ (step_pat_151 (v3 (vars 0 + 1) (vars 1) (vars 2)))
  dsimp only [pat_185, pat_151, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_152 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_185 (v3 (vars 2 + vars 0) (vars 1) (vars 3))

private theorem step_pat_152 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_152 vars) (target_pat_152 vars) := by
  induction h_vr : vars 2 generalizing vars with
  | zero =>
    have h_eq : target_pat_152 vars = target_pat_185 (v3 (vars 0) (vars 1) (vars 3)) := by
      simp -failIfUnchanged only [target_pat_152]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain ?_ (step_pat_185 (v3 (vars 0) (vars 1) (vars 3)))
    dsimp only [pat_152, pat_185, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  | succ u ih =>
    have h_eq : target_pat_152 vars = target_pat_152 (v4 (vars 0 + 1) (vars 1) u (vars 3)) := by
      simp -failIfUnchanged only [target_pat_152]; rw [h_vr]; congr_vars
    rw [h_eq]
    refine step_chain_explicit (evalTapePattern pat_186 (v4 (vars 0) (vars 1) u (vars 3)))
      ?_ (step_chain ?_ (ih (v4 (vars 0 + 1) (vars 1) u (vars 3)) rfl))
    · dsimp only [pat_152, pat_186, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
    · dsimp only [pat_186, pat_152, evalTapePattern, evalTapeExpr]; pat_step


private def target_pat_128 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_152 (v4 1 (vars 0) (vars 1) (vars 2))

private theorem step_pat_128 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_128 vars) (target_pat_128 vars) := by
  refine step_chain ?_ (step_pat_152 (v4 1 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_128, pat_152, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_110 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_127 (v2 (vars 0) (vars 2)) | u + 1 => target_pat_128 (v3 (vars 0) u (vars 2))

private theorem step_pat_110 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_110 vars) (target_pat_110 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_110]; rw [h_vr]
    refine step_chain ?_ (step_pat_127 (v2 (vars 0) (vars 2)))
    dsimp only [pat_110, pat_127, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step
  · simp -failIfUnchanged only [target_pat_110]; rw [h_vr]
    refine step_chain ?_ (step_pat_128 (v3 (vars 0) u (vars 2)))
    dsimp only [pat_110, pat_128, evalTapePattern, evalTapeExpr]; rw [h_vr];
      pat_step

private def target_pat_95 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_108 (v2 0 (vars 0))

private theorem step_pat_95 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_95 vars) (target_pat_95 vars) := by
  refine step_chain ?_ (step_pat_108 (v2 0 (vars 0)))
  dsimp only [pat_95, pat_108, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_97 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_109 (v2 (vars 0) (vars 1))

private theorem step_pat_97 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_97 vars) (target_pat_97 vars) := by
  refine step_chain ?_ (step_pat_109 (v2 (vars 0) (vars 1)))
  dsimp only [pat_97, pat_109, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_98 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_110 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_98 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_98 vars) (target_pat_98 vars) := by
  refine step_chain ?_ (step_pat_110 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_98, pat_110, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_83 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_97 (v2 (vars 0) (vars 2)) | u + 1 => target_pat_98 (v3 (vars 0) u (vars 2))

private theorem step_pat_83 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_83 vars) (target_pat_83 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_83]; rw [h_vr]
    refine step_chain ?_ (step_pat_97 (v2 (vars 0) (vars 2)))
    dsimp only [pat_83, pat_97, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_83]; rw [h_vr]
    refine step_chain ?_ (step_pat_98 (v3 (vars 0) u (vars 2)))
    dsimp only [pat_83, pat_98, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_96 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_83 (v3 0 (vars 0) (vars 1))

private theorem step_pat_96 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_96 vars) (target_pat_96 vars) := by
  refine step_chain ?_ (step_pat_83 (v3 0 (vars 0) (vars 1)))
  dsimp only [pat_96, pat_83, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_82 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_95 (v1 (vars 1)) | u + 1 => target_pat_96 (v2 u (vars 1))

private theorem step_pat_82 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_82 vars) (target_pat_82 vars) := by
  rcases h_vr : vars 0 with _ | u
  · simp -failIfUnchanged only [target_pat_82]; rw [h_vr]
    refine step_chain ?_ (step_pat_95 (v1 (vars 1)))
    dsimp only [pat_82, pat_95, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_82]; rw [h_vr]
    refine step_chain ?_ (step_pat_96 (v2 u (vars 1)))
    dsimp only [pat_82, pat_96, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_270 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_82 (v2 (vars 1 + 1) (vars 2)) | v + 1 => target_pat_83
    (v3 v (vars 1 + 1) (vars 2))

private theorem step_pat_270 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_270 vars) (target_pat_270 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_270]; rw [h_vl]
    refine step_chain ?_ (step_pat_82 (v2 (vars 1 + 1) (vars 2)))
    dsimp only [pat_270, pat_82, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_270]; rw [h_vl]
    refine step_chain ?_ (step_pat_83 (v3 v (vars 1 + 1) (vars 2)))
    dsimp only [pat_270, pat_83, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_75 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_84 (v1 1)

private theorem step_pat_75 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_75 vars) (target_pat_75 vars) := by
  refine step_chain ?_ (step_pat_84 (v1 1))
  dsimp only [pat_75, pat_84, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_69 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_75 (fun _ => 0)

private theorem step_pat_69 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_69 vars) (target_pat_69 vars) := by
  refine step_chain ?_ (step_pat_75 (fun _ => 0))
  dsimp only [pat_69, pat_75, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_70 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_76 (v1 1) | v + 1 => target_pat_77 (v2 v 1)

private theorem step_pat_70 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_70 vars) (target_pat_70 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_70]; rw [h_vl]
    refine step_chain ?_ (step_pat_76 (v1 1))
    dsimp only [pat_70, pat_76, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_70]; rw [h_vl]
    refine step_chain ?_ (step_pat_77 (v2 v 1) (by var_omega))
    dsimp only [pat_70, pat_77, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_66 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_69 (fun _ => 0) | v + 1 => target_pat_70 (v1 v)

private theorem step_pat_66 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_66 vars) (target_pat_66 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_66]; rw [h_vl]
    refine step_chain ?_ (step_pat_69 (fun _ => 0))
    dsimp only [pat_66, pat_69, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_66]; rw [h_vl]
    refine step_chain ?_ (step_pat_70 (v1 v))
    dsimp only [pat_66, pat_70, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_64 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_66 (v1 (vars 0))

private theorem step_pat_64 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_64 vars) (target_pat_64 vars) := by
  refine step_chain ?_ (step_pat_66 (v1 (vars 0)))
  dsimp only [pat_64, pat_66, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_62 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_64 (v1 (vars 0))

private theorem step_pat_62 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_62 vars) (target_pat_62 vars) := by
  refine step_chain ?_ (step_pat_64 (v1 (vars 0)))
  dsimp only [pat_62, pat_64, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_78 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_89 (v1 1)

private theorem step_pat_78 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_78 vars) (target_pat_78 vars) := by
  refine step_chain ?_ (step_pat_89 (v1 1))
  dsimp only [pat_78, pat_89, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_71 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_78 (fun _ => 0)

private theorem step_pat_71 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_71 vars) (target_pat_71 vars) := by
  refine step_chain ?_ (step_pat_78 (fun _ => 0))
  dsimp only [pat_71, pat_78, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_72 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_79 (v1 1) | v + 1 => target_pat_80 (v2 v 1)

private theorem step_pat_72 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_72 vars) (target_pat_72 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_72]; rw [h_vl]
    refine step_chain ?_ (step_pat_79 (v1 1))
    dsimp only [pat_72, pat_79, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_72]; rw [h_vl]
    refine step_chain ?_ (step_pat_80 (v2 v 1))
    dsimp only [pat_72, pat_80, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_67 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_71 (fun _ => 0) | v + 1 => target_pat_72 (v1 v)

private theorem step_pat_67 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_67 vars) (target_pat_67 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_67]; rw [h_vl]
    refine step_chain ?_ (step_pat_71 (fun _ => 0))
    dsimp only [pat_67, pat_71, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_67]; rw [h_vl]
    refine step_chain ?_ (step_pat_72 (v1 v))
    dsimp only [pat_67, pat_72, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_81 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_94 (v2 1 (vars 0))

private theorem step_pat_81 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_81 vars) (target_pat_81 vars) := by
  refine step_chain ?_ (step_pat_94 (v2 1 (vars 0)))
  dsimp only [pat_81, pat_94, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_73 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_81 (v1 (vars 0))

private theorem step_pat_73 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_73 vars) (target_pat_73 vars) := by
  refine step_chain ?_ (step_pat_81 (v1 (vars 0)))
  dsimp only [pat_73, pat_81, evalTapePattern, evalTapeExpr]; pat_step
private def target_pat_68 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_73 (v1 (vars 1)) | v + 1 => some (evalTapePattern pat_270 (v3 v 0 (vars 1)))

private theorem step_pat_68 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_68 vars) (target_pat_68 vars) := by
  rcases h_vl : vars 0 with _ | v
  · simp -failIfUnchanged only [target_pat_68]; rw [h_vl]
    refine step_chain ?_ (step_pat_73 (v1 (vars 1)))
    dsimp only [pat_68, pat_73, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · simp -failIfUnchanged only [target_pat_68]; rw [h_vl]
    refine step_base ?_ (in_ps_270 (v3 v 0 (vars 1)))
    dsimp only [pat_68, pat_270, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_65 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_67 (v1 (vars 0)) | u + 1 => target_pat_68 (v2 (vars 0) u)

private theorem step_pat_65 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_65 vars) (target_pat_65 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_65]; rw [h_vr]
    refine step_chain ?_ (step_pat_67 (v1 (vars 0)))
    dsimp only [pat_65, pat_67, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_65]; rw [h_vr]
    refine step_chain ?_ (step_pat_68 (v2 (vars 0) u))
    dsimp only [pat_65, pat_68, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_63 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_36 (v1 (vars 0)) | u + 1 => target_pat_65 (v2 (vars 0) u)

private theorem step_pat_63 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_63 vars) (target_pat_63 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_63]; rw [h_vr]
    refine step_chain ?_ (step_pat_36 (v1 (vars 0)))
    dsimp only [pat_63, pat_36, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_63]; rw [h_vr]
    refine step_chain ?_ (step_pat_65 (v2 (vars 0) u))
    dsimp only [pat_63, pat_65, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_61 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_62 (v1 (vars 0 + 1)) | u + 1 => target_pat_63 (v2 (vars 0 + 1) u)

private theorem step_pat_61 (vars : Nat → Nat) :
  ReachesTarget ps (evalTapePattern pat_61 vars) (target_pat_61 vars) := by
  rcases h_vr : vars 1 with _ | u
  · simp -failIfUnchanged only [target_pat_61]; rw [h_vr]
    refine step_chain ?_ (step_pat_62 (v1 (vars 0 + 1)))
    dsimp only [pat_61, pat_62, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · simp -failIfUnchanged only [target_pat_61]; rw [h_vr]
    refine step_chain ?_ (step_pat_63 (v2 (vars 0 + 1) u))
    dsimp only [pat_61, pat_63, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem init_reaches_pat_61 :
    ReachesStar target (init [])
      (evalTapePattern pat_61 fun k => match k with | 0 => 0 | 1 => 7 | _ => 0) := by
  dsimp only [pat_61, evalTapePattern, evalTapeExpr]
  bb_steps

private theorem init_reaches_ps :
    ∃ cfg₀, ReachesStar target (init []) cfg₀ ∧ IsInPatternSet ps cfg₀ :=
  ⟨_, init_reaches_pat_61, in_ps_61 fun k => match k with | 0 => 0 | 1 => 7 | _ => 0⟩



private theorem rule_1 (a : Nat) :
    ReachesPlus target (cfg_P61 a 0) (cfg_P61 0 (4 * a + 4 * (a / 2) + 15)) := by
  have h := step_pat_61 (v2 a 0)
  have h_t : target_pat_61 (v2 a 0) = some (cfg_P61 0 (4 * a + 4 * (a / 2) + 15)) := by
    rcases a with _ | _ | a' <;> (congr_cfg pat_61)
  rw [h_t] at h
  exact h.1

private theorem rule_2 (a : Nat) :
    ReachesPlus target (cfg_P61 a 1) (cfg_P61 0 (2 * a + 11)) := by
  have h := step_pat_61 (v2 a 1)
  have h_t : target_pat_61 (v2 a 1) = some (cfg_P61 0 (2 * a + 11)) := by
    rcases a with _ | _ | a' <;> (congr_cfg pat_61)
  rw [h_t] at h
  exact h.1

private theorem rule_3 (a : Nat) :
    ∃ cfg_h, ReachesPlus target (cfg_P61 a 2) cfg_h ∧ (step target cfg_h).isNone := by
  have h := step_pat_61 (v2 a 2)
  have h_t : target_pat_61 (v2 a 2) = none := by
    rcases a with _ | _ | a' <;> rfl
  rw [h_t] at h
  exact h

private theorem rule_4 (a c : Nat) :
    ReachesPlus target (cfg_P61 a (c + 3)) (cfg_P270 a 0 c) := by
  have h := step_pat_61 (v2 a (c + 3))
  have h_t : target_pat_61 (v2 a (c + 3)) = some (cfg_P270 a 0 c) := by
    rcases a with _ | a' <;> rfl
  rw [h_t] at h
  exact h.1

private theorem rule_5_0 (b : Nat) :
    ∃ cfg_h, ReachesPlus target (cfg_P270 0 b 0) cfg_h ∧ (step target cfg_h).isNone := by
  have h := step_pat_270 (v3 0 b 0)
  have h_t : target_pat_270 (v3 0 b 0) = none := by
    rcases b with _ | _ | b' <;> rfl
  rw [h_t] at h
  exact h

private theorem rule_5_1 (b : Nat) :
    ∃ cfg_h, ReachesPlus target (cfg_P270 1 b 0) cfg_h ∧ (step target cfg_h).isNone := by
  have h := step_pat_270 (v3 1 b 0)
  have h_t : target_pat_270 (v3 1 b 0) = none := by
    rcases b with _ | _ | b' <;> rfl
  rw [h_t] at h
  exact h

private theorem rule_6 (a b : Nat) :
    ReachesPlus target (cfg_P270 (a + 2) b 0)
      (cfg_P61 0 (4 * a + 4 * (a / 2) + 4 * b + 35)) := by
  have h := step_pat_270 (v3 (a + 2) b 0)
  have h_t : target_pat_270 (v3 (a + 2) b 0) = some (cfg_P61 0 (4 * a + 4 * (a / 2) + 4 * b +
    35)) := by
    rcases a with _ | _ | a' <;> rcases b with _ | _ | b' <;> (congr_cfg pat_61)
  rw [h_t] at h
  exact h.1

private theorem rule_7_0 (b : Nat) :
    ∃ cfg_h, ReachesPlus target (cfg_P270 0 b 1) cfg_h ∧ (step target cfg_h).isNone := by
  have h := step_pat_270 (v3 0 b 1)
  have h_t : target_pat_270 (v3 0 b 1) = none := by
    rcases b with _ | _ | b' <;> rfl
  rw [h_t] at h
  exact h

private theorem rule_7_1 (b : Nat) :
    ∃ cfg_h, ReachesPlus target (cfg_P270 1 b 1) cfg_h ∧ (step target cfg_h).isNone := by
  have h := step_pat_270 (v3 1 b 1)
  have h_t : target_pat_270 (v3 1 b 1) = none := by
    rcases b with _ | _ | b' <;> rfl
  rw [h_t] at h
  exact h

private theorem rule_8 (a b : Nat) :
    ReachesPlus target (cfg_P270 (a + 2) b 1)
      (cfg_P61 0 (4 * a + 4 * (a / 2) + 4 * b + 27)) := by
  have h := step_pat_270 (v3 (a + 2) b 1)
  have h_t : target_pat_270 (v3 (a + 2) b 1) = some (cfg_P61 0 (4 * a + 4 * (a / 2) + 4 * b +
    27)) := by
    rcases a with _ | _ | a' <;> rcases b with _ | _ | b' <;> (congr_cfg pat_61)
  rw [h_t] at h
  exact h.1

private theorem rule_9 (a b : Nat) :
    ReachesPlus target (cfg_P270 a b 2) (cfg_P61 0 (2 * a + 2 * b + 13)) := by
  have h := step_pat_270 (v3 a b 2)
  have h_t : target_pat_270 (v3 a b 2) = some (cfg_P61 0 (2 * a + 2 * b + 13)) := by
    rcases a with _ | _ | _ | a' <;> rcases b with _ | _ | b' <;> (congr_cfg pat_61)
  rw [h_t] at h
  exact h.1

private theorem rule_10_0 (b c : Nat) :
    ReachesPlus target (cfg_P270 0 b (c + 3)) (cfg_P61 (2 * b + 8) c) := by
  have h := step_pat_270 (v3 0 b (c + 3))
  have h_t : target_pat_270 (v3 0 b (c + 3)) = some (cfg_P61 (2 * b + 8) c) := by
    rcases b with _ | _ | b' <;> rcases c with _ | c' <;> (congr_cfg pat_61)
  rw [h_t] at h
  exact h.1

private theorem rule_10_1 (b c : Nat) :
    ReachesPlus target (cfg_P270 1 b (c + 3)) (cfg_P61 (2 * b + 10) c) := by
  have h := step_pat_270 (v3 1 b (c + 3))
  have h_t : target_pat_270 (v3 1 b (c + 3)) = some (cfg_P61 (2 * b + 10) c) := by
    rcases b with _ | _ | b' <;> rcases c with _ | c' <;> (congr_cfg pat_61)
  rw [h_t] at h
  exact h.1

private theorem rule_11 (a b : Nat) :
    ∃ cfg_h, ReachesPlus target (cfg_P270 (a + 2) b 3) cfg_h ∧ (step target cfg_h).isNone := by
  have h := step_pat_270 (v3 (a + 2) b 3)
  have h_t : target_pat_270 (v3 (a + 2) b 3) = none := by
    rcases a with _ | a' <;> rcases b with _ | _ | b' <;> rfl
  rw [h_t] at h
  exact h

private theorem rule_12 (a b c : Nat) :
    ReachesPlus target (cfg_P270 (a + 2) b (c + 4)) (cfg_P270 a (b + 3) c) := by
  have h := step_pat_270 (v3 (a + 2) b (c + 4))
  have h_t : target_pat_270 (v3 (a + 2) b (c + 4)) = some (cfg_P270 a (b + 3) c) := by
    rcases a with _ | _ | a' <;> rcases b with _ | _ | b' <;> rcases c with _ | c' <;> (congr_cfg
      pat_270)
  rw [h_t] at h
  exact h.1


/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨init_reaches_ps, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · exact reachesTarget_to_exists (step_pat_61 vars)
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · exact reachesTarget_to_exists (step_pat_270 vars)
  · nomatch h_mem

/-- `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`. -/
inductive State where
  /-- $P_{61}(a, c) := 0^\infty\,1^{a+1}\,\mathrm{B}{>}\,1^{c+3}\,01\,0^\infty$. -/
  | P61 (a c : ℕ)
  /-- $P_{270}(a, b,
    c) := 0^\infty\,1^{a+1}\,\mathrm{D}{>}\,110\,(10)^b\,1^{c+3}\,01\,0^\infty$. -/
  | P270 (a b c : ℕ)

/-- Initial symbolic state $P_{61}(0, 7)$, reached after 44 raw TM steps. -/
def start : State := .P61 0 7

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .P61 a c =>
    Cfg.headRight B
      (ListBlank.cons 1 (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
      (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
        (ListBlank.append (([1] : List (Fin 2)) ^ c)
          (ListBlank.cons 0 (ListBlank.cons 1 default))))))
  | .P270 a b c =>
    Cfg.headRight D
      (ListBlank.cons 1 (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
      (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
          (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
            (ListBlank.append (([1] : List (Fin 2)) ^ c)
              (ListBlank.cons 0 (ListBlank.cons 1 default))))))))))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .P61 a 0 => some (.P61 0 (4 * a + 4 * (a / 2) + 15))
  | .P61 a 1 => some (.P61 0 (2 * a + 11))
  | .P61 _ 2 => none
  | .P61 a (c + 3) => some (.P270 a 0 c)
  | .P270 0 _ 0 => none
  | .P270 1 _ 0 => none
  | .P270 (a + 2) b 0 => some (.P61 0 (4 * a + 4 * (a / 2) + 4 * b + 35))
  | .P270 0 _ 1 => none
  | .P270 1 _ 1 => none
  | .P270 (a + 2) b 1 => some (.P61 0 (4 * a + 4 * (a / 2) + 4 * b + 27))
  | .P270 a b 2 => some (.P61 0 (2 * a + 2 * b + 13))
  | .P270 0 b (c + 3) => some (.P61 (2 * b + 8) c)
  | .P270 1 b (c + 3) => some (.P61 (2 * b + 10) c)
  | .P270 (_ + 2) _ 3 => none
  | .P270 (a + 2) b (c + 4) => some (.P270 a (b + 3) c)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_pat_61
  step_some := by
    rintro (⟨a, c⟩ | ⟨a, b, c⟩) s' hnext
    · rcases c with _ | _ | _ | c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_1 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_2 a
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_4 a c
    · rcases c with _ | _ | _ | _ | c
      · rcases a with _ | _ | a
        · simp [next] at hnext
        · simp [next] at hnext
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_6 a b
      · rcases a with _ | _ | a
        · simp [next] at hnext
        · simp [next] at hnext
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_8 a b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_9 a b
      · rcases a with _ | _ | a
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_10_0 b 0
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_10_1 b 0
        · simp [next] at hnext
      · rcases a with _ | _ | a
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_10_0 b (c + 1)
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_10_1 b (c + 1)
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_12 a b c
  step_none := by
    rintro (⟨a, c⟩ | ⟨a, b, c⟩) hnext
    · rcases c with _ | _ | _ | c
      · simp [next] at hnext
      · simp [next] at hnext
      · obtain ⟨cfg_h, h_reach, h_halt⟩ := rule_3 a
        exact ⟨cfg_h, h_reach.to_star, h_halt⟩
      · simp [next] at hnext
    · rcases c with _ | _ | _ | _ | c
      · rcases a with _ | _ | a
        · obtain ⟨cfg_h, h_reach, h_halt⟩ := rule_5_0 b
          exact ⟨cfg_h, h_reach.to_star, h_halt⟩
        · obtain ⟨cfg_h, h_reach, h_halt⟩ := rule_5_1 b
          exact ⟨cfg_h, h_reach.to_star, h_halt⟩
        · simp [next] at hnext
      · rcases a with _ | _ | a
        · obtain ⟨cfg_h, h_reach, h_halt⟩ := rule_7_0 b
          exact ⟨cfg_h, h_reach.to_star, h_halt⟩
        · obtain ⟨cfg_h, h_reach, h_halt⟩ := rule_7_1 b
          exact ⟨cfg_h, h_reach.to_star, h_halt⟩
        · simp [next] at hnext
      · simp [next] at hnext
      · rcases a with _ | _ | a
        · simp [next] at hnext
        · simp [next] at hnext
        · obtain ⟨cfg_h, h_reach, h_halt⟩ := rule_11 a b
          exact ⟨cfg_h, h_reach.to_star, h_halt⟩
      · rcases a with _ | _ | a <;> simp [next] at hnext

/-- Halting of `target` is equivalent to halting of the accelerated system `(next, start)`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-like Acceleration -/

/-- High-level symbolic state $P(c) := P_{61}(0, c)$ on a single counter $c$. -/
inductive HighLevelState where
  | P (c : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $P(7)$. -/
def highLevelStart : HighLevelState := .P 7

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .P c => .P61 0 c

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Evaluate $P_{61}(a, c)$ across the $P_{270}$ diagonal sweep and any intermediate $a' > 0$
returns (which strictly decrease $c$ by at least $6$) until reaching $P_{61}(0, c')$ or halting. -/
def drainP (a c : ℕ) : Option HighLevelState :=
  if c = 0 then some (.P (4 * a + 4 * (a / 2) + 15))
  else if c = 1 then some (.P (2 * a + 11))
  else if c = 2 then none
  else
    let c0 := c - 3
    let k := min (a / 2) (c0 / 4)
    let a1 := a - 2 * k
    let b1 := 3 * k
    let c1 := c0 - 4 * k
    if c1 = 0 then
      if a1 < 2 then none
      else some (.P (4 * (a1 - 2) + 4 * ((a1 - 2) / 2) + 4 * b1 + 35))
    else if c1 = 1 then
      if a1 < 2 then none
      else some (.P (4 * (a1 - 2) + 4 * ((a1 - 2) / 2) + 4 * b1 + 27))
    else if c1 = 2 then
      some (.P (2 * a1 + 2 * b1 + 13))
    else if c1 = 3 then
      if a1 = 0 then some (.P (12 * b1 + 63))
      else if a1 = 1 then some (.P (12 * b1 + 75))
      else none
    else if a1 = 0 then drainP (2 * b1 + 8) (c1 - 3)
    else drainP (2 * b1 + 10) (c1 - 3)
termination_by c
decreasing_by
  all_goals exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)) (by omega)

/-- High-level single-counter Collatz-like transition function on $P(c)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .P c => drainP 0 c

private theorem reaches_P270_diag (k : ℕ) (a b c : ℕ) :
    CollatzReachesStar next (.P270 (a + 2 * k) b (c + 4 * k)) (.P270 a (b + 3 * k) c) := by
  induction k generalizing b with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    have h_step : next (.P270 (a + 2 * (k + 1)) b (c + 4 * (k + 1))) =
        some (.P270 (a + 2 * k) (b + 3) (c + 4 * k)) := by
      have ha : a + 2 * (k + 1) = (a + 2 * k) + 2 := by omega
      have hc : c + 4 * (k + 1) = (c + 4 * k) + 4 := by omega
      rw [ha, hc]
      simp [next]
    have ih' := ih (b + 3)
    have hb : b + 3 + 3 * k = b + 3 * (k + 1) := by omega
    rw [hb] at ih'
    exact CollatzReachesStar.head h_step ih'

private theorem stepsTo_drainP (c : ℕ) : ∀ (a : ℕ),
    CollatzStepsTo next (.P61 a c) ((drainP a c).map toState) := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro a
    rw [drainP]
    rcases c with _ | _ | _ | c0
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
    · have hc_ne0 : c0 + 1 + 1 + 1 ≠ 0 := by omega
      have hc_ne1 : c0 + 1 + 1 + 1 ≠ 1 := by omega
      have hc_ne2 : c0 + 1 + 1 + 1 ≠ 2 := by omega
      have hc_sub : c0 + 1 + 1 + 1 - 3 = c0 := by omega
      simp only [hc_ne0, hc_ne1, hc_ne2, ↓reduceIte, hc_sub]
      refine CollatzStepsTo.head rfl ?_
      let k := min (a / 2) (c0 / 4)
      have h_diag := reaches_P270_diag k (a - 2 * k) 0 (c0 - 4 * k)
      have ha_eq : a - 2 * k + 2 * k = a := by omega
      have hc_eq : c0 - 4 * k + 4 * k = c0 := by omega
      rw [Nat.zero_add, ha_eq, hc_eq] at h_diag
      refine CollatzStepsTo.of_reachesStar h_diag ?_
      change CollatzStepsTo next (.P270 (a - 2 * k) (3 * k) (c0 - 4 * k))
        ((let a1 := a - 2 * k
          let b1 := 3 * k
          let c1 := c0 - 4 * k
          if c1 = 0 then
            if a1 < 2 then none
            else some (.P (4 * (a1 - 2) + 4 * ((a1 - 2) / 2) + 4 * b1 + 35))
          else if c1 = 1 then
            if a1 < 2 then none
            else some (.P (4 * (a1 - 2) + 4 * ((a1 - 2) / 2) + 4 * b1 + 27))
          else if c1 = 2 then
            some (.P (2 * a1 + 2 * b1 + 13))
          else if c1 = 3 then
            if a1 = 0 then some (.P (12 * b1 + 63))
            else if a1 = 1 then some (.P (12 * b1 + 75))
            else none
          else if a1 = 0 then drainP (2 * b1 + 8) (c1 - 3)
          else drainP (2 * b1 + 10) (c1 - 3)).map toState)
      set a1 := a - 2 * k
      set b1 := 3 * k
      set c1 := c0 - 4 * k
      rcases c1 with _ | _ | _ | _ | c2
      · simp only [↓reduceIte]
        rcases a1 with _ | _ | a2
        · exact CollatzStepsTo.of_eq rfl
        · exact CollatzStepsTo.of_eq rfl
        · have hlt : ¬ (a2 + 2 < 2) := by omega
          have hsub2 : a2 + 2 - 2 = a2 := by omega
          simp only [hlt, ↓reduceIte, hsub2, Option.map, toState]
          exact CollatzStepsTo.of_eq rfl
      · simp only [↓reduceIte]
        rcases a1 with _ | _ | a2
        · exact CollatzStepsTo.of_eq rfl
        · exact CollatzStepsTo.of_eq rfl
        · have hlt : ¬ (a2 + 2 < 2) := by omega
          have hsub2 : a2 + 2 - 2 = a2 := by omega
          simp only [hlt, ↓reduceIte, hsub2, Option.map, toState]
          exact CollatzStepsTo.of_eq rfl
      · simp only [Nat.reduceEqDiff, ↓reduceIte, Option.map, toState]
        rcases a1 with _ | _ | a2 <;> exact CollatzStepsTo.of_eq rfl
      · simp only [Nat.reduceEqDiff, ↓reduceIte]
        rcases a1 with _ | _ | a2
        · simp only [↓reduceIte, Option.map, toState]
          refine CollatzStepsTo.head rfl ?_
          have h_eq : 4 * (2 * b1 + 8) + 4 * ((2 * b1 + 8) / 2) + 15 = 12 * b1 + 63 := by omega
          exact CollatzStepsTo.of_eq (by simp [next, h_eq])
        · simp only [Nat.reduceEqDiff, ↓reduceIte, Option.map, toState]
          refine CollatzStepsTo.head rfl ?_
          have h_eq : 4 * (2 * b1 + 10) + 4 * ((2 * b1 + 10) / 2) + 15 = 12 * b1 + 75 := by omega
          exact CollatzStepsTo.of_eq (by simp [next, h_eq])
        · have hne0 : a2 + 2 ≠ 0 := by omega
          have hne1 : a2 + 2 ≠ 1 := by omega
          simp only [hne0, hne1, ↓reduceIte, Option.map]
          exact CollatzStepsTo.of_eq rfl
      · have hne0 : c2 + 1 + 1 + 1 + 1 ≠ 0 := by omega
        have hne1 : c2 + 1 + 1 + 1 + 1 ≠ 1 := by omega
        have hne2 : c2 + 1 + 1 + 1 + 1 ≠ 2 := by omega
        have hne3 : c2 + 1 + 1 + 1 + 1 ≠ 3 := by omega
        have ha1_lt : a1 < 2 := by omega
        have hsub : c2 + 1 + 1 + 1 + 1 - 3 = c2 + 1 := by omega
        have hlt_c : c2 + 1 < c0 + 1 + 1 + 1 := by omega
        simp only [hne0, hne1, hne2, hne3, ↓reduceIte, hsub]
        interval_cases a1
        · simp only [↓reduceIte]
          exact CollatzStepsTo.head rfl (ih (c2 + 1) hlt_c (2 * b1 + 8))
        · simp only [Nat.reduceEqDiff, ↓reduceIte]
          exact CollatzStepsTo.head rfl (ih (c2 + 1) hlt_c (2 * b1 + 10))

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState) (CollatzReachesStar.refl next _) ?_
  rintro ⟨c⟩
  exact stepsTo_drainP c 0

/-- Halting of `target` is equivalent to halting of `(highLevelNext, highLevelStart)`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- Equivalence between the low-level and high-level Collatz-like accelerations. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RBHHH
