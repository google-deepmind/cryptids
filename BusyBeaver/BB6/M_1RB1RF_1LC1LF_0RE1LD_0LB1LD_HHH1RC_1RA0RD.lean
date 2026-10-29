/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD`

We formalize a closed Collatz-like reduction (`HasCollatzReduction` and `IsValidAcceleration`) for
the 6-state, 2-symbol Busy Beaver holdout `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD`
(holdout #688, `suspect_33`), listed on the bbchallenge Wiki at
<https://wiki.bbchallenge.org/wiki/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD>.

## Collatz-like Acceleration Rules

 Canonical configuration:
```text
E(a, b, c) := 0^∞ 1 (01)^(b+1) (11)^a 111 A> 1^(c+1) 0^∞   (pat_64)
```

Start state (at step 65 from the blank tape):
```text
E(0, 0, 2) = 0^∞ 1 01 111 A> 111 0^∞
```

Accelerated transitions:
```text
E(a, 0, 0)         --> E(0, 0, 2a + 5)
E(a, 0, 1)         --> E(0, 0, 2a + 3)
E(a, 0, 2)         --> E(0, 0, 2a + 9)
E(a, 0, 3)         --> E(0, 0, 2a + 7)
E(a, 0, 4)         --> E(0, 0, 2a + 12)
E(a, 0, 5)         --> E(0, 0, 2a + 10)
E(a, 0, 6)         --> Halt
E(a, 0, c + 7)     --> E(0, a + 4, c + 1)
E(a, 1, 0)         --> E(0, 2, 2a + 3)
E(a, 1, 1)         --> E(0, 2, 2a + 1)
E(a, b + 1, c + 2) --> E(a + 2, b, c)
E(a, b + 2, 0)     --> E(0, b, 2a + 7)
E(a, b + 2, 1)     --> E(0, b, 2a + 5)
```

<!-- hardness:begin -->
## Hardness

*Hardness class:* Cascade — trigger **EQ**, growth exponential, shield see family.

*Verdict (heuristic; community analysis, see the wiki page):* wiki rediscovery (RobinCodes *Next
Steps* list).

*Hazard:* not re-measured in our dossiers

*Simulated horizon:* —

*Why it is hard:* E1 pair of #116

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD

open SixState Turing

/-- RLE definition of `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD`. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD"

/-- Transition function for `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

private theorem target_A_0 : target A 0 = some (some B, Stmt.write 1 Dir.right) := rfl
private theorem target_A_1 : target A 1 = some (some F, Stmt.write 1 Dir.right) := rfl
private theorem target_B_0 : target B 0 = some (some C, Stmt.write 1 Dir.left) := rfl
private theorem target_B_1 : target B 1 = some (some F, Stmt.write 1 Dir.left) := rfl
private theorem target_C_0 : target C 0 = some (some E, Stmt.write 0 Dir.right) := rfl
private theorem target_C_1 : target C 1 = some (some D, Stmt.write 1 Dir.left) := rfl
private theorem target_D_0 : target D 0 = some (some B, Stmt.write 0 Dir.left) := rfl
private theorem target_D_1 : target D 1 = some (some D, Stmt.write 1 Dir.left) := rfl
private theorem target_E_0 : target E 0 = none := rfl
private theorem target_E_1 : target E 1 = some (some C, Stmt.write 1 Dir.right) := rfl
private theorem target_F_0 : target F 0 = some (some A, Stmt.write 1 Dir.right) := rfl
private theorem target_F_1 : target F 1 = some (some D, Stmt.write 0 Dir.right) := rfl

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
    simp only [step, Cfg.headRight, Cfg.headLeft,
      target_A_0, target_A_1, target_B_0, target_B_1,
      target_C_0, target_C_1, target_D_0, target_D_1, target_E_0, target_E_1,
      target_F_0, target_F_1, evalTapePattern, evalTapeExpr,
      list_pow_zero, list_pow_succ, List.cons_append, List.singleton_append,
      List.nil_append, Tape.write, Tape.move, ListBlank.append_nil,
      ListBlank.append_cons, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.cons_zero_default,
      ListBlank.head_default_fin, ListBlank.tail_default,
      Option.map, Option.isNone]
    try rfl))

local macro "congr_vars" : tactic =>
  `(tactic| (
    refine congrArg _ (funext fun k => ?_)
    rcases k with _ | _ | _ | _ | k <;> (first | rfl | (simp -failIfUnchanged only []; omega))))

/-! ## Closed Pattern Set (Level A) -/

private def pat_0 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 .default)
    head := some D
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some D
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_3 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some F
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_4 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some A
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_5 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some F
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_6 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some F
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_7 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some A
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_8 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some A
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_9 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some F
    right := .default }

private def pat_10 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some F
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_11 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some A
    right := .default }

private def pat_12 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some D
    right := .default }

private def pat_13 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_14 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some B
    right := .default }

private def pat_15 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some D
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_16 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some C
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_17 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_18 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some B
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_19 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some B
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_20 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_21 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_22 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some F
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_23 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some F
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_24 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_25 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some D
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_26 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_27 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_28 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some D
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_29 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 0 (.rep [0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_30 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_31 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_32 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_33 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 1 (.sym 0 (.sym 0 (.rep [0] 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_34 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 0 (.rep [0] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2
             .default))))))) }

private def pat_35 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_36 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 1 (.sym 0 (.sym 0 (.rep [0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_37 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 1 (.sym 0 (.sym 0 (.rep [0] 0 (.sym 1 (.sym 0 (.rep [1,
      0] 1 (.sym 1 (.rep
             [1] 2 .default))))))))) }

private def pat_38 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some C
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_39 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some C
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_40 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some C
    right := .sym 0 (.sym 0 (.rep [0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_41 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 1 (.sym 0 (.sym 0 (.rep [0] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2
             .default)))))))) }

private def pat_42 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 .default)
    head := some E
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_43 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 .default)
    head := some E
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_44 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some C
    right := .sym 0 (.sym 0 (.rep [0] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2
             .default))))))) }

private def pat_45 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))
    head := some C
    right := .default }

private def pat_46 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_47 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))
    head := some C
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_48 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))
    head := some C
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_49 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_50 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))
    head := some E
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_51 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))
    head := some E
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_52 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))
    head := some D
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_53 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 .default)
    head := some B
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_54 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))
    head := some B
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_55 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some F
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_56 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))
    head := some F
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_57 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some A
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_58 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))
    head := some A
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_59 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some F
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_60 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some F
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_61 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))))))
    head := some F
    right := .sym 0 (.sym 1 (.rep [1] 2 .default)) }

private def pat_62 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))))))
    head := some F
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default))))) }

private def pat_63 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some A
    right := .sym 1 (.rep [1] 1 .default) }

/-- Canonical tape pattern
$E(a, b, c) := 0^\infty\,1\,(01)^{b+1}\,(11)^a\,111\,\mathrm{A}{>}\,1^{c+1}\,0^\infty$. -/
def pat_64 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1
            .default)))))))
    head := some A
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_65 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1
            .default)))))))
    head := some A
    right := .sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default)))) }

private def pat_66 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some F
    right := .default }

private def pat_67 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some F
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_68 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))))))
    head := some F
    right := .default }

private def pat_69 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))))))
    head := some F
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_70 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some A
    right := .default }

private def pat_71 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default))))
    head := some D
    right := .default }

private def pat_72 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default))))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_73 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1
            .default)))))))
    head := some A
    right := .default }

private def pat_74 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1
            .default)))))))
    head := some D
    right := .default }

private def pat_75 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1
            .default)))))))
    head := some D
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_76 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some B
    right := .default }

private def pat_77 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some D
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_78 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))))))
    head := some B
    right := .default }

private def pat_79 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))))))
    head := some D
    right := .sym 0 (.sym 1 (.rep [1] 2 .default)) }

private def pat_80 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_81 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some B
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_82 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_83 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1
            .default)))))))
    head := some C
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_84 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))
    head := some B
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_85 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1
            .default)))))))
    head := some B
    right := .sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default)))) }

private def pat_86 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some F
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_87 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some F
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_88 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_89 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))))))
    head := some D
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_90 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))
    head := some F
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_91 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))))))
    head := some F
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default))))) }

private def pat_92 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 .default)
    head := some D
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_93 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default))))
    head := some D
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_94 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_95 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1
            .default)))))))
    head := some D
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_96 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))
    head := some D
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_97 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1
            .default)))))))
    head := some D
    right := .sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default)))) }

private def pat_98 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_99 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_100 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default)))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_101 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 .default))))))
    head := some D
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default))))) }

/-- Closed pattern set containing the canonical pattern `pat_64`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_64, VarCond.true)]

private def ReachesTarget (s : TapePatternSet (Fin 2) (Fin 6))
    (cfg : Cfg (Fin 2) (Fin 6)) : Option (Cfg (Fin 2) (Fin 6)) → Prop
  | some cfg' => ReachesPlus target cfg cfg' ∧ IsInPatternSet s cfg'
  | none => ∃ cfg_h, ReachesPlus target cfg cfg_h ∧ (step target cfg_h).isNone

private theorem reachesTarget_to_exists {s : TapePatternSet (Fin 2) (Fin 6)}
    {cfg : Cfg (Fin 2) (Fin 6)} {t : Option (Cfg (Fin 2) (Fin 6))}
    (h : ReachesTarget s cfg t) :
    ∃ cfg', ReachesPlus target cfg cfg' ∧
      (IsInPatternSet s cfg' ∨ (step target cfg').isNone) := by
  cases t with
  | some cfg' => exact ⟨cfg', h.1, Or.inl h.2⟩
  | none =>
    rcases h with ⟨cfg_h, h1, h2⟩
    exact ⟨cfg_h, h1, Or.inr h2⟩

private theorem step_base {s : TapePatternSet (Fin 2) (Fin 6)}
    {cfg cfg' : Cfg (Fin 2) (Fin 6)} (h1 : step target cfg = some cfg')
    (h2 : IsInPatternSet s cfg') : ReachesTarget s cfg (some cfg') :=
  ⟨ReachesPlus.single h1, h2⟩

private theorem step_chain {s : TapePatternSet (Fin 2) (Fin 6)}
    {cfg cfg1 : Cfg (Fin 2) (Fin 6)} {t : Option (Cfg (Fin 2) (Fin 6))}
    (h1 : step target cfg = some cfg1) (h2 : ReachesTarget s cfg1 t) :
    ReachesTarget s cfg t := by
  cases t with
  | some cfg' => exact ⟨(ReachesPlus.single h1).trans h2.1, h2.2⟩
  | none =>
    rcases h2 with ⟨cfg_h, h2a, h2b⟩
    exact ⟨cfg_h, (ReachesPlus.single h1).trans h2a, h2b⟩

private theorem stepPlus_chain {s : TapePatternSet (Fin 2) (Fin 6)}
    {cfg cfg1 : Cfg (Fin 2) (Fin 6)} {t : Option (Cfg (Fin 2) (Fin 6))}
    (h1 : ReachesPlus target cfg cfg1) (h2 : ReachesTarget s cfg1 t) :
    ReachesTarget s cfg t := by
  cases t with
  | some cfg' => exact ⟨h1.trans h2.1, h2.2⟩
  | none =>
    rcases h2 with ⟨cfg_h, h2a, h2b⟩
    exact ⟨cfg_h, h1.trans h2a, h2b⟩

private theorem cast_target {s : TapePatternSet (Fin 2) (Fin 6)}
    {cfg : Cfg (Fin 2) (Fin 6)} {t1 t2 : Option (Cfg (Fin 2) (Fin 6))}
    (h_eq : t1 = t2) (h : ReachesTarget s cfg t2) :
    ReachesTarget s cfg t1 :=
  h_eq ▸ h

private theorem in_ps_64 (vars : ℕ → ℕ) :
    IsInPatternSet ps (evalTapePattern pat_64 vars) :=
  ⟨(pat_64, VarCond.true), List.Mem.head _, vars, rfl, trivial⟩

private def target_pat_61 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  some (evalTapePattern pat_64 (v3 (vars 0) (vars 1) (vars 2)))

private theorem step_pat_61 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_61 vars) (target_pat_61 vars) := by
  unfold target_pat_61
  refine step_base ?_ (in_ps_64 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [evalTapePattern, pat_61, pat_64, evalTapeExpr]; pat_step
private def target_pat_65 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_61 (v3 ((vars 0 + (vars 2)) + 1) (vars 1) (vars 3))

private theorem step_pat_65 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_65 vars) (target_pat_65 vars) := by
  induction h_vr : vars 2 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain ?_ (step_pat_61 (v3 (vars 0 + 1) (vars 1) (vars 3))))
    · dsimp only [target_pat_65]; congr_vars
    · dsimp only [evalTapePattern, pat_65, pat_61, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_62
      (v4 (vars 0 + 1) (vars 1) u (vars 3))) ?_ (step_chain ?_
        (ih (v4 (vars 0 + 1) (vars 1) u (vars 3)) rfl)))
    · dsimp only [target_pat_65]; congr_vars
    · dsimp only [evalTapePattern, pat_65, pat_62, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [evalTapePattern, pat_62, pat_65, evalTapeExpr]; pat_step
private def target_pat_62 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_65 (v4 (vars 0) (vars 1) (vars 2) (vars 3))

private theorem step_pat_62 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_62 vars) (target_pat_62 vars) := by
  unfold target_pat_62
  refine step_chain ?_ (step_pat_65 (v4 (vars 0) (vars 1) (vars 2) (vars 3)))
  dsimp only [evalTapePattern, pat_62, pat_65, evalTapeExpr]; pat_step
private def target_pat_58 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_61 (v3 0 (vars 0) (vars 2))
  | u + 1 => target_pat_62 (v4 0 (vars 0) u (vars 2))

private theorem step_pat_58 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_58 vars) (target_pat_58 vars) := by
  unfold target_pat_58
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_61 (v3 0 (vars 0) (vars 2)))
    dsimp only [evalTapePattern, pat_58, pat_61, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_62 (v4 0 (vars 0) u (vars 2)))
    dsimp only [evalTapePattern, pat_58, pat_62, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_56 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_58 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_56 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_56 vars) (target_pat_56 vars) := by
  unfold target_pat_56
  refine step_chain ?_ (step_pat_58 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [evalTapePattern, pat_56, pat_58, evalTapeExpr]; pat_step
private def target_pat_54 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_56 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_54 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_54 vars) (target_pat_54 vars) := by
  unfold target_pat_54
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_56 (v3 (vars 0) 0 (vars 2)))
    dsimp only [evalTapePattern, pat_54, pat_56, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_56 (v3 (vars 0) (u + 1) (vars 2)))
    dsimp only [evalTapePattern, pat_54, pat_56, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_45 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  none

private theorem step_pat_45 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_45 vars) (target_pat_45 vars) := by
  unfold target_pat_45
  refine ⟨evalTapePattern
    { left := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 .default))))
      head := some E
      right := .default } (v1 (vars 0)), ReachesPlus.single ?_, by pat_step⟩
  dsimp only [evalTapePattern, pat_45, evalTapeExpr]; pat_step
private def target_pat_42 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_45 (v1 0)
  | u + 1 => match u with
    | 0 => some (evalTapePattern pat_64 (v3 0 0 2))
    | u1 + 1 => match u1 with
      | 0 => target_pat_45 (v1 2)
      | u2 + 1 => target_pat_54 (v3 0 0 (u2 + 1))

private theorem step_pat_42 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_42 vars) (target_pat_42 vars) := by
  unfold target_pat_42
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_45 (v1 0))
    dsimp only [evalTapePattern, pat_42, pat_45, evalTapeExpr]; rw [h_vr]; pat_step
  · rcases u with _ | u1
    · refine ⟨?_, in_ps_64 _⟩
      dsimp only [pat_42, pat_64, evalTapePattern, evalTapeExpr]
      rw [h_vr]
      simp only [list_pow_zero, list_pow_succ, List.cons_append,
        List.nil_append, ListBlank.append_nil, ListBlank.append_cons]
      bb_steps
    · rcases u1 with _ | u2
      · refine stepPlus_chain ?_ (step_pat_45 (v1 2))
        dsimp only [pat_42, pat_45, evalTapePattern, evalTapeExpr]
        rw [h_vr]
        simp only [list_pow_zero, list_pow_succ, List.cons_append,
          List.nil_append, ListBlank.append_nil, ListBlank.append_cons]
        bb_steps
      · refine stepPlus_chain ?_
          (step_pat_54 (v3 0 0 (u2 + 1)))
        dsimp only [pat_42, pat_54, evalTapePattern, evalTapeExpr]
        rw [h_vr]
        simp only [list_pow_zero, list_pow_succ, List.cons_append,
          List.nil_append, ListBlank.append_nil, ListBlank.append_cons]
        bb_steps
private def target_pat_38 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_42 (v1 (vars 0))

private theorem step_pat_38 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_38 vars) (target_pat_38 vars) := by
  unfold target_pat_38
  refine step_chain ?_ (step_pat_42 (v1 (vars 0)))
  dsimp only [evalTapePattern, pat_38, pat_42, evalTapeExpr]; pat_step
private def target_pat_51 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_45 (v1 (((vars 0 + (vars 1)) + 1) + 1))
  | u + 1 => target_pat_54 (v3 (vars 0 + (vars 1)) 0 (u + 1))

private theorem step_pat_51 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_51 vars) (target_pat_51 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    rcases h_v2 : vars 2 with _ | u
    · refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_47 (v2 (vars 0 + 1) 0)) ?_
        (step_chain (cfg1 := evalTapePattern pat_50 (v2 (vars 0 + 1) 0)) ?_
          (step_chain ?_ (step_pat_45 (v1 ((vars 0 + 1) + 1))))))
      · dsimp only [target_pat_51]; rw [h_v2]; simp -failIfUnchanged only [];
        congr_vars
      · dsimp only [evalTapePattern, pat_51, pat_47, evalTapeExpr]; rw [h_vr, h_v2]; pat_step
      · dsimp only [evalTapePattern, pat_47, pat_50, evalTapeExpr]; pat_step
      · dsimp only [evalTapePattern, pat_50, pat_45, evalTapeExpr]; pat_step
    · refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_47 (v2 (vars 0 + 1) (u + 1)))
      ?_
        (step_chain (cfg1 := evalTapePattern pat_50 (v2 (vars 0 + 1) (u + 1))) ?_
          (step_chain (cfg1 := evalTapePattern pat_46 (v2 ((vars 0 + 1) + 1) u)) ?_
            (step_chain (cfg1 := evalTapePattern pat_49 (v2 (vars 0 + 1) (u + 1))) ?_
              (step_chain (cfg1 := evalTapePattern pat_52 (v2 (vars 0 + 1) (u + 1))) ?_
                (step_chain ?_ (step_pat_54 (v3 (vars 0) 0 (u + 1)))))))))
      · dsimp only [target_pat_51]; rw [h_v2]; simp -failIfUnchanged only [];
        congr_vars
      · dsimp only [evalTapePattern, pat_51, pat_47, evalTapeExpr]; rw [h_vr, h_v2]; pat_step
      · dsimp only [evalTapePattern, pat_47, pat_50, evalTapeExpr]; pat_step
      · dsimp only [evalTapePattern, pat_50, pat_46, evalTapeExpr]; pat_step
      · dsimp only [evalTapePattern, pat_46, pat_49, evalTapeExpr]; pat_step
      · dsimp only [evalTapePattern, pat_49, pat_52, evalTapeExpr]; pat_step
      · dsimp only [evalTapePattern, pat_52, pat_54, evalTapeExpr]; pat_step
  | succ u ih =>
    refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_48 (v3 (vars 0 + 1) u (vars 2)))
      ?_ (step_chain ?_ (ih
        (v3 (vars 0 + 1) u (vars 2)) rfl)))
    · dsimp only [target_pat_51]; cases vars 2 <;> simp -failIfUnchanged only [] <;> congr_vars
    · dsimp only [evalTapePattern, pat_51, pat_48, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [evalTapePattern, pat_48, pat_51, evalTapeExpr]; pat_step
private def target_pat_48 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_51 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_48 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_48 vars) (target_pat_48 vars) := by
  unfold target_pat_48
  refine step_chain ?_ (step_pat_51 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [evalTapePattern, pat_48, pat_51, evalTapeExpr]; pat_step
private def target_pat_40 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  none

private theorem step_pat_40 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_40 vars) (target_pat_40 vars) := by
  unfold target_pat_40
  rcases h_vr : vars 0 with _ | u
  · refine ⟨evalTapePattern
      { left := .sym 0 (.sym 1 .default)
        head := some E
        right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }
      (v1 (vars 1)), ReachesPlus.single ?_, by pat_step⟩
    dsimp only [evalTapePattern, pat_40, evalTapeExpr]; rw [h_vr]; pat_step
  · refine ⟨evalTapePattern
      { left := .sym 0 (.sym 1 .default)
        head := some E
        right := .sym 0 (.sym 0 (.rep [0] 0 (.sym 1 (.rep [1] 1 .default)))) }
      (v2 u (vars 1)), ReachesPlus.single ?_, by pat_step⟩
    dsimp only [evalTapePattern, pat_40, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_36 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_40 (v2 (vars 0) (vars 1))

private theorem step_pat_36 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_36 vars) (target_pat_36 vars) := by
  unfold target_pat_36
  refine step_chain ?_ (step_pat_40 (v2 (vars 0) (vars 1)))
  dsimp only [evalTapePattern, pat_36, pat_40, evalTapeExpr]; pat_step
private def target_pat_33 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_36 (v2 (vars 0) (vars 1))

private theorem step_pat_33 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_33 vars) (target_pat_33 vars) := by
  unfold target_pat_33
  refine step_chain ?_ (step_pat_36 (v2 (vars 0) (vars 1)))
  dsimp only [evalTapePattern, pat_33, pat_36, evalTapeExpr]; pat_step
private def target_pat_29 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_38 (v1 (vars 1))
  | u + 1 => target_pat_33 (v2 u (vars 1))

private theorem step_pat_29 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_29 vars) (target_pat_29 vars) := by
  unfold target_pat_29
  rcases h_vr : vars 0 with _ | u
  · refine step_chain (cfg1 := evalTapePattern pat_32 (v2 0 (vars 1))) ?_
      (step_chain (cfg1 := evalTapePattern pat_35 (v2 0 (vars 1))) ?_
        (step_chain ?_ (step_pat_38 (v1 (vars 1)))))
    · dsimp only [evalTapePattern, pat_29, pat_32, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [evalTapePattern, pat_32, pat_35, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_35, pat_38, evalTapeExpr]; pat_step
  · refine step_chain ?_ (step_pat_33 (v2 u (vars 1)))
    dsimp only [evalTapePattern, pat_29, pat_33, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_24 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_29 (v2 0 (vars 0))

private theorem step_pat_24 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_24 vars) (target_pat_24 vars) := by
  unfold target_pat_24
  refine step_chain ?_ (step_pat_29 (v2 0 (vars 0)))
  dsimp only [evalTapePattern, pat_24, pat_29, evalTapeExpr]; pat_step
private def target_pat_20 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_24 (v1 (vars 0))

private theorem step_pat_20 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_20 vars) (target_pat_20 vars) := by
  unfold target_pat_20
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_24 (v1 0))
    dsimp only [evalTapePattern, pat_20, pat_24, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_24 (v1 (u + 1)))
    dsimp only [evalTapePattern, pat_20, pat_24, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_16 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_20 (v1 ((vars 0) + 1))

private theorem step_pat_16 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_16 vars) (target_pat_16 vars) := by
  unfold target_pat_16
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_20 (v1 1))
    dsimp only [evalTapePattern, pat_16, pat_20, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_20 (v1 ((u + 1) + 1)))
    dsimp only [evalTapePattern, pat_16, pat_20, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_25 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_20 (v1 ((vars 0) + 1))

private theorem step_pat_25 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_25 vars) (target_pat_25 vars) := by
  unfold target_pat_25
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_20 (v1 1))
    dsimp only [evalTapePattern, pat_25, pat_20, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_20 (v1 ((u + 1) + 1)))
    dsimp only [evalTapePattern, pat_25, pat_20, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_21 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_25 (v1 ((2 * vars 0 + (vars 1)) + 1))

private theorem step_pat_21 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_21 vars) (target_pat_21 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    rcases h_vr : vars 1 with _ | u
    · refine cast_target ?_ (step_chain ?_ (step_pat_25 (v1 1)))
      · dsimp only [target_pat_21]; congr_vars
      · dsimp only [evalTapePattern, pat_21, pat_25, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine cast_target ?_ (step_chain ?_ (step_pat_25 (v1 ((u + 1) + 1))))
      · dsimp only [target_pat_21]; congr_vars
      · dsimp only [evalTapePattern, pat_21, pat_25, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  | succ v ih =>
    rcases h_vr : vars 1 with _ | u
    · refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_26 (v2 v 1)) ?_ (step_chain
        ?_ (ih (v2 v 2) rfl)))
      · dsimp only [target_pat_21]; congr_vars
      · dsimp only [evalTapePattern, pat_21, pat_26, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
      · dsimp only [evalTapePattern, pat_26, pat_21, evalTapeExpr]; pat_step
    · refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_26 (v2 v ((u + 1) + 1)))
        ?_ (step_chain ?_ (ih (v2 v (((u + 1) + 1) + 1)) rfl)))
      · dsimp only [target_pat_21]; congr_vars
      · dsimp only [evalTapePattern, pat_21, pat_26, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
      · dsimp only [evalTapePattern, pat_26, pat_21, evalTapeExpr]; pat_step
private def target_pat_17 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_21 (v2 (vars 0) ((vars 1) + 1))

private theorem step_pat_17 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_17 vars) (target_pat_17 vars) := by
  unfold target_pat_17
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_21 (v2 (vars 0) 1))
    dsimp only [evalTapePattern, pat_17, pat_21, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_21 (v2 (vars 0) ((u + 1) + 1)))
    dsimp only [evalTapePattern, pat_17, pat_21, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_14 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_16 (v1 1)
  | v + 1 => target_pat_17 (v2 v 1)

private theorem step_pat_14 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_14 vars) (target_pat_14 vars) := by
  unfold target_pat_14
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_16 (v1 1))
    dsimp only [evalTapePattern, pat_14, pat_16, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_ (step_pat_17 (v2 v 1))
    dsimp only [evalTapePattern, pat_14, pat_17, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_11 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_14 (v1 (vars 0 + 1))

private theorem step_pat_11 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_11 vars) (target_pat_11 vars) := by
  unfold target_pat_11
  refine step_chain ?_ (step_pat_14 (v1 (vars 0 + 1)))
  dsimp only [evalTapePattern, pat_11, pat_14, evalTapeExpr]; pat_step
private def target_pat_9 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_11 (v1 (vars 0))

private theorem step_pat_9 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_9 vars) (target_pat_9 vars) := by
  unfold target_pat_9
  refine step_chain ?_ (step_pat_11 (v1 (vars 0)))
  dsimp only [evalTapePattern, pat_9, pat_11, evalTapeExpr]; pat_step
private def target_pat_12 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_14 (v1 (vars 0))

private theorem step_pat_12 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_12 vars) (target_pat_12 vars) := by
  unfold target_pat_12
  refine step_chain ?_ (step_pat_14 (v1 (vars 0)))
  dsimp only [evalTapePattern, pat_12, pat_14, evalTapeExpr]; pat_step
private def target_pat_44 (_vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  none

private theorem step_pat_44 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_44 vars) (target_pat_44 vars) := by
  unfold target_pat_44
  rcases h_vr : vars 0 with _ | u
  · refine ⟨evalTapePattern
      { left := .sym 0 (.sym 1 .default)
        head := some E
        right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }
      (v2 (vars 1) (vars 2)), ReachesPlus.single ?_, by pat_step⟩
    dsimp only [evalTapePattern, pat_44, evalTapeExpr]; rw [h_vr]; pat_step
  · refine ⟨evalTapePattern
      { left := .sym 0 (.sym 1 .default)
        head := some E
        right := .sym 0 (.sym 0 (.rep [0] 0
          (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))))) }
      (v3 u (vars 1) (vars 2)), ReachesPlus.single ?_, by pat_step⟩
    dsimp only [evalTapePattern, pat_44, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_41 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_44 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_41 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_41 vars) (target_pat_41 vars) := by
  unfold target_pat_41
  refine step_chain ?_ (step_pat_44 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [evalTapePattern, pat_41, pat_44, evalTapeExpr]; pat_step
private def target_pat_37 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_41 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_37 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_37 vars) (target_pat_37 vars) := by
  unfold target_pat_37
  refine step_chain ?_ (step_pat_41 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [evalTapePattern, pat_37, pat_41, evalTapeExpr]; pat_step
private def target_pat_31 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_48 (v3 0 (vars 1 + (vars 0)) (vars 2))

private theorem step_pat_31 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_31 vars) (target_pat_31 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_18 (v2 (vars 1 + 1) (vars 2)))
      ?_
      (step_chain (cfg1 := evalTapePattern pat_22 (v2 (vars 1 + 1) (vars 2))) ?_
        (step_chain (cfg1 := evalTapePattern pat_27 (v2 (vars 1 + 1) (vars 2))) ?_
          (step_chain (cfg1 := evalTapePattern pat_30 (v2 (vars 1 + 1) (vars 2))) ?_
            (step_chain (cfg1 := evalTapePattern pat_34 (v3 0 (vars 1 + 1) (vars 2))) ?_
              (step_chain (cfg1 := evalTapePattern pat_32 (v2 ((vars 1 + 1) + 1) (vars 2))) ?_
                (step_chain (cfg1 := evalTapePattern pat_35 (v2 ((vars 1 + 1) + 1) (vars 2))) ?_
                  (step_chain (cfg1 := evalTapePattern pat_39 (v2 (vars 1 + 1) (vars 2))) ?_
                    (step_chain (cfg1 := evalTapePattern pat_43 (v2 (vars 1 + 1) (vars 2))) ?_
                      (step_chain ?_ (step_pat_48 (v3 0 (vars 1) (vars 2)))))))))))))
    · dsimp only [target_pat_31]; congr_vars
    · dsimp only [evalTapePattern, pat_31, pat_18, evalTapeExpr]; rw [h_vl]; pat_step
    · dsimp only [evalTapePattern, pat_18, pat_22, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_22, pat_27, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_27, pat_30, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_30, pat_34, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_34, pat_32, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_32, pat_35, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_35, pat_39, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_39, pat_43, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_43, pat_48, evalTapeExpr]; pat_step
  | succ v ih =>
    refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_19 (v3 v (vars 1 + 1) (vars
      2))) ?_
      (step_chain (cfg1 := evalTapePattern pat_23 (v3 v (vars 1 + 1) (vars 2))) ?_
        (step_chain (cfg1 := evalTapePattern pat_28 (v3 v (vars 1 + 1) (vars 2))) ?_
          (step_chain ?_ (ih (v3 v (vars 1 + 1) (vars 2)) rfl)))))
    · dsimp only [target_pat_31]; congr_vars
    · dsimp only [evalTapePattern, pat_31, pat_19, evalTapeExpr]; rw [h_vl]; pat_step
    · dsimp only [evalTapePattern, pat_19, pat_23, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_23, pat_28, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_28, pat_31, evalTapeExpr]; pat_step
private def target_pat_28 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_31 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_28 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_28 vars) (target_pat_28 vars) := by
  unfold target_pat_28
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_31 (v3 (vars 0) 0 (vars 2)))
    dsimp only [evalTapePattern, pat_28, pat_31, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_31 (v3 (vars 0) (u + 1) (vars 2)))
    dsimp only [evalTapePattern, pat_28, pat_31, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_23 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_28 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_23 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_23 vars) (target_pat_23 vars) := by
  unfold target_pat_23
  refine step_chain ?_ (step_pat_28 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [evalTapePattern, pat_23, pat_28, evalTapeExpr]; pat_step
private def target_pat_19 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_23 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_19 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_19 vars) (target_pat_19 vars) := by
  unfold target_pat_19
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_23 (v3 (vars 0) 0 (vars 2)))
    dsimp only [evalTapePattern, pat_19, pat_23, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_23 (v3 (vars 0) (u + 1) (vars 2)))
    dsimp only [evalTapePattern, pat_19, pat_23, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_7 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_9 (v1 (vars 0 + 1))
  | u + 1 => match u with
    | 0 => target_pat_12 (v1 (vars 0 + 1))
    | u' + 1 => target_pat_19 (v3 (vars 0) 0 u')

private theorem step_pat_7 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_7 vars) (target_pat_7 vars) := by
  unfold target_pat_7
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_9 (v1 (vars 0 + 1)))
    dsimp only [evalTapePattern, pat_7, pat_9, evalTapeExpr]; rw [h_vr]; pat_step
  · rcases u with _ | u'
    · refine step_chain (cfg1 := evalTapePattern pat_10 (v2 (vars 0 + 1) 0)) ?_
        (step_chain ?_ (step_pat_12 (v1 (vars 0 + 1))))
      · dsimp only [evalTapePattern, pat_7, pat_10, evalTapeExpr]; rw [h_vr]; pat_step
      · dsimp only [evalTapePattern, pat_10, pat_12, evalTapeExpr]; pat_step
    · refine step_chain (cfg1 := evalTapePattern pat_10 (v2 (vars 0 + 1) (u' + 1))) ?_
        (step_chain (cfg1 := evalTapePattern pat_13 (v2 (vars 0 + 1) u')) ?_
          (step_chain (cfg1 := evalTapePattern pat_15 (v2 (vars 0 + 1) u')) ?_
            (step_chain ?_ (step_pat_19 (v3 (vars 0) 0 u')))))
      · dsimp only [evalTapePattern, pat_7, pat_10, evalTapeExpr]; rw [h_vr]; pat_step
      · dsimp only [evalTapePattern, pat_10, pat_13, evalTapeExpr]; pat_step
      · dsimp only [evalTapePattern, pat_13, pat_15, evalTapeExpr]; pat_step
      · dsimp only [evalTapePattern, pat_15, pat_19, evalTapeExpr]; pat_step
private def target_pat_5 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_7 (v2 (vars 0) (vars 1))

private theorem step_pat_5 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_5 vars) (target_pat_5 vars) := by
  unfold target_pat_5
  refine step_chain ?_ (step_pat_7 (v2 (vars 0) (vars 1)))
  dsimp only [evalTapePattern, pat_5, pat_7, evalTapeExpr]; pat_step
private def target_pat_8 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_5 (v2 ((vars 0 + (vars 1)) + 1) (vars 2))

private theorem step_pat_8 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_8 vars) (target_pat_8 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain ?_ (step_pat_5 (v2 (vars 0 + 1) (vars 2))))
    · dsimp only [target_pat_8]; congr_vars
    · dsimp only [evalTapePattern, pat_8, pat_5, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_6 (v3 (vars 0 + 1) u (vars 2)))
      ?_ (step_chain ?_ (ih
        (v3 (vars 0 + 1) u (vars 2)) rfl)))
    · dsimp only [target_pat_8]; congr_vars
    · dsimp only [evalTapePattern, pat_8, pat_6, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [evalTapePattern, pat_6, pat_8, evalTapeExpr]; pat_step
private def target_pat_6 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_8 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_6 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_6 vars) (target_pat_6 vars) := by
  unfold target_pat_6
  refine step_chain ?_ (step_pat_8 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [evalTapePattern, pat_6, pat_8, evalTapeExpr]; pat_step
private def target_pat_4 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_5 (v2 0 (vars 1))
  | u + 1 => target_pat_6 (v3 0 u (vars 1))

private theorem step_pat_4 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_4 vars) (target_pat_4 vars) := by
  unfold target_pat_4
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_5 (v2 0 (vars 1)))
    dsimp only [evalTapePattern, pat_4, pat_5, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_6 (v3 0 u (vars 1)))
    dsimp only [evalTapePattern, pat_4, pat_6, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_3 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_4 (v2 (vars 0) (vars 1))

private theorem step_pat_3 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_3 vars) (target_pat_3 vars) := by
  unfold target_pat_3
  refine step_chain ?_ (step_pat_4 (v2 (vars 0) (vars 1)))
  dsimp only [evalTapePattern, pat_3, pat_4, evalTapeExpr]; pat_step
private def target_pat_2 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_3 (v2 (vars 0) (vars 1))

private theorem step_pat_2 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_2 vars) (target_pat_2 vars) := by
  unfold target_pat_2
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_3 (v2 0 (vars 1)))
    dsimp only [evalTapePattern, pat_2, pat_3, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_3 (v2 (u + 1) (vars 1)))
    dsimp only [evalTapePattern, pat_2, pat_3, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_1 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_2 (v2 0 (vars 0))

private theorem step_pat_1 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_1 vars) (target_pat_1 vars) := by
  unfold target_pat_1
  refine step_chain ?_ (step_pat_2 (v2 0 (vars 0)))
  dsimp only [evalTapePattern, pat_1, pat_2, evalTapeExpr]; pat_step
private def target_pat_0 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_1 (v1 (vars 0))

private theorem step_pat_0 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_0 vars) (target_pat_0 vars) := by
  unfold target_pat_0
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_1 (v1 0))
    dsimp only [evalTapePattern, pat_0, pat_1, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_1 (v1 (u + 1)))
    dsimp only [evalTapePattern, pat_0, pat_1, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_26 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_21 (v2 (vars 0) ((vars 1) + 1))

private theorem step_pat_26 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_26 vars) (target_pat_26 vars) := by
  unfold target_pat_26
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_21 (v2 (vars 0) 1))
    dsimp only [evalTapePattern, pat_26, pat_21, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_21 (v2 (vars 0) ((u + 1) + 1)))
    dsimp only [evalTapePattern, pat_26, pat_21, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_80 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
    | 0 => target_pat_25 (v1 ((vars 1) + 1))
    | v + 1 => target_pat_26 (v2 v ((vars 1) + 1))

private theorem step_pat_80 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_80 vars) (target_pat_80 vars) := by
  unfold target_pat_80
  rcases h_vr : vars 1 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_25 (v1 1))
      dsimp only [evalTapePattern, pat_80, pat_25, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_26 (v2 v 1))
      dsimp only [evalTapePattern, pat_80, pat_26, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_25 (v1 ((u + 1) + 1)))
      dsimp only [evalTapePattern, pat_80, pat_25, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_26 (v2 v ((u + 1) + 1)))
      dsimp only [evalTapePattern, pat_80, pat_26, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
private def target_pat_76 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_80 (v2 (vars 0) 1)

private theorem step_pat_76 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_76 vars) (target_pat_76 vars) := by
  unfold target_pat_76
  refine step_chain ?_ (step_pat_80 (v2 (vars 0) 1))
  dsimp only [evalTapePattern, pat_76, pat_80, evalTapeExpr]; pat_step
private def target_pat_70 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_76 (v1 (vars 0))

private theorem step_pat_70 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_70 vars) (target_pat_70 vars) := by
  unfold target_pat_70
  refine step_chain ?_ (step_pat_76 (v1 (vars 0)))
  dsimp only [evalTapePattern, pat_70, pat_76, evalTapeExpr]; pat_step
private def target_pat_66 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_70 (v1 (vars 0 + 1))

private theorem step_pat_66 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_66 vars) (target_pat_66 vars) := by
  unfold target_pat_66
  refine step_chain ?_ (step_pat_70 (v1 (vars 0 + 1)))
  dsimp only [evalTapePattern, pat_66, pat_70, evalTapeExpr]; pat_step
private def target_pat_71 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_76 (v1 (vars 0))

private theorem step_pat_71 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_71 vars) (target_pat_71 vars) := by
  unfold target_pat_71
  refine step_chain ?_ (step_pat_76 (v1 (vars 0)))
  dsimp only [evalTapePattern, pat_71, pat_76, evalTapeExpr]; pat_step
private def target_pat_98 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_2 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_98 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_98 vars) (target_pat_98 vars) := by
  unfold target_pat_98
  refine step_chain ?_ (step_pat_2 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [evalTapePattern, pat_98, pat_2, evalTapeExpr]; pat_step
private def target_pat_92 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_98 (v2 (vars 0) (vars 1))

private theorem step_pat_92 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_92 vars) (target_pat_92 vars) := by
  unfold target_pat_92
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_98 (v2 0 (vars 1)))
    dsimp only [evalTapePattern, pat_92, pat_98, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_98 (v2 (u + 1) (vars 1)))
    dsimp only [evalTapePattern, pat_92, pat_98, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_86 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_92 (v2 (vars 0) (vars 1))

private theorem step_pat_86 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_86 vars) (target_pat_86 vars) := by
  unfold target_pat_86
  refine step_chain ?_ (step_pat_92 (v2 (vars 0) (vars 1)))
  dsimp only [evalTapePattern, pat_86, pat_92, evalTapeExpr]; pat_step
private def target_pat_81 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_86 (v2 (vars 0 + (vars 1)) (vars 2))

private theorem step_pat_81 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_81 vars) (target_pat_81 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    rcases h_vr : vars 1 with _ | u
    · refine cast_target ?_ (step_chain ?_ (step_pat_86 (v2 0 (vars 2))))
      · dsimp only [target_pat_81]; congr_vars
      · dsimp only [evalTapePattern, pat_81, pat_86, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine cast_target ?_ (step_chain ?_ (step_pat_86 (v2 (u + 1) (vars 2))))
      · dsimp only [target_pat_81]; congr_vars
      · dsimp only [evalTapePattern, pat_81, pat_86, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  | succ v ih =>
    rcases h_vr : vars 1 with _ | u
    · refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_87 (v3 v 0 (vars 2))) ?_
        (step_chain (cfg1 := evalTapePattern pat_93 (v3 v 0 (vars 2))) ?_
          (step_chain (cfg1 := evalTapePattern pat_99 (v3 v 0 (vars 2))) ?_
            (step_chain ?_ (ih (v3 v 1 (vars 2)) rfl)))))
      · dsimp only [target_pat_81]; congr_vars
      · dsimp only [evalTapePattern, pat_81, pat_87, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
      · dsimp only [evalTapePattern, pat_87, pat_93, evalTapeExpr]; pat_step
      · dsimp only [evalTapePattern, pat_93, pat_99, evalTapeExpr]; pat_step
      · dsimp only [evalTapePattern, pat_99, pat_81, evalTapeExpr]; pat_step
    · refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_87 (v3 v (u + 1) (vars 2))) ?_
        (step_chain (cfg1 := evalTapePattern pat_93 (v3 v (u + 1) (vars 2))) ?_
          (step_chain (cfg1 := evalTapePattern pat_99 (v3 v (u + 1) (vars 2))) ?_
            (step_chain ?_ (ih (v3 v ((u + 1) + 1) (vars 2)) rfl)))))
      · dsimp only [target_pat_81]; congr_vars
      · dsimp only [evalTapePattern, pat_81, pat_87, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
      · dsimp only [evalTapePattern, pat_87, pat_93, evalTapeExpr]; pat_step
      · dsimp only [evalTapePattern, pat_93, pat_99, evalTapeExpr]; pat_step
      · dsimp only [evalTapePattern, pat_99, pat_81, evalTapeExpr]; pat_step
private def target_pat_77 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_81 (v3 (vars 0) 0 (vars 1))

private theorem step_pat_77 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_77 vars) (target_pat_77 vars) := by
  unfold target_pat_77
  refine step_chain ?_ (step_pat_81 (v3 (vars 0) 0 (vars 1)))
  dsimp only [evalTapePattern, pat_77, pat_81, evalTapeExpr]; pat_step
private def target_pat_72 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_77 (v2 (vars 0) (vars 1))

private theorem step_pat_72 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_72 vars) (target_pat_72 vars) := by
  unfold target_pat_72
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_77 (v2 (vars 0) 0))
    dsimp only [evalTapePattern, pat_72, pat_77, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_77 (v2 (vars 0) (u + 1)))
    dsimp only [evalTapePattern, pat_72, pat_77, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_67 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_71 (v1 (vars 0))
  | u + 1 => target_pat_72 (v2 (vars 0) u)

private theorem step_pat_67 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_67 vars) (target_pat_67 vars) := by
  unfold target_pat_67
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_71 (v1 (vars 0)))
    dsimp only [evalTapePattern, pat_67, pat_71, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_72 (v2 (vars 0) u))
    dsimp only [evalTapePattern, pat_67, pat_72, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_63 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_66 (v1 (vars 0))
  | u + 1 => target_pat_67 (v2 (vars 0) u)

private theorem step_pat_63 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_63 vars) (target_pat_63 vars) := by
  unfold target_pat_63
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_66 (v1 (vars 0)))
    dsimp only [evalTapePattern, pat_63, pat_66, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_67 (v2 (vars 0) u))
    dsimp only [evalTapePattern, pat_63, pat_67, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_59 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_63 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_59 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_59 vars) (target_pat_59 vars) := by
  unfold target_pat_59
  refine step_chain ?_ (step_pat_63 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [evalTapePattern, pat_59, pat_63, evalTapeExpr]; pat_step
private def target_pat_57 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_59 (v2 (vars 0 + (vars 1)) (vars 2))

private theorem step_pat_57 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_57 vars) (target_pat_57 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain ?_ (step_pat_59 (v2 (vars 0) (vars 2))))
    · dsimp only [target_pat_57]; congr_vars
    · dsimp only [evalTapePattern, pat_57, pat_59, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_60 (v3 (vars 0) u (vars 2)))
      ?_ (step_chain ?_ (ih (v3 (vars 0 + 1) u (vars 2)) rfl)))
    · dsimp only [target_pat_57]; congr_vars
    · dsimp only [evalTapePattern, pat_57, pat_60, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [evalTapePattern, pat_60, pat_57, evalTapeExpr]; pat_step
private def target_pat_55 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_57 (v3 0 (vars 0) (vars 1))

private theorem step_pat_55 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_55 vars) (target_pat_55 vars) := by
  unfold target_pat_55
  refine step_chain ?_ (step_pat_57 (v3 0 (vars 0) (vars 1)))
  dsimp only [evalTapePattern, pat_55, pat_57, evalTapeExpr]; pat_step
private def target_pat_53 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_55 (v2 (vars 0) (vars 1))

private theorem step_pat_53 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_53 vars) (target_pat_53 vars) := by
  unfold target_pat_53
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_55 (v2 0 (vars 1)))
    dsimp only [evalTapePattern, pat_53, pat_55, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_55 (v2 (u + 1) (vars 1)))
    dsimp only [evalTapePattern, pat_53, pat_55, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_52 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_53 (v2 0 (vars 1))
  | v + 1 => target_pat_54 (v3 v 0 (vars 1))

private theorem step_pat_52 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_52 vars) (target_pat_52 vars) := by
  unfold target_pat_52
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_53 (v2 0 (vars 1)))
    dsimp only [evalTapePattern, pat_52, pat_53, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_ (step_pat_54 (v3 v 0 (vars 1)))
    dsimp only [evalTapePattern, pat_52, pat_54, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_49 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_52 (v2 (vars 0) (vars 1))

private theorem step_pat_49 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_49 vars) (target_pat_49 vars) := by
  unfold target_pat_49
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_52 (v2 (vars 0) 0))
    dsimp only [evalTapePattern, pat_49, pat_52, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_52 (v2 (vars 0) (u + 1)))
    dsimp only [evalTapePattern, pat_49, pat_52, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_46 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
    | 0 => target_pat_0 (v1 ((vars 1) + 1))
    | v + 1 => target_pat_49 (v2 v ((vars 1) + 1))

private theorem step_pat_46 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_46 vars) (target_pat_46 vars) := by
  unfold target_pat_46
  rcases h_vr : vars 1 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_0 (v1 1))
      dsimp only [evalTapePattern, pat_46, pat_0, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_49 (v2 v 1))
      dsimp only [evalTapePattern, pat_46, pat_49, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_0 (v1 ((u + 1) + 1)))
      dsimp only [evalTapePattern, pat_46, pat_0, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_49 (v2 v ((u + 1) + 1)))
      dsimp only [evalTapePattern, pat_46, pat_49, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
private def target_pat_60 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_57 (v3 (vars 0 + 1) (vars 1) (vars 2))

private theorem step_pat_60 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_60 vars) (target_pat_60 vars) := by
  unfold target_pat_60
  refine step_chain ?_ (step_pat_57 (v3 (vars 0 + 1) (vars 1) (vars 2)))
  dsimp only [evalTapePattern, pat_60, pat_57, evalTapeExpr]; pat_step
private def target_pat_88 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
    | 0 => target_pat_0 (v1 ((vars 1) + 1))
    | v + 1 => target_pat_49 (v2 v ((vars 1) + 1))

private theorem step_pat_88 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_88 vars) (target_pat_88 vars) := by
  unfold target_pat_88
  rcases h_vr : vars 1 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_0 (v1 1))
      dsimp only [evalTapePattern, pat_88, pat_0, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_49 (v2 v 1))
      dsimp only [evalTapePattern, pat_88, pat_49, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_0 (v1 ((u + 1) + 1)))
      dsimp only [evalTapePattern, pat_88, pat_0, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_49 (v2 v ((u + 1) + 1)))
      dsimp only [evalTapePattern, pat_88, pat_49, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
private def target_pat_82 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_88 (v2 (vars 0) ((vars 1) + 1))

private theorem step_pat_82 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_82 vars) (target_pat_82 vars) := by
  unfold target_pat_82
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_88 (v2 (vars 0) 1))
    dsimp only [evalTapePattern, pat_82, pat_88, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_88 (v2 (vars 0) ((u + 1) + 1)))
    dsimp only [evalTapePattern, pat_82, pat_88, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_94 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_88 (v2 (vars 0) ((vars 1) + 1))

private theorem step_pat_94 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_94 vars) (target_pat_94 vars) := by
  unfold target_pat_94
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_88 (v2 (vars 0) 1))
    dsimp only [evalTapePattern, pat_94, pat_88, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_88 (v2 (vars 0) ((u + 1) + 1)))
    dsimp only [evalTapePattern, pat_94, pat_88, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_89 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_94 (v2 (vars 1) ((2 * vars 0 + (vars 2)) + 1))

private theorem step_pat_89 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_89 vars) (target_pat_89 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    rcases h_vr : vars 2 with _ | u
    · refine cast_target ?_ (step_chain ?_ (step_pat_94 (v2 (vars 1) 1)))
      · dsimp only [target_pat_89]; congr_vars
      · dsimp only [evalTapePattern, pat_89, pat_94, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine cast_target ?_ (step_chain ?_ (step_pat_94 (v2 (vars 1) ((u + 1) + 1))))
      · dsimp only [target_pat_89]; congr_vars
      · dsimp only [evalTapePattern, pat_89, pat_94, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  | succ v ih =>
    rcases h_vr : vars 2 with _ | u
    · refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_95 (v3 v (vars 1) 1))
        ?_ (step_chain ?_ (ih (v3 v (vars 1) ((0 + 1) + 1)) rfl)))
      · dsimp only [target_pat_89]; congr_vars
      · dsimp only [evalTapePattern, pat_89, pat_95, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
      · dsimp only [evalTapePattern, pat_95, pat_89, evalTapeExpr]; pat_step
    · refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_95
        (v3 v (vars 1) ((u + 1) + 1))) ?_ (step_chain ?_ (ih
          (v3 v (vars 1) (((u + 1) + 1) + 1)) rfl)))
      · dsimp only [target_pat_89]; congr_vars
      · dsimp only [evalTapePattern, pat_89, pat_95, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
      · dsimp only [evalTapePattern, pat_95, pat_89, evalTapeExpr]; pat_step
private def target_pat_83 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_89 (v3 (vars 0) (vars 1) ((vars 2) + 1))

private theorem step_pat_83 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_83 vars) (target_pat_83 vars) := by
  unfold target_pat_83
  rcases h_vr : vars 2 with _ | u
  · refine step_chain ?_ (step_pat_89 (v3 (vars 0) (vars 1) 1))
    dsimp only [evalTapePattern, pat_83, pat_89, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_89 (v3 (vars 0) (vars 1) ((u + 1) + 1)))
    dsimp only [evalTapePattern, pat_83, pat_89, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_78 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_82 (v2 (vars 1) 1)
  | v + 1 => target_pat_83 (v3 v (vars 1) 1)

private theorem step_pat_78 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_78 vars) (target_pat_78 vars) := by
  unfold target_pat_78
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_82 (v2 (vars 1) 1))
    dsimp only [evalTapePattern, pat_78, pat_82, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_ (step_pat_83 (v3 v (vars 1) 1))
    dsimp only [evalTapePattern, pat_78, pat_83, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_73 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_78 (v2 (vars 0 + 1) (vars 1))

private theorem step_pat_73 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_73 vars) (target_pat_73 vars) := by
  unfold target_pat_73
  refine step_chain ?_ (step_pat_78 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [evalTapePattern, pat_73, pat_78, evalTapeExpr]; pat_step
private def target_pat_68 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_73 (v2 (vars 0) (vars 1))

private theorem step_pat_68 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_68 vars) (target_pat_68 vars) := by
  unfold target_pat_68
  refine step_chain ?_ (step_pat_73 (v2 (vars 0) (vars 1)))
  dsimp only [evalTapePattern, pat_68, pat_73, evalTapeExpr]; pat_step
private def target_pat_74 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_78 (v2 (vars 0) (vars 1))

private theorem step_pat_74 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_74 vars) (target_pat_74 vars) := by
  unfold target_pat_74
  refine step_chain ?_ (step_pat_78 (v2 (vars 0) (vars 1)))
  dsimp only [evalTapePattern, pat_74, pat_78, evalTapeExpr]; pat_step
private def target_pat_100 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_53 (v2 (vars 1 + 1) (vars 2))
  | v + 1 => target_pat_54 (v3 v (vars 1 + 1) (vars 2))

private theorem step_pat_100 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_100 vars) (target_pat_100 vars) := by
  unfold target_pat_100
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_53 (v2 (vars 1 + 1) (vars 2)))
    dsimp only [evalTapePattern, pat_100, pat_53, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_ (step_pat_54 (v3 v (vars 1 + 1) (vars 2)))
    dsimp only [evalTapePattern, pat_100, pat_54, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_96 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_100 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_96 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_96 vars) (target_pat_96 vars) := by
  unfold target_pat_96
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_100 (v3 (vars 0) 0 (vars 2)))
    dsimp only [evalTapePattern, pat_96, pat_100, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_100 (v3 (vars 0) (u + 1) (vars 2)))
    dsimp only [evalTapePattern, pat_96, pat_100, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_90 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_96 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_90 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_90 vars) (target_pat_90 vars) := by
  unfold target_pat_90
  refine step_chain ?_ (step_pat_96 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [evalTapePattern, pat_90, pat_96, evalTapeExpr]; pat_step
private def target_pat_84 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_90 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_84 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_84 vars) (target_pat_84 vars) := by
  unfold target_pat_84
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_90 (v3 (vars 0) 0 (vars 2)))
    dsimp only [evalTapePattern, pat_84, pat_90, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_90 (v3 (vars 0) (u + 1) (vars 2)))
    dsimp only [evalTapePattern, pat_84, pat_90, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_101 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_84 (v3 (vars 1) ((vars 2 + (vars 0)) + 1) (vars 3))

private theorem step_pat_101 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_101 vars) (target_pat_101 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain ?_ (step_pat_84 (v3 (vars 1) (vars 2 + 1) (vars 3))))
    · dsimp only [target_pat_101]; congr_vars
    · dsimp only [evalTapePattern, pat_101, pat_84, evalTapeExpr]; rw [h_vl]; pat_step
  | succ v ih =>
    refine cast_target ?_ (step_chain (cfg1 := evalTapePattern pat_85
      (v4 v (vars 1) (vars 2 + 1) (vars 3))) ?_
      (step_chain (cfg1 := evalTapePattern pat_91 (v4 v (vars 1) (vars 2 + 1) (vars 3))) ?_
        (step_chain (cfg1 := evalTapePattern pat_97 (v4 v (vars 1) (vars 2 + 1) (vars 3))) ?_
          (step_chain ?_ (ih (v4 v (vars 1) (vars 2 + 1) (vars 3)) rfl)))))
    · dsimp only [target_pat_101]; congr_vars
    · dsimp only [evalTapePattern, pat_101, pat_85, evalTapeExpr]; rw [h_vl]; pat_step
    · dsimp only [evalTapePattern, pat_85, pat_91, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_91, pat_97, evalTapeExpr]; pat_step
    · dsimp only [evalTapePattern, pat_97, pat_101, evalTapeExpr]; pat_step
private def target_pat_97 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_101 (v4 (vars 0) (vars 1) (vars 2) (vars 3))

private theorem step_pat_97 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_97 vars) (target_pat_97 vars) := by
  unfold target_pat_97
  rcases h_vr : vars 2 with _ | u
  · refine step_chain ?_ (step_pat_101 (v4 (vars 0) (vars 1) 0 (vars 3)))
    dsimp only [evalTapePattern, pat_97, pat_101, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_101 (v4 (vars 0) (vars 1) (u + 1) (vars 3)))
    dsimp only [evalTapePattern, pat_97, pat_101, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_91 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_97 (v4 (vars 0) (vars 1) (vars 2) (vars 3))

private theorem step_pat_91 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_91 vars) (target_pat_91 vars) := by
  unfold target_pat_91
  refine step_chain ?_ (step_pat_97 (v4 (vars 0) (vars 1) (vars 2) (vars 3)))
  dsimp only [evalTapePattern, pat_91, pat_97, evalTapeExpr]; pat_step
private def target_pat_85 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_91 (v4 (vars 0) (vars 1) (vars 2) (vars 3))

private theorem step_pat_85 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_85 vars) (target_pat_85 vars) := by
  unfold target_pat_85
  rcases h_vr : vars 2 with _ | u
  · refine step_chain ?_ (step_pat_91 (v4 (vars 0) (vars 1) 0 (vars 3)))
    dsimp only [evalTapePattern, pat_85, pat_91, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_91 (v4 (vars 0) (vars 1) (u + 1) (vars 3)))
    dsimp only [evalTapePattern, pat_85, pat_91, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_79 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_84 (v3 (vars 1) 0 (vars 2))
  | v + 1 => target_pat_85 (v4 v (vars 1) 0 (vars 2))

private theorem step_pat_79 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_79 vars) (target_pat_79 vars) := by
  unfold target_pat_79
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_84 (v3 (vars 1) 0 (vars 2)))
    dsimp only [evalTapePattern, pat_79, pat_84, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_ (step_pat_85 (v4 v (vars 1) 0 (vars 2)))
    dsimp only [evalTapePattern, pat_79, pat_85, evalTapeExpr]; rw [h_vl]; pat_step
private def target_pat_75 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_79 (v3 (vars 0) (vars 1) (vars 2))

private theorem step_pat_75 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_75 vars) (target_pat_75 vars) := by
  unfold target_pat_75
  rcases h_vr : vars 2 with _ | u
  · refine step_chain ?_ (step_pat_79 (v3 (vars 0) (vars 1) 0))
    dsimp only [evalTapePattern, pat_75, pat_79, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_79 (v3 (vars 0) (vars 1) (u + 1)))
    dsimp only [evalTapePattern, pat_75, pat_79, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_69 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_74 (v2 (vars 0) (vars 1))
  | u + 1 => target_pat_75 (v3 (vars 0) (vars 1) u)

private theorem step_pat_69 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_69 vars) (target_pat_69 vars) := by
  unfold target_pat_69
  rcases h_vr : vars 2 with _ | u
  · refine step_chain ?_ (step_pat_74 (v2 (vars 0) (vars 1)))
    dsimp only [evalTapePattern, pat_69, pat_74, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_75 (v3 (vars 0) (vars 1) u))
    dsimp only [evalTapePattern, pat_69, pat_75, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_64 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_68 (v2 (vars 0 + 1) (vars 1))
  | u + 1 => target_pat_69 (v3 (vars 0 + 1) (vars 1) u)

private theorem step_pat_64 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_64 vars) (target_pat_64 vars) := by
  unfold target_pat_64
  rcases h_vr : vars 2 with _ | u
  · refine step_chain ?_ (step_pat_68 (v2 (vars 0 + 1) (vars 1)))
    dsimp only [evalTapePattern, pat_64, pat_68, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_69 (v3 (vars 0 + 1) (vars 1) u))
    dsimp only [evalTapePattern, pat_64, pat_69, evalTapeExpr]; rw [h_vr]; pat_step
private def target_pat_95 (vars : Nat → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_89 (v3 (vars 0) (vars 1) ((vars 2) + 1))

private theorem step_pat_95 (vars : Nat → Nat) :
    ReachesTarget ps (evalTapePattern pat_95 vars) (target_pat_95 vars) := by
  unfold target_pat_95
  rcases h_vr : vars 2 with _ | u
  · refine step_chain ?_ (step_pat_89 (v3 (vars 0) (vars 1) 1))
    dsimp only [evalTapePattern, pat_95, pat_89, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_89 (v3 (vars 0) (vars 1) ((u + 1) + 1)))
    dsimp only [evalTapePattern, pat_95, pat_89, evalTapeExpr]; rw [h_vr]; pat_step
private theorem init_reaches_pat_64 :
    ReachesStar target (init [])
      (evalTapePattern pat_64 fun k => match k with | 0 => 0 | 1 => 0 | 2 => 2 | _ => 0) := by
  dsimp only [pat_64, evalTapePattern, evalTapeExpr]
  simp only [list_pow_zero, list_pow_succ, List.cons_append,
    List.nil_append, ListBlank.append_nil, ListBlank.append_cons]
  bb_steps

private theorem init_reaches_ps :
    ∃ cfg₀, ReachesStar target (init []) cfg₀ ∧ IsInPatternSet ps cfg₀ :=
  ⟨_, init_reaches_pat_64, in_ps_64 _⟩

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨init_reaches_ps, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · exact reachesTarget_to_exists (step_pat_64 vars)
  · nomatch h_mem

/-- `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Concrete-Target Macro-Transition Rules and Level B Acceleration -/

/-- Canonical configuration
$E(a, b, c) := 0^\infty\,1\,(01)^{b+1}\,(11)^a\,111\,\mathrm{A}{>}\,1^{c+1}\,0^\infty$. -/
private def cfg_E (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  evalTapePattern pat_64 (v3 a b c)

local macro "unfold_targets" : tactic =>
  `(tactic| dsimp only [cfg_E, target_pat_61, target_pat_65, target_pat_62, target_pat_58,
    target_pat_56, target_pat_54, target_pat_45, target_pat_42, target_pat_38, target_pat_51,
    target_pat_48, target_pat_40, target_pat_36, target_pat_33, target_pat_29, target_pat_24,
    target_pat_20, target_pat_16, target_pat_25, target_pat_21, target_pat_17, target_pat_14,
    target_pat_11, target_pat_9, target_pat_12, target_pat_44, target_pat_41, target_pat_37,
    target_pat_31, target_pat_28, target_pat_23, target_pat_19, target_pat_7, target_pat_5,
    target_pat_8, target_pat_6, target_pat_4, target_pat_3, target_pat_2, target_pat_1,
    target_pat_0, target_pat_26, target_pat_80, target_pat_76, target_pat_70, target_pat_66,
    target_pat_71, target_pat_98, target_pat_92, target_pat_86, target_pat_81, target_pat_77,
    target_pat_72, target_pat_67, target_pat_63, target_pat_59, target_pat_57, target_pat_55,
    target_pat_53, target_pat_52, target_pat_49, target_pat_46, target_pat_60, target_pat_88,
    target_pat_82, target_pat_94, target_pat_89, target_pat_83, target_pat_78, target_pat_73,
    target_pat_68, target_pat_74, target_pat_100, target_pat_96, target_pat_90, target_pat_84,
    target_pat_101, target_pat_97, target_pat_91, target_pat_85, target_pat_79, target_pat_75,
    target_pat_69, target_pat_64, target_pat_95])

private theorem rule_1 (a : ℕ) :
    ReachesPlus target (cfg_E a 0 0) (cfg_E 0 0 (2 * a + 5)) := by
  have h := step_pat_64 (v3 a 0 0)
  have h_t :
      target_pat_64 (v3 a 0 0) =
        some (cfg_E 0 0 (2 * a + 5)) := by
    unfold_targets
    refine congrArg some (congrArg (evalTapePattern pat_64) (funext fun k => ?_))
    rcases k with _ | _ | _ | _ | k <;> rfl
  rw [h_t] at h
  exact h.1

private theorem rule_2 (a : ℕ) :
    ReachesPlus target (cfg_E a 0 1) (cfg_E 0 0 (2 * a + 3)) := by
  have h := step_pat_64 (v3 a 0 1)
  have h_t :
      target_pat_64 (v3 a 0 1) =
        some (cfg_E 0 0 (2 * a + 3)) := rfl
  rw [h_t] at h
  exact h.1

private theorem rule_3 (a : ℕ) :
    ReachesPlus target (cfg_E a 0 2) (cfg_E 0 0 (2 * a + 9)) := by
  have h := step_pat_64 (v3 a 0 2)
  have h_t :
      target_pat_64 (v3 a 0 2) =
        some (cfg_E 0 0 (2 * a + 9)) := by
    unfold_targets
    refine congrArg some (congrArg (evalTapePattern pat_64) (funext fun k => ?_))
    rcases k with _ | _ | _ | _ | k <;>
      (first | rfl | (simp -failIfUnchanged only [Nat.add_eq]; omega))
  rw [h_t] at h
  exact h.1

private theorem rule_4 (a : ℕ) :
    ReachesPlus target (cfg_E a 0 3) (cfg_E 0 0 (2 * a + 7)) := by
  have h := step_pat_64 (v3 a 0 3)
  have h_t :
      target_pat_64 (v3 a 0 3) =
        some (cfg_E 0 0 (2 * a + 7)) := by
    unfold_targets
    refine congrArg some (congrArg (evalTapePattern pat_64) (funext fun k => ?_))
    rcases k with _ | _ | _ | _ | k <;>
      (first | rfl | (simp -failIfUnchanged only [Nat.add_eq]; omega))
  rw [h_t] at h
  exact h.1

private theorem rule_5 (a : ℕ) :
    ReachesPlus target (cfg_E a 0 4) (cfg_E 0 0 (2 * a + 12)) := by
  have h := step_pat_64 (v3 a 0 4)
  have h_t :
      target_pat_64 (v3 a 0 4) =
        some (cfg_E 0 0 (2 * a + 12)) := by
    unfold_targets
    refine congrArg some (congrArg (evalTapePattern pat_64) (funext fun k => ?_))
    rcases k with _ | _ | _ | _ | k <;>
      (first | rfl | (simp -failIfUnchanged only [Nat.add_eq]; omega))
  rw [h_t] at h
  exact h.1

private theorem rule_6 (a : ℕ) :
    ReachesPlus target (cfg_E a 0 5) (cfg_E 0 0 (2 * a + 10)) := by
  have h := step_pat_64 (v3 a 0 5)
  have h_t :
      target_pat_64 (v3 a 0 5) =
        some (cfg_E 0 0 (2 * a + 10)) := by
    unfold_targets
    refine congrArg some (congrArg (evalTapePattern pat_64) (funext fun k => ?_))
    rcases k with _ | _ | _ | _ | k <;>
      (first | rfl | (simp -failIfUnchanged only [Nat.add_eq]; omega))
  rw [h_t] at h
  exact h.1

private theorem rule_7 (a : ℕ) :
    ∃ cfg_h, ReachesPlus target (cfg_E a 0 6) cfg_h ∧ (step target cfg_h).isNone := by
  have h := step_pat_64 (v3 a 0 6)
  have h_t :
      target_pat_64 (v3 a 0 6) = none := rfl
  rw [h_t] at h
  exact h

private theorem rule_8 (a c : ℕ) :
    ReachesPlus target (cfg_E a 0 (c + 7)) (cfg_E 0 (a + 4) (c + 1)) := by
  have h := step_pat_64 (v3 a 0 (c + 7))
  have h_t :
      target_pat_64 (v3 a 0 (c + 7)) =
        some (cfg_E 0 (a + 4) (c + 1)) := by
    unfold_targets
    refine congrArg some (congrArg (evalTapePattern pat_64) (funext fun k => ?_))
    rcases k with _ | _ | _ | _ | k <;>
      (first | rfl | (simp -failIfUnchanged only []; omega))
  rw [h_t] at h
  exact h.1

private theorem rule_9 (a : ℕ) :
    ReachesPlus target (cfg_E a 1 0) (cfg_E 0 2 (2 * a + 3)) := by
  have h := step_pat_64 (v3 a 1 0)
  have h_t :
      target_pat_64 (v3 a 1 0) =
        some (cfg_E 0 2 (2 * a + 3)) := by
    unfold_targets
    refine congrArg some (congrArg (evalTapePattern pat_64) (funext fun k => ?_))
    rcases k with _ | _ | _ | _ | k <;> rfl
  rw [h_t] at h
  exact h.1

private theorem rule_10 (a : ℕ) :
    ReachesPlus target (cfg_E a 1 1) (cfg_E 0 2 (2 * a + 1)) := by
  have h := step_pat_64 (v3 a 1 1)
  have h_t :
      target_pat_64 (v3 a 1 1) =
        some (cfg_E 0 2 (2 * a + 1)) := rfl
  rw [h_t] at h
  exact h.1

private theorem rule_11 (a b c : ℕ) :
    ReachesPlus target (cfg_E a (b + 1) (c + 2)) (cfg_E (a + 2) b c) := by
  have h := step_pat_64 (v3 a (b + 1) (c + 2))
  have h_t :
      target_pat_64 (v3 a (b + 1) (c + 2)) =
        some (cfg_E (a + 2) b c) := by
    unfold_targets
    refine congrArg some (congrArg (evalTapePattern pat_64) (funext fun k => ?_))
    rcases k with _ | _ | _ | _ | k <;>
      (first | rfl | (simp -failIfUnchanged only []; omega))
  rw [h_t] at h
  exact h.1

private theorem rule_12 (a b : ℕ) :
    ReachesPlus target (cfg_E a (b + 2) 0) (cfg_E 0 b (2 * a + 7)) := by
  have h := step_pat_64 (v3 a (b + 2) 0)
  have h_t :
      target_pat_64 (v3 a (b + 2) 0) =
        some (cfg_E 0 b (2 * a + 7)) := by
    unfold_targets
    refine congrArg some (congrArg (evalTapePattern pat_64) (funext fun k => ?_))
    rcases k with _ | _ | _ | _ | k <;> rfl
  rw [h_t] at h
  exact h.1

private theorem rule_13 (a b : ℕ) :
    ReachesPlus target (cfg_E a (b + 2) 1) (cfg_E 0 b (2 * a + 5)) := by
  have h := step_pat_64 (v3 a (b + 2) 1)
  have h_t :
      target_pat_64 (v3 a (b + 2) 1) =
        some (cfg_E 0 b (2 * a + 5)) := rfl
  rw [h_t] at h
  exact h.1

/-- Symbolic configuration state space for `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD`. -/
inductive State where
  /-- $E(a, b, c) := 0^\infty\,1\,(01)^{b+1}\,(11)^a\,111\,\mathrm{A}{>}\,1^{c+1}\,0^\infty$. -/
  | E (a b c : ℕ)

/-- Initial symbolic state $E(0, 0, 2)$, reached after 65 raw TM steps. -/
def start : State := .E 0 0 2

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .E a b c =>
    Cfg.headRight A
      (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
          (ListBlank.cons 1 (ListBlank.cons 0
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
              (ListBlank.cons 1 default))))))))
      (ListBlank.cons 1 (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .E a 0 0 => some (.E 0 0 (2 * a + 5))
  | .E a 0 1 => some (.E 0 0 (2 * a + 3))
  | .E a 0 2 => some (.E 0 0 (2 * a + 9))
  | .E a 0 3 => some (.E 0 0 (2 * a + 7))
  | .E a 0 4 => some (.E 0 0 (2 * a + 12))
  | .E a 0 5 => some (.E 0 0 (2 * a + 10))
  | .E _ 0 6 => none
  | .E a 0 (c + 7) => some (.E 0 (a + 4) (c + 1))
  | .E a 1 0 => some (.E 0 2 (2 * a + 3))
  | .E a 1 1 => some (.E 0 2 (2 * a + 1))
  | .E a (b + 1) (c + 2) => some (.E (a + 2) b c)
  | .E a (b + 2) 0 => some (.E 0 b (2 * a + 7))
  | .E a (b + 2) 1 => some (.E 0 b (2 * a + 5))

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_pat_64
  step_some := by
    rintro ⟨a, b, c⟩ s' hnext
    rcases b with _ | _ | b
    · rcases c with _ | _ | _ | _ | _ | _ | _ | c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_1 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_2 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_3 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_4 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_5 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_6 a
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_8 a c
    · rcases c with _ | _ | c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_9 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_10 a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_11 a 0 c
    · rcases c with _ | _ | c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_12 a b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_13 a b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_11 a (b + 1) c
  step_none := by
    rintro ⟨a, b, c⟩ hnext
    rcases b with _ | _ | b
    · rcases c with _ | _ | _ | _ | _ | _ | _ | c
      · simp [next] at hnext
      · simp [next] at hnext
      · simp [next] at hnext
      · simp [next] at hnext
      · simp [next] at hnext
      · simp [next] at hnext
      · rcases rule_7 a with ⟨cfg_h, h_reach, h_halt⟩
        exact ⟨cfg_h, h_reach.to_star, h_halt⟩
      · simp [next] at hnext
    · rcases c with _ | _ | c <;> simp [next] at hnext
    · rcases c with _ | _ | c <;> simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD
