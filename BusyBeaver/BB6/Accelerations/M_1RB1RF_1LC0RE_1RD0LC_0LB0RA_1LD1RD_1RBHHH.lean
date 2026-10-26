/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---`.

Each digit stack $S = [s_0, s_1, \dots]$ encodes unary blocks $1^{s_i + 1}$ separated by single
zeros (`encStack`), ordered from the tape head outward. Starting from `init []`, the machine
reaches $E([])$ in 6 raw steps, where $E(R)$ has state `E` reading `0` between the blank left tape
and $1\,\mathrm{encStack}(R)$.

## Accelerated Transition Rules

```text
E([])           -> E([0, 0])
E(0 :: R)       -> E(scanPass(false, [false, false], R))
E(1 :: R)       -> E(scanPass(true, [false], R))
E((d + 2) :: R) -> Halt

scanPass scans right over digits in {0, 1, 2, 3} (halting on any digit >= 4) and then sweeps left
via retPass + finishRet to produce the next right stack.

Start: E([]), reached after 6 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Normalize the right stack when the leftward return sweep reaches the left blank boundary. -/
def finishRet (s : List ℕ) : List ℕ :=
  List.casesOn s [] fun r₀ R =>
    Nat.casesOn r₀ (List.casesOn R [] fun r2 R' => 0 :: (r2 + 1) :: R') fun r => r :: R

/-- Leftward return sweep converting accumulated scan bits `bs` into right-stack digits. -/
def retPass : Bool → List Bool → List ℕ → List ℕ
  | false, [], R => finishRet (bumpHead R)
  | true, [], R => finishRet (0 :: bumpHead R)
  | false, false :: bs, R => retPass true bs (bumpHead R)
  | false, true :: bs, R => retPass true bs (bumpHead (bumpHead R))
  | true, false :: bs, R => retPass false bs (0 :: bumpHead R)
  | true, [true], R => finishRet (0 :: 0 :: bumpHead R)
  | true, true :: false :: bs, R => retPass true bs (0 :: 0 :: bumpHead R)
  | true, true :: true :: bs, R => retPass true bs (1 :: 0 :: bumpHead R)

/-- Rightward scan across `R` in mode `A` (`false`) or `F` (`true`), halting on digits `≥ 4`. -/
def scanPass : Bool → List Bool → List ℕ → Option (List ℕ)
  | false, bs, [] => some (retPass false bs [0])
  | true, bs, [] => some (retPass true bs [0, 0])
  | false, bs, 0 :: R => some (retPass false (false :: bs) R)
  | false, bs, 1 :: R => some (retPass true (false :: bs) R)
  | false, bs, 2 :: R => scanPass false (false :: false :: bs) R
  | false, bs, 3 :: R => scanPass true (false :: bs) R
  | false, _, (_ + 4) :: _ => none
  | true, bs, 0 :: R => some (retPass false (true :: false :: bs) R)
  | true, bs, 1 :: R => some (retPass true (true :: false :: bs) R)
  | true, bs, 2 :: R => scanPass false (false :: true :: false :: bs) R
  | true, bs, 3 :: R => scanPass true (true :: false :: bs) R
  | true, _, (_ + 4) :: _ => none

/-- Symbolic state space for the accelerated odometer transition system of `target`. -/
inductive State where
  /-- Left-boundary configuration `E(R)`: state `E` reading `0` before `1 :: R`. -/
  | E (R : List ℕ)
  deriving DecidableEq, Repr

/-- Initial symbolic state `E([])`, reached from `init []` in 6 raw steps. -/
def start : State := .E []

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .E R => Cfg.headRight E default (ListBlank.cons 0 (ListBlank.cons 1 (encStack R)))

/-- Accelerated transition function (`none` indicates halting). -/
def next : State → Option State
  | .E [] => some (.E [0, 0])
  | .E (0 :: R) => (scanPass false [false, false] R).map .E
  | .E (1 :: R) => (scanPass true [false] R).map .E
  | .E ((_ + 2) :: _) => none

/-! ## Stack Encoding and Intermediate Sweep Configurations -/

private theorem encStack_zero (s : List ℕ) :
    encStack (0 :: s) = ListBlank.cons 1 (ListBlank.cons 0 (encStack s)) :=
  rfl

private theorem encStack_succ (a : ℕ) (s : List ℕ) :
    encStack ((a + 1) :: s) = ListBlank.cons 1 (encStack (a :: s)) := by
  simp only [encStack, ListBlank.append_pow_succ, ListBlank.append_cons, ListBlank.append_nil]

private theorem encStack_cons_exp (a : ℕ) (s : List ℕ) :
    encStack (a :: s) =
      ListBlank.cons 1
        (ListBlank.append (([1] : List (Fin 2)) ^ a) (ListBlank.cons 0 (encStack s))) := by
  simp only [encStack, ListBlank.append_pow_succ, ListBlank.append_cons, ListBlank.append_nil]

private theorem encStack_bumpHead (s : List ℕ) :
    ListBlank.cons 1 (encStack s) = encStack (bumpHead s) := by
  rcases s with _ | ⟨a, s'⟩
  · simp [bumpHead, encStack]
  · exact (encStack_succ a s').symm

private def encLBot : List Bool → ListBlank (Fin 2)
  | [] => ListBlank.cons 1 (ListBlank.cons 0 default)
  | false :: bs => ListBlank.cons 1 (ListBlank.cons 0 (encLBot bs))
  | true :: bs => ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0 (encLBot bs)))

private def retEnd (R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E default (ListBlank.cons 0 (encStack R))

private def retCfg : Bool → List Bool → List ℕ → Cfg (Fin 2) (Fin 6)
  | false, bs, R => Cfg.headRight E (ListBlank.cons 0 (encLBot bs)) (ListBlank.cons 0 (encStack R))
  | true, bs, R =>
    Cfg.headRight E (ListBlank.cons 0 (ListBlank.cons 0 (encLBot bs)))
      (ListBlank.cons 0 (encStack R))

private def scanCfg : Bool → List Bool → List ℕ → Cfg (Fin 2) (Fin 6)
  | false, bs, R => Cfg.headRight A (ListBlank.cons 0 (encLBot bs)) (ListBlank.cons 0 (encStack R))
  | true, bs, R =>
    Cfg.headRight F
      (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 0 (encLBot bs)))))
      (ListBlank.cons 0 (encStack R))

/-! ## Return and Scan Phase Verification -/

private theorem finish_retEnd (d : ℕ) (R : List ℕ) {c : Cfg (Fin 2) (Fin 6)}
    (h : ReachesPlus target c (retEnd (d :: R))) :
    ReachesPlus target c (encode (.E (finishRet (d :: R)))) := by
  rcases d with _ | r
  · rcases R with _ | ⟨r2, R'⟩
    · have heq : retEnd [0] = encode (.E []) := by
        simp [retEnd, encode, encStack]
      simpa [finishRet, heq] using h
    · have h2 : ReachesPlus target (retEnd (0 :: r2 :: R'))
          (encode (.E (0 :: (r2 + 1) :: R'))) := by
        simp only [retEnd, encode, encStack_zero, encStack_succ, encStack_cons_exp r2 R']
        bb_steps
      simpa [finishRet] using h.trans h2
  · have heq : retEnd ((r + 1) :: R) = encode (.E (r :: R)) := by
      rw [retEnd, encode, encStack_succ]
    simpa [finishRet, heq] using h

private theorem bumpHead_nonempty (R : List ℕ) :
    ∃ d R', bumpHead R = d :: R' := by
  rcases R with _ | ⟨r, R'⟩
  · exact ⟨0, [], rfl⟩
  · exact ⟨r + 1, R', rfl⟩

private theorem step_retPass :
    ∀ (n : ℕ) (bs : List Bool), bs.length ≤ n →
      ∀ (carry : Bool) (R : List ℕ),
        ReachesPlus target (retCfg carry bs R) (encode (.E (retPass carry bs R)))
  | _, [], _ => by
      intro carry R
      cases carry with
      | false =>
        have h1 : ReachesPlus target (retCfg false [] R) (retEnd (bumpHead R)) := by
          simp only [retCfg, retEnd, encLBot, ← encStack_bumpHead]
          bb_steps
        obtain ⟨d, R', hd⟩ := bumpHead_nonempty R
        simpa [retPass, hd] using finish_retEnd d R' (hd ▸ h1)
      | true =>
        have h1 : ReachesPlus target (retCfg true [] R) (retEnd (0 :: bumpHead R)) := by
          simp only [retCfg, retEnd, encLBot, encStack_zero, ← encStack_bumpHead]
          bb_steps
        simpa [retPass] using finish_retEnd 0 (bumpHead R) h1
  | 0, _ :: _, hlen => by
      simp at hlen
  | n + 1, false :: bs, hlen => by
      have ih := step_retPass n bs (Nat.le_of_succ_le_succ hlen)
      intro carry R
      cases carry with
      | false =>
        have h1 : ReachesPlus target (retCfg false (false :: bs) R)
            (retCfg true bs (bumpHead R)) := by
          simp only [retCfg, encLBot, ← encStack_bumpHead]
          bb_steps
        simpa [retPass] using h1.trans (ih true (bumpHead R))
      | true =>
        have h1 : ReachesPlus target (retCfg true (false :: bs) R)
            (retCfg false bs (0 :: bumpHead R)) := by
          simp only [retCfg, encLBot, encStack_zero, ← encStack_bumpHead]
          bb_steps
        simpa [retPass] using h1.trans (ih false (0 :: bumpHead R))
  | n + 1, true :: bs, hlen => by
      have hlen' : bs.length ≤ n := Nat.le_of_succ_le_succ hlen
      have ih := step_retPass n bs hlen'
      intro carry R
      cases carry with
      | false =>
        have h1 : ReachesPlus target (retCfg false (true :: bs) R)
            (retCfg true bs (bumpHead (bumpHead R))) := by
          simp only [retCfg, encLBot, ← encStack_bumpHead]
          bb_steps
        simpa [retPass] using h1.trans (ih true (bumpHead (bumpHead R)))
      | true =>
        rcases bs with _ | ⟨b2, bs'⟩
        · have h1 : ReachesPlus target (retCfg true [true] R)
              (retEnd (0 :: 0 :: bumpHead R)) := by
            simp only [retCfg, retEnd, encLBot, encStack_zero, ← encStack_bumpHead]
            bb_steps
          simpa [retPass] using finish_retEnd 0 (0 :: bumpHead R) h1
        · have ih' := step_retPass n bs' (Nat.le_trans (Nat.le_succ _) hlen')
          cases b2 with
          | false =>
            have h1 : ReachesPlus target (retCfg true (true :: false :: bs') R)
                (retCfg true bs' (0 :: 0 :: bumpHead R)) := by
              simp only [retCfg, encLBot, encStack_zero, ← encStack_bumpHead]
              bb_steps
            simpa [retPass] using h1.trans (ih' true (0 :: 0 :: bumpHead R))
          | true =>
            have h1 : ReachesPlus target (retCfg true (true :: true :: bs') R)
                (retCfg true bs' (1 :: 0 :: bumpHead R)) := by
              simp only [retCfg, encLBot, encStack_succ, encStack_zero, ← encStack_bumpHead]
              bb_steps
            simpa [retPass] using h1.trans (ih' true (1 :: 0 :: bumpHead R))

private theorem step_ret (carry : Bool) (bs : List Bool) (R : List ℕ) :
    ReachesPlus target (retCfg carry bs R) (encode (.E (retPass carry bs R))) :=
  step_retPass bs.length bs (Nat.le_refl _) carry R

private theorem step_scanPass (R : List ℕ) :
    ∀ (isF : Bool) (bs : List Bool),
      match scanPass isF bs R with
      | some R' => ReachesPlus target (scanCfg isF bs R) (encode (.E R'))
      | none => ∃ cfg', ReachesStar target (scanCfg isF bs R) cfg' ∧ (step target cfg').isNone := by
  induction R with
  | nil =>
    intro isF bs
    cases isF with
    | false =>
      simp only [scanPass]
      have h1 : ReachesPlus target (scanCfg false bs []) (retCfg false bs [0]) := by
        simp only [scanCfg, retCfg, encStack]
        bb_steps
      exact h1.trans (step_ret false bs [0])
    | true =>
      simp only [scanPass]
      have h1 : ReachesPlus target (scanCfg true bs []) (retCfg true bs [0, 0]) := by
        simp only [scanCfg, retCfg, encStack]
        bb_steps
      exact h1.trans (step_ret true bs [0, 0])
  | cons d R' ih =>
    intro isF bs
    cases isF with
    | false =>
      rcases d with _ | _ | _ | _ | d'
      · simp only [scanPass]
        have h1 : ReachesPlus target (scanCfg false bs (0 :: R'))
            (retCfg false (false :: bs) R') := by
          simp only [scanCfg, retCfg, encStack_zero, encLBot]
          bb_steps
        exact h1.trans (step_ret false (false :: bs) R')
      · simp only [scanPass]
        have h1 : ReachesPlus target (scanCfg false bs (1 :: R'))
            (retCfg true (false :: bs) R') := by
          simp only [scanCfg, retCfg, encStack_succ, encStack_zero, encLBot]
          bb_steps
        exact h1.trans (step_ret true (false :: bs) R')
      · simp only [scanPass]
        have h1 : ReachesPlus target (scanCfg false bs (2 :: R'))
            (scanCfg false (false :: false :: bs) R') := by
          simp only [scanCfg, encStack_succ, encStack_zero, encLBot]
          bb_steps
        have ih' := ih false (false :: false :: bs)
        rcases hres : scanPass false (false :: false :: bs) R' with _ | R''
        · rw [hres] at ih'
          obtain ⟨cfg', hstar, hnone⟩ := ih'
          exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
        · rw [hres] at ih'
          exact h1.trans ih'
      · simp only [scanPass]
        have h1 : ReachesPlus target (scanCfg false bs (3 :: R'))
            (scanCfg true (false :: bs) R') := by
          simp only [scanCfg, encStack_succ, encStack_zero, encLBot]
          bb_steps
        have ih' := ih true (false :: bs)
        rcases hres : scanPass true (false :: bs) R' with _ | R''
        · rw [hres] at ih'
          obtain ⟨cfg', hstar, hnone⟩ := ih'
          exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
        · rw [hres] at ih'
          exact h1.trans ih'
      · simp only [scanPass]
        refine ⟨Cfg.headRight F
          (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1
            (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 0 (encLBot bs)))))))
          (ListBlank.cons 1
            (ListBlank.append (([1] : List (Fin 2)) ^ d') (ListBlank.cons 0 (encStack R')))),
          ?_, by bb_halt⟩
        simp only [scanCfg, encStack_succ (d' + 3), encStack_succ (d' + 2),
          encStack_succ (d' + 1), encStack_succ d', encStack_cons_exp d']
        bb_steps
    | true =>
      rcases d with _ | _ | _ | _ | d'
      · simp only [scanPass]
        have h1 : ReachesPlus target (scanCfg true bs (0 :: R'))
            (retCfg false (true :: false :: bs) R') := by
          simp only [scanCfg, retCfg, encStack_zero, encLBot]
          bb_steps
        exact h1.trans (step_ret false (true :: false :: bs) R')
      · simp only [scanPass]
        have h1 : ReachesPlus target (scanCfg true bs (1 :: R'))
            (retCfg true (true :: false :: bs) R') := by
          simp only [scanCfg, retCfg, encStack_succ, encStack_zero, encLBot]
          bb_steps
        exact h1.trans (step_ret true (true :: false :: bs) R')
      · simp only [scanPass]
        have h1 : ReachesPlus target (scanCfg true bs (2 :: R'))
            (scanCfg false (false :: true :: false :: bs) R') := by
          simp only [scanCfg, encStack_succ, encStack_zero, encLBot]
          bb_steps
        have ih' := ih false (false :: true :: false :: bs)
        rcases hres : scanPass false (false :: true :: false :: bs) R' with _ | R''
        · rw [hres] at ih'
          obtain ⟨cfg', hstar, hnone⟩ := ih'
          exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
        · rw [hres] at ih'
          exact h1.trans ih'
      · simp only [scanPass]
        have h1 : ReachesPlus target (scanCfg true bs (3 :: R'))
            (scanCfg true (true :: false :: bs) R') := by
          simp only [scanCfg, encStack_succ, encStack_zero, encLBot]
          bb_steps
        have ih' := ih true (true :: false :: bs)
        rcases hres : scanPass true (true :: false :: bs) R' with _ | R''
        · rw [hres] at ih'
          obtain ⟨cfg', hstar, hnone⟩ := ih'
          exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
        · rw [hres] at ih'
          exact h1.trans ih'
      · simp only [scanPass]
        refine ⟨Cfg.headRight F
          (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 0
            (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 0
              (ListBlank.cons 1 (ListBlank.cons 0 (encLBot bs))))))))))
          (ListBlank.cons 1
            (ListBlank.append (([1] : List (Fin 2)) ^ d') (ListBlank.cons 0 (encStack R')))),
          ?_, by bb_halt⟩
        simp only [scanCfg, encStack_succ (d' + 3), encStack_succ (d' + 2),
          encStack_succ (d' + 1), encStack_succ d', encStack_cons_exp d']
        bb_steps

/-! ## Accelerated Step Verification -/

private theorem init_reaches_start : ReachesStar target (init []) (encode start) := by
  have h : ReachesPlus target (init []) (encode start) := by
    simp only [start, encode, encStack]
    bb_steps
  exact h.to_star

private theorem step_accel (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨R⟩
  rcases R with _ | ⟨d, R'⟩
  · simp only [next, encode, encStack]
    bb_steps
  · rcases d with _ | _ | d'
    · simp only [next]
      have h1 : ReachesPlus target (encode (.E (0 :: R')))
          (scanCfg false [false, false] R') := by
        rw [encode, scanCfg, encStack_zero]
        simp only [encLBot]
        bb_steps
      have hs := step_scanPass R' false [false, false]
      rcases hres : scanPass false [false, false] R' with _ | R''
      · rw [hres] at hs
        simp only [Option.map_none]
        obtain ⟨cfg', hstar, hnone⟩ := hs
        exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
      · rw [hres] at hs
        simp only [Option.map_some]
        exact h1.trans hs
    · simp only [next]
      have h1 : ReachesPlus target (encode (.E (1 :: R')))
          (scanCfg true [false] R') := by
        rw [encode, scanCfg, encStack_succ, encStack_zero]
        simp only [encLBot]
        bb_steps
      have hs := step_scanPass R' true [false]
      rcases hres : scanPass true [false] R' with _ | R''
      · rw [hres] at hs
        simp only [Option.map_none]
        obtain ⟨cfg', hstar, hnone⟩ := hs
        exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
      · rw [hres] at hs
        simp only [Option.map_some]
        exact h1.trans hs
    · simp only [next]
      refine ⟨Cfg.headRight F
        (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 (ListBlank.cons 0
          (ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 1 default)))))))
        (ListBlank.cons 1
          (ListBlank.append (([1] : List (Fin 2)) ^ d') (ListBlank.cons 0 (encStack R')))),
        ?_, by bb_halt⟩
      rw [encode, encStack_succ (d' + 1), encStack_succ d', encStack_cons_exp d']
      bb_steps

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start fun s => ?_
  have hs := step_accel s
  rcases h : next s with _ | s' <;> simpa [h] using hs

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RBHHH
