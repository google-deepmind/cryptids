/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA`.

Each digit stack $S = [s_0, s_1, \dots]$ encodes odd-length unary blocks $1^{2 s_i + 1}$ separated
by single zeros (`encStack`), ordered from the tape head outward. Starting from `init []`, the
machine reaches $B([], [0, 1])$ in 16 raw steps, where $B(L, R)$ has state `B` reading the head of
`encStack R` with `0 :: encStack L` to its left.

## Accelerated Transition Rules

```text
bounceRight(0, [])       = [0, 0]
bounceRight(0, d :: R)   = (d + 1) :: R
bounceRight(b + 1, R)    = 0 :: bounceRight(b, R)

scanZeros(a, L, [])              = Halt
scanZeros(a, L, [0])             = B([], reverse(L) ++ [a + 2, 0])
scanZeros(a, L, 0 :: 0 :: R)     = scanZeros(a + 2, L, R)
scanZeros(a, L, 0 :: (b+1) :: R) = B((a + 2) :: L, b :: R)
scanZeros(a, L, (b + 1) :: R)    = B((a + 1) :: L, bounceRight(b, R))

B(L, [])      -> B([], reverse(L) ++ [0, 0])
B(L, d :: R)  -> scanZeros(0, replicate(d, 0) ++ L, R)

Start: B([], [0, 1]), reached after 16 raw TM steps
```

Restricting to the Poincaré return section $L = []$ eliminates the left stack completely, yielding
a single-stack transition system $B_{\mathrm{HL}}(R) := B([], R)$ starting at
$B_{\mathrm{HL}}([0, 1])$.
-/

@[expose] public section

namespace BusyBeaver.M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Encode a digit stack `s` as `1^{2a+1} 0 ...` from the tape head outward. -/
def encStack (s : List ℕ) : ListBlank (Fin 2) :=
  List.rec default
    (fun a _ ih =>
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 1)) (ListBlank.cons 0 ih))
    s

/-- Right-stack update produced when state `E` bounces across block `b` into `R`. -/
def bounceRight : ℕ → List ℕ → List ℕ
  | 0, [] => [0, 0]
  | 0, d :: R => (d + 1) :: R
  | b + 1, R => 0 :: bounceRight b R

/-- Symbolic state space for the accelerated stack transition system of `target`. -/
inductive State where
  /-- Configuration `B(L, R)`: state `B` reading `encStack R` with `0 :: encStack L` on the left. -/
  | B (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Peel pairs of `0` digits from `R` in the `E`/`A` chain (`none` indicates halting at `F0`). -/
def scanZeros (a : ℕ) (L : List ℕ) : List ℕ → Option State
  | [] => none
  | [0] => some (.B [] (L.reverse ++ [a + 2, 0]))
  | 0 :: 0 :: R => scanZeros (a + 2) L R
  | 0 :: (b + 1) :: R => some (.B ((a + 2) :: L) (b :: R))
  | (b + 1) :: R => some (.B ((a + 1) :: L) (bounceRight b R))

/-- Initial symbolic state `B([], [0, 1])`, reached from `init []` in 16 raw steps. -/
def start : State := .B [] [0, 1]

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .B L R => Cfg.headRight B (ListBlank.cons 0 (encStack L)) (encStack R)

/-- Accelerated transition function (`none` indicates halting). -/
def next : State → Option State
  | .B L [] => some (.B [] (L.reverse ++ [0, 0]))
  | .B L (d :: R) => scanZeros 0 (List.replicate d 0 ++ L) R

/-! ## Stack Encoding and Sweep Helpers -/

private theorem encStack_nil : encStack [] = default := rfl

private theorem encStack_cons (a : ℕ) (s : List ℕ) :
    encStack (a :: s) =
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 1)) (ListBlank.cons 0 (encStack s)) := rfl

private theorem encStack_zero (s : List ℕ) :
    encStack (0 :: s) = ListBlank.cons 1 (ListBlank.cons 0 (encStack s)) := by
  simp [encStack_cons, list_pow_one]

private theorem encStack_succ (a : ℕ) (s : List ℕ) :
    encStack ((a + 1) :: s) = ListBlank.cons 1 (ListBlank.cons 1 (encStack (a :: s))) := by
  simp only [encStack_cons]
  rw [show 2 * (a + 1) + 1 = 1 + (1 + (2 * a + 1)) by omega,
    ListBlank.append_pow_add, ListBlank.append_pow_add, list_pow_one]
  rfl

private theorem walk_C_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ k)) <{{C}} r) [target]⊢*
      (l <{{C}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => bb_refl
  | succ k ih =>
    have h1 :
        ((l <+ (([1] : List (Fin 2)) ^ (k + 1))) <{{C}} r) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ k)) <{{C}} ([1] +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l ([1] +> r)
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

/-! ## Intermediate Configurations and Layer Contractions -/

private def cfgD0 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgE1 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E (encStack L) (ListBlank.cons 1 (encStack R))

private def cfgE0 (a : ℕ) (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E (encStack (a :: L)) (ListBlank.cons 0 (encStack R))

private def cfgA0 (a : ℕ) (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A (encStack (a :: L)) (ListBlank.cons 0 (encStack R))

private def cfgCMid (L : List ℕ) (b : ℕ) (R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C (encStack L)
    (ListBlank.cons 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * b))
      (ListBlank.cons 0 (encStack R))))

private theorem d0_to_B (L R : List ℕ) : (cfgD0 L R) [target]⊢⁺ (encode (.B L R)) := by
  unfold cfgD0 encode
  bb_steps

private theorem e1_to_B (L R : List ℕ) : (cfgE1 L R) [target]⊢⁺ (encode (.B L R)) := by
  unfold cfgE1 encode
  bb_steps

private theorem cMid_nil (b : ℕ) (R : List ℕ) :
    (cfgCMid [] b R) [target]⊢⁺ (cfgD0 [] (b :: R)) := by
  unfold cfgCMid cfgD0
  simp only [encStack_nil, encStack_cons]
  rw [show 2 * b + 1 = 1 + 2 * b by omega, ListBlank.append_pow_add, list_pow_one]
  bb_steps

private theorem cMid_cons (a : ℕ) (L : List ℕ) (b : ℕ) (R : List ℕ) :
    (cfgCMid (a :: L) b R) [target]⊢⁺ (cfgCMid L a (b :: R)) := by
  unfold cfgCMid
  have h_pre :
      (Cfg.headRight C (encStack (a :: L))
        (ListBlank.cons 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * b))
          (ListBlank.cons 0 (encStack R))))) [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (2 * a))) <{{C}}
          (ListBlank.cons 0 (encStack (b :: R)))) := by
    simp only [encStack_cons]
    rw [show 2 * a + 1 = 1 + 2 * a by omega, ListBlank.append_pow_add,
      show 2 * b + 1 = 1 + 2 * b by omega, ListBlank.append_pow_add, list_pow_one]
    bb_steps
  have h_walk := walk_C_left (2 * a) ((encStack L).cons 0) (ListBlank.cons 0 (encStack (b :: R)))
  simpa only [Cfg.headLeft_cons] using h_pre.trans_star h_walk

private theorem cMid_sweep (L : List ℕ) (b : ℕ) (R : List ℕ) :
    (cfgCMid L b R) [target]⊢⁺ (encode (.B [] (L.reverse ++ (b :: R)))) := by
  induction L generalizing b R with
  | nil =>
    simpa using (cMid_nil b R).trans (d0_to_B [] (b :: R))
  | cons a L ih =>
    have h := (cMid_cons a L b R).trans (ih a (b :: R))
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h

private def rAfter : ℕ → List ℕ → ListBlank (Fin 2)
  | 0, [] => ListBlank.cons 0 (encStack [0])
  | 0, d :: R => ListBlank.cons 1 (encStack (d :: R))
  | b + 1, R => ListBlank.cons 0 (encStack (bounceRight b R))

private theorem rAfter_cons_one (b : ℕ) (R : List ℕ) :
    ListBlank.cons 1 (rAfter b R) = encStack (bounceRight b R) := by
  rcases b with _ | b <;> rcases R with _ | ⟨d, R'⟩
  · simp [rAfter, bounceRight, encStack_zero]
  · simp [rAfter, bounceRight, encStack_succ]
  · simp [rAfter, bounceRight, encStack_zero]
  · simp [rAfter, bounceRight, encStack_zero]

private theorem eb_bounce (b : ℕ) (l : ListBlank (Fin 2)) (R : List ℕ) :
    (Cfg.headRight E l (encStack (b :: R))) [target]⊢⁺
      (Cfg.headRight C l (ListBlank.cons 0 (rAfter b R))) := by
  induction b generalizing l with
  | zero =>
    rcases R with _ | ⟨d, R'⟩
    · rw [encStack_zero]
      simp only [rAfter]
      rw [encStack_zero]
      simp only [encStack_nil]
      bb_steps
    · rw [encStack_zero]
      simp only [rAfter, encStack_cons]
      rw [show 2 * d + 1 = 1 + 2 * d by omega, ListBlank.append_pow_add, list_pow_one]
      bb_steps
  | succ b ih =>
    have h_pre :
        (Cfg.headRight E l (encStack ((b + 1) :: R))) [target]⊢⁺
          (Cfg.headRight E (ListBlank.cons 1 (ListBlank.cons 0 l)) (encStack (b :: R))) := by
      rw [encStack_succ]
      bb_steps
    have h_mid := ih (ListBlank.cons 1 (ListBlank.cons 0 l))
    have h_post :
        (Cfg.headRight C (ListBlank.cons 1 (ListBlank.cons 0 l))
          (ListBlank.cons 0 (rAfter b R))) [target]⊢⁺
          (Cfg.headRight C l
            (ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.cons 1 (rAfter b R))))) :=
      by bb_steps
    rw [rAfter_cons_one] at h_post
    exact (h_pre.trans h_mid).trans h_post

/-! ## `E0`/`A0` Chain and `B` Step Rules -/

private theorem halt_E0_nil (a : ℕ) (L : List ℕ) :
    ∃ cfg', ReachesStar target (cfgE0 a L []) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F (ListBlank.cons 1 (encStack (a :: L))) default, ?_, ?_⟩
  · have h :
        (cfgE0 a L []) [target]⊢⁺
          Cfg.headRight F (ListBlank.cons 1 (encStack (a :: L))) default := by
      unfold cfgE0
      simp only [encStack_nil, encStack_cons]
      bb_steps
    exact h.to_star
  · bb_halt

private theorem rule_A0_nil (a : ℕ) (L : List ℕ) :
    (cfgA0 a L []) [target]⊢⁺ (encode (.B [] (L.reverse ++ [a + 1, 0]))) := by
  have h1 : (cfgA0 a L []) [target]⊢⁺ (cfgCMid ((a + 1) :: L) 0 []) := by
    unfold cfgA0 cfgCMid
    rw [encStack_succ]
    simp only [encStack_nil, encStack_cons]
    bb_steps
  have h2 := cMid_sweep ((a + 1) :: L) 0 []
  simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h1.trans h2

private theorem rule_E0_zero (a : ℕ) (L R : List ℕ) :
    (cfgE0 a L (0 :: R)) [target]⊢⁺ (cfgA0 (a + 1) L R) := by
  unfold cfgE0 cfgA0
  rw [encStack_zero, encStack_succ]
  bb_steps

private theorem rule_A0_zero (a : ℕ) (L R : List ℕ) :
    (cfgA0 a L (0 :: R)) [target]⊢⁺ (cfgE0 (a + 1) L R) := by
  unfold cfgA0 cfgE0
  rw [encStack_zero, encStack_succ]
  bb_steps

private theorem rule_A0_succ (a b : ℕ) (L R : List ℕ) :
    (cfgA0 a L ((b + 1) :: R)) [target]⊢⁺ (encode (.B ((a + 1) :: L) (b :: R))) := by
  have h1 : (cfgA0 a L ((b + 1) :: R)) [target]⊢⁺ (cfgE1 ((a + 1) :: L) (b :: R)) := by
    unfold cfgA0 cfgE1
    rw [encStack_succ b R, encStack_succ a L]
    bb_steps
  exact h1.trans (e1_to_B ((a + 1) :: L) (b :: R))

private theorem rule_E0_succ (a b : ℕ) (L R : List ℕ) :
    (cfgE0 a L ((b + 1) :: R)) [target]⊢⁺ (encode (.B ((a + 1) :: L) (bounceRight b R))) := by
  have h_pre :
      (cfgE0 a L ((b + 1) :: R)) [target]⊢⁺
        (Cfg.headRight E (ListBlank.cons 0 (encStack ((a + 1) :: L))) (encStack (b :: R))) := by
    unfold cfgE0
    rw [encStack_succ b R, encStack_succ a L]
    simp only [encStack_cons]
    rw [show 2 * b + 1 = 1 + 2 * b by omega, ListBlank.append_pow_add, list_pow_one]
    bb_steps
  have h_mid := eb_bounce b (ListBlank.cons 0 (encStack ((a + 1) :: L))) R
  have h_post :
      (Cfg.headRight C (ListBlank.cons 0 (encStack ((a + 1) :: L)))
        (ListBlank.cons 0 (rAfter b R))) [target]⊢⁺
        (cfgD0 ((a + 1) :: L) (bounceRight b R)) := by
    unfold cfgD0
    rw [← rAfter_cons_one]
    bb_steps
  exact ((h_pre.trans h_mid).trans h_post).trans (d0_to_B ((a + 1) :: L) (bounceRight b R))

private theorem reaches_scanZeros (a : ℕ) (L R : List ℕ) :
    match scanZeros a L R with
    | some s' => ReachesPlus target (cfgE0 a L R) (encode s')
    | none => ∃ cfg', ReachesStar target (cfgE0 a L R) cfg' ∧ (step target cfg').isNone := by
  match R with
  | [] =>
    simp only [scanZeros]
    exact halt_E0_nil a L
  | [0] =>
    simp only [scanZeros]
    exact (rule_E0_zero a L []).trans (rule_A0_nil (a + 1) L)
  | 0 :: 0 :: R' =>
    simp only [scanZeros]
    have h12 := (rule_E0_zero a L (0 :: R')).trans (rule_A0_zero (a + 1) L R')
    have ih := reaches_scanZeros (a + 2) L R'
    rcases h : scanZeros (a + 2) L R' with _ | s'
    · rw [h] at ih
      obtain ⟨cfg', hstar, hnone⟩ := ih
      exact ⟨cfg', h12.to_star.trans hstar, hnone⟩
    · rw [h] at ih
      exact h12.trans ih
  | 0 :: (b + 1) :: R' =>
    simp only [scanZeros]
    exact (rule_E0_zero a L ((b + 1) :: R')).trans (rule_A0_succ (a + 1) b L R')
  | (b + 1) :: R' =>
    simp only [scanZeros]
    exact rule_E0_succ a b L R'

private theorem rule_B_nil (L : List ℕ) :
    (encode (.B L [])) [target]⊢⁺ (encode (.B [] (L.reverse ++ [0, 0]))) := by
  have h1 : (encode (.B L [])) [target]⊢⁺ (cfgCMid (0 :: L) 0 []) := by
    simp only [encode, cfgCMid]
    rw [encStack_zero]
    simp only [encStack_nil]
    bb_steps
  have h2 := cMid_sweep (0 :: L) 0 []
  simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h1.trans h2

private theorem rule_B_zero (L R : List ℕ) :
    (encode (.B L (0 :: R))) [target]⊢⁺ (cfgE0 0 L R) := by
  simp only [encode, cfgE0]
  rw [encStack_zero, encStack_zero]
  bb_steps

private theorem rule_B_succ (d : ℕ) (L R : List ℕ) :
    (encode (.B L ((d + 1) :: R))) [target]⊢⁺ (encode (.B (0 :: L) (d :: R))) := by
  simp only [encode]
  rw [encStack_succ d R, encStack_zero L]
  simp only [encStack_cons]
  rw [show 2 * d + 1 = 1 + 2 * d by omega, ListBlank.append_pow_add, list_pow_one]
  bb_steps

private theorem b_peel_d (d : ℕ) (L R : List ℕ) :
    (encode (.B L (d :: R))) [target]⊢⁺ (cfgE0 0 (List.replicate d 0 ++ L) R) := by
  induction d generalizing L with
  | zero =>
    simpa using rule_B_zero L R
  | succ d ih =>
    have h := (rule_B_succ d L R).trans (ih (0 :: L))
    have h_rep : List.replicate d 0 ++ (0 :: L) = List.replicate (d + 1) 0 ++ L := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rwa [h_rep] at h

/-! ## Accelerated Step Verification -/

private theorem init_reaches_start : (init []) [target]⊢* (encode start) := by
  have h : (init []) [target]⊢⁺ (encode start) := by
    simp only [start, encode]
    rw [encStack_zero, encStack_succ, encStack_zero]
    simp only [encStack_nil]
    bb_steps
  exact h.to_star

private theorem step_accel (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨L, _ | ⟨d, R⟩⟩
  · simp only [next]
    exact rule_B_nil L
  · simp only [next]
    have h1 := b_peel_d d L R
    have h2 := reaches_scanZeros 0 (List.replicate d 0 ++ L) R
    rcases h : scanZeros 0 (List.replicate d 0 ++ L) R with _ | s'
    · rw [h] at h2
      obtain ⟨cfg', hstar, hnone⟩ := h2
      exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
    · rw [h] at h2
      exact h1.trans h2

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next :=
  IsValidAcceleration.of_step init_reaches_start fun s => by
    cases h : next s <;> simpa [h] using step_accel s

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Acceleration -/

/-- Reduced single-stack state space $B_{\mathrm{HL}}(R) := B([], R)$ on the $L = []$ Poincaré
return section. -/
inductive HighLevelState where
  /-- Configuration $B([], R)$ at the start of an epoch ($L = []$). -/
  | B (R : List ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level state $B_{\mathrm{HL}}([0, 1])$, coinciding with `start`. -/
def highLevelStart : HighLevelState := .B [0, 1]

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .B R => .B [] R

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Peel leading pairs of `0` digits from `R`, accumulating `2` into `a` per pair. -/
def peelZeroPairs (a : ℕ) : List ℕ → ℕ × List ℕ
  | d₁ :: d₂ :: R => if d₁ = 0 ∧ d₂ = 0 then peelZeroPairs (a + 2) R else (a, d₁ :: d₂ :: R)
  | R => (a, R)

/-- Contract an entire right-scan epoch from $B(L, R)$ until returning to $L = []$ or halting. -/
def scanEpoch (L R : List ℕ) : Option HighLevelState :=
  if R = [] then
    some (.B (L.reverse ++ [0, 0]))
  else
    let d := R.headD 0
    let R₁ := R.tail
    let L₁ := List.replicate d 0 ++ L
    let p := peelZeroPairs 0 R₁
    List.casesOn (motive := fun _ => Option HighLevelState) p.2 none fun c R₃ =>
      if c = 0 then
        List.casesOn (motive := fun _ => Option HighLevelState) R₃
          (some (.B (L₁.reverse ++ [p.1 + 2, 0]))) fun e R₄ =>
            if ((e - 1) :: R₄).sum + ((e - 1) :: R₄).length <
                (d :: R₁).sum + (d :: R₁).length then
              scanEpoch ((p.1 + 2) :: L₁) ((e - 1) :: R₄)
            else none
      else
        if (bounceRight (c - 1) R₃).sum + (bounceRight (c - 1) R₃).length <
            (d :: R₁).sum + (d :: R₁).length then
          scanEpoch ((p.1 + 1) :: L₁) (bounceRight (c - 1) R₃)
        else none
termination_by R.sum + R.length
decreasing_by
  all_goals simp_wf
  all_goals
    cases R with
    | nil => contradiction
    | cons _ _ =>
      simp +zetaDelta only [List.headD_cons, List.tail_cons, List.sum_cons, List.length_cons] at *
      omega

/-- High-level single-stack accelerated transition function on $B_{\mathrm{HL}}(R)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .B R => scanEpoch [] R

private theorem peelZeroPairs_props (a : ℕ) (L : List ℕ) : ∀ R : List ℕ,
    scanZeros a L R = scanZeros (peelZeroPairs a R).1 L (peelZeroPairs a R).2 ∧
    (∀ R', (peelZeroPairs a R).2 ≠ 0 :: 0 :: R') ∧
    (peelZeroPairs a R).2.sum + (peelZeroPairs a R).2.length ≤ R.sum + R.length
  | [] => ⟨rfl, fun _ h => by simp [peelZeroPairs] at h, le_rfl⟩
  | [d₁] => ⟨rfl, fun _ h => by simp [peelZeroPairs] at h, le_rfl⟩
  | d₁ :: d₂ :: R => by
    simp only [peelZeroPairs]
    by_cases h00 : d₁ = 0 ∧ d₂ = 0
    · rcases h00 with ⟨rfl, rfl⟩
      simp only [and_self, ↓reduceIte, scanZeros]
      obtain ⟨h1, h2, h3⟩ := peelZeroPairs_props (a + 2) L R
      refine ⟨h1, h2, ?_⟩
      simp only [List.sum_cons, List.length_cons]
      omega
    · simp only [h00, ↓reduceIte]
      refine ⟨trivial, fun R' h => ?_, le_rfl⟩
      injection h with hd₁ htl
      injection htl with hd₂ _
      exact h00 ⟨hd₁, hd₂⟩

private theorem bounceRight_measure_le (b : ℕ) (R : List ℕ) :
    (bounceRight b R).sum + (bounceRight b R).length ≤ b + R.sum + R.length + 2 := by
  induction b with
  | zero =>
    cases R with
    | nil => simp [bounceRight]
    | cons x xs =>
      simp only [bounceRight, List.sum_cons, List.length_cons]
      omega
  | succ b ih =>
    simp only [bounceRight, List.sum_cons, List.length_cons]
    omega

private theorem scanZeros_succ (a b : ℕ) (L R : List ℕ) :
    scanZeros a L ((b + 1) :: R) = some (.B ((a + 1) :: L) (bounceRight b R)) := by
  cases R <;> rfl

private theorem stepsTo_scanEpoch_aux (m : ℕ) : ∀ (L R : List ℕ),
    R.sum + R.length = m → CollatzStepsTo next (.B L R) ((scanEpoch L R).map toState) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro L R hm
    rw [scanEpoch.eq_def]
    rcases R with _ | ⟨d, R₁⟩
    · simp only [↓reduceIte]
      exact CollatzStepsTo.of_eq rfl
    · simp only [reduceCtorEq, ↓reduceIte, List.headD_cons, List.tail_cons]
      set L₁ := List.replicate d 0 ++ L
      obtain ⟨hscan, hno00, hmeas⟩ := peelZeroPairs_props 0 L₁ R₁
      rcases hp : (peelZeroPairs 0 R₁).2 with _ | ⟨c, R₃⟩
      · simp only [Option.map_none]
        apply CollatzStepsTo.of_eq
        simp only [next, L₁, hscan, hp, scanZeros]
      · dsimp only
        rcases c with _ | b
        · simp only [↓reduceIte]
          rcases R₃ with _ | ⟨e, R₄⟩
          · simp only [Option.map_some, toState]
            apply CollatzStepsTo.of_eq
            simp only [next, L₁, hscan, hp, scanZeros]
          · rcases e with _ | b'
            · exact absurd hp (hno00 R₄)
            · simp only [Nat.add_sub_cancel]
              have hlt : (b' :: R₄).sum + (b' :: R₄).length <
                  (d :: R₁).sum + (d :: R₁).length := by
                simp only [hp, List.sum_cons, List.length_cons] at hmeas ⊢
                omega
              simp only [hlt, ↓reduceIte]
              have hstep : next (.B L (d :: R₁)) =
                  some (.B (((peelZeroPairs 0 R₁).1 + 2) :: L₁) (b' :: R₄)) := by
                simp only [next, L₁, hscan, hp, scanZeros]
              exact CollatzStepsTo.head hstep (ih _ (hm ▸ hlt) _ _ rfl)
        · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
          have hb := bounceRight_measure_le b R₃
          have hlt : (bounceRight b R₃).sum + (bounceRight b R₃).length <
              (d :: R₁).sum + (d :: R₁).length := by
            simp only [hp, List.sum_cons, List.length_cons] at hmeas ⊢
            omega
          simp only [hlt, ↓reduceIte]
          have hstep : next (.B L (d :: R₁)) =
              some (.B (((peelZeroPairs 0 R₁).1 + 1) :: L₁) (bounceRight b R₃)) := by
            simp only [next, L₁, hscan, hp, scanZeros_succ]
          exact CollatzStepsTo.head hstep (ih _ (hm ▸ hlt) _ _ rfl)

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid acceleration of
`target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState)
    (CollatzReachesStar.refl next start) ?_
  rintro ⟨R⟩
  exact stepsTo_scanEpoch_aux (R.sum + R.length) [] R rfl

/-- `target` halts from the blank tape iff `highLevelNext` halts from `highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- The initial acceleration `next` halts from `start` iff `highLevelNext` halts from
`highLevelStart`. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_HHH1RA
