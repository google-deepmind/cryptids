/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LB---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

/-!
Two-DFA closed tape language (CTL / FAR) certificate.

Left DFA: 3 states, right DFA: 2 states, accepted tuples: 4.
Decider verdict: `chain_spinout` (Infinite chain repeat after 3 steps); certificate method: `infer:right-dfa-2`.
The generic development (namespace `CtlCert`) is inlined verbatim from
`gdm/rl/busy_beavers/deciders/CtlCertificate.lean`; the goal theorem
applies its soundness theorem to the concrete tables below, and the
finite closure check `ctlCheck` is discharged by kernel reduction
(`by decide +kernel`).
-/

namespace CtlCert

/-- Run a binary DFA over a half-tape representative `l` (head-adjacent cell
first), processing the far end first and the head-adjacent cell last. -/
def readList {n : ℕ} [NeZero n] (d : Fin n → Fin 2 → Fin n) (l : List (Fin 2)) :
    Fin n :=
  l.foldr (fun a q => d q a) 0

theorem readList_nil {n : ℕ} [NeZero n] (d : Fin n → Fin 2 → Fin n) :
    readList d [] = 0 := rfl

theorem readList_cons {n : ℕ} [NeZero n] (d : Fin n → Fin 2 → Fin n) (a : Fin 2)
    (l : List (Fin 2)) : readList d (a :: l) = d (readList d l) a := rfl

/-- Appending blanks at the far end does not change the DFA state. -/
theorem readList_append_replicate {n : ℕ} [NeZero n] (d : Fin n → Fin 2 → Fin n)
    (h0 : d 0 0 = 0) (l : List (Fin 2)) (k : ℕ) :
    readList d (l ++ List.replicate k default) = readList d l := by
  unfold readList
  rw [List.foldr_append]
  congr 1
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.foldr_cons, ih]
    exact h0

/-- The DFA state of a half-tape (`ListBlank`), well defined thanks to blank
absorption. -/
def readBlank {n : ℕ} [NeZero n] (d : Fin n → Fin 2 → Fin n) (h0 : d 0 0 = 0)
    (L : ListBlank (Fin 2)) : Fin n :=
  L.liftOn (readList d) (by
    rintro a _ ⟨k, rfl⟩
    exact (readList_append_replicate d h0 a k).symm)

theorem readBlank_mk {n : ℕ} [NeZero n] (d : Fin n → Fin 2 → Fin n) (h0 : d 0 0 = 0)
    (l : List (Fin 2)) : readBlank d h0 (ListBlank.mk l) = readList d l := rfl

theorem readBlank_cons {n : ℕ} [NeZero n] (d : Fin n → Fin 2 → Fin n) (h0 : d 0 0 = 0)
    (a : Fin 2) (L : ListBlank (Fin 2)) :
    readBlank d h0 (L.cons a) = d (readBlank d h0 L) a := by
  refine ListBlank.induction_on L (fun l => ?_)
  rfl

/-- Closure check for a single accepted tuple `(p, s, a, q)`: the transition
must be defined and non-halting, and every abstract successor must be accepted. -/
def closureOk {Λ : Type*} [Inhabited Λ] [DecidableEq Λ] {nL nR : ℕ} [NeZero nL] [NeZero nR]
    (M : Machine (Fin 2) Λ)
    (dL : Fin nL → Fin 2 → Fin nL) (dR : Fin nR → Fin 2 → Fin nR)
    (acc : List (Fin nL × Λ × Fin 2 × Fin nR)) : Fin nL × Λ × Fin 2 × Fin nR → Bool
  | (p, s, a, q) =>
    match M s a with
    | none => false
    | some (none, _) => false
    | some (some s', Stmt.write b Dir.right) =>
      (List.finRange 2).all fun a' => (List.finRange nR).all fun q' =>
        if dR q' a' = q then decide ((dL p b, s', a', q') ∈ acc) else true
    | some (some s', Stmt.write b Dir.left) =>
      (List.finRange 2).all fun a' => (List.finRange nL).all fun p' =>
        if dL p' a' = p then decide ((p', s', a', dR q b) ∈ acc) else true

/-- The complete Boolean certificate check. -/
def ctlCheck {Λ : Type*} [Inhabited Λ] [DecidableEq Λ] {nL nR : ℕ} [NeZero nL] [NeZero nR]
    (M : Machine (Fin 2) Λ)
    (dL : Fin nL → Fin 2 → Fin nL) (dR : Fin nR → Fin 2 → Fin nR)
    (acc : List (Fin nL × Λ × Fin 2 × Fin nR)) : Bool :=
  decide (dL 0 0 = 0) && decide (dR 0 0 = 0) &&
    decide (((0 : Fin nL), (default : Λ), (default : Fin 2), (0 : Fin nR)) ∈ acc) &&
    acc.all (closureOk M dL dR acc)

/-- The invariant induced by a certificate: the abstraction of the
configuration is an accepted tuple. -/
def ctlInv {Λ : Type*} {nL nR : ℕ} [NeZero nL] [NeZero nR]
    (dL : Fin nL → Fin 2 → Fin nL) (hL : dL 0 0 = 0)
    (dR : Fin nR → Fin 2 → Fin nR) (hR : dR 0 0 = 0)
    (acc : List (Fin nL × Λ × Fin 2 × Fin nR)) (c : Cfg (Fin 2) Λ) : Prop :=
  ∃ s, c.q = some s ∧
    (readBlank dL hL c.tape.left, s, c.tape.head, readBlank dR hR c.tape.right) ∈ acc

theorem ctlInv_init {Λ : Type*} [Inhabited Λ] {nL nR : ℕ} [NeZero nL] [NeZero nR]
    (dL : Fin nL → Fin 2 → Fin nL) (hL : dL 0 0 = 0)
    (dR : Fin nR → Fin 2 → Fin nR) (hR : dR 0 0 = 0)
    (acc : List (Fin nL × Λ × Fin 2 × Fin nR))
    (h : ((0 : Fin nL), (default : Λ), (default : Fin 2), (0 : Fin nR)) ∈ acc) :
    ctlInv dL hL dR hR acc (init []) :=
  ⟨default, rfl, h⟩

theorem ctlInv_step {Λ : Type*} [Inhabited Λ] [DecidableEq Λ] {nL nR : ℕ} [NeZero nL] [NeZero nR]
    (M : Machine (Fin 2) Λ)
    (dL : Fin nL → Fin 2 → Fin nL) (hL : dL 0 0 = 0)
    (dR : Fin nR → Fin 2 → Fin nR) (hR : dR 0 0 = 0)
    (acc : List (Fin nL × Λ × Fin 2 × Fin nR))
    (hclos : acc.all (closureOk M dL dR acc) = true)
    (c : Cfg (Fin 2) Λ) (hc : ctlInv dL hL dR hR acc c) :
    ∃ c', step M c = some c' ∧ ctlInv dL hL dR hR acc c' := by
  obtain ⟨s, hq, hmem⟩ := hc
  obtain ⟨q, ⟨a, L, R⟩⟩ := c
  simp only at hq hmem
  subst hq
  have hrow := List.all_eq_true.mp hclos _ hmem
  simp only [closureOk] at hrow
  cases hM : M s a with
  | none =>
    rw [hM] at hrow
    exact absurd hrow Bool.false_ne_true
  | some r =>
    obtain ⟨s', b, dir⟩ := r
    cases s' with
    | none =>
      rw [hM] at hrow
      exact absurd hrow Bool.false_ne_true
    | some s' =>
      cases dir with
      | right =>
        rw [hM] at hrow
        refine ⟨⟨some s', ⟨R.head, L.cons b, R.tail⟩⟩, ?_, ?_⟩
        · simp only [step, hM, Option.map_some]
          rfl
        · refine ⟨s', rfl, ?_⟩
          have h1 := List.all_eq_true.mp hrow R.head (List.mem_finRange _)
          have h2 := List.all_eq_true.mp h1 (readBlank dR hR R.tail) (List.mem_finRange _)
          rw [if_pos (by rw [← readBlank_cons dR hR, ListBlank.cons_head_tail])] at h2
          have h3 := of_decide_eq_true h2
          simpa only [readBlank_cons] using h3
      | left =>
        rw [hM] at hrow
        refine ⟨⟨some s', ⟨L.head, L.tail, R.cons b⟩⟩, ?_, ?_⟩
        · simp only [step, hM, Option.map_some]
          rfl
        · refine ⟨s', rfl, ?_⟩
          have h1 := List.all_eq_true.mp hrow L.head (List.mem_finRange _)
          have h2 := List.all_eq_true.mp h1 (readBlank dL hL L.tail) (List.mem_finRange _)
          rw [if_pos (by rw [← readBlank_cons dL hL, ListBlank.cons_head_tail])] at h2
          have h3 := of_decide_eq_true h2
          simpa only [readBlank_cons] using h3

/-- Every configuration reachable from `c₀` satisfies an inductive invariant. -/
theorem ctl_multiStep_inv {Λ : Type*} [Inhabited Λ] (M : Machine (Fin 2) Λ)
    (Inv : Cfg (Fin 2) Λ → Prop)
    (h_step : ∀ c, Inv c → ∃ c', step M c = some c' ∧ Inv c')
    (c₀ : Cfg (Fin 2) Λ) (h₀ : Inv c₀) :
    ∀ n c, multiStep M c₀ n = some c → Inv c := by
  intro n
  induction n with
  | zero =>
    intro c hc
    have hc' : some c₀ = some c := hc
    cases hc'
    exact h₀
  | succ n ih =>
    intro c hc
    have hc' : Option.bind (multiStep M c₀ n) (step M) = some c := by
      rw [← hc, multiStep, multiStep, Function.iterate_succ_apply']
    cases hmid : multiStep M c₀ n with
    | none =>
      rw [hmid] at hc'
      exact absurd hc' (by simp)
    | some cm =>
      rw [hmid] at hc'
      obtain ⟨c', hstep, hinv'⟩ := h_step cm (ih cm hmid)
      have hc'' : step M cm = some c := hc'
      rw [hstep] at hc''
      cases hc''
      exact hinv'

/-- **Soundness of two-DFA CTL certificates.**  If the finite checker
`ctlCheck` accepts `(dL, dR, acc)` for `M`, then `M` never halts from the blank
tape. -/
theorem ctl_certificate_implies_is_does_not_halt {Λ : Type*} [Inhabited Λ] [DecidableEq Λ]
    {nL nR : ℕ} [NeZero nL] [NeZero nR] (M : Machine (Fin 2) Λ)
    (dL : Fin nL → Fin 2 → Fin nL) (dR : Fin nR → Fin 2 → Fin nR)
    (acc : List (Fin nL × Λ × Fin 2 × Fin nR))
    (h : ctlCheck M dL dR acc = true) : IsNotHalt M := by
  simp only [ctlCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hL, hR⟩, hinit⟩, hclos⟩ := h
  intro cfg ⟨n, hn⟩
  have hinv := ctl_multiStep_inv M (ctlInv dL hL dR hR acc)
    (ctlInv_step M dL hL dR hR acc hclos) (init [])
    (ctlInv_init dL hL dR hR acc hinit) n cfg hn
  obtain ⟨c', hc', -⟩ := ctlInv_step M dL hL dR hR acc hclos cfg hinv
  rw [hc']
  rfl

end CtlCert

/-- Transition table of `ctlLeftDfa`, row-major `[d 0 0, d 0 1, d 1 0, d 1 1, …]`. -/
def ctlLeftDfaTable : List (Fin 3) := [
  0, 1, 2, 2, 2, 2
]

/-- Left half-tape DFA of the certificate (3 states, read from the blank end towards the head). -/
def ctlLeftDfa (p : Fin 3) (a : Fin 2) : Fin 3 := ctlLeftDfaTable.getD (2 * p.val + a.val) 0

/-- Transition table of `ctlRightDfa`, row-major `[d 0 0, d 0 1, d 1 0, d 1 1, …]`. -/
def ctlRightDfaTable : List (Fin 2) := [
  0, 1, 1, 1
]

/-- Right half-tape DFA of the certificate (2 states, read from the blank end towards the head). -/
def ctlRightDfa (p : Fin 2) (a : Fin 2) : Fin 2 := ctlRightDfaTable.getD (2 * p.val + a.val) 0

/-- Accepted abstract configurations `(left DFA state, machine state, head symbol, right DFA state)`. -/
def ctlAcc : List (Fin 3 × Fin 6 × Fin 2 × Fin 2) := [
  (0, 0, 0, 0), (0, 2, 1, 1), (0, 4, 0, 1), (1, 1, 0, 0)
]

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  exact CtlCert.ctl_certificate_implies_is_does_not_halt target_tm ctlLeftDfa ctlRightDfa ctlAcc (by decide +kernel)

end BusyBeaver.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH
