module

public import BusyBeaver.Defs

/-!
# Two-DFA Closed Tape Language Certificates (`BusyBeaver.CtlCertificate`)

A *two-DFA CTL certificate* (FAR / CTL style) for a binary Turing machine
`M : Machine (Fin 2) Λ` consists of

* a left DFA `dL : Fin nL → Fin 2 → Fin nL` with start state `0` and the
  blank-absorbing property `dL 0 0 = 0`;
* a right DFA `dR : Fin nR → Fin 2 → Fin nR` with the same properties;
* a finite accept set `acc : List (Fin nL × Λ × Fin 2 × Fin nR)`.

Each DFA reads its half-tape from the far (blank) end towards the head, so the
abstraction of a configuration `⟨some s, ⟨a, L, R⟩⟩` is the tuple
`(readBlank dL L, s, a, readBlank dR R)`.  The Boolean checker `ctlCheck`
verifies by finite enumeration that

1. `dL 0 0 = 0` and `dR 0 0 = 0`;
2. the abstraction `(0, default, default, 0)` of the initial configuration is
   accepted;
3. every accepted tuple has a defined, non-halting machine transition, and the
   abstraction of every possible successor configuration is accepted again
   (moving right pushes the written symbol onto the left DFA and pops an
   arbitrary predecessor state off the right DFA, and symmetrically for left
   moves).

`CtlCert.ctl_certificate_implies_is_does_not_halt` shows that `ctlCheck … = true`
implies `IsNotHalt M`.  Only the computational checker functions (`readList`,
`closureOk`, `ctlCheck`) carry `@[expose]` for kernel reduction (`by decide +kernel`),
while `readBlank` and `ctlInv` keep their bodies in `.olean.private`.
-/

public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver

-- BEGIN CTL CERTIFICATE DEVELOPMENT

namespace CtlCert

/-- Run a binary DFA over a half-tape representative `l` (head-adjacent cell
first), processing the far end first and the head-adjacent cell last. -/
@[expose] def readList {n : ℕ} [NeZero n] (d : Fin n → Fin 2 → Fin n) (l : List (Fin 2)) :
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
    (l : List (Fin 2)) : readBlank d h0 (ListBlank.mk l) = readList d l := by
  rfl

theorem readBlank_cons {n : ℕ} [NeZero n] (d : Fin n → Fin 2 → Fin n) (h0 : d 0 0 = 0)
    (a : Fin 2) (L : ListBlank (Fin 2)) :
    readBlank d h0 (L.cons a) = d (readBlank d h0 L) a := by
  refine ListBlank.induction_on L (fun l => ?_)
  rfl

/-- Closure check for a single accepted tuple `(p, s, a, q)`: the transition
must be defined and non-halting, and every abstract successor must be accepted. -/
@[expose] def closureOk {Λ : Type*} [Inhabited Λ] [DecidableEq Λ] {nL nR : ℕ} [NeZero nL] [NeZero nR]
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
@[expose] def ctlCheck {Λ : Type*} [Inhabited Λ] [DecidableEq Λ] {nL nR : ℕ} [NeZero nL] [NeZero nR]
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
    ctlInv dL hL dR hR acc (init []) := by
  exact ⟨default, rfl, h⟩

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

-- END CTL CERTIFICATE DEVELOPMENT

end BusyBeaver
