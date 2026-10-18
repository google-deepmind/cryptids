/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Auxiliary95RawPhysical

@[expose] public section
namespace ConjectureMachines.Riemann95Auxiliary.PhysicalRaw

open Turing ConjectureMachines
open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2
open ConjectureMachines.Semantics.Riemann.Layer1 (encodeRegs)

/-- Exact padding change; exhausting the root marker creates one extra blank cell. -/
def exactPad (k : Fin 2) (walked : List (Fin 2)) (fill : Nat) : Nat :=
  walked.length + fill + if k.val < walked.count 0 then 0 else 1

theorem fenceReturn_exact (k : Fin 2) (walked : List (Fin 2)) (fill : Nat) (hfill : 3 ≤ fill) (hk :
  k.val ≤ walked.count 0) (hguard : Riemann104.OnePassGuard.NoThreeZeros (1 :: (popBreakRev k.val
  walked.reverse).reverse).reverse = true) (bank : List Nat) : ∃ s ≥ 1, Raw.nSteps s
  ⟨(if k = 0 then 9 else 63), Tape.mk' (ListBlank.append (List.replicate fill 1)
  (stackLeftOf true walked)) (ListBlank.append [0, 0]
  (ConjectureMachines.Semantics.Riemann.Layer1.regsTape bank))⟩ =
    some (rawRoot98 (exactPad k walked fill)
  (popBreakRev k.val walked.reverse).reverse bank) := by
  let mkL := Semantics.Riemann.Layer1.Tape.mkL
  let ns := Semantics.Riemann.Layer1.nSteps Raw.machine
  have sLL {q q' : Fin 98} {a b : Fin 2}
      (h : Raw.machine.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
      step Raw.machine ⟨q, mkL (L.cons a) R⟩ = some ⟨q', mkL L (R.cons b)⟩ := by
    simp [step, mkL, Semantics.Riemann.Layer1.Tape.mkL, h, Tape.write, Tape.move]
  have sLR {q q' : Fin 98} {a b : Fin 2}
      (h : Raw.machine.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
      step Raw.machine ⟨q, mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
    simp [step, mkL, h, Tape.mk', Tape.write, Tape.move]
  have sPL {q q' : Fin 98} {a b : Fin 2}
      (h : Raw.machine.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
      step Raw.machine ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', mkL L (R.cons b)⟩ := by
    simp [step, mkL, Semantics.Riemann.Layer1.Tape.mkL, h, Tape.mk', Tape.write, Tape.move]
  have sPR {q q' : Fin 98} {a b : Fin 2}
      (h : Raw.machine.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
      step Raw.machine ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
    simp [step, h, Tape.mk', Tape.write, Tape.move]
  have scanL {q : Fin 98} {a b : Fin 2}
      (h : Raw.machine.transition q a = some (b, .left, q)) (n : Nat) (L R : ListBlank (Fin 2)) :
      ns n ⟨q, mkL (ListBlank.append (List.replicate n a) L) R⟩ =
        some ⟨q, mkL L (ListBlank.append (List.replicate n b) R)⟩ := by
    dsimp [ns]
    induction n generalizing R with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ, ListBlank.append, Semantics.Riemann.Layer1.nSteps_succ, sLL h]
      simp only [Option.bind_some]
      rw [ih (R.cons b), Semantics.Riemann.Layer1.append_replicate_cons]
  have popscan (rev : List (Fin 2)) (j : Nat) (hj : j ≤ 1) (hc : j < rev.count 0)
      (L R : ListBlank (Fin 2)) :
      ∃ s ≥ 1, ns s ⟨(if j = 0 then 11 else 2), mkL (ListBlank.append rev L) R⟩ =
        some ⟨5, mkL (ListBlank.append (popBreakRev j rev) L).tail
          ((ListBlank.append
            (List.replicate (rev.length - (popBreakRev j rev).length) 0) R).cons 1)⟩ := by
    induction rev generalizing j R with
    | nil => simp only [List.count_nil] at hc; omega
    | cons b xs ih =>
      rcases Semantics.Riemann.Layer1.fin2_cases b with rfl | rfl
      · cases j with
        | zero =>
          refine ⟨1, le_refl 1, ?_⟩
          simp only [popBreakRev, beq_self_eq_true, ↓reduceIte, List.length_cons,
            Nat.sub_self, List.replicate_zero, ListBlank.append, ListBlank.tail_cons]
          exact Semantics.Riemann.Layer1.step_one (sLL (by rfl) _ _)
        | succ j =>
          have hj0 : j = 0 := by omega
          subst j
          have hc' : 0 < xs.count 0 := by simp only [List.count_cons_self] at hc; omega
          obtain ⟨s, hs, ht⟩ := ih 0 (by omega) hc' (R.cons 0)
          have hlen := popBreakRev_length_le 0 xs
          have he : (0 :: xs).length - (popBreakRev 0 xs).length =
              xs.length - (popBreakRev 0 xs).length + 1 := by simp only [List.length_cons]; omega
          rw [Semantics.Riemann.Layer1.append_replicate_cons, ← he] at ht
          refine ⟨s + 1, by omega, ?_⟩
          simpa only [popBreakRev, beq_self_eq_true, ↓reduceIte, ListBlank.append,
            Nat.reduceEqDiff] using Semantics.Riemann.Layer1.step_nSteps (sLL (q := 2) (q' := 11)
              (a := 0) (b := 0) (by rfl) _ _) ht
      · have hc' : j < xs.count 0 := by
          simpa only [List.count_cons, show ((1 : Fin 2) == 0) = false from rfl,
            Bool.false_eq_true, ite_false, Nat.add_zero] using hc
        obtain ⟨s, hs, ht⟩ := ih j hj hc' (R.cons 0)
        have hp : popBreakRev j (1 :: xs) = popBreakRev j xs := by cases j <;> rfl
        have hlen := popBreakRev_length_le j xs
        have he : (1 :: xs).length - (popBreakRev j xs).length =
            xs.length - (popBreakRev j xs).length + 1 := by simp only [List.length_cons]; omega
        rw [Semantics.Riemann.Layer1.append_replicate_cons, ← he] at ht
        have htrans : Raw.machine.transition (if j = 0 then 11 else 2) 1 =
            some (0, .left, (if j = 0 then 11 else 2)) := by split <;> rfl
        refine ⟨s + 1, by omega, ?_⟩
        simpa only [hp, ListBlank.append] using Semantics.Riemann.Layer1.step_nSteps (sLL htrans _
          _) ht
  let R := ListBlank.append [1, 0] (Semantics.Riemann.Layer1.regsTape bank)
  have hinit : ∃ t ≥ 1, ns t
      ⟨(if k = 0 then 9 else 63), Tape.mk'
        (ListBlank.append (List.replicate fill 1) (stackLeftOf true walked))
        (ListBlank.append [0, 0] (Semantics.Riemann.Layer1.regsTape bank))⟩ =
      some ⟨(if k.val = 0 then 11 else 2), mkL (stackLeftOf true walked)
        (ListBlank.append (List.replicate fill 0) R)⟩ := by
    rcases Semantics.Riemann.Layer1.fin2_cases k with rfl | rfl
    · obtain ⟨f, hf⟩ : ∃ f, fill = f + 1 := ⟨fill - 1, by omega⟩
      subst fill
      have h1 := sPL (q := 9) (q' := 11) (a := 0) (b := 1) (by rfl)
        (ListBlank.append (List.replicate (f + 1) 1) (stackLeftOf true walked))
        ((Semantics.Riemann.Layer1.regsTape bank).cons 0)
      have h2 := sLL (q := 11) (q' := 11) (a := 1) (b := 0) (by rfl)
        (ListBlank.append (List.replicate f 1) (stackLeftOf true walked)) R
      have hscan := scanL (q := 11) (a := 1) (b := 0) (by rfl) f
        (stackLeftOf true walked) (R.cons 0)
      have ht := Semantics.Riemann.Layer1.step_nSteps h1
        (Semantics.Riemann.Layer1.step_nSteps h2 hscan)
      rw [Semantics.Riemann.Layer1.append_replicate_cons] at ht
      refine ⟨f + 1 + 1, by omega, ?_⟩
      simpa only [Fin.val_zero, ↓reduceIte, List.replicate_succ, ListBlank.append, R] using ht
    · have h1 := sPL (q := 63) (q' := 2) (a := 0) (b := 1) (by rfl)
        (ListBlank.append (List.replicate fill 1) (stackLeftOf true walked))
        ((Semantics.Riemann.Layer1.regsTape bank).cons 0)
      have hscan := scanL (q := 2) (a := 1) (b := 0) (by rfl) fill
        (stackLeftOf true walked) R
      refine ⟨fill + 1, by omega, ?_⟩
      simpa only [Fin.val_one, Nat.one_ne_zero, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide,
        ListBlank.append, R] using Semantics.Riemann.Layer1.step_nSteps h1 hscan
  let w := (popBreakRev k.val walked.reverse).reverse
  have hwlen : w.length ≤ walked.length := by
    dsimp [w]
    simpa only [List.length_reverse] using popBreakRev_length_le k.val walked.reverse
  have hmid : ∃ pad', pad' = exactPad k walked fill ∧ ∃ t ≥ 1, ns t
      ⟨(if k.val = 0 then 11 else 2), mkL (stackLeftOf true walked)
        (ListBlank.append (List.replicate fill 0) R)⟩ =
      some ⟨5, mkL (stackLeftOf true w).tail
        ((ListBlank.append (List.replicate (pad' - w.length) 0) R).cons 1)⟩ := by
    by_cases hc : k.val < walked.count 0
    · have hc' : k.val < walked.reverse.count 0 := by simpa only [List.count_reverse] using hc
      obtain ⟨t, ht, hscan⟩ := popscan walked.reverse k.val (by omega) hc'
        (rootLeftOf true) (ListBlank.append (List.replicate fill 0) R)
      rw [append_replicate_zeros_eq] at hscan
      have he : walked.reverse.length - (popBreakRev k.val walked.reverse).length + fill =
          walked.length + fill - w.length := by
        have hl : (popBreakRev k.val walked.reverse).length = w.length := by
          simp only [w, List.length_reverse]
        rw [List.length_reverse, hl]
        omega
      refine ⟨walked.length + fill, by simp only [exactPad, hc, ite_true, Nat.add_zero],
        t, ht, ?_⟩
      simpa only [he, stackLeftOf, w, List.reverse_reverse] using hscan
    · have heq : walked.reverse.count 0 = k.val := by rw [List.count_reverse]; omega
      have hnil : w = [] := by simp only [w, (popBreakRev_of_count_eq k.val walked.reverse heq).1,
        List.reverse_nil]
      have heq' : (walked.reverse ++ [1]).count 0 = k.val := by
        simp only [List.count_append, List.count_cons, List.count_nil,
          show ((1 : Fin 2) == 0) = false from rfl, Bool.false_eq_true, ite_false,
          Nat.add_zero, heq]
      have hp := (popBreakRev_of_count_eq k.val (walked.reverse ++ [1]) heq').2
      have hc' : k.val < ((walked.reverse ++ [1]) ++ [0]).count 0 := by
        simp only [List.count_append, heq', List.count_cons_self, List.count_nil]
        omega
      have hstack : stackLeftOf true walked =
          ListBlank.append ((walked.reverse ++ [1]) ++ [0]) default := by
        simp only [stackLeftOf, rootLeftOf, ↓reduceIte, ListBlank.append_assoc,
          ListBlank.append, Semantics.Riemann.Layer1.default_cons_zero]
      obtain ⟨t, ht, hscan⟩ := popscan ((walked.reverse ++ [1]) ++ [0]) k.val
        (by omega) hc' default (ListBlank.append (List.replicate fill 0) R)
      rw [← hstack, hp, append_replicate_zeros_eq] at hscan
      have he : ((walked.reverse ++ [1]) ++ [0]).length - ([1] : List (Fin 2)).length + fill =
          walked.length + fill + 1 := by
        simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]
        omega
      rw [he] at hscan
      refine ⟨walked.length + fill + 1, by simp only [exactPad, hc, ite_false],
        t, ht, ?_⟩
      simpa only [hnil, stackLeftOf, rootLeftOf, ↓reduceIte, List.reverse_nil,
        List.length_nil, ListBlank.append, Nat.sub_zero] using hscan
  have pop_head : ∀ (j : Nat) (rev : List (Fin 2)),
      popBreakRev j rev = [] ∨ ∃ xs, popBreakRev j rev = 1 :: xs := by
    intro j rev
    induction rev generalizing j with
    | nil => exact Or.inl rfl
    | cons b xs ih =>
      rcases Semantics.Riemann.Layer1.fin2_cases b with rfl | rfl
      · cases j with
        | zero => exact Or.inr ⟨xs, rfl⟩
        | succ j => simpa only [popBreakRev, beq_self_eq_true, ite_true] using ih j
      · cases j with
        | zero => simpa only [popBreakRev, show ((1 : Fin 2) == 0) = false from rfl,
            Bool.false_eq_true, ite_false] using ih 0
        | succ j => simpa only [popBreakRev, show ((1 : Fin 2) == 0) = false from rfl,
            Bool.false_eq_true, ite_false] using ih (j + 1)
  have hheadw : (stackLeftOf true w).head = 1 := by
    simp only [w, stackLeftOf, List.reverse_reverse]
    obtain hz | ⟨xs, hx⟩ := pop_head k.val walked.reverse
    · rw [hz]; rfl
    · rw [hx]; simp only [ListBlank.append, ListBlank.head_cons]
  have finish (pad : Nat) (v : List (Fin 2))
      (hv : Riemann104.OnePassGuard.NoThreeZeros (1 :: v).reverse = true)
      (hhead : (stackLeftOf true v).head = 1) :
      ∃ t ≥ 1, ns t ⟨5, mkL (stackLeftOf true v).tail
        ((ListBlank.append (List.replicate (pad - v.length) 0) R).cons 1)⟩ =
        some (rawRoot98 pad v bank) := by
    let z := pad - v.length
    let S := ListBlank.append (List.replicate z 0) R
    obtain ⟨t, ht, hr⟩ := ReturnRaw.run_return98_after_one v hv hhead S
    have hroot : ⟨15, Tape.mk' (rootLeftOf true) (ListBlank.append v S)⟩ =
        rawRoot98 pad v bank := by
      simp only [rawRoot98, ListBlank.append_assoc, Semantics.Riemann.Layer1.regsTape, R, z, S]
    rw [hroot, nSteps98_eq] at hr
    exact ⟨t, ht, hr⟩
  obtain ⟨t₀, ht₀, h₀⟩ := hinit
  obtain ⟨pad', hpad', t₁, ht₁, h₁⟩ := hmid
  obtain ⟨t₂, ht₂, h₂⟩ := finish pad' w hguard hheadw
  refine ⟨t₀ + (t₁ + t₂), by omega, ?_⟩
  rw [← hpad']
  rw [nSteps98_eq]
  exact Semantics.Riemann.Layer1.nSteps_bind_eq h₀
    (Semantics.Riemann.Layer1.nSteps_bind_eq h₁ h₂)

end ConjectureMachines.Riemann95Auxiliary.PhysicalRaw
