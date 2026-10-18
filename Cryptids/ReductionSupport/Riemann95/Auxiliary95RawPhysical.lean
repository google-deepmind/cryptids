/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Auxiliary95Raw
public import Cryptids.ReductionSupport.Riemann95.Auxiliary95RawReturn

/-! Universal physical arithmetic and fence factors; no abstract-program semantics. -/

@[expose] public section

namespace ConjectureMachines.Riemann95Auxiliary.PhysicalRaw

open Turing ConjectureMachines
open ConjectureMachines.Riemann120 ConjectureMachines.Riemann120.Layer2
open ConjectureMachines.Semantics.Riemann.Layer1 (encodeRegs)

def decLeaf98 : Fin 5 → Fin 98
  | ⟨0, _⟩ => 18
  | ⟨1, _⟩ => 32
  | ⟨2, _⟩ => 56
  | ⟨3, _⟩ => 31
  | _ => 58

def incLeaf98 : Fin 5 → Fin 98
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 29
  | ⟨2, _⟩ => 79
  | ⟨3, _⟩ => 23
  | _ => 55

theorem nSteps98_eq (n : Nat) (c : Cfg 98 2) : Raw.nSteps n c =
  ConjectureMachines.Semantics.Riemann.Layer1.nSteps Raw.machine n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [Raw.nSteps, ConjectureMachines.Semantics.Riemann.Layer1.nSteps, ih]

open ConjectureMachines.Semantics.Riemann.Layer1 in
theorem decScanShift98 (suff : List Nat) (m : Nat) (L : ListBlank (Fin 2)) : ∃ s ≥ 1, Raw.nSteps s
  ⟨74, Tape.mk' (ListBlank.append (ConjectureMachines.Semantics.Riemann.Layer1.encodeReg
  m).reverse (L.cons 0)) (ConjectureMachines.Semantics.Riemann.Layer1.regsTape suff)⟩ = some ⟨86,
  ConjectureMachines.Semantics.Riemann.Layer1.Tape.mkL L
  (ConjectureMachines.Semantics.Riemann.Layer1.regsTape (m :: (suff ++ [0])))⟩ := by
  simp only [nSteps98_eq]
  have stepL {q q' : Fin 98} {a b : Fin 2}
      (h : Raw.machine.transition q a = some (b, .left, q'))
      (L R : ListBlank (Fin 2)) :
      step Raw.machine ⟨q, Tape.mkL (L.cons a) R⟩ =
        some ⟨q', Tape.mkL L (R.cons b)⟩ := by
    simp [step, h, Tape.mkL, Tape.write, Tape.move]
  have stepR {q q' : Fin 98} {a b : Fin 2}
      (h : Raw.machine.transition q a = some (b, .right, q'))
      (L R : ListBlank (Fin 2)) :
      step Raw.machine ⟨q, Tape.mk' L (R.cons a)⟩ =
        some ⟨q', Tape.mk' (L.cons b) R⟩ := by
    simp [step, h, Tape.mk', Tape.write, Tape.move]
  have stepPL {q q' : Fin 98} {a b : Fin 2}
      (h : Raw.machine.transition q a = some (b, .left, q'))
      (L R : ListBlank (Fin 2)) :
      step Raw.machine ⟨q, Tape.mk' L (R.cons a)⟩ =
        some ⟨q', Tape.mkL L (R.cons b)⟩ := by
    simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]
  have trans83 : Raw.machine.transition 80 1 = some (1, .left, 80) := by decide
  have trans67 : Raw.machine.transition 64 1 = some (1, .right, 64) := by decide
  have scanL (k : ℕ) (L R : ListBlank (Fin 2)) :
      Semantics.Riemann.Layer1.nSteps Raw.machine k
        ⟨80, Tape.mkL (ListBlank.append (List.replicate k 1) L) R⟩ =
      some ⟨80, Tape.mkL L (ListBlank.append (List.replicate k 1) R)⟩ := by
    induction k generalizing R with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, ListBlank.append, nSteps_succ, stepL trans83]
      simp only [Option.bind_some]
      rw [ih (R.cons 1), append_replicate_cons, List.replicate_succ]
  have scanR (k : ℕ) (L R : ListBlank (Fin 2)) :
      Semantics.Riemann.Layer1.nSteps Raw.machine k
        ⟨64, Tape.mk' L (ListBlank.append (List.replicate k 1) R)⟩ =
      some ⟨64, Tape.mk' (ListBlank.append (List.replicate k 1) L) R⟩ := by
    induction k generalizing L with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, ListBlank.append, nSteps_succ, stepR trans67]
      simp only [Option.bind_some]
      rw [ih (L.cons 1), append_replicate_cons, List.replicate_succ]
  have shift (m : ℕ) (L R : ListBlank (Fin 2)) :
      Semantics.Riemann.Layer1.nSteps Raw.machine (m + 2)
        ⟨86, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) R⟩ =
      some ⟨86, Tape.mkL L (ListBlank.append (encodeReg m) R)⟩ := by
    rw [List.replicate_succ, ListBlank.append]
    have h1 : step Raw.machine
        ⟨86, Tape.mkL ((ListBlank.append (List.replicate m 1) (L.cons 0)).cons 1) R⟩ =
        some ⟨80, Tape.mkL (ListBlank.append (List.replicate m 1) (L.cons 0)) (R.cons 0)⟩ :=
      stepL (by decide) _ _
    have hscan := scanL m (L.cons 0) (R.cons 0)
    have h2 : step Raw.machine
        ⟨80, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate m 1) (R.cons 0))⟩ =
        some ⟨86, Tape.mkL L ((ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1)⟩ :=
      stepL (by decide) _ _
    have hcons : (ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1 =
        ListBlank.append (encodeReg m) R := by
      rw [append_encodeReg, List.replicate_succ, ListBlank.append]
    rw [hcons] at h2
    have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    simpa only [Nat.add_assoc] using hcomb
  induction suff generalizing m L with
  | nil =>
    rw [regsTape_nil, append_encodeReg_reverse]
    have h1 : step Raw.machine
        ⟨74, Tape.mk'
          ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨80, Tape.mkL
          ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      rw [stepPL (q := 74) (q' := 80) (a := 0) (b := 0) (by decide), default_cons_zero]
    have h2 : step Raw.machine
        ⟨80, Tape.mkL
          ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨86, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0))
          (regsTape [0])⟩ := by
      have h := stepL (q := 80) (q' := 86) (a := 0) (b := 1) (by decide)
        (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) default
      have h0 : (default : ListBlank (Fin 2)).cons 1 = regsTape [0] := by
        rw [regsTape_cons, regsTape_nil, append_encodeReg, default_cons_zero]
        rfl
      rw [h0] at h
      exact h
    have hshift := shift m L (regsTape [0])
    rw [← regsTape_cons] at hshift
    exact ⟨m + 4, by omega, step_nSteps h1 (step_nSteps h2 hshift)⟩
  | cons r rs ih =>
    let L' := ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)
    have hL' : ListBlank.append (encodeReg m).reverse (L.cons 0) = L'.cons 0 :=
      append_encodeReg_reverse m (L.cons 0)
    rw [hL', regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step Raw.machine
        ⟨74, Tape.mk' (L'.cons 0)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨64, Tape.mk' ((L'.cons 0).cons 1)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      stepR (by decide) _ _
    have hscan := scanR r ((L'.cons 0).cons 1) ((regsTape rs).cons 0)
    have h2 : step Raw.machine
        ⟨64, Tape.mk' (ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1))
          ((regsTape rs).cons 0)⟩ =
        some ⟨74, Tape.mk' ((ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1)).cons 0)
          (regsTape rs)⟩ :=
      stepR (by decide) _ _
    have hscan_reg := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r (L'.cons 0)] at hscan_reg
    obtain ⟨s, hs1, hs⟩ := ih r L'
    have hshift := shift m L (regsTape (r :: (rs ++ [0])))
    rw [← regsTape_cons] at hshift
    have hcomb := nSteps_bind_eq hscan_reg (nSteps_bind_eq hs hshift)
    exact ⟨_, by omega, hcomb⟩

def rawRoot98 (pad : Nat) (w : List (Fin 2)) (bank : List Nat) : Cfg 98 2 :=
  ⟨15, Tape.mk' (rootLeftOf true) (ListBlank.append (w ++ List.replicate (pad - w.length) 0 ++ [1,
    0] ++ encodeRegs bank) default)⟩

theorem unary98_dec_pos (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length) (hpos : 0 <
  bank.getD r.val 0) (L : ListBlank (Fin 2)) : ∃ s ≥ 1, Raw.nSteps s ⟨decLeaf98 r, Tape.mk' L
  (ListBlank.append [1, 0] (ConjectureMachines.Semantics.Riemann.Layer1.regsTape bank))⟩ = some
  ⟨9, Tape.mk' L (ListBlank.append [0, 0] (ConjectureMachines.Semantics.Riemann.Layer1.regsTape
  (bank.set r.val (bank.getD r.val 0 - 1) ++ [0])))⟩ := by
  open ConjectureMachines.Semantics.Riemann.Layer1 in
  have sr : ∀ (q q' : Fin 98) (a b : Fin 2),
      Raw.machine.transition q a = some (b, Dir.right, q') → ∀ (L R : ListBlank (Fin 2)),
      step Raw.machine ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
    intro q q' a b h L R
    simp [step, h, Tape.mk', Tape.write, Tape.move]
  have scanR : ∀ (q : Fin 98), Raw.machine.transition q 1 = some (1, Dir.right, q) →
      ∀ (k : Nat) (L R : ListBlank (Fin 2)),
      Semantics.Riemann.Layer1.nSteps Raw.machine k
        ⟨q, Tape.mk' L (ListBlank.append (List.replicate k 1) R)⟩ =
        some ⟨q, Tape.mk' (ListBlank.append (List.replicate k 1) L) R⟩ := by
    intro q h k L R
    induction k generalizing L with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, ListBlank.append, nSteps_succ, sr q q 1 1 h]
      simp only [Option.bind_some]
      rw [ih (L.cons 1), append_replicate_cons, List.replicate_succ]
  let chain : Nat → Fin 98 := fun m => match m with
    | 0 => 36 | 1 => 28 | 2 => 22 | 3 => 42 | 4 => 54 | _ => 41
  have chain0 : ∀ m, m < 5 → Raw.machine.transition (chain (m + 1)) 0 = some (0, Dir.right, chain m)
    := by
    intro m hm
    interval_cases m <;> rfl
  have chain1 : ∀ m, 1 ≤ m → m ≤ 4 →
      Raw.machine.transition (chain m) 1 = some (1, Dir.right, chain m) := by
    intro m hm1 hm5
    interval_cases m <;> rfl
  have leaf : Raw.machine.transition (decLeaf98 r) 1 = some (0, Dir.right, chain (r.val + 1)) := by
    fin_cases r <;> rfl
  have scan_pref : ∀ (pref : List Nat), pref.length ≤ 4 → ∀ (L R : ListBlank (Fin 2)),
      Semantics.Riemann.Layer1.nSteps Raw.machine ((encodeRegs pref).length + 1)
        ⟨chain (pref.length + 1), Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
        some ⟨36, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
    intro pref
    induction pref with
    | nil =>
      intro hpref L R
      exact step_one (sr 28 36 0 0 (by rfl) L R)
    | cons v vs ih =>
      intro hpref L R
      simp only [List.length_cons] at hpref ⊢
      have h0 : step Raw.machine
          ⟨chain (vs.length + 1 + 1), Tape.mk' L ((ListBlank.append (encodeRegs (v :: vs)) R).cons
            0)⟩ =
          some ⟨chain (vs.length + 1), Tape.mk' (L.cons 0)
            (ListBlank.append (List.replicate (v + 1) 1) ((ListBlank.append (encodeRegs vs)
              R).cons 0))⟩ := by
        have h := sr _ _ 0 0 (chain0 (vs.length + 1) (by omega)) L
          (ListBlank.append (encodeRegs (v :: vs)) R)
        conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
        exact h
      have hones := scanR _ (chain1 (vs.length + 1) (by omega) (by omega))
        (v + 1) (L.cons 0) ((ListBlank.append (encodeRegs vs) R).cons 0)
      have hrest := ih (by omega) (ListBlank.append (List.replicate (v + 1) 1) (L.cons 0)) R
      rw [← append_encodeReg_reverse, ← ListBlank.append_assoc, ← List.reverse_append,
        ← encodeRegs_cons] at hrest
      have hcomb := step_nSteps h0 (nSteps_bind_eq hones hrest)
      have hlen : (v + 1) + ((encodeRegs vs).length + 1) + 1 =
          (encodeRegs (v :: vs)).length + 1 := by
        simp only [encodeRegs_cons, List.length_append, encodeReg_length]
        omega
      rw [hlen] at hcomb
      exact hcomb
  have sl : ∀ (q q' : Fin 98) (a b : Fin 2),
      Raw.machine.transition q a = some (b, Dir.left, q') → ∀ (L R : ListBlank (Fin 2)),
      step Raw.machine ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
    intro q q' a b h L R
    simp [step, h, Tape.mkL, Tape.write, Tape.move]
  have scanL : ∀ (k : Nat) (L R : ListBlank (Fin 2)),
      Semantics.Riemann.Layer1.nSteps Raw.machine k
        ⟨8, Tape.mkL (ListBlank.append (List.replicate k 1) L) R⟩ =
        some ⟨8, Tape.mkL L (ListBlank.append (List.replicate k 1) R)⟩ := by
    intro k L R
    induction k generalizing R with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, ListBlank.append, nSteps_succ, sl 8 8 1 1 (by rfl)]
      simp only [Option.bind_some]
      rw [ih (R.cons 1), append_replicate_cons, List.replicate_succ]
  have ret_reg : ∀ (q : Fin 98), Raw.machine.transition q 0 = some (0, Dir.left, 9) →
      ∀ (v : Nat) (L R : ListBlank (Fin 2)),
      Semantics.Riemann.Layer1.nSteps Raw.machine (v + 2)
        ⟨q, Tape.mkL (ListBlank.append (encodeReg v).reverse L) R⟩ =
        some ⟨8, Tape.mkL L (ListBlank.append (encodeReg v) R)⟩ := by
    intro q h v L R
    rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
    have h1 := sl q 9 0 0 h ((ListBlank.append (List.replicate v 1) L).cons 1) R
    have h2 := sl 9 8 1 1 (by rfl) (ListBlank.append (List.replicate v 1) L) (R.cons 0)
    have hs := scanL v L ((R.cons 0).cons 1)
    have hc := step_nSteps h1 (step_nSteps h2 hs)
    rw [hc, append_replicate_cons, append_cons_snoc]
    rfl
  have ret_regs : ∀ (pref : List Nat) (L R : ListBlank (Fin 2)),
      Semantics.Riemann.Layer1.nSteps Raw.machine (encodeRegs pref).length
        ⟨8, Tape.mkL (ListBlank.append (encodeRegs pref).reverse L) R⟩ =
        some ⟨8, Tape.mkL L (ListBlank.append (encodeRegs pref) R)⟩ := by
    intro pref
    induction pref with
    | nil => intros; rfl
    | cons v vs ih =>
      intro L R
      rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
        List.length_append, Nat.add_comm, nSteps_add]
      rw [ih, Option.bind_some, encodeReg_length, ret_reg 8 (by rfl), ListBlank.append_assoc]
  have ret_fence : ∀ (pref : List Nat) (L R : ListBlank (Fin 2)),
      Semantics.Riemann.Layer1.nSteps Raw.machine ((encodeRegs pref).length + 1)
        ⟨86, Tape.mkL (ListBlank.append (encodeRegs pref).reverse ((L.cons 0).cons 0)) R⟩ =
        some ⟨9, Tape.mk' L (((ListBlank.append (encodeRegs pref) R).cons 0).cons 0)⟩ := by
    intro pref L R
    cases pref with
    | nil =>
      have hs := step_one (sl 86 9 0 0 (by rfl) (L.cons 0) R)
      simpa only [encodeRegs_nil, List.reverse_nil, List.length_nil, ListBlank.append,
        Tape.mkL_cons, Tape.mk'_cons] using hs
    | cons v vs =>
      have hne : ∀ (pref : List Nat), pref ≠ [] → ∀ L R,
          Semantics.Riemann.Layer1.nSteps Raw.machine (encodeRegs pref).length
            ⟨86, Tape.mkL (ListBlank.append (encodeRegs pref).reverse L) R⟩ =
            some ⟨8, Tape.mkL L (ListBlank.append (encodeRegs pref) R)⟩ := by
        intro pref hp L R
        induction pref using List.reverseRecOn generalizing L R with
        | nil => contradiction
        | append_singleton xs x ih =>
          rw [encodeRegs_append, encodeRegs_cons, encodeRegs_nil, List.append_nil,
            List.reverse_append, ListBlank.append_assoc, List.length_append,
            Nat.add_comm, nSteps_add, encodeReg_length, ret_reg 86 (by rfl),
            Option.bind_some, ret_regs, ListBlank.append_assoc]
      have hs := hne (v :: vs) (List.cons_ne_nil _ _) ((L.cons 0).cons 0) R
      have hf := step_one (sl 8 9 0 0 (by rfl) (L.cons 0) (ListBlank.append (encodeRegs (v ::
        vs)) R))
      have hc := nSteps_bind_eq hs hf
      simpa only [Tape.mkL_cons, Tape.mk'_cons] using hc
  set pref := bank.take r.val
  set m := bank.getD r.val 0 - 1
  set suff := bank.drop (r.val + 1)
  have hv : bank.getD r.val 0 = m + 1 := by dsimp [m]; omega
  have hplen : pref.length = r.val := by
    simp only [pref, List.length_take]
    omega
  have hsplit : regsTape bank = ListBlank.append (encodeRegs pref) (regsTape ((m + 1) :: suff)) :=
    by
    have hb : bank = pref ++ (m + 1) :: suff := by
      rw [← hv, List.getD_eq_getElem bank 0 hr]
      exact (list_take_cons_drop bank r.val hr).symm
    rw [hb, regsTape_append]
  have h0 : step Raw.machine
      ⟨decLeaf98 r, Tape.mk' L (ListBlank.append [1, 0] (regsTape bank))⟩ =
      some ⟨chain (pref.length + 1), Tape.mk' (L.cons 0)
        ((ListBlank.append (encodeRegs pref) (regsTape ((m + 1) :: suff))).cons 0)⟩ := by
    simp only [ListBlank.append]
    rw [hsplit, hplen]
    exact sr _ _ 1 0 leaf _ _
  have hpref := scan_pref pref (by have := r.isLt; omega) (L.cons 0) (regsTape ((m + 1) :: suff))
  set A := ListBlank.append (encodeRegs pref).reverse ((L.cons 0).cons 0)
  have hinit : step Raw.machine ⟨36, Tape.mk' A (regsTape ((m + 1) :: suff))⟩ =
      some ⟨49, Tape.mk' (A.cons 0) (regsTape (m :: suff))⟩ := by
    have hc : regsTape ((m + 1) :: suff) = (regsTape (m :: suff)).cons 1 := by
      rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append,
        ← append_encodeReg, ← regsTape_cons]
    rw [hc]
    exact sr 36 49 1 0 (by rfl) _ _
  have hm_scan : Semantics.Riemann.Layer1.nSteps Raw.machine (m + 2)
      ⟨49, Tape.mk' (A.cons 0) (regsTape (m :: suff))⟩ =
      some ⟨74, Tape.mk' (ListBlank.append (encodeReg m).reverse (A.cons 0)) (regsTape suff)⟩ := by
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 := sr 49 64 1 1 (by rfl) (A.cons 0)
      (ListBlank.append (List.replicate m 1) ((regsTape suff).cons 0))
    have hs := scanR 64 (by rfl) m ((A.cons 0).cons 1) ((regsTape suff).cons 0)
    have h2 := sr 64 74 0 0 (by rfl)
      (ListBlank.append (List.replicate m 1) ((A.cons 0).cons 1)) (regsTape suff)
    have hc := step_nSteps h1 (nSteps_bind_eq hs (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse m (A.cons 0)] at hc
    simpa only [Nat.add_assoc] using hc
  obtain ⟨s_shift, hs1, hshift⟩ := decScanShift98 suff m A
  rw [nSteps98_eq] at hshift
  have hret := ret_fence pref L (regsTape (m :: (suff ++ [0])))
  have hset : ListBlank.append (encodeRegs pref) (regsTape (m :: (suff ++ [0]))) =
      regsTape (bank.set r.val m ++ [0]) := by
    rw [← regsTape_append]
    congr 1
    change bank.take r.val ++ m :: (bank.drop (r.val + 1) ++ [0]) = _
    rw [← List.cons_append, ← List.append_assoc, list_take_set_drop bank r.val m hr]
  rw [hset] at hret
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref
    (step_nSteps hinit (nSteps_bind_eq hm_scan (nSteps_bind_eq hshift hret))))
  refine ⟨(encodeRegs pref).length + 1 + (m + 2 + (s_shift + ((encodeRegs pref).length + 1)) + 1)
    + 1,
    by omega, ?_⟩
  rw [nSteps98_eq]
  simpa only [ListBlank.append] using htotal

theorem unary98_dec_zero (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length) (hz : bank.getD
  r.val 0 = 0) (L : ListBlank (Fin 2)) : ∃ s ≥ 1, Raw.nSteps s ⟨decLeaf98 r, Tape.mk' L
  (ListBlank.append [1, 0] (ConjectureMachines.Semantics.Riemann.Layer1.regsTape bank))⟩ = some
  ⟨63, Tape.mk' L (ListBlank.append [0, 0] (ConjectureMachines.Semantics.Riemann.Layer1.regsTape
  bank))⟩ := by
  exact (open ConjectureMachines.Semantics.Riemann.Layer1 in by
    let run := ConjectureMachines.Semantics.Riemann.Layer1.nSteps Raw.machine
    have stepR {q q' : Fin 98} {a b : Fin 2}
        (h : Raw.machine.transition q a = some (b, .right, q'))
        (A B : ListBlank (Fin 2)) :
        step Raw.machine ⟨q, Tape.mk' A (B.cons a)⟩ =
          some ⟨q', Tape.mk' (A.cons b) B⟩ := by
      simp [step, h, Tape.mk', Tape.write, Tape.move]
    have stepL {q q' : Fin 98} {a b : Fin 2}
        (h : Raw.machine.transition q a = some (b, .left, q'))
        (A B : ListBlank (Fin 2)) :
        step Raw.machine ⟨q, Tape.mkL (A.cons a) B⟩ =
          some ⟨q', Tape.mkL A (B.cons b)⟩ := by
      simp [step, h, Tape.mkL, Tape.write, Tape.move]
    have stepRL {q q' : Fin 98} {a b : Fin 2}
        (h : Raw.machine.transition q a = some (b, .left, q'))
        (A B : ListBlank (Fin 2)) :
        step Raw.machine ⟨q, Tape.mk' A (B.cons a)⟩ =
          some ⟨q', Tape.mkL A (B.cons b)⟩ := by
      simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]
    have scanR {q : Fin 98}
        (h : Raw.machine.transition q 1 = some (1, .right, q))
        (k : Nat) (A B : ListBlank (Fin 2)) :
        run k ⟨q, Tape.mk' A (ListBlank.append (List.replicate k 1) B)⟩ =
          some ⟨q, Tape.mk' (ListBlank.append (List.replicate k 1) A) B⟩ := by
      induction k generalizing A with
      | zero => rfl
      | succ k ih =>
        dsimp only [run] at ih ⊢
        rw [List.replicate_succ, ListBlank.append, nSteps_succ, stepR h]
        simp only [Option.bind_some]
        rw [ih, append_replicate_cons, List.replicate_succ]
    have scanL (k : Nat) (A B : ListBlank (Fin 2)) :
        run k ⟨48, Tape.mkL (ListBlank.append (List.replicate k 1) A) B⟩ =
          some ⟨48, Tape.mkL A (ListBlank.append (List.replicate k 1) B)⟩ := by
      induction k generalizing B with
      | zero => rfl
      | succ k ih =>
        dsimp only [run] at ih ⊢
        rw [List.replicate_succ, ListBlank.append, nSteps_succ,
          stepL (show Raw.machine.transition 48 1 = some (1, .left, 48) by decide)]
        simp only [Option.bind_some]
        rw [ih, append_replicate_cons, List.replicate_succ]
    let sel : Nat → Fin 98 := fun k => match k with
      | 0 => 36 | 1 => 28 | 2 => 22 | 3 => 42 | 4 => 54 | _ => 41
    have selZ (m : Nat) (hm : m < 5) :
        Raw.machine.transition (sel (m + 1)) 0 = some (0, .right, sel m) := by
      interval_cases m <;> decide
    have selO (m : Nat) (hm1 : 1 ≤ m) (hm4 : m ≤ 4) :
        Raw.machine.transition (sel m) 1 = some (1, .right, sel m) := by
      interval_cases m <;> decide
    have leafO : Raw.machine.transition (decLeaf98 r) 1 =
        some (0, .right, sel (r.val + 1)) := by
      fin_cases r <;> decide
    have select_scan (pref : List Nat) (hpref : pref.length ≤ 4)
        (A B : ListBlank (Fin 2)) :
        run ((encodeRegs pref).length + 1)
          ⟨sel (pref.length + 1),
            Tape.mk' A ((ListBlank.append (encodeRegs pref) B).cons 0)⟩ =
          some ⟨36, Tape.mk'
            (ListBlank.append (encodeRegs pref).reverse (A.cons 0)) B⟩ := by
      induction pref generalizing A with
      | nil => exact step_one (stepR (by decide) A B)
      | cons v vs ih =>
        simp only [List.length_cons] at hpref ⊢
        have h0 : step Raw.machine
            ⟨sel (vs.length + 1 + 1),
              Tape.mk' A ((ListBlank.append (encodeRegs (v :: vs)) B).cons 0)⟩ =
            some ⟨sel (vs.length + 1),
              Tape.mk' (A.cons 0)
                (ListBlank.append (List.replicate (v + 1) 1)
                  ((ListBlank.append (encodeRegs vs) B).cons 0))⟩ := by
          have h := stepR (selZ (vs.length + 1) (by omega)) A
            (ListBlank.append (encodeRegs (v :: vs)) B)
          conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
          exact h
        have hones := scanR (selO (vs.length + 1) (by omega) (by omega))
          (v + 1) (A.cons 0) ((ListBlank.append (encodeRegs vs) B).cons 0)
        have hrest := ih (by omega)
          (ListBlank.append (List.replicate (v + 1) 1) (A.cons 0))
        rw [← append_encodeReg_reverse, ← ListBlank.append_assoc,
          ← List.reverse_append, ← encodeRegs_cons] at hrest
        have hcomb := step_nSteps h0 (nSteps_bind_eq hones hrest)
        have hlen : (v + 1) + ((encodeRegs vs).length + 1) + 1 =
            (encodeRegs (v :: vs)).length + 1 := by
          simp only [encodeRegs_cons, List.length_append, encodeReg_length]
          omega
        rw [hlen] at hcomb
        exact hcomb
    have return_reg (v : Nat) (A B : ListBlank (Fin 2)) :
        run (v + 2) ⟨48, Tape.mkL (ListBlank.append (encodeReg v).reverse A) B⟩ =
          some ⟨48, Tape.mkL A (ListBlank.append (encodeReg v) B)⟩ := by
      dsimp only [run]
      rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
      have h1 : step Raw.machine
          ⟨48, Tape.mkL (((ListBlank.append (List.replicate v 1) A).cons 1).cons 0) B⟩ =
          some ⟨63, Tape.mkL ((ListBlank.append (List.replicate v 1) A).cons 1) (B.cons 0)⟩ :=
        stepL (by decide) _ _
      have h2 : step Raw.machine
          ⟨63, Tape.mkL ((ListBlank.append (List.replicate v 1) A).cons 1) (B.cons 0)⟩ =
          some ⟨48, Tape.mkL (ListBlank.append (List.replicate v 1) A) ((B.cons 0).cons 1)⟩ :=
        stepL (by decide) _ _
      have hscan := scanL v A ((B.cons 0).cons 1)
      have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
      rw [hcomb, append_replicate_cons, append_cons_snoc]
      rfl
    have return_regs (pref : List Nat) (A B : ListBlank (Fin 2)) :
        run (encodeRegs pref).length
          ⟨48, Tape.mkL (ListBlank.append (encodeRegs pref).reverse A) B⟩ =
          some ⟨48, Tape.mkL A (ListBlank.append (encodeRegs pref) B)⟩ := by
      induction pref generalizing A B with
      | nil => rfl
      | cons v vs ih =>
        dsimp only [run] at ih ⊢
        dsimp only [run] at return_reg
        rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
          List.length_append, Nat.add_comm, nSteps_add]
        rw [ih, Option.bind_some, encodeReg_length, return_reg, ListBlank.append_assoc]
    let pref := bank.take r.val
    let suff := bank.drop (r.val + 1)
    have hpref_len : pref.length = r.val := List.length_take_of_le (by omega)
    have hz' : bank[r.val] = 0 := by
      simpa only [List.getD, List.getElem?_eq_getElem hr, Option.getD_some] using hz
    have hregs_split : regsTape bank =
        ListBlank.append (encodeRegs pref) (regsTape (0 :: suff)) := by
      rw [← regsTape_append]
      congr 1
      rw [← hz']
      exact (list_take_cons_drop bank r.val hr).symm
    have h0 : step Raw.machine
        ⟨decLeaf98 r, Tape.mk' L ((regsTape bank).cons 0 |>.cons 1)⟩ =
        some ⟨sel (pref.length + 1), Tape.mk' (L.cons 0)
          ((ListBlank.append (encodeRegs pref) (regsTape (0 :: suff))).cons 0)⟩ := by
      rw [hregs_split, hpref_len]
      exact stepR leafO L _
    have hpref_scan := select_scan pref (by rw [hpref_len]; omega)
      (L.cons 0) (regsTape (0 :: suff))
    let LP := ListBlank.append (encodeRegs pref).reverse ((L.cons 0).cons 0)
    have h1 : step Raw.machine ⟨36, Tape.mk' LP (regsTape (0 :: suff))⟩ =
        some ⟨49, Tape.mk' (LP.cons 0) ((regsTape suff).cons 0)⟩ := by
      rw [regsTape_cons, append_encodeReg]
      exact stepR (by decide) LP ((regsTape suff).cons 0)
    have h2 : step Raw.machine ⟨49, Tape.mk' (LP.cons 0) ((regsTape suff).cons 0)⟩ =
        some ⟨36, Tape.mkL (LP.cons 0) ((regsTape suff).cons 0)⟩ :=
      stepRL (by decide) (LP.cons 0) (regsTape suff)
    have h3 : step Raw.machine ⟨36, Tape.mkL (LP.cons 0) ((regsTape suff).cons 0)⟩ =
        some ⟨48, Tape.mkL LP (regsTape (0 :: suff))⟩ := by
      rw [regsTape_cons, append_encodeReg]
      exact stepL (by decide) LP ((regsTape suff).cons 0)
    have hret := return_regs pref ((L.cons 0).cons 0) (regsTape (0 :: suff))
    rw [← hregs_split] at hret
    have hsep : step Raw.machine ⟨48, Tape.mkL ((L.cons 0).cons 0) (regsTape bank)⟩ =
        some ⟨63, Tape.mk' L ((regsTape bank).cons 0 |>.cons 0)⟩ := by
      simpa only [Tape.mkL_cons, Tape.mk'_cons] using
        stepL (show Raw.machine.transition 48 0 = some (0, .left, 63) by decide)
          (L.cons 0) (regsTape bank)
    have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
      (step_nSteps h1 (step_nSteps h2 (step_nSteps h3
        (nSteps_bind_eq hret (step_one hsep))))))
    refine ⟨(encodeRegs pref).length + 1 +
      ((encodeRegs pref).length + 1 + 1 + 1 + 1) + 1, by omega, ?_⟩
    rw [nSteps98_eq]
    exact htotal)

theorem unary98_inc (r : Fin 5) (bank : List Nat) (hr : r.val < bank.length) (L : ListBlank (Fin
  2)) : ∃ s ≥ 1, Raw.nSteps s ⟨incLeaf98 r, Tape.mk' L (ListBlank.append [1, 0]
  (ConjectureMachines.Semantics.Riemann.Layer1.regsTape bank))⟩ = some ⟨9, Tape.mk' L
  (ListBlank.append [0, 0] (ConjectureMachines.Semantics.Riemann.Layer1.regsTape (bank.set r.val
  (bank.getD r.val 0 + 1))))⟩ := by
  open Semantics.Riemann.Layer1 in
    classical
    simp only [nSteps98_eq]
    let run := Semantics.Riemann.Layer1.nSteps Raw.machine
    have sr {q q' : Fin 98} {a b : Fin 2}
        (h : Raw.machine.transition q a = some (b, .right, q'))
        (L R : ListBlank (Fin 2)) :
        step Raw.machine ⟨q, Tape.mk' L (R.cons a)⟩ =
          some ⟨q', Tape.mk' (L.cons b) R⟩ := by
      simp [step, Tape.mk', Tape.write, Tape.move, h]
    have sl {q q' : Fin 98} {a b : Fin 2}
        (h : Raw.machine.transition q a = some (b, .left, q'))
        (L R : ListBlank (Fin 2)) :
        step Raw.machine ⟨q, Tape.mkL (L.cons a) R⟩ =
          some ⟨q', Tape.mkL L (R.cons b)⟩ := by
      simp [step, Tape.mkL, Tape.write, Tape.move, h]
    have srl {q q' : Fin 98} {a b : Fin 2}
        (h : Raw.machine.transition q a = some (b, .left, q'))
        (L R : ListBlank (Fin 2)) :
        step Raw.machine ⟨q, Tape.mk' L (R.cons a)⟩ =
          some ⟨q', Tape.mkL L (R.cons b)⟩ := by
      simp [step, Tape.mk', Tape.mkL, Tape.write, Tape.move, h]
    have scanR {q : Fin 98} {a b : Fin 2}
        (h : Raw.machine.transition q a = some (b, .right, q))
        (k : Nat) (L R : ListBlank (Fin 2)) :
        run k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
          some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
      induction k generalizing L with
      | zero => rfl
      | succ k ih =>
        rw [List.replicate_succ, ListBlank.append]
        change ((step Raw.machine _).bind (run k)) = _
        rw [sr h, Option.bind_some, ih, append_replicate_cons]
    have scanL {q : Fin 98} {a b : Fin 2}
        (h : Raw.machine.transition q a = some (b, .left, q))
        (k : Nat) (L R : ListBlank (Fin 2)) :
        run k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
          some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
      induction k generalizing R with
      | zero => rfl
      | succ k ih =>
        rw [List.replicate_succ, ListBlank.append]
        change ((step Raw.machine _).bind (run k)) = _
        rw [sl h, Option.bind_some, ih, append_replicate_cons]
    have retReg (m : Nat) (L R : ListBlank (Fin 2)) :
        run (m + 2) ⟨8, Tape.mkL (ListBlank.append (encodeReg m).reverse L) R⟩ =
          some ⟨8, Tape.mkL L (ListBlank.append (encodeReg m) R)⟩ := by
      rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
      have h1 := sl (q := 8) (q' := 9) (a := 0) (b := 0) (by decide)
        ((ListBlank.append (List.replicate m 1) L).cons 1) R
      have h2 := sl (q := 9) (q' := 8) (a := 1) (b := 1) (by decide)
        (ListBlank.append (List.replicate m 1) L) (R.cons 0)
      have hscan := scanL (q := 8) (a := 1) (b := 1) (by decide)
        m L ((R.cons 0).cons 1)
      have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
      dsimp only [run]
      rw [hcomb, append_replicate_cons, append_cons_snoc]
      rfl
    have retRegs (regs : List Nat) (L R : ListBlank (Fin 2)) :
        run (encodeRegs regs).length
          ⟨8, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
          some ⟨8, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
      induction regs generalizing L R with
      | nil => rfl
      | cons m ms ih =>
        dsimp only [run] at ih ⊢
        rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
          List.length_append, Nat.add_comm, nSteps_add]
        rw [ih, Option.bind_some, encodeReg_length]
        change run (m + 2) _ = _
        rw [retReg, ListBlank.append_assoc]
    have shift (suff : List Nat) (m : Nat) (LP : ListBlank (Fin 2)) :
        ∃ s, 1 ≤ s ∧ run s
          ⟨6, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) LP) (regsTape suff)⟩ =
          some ⟨8, Tape.mkL LP (regsTape (m :: suff))⟩ := by
      induction suff generalizing m LP with
      | nil =>
        rw [regsTape_nil, List.replicate_succ, ListBlank.append]
        have h1 : step Raw.machine
            ⟨6, Tape.mk' ((ListBlank.append (List.replicate m 1) LP).cons 1) default⟩ =
            some ⟨8, Tape.mkL ((ListBlank.append (List.replicate m 1) LP).cons 1)
              (ListBlank.cons 0 default)⟩ := by
          have hd : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
            default_cons_zero.symm
          conv_lhs => rw [hd]
          exact srl (by decide) _ default
        have hscan := scanL (q := 8) (a := 1) (b := 1) (by decide)
          (m + 1) LP (ListBlank.cons 0 default)
        conv at hscan => lhs; rw [List.replicate_succ, ListBlank.append]
        have hcomb := step_nSteps h1 hscan
        rw [← append_encodeReg, ← regsTape_nil, ← regsTape_cons] at hcomb
        exact ⟨m + 2, by omega, hcomb⟩
      | cons v vs ih =>
        rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
        have h1 := sr (q := 6) (q' := 0) (a := 1) (b := 0) (by decide)
          (ListBlank.append (List.replicate (m + 1) 1) LP)
          (ListBlank.append (List.replicate v 1) ((regsTape vs).cons 0))
        rw [← append_encodeReg_reverse] at h1
        have hscan := scanR (q := 0) (a := 1) (b := 1) (by decide)
          v (ListBlank.append (encodeReg m).reverse LP) ((regsTape vs).cons 0)
        have h2 := sr (q := 0) (q' := 6) (a := 0) (b := 1) (by decide)
          (ListBlank.append (List.replicate v 1) (ListBlank.append (encodeReg m).reverse LP))
          (regsTape vs)
        rw [← ListBlank.append, ← List.replicate_succ] at h2
        obtain ⟨s, hs1, hs⟩ := ih v (ListBlank.append (encodeReg m).reverse LP)
        have hret := retReg m LP (regsTape (v :: vs))
        rw [← regsTape_cons] at hret
        have hcomb := step_nSteps h1 (nSteps_bind_eq hscan
          (step_nSteps h2 (nSteps_bind_eq hs hret)))
        exact ⟨_, by omega, hcomb⟩
    let chain : Nat → Fin 98 := fun i => match i with
      | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 38 | 4 => 37 | _ => 71
    have chOne (i : Nat) (hi : i ≤ 4) :
        Raw.machine.transition (chain i) 1 = some (1, .right, chain i) := by
      interval_cases i <;> decide
    have chZero (i : Nat) (hi : i < 5) :
        Raw.machine.transition (chain (i + 1)) 0 = some (0, .right, chain i) := by
      interval_cases i <;> decide
    have select (pref : List Nat) (hpref : pref.length ≤ 4) (L R : ListBlank (Fin 2)) :
        run ((encodeRegs pref).length + 1)
          ⟨chain (pref.length + 1), Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
          some ⟨0, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
      induction pref generalizing L with
      | nil => exact step_one (sr (by decide) L R)
      | cons v vs ih =>
        simp only [List.length_cons] at hpref ⊢
        have hvlt : vs.length + 1 < 5 := by omega
        have hvle : vs.length ≤ 4 := by omega
        have h0 : step Raw.machine
            ⟨chain (vs.length + 1 + 1),
              Tape.mk' L ((ListBlank.append (encodeRegs (v :: vs)) R).cons 0)⟩ =
            some ⟨chain (vs.length + 1), Tape.mk' (L.cons 0)
              (ListBlank.append (List.replicate (v + 1) 1)
                ((ListBlank.append (encodeRegs vs) R).cons 0))⟩ := by
          have h := sr (chZero (vs.length + 1) hvlt) L
            (ListBlank.append (encodeRegs (v :: vs)) R)
          conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
          exact h
        have hones := scanR (chOne (vs.length + 1) (by omega))
          (v + 1) (L.cons 0) ((ListBlank.append (encodeRegs vs) R).cons 0)
        have hrest := ih hvle (ListBlank.append (List.replicate (v + 1) 1) (L.cons 0))
        rw [← append_encodeReg_reverse, ← ListBlank.append_assoc, ← List.reverse_append,
          ← encodeRegs_cons] at hrest
        have hcomb := step_nSteps h0 (nSteps_bind_eq hones hrest)
        have hlen : (v + 1) + ((encodeRegs vs).length + 1) + 1 =
            (encodeRegs (v :: vs)).length + 1 := by
          simp only [encodeRegs_cons, List.length_append, encodeReg_length]
          omega
        rw [hlen] at hcomb
        exact hcomb
    let pref := bank.take r.val
    let v := bank[r.val]
    let suff := bank.drop (r.val + 1)
    have hpref : pref.length = r.val := List.length_take_of_le (by omega)
    have hbank : regsTape bank = ListBlank.append (encodeRegs pref) (regsTape (v :: suff)) := by
      dsimp only [pref, v, suff]
      rw [← regsTape_append, list_take_cons_drop bank r.val hr]
    have hleaf : Raw.machine.transition (incLeaf98 r) 1 = some (0, .right, chain (r.val + 1)) := by
      fin_cases r <;> decide
    have h0 : step Raw.machine ⟨incLeaf98 r, Tape.mk' L (ListBlank.append [1, 0] (regsTape bank))⟩ =
        some ⟨chain (pref.length + 1), Tape.mk' (L.cons 0)
          ((ListBlank.append (encodeRegs pref) (regsTape (v :: suff))).cons 0)⟩ := by
      rw [hbank, hpref]
      exact sr hleaf L _
    have hselect := select pref (by omega) (L.cons 0) (regsTape (v :: suff))
    let LP := ListBlank.append (encodeRegs pref).reverse ((L.cons 0).cons 0)
    have hvscan : run (v + 2) ⟨0, Tape.mk' LP (regsTape (v :: suff))⟩ =
        some ⟨6, Tape.mk' (ListBlank.append (List.replicate (v + 2) 1) LP) (regsTape suff)⟩ := by
      rw [regsTape_cons, append_encodeReg]
      have hones := scanR (q := 0) (a := 1) (b := 1) (by decide)
        (v + 1) LP ((regsTape suff).cons 0)
      have hz := sr (q := 0) (q' := 6) (a := 0) (b := 1) (by decide)
        (ListBlank.append (List.replicate (v + 1) 1) LP) (regsTape suff)
      have hcomb := nSteps_bind_eq hones (step_one hz)
      have hc : (ListBlank.append (List.replicate (v + 1) 1) LP).cons 1 =
          ListBlank.append (List.replicate (v + 2) 1) LP := by
        rw [← ListBlank.append, ← List.replicate_succ]
      rw [hc] at hcomb
      exact hcomb
    obtain ⟨s, hs, hshift⟩ := shift suff (v + 1) LP
    have hret := retRegs pref ((L.cons 0).cons 0) (regsTape ((v + 1) :: suff))
    have hset : ListBlank.append (encodeRegs pref) (regsTape ((v + 1) :: suff)) =
        regsTape (bank.set r.val (bank.getD r.val 0 + 1)) := by
      rw [← regsTape_append, List.getD_eq_getElem bank 0 hr]
      congr 1
      exact list_take_set_drop bank r.val (v + 1) hr
    rw [hset] at hret
    have hf := sl (q := 8) (q' := 9) (a := 0) (b := 0) (by decide)
      (L.cons 0) (regsTape (bank.set r.val (bank.getD r.val 0 + 1)))
    have htotal := step_nSteps h0 (nSteps_bind_eq hselect
      (nSteps_bind_eq hvscan (nSteps_bind_eq hshift (nSteps_bind_eq hret (step_one hf)))))
    refine ⟨(encodeRegs pref).length + 1 + (v + 2 + (s + ((encodeRegs pref).length + 1))) + 1,
      by omega, ?_⟩
    simpa [Tape.mkL_cons, Tape.mk', ListBlank.append] using htotal


end ConjectureMachines.Riemann95Auxiliary.PhysicalRaw
