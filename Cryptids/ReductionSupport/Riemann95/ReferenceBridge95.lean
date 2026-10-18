/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.ReferencePermutation95
public import Cryptids.ReductionSupport.Riemann.FiniteStage

@[expose] public section

namespace ConjectureMachines.Riemann95

def OriginalCallerScope95 (P bits : List (Fin 2)) : Prop :=
  bits = Riemann120.Layer2.trimZeros P ∨ ∃ suffix, bits = P ++ suffix

def OriginalDivideFn95 (regs : List Nat) : List Nat :=
  let J := regs.getD 1 0 + regs.getD 4 0 + 1
  let B := regs.getD 0 0 + regs.getD 2 0
  [0, B % J, B / J, regs.getD 3 0, J - 1 - B % J]

def OriginalProductStepFn95 (regs : List Nat) : List Nat :=
  let J := regs.getD 1 0 + 1 + regs.getD 4 0 + 1
  let B := regs.getD 0 0 + regs.getD 2 0
  let r := B % J
  let q := B / J
  let v := J - 1 - r
  let xmid := if v = 0 then q else q * J + r
  let x1 := xmid * J + (J - 1)
  [0, J - 1, x1 * J + (J - 1), regs.getD 3 0, 0]

def OriginalRegion95 (lo hi : Nat) (bits : List (Fin 2)) : Prop :=
  ∃ s : Fin 121, lo ≤ s.val ∧ s.val < hi ∧ bits = ReferenceProgram.oldWord s

def OriginalRegionEdge95 (lo hi : Nat) (a b : Riemann120.Layer2.RhRegCfg) : Prop :=
  Riemann120.Layer2.rhRegStep a = some b ∧ OriginalRegion95 lo hi a.stack

def OriginalScopedSubEval95 (q : Fin 121) (F : List Nat → List Nat) : Prop :=
  ∀ P : List (Fin 2), Riemann120.Layer2.walkInternal 27 P = some q →
  ∀ regs : List Nat, regs.length = 5 →
    Relation.TransGen (fun a b : Riemann120.Layer2.RhRegCfg =>
      Riemann120.Layer2.rhRegStep a = some b ∧ OriginalCallerScope95 P a.stack)
      ⟨Riemann120.Layer2.trimZeros P, regs⟩ ⟨Riemann120.Layer2.retStack P,F regs⟩ ∧
      (F regs).length = 5

def OriginalTickFn95 (regs : List Nat) : List Nat :=
  if regs.getD 4 0 = 0 then
    [regs.getD 0 0, 0, regs.getD 2 0 + 1, regs.getD 3 0, regs.getD 1 0]
  else
    [regs.getD 0 0, regs.getD 1 0 + 1, regs.getD 2 0, regs.getD 3 0, regs.getD 4 0 - 1]

def OriginalTransformFn95 (regs : List Nat) : List Nat :=
  let J := regs.getD 1 0 + regs.getD 4 0 + 1
  [0, regs.getD 1 0 + regs.getD 4 0,
    (regs.getD 0 0 + regs.getD 2 0) * J + regs.getD 1 0, regs.getD 3 0, 0]

def ReferencePreOldStep95 (c : Riemann120.Layer2.RhRegCfg) : Option Riemann120.Layer2.RhRegCfg :=
  if c.stack = [1,1,1,1] then none else Riemann120.Layer2.rhRegStep c

def ReferencePreStep95 (c : Riemann120.Layer2.RhRegCfg) : Option Riemann120.Layer2.RhRegCfg :=
  if c.stack = ReferenceProgram.word 88 then none else ReferenceProgram.step c

namespace DefaultLookup95

theorem oldWord62 : ReferenceProgram.oldWord 62 = [1, 1] := by decide +kernel
theorem oldWord63 : ReferenceProgram.oldWord 63 = [1, 1, 0, 1] := by decide +kernel
theorem oldWord64 : ReferenceProgram.oldWord 64 = [1, 1, 0, 1, 0, 1] := by decide +kernel
theorem oldWord65 : ReferenceProgram.oldWord 65 = [1, 1, 0, 1, 1] := by decide +kernel
theorem word0 : ReferenceProgram.word 0 = [] := by decide +kernel
theorem oldWord0 : ReferenceProgram.oldWord 0 = [] := by decide +kernel
theorem word88 : ReferenceProgram.word 88 = [1, 1, 1, 1] := by decide +kernel
theorem role0 : ReferenceLogical.role 0 = .plain := by decide +kernel
theorem role88 : ReferenceLogical.role 88 = .plain := by decide +kernel
end DefaultLookup95

theorem original_regions_cut_lift95 (lo hi : Nat) (hgate : ∀ s : Fin 121, lo ≤ s.val → s.val < hi
  → ReferenceProgram.oldWord s ≠ [1, 1, 1, 1]) (a b : Riemann120.Layer2.RhRegCfg) (h :
  Relation.TransGen (OriginalRegionEdge95 lo hi) a b) : StateTransition.Reaches₁
  ReferencePreOldStep95 a b := by
  have hedge : ∀ x y, OriginalRegionEdge95 lo hi x y →
      ReferencePreOldStep95 x = some y := by
    intro x y hx
    rcases hx with ⟨hstep, s, hlo, hhi, hs⟩
    have hg : x.stack ≠ [1,1,1,1] := by
      rw [hs]
      exact hgate s hlo hhi
    simpa only [ReferencePreOldStep95, ite_eq_right hg] using hstep
  induction h with
  | single hab =>
      exact Relation.TransGen.single (hedge _ _ hab)
  | tail hab hbc ih =>
      exact Relation.TransGen.tail ih (hedge _ _ hbc)

theorem original_scope_cut_transfer95 (P : List (Fin 2)) (hgate : ∀ bits, OriginalCallerScope95 P
  bits → bits ≠ [1, 1, 1, 1]) (a b : Riemann120.Layer2.RhRegCfg) (htrace : Relation.TransGen (fun
  a b : Riemann120.Layer2.RhRegCfg => Riemann120.Layer2.rhRegStep a = some b ∧
  OriginalCallerScope95 P a.stack) a b) : StateTransition.Reaches₁ ReferencePreOldStep95 a b := by
  induction htrace with
  | single h =>
      apply Relation.TransGen.single
      rw [ReferencePreOldStep95, ite_eq_right (hgate _ h.2), h.1]
      rfl
  | tail htrace h ih =>
      apply Relation.TransGen.tail ih
      rw [ReferencePreOldStep95, ite_eq_right (hgate _ h.2), h.1]
      rfl

theorem original_scoped_combinators95 : (∀ (q q₀ q₁ : Fin 121) (F G : List Nat → List Nat),
  Riemann120.rh121Trans q 0 = some (0, .right, q₀) → Riemann120.Layer2.isInternalNode q₀ = true →
  Riemann120.rh121Trans q 1 = some (1, .right, q₁) → Riemann120.Layer2.isInternalNode q₁ = true →
  OriginalScopedSubEval95 q₀ F → OriginalScopedSubEval95 q₁ G → OriginalScopedSubEval95 q (fun
  regs => G (F regs))) ∧ (∀ (q q_dec q_cont q_body : Fin 121) (r : Nat) (body result : List Nat →
  List Nat), Riemann120.rh121Trans q 0 = some (0, .right, q_dec) → Riemann120.Layer2.isLeafState
  q_dec = true → Riemann120.Layer2.isLeafInc q_dec = false → Riemann120.Layer2.leafReg q_dec = r →
  Riemann120.rh121Trans q 1 = some (1, .right, q_cont) → Riemann120.Layer2.isInternalNode q_cont =
  true → Riemann120.rh121Trans q_cont 0 = some (0, .right, q_body) →
  Riemann120.Layer2.isInternalNode q_body = true → Riemann120.rh121Trans q_cont 1 = some (0,
  .left, 37) → OriginalScopedSubEval95 q_body body → (∀ regs : List Nat, regs.length = 5 → (result
  regs).length = 5) → (∀ regs : List Nat, regs.length = 5 → regs.getD r 0 = 0 → result regs =
  regs) → (∀ (regs : List Nat) (k : Nat), regs.length = 5 → regs.getD r 0 = k + 1 → result (body
  (regs.set r k)) = result regs) → (∀ (regs : List Nat) (k : Nat), regs.length = 5 → regs.getD r 0
  = k + 1 → (body (regs.set r k)).getD r 0 ≤ k) → OriginalScopedSubEval95 q result) := by
  constructor
  · intro q q₀ q₁ F G h0 hi0 h1 hi1 hF hG P hP regs hregs
    let R : Riemann120.Layer2.RhRegCfg → Riemann120.Layer2.RhRegCfg → Prop :=
      fun a b => Riemann120.Layer2.rhRegStep a = some b ∧ OriginalCallerScope95 P a.stack
    have hP0 := Riemann120.Layer2.walkInternal_snoc hP h0 hi0
    have hP1 := Riemann120.Layer2.walkInternal_snoc hP h1 hi1
    obtain ⟨tF, lenF⟩ := hF (P ++ [0]) hP0 regs hregs
    obtain ⟨tG, lenG⟩ := hG (P ++ [1]) hP1 (F regs) lenF
    have scope0 : ∀ bits, OriginalCallerScope95 (P ++ [0]) bits → OriginalCallerScope95 P bits := by
      intro bits hb
      rcases hb with htrim | ⟨suffix, hsuf⟩
      · exact Or.inl (htrim.trans (Riemann120.Layer2.trimZeros_append_zero P))
      · exact Or.inr ⟨[0] ++ suffix, by simpa only [List.append_assoc] using hsuf⟩
    have scope1 : ∀ bits, OriginalCallerScope95 (P ++ [1]) bits → OriginalCallerScope95 P bits := by
      intro bits hb
      rcases hb with htrim | ⟨suffix, hsuf⟩
      · exact Or.inr ⟨[1], htrim.trans (Riemann120.Layer2.trimZeros_append_one P)⟩
      · exact Or.inr ⟨[1] ++ suffix, by simpa only [List.append_assoc] using hsuf⟩
    have tF' : Relation.TransGen R _ _ :=
      Relation.TransGen.mono (fun a b h => ⟨h.1, scope0 a.stack h.2⟩) _ _ tF
    have tG' : Relation.TransGen R _ _ :=
      Relation.TransGen.mono (fun a b h => ⟨h.1, scope1 a.stack h.2⟩) _ _ tG
    rw [Riemann120.Layer2.trimZeros_append_zero, Riemann120.Layer2.retStack_append_zero] at tF'
    rw [Riemann120.Layer2.trimZeros_append_one, Riemann120.Layer2.retStack_append_one] at tG'
    exact ⟨tF'.trans tG', lenG⟩
  · intro q q_dec q_cont q_body r body result h0 hl hd hr h1 hic hc0 hib hc1 hb hlen hz hs hdec P hP
    let R : Riemann120.Layer2.RhRegCfg → Riemann120.Layer2.RhRegCfg → Prop :=
      fun a b => Riemann120.Layer2.rhRegStep a = some b ∧ OriginalCallerScope95 P a.stack
    have hP1 := Riemann120.Layer2.walkInternal_snoc hP h1 hic
    have hP10 := Riemann120.Layer2.walkInternal_snoc hP1 hc0 hib
    have hev0 : Riemann120.Layer2.evalStack (Riemann120.Layer2.trimZeros P) =
        .decnz r (P ++ [1]) (Riemann120.Layer2.retStack P) := by
      rw [Riemann120.Layer2.evalStack_trimZeros_of_walkInternal hP,
        Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP h0 hl]
      simp only [hd, hr, Bool.false_eq_true, ↓reduceIte]
    have hev11 : Riemann120.Layer2.evalStack (P ++ [1] ++ [1]) =
        .jump (Riemann120.Layer2.trimZeros P) := by
      have h := Riemann120.Layer2.evalStack_continue1_of_walkInternal
        (P := P ++ [1]) (k := 1) hP1 hc1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      simpa [Riemann120.Layer2.popContinueRev,
        Riemann120.Layer2.popContinueRev_zero_eq_dropLeadingZeros,
        Riemann120.Layer2.trimZeros] using h
    have scopeBody : ∀ bits, OriginalCallerScope95 (P ++ [1] ++ [0]) bits →
        OriginalCallerScope95 P bits := by
      intro bits hscope
      rcases hscope with htrim | ⟨suffix, hsuf⟩
      · rw [Riemann120.Layer2.trimZeros_append_zero,
          Riemann120.Layer2.trimZeros_append_one] at htrim
        exact Or.inr ⟨[1], htrim⟩
      · exact Or.inr ⟨[1] ++ [0] ++ suffix, by simpa only [List.append_assoc] using hsuf⟩
    have hloop : ∀ (k : Nat) (regs : List Nat), regs.length = 5 → regs.getD r 0 = k →
        Relation.TransGen R ⟨Riemann120.Layer2.trimZeros P, regs⟩
          ⟨Riemann120.Layer2.retStack P, result regs⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro regs hregs hk
        cases k with
        | zero =>
          have hstep := Riemann120.Layer2.rhRegStep_of_decnz_zero hev0 hk
          rw [hz regs hregs hk]
          exact Relation.TransGen.single ⟨hstep, Or.inl rfl⟩
        | succ v =>
          have hstep1 := Riemann120.Layer2.rhRegStep_of_decnz_succ hev0 hk
          obtain ⟨tB, lenB⟩ := hb (P ++ [1] ++ [0]) hP10 (regs.set r v)
            (by simpa only [List.length_set] using hregs)
          have tB' : Relation.TransGen R _ _ :=
            Relation.TransGen.mono (fun a b h => ⟨h.1, scopeBody a.stack h.2⟩) _ _ tB
          rw [Riemann120.Layer2.trimZeros_append_zero,
            Riemann120.Layer2.trimZeros_append_one,
            Riemann120.Layer2.retStack_append_zero] at tB'
          have hstep3 := Riemann120.Layer2.rhRegStep_of_jump
            (regs := body (regs.set r v)) hev11
          have hlt : (body (regs.set r v)).getD r 0 < v + 1 := by
            have hle := hdec regs v hregs hk
            omega
          have tRec := ih _ hlt (body (regs.set r v)) lenB rfl
          rw [hs regs v hregs hk] at tRec
          have t1 : Relation.TransGen R ⟨Riemann120.Layer2.trimZeros P, regs⟩
              ⟨P ++ [1], regs.set r v⟩ :=
            Relation.TransGen.single ⟨hstep1, Or.inl rfl⟩
          have t3 : Relation.TransGen R ⟨P ++ [1] ++ [1], body (regs.set r v)⟩
              ⟨Riemann120.Layer2.trimZeros P, body (regs.set r v)⟩ :=
            Relation.TransGen.single ⟨hstep3, Or.inr ⟨[1] ++ [1], List.append_assoc P [1] [1]⟩⟩
          exact ((t1.trans tB').trans t3).trans tRec
    intro regs hregs
    exact ⟨hloop (regs.getD r 0) regs hregs rfl, hlen regs hregs⟩

theorem original_scoped_move95 (q q_dec q₁ q_inc : Fin 121) (r₁ r₂ : Nat) (hr₁ : r₁ < 5) (hr₂ : r₂
  < 5) (hne : r₁ ≠ r₂) (htr0 : Riemann120.rh121Trans q 0 = some (0, .right, q_dec)) (hleaf :
  Riemann120.Layer2.isLeafState q_dec = true) (hdec : Riemann120.Layer2.isLeafInc q_dec = false)
  (hlr₁ : Riemann120.Layer2.leafReg q_dec = r₁) (htr1 : Riemann120.rh121Trans q 1 = some (1,
  .right, q₁)) (hq₁ : Riemann120.Layer2.isInternalNode q₁ = true) (htr10 : Riemann120.rh121Trans
  q₁ 0 = some (0, .right, q_inc)) (hincleaf : Riemann120.Layer2.isLeafState q_inc = true) (hinc :
  Riemann120.Layer2.isLeafInc q_inc = true) (hlr₂ : Riemann120.Layer2.leafReg q_inc = r₂) (htr11 :
  Riemann120.rh121Trans q₁ 1 = some (0, .left, 37)) : OriginalScopedSubEval95 q (fun regs =>
  (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + regs.getD r₁ 0)) := by
  intro P hP
  have hP1 := Riemann120.Layer2.walkInternal_snoc hP htr1 hq₁
  have hev0 : Riemann120.Layer2.evalStack (Riemann120.Layer2.trimZeros P) =
      .decnz r₁ (P ++ [1]) (Riemann120.Layer2.retStack P) := by
    rw [Riemann120.Layer2.evalStack_trimZeros_of_walkInternal hP,
      Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP htr0 hleaf]
    simp only [hdec, hlr₁, Bool.false_eq_true, ↓reduceIte]
  have hev10 : Riemann120.Layer2.evalStack (P ++ [1]) = .inc r₂ (P ++ [1] ++ [1]) := by
    have h := Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP1 htr10 hincleaf
    simpa only [hinc, hlr₂, ↓reduceIte] using h
  have hev11 : Riemann120.Layer2.evalStack (P ++ [1] ++ [1]) =
      .jump (Riemann120.Layer2.trimZeros P) := by
    have h := Riemann120.Layer2.evalStack_continue1_of_walkInternal
      (P := P ++ [1]) (k := 1) hP1 htr11 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    simpa [Riemann120.Layer2.popContinueRev,
      Riemann120.Layer2.popContinueRev_zero_eq_dropLeadingZeros,
      Riemann120.Layer2.trimZeros] using h
  let R := fun a b : Riemann120.Layer2.RhRegCfg =>
    Riemann120.Layer2.rhRegStep a = some b ∧ OriginalCallerScope95 P a.stack
  have hloop : ∀ (v : Nat) (regs : List Nat), regs.length = 5 → regs.getD r₁ 0 = v →
      Relation.TransGen R ⟨Riemann120.Layer2.trimZeros P, regs⟩
        ⟨Riemann120.Layer2.retStack P, (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)⟩ := by
    have hr₁' : r₁ = 0 ∨ r₁ = 1 ∨ r₁ = 2 ∨ r₁ = 3 ∨ r₁ = 4 := by omega
    have hr₂' : r₂ = 0 ∨ r₂ = 1 ∨ r₂ = 2 ∨ r₂ = 3 ∨ r₂ = 4 := by omega
    intro v
    induction v with
    | zero =>
      intro regs hlen hv
      rcases regs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | _⟩⟩⟩⟩⟩ <;>
        try simp at hlen
      have hstep := Riemann120.Layer2.rhRegStep_of_decnz_zero hev0 hv
      have hs : Relation.TransGen R
          ⟨Riemann120.Layer2.trimZeros P, [a0, a1, a2, a3, a4]⟩
          ⟨Riemann120.Layer2.retStack P, [a0, a1, a2, a3, a4]⟩ :=
        Relation.TransGen.single ⟨hstep, Or.inl rfl⟩
      rcases hr₁' with rfl | rfl | rfl | rfl | rfl <;>
        rcases hr₂' with rfl | rfl | rfl | rfl | rfl <;>
        simp at hne hv ⊢ <;>
        simpa [hv] using hs
    | succ v ih =>
      intro regs hlen hv
      rcases regs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | _⟩⟩⟩⟩⟩ <;>
        try simp at hlen
      let regs₁ := ([a0, a1, a2, a3, a4].set r₁ v).set r₂
        ([a0, a1, a2, a3, a4].getD r₂ 0 + 1)
      have hstep1 := Riemann120.Layer2.rhRegStep_of_decnz_succ hev0 hv
      have hstep2 : Riemann120.Layer2.rhRegStep
          ⟨P ++ [1], [a0, a1, a2, a3, a4].set r₁ v⟩ =
          some ⟨P ++ [1] ++ [1], regs₁⟩ := by
        rw [Riemann120.Layer2.rhRegStep_of_inc hev10]
        congr 2
        rcases hr₁' with rfl | rfl | rfl | rfl | rfl <;>
          rcases hr₂' with rfl | rfl | rfl | rfl | rfl <;>
          simp at hne <;> rfl
      have hstep3 := Riemann120.Layer2.rhRegStep_of_jump (regs := regs₁) hev11
      have hv₁ : regs₁.getD r₁ 0 = v := by
        rcases hr₁' with rfl | rfl | rfl | rfl | rfl <;>
          rcases hr₂' with rfl | rfl | rfl | rfl | rfl <;>
          simp [regs₁] at hne ⊢
      have hsteps := ih regs₁ (by simp [regs₁]) hv₁
      have heq : (regs₁.set r₁ 0).set r₂ (regs₁.getD r₂ 0 + v) =
          ([a0, a1, a2, a3, a4].set r₁ 0).set r₂
            ([a0, a1, a2, a3, a4].getD r₂ 0 + (v + 1)) := by
        rcases hr₁' with rfl | rfl | rfl | rfl | rfl <;>
          rcases hr₂' with rfl | rfl | rfl | rfl | rfl <;>
          simp [regs₁] at hne ⊢ <;> omega
      rw [heq] at hsteps
      exact (Relation.TransGen.single ⟨hstep1, Or.inl rfl⟩).trans
        ((Relation.TransGen.single ⟨hstep2, Or.inr ⟨[1], rfl⟩⟩).trans
          ((Relation.TransGen.single
            ⟨hstep3, Or.inr ⟨[1] ++ [1], List.append_assoc P [1] [1]⟩⟩).trans hsteps))
  intro regs hlen
  exact ⟨hloop (regs.getD r₁ 0) regs hlen rfl, by simp only [List.length_set, hlen]⟩

theorem original_scoped_fold95 : OriginalScopedSubEval95 102 (fun regs => [regs.getD 0 0,
  regs.getD 1 0 + regs.getD 4 0, regs.getD 2 0 + regs.getD 1 0, regs.getD 3 0, 0]) := by
  have hloop : OriginalScopedSubEval95 109 (fun regs =>
      [regs.getD 0 0, 0, regs.getD 2 0 + regs.getD 1 0,
       regs.getD 3 0, regs.getD 4 0 + regs.getD 1 0]) := by
    intro P hP
    have hP1 := Riemann120.Layer2.walkInternal_snoc hP (b := 1) (q_end := 113) rfl rfl
    have hP11 := Riemann120.Layer2.walkInternal_snoc hP1 (b := 1) (q_end := 89) rfl rfl
    have hev0 : Riemann120.Layer2.evalStack (Riemann120.Layer2.trimZeros P) =
        .decnz 1 (P ++ [1]) (Riemann120.Layer2.retStack P) := by
      rw [Riemann120.Layer2.evalStack_trimZeros_of_walkInternal hP,
        Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP (q' := 47) rfl rfl]
      rfl
    have hevv : Riemann120.Layer2.evalStack (P ++ [1]) = .inc 4 (P ++ [1] ++ [1]) := by
      rw [Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP1 (q' := 70) rfl rfl]
      rfl
    have hevx : Riemann120.Layer2.evalStack (P ++ [1] ++ [1]) =
        .inc 2 (P ++ [1] ++ [1] ++ [1]) := by
      rw [Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP11 (q' := 99) rfl rfl]
      rfl
    have hevc : Riemann120.Layer2.evalStack (P ++ [1] ++ [1] ++ [1]) =
        .jump (Riemann120.Layer2.trimZeros P) := by
      have h := Riemann120.Layer2.evalStack_continue1_of_walkInternal
        (P := P ++ [1] ++ [1]) (k := 2) hP11 rfl (Or.inr (Or.inr ⟨rfl, rfl⟩))
      simpa [Riemann120.Layer2.popContinueRev,
        Riemann120.Layer2.popContinueRev_zero_eq_dropLeadingZeros,
        Riemann120.Layer2.trimZeros] using h
    have hscope0 : OriginalCallerScope95 P (Riemann120.Layer2.trimZeros P) := Or.inl rfl
    have hscope1 : OriginalCallerScope95 P (P ++ [1]) := Or.inr ⟨[1], rfl⟩
    have hscope11 : OriginalCallerScope95 P (P ++ [1] ++ [1]) :=
      Or.inr ⟨[1, 1], by simp only [List.append_assoc, List.cons_append, List.nil_append]⟩
    have hscope111 : OriginalCallerScope95 P (P ++ [1] ++ [1] ++ [1]) :=
      Or.inr ⟨[1, 1, 1], by simp only [List.append_assoc, List.cons_append, List.nil_append]⟩
    let R := fun a b : Riemann120.Layer2.RhRegCfg =>
      Riemann120.Layer2.rhRegStep a = some b ∧ OriginalCallerScope95 P a.stack
    have hbank : ∀ j m x f v : Nat, Relation.TransGen R
        ⟨Riemann120.Layer2.trimZeros P, [m, j, x, f, v]⟩
        ⟨Riemann120.Layer2.retStack P, [m, 0, x + j, f, v + j]⟩ := by
      intro j
      induction j with
      | zero =>
        intro m x f v
        apply Relation.TransGen.single
        exact ⟨Riemann120.Layer2.rhRegStep_of_decnz_zero hev0 rfl, hscope0⟩
      | succ j ih =>
        intro m x f v
        have s0 : R ⟨Riemann120.Layer2.trimZeros P, [m, j + 1, x, f, v]⟩
            ⟨P ++ [1], [m, j, x, f, v]⟩ :=
          ⟨Riemann120.Layer2.rhRegStep_of_decnz_succ hev0 rfl, hscope0⟩
        have s1 : R ⟨P ++ [1], [m, j, x, f, v]⟩
            ⟨P ++ [1] ++ [1], [m, j, x, f, v + 1]⟩ :=
          ⟨Riemann120.Layer2.rhRegStep_of_inc hevv, hscope1⟩
        have s2 : R ⟨P ++ [1] ++ [1], [m, j, x, f, v + 1]⟩
            ⟨P ++ [1] ++ [1] ++ [1], [m, j, x + 1, f, v + 1]⟩ :=
          ⟨Riemann120.Layer2.rhRegStep_of_inc hevx, hscope11⟩
        have s3 : R ⟨P ++ [1] ++ [1] ++ [1], [m, j, x + 1, f, v + 1]⟩
            ⟨Riemann120.Layer2.trimZeros P, [m, j, x + 1, f, v + 1]⟩ :=
          ⟨Riemann120.Layer2.rhRegStep_of_jump hevc, hscope111⟩
        have ht := (Relation.TransGen.single s0).trans
          ((Relation.TransGen.single s1).trans
            ((Relation.TransGen.single s2).trans
              ((Relation.TransGen.single s3).trans (ih m (x + 1) f (v + 1)))))
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
    intro regs hlen
    rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, tail⟩⟩⟩⟩⟩ <;>
      simp only [List.length_nil, List.length_cons] at hlen
    all_goals try omega
    have htail : tail = [] := by simpa only [List.length_eq_zero_iff] using (show tail.length = 0
      by omega)
    subst tail
    exact ⟨hbank j m x f v, rfl⟩
  have hmove := original_scoped_move95 60 73 74 44 4 1 (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hseq := original_scoped_combinators95.1 102 109 60 _ _ rfl rfl rfl rfl hloop hmove
  intro P hP regs hlen
  obtain ⟨hs, hl⟩ := hseq P hP regs hlen
  simpa only [List.set, List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add, Nat.add_comm]
    using And.intro hs hl

theorem original_scoped_tick95 : OriginalScopedSubEval95 101 OriginalTickFn95 := by
  have hmove : OriginalScopedSubEval95 65
      (fun regs => (regs.set 1 0).set 4 (regs.getD 4 0 + regs.getD 1 0)) := by
    exact original_scoped_move95 65 _ _ _ 1 4 (by decide) (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  intro P hP regs hlen
  have hP0 := Riemann120.Layer2.walkInternal_snoc hP (b := 0) (q_end := 107) rfl rfl
  have hP1 := Riemann120.Layer2.walkInternal_snoc hP (b := 1) (q_end := 108) rfl rfl
  have hP01 := Riemann120.Layer2.walkInternal_snoc hP0 (b := 1) (q_end := 112) rfl rfl
  have hev0 : Riemann120.Layer2.evalStack (Riemann120.Layer2.trimZeros P) =
      .decnz 4 (P ++ [0] ++ [1]) (P ++ [1]) := by
    have h := Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP0 (q' := 73) rfl rfl
    have htz := Riemann120.Layer2.evalStack_trimZeros_of_walkInternal hP0
    rw [Riemann120.Layer2.trimZeros_append_zero] at htz
    rw [← htz, Riemann120.Layer2.retStack_append_zero] at h
    simpa [Riemann120.Layer2.isLeafInc, Riemann120.Layer2.leafReg] using h
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
    try simp at hlen
  rcases v with _ | v'
  · have hs0 := Riemann120.Layer2.rhRegStep_of_decnz_zero (regs := [m, j, x, f, 0]) hev0 rfl
    have hP10 := Riemann120.Layer2.walkInternal_snoc hP1 (b := 0) (q_end := 65) rfl rfl
    obtain ⟨hm, hmlen⟩ := hmove (P ++ [1] ++ [0]) hP10 [m, j, x, f, 0] rfl
    rw [Riemann120.Layer2.trimZeros_append_zero, Riemann120.Layer2.trimZeros_append_one,
      Riemann120.Layer2.retStack_append_zero] at hm
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add,
      List.set_cons_zero, List.set_cons_succ] at hm
    have hscope : ∀ bits, OriginalCallerScope95 (P ++ [1] ++ [0]) bits →
        OriginalCallerScope95 P bits := by
      intro bits hb
      rcases hb with hb | ⟨suffix, hb⟩
      · rw [Riemann120.Layer2.trimZeros_append_zero,
          Riemann120.Layer2.trimZeros_append_one] at hb
        exact Or.inr ⟨[1], hb⟩
      · exact Or.inr ⟨[1] ++ [0] ++ suffix, by simpa only [List.append_assoc] using hb⟩
    have hm' : Relation.TransGen
        (fun a b : Riemann120.Layer2.RhRegCfg =>
          Riemann120.Layer2.rhRegStep a = some b ∧ OriginalCallerScope95 P a.stack)
        ⟨P ++ [1], [m, j, x, f, 0]⟩ ⟨P ++ [1] ++ [1], [m, 0, x, f, j]⟩ := by
      apply Relation.TransGen.mono ?_ _ _ hm
      intro a b h
      exact ⟨h.1, hscope a.stack h.2⟩
    have hev_x := Riemann120.Layer2.evalStack_leaf1_inc_of_walkInternal hP1 (q' := 99) rfl rfl rfl
    have hsx := Riemann120.Layer2.rhRegStep_of_inc (regs := [m, 0, x, f, j]) hev_x
    rw [Riemann120.Layer2.retStack_append_one] at hsx
    simp only [show Riemann120.Layer2.leafReg 99 = 2 from rfl,
      List.getD_cons_zero, List.getD_cons_succ, List.set_cons_zero, List.set_cons_succ] at hsx
    simp only [OriginalTickFn95, List.getD_cons_zero, List.getD_cons_succ, ↓reduceIte]
    refine ⟨?_, rfl⟩
    exact (Relation.TransGen.single ⟨hs0, Or.inl rfl⟩).trans
      (hm'.trans (Relation.TransGen.single ⟨hsx,
        Or.inr ⟨[1] ++ [1], by simp only [List.append_assoc]⟩⟩))
  · have hs0 := Riemann120.Layer2.rhRegStep_of_decnz_succ (regs := [m, j, x, f, v' + 1]) hev0 rfl
    have hev_inc : Riemann120.Layer2.evalStack (P ++ [0] ++ [1]) =
        .inc 1 (P ++ [0] ++ [1] ++ [1]) := by
      rw [Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP01 (q' := 44) rfl rfl]
      simp [Riemann120.Layer2.isLeafInc, Riemann120.Layer2.leafReg]
    have hev_brk : Riemann120.Layer2.evalStack (P ++ [0] ++ [1] ++ [1]) =
        .jump (Riemann120.Layer2.retStack P) := by
      have h := Riemann120.Layer2.evalStack_break1_of_walkInternal
        (P := P ++ [0] ++ [1]) (q' := 91) (k := 1) hP01 rfl (Or.inr ⟨rfl, rfl⟩)
      simpa [Riemann120.Layer2.retStack, Riemann120.Layer2.popBreakRev] using h
    have hs1 := Riemann120.Layer2.rhRegStep_of_inc (regs := [m, j, x, f, v']) hev_inc
    have hs2 := Riemann120.Layer2.rhRegStep_of_jump (regs := [m, j + 1, x, f, v']) hev_brk
    simp only [List.getD_cons_zero, List.getD_cons_succ,
      List.set_cons_zero, List.set_cons_succ] at hs0 hs1
    simp only [OriginalTickFn95, List.getD_cons_zero, List.getD_cons_succ,
      Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    refine ⟨?_, rfl⟩
    exact (Relation.TransGen.single ⟨hs0, Or.inl rfl⟩).trans
      ((Relation.TransGen.single ⟨hs1,
        Or.inr ⟨[0] ++ [1], by simp only [List.append_assoc]⟩⟩).trans
        (Relation.TransGen.single ⟨hs2,
          Or.inr ⟨[0] ++ [1] ++ [1], by simp only [List.append_assoc]⟩⟩))

theorem original_scoped_divide95 : OriginalScopedSubEval95 54 OriginalDivideFn95 := by
  have hcongr {q : Fin 121} {F G : List Nat → List Nat}
      (h : OriginalScopedSubEval95 q F)
      (heq : ∀ regs, regs.length = 5 → F regs = G regs) :
      OriginalScopedSubEval95 q G := by
    intro P hP regs hlen
    obtain ⟨hs, hl⟩ := h P hP regs hlen
    rw [heq regs hlen] at hs hl
    exact ⟨hs, hl⟩
  have hloop : OriginalScopedSubEval95 82 (fun regs =>
      let J := regs.getD 1 0 + regs.getD 4 0 + 1
      let N := regs.getD 2 0 * J + regs.getD 1 0 + regs.getD 0 0
      [0, N % J, N / J, regs.getD 3 0, J - 1 - N % J]) := by
    refine original_scoped_combinators95.2 82 31 94 101 0 OriginalTickFn95
      (fun regs =>
        let J := regs.getD 1 0 + regs.getD 4 0 + 1
        let N := regs.getD 2 0 * J + regs.getD 1 0 + regs.getD 0 0
        [0, N % J, N / J, regs.getD 3 0, J - 1 - N % J])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl original_scoped_tick95 ?_ ?_ ?_ ?_
    · intro regs hlen
      simp only [List.length_cons, List.length_nil]
    · intro regs hlen hm
      rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
        try simp only [List.length_nil, OfNat.zero_ne_ofNat, List.length_cons, zero_add,
      OfNat.one_ne_ofNat, Nat.reduceAdd, Nat.reduceEqDiff, List.getD_eq_getElem?_getD,
      Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.getD_some] at hlen hm
      subst hm
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
      have hj_lt : j < j + v + 1 := by omega
      have hdiv : (x * (j + v + 1) + j) / (j + v + 1) = x := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj_lt, Nat.add_zero]
      have hmod : (x * (j + v + 1) + j) % (j + v + 1) = j := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj_lt]
      simp [hdiv, hmod]
    · intro regs k hlen hm
      rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
        try simp only [List.length_nil, OfNat.zero_ne_ofNat, List.length_cons, zero_add,
      OfNat.one_ne_ofNat, Nat.reduceAdd, Nat.reduceEqDiff, List.getD_eq_getElem?_getD,
      Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.getD_some] at hlen hm
      subst hm
      rcases v with _ | v'
      · simp only [OriginalTickFn95, List.set, List.getD_cons_zero, List.getD_cons_succ,
          ↓reduceIte, Nat.zero_add, Nat.add_zero]
        have hN : (x + 1) * (j + 1) + k = x * (j + 1) + j + (k + 1) := by ring
        rw [hN]
      · simp only [OriginalTickFn95, List.set, List.getD_cons_zero, List.getD_cons_succ,
          Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        have hJ : j + 1 + v' + 1 = j + (v' + 1) + 1 := by omega
        have hJ2 : j + 1 + v' = j + (v' + 1) := by omega
        have hN : x * (j + (v' + 1) + 1) + (j + 1) + k =
            x * (j + (v' + 1) + 1) + j + (k + 1) := by ring
        rw [hJ, hJ2, hN]
    · intro regs k hlen hm
      rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
        try simp only [List.length_nil, OfNat.zero_ne_ofNat, List.length_cons, zero_add,
      OfNat.one_ne_ofNat, Nat.reduceAdd, Nat.reduceEqDiff, List.getD_eq_getElem?_getD,
      Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.getD_some] at hlen hm
      subst hm
      rcases v with _ | v' <;> simp [OriginalTickFn95]
  have hjv := original_scoped_move95 65 47 80 70 1 4 (by decide) (by decide)
    (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hxm := original_scoped_move95 81 71 93 4 2 0 (by decide) (by decide)
    (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have h66 := original_scoped_combinators95.1 66 81 82 _ _ rfl rfl rfl rfl hxm hloop
  apply hcongr (original_scoped_combinators95.1 54 65 66 _ _ rfl rfl rfl rfl hjv h66)
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> try simp at hlen
  simp only [OriginalDivideFn95, List.set, List.getD_cons_zero, List.getD_cons_succ,
    Nat.zero_add, Nat.add_zero, Nat.zero_mul]
  have h1 : m + x = x + m := by ring
  have h2 : j + v + 1 - 1 = j + v := by omega
  have h3 : v + j = j + v := by omega
  simp [h1, h2, h3]

theorem original_digits_scoped95 (j x f v : Nat) (hJ : 2 ≤ j + v + 1) : Relation.TransGen (fun a b
  : Riemann120.Layer2.RhRegCfg => Riemann120.Layer2.rhRegStep a = some b ∧ OriginalCallerScope95
  [1, 1, 1, 0] a.stack) ⟨[1, 1, 1], [0, j, x, f, v]⟩ ⟨[1, 1, 1, 1], [0, j + v, 0, f -
  Riemann120.offsetDigits (j + v + 1) x, 0]⟩ := by
  have hm60 : OriginalScopedSubEval95 60 (fun regs => (regs.set 4 0).set 1 (regs.getD 1 0 +
    regs.getD 4 0)) :=
    original_scoped_move95 60 _ _ _ 4 1 (by decide) (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hmap (suffix : List (Fin 2))
      (hs : OriginalCallerScope95 [1,1,1,0] (Riemann120.Layer2.trimZeros ([1,1,1,0] ++ suffix)))
      {a b : Riemann120.Layer2.RhRegCfg}
      (h : Relation.TransGen (fun c d : Riemann120.Layer2.RhRegCfg =>
        Riemann120.Layer2.rhRegStep c = some d ∧ OriginalCallerScope95 ([1,1,1,0] ++ suffix)
          c.stack) a b) :
      Relation.TransGen (fun c d : Riemann120.Layer2.RhRegCfg =>
        Riemann120.Layer2.rhRegStep c = some d ∧ OriginalCallerScope95 [1,1,1,0] c.stack) a b := by
    refine Relation.TransGen.mono (fun c d hc => ?_) a b h
    refine ⟨hc.1, ?_⟩
    rcases hc.2 with hc | ⟨t, ht⟩
    · simpa only [hc] using hs
    · exact Or.inr ⟨suffix ++ t, by simpa only [List.append_assoc] using ht⟩
  have hdecf (a b c d : Nat) :
      Relation.TransGen (fun u w : Riemann120.Layer2.RhRegCfg =>
        Riemann120.Layer2.rhRegStep u = some w ∧ OriginalCallerScope95 [1,1,1,0] u.stack)
        ⟨[1,1,1,0,0,1,1], [0,a,b,c,d]⟩
        ⟨[1,1,1,0,0,1,1,1], [0,a,b,c-1,d]⟩ := by
    cases c with
    | zero =>
      apply Relation.TransGen.single
      refine ⟨?_, Or.inr ⟨[0,1,1], rfl⟩⟩
      exact Riemann120.Layer2.rhRegStep_of_decnz_zero (by rfl) rfl
    | succ c =>
      have hs : Riemann120.Layer2.rhRegStep ⟨[1,1,1,0,0,1,1], [0,a,b,c+1,d]⟩ =
          some ⟨[1,1,1,0,0,1,1,0,1], [0,a,b,c,d]⟩ :=
        Riemann120.Layer2.rhRegStep_of_decnz_succ
          (s := [1,1,1,0,0,1,1]) (r := 3) (v := c) (by rfl) rfl
      have ht : Riemann120.Layer2.rhRegStep ⟨[1,1,1,0,0,1,1,0,1], [0,a,b,c,d]⟩ =
          some ⟨[1,1,1,0,0,1,1,1], [0,a,b,c,d]⟩ :=
        Riemann120.Layer2.rhRegStep_of_jump (by rfl)
      simpa only [Nat.add_sub_cancel] using
        (Relation.TransGen.single ⟨hs, Or.inr ⟨[0,1,1], rfl⟩⟩).tail
          ⟨ht, Or.inr ⟨[0,1,1,0,1], rfl⟩⟩
  induction x using Nat.strong_induction_on generalizing j f v with
  | h x ih =>
    cases x with
    | zero =>
      obtain ⟨hm, _⟩ := hm60 [1,1,1,0,1] rfl [0,j,0,f,v] rfl
      have hm' := hmap [1] (Or.inr ⟨[1], rfl⟩) hm
      have hs : Riemann120.Layer2.rhRegStep ⟨[1,1,1], [0,j,0,f,v]⟩ =
          some ⟨[1,1,1,0,1], [0,j,0,f,v]⟩ :=
        Riemann120.Layer2.rhRegStep_of_decnz_zero (by rfl) rfl
      have ht := (Relation.TransGen.single ⟨hs, Or.inl rfl⟩).trans hm'
      simpa [Riemann120.Layer2.retStack, Riemann120.Layer2.popBreakRev,
        Riemann120.Layer2.trimZeros, Riemann120.Layer2.dropLeadingZeros,
        Riemann120.offsetDigits] using ht
    | succ x =>
      let J := j + v + 1
      have hs : Riemann120.Layer2.rhRegStep ⟨[1,1,1], [0,j,x+1,f,v]⟩ =
          some ⟨[1,1,1,0,0,1], [0,j,x,f,v]⟩ :=
        Riemann120.Layer2.rhRegStep_of_decnz_succ
          (s := [1,1,1]) (r := 2) (v := x) (by rfl) rfl
      obtain ⟨hd, _⟩ := original_scoped_divide95 [1,1,1,0,0,1,0] rfl [0,j,x,f,v] rfl
      have hd' := hmap [0,1,0] (Or.inr ⟨[0,1], rfl⟩) hd
      simp only [Fin.isValue, Riemann120.Layer2.trimZeros, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.cons_append, Riemann120.Layer2.dropLeadingZeros,
        BEq.rfl, ↓reduceIte, Fin.reduceBEq, Bool.false_eq_true, Riemann120.Layer2.retStack,
        Riemann120.Layer2.popBreakRev, OriginalDivideFn95, List.getD_eq_getElem?_getD,
        List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
        List.getElem_cons_zero, Option.getD_some, Nat.reduceLT, List.getElem_cons_succ,
        Nat.one_lt_ofNat, Nat.lt_add_one, add_tsub_cancel_right] at hd'
      have hf := hdecf (x % J) (x / J) f (J - 1 - x % J)
      have hc : Riemann120.Layer2.rhRegStep
          ⟨[1,1,1,0,0,1,1,1], [0,x % J,x / J,f-1,J-1-x % J]⟩ =
          some ⟨[1,1,1], [0,x % J,x / J,f-1,J-1-x % J]⟩ :=
        Riemann120.Layer2.rhRegStep_of_jump (by rfl)
      have hr : x % J < J := Nat.mod_lt x (by dsimp [J]; omega)
      have hjv : x % J + (J - 1 - x % J) + 1 = J := by omega
      have hi := ih (x / J) (Nat.lt_succ_of_le (Nat.div_le_self x J))
        (x % J) (f-1) (J-1-x % J) (by rw [hjv]; exact hJ)
      have hoff : f - 1 - Riemann120.offsetDigits J (x / J) =
          f - Riemann120.offsetDigits J (x+1) := by
        simp [Riemann120.offsetDigits, show 2 ≤ J from hJ]
        omega
      have heq : x % J + (J-1-x % J) = j+v := by dsimp [J] at *; omega
      simp only [heq] at hi
      rw [hoff] at hi
      exact ((Relation.TransGen.single ⟨hs, Or.inl rfl⟩).trans hd').trans
        (hf.trans ((Relation.TransGen.single ⟨hc, Or.inr ⟨[0,1,1,1], rfl⟩⟩).trans hi))

theorem original_scoped_transform95 : OriginalScopedSubEval95 84 OriginalTransformFn95 := by
  have hl : OriginalScopedSubEval95 95 (fun regs =>
      let J := regs.getD 1 0 + regs.getD 4 0 + 1
      [0, regs.getD 1 0 + regs.getD 4 0,
        regs.getD 2 0 + regs.getD 0 0 * J + regs.getD 1 0, regs.getD 3 0, 0]) := by
    intro P hP
    have hP0 := Riemann120.Layer2.walkInternal_snoc hP (b := 0) (q_end := 102) rfl rfl
    have hP1 := Riemann120.Layer2.walkInternal_snoc hP (b := 1) (q_end := 103) rfl rfl
    have hP11 := Riemann120.Layer2.walkInternal_snoc hP1 (b := 1) (q_end := 89) rfl rfl
    have hev_m : Riemann120.Layer2.evalStack (P ++ [1]) =
        .decnz 0 (P ++ [1] ++ [1]) (Riemann120.Layer2.retStack P) := by
      rw [Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP1 (q' := 31) rfl rfl]
      simp [Riemann120.Layer2.isLeafInc, Riemann120.Layer2.leafReg,
        Riemann120.Layer2.retStack_append_one]
    have hev_x : Riemann120.Layer2.evalStack (P ++ [1] ++ [1]) =
        .inc 2 (P ++ [1] ++ [1] ++ [1]) := by
      rw [Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP11 (q' := 99) rfl rfl]
      simp [Riemann120.Layer2.isLeafInc, Riemann120.Layer2.leafReg]
    have hev_cont : Riemann120.Layer2.evalStack (P ++ [1] ++ [1] ++ [1]) =
        .jump (Riemann120.Layer2.trimZeros P) := by
      have h := Riemann120.Layer2.evalStack_continue1_of_walkInternal
        (P := P ++ [1] ++ [1]) (k := 2) hP11 rfl (Or.inr (Or.inr ⟨rfl, rfl⟩))
      simpa [Riemann120.Layer2.popContinueRev,
        Riemann120.Layer2.popContinueRev_zero_eq_dropLeadingZeros,
        Riemann120.Layer2.trimZeros] using h
    have hscope : ∀ suffix : List (Fin 2), OriginalCallerScope95 P (P ++ suffix) :=
      fun suffix => Or.inr ⟨suffix, rfl⟩
    let R := fun a b : Riemann120.Layer2.RhRegCfg =>
      Riemann120.Layer2.rhRegStep a = some b ∧ OriginalCallerScope95 P a.stack
    have hfold : ∀ k j x f v : Nat,
        Relation.TransGen R
          ⟨Riemann120.Layer2.trimZeros P, [k, j, x, f, v]⟩
          ⟨P ++ [1], [k, j + v, x + j, f, 0]⟩ := by
      intro k j x f v
      have hf := (original_scoped_fold95 (P ++ [0]) hP0 [k,j,x,f,v] rfl).1
      rw [Riemann120.Layer2.trimZeros_append_zero,
        Riemann120.Layer2.retStack_append_zero] at hf
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hf
      apply Relation.TransGen.mono (r := fun a b =>
        Riemann120.Layer2.rhRegStep a = some b ∧ OriginalCallerScope95 (P ++ [0]) a.stack) _ _ _ hf
      intro a b hab
      refine ⟨hab.1, ?_⟩
      rcases hab.2 with hz | ⟨suffix, hs⟩
      · left
        simpa only [Riemann120.Layer2.trimZeros_append_zero] using hz
      · right
        exact ⟨[0] ++ suffix, by simpa only [List.append_assoc] using hs⟩
    have hloop : ∀ k j x f v : Nat,
        Relation.TransGen R
          ⟨Riemann120.Layer2.trimZeros P, [k,j,x,f,v]⟩
          ⟨Riemann120.Layer2.retStack P,
            [0, j+v, x + k * (j+v+1) + j, f, 0]⟩ := by
      intro k
      induction k with
      | zero =>
        intro j x f v
        have hf := hfold 0 j x f v
        have hs := Riemann120.Layer2.rhRegStep_of_decnz_zero
          (regs := [0,j+v,x+j,f,0]) hev_m rfl
        simp only [Nat.zero_mul, Nat.add_zero]
        exact hf.trans (Relation.TransGen.single ⟨hs, hscope [1]⟩)
      | succ k ih =>
        intro j x f v
        have hf := hfold (k+1) j x f v
        have hs_m := Riemann120.Layer2.rhRegStep_of_decnz_succ
          (regs := [k+1,j+v,x+j,f,0]) hev_m rfl
        have hs_x := Riemann120.Layer2.rhRegStep_of_inc
          (regs := [k,j+v,x+j,f,0]) hev_x
        have hs_c := Riemann120.Layer2.rhRegStep_of_jump
          (regs := [k,j+v,x+j+1,f,0]) hev_cont
        have hi := ih (j+v) (x+j+1) f 0
        have h2 : x+j+1+k*(j+v+0+1)+(j+v) = x+(k+1)*(j+v+1)+j := by ring
        simp only [Nat.add_zero] at hi h2
        rw [h2] at hi
        have hm : R ⟨P ++ [1], [k+1,j+v,x+j,f,0]⟩
            ⟨P ++ [1] ++ [1], [k,j+v,x+j,f,0]⟩ := ⟨hs_m, hscope [1]⟩
        have hx : R ⟨P ++ [1] ++ [1], [k,j+v,x+j,f,0]⟩
            ⟨P ++ [1] ++ [1] ++ [1], [k,j+v,x+j+1,f,0]⟩ :=
          ⟨hs_x, by simpa only [List.append_assoc] using hscope ([1] ++ [1])⟩
        have hc : R ⟨P ++ [1] ++ [1] ++ [1], [k,j+v,x+j+1,f,0]⟩
            ⟨Riemann120.Layer2.trimZeros P, [k,j+v,x+j+1,f,0]⟩ :=
          ⟨hs_c, by simpa only [List.append_assoc] using hscope ([1] ++ ([1] ++ [1]))⟩
        exact hf.trans ((Relation.TransGen.single hm).trans
          ((Relation.TransGen.single hx).trans ((Relation.TransGen.single hc).trans hi)))
    intro regs hlen
    rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> try simp at hlen
    exact ⟨hloop m j x f v, rfl⟩
  have hm : OriginalScopedSubEval95 81 (fun regs =>
      (regs.set 2 0).set 0 (regs.getD 0 0 + regs.getD 2 0)) := by
    exact original_scoped_move95 81 _ _ _ 2 0 (by decide) (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hseq := original_scoped_combinators95.1 84 81 95 _ _ rfl rfl rfl rfl hm hl
  intro P hP regs hlen
  have hs := hseq P hP regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> try simp at hlen
  simpa [OriginalTransformFn95] using hs

theorem original_scoped_product_step95 : OriginalScopedSubEval95 38 OriginalProductStepFn95 := by
  have scope_one (P : List (Fin 2)) (s : List (Fin 2))
      (h : OriginalCallerScope95 (P ++ [1]) s) : OriginalCallerScope95 P s := by
    rcases h with h | ⟨suffix, h⟩
    · exact Or.inr ⟨[1], by simpa only [Riemann120.Layer2.trimZeros_append_one] using h⟩
    · exact Or.inr ⟨[1] ++ suffix, by simpa only [List.append_assoc] using h⟩
  have inc_seq : ∀ (q q₀ q₁ : Fin 121) (F : List Nat → List Nat),
      Riemann120.rh121Trans q 0 = some (0, .right, q₀) →
      Riemann120.Layer2.isLeafState q₀ = true →
      Riemann120.Layer2.isLeafInc q₀ = true →
      Riemann120.rh121Trans q 1 = some (1, .right, q₁) →
      Riemann120.Layer2.isInternalNode q₁ = true →
      OriginalScopedSubEval95 q₁ F →
      OriginalScopedSubEval95 q (fun regs =>
        F (regs.set (Riemann120.Layer2.leafReg q₀)
          (regs.getD (Riemann120.Layer2.leafReg q₀) 0 + 1))) := by
    intro q q₀ q₁ F htr0 hleaf hinc htr1 hq₁ hF P hP regs hlen
    have hev : Riemann120.Layer2.evalStack (Riemann120.Layer2.trimZeros P) =
        .inc (Riemann120.Layer2.leafReg q₀) (P ++ [1]) := by
      rw [Riemann120.Layer2.evalStack_trimZeros_of_walkInternal hP,
        Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP htr0 hleaf]
      simp only [hinc, ↓reduceIte]
    have hs := Riemann120.Layer2.rhRegStep_of_inc (regs := regs) hev
    have hP1 := Riemann120.Layer2.walkInternal_snoc hP htr1 hq₁
    obtain ⟨hpath, hlength⟩ := hF (P ++ [1]) hP1
      (regs.set (Riemann120.Layer2.leafReg q₀)
        (regs.getD (Riemann120.Layer2.leafReg q₀) 0 + 1)) (by simpa only [List.length_set] using
          hlen)
    rw [Riemann120.Layer2.trimZeros_append_one,
      Riemann120.Layer2.retStack_append_one] at hpath
    refine ⟨(Relation.TransGen.single ⟨hs, Or.inl rfl⟩).trans ?_, hlength⟩
    refine Relation.TransGen.mono ?_ _ _ hpath
    intro a b hab
    exact ⟨hab.1, scope_one P a.stack hab.2⟩
  have decnz_seq : ∀ (q q₀ q₁ : Fin 121) (F : List Nat → List Nat),
      Riemann120.rh121Trans q 0 = some (0, .right, q₀) →
      Riemann120.Layer2.isLeafState q₀ = true →
      Riemann120.Layer2.isLeafInc q₀ = false →
      Riemann120.rh121Trans q 1 = some (1, .right, q₁) →
      Riemann120.Layer2.isInternalNode q₁ = true →
      OriginalScopedSubEval95 q₁ F →
      OriginalScopedSubEval95 q (fun regs =>
        if regs.getD (Riemann120.Layer2.leafReg q₀) 0 = 0 then regs
        else F (regs.set (Riemann120.Layer2.leafReg q₀)
          (regs.getD (Riemann120.Layer2.leafReg q₀) 0 - 1))) := by
    intro q q₀ q₁ F htr0 hleaf hdec htr1 hq₁ hF P hP regs hlen
    have hev : Riemann120.Layer2.evalStack (Riemann120.Layer2.trimZeros P) =
        .decnz (Riemann120.Layer2.leafReg q₀) (P ++ [1]) (Riemann120.Layer2.retStack P) := by
      rw [Riemann120.Layer2.evalStack_trimZeros_of_walkInternal hP,
        Riemann120.Layer2.evalStack_leaf0_of_walkInternal hP htr0 hleaf]
      simp only [hdec, Bool.false_eq_true, ↓reduceIte]
    rcases hv : regs.getD (Riemann120.Layer2.leafReg q₀) 0 with _ | v
    · simp only [hv, ↓reduceIte]
      exact ⟨Relation.TransGen.single ⟨Riemann120.Layer2.rhRegStep_of_decnz_zero hev hv,
        Or.inl rfl⟩, hlen⟩
    · simp only [hv, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      have hs := Riemann120.Layer2.rhRegStep_of_decnz_succ hev hv
      have hP1 := Riemann120.Layer2.walkInternal_snoc hP htr1 hq₁
      obtain ⟨hpath, hlength⟩ := hF (P ++ [1]) hP1
        (regs.set (Riemann120.Layer2.leafReg q₀) v) (by simpa only [List.length_set] using hlen)
      rw [Riemann120.Layer2.trimZeros_append_one,
        Riemann120.Layer2.retStack_append_one] at hpath
      refine ⟨(Relation.TransGen.single ⟨hs, Or.inl rfl⟩).trans ?_, hlength⟩
      refine Relation.TransGen.mono ?_ _ _ hpath
      intro a b hab
      exact ⟨hab.1, scope_one P a.stack hab.2⟩
  have congr {q : Fin 121} {F G : List Nat → List Nat}
      (h : OriginalScopedSubEval95 q F)
      (heq : ∀ regs, regs.length = 5 → F regs = G regs) : OriginalScopedSubEval95 q G := by
    intro P hP regs hlen
    simpa only [heq regs hlen] using h P hP regs hlen
  rcases original_scoped_combinators95 with ⟨hseq, _⟩
  have h68 : OriginalScopedSubEval95 68 (fun regs =>
      let J := regs.getD 1 0 + regs.getD 4 0 + 1
      let x1 := (regs.getD 0 0 + regs.getD 2 0) * J + regs.getD 1 0
      [0, J - 1, x1 * J + (J - 1), regs.getD 3 0, 0]) := by
    apply congr (hseq 68 84 84 _ _ rfl rfl rfl rfl
      original_scoped_transform95 original_scoped_transform95)
    intro regs hlen
    rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
      simp [OriginalTransformFn95] at hlen ⊢
  have h83 : OriginalScopedSubEval95 83 (fun regs =>
      let J := regs.getD 1 0 + (regs.getD 4 0 + 1) + 1
      [0, regs.getD 1 0 + (regs.getD 4 0 + 1),
        (regs.getD 0 0 + regs.getD 2 0) * J + regs.getD 1 0, regs.getD 3 0, 0]) := by
    apply congr (inc_seq 83 70 84 _ rfl rfl rfl rfl rfl original_scoped_transform95)
    intro regs hlen
    rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
      simp [OriginalTransformFn95, Riemann120.Layer2.leafReg] at hlen ⊢
  have h67 : OriginalScopedSubEval95 67 (fun regs =>
      if regs.getD 4 0 = 0 then regs else
        let J := regs.getD 1 0 + regs.getD 4 0 + 1
        [0, regs.getD 1 0 + regs.getD 4 0,
          (regs.getD 0 0 + regs.getD 2 0) * J + regs.getD 1 0, regs.getD 3 0, 0]) := by
    apply congr (decnz_seq 67 73 83 _ rfl rfl rfl rfl rfl h83)
    intro regs hlen
    rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;>
      try simp at hlen
    rcases v with _ | v' <;> simp [Riemann120.Layer2.leafReg]
  have h55 := hseq 55 67 68 _ _ rfl rfl rfl rfl h67 h68
  have h45 := hseq 45 54 55 _ _ rfl rfl rfl rfl original_scoped_divide95 h55
  apply congr (inc_seq 38 44 45 _ rfl rfl rfl rfl rfl h45)
  intro regs hlen
  rcases regs with _ | ⟨m, _ | ⟨j, _ | ⟨x, _ | ⟨f, _ | ⟨v, _ | _⟩⟩⟩⟩⟩ <;> try simp at hlen
  simp only [OriginalDivideFn95, OriginalProductStepFn95, Riemann120.Layer2.leafReg,
    List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add]
  have hr_lt : (m + x) % (j + 1 + v + 1) < j + 1 + v + 1 := Nat.mod_lt (m + x) (by omega)
  by_cases hv0 : j + 1 + v - (m + x) % (j + 1 + v + 1) = 0
  · have hr_eq : (m + x) % (j + 1 + v + 1) = j + 1 + v := by omega
    simp [hr_eq]
  · have hjv : (m + x) % (j + 1 + v + 1) + (j + 1 + v - (m + x) % (j + 1 + v + 1)) =
        j + 1 + v := by omega
    simp [hv0, hjv]

theorem original_product_scoped95 (M : Nat) : Relation.TransGen (fun a b :
  Riemann120.Layer2.RhRegCfg => Riemann120.Layer2.rhRegStep a = some b ∧ OriginalCallerScope95 [1,
  0] a.stack) ⟨[1], [0, 0, 0, M, 0]⟩ ⟨[1, 1], [0, M + 1, Riemann120.shuniaProd (M + 2) - 1, 0, 0]⟩
  := by
  have lift {P Q : List (Fin 2)} {a b : Riemann120.Layer2.RhRegCfg}
      (hs : ∀ s, OriginalCallerScope95 Q s → OriginalCallerScope95 P s)
      (h : Relation.TransGen (fun x y => Riemann120.Layer2.rhRegStep x = some y ∧
        OriginalCallerScope95 Q x.stack) a b) :
      Relation.TransGen (fun x y => Riemann120.Layer2.rhRegStep x = some y ∧ OriginalCallerScope95
        P x.stack) a b := by
    exact Relation.TransGen.mono (fun x y hxy => ⟨hxy.1, hs x.stack hxy.2⟩) a b h
  have hs : ∀ s, OriginalCallerScope95 ([1,0] ++ [0]) s → OriginalCallerScope95 [1,0] s := by
    intro s h
    rcases h with h | ⟨suffix, h⟩
    · exact Or.inl (h.trans (Riemann120.Layer2.trimZeros_append_zero [1,0]))
    · exact Or.inr ⟨[0] ++ suffix, by simpa only [List.append_assoc] using h⟩
  have hfn (K f : Nat) (hK : 2 ≤ K) :
      OriginalProductStepFn95 [0,K-2,Riemann120.shuniaProd (K-1)-1,f,0] =
        [0,K-1,Riemann120.shuniaProd K-1,f,0] :=
    Riemann120.Layer2.product_step_shuniaProd hK f
  have hev_f : Riemann120.Layer2.evalStack [1,0,1] =
      .decnz 3 [1,0,1,1] [1,1] := rfl
  have hev_c : Riemann120.Layer2.evalStack [1,0,1,1] = .jump [1] := rfl
  have loop (rem : Nat) : ∀ K : Nat, 2 ≤ K →
      Relation.TransGen (fun a b : Riemann120.Layer2.RhRegCfg => Riemann120.Layer2.rhRegStep a =
        some b ∧ OriginalCallerScope95 [1,0] a.stack)
        ⟨[1],[0,K-2,Riemann120.shuniaProd (K-1)-1,rem,0]⟩
        ⟨[1,1],[0,K+rem-1,Riemann120.shuniaProd (K+rem)-1,0,0]⟩ := by
    induction rem with
    | zero =>
      intro K hK
      obtain ⟨hp, _⟩ := original_scoped_product_step95 ([1,0] ++ [0]) rfl
        [0,K-2,Riemann120.shuniaProd (K-1)-1,0,0] rfl
      have hp := lift hs hp
      rw [hfn K 0 hK] at hp
      change Relation.TransGen _ (⟨[1], _⟩ : Riemann120.Layer2.RhRegCfg)
        (⟨[1,0,1], _⟩ : Riemann120.Layer2.RhRegCfg) at hp
      have hf := Riemann120.Layer2.rhRegStep_of_decnz_zero
        (regs := [0,K-1,Riemann120.shuniaProd K-1,0,0]) hev_f rfl
      simpa only [Nat.add_zero] using
        hp.tail ⟨hf, Or.inr ⟨[1], rfl⟩⟩
    | succ rem ih =>
      intro K hK
      obtain ⟨hp, _⟩ := original_scoped_product_step95 ([1,0] ++ [0]) rfl
        [0,K-2,Riemann120.shuniaProd (K-1)-1,rem+1,0] rfl
      have hp := lift hs hp
      rw [hfn K (rem+1) hK] at hp
      change Relation.TransGen _ (⟨[1], _⟩ : Riemann120.Layer2.RhRegCfg)
        (⟨[1,0,1], _⟩ : Riemann120.Layer2.RhRegCfg) at hp
      have hf := Riemann120.Layer2.rhRegStep_of_decnz_succ
        (regs := [0,K-1,Riemann120.shuniaProd K-1,rem+1,0]) hev_f rfl
      have hc := Riemann120.Layer2.rhRegStep_of_jump
        (regs := [0,K-1,Riemann120.shuniaProd K-1,rem,0]) hev_c
      have hr := ih (K+1) (by omega)
      have h_in : [0,K+1-2,Riemann120.shuniaProd (K+1-1)-1,rem,0] =
          [0,K-1,Riemann120.shuniaProd K-1,rem,0] := rfl
      have hadd : K+1+rem = K+(rem+1) := by omega
      rw [h_in, hadd] at hr
      have hpf := hp.tail ⟨hf, Or.inr ⟨[1], rfl⟩⟩
      have hpfc := hpf.tail ⟨hc, Or.inr ⟨[1,1], rfl⟩⟩
      exact hpfc.trans hr
  have h1 : Riemann120.shuniaProd 1 = 1 := by decide
  have h2 : 2+M = M+2 := by omega
  have h3 : M+2-1 = M+1 := by omega
  simpa only [h1, h2, h3, Nat.reduceSub] using loop M 2 (by omega)

theorem original_seed_guarded95 (j x : Nat) : Relation.TransGen (OriginalRegionEdge95 62 66) ⟨[1,
  1], [0, j, x, 0, 0]⟩ ⟨[1, 1, 1], [0, 0, x, j, j]⟩ := by
  have loop : ∀ (n f v : Nat), Relation.TransGen (OriginalRegionEdge95 62 66)
      ⟨[1,1],[0,n,x,f,v]⟩ ⟨[1,1,1],[0,0,x,f+n,v+n]⟩ := by
    intro n
    induction n with
    | zero =>
      intro f v
      apply Relation.TransGen.single
      constructor
      · rfl
      · exact ⟨⟨62, by decide⟩, by decide, by decide, DefaultLookup95.oldWord62.symm⟩
    | succ n ih =>
      intro f v
      have e1 : OriginalRegionEdge95 62 66
          ⟨[1,1],[0,n+1,x,f,v]⟩ ⟨[1,1,0,1],[0,n,x,f,v]⟩ := by
        constructor
        · rfl
        · exact ⟨⟨62, by decide⟩, by decide, by decide, DefaultLookup95.oldWord62.symm⟩
      have e2 : OriginalRegionEdge95 62 66
          ⟨[1,1,0,1],[0,n,x,f,v]⟩ ⟨[1,1,0,1,0,1],[0,n,x,f,v+1]⟩ := by
        constructor
        · rfl
        · exact ⟨⟨63, by decide⟩, by decide, by decide, DefaultLookup95.oldWord63.symm⟩
      have e3 : OriginalRegionEdge95 62 66
          ⟨[1,1,0,1,0,1],[0,n,x,f,v+1]⟩ ⟨[1,1,0,1,1],[0,n,x,f+1,v+1]⟩ := by
        constructor
        · rfl
        · exact ⟨⟨64, by decide⟩, by decide, by decide, DefaultLookup95.oldWord64.symm⟩
      have e4 : OriginalRegionEdge95 62 66
          ⟨[1,1,0,1,1],[0,n,x,f+1,v+1]⟩ ⟨[1,1],[0,n,x,f+1,v+1]⟩ := by
        constructor
        · rfl
        · exact ⟨⟨65, by decide⟩, by decide, by decide, DefaultLookup95.oldWord65.symm⟩
      have cycle : Relation.TransGen (OriginalRegionEdge95 62 66)
          ⟨[1,1],[0,n+1,x,f,v]⟩ ⟨[1,1],[0,n,x,f+1,v+1]⟩ :=
        ((Relation.TransGen.single e1).tail e2).tail e3 |>.tail e4
      have result := cycle.trans (ih (f+1) (v+1))
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using result
  simpa only [Nat.zero_add] using loop j 0 0

theorem original_prewidth_cut_routines95 : (∀ M : Nat, StateTransition.Reaches₁
  ReferencePreOldStep95 ⟨[1], [0, 0, 0, M, 0]⟩ ⟨[1, 1], [0, M + 1, Riemann120.shuniaProd (M + 2) -
  1, 0, 0]⟩) ∧ (∀ j x : Nat, StateTransition.Reaches₁ ReferencePreOldStep95 ⟨[1, 1], [0, j, x, 0,
  0]⟩ ⟨[1, 1, 1], [0, 0, x, j, j]⟩) ∧ (∀ j x f v : Nat, 2 ≤ j + v + 1 → StateTransition.Reaches₁
  ReferencePreOldStep95 ⟨[1, 1, 1], [0, j, x, f, v]⟩ ⟨[1, 1, 1, 1], [0, j + v, 0, f -
  Riemann120.offsetDigits (j + v + 1) x, 0]⟩) := by
  constructor
  · intro M
    apply original_scope_cut_transfer95 [1,0] _ _ _ (original_product_scoped95 M)
    intro bits hscope
    rcases hscope with htrim | ⟨suffix, hsuffix⟩
    · subst bits
      decide
    · subst bits
      simp only [List.cons_append, List.nil_append, ne_eq, List.cons.injEq,
        Fin.reduceEq, false_and, and_false, not_false_eq_true]
  · constructor
    · intro j x
      apply original_regions_cut_lift95 62 66 _ _ _ (original_seed_guarded95 j x)
      intro s hlo hhi
      have hs : s.val = 62 ∨ s.val = 63 ∨ s.val = 64 ∨ s.val = 65 := by omega
      rcases hs with hs | hs | hs | hs
      · have he : s = (62 : Fin 121) := Fin.ext hs
        subst s
        decide +kernel
      · have he : s = (63 : Fin 121) := Fin.ext hs
        subst s
        decide +kernel
      · have he : s = (64 : Fin 121) := Fin.ext hs
        subst s
        decide +kernel
      · have he : s = (65 : Fin 121) := Fin.ext hs
        subst s
        decide +kernel
    · intro j x f v hJ
      apply original_scope_cut_transfer95 [1,1,1,0] _ _ _
        (original_digits_scoped95 j x f v hJ)
      intro bits hscope
      rcases hscope with htrim | ⟨suffix, hsuffix⟩
      · subst bits
        decide
      · subst bits
        simp only [List.cons_append, List.nil_append, ne_eq, List.cons.injEq,
          Fin.reduceEq, false_and, and_false, not_false_eq_true]

theorem original_prewidth_cut95 (M : Nat) : StateTransition.Reaches₁ ReferencePreOldStep95
  (Riemann104.FiniteStage.stageCfg M) ⟨[1, 1, 1, 1], [0, M + 1, 0, Riemann120.shuniaDeficit (M +
  2), 0]⟩ := by
  have hmove : ∀ m f : Nat, StateTransition.Reaches₁ ReferencePreOldStep95
      (Riemann120.Layer2.RhRegCfg.mk [] [m,0,0,f,0])
      ⟨[1],[0,0,0,f+m,0]⟩ := by
    intro m
    induction m with
    | zero =>
      intro f
      exact Relation.TransGen.single (show ReferencePreOldStep95 ⟨[],[0,0,0,f,0]⟩ =
        some ⟨[1],[0,0,0,f+0,0]⟩ from rfl)
    | succ m ih =>
      intro f
      have h0 : ReferencePreOldStep95 ⟨[],[m+1,0,0,f,0]⟩ =
          some ⟨[0,1],[m,0,0,f,0]⟩ := by rfl
      have h1 : ReferencePreOldStep95 ⟨[0,1],[m,0,0,f,0]⟩ =
          some ⟨[0,1,1],[m,0,0,f+1,0]⟩ := by rfl
      have h2 : ReferencePreOldStep95 ⟨[0,1,1],[m,0,0,f+1,0]⟩ =
          some ⟨[],[m,0,0,f+1,0]⟩ := by rfl
      have h0r : StateTransition.Reaches₁ ReferencePreOldStep95
          ⟨[],[m+1,0,0,f,0]⟩ ⟨[0,1],[m,0,0,f,0]⟩ :=
        Relation.TransGen.single h0
      have h1r : StateTransition.Reaches₁ ReferencePreOldStep95
          ⟨[0,1],[m,0,0,f,0]⟩ ⟨[0,1,1],[m,0,0,f+1,0]⟩ :=
        Relation.TransGen.single h1
      have h2r : StateTransition.Reaches₁ ReferencePreOldStep95
          ⟨[0,1,1],[m,0,0,f+1,0]⟩ ⟨[],[m,0,0,f+1,0]⟩ :=
        Relation.TransGen.single h2
      have hh : StateTransition.Reaches₁ ReferencePreOldStep95
          ⟨[],[m+1,0,0,f,0]⟩ ⟨[1],[0,0,0,f+1+m,0]⟩ :=
        h0r.trans (h1r.trans (h2r.trans (ih (f+1))))
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  have h₁ : StateTransition.Reaches₁ ReferencePreOldStep95
      (Riemann104.FiniteStage.stageCfg M) ⟨[1],[0,0,0,M,0]⟩ := by
    simpa only [Riemann104.FiniteStage.stageCfg, Nat.zero_add] using hmove M 0
  rcases original_prewidth_cut_routines95 with ⟨hprod, hseed, hdigits⟩
  have h₂ := hprod M
  have h₃ := hseed (M+1) (Riemann120.shuniaProd (M+2)-1)
  have hJ : 2 ≤ 0 + (M+1) + 1 := by omega
  have h₄ := hdigits 0 (Riemann120.shuniaProd (M+2)-1) (M+1) (M+1) hJ
  have hsum : M+1+1 = M+2 := by omega
  have hsub : M+2-1 = M+1 := by omega
  have h₄' : StateTransition.Reaches₁ ReferencePreOldStep95
      ⟨[1,1,1],[0,0,Riemann120.shuniaProd (M+2)-1,M+1,M+1]⟩
      ⟨[1,1,1,1],[0,M+1,0,Riemann120.shuniaDeficit (M+2),0]⟩ := by
    simpa only [Nat.zero_add, hsum, Riemann120.shuniaDeficit, hsub] using h₄
  exact h₁.trans (h₂.trans (h₃.trans h₄'))

theorem reference_halts_iff_stage1_witness95 : Halts Riemann104.candidate ↔ ∃ M : Nat, 1 ≤ M ∧
  Riemann120.ShuniaCounterexample (M + 2) := by
  have hmain : Halts Riemann104.candidate ↔
      ∃ n ≥ 2, Riemann120.ShuniaCounterexample n :=
    Riemann104.halts_candidate_iff_halts_edited121
      |>.trans (Riemann120.halts_tm_iff_rhRegHaltsOf true)
      |>.trans Riemann104.rhRegHalts_true_iff_false
      |>.trans Riemann120.rhRegHaltsOf_false_iff_rhRegHalts
      |>.trans Riemann120.Layer2.rhRegHalts_iff_exists_shuniaCounterexample
  rw [hmain]
  have htwo : ¬ Riemann120.ShuniaCounterexample 2 :=
    Riemann104.FiniteStage.earlier_stages_safe (M := 1) (by decide)
      (j := 0) (by decide)
  constructor
  · rintro ⟨n, hn, hce⟩
    have hn2 : n ≠ 2 := by
      intro heq
      exact htwo (heq ▸ hce)
    refine ⟨n - 2, by omega, ?_⟩
    have heq : n - 2 + 2 = n := by omega
    simpa only [heq] using hce
  · rintro ⟨M, hM, hce⟩
    exact ⟨M + 2, by omega, hce⟩

section
attribute [local irreducible] ReferenceLogical.rows ReferenceLogical.row
  ReferenceLogical.word ReferenceLogical.oldWord ReferenceLogical.rowInstr
  ReferenceLogical.role ReferenceLogical.Spec

theorem reference_prewidth_cut_transport95 : StateTransition.Respects ReferencePreStep95
  ReferencePreOldStep95 (fun fresh old : Riemann120.Layer2.RhRegCfg => fresh.regs.length = 5 ∧ ∃ s
  : Fin 89, fresh.stack = ReferenceProgram.word ⟨s.val, by omega⟩ ∧ old.stack =
  ReferenceProgram.oldWord ⟨s.val, by omega⟩ ∧ ReferenceLogical.RegRel ⟨s.val, by omega⟩
  (ReferenceProgram.decodeBank fresh.regs) old.regs) := by
  have hchart : ∀ t : Fin 88,
      ReferenceLogical.role ⟨t.val, Nat.lt_trans t.isLt (by decide : 88 < 121)⟩ ≠ .halfDec ∧
      ReferenceProgram.oldWord ⟨t.val, Nat.lt_trans t.isLt (by decide : 88 < 121)⟩ ≠ [1,1,1,1] ∧
      ReferenceProgram.word ⟨t.val, Nat.lt_trans t.isLt (by decide : 88 < 121)⟩ ≠
        ReferenceProgram.word 88 ∧
      Riemann120.evalStackOf true (ReferenceLogical.oldWord ⟨t.val, Nat.lt_trans t.isLt (by decide
        : 88 < 121)⟩) =
        Riemann120.Layer2.evalStack (ReferenceLogical.oldWord ⟨t.val, Nat.lt_trans t.isLt (by
          decide : 88 < 121)⟩) ∧
      (match ReferenceLogical.rowInstr ⟨t.val, Nat.lt_trans t.isLt (by decide : 88 < 121)⟩ with
       | .halt => false
       | .jump n | .inc _ n => decide (n.val < 89)
       | .decnz _ p z => decide (p.val < 89 ∧ z.val < 89)) = true := by decide +kernel
  intro fresh old h
  rcases h with ⟨hlen, s, hf, ho, hr⟩
  by_cases hs : s.val = 88
  · have ht : (⟨s.val, by omega⟩ : Fin 121) = 88 := Fin.ext hs
    rw [ht] at hf ho
    have hw : ReferenceProgram.oldWord 88 = [1,1,1,1] := by decide +kernel
    simp only [ReferencePreStep95, ReferencePreOldStep95, hf, ho, hw, ↓reduceIte]
  · have hslt : s.val < 88 := by omega
    obtain ⟨hrole, hcutOld, hcutFresh, heval, htargets⟩ := hchart ⟨s.val, hslt⟩
    rcases fresh with ⟨fw, fr⟩
    rcases old with ⟨ow, ors⟩
    dsimp only at hf ho hlen hr
    subst fw
    subst ow
    let t : Fin 121 := ⟨s.val, by omega⟩
    let regs := ReferenceProgram.decodeBank fr
    change ReferenceLogical.RegRel t regs ors at hr
    change (match ReferenceLogical.rowInstr t with
      | .halt => false
      | .jump n | .inc _ n => decide (n.val < 89)
      | .decnz _ p z => decide (p.val < 89 ∧ z.val < 89)) = true at htargets
    have hl : regs.length = 5 := ReferenceProgram.decodeBank_length fr
    have hp : ReferenceProgram.encodeCfg ⟨ReferenceLogical.word t, regs⟩ =
        (⟨ReferenceProgram.word t, fr⟩ : Riemann120.Layer2.RhRegCfg) := by
      unfold ReferenceProgram.encodeCfg
      dsimp only
      rw [ReferenceProgram.encode_decode fr hlen]
      rfl
    have hstep : ReferenceProgram.step ⟨ReferenceProgram.word t, fr⟩ =
        (ReferenceLogical.step ⟨ReferenceLogical.word t, regs⟩).map ReferenceProgram.encodeCfg := by
      rw [← hp]
      exact ReferenceProgram.step_encode _ hl
    have holdstep : ReferencePreOldStep95 ⟨ReferenceProgram.oldWord t, ors⟩ =
        Riemann120.rhRegStepOf true ⟨ReferenceLogical.oldWord t, ors⟩ := by
      unfold ReferencePreOldStep95
      rw [ite_eq_right hcutOld]
      unfold Riemann120.rhRegStepOf Riemann120.Layer2.rhRegStep
      dsimp only
      rw [heval]
      rfl
    have hpre : ReferencePreStep95 ⟨ReferenceProgram.word t, fr⟩ =
        (ReferenceLogical.step ⟨ReferenceLogical.word t, regs⟩).map ReferenceProgram.encodeCfg := by
      unfold ReferencePreStep95
      rw [ite_eq_right hcutFresh]
      exact hstep
    have hmatch : ∃ (n : Fin 121), n.val < 89 ∧ ∃ nr no : List Nat,
        nr.length = 5 ∧ ReferenceLogical.RegRel n nr no ∧
        ReferenceLogical.step ⟨ReferenceLogical.word t, regs⟩ = some ⟨ReferenceLogical.word n, nr⟩ ∧
        Riemann120.rhRegStepOf true ⟨ReferenceLogical.oldWord t, ors⟩ = some
          ⟨ReferenceLogical.oldWord n, no⟩ := by
      cases hrt : ReferenceLogical.role t with
      | halfDec => exact False.elim (hrole hrt)
      | plain =>
        have heq : ors = regs := (show regs.length = 5 ∧ ors = regs from by
          simpa only [ReferenceLogical.RegRel, hrt] using hr).2
        have hc := ReferenceLogical.specs t
        simp only [ReferenceLogical.Spec, hrt] at hc
        cases hi : ReferenceLogical.rowInstr t with
        | halt => simp only [hi, Bool.false_eq_true] at htargets
        | jump n =>
          have hn : n.val < 89 := by simpa only [hi, decide_eq_true_eq] using htargets
          refine ⟨n, hn, regs, regs, hl, ?_, ?_, ?_⟩
          · apply ReferenceLogical.regRel_ordinary n
            · simpa only [hi, ReferenceLogical.ordinaryTargets] using hc.2
            · exact hl
            · rfl
          · rw [ReferenceLogical.step_on_word]
            simp only [ReferenceLogical.decoded, hi, ReferenceLogical.toInstr,
              ReferenceLogical.applyInstr]
          · rw [heq]
            exact ReferenceLogical.old_step _ _ regs (by simpa only [hi, ReferenceLogical.toInstr]
              using hc.1)
        | inc r n =>
          have hn : n.val < 89 := by simpa only [hi, decide_eq_true_eq] using htargets
          have hnr : (ReferenceLogical.incReg r regs).length = 5 := (ReferenceLogical.inc_length r
            regs).trans hl
          refine ⟨n, hn, ReferenceLogical.incReg r regs, ReferenceLogical.incReg r regs, hnr, ?_,
            ?_, ?_⟩
          · apply ReferenceLogical.regRel_ordinary n
            · simpa only [hi, ReferenceLogical.ordinaryTargets] using hc.2
            · exact hnr
            · rfl
          · rw [ReferenceLogical.step_on_word]
            simp only [ReferenceLogical.decoded, hi, ReferenceLogical.toInstr,
              ReferenceLogical.applyInstr]
          · rw [heq]
            exact ReferenceLogical.old_step _ _ regs (by simpa only [hi, ReferenceLogical.toInstr]
              using hc.1)
        | decnz r p z =>
          have hn : p.val < 89 ∧ z.val < 89 := by simpa only [hi, decide_eq_true_eq] using htargets
          have hordinary : ReferenceLogical.ordinary p ∧ ReferenceLogical.ordinary z := by
            simpa only [hi, ReferenceLogical.ordinaryTargets] using hc.2
          have hOld := ReferenceLogical.old_step _ _ regs
            (show Riemann120.evalStackOf true (ReferenceLogical.oldWord t) =
              Riemann120.Layer2.RhInstr.decnz r (ReferenceLogical.oldWord p)
                (ReferenceLogical.oldWord z) from by
              simpa only [hi, ReferenceLogical.toInstr] using hc.1)
          by_cases hz : (regs.getD r 0 == 0) = true
          · refine ⟨z, hn.2, regs, regs, hl, ?_, ?_, ?_⟩
            · exact ReferenceLogical.regRel_ordinary z hordinary.2 regs regs hl rfl
            · rw [ReferenceLogical.step_on_word]
              simp only [ReferenceLogical.decoded, hi, ReferenceLogical.toInstr,
                ReferenceLogical.applyInstr, hz, ↓reduceIte]
            · rw [heq]
              simpa only [ReferenceLogical.applyInstr, hz, ↓reduceIte] using hOld
          · have hfalse : (regs.getD r 0 == 0) = false := Bool.eq_false_iff.mpr hz
            have hnr : (regs.set r (regs.getD r 0 - 1)).length = 5 := by simpa only
              [List.length_set] using hl
            refine ⟨p, hn.1, regs.set r (regs.getD r 0 - 1), regs.set r (regs.getD r 0 - 1), hnr,
              ?_, ?_, ?_⟩
            · exact ReferenceLogical.regRel_ordinary p hordinary.1 _ _ hnr rfl
            · rw [ReferenceLogical.step_on_word]
              simp only [ReferenceLogical.decoded, hi, ReferenceLogical.toInstr,
                ReferenceLogical.applyInstr, hfalse, Bool.false_eq_true, ↓reduceIte]
            · rw [heq]
              simpa only [ReferenceLogical.applyInstr, hfalse, Bool.false_eq_true, ↓reduceIte]
                using hOld
      | firstSwap r =>
        have heq : ors = regs := (show regs.length = 5 ∧ ors = regs from by
          simpa only [ReferenceLogical.RegRel, hrt] using hr).2
        have hc := ReferenceLogical.specs t
        simp only [ReferenceLogical.Spec, hrt] at hc
        cases hi : ReferenceLogical.rowInstr t <;> simp only [hi] at hc
        case inc r' n =>
          obtain ⟨hr', hnrole, hOld, _⟩ := hc
          subst r'
          have hn : n.val < 89 := by simpa only [hi, decide_eq_true_eq] using htargets
          have hnr : (ReferenceLogical.incReg r regs).length = 5 := (ReferenceLogical.inc_length r
            regs).trans hl
          refine ⟨n, hn, ReferenceLogical.incReg r regs, ReferenceLogical.incReg 4 regs, hnr, ?_,
            ?_, ?_⟩
          · simp only [ReferenceLogical.RegRel, hnrole]
            exact ⟨regs, hl, rfl, rfl⟩
          · rw [ReferenceLogical.step_on_word]
            simp only [ReferenceLogical.decoded, hi, ReferenceLogical.toInstr,
              ReferenceLogical.applyInstr]
          · rw [heq]
            exact ReferenceLogical.old_step _ _ regs hOld
      | secondSwap r =>
        have hc := ReferenceLogical.specs t
        simp only [ReferenceLogical.Spec, hrt] at hc
        have hreg : ∃ base : List Nat, base.length = 5 ∧ regs = ReferenceLogical.incReg r base ∧
          ors = ReferenceLogical.incReg 4 base := by
          simpa only [ReferenceLogical.RegRel, hrt] using hr
        obtain ⟨base, hb, hfr, hor⟩ := hreg
        cases hi : ReferenceLogical.rowInstr t <;> simp only [hi] at hc
        case inc r' n =>
          obtain ⟨hr', hnordinary, hOld, hrange⟩ := hc
          subst r'
          have hn : n.val < 89 := by simpa only [hi, decide_eq_true_eq] using htargets
          have hnr : (ReferenceLogical.incReg 4 regs).length = 5 := (ReferenceLogical.inc_length 4
            regs).trans hl
          refine ⟨n, hn, ReferenceLogical.incReg 4 regs, ReferenceLogical.incReg r ors, hnr, ?_,
            ?_, ?_⟩
          · apply ReferenceLogical.regRel_ordinary n hnordinary _ _ hnr
            rw [hfr, hor]
            exact ReferenceLogical.inc_commute r base hb hrange
          · rw [ReferenceLogical.step_on_word]
            simp only [ReferenceLogical.decoded, hi, ReferenceLogical.toInstr,
              ReferenceLogical.applyInstr]
          · exact ReferenceLogical.old_step _ _ ors hOld
    obtain ⟨n, hn, nr, no, hnr, hrel, hnew, hold⟩ := hmatch
    rw [hpre, hnew]
    simp only [Option.map_some]
    refine ⟨⟨ReferenceLogical.oldWord n, no⟩, ?_, Relation.TransGen.single ?_⟩
    · refine ⟨ReferenceProgram.encodeBank_length nr, ⟨n.val, hn⟩, rfl, rfl, ?_⟩
      simpa only [ReferenceProgram.encodeCfg, ReferenceProgram.decode_encode nr hnr] using hrel
    · rw [holdstep]
      exact hold

theorem reference_prewidth_execution95 (M : Nat) : StateTransition.Reaches₁ ReferencePreStep95
  (ReferenceProgram.stageCfg M) ⟨ReferenceProgram.word 88, [0, 0, Riemann120.shuniaDeficit (M +
  2), 0, M + 1]⟩ := by
  have hstart : (ReferenceProgram.stageCfg M).regs.length = 5 ∧ ∃ s : Fin 89,
      (ReferenceProgram.stageCfg M).stack = ReferenceProgram.word ⟨s.val, by omega⟩ ∧
      (Riemann104.FiniteStage.stageCfg M).stack = ReferenceProgram.oldWord ⟨s.val, by omega⟩ ∧
      ReferenceLogical.RegRel ⟨s.val, by omega⟩
        (ReferenceProgram.decodeBank (ReferenceProgram.stageCfg M).regs)
        (Riemann104.FiniteStage.stageCfg M).regs := by
    refine ⟨rfl, (0 : Fin 89), ?_, ?_, ?_⟩
    · exact DefaultLookup95.word0.symm
    · exact DefaultLookup95.oldWord0.symm
    · have h0 : (⟨(0 : Fin 89).val, by omega⟩ : Fin 121) = 0 := Fin.ext rfl
      rw [h0, ReferenceLogical.RegRel, DefaultLookup95.role0]
      exact ⟨rfl, rfl⟩
  have hmem : (⟨[1,1,1,1], [0,M+1,0,Riemann120.shuniaDeficit (M+2),0]⟩ :
      Riemann120.Layer2.RhRegCfg) ∈ StateTransition.eval ReferencePreOldStep95
        (Riemann104.FiniteStage.stageCfg M) := by
    apply StateTransition.mem_eval.mpr
    exact ⟨(original_prewidth_cut95 M).to_reflTransGen, by simp [ReferencePreOldStep95]⟩
  obtain ⟨fresh, ⟨hlen, s, hword, hold, hreg⟩, hfresh⟩ :=
    StateTransition.tr_eval_rev reference_prewidth_cut_transport95 hstart hmem
  have hunique : ∀ t : Fin 89, ReferenceProgram.oldWord (t.castLE (by decide)) = [1,1,1,1] →
      t.val = 88 := by decide +kernel
  have hs : s.val = 88 := hunique s hold.symm
  have hs' : (⟨s.val, by omega⟩ : Fin 121) = 88 := by apply Fin.ext; exact hs
  rw [hs'] at hword hreg
  have hr : ReferenceLogical.role 88 = .plain := DefaultLookup95.role88
  simp only [ReferenceLogical.RegRel, hr] at hreg
  have hbank : fresh.regs = [0,0,Riemann120.shuniaDeficit (M+2),0,M+1] := by
    calc
      fresh.regs = ReferenceProgram.encodeBank (ReferenceProgram.decodeBank fresh.regs) :=
        (ReferenceProgram.encode_decode fresh.regs hlen).symm
      _ = ReferenceProgram.encodeBank [0,M+1,0,Riemann120.shuniaDeficit (M+2),0] :=
        congrArg ReferenceProgram.encodeBank hreg.2.symm
      _ = [0,0,Riemann120.shuniaDeficit (M+2),0,M+1] := rfl
  have heq : fresh = ⟨ReferenceProgram.word 88,[0,0,Riemann120.shuniaDeficit (M+2),0,M+1]⟩ := by
    cases fresh
    exact congrArg₂ Riemann120.Layer2.RhRegCfg.mk hword hbank
  have hreach := (StateTransition.mem_eval.mp hfresh).1
  rw [heq] at hreach
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hreach with hsame | hnontrivial
  · have hstack := congrArg Riemann120.Layer2.RhRegCfg.stack hsame
    change ReferenceProgram.word 88 = [] at hstack
    rw [DefaultLookup95.word88] at hstack
    cases hstack
  · exact hnontrivial

end

end ConjectureMachines.Riemann95
