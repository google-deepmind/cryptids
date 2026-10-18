/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.Jump95
public import Cryptids.ReductionSupport.Riemann95.ParserSchema95
public import Cryptids.ReductionSupport.Riemann95.TypedClosure95
public import Cryptids.ReductionSupport.Riemann95.Physical95

@[expose] public section

namespace ConjectureMachines.Riemann95.RootJump

open Turing ConjectureMachines
open ConjectureMachines.Riemann120 (rootLeftOf stackLeftOf)
open Schema
open FinitePrefix
open CryptidsResearch.Recursive95Parser

theorem root_layout (pad : Nat) (bank : List Nat) (v : Word) (K : Nat)
    (hv : v.length ≤ K) (hK : K ≤ pad) :
    (⟨15, Tape.mk' (rootLeftOf true)
      (ListBlank.append (v ++ List.replicate (K - v.length) 0)
        (ListBlank.mk (List.replicate (pad - K) 0 ++ [1, 0] ++
          Semantics.Riemann.Layer1.encodeRegs bank)))⟩ : ConjectureMachines.Cfg 95 2) =
      Physical.rootCfg pad v bank := by
  unfold Physical.rootCfg
  rw [show pad - v.length = K - v.length + (pad - K) by omega, List.replicate_add]
  simp only [ListBlank.append_mk, List.append_assoc]
  rfl

theorem root_append (pad : Nat) (word : Word) (bank : List Nat) :
    Physical.rootCfg pad word bank =
      ⟨15, Tape.mk' (rootLeftOf true)
        (ListBlank.append word (ListBlank.append (List.replicate (pad - word.length) 0)
          (ListBlank.append [1, 0] (Semantics.Riemann.Layer1.regsTape bank))))⟩ := by
  unfold Physical.rootCfg Semantics.Riemann.Layer1.regsTape
  rw [show (default : ListBlank (Fin 2)) = ListBlank.mk [] from rfl]
  simp only [ListBlank.append_mk, List.append_nil, List.append_assoc]
  rfl

/-- Lift any exact terminal-to-root jump with a retained zero suffix through
the actual parser, with precisely the original padding and arbitrary bank. -/
theorem root_of_terminal (source walked target : Word) (q : Fin 95) (erased : Nat)
    (hsource : source = walked ++ [1])
    (hparse : walkInternal 15 walked = some q)
    (hlen : source.length = target.length + erased)
    (hj : ∀ R : ListBlank (Fin 2), ∃ s ≥ 1,
      nSteps s ⟨q, Tape.mk' (stackLeftOf true walked) (R.cons 1)⟩ =
        some ⟨15, Tape.mk' (rootLeftOf true)
          (ListBlank.append target (ListBlank.append (List.replicate erased 0) R))⟩)
    (pad : Nat) (hpad : walked.length + 3 ≤ pad) (bank : List Nat) :
    ∃ s ≥ 1, nSteps s (Physical.rootCfg pad source bank) =
      some (Physical.rootCfg pad target bank) := by
  let R := ListBlank.append (List.replicate (pad - source.length) 0)
    (ListBlank.append [1, 0] (Semantics.Riemann.Layer1.regsTape bank))
  have hstart : Physical.rootCfg pad source bank =
      ⟨15, Tape.mk' (rootLeftOf true) (ListBlank.append walked (R.cons 1))⟩ := by
    rw [root_append]
    dsimp only [R]
    rw [hsource]
    simp only [ListBlank.append_assoc, ListBlank.append]
  have hp := walkInternal_nSteps walked 15 q (rootLeftOf true) (R.cons 1) hparse
  rw [← hstart] at hp
  change nSteps walked.length (Physical.rootCfg pad source bank) =
    some ⟨q, Tape.mk' (stackLeftOf true walked) (R.cons 1)⟩ at hp
  obtain ⟨s, hs, ht⟩ := hj R
  have hfinish :
      (⟨15, Tape.mk' (rootLeftOf true)
        (ListBlank.append target (ListBlank.append (List.replicate erased 0) R))⟩ :
          ConjectureMachines.Cfg 95 2) = Physical.rootCfg pad target bank := by
    have hsl : source.length ≤ pad := by
      rw [hsource, List.length_append] at *
      simp only [List.length_singleton] at *
      omega
    have hgap : pad - target.length = erased + (pad - source.length) := by omega
    rw [root_append, hgap, List.replicate_add]
    simp only [ListBlank.append_assoc]
    rfl
  rw [hfinish] at ht
  exact ⟨walked.length + s, by omega, Jump.nSteps_bind hp ht⟩

def outsideSteps : Array Nat := #[
  0,0,12,0,0,0,22,0,0,24,0,0,0,30,0,0,32,0,24,0,0,0,0,28,0,0,0,34,
  0,0,34,0,0,30,0,0,26,0,0,0,32,0,0,32,0,0,28,0,0,26,0,0,0,32,0,0,
  32,0,0,28,0,14,0,0,0,18,0,0,0,26,0,0,28,0,0,0,34,0,0,36,0,28,0,24,
  22,0,0,22,0,0,0,24,0,0,24,0,0]

def outsideCertificate (i : Fin 97) : Prop :=
  let word := outsideWord i
  let K := (outsideWalk i).length + 3
  let n := outsideSteps.getD i.val 0
  match Control.rawInstr (.outside i) with
  | .jump target => word.length ≤ K ∧ target.length ≤ K ∧ 1 ≤ n ∧
      prefixRun95 n 15 [1, 0, 0, 0]
        (word ++ List.replicate (K - word.length) 0) =
          some (15, [1, 0, 0, 0], target ++ List.replicate (K - target.length) 0)
  | _ => True

instance (i : Fin 97) : Decidable (outsideCertificate i) := by
  unfold outsideCertificate
  split <;> infer_instance

theorem outside_certificate : ∀ i : Fin 97, outsideCertificate i := by decide +kernel

theorem root_outside (i : Fin 97) (target : Word)
    (h : Control.rawInstr (.outside i) = .jump target)
    (pad : Nat) (hpad : (Control.walked (.outside i)).length + 3 ≤ pad)
    (bank : List Nat) :
    ∃ s ≥ 1, nSteps s (Physical.rootCfg pad (word (.outside i)) bank) =
      some (Physical.rootCfg pad target bank) := by
  have hc := outside_certificate i
  unfold outsideCertificate at hc
  rw [h] at hc
  obtain ⟨hw, ht, hn, hr⟩ := hc
  have he := prefixRun96_sound hr (default : ListBlank (Fin 2))
    (ListBlank.mk (List.replicate (pad - ((outsideWalk i).length + 3)) 0 ++ [1, 0] ++
      Semantics.Riemann.Layer1.encodeRegs bank))
  have hleft : ListBlank.append [1, 0, 0, 0] (default : ListBlank (Fin 2)) =
      rootLeftOf true := by
    simp only [ListBlank.append, Semantics.Riemann.Layer1.default_cons_zero]
    rfl
  change (outsideWalk i).length + 3 ≤ pad at hpad
  rw [hleft, root_layout pad bank _ _ hw hpad, root_layout pad bank _ _ ht hpad] at he
  exact ⟨outsideSteps.getD i.val 0, hn, he⟩

theorem root43 (P : Word) (pad : Nat) (bank : List Nat)
    (hp : walkInternal 15 (P ++ [1, 0, 0, 1, 1]) = some 43)
    (hg : Riemann104.OnePassGuard.NoThreeZeros (1 :: (P ++ [1])).reverse = true)
    (hpad : (P ++ [1, 0, 0, 1, 1]).length + 3 ≤ pad) :
    ∃ n ≥ 1, nSteps n (Physical.rootCfg pad (P ++ [1, 0, 0, 1, 1, 1]) bank) =
      some (Physical.rootCfg pad (P ++ [1]) bank) := by
  exact root_of_terminal _ _ _ 43 5 (by simp only [List.append_assoc]; rfl) hp
    (by simp only [List.length_append, List.length_cons, List.length_nil])
    (fun R => Jump.jump43 P R hg) pad hpad bank

theorem root59 (P : Word) (pad : Nat) (bank : List Nat)
    (hp : walkInternal 15 (P ++ [1, 1]) = some 59)
    (hg : Riemann104.OnePassGuard.NoThreeZeros (1 :: (P ++ [1])).reverse = true)
    (hpad : (P ++ [1, 1]).length + 3 ≤ pad) :
    ∃ n ≥ 1, nSteps n (Physical.rootCfg pad (P ++ [1, 1, 1]) bank) =
      some (Physical.rootCfg pad (P ++ [1]) bank) := by
  exact root_of_terminal _ _ _ 59 2 (by simp only [List.append_assoc]; rfl) hp
    (by simp only [List.length_append, List.length_cons, List.length_nil])
    (fun R => Jump.jump59 P R hg) pad hpad bank

theorem root19 (P : Word) (pad : Nat) (bank : List Nat)
    (hp : walkInternal 15 (P ++ [1, 1]) = some 19)
    (hg : Riemann104.OnePassGuard.NoThreeZeros (1 :: (P ++ [1])).reverse = true)
    (hpad : (P ++ [1, 1]).length + 3 ≤ pad) :
    ∃ n ≥ 1, nSteps n (Physical.rootCfg pad (P ++ [1, 1, 1]) bank) =
      some (Physical.rootCfg pad (P ++ [1]) bank) := by
  exact root_of_terminal _ _ _ 19 2 (by simp only [List.append_assoc]; rfl) hp
    (by simp only [List.length_append, List.length_cons, List.length_nil])
    (fun R => Jump.jump19 P R hg) pad hpad bank

theorem root_local (d : Nat) (s : Fin 22) (target : Word)
    (h : Control.rawInstr (.local d s) = .jump target)
    (pad : Nat) (hpad : (Control.walked (.local d s)).length + 3 ≤ pad)
    (bank : List Nat) :
    ∃ n ≥ 1, nSteps n (Physical.rootCfg pad (word (.local d s)) bank) =
      some (Physical.rootCfg pad target bank) := by
  have hnext : Control.applyInstr (Control.rawInstr (.local d s)) bank =
      some ⟨target, bank⟩ := by rw [h]; rfl
  have hg := (Control.decoded_next_noThree (.local d s) bank _ hnext).2
  have hp := localWalk_parse d s
  fin_cases s <;> first
    | (solve | cases h)
    | skip
  case «3» =>
    have ht : target = callerPrefix d ++ [1] := by
      simpa [Control.rawInstr, Control.effect, Control.localEffects, Control.walked,
        Control.returned, localWalk, localWalkSuffix, localWalkSuffixes,
        Riemann120.Layer2.popContinueRev, List.reverse_append] using h.symm
    subst target
    have hsuf : suffix (⟨3, by decide⟩ : Fin 22) = [1, 0, 0, 1, 1, 1] := by decide +kernel
    have hw : localWalkSuffix (⟨3, by decide⟩ : Fin 22) = [1, 0, 0, 1, 1] := by decide +kernel
    have hq : localTerminal (⟨3, by decide⟩ : Fin 22) = 43 := by decide +kernel
    have hp' : walkInternal 15 ((callerPrefix d) ++ [1, 0, 0, 1, 1]) = some 43 := by
      simpa only [localWalk, hw, hq, List.append_assoc, List.cons_append,
        List.nil_append] using hp
    have hg' :
        Riemann104.OnePassGuard.NoThreeZeros (1 :: ((callerPrefix d) ++ [1])).reverse = true := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hg
    have hpad' : ((callerPrefix d) ++ [1, 0, 0, 1, 1]).length + 3 ≤ pad := by
      simpa only [Control.walked, localWalk, hw, List.append_assoc,
        List.cons_append, List.nil_append] using hpad
    simpa only [word, hsuf, List.append_assoc, List.cons_append, List.nil_append] using
      root43 (callerPrefix d) pad bank hp' hg' hpad'
  case «6» =>
    have ht : target = callerPrefix d ++ [1, 0, 1] := by
      simpa [Control.rawInstr, Control.effect, Control.localEffects, Control.walked,
        Control.returned, localWalk, localWalkSuffix, localWalkSuffixes,
        Riemann120.Layer2.popContinueRev, List.reverse_append] using h.symm
    subst target
    have hsuf : suffix (⟨6, by decide⟩ : Fin 22) = [1, 0, 1, 1, 1] := by decide +kernel
    have hw : localWalkSuffix (⟨6, by decide⟩ : Fin 22) = [1, 0, 1, 1] := by decide +kernel
    have hq : localTerminal (⟨6, by decide⟩ : Fin 22) = 59 := by decide +kernel
    have hp' : walkInternal 15 ((callerPrefix d ++ [1, 0]) ++ [1, 1]) = some 59 := by
      simpa only [localWalk, hw, hq, List.append_assoc, List.cons_append,
        List.nil_append] using hp
    have hg' :
        Riemann104.OnePassGuard.NoThreeZeros
          (1 :: ((callerPrefix d ++ [1, 0]) ++ [1])).reverse = true := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hg
    have hpad' : ((callerPrefix d ++ [1, 0]) ++ [1, 1]).length + 3 ≤ pad := by
      simpa only [Control.walked, localWalk, hw, List.append_assoc,
        List.cons_append, List.nil_append] using hpad
    simpa only [word, hsuf, List.append_assoc, List.cons_append, List.nil_append] using
      root59 (callerPrefix d ++ [1, 0]) pad bank hp' hg' hpad'
  case «10» =>
    have ht : target = callerPrefix d ++ [1, 1] := by
      simpa [Control.rawInstr, Control.effect, Control.localEffects, Control.walked,
        Control.returned, localWalk, localWalkSuffix, localWalkSuffixes,
        Riemann120.Layer2.popContinueRev, List.reverse_append] using h.symm
    subst target
    have hsuf : suffix (⟨10, by decide⟩ : Fin 22) = [1, 1, 0, 0, 1, 1, 1] := by decide +kernel
    have hw : localWalkSuffix (⟨10, by decide⟩ : Fin 22) = [1, 1, 0, 0, 1, 1] := by decide +kernel
    have hq : localTerminal (⟨10, by decide⟩ : Fin 22) = 43 := by decide +kernel
    have hp' : walkInternal 15 ((callerPrefix d ++ [1]) ++ [1, 0, 0, 1, 1]) = some 43 := by
      simpa only [localWalk, hw, hq, List.append_assoc, List.cons_append,
        List.nil_append] using hp
    have hg' :
        Riemann104.OnePassGuard.NoThreeZeros
          (1 :: ((callerPrefix d ++ [1]) ++ [1])).reverse = true := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hg
    have hpad' : ((callerPrefix d ++ [1]) ++ [1, 0, 0, 1, 1]).length + 3 ≤ pad := by
      simpa only [Control.walked, localWalk, hw, List.append_assoc,
        List.cons_append, List.nil_append] using hpad
    simpa only [word, hsuf, List.append_assoc, List.cons_append, List.nil_append] using
      root43 (callerPrefix d ++ [1]) pad bank hp' hg' hpad'
  case «13» =>
    have ht : target = callerPrefix d ++ [1, 1, 0, 1] := by
      simpa [Control.rawInstr, Control.effect, Control.localEffects, Control.walked,
        Control.returned, localWalk, localWalkSuffix, localWalkSuffixes,
        Riemann120.Layer2.popContinueRev, List.reverse_append] using h.symm
    subst target
    have hsuf : suffix (⟨13, by decide⟩ : Fin 22) = [1, 1, 0, 1, 1, 1] := by decide +kernel
    have hw : localWalkSuffix (⟨13, by decide⟩ : Fin 22) = [1, 1, 0, 1, 1] := by decide +kernel
    have hq : localTerminal (⟨13, by decide⟩ : Fin 22) = 59 := by decide +kernel
    have hp' : walkInternal 15 ((callerPrefix d ++ [1, 1, 0]) ++ [1, 1]) = some 59 := by
      simpa only [localWalk, hw, hq, List.append_assoc, List.cons_append,
        List.nil_append] using hp
    have hg' :
        Riemann104.OnePassGuard.NoThreeZeros
          (1 :: ((callerPrefix d ++ [1, 1, 0]) ++ [1])).reverse = true := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hg
    have hpad' : ((callerPrefix d ++ [1, 1, 0]) ++ [1, 1]).length + 3 ≤ pad := by
      simpa only [Control.walked, localWalk, hw, List.append_assoc,
        List.cons_append, List.nil_append] using hpad
    simpa only [word, hsuf, List.append_assoc, List.cons_append, List.nil_append] using
      root59 (callerPrefix d ++ [1, 1, 0]) pad bank hp' hg' hpad'
  case «17» =>
    have ht : target = callerPrefix d ++ [1, 1, 1] := by
      simpa [Control.rawInstr, Control.effect, Control.localEffects, Control.walked,
        Control.returned, localWalk, localWalkSuffix, localWalkSuffixes,
        Riemann120.Layer2.popContinueRev, List.reverse_append] using h.symm
    subst target
    have hsuf : suffix (⟨17, by decide⟩ : Fin 22) = [1, 1, 1, 0, 0, 1, 1, 1] := by decide +kernel
    have hw : localWalkSuffix (⟨17, by decide⟩ : Fin 22) = [1, 1, 1, 0, 0, 1, 1] := by
      decide +kernel
    have hq : localTerminal (⟨17, by decide⟩ : Fin 22) = 43 := by decide +kernel
    have hp' : walkInternal 15 ((callerPrefix d ++ [1, 1]) ++ [1, 0, 0, 1, 1]) = some 43 := by
      simpa only [localWalk, hw, hq, List.append_assoc, List.cons_append,
        List.nil_append] using hp
    have hg' :
        Riemann104.OnePassGuard.NoThreeZeros
          (1 :: ((callerPrefix d ++ [1, 1]) ++ [1])).reverse = true := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hg
    have hpad' : ((callerPrefix d ++ [1, 1]) ++ [1, 0, 0, 1, 1]).length + 3 ≤ pad := by
      simpa only [Control.walked, localWalk, hw, List.append_assoc,
        List.cons_append, List.nil_append] using hpad
    simpa only [word, hsuf, List.append_assoc, List.cons_append, List.nil_append] using
      root43 (callerPrefix d ++ [1, 1]) pad bank hp' hg' hpad'
  case «20» =>
    have ht : target = callerPrefix d ++ [1, 1, 1, 0, 1] := by
      simpa [Control.rawInstr, Control.effect, Control.localEffects, Control.walked,
        Control.returned, localWalk, localWalkSuffix, localWalkSuffixes,
        Riemann120.Layer2.popContinueRev, List.reverse_append] using h.symm
    subst target
    have hsuf : suffix (⟨20, by decide⟩ : Fin 22) = [1, 1, 1, 0, 1, 1, 1] := by decide +kernel
    have hw : localWalkSuffix (⟨20, by decide⟩ : Fin 22) = [1, 1, 1, 0, 1, 1] := by decide +kernel
    have hq : localTerminal (⟨20, by decide⟩ : Fin 22) = 19 := by decide +kernel
    have hp' : walkInternal 15 ((callerPrefix d ++ [1, 1, 1, 0]) ++ [1, 1]) = some 19 := by
      simpa only [localWalk, hw, hq, List.append_assoc, List.cons_append,
        List.nil_append] using hp
    have hg' :
        Riemann104.OnePassGuard.NoThreeZeros
          (1 :: ((callerPrefix d ++ [1, 1, 1, 0]) ++ [1])).reverse = true := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hg
    have hpad' : ((callerPrefix d ++ [1, 1, 1, 0]) ++ [1, 1]).length + 3 ≤ pad := by
      simpa only [Control.walked, localWalk, hw, List.append_assoc,
        List.cons_append, List.nil_append] using hpad
    simpa only [word, hsuf, List.append_assoc, List.cons_append, List.nil_append] using
      root19 (callerPrefix d ++ [1, 1, 1, 0]) pad bank hp' hg' hpad'

theorem root_jump (c : ControlWord) (target : Word)
    (h : Control.rawInstr c = .jump target) (pad : Nat)
    (hpad : (Control.walked c).length + 3 ≤ pad) (bank : List Nat) :
    ∃ s ≥ 1, nSteps s (Physical.rootCfg pad (word c) bank) =
      some (Physical.rootCfg pad target bank) := by
  cases c with
  | outside i => exact root_outside i target h pad hpad bank
  | entry d => simp [Control.rawInstr, Control.effect] at h
  | «local» d s => exact root_local d s target h pad hpad bank

end ConjectureMachines.Riemann95.RootJump
