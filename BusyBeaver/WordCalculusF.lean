module

public import BusyBeaver.Counter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.WordVKQ

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)

@[scoped simp] lemma zMz (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 0 = some config := rfl
@[scoped simp] lemma zMo (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 1 = step M config := rfl
@[scoped simp] lemma zMs (M : Machine zG_ zL_) (config : Cfg zG_ zL_) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[scoped simp] lemma z00 : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[scoped simp] lemma zDh : (default : zB).head = 0 := rfl
@[scoped simp] lemma zDt : (default : zB).tail = default := rfl
@[scoped simp] lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[scoped simp] lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[scoped simp] lemma append_assoc (l1 l2 : zF) (s : zB) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, append_cons, ih]

lemma zSm {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (M : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [M]⊢ c_2) :
    c_1 [M]⊢^{1} c_2 := by simp [h]
lemma z01 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (M : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [M]⊢ c_2) :
    c_1 [M]⊢⁺ c_2 := ⟨1, by decide, zSm M c_1 c_2 h⟩
lemma zMa {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (M : Machine zG_ zL_) (c_1 : Cfg zG_ zL_) (n m : Nat) :
    multiStep M c_1 (n + m) = (multiStep M c_1 n).bind (fun c_2 => multiStep M c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (M : Machine zG_ zL_) (c_1 c_2 c_3 : Cfg zG_ zL_) (n m : Nat)
    (h1 : c_1 [M]⊢^{n} c_2) (h2 : c_2 [M]⊢^{m} c_3) :
    c_1 [M]⊢^{n+m} c_3 := by
  rw [zMa, h1]; simp [h2]
lemma zPs {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {M : Machine zG_ zL_} {c_1 c_2 : Cfg zG_ zL_} (h : c_1 [M]⊢⁺ c_2) :
    c_1 [M]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma zPt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {M : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h1 : c_1 [M]⊢⁺ c_2) (h2 : c_2 [M]⊢⁺ c_3) : c_1 [M]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h1; obtain ⟨m, m_pos, hm⟩ := h2
  exact ⟨n + m, by omega, zMt M c_1 c_2 c_3 n m hn hm⟩
lemma z02 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {M : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h1 : c_1 [M]⊢⁺ c_2) (h2 : c_2 [M]⊢* c_3) : c_1 [M]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h1; obtain ⟨m, hm⟩ := h2
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt M c_1 c_2 c_3 n m hn hm⟩
lemma z03 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {M : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h1 : c_1 [M]⊢ c_2) (h2 : c_2 [M]⊢* c_3) : c_1 [M]⊢⁺ c_3 :=
  z02 (z01 M c_1 c_2 h1) h2

abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev z04 (c : CCfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨some c.q, ⟨c.cur, c.l +> default, c.r +> default⟩⟩

abbrev V_u : zF := [1, 1, 0, 0]
abbrev K_u : zF := [0, 0]
abbrev Q_u : zF := [1, 0]
abbrev Vp : zF := [0, 1, 1, 0]
abbrev Kp : zF := [0, 0]
abbrev Qp : zF := [0, 1]

@[scoped simp] lemma zKd : K_u +> (default : zB) = default := by simp [K_u]
@[scoped simp] lemma zKpd : Kp +> (default : zB) = default := by simp [Kp]

inductive Call where
  | ch
  | ca
deriving DecidableEq

inductive SideP {Call : Type*} (z0f : Call -> zB -> zB -> Prop) : List Call -> zB -> zB -> Prop where
  | nil (w : zB) : SideP z0f [] w w
  | cons {c : Call} {ls : List Call} {w1 w2 w3 : zB} :
      z0f c w1 w2 -> SideP z0f ls w2 w3 -> SideP z0f (c :: ls) w1 w3

abbrev SegP {Call : Type*} (z0f : Call -> zB -> zB -> Prop) (ls_in ls_out : List Call) (w1 w2 : zF) : Prop :=
  ∀ u1 u2, SideP z0f ls_out u1 u2 -> SideP z0f ls_in (w1 +> u1) (w2 +> u2)

@[scoped simp] lemma z0g {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[scoped simp] lemma zLp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[scoped simp] lemma zLp' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[scoped simp] lemma z0h {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l
lemma z0i {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.add_right_comm, zLp, zLp, ih, List.append_assoc]


lemma z0j {Call : Type*} {z0f : Call -> zB -> zB -> Prop} {ls1 ls2 : List Call} {w1 w2 w3 : zB}
    (h1 : SideP z0f ls1 w1 w2) (h2 : SideP z0f ls2 w2 w3) : SideP z0f (ls1 ++ ls2) w1 w3 := by
  induction h1 with
  | nil _ => exact h2
  | cons hc _ ih => exact SideP.cons hc (ih h2)

lemma z0k {Call : Type*} {z0f : Call -> zB -> zB -> Prop} {ls1 ls2 : List Call} {w1 w3 : zB}
    (h : SideP z0f (ls1 ++ ls2) w1 w3) : ∃ w2, SideP z0f ls1 w1 w2 ∧ SideP z0f ls2 w2 w3 := by
  induction ls1 generalizing w1 with
  | nil => exact ⟨w1, SideP.nil w1, h⟩
  | cons c ls1 ih =>
    rcases h with _ | ⟨hc, hrest⟩
    rcases ih hrest with ⟨w2, h1, h2⟩
    exact ⟨w2, SideP.cons hc h1, h2⟩

lemma z0l {Call : Type*} {z0f : Call -> zB -> zB -> Prop} (w : zF) : SegP z0f [] [] w w := by
  intro u1 u2 h; cases h; exact SideP.nil (w +> u1)

lemma z0m {Call : Type*} {z0f : Call -> zB -> zB -> Prop} (ls : List Call) : SegP z0f ls ls [] [] := by
  intro u1 u2 h; exact h

lemma zSc {Call : Type*} {z0f : Call -> zB -> zB -> Prop} {ls1 ls2 : List Call} {w1 w2 : zF} {u1 u2 : zB}
    (h1 : SegP z0f ls1 ls2 w1 w2) (h2 : SideP z0f ls2 u1 u2) :
    SideP z0f ls1 (w1 +> u1) (w2 +> u2) :=
  h1 u1 u2 h2

lemma zSg {Call : Type*} {z0f : Call -> zB -> zB -> Prop} {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : zF}
    (h1 : SegP z0f ls1 ls2 w1 w2) (h2 : SegP z0f ls3 ls4 w2 w3) :
    SegP z0f (ls1 ++ ls3) (ls2 ++ ls4) w1 w3 := by
  intro u1 u3 h
  rcases z0k h with ⟨u2, ha, hb⟩
  exact z0j (h1 u1 u2 ha) (h2 u2 u3 hb)

lemma zS0 {Call : Type*} {z0f : Call -> zB -> zB -> Prop} {ls1 ls2 ls3 : List Call} {w1 w2 v1 v2 : zF}
    (h1 : SegP z0f ls1 ls2 w1 w2) (h2 : SegP z0f ls2 ls3 v1 v2) :
    SegP z0f ls1 ls3 (w1 ++ v1) (w2 ++ v2) := by
  intro u1 u2 h
  rw [append_assoc, append_assoc]
  exact h1 (v1 +> u1) (v2 +> u2) (h2 u1 u2 h)

lemma zS4 {Call : Type*} {tm : Machine (Fin 2) (Fin 6)}
    {zCR : zB -> Call -> zB -> Cfg (Fin 2) (Fin 6)}
    {zCL : zB -> zB -> Cfg (Fin 2) (Fin 6)}
    {c : Call} {w1 w2 : zF}
    (h1 : ∀ u r, (zCR (w1 +> u) c r) [tm]⊢⁺ (zCL (w2 +> u) r)) :
    SegP (fun c w1 w2 => ∀ r, (zCR w1 c r) [tm]⊢⁺ (zCL w2 r)) [c] [] w1 w2 := by
  intro u1 u2 h; cases h
  exact SideP.cons (fun r => h1 u1 r) (SideP.nil _)

lemma zS2 {Call : Type*} {tm : Machine (Fin 2) (Fin 6)}
    {zCR : zB -> Call -> zB -> Cfg (Fin 2) (Fin 6)}
    {zCL : zB -> zB -> Cfg (Fin 2) (Fin 6)}
    {c_in c_out : Call} {w1 w2 mid : zF}
    (h1 : ∀ u r, (zCR (w1 +> u) c_in r) [tm]⊢⁺ (zCR u c_out (mid +> r)))
    (h2 : ∀ u r, (zCL u (mid +> r)) [tm]⊢⁺ (zCL (w2 +> u) r)) :
    SegP (fun c w1 w2 => ∀ r, (zCR w1 c r) [tm]⊢⁺ (zCL w2 r)) [c_in] [c_out] w1 w2 := by
  intro u1 u2 h
  rcases h with _ | ⟨hc1, hnil⟩
  cases hnil
  refine SideP.cons (fun r => ?_) (SideP.nil _)
  exact zPt (h1 u1 r) (zPt (hc1 (mid +> r)) (h2 u2 r))

lemma zS5 {Call : Type*} {tm : Machine (Fin 2) (Fin 6)}
    {zCR : zB -> Call -> zB -> Cfg (Fin 2) (Fin 6)}
    {zCL : zB -> zB -> Cfg (Fin 2) (Fin 6)}
    {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : zF}
    (h1 : ∀ u r, (zCR (w1 +> u) c_in r) [tm]⊢⁺ (zCR u c1 (mid1 +> r)))
    (h2 : ∀ u r, (zCL u (mid1 +> r)) [tm]⊢⁺ (zCR u c2 (mid2 +> r)))
    (h3 : ∀ u r, (zCL u (mid2 +> r)) [tm]⊢⁺ (zCL (w2 +> u) r)) :
    SegP (fun c w1 w2 => ∀ r, (zCR w1 c r) [tm]⊢⁺ (zCL w2 r)) [c_in] [c1, c2] w1 w2 := by
  intro u1 u3 h
  rcases h with _ | ⟨hc1, hrest⟩
  rcases hrest with _ | ⟨hc2, hnil⟩
  cases hnil
  refine SideP.cons (fun r => ?_) (SideP.nil _)
  exact zPt (h1 u1 r)
    (zPt (hc1 (mid1 +> r))
      (zPt (h2 _ r)
        (zPt (hc2 (mid2 +> r)) (h3 u3 r))))

inductive Word where
  | V
  | K
  | Q
deriving DecidableEq
open Word

def dVal : Word -> Nat
  | V => 0
  | K => 0
  | Q => 1

lemma dVal_le_one (w : Word) : dVal w <= 1 := by
  cases w <;> decide

def zWt : List Word -> zF
  | [] => []
  | V :: u => V_u ++ zWt u
  | K :: u => K_u ++ zWt u
  | Q :: u => Q_u ++ zWt u

def zWt' : List Word -> zF
  | [] => []
  | V :: u => Vp ++ zWt' u
  | K :: u => Kp ++ zWt' u
  | Q :: u => Qp ++ zWt' u

def zTs : List Word -> zB -> zB
  | [], r => r
  | V :: u, r => V_u +> zTs u r
  | K :: u, r => K_u +> zTs u r
  | Q :: u, r => Q_u +> zTs u r

def zTs' : List Word -> zB -> zB
  | [], r => r
  | V :: u, r => Vp +> zTs' u r
  | K :: u, r => Kp +> zTs' u r
  | Q :: u, r => Qp +> zTs' u r

lemma zWt_cons (w : Word) (u : List Word) : zWt (w :: u) = zWt [w] ++ zWt u := by
  cases w <;> rfl

lemma zWt'_cons (w : Word) (u : List Word) : zWt' (w :: u) = zWt' [w] ++ zWt' u := by
  cases w <;> rfl

lemma zWt_append (u v : List Word) : zWt (u ++ v) = zWt u ++ zWt v := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> (dsimp [zWt]; rw [ih])

lemma zWt'_append (u v : List Word) : zWt' (u ++ v) = zWt' u ++ zWt' v := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> (dsimp [zWt']; rw [ih])

lemma zWt_zTs (u : List Word) (r : zB) : zWt u +> r = zTs u r := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> (dsimp [zWt, zTs]; rw [ih])

lemma zWt'_zTs' (u : List Word) (r : zB) : zWt' u +> r = zTs' u r := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> (dsimp [zWt', zTs']; rw [ih])

lemma zTs_append (u v : List Word) (r : zB) : zTs (u ++ v) r = zTs u (zTs v r) := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> simp [zTs, ih]

lemma zTs'_append (u v : List Word) (r : zB) : zTs' (u ++ v) r = zTs' u (zTs' v r) := by
  induction u with
  | nil => rfl
  | cons a u ih => cases a <;> simp [zTs', ih]

lemma zWt_shift (v : List Word) : [0] ++ zWt v = zWt' v ++ [0] := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    cases a <;> (simp [zWt, zWt', V_u, K_u, Q_u, Vp, Kp, Qp] at ih ⊢; exact ih)

lemma zTs_shift (v : List Word) : [0] +> zTs v default = zTs' v default := by
  rw [<- zWt_zTs, <- append_assoc, zWt_shift, append_assoc]
  simp only [append_cons, append_nil, z00, zWt'_zTs']

lemma zTs_V_shift (v : List Word) : [1, 1, 0] +> zTs' v default = zTs (V :: v) default := by
  rw [<- zTs_shift, <- append_assoc]
  rfl

lemma zTs_rep_K (n : Nat) : zTs (List.replicate n K) default = default := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, zTs, ih, zKd]

lemma zPp (n : Nat) : 0 < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

lemma zPow1 (n : Nat) : 2 ^ (1 + n) = 2 ^ n + 2 ^ n := by
  rw [Nat.add_comm 1 n, Nat.pow_succ]; omega

lemma z0U (n : Nat) : (∃ a, n = a * 2) ∨ (∃ a, n = 1 + a * 2) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · left; exact ⟨n / 2, by omega⟩
  · right; exact ⟨n / 2, by omega⟩

inductive zDg : Nat -> Nat -> List Word -> Prop where
  | nil : zDg 0 0 []
  | zero {A H : Nat} {u : List Word} : zDg A H u -> zDg (A * 2) (1 + H) (K :: u)
  | one {A H : Nat} {u : List Word} : zDg A H u -> zDg (1 + A * 2) (1 + H) (Q :: u)

lemma zDg_lt {A H : Nat} {u : List Word} (h : zDg A H u) : A < 2 ^ H := by
  induction h with
  | nil => decide
  | zero _ ih => rw [zPow1]; omega
  | one _ ih => rw [zPow1]; omega

lemma zDg_len {A H : Nat} {u : List Word} (h : zDg A H u) : u.length = H := by
  induction h with
  | nil => rfl
  | zero _ ih => simp [ih]; omega
  | one _ ih => simp [ih]; omega

lemma zDg_exists (H : Nat) : ∀ A, A < 2 ^ H -> ∃ u, zDg A H u := by
  induction H with
  | zero =>
    intro A hA
    have h0 : A = 0 := by simpa using hA
    subst h0; exact ⟨[], zDg.nil⟩
  | succ H ih =>
    intro A hA
    have hpow : 2 ^ (H + 1) = 2 ^ H * 2 := Nat.pow_succ 2 H
    have h1H : H + 1 = 1 + H := by omega
    rcases z0U A with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rcases ih a (by omega) with ⟨u, hI⟩
      rw [h1H]; exact ⟨K :: u, zDg.zero hI⟩
    · rcases ih a (by omega) with ⟨u, hI⟩
      rw [h1H]; exact ⟨Q :: u, zDg.one hI⟩

lemma zDg_append {A H : Nat} {u : List Word} (h1 : zDg A H u) :
    ∀ {B J : Nat} {v : List Word}, zDg B J v -> zDg (A + B * 2 ^ H) (H + J) (u ++ v) := by
  induction h1 with
  | nil =>
    intro B J v h2; simpa using h2
  | @zero A H u _ ih =>
    intro B J v h2
    have h3 := zDg.zero (ih h2)
    have heq1 : (A + B * 2 ^ H) * 2 = A * 2 + B * 2 ^ (1 + H) := by rw [zPow1]; ring
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    rwa [heq1, heq2] at h3
  | @one A H u _ ih =>
    intro B J v h2
    have h3 := zDg.one (ih h2)
    have heq1 : 1 + (A + B * 2 ^ H) * 2 = (1 + A * 2) + B * 2 ^ (1 + H) := by rw [zPow1]; ring
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    rwa [heq1, heq2] at h3

def checkDg : Nat -> List Word -> Bool
  | 0, [] => true
  | b, K :: u => (b % 2 == 0) && checkDg (b / 2) u
  | b, Q :: u => (b % 2 == 1) && checkDg (b / 2) u
  | _, _ => false

lemma checkDg_sound : ∀ b u, checkDg b u = true -> zDg b u.length u
  | 0, [], _ => zDg.nil
  | 0, K :: u, h => by
    unfold checkDg at h; simp at h
    have hI := checkDg_sound 0 u h
    have hZ := zDg.zero hI
    simpa [Nat.add_comm 1 u.length] using hZ
  | b + 1, K :: u, h => by
    unfold checkDg at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hI := checkDg_sound ((b + 1) / 2) u h.2
    have hZ := zDg.zero hI
    have hb : ((b + 1) / 2) * 2 = b + 1 := by omega
    rwa [hb, Nat.add_comm 1 u.length] at hZ
  | 0, Q :: u, h => by unfold checkDg at h; simp at h
  | b + 1, Q :: u, h => by
    unfold checkDg at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hI := checkDg_sound ((b + 1) / 2) u h.2
    have hO := zDg.one hI
    have hb : 1 + ((b + 1) / 2) * 2 = b + 1 := by omega
    rwa [hb, Nat.add_comm 1 u.length] at hO
  | _ + 1, [], h => by unfold checkDg at h; contradiction
  | 0, V :: _, h => by unfold checkDg at h; contradiction
  | _ + 1, V :: _, h => by unfold checkDg at h; contradiction

inductive Parse : Nat -> List Word -> Nat -> Nat -> Prop where
  | nil (a : Nat) : Parse a [] a 0
  | T {a a' g : Nat} {u : List Word} :
      Parse (1 + a * 2) u a' g -> Parse a (V :: u) a' g
  | VK {a a' g : Nat} {u : List Word} :
      Parse a u a' g -> Parse a (V :: K :: u) a' g
  | D {a q1 a' g : Nat} {w0 : Word} {u : List Word}
      (hw0 : w0 ≠ V) (hq1 : a + dVal w0 = q1 * 2) :
      Parse q1 u a' g -> Parse a (w0 :: u) a' g
  | P {a q2 a' g : Nat} {w0 w1 : Word} {u : List Word}
      (hw0 : w0 ≠ V) (hw1 : w1 ≠ V) (hq2 : (a + dVal w0) / 2 + dVal w1 = 1 + q2 * 2) :
      Parse q2 u a' g -> Parse a (w0 :: w1 :: u) a' (1 + g)

inductive Scan : Nat -> Nat -> List Word -> Nat -> Nat -> List Word -> Nat -> Prop where
  | nil (a b : Nat) (hb : 1 <= b) :
      Scan a b [] a b [] 0
  | T {a b a' b' g : Nat} {u v : List Word} (hb : 2 <= b) :
      Scan (1 + a * 2) ((b - 1) * 2) u a' b' v g ->
      Scan a b (V :: u) a' b' (V :: v) g
  | VK0 {a k a' b' g : Nat} {u v : List Word} (hk : 1 <= k) :
      Scan a (1 + (k - 1) * 2) u a' b' v g ->
      Scan a (k * 2) (V :: K :: u) a' b' (K :: V :: v) g
  | VK1 {a k a' b' g : Nat} {u v : List Word} (hk : 1 <= k) :
      Scan a (1 + (k - 1) * 2) u a' b' v g ->
      Scan a (1 + k * 2) (V :: K :: u) a' b' (Q :: V :: v) g
  | D {a b q1 a' b' g : Nat} {w0 : Word} {u v : List Word}
      (hw0 : w0 ≠ V) (hq1 : a + dVal w0 = q1 * 2) (hb : 2 <= b) :
      Scan q1 (b / 2) u a' b' v g ->
      Scan a b (w0 :: u) a' b' ((if b % 2 == 1 then Q else K) :: v) g
  | P0 {a b q1 q2 a' b' g : Nat} {w0 w1 : Word} {u v : List Word}
      (hw0 : w0 ≠ V) (hw1 : w1 ≠ V)
      (hq1 : a + dVal w0 = q1 * 2) (hq2 : q1 + dVal w1 = 1 + q2 * 2) (hb : 2 <= b) :
      Scan q2 ((b - 1) * 2) u a' b' v g ->
      Scan a b (w0 :: w1 :: u) a' b' (V :: v) (1 + g)
  | P1 {a b q1 q2 a' b' g : Nat} {w0 w1 : Word} {u v : List Word}
      (hw0 : w0 ≠ V) (hw1 : w1 ≠ V)
      (hq1 : a + dVal w0 = 1 + q1 * 2) (hq2 : q1 + dVal w1 = 1 + q2 * 2) (hb : 2 <= b) :
      Scan q2 (1 + (b - 1) * 2) u a' b' v g ->
      Scan a b (w0 :: w1 :: u) a' b' (V :: v) (1 + g)


abbrev StepB (b0 : Nat) (u u' : List Word) : Prop :=
  ∃ n b' v da H g,
    Scan 0 b0 (u ++ List.replicate n K) 0 b' v g ∧
    zDg b' H da ∧
    u' = V :: (v ++ da)

inductive RoundsB (b0 : Nat) : List Word -> List Word -> Prop where
  | refl (u : List Word) : RoundsB b0 u u
  | next {u v w : List Word} : StepB b0 u v -> RoundsB b0 v w -> RoundsB b0 u w

abbrev Step := StepB 6
abbrev Rounds := RoundsB 6
abbrev Rounds.refl := @RoundsB.refl 6
abbrev Rounds.next := @RoundsB.next 6

structure SegSpec (z0f : Call -> zB -> zB -> Prop) : Prop where
  seg_ch_V : SegP z0f [.ch] [.ch, .ch] V_u V_u
  seg_ca_V : SegP z0f [.ca] [.ch] V_u Vp
  seg_ca_Vp : SegP z0f [.ca] [.ca, .ca] Vp Vp
  seg_ch_K : SegP z0f [.ch] [] K_u Q_u
  seg_ch_Q : SegP z0f [.ch] [.ch] Q_u K_u
  seg_ca_VpQ : SegP z0f [.ca] [.ca] (Vp ++ Q_u) (Kp ++ Vp)
  seg_ca_KpVp : SegP z0f [.ca] [] (Kp ++ Vp) (Qp ++ Vp)
  seg_ca_QpVp : SegP z0f [.ca] [.ca, .ca] (Qp ++ Vp) (Kp ++ Vp)
  seg_ca_Kp : SegP z0f [.ca] [] Kp Qp
  seg_ca_Qp : SegP z0f [.ca] [.ca] Qp Kp
  seg_ca_KQ : SegP z0f [.ca] [] (K_u ++ Q_u) Vp
  seg_ca_QQ : SegP z0f [.ca] [.ca] (Q_u ++ Q_u) Vp

lemma seg_ch_V_pow {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (n : Nat) : SegP z0f ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) V_u V_u := by
  induction n with
  | zero => exact z0l V_u
  | succ n ih =>
    have heq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [zLp, heq, z0i]
    exact zSg S.seg_ch_V ih

lemma seg_ca_Vp_pow {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (n : Nat) : SegP z0f ([Call.ca] ^ n) ([Call.ca] ^ (n * 2)) Vp Vp := by
  induction n with
  | zero => exact z0l Vp
  | succ n ih =>
    have heq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [zLp, heq, z0i]
    exact zSg S.seg_ca_Vp ih

lemma seg_double {z0f : Call -> zB -> zB -> Prop} {c : Call} {w : zF} (hw : SegP z0f [c, c] [c] w w) (n : Nat) :
    SegP z0f ([c] ^ (n * 2)) ([c] ^ n) w w := by
  induction n with
  | zero => exact z0l w
  | succ n ih =>
    have heq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [heq, z0i, zLp]
    exact zSg hw ih

lemma seg_ch_K_even {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (n : Nat) : SegP z0f ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) K_u K_u :=
  seg_double (zSg S.seg_ch_K S.seg_ch_Q) n

lemma seg_ch_Q_even {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (n : Nat) : SegP z0f ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) Q_u Q_u :=
  seg_double (zSg S.seg_ch_Q S.seg_ch_K) n

lemma seg_ch_K_odd {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (n : Nat) : SegP z0f ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ n) K_u Q_u := by
  have heq : 1 + n * 2 = n * 2 + 1 := by omega
  rw [heq, z0i, z0h]
  simpa using zSg ((seg_ch_K_even S) n) S.seg_ch_K

lemma seg_ch_Q_odd {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (n : Nat) : SegP z0f ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ (1 + n)) Q_u K_u := by
  simpa only [zLp', List.cons_append, List.nil_append] using zSg S.seg_ch_Q ((seg_ch_K_even S) n)

lemma seg_ch_d_even {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) {w0 : Word} {a q1 : Nat} (hw0 : w0 ≠ V) (hq1 : a + dVal w0 = q1 * 2) :
    SegP z0f ([Call.ch] ^ a) ([Call.ch] ^ q1) (zWt [w0]) K_u := by
  cases w0 with
  | V => contradiction
  | K =>
    have ha : a = q1 * 2 := by dsimp [dVal] at hq1; omega
    subst ha; simpa [zWt] using (seg_ch_K_even S) q1
  | Q =>
    dsimp [dVal] at hq1
    cases q1 with
    | zero => omega
    | succ m =>
      have ha : a = 1 + m * 2 := by omega
      have h1m : m + 1 = 1 + m := by omega
      subst ha; rw [h1m]
      simpa [zWt] using (seg_ch_Q_odd S) m

lemma seg_ch_d_odd {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) {w0 : Word} {a q1 : Nat} (hw0 : w0 ≠ V) (hq1 : a + dVal w0 = 1 + q1 * 2) :
    SegP z0f ([Call.ch] ^ a) ([Call.ch] ^ q1) (zWt [w0]) Q_u := by
  cases w0 with
  | V => contradiction
  | K =>
    have ha : a = 1 + q1 * 2 := by dsimp [dVal] at hq1; omega
    subst ha; simpa [zWt] using (seg_ch_K_odd S) q1
  | Q =>
    have ha : a = q1 * 2 := by dsimp [dVal] at hq1; omega
    subst ha; simpa [zWt] using (seg_ch_Q_even S) q1

lemma seg_ca_Kp_even {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (n : Nat) : SegP z0f ([Call.ca] ^ (n * 2)) ([Call.ca] ^ n) Kp Kp :=
  seg_double (zSg S.seg_ca_Kp S.seg_ca_Qp) n

lemma seg_ca_Kp_odd {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (n : Nat) : SegP z0f ([Call.ca] ^ (1 + n * 2)) ([Call.ca] ^ n) Kp Qp := by
  have heq : 1 + n * 2 = n * 2 + 1 := by omega
  rw [heq, z0i, z0h]
  simpa using zSg ((seg_ca_Kp_even S) n) S.seg_ca_Kp

lemma seg_ca_KpVp_even {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (n : Nat) :
    SegP z0f ([Call.ca] ^ (n * 2)) ([Call.ca] ^ (n * 2)) (Kp ++ Vp) (Kp ++ Vp) := by
  induction n with
  | zero => exact z0l (Kp ++ Vp)
  | succ n ih =>
    have heq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [heq, z0i]
    have h2 : SegP z0f [.ca, .ca] [.ca, .ca] (Kp ++ Vp) (Kp ++ Vp) := zSg S.seg_ca_KpVp S.seg_ca_QpVp
    exact zSg h2 ih

lemma Side_ca_default {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) {b' H : Nat} {da : List Word} (h : zDg b' H da) :
    SideP z0f ([Call.ca] ^ b') default (zTs' da default) := by
  induction h with
  | nil => exact SideP.nil default
  | @zero A H u _ ih =>
    have hS := zSc ((seg_ca_Kp_even S) A) ih
    simpa [zTs', zKpd] using hS
  | @one A H u _ ih =>
    have hS := zSc ((seg_ca_Kp_odd S) A) ih
    simpa [zTs', zKpd] using hS

lemma seg_Scan_T {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (a b : Nat) (hb : 2 <= b) :
    SegP z0f ([Call.ch] ^ a ++ [Call.ca] ^ b)
        ([Call.ch] ^ (1 + a * 2) ++ [Call.ca] ^ ((b - 1) * 2)) V_u Vp := by
  have hb_pow : [Call.ca] ^ b = [Call.ca] ++ [Call.ca] ^ (b - 1) := by
    have hb1 : b = 1 + (b - 1) := by omega
    conv_lhs => rw [hb1, zLp']
  rw [hb_pow, <- List.append_assoc]
  have h1 : SegP z0f ([Call.ch] ^ a ++ [Call.ca]) ([Call.ch] ^ (1 + a * 2)) V_u Vp := by
    have heq : 1 + a * 2 = a * 2 + 1 := by omega
    rw [heq, z0i, z0h]
    exact zSg ((seg_ch_V_pow S) a) S.seg_ca_V
  exact zSg h1 ((seg_ca_Vp_pow S) (b - 1))

lemma seg_Scan_VK_base {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (a : Nat) :
    SegP z0f ([Call.ch] ^ a ++ [Call.ca]) ([Call.ch] ^ a) (V_u ++ K_u) (Vp ++ Q_u) := by
  have hV : SegP z0f ([Call.ch] ^ a ++ [Call.ca]) ([Call.ch] ^ (1 + a * 2)) V_u Vp := by
    have heq : 1 + a * 2 = a * 2 + 1 := by omega
    rw [heq, z0i, z0h]
    exact zSg ((seg_ch_V_pow S) a) S.seg_ca_V
  exact zS0 hV ((seg_ch_K_odd S) a)

lemma seg_Scan_VK0 {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (a k : Nat) (hk : 1 <= k) :
    SegP z0f ([Call.ch] ^ a ++ [Call.ca] ^ (k * 2))
        ([Call.ch] ^ a ++ [Call.ca] ^ (1 + (k - 1) * 2)) (V_u ++ K_u) (Kp ++ Vp) := by
  have hk_pow : [Call.ca] ^ (k * 2) = [Call.ca] ++ ([Call.ca] ++ [Call.ca] ^ ((k - 1) * 2)) := by
    have hk2 : k * 2 = 1 + (1 + (k - 1) * 2) := by omega
    conv_lhs => rw [hk2, zLp', zLp']
  rw [hk_pow, <- List.append_assoc]
  have h_ca : SegP z0f ([Call.ca] ++ [Call.ca] ^ ((k - 1) * 2))
                  ([Call.ca] ^ (1 + (k - 1) * 2)) (Vp ++ Q_u) (Kp ++ Vp) := by
    have h_rhs : [Call.ca] ^ (1 + (k - 1) * 2) = [Call.ca] ++ [Call.ca] ^ ((k - 1) * 2) :=
      zLp' [Call.ca] ((k - 1) * 2)
    rw [h_rhs]
    exact zSg S.seg_ca_VpQ ((seg_ca_KpVp_even S) (k - 1))
  exact zSg ((seg_Scan_VK_base S) a) h_ca

lemma seg_Scan_VK1 {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) (a k : Nat) (hk : 1 <= k) :
    SegP z0f ([Call.ch] ^ a ++ [Call.ca] ^ (1 + k * 2))
        ([Call.ch] ^ a ++ [Call.ca] ^ (1 + (k - 1) * 2)) (V_u ++ K_u) (Qp ++ Vp) := by
  have hk_pow : [Call.ca] ^ (1 + k * 2) = [Call.ca] ^ (k * 2) ++ [Call.ca] := by
    have hk2 : 1 + k * 2 = k * 2 + 1 := by omega
    rw [hk2, z0i, z0h]
  rw [hk_pow, <- List.append_assoc]
  have h_tot := zSg ((seg_Scan_VK0 S) a k hk) S.seg_ca_KpVp
  simpa only [List.append_nil] using h_tot

lemma seg_Scan_D {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) {w0 : Word} {a b q1 : Nat}
    (hw0 : w0 ≠ V) (hq1 : a + dVal w0 = q1 * 2) (hb : 2 <= b) :
    SegP z0f ([Call.ch] ^ a ++ [Call.ca] ^ b)
        ([Call.ch] ^ q1 ++ [Call.ca] ^ (b / 2))
        (zWt [w0]) (zWt' [if b % 2 == 1 then Q else K]) := by
  have h_ch := (seg_ch_d_even S) hw0 hq1
  rcases Nat.mod_two_eq_zero_or_one b with hb0 | hb1
  · have hb_pow : [Call.ca] ^ b = [Call.ca] ^ ((b / 2) * 2) := by
      have hb_eq : b = (b / 2) * 2 := by omega
      conv_lhs => rw [hb_eq]
    have h_if : (if b % 2 == 1 then Q else K) = K := by rw [hb0]; rfl
    rw [hb_pow, h_if]
    simpa [zWt'] using zSg h_ch ((seg_ca_Kp_even S) (b / 2))
  · have hb_pow : [Call.ca] ^ b = [Call.ca] ^ (1 + (b / 2) * 2) := by
      have hb_eq : b = 1 + (b / 2) * 2 := by omega
      conv_lhs => rw [hb_eq]
    have h_if : (if b % 2 == 1 then Q else K) = Q := by rw [hb1]; rfl
    rw [hb_pow, h_if]
    simpa [zWt'] using zSg h_ch ((seg_ca_Kp_odd S) (b / 2))

lemma seg_Scan_P0 {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) {w0 w1 : Word} {a b q1 q2 : Nat}
    (hw0 : w0 ≠ V) (hw1 : w1 ≠ V)
    (hq1 : a + dVal w0 = q1 * 2) (hq2 : q1 + dVal w1 = 1 + q2 * 2) (hb : 2 <= b) :
    SegP z0f ([Call.ch] ^ a ++ [Call.ca] ^ b)
        ([Call.ch] ^ q2 ++ [Call.ca] ^ ((b - 1) * 2))
        (zWt [w0, w1]) Vp := by
  have h_ch1 := (seg_ch_d_even S) hw0 hq1
  have h_ch2 := (seg_ch_d_odd S) hw1 hq2
  have h_ch : SegP z0f ([Call.ch] ^ a) ([Call.ch] ^ q2) (zWt [w0, w1]) (K_u ++ Q_u) := by
    have h0 := zS0 h_ch1 h_ch2
    rwa [<- zWt_cons] at h0
  have hb_pow : [Call.ca] ^ b = [Call.ca] ++ [Call.ca] ^ (b - 1) := by
    have hb1 : b = 1 + (b - 1) := by omega
    conv_lhs => rw [hb1, zLp']
  rw [hb_pow]
  have h_ca : SegP z0f ([Call.ca] ++ [Call.ca] ^ (b - 1)) ([Call.ca] ^ ((b - 1) * 2)) (K_u ++ Q_u) Vp := by
    simpa using zSg S.seg_ca_KQ ((seg_ca_Vp_pow S) (b - 1))
  exact zSg h_ch h_ca

lemma seg_Scan_P1 {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) {w0 w1 : Word} {a b q1 q2 : Nat}
    (hw0 : w0 ≠ V) (hw1 : w1 ≠ V)
    (hq1 : a + dVal w0 = 1 + q1 * 2) (hq2 : q1 + dVal w1 = 1 + q2 * 2) (hb : 2 <= b) :
    SegP z0f ([Call.ch] ^ a ++ [Call.ca] ^ b)
        ([Call.ch] ^ q2 ++ [Call.ca] ^ (1 + (b - 1) * 2))
        (zWt [w0, w1]) Vp := by
  have h_ch1 := (seg_ch_d_odd S) hw0 hq1
  have h_ch2 := (seg_ch_d_odd S) hw1 hq2
  have h_ch : SegP z0f ([Call.ch] ^ a) ([Call.ch] ^ q2) (zWt [w0, w1]) (Q_u ++ Q_u) := by
    have h0 := zS0 h_ch1 h_ch2
    rwa [<- zWt_cons] at h0
  have hb_pow : [Call.ca] ^ b = [Call.ca] ++ [Call.ca] ^ (b - 1) := by
    have hb1 : b = 1 + (b - 1) := by omega
    conv_lhs => rw [hb1, zLp']
  rw [hb_pow]
  have h_ca : SegP z0f ([Call.ca] ++ [Call.ca] ^ (b - 1)) ([Call.ca] ^ (1 + (b - 1) * 2)) (Q_u ++ Q_u) Vp := by
    have h_rhs : [Call.ca] ^ (1 + (b - 1) * 2) = [Call.ca] ++ [Call.ca] ^ ((b - 1) * 2) :=
      zLp' [Call.ca] ((b - 1) * 2)
    rw [h_rhs]
    exact zSg S.seg_ca_QQ ((seg_ca_Vp_pow S) (b - 1))
  exact zSg h_ch h_ca

lemma Seg_of_Scan {z0f : Call -> zB -> zB -> Prop} (S : SegSpec z0f) {a b a' b' g : Nat} {u v : List Word}
    (h : Scan a b u a' b' v g) :
    SegP z0f ([Call.ch] ^ a ++ [Call.ca] ^ b) ([Call.ch] ^ a' ++ [Call.ca] ^ b') (zWt u) (zWt' v) := by
  induction h with
  | nil a b _ => exact z0m _
  | T hb _ ih =>
    simpa [zWt, zWt'] using zS0 ((seg_Scan_T S) _ _ hb) ih
  | VK0 hk _ ih =>
    have h0 := zS0 ((seg_Scan_VK0 S) _ _ hk) ih
    simpa [zWt, zWt', List.append_assoc] using h0
  | VK1 hk _ ih =>
    have h0 := zS0 ((seg_Scan_VK1 S) _ _ hk) ih
    simpa [zWt, zWt', List.append_assoc] using h0
  | D hw0 hq1 hb _ ih =>
    have h0 := zS0 ((seg_Scan_D S) hw0 hq1 hb) ih
    rwa [<- zWt_cons, <- zWt'_cons] at h0
  | P0 hw0 hw1 hq1 hq2 hb _ ih =>
    have h0 := zS0 ((seg_Scan_P0 S) hw0 hw1 hq1 hq2 hb) ih
    rwa [<- zWt_append [_, _] _] at h0
  | P1 hw0 hw1 hq1 hq2 hb _ ih =>
    have h0 := zS0 ((seg_Scan_P1 S) hw0 hw1 hq1 hq2 hb) ih
    rwa [<- zWt_append [_, _] _] at h0

-- Section 3: Universal Parse_V_start, Scan_of_Parse, and Trace Evaluators
abbrev CanParse (a : Nat) (u : List Word) : Prop :=
  ∃ a' g, Parse a u a' g

lemma Parse_all (u : List Word) :
    (∀ a, CanParse a (V :: u)) ∧
    (∀ w0 a q1, w0 ≠ V -> a + dVal w0 = q1 * 2 -> CanParse a (w0 :: u)) ∧
    (∀ w1 k, w1 ≠ V -> CanParse k u ∨ CanParse (2 * k + 1 - dVal w1) (w1 :: u)) := by
  induction u with
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · intro a; exact ⟨1 + a * 2, 0, Parse.T (Parse.nil _)⟩
    · intro w0 a q1 hw0 hq1; exact ⟨q1, 0, Parse.D hw0 hq1 (Parse.nil q1)⟩
    · intro w1 k _; left; exact ⟨k, 0, Parse.nil k⟩
  | cons x u' ih =>
    rcases ih with ⟨hV, hEven, hChoice⟩
    cases x with
    | V =>
      refine ⟨?_, ?_, ?_⟩
      · intro a
        rcases hV (1 + a * 2) with ⟨a', g, hp⟩
        exact ⟨a', g, Parse.T hp⟩
      · intro w0 a q1 hw0 hq1
        rcases hV q1 with ⟨a', g, hp⟩
        exact ⟨a', g, Parse.D hw0 hq1 hp⟩
      · intro w1 k _
        left; exact hV k
    | K =>
      have h_choice_K : ∀ w1 k, w1 ≠ V -> CanParse k (K :: u') ∨ CanParse (2 * k + 1 - dVal w1) (w1 :: K :: u') := by
        intro w1 k hw1
        rcases z0U (k + dVal K) with ⟨q2, hq2⟩ | ⟨q2, hq2⟩
        · left; exact hEven K k q2 (by decide) hq2
        · rcases hChoice K q2 (by decide) with ⟨a', g, hp2⟩ | hR
          · right
            have hdiv : (2 * k + 1 - dVal w1 + dVal w1) / 2 + dVal K = 1 + q2 * 2 := by
              cases w1 <;> (dsimp [dVal] at hq2 ⊢; omega)
            exact ⟨a', 1 + g, Parse.P hw1 (by decide) hdiv hp2⟩
          · left
            have heq : 2 * q2 + 1 - dVal K = k := by dsimp [dVal] at hq2 ⊢; omega
            rwa [heq] at hR
      have h_even_K : ∀ w0 a q1, w0 ≠ V -> a + dVal w0 = q1 * 2 -> CanParse a (w0 :: K :: u') := by
        intro w0 a q1 hw0 hq1
        rcases z0U (q1 + dVal K) with ⟨q2, hq2⟩ | ⟨q2, hq2⟩
        · rcases hEven K q1 q2 (by decide) hq2 with ⟨a', g, hp⟩
          exact ⟨a', g, Parse.D hw0 hq1 hp⟩
        · rcases hChoice K q2 (by decide) with ⟨a', g, hp2⟩ | hR
          · have hdiv : (a + dVal w0) / 2 + dVal K = 1 + q2 * 2 := by
              cases w0 <;> (dsimp [dVal] at hq1 hq2 ⊢; omega)
            exact ⟨a', 1 + g, Parse.P hw0 (by decide) hdiv hp2⟩
          · have heq : 2 * q2 + 1 - dVal K = q1 := by dsimp [dVal] at hq2 ⊢; omega
            rw [heq] at hR
            rcases hR with ⟨a', g, hp⟩
            exact ⟨a', g, Parse.D hw0 hq1 hp⟩
      have h_V_K : ∀ a, CanParse a (V :: K :: u') := by
        intro a
        rcases hChoice K a (by decide) with ⟨a', g, hp⟩ | hR
        · exact ⟨a', g, Parse.VK hp⟩
        · have heq : 2 * a + 1 - dVal K = 1 + a * 2 := by dsimp [dVal]; omega
          rw [heq] at hR
          rcases hR with ⟨a', g, hp⟩
          exact ⟨a', g, Parse.T hp⟩
      exact ⟨h_V_K, h_even_K, h_choice_K⟩
    | Q =>
      have h_choice_Q : ∀ w1 k, w1 ≠ V -> CanParse k (Q :: u') ∨ CanParse (2 * k + 1 - dVal w1) (w1 :: Q :: u') := by
        intro w1 k hw1
        rcases z0U (k + dVal Q) with ⟨q2, hq2⟩ | ⟨q2, hq2⟩
        · left; exact hEven Q k q2 (by decide) hq2
        · rcases hChoice Q q2 (by decide) with ⟨a', g, hp2⟩ | hR
          · right
            have hdiv2 : (2 * k + 1 - dVal w1 + dVal w1) / 2 + dVal Q = 1 + q2 * 2 := by
              cases w1 <;> (dsimp [dVal] at hq2 ⊢; omega)
            exact ⟨a', 1 + g, Parse.P hw1 (by decide) hdiv2 hp2⟩
          · left
            have heq : 2 * q2 + 1 - dVal Q = k := by dsimp [dVal] at hq2 ⊢; omega
            rwa [heq] at hR
      have h_even_Q : ∀ w0 a q1, w0 ≠ V -> a + dVal w0 = q1 * 2 -> CanParse a (w0 :: Q :: u') := by
        intro w0 a q1 hw0 hq1
        rcases z0U (q1 + dVal Q) with ⟨q2, hq2⟩ | ⟨q2, hq2⟩
        · rcases hEven Q q1 q2 (by decide) hq2 with ⟨a', g, hp⟩
          exact ⟨a', g, Parse.D hw0 hq1 hp⟩
        · rcases hChoice Q q2 (by decide) with ⟨a', g, hp2⟩ | hR
          · have hdiv : (a + dVal w0) / 2 + dVal Q = 1 + q2 * 2 := by
              cases w0 <;> (dsimp [dVal] at hq1 hq2 ⊢; omega)
            exact ⟨a', 1 + g, Parse.P hw0 (by decide) hdiv hp2⟩
          · have heq : 2 * q2 + 1 - dVal Q = q1 := by dsimp [dVal] at hq2 ⊢; omega
            rw [heq] at hR
            rcases hR with ⟨a', g, hp⟩
            exact ⟨a', g, Parse.D hw0 hq1 hp⟩
      have h_V_Q : ∀ a, CanParse a (V :: Q :: u') := by
        intro a
        have hev : (1 + a * 2) + dVal Q = (1 + a) * 2 := by dsimp [dVal]; omega
        rcases hEven Q (1 + a * 2) (1 + a) (by decide) hev with ⟨a', g, hp⟩
        exact ⟨a', g, Parse.T hp⟩
      exact ⟨h_V_Q, h_even_Q, h_choice_Q⟩

lemma Parse_V_start (a : Nat) (u : List Word) : ∃ a' g, Parse a (V :: u) a' g :=
  (Parse_all u).1 a

-- Algebraic summaries
def z10 : List Word -> Rat
  | [] => 0
  | V :: u => (1 / 2) * z10 u
  | _ :: u => 1 + 2 * z10 u

def z12 : List Word -> Rat
  | [] => 0
  | V :: u => (1 / 2) * z12 u
  | K :: u => 2 * z12 u
  | Q :: u => 1 + 2 * z12 u

def z13 : List Word -> Rat
  | [] => 1
  | V :: u => (1 / 2) * z13 u
  | _ :: u => 2 * z13 u

def zWPair : List Word -> Rat × Rat
  | [] => (0, 0)
  | V :: u =>
    let p := zWPair u
    (p.2, (1 / 2) * p.2)
  | K :: u =>
    let p := zWPair u
    (3 / 2 + 2 * p.1, 1 + p.1)
  | Q :: u =>
    let p := zWPair u
    (3 / 2 + 2 * p.1, 3 / 4 + p.1)

def zW (u : List Word) : Rat := (zWPair u).1
def zW_V (u : List Word) : Rat := (zWPair u).2

def dCount : List Word -> Nat
  | [] => 0
  | V :: u => dCount u
  | _ :: u => 1 + dCount u

@[scoped simp] lemma zW_nil : zW [] = 0 := rfl
@[scoped simp] lemma zW_V_nil : zW_V [] = 0 := rfl
@[scoped simp] lemma zW_cons_V (u : List Word) : zW (V :: u) = zW_V u := rfl
@[scoped simp] lemma zW_V_cons_V (u : List Word) : zW_V (V :: u) = (1 / 2) * zW_V u := rfl
@[scoped simp] lemma zW_cons_K (u : List Word) : zW (K :: u) = 3 / 2 + 2 * zW u := rfl
@[scoped simp] lemma zW_V_cons_K (u : List Word) : zW_V (K :: u) = 1 + zW u := rfl
@[scoped simp] lemma zW_cons_Q (u : List Word) : zW (Q :: u) = 3 / 2 + 2 * zW u := rfl
@[scoped simp] lemma zW_V_cons_Q (u : List Word) : zW_V (Q :: u) = 3 / 4 + zW u := rfl

lemma z10_nonneg (u : List Word) : 0 <= z10 u := by
  induction u with
  | nil => simp [z10]
  | cons a u ih => cases a <;> (dsimp [z10]; linarith)

lemma z12_nonneg (u : List Word) : 0 <= z12 u := by
  induction u with
  | nil => simp [z12]
  | cons a u ih => cases a <;> (dsimp [z12]; linarith)

lemma z10_cons_d {w0 : Word} (hw0 : w0 ≠ V) (u : List Word) :
    z10 (w0 :: u) = 1 + 2 * z10 u := by
  cases w0 with
  | V => contradiction
  | K => rfl
  | Q => rfl

lemma z13_cons_d {w0 : Word} (hw0 : w0 ≠ V) (u : List Word) :
    z13 (w0 :: u) = 2 * z13 u := by
  cases w0 with
  | V => contradiction
  | K => rfl
  | Q => rfl

lemma zW_cons_d {w0 : Word} (hw0 : w0 ≠ V) (u : List Word) :
    zW (w0 :: u) = 3 / 2 + 2 * zW u := by
  cases w0 with
  | V => contradiction
  | K => rfl
  | Q => rfl

lemma Scan_of_Parse {a a' g : Nat} {u : List Word} (h : Parse a u a' g) :
    ∀ b : Nat, 2 + 4 * z10 u < (b : Rat) -> ∃ b' v, Scan a b u a' b' v g ∧ 3 <= b' := by
  induction h with
  | nil a =>
    intro b hb
    dsimp [z10] at hb
    have hb_rat : (2 : Rat) < (b : Rat) := by linarith
    have hb_lt : 2 < b := by exact_mod_cast hb_rat
    have hb3 : 3 <= b := by omega
    exact ⟨b, [], Scan.nil a b (by omega), hb3⟩
  | @T a a' g u _ ih =>
    intro b hb
    have hz := z10_nonneg u
    dsimp [z10] at hb
    have hb_rat : (2 : Rat) < (b : Rat) := by linarith
    have hb_lt : 2 < b := by exact_mod_cast hb_rat
    have hb2 : 2 <= b := by omega
    have hb_next : 2 + 4 * z10 u < (((b - 1) * 2 : Nat) : Rat) := by
      have hcast : (((b - 1) * 2 : Nat) : Rat) = 2 * (b : Rat) - 2 := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 <= b)]; push_cast; ring
      linarith
    rcases ih ((b - 1) * 2) hb_next with ⟨b', v, hS, hb'⟩
    exact ⟨b', V :: v, Scan.T hb2 hS, hb'⟩
  | @VK a a' g u _ ih =>
    intro b hb
    have hz := z10_nonneg u
    dsimp [z10] at hb
    have hb_rat : (4 : Rat) < (b : Rat) := by linarith
    have hb_lt : 4 < b := by exact_mod_cast hb_rat
    rcases z0U b with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hk : 1 <= k := by omega
      have hb_next : 2 + 4 * z10 u < ((1 + (k - 1) * 2 : Nat) : Rat) := by
        have hcast : ((1 + (k - 1) * 2 : Nat) : Rat) = ((k * 2 : Nat) : Rat) - 1 := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hk]; push_cast; ring
        linarith
      rcases ih (1 + (k - 1) * 2) hb_next with ⟨b', v, hS, hb'⟩
      exact ⟨b', K :: V :: v, Scan.VK0 hk hS, hb'⟩
    · have hk : 1 <= k := by omega
      have hb_next : 2 + 4 * z10 u < ((1 + (k - 1) * 2 : Nat) : Rat) := by
        have hcast : ((1 + (k - 1) * 2 : Nat) : Rat) = ((1 + k * 2 : Nat) : Rat) - 2 := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hk]; push_cast; ring
        linarith
      rcases ih (1 + (k - 1) * 2) hb_next with ⟨b', v, hS, hb'⟩
      exact ⟨b', Q :: V :: v, Scan.VK1 hk hS, hb'⟩
  | @D a q1 a' g w0 u hw0 hq1 _ ih =>
    intro b hb
    have hz := z10_nonneg u
    rw [z10_cons_d hw0] at hb
    have hb_rat : (6 : Rat) < (b : Rat) := by linarith
    have hb_lt : 6 < b := by exact_mod_cast hb_rat
    have hb2 : 2 <= b := by omega
    have hb_div : 2 + 4 * z10 u < ((b / 2 : Nat) : Rat) := by
      have hmod : b <= (b / 2) * 2 + 1 := by omega
      have hmod_r : (b : Rat) <= ((b / 2 : Nat) : Rat) * 2 + 1 := by exact_mod_cast hmod
      linarith
    rcases ih (b / 2) hb_div with ⟨b', v, hS, hb'⟩
    exact ⟨b', (if b % 2 == 1 then Q else K) :: v, Scan.D hw0 hq1 hb2 hS, hb'⟩
  | @P a q2 a' g w0 w1 u hw0 hw1 hq2 _ ih =>
    intro b hb
    have hz := z10_nonneg u
    rw [z10_cons_d hw0, z10_cons_d hw1] at hb
    have hb_rat : (14 : Rat) < (b : Rat) := by linarith
    have hb_lt : 14 < b := by exact_mod_cast hb_rat
    have hb2 : 2 <= b := by omega
    rcases z0U (a + dVal w0) with ⟨q1, hq1⟩ | ⟨q1, hq1⟩
    · have hq2' : q1 + dVal w1 = 1 + q2 * 2 := by omega
      have hb_next : 2 + 4 * z10 u < (((b - 1) * 2 : Nat) : Rat) := by
        have hcast : (((b - 1) * 2 : Nat) : Rat) = 2 * (b : Rat) - 2 := by
          rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 <= b)]; push_cast; ring
        linarith
      rcases ih ((b - 1) * 2) hb_next with ⟨b', v, hS, hb'⟩
      exact ⟨b', V :: v, Scan.P0 hw0 hw1 hq1 hq2' hb2 hS, hb'⟩
    · have hq2' : q1 + dVal w1 = 1 + q2 * 2 := by omega
      have hb_next : 2 + 4 * z10 u < ((1 + (b - 1) * 2 : Nat) : Rat) := by
        have hcast : ((1 + (b - 1) * 2 : Nat) : Rat) = 2 * (b : Rat) - 1 := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 1 <= b)]; push_cast; ring
        linarith
      rcases ih (1 + (b - 1) * 2) hb_next with ⟨b', v, hS, hb'⟩
      exact ⟨b', V :: v, Scan.P1 hw0 hw1 hq1 hq2' hb2 hS, hb'⟩

lemma Scan_append {a b a1 b1 g1 : Nat} {u1 v1 : List Word}
    (h1 : Scan a b u1 a1 b1 v1 g1) :
    ∀ {a2 b2 g2 : Nat} {u2 v2 : List Word},
      Scan a1 b1 u2 a2 b2 v2 g2 ->
      Scan a b (u1 ++ u2) a2 b2 (v1 ++ v2) (g1 + g2) := by
  induction h1 with
  | nil _ _ _ => intro _ _ _ _ _ h2; simpa using h2
  | T hb _ ih => intro _ _ _ _ _ h2; exact Scan.T hb (ih h2)
  | VK0 hk _ ih => intro _ _ _ _ _ h2; exact Scan.VK0 hk (ih h2)
  | VK1 hk _ ih => intro _ _ _ _ _ h2; exact Scan.VK1 hk (ih h2)
  | D hw0 hq1 hb _ ih => intro _ _ _ _ _ h2; exact Scan.D hw0 hq1 hb (ih h2)
  | @P0 _ _ _ _ _ _ g1 _ _ _ _ hw0 hw1 hq1 hq2 hb _ ih =>
    intro _ _ g2 _ _ h2
    have heq : 1 + g1 + g2 = 1 + (g1 + g2) := by omega
    rw [heq]; exact Scan.P0 hw0 hw1 hq1 hq2 hb (ih h2)
  | @P1 _ _ _ _ _ _ g1 _ _ _ _ hw0 hw1 hq1 hq2 hb _ ih =>
    intro _ _ g2 _ _ h2
    have heq : 1 + g1 + g2 = 1 + (g1 + g2) := by omega
    rw [heq]; exact Scan.P1 hw0 hw1 hq1 hq2 hb (ih h2)

-- Trace evaluators
def evalAffineScan : List Nat -> Nat -> Nat -> Nat -> Nat -> List Word ->
    Option (Nat × Nat × Nat × Nat × List Word × Nat)
  | [], ma, ca, mb, cb, [] =>
    if 1 <= cb then some (ma, ca, mb, cb, [], 0) else none
  | 0 :: ts, ma, ca, mb, cb, V :: u =>
    if 2 <= cb then
      match evalAffineScan ts (ma * 2) (1 + ca * 2) (mb * 2) ((cb - 1) * 2) u with
      | some (ma', ca', mb', cb', v, g) => some (ma', ca', mb', cb', V :: v, g)
      | none => none
    else none
  | 1 :: ts, ma, ca, mb, cb, V :: K :: u =>
    if 2 <= cb && mb % 2 == 0 && cb % 2 == 0 then
      match evalAffineScan ts ma ca mb (cb - 1) u with
      | some (ma', ca', mb', cb', v, g) => some (ma', ca', mb', cb', K :: V :: v, g)
      | none => none
    else none
  | 2 :: ts, ma, ca, mb, cb, V :: K :: u =>
    if 3 <= cb && mb % 2 == 0 && cb % 2 == 1 then
      match evalAffineScan ts ma ca mb (cb - 2) u with
      | some (ma', ca', mb', cb', v, g) => some (ma', ca', mb', cb', Q :: V :: v, g)
      | none => none
    else none
  | 3 :: ts, ma, ca, mb, cb, w0 :: u =>
    if w0 != V && ma % 2 == 0 && (ca + dVal w0) % 2 == 0 && 2 <= cb && mb % 2 == 0 then
      match evalAffineScan ts (ma / 2) ((ca + dVal w0) / 2) (mb / 2) (cb / 2) u with
      | some (ma', ca', mb', cb', v, g) =>
        some (ma', ca', mb', cb', (if cb % 2 == 1 then Q else K) :: v, g)
      | none => none
    else none
  | 4 :: ts, ma, ca, mb, cb, w0 :: w1 :: u =>
    if w0 != V && w1 != V && ma % 4 == 0 && (ca + dVal w0) % 2 == 0 &&
       ((ca + dVal w0) / 2 + dVal w1) % 2 == 1 && 2 <= cb then
      match evalAffineScan ts (ma / 4) (((ca + dVal w0) / 2 + dVal w1) / 2) (mb * 2) ((cb - 1) * 2) u with
      | some (ma', ca', mb', cb', v, g) => some (ma', ca', mb', cb', V :: v, 1 + g)
      | none => none
    else none
  | 5 :: ts, ma, ca, mb, cb, w0 :: w1 :: u =>
    if w0 != V && w1 != V && ma % 4 == 0 && (ca + dVal w0) % 2 == 1 &&
       ((ca + dVal w0) / 2 + dVal w1) % 2 == 1 && 2 <= cb then
      match evalAffineScan ts (ma / 4) (((ca + dVal w0) / 2 + dVal w1) / 2) (mb * 2) (1 + (cb - 1) * 2) u with
      | some (ma', ca', mb', cb', v, g) => some (ma', ca', mb', cb', V :: v, 1 + g)
      | none => none
    else none
  | _, _, _, _, _, _ => none

lemma evalAffineScan_sound :
    ∀ ts ma ca mb cb u ma' ca' mb' cb' v g xa xb,
      evalAffineScan ts ma ca mb cb u = some (ma', ca', mb', cb', v, g) ->
      Scan (ma * xa + ca) (mb * xb + cb) u (ma' * xa + ca') (mb' * xb + cb') v g := by
  intro ts
  induction ts with
  | nil =>
    intro ma ca mb cb u ma' ca' mb' cb' v g xa xb h
    cases u with
    | nil =>
      simp only [evalAffineScan] at h
      split_ifs at h with hcb
      simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact Scan.nil _ _ (by omega)
    | cons _ _ => unfold evalAffineScan at h; contradiction
  | cons t ts ih =>
    intro ma ca mb cb u ma' ca' mb' cb' v g xa xb h
    rcases t with _ | _ | _ | _ | _ | _ | t
    · -- t = 0 (T)
      cases u with
      | nil => unfold evalAffineScan at h; contradiction
      | cons w0 u =>
        cases w0 with
        | K => unfold evalAffineScan at h; contradiction
        | Q => unfold evalAffineScan at h; contradiction
        | V =>
          change evalAffineScan (0 :: ts) ma ca mb cb (V :: u) = _ at h
          simp only [evalAffineScan] at h
          split_ifs at h with hcb
          cases hrec : evalAffineScan ts (ma * 2) (1 + ca * 2) (mb * 2) ((cb - 1) * 2) u with
          | none => rw [hrec] at h; contradiction
          | some val =>
            rw [hrec] at h
            rcases val with ⟨ma1, ca1, mb1, cb1, v1, g1⟩
            simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
            have hI := ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec
            have ha : 1 + (ma * xa + ca) * 2 = ma * 2 * xa + (1 + ca * 2) := by ring
            have hb : (mb * xb + cb - 1) * 2 = mb * 2 * xb + (cb - 1) * 2 := by
              have hsub : mb * xb + cb - 1 = mb * xb + (cb - 1) := by omega
              rw [hsub]; ring
            rw [<- ha, <- hb] at hI
            exact Scan.T (by omega) hI
    · -- t = 1 (VK0)
      rcases u with _ | ⟨w0, _ | ⟨w1, u⟩⟩
      · unfold evalAffineScan at h; contradiction
      · cases w0 <;> (unfold evalAffineScan at h; contradiction)
      · cases w0 <;> try (unfold evalAffineScan at h; contradiction)
        cases w1 <;> try (unfold evalAffineScan at h; contradiction)
        change evalAffineScan (1 :: ts) ma ca mb cb (V :: K :: u) = _ at h
        simp only [evalAffineScan] at h
        split_ifs at h with hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
        rcases hcond with ⟨⟨hcb, hmb⟩, hcb2⟩
        cases hrec : evalAffineScan ts ma ca mb (cb - 1) u with
        | none => rw [hrec] at h; contradiction
        | some val =>
          rw [hrec] at h
          rcases val with ⟨ma1, ca1, mb1, cb1, v1, g1⟩
          simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          have hI := ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec
          let k := (mb / 2) * xb + cb / 2
          have hmb_eq : mb = (mb / 2) * 2 := by omega
          have hcb_eq : cb = (cb / 2) * 2 := by omega
          have hcb1_eq : cb - 1 = 1 + (cb / 2 - 1) * 2 := by omega
          have hcb_div_pos : 1 <= cb / 2 := by omega
          have hk : 1 <= k := by dsimp [k]; omega
          have hb_in : mb * xb + cb = k * 2 := by
            dsimp [k]
            calc mb * xb + cb = ((mb / 2) * 2) * xb + (cb / 2) * 2 := by rw [<- hmb_eq, <- hcb_eq]
              _ = ((mb / 2) * xb + cb / 2) * 2 := by ring
          have hb_out : mb * xb + (cb - 1) = 1 + (k - 1) * 2 := by
            have hk_sub : k - 1 = (mb / 2) * xb + (cb / 2 - 1) := by dsimp [k]; omega
            calc mb * xb + (cb - 1) = ((mb / 2) * 2) * xb + (1 + (cb / 2 - 1) * 2) := by rw [<- hmb_eq, hcb1_eq]
              _ = 1 + ((mb / 2) * xb + (cb / 2 - 1)) * 2 := by ring
              _ = 1 + (k - 1) * 2 := by rw [<- hk_sub]
          rw [hb_out] at hI
          rw [hb_in]
          exact Scan.VK0 hk hI
    · -- t = 2 (VK1)
      rcases u with _ | ⟨w0, _ | ⟨w1, u⟩⟩
      · unfold evalAffineScan at h; contradiction
      · cases w0 <;> (unfold evalAffineScan at h; contradiction)
      · cases w0 <;> try (unfold evalAffineScan at h; contradiction)
        cases w1 <;> try (unfold evalAffineScan at h; contradiction)
        change evalAffineScan (2 :: ts) ma ca mb cb (V :: K :: u) = _ at h
        simp only [evalAffineScan] at h
        split_ifs at h with hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
        rcases hcond with ⟨⟨hcb, hmb⟩, hcb2⟩
        cases hrec : evalAffineScan ts ma ca mb (cb - 2) u with
        | none => rw [hrec] at h; contradiction
        | some val =>
          rw [hrec] at h
          rcases val with ⟨ma1, ca1, mb1, cb1, v1, g1⟩
          simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          have hI := ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec
          let k := (mb / 2) * xb + cb / 2
          have hmb_eq : mb = (mb / 2) * 2 := by omega
          have hcb_eq : cb = 1 + (cb / 2) * 2 := by omega
          have hcb2_eq : cb - 2 = 1 + (cb / 2 - 1) * 2 := by omega
          have hcb_div_pos : 1 <= cb / 2 := by omega
          have hk : 1 <= k := by dsimp [k]; omega
          have hb_in : mb * xb + cb = 1 + k * 2 := by
            dsimp [k]
            calc mb * xb + cb = ((mb / 2) * 2) * xb + (1 + (cb / 2) * 2) := by rw [<- hmb_eq, <- hcb_eq]
              _ = 1 + ((mb / 2) * xb + cb / 2) * 2 := by ring
          have hb_out : mb * xb + (cb - 2) = 1 + (k - 1) * 2 := by
            have hk_sub : k - 1 = (mb / 2) * xb + (cb / 2 - 1) := by dsimp [k]; omega
            calc mb * xb + (cb - 2) = ((mb / 2) * 2) * xb + (1 + (cb / 2 - 1) * 2) := by rw [<- hmb_eq, hcb2_eq]
              _ = 1 + ((mb / 2) * xb + (cb / 2 - 1)) * 2 := by ring
              _ = 1 + (k - 1) * 2 := by rw [<- hk_sub]
          rw [hb_out] at hI
          rw [hb_in]
          exact Scan.VK1 hk hI
    · -- t = 3 (D)
      cases u with
      | nil => unfold evalAffineScan at h; contradiction
      | cons w0 u =>
        change evalAffineScan (3 :: ts) ma ca mb cb (w0 :: u) = _ at h
        simp only [evalAffineScan] at h
        cases hcond : (w0 != V && ma % 2 == 0 && (ca + dVal w0) % 2 == 0 && 2 <= cb && mb % 2 == 0)
        · rw [hcond] at h; simp at h
        · rw [hcond, if_pos rfl] at h
          simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, beq_iff_eq] at hcond
          rcases hcond with ⟨⟨⟨⟨hw0, hma⟩, hca⟩, hcb⟩, hmb⟩
          cases hrec : evalAffineScan ts (ma / 2) ((ca + dVal w0) / 2) (mb / 2) (cb / 2) u with
          | none => rw [hrec] at h; contradiction
          | some val =>
            rw [hrec] at h
            rcases val with ⟨ma1, ca1, mb1, cb1, v1, g1⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
            have hI := ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec
            have hma_eq : ma = (ma / 2) * 2 := by omega
            have hca_eq : ca + dVal w0 = ((ca + dVal w0) / 2) * 2 := by omega
            have hmb_eq : mb = (mb / 2) * 2 := by omega
            let q1 := (ma / 2) * xa + (ca + dVal w0) / 2
            have hq1 : (ma * xa + ca) + dVal w0 = q1 * 2 := by
              dsimp [q1]
              calc (ma * xa + ca) + dVal w0 = ma * xa + (ca + dVal w0) := by ring
                _ = ((ma / 2) * 2) * xa + ((ca + dVal w0) / 2) * 2 := by rw [<- hma_eq, <- hca_eq]
                _ = ((ma / 2) * xa + (ca + dVal w0) / 2) * 2 := by ring
            have hb_div : (mb * xb + cb) / 2 = (mb / 2) * xb + cb / 2 := by
              have hmb_xb : mb * xb + cb = 2 * ((mb / 2) * xb) + cb := by
                calc mb * xb + cb = ((mb / 2) * 2) * xb + cb := by rw [<- hmb_eq]
                  _ = 2 * ((mb / 2) * xb) + cb := by ring
              rw [hmb_xb, Nat.mul_add_div (by decide : 0 < 2)]
            have hb_mod : (mb * xb + cb) % 2 = cb % 2 := by
              have hmb_xb : mb * xb + cb = cb + 2 * ((mb / 2) * xb) := by
                calc mb * xb + cb = ((mb / 2) * 2) * xb + cb := by rw [<- hmb_eq]
                  _ = cb + 2 * ((mb / 2) * xb) := by ring
              rw [hmb_xb, Nat.add_mul_mod_self_left]
            rw [<- hb_div] at hI
            have hD := Scan.D hw0 hq1 (by omega : 2 <= mb * xb + cb) hI
            rwa [hb_mod] at hD
    · -- t = 4 (P0)
      rcases u with _ | ⟨w0, _ | ⟨w1, u⟩⟩
      · unfold evalAffineScan at h; contradiction
      · unfold evalAffineScan at h; contradiction
      · change evalAffineScan (4 :: ts) ma ca mb cb (w0 :: w1 :: u) = _ at h
        simp only [evalAffineScan] at h
        split_ifs at h with hcond
        simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, beq_iff_eq] at hcond
        rcases hcond with ⟨⟨⟨⟨⟨hw0, hw1⟩, hma⟩, hca0⟩, hca1⟩, hcb⟩
        cases hrec : evalAffineScan ts (ma / 4) (((ca + dVal w0) / 2 + dVal w1) / 2) (mb * 2) ((cb - 1) * 2) u with
        | none => rw [hrec] at h; contradiction
        | some val =>
          rw [hrec] at h
          rcases val with ⟨ma1, ca1, mb1, cb1, v1, g1⟩
          simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          have hI := ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec
          have hma2_eq : ma = (ma / 2) * 2 := by omega
          have hma4_eq : ma / 2 = (ma / 4) * 2 := by omega
          have hca0_eq : ca + dVal w0 = ((ca + dVal w0) / 2) * 2 := by omega
          have hca1_eq : (ca + dVal w0) / 2 + dVal w1 = 1 + (((ca + dVal w0) / 2 + dVal w1) / 2) * 2 := by omega
          let q1 := (ma / 2) * xa + (ca + dVal w0) / 2
          let q2 := (ma / 4) * xa + ((ca + dVal w0) / 2 + dVal w1) / 2
          have hq1 : (ma * xa + ca) + dVal w0 = q1 * 2 := by
            dsimp [q1]
            calc (ma * xa + ca) + dVal w0 = ma * xa + (ca + dVal w0) := by ring
              _ = ((ma / 2) * 2) * xa + ((ca + dVal w0) / 2) * 2 := by rw [<- hma2_eq, <- hca0_eq]
              _ = ((ma / 2) * xa + (ca + dVal w0) / 2) * 2 := by ring
          have hq2 : q1 + dVal w1 = 1 + q2 * 2 := by
            dsimp [q1, q2]
            calc (ma / 2) * xa + (ca + dVal w0) / 2 + dVal w1 = (ma / 2) * xa + ((ca + dVal w0) / 2 + dVal w1) := by ring
              _ = ((ma / 4) * 2) * xa + (1 + (((ca + dVal w0) / 2 + dVal w1) / 2) * 2) := by rw [<- hma4_eq, <- hca1_eq]
              _ = 1 + ((ma / 4) * xa + ((ca + dVal w0) / 2 + dVal w1) / 2) * 2 := by ring
          have hb : (mb * xb + cb - 1) * 2 = mb * 2 * xb + (cb - 1) * 2 := by
            have hsub : mb * xb + cb - 1 = mb * xb + (cb - 1) := by omega
            rw [hsub]; ring
          rw [<- hb] at hI
          exact Scan.P0 hw0 hw1 hq1 hq2 (by omega) hI
    · -- t = 5 (P1)
      rcases u with _ | ⟨w0, _ | ⟨w1, u⟩⟩
      · unfold evalAffineScan at h; contradiction
      · unfold evalAffineScan at h; contradiction
      · change evalAffineScan (5 :: ts) ma ca mb cb (w0 :: w1 :: u) = _ at h
        simp only [evalAffineScan] at h
        split_ifs at h with hcond
        simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, beq_iff_eq] at hcond
        rcases hcond with ⟨⟨⟨⟨⟨hw0, hw1⟩, hma⟩, hca0⟩, hca1⟩, hcb⟩
        cases hrec : evalAffineScan ts (ma / 4) (((ca + dVal w0) / 2 + dVal w1) / 2) (mb * 2) (1 + (cb - 1) * 2) u with
        | none => rw [hrec] at h; contradiction
        | some val =>
          rw [hrec] at h
          rcases val with ⟨ma1, ca1, mb1, cb1, v1, g1⟩
          simp at h; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          have hI := ih _ _ _ _ _ _ _ _ _ _ _ xa xb hrec
          have hma2_eq : ma = (ma / 2) * 2 := by omega
          have hma4_eq : ma / 2 = (ma / 4) * 2 := by omega
          have hca0_eq : ca + dVal w0 = 1 + ((ca + dVal w0) / 2) * 2 := by omega
          have hca1_eq : (ca + dVal w0) / 2 + dVal w1 = 1 + (((ca + dVal w0) / 2 + dVal w1) / 2) * 2 := by omega
          let q1 := (ma / 2) * xa + (ca + dVal w0) / 2
          let q2 := (ma / 4) * xa + ((ca + dVal w0) / 2 + dVal w1) / 2
          have hq1 : (ma * xa + ca) + dVal w0 = 1 + q1 * 2 := by
            dsimp [q1]
            calc (ma * xa + ca) + dVal w0 = ma * xa + (ca + dVal w0) := by ring
              _ = ((ma / 2) * 2) * xa + (1 + ((ca + dVal w0) / 2) * 2) := by rw [<- hma2_eq, <- hca0_eq]
              _ = 1 + ((ma / 2) * xa + (ca + dVal w0) / 2) * 2 := by ring
          have hq2 : q1 + dVal w1 = 1 + q2 * 2 := by
            dsimp [q1, q2]
            calc (ma / 2) * xa + (ca + dVal w0) / 2 + dVal w1 = (ma / 2) * xa + ((ca + dVal w0) / 2 + dVal w1) := by ring
              _ = ((ma / 4) * 2) * xa + (1 + (((ca + dVal w0) / 2 + dVal w1) / 2) * 2) := by rw [<- hma4_eq, <- hca1_eq]
              _ = 1 + ((ma / 4) * xa + ((ca + dVal w0) / 2 + dVal w1) / 2) * 2 := by ring
          have hb : 1 + (mb * xb + cb - 1) * 2 = mb * 2 * xb + (1 + (cb - 1) * 2) := by
            have hsub : mb * xb + cb - 1 = mb * xb + (cb - 1) := by omega
            rw [hsub]; ring
          rw [<- hb] at hI
          exact Scan.P1 hw0 hw1 hq1 hq2 (by omega) hI
    · unfold evalAffineScan at h; contradiction

def checkAffineScan (ts : List Nat) (ma ca mb cb : Nat) (u : List Word)
    (ma' ca' mb' cb' : Nat) (v : List Word) (g : Nat) : Bool :=
  match evalAffineScan ts ma ca mb cb u with
  | some (ma1, ca1, mb1, cb1, v1, g1) =>
    ma1 == ma' && ca1 == ca' && mb1 == mb' && cb1 == cb' && v1 == v && g1 == g
  | none => false

lemma checkAffineScan_sound (ts : List Nat) (ma ca mb cb : Nat) (u : List Word)
    (ma' ca' mb' cb' : Nat) (v : List Word) (g xa xb : Nat)
    (h : checkAffineScan ts ma ca mb cb u ma' ca' mb' cb' v g = true) :
    Scan (ma * xa + ca) (mb * xb + cb) u (ma' * xa + ca') (mb' * xb + cb') v g := by
  unfold checkAffineScan at h
  cases hrec : evalAffineScan ts ma ca mb cb u with
  | none => rw [hrec] at h; contradiction
  | some val =>
    rcases val with ⟨ma1, ca1, mb1, cb1, v1, g1⟩
    rw [hrec] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact evalAffineScan_sound ts ma ca mb cb u ma1 ca1 mb1 cb1 v1 g1 xa xb hrec


def checkStepB (b0 n : Nat) (ts : List Nat) (u da u' : List Word) : Bool :=
  match evalAffineScan ts 0 0 0 b0 (u ++ List.replicate n K) with
  | some (0, 0, 0, b', v, _) => checkDg b' da && (u' == V :: (v ++ da))
  | _ => false

lemma checkStepB_sound (b0 n : Nat) (ts : List Nat) (u da u' : List Word)
    (h : checkStepB b0 n ts u da u' = true) : StepB b0 u u' := by
  unfold checkStepB at h
  cases hrec : evalAffineScan ts 0 0 0 b0 (u ++ List.replicate n K) with
  | none => rw [hrec] at h; contradiction
  | some val =>
    rw [hrec] at h
    rcases val with ⟨ma', ca', mb', b', v, g⟩
    rcases ma' with _ | ma'
    · rcases ca' with _ | ca'
      · rcases mb' with _ | mb'
        · simp only [Bool.and_eq_true, beq_iff_eq] at h
          have hScan := evalAffineScan_sound ts 0 0 0 b0 (u ++ List.replicate n K) 0 0 0 b' v g 0 0 hrec
          simp only [Nat.zero_mul, Nat.zero_add] at hScan
          exact ⟨n, b', v, da, da.length, g, hScan, checkDg_sound b' da h.1, h.2⟩
        · contradiction
      · contradiction
    · contradiction

abbrev checkStep := checkStepB 6
lemma checkStep_sound (n : Nat) (ts : List Nat) (u da u' : List Word)
    (h : checkStep n ts u da u' = true) : Step u u' :=
  checkStepB_sound 6 n ts u da u' h

def evalTopTrace : List Nat -> Nat -> List Word -> Option (Nat × List Word × Nat)
  | [], a, [] => some (a, [], 0)
  | 3 :: ts, a, w0 :: u =>
    if w0 != V && (a + dVal w0) % 2 == 0 then
      match evalTopTrace ts ((a + dVal w0) / 2) u with
      | some (a', vw, g) => some (a', K :: vw, g)
      | none => none
    else none
  | 4 :: ts, a, w0 :: w1 :: u =>
    if w0 != V && w1 != V && (a + dVal w0) % 2 == 0 && ((a + dVal w0) / 2 + dVal w1) % 2 == 1 then
      match evalTopTrace ts (((a + dVal w0) / 2 + dVal w1) / 2) u with
      | some (a', vw, g) => some (a', V :: vw, 1 + g)
      | none => none
    else none
  | 5 :: ts, a, w0 :: w1 :: u =>
    if w0 != V && w1 != V && (a + dVal w0) % 2 == 1 && ((a + dVal w0) / 2 + dVal w1) % 2 == 1 then
      match evalTopTrace ts (((a + dVal w0) / 2 + dVal w1) / 2) u with
      | some (a', vw, g) => some (a', V :: vw, 1 + g)
      | none => none
    else none
  | _, _, _ => none

lemma evalTopTrace_sound :
    ∀ ts (a : Nat) (u : List Word) (a' : Nat) (vw : List Word) (g : Nat) (b : Nat),
      evalTopTrace ts a u = some (a', vw, g) ->
      2 + 4 * z10 u < (b : Rat) ->
      ∃ b' v, Scan a b u a' b' v g ∧ zW v <= zW vw ∧ zW_V v <= zW_V vw ∧ 3 <= b' := by
  intro ts
  induction ts with
  | nil =>
    intro a u a' vw g b h hb
    cases u with
    | nil =>
      dsimp [evalTopTrace] at h; simp at h; rcases h with ⟨rfl, rfl, rfl⟩
      dsimp [z10] at hb
      have hb_rat : (2 : Rat) < (b : Rat) := by linarith
      have hb_lt : 2 < b := by exact_mod_cast hb_rat
      exact ⟨b, [], Scan.nil a b (by omega), le_rfl, le_rfl, by omega⟩
    | cons _ _ => unfold evalTopTrace at h; contradiction
  | cons t ts ih =>
    intro a u a' vw g b h hb
    rcases t with _ | _ | _ | _ | _ | _ | t
    · unfold evalTopTrace at h; contradiction
    · unfold evalTopTrace at h; contradiction
    · unfold evalTopTrace at h; contradiction
    · -- t = 3 (D)
      cases u with
      | nil => unfold evalTopTrace at h; contradiction
      | cons w0 u =>
        change evalTopTrace (3 :: ts) a (w0 :: u) = _ at h
        simp only [evalTopTrace] at h
        split_ifs at h with hcond
        simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hcond
        rcases hcond with ⟨hw0, ha0⟩
        cases hrec : evalTopTrace ts ((a + dVal w0) / 2) u with
        | none => rw [hrec] at h; contradiction
        | some val =>
          rw [hrec] at h
          rcases val with ⟨a1, vw1, g1⟩
          simp at h; rcases h with ⟨rfl, rfl, rfl⟩
          have hz := z10_nonneg u
          rw [z10_cons_d hw0] at hb
          have hb_rat : (6 : Rat) < (b : Rat) := by linarith
          have hb_lt : 6 < b := by exact_mod_cast hb_rat
          have hb_div : 2 + 4 * z10 u < ((b / 2 : Nat) : Rat) := by
            have hmod : b <= (b / 2) * 2 + 1 := by omega
            have hmod_r : (b : Rat) <= ((b / 2 : Nat) : Rat) * 2 + 1 := by exact_mod_cast hmod
            linarith
          rcases ih _ _ _ _ _ (b / 2) hrec hb_div with ⟨b', v1, hS, hW, hWV, hb'⟩
          refine ⟨b', (if b % 2 == 1 then Q else K) :: v1,
                  Scan.D hw0 (by omega) (by omega) hS, ?_, ?_, hb'⟩
          · split_ifs <;> (simp [zW_cons_K, zW_cons_Q]; linarith)
          · split_ifs <;> (simp [zW_V_cons_K, zW_V_cons_Q]; linarith)
    · -- t = 4 (P0)
      rcases u with _ | ⟨w0, _ | ⟨w1, u⟩⟩
      · unfold evalTopTrace at h; contradiction
      · unfold evalTopTrace at h; contradiction
      · change evalTopTrace (4 :: ts) a (w0 :: w1 :: u) = _ at h
        simp only [evalTopTrace] at h
        split_ifs at h with hcond
        simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hcond
        rcases hcond with ⟨⟨⟨hw0, hw1⟩, ha0⟩, ha1⟩
        cases hrec : evalTopTrace ts (((a + dVal w0) / 2 + dVal w1) / 2) u with
        | none => rw [hrec] at h; contradiction
        | some val =>
          rw [hrec] at h
          rcases val with ⟨a1, vw1, g1⟩
          simp at h; rcases h with ⟨rfl, rfl, rfl⟩
          have hz := z10_nonneg u
          rw [z10_cons_d hw0, z10_cons_d hw1] at hb
          have hb_rat : (14 : Rat) < (b : Rat) := by linarith
          have hb_lt : 14 < b := by exact_mod_cast hb_rat
          have hb_next : 2 + 4 * z10 u < (((b - 1) * 2 : Nat) : Rat) := by
            have hcast : (((b - 1) * 2 : Nat) : Rat) = 2 * (b : Rat) - 2 := by
              rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 <= b)]; push_cast; ring
            linarith
          rcases ih _ _ _ _ _ ((b - 1) * 2) hrec hb_next with ⟨b', v1, hS, hW, hWV, hb'⟩
          exact ⟨b', V :: v1,
                 Scan.P0 hw0 hw1 (q1 := (a + dVal w0) / 2) (by omega) (by omega) (by omega) hS,
                 by simpa using hWV, by simp [zW_V_cons_V]; linarith, hb'⟩
    · -- t = 5 (P1)
      rcases u with _ | ⟨w0, _ | ⟨w1, u⟩⟩
      · unfold evalTopTrace at h; contradiction
      · unfold evalTopTrace at h; contradiction
      · change evalTopTrace (5 :: ts) a (w0 :: w1 :: u) = _ at h
        simp only [evalTopTrace] at h
        split_ifs at h with hcond
        simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hcond
        rcases hcond with ⟨⟨⟨hw0, hw1⟩, ha0⟩, ha1⟩
        cases hrec : evalTopTrace ts (((a + dVal w0) / 2 + dVal w1) / 2) u with
        | none => rw [hrec] at h; contradiction
        | some val =>
          rw [hrec] at h
          rcases val with ⟨a1, vw1, g1⟩
          simp at h; rcases h with ⟨rfl, rfl, rfl⟩
          have hz := z10_nonneg u
          rw [z10_cons_d hw0, z10_cons_d hw1] at hb
          have hb_rat : (14 : Rat) < (b : Rat) := by linarith
          have hb_lt : 14 < b := by exact_mod_cast hb_rat
          have hb_next : 2 + 4 * z10 u < ((1 + (b - 1) * 2 : Nat) : Rat) := by
            have hcast : ((1 + (b - 1) * 2 : Nat) : Rat) = 2 * (b : Rat) - 1 := by
              rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 1 <= b)]; push_cast; ring
            linarith
          rcases ih _ _ _ _ _ (1 + (b - 1) * 2) hrec hb_next with ⟨b', v1, hS, hW, hWV, hb'⟩
          exact ⟨b', V :: v1,
                 Scan.P1 hw0 hw1 (q1 := (a + dVal w0) / 2) (by omega) (by omega) (by omega) hS,
                 by simpa using hWV, by simp [zW_V_cons_V]; linarith, hb'⟩
    · unfold evalTopTrace at h; contradiction

def checkTopTrace (ts : List Nat) (a : Nat) (u : List Word)
    (a' : Nat) (vw : List Word) (g : Nat) : Bool :=
  match evalTopTrace ts a u with
  | some (a1, vw1, g1) => a1 == a' && vw1 == vw && g1 == g
  | none => false

lemma checkTopTrace_sound (ts : List Nat) (a : Nat) (u : List Word)
    (a' : Nat) (vw : List Word) (g b : Nat)
    (h : checkTopTrace ts a u a' vw g = true)
    (hb : 2 + 4 * z10 u < (b : Rat)) :
    ∃ b' v, Scan a b u a' b' v g ∧ zW v <= zW vw ∧ zW_V v <= zW_V vw ∧ 3 <= b' := by
  unfold checkTopTrace at h
  cases hrec : evalTopTrace ts a u with
  | none => rw [hrec] at h; contradiction
  | some val =>
    rcases val with ⟨a1, vw1, g1⟩
    rw [hrec] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    exact evalTopTrace_sound ts a u a1 vw1 g1 b hrec hb


end BusyBeaver.WordVKQ
