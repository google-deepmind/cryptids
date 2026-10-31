module

public import BusyBeaver.WordCalculusH
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver Counter

namespace BusyBeaver.WordCanonBR

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
open WordCalculus Word BRIncs
local notation "zW" => List Word
local notation "zR" => List.replicate

def zSwt : Bool -> Rat
  | false => 1
  | true => 1 / 4

lemma z1p_upper {s : Bool} {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : BScan s k u k' v a b) :
    z1h v <= zSwt s * z1h u := by
  induction h with
  | nil _ => simp [z1h,zSwt]
  | T _ ih => dsimp [z1h,zSwt] at ih ⊢; linarith
  | @pair0 _ u _ _ _ _ _ ih => have hp := zSp u; dsimp [z1h,zSwt] at ih ⊢; linarith
  | @pair1 _ u _ _ _ _ _ ih => have hp := zSp u; dsimp [z1h,zSwt] at ih ⊢; linarith
  | short00 _ ih => dsimp [z1h,zSwt] at ih ⊢; linarith
  | short01 _ ih => dsimp [z1h,zSwt] at ih ⊢; linarith
  | short10 _ ih => dsimp [z1h,zSwt] at ih ⊢; linarith
  | short11 _ ih => dsimp [z1h,zSwt] at ih ⊢; linarith
  | @odd_chain0 r m u k v a b _ ih =>
    dsimp [z1h,zSwt] at ih ⊢; rw [z11_R,z11_QK]; dsimp [z1h]
    have hp := zSp u
    rcases zIv_P4 r with ⟨hiv1,hiv2,hp4,_⟩
    nlinarith
  | @odd_chain1 r m u k v a b _ ih =>
    dsimp [z1h,zSwt] at ih ⊢; rw [z11_R,z11_QK]; dsimp [z1h]
    have hp := zSp u
    rcases zIv_P4 r with ⟨hiv1,hiv2,hp4,_⟩
    nlinarith
  | @even_chain r m u k v a b _ ih =>
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    rw [h1r]; dsimp [z1h,zSwt] at ih ⊢; rw [z11_R,z11_QK]; dsimp [z1h]
    have hp := zSp u
    rcases zIv_P4 r with ⟨hiv1,hiv2,hp4,_⟩
    nlinarith
  | shift_pair0 _ ih => dsimp [z1h,zSwt] at ih ⊢; linarith
  | shift_pair1 _ ih => dsimp [z1h,zSwt] at ih ⊢; linarith
  | @shift_chain0 r m u k v a b _ ih =>
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    dsimp [z1h,zSwt] at ih ⊢; rw [h1r]; dsimp [z1h]; rw [z11_R,z11_QK]; dsimp [z1h]
    have hp := zSp u
    rcases zIv_P4 r with ⟨hiv1,hiv2,hp4,_⟩
    nlinarith
  | @shift_chain1 r m u k v a b _ ih =>
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    dsimp [z1h,zSwt] at ih ⊢; rw [h1r]; dsimp [z1h]; rw [z11_R,z11_QK]; dsimp [z1h]
    have hp := zSp u
    rcases zIv_P4 r with ⟨hiv1,hiv2,hp4,_⟩
    nlinarith

lemma zBz (n : Nat) (u : zW) (k' : Nat) (v : zW) (a b : Rat) :
    ¬ BScan false (1 + n * 2) (K :: u) k' v a b := by
  intro h
  generalize hs : false = s at h
  generalize hk : 1 + n * 2 = k at h
  generalize hu : K :: u = w at h
  cases h with
  | short00 _ => omega
  | short10 _ => omega
  | odd_chain0 r _ => cases r <;> simp [zQK] at hu
  | odd_chain1 r _ => cases r <;> simp [zQK] at hu
  | even_chain _ _ => omega
  | _ => simp at hs hu

lemma z0L_odd_bscan {n : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : BScan false (1 + n * 2) u k' v a b)
    (hL : z0L (Q :: u) = true) :
    z0L u = true := by
  cases u with
  | nil => contradiction
  | cons t0 u' =>
    cases t0 with
    | V => exact hL
    | K => exact False.elim (zBz n u' k' v a b h)
    | Q =>
      generalize hs : false = s at h
      generalize hk : 1 + n * 2 = k at h
      generalize hu : Q :: u' = w at h
      cases h with
      | pair0 _ => simp [z0L] at hu ⊢
      | pair1 _ => simp [z0L] at hu ⊢
      | short01 _ => omega
      | short11 _ => omega
      | odd_chain0 r _ =>
        cases r with
        | zero => simp [zQK] at hu
        | succ r' => simp [zQK,z0L] at hu ⊢
      | odd_chain1 r _ =>
        cases r with
        | zero => simp [zQK] at hu
        | succ r' => simp [zQK,z0L] at hu ⊢
      | _ => simp at hs hu

lemma z1p_z0L {s : Bool} {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h : BScan s k u k' v a b)
    (hL : z0L u = true) :
    z1h v <= (1 / 8) * zSwt s * z1h u := by
  induction h with
  | nil _ => contradiction
  | T _ ih =>
    have hIH := ih hL
    dsimp [z1h,zSwt] at hIH ⊢; linarith
  | pair0 hSub _ =>
    have hUp := z1p_upper hSub
    dsimp [z1h,zSwt] at hUp ⊢; linarith
  | pair1 hSub _ =>
    have hUp := z1p_upper hSub
    dsimp [z1h,zSwt] at hUp ⊢; linarith
  | short00 _ ih =>
    have hIH := ih hL
    dsimp [z1h,zSwt] at hIH ⊢; linarith
  | short01 hSub ih =>
    have hIH := ih (z0L_odd_bscan hSub hL)
    dsimp [z1h,zSwt] at hIH ⊢; linarith
  | short10 _ ih =>
    have hIH := ih hL
    dsimp [z1h,zSwt] at hIH ⊢; linarith
  | short11 hSub ih =>
    have hIH := ih (z0L_odd_bscan hSub hL)
    dsimp [z1h,zSwt] at hIH ⊢; linarith
  | @odd_chain0 r m u k v a b hSub ih =>
    cases r with
    | zero =>
      have hIH := ih hL
      dsimp [zQK,List.replicate,z1h,zSwt,zIv] at hIH ⊢; linarith
    | succ r' =>
      have hUp := z1p_upper hSub
      dsimp [z1h,zSwt] at hUp ⊢; rw [z11_R,z11_QK]; dsimp [z1h]
      have hp := zSp u
      rcases zIv_P4 (r' + 1) with ⟨hiv1,hiv2,hp4,hge1⟩
      rcases hge1 (by omega) with ⟨_,h8⟩
      nlinarith
  | @odd_chain1 r m u k v a b hSub ih =>
    cases r with
    | zero =>
      have hIH := ih hL
      dsimp [zQK,List.replicate,z1h,zSwt,zIv] at hIH ⊢; linarith
    | succ r' =>
      have hUp := z1p_upper hSub
      dsimp [z1h,zSwt] at hUp ⊢; rw [z11_R,z11_QK]; dsimp [z1h]
      have hp := zSp u
      rcases zIv_P4 (r' + 1) with ⟨hiv1,hiv2,hp4,hge1⟩
      rcases hge1 (by omega) with ⟨_,h8⟩
      nlinarith
  | @even_chain r m u k v a b hSub _ =>
    have hUp := z1p_upper hSub
    have h1r : zR (1 + r) V ++ v = V :: (zR r V ++ v) := by
      rw [Nat.add_comm 1 r,List.replicate_succ,List.cons_append]
    rw [h1r]; dsimp [z1h,zSwt] at hUp ⊢; rw [z11_R,z11_QK]; dsimp [z1h]
    have hp := zSp u
    rcases zIv_P4 r with ⟨hiv1,hiv2,hp4,_⟩
    nlinarith
  | shift_pair0 _ ih =>
    have hIH := ih hL
    dsimp [z1h,zSwt] at hIH ⊢; linarith
  | shift_pair1 hSub ih =>
    have hIH := ih (z0L_odd_bscan hSub hL)
    dsimp [z1h,zSwt] at hIH ⊢; linarith
  | @shift_chain0 r m u k v a b hSub ih =>
    cases r with
    | zero =>
      have hIH := ih hL
      dsimp [zQK,List.replicate,z1h,zSwt,zIv] at hIH ⊢; linarith
    | succ r' =>
      have hUp := z1p_upper hSub
      have h1r : zR (1 + (r' + 1)) V ++ v = V :: (zR (r' + 1) V ++ v) := by
        rw [Nat.add_comm 1 (r' + 1),List.replicate_succ,List.cons_append]
      dsimp [z1h,zSwt] at hUp ⊢; rw [h1r]; dsimp [z1h]; rw [z11_R,z11_QK]; dsimp [z1h]
      have hp := zSp u
      rcases zIv_P4 (r' + 1) with ⟨hiv1,hiv2,hp4,hge1⟩
      rcases hge1 (by omega) with ⟨_,h8⟩
      nlinarith
  | @shift_chain1 r m u k v a b hSub ih =>
    cases r with
    | zero =>
      have hIH := ih hL
      dsimp [zQK,List.replicate,z1h,zSwt,zIv] at hIH ⊢; linarith
    | succ r' =>
      have hUp := z1p_upper hSub
      have h1r : zR (1 + (r' + 1)) V ++ v = V :: (zR (r' + 1) V ++ v) := by
        rw [Nat.add_comm 1 (r' + 1),List.replicate_succ,List.cons_append]
      dsimp [z1h,zSwt] at hUp ⊢; rw [h1r]; dsimp [z1h]; rw [z11_R,z11_QK]; dsimp [z1h]
      have hp := zSp u
      rcases zIv_P4 (r' + 1) with ⟨hiv1,hiv2,hp4,hge1⟩
      rcases hge1 (by omega) with ⟨_,h8⟩
      nlinarith

-- ModeU and zPrU (downward BScan existence on u)
inductive ModeU where
  | ME
  | MO
  | MS
deriving DecidableEq

open ModeU

inductive zPrU : ModeU -> zW -> Prop where
  | base_E : zPrU ME [V]
  | base_O : zPrU MO [V]
  | T_E {u : zW} : zPrU MO u -> zPrU ME (V :: u)
  | T_O {u : zW} : zPrU MO u -> zPrU MO (V :: u)
  | odd_c (r : Nat) {u : zW} : zPrU MS u -> zPrU MO (zQK r (V :: u))
  | short_K {u : zW} : zPrU ME u -> zPrU ME (K :: u)
  | even_c (r : Nat) {u : zW} : zPrU MS u -> zPrU ME (K :: zQK r (V :: u))
  | shift_K {u : zW} : zPrU ME u -> zPrU MS (K :: u)
  | shift_c (r : Nat) {u : zW} : zPrU MS u -> zPrU MS (K :: zQK r (V :: u))
  | short_Q {u : zW} : zPrU MO u -> zPrU ME (Q :: u)
  | shift_Q {u : zW} : zPrU MO u -> zPrU MS (Q :: u)
  | pair0_E {u : zW} : zPrU ME u -> zPrU ME (Q :: K :: u)
  | pair0_O {u : zW} : zPrU ME u -> zPrU MO (Q :: K :: u)
  | pair1_E {u : zW} : zPrU MO u -> zPrU ME (Q :: Q :: u)
  | pair1_O {u : zW} : zPrU MO u -> zPrU MO (Q :: Q :: u)

def zPrC (w : zW) : Prop := ∃ r u,w = zQK r (V :: u) /\ zPrU MS u

lemma zPrU_all (u_pre : zW) :
    let w := u_pre ++ [V]
    (zPrU ME w \/ zPrC w) /\
    (zPrU MO w \/ (zPrU MS w /\ (zPrU ME (Q :: w) \/ zPrC (Q :: w)) /\ zPrU MO (Q :: w))) := by
  induction u_pre with
  | nil =>
    exact ⟨Or.inl zPrU.base_E,Or.inl zPrU.base_O⟩
  | cons a u ih =>
    rcases ih with ⟨hEC,hOS⟩
    cases a with
    | V =>
      rcases hOS with hO | ⟨hS,_,_⟩
      · exact ⟨Or.inl (zPrU.T_E hO),Or.inl (zPrU.T_O hO)⟩
      · exact ⟨Or.inr ⟨0,u ++ [V],rfl,hS⟩,Or.inl (zPrU.odd_c 0 hS)⟩
    | K =>
      rcases hEC with hE | ⟨r,u0,hw,hS⟩
      · exact ⟨Or.inl (zPrU.short_K hE),
          Or.inr ⟨zPrU.shift_K hE,Or.inl (zPrU.pair0_E hE),zPrU.pair0_O hE⟩⟩
      · dsimp at hw ⊢; rw [hw]
        exact ⟨Or.inl (zPrU.even_c r hS),
          Or.inr ⟨zPrU.shift_c r hS,Or.inr ⟨r + 1,u0,rfl,hS⟩,zPrU.odd_c (r + 1) hS⟩⟩
    | Q =>
      rcases hOS with hO | ⟨_,hQ_EC,hQ_O⟩
      · exact ⟨Or.inl (zPrU.short_Q hO),
          Or.inr ⟨zPrU.shift_Q hO,Or.inl (zPrU.pair1_E hO),zPrU.pair1_O hO⟩⟩
      · exact ⟨hQ_EC,Or.inl hQ_O⟩

lemma zPrU_MO_V (w : zW) : zPrU MO (V :: (w ++ [V])) := by
  rcases (zPrU_all w).2 with hO | ⟨hS,_,_⟩
  · exact zPrU.T_O hO
  · exact zPrU.odd_c 0 hS

lemma zPrU_ME_VV (w : zW) : zPrU ME (V :: V :: (w ++ [V])) :=
  zPrU.T_E (zPrU_MO_V w)

lemma zPrU_MS_W {u : zW} (h : zPrU MS u) : 1 <= loc_z0W u := by
  generalize hm : MS = m at h
  cases h with
  | @shift_K u0 _ => have := (loc_zWn u0).2.2.2; dsimp [loc_z0W]; linarith
  | @shift_c r u0 _ =>
    have := (loc_zWn u0).2.2.2
    dsimp [loc_z0W]; rw [z0W_QK]; dsimp [loc_z0W]
    rcases zIv_P4 r with ⟨_,_,hp4,_⟩
    nlinarith
  | @shift_Q u0 _ => have := (loc_zWn u0).2.2.2; dsimp [loc_z0W]; linarith
  | _ => contradiction

lemma zPrU_bscan {m : ModeU} {w : zW} (hI : zPrU m w) :
    ((m = ME \/ m = MO) ->
      ∀ (k : Nat),
        (m = ME -> ∃ n,k = n * 2) ->
        (m = MO -> ∃ n,k = 1 + n * 2) ->
        16 * loc_z0W w < (k : Rat) - 3 ->
        ∃ m' v a b,BScan false k w (1 + m') v a b /\ 0 < m') /\
    (m = MS ->
      ∀ (k : Nat),
        (∃ n,k = 1 + n * 2) ->
        4 * loc_z0W w - 4 < (k : Rat) - 3 ->
        ∃ m' v a b,BScan true k w (1 + m') v a b /\ 0 < m') := by
  induction hI with
  | base_E =>
    refine ⟨fun _ k hE _ hk => ?_,fun h => by contradiction⟩
    rcases hE rfl with ⟨n,rfl⟩
    dsimp [loc_z0W] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    refine ⟨(2 * n - 2) * 2,[V],0,0,?_ ,by omega⟩
    have heq1 : n * 2 = 2 + (n - 1) * 2 := by omega
    have heq2 : 1 + (2 * n - 2) * 2 = 1 + ((n - 1) * 2) * 2 := by omega
    rw [heq1,heq2]
    simpa using! BScan.T (BScan.nil _)
  | base_O =>
    refine ⟨fun _ k _ hO hk => ?_,fun h => by contradiction⟩
    rcases hO rfl with ⟨n,rfl⟩
    dsimp [loc_z0W] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    refine ⟨(2 * n - 1) * 2,[V],0,0,?_ ,by omega⟩
    have heq1 : 1 + n * 2 = 2 + (n * 2 - 1) := by omega
    have heq2 : 1 + (2 * n - 1) * 2 = 1 + (n * 2 - 1) * 2 := by omega
    rw [heq1,heq2]
    simpa using! BScan.T (BScan.nil _)
  | @T_E u hO ih =>
    refine ⟨fun _ k hE _ hk => ?_,fun h => by contradiction⟩
    rcases hE rfl with ⟨n,rfl⟩
    have hw := (loc_zWn u).2.2.2
    dsimp [loc_z0W] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    have hn_q : (n : Rat) * 2 = 2 + ((n * 2 - 2 : Nat) : Rat) := by exact_mod_cast (by omega : n * 2 = 2 + (n * 2 - 2))
    rcases ih.1 (Or.inr rfl) (1 + (n * 2 - 2) * 2) (fun h => by contradiction) (fun _ => ⟨n * 2 - 2,rfl⟩)
      (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hS,hm'⟩
    have heq : n * 2 = 2 + (n * 2 - 2) := by omega
    rw [heq]
    exact ⟨m',V :: v,a * (1 / 2),b * (1 / 2),BScan.T hS,hm'⟩
  | @T_O u hO ih =>
    refine ⟨fun _ k _ hO_k hk => ?_,fun h => by contradiction⟩
    rcases hO_k rfl with ⟨n,rfl⟩
    have hw := (loc_zWn u).2.2.2
    dsimp [loc_z0W] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    have hn_q : 1 + (n : Rat) * 2 = 2 + ((n * 2 - 1 : Nat) : Rat) := by exact_mod_cast (by omega : 1 + n * 2 = 2 + (n * 2 - 1))
    rcases ih.1 (Or.inr rfl) (1 + (n * 2 - 1) * 2) (fun h => by contradiction) (fun _ => ⟨n * 2 - 1,rfl⟩)
      (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hS,hm'⟩
    have heq : 1 + n * 2 = 2 + (n * 2 - 1) := by omega
    rw [heq]
    exact ⟨m',V :: v,a * (1 / 2),b * (1 / 2),BScan.T hS,hm'⟩
  | @odd_c r u hS ih =>
    refine ⟨fun _ k _ hO_k hk => ?_,fun h => by contradiction⟩
    rcases hO_k rfl with ⟨n,rfl⟩
    have hWu := zPrU_MS_W hS
    rw [z0W_QK] at hk; dsimp [loc_z0W] at hk
    rcases zIv_P4 r with ⟨_,_,hp4,_⟩
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; nlinarith
    have hpow_ge : 2 <= 2 ^ (1 + r) := by
      rw [zP2 r]; have := zPp r; omega
    rcases z0U (n - 1) with ⟨m,hm⟩ | ⟨m,hm⟩
    · have hk_eq : 1 + n * 2 = 3 + m * 4 := by omega
      have hm_pow : m * 2 <= m * 2 ^ (1 + r) := Nat.mul_le_mul_left m hpow_ge
      have hm_pow_q : (m : Rat) * 2 <= ((m * 2 ^ (1 + r) : Nat) : Rat) := by exact_mod_cast hm_pow
      have hm_q : (n : Rat) = 1 + (m : Rat) * 2 := by exact_mod_cast (by omega : n = 1 + m * 2)
      rcases ih.2 rfl (1 + m * 2 ^ (1 + r)) ⟨m * 2 ^ r,by rw [zP2 r]; ring⟩
        (by push_cast at hk hm_pow_q ⊢; nlinarith) with ⟨m',v,a,b,hSub,hm'⟩
      rw [hk_eq]
      exact ⟨m',K :: (zR r V ++ v),(2 + a * 2) * zIv r,b * 2 * zIv r,BScan.odd_chain0 r hSub,hm'⟩
    · have hk_eq : 1 + n * 2 = 5 + m * 4 := by omega
      have hm_pow : m * 2 <= m * 2 ^ (1 + r) := Nat.mul_le_mul_left m hpow_ge
      have hm_pow_q : (m : Rat) * 2 <= ((m * 2 ^ (1 + r) : Nat) : Rat) := by exact_mod_cast hm_pow
      have hm_q : (n : Rat) = 2 + (m : Rat) * 2 := by exact_mod_cast (by omega : n = 2 + m * 2)
      rcases ih.2 rfl (1 + m * 2 ^ (1 + r)) ⟨m * 2 ^ r,by rw [zP2 r]; ring⟩
        (by push_cast at hk hm_pow_q ⊢; nlinarith) with ⟨m',v,a,b,hSub,hm'⟩
      rw [hk_eq]
      exact ⟨m',Q :: (zR r V ++ v),1 + (2 + a * 2) * zIv r,b * 2 * zIv r,BScan.odd_chain1 r hSub,hm'⟩
  | @short_K u hE ih =>
    refine ⟨fun _ k hE_k _ hk => ?_,fun h => by contradiction⟩
    rcases hE_k rfl with ⟨n,rfl⟩
    have hw := (loc_zWn u).2.2.2
    dsimp [loc_z0W] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    rcases z0U n with ⟨m,rfl⟩ | ⟨m,rfl⟩
    · have hm1 : 1 <= m := by omega
      have hk_eq : m * 2 * 2 = 4 + (m - 1) * 4 := by omega
      have hm_q : (m : Rat) = 1 + ((m - 1 : Nat) : Rat) := by exact_mod_cast (by omega : m = 1 + (m - 1))
      rcases ih.1 (Or.inl rfl) ((m - 1) * 2) (fun _ => ⟨m - 1,rfl⟩) (fun h => by contradiction)
        (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hSub,hm'⟩
      rw [hk_eq]
      exact ⟨m',Q :: v,(7 / 2) + a * 2,b * 2,BScan.short10 hSub,hm'⟩
    · have hk_eq : (1 + m * 2) * 2 = 2 + m * 4 := by omega
      rcases ih.1 (Or.inl rfl) (m * 2) (fun _ => ⟨m,rfl⟩) (fun h => by contradiction)
        (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hSub,hm'⟩
      rw [hk_eq]
      exact ⟨m',K :: v,(5 / 2) + a * 2,b * 2,BScan.short00 hSub,hm'⟩
  | @even_c r u hS ih =>
    refine ⟨fun _ k hE_k _ hk => ?_,fun h => by contradiction⟩
    rcases hE_k rfl with ⟨n,rfl⟩
    have hWu := zPrU_MS_W hS
    dsimp [loc_z0W] at hk; rw [z0W_QK] at hk; dsimp [loc_z0W] at hk
    rcases zIv_P4 r with ⟨_,_,hp4,_⟩
    have hn3 : 3 <= n := by
      by_contra hlt; have : n <= 2 := by omega
      have hq : (n : Rat) <= 2 := by exact_mod_cast this
      push_cast at hk; nlinarith
    have hk_eq : n * 2 = 6 + (n - 3) * 2 := by omega
    have hn_q : (n : Rat) = 3 + ((n - 3 : Nat) : Rat) := by exact_mod_cast (by omega : n = 3 + (n - 3))
    have hpow_ge : 2 <= 2 ^ (1 + r) := by
      rw [zP2 r]; have := zPp r; omega
    have hm_pow : (1 + (n - 3) * 2) * 2 <= (1 + (n - 3) * 2) * 2 ^ (1 + r) :=
      Nat.mul_le_mul_left (1 + (n - 3) * 2) hpow_ge
    have hm_pow_q : (((1 + (n - 3) * 2) * 2 : Nat) : Rat) <= (((1 + (n - 3) * 2) * 2 ^ (1 + r) : Nat) : Rat) := by
      exact_mod_cast hm_pow
    rcases ih.2 rfl (1 + (1 + (n - 3) * 2) * 2 ^ (1 + r)) ⟨(1 + (n - 3) * 2) * 2 ^ r,by rw [zP2 r]; ring⟩
      (by push_cast at hk hm_pow_q ⊢; nlinarith) with ⟨m',v,a,b,hSub,hm'⟩
    rw [hk_eq]
    exact ⟨m',zR (1 + r) V ++ v,1 + (1 + a) * (1 / 2) * zIv r,b * (1 / 2) * zIv r,BScan.even_chain r hSub,hm'⟩
  | @shift_K u hE ih =>
    refine ⟨fun h => by rcases h with h | h <;> contradiction,fun _ k hO_k hk => ?_⟩
    rcases hO_k with ⟨n,rfl⟩
    have hw := (loc_zWn u).2.2.2
    dsimp [loc_z0W] at hk
    rcases ih.1 (Or.inl rfl) ((n * 2) * 2) (fun _ => ⟨n * 2,rfl⟩) (fun h => by contradiction)
      (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hSub,hm'⟩
    exact ⟨m',V :: v,a * (1 / 2),(1 / 4) + b * (1 / 2),BScan.shift_pair0 hSub,hm'⟩
  | @shift_c r u hS ih =>
    refine ⟨fun h => by rcases h with h | h <;> contradiction,fun _ k hO_k hk => ?_⟩
    rcases hO_k with ⟨n,rfl⟩
    have hWu := zPrU_MS_W hS
    dsimp [loc_z0W] at hk; rw [z0W_QK] at hk; dsimp [loc_z0W] at hk
    rcases zIv_P4 r with ⟨_,_,hp4,_⟩
    have hn4 : 4 <= n := by
      by_contra hlt; have : n <= 3 := by omega
      have hq : (n : Rat) <= 3 := by exact_mod_cast this
      push_cast at hk; nlinarith
    have hpow_ge : 4 <= 2 ^ (2 + r) := by
      have h2r : 2 + r = 1 + (1 + r) := by omega
      rw [h2r,zP2 (1 + r),zP2 r]; have := zPp r; omega
    rcases z0U (n - 1) with ⟨m,hm⟩ | ⟨m,hm⟩
    · have hk_eq : 1 + n * 2 = 3 + m * 4 := by omega
      have hm_q : (n : Rat) = 1 + (m : Rat) * 2 := by exact_mod_cast (by omega : n = 1 + m * 2)
      have h_even_sub : ∃ n',1 + m * 2 ^ (2 + r) = 1 + n' * 2 := by
        refine ⟨m * 2 ^ (1 + r),?_⟩
        have h2r : 2 + r = (1 + r) + 1 := by omega
        rw [h2r,Nat.pow_succ]; ring
      have hm_pow : m * 4 <= m * 2 ^ (2 + r) := Nat.mul_le_mul_left m hpow_ge
      have hm_pow_q : ((m * 4 : Nat) : Rat) <= ((m * 2 ^ (2 + r) : Nat) : Rat) := by exact_mod_cast hm_pow
      rcases ih.2 rfl (1 + m * 2 ^ (2 + r)) h_even_sub
        (by push_cast at hk hm_pow_q ⊢; nlinarith) with ⟨m',v,a,b,hSub,hm'⟩
      rw [hk_eq]
      exact ⟨m',K :: (zR (1 + r) V ++ v),(1 + a) * zIv r,b * zIv r,BScan.shift_chain0 r hSub,hm'⟩
    · have hk_eq : 1 + n * 2 = 5 + m * 4 := by omega
      have hm_q : (n : Rat) = 2 + (m : Rat) * 2 := by exact_mod_cast (by omega : n = 2 + m * 2)
      have h_even_sub : ∃ n',1 + m * 2 ^ (2 + r) = 1 + n' * 2 := by
        refine ⟨m * 2 ^ (1 + r),?_⟩
        have h2r : 2 + r = (1 + r) + 1 := by omega
        rw [h2r,Nat.pow_succ]; ring
      have hm_pow : m * 4 <= m * 2 ^ (2 + r) := Nat.mul_le_mul_left m hpow_ge
      have hm_pow_q : ((m * 4 : Nat) : Rat) <= ((m * 2 ^ (2 + r) : Nat) : Rat) := by exact_mod_cast hm_pow
      rcases ih.2 rfl (1 + m * 2 ^ (2 + r)) h_even_sub
        (by push_cast at hk hm_pow_q ⊢; nlinarith) with ⟨m',v,a,b,hSub,hm'⟩
      rw [hk_eq]
      exact ⟨m',Q :: (zR (1 + r) V ++ v),1 + (1 + a) * zIv r,b * zIv r,BScan.shift_chain1 r hSub,hm'⟩
  | @short_Q u hO ih =>
    refine ⟨fun _ k hE_k _ hk => ?_,fun h => by contradiction⟩
    rcases hE_k rfl with ⟨n,rfl⟩
    have hw := (loc_zWn u).2.2.2
    dsimp [loc_z0W] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    rcases z0U n with ⟨m,rfl⟩ | ⟨m,rfl⟩
    · have hm1 : 1 <= m := by omega
      have hk_eq : m * 2 * 2 = 4 + (m - 1) * 4 := by omega
      have hm_q : (m : Rat) = 1 + ((m - 1 : Nat) : Rat) := by exact_mod_cast (by omega : m = 1 + (m - 1))
      rcases ih.1 (Or.inr rfl) (1 + (m - 1) * 2) (fun h => by contradiction) (fun _ => ⟨m - 1,rfl⟩)
        (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hSub,hm'⟩
      rw [hk_eq]
      exact ⟨m',Q :: v,(5 / 2) + a * 2,b * 2,BScan.short11 hSub,hm'⟩
    · have hk_eq : (1 + m * 2) * 2 = 2 + m * 4 := by omega
      rcases ih.1 (Or.inr rfl) (1 + m * 2) (fun h => by contradiction) (fun _ => ⟨m,rfl⟩)
        (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hSub,hm'⟩
      rw [hk_eq]
      exact ⟨m',K :: v,(3 / 2) + a * 2,b * 2,BScan.short01 hSub,hm'⟩
  | @shift_Q u hO ih =>
    refine ⟨fun h => by rcases h with h | h <;> contradiction,fun _ k hO_k hk => ?_⟩
    rcases hO_k with ⟨n,rfl⟩
    have hw := (loc_zWn u).2.2.2
    dsimp [loc_z0W] at hk
    rcases ih.1 (Or.inr rfl) (1 + (n * 2) * 2) (fun h => by contradiction) (fun _ => ⟨n * 2,rfl⟩)
      (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hSub,hm'⟩
    exact ⟨m',V :: v,a * (1 / 2),(1 / 2) + b * (1 / 2),BScan.shift_pair1 hSub,hm'⟩
  | @pair0_E u hE ih =>
    refine ⟨fun _ k hE_k _ hk => ?_,fun h => by contradiction⟩
    rcases hE_k rfl with ⟨n,rfl⟩
    have hw := (loc_zWn u).2.2.2
    dsimp [loc_z0W] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    have hk_eq : n * 2 = 1 + (n * 2 - 1) := by omega
    have hn_q : (n : Rat) * 2 = 1 + ((n * 2 - 1 : Nat) : Rat) := by exact_mod_cast hk_eq
    rcases ih.1 (Or.inl rfl) ((n * 2 - 1) * 2) (fun _ => ⟨n * 2 - 1,rfl⟩) (fun h => by contradiction)
      (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hSub,hm'⟩
    rw [hk_eq]
    exact ⟨m',V :: v,a * (1 / 2),(1 / 4) + b * (1 / 2),BScan.pair0 hSub,hm'⟩
  | @pair0_O u hE ih =>
    refine ⟨fun _ k _ hO_k hk => ?_,fun h => by contradiction⟩
    rcases hO_k rfl with ⟨n,rfl⟩
    have hw := (loc_zWn u).2.2.2
    dsimp [loc_z0W] at hk
    rcases ih.1 (Or.inl rfl) ((n * 2) * 2) (fun _ => ⟨n * 2,rfl⟩) (fun h => by contradiction)
      (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hSub,hm'⟩
    exact ⟨m',V :: v,a * (1 / 2),(1 / 4) + b * (1 / 2),BScan.pair0 hSub,hm'⟩
  | @pair1_E u hO ih =>
    refine ⟨fun _ k hE_k _ hk => ?_,fun h => by contradiction⟩
    rcases hE_k rfl with ⟨n,rfl⟩
    have hw := (loc_zWn u).2.2.2
    dsimp [loc_z0W] at hk
    have hn2 : 2 <= n := by
      by_contra hlt; have : n <= 1 := by omega
      have hq : (n : Rat) <= 1 := by exact_mod_cast this
      push_cast at hk; linarith
    have hk_eq : n * 2 = 1 + (n * 2 - 1) := by omega
    have hn_q : (n : Rat) * 2 = 1 + ((n * 2 - 1 : Nat) : Rat) := by exact_mod_cast hk_eq
    rcases ih.1 (Or.inr rfl) (1 + (n * 2 - 1) * 2) (fun h => by contradiction) (fun _ => ⟨n * 2 - 1,rfl⟩)
      (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hSub,hm'⟩
    rw [hk_eq]
    exact ⟨m',V :: v,a * (1 / 2),(1 / 2) + b * (1 / 2),BScan.pair1 hSub,hm'⟩
  | @pair1_O u hO ih =>
    refine ⟨fun _ k _ hO_k hk => ?_,fun h => by contradiction⟩
    rcases hO_k rfl with ⟨n,rfl⟩
    have hw := (loc_zWn u).2.2.2
    dsimp [loc_z0W] at hk
    rcases ih.1 (Or.inr rfl) (1 + (n * 2) * 2) (fun h => by contradiction) (fun _ => ⟨n * 2,rfl⟩)
      (by push_cast at hk ⊢; linarith) with ⟨m',v,a,b,hSub,hm'⟩
    exact ⟨m',V :: v,a * (1 / 2),(1 / 2) + b * (1 / 2),BScan.pair1 hSub,hm'⟩

lemma zDg_zero_Z {A H : Nat} {w : zW} (h : zDg A H w) (h0 : A = 0) :
    z1f w = ((2 ^ H : Nat) : Rat) - 1 := by
  induction h with
  | nil => simp [z1f]
  | @zero A1 H1 u1 _ ih =>
    have hA1 : A1 = 0 := by omega
    rw [zP2]; dsimp [z1f]; rw [ih hA1]; push_cast; ring
  | one _ => omega

lemma zPiece3 {n_mid : Nat} (hn : 2 <= n_mid) :
    ∃ m_end d1 a_t b_t,
      BScan false (n_mid * 4) [K,Q,Q,Q,Q,K] (m_end * 8) [Q,d1,V,V] a_t b_t /\
      z1h [Q,d1,V,V] = 1 /\
      loc_z0W [Q,d1,V,V] <= 15 / 4 /\
      z0L [Q,d1,V,V] = true /\
      a_t - b_t <= 6 /\
      b_t - a_t <= 0 := by
  have hm0 : 1 <= n_mid - 1 := by omega
  rcases z0U (n_mid - 1) with ⟨m1,hm1⟩ | ⟨m1,hm1⟩
  · have hm1_pos : 1 <= m1 := by omega
    have hk0 : n_mid * 4 = 4 + ((m1 - 1) * 2 + 2) * 4 := by omega
    have hk1 : ((m1 - 1) * 2 + 2) * 2 = 4 + (m1 - 1) * 4 := by omega
    have hB0 : BScan false (1 + ((m1 - 1) * 2) * 2) [Q,K] ((m1 - 1) * 8) [V] (0 * (1 / 2)) ((1 / 4) + 0 * (1 / 2)) := by
      have h := BScan.pair0 (BScan.nil (((m1 - 1) * 2) * 2 * 2))
      have heq : ((m1 - 1) * 2) * 2 * 2 = (m1 - 1) * 8 := by ring
      rw [heq] at h
      exact h
    have hB1 := BScan.pair1 hB0
    have hB2 := BScan.short11 hB1
    rw [<- hk1] at hB2
    have hB3 := BScan.short10 hB2
    rw [<- hk0] at hB3
    refine ⟨m1 - 1,Q,_,_,hB3,?_⟩
    refine ⟨by norm_num [z1h],by norm_num [loc_z0W],rfl,by norm_num,by norm_num⟩
  · have hk0 : n_mid * 4 = 4 + (1 + m1 * 2) * 4 := by omega
    have hk1 : (1 + m1 * 2) * 2 = 2 + m1 * 4 := by omega
    have hB0 : BScan false (1 + (m1 * 2) * 2) [Q,K] (m1 * 8) [V] (0 * (1 / 2)) ((1 / 4) + 0 * (1 / 2)) := by
      have h := BScan.pair0 (BScan.nil ((m1 * 2) * 2 * 2))
      have heq : (m1 * 2) * 2 * 2 = m1 * 8 := by ring
      rw [heq] at h
      exact h
    have hB1 := BScan.pair1 hB0
    have hB2 := BScan.short01 hB1
    rw [<- hk1] at hB2
    have hB3 := BScan.short10 hB2
    rw [<- hk0] at hB3
    refine ⟨m1,K,_,_,hB3,?_⟩
    refine ⟨by norm_num [z1h],by norm_num [loc_z0W],rfl,by norm_num,by norm_num⟩

lemma loc_z1l {s : Bool} {k : Nat} {u : zW} {k' : Nat} {v : zW} {a b : Rat}
    (h1 : BScan s k u k' v a b) :
    ∀ {r r' : zB},BRIncs false k' r r' -> BRIncs s k (zTs u r) (zTs v r') := by
  induction h1 with
  | nil _ => intro r r' h2; exact h2
  | T _ ih => intro r r' h2; exact BRIncs.T (ih h2)
  | pair0 _ ih => intro r r' h2; exact BRIncs.pair0 (ih h2)
  | pair1 _ ih => intro r r' h2; exact BRIncs.pair1 (ih h2)
  | short00 _ ih => intro r r' h2; exact BRIncs.short00 (ih h2)
  | short01 _ ih => intro r r' h2; exact BRIncs.short01 (ih h2)
  | short10 _ ih => intro r r' h2; exact BRIncs.short10 (ih h2)
  | short11 _ ih => intro r r' h2; exact BRIncs.short11 (ih h2)
  | @odd_chain0 r_ch m u k v a b _ ih =>
    intro r r' h2
    have h_in : zTs (zQK r_ch (V :: u)) r = zTs (zQK r_ch [V]) (zTs u r) := by
      rw [<- z15,<- zQK_append]; rfl
    have h_out : zTs (K :: (zR r_ch V ++ v)) r' = d0 +> zTs (zR r_ch V) (zTs v r') := by
      dsimp [zTs]; rw [z15]
    rw [h_in,h_out]
    exact BRIncs.odd_chain0 r_ch (ih h2)
  | @odd_chain1 r_ch m u k v a b _ ih =>
    intro r r' h2
    have h_in : zTs (zQK r_ch (V :: u)) r = zTs (zQK r_ch [V]) (zTs u r) := by
      rw [<- z15,<- zQK_append]; rfl
    have h_out : zTs (Q :: (zR r_ch V ++ v)) r' = d1 +> zTs (zR r_ch V) (zTs v r') := by
      dsimp [zTs]; rw [z15]
    rw [h_in,h_out]
    exact BRIncs.odd_chain1 r_ch (ih h2)
  | @even_chain r_ch m u k v a b _ ih =>
    intro r r' h2
    have h_in : zTs (K :: zQK r_ch (V :: u)) r = d0 +> zTs (zQK r_ch [V]) (zTs u r) := by
      dsimp [zTs]; rw [<- z15,<- zQK_append]; rfl
    have h_out : zTs (zR (1 + r_ch) V ++ v) r' = zTs (zR (1 + r_ch) V) (zTs v r') := by
      rw [z15]
    rw [h_in,h_out]
    exact BRIncs.even_chain r_ch (ih h2)
  | shift_pair0 _ ih => intro r r' h2; exact BRIncs.shift_pair0 (ih h2)
  | shift_pair1 _ ih => intro r r' h2; exact BRIncs.shift_pair1 (ih h2)
  | @shift_chain0 r_ch m u k v a b _ ih =>
    intro r r' h2
    have h_in : zTs (K :: zQK r_ch (V :: u)) r = d0 +> zTs (zQK r_ch [V]) (zTs u r) := by
      dsimp [zTs]; rw [<- z15,<- zQK_append]; rfl
    have h_out : zTs (K :: (zR (1 + r_ch) V ++ v)) r' = d0 +> zTs (zR (1 + r_ch) V) (zTs v r') := by
      dsimp [zTs]; rw [z15]
    rw [h_in,h_out]
    exact BRIncs.shift_chain0 r_ch (ih h2)
  | @shift_chain1 r_ch m u k v a b _ ih =>
    intro r r' h2
    have h_in : zTs (K :: zQK r_ch (V :: u)) r = d0 +> zTs (zQK r_ch [V]) (zTs u r) := by
      dsimp [zTs]; rw [<- z15,<- zQK_append]; rfl
    have h_out : zTs (Q :: (zR (1 + r_ch) V ++ v)) r' = d1 +> zTs (zR (1 + r_ch) V) (zTs v r') := by
      dsimp [zTs]; rw [z15]
    rw [h_in,h_out]
    exact BRIncs.shift_chain1 r_ch (ih h2)

lemma zDg_to_Binary {A H : Nat} {ds : zW} (hD : zDg A H ds) :
    ∀ (n : Nat),A = 1 + n -> 2 ^ (H - 1) <= 1 + n -> Binary (1 + n) H (zTs ds default) := by
  induction hD with
  | nil => intro n hA _; omega
  | @zero A' H' u hD' ih =>
    intro n hA hPow
    have hA'_pos : 1 <= A' := by omega
    cases H' with
    | zero =>
      have hlt := z1b hD'
      omega
    | succ H'' =>
      have hpow_sub : 2 ^ ((1 + (H'' + 1)) - 1) = 2 ^ ((H'' + 1) - 1) * 2 := by
        simp [Nat.pow_succ]
      have hIH := ih (A' - 1) (by omega) (by omega)
      have hB := Binary.zero hIH
      have heq1 : 2 + (A' - 1) * 2 = 1 + n := by omega
      rw [heq1] at hB
      exact hB
  | @one A' H' u hD' ih =>
    intro n hA hPow
    cases H' with
    | zero =>
      have hlt := z1b hD'
      have hA'0 : A' = 0 := by omega
      subst hA'0
      have hu : u = [] := (loc_z0X zDg.nil hD').symm
      subst hu
      have hn0 : n = 0 := by omega
      subst hn0
      exact Binary.one
    | succ H'' =>
      have hpow_sub : 2 ^ ((1 + (H'' + 1)) - 1) = 2 ^ ((H'' + 1) - 1) * 2 := by
        simp [Nat.pow_succ]
      have h_ge1 : 1 <= 2 ^ ((H'' + 1) - 1) := by
        have := zPp ((H'' + 1) - 1); omega
      have hA'_pos : 1 <= A' := by omega
      have hIH := ih (A' - 1) (by omega) (by omega)
      have hB := Binary.two hIH
      have heq1 : 3 + (A' - 1) * 2 = 1 + n := by omega
      rw [heq1] at hB
      exact hB

-- Section 7D: P33 prefix, BGood, BStep, z1N, finite rounds executor, and machine glue

def zP33 : zW := ([V,V,Q,V,V,Q,V,V,K,V,V,K,V,V,Q,V,V,Q,V,V,K,V,V,K,V,V,Q,V,V,Q,V,V] ++ [K])

def zOut33 : zW := ([V,Q,V,V,K,V,V,K,V,V,Q,V,V,Q,V,V,K,V,V,K,V,V,Q,V,V,Q,V,V,K,V,V,K] ++ [V])

def zTail8 : zW := [Q,Q,K,K,Q,Q,Q,Q]

lemma zDg_tail8 : zDg 243 8 zTail8 :=
  zDg.one (zDg.one (zDg.zero (zDg.zero (zDg.one (zDg.one (zDg.one (zDg.one zDg.nil)))))))

lemma zP3_11 (m : Nat) {k_in k_out : Nat} {r r' : zB}
    (h1 : k_in = 4 + m * 2) (h2 : k_out = 1 + m * 4)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t +> (t +> (d1 +> r))) (t +> (d1 +> (t +> r'))) := by
  have h_in : k_in = 2 + (2 + m * 2) := by omega
  have h_out : k_out = 1 + (m * 2) * 2 := by omega
  rw [h_out] at h
  have h_sp := BRIncs.shift_pair1 h
  have h_oc := BRIncs.odd_chain1 0 h_sp
  have h_mid : 5 + m * 4 = 1 + (2 + m * 2) * 2 := by omega
  rw [h_mid] at h_oc
  rw [h_in]
  exact BRIncs.T h_oc

lemma zP3_01 (m : Nat) {k_in k_out : Nat} {r r' : zB}
    (h1 : k_in = 3 + m * 2) (h2 : k_out = 1 + m * 4)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t +> (t +> (d1 +> r))) (t +> (d0 +> (t +> r'))) := by
  have h_in : k_in = 2 + (1 + m * 2) := by omega
  have h_out : k_out = 1 + (m * 2) * 2 := by omega
  rw [h_out] at h
  have h_sp := BRIncs.shift_pair1 h
  have h_oc := BRIncs.odd_chain0 0 h_sp
  have h_mid : 3 + m * 4 = 1 + (1 + m * 2) * 2 := by omega
  rw [h_mid] at h_oc
  rw [h_in]
  exact BRIncs.T h_oc

lemma zP3_00 (m : Nat) {k_in k_out : Nat} {r r' : zB}
    (h1 : k_in = 3 + m * 2) (h2 : k_out = m * 4)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t +> (t +> (d0 +> r))) (t +> (d0 +> (t +> r'))) := by
  have h_in : k_in = 2 + (1 + m * 2) := by omega
  have h_out : k_out = (m * 2) * 2 := by omega
  rw [h_out] at h
  have h_sp := BRIncs.shift_pair0 h
  have h_oc := BRIncs.odd_chain0 0 h_sp
  have h_mid : 3 + m * 4 = 1 + (1 + m * 2) * 2 := by omega
  rw [h_mid] at h_oc
  rw [h_in]
  exact BRIncs.T h_oc

lemma zP3_10 (m : Nat) {k_in k_out : Nat} {r r' : zB}
    (h1 : k_in = 4 + m * 2) (h2 : k_out = m * 4)
    (h : BRIncs false k_out r r') :
    BRIncs false k_in (t +> (t +> (d0 +> r))) (t +> (d1 +> (t +> r'))) := by
  have h_in : k_in = 2 + (2 + m * 2) := by omega
  have h_out : k_out = (m * 2) * 2 := by omega
  rw [h_out] at h
  have h_sp := BRIncs.shift_pair0 h
  have h_oc := BRIncs.odd_chain1 0 h_sp
  have h_mid : 5 + m * 4 = 1 + (2 + m * 2) * 2 := by omega
  rw [h_mid] at h_oc
  rw [h_in]
  exact BRIncs.T h_oc

lemma zBRIncs_P33 {r r' : zB} (h : BRIncs false 249044 r r') :
    BRIncs false 128 (zTs zP33 r) (zTs zOut33 r') := by
  exact
    zP3_11 62 rfl rfl (
    zP3_01 123 rfl rfl (
    zP3_00 245 rfl rfl (
    zP3_10 488 rfl rfl (
    zP3_11 974 rfl rfl (
    zP3_01 1947 rfl rfl (
    zP3_00 3893 rfl rfl (
    zP3_10 7784 rfl rfl (
    zP3_11 15566 rfl rfl (
    zP3_01 31131 rfl rfl (
    zP3_00 62261 rfl rfl h))))))))))

inductive BGood : zW -> Prop where
  | intro (H : Nat) (u : zW) (A : Nat) (hi8 : zW) :
      zDg A H hi8 ->
      z1h u * ((2 ^ H : Nat) : Rat) = 128 ->
      z1h u <= 1 / 16 ->
      (∃ w,u = V :: V :: (w ++ [V])) ->
      z0L u = true ->
      (∃ w,hi8 = Q :: K :: w) ->
      loc_z0W u <= 74 / 5 ->
      z1h u * z1f hi8 <= 1273 / 10 ->
      BGood (u ++ (hi8 ++ zTail8))

inductive BStep : zW -> zW -> Prop where
  | intro (orig : zW) (n : Nat) (v : zW) (a b : Rat) (J : Nat) (ds : zW) :
      BScan false 249044 (orig ++ [K]) (n * 2) v a b ->
      zDg (1 + n) J ds ->
      BStep orig ([V,V,K,V] ++ v ++ ds)

lemma loc_z1N {orig : zW} (hG : BGood orig) :
    ∃ out,BStep orig out /\ BGood out := by
  rcases hG with ⟨H,u,A,hi8,hDig,hHeight,hU11,⟨wu,hwu⟩,hLu,⟨w0,hw0⟩,hWu_max,hZ_max⟩
  have hWu_nonneg := (loc_zWn u).2.2.2
  have hSu := zSp u
  have hPrU : zPrU ME u := by rw [hwu]; exact zPrU_ME_VV wu
  have hk_in : 16 * loc_z0W u < (249044 : Rat) - 3 := by linarith only [hWu_max]
  rcases (zPrU_bscan hPrU).1 (Or.inl rfl) 249044 (fun _ => ⟨124522,rfl⟩) (fun h => by contradiction) hk_in with ⟨m1,v1,a1,b1,hB1,hm1⟩
  have hSv1 := zSp v1
  have hWv1_nonneg := (loc_zWn v1).2.2.2
  have h11_v1 : z1h v1 <= (1 / 8) * z1h u := by
    have := z1p_z0L hB1 hLu; dsimp [zSwt] at this; linarith only [this]
  rcases (loc_z1j hB1).1 rfl with ⟨hW_v1,hAB_1,hBA_1⟩
  have hBud1 := loc_z1i hB1
  subst hw0
  rcases zD1 hDig with ⟨A1,H1,hD1,hA1,hH1⟩
  rcases zD0 hD1 with ⟨A0,H0,hD0,hA0,hH0⟩
  have hDw0 := zDw hD0
  have hSw0 := zSp w0
  have hZw0_nonneg := (loc_zWn w0).2.1
  have hPowH : ((2 ^ H : Nat) : Rat) = 4 * z1h w0 := by
    have h1 : 2 ^ H = 4 * 2 ^ H0 := by rw [hH1,hH0,zP2 (1 + H0),zP2 H0]; ring
    have h2 : ((2 ^ H : Nat) : Rat) = ((4 * 2 ^ H0 : Nat) : Rat) := by exact_mod_cast h1
    rw [Nat.cast_mul] at h2
    change ((2 ^ H : Nat) : Rat) = 4 * ((2 ^ H0 : Nat) : Rat) at h2
    linarith only [h2,hDw0.1]
  have hZ_hi8 : z1f (Q :: K :: w0) = 2 + 4 * z1f w0 := by dsimp [z1f]; ring
  have hA0_pos : 0 < A0 := by
    by_contra hle; have hA0_0 : A0 = 0 := by omega
    have hZw0_0 := zDg_zero_Z hD0 hA0_0
    rw [<- hDw0.1] at hZw0_0
    have h_prod : z1h u * z1f (Q :: K :: w0) + 2 * z1h u = z1h u * (4 * z1h w0) := by
      rw [hZ_hi8,hZw0_0]; ring
    have h_pow_u : z1h u * ((2 ^ H : Nat) : Rat) = z1h u * (4 * z1h w0) := by rw [hPowH]
    linarith only [h_prod,h_pow_u,hHeight,hU11,hZ_max]
  have hLw0 : z0L (w0 ++ [K]) = true := zDg_pos_z0L hD0 hA0_pos
  have hY_w0qqk : z1e (w0 ++ [Q,Q,K]) = z1e w0 + 7 * z1h w0 := by rw [z1j]; dsimp [z1e]; ring
  have hZ_w0qqk : z1f (w0 ++ [Q,Q,K]) = z1f w0 + 4 * z1h w0 := by rw [z1k]; dsimp [z1f]; ring
  have hScan_cond : (z1e (w0 ++ [Q,Q,K]) + z1f (w0 ++ [Q,Q,K])) * 2 < ((m1 * 2 : Nat) : Rat) := by
    have h_yw0 : z1e w0 = z1h w0 - 1 := by linarith only [hDw0.1,hDw0.2.1]
    push_cast at hBud1 ⊢
    have hm1_nn : (0 : Rat) <= (m1 : Rat) := Nat.cast_nonneg m1
    have hm1_ub : ((m1 : Rat) * 2) * z1h v1 <= ((m1 : Rat) * 2) * ((1 / 8) * z1h u) := by
      nlinarith only [hm1_nn,h11_v1]
    have h_bud1_exp : (1 + (m1 : Rat) - 3) * z1h v1 = (1 / 2) * (((m1 : Rat) * 2) * z1h v1) - 2 * z1h v1 := by ring
    have h_lhs_u : z1h u * ((z1e (w0 ++ [Q,Q,K]) + z1f (w0 ++ [Q,Q,K])) * 2) =
        6 * (z1h u * (4 * z1h w0)) + (1 / 2) * (z1h u * z1f (Q :: K :: w0)) - 3 * z1h u := by
      rw [hY_w0qqk,hZ_w0qqk,h_yw0,hZ_hi8]; ring
    have h_pow_u : z1h u * ((2 ^ H : Nat) : Rat) = z1h u * (4 * z1h w0) := by rw [hPowH]
    have h_rhs_u : ((m1 : Rat) * 2) * ((1 / 8) * z1h u) = (1 / 8) * (z1h u * ((m1 : Rat) * 2)) := by ring
    have h_lt_u : z1h u * ((z1e (w0 ++ [Q,Q,K]) + z1f (w0 ++ [Q,Q,K])) * 2) < z1h u * ((m1 : Rat) * 2) := by
      linarith only [h_lhs_u,h_pow_u,hHeight,hZ_max,hSu,hBud1,h_bud1_exp,hm1_ub,h_rhs_u,hAB_1,hWu_max,hSv1]
    nlinarith only [hSu,h_lt_u]
  rcases z1q (w0 ++ [Q,Q,K]) m1 hScan_cond with ⟨b2,y,l2,hS2,_⟩
  rcases zScan_qqk hS2 w0 rfl with ⟨_,h11_y_fn,⟨n_mid,hb2_eq⟩,⟨y0,hy0⟩⟩
  subst hb2_eq
  have h11_y : z1h (V :: y) <= (1 / 64) * ((2 ^ H : Nat) : Rat) := by
    have hy := h11_y_fn hLw0
    have h11_qqk : z1h (w0 ++ [Q,Q,K]) = 8 * z1h w0 := by rw [z1m]; dsimp [z1h]; ring
    dsimp [z1h]; linarith only [hy,h11_qqk,hPowH]
  rcases zHi_bscan hS2 hD0 with ⟨a2,b2_r,hB2,hY_vy,hAB_2,hBA_2⟩
  have hW_vy : loc_z0W (V :: y) <= (11 / 32) * z1f (Q :: K :: w0) := by
    have := (zWY (V :: y)).2; linarith only [this,hY_vy]
  rcases loc_z1k hB1 hB2 with ⟨a12,b12,hB12,ha12,hb12⟩
  have h11_v12 : z1h (v1 ++ (V :: y)) <= 1 / 4 := by
    rw [z1m]; have hS_vy := zSp (V :: y)
    have h_prod : z1h v1 * z1h (V :: y) <= ((1 / 8) * z1h u) * ((1 / 64) * ((2 ^ H : Nat) : Rat)) := by
      nlinarith only [h11_v1,h11_y,hSv1,hS_vy]
    have h_eq : ((1 / 8) * z1h u) * ((1 / 64) * ((2 ^ H : Nat) : Rat)) = (1 / 512) * (z1h u * ((2 ^ H : Nat) : Rat)) := by ring
    linarith only [h_prod,h_eq,hHeight]
  have hSv12 := zSp (v1 ++ (V :: y))
  have hBud12 := loc_z1i hB12
  have hZ_hi8_nn : 0 <= z1f (Q :: K :: w0) := (loc_zWn (Q :: K :: w0)).2.1
  have hp1_ab : z1h v1 * (a2 - b2_r) <= (7 / 64) * (z1h u * z1f (Q :: K :: w0)) := by
    have hp : z1h v1 * (a2 - b2_r) <= ((1 / 8) * z1h u) * ((7 / 8) * z1f (Q :: K :: w0)) := by
      nlinarith only [h11_v1,hAB_2,hSv1,hZ_hi8_nn]
    have heq : ((1 / 8) * z1h u) * ((7 / 8) * z1f (Q :: K :: w0)) = (7 / 64) * (z1h u * z1f (Q :: K :: w0)) := by ring
    linarith only [hp,heq]
  have h_ab12 : a12 - b12 <= (64 / 11) * loc_z0W u + (7 / 64) * (z1h u * z1f (Q :: K :: w0)) := by
    have h_diff : a12 - b12 = (a1 - b1) + z1h v1 * (a2 - b2_r) := by rw [ha12,hb12]; ring
    linarith only [h_diff,hAB_1,hp1_ab]
  have hn_mid2 : 2 <= n_mid := by
    by_contra hlt; have : n_mid <= 1 := by omega
    have hq : (n_mid : Rat) <= 1 := by exact_mod_cast this
    push_cast at hBud12
    have h_ub : ((n_mid : Rat) * 4 - 3) * z1h (v1 ++ (V :: y)) <= 1 := by
      nlinarith only [hq,h11_v12,hSv12]
    linarith only [hBud12,h_ub,h_ab12,hWu_max,hZ_max]
  rcases zPiece3 hn_mid2 with ⟨m_end,d1_tok,a3,b3,hB3,h11_p3,hW_p3,hL_p3,hAB_3,hBA_3⟩
  rcases loc_z1k hB12 hB3 with ⟨a,b,hB_all,ha_all,hb_all⟩
  let v := (v1 ++ (V :: y)) ++ [Q,d1_tok,V,V]
  have h11_v : z1h v = z1h (v1 ++ (V :: y)) := by dsimp [v]; rw [z1m,h11_p3]; ring
  have hSv : 0 < z1h v := zSp v
  have h11_v_le : z1h v <= 1 / 4 := by linarith only [h11_v,h11_v12]
  have hW_v : loc_z0W v <= (66 / 19) * loc_z0W u + (11 / 256) * (z1h u * z1f (Q :: K :: w0)) + 15 / 16 := by
    dsimp [v]; rw [z13W,z13W]
    have hW_p3_nn := (loc_zWn [Q,d1_tok,V,V]).2.2.2
    have hW_vy_nn := (loc_zWn (V :: y)).2.2.2
    have hp1 : z1h v1 * loc_z0W (V :: y) <= ((1 / 8) * z1h u) * ((11 / 32) * z1f (Q :: K :: w0)) := by
      nlinarith only [h11_v1,hW_vy,hSv1,hW_vy_nn]
    have hp2 : z1h (v1 ++ (V :: y)) * loc_z0W [Q,d1_tok,V,V] <= (1 / 4) * (15 / 4) := by
      nlinarith only [h11_v12,hW_p3,hSv12,hW_p3_nn]
    have hp1_eq : ((1 / 8) * z1h u) * ((11 / 32) * z1f (Q :: K :: w0)) = (11 / 256) * (z1h u * z1f (Q :: K :: w0)) := by ring
    linarith only [hW_v1,hp1,hp1_eq,hp2]
  have hAB : a - b <= 508 / 5 := by
    have hp2 : z1h (v1 ++ (V :: y)) * (a3 - b3) <= (1 / 4) * 6 := by
      nlinarith only [h11_v12,hAB_3,hSv12]
    have h_diff : a - b = (a12 - b12) + z1h (v1 ++ (V :: y)) * (a3 - b3) := by
      rw [ha_all,hb_all]; ring
    linarith only [h_diff,h_ab12,hp2,hWu_max,hZ_max]
  have hBA : b - a <= 8 := by
    have hp1 : z1h v1 * (b2_r - a2) <= z1h v1 := by nlinarith only [hSv1,hBA_2]
    have hp2 : z1h (v1 ++ (V :: y)) * (b3 - a3) <= 0 := by nlinarith only [hSv12,hBA_3]
    have h_diff : b - a = (b1 - a1) + z1h v1 * (b2_r - a2) + z1h (v1 ++ (V :: y)) * (b3 - a3) := by
      rw [ha_all,hb_all,ha12,hb12]; ring
    linarith only [h_diff,hBA_1,hp1,hp2,h11_v1,hU11,hWu_max]
  have hY_v_lt : z1e v < ((2 ^ 17 : Nat) : Rat) := by
    have := (zWY v).1; push_cast; linarith only [this,hW_v,hWu_max,hZ_max]
  rcases loc_z1B v 17 hY_v_lt with ⟨J,hHn⟩
  have hUnit := z2e v 17 J hHn
  have hJ10 : 10 <= J := by
    by_contra hlt; have hJ9 : J <= 9 := by omega
    have hpow9 : 2 ^ J <= 2 ^ 9 := Nat.pow_le_pow_right (by decide) hJ9
    have hpow9_q : ((2 ^ J : Nat) : Rat) <= ((2 ^ 9 : Nat) : Rat) := by exact_mod_cast hpow9
    push_cast at hpow9_q hUnit
    nlinarith only [hpow9_q,hUnit,h11_v_le,hSv]
  let H8' := J - 8
  have hH8'_2 : 2 <= H8' := by omega
  have hJ_eq : J = H8' + 8 := by omega
  have hUnit_H8' : z1h v * ((2 ^ H8' : Nat) : Rat) = 512 := by
    have hpow : 2 ^ J = 2 ^ H8' * 256 := by rw [hJ_eq,Nat.pow_add]
    have hpow_q : ((2 ^ J : Nat) : Rat) = ((2 ^ H8' : Nat) : Rat) * 256 := by
      exact_mod_cast hpow
    have h_eq : z1h v * (((2 ^ H8' : Nat) : Rat) * 256) = 256 * (z1h v * ((2 ^ H8' : Nat) : Rat)) := by ring
    have h17 : ((2 ^ 17 : Nat) : Rat) = 131072 := by norm_num
    rw [hpow_q,h_eq,h17] at hUnit
    linarith only [hUnit]
  have hBud := loc_z1i hB_all
  have hBud_v : ((m_end : Rat) * 8) * z1h v = 249041 + 3 * z1h v - 2 * (a - b) := by
    have h1 : z1h ((v1 ++ (V :: y)) ++ [Q,d1_tok,V,V]) = z1h v := rfl
    rw [h1] at hBud
    push_cast at hBud
    have h2 : ((m_end : Rat) * 8 - 3) * z1h v = ((m_end : Rat) * 8) * z1h v - 3 * z1h v := by ring
    linarith only [hBud,h2]
  let B := 1 + m_end * 4
  have hB_cast : (B : Rat) = 1 + (m_end : Rat) * 4 := by dsimp [B]; push_cast; rfl
  have hB_lo : 243 * 2 ^ H8' <= B := by
    have h243_cast : ((243 * 2 ^ H8' : Nat) : Rat) = 243 * ((2 ^ H8' : Nat) : Rat) := by
      rw [Nat.cast_mul]; rfl
    have h_b_v : ((B : Rat) - ((243 * 2 ^ H8' : Nat) : Rat)) * z1h v =
        z1h v + (1 / 2) * (((m_end : Rat) * 8) * z1h v) - 243 * (z1h v * ((2 ^ H8' : Nat) : Rat)) := by
      rw [hB_cast,h243_cast]; ring
    have h_pos_v : 0 < ((B : Rat) - ((243 * 2 ^ H8' : Nat) : Rat)) * z1h v := by
      linarith only [h_b_v,hBud_v,hUnit_H8',hAB,hSv]
    have hq : ((243 * 2 ^ H8' : Nat) : Rat) <= (B : Rat) := by
      nlinarith only [h_pos_v,hSv]
    exact_mod_cast hq
  have hB_hi : B < 244 * 2 ^ H8' := by
    have h244_cast : ((244 * 2 ^ H8' : Nat) : Rat) = 244 * ((2 ^ H8' : Nat) : Rat) := by
      rw [Nat.cast_mul]; rfl
    have h_b_v : (((244 * 2 ^ H8' : Nat) : Rat) - (B : Rat)) * z1h v =
        244 * (z1h v * ((2 ^ H8' : Nat) : Rat)) - z1h v - (1 / 2) * (((m_end : Rat) * 8) * z1h v) := by
      rw [hB_cast,h244_cast]; ring
    have h_pos_v : 0 < (((244 * 2 ^ H8' : Nat) : Rat) - (B : Rat)) * z1h v := by
      linarith only [h_b_v,hBud_v,hUnit_H8',hBA,h11_v_le]
    have hq : (B : Rat) < ((244 * 2 ^ H8' : Nat) : Rat) := by
      nlinarith only [h_pos_v,hSv]
    exact_mod_cast hq
  let A8' := B - 243 * 2 ^ H8'
  have hA8'_lt : A8' < 2 ^ H8' := by omega
  rcases z18 H8' A8' hA8'_lt with ⟨hi8',hD_hi8'⟩
  have hA8'_mod : ∃ m', A8' = 1 + m' * 4 := by
    have hpow4 : 2 ^ H8' = 2 ^ (H8' - 2) * 4 := by
      have heq : H8' = (H8' - 2) + 2 := by omega
      conv_lhs => rw [heq,Nat.pow_add]
    refine ⟨m_end - 243 * 2 ^ (H8' - 2),?_⟩
    dsimp [A8',B]; omega
  rcases hA8'_mod with ⟨m_a8,hm_a8⟩
  have hLow' : ∃ w,hi8' = Q :: K :: w := by
    rw [hm_a8] at hD_hi8'; exact loc_z1K hD_hi8' hH8'_2
  have hD_ds' : zDg (1 + m_end * 4) J (hi8' ++ zTail8) := by
    have hU := z19 hD_hi8' zDg_tail8
    have heqA : A8' + 243 * 2 ^ H8' = 1 + m_end * 4 := by dsimp [A8',B]; omega
    rw [heqA,<- hJ_eq] at hU; exact hU
  let u' := [V,V,K,V] ++ v
  have h11_u' : z1h u' = (1 / 4) * z1h v := by dsimp [u',z1h]; ring
  have hW_u' : loc_z0W u' = (11 / 32) + (1 / 4) * loc_z0W v := by dsimp [u',loc_z0W]; ring
  have hDef' := z1n hD_hi8'
  have hA8'_q : (A8' : Rat) + 243 * ((2 ^ H8' : Nat) : Rat) = 1 + (m_end : Rat) * 4 := by
    have heq : A8' + 243 * 2 ^ H8' = 1 + m_end * 4 := by dsimp [A8',B]; omega
    exact_mod_cast heq
  have hZ_new : z1h u' * z1f hi8' <= 1273 / 10 := by
    have h1 : z1f hi8' = ((2 ^ H8' : Nat) : Rat) - 1 - (A8' : Rat) := by linarith only [hDef']
    have h2 : (A8' : Rat) = 1 + (m_end : Rat) * 4 - 243 * ((2 ^ H8' : Nat) : Rat) := by linarith only [hA8'_q]
    have h_z_prod : z1h u' * z1f hi8' =
        (244 / 4) * (z1h v * ((2 ^ H8' : Nat) : Rat)) - (1 / 2) * z1h v -
        (1 / 8) * (((m_end : Rat) * 8) * z1h v) := by
      rw [h11_u',h1,h2]; ring
    linarith only [h_z_prod,hUnit_H8',hBud_v,hAB,hSv]
  have hHeight' : z1h u' * ((2 ^ H8' : Nat) : Rat) = 128 := by
    have h_eq : z1h u' * ((2 ^ H8' : Nat) : Rat) = (1 / 4) * (z1h v * ((2 ^ H8' : Nat) : Rat)) := by
      rw [h11_u']; ring
    linarith only [h_eq,hUnit_H8']
  refine ⟨u' ++ (hi8' ++ zTail8),?_,?_⟩
  · have h_in_eq : (u ++ ((Q :: K :: w0) ++ zTail8)) ++ [K] =
        (u ++ ((Q :: K :: w0) ++ [Q,Q,K])) ++ [K,Q,Q,Q,Q,K] := by
      dsimp [zTail8]; simp [List.append_assoc]
    have h_out_eq : u' ++ (hi8' ++ zTail8) = [V,V,K,V] ++ v ++ (hi8' ++ zTail8) := by
      simp [u',List.append_assoc]
    rw [h_out_eq]
    refine BStep.intro _ (m_end * 4) v a b J (hi8' ++ zTail8) ?_ hD_ds'
    have hk_out_eq : (m_end * 4) * 2 = m_end * 8 := by ring
    rw [hk_out_eq,h_in_eq]; exact hB_all
  · refine BGood.intro H8' u' A8' hi8' hD_hi8' hHeight' (by linarith only [h11_u',h11_v_le]) ?_ ?_ hLow' (by linarith only [hW_u',hW_v,hWu_max,hZ_max]) hZ_new
    · refine ⟨[K,V] ++ v1 ++ (V :: y) ++ [Q,d1_tok,V],?_⟩
      simp [u',v,List.append_assoc]
    · have heq_u' : u' = ([V,V,K,V] ++ (v1 ++ (V :: y))) ++ [Q,d1_tok,V,V] := by
        simp [u',v,List.append_assoc]
      rw [heq_u']; exact loc_z1I _ _ hL_p3

lemma loc_z1P {A H : Nat} {da : zW} (hD : zDg A H da) (hZ : A = 0) :
    zTs da default = default := by
  induction hD with
  | nil => rfl
  | @zero A H u _ ih =>
    have hA0 : A = 0 := by omega
    change d0 +> zTs u default = default
    rw [ih hA0,zDd]
  | one _ => omega

lemma loc_z1Q {A H : Nat} {da : zW} (hD : zDg A H da) (hPos : 0 < A) :
    BRIncs false ((A - 1) * 2) default (zTs da default) := by
  induction hD with
  | nil => omega
  | @zero A H u _ ih =>
    have hA_pos : 0 < A := by omega
    have hIH := ih hA_pos
    have hs := BRIncs.short00 hIH
    rw [zDd] at hs
    have heq : (A * 2 - 1) * 2 = 2 + (A - 1) * 4 := by omega
    dsimp [zTs]
    rwa [heq]
  | @one A H u hDu ih =>
    cases A with
    | zero =>
      change BRIncs false 0 default (d1 +> zTs u default)
      rw [loc_z1P hDu rfl]
      have h0 := BRIncs.zero (default : zB)
      have hd : d1 +> (default : zB) = one +> default := by simp [d1,one]
      rw [hd]; exact h0
    | succ A =>
      have hA_pos : 0 < A + 1 := by omega
      have hIH := ih hA_pos
      have heq_in : (A + 1 - 1) * 2 = A * 2 := by omega
      rw [heq_in] at hIH
      have hs := BRIncs.short10 hIH
      rw [zDd] at hs
      have heq : (1 + (A + 1) * 2 - 1) * 2 = 4 + A * 4 := by omega
      dsimp [zTs]
      rwa [heq]

lemma loc_z1R {orig out : zW} (hS : BStep orig out) :
    ∃ r,BRIncs false 128 (zTs (zP33 ++ orig) default) r /\
      zTs (zP33 ++ out) default = zTs [V,V,Q,V] r := by
  rcases hS with ⟨n,v,a,b,J,ds,hI,hD⟩
  have hB : BRIncs false (n * 2) default (zTs ds default) := by
    have heq : n * 2 = ((1 + n) - 1) * 2 := by omega
    rw [heq]; exact loc_z1Q hD (by omega)
  have hR_orig : BRIncs false 249044 (zTs orig default) (zTs (v ++ ds) default) := by
    have hR := loc_z1l hI hB
    simpa [z15,zTs,zDd] using! hR
  have hR_p33 := zBRIncs_P33 hR_orig
  refine ⟨zTs (zOut33 ++ (v ++ ds)) default,?_ ,?_⟩
  · rw [z15,z15]; exact hR_p33
  · have h_eq : zP33 ++ ([V,V,K,V] ++ v ++ ds) = [V,V,Q,V] ++ (zOut33 ++ (v ++ ds)) := by
      simp [zP33,zOut33,List.append_assoc]
    rw [h_eq,z15]

def loc_zPf : Nat -> Nat -> Option zW
  | 0,_ => none
  | _ + 1,0 => none
  | _ + 1,1 => some [Q]
  | fuel + 1,m + 2 =>
    match loc_zPf fuel ((m + 2) / 2) with
    | none => none
    | some ws => some ((if (m + 2) % 2 == 0 then K else Q) :: ws)

lemma loc_z1S (fuel : Nat) :
    ∀ (m : Nat) (ws : zW),loc_zPf fuel m = some ws ->
      ∃ H,Binary m H (zTs ws default) := by
  induction fuel with
  | zero => intro m ws h; contradiction
  | succ fuel ih =>
    intro m ws h
    rcases m with _ | _ | m
    · contradiction
    · injection h with h; subst h
      exact ⟨1,Binary.one⟩
    · dsimp [loc_zPf] at h
      cases hrec : loc_zPf fuel ((m + 2) / 2) with
      | none => rw [hrec] at h; contradiction
      | some ws' =>
        rw [hrec] at h
        injection h with h; subst h
        rcases ih ((m + 2) / 2) ws' hrec with ⟨H,hB⟩
        have hq : (m + 2) / 2 = 1 + ((m + 2) / 2 - 1) := by omega
        rw [hq] at hB
        rcases Nat.mod_two_eq_zero_or_one (m + 2) with hmod | hmod
        · have hcond : ((m + 2) % 2 == 0) = true := beq_iff_eq.mpr hmod
          rw [hcond]; dsimp [zTs]
          refine ⟨1 + H,?_⟩
          have heq : m + 2 = 2 + ((m + 2) / 2 - 1) * 2 := by omega
          rw [heq]; exact Binary.zero hB
        · have hcond : ((m + 2) % 2 == 0) = false := beq_false_of_ne (by omega)
          rw [hcond]; dsimp [zTs]
          refine ⟨1 + H,?_⟩
          have heq : m + 2 = 3 + ((m + 2) / 2 - 1) * 2 := by omega
          rw [heq]; exact Binary.two hB

inductive Choice where
  | CT | CP0 | CP1 | CS00 | CS01 | CS10 | CS11
  | COC0 (r : Nat) | COC1 (r : Nat) | CEC (r : Nat)
  | CSP0 | CSP1 | CSC0 (r : Nat) | CSC1 (r : Nat)
deriving DecidableEq

open Choice

def zInS : Choice -> Bool
  | CSP0 | CSP1 | CSC0 _ | CSC1 _ => true
  | _ => false

def zOutS : Choice -> Bool
  | COC0 _ | COC1 _ | CEC _ | CSC0 _ | CSC1 _ => true
  | _ => false

def zGetN : Choice -> Nat -> Nat
  | CT,k => k - 2
  | CP0,k | CP1,k | CSP0,k | CSP1,k => k - 1
  | CS00,k | CS01,k => (k - 2) / 4
  | CS10,k | CS11,k => (k - 4) / 4
  | COC0 _,k | CSC0 _,k => (k - 3) / 4
  | COC1 _,k | CSC1 _,k => (k - 5) / 4
  | CEC _,k => (k - 6) / 2

def loc_z1W : Choice -> Nat -> Nat
  | CT,n => 2 + n
  | CP0,n | CP1,n | CSP0,n | CSP1,n => 1 + n
  | CS00,n | CS01,n => 2 + n * 4
  | CS10,n | CS11,n => 4 + n * 4
  | COC0 _,n | CSC0 _,n => 3 + n * 4
  | COC1 _,n | CSC1 _,n => 5 + n * 4
  | CEC _,n => 6 + n * 2

def loc_z1X : Choice -> Nat -> Nat
  | CT,n | CP1,n | CS01,n | CS11,n | CSP1,n => 1 + n * 2
  | CP0,n | CS00,n | CS10,n | CSP0,n => n * 2
  | COC0 r,n | COC1 r,n => 1 + n * 2 ^ (1 + r)
  | CEC r,n => 1 + (1 + n * 2) * 2 ^ (1 + r)
  | CSC0 r,n | CSC1 r,n => 1 + n * 2 ^ (2 + r)

def loc_z1Y : Choice -> zW
  | CT => [V]
  | CP0 => [Q,K]
  | CP1 => [Q,Q]
  | CS00 | CS10 | CSP0 => [K]
  | CS01 | CS11 | CSP1 => [Q]
  | COC0 r | COC1 r => zQK r [V]
  | CEC r | CSC0 r | CSC1 r => K :: zQK r [V]

def loc_z1Z : Choice -> zW
  | CT | CP0 | CP1 | CSP0 | CSP1 => [V]
  | CS00 | CS01 => [K]
  | CS10 | CS11 => [Q]
  | COC0 r => K :: zR r V
  | COC1 r => Q :: zR r V
  | CEC r => zR (1 + r) V
  | CSC0 r => K :: zR (1 + r) V
  | CSC1 r => Q :: zR (1 + r) V

def loc_z20 : List Choice -> Bool -> Nat -> zW -> Option zW
  | [],s,k,u =>
    forceNat (k / 2) (fun n =>
    if s == false then
      if k == n * 2 then
        if u.all z23 then loc_zPf 600 (1 + n) else none
      else none
    else none)
  | ch :: cs,s,k,u =>
    forceNat (zGetN ch k) (fun n =>
    if s == zInS ch then
      if k == loc_z1W ch n then
        match zSw (loc_z1Y ch) u with
        | none => none
        | some w =>
          forceNat (loc_z1X ch n) (fun k' =>
          match loc_z20 cs (zOutS ch) k' w with
          | none => none
          | some x => some (loc_z1Z ch ++ x))
      else none
    else none)

lemma loc_z21 (cs : List Choice) :
    ∀ (s : Bool) (k : Nat) (u v : zW),loc_z20 cs s k u = some v ->
      BRIncs s k (zTs u default) (zTs v default) := by
  induction cs with
  | nil =>
    intro s k u v hE
    dsimp [loc_z20, forceNat_eq] at hE
    cases hs : (s == false) with
    | false => rw [hs] at hE; contradiction
    | true =>
      rw [hs] at hE
      have rfl_s : s = false := beq_iff_eq.mp hs
      subst rfl_s
      cases hk : (k == (k / 2) * 2) with
      | false => rw [hk] at hE; contradiction
      | true =>
        rw [hk] at hE
        have rfl_k : k = (k / 2) * 2 := beq_iff_eq.mp hk
        cases hu : u.all z23 with
        | false => rw [hu] at hE; contradiction
        | true =>
          rw [hu] at hE
          dsimp at hE
          rw [z24 u hu]
          rcases loc_z1S 600 (1 + k / 2) v hE with ⟨H,hB⟩
          have hR := z0H hB
          have heq : ((1 + k / 2) - 1) * 2 = k := by omega
          rwa [heq] at hR
  | cons ch cs ih =>
    intro s k u v hE
    dsimp [loc_z20, forceNat_eq] at hE
    cases hs : (s == zInS ch) with
    | false => rw [hs] at hE; contradiction
    | true =>
      rw [hs] at hE
      have rfl_s : s = zInS ch := beq_iff_eq.mp hs
      subst rfl_s
      cases hk : (k == loc_z1W ch (zGetN ch k)) with
      | false => rw [hk] at hE; contradiction
      | true =>
        rw [hk] at hE
        dsimp at hE
        have rfl_k : k = loc_z1W ch (zGetN ch k) := beq_iff_eq.mp hk
        cases hU : zSw (loc_z1Y ch) u with
        | none => rw [hU] at hE; contradiction
        | some w =>
          rw [hU] at hE
          dsimp at hE
          cases hC : loc_z20 cs (zOutS ch) (loc_z1X ch (zGetN ch k)) w with
          | none => rw [hC] at hE; contradiction
          | some x =>
            rw [hC] at hE
            injection hE with hE; subst hE
            have rfl_u := z22 (loc_z1Y ch) u w hU
            subst rfl_u
            have hIH := ih (zOutS ch) (loc_z1X ch (zGetN ch k)) w x hC
            rw [rfl_k]
            cases ch with
            | CT => exact BRIncs.T hIH
            | CP0 => exact BRIncs.pair0 hIH
            | CP1 => exact BRIncs.pair1 hIH
            | CS00 => exact BRIncs.short00 hIH
            | CS01 => exact BRIncs.short01 hIH
            | CS10 => exact BRIncs.short10 hIH
            | CS11 => exact BRIncs.short11 hIH
            | COC0 r =>
              dsimp [loc_z1Y,loc_z1Z,zInS,zOutS,loc_z1W,loc_z1X] at hIH ⊢
              rw [z15 (zQK r [V]) w]; dsimp [zTs]; rw [z15 (zR r V) x]
              exact BRIncs.odd_chain0 r hIH
            | COC1 r =>
              dsimp [loc_z1Y,loc_z1Z,zInS,zOutS,loc_z1W,loc_z1X] at hIH ⊢
              rw [z15 (zQK r [V]) w]; dsimp [zTs]; rw [z15 (zR r V) x]
              exact BRIncs.odd_chain1 r hIH
            | CEC r =>
              dsimp [loc_z1Y,loc_z1Z,zInS,zOutS,loc_z1W,loc_z1X] at hIH ⊢
              dsimp [zTs]; rw [z15 (zQK r [V]) w,z15 (zR (1 + r) V) x]
              exact BRIncs.even_chain r hIH
            | CSP0 => exact BRIncs.shift_pair0 hIH
            | CSP1 => exact BRIncs.shift_pair1 hIH
            | CSC0 r =>
              dsimp [loc_z1Y,loc_z1Z,zInS,zOutS,loc_z1W,loc_z1X] at hIH ⊢
              dsimp [zTs]; rw [z15 (zQK r [V]) w,z15 (zR (1 + r) V) x]
              exact BRIncs.shift_chain0 r hIH
            | CSC1 r =>
              dsimp [loc_z1Y,loc_z1Z,zInS,zOutS,loc_z1W,loc_z1X] at hIH ⊢
              dsimp [zTs]; rw [z15 (zQK r [V]) w,z15 (zR (1 + r) V) x]
              exact BRIncs.shift_chain1 r hIH

def loc_z22 (cs : List Choice) (u : zW) : Option zW :=
  match loc_z20 cs false 128 (u ++ [K]) with
  | some v => some ([V,V,Q,V] ++ v)
  | none => none

lemma loc_z23 (cs : List Choice) (u v : zW) (h : loc_z22 cs u = some v) :
    ∃ r,BRIncs false 128 (zTs u default) r /\ zTs v default = zTs [V,V,Q,V] r := by
  dsimp [loc_z22] at h
  cases hE : loc_z20 cs false 128 (u ++ [K]) with
  | none => rw [hE] at h; contradiction
  | some w =>
    rw [hE] at h
    injection h with h; subst h
    refine ⟨zTs w default,?_,rfl⟩
    have hR := loc_z21 cs false 128 (u ++ [K]) w hE
    simpa [z15,zTs,zDd] using! hR

inductive loc_Rounds : zB -> zB -> Prop where
  | refl (r : zB) : loc_Rounds r r
  | next {r s t0 : zB} :
      BRIncs false 128 r s -> loc_Rounds (zTs [V,V,Q,V] s) t0 -> loc_Rounds r t0

def loc_z24 : List (List Choice) -> zW -> Option zW
  | [],u => some u
  | c :: cs,u =>
    match loc_z22 c u with
    | none => none
    | some v => loc_z24 cs v

lemma loc_z25 (cs : List (List Choice)) :
    ∀ (u v : zW),loc_z24 cs u = some v ->
      loc_Rounds (zTs u default) (zTs v default) := by
  induction cs with
  | nil =>
    intro u v h
    injection h with h; subst h
    exact loc_Rounds.refl _
  | cons c cs ih =>
    intro u v h
    dsimp [loc_z24] at h
    cases hW : loc_z22 c u with
    | none => rw [hW] at h; contradiction
    | some w =>
      rw [hW] at h
      rcases loc_z23 c u w hW with ⟨r,hR,hEq⟩
      refine loc_Rounds.next hR ?_
      rw [<- hEq]
      exact ih w v h

def zN11 : zW -> Nat
  | [] => 0
  | V :: u => 1 + zN11 u
  | K :: u => zN11 u
  | Q :: u => zN11 u

def zP11 : zW -> Nat
  | [] => 0
  | V :: u => zP11 u
  | K :: u => 1 + zP11 u
  | Q :: u => 1 + zP11 u

lemma z11_pow (u : zW) :
    z1h u * ((2 ^ zN11 u : Nat) : Rat) = ((2 ^ zP11 u : Nat) : Rat) := by
  induction u with
  | nil => simp [z1h,zN11,zP11]
  | cons w u ih =>
    cases w with
    | V =>
      dsimp [z1h,zN11,zP11]
      rw [zP2 (zN11 u),Nat.cast_add]
      have h_eq : z1h u * (1 / 2) * (((2 ^ zN11 u : Nat) : Rat) + ((2 ^ zN11 u : Nat) : Rat)) =
          z1h u * ((2 ^ zN11 u : Nat) : Rat) := by ring
      linarith only [h_eq,ih]
    | K =>
      dsimp [z1h,zN11,zP11]
      rw [zP2 (zP11 u),Nat.cast_add]
      have h_eq : z1h u * 2 * ((2 ^ zN11 u : Nat) : Rat) =
          2 * (z1h u * ((2 ^ zN11 u : Nat) : Rat)) := by ring
      linarith only [h_eq,ih]
    | Q =>
      dsimp [z1h,zN11,zP11]
      rw [zP2 (zP11 u),Nat.cast_add]
      have h_eq : z1h u * 2 * ((2 ^ zN11 u : Nat) : Rat) =
          2 * (z1h u * ((2 ^ zN11 u : Nat) : Rat)) := by ring
      linarith only [h_eq,ih]

def zWU : zW -> Nat
  | [] => 0
  | V :: u => (zWU u + 1) / 2
  | K :: u => 90112 + 2 * zWU u
  | Q :: u => 65536 + 2 * zWU u

lemma zWU_ge (u : zW) :
    65536 * loc_z0W u <= ((zWU u : Nat) : Rat) := by
  induction u with
  | nil => simp [loc_z0W,zWU]
  | cons w u ih =>
    cases w with
    | V =>
      dsimp [loc_z0W,zWU]
      have hdiv : zWU u <= 2 * ((zWU u + 1) / 2) := by omega
      have hdiv_q : ((zWU u : Nat) : Rat) <= ((2 * ((zWU u + 1) / 2) : Nat) : Rat) := by exact_mod_cast hdiv
      push_cast at hdiv_q
      linarith only [ih,hdiv_q]
    | K =>
      dsimp [loc_z0W,zWU]; push_cast; linarith only [ih]
    | Q =>
      dsimp [loc_z0W,zWU]; push_cast; linarith only [ih]

def zZNat : zW -> Nat
  | [] => 0
  | V :: u => zZNat u
  | K :: u => 1 + 2 * zZNat u
  | Q :: u => 2 * zZNat u

lemma zZNat_eq (u : zW) (h : u.all z25 = true) :
    z1f u = ((zZNat u : Nat) : Rat) := by
  induction u with
  | nil => simp [z1f,zZNat]
  | cons w u ih =>
    cases w with
    | V => contradiction
    | K =>
      dsimp [List.all,z25] at h
      dsimp [z1f,zZNat]; rw [ih h]; push_cast; ring
    | Q =>
      dsimp [List.all,z25] at h
      dsimp [z1f,zZNat]; rw [ih h]; push_cast; ring

def zLastV : zW -> Bool
  | [] => false
  | [x] => x == V
  | _ :: y :: ys => zLastV (y :: ys)

lemma zLastV_eq (u : zW) (h : zLastV u = true) : ∃ w,u = w ++ [V] := by
  induction u with
  | nil => contradiction
  | cons x u ih =>
    cases u with
    | nil =>
      cases x <;> try contradiction
      exact ⟨[],rfl⟩
    | cons y ys =>
      change zLastV (y :: ys) = true at h
      rcases ih h with ⟨w,hw⟩
      exact ⟨x :: w,by rw [hw]; rfl⟩

def zInitVV : zW -> Bool
  | V :: V :: u => zLastV u
  | _ => false

lemma zInitVV_eq (u : zW) (h : zInitVV u = true) : ∃ w,u = V :: V :: (w ++ [V]) := by
  rcases u with _ | ⟨_ | _ | _,_ | ⟨_ | _ | _,u'⟩⟩ <;> try contradiction
  change zLastV u' = true at h
  rcases zLastV_eq u' h with ⟨w,hw⟩
  exact ⟨w,by rw [hw]⟩

def zInitQK : zW -> Bool
  | Q :: K :: _ => true
  | _ => false

lemma zInitQK_eq (u v : zW) (h : zInitQK u = true) : ∃ w,u ++ v = Q :: K :: w := by
  rcases u with _ | ⟨_ | _ | _,_ | ⟨_ | _ | _,u'⟩⟩ <;> try contradiction
  exact ⟨u' ++ v,rfl⟩

lemma loc_z28 (u hi_low hi_top : zW)
    (hD_low : hi_low.all z25 = true)
    (hD_top : hi_top.all z25 = true)
    (hTopLen : hi_top.length = 16)
    (hPow : zP11 u + (hi_low.length + 16) = 7 + zN11 u)
    (hU11_nat : 4 + zP11 u <= zN11 u)
    (hEnd : zInitVV u = true)
    (hLu : z0L u = true)
    (hLo : zInitQK hi_low = true)
    (hW_nat : zWU u <= 969932)
    (hZ_nat : 10 * (1 + zZNat hi_top) <= 651776) :
    BGood (u ++ ((hi_low ++ hi_top) ++ zTail8)) := by
  let hi8 := hi_low ++ hi_top
  have hD : hi8.all z25 = true := by dsimp [hi8]; rw [List.all_append,hD_low,hD_top]; rfl
  rcases z26 hi8 hD with ⟨A,hI⟩
  have hLen : hi8.length = hi_low.length + 16 := by dsimp [hi8]; rw [List.length_append,hTopLen]
  have h11_u := z11_pow u
  have hPow2 : 2 ^ zP11 u * 2 ^ hi8.length = 128 * 2 ^ zN11 u := by
    rw [<- Nat.pow_add,hLen,hPow,Nat.pow_add]
  have hPow2_q : ((2 ^ zP11 u : Nat) : Rat) * ((2 ^ hi8.length : Nat) : Rat) = 128 * ((2 ^ zN11 u : Nat) : Rat) := by
    exact_mod_cast hPow2
  have hPos : 0 < ((2 ^ zN11 u : Nat) : Rat) := by exact_mod_cast zPp (zN11 u)
  have hHeight : z1h u * ((2 ^ hi8.length : Nat) : Rat) = 128 := by
    nlinarith only [h11_u,hPow2_q,hPos]
  have hLe2 : 16 * 2 ^ zP11 u <= 2 ^ zN11 u := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hU11_nat
    rw [Nat.pow_add] at this; omega
  have hLe2_q : 16 * ((2 ^ zP11 u : Nat) : Rat) <= ((2 ^ zN11 u : Nat) : Rat) := by
    exact_mod_cast hLe2
  have hU11 : z1h u <= 1 / 16 := by
    nlinarith only [h11_u,hLe2_q,hPos]
  have hW_q : ((zWU u : Nat) : Rat) <= 969932 := by exact_mod_cast hW_nat
  have hW_ge := zWU_ge u
  have hW : loc_z0W u <= 74 / 5 := by linarith only [hW_q,hW_ge]
  rcases z26 hi_low hD_low with ⟨A_low,hI_low⟩
  rcases z26 hi_top hD_top with ⟨A_top,hI_top⟩
  have hDw_low := zDw hI_low
  have hDw_top := zDw hI_top
  have hZ_low_le : z1f hi_low <= z1h hi_low := by
    have h1 := z1i hi_low
    have h2 := (loc_zWn hi_low).2.2.1
    linarith only [h1,h2,hDw_low.1,hDw_low.2.1]
  have h11_top : z1h hi_top = 65536 := by
    have h1 := hDw_top.1; rw [hTopLen] at h1
    have h2 : ((2 ^ 16 : Nat) : Rat) = 65536 := by norm_num
    linarith only [h1,h2]
  have h11_hi8 : z1h hi8 = ((2 ^ hi8.length : Nat) : Rat) := (zDw hI).1
  have h11_split : z1h hi8 = z1h hi_low * z1h hi_top := by dsimp [hi8]; exact z1m hi_low hi_top
  have h_u_low : z1h u * z1h hi_low = 1 / 512 := by
    have h_eq : z1h u * ((2 ^ hi8.length : Nat) : Rat) = 65536 * (z1h u * z1h hi_low) := by
      rw [<- h11_hi8,h11_split,h11_top]; ring
    linarith only [hHeight,h_eq]
  have hZ_split : z1f hi8 = z1f hi_low + z1h hi_low * z1f hi_top := by
    dsimp [hi8]; exact z1k hi_low hi_top
  have hZ_top_eq := zZNat_eq hi_top hD_top
  have hZ_top_q : 10 * (1 + ((zZNat hi_top : Nat) : Rat)) <= 651776 := by
    exact_mod_cast hZ_nat
  have hSu := zSp u
  have hZ : z1h u * z1f hi8 <= 1273 / 10 := by
    have h_uz_split : z1h u * z1f hi8 = z1h u * z1f hi_low + (z1h u * z1h hi_low) * z1f hi_top := by
      rw [hZ_split]; ring
    have h_uz_low : z1h u * z1f hi_low <= z1h u * z1h hi_low := by
      nlinarith only [hSu,hZ_low_le]
    have h_uz_top : (z1h u * z1h hi_low) * z1f hi_top = (1 / 512) * ((zZNat hi_top : Nat) : Rat) := by
      rw [h_u_low,hZ_top_eq]
    linarith only [h_uz_split,h_uz_low,h_u_low,h_uz_top,hZ_top_q]
  exact BGood.intro hi8.length u A hi8 hI hHeight hU11
    (zInitVV_eq u hEnd) hLu (zInitQK_eq hi_low hi_top hLo) hW hZ

lemma zH_d1_odd (n : Nat) : Seg ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ (1 + n)) d1 d0 := by
  simpa only [zLp',List.cons_append,List.nil_append] using! zSg zH4 (zSa z0k n)

def zHExec : Nat -> zW -> Option zW
  | 0,u => some u
  | _,[] => none
  | k + 1,V :: u =>
    match zHExec ((k + 1) * 2) u with
    | some v => some (V :: v)
    | none => none
  | k + 1,K :: u =>
    let m := (k + 1) / 2
    if k + 1 == m * 2 then
      match zHExec m u with
      | some v => some (K :: v)
      | none => none
    else
      match zHExec m u with
      | some v => some (Q :: v)
      | none => none
  | k + 1,Q :: u =>
    let m := (k + 1) / 2
    if k + 1 == m * 2 then
      match zHExec m u with
      | some v => some (Q :: v)
      | none => none
    else
      match zHExec (1 + m) u with
      | some v => some (K :: v)
      | none => none

lemma zHExec_ok (u : zW) :
    ∀ (k : Nat) (v : zW),zHExec k u = some v ->
      Side ([Call.ch] ^ k) (zTs u default) (zTs v default) := by
  induction u with
  | nil =>
    intro k v h
    cases k with
    | zero =>
      injection h with h; subst h
      exact Side.nil _
    | succ k => contradiction
  | cons w u ih =>
    intro k v h
    cases k with
    | zero =>
      injection h with h; subst h
      exact Side.nil _
    | succ k =>
      cases w with
      | V =>
        dsimp [zHExec] at h
        cases hE : zHExec ((k + 1) * 2) u with
        | none => rw [hE] at h; contradiction
        | some v' =>
          rw [hE] at h
          injection h with h; subst h
          exact zSc (zS3 (k + 1)) (ih _ _ hE)
      | K =>
        dsimp [zHExec] at h
        cases hk : (k + 1 == ((k + 1) / 2) * 2) with
        | true =>
          rw [hk] at h; dsimp at h
          cases hE : zHExec ((k + 1) / 2) u with
          | none => rw [hE] at h; contradiction
          | some v' =>
            rw [hE] at h
            injection h with h; subst h
            have heq : k + 1 = ((k + 1) / 2) * 2 := beq_iff_eq.mp hk
            rw [heq]
            exact zSc (zH_d0_even ((k + 1) / 2)) (ih _ _ hE)
        | false =>
          rw [hk] at h; dsimp at h
          cases hE : zHExec ((k + 1) / 2) u with
          | none => rw [hE] at h; contradiction
          | some v' =>
            rw [hE] at h
            injection h with h; subst h
            have hne : k + 1 ≠ ((k + 1) / 2) * 2 := by
              intro hc; have := beq_iff_eq.mpr hc; rw [this] at hk; contradiction
            have heq : k + 1 = 1 + ((k + 1) / 2) * 2 := by omega
            rw [heq]
            exact zSc (zH_d0_odd ((k + 1) / 2)) (ih _ _ hE)
      | Q =>
        dsimp [zHExec] at h
        cases hk : (k + 1 == ((k + 1) / 2) * 2) with
        | true =>
          rw [hk] at h; dsimp at h
          cases hE : zHExec ((k + 1) / 2) u with
          | none => rw [hE] at h; contradiction
          | some v' =>
            rw [hE] at h
            injection h with h; subst h
            have heq : k + 1 = ((k + 1) / 2) * 2 := beq_iff_eq.mp hk
            rw [heq]
            exact zSc (zH_d1_even ((k + 1) / 2)) (ih _ _ hE)
        | false =>
          rw [hk] at h; dsimp at h
          cases hE : zHExec (1 + (k + 1) / 2) u with
          | none => rw [hE] at h; contradiction
          | some v' =>
            rw [hE] at h
            injection h with h; subst h
            have hne : k + 1 ≠ ((k + 1) / 2) * 2 := by
              intro hc; have := beq_iff_eq.mpr hc; rw [this] at hk; contradiction
            have heq : k + 1 = 1 + ((k + 1) / 2) * 2 := by omega
            rw [heq]
            exact zSc (zH_d1_odd ((k + 1) / 2)) (ih _ _ hE)

abbrev w_pre3_rest : zF := t ++ t ++ (t ++ d1)

abbrev w_pre3 : zF := w_word ++ w_pre3_rest

abbrev w_pre5_rest : zF := w_pre3_rest ++ t ++ (t ++ d0)

abbrev w_pre5 : zF := w_word ++ w_pre5_rest

abbrev w_pre_rest : zF := w_pre5_rest ++ t ++ (t ++ d0)

abbrev w_pre : zF := w_word ++ w_pre_rest

lemma zW_pre3_seg :
    Seg [.ch,.cj,.ch] ([.ch] ^ 4 ++ [.cp] ++ [.ch] ^ 2) w_pre3_rest
      (t ++ t ++ (d0 ++ t)) := by
  unfold w_pre3_rest
  exact zS0 (zS0 zW_s1 zW_s2) zW_s3

lemma zW_pre5_seg :
    Seg [.ch,.cj,.ch] ([.ch] ^ 8 ++ [.cj,.ch]) w_pre5_rest
      (t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t)) := by
  unfold w_pre5_rest
  exact zS0 (zS0 zW_pre3_seg zW_s4) zW_s5

lemma zW_pre_seg :
    Seg [.ch,.cj,.ch] ([.ch] ^ 16) w_pre_rest
      (t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one))) := by
  unfold w_pre_rest
  exact zS0 (zS0 zW_pre5_seg zW_s6) zW_s7

lemma zW_pre3_full {r r' : zB} (h : Side ([.ch] ^ 4 ++ [.cp] ++ [.ch] ^ 2) r r') :
    (zCL lh (w_pre3 +> r)) [canon_tm]⊢⁺ (zCL lh (w_pre5 +> (t +> r'))) := by
  have h_side := zW_pre3_seg r r' h
  have h_turn := zW_turn h_side
  have h_in : w_word +> (w_pre3_rest +> r) = w_pre3 +> r := by
    unfold w_pre3 w_pre3_rest; simp only [List.append_assoc,append_assoc]
  have h_out : (w_word ++ t ++ t ++ (t ++ d1)) +>
      ((t ++ t ++ (d0 ++ t)) +> r') =
      w_pre5 +> (t +> r') := by
    unfold w_pre5 w_pre5_rest w_pre3_rest w_word t d0 d1
    simp only [List.cons_append,List.nil_append,append_cons,append_nil]
  rwa [h_in,h_out] at h_turn

lemma zW_pre5_full {r r' : zB} (h : Side ([.ch] ^ 8 ++ [.cj,.ch]) r r') :
    (zCL lh (w_pre5 +> r)) [canon_tm]⊢⁺ (zCL lh (w_pre +> (t +> r'))) := by
  have h_side := zW_pre5_seg r r' h
  have h_turn := zW_turn h_side
  have h_in : w_word +> (w_pre5_rest +> r) = w_pre5 +> r := by
    unfold w_pre5 w_pre5_rest; simp only [List.append_assoc,append_assoc]
  have h_out : (w_word ++ t ++ t ++ (t ++ d1)) +>
      ((t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t)) +> r') =
      w_pre +> (t +> r') := by
    unfold w_pre w_pre_rest w_pre5_rest w_pre3_rest w_word t d0 d1
    simp only [List.cons_append,List.nil_append,append_cons,append_nil]
  rwa [h_in,h_out] at h_turn

lemma zW_pre_full {r r' : zB} (h : Side ([.ch] ^ 16) r r') :
    (zCL lh (w_pre +> r)) [canon_tm]⊢⁺ (zCf r') := by
  have h_side := zW_pre_seg r r' h
  have h_turn := zW_turn h_side
  have h_in : w_word +> (w_pre_rest +> r) = w_pre +> r := by
    unfold w_pre w_pre_rest; simp only [List.append_assoc,append_assoc]
  have h_out : (w_word ++ t ++ t ++ (t ++ d1)) +>
      ((t ++ t ++ (d0 ++ t) ++ t ++ (d0 ++ t) ++ t ++ (d1 ++ (t ++ one))) +> r') =
      w_base +> r' := by
    unfold w_base w_word w_rest t d0 d1 one
    simp only [List.cons_append,List.nil_append,append_cons,append_nil]
  unfold zCf
  rwa [h_in,h_out] at h_turn

lemma z108_seg :
    Seg ([.ch] ^ 16) ([.cj] ++ [.ch] ^ 31) (d0 ++ t ++ (t ++ one)) (d0 ++ t ++ t) := by
  have h1 : Seg ([.ch] ^ 16) ([.ch] ^ 8) d0 d0 := zH_d0_even 8
  have h2 : Seg ([.ch] ^ 8) ([.ch] ^ 16) t t := zS3 8
  have h3 : Seg ([.ch] ^ 16) ([.cj] ++ [.ch] ^ 31) (t ++ one) t := by
    have ha := zSg zH2 (zS3 15)
    have heq_in : ([Call.ch] : List Call) ++ [Call.ch] ^ 15 = [Call.ch] ^ 16 := rfl
    have heq_out : ([Call.cj,Call.ch] : List Call) ++ [Call.ch] ^ (15 * 2) = [Call.cj] ++ [Call.ch] ^ 31 := rfl
    rwa [heq_in,heq_out] at ha
  exact zS0 (zS0 h1 h2) h3

abbrev zCmF (c : CCfg) (n : Nat) : Option CCfg := Counter.bmultiStep canon_tm n c

lemma zTcF {c1 c2 : CCfg} {n : Nat} (hn : 0 < n) (h : zCmF c1 n = some c2) :
    (c_to_cfg c1) [canon_tm]⊢⁺ (c_to_cfg c2) :=
  ⟨n, hn, Counter.bmultiStep_sound n c1 c2 h⟩

lemma loc_z2q {orig out : zW} (hS : BStep orig out) :
    (zCf (zTs (zP33 ++ orig) default)) [canon_tm]⊢⁺ (zCf (zTs (zP33 ++ out) default)) := by
  rcases loc_z1R hS with ⟨r,hI,hEq⟩
  rw [hEq]
  exact loc_z2p hI

lemma loc_z2r {r r' : zB} (h : loc_Rounds r r') :
    (zCf r) [canon_tm]⊢* (zCf r') := by
  induction h with
  | refl _ => exact ⟨0,rfl⟩
  | next hR _ ih =>
    rcases loc_z2p hR with ⟨n,_,hn⟩
    rcases ih with ⟨m,hm⟩
    exact ⟨n + m,zMt canon_tm _ _ _ n m hn hm⟩

lemma zIm {M : Machine (Fin 2) (Fin 6)} {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep M c (j + d) = some c') :
    (multiStep M c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep M c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl


end BusyBeaver.WordCanonBR
