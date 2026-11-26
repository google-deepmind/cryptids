/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA`

Formal Collatz-like transducer acceleration (`IsValidAcceleration`) for the 6-state, 2-symbol
Busy Beaver holdout `1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA`.

Both half-tapes are represented as `(1, 4)` stacks `List (ℕ × Sep)` via `encStack`, where each
entry `(a, b)` encodes `1^{a+1} 0^{1..4}` (`b ∈ {.s1, .s2, .s3, .s4}`):
$$
M_0(L, R) :=
  \mathrm{tail}(\mathrm{encStack}(L))\,\mathrm{A}{>}\,0\,\mathrm{tail}(\mathrm{encStack}(R)).
$$
Starting from the blank tape (`init []`), the machine reaches
`start = .M0 [(0, .s1), (0, .s1)] [(1, .s1)]` after 6 raw Turing machine steps. Halting
(`A1 -> ---`) occurs only at the four genuine overflow gates in `next`, `stepD`, `evalQ0Aux`, and
`stepBit1`.

## Accelerated Transition Rules

```text
encStack []            = 0^inf
encStack ((a, b) :: S) = 1^{a+1} ++ encSep b ++ encStack S

M0(L, [])             -> stepD .s1 L []
M0(L, (0, bR) :: Rt)  -> stepD .s1 L (peelSep bR Rt)
M0(L, (1, bR) :: Rt)  -> M0((0, .s1) :: tailAsRight L, peelSep bR Rt)
M0(L, (2, bR) :: Rt)  -> M0((0, .s2) :: tailAsRight L, peelSep bR Rt)
M0(L, (d+3, _) :: _)  -> Halt

Start: M0([(0, .s1), (0, .s1)], [(1, .s1)]), reached after 6 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Separator zero-run width (`s1` = `0`, `s2` = `00`, `s3` = `000`, `s4` = `0000`). -/
inductive Sep where
  | s1
  | s2
  | s3
  | s4
  deriving DecidableEq, Repr

/-- Render a separator width as a list of `1` to `4` zeros. -/
def encSep : Sep → List (Fin 2)
  | .s1 => [0]
  | .s2 => [0, 0]
  | .s3 => [0, 0, 0]
  | .s4 => [0, 0, 0, 0]

/-- Encode a `(1, 4)` stack `List (ℕ × Sep)` into a `ListBlank (Fin 2)` half-tape. -/
def encStack : List (ℕ × Sep) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: xs =>
    ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
      (ListBlank.append (encSep b) (encStack xs))

/-- Symbolic configuration state `M0(L, R)` over `(1, 4)` stacks. -/
inductive State where
  | M0 (L R : List (ℕ × Sep))
  deriving DecidableEq, Repr

/-- Prepend a leading `1` to `encStack S`. -/
def bumpHead : List (ℕ × Sep) → List (ℕ × Sep)
  | [] => [(0, .s1)]
  | (a, b) :: xs => (a + 1, b) :: xs

/-- Convert `1 :: (encStack S).tail` into a full `encStack` list. -/
def tailAsRight : List (ℕ × Sep) → List (ℕ × Sep)
  | [] => [(0, .s1)]
  | (a, b) :: xs => (a, b) :: xs

/-- Convert `encStack S` into `(encStack _).tail` form. -/
def rightAsTail : List (ℕ × Sep) → List (ℕ × Sep)
  | [] => []
  | (a, b) :: xs => (a + 1, b) :: xs

/-- Prepend `encSep b` to `encStack S` in `(encStack _).tail` form. -/
def pushZeroSep (b : Sep) : List (ℕ × Sep) → List (ℕ × Sep)
  | [] => []
  | (a, b') :: xs => (0, b) :: (a, b') :: xs

/-- Peel one leading `0` from `(encStack ((0, b) :: S)).tail`. -/
def peelSep : Sep → List (ℕ × Sep) → List (ℕ × Sep)
  | _, [] => []
  | .s1, (a, b') :: xs => (a + 1, b') :: xs
  | .s2, (a, b') :: xs => (0, .s1) :: (a, b') :: xs
  | .s3, (a, b') :: xs => (0, .s2) :: (a, b') :: xs
  | .s4, (a, b') :: xs => (0, .s3) :: (a, b') :: xs

/-- Peel `00` from `(encStack ((0, b) :: S)).tail` when `S = []` or `b ≠ .s1`. -/
def peelInner : Sep → List (ℕ × Sep) → List (ℕ × Sep)
  | _, [] => [(0, .s1)]
  | .s2, (a₂, b₂) :: rs => (a₂ + 1, b₂) :: rs
  | .s3, (a₂, b₂) :: rs => (0, .s1) :: (a₂, b₂) :: rs
  | _, (a₂, b₂) :: rs => (0, .s2) :: (a₂, b₂) :: rs

/-- Peel one leading `0` from `encSep c ++ 1 :: (encStack R).tail`. -/
def popRD : Sep → List (ℕ × Sep) → List (ℕ × Sep)
  | .s1, R => rightAsTail (tailAsRight R)
  | .s2, R => (0, .s1) :: tailAsRight R
  | .s3, R => (0, .s2) :: tailAsRight R
  | .s4, R => (0, .s3) :: tailAsRight R

/-- Parity contribution of a separator width to the pushdown termination weight. -/
def sepParity : Sep → ℕ
  | .s1 => 0
  | .s2 => 1
  | .s3 => 0
  | .s4 => 1

/-- Pushdown termination weight of a right-hand `(1, 4)` stack. -/
def weightR : List (ℕ × Sep) → ℕ
  | [] => 0
  | (a, b) :: rs => if rs.isEmpty then a else a + sepParity b + weightR rs

/-- Control modes at the left return boundary of the pushdown sweep. -/
inductive FState where
  | f00
  | f01
  | f02
  | f03
  | f04
  | f05
  deriving DecidableEq, Repr

/-- Entry context modes (`[]`, `[0]`, or `[0, 1]`) for the pushdown sweep. -/
inductive Stage3Mode where
  | q0
  | qz
  | qz1
  deriving DecidableEq, Repr

/-- Consume a `0` bit from the pushdown left-buffer in `FState`. -/
def stepBit0 (runZ1 : List (ℕ × Sep) → Option (FState × List (ℕ × Sep))) :
    FState × List (ℕ × Sep) → Option (FState × List (ℕ × Sep))
  | (.f00, R₁) => some (.f01, R₁)
  | (.f01, R₁) => some (.f02, bumpHead R₁)
  | (.f02, R₁) => runZ1 R₁
  | (.f03, R₁) => some (.f04, R₁)
  | (.f04, R₁) => some (.f00, (0, .s1) :: (0, .s1) :: R₁)
  | (.f05, R₁) => some (.f00, (0, .s1) :: (0, .s1) :: R₁)

/-- Consume a `1` bit from the pushdown left-buffer in `FState` (`none` on `.f05`). -/
def stepBit1 (runZ : List (ℕ × Sep) → Option (FState × List (ℕ × Sep))) :
    FState × List (ℕ × Sep) → Option (FState × List (ℕ × Sep))
  | (.f00, R₁) => runZ R₁
  | (.f01, R₁) => some (.f03, R₁)
  | (.f02, R₁) => some (.f00, (0, .s1) :: R₁)
  | (.f03, R₁) => some (.f05, R₁)
  | (.f04, R₁) => some (.f00, (0, .s3) :: R₁)
  | (.f05, _) => none

/-- Structural inner pass across `R` during a `q0` pushdown sweep (`none` on `a ≥ 2`). -/
def evalQ0Aux
    (runZ runZ1 : List (ℕ × Sep) → Option (FState × List (ℕ × Sep))) :
    List (ℕ × Sep) → Option (FState × List (ℕ × Sep))
  | [] => some (.f00, [(0, .s1)])
  | (0, .s1) :: Rt =>
    if Rt.isEmpty then
      some (.f00, (0, .s1) :: peelInner .s1 [])
    else
      ((evalQ0Aux runZ runZ1 Rt).bind (stepBit0 runZ1)).bind (stepBit1 runZ)
  | (0, .s2) :: Rt => some (.f00, (0, .s1) :: peelInner .s2 Rt)
  | (0, .s3) :: Rt => some (.f00, (0, .s1) :: peelInner .s3 Rt)
  | (0, .s4) :: Rt => some (.f00, (0, .s1) :: peelInner .s4 Rt)
  | (1, .s1) :: Rt =>
    if Rt.isEmpty then
      (runZ1 (peelInner .s1 [])).bind (stepBit1 runZ)
    else
      ((runZ Rt).bind (stepBit0 runZ1)).bind (stepBit1 runZ)
  | (1, .s2) :: Rt => (runZ1 (peelInner .s2 Rt)).bind (stepBit1 runZ)
  | (1, .s3) :: Rt => (runZ1 (peelInner .s3 Rt)).bind (stepBit1 runZ)
  | (1, .s4) :: Rt => (runZ1 (peelInner .s4 Rt)).bind (stepBit1 runZ)
  | (_ + 2, _) :: _ => none

/-- Structural pushdown evaluator bounded by `weightR R + 1` fuel. -/
def evalStage3 : ℕ → Stage3Mode → List (ℕ × Sep) → Option (FState × List (ℕ × Sep))
  | 0, _, _ => some (.f00, [(0, .s1)])
  | fuel + 1, m, R =>
    let runZ := evalStage3 fuel .qz
    let runZ1 := evalStage3 fuel .qz1
    let res0 := evalQ0Aux runZ runZ1 R
    match m with
    | .q0 => res0
    | .qz => res0.bind (stepBit0 runZ1)
    | .qz1 => (res0.bind (stepBit0 runZ1)).bind (stepBit1 runZ)

/-- Exit the `000001` left wall at the end of a pushdown sweep back into `State.M0`. -/
def exitF (L₂ : List (ℕ × Sep)) : FState × List (ℕ × Sep) → State
  | (.f00, R) => .M0 ((0, .s4) :: tailAsRight L₂) ((0, .s1) :: R)
  | (.f01, R) => .M0 ((0, .s1) :: (0, .s3) :: tailAsRight L₂) (rightAsTail (bumpHead R))
  | (.f02, R) => .M0 ((0, .s1) :: (0, .s4) :: tailAsRight L₂) (rightAsTail R)
  | (.f03, R) => .M0 ((0, .s1) :: (0, .s3) :: tailAsRight L₂) ((0, .s2) :: R)
  | (.f04, R) => .M0 ((0, .s1) :: (0, .s4) :: tailAsRight L₂) ((0, .s2) :: R)
  | (.f05, R) => .M0 ((0, .s1) :: (0, .s4) :: tailAsRight L₂) ((0, .s2) :: R)

/-- Leftward `D`-mode sweep across `L` (`none` on `a₁ ≥ 2` or halting pushdown sweep). -/
def stepD : Sep → List (ℕ × Sep) → List (ℕ × Sep) → Option State
  | c, [], R => some (.M0 [(0, .s1), (0, .s1)] (popRD c R))
  | c, (0, .s1) :: [], R => some (.M0 [(0, .s1), (0, .s1)] (popRD c R))
  | c, (0, .s1) :: (0, .s1) :: L₂, R =>
    if L₂.isEmpty then
      some (.M0 [] ((0, .s1) :: (0, c) :: tailAsRight R))
    else
      stepD .s3 L₂ ((0, c) :: tailAsRight R)
  | c, (0, .s1) :: (0, .s2) :: L₂, R =>
    some (.M0 (pushZeroSep .s1 L₂) ((0, .s1) :: (0, c) :: tailAsRight R))
  | c, (0, .s1) :: (0, .s3) :: L₂, R =>
    some (.M0 (pushZeroSep .s2 L₂) ((0, .s1) :: (0, c) :: tailAsRight R))
  | c, (0, .s1) :: (0, .s4) :: L₂, R =>
    some (.M0 (pushZeroSep .s3 L₂) ((0, .s1) :: (0, c) :: tailAsRight R))
  | c, (0, .s1) :: (1, .s1) :: L₂, R =>
    some (.M0 (pushZeroSep .s2 L₂) ((1, c) :: tailAsRight R))
  | c, (0, .s1) :: (1, .s2) :: L₂, R =>
    some (.M0 (pushZeroSep .s3 L₂) ((1, c) :: tailAsRight R))
  | c, (0, .s1) :: (1, .s3) :: L₂, R =>
    some (.M0 (pushZeroSep .s4 L₂) ((1, c) :: tailAsRight R))
  | c, (0, .s1) :: (1, .s4) :: L₂, R =>
    if L₂.isEmpty then
      some (.M0 [] ((1, c) :: tailAsRight R))
    else
      let rP := (0, c) :: tailAsRight R
      exitF L₂ <$> evalStage3 (weightR rP + 1) .q0 rP
  | c, (0, .s1) :: (a₂ + 2, b₂) :: L₂, R =>
    some (.M0 ((0, .s1) :: (a₂, b₂) :: L₂) ((1, c) :: tailAsRight R))
  | c, (0, .s2) :: L₁, R =>
    some (.M0 ((0, .s1) :: peelInner .s2 L₁) (popRD c R))
  | c, (0, .s3) :: L₁, R =>
    some (.M0 ((0, .s1) :: peelInner .s3 L₁) (popRD c R))
  | c, (0, .s4) :: L₁, R =>
    some (.M0 ((0, .s1) :: peelInner .s4 L₁) (popRD c R))
  | c, (1, b₁) :: L₁, R =>
    some (.M0 (peelSep b₁ L₁) ((1, c) :: tailAsRight R))
  | _, (_ + 2, _) :: _, _ => none

/-- Initial accelerated state, reached after 6 raw Turing machine steps from `init []`. -/
def start : State := .M0 [(0, .s1), (0, .s1)] [(1, .s1)]

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .M0 L R =>
    Cfg.headRight SixState.A (encStack L).tail (ListBlank.cons 0 (encStack R).tail)

/-- Accelerated transition function (`none` indicates halting). -/
def next : State → Option State
  | .M0 L [] => stepD .s1 L []
  | .M0 L ((0, bR) :: Rt) => stepD .s1 L (peelSep bR Rt)
  | .M0 L ((1, bR) :: Rt) => some (.M0 ((0, .s1) :: tailAsRight L) (peelSep bR Rt))
  | .M0 L ((2, bR) :: Rt) => some (.M0 ((0, .s2) :: tailAsRight L) (peelSep bR Rt))
  | .M0 _ ((_ + 3, _) :: _) => none

/-! ## Stack Encoding Lemmas -/

private def encTail (S : List (ℕ × Sep)) : ListBlank (Fin 2) :=
  (encStack S).tail

private theorem encode_eq (L R : List (ℕ × Sep)) :
    encode (.M0 L R) = Cfg.headRight A (encTail L) (ListBlank.cons 0 (encTail R)) :=
  rfl

private theorem encStack_nil : encStack [] = default :=
  rfl

private theorem encTail_nil : encTail [] = default :=
  ListBlank.tail_default

private theorem encStack_zero (b : Sep) (S : List (ℕ × Sep)) :
    encStack ((0, b) :: S) = ListBlank.cons 1 (ListBlank.append (encSep b) (encStack S)) :=
  rfl

private theorem encStack_succ (a : ℕ) (b : Sep) (S : List (ℕ × Sep)) :
    encStack ((a + 1, b) :: S) = ListBlank.cons 1 (encStack ((a, b) :: S)) := by
  simp only [encStack, ListBlank.append_pow_succ, ListBlank.append_cons, ListBlank.append_nil]

private theorem encStack_head_one (a : ℕ) (b : Sep) (S : List (ℕ × Sep)) :
    (encStack ((a, b) :: S)).head = 1 := by
  rcases a with _ | a
  · rw [encStack_zero, ListBlank.head_cons]
  · rw [encStack_succ, ListBlank.head_cons]

private theorem encStack_cons_eq_one_cons_encTail (a : ℕ) (b : Sep) (S : List (ℕ × Sep)) :
    encStack ((a, b) :: S) = ListBlank.cons 1 (encTail ((a, b) :: S)) := by
  unfold encTail
  nth_rw 1 [← ListBlank.cons_head_tail (encStack ((a, b) :: S))]
  rw [encStack_head_one]

private theorem encTail_zero (b : Sep) (S : List (ℕ × Sep)) :
    encTail ((0, b) :: S) = ListBlank.append (encSep b) (encStack S) := by
  unfold encTail
  rw [encStack_zero, ListBlank.tail_cons]

private theorem encTail_succ (a : ℕ) (b : Sep) (S : List (ℕ × Sep)) :
    encTail ((a + 1, b) :: S) = ListBlank.cons 1 (encTail ((a, b) :: S)) := by
  unfold encTail
  rw [encStack_succ, ListBlank.tail_cons, encStack_cons_eq_one_cons_encTail, ListBlank.tail_cons]

private theorem encStack_bumpHead (S : List (ℕ × Sep)) :
    encStack (bumpHead S) = ListBlank.cons 1 (encStack S) := by
  rcases S with _ | ⟨⟨a, b⟩, xs⟩
  · simp [bumpHead, encStack, encSep]
  · exact encStack_succ a b xs

private theorem encStack_tailAsRight (S : List (ℕ × Sep)) :
    encStack (tailAsRight S) = ListBlank.cons 1 (encTail S) := by
  rcases S with _ | ⟨⟨a, b⟩, xs⟩
  · simp [tailAsRight, encStack, encSep, encTail_nil]
  · exact encStack_cons_eq_one_cons_encTail a b xs

private theorem encTail_rightAsTail (S : List (ℕ × Sep)) :
    encTail (rightAsTail S) = encStack S := by
  rcases S with _ | ⟨⟨a, b⟩, xs⟩
  · exact encTail_nil
  · dsimp only [rightAsTail]
    unfold encTail
    rw [encStack_succ, ListBlank.tail_cons]

private theorem encTail_pushZeroSep (b : Sep) (S : List (ℕ × Sep)) :
    encTail (pushZeroSep b S) = ListBlank.append (encSep b) (encStack S) := by
  rcases S with _ | ⟨⟨a, b'⟩, xs⟩
  · cases b <;> simp [pushZeroSep, encTail_nil, encStack_nil, encSep]
  · exact encTail_zero b ((a, b') :: xs)

private theorem encTail_zero_eq_zero_cons_peelSep (b : Sep) (S : List (ℕ × Sep)) :
    encTail ((0, b) :: S) = ListBlank.cons 0 (encTail (peelSep b S)) := by
  rcases S with _ | ⟨⟨a, b'⟩, xs⟩
  · cases b <;> simp [peelSep, encTail_zero, encTail_nil, encStack_nil, encSep]
  · cases b with
    | s1 =>
      dsimp only [peelSep, encSep]
      rw [encTail_zero, encTail_succ, ← encStack_cons_eq_one_cons_encTail]
      rfl
    | s2 =>
      dsimp only [peelSep, encSep]
      rw [encTail_zero, encTail_zero]
      rfl
    | s3 =>
      dsimp only [peelSep, encSep]
      rw [encTail_zero, encTail_zero]
      rfl
    | s4 =>
      dsimp only [peelSep, encSep]
      rw [encTail_zero, encTail_zero]
      rfl

private theorem peelInner_ne_nil (b : Sep) (S : List (ℕ × Sep)) : peelInner b S ≠ [] := by
  rcases S with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · simp [peelInner]
  · cases b <;> simp [peelInner]

private theorem encStack_peelInner (b : Sep) (S : List (ℕ × Sep)) :
    encStack (peelInner b S) = ListBlank.cons 1 (encTail (peelInner b S)) := by
  rcases h : peelInner b S with _ | ⟨⟨ai, bi⟩, rsi⟩
  · exact absurd h (peelInner_ne_nil b S)
  · exact encStack_cons_eq_one_cons_encTail ai bi rsi

private theorem encTail_zero_peelInner (b : Sep) (S : List (ℕ × Sep)) (h : S = [] ∨ b ≠ .s1) :
    encTail ((0, b) :: S) = ListBlank.cons 0 (ListBlank.cons 0 (encTail (peelInner b S))) := by
  rcases S with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · cases b <;> simp [peelInner, encTail_zero, encStack_nil, encSep]
  · cases b with
    | s1 =>
      rcases h with hnil | hne
      · cases hnil
      · exact absurd rfl hne
    | s2 =>
      dsimp only [peelInner, encSep]
      rw [encTail_zero, encTail_succ, ← encStack_cons_eq_one_cons_encTail]
      rfl
    | s3 =>
      dsimp only [peelInner, encSep]
      rw [encTail_zero, encTail_zero]
      rfl
    | s4 =>
      dsimp only [peelInner, encSep]
      rw [encTail_zero, encTail_zero]
      rfl

private theorem encStack_zero_peelInner (b : Sep) (S : List (ℕ × Sep)) (h : S = [] ∨ b ≠ .s1) :
    encStack ((0, b) :: S) =
      ListBlank.append [1, 0, 0] (encTail (peelInner b S)) := by
  rw [encStack_cons_eq_one_cons_encTail, encTail_zero_peelInner b S h]
  rfl

private theorem encStack_one_peelInner (b : Sep) (S : List (ℕ × Sep)) (h : S = [] ∨ b ≠ .s1) :
    encStack ((1, b) :: S) =
      ListBlank.append [1, 1, 0, 0] (encTail (peelInner b S)) := by
  rw [encStack_succ, encStack_zero_peelInner b S h]
  rfl

/-! ## Pushdown Sweep (`evalStage3`) Specification -/

private def wall (L₂ : List (ℕ × Sep)) : ListBlank (Fin 2) :=
  ListBlank.append [0, 0, 0, 0, 0, 1] (encTail L₂)

private def pCfg (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A (ListBlank.append W (wall L₂)) (ListBlank.cons 0 (encStack R))

private def fCfg : FState → List (ℕ × Sep) → List (Fin 2) → List (ℕ × Sep) → Cfg (Fin 2) (Fin 6)
  | .f00, L₂, W, R =>
    Cfg.headLeft F (ListBlank.append W (wall L₂)) (ListBlank.cons 0 (encStack R))
  | .f01, L₂, W, R =>
    Cfg.headLeft C (ListBlank.append W (wall L₂)) (ListBlank.append [0, 0] (encStack R))
  | .f02, L₂, W, R =>
    Cfg.headLeft E (ListBlank.append W (wall L₂)) (ListBlank.append [1, 0] (encStack R))
  | .f03, L₂, W, R =>
    Cfg.headLeft D (ListBlank.append W (wall L₂)) (ListBlank.append [0, 0, 0] (encStack R))
  | .f04, L₂, W, R =>
    Cfg.headLeft E (ListBlank.append W (wall L₂)) (ListBlank.append [1, 0, 0, 0] (encStack R))
  | .f05, L₂, W, R =>
    Cfg.headLeft A (ListBlank.append W (wall L₂)) (ListBlank.append [1, 0, 0, 0] (encStack R))

private def cost0 : FState → ℕ
  | .f00 => 0
  | .f01 => 1
  | .f02 => 1
  | .f03 => 0
  | .f04 => 1
  | .f05 => 1

private def cost1 : FState → ℕ
  | .f00 => 1
  | .f01 => 0
  | .f02 => 0
  | .f03 => 1
  | .f04 => 0
  | .f05 => 0

private def modeWords : Stage3Mode → List (Fin 2) → List (Fin 2)
  | .q0, W => W
  | .qz, W => 0 :: W
  | .qz1, W => 0 :: 1 :: W

private def modeCost : Stage3Mode → FState → ℕ
  | .q0 => cost0
  | .qz => cost1
  | .qz1 => cost0

private theorem cost0_le_cost1_succ (s : FState) : cost0 s ≤ cost1 s + 1 := by
  cases s <;> decide

private theorem cost1_le_cost0_succ (s : FState) : cost1 s ≤ cost0 s + 1 := by
  cases s <;> decide

private theorem weightR_cons_nonempty (a : ℕ) (b : Sep) (R : List (ℕ × Sep)) (hR : R ≠ []) :
    weightR ((a, b) :: R) = a + sepParity b + weightR R := by
  rcases R with _ | ⟨r₂, rs⟩
  · contradiction
  · rfl

private theorem weightR_bumpHead (R : List (ℕ × Sep)) (hR : R ≠ []) :
    weightR (bumpHead R) = 1 + weightR R := by
  rcases R with _ | ⟨⟨a, b⟩, rs⟩
  · contradiction
  · rcases rs with _ | ⟨r₂, rs'⟩
    · simp only [bumpHead, weightR, List.isEmpty_nil, ite_true]
      omega
    · simp only [bumpHead, weightR, List.isEmpty_cons, Bool.false_eq_true, ite_false]
      omega

private theorem weightR_peelInner_zero (b : Sep) (S : List (ℕ × Sep)) (h : S = [] ∨ b ≠ .s1) :
    weightR ((0, .s1) :: peelInner b S) = weightR ((0, b) :: S) := by
  rcases S with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · rfl
  · cases b with
    | s1 =>
      rcases h with hnil | hne
      · cases hnil
      · exact absurd rfl hne
    | s2 =>
      dsimp only [peelInner]
      rw [weightR_cons_nonempty 0 .s1 _ (by simp), weightR_cons_nonempty 0 .s2 _ (by simp)]
      have hbmp := weightR_bumpHead ((a₂, b₂) :: rs) (by simp)
      dsimp only [bumpHead, sepParity] at hbmp ⊢
      omega
    | s3 =>
      simp only [peelInner, weightR, List.isEmpty_cons, Bool.false_eq_true, ite_false, sepParity]
      omega
    | s4 =>
      simp only [peelInner, weightR, List.isEmpty_cons, Bool.false_eq_true, ite_false, sepParity]
      omega

private theorem weightR_peelInner_one (b : Sep) (S : List (ℕ × Sep)) (h : S = [] ∨ b ≠ .s1) :
    weightR (peelInner b S) + 1 = weightR ((1, b) :: S) := by
  have hne := peelInner_ne_nil b S
  have h0 : weightR ((0, .s1) :: peelInner b S) = weightR (peelInner b S) := by
    rw [weightR_cons_nonempty 0 .s1 _ hne]
    simp [sepParity]
  rw [← h0, weightR_peelInner_zero b S h]
  rcases S with _ | ⟨r₂, rs⟩
  · simp [weightR]
  · simp only [weightR, List.isEmpty_cons, Bool.false_eq_true, ite_false]
    omega

private theorem raw_P_0_rec (L₂ : List (ℕ × Sep)) (W : List (Fin 2))
    (Rt : List (ℕ × Sep)) (hR : Rt ≠ []) :
    ReachesPlus target (pCfg L₂ W ((0, .s1) :: Rt)) (pCfg L₂ (0 :: 1 :: W) Rt) := by
  rcases Rt with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · contradiction
  · dsimp only [pCfg]
    rw [encStack_zero, encStack_cons_eq_one_cons_encTail a₂ b₂ rs]
    dsimp only [encSep]
    bb_steps

private theorem raw_P_0_other (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (b : Sep)
    (Rt : List (ℕ × Sep)) (h : Rt = [] ∨ b ≠ .s1) :
    ReachesPlus target (pCfg L₂ W ((0, b) :: Rt))
      (fCfg .f00 L₂ W ((0, .s1) :: peelInner b Rt)) := by
  dsimp only [pCfg, fCfg]
  rw [encStack_zero_peelInner b Rt h]
  rcases hin : peelInner b Rt with _ | ⟨⟨ai, bi⟩, rsi⟩
  · exact absurd hin (peelInner_ne_nil b Rt)
  · rw [encStack_zero .s1, encStack_cons_eq_one_cons_encTail ai bi rsi]
    dsimp only [encSep]
    bb_steps

private theorem raw_P_1_rec (L₂ : List (ℕ × Sep)) (W : List (Fin 2))
    (Rt : List (ℕ × Sep)) (hR : Rt ≠ []) :
    ReachesPlus target (pCfg L₂ W ((1, .s1) :: Rt)) (pCfg L₂ (0 :: 0 :: 1 :: W) Rt) := by
  rcases Rt with _ | ⟨⟨a₂, b₂⟩, rs⟩
  · contradiction
  · dsimp only [pCfg]
    rw [encStack_succ 0 .s1, encStack_zero, encStack_cons_eq_one_cons_encTail a₂ b₂ rs]
    dsimp only [encSep]
    bb_steps

private theorem raw_P_1_other (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (b : Sep)
    (Rt : List (ℕ × Sep)) (h : Rt = [] ∨ b ≠ .s1) :
    ReachesPlus target (pCfg L₂ W ((1, b) :: Rt))
      (pCfg L₂ (0 :: 1 :: 1 :: W) (peelInner b Rt)) := by
  dsimp only [pCfg]
  rw [encStack_one_peelInner b Rt h]
  rcases hin : peelInner b Rt with _ | ⟨⟨ai, bi⟩, rsi⟩
  · exact absurd hin (peelInner_ne_nil b Rt)
  · rw [encStack_cons_eq_one_cons_encTail ai bi rsi]
    bb_steps

private theorem raw_P_ge2 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (a : ℕ) (b : Sep)
    (Rt : List (ℕ × Sep)) :
    ∃ cfg', ReachesStar target (pCfg L₂ W ((a + 2, b) :: Rt)) cfg' ∧
      (step target cfg').isNone := by
  dsimp only [pCfg]
  rw [encStack_succ (a + 1) b, encStack_succ a b, encStack_cons_eq_one_cons_encTail a b Rt]
  refine ⟨Cfg.headRight A (ListBlank.append [0, 0, 1] (ListBlank.append W (wall L₂)))
    (ListBlank.cons 1 (encTail ((a, b) :: Rt))), ?_, by bb_halt⟩
  exact (by bb_steps : ReachesPlus target _ _).to_star

private theorem raw_F00_bit0 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    ReachesPlus target (fCfg .f00 L₂ (0 :: W) R) (fCfg .f01 L₂ W R) := by
  dsimp only [fCfg]; bb_steps

private theorem raw_F01_bit0 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    ReachesPlus target (fCfg .f01 L₂ (0 :: W) R) (fCfg .f02 L₂ W (bumpHead R)) := by
  dsimp only [fCfg]; rw [encStack_bumpHead]; bb_steps

private theorem raw_F02_bit0 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    ReachesPlus target (fCfg .f02 L₂ (0 :: W) R) (pCfg L₂ (0 :: 1 :: W) R) := by
  dsimp only [fCfg, pCfg]; bb_steps

private theorem raw_F03_bit0 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    ReachesPlus target (fCfg .f03 L₂ (0 :: W) R) (fCfg .f04 L₂ W R) := by
  dsimp only [fCfg]; bb_steps

private theorem raw_F04_bit0 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    ReachesPlus target (fCfg .f04 L₂ (0 :: W) R)
      (fCfg .f00 L₂ W ((0, .s1) :: (0, .s1) :: R)) := by
  dsimp only [fCfg]; rw [encStack_zero, encStack_zero]; dsimp only [encSep]; bb_steps

private theorem raw_F05_bit0 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    ReachesPlus target (fCfg .f05 L₂ (0 :: W) R)
      (fCfg .f00 L₂ W ((0, .s1) :: (0, .s1) :: R)) := by
  dsimp only [fCfg]; rw [encStack_zero, encStack_zero]; dsimp only [encSep]; bb_steps

private theorem raw_F00_bit1 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    ReachesPlus target (fCfg .f00 L₂ (1 :: W) R) (pCfg L₂ (0 :: W) R) := by
  dsimp only [fCfg, pCfg]; bb_steps

private theorem raw_F01_bit1 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    ReachesPlus target (fCfg .f01 L₂ (1 :: W) R) (fCfg .f03 L₂ W R) := by
  dsimp only [fCfg]; bb_steps

private theorem raw_F02_bit1 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    ReachesPlus target (fCfg .f02 L₂ (1 :: W) R) (fCfg .f00 L₂ W ((0, .s1) :: R)) := by
  dsimp only [fCfg]; rw [encStack_zero]; dsimp only [encSep]; bb_steps

private theorem raw_F03_bit1 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    ReachesPlus target (fCfg .f03 L₂ (1 :: W) R) (fCfg .f05 L₂ W R) := by
  dsimp only [fCfg]; bb_steps

private theorem raw_F04_bit1 (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    ReachesPlus target (fCfg .f04 L₂ (1 :: W) R) (fCfg .f00 L₂ W ((0, .s3) :: R)) := by
  dsimp only [fCfg]; rw [encStack_zero]; dsimp only [encSep]; bb_steps

private theorem raw_F05_bit1_halt (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) (R : List (ℕ × Sep)) :
    (step target (fCfg .f05 L₂ (1 :: W) R)).isNone := by
  dsimp only [fCfg]; bb_halt

private def Stage3ResSpec (startCfg : Cfg (Fin 2) (Fin 6)) (L₂ : List (ℕ × Sep))
    (W_out : List (Fin 2)) (wBound : ℕ) (cost : FState → ℕ) :
    Option (FState × List (ℕ × Sep)) → Prop
  | some (s, R_out) =>
    R_out ≠ [] ∧ weightR R_out + cost s ≤ wBound ∧
      ReachesPlus target startCfg (fCfg s L₂ W_out R_out)
  | none =>
    ∃ cfg', ReachesStar target startCfg cfg' ∧ (step target cfg').isNone

private theorem stage3ResSpec_prepend {c₀ c₁ : Cfg (Fin 2) (Fin 6)} {L₂ : List (ℕ × Sep)}
    {W_out : List (Fin 2)} {wBound : ℕ} {cost : FState → ℕ}
    {res : Option (FState × List (ℕ × Sep))}
    (hstep : ReachesPlus target c₀ c₁)
    (hres : Stage3ResSpec c₁ L₂ W_out wBound cost res) :
    Stage3ResSpec c₀ L₂ W_out wBound cost res := by
  rcases res with _ | ⟨s, R_out⟩
  · obtain ⟨cfg', hstar, hhalt⟩ := hres
    exact ⟨cfg', hstep.to_star.trans hstar, hhalt⟩
  · obtain ⟨hne, hw, hplus⟩ := hres
    exact ⟨hne, hw, hstep.trans hplus⟩

private theorem stage3ResSpec_mono {c₀ : Cfg (Fin 2) (Fin 6)} {L₂ : List (ℕ × Sep)}
    {W_out : List (Fin 2)} {w₁ w₂ : ℕ} {cost₁ cost₂ : FState → ℕ}
    {res : Option (FState × List (ℕ × Sep))}
    (hres : Stage3ResSpec c₀ L₂ W_out w₁ cost₁ res)
    (hle : ∀ s R_out, weightR R_out + cost₁ s ≤ w₁ → weightR R_out + cost₂ s ≤ w₂) :
    Stage3ResSpec c₀ L₂ W_out w₂ cost₂ res := by
  rcases res with _ | ⟨s, R_out⟩
  · exact hres
  · obtain ⟨hne, hw, hplus⟩ := hres
    exact ⟨hne, hle s R_out hw, hplus⟩

private theorem stepBit0_spec
    {runZ1 : List (ℕ × Sep) → Option (FState × List (ℕ × Sep))}
    {c₀ : Cfg (Fin 2) (Fin 6)} {L₂ : List (ℕ × Sep)} {W_out : List (Fin 2)} {wBound : ℕ}
    {res : Option (FState × List (ℕ × Sep))}
    (hres : Stage3ResSpec c₀ L₂ (0 :: W_out) wBound cost0 res)
    (ihZ1 : ∀ R', R' ≠ [] → weightR R' < wBound →
      ∀ L' W', Stage3ResSpec (pCfg L' (0 :: 1 :: W') R') L' W' (weightR R') cost0 (runZ1 R')) :
    Stage3ResSpec c₀ L₂ W_out wBound cost1 (res.bind (stepBit0 runZ1)) := by
  rcases res with _ | ⟨s, R₁⟩
  · exact hres
  · obtain ⟨hR₁, hw₁, hreach⟩ := hres
    cases s with
    | f00 =>
      dsimp only [Option.bind, stepBit0, Stage3ResSpec]
      exact ⟨hR₁, by dsimp [cost0, cost1] at hw₁ ⊢; omega,
        hreach.trans (raw_F00_bit0 L₂ W_out R₁)⟩
    | f01 =>
      dsimp only [Option.bind, stepBit0, Stage3ResSpec]
      have hne : bumpHead R₁ ≠ [] := by
        rcases R₁ with _ | ⟨⟨a, b⟩, rs⟩
        · contradiction
        · simp [bumpHead]
      refine ⟨hne, ?_, hreach.trans (raw_F01_bit0 L₂ W_out R₁)⟩
      rw [weightR_bumpHead R₁ hR₁]
      dsimp [cost0, cost1] at hw₁ ⊢
      omega
    | f02 =>
      dsimp only [Option.bind, stepBit0]
      have hlt : weightR R₁ < wBound := by dsimp [cost0] at hw₁; omega
      have hp := hreach.trans (raw_F02_bit0 L₂ W_out R₁)
      have hsub := stage3ResSpec_prepend hp (ihZ1 R₁ hR₁ hlt L₂ W_out)
      refine stage3ResSpec_mono hsub (fun s' R_out hw_out => ?_)
      have hc := cost1_le_cost0_succ s'
      dsimp [cost0] at hw₁
      omega
    | f03 =>
      dsimp only [Option.bind, stepBit0, Stage3ResSpec]
      exact ⟨hR₁, by dsimp [cost0, cost1] at hw₁ ⊢; omega,
        hreach.trans (raw_F03_bit0 L₂ W_out R₁)⟩
    | f04 =>
      dsimp only [Option.bind, stepBit0, Stage3ResSpec]
      refine ⟨by simp, ?_, hreach.trans (raw_F04_bit0 L₂ W_out R₁)⟩
      rw [weightR_cons_nonempty 0 .s1 _ (by simp), weightR_cons_nonempty 0 .s1 R₁ hR₁]
      dsimp [sepParity, cost0, cost1] at hw₁ ⊢
      omega
    | f05 =>
      dsimp only [Option.bind, stepBit0, Stage3ResSpec]
      refine ⟨by simp, ?_, hreach.trans (raw_F05_bit0 L₂ W_out R₁)⟩
      rw [weightR_cons_nonempty 0 .s1 _ (by simp), weightR_cons_nonempty 0 .s1 R₁ hR₁]
      dsimp [sepParity, cost0, cost1] at hw₁ ⊢
      omega

private theorem stepBit1_spec
    {runZ : List (ℕ × Sep) → Option (FState × List (ℕ × Sep))}
    {c₀ : Cfg (Fin 2) (Fin 6)} {L₂ : List (ℕ × Sep)} {W_out : List (Fin 2)} {wBound : ℕ}
    {res : Option (FState × List (ℕ × Sep))}
    (hres : Stage3ResSpec c₀ L₂ (1 :: W_out) wBound cost1 res)
    (ihZ : ∀ R', R' ≠ [] → weightR R' < wBound →
      ∀ L' W', Stage3ResSpec (pCfg L' (0 :: W') R') L' W' (weightR R') cost1 (runZ R')) :
    Stage3ResSpec c₀ L₂ W_out wBound cost0 (res.bind (stepBit1 runZ)) := by
  rcases res with _ | ⟨s, R₁⟩
  · exact hres
  · obtain ⟨hR₁, hw₁, hreach⟩ := hres
    cases s with
    | f00 =>
      dsimp only [Option.bind, stepBit1]
      have hlt : weightR R₁ < wBound := by dsimp [cost1] at hw₁; omega
      have hp := hreach.trans (raw_F00_bit1 L₂ W_out R₁)
      have hsub := stage3ResSpec_prepend hp (ihZ R₁ hR₁ hlt L₂ W_out)
      refine stage3ResSpec_mono hsub (fun s' R_out hw_out => ?_)
      have hc := cost0_le_cost1_succ s'
      dsimp [cost1] at hw₁
      omega
    | f01 =>
      dsimp only [Option.bind, stepBit1, Stage3ResSpec]
      exact ⟨hR₁, by dsimp [cost1, cost0] at hw₁ ⊢; omega,
        hreach.trans (raw_F01_bit1 L₂ W_out R₁)⟩
    | f02 =>
      dsimp only [Option.bind, stepBit1, Stage3ResSpec]
      refine ⟨by simp, ?_, hreach.trans (raw_F02_bit1 L₂ W_out R₁)⟩
      rw [weightR_cons_nonempty 0 .s1 R₁ hR₁]
      dsimp [sepParity, cost1, cost0] at hw₁ ⊢
      omega
    | f03 =>
      dsimp only [Option.bind, stepBit1, Stage3ResSpec]
      exact ⟨hR₁, by dsimp [cost1, cost0] at hw₁ ⊢; omega,
        hreach.trans (raw_F03_bit1 L₂ W_out R₁)⟩
    | f04 =>
      dsimp only [Option.bind, stepBit1, Stage3ResSpec]
      refine ⟨by simp, ?_, hreach.trans (raw_F04_bit1 L₂ W_out R₁)⟩
      rw [weightR_cons_nonempty 0 .s3 R₁ hR₁]
      dsimp [sepParity, cost1, cost0] at hw₁ ⊢
      omega
    | f05 =>
      dsimp only [Option.bind, stepBit1, Stage3ResSpec]
      exact ⟨fCfg .f05 L₂ (1 :: W_out) R₁, hreach.to_star, raw_F05_bit1_halt L₂ W_out R₁⟩

private theorem evalQ0Aux_spec
    (runZ runZ1 : List (ℕ × Sep) → Option (FState × List (ℕ × Sep))) (fuel : ℕ)
    (ihZ : ∀ R', R' ≠ [] → weightR R' < fuel →
      ∀ L' W', Stage3ResSpec (pCfg L' (0 :: W') R') L' W' (weightR R') cost1 (runZ R'))
    (ihZ1 : ∀ R', R' ≠ [] → weightR R' < fuel →
      ∀ L' W', Stage3ResSpec (pCfg L' (0 :: 1 :: W') R') L' W' (weightR R') cost0 (runZ1 R'))
    (R : List (ℕ × Sep)) (hR : R ≠ []) (hfuel : weightR R ≤ fuel)
    (L₂ : List (ℕ × Sep)) (W : List (Fin 2)) :
    Stage3ResSpec (pCfg L₂ W R) L₂ W (weightR R) cost0 (evalQ0Aux runZ runZ1 R) := by
  induction R generalizing L₂ W with
  | nil => contradiction
  | cons hd Rt ihRt =>
    have ihZ_w : ∀ R', R' ≠ [] → weightR R' < weightR (hd :: Rt) →
        ∀ L' W', Stage3ResSpec (pCfg L' (0 :: W') R') L' W' (weightR R') cost1 (runZ R') :=
      fun R' hne hlt => ihZ R' hne (by omega)
    have ihZ1_w : ∀ R', R' ≠ [] → weightR R' < weightR (hd :: Rt) →
        ∀ L' W', Stage3ResSpec (pCfg L' (0 :: 1 :: W') R') L' W' (weightR R') cost0 (runZ1 R') :=
      fun R' hne hlt => ihZ1 R' hne (by omega)
    rcases hd with ⟨_ | _ | a, b⟩
    · cases b with
      | s1 =>
        rcases Rt with _ | ⟨r₂, rs⟩
        · dsimp only [evalQ0Aux, List.isEmpty_nil, ite_true, Stage3ResSpec]
          refine ⟨by simp, ?_, raw_P_0_other L₂ W .s1 [] (Or.inl rfl)⟩
          rw [weightR_peelInner_zero .s1 [] (Or.inl rfl)]
          dsimp [cost0]
          omega
        · dsimp only [evalQ0Aux, List.isEmpty_cons, Bool.false_eq_true, ite_false]
          have hne : (r₂ :: rs) ≠ [] := by simp
          have hweq : weightR ((0, .s1) :: r₂ :: rs) = weightR (r₂ :: rs) := by
            rw [weightR_cons_nonempty 0 .s1 _ hne]
            simp [sepParity]
          have hsub0 := ihRt hne (by omega) L₂ (0 :: 1 :: W)
          have hprep := stage3ResSpec_prepend (raw_P_0_rec L₂ W (r₂ :: rs) hne) hsub0
          have hprep' : Stage3ResSpec (pCfg L₂ W ((0, .s1) :: r₂ :: rs)) L₂ (0 :: 1 :: W)
              (weightR ((0, .s1) :: r₂ :: rs)) cost0
              (evalQ0Aux runZ runZ1 (r₂ :: rs)) := by
            rwa [hweq]
          exact stepBit1_spec (stepBit0_spec hprep' ihZ1_w) ihZ_w
      | s2 =>
        dsimp only [evalQ0Aux, Stage3ResSpec]
        have hcond : Rt = [] ∨ Sep.s2 ≠ .s1 := Or.inr (by decide)
        refine ⟨by simp, ?_, raw_P_0_other L₂ W .s2 Rt hcond⟩
        rw [weightR_peelInner_zero .s2 Rt hcond]
        dsimp [cost0]; omega
      | s3 =>
        dsimp only [evalQ0Aux, Stage3ResSpec]
        have hcond : Rt = [] ∨ Sep.s3 ≠ .s1 := Or.inr (by decide)
        refine ⟨by simp, ?_, raw_P_0_other L₂ W .s3 Rt hcond⟩
        rw [weightR_peelInner_zero .s3 Rt hcond]
        dsimp [cost0]; omega
      | s4 =>
        dsimp only [evalQ0Aux, Stage3ResSpec]
        have hcond : Rt = [] ∨ Sep.s4 ≠ .s1 := Or.inr (by decide)
        refine ⟨by simp, ?_, raw_P_0_other L₂ W .s4 Rt hcond⟩
        rw [weightR_peelInner_zero .s4 Rt hcond]
        dsimp [cost0]; omega
    · simp only [Nat.zero_add] at ihZ_w ihZ1_w hfuel
      have hOtherB : Rt = [] ∨ b ≠ .s1 →
          Stage3ResSpec (pCfg L₂ W ((1, b) :: Rt)) L₂ W (weightR ((1, b) :: Rt)) cost0
            ((runZ1 (peelInner b Rt)).bind (stepBit1 runZ)) := by
        intro hcond
        set R₁ := peelInner b Rt
        have hR₁ : R₁ ≠ [] := peelInner_ne_nil b Rt
        have hw₁ : weightR R₁ + 1 = weightR ((1, b) :: Rt) := weightR_peelInner_one b Rt hcond
        have hsub := ihZ1_w R₁ hR₁ (by omega) L₂ (1 :: W)
        have hprep := stage3ResSpec_prepend (raw_P_1_other L₂ W b Rt hcond) hsub
        have hmono := stage3ResSpec_mono hprep (w₂ := weightR ((1, b) :: Rt)) (cost₂ := cost1)
          (fun s' R_out hw_out => by have := cost1_le_cost0_succ s'; omega)
        exact stepBit1_spec hmono ihZ_w
      cases b with
      | s1 =>
        rcases Rt with _ | ⟨r₂, rs⟩
        · simp only [evalQ0Aux, List.isEmpty_nil, ite_true]
          exact hOtherB (Or.inl rfl)
        · simp only [evalQ0Aux, List.isEmpty_cons, Bool.false_eq_true, ite_false]
          have hne : (r₂ :: rs) ≠ [] := by simp
          have hw_tail : weightR (r₂ :: rs) + 1 = weightR ((1, .s1) :: r₂ :: rs) := by
            rw [weightR_cons_nonempty 1 .s1 _ hne]
            dsimp [sepParity]; omega
          have hsub := ihZ_w (r₂ :: rs) hne (by omega) L₂ (0 :: 1 :: W)
          have hprep := stage3ResSpec_prepend (raw_P_1_rec L₂ W (r₂ :: rs) hne) hsub
          have hmono := stage3ResSpec_mono hprep
            (w₂ := weightR ((1, .s1) :: r₂ :: rs)) (cost₂ := cost0)
            (fun s' R_out hw_out => by have := cost0_le_cost1_succ s'; omega)
          exact stepBit1_spec (stepBit0_spec hmono ihZ1_w) ihZ_w
      | s2 =>
        dsimp only [evalQ0Aux]
        exact hOtherB (Or.inr (by decide))
      | s3 =>
        dsimp only [evalQ0Aux]
        exact hOtherB (Or.inr (by decide))
      | s4 =>
        dsimp only [evalQ0Aux]
        exact hOtherB (Or.inr (by decide))
    · dsimp only [evalQ0Aux, Stage3ResSpec]
      exact raw_P_ge2 L₂ W a b Rt

private theorem evalStage3_spec (fuel : ℕ) :
    ∀ (m : Stage3Mode) (R : List (ℕ × Sep)), R ≠ [] → weightR R < fuel →
      ∀ (L₂ : List (ℕ × Sep)) (W : List (Fin 2)),
        Stage3ResSpec (pCfg L₂ (modeWords m W) R) L₂ W (weightR R) (modeCost m)
          (evalStage3 fuel m R) := by
  induction fuel with
  | zero =>
    intro _ _ _ hlt
    omega
  | succ fuel ih =>
    intro m R hR hlt L₂ W
    have ihZ : ∀ R', R' ≠ [] → weightR R' < fuel →
        ∀ L' W', Stage3ResSpec (pCfg L' (0 :: W') R') L' W' (weightR R') cost1
          (evalStage3 fuel .qz R') :=
      fun R' hne hlt' L' W' => ih .qz R' hne hlt' L' W'
    have ihZ1 : ∀ R', R' ≠ [] → weightR R' < fuel →
        ∀ L' W', Stage3ResSpec (pCfg L' (0 :: 1 :: W') R') L' W' (weightR R') cost0
          (evalStage3 fuel .qz1 R') :=
      fun R' hne hlt' L' W' => ih .qz1 R' hne hlt' L' W'
    have ihZ_R : ∀ R', R' ≠ [] → weightR R' < weightR R →
        ∀ L' W', Stage3ResSpec (pCfg L' (0 :: W') R') L' W' (weightR R') cost1
          (evalStage3 fuel .qz R') :=
      fun R' hne hlt' => ihZ R' hne (by omega)
    have ihZ1_R : ∀ R', R' ≠ [] → weightR R' < weightR R →
        ∀ L' W', Stage3ResSpec (pCfg L' (0 :: 1 :: W') R') L' W' (weightR R') cost0
          (evalStage3 fuel .qz1 R') :=
      fun R' hne hlt' => ihZ1 R' hne (by omega)
    cases m with
    | q0 =>
      dsimp only [evalStage3, modeWords, modeCost]
      exact evalQ0Aux_spec _ _ fuel ihZ ihZ1 R hR (by omega) L₂ W
    | qz =>
      dsimp only [evalStage3, modeWords, modeCost]
      have h0 := evalQ0Aux_spec _ _ fuel ihZ ihZ1 R hR (by omega) L₂ (0 :: W)
      exact stepBit0_spec h0 ihZ1_R
    | qz1 =>
      dsimp only [evalStage3, modeWords, modeCost]
      have h0 := evalQ0Aux_spec _ _ fuel ihZ ihZ1 R hR (by omega) L₂ (0 :: 1 :: W)
      exact stepBit1_spec (stepBit0_spec h0 ihZ1_R) ihZ_R

private theorem exitF_spec (L₂ : List (ℕ × Sep)) (p : FState × List (ℕ × Sep)) :
    ReachesPlus target (fCfg p.1 L₂ [] p.2) (encode (exitF L₂ p)) := by
  rcases p with ⟨s, R⟩
  cases s with
  | f00 =>
    dsimp only [fCfg, wall, exitF]
    rw [encode_eq, ListBlank.append_nil, encTail_zero .s4, encStack_tailAsRight, encTail_zero .s1]
    dsimp only [encSep]; bb_steps
  | f01 =>
    dsimp only [fCfg, wall, exitF]
    rw [encode_eq, ListBlank.append_nil, encTail_zero .s1, encStack_zero .s3,
      encStack_tailAsRight, encTail_rightAsTail, encStack_bumpHead]
    dsimp only [encSep]; bb_steps
  | f02 =>
    dsimp only [fCfg, wall, exitF]
    rw [encode_eq, ListBlank.append_nil, encTail_zero .s1, encStack_zero .s4,
      encStack_tailAsRight, encTail_rightAsTail]
    dsimp only [encSep]; bb_steps
  | f03 =>
    dsimp only [fCfg, wall, exitF]
    rw [encode_eq, ListBlank.append_nil, encTail_zero .s1, encStack_zero .s3,
      encStack_tailAsRight, encTail_zero .s2]
    dsimp only [encSep]; bb_steps
  | f04 =>
    dsimp only [fCfg, wall, exitF]
    rw [encode_eq, ListBlank.append_nil, encTail_zero .s1, encStack_zero .s4,
      encStack_tailAsRight, encTail_zero .s2]
    dsimp only [encSep]; bb_steps
  | f05 =>
    dsimp only [fCfg, wall, exitF]
    rw [encode_eq, ListBlank.append_nil, encTail_zero .s1, encStack_zero .s4,
      encStack_tailAsRight, encTail_zero .s2]
    dsimp only [encSep]; bb_steps

/-! ## Leftward `D`-Sweep (`stepD`) and Stage-1 (`next`) Validity -/

private def rD (c : Sep) (R : List (ℕ × Sep)) : ListBlank (Fin 2) :=
  ListBlank.append (encSep c) (ListBlank.cons 1 (encTail R))

private def cfgD (c : Sep) (L R : List (ℕ × Sep)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft D (encTail L) (rD c R)

private theorem one_cons_rD_eq_encStack (c : Sep) (R : List (ℕ × Sep)) :
    ListBlank.cons 1 (rD c R) = encStack ((0, c) :: tailAsRight R) := by
  unfold rD
  rw [encStack_zero, encStack_tailAsRight]

private theorem one_cons_rD_eq_encTail_one (c : Sep) (R : List (ℕ × Sep)) :
    ListBlank.cons 1 (rD c R) = encTail ((1, c) :: tailAsRight R) := by
  rw [encTail_succ, encTail_zero, encStack_tailAsRight]
  rfl

private theorem rD_eq_encTail_zero (c : Sep) (R : List (ℕ × Sep)) :
    rD c R = encTail ((0, c) :: tailAsRight R) := by
  unfold rD
  rw [encTail_zero, encStack_tailAsRight]

private theorem rD_eq_zero_cons_popRD (c : Sep) (R : List (ℕ × Sep)) :
    rD c R = ListBlank.cons 0 (encTail (popRD c R)) := by
  cases c with
  | s1 =>
    dsimp only [popRD, rD, encSep]
    rw [encTail_rightAsTail, encStack_tailAsRight]
    rfl
  | s2 =>
    dsimp only [popRD, rD, encSep]
    rw [encTail_zero, encStack_tailAsRight]
    rfl
  | s3 =>
    dsimp only [popRD, rD, encSep]
    rw [encTail_zero, encStack_tailAsRight]
    rfl
  | s4 =>
    dsimp only [popRD, rD, encSep]
    rw [encTail_zero, encStack_tailAsRight]
    rfl

private theorem raw_D_00 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headLeft D (ListBlank.append [0, 0] W) (ListBlank.cons 0 Z))
      (Cfg.headRight A (ListBlank.append [0, 1] W) (ListBlank.cons 0 Z)) := by
  bb_steps

private theorem raw_D_0100 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headLeft D (ListBlank.append [0, 1, 0, 0] W) Z)
      (Cfg.headRight A (ListBlank.cons 0 W) (ListBlank.append [0, 0, 1] Z)) := by
  bb_steps

private theorem raw_D_0101 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headLeft D (ListBlank.append [0, 1, 0, 1] W) Z)
      (Cfg.headLeft D W (ListBlank.append [0, 0, 0, 1] Z)) := by
  bb_steps

private theorem raw_D_011 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headLeft D (ListBlank.append [0, 1, 1] W) Z)
      (Cfg.headRight A (ListBlank.cons 0 W) (ListBlank.append [0, 1] Z)) := by
  bb_steps

private theorem raw_D_10 (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headLeft D (ListBlank.append [1, 0] W) Z)
      (Cfg.headRight A W (ListBlank.append [0, 1] Z)) := by
  bb_steps

private theorem raw_D_11_halt (W Z : ListBlank (Fin 2)) :
    ∃ cfg', ReachesStar target (Cfg.headLeft D (ListBlank.append [1, 1] W) Z) cfg' ∧
      (step target cfg').isNone := by
  refine ⟨Cfg.headLeft A (ListBlank.cons 1 W) (ListBlank.cons 1 Z), ?_, by bb_halt⟩
  exact (by bb_steps : ReachesPlus target _ _).to_star

private theorem stepD_spec (n : ℕ) :
    ∀ (L : List (ℕ × Sep)), L.length ≤ n → ∀ (c : Sep) (R : List (ℕ × Sep)),
      match stepD c L R with
      | some s' => ReachesPlus target (cfgD c L R) (encode s')
      | none => ∃ cfg', ReachesStar target (cfgD c L R) cfg' ∧ (step target cfg').isNone := by
  induction n with
  | zero =>
    intro L hlen c R
    rcases L with _ | ⟨_, _⟩
    · dsimp only [stepD, cfgD]
      rw [encode_eq, encTail_nil, rD_eq_zero_cons_popRD, encTail_zero, encStack_zero, encStack_nil]
      dsimp only [encSep]
      simpa using raw_D_00 default (encTail (popRD c R))
    · simp at hlen
  | succ n ih =>
    intro L hlen c R
    rcases L with _ | ⟨⟨_ | _ | a₁, b₁⟩, L₁⟩
    · dsimp only [stepD, cfgD]
      rw [encode_eq, encTail_nil, rD_eq_zero_cons_popRD, encTail_zero, encStack_zero, encStack_nil]
      dsimp only [encSep]
      simpa using raw_D_00 default (encTail (popRD c R))
    · cases b₁ with
      | s1 =>
        rcases L₁ with _ | ⟨⟨_ | _ | a₂, b₂⟩, L₂⟩
        · dsimp only [stepD, cfgD]
          rw [encode_eq, encTail_zero, encStack_nil, rD_eq_zero_cons_popRD,
            encTail_zero, encStack_zero, encStack_nil]
          dsimp only [encSep]
          simpa using raw_D_00 default (encTail (popRD c R))
        · cases b₂ with
          | s1 =>
            rcases L₂ with _ | ⟨r₃, L₃⟩
            · simp only [stepD, List.isEmpty_nil, ite_true, cfgD]
              rw [encode_eq, encTail_zero .s1, encStack_zero .s1, encStack_nil, encTail_nil,
                encTail_zero .s1, ← one_cons_rD_eq_encStack]
              dsimp only [encSep]
              simpa using raw_D_0100 default (rD c R)
            · simp only [stepD, List.isEmpty_cons, Bool.false_eq_true, ite_false]
              have h1 : ReachesPlus target
                  (cfgD c ((0, .s1) :: (0, .s1) :: r₃ :: L₃) R)
                  (cfgD .s3 (r₃ :: L₃) ((0, c) :: tailAsRight R)) := by
                rcases r₃ with ⟨a₃, b₃⟩
                have hr3 : rD .s3 ((0, c) :: tailAsRight R) =
                    ListBlank.append [0, 0, 0, 1] (rD c R) := by
                  dsimp only [rD, encSep]
                  rw [← rD_eq_encTail_zero]
                  rfl
                dsimp only [cfgD]
                rw [hr3, encTail_zero .s1, encStack_zero .s1,
                  encStack_cons_eq_one_cons_encTail a₃ b₃ L₃]
                dsimp only [encSep]
                exact raw_D_0101 (encTail ((a₃, b₃) :: L₃)) (rD c R)
              have hlen3 : (r₃ :: L₃).length ≤ n := by
                simp only [List.length_cons] at hlen ⊢
                omega
              have hsub := ih (r₃ :: L₃) hlen3 .s3 ((0, c) :: tailAsRight R)
              rcases hres : stepD .s3 (r₃ :: L₃) ((0, c) :: tailAsRight R) with _ | s'
              · rw [hres] at hsub
                obtain ⟨cfg', hstar, hhalt⟩ := hsub
                exact ⟨cfg', h1.to_star.trans hstar, hhalt⟩
              · rw [hres] at hsub
                exact h1.trans hsub
          | s2 =>
            dsimp only [stepD, cfgD]
            rw [encode_eq, encTail_zero .s1, encStack_zero .s2, encTail_pushZeroSep .s1,
              encTail_zero .s1, ← one_cons_rD_eq_encStack]
            dsimp only [encSep]
            exact raw_D_0100 (encStack L₂) (rD c R)
          | s3 =>
            dsimp only [stepD, cfgD]
            rw [encode_eq, encTail_zero .s1, encStack_zero .s3, encTail_pushZeroSep .s2,
              encTail_zero .s1, ← one_cons_rD_eq_encStack]
            dsimp only [encSep]
            exact raw_D_0100 (ListBlank.cons 0 (encStack L₂)) (rD c R)
          | s4 =>
            dsimp only [stepD, cfgD]
            rw [encode_eq, encTail_zero .s1, encStack_zero .s4, encTail_pushZeroSep .s3,
              encTail_zero .s1, ← one_cons_rD_eq_encStack]
            dsimp only [encSep]
            exact raw_D_0100 (ListBlank.append [0, 0] (encStack L₂)) (rD c R)
        · cases b₂ with
          | s1 =>
            dsimp only [stepD, cfgD]
            rw [encode_eq, encTail_zero .s1, encStack_succ 0 .s1, encStack_zero .s1,
              encTail_pushZeroSep .s2, ← one_cons_rD_eq_encTail_one]
            dsimp only [encSep]
            exact raw_D_011 (ListBlank.cons 0 (encStack L₂)) (rD c R)
          | s2 =>
            dsimp only [stepD, cfgD]
            rw [encode_eq, encTail_zero .s1, encStack_succ 0 .s2, encStack_zero .s2,
              encTail_pushZeroSep .s3, ← one_cons_rD_eq_encTail_one]
            dsimp only [encSep]
            exact raw_D_011 (ListBlank.append [0, 0] (encStack L₂)) (rD c R)
          | s3 =>
            dsimp only [stepD, cfgD]
            rw [encode_eq, encTail_zero .s1, encStack_succ 0 .s3, encStack_zero .s3,
              encTail_pushZeroSep .s4, ← one_cons_rD_eq_encTail_one]
            dsimp only [encSep]
            exact raw_D_011 (ListBlank.append [0, 0, 0] (encStack L₂)) (rD c R)
          | s4 =>
            rcases L₂ with _ | ⟨⟨a₃, b₃⟩, L₃⟩
            · simp only [stepD, List.isEmpty_nil, ite_true, cfgD, Nat.zero_add]
              rw [encode_eq, encTail_zero .s1, encStack_succ 0 .s4, encStack_zero .s4,
                encStack_nil, encTail_nil, ← one_cons_rD_eq_encTail_one]
              dsimp only [encSep]
              simpa using raw_D_011 default (rD c R)
            · simp only [stepD, List.isEmpty_cons, Bool.false_eq_true, ite_false, Nat.zero_add]
              set rP := (0, c) :: tailAsRight R
              have h1 : ReachesPlus target
                  (cfgD c ((0, .s1) :: (1, .s4) :: (a₃, b₃) :: L₃) R)
                  (pCfg ((a₃, b₃) :: L₃) [] rP) := by
                dsimp only [cfgD, pCfg, wall]
                rw [ListBlank.append_nil, encTail_zero .s1, encStack_succ 0 .s4, encStack_zero .s4,
                  encStack_cons_eq_one_cons_encTail a₃ b₃ L₃, ← one_cons_rD_eq_encStack]
                dsimp only [encSep]
                exact raw_D_011 (ListBlank.append [0, 0, 0, 0, 1] (encTail ((a₃, b₃) :: L₃)))
                  (rD c R)
              have hs3 := evalStage3_spec (weightR rP + 1) .q0 rP (by simp [rP]) (by omega)
                ((a₃, b₃) :: L₃) []
              dsimp only [modeWords] at hs3
              rcases hres : evalStage3 (weightR rP + 1) .q0 rP with _ | p
              · rw [hres] at hs3
                obtain ⟨cfg', hstar, hhalt⟩ := hs3
                exact ⟨cfg', h1.to_star.trans hstar, hhalt⟩
              · rw [hres] at hs3
                obtain ⟨_, _, hplus⟩ := hs3
                exact (h1.trans hplus).trans (exitF_spec ((a₃, b₃) :: L₃) p)
        · dsimp only [stepD, cfgD]
          rw [encode_eq, encTail_zero .s1, encStack_succ (a₂ + 1) b₂, encStack_succ a₂ b₂,
            encStack_cons_eq_one_cons_encTail a₂ b₂ L₂, encTail_zero .s1,
            encStack_cons_eq_one_cons_encTail a₂ b₂ L₂, ← one_cons_rD_eq_encTail_one]
          dsimp only [encSep]
          exact raw_D_011 (ListBlank.cons 1 (encTail ((a₂, b₂) :: L₂))) (rD c R)
      | s2 =>
        dsimp only [stepD, cfgD]
        have hcond : L₁ = [] ∨ Sep.s2 ≠ .s1 := Or.inr (by decide)
        rw [encode_eq, encTail_zero_peelInner .s2 L₁ hcond, rD_eq_zero_cons_popRD,
          encTail_zero .s1, encStack_peelInner]
        dsimp only [encSep]
        exact raw_D_00 (encTail (peelInner .s2 L₁)) (encTail (popRD c R))
      | s3 =>
        dsimp only [stepD, cfgD]
        have hcond : L₁ = [] ∨ Sep.s3 ≠ .s1 := Or.inr (by decide)
        rw [encode_eq, encTail_zero_peelInner .s3 L₁ hcond, rD_eq_zero_cons_popRD,
          encTail_zero .s1, encStack_peelInner]
        dsimp only [encSep]
        exact raw_D_00 (encTail (peelInner .s3 L₁)) (encTail (popRD c R))
      | s4 =>
        dsimp only [stepD, cfgD]
        have hcond : L₁ = [] ∨ Sep.s4 ≠ .s1 := Or.inr (by decide)
        rw [encode_eq, encTail_zero_peelInner .s4 L₁ hcond, rD_eq_zero_cons_popRD,
          encTail_zero .s1, encStack_peelInner]
        dsimp only [encSep]
        exact raw_D_00 (encTail (peelInner .s4 L₁)) (encTail (popRD c R))
    · dsimp only [stepD, cfgD]
      rw [encode_eq, encTail_succ 0 b₁, encTail_zero_eq_zero_cons_peelSep b₁ L₁,
        ← one_cons_rD_eq_encTail_one]
      exact raw_D_10 (encTail (peelSep b₁ L₁)) (rD c R)
    · dsimp only [stepD, cfgD]
      rw [encTail_succ (a₁ + 1) b₁, encTail_succ a₁ b₁]
      exact raw_D_11_halt (encTail ((a₁, b₁) :: L₁)) (rD c R)

private theorem raw_M0_nil (W : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A W (ListBlank.cons 0 default))
      (Cfg.headLeft D W (ListBlank.append [0, 1] default)) := by
  bb_steps

private theorem raw_M0_zero (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A W (ListBlank.append [0, 0] Z))
      (Cfg.headLeft D W (ListBlank.append [0, 1] Z)) := by
  bb_steps

private theorem raw_M0_one (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A W (ListBlank.append [0, 1, 0] Z))
      (Cfg.headRight A (ListBlank.append [0, 1] W) (ListBlank.cons 0 Z)) := by
  bb_steps

private theorem raw_M0_two (W Z : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A W (ListBlank.append [0, 1, 1, 0] Z))
      (Cfg.headRight A (ListBlank.append [0, 0, 1] W) (ListBlank.cons 0 Z)) := by
  bb_steps

private theorem raw_M0_ge3_halt (W Z : ListBlank (Fin 2)) :
    ∃ cfg', ReachesStar target
      (Cfg.headRight A W (ListBlank.append [0, 1, 1, 1] Z)) cfg' ∧
      (step target cfg').isNone := by
  refine ⟨Cfg.headRight A (ListBlank.append [0, 0, 1] W) (ListBlank.cons 1 Z), ?_, by bb_halt⟩
  exact (by bb_steps : ReachesPlus target _ _).to_star

/-! ## Acceleration Validity -/

private theorem init_reaches_start : ReachesStar target (init []) (encode start) := by
  refine (?_ : ReachesPlus target (init []) (encode start)).to_star
  dsimp only [start]
  rw [encode_eq, encTail_zero .s1, encStack_zero .s1, encStack_nil,
    encTail_succ 0 .s1, encTail_zero .s1, encStack_nil]
  dsimp only [encSep]
  bb_steps

private theorem step_all (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨L, _ | ⟨⟨_ | _ | _ | d, bR⟩, Rt⟩⟩
  · dsimp only [next]
    have h1 : ReachesPlus target (encode (.M0 L [])) (cfgD .s1 L []) := by
      rw [encode_eq, encTail_nil]
      exact raw_M0_nil (encTail L)
    have h2 := stepD_spec L.length L (Nat.le_refl _) .s1 []
    rcases hres : stepD .s1 L [] with _ | s'
    · rw [hres] at h2
      obtain ⟨cfg', hstar, hhalt⟩ := h2
      exact ⟨cfg', h1.to_star.trans hstar, hhalt⟩
    · rw [hres] at h2
      exact h1.trans h2
  · dsimp only [next]
    have h1 :
        ReachesPlus target (encode (.M0 L ((0, bR) :: Rt))) (cfgD .s1 L (peelSep bR Rt)) := by
      rw [encode_eq, encTail_zero_eq_zero_cons_peelSep bR Rt]
      exact raw_M0_zero (encTail L) (encTail (peelSep bR Rt))
    have h2 := stepD_spec L.length L (Nat.le_refl _) .s1 (peelSep bR Rt)
    rcases hres : stepD .s1 L (peelSep bR Rt) with _ | s'
    · rw [hres] at h2
      obtain ⟨cfg', hstar, hhalt⟩ := h2
      exact ⟨cfg', h1.to_star.trans hstar, hhalt⟩
    · rw [hres] at h2
      exact h1.trans h2
  · dsimp only [next]
    rw [encode_eq, encode_eq, encTail_succ 0 bR, encTail_zero_eq_zero_cons_peelSep bR Rt,
      encTail_zero .s1, encStack_tailAsRight]
    dsimp only [encSep]
    exact raw_M0_one (encTail L) (encTail (peelSep bR Rt))
  · dsimp only [next]
    rw [encode_eq, encode_eq, encTail_succ 1 bR, encTail_succ 0 bR,
      encTail_zero_eq_zero_cons_peelSep bR Rt, encTail_zero .s2, encStack_tailAsRight]
    dsimp only [encSep]
    exact raw_M0_two (encTail L) (encTail (peelSep bR Rt))
  · dsimp only [next]
    rw [encode_eq, encTail_succ (d + 2) bR, encTail_succ (d + 1) bR, encTail_succ d bR]
    exact raw_M0_ge3_halt (encTail L) (encTail ((d, bR) :: Rt))

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some s s' h := by
    have hs := step_all s
    rw [h] at hs
    exact hs
  step_none s h := by
    have hs := step_all s
    rw [h] at hs
    exact hs

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RBHHH_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA
