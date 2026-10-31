/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.AffRLE
meta import BusyBeaver.WordRLE
meta import BusyBeaver.AffRLE
public meta import Lean.Elab.Term

/-!
# Elaboration-Time RLE Certificate Synthesis & Kernel Proof Drivers (`BusyBeaver.ElabRLE`)

Pure-Lean elaboration-time infrastructure pairing with `BusyBeaver.WordRLE` and
`BusyBeaver.AffRLE`:

- `ToExpr` instances for `Run`, `EntryCfg`, `BTree`, `NatTrie`, `AffNat`, `AffRun`, `AffCfg`,
  `CompExit`, `AffOp`, and `ReturnCert`.
- `discoverReturnCert` — Machine-polymorphic symbolic affine simulator with automatic composite
  word interning and inner countdown-cycle synthesis (`SymExpr` probe + `verifyCycle` validation).
- `proveEntryPhase`, `proveCheckAll`, and `proveAffReplay` — Sliced `mkAuxTheorem` kernel proof
  drivers that reset Lean's WHNF cache between bounded slices so peak memory stays flat.
-/

@[expose] public section

namespace BusyBeaver.ElabRLE

open BusyBeaver.WordRLE BusyBeaver.AffRLE

/-- Construct a `NatTrie.checkAll` proof on an internal `.node` from proofs of its local value and
even/odd child subtries. -/
theorem checkAll_node {α : Type} {p : ℕ → α → Bool} {keyPrefix bitMul : ℕ}
    {val? : Option α} {l r : NatTrie α}
    (hv : (match val? with | none => true | some v => p keyPrefix v) = true)
    (hl : NatTrie.checkAll p keyPrefix (bitMul * 2) l = true)
    (hr : NatTrie.checkAll p (keyPrefix + bitMul) (bitMul * 2) r = true) :
    NatTrie.checkAll p keyPrefix bitMul (.node val? l r) = true :=
  (NatTrie.checkAll_node_iff p keyPrefix bitMul val? l r).mpr ⟨hv, hl, hr⟩

end BusyBeaver.ElabRLE

end

public meta section

namespace BusyBeaver.ElabRLE

open Lean Meta Elab Term
open BusyBeaver.WordRLE BusyBeaver.AffRLE

/-! ## `ToExpr` Instances for Certificate Data Structures -/

instance : ToExpr Run where
  toExpr r := mkApp2 (mkConst ``Run.mk) (toExpr r.sym) (toExpr r.count)
  toTypeExpr := mkConst ``Run

instance : ToExpr EntryCfg where
  toExpr c := mkApp4 (mkConst ``EntryCfg.mk)
    (toExpr c.q) (toExpr c.dir) (toExpr c.left) (toExpr c.right)
  toTypeExpr := mkConst ``EntryCfg

/-- Serialize a `BTree α` to a Lean kernel `Expr`. -/
def btreeToExpr {α : Type} [ToExpr α] (ty : Expr) : BTree α → Expr
  | .empty => mkApp (mkConst ``BTree.empty) ty
  | .leaf x => mkApp2 (mkConst ``BTree.leaf) ty (toExpr x)
  | .node l r => mkApp3 (mkConst ``BTree.node) ty (btreeToExpr ty l) (btreeToExpr ty r)

instance {α : Type} [ToExpr α] : ToExpr (BTree α) where
  toExpr t := btreeToExpr (toTypeExpr α) t
  toTypeExpr := mkApp (mkConst ``BTree) (toTypeExpr α)

/-- Serialize a `NatTrie α` to a Lean kernel `Expr`. -/
def natTrieToExpr {α : Type} [ToExpr α] (ty : Expr) : NatTrie α → Expr
  | .leaf => mkApp (mkConst ``NatTrie.leaf) ty
  | .node v l r =>
    mkApp4 (mkConst ``NatTrie.node) ty (toExpr v) (natTrieToExpr ty l) (natTrieToExpr ty r)

instance {α : Type} [ToExpr α] : ToExpr (NatTrie α) where
  toExpr t := natTrieToExpr (toTypeExpr α) t
  toTypeExpr := mkApp (mkConst ``NatTrie) (toTypeExpr α)

instance : ToExpr AffNat where
  toExpr x := mkApp2 (mkConst ``AffNat.mk) (toExpr x.a) (toExpr x.b)
  toTypeExpr := mkConst ``AffNat

instance : ToExpr AffRun where
  toExpr r := mkApp2 (mkConst ``AffRun.mk) (toExpr r.wid) (toExpr r.count)
  toTypeExpr := mkConst ``AffRun

instance : ToExpr AffCfg where
  toExpr c := mkApp4 (mkConst ``AffCfg.mk)
    (toExpr c.q) (toExpr c.dir) (toExpr c.left) (toExpr c.right)
  toTypeExpr := mkConst ``AffCfg

instance : ToExpr CompExit where
  toExpr e := mkApp4 (mkConst ``CompExit.mk)
    (toExpr e.wid') (toExpr e.q') (toExpr e.dir') (toExpr e.dt)
  toTypeExpr := mkConst ``CompExit

instance : ToExpr AffOp where
  toExpr
    | .steps n => mkApp (mkConst ``AffOp.steps) (toExpr n)
    | .cycle L K ds => mkApp3 (mkConst ``AffOp.cycle) (toExpr L) (toExpr K) (toExpr ds)
  toTypeExpr := mkConst ``AffOp

instance : ToExpr ReturnCert where
  toExpr c := mkApp3 (mkConst ``ReturnCert.mk)
    (toExpr c.vocab) (toExpr c.exits) (toExpr c.ops)
  toTypeExpr := mkConst ``ReturnCert

/-! ## Balanced `BTree` Construction -/

private def buildBTree {α : Type} : ℕ → List α → BTree α × List α
  | 0, xs => (.empty, xs)
  | 1, [] => (.empty, [])
  | 1, x :: xs => (.leaf x, xs)
  | n + 2, xs =>
    let half := (n + 2) / 2
    let (l, xs₁) := buildBTree half xs
    let (r, xs₂) := buildBTree (n + 2 - half) xs₁
    (.node l r, xs₂)

/-- Construct a balanced `BTree α` from `xs` in `O(N)` time. -/
def btreeOfList {α : Type} (xs : List α) : BTree α :=
  (buildBTree xs.length xs).1

/-! ## Pure-Lean Symbolic Return Certificate Discovery Oracle -/

private structure OracleEnv where
  nextWid : ℕ
  vocabList : NatTrie (List ℕ)
  vocabTree : NatTrie (BTree ℕ)
  wordMap : Std.HashMap (List ℕ) ℕ
  exits : NatTrie CompExit

private def internWord (w : List ℕ) (env : OracleEnv) : ℕ × OracleEnv :=
  match env.wordMap[w]? with
  | some id => (id, env)
  | none =>
    let id := env.nextWid
    (id, {
      env with
      nextWid := id + 1
      vocabList := env.vocabList.insert id w
      vocabTree := env.vocabTree.insert id (btreeOfList w)
      wordMap := env.wordMap.insert w id
    })

private def getOrComputeExit (numStates : ℕ)
    (baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ))
    (wid q : ℕ) (dir : Bool) (env : OracleEnv) : Option (CompExit × OracleEnv) :=
  let key := compKey numStates wid q dir
  match env.exits.find? key with
  | some ex => some (ex, env)
  | none =>
    match env.vocabList.find? wid with
    | none => none
    | some u =>
      match runCompositeExit baseExit u q dir with
      | none => none
      | some (v, q', dir', dt) =>
        let (wid', env₁) := internWord v env
        let ex : CompExit := ⟨wid', q', dir', dt⟩
        some (ex, { env₁ with exits := env₁.exits.insert key ex })

private structure SymExpr where
  vid : Option ℕ
  offP : ℕ
  offN : ℕ
  deriving DecidableEq

private def symNorm (vid : Option ℕ) (p n : ℕ) : SymExpr :=
  if n ≤ p then ⟨vid, p - n, 0⟩ else ⟨vid, 0, n - p⟩

private def symConst? (e : SymExpr) : Option ℕ :=
  if e.vid.isNone && e.offN == 0 then some e.offP else none

private def symAdd? (e₁ e₂ : SymExpr) : Option SymExpr :=
  match e₁.vid, e₂.vid with
  | none, none => some (symNorm none (e₁.offP + e₂.offP) (e₁.offN + e₂.offN))
  | some v, none => some (symNorm (some v) (e₁.offP + e₂.offP) (e₁.offN + e₂.offN))
  | none, some v => some (symNorm (some v) (e₁.offP + e₂.offP) (e₁.offN + e₂.offN))
  | some _, some _ => none

private def symSub? (e₁ e₂ : SymExpr) : Option SymExpr :=
  if e₁.vid == e₂.vid then
    some (symNorm none (e₁.offP + e₂.offN) (e₁.offN + e₂.offP))
  else if e₂.vid.isNone then
    some (symNorm e₁.vid (e₁.offP + e₂.offN) (e₁.offN + e₂.offP))
  else none

private def symReqGe (e : SymExpr) (k : ℕ) (mins : NatTrie ℕ) : Option (NatTrie ℕ) :=
  match e.vid with
  | none => if k + e.offN ≤ e.offP then some mins else none
  | some idx =>
    let req := if e.offP ≤ k + e.offN then (k + e.offN) - e.offP else 0
    let cur := match mins.find? idx with | some m => m | none => 2
    if req ≤ cur then some mins else some (mins.insert idx req)

private def buildSymStack :
    List AffRun → ℕ → NatTrie ℕ → List (ℕ × SymExpr) × ℕ × NatTrie ℕ
  | [], nxt, mins => ([], nxt, mins)
  | r :: rs, nxt, mins =>
    if r.count.isOne then
      let (out, nxt', mins') := buildSymStack rs nxt mins
      ((r.wid, ⟨none, 1, 0⟩) :: out, nxt', mins')
    else
      let vid := nxt
      let mins₁ := mins.insert vid 2
      let (out, nxt', mins') := buildSymStack rs (nxt + 1) mins₁
      ((r.wid, ⟨some vid, 0, 0⟩) :: out, nxt', mins')

private def simCycleProbe (numStates : ℕ)
    (baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)) :
    ℕ → ℕ → Bool → List (ℕ × SymExpr) → List (ℕ × SymExpr) → NatTrie ℕ → OracleEnv →
    Option (ℕ × Bool × List (ℕ × SymExpr) × List (ℕ × SymExpr) × NatTrie ℕ × OracleEnv)
  | 0, q, dir, l, r, mins, env => some (q, dir, l, r, mins, env)
  | n + 1, q, dir, l, r, mins, env =>
    let src := if dir then r else l
    let (wid, cExpr) : ℕ × SymExpr := match src with | [] => (0, ⟨none, 1, 0⟩) | top :: _ => top
    match getOrComputeExit numStates baseExit wid q dir env with
    | none => none
    | some (ex, env₁) =>
      let same := ex.q' == q && ex.dir' == dir
      if src.isEmpty && same then none
      else
        let count : SymExpr := if same then cExpr else ⟨none, 1, 0⟩
        match symConst? count with
        | none => none
        | some cntVal =>
          let popRes? : Option (List (ℕ × SymExpr) × NatTrie ℕ) :=
            match src with
            | [] => some ([], mins)
            | (tw, tc) :: rest =>
              match symSub? tc count with
              | none => none
              | some rem =>
                if rem == (⟨none, 0, 0⟩ : SymExpr) then some (rest, mins)
                else (symReqGe rem 1 mins).map fun m' ↦ ((tw, rem) :: rest, m')
          match popRes? with
          | none => none
          | some (src', mins₁) =>
            let l₁ := if dir then l else src'
            let r₁ := if dir then src' else r
            let pushSide (dst : List (ℕ × SymExpr)) (m : NatTrie ℕ) :
                Option (List (ℕ × SymExpr) × NatTrie ℕ) :=
              if cntVal == 0 then some (dst, m)
              else if dst.isEmpty && ex.wid' == 0 then some ([], m)
              else
                match symReqGe count 1 m with
                | none => none
                | some m₁ =>
                  match dst with
                  | [] => some ([(ex.wid', count)], m₁)
                  | (dw, dc) :: drest =>
                    if dw == ex.wid' then
                      (symAdd? dc count).map fun merged ↦ ((dw, merged) :: drest, m₁)
                    else some ((ex.wid', count) :: dst, m₁)
            let dstRes? :=
              if ex.dir' then (pushSide l₁ mins₁).map fun (l₂, m₂) ↦ (l₂, r₁, m₂)
              else (pushSide r₁ mins₁).map fun (r₂, m₂) ↦ (l₁, r₂, m₂)
            match dstRes? with
            | none => none
            | some (l₂, r₂, mins₂) =>
              simCycleProbe numStates baseExit n ex.q' ex.dir' l₂ r₂ mins₂ env₁

private def extractCycleDeltas (mins : NatTrie ℕ) :
    List AffRun → List (ℕ × SymExpr) → List (ℕ × SymExpr) →
    Option (List (ℕ × ℕ) × List AffNat)
  | [], [], [] => some ([], [])
  | r :: rs, (ow, oe) :: os, (nw, ne) :: ns =>
    if ow != nw || oe.vid != ne.vid then none
    else
      let p := ne.offP + oe.offN
      let n := ne.offN + oe.offP
      let (dp, dn) := if n ≤ p then (p - n, 0) else (0, n - p)
      if oe.vid.isNone && (dp != 0 || dn != 0) then none
      else if 2 ≤ dn then none
      else
        let minBound := match oe.vid with
          | none => 1
          | some vid => match mins.find? vid with | some m => m | none => 2
        if !r.count.geConst minBound then none
        else
          match extractCycleDeltas mins rs os ns with
          | none => none
          | some (ds, choices) =>
            let choices' :=
              if dn == 1 then
                match r.count.sub? ⟨0, minBound - 1⟩ with
                | some ch => ch :: choices
                | none => choices
              else choices
            some ((dp, dn) :: ds, choices')
  | _, _, _ => none

private def minChoiceAux (cur : AffNat) : List AffNat → AffNat
  | [] => cur
  | y :: rest => minChoiceAux (if AffNat.lexLt cur y then cur else y) rest

private def minChoice : List AffNat → Option AffNat
  | [] => none
  | x :: rest => some (minChoiceAux x rest)

private def tryDiscoverCycle (numStates : ℕ)
    (baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ))
    (oldCfg : AffCfg) (L : ℕ) (env : OracleEnv) :
    Option (AffNat × List (ℕ × ℕ) × OracleEnv) :=
  let (lOrig, nxt₁, mins₁) := buildSymStack oldCfg.left 0 .leaf
  let (rOrig, _, mins₂) := buildSymStack oldCfg.right nxt₁ mins₁
  match simCycleProbe numStates baseExit L oldCfg.q oldCfg.dir lOrig rOrig mins₂ env with
  | none => none
  | some (q', dir', lNew, rNew, minsFinal, env₁) =>
    if q' != oldCfg.q || dir' != oldCfg.dir then none
    else
      match extractCycleDeltas minsFinal (oldCfg.left ++ oldCfg.right)
          (lOrig ++ rOrig) (lNew ++ rNew) with
      | none => none
      | some (deltas, choices) =>
        match minChoice choices with
        | none => none
        | some K =>
          let allGe := choices.all fun ch ↦ (ch.sub? K).isSome
          if K.geConst 1 && allGe then some (K, deltas, env₁)
          else none

private def shapeKey (c : AffCfg) : List ℕ :=
  let encSide (s : List AffRun) : List ℕ :=
    s.foldr (fun r acc ↦ (r.wid * 2 + (if r.count.isOne then 1 else 0) + 1) :: acc) []
  (c.q * 2 + (if c.dir then 1 else 0)) :: (encSide c.left ++ (0 :: encSide c.right))

private def addStepOp (ops : List AffOp) : List AffOp :=
  match ops with
  | .steps n :: rest => .steps (n + 1) :: rest
  | _ => .steps 1 :: ops

/-- Discover a verified symbolic `ReturnCert` (and final `AffCfg`) driving `initCfg` for exactly
`target` symbolic steps over a machine with `numStates` states and base-word exit function
`baseExit`. Automatically interns `[0]` at `wid = 0` followed by `seedWords`. -/
partial def discoverReturnCert
    (numStates : ℕ)
    (baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ))
    (seedWords : List (List ℕ))
    (initCfg : AffCfg)
    (target : AffNat)
    (maxLoops : ℕ := 200000) : Option (ReturnCert × AffCfg) := Id.run do
  let mut env : OracleEnv := {
    nextWid := 0
    vocabList := .leaf
    vocabTree := .leaf
    wordMap := {}
    exits := .leaf
  }
  for w in ([0] :: seedWords) do
    let (_, env') := internWord w env
    env := env'
  let mut loops : ℕ := 0
  let mut curSteps : AffNat := ⟨0, 0⟩
  let mut c : AffCfg := initCfg
  let mut past : Std.HashMap (List ℕ) (AffCfg × AffNat × ℕ × List AffOp) := {}
  let mut failed : Std.HashSet (List ℕ) := {}
  let mut revOps : List AffOp := []
  while curSteps != target && loops < maxLoops do
    let sk := shapeKey c
    if !failed.contains sk then
      if let some (oldCfg, oldSteps, oldLoops, oldRevOps) := past[sk]? then
        let L := loops - oldLoops
        match tryDiscoverCycle numStates baseExit oldCfg L env with
        | some (K, deltas, env₁) =>
          env := env₁
          if let some (dtCyc, afterCfg) := verifyCycle numStates env.exits L K deltas oldCfg then
            curSteps := oldSteps.add dtCyc
            c := afterCfg
            loops := oldLoops + 1
            revOps := .cycle L K deltas :: oldRevOps
            past := {}
            continue
          else
            failed := failed.insert sk
        | none =>
          failed := failed.insert sk
    past := past.insert sk (c, curSteps, loops, revOps)
    let src := if c.dir then c.right else c.left
    let wid := match src with | [] => 0 | top :: _ => top.wid
    let some (_, env₁) := getOrComputeExit numStates baseExit wid c.q c.dir env | return none
    env := env₁
    let rem? := target.sub? curSteps
    let some (dt, c') := stepAffOnce numStates env.exits rem? c.q c.dir c.left c.right
      | return none
    curSteps := curSteps.add dt
    c := c'
    loops := loops + 1
    revOps := addStepOp revOps
  if curSteps == target then
    return some (⟨env.vocabTree, env.exits, btreeOfList revOps.reverse⟩, c)
  else
    return none

/-! ## Sliced Kernel Proof Drivers (`mkAuxTheorem`) -/

private def mkBoolEqTrue (lhs : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) lhs (mkConst ``Bool.true)

private def boolReflTrue : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- Elaborate a chunked kernel proof of `EntryReaches stepFn expDt startCfg expCfg`, running at
most `chunkSize` RLE steps per `mkAuxTheorem` slice so kernel memory stays bounded, and casting
endpoint expressions in the kernel via `EntryReaches.cast_ends`. -/
def proveEntryPhase
    (stepFn : ℕ → Bool → List Run → List Run → Option (ℕ × EntryCfg))
    (stepFnE : Expr)
    (totalLoops chunkSize expDt : ℕ)
    (startCfg expCfg : EntryCfg)
    (startCfgE? : Option Expr := none)
    (expCfgE? : Option Expr := none) : MetaM Expr := do
  let mut remLoops := totalLoops
  let mut cur := startCfg
  let startE := toExpr startCfg
  let mut proofExpr := mkApp2 (mkConst ``EntryReaches.refl) stepFnE startE
  let mut sumExpr := toExpr (0 : ℕ)
  let mut curExpr := startE
  let mut totDt : ℕ := 0
  while remLoops > 0 do
    let fuel := Nat.min remLoops chunkSize
    let some (dt, nxt) := runExact stepFn fuel 0 cur
      | throwError "proveEntryPhase: simulation failed with remaining loops {remLoops}"
    let fuelE := toExpr fuel
    let dtE := toExpr dt
    let nxtE := toExpr nxt
    let lhs := mkApp5 (mkConst ``checkRunExact) stepFnE fuelE dtE curExpr nxtE
    let auxThm ← mkAuxTheorem (mkBoolEqTrue lhs) boolReflTrue
    let stepPrf := mkApp6 (mkConst ``EntryReaches.chunk) stepFnE fuelE dtE curExpr nxtE auxThm
    proofExpr := mkApp8 (mkConst ``EntryReaches.trans)
      stepFnE sumExpr dtE startE curExpr nxtE proofExpr stepPrf
    sumExpr := mkApp2 (mkConst ``Nat.add) sumExpr dtE
    curExpr := nxtE
    cur := nxt
    totDt := totDt + dt
    remLoops := remLoops - fuel
  if totDt != expDt then
    throwError "proveEntryPhase: step count mismatch: got {totDt}, expected {expDt}"
  if cur != expCfg then
    throwError "proveEntryPhase: final configuration mismatch"
  let expDtE := toExpr expDt
  let tgtStartE := startCfgE?.getD startE
  let tgtExpE := expCfgE?.getD curExpr
  let endsLhs := mkApp6 (mkConst ``checkEntryEnds)
    sumExpr expDtE startE tgtStartE curExpr tgtExpE
  let endsPrf ← mkAuxTheorem (mkBoolEqTrue endsLhs) boolReflTrue
  return mkAppN (mkConst ``EntryReaches.cast_ends)
    #[stepFnE, sumExpr, expDtE, startE, tgtStartE, curExpr, tgtExpE, proofExpr, endsPrf]

/-- Elaborate a depth-split `mkAuxTheorem` proof of `NatTrie.checkAll p 0 1 t = true`. -/
def proveCheckAll {α : Type} [ToExpr α]
    (pE : Expr) (t : NatTrie α) (splitDepth : ℕ := 3) : MetaM Expr := do
  let αTy := toTypeExpr α
  let optTy := mkApp (mkConst ``Option [Level.zero]) αTy
  let rec go (depth kp bm : ℕ) (sub : NatTrie α) : MetaM Expr := do
    match depth, sub with
    | d + 1, .node val? l r =>
      let valE : Expr := toExpr val?
      let lE := toExpr l
      let rE := toExpr r
      let kpE := toExpr kp
      let bmE := toExpr bm
      let selfPrf ← match val? with
        | none => pure boolReflTrue
        | some v =>
          let selfLhs := mkApp2 pE kpE (toExpr v)
          mkAuxTheorem (mkBoolEqTrue selfLhs) boolReflTrue
      let lPrf ← go d kp (bm * 2) l
      let rPrf ← go d (kp + bm) (bm * 2) r
      return mkAppN (mkConst ``checkAll_node)
        #[αTy, pE, kpE, bmE, valE, lE, rE, selfPrf, lPrf, rPrf]
    | _, _ =>
      let subE := toExpr sub
      let lhs := mkApp5 (mkConst ``NatTrie.checkAll) αTy pE (toExpr kp) (toExpr bm) subE
      let _ := optTy
      mkAuxTheorem (mkBoolEqTrue lhs) boolReflTrue
  go splitDepth 0 1 t

/-- Elaborate a depth-split `mkAuxTheorem` proof of
`AffReplayReaches numStates exits target ops ⟨0, 0⟩ initCfg target finalCfg`. -/
def proveAffReplay
    (numStates : ℕ)
    (exits : NatTrie CompExit) (exitsE : Expr)
    (target : AffNat) (targetE : Expr)
    (ops : BTree AffOp)
    (initCfg expFinalCfg : AffCfg)
    (splitDepth : ℕ := 3) : MetaM Expr := do
  let numStatesE := toExpr numStates
  let rec go (depth : ℕ) (sub : BTree AffOp) (acc : AffNat) (accE : Expr)
      (c : AffCfg) (cE : Expr) : MetaM (AffNat × AffCfg × Expr × Expr × Expr) := do
    match depth, sub with
    | d + 1, .node l r =>
      let (a₁, c₁, a₁E, c₁E, prfL) ← go d l acc accE c cE
      let (a₂, c₂, a₂E, c₂E, prfR) ← go d r a₁ a₁E c₁ c₁E
      let lE := toExpr l
      let rE := toExpr r
      let prf := mkAppN (mkConst ``AffReplayReaches.node)
        #[numStatesE, exitsE, targetE, lE, rE, accE, a₁E, a₂E, cE, c₁E, c₂E, prfL, prfR]
      return (a₂, c₂, a₂E, c₂E, prf)
    | _, _ =>
      let some (acc', c') := replayAffTree numStates exits target sub acc c
        | throwError "proveAffReplay: slice replay failed"
      let subE := toExpr sub
      let acc'E := toExpr acc'
      let c'E := toExpr c'
      let lhs := mkApp8 (mkConst ``checkReplaySlice)
        numStatesE exitsE targetE subE accE cE acc'E c'E
      let auxThm ← mkAuxTheorem (mkBoolEqTrue lhs) boolReflTrue
      let prf := mkApp9 (mkConst ``AffReplayReaches.slice)
        numStatesE exitsE targetE subE accE acc'E cE c'E auxThm
      return (acc', c', acc'E, c'E, prf)
  let zeroAff : AffNat := ⟨0, 0⟩
  let (tot, finCfg, _, _, prf) ←
    go splitDepth ops zeroAff (toExpr zeroAff) initCfg (toExpr initCfg)
  if tot != target then
    throwError "proveAffReplay: total affine step mismatch"
  if finCfg != expFinalCfg then
    throwError "proveAffReplay: final symbolic configuration mismatch"
  return prf

end BusyBeaver.ElabRLE

end
