module
public import BusyBeaver.Calculi.HaltShared

@[expose] public section

/-!
# Machine-specific primitive-cost model directly importing the upstream
# source's original `SymRunEngine.stepPure` state transition.

The definition uses the same case split as the pinned source
google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a.
The costs are read from F424/F412's exact `execute n` step lemmas. This
typechecks against real source datatypes and uses its literal stepPure for
all state changes; the residual *semantic* gate is a source-connected proof
of `ReachesIn (costPure s)` for each original-machine transition.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 0

open BusyBeaver.SymRunEngine

namespace BB6.Agent11.SourceCost

abbrev SymState := SymMode × List SymTok × List SymTok

/-- Choose F424's primitive rule cost when `is424` is true; F412 otherwise. -/
def fcost (is424 : Bool) (v424 v412 : Nat) : Nat :=
  if is424 then v424 else v412

def costElemBB (is424 : Bool) : List SymTok → Nat
  | [] => 1
  | .item .zero :: _ => 1
  | .item (.run 0) :: _ => fcost is424 8 6
  | .item (.run 1) :: _ => 3
  | .item (.run 2) :: _ => 5
  | .item (.run 3) :: _ => 9
  | .item (.run (_ + 4)) :: _ => 9
  | .repB1 _ :: _ => 0
  | .rep2 _ :: _ => 0
  | .rep12 _ :: _ => 0

def costElemDL (is424 : Bool) (L R : List SymTok) : Nat :=
  match L, R with
  | .item (.run 0) :: _, _ => 1
  | .item (.run 1) :: _, _ => 3
  | .item (.run 2) :: _, .item (.run d) :: _ => 3 * d + fcost is424 22 20
  | _, _ => 0

def costElemCBRun0 (is424 : Bool) : List SymTok → Nat
  | [] => 3
  | .item .zero :: _ => 3
  | .item (.run 0) :: _ => 6
  | .item (.run (d+1)) :: _ => 3 * d + fcost is424 21 19
  | .repB1 _ :: _ => 0
  | .rep2 _ :: _ => 0
  | .rep12 _ :: _ => 0

def costElemCB (is424 : Bool) : List SymTok → Nat
  | [] => 2
  | .item .zero :: _ => 2
  | .item (.run 0) :: R => costElemCBRun0 is424 R
  | .item (.run 1) :: _ => 3
  | .item (.run 2) :: _ => 5
  | .item (.run (_ + 3)) :: _ => 5
  | .repB1 _ :: _ => 0
  | .rep2 _ :: _ => 0
  | .rep12 _ :: _ => 0

/-- Exact primitive charge for `stepPureBB L R`'s source witness. -/
def costPureBB (is424 : Bool) : List SymTok → List SymTok → Nat
  | [], _ => costElemBB is424 []
  | .item x :: L1, _ => costElemBB is424 (.item x :: L1)
  | .repB1 k :: _, _ => fcost is424 11 9 * k
  | .rep2 p :: L1, R =>
      match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some _ => fcost is424 14 12 * p
      | none => costElemBB is424 (peelPureTok (.rep2 p) L1)
  | .rep12 m :: L1, R =>
      match stripPrefixSym [.item (.run 0), .item (.run 1)] R with
      | some _ => fcost is424 25 21 * m
      | none => costElemBB is424 (peelPureTok (.rep12 m) L1)

/-- Exact primitive charge for `stepPureDL L R`. -/
def costPureDL (is424 : Bool) : List SymTok → List SymTok → Nat
  | [], _ => 0
  | t :: L1, R => costElemDL is424 (peelPureTok t L1) R

/-- Exact primitive charge for `stepPureCB L R`. -/
def costPureCB (is424 : Bool) (L : List SymTok) : List SymTok → Nat
  | [] => costElemCB is424 []
  | .item .zero :: R1 => costElemCB is424 (.item .zero :: R1)
  | .item (.run 0) :: R1 => costElemCBRun0 is424 R1
  | .item (.run 1) :: R1 => costElemCB is424 (.item (.run 1) :: R1)
  | .item (.run 2) :: R1 => costElemCB is424 (.item (.run 2) :: R1)
  | .item (.run (_ + 3)) :: _ => 5
  | .repB1 k :: _ =>
      if (stripPrefixSym [.item (.run 0), .item (.run 0), .item (.run 1)] L).isSome ||
         (stripPrefixSym [.item (.run 0)] L).isSome
      then fcost is424 21 19 * k else 0
  | .rep2 p :: _ =>
      if (stripPrefixSym [.item (.run 0), .item (.run 1), .item (.run 0), .item (.run 1)] L).isSome ||
         (stripPrefixSym [.item (.run 0)] L).isSome
      then fcost is424 24 22 * p else 0
  | .rep12 m :: _ =>
      if (stripPrefixSym [.item (.run 0)] L).isSome
      then fcost is424 45 41 * m else 0

def costPure (is424 : Bool) : SymState → Nat
  | (.BB, L, R) => costPureBB is424 L R
  | (.DL, L, R) => costPureDL is424 L R
  | (.CB, L, R) => costPureCB is424 L R
  | (.HALT, _, _) => 0

/-- Each iteration advances the **real upstream stepPure** function. -/
def costIter (is424 : Bool) : Nat → SymState → Nat
  | 0, _ => 0
  | n+1, s => costPure is424 s + costIter is424 n (stepPure s)

example : costPure true (.BB, [.item (.run 0)], []) = 8 := rfl
example : costPure false (.BB, [.item (.run 0)], []) = 6 := rfl
example : costPure true (.CB, [], [.item (.run 0), .item (.run 5)]) = 33 := rfl
example : costPure false (.CB, [], [.item (.run 0), .item (.run 5)]) = 31 := rfl
example : costPure true (.DL, [.item (.run 2)], [.item (.run 5)]) = 37 := rfl
example : costPure false (.DL, [.item (.run 2)], [.item (.run 5)]) = 35 := rfl

/-- Small exact-block samples can be checked against upstream
    `stepPure` itself, without the independent JavaScript translation. -/
example : costIter true 46 (stateA0 4 46 []) = 32 * 3 + 314 := by decide
example : costIter false 46 (stateA0 4 46 []) = 28 * 3 + 284 := by decide

end BB6.Agent11.SourceCost

end
