import Lean

open Lean

/-!
Self-contained finite replay of the original TM2 transition table on two
m=0, n=32*k+14 source configurations. The transition table is copied
verbatim from ChampionRootBridge.lean; the S1 tape encoding is copied
from S1Encoder.lean. This is a sample computation, not a generic proof.
-/

def d0 : List Bool := [false,false,true]
def d1 : List Bool := [true,true,true]
def lh : List Bool := [true,true,false,true,true,true]

def markerWord : Nat → List Bool
  | 0 => [false,true]
  | 1 => [true,false,true]
  | _ => [true,true,false,true]

def d1pow (n : Nat) : List Bool := List.replicate (3*n) true

def binaryCounterFuel : Nat → Nat → List Bool
  | 0, _ => []
  | fuel+1, p =>
      if p ≤ 1 then []
      else if p % 2 = 0 then d0 ++ binaryCounterFuel fuel (p/2)
      else d1 ++ binaryCounterFuel fuel (p/2)

def binDec (L n : Nat) : List Bool :=
  binaryCounterFuel L (2^(L+1)-1-n)

def s1LeftFacing (L n m a z : Nat) : List Bool :=
  binDec a z ++ markerWord m ++ d0 ++ binDec L n ++ lh

def s0RightFacing (b : Nat) : List Bool :=
  [false,true,true,true,false,false] ++ d1pow (b+1)

def leftOnes (xs : List Bool) : List Int :=
  (List.range xs.length).filterMap fun i =>
    if xs.getD i false then some (-(Int.ofNat i)) else none

def rightOnes (xs : List Bool) : List Int :=
  (List.range xs.length).filterMap fun i =>
    if xs.getD i false then some (Int.ofNat (i+1)) else none

structure FConfig where
  state : Nat
  head : Int
  ones : List Int
  deriving DecidableEq, Repr

def writeCell (xs : List Int) (x : Int) (v : Bool) : List Int :=
  if v then (if x ∈ xs then xs else x :: xs) else xs.filter (fun y => y != x)

/-- (write, displacement, next-state), with displacement -1 or +1. -/
def tm2Transition (q : Nat) (bit : Bool) : Option (Bool × Int × Nat) :=
  match q, bit with
  | 0, false => some (true, 1, 1)
  | 0, true => none
  | 1, false => some (true, -1, 2)
  | 1, true => some (false, 1, 5)
  | 2, false => some (true, 1, 4)
  | 2, true => some (false, -1, 3)
  | 3, false => some (false, -1, 2)
  | 3, true => some (true, 1, 1)
  | 4, false => some (true, 1, 0)
  | 4, true => some (true, 1, 4)
  | 5, false => some (true, 1, 4)
  | 5, true => some (false, 1, 3)
  | _, _ => none

def tm2Step (c : FConfig) : Option FConfig := do
  let (w, dir, q') ← tm2Transition c.state (c.head ∈ c.ones)
  return { state := q', head := c.head + dir, ones := writeCell c.ones c.head w }

def runN : Nat → FConfig → Option FConfig
  | 0, c => some c
  | n+1, c => (tm2Step c).bind (runN n)

def runTrace : Nat → FConfig → List FConfig
  | 0, c => [c]
  | n+1, c => c :: (match tm2Step c with
      | none => []
      | some d => runTrace n d)

def startConfig (L n m a b : Nat) : FConfig :=
  { state := 3, head := 0,
    ones := leftOnes (s1LeftFacing L n m a 0) ++ rightOnes (s0RightFacing b) }

def targetQ4Left (L n a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ binDec L (n-1) ++ lh

def leftMatches (c : FConfig) (xs : List Bool) : Bool :=
  (List.range xs.length).all fun i =>
    (decide ((c.head - Int.ofNat i) ∈ c.ones)) == xs.getD i false

def q4ResultOk (N : Nat) (c : FConfig) (target : List Bool) : Bool :=
  match runN N c with
  | none => false
  | some d => decide (d.state = 4 ∧ d.head = 0) && leftMatches d target

def traceHeadsOk (N : Nat) (c : FConfig) (lo hi : Int) : Bool :=
  (runTrace N c).all fun d => decide (lo ≤ d.head ∧ d.head ≤ hi)

theorem sample14_a1_b1 :
    q4ResultOk 48 (startConfig 5 14 0 1 1) (targetQ4Left 5 14 1) = true := by
  decide

theorem sample46_a2_b0 :
    q4ResultOk 60 (startConfig 6 46 0 2 0) (targetQ4Left 6 46 2) = true := by
  decide

theorem sample14_head_bound :
    traceHeadsOk 48 (startConfig 5 14 0 1 1) (-12) 1 = true := by
  decide

theorem sample46_head_bound :
    traceHeadsOk 60 (startConfig 6 46 0 2 0) (-15) 1 = true := by
  decide

#print axioms sample14_a1_b1
#print axioms sample46_a2_b0
#print axioms sample14_head_bound
#print axioms sample46_head_bound
