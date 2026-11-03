import Lean

set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

namespace BoundWitness

/-- Literal six-state cryptid table in an independent finite zipper with implicit blanks. -/
structure Cfg where
  l : List Bool
  h : Bool
  r : List Bool
  st : Nat
  deriving DecidableEq, Repr

def goR (c : Cfg) (w : Bool) (n : Nat) : Cfg :=
  match c.r with
  | [] => ⟨w :: c.l, false, [], n⟩
  | x :: xs => ⟨w :: c.l, x, xs, n⟩

def goL (c : Cfg) (w : Bool) (n : Nat) : Cfg :=
  match c.l with
  | [] => ⟨[], false, w :: c.r, n⟩
  | x :: xs => ⟨xs, x, w :: c.r, n⟩

def step (c : Cfg) : Cfg :=
  match c.st, c.h with
  | 0, false => goR c true 1
  | 0, true => goR c false 4
  | 1, false => goL c true 2
  | 1, true => goR c false 0
  | 2, false => goL c true 0
  | 2, true => goL c true 3
  | 3, false => goL c true 2
  | 3, true => goL c true 5
  | 4, false => goL c false 2
  | 4, true => goL c false 1
  | 5, false => goL c true 4
  | 5, true => ⟨c.l,c.h,c.r,6⟩
  | _, _ => c

def run : Nat → Cfg → Cfg
  | 0, c => c
  | n + 1, c => run n (step c)

def init (a : Nat) (suffix : List Bool) : Cfg :=
  ⟨[], false, List.replicate a true ++ suffix, 5⟩

def Linput (a q b : Nat) : Cfg :=
  init a (List.flatten (List.replicate q [false,true]) ++ List.replicate b true)

def isPhysicalF0 (c : Cfg) : Bool :=
  c.st == 5 && !c.h && c.l.all (· == false)

def noPositiveReturn : Nat → Cfg → Bool
  | 0, _ => true
  | n + 1, c =>
    let d := step c
    !isPhysicalF0 d && noPositiveReturn n d

/-- No earlier positive-time F/0 section, including passes with nonblank left tape. -/
theorem no_earlier_return :
    noPositiveReturn 156 (Linput 7 1 1) = true := by decide

def escaped (c : Cfg) : Bool :=
  let w := c.r.reverse.dropWhile (· == false) |>.reverse
  let a := w.takeWhile (· == true)
  let rest := w.drop a.length
  let rec tokenPairs : List Bool → List Bool
    | false :: true :: xs => tokenPairs xs
    | xs => xs
  let rem := tokenPairs rest
  !(rem.all (· == true))

/-- First physically blank-left F/0 return leaves 1⁺(01)*1* after exactly 157 transitions. -/
theorem counterexample_one_return :
    (run 157 (Linput 7 1 1)).st = 5 ∧
    (run 157 (Linput 7 1 1)).h = false ∧
    (run 157 (Linput 7 1 1)).l.all (· == false) = true ∧
    escaped (run 157 (Linput 7 1 1)) = true := by decide

#print axioms no_earlier_return
#print axioms counterexample_one_return

end BoundWitness
