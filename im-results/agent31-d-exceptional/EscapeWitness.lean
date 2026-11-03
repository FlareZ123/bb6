import Lean.Elab.Tactic.Omega

set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace BB6.Agent31Escape

structure Cfg where
  left : List Bool
  read : Bool
  right : List Bool
  state : Nat
  deriving DecidableEq, Repr

def rightMove (c : Cfg) (b : Bool) (st : Nat) : Cfg :=
  { left := b :: c.left, read := c.right.headD false,
    right := c.right.drop 1, state := st }

def leftMove (c : Cfg) (b : Bool) (st : Nat) : Cfg :=
  { left := c.left.drop 1, read := c.left.headD false,
    right := b :: c.right, state := st }

def next (c : Cfg) : Cfg :=
  match c.state, c.read with
  | 0, false => rightMove c true 1
  | 0, true => rightMove c false 4
  | 1, false => leftMove c true 2
  | 1, true => rightMove c false 0
  | 2, false => leftMove c true 0
  | 2, true => leftMove c true 3
  | 3, false => leftMove c true 2
  | 3, true => leftMove c true 5
  | 4, false => leftMove c false 2
  | 4, true => leftMove c false 1
  | 5, false => leftMove c true 4
  | 5, true => { c with state := 6 }
  | _, _ => c

def run : Nat → Cfg → Cfg
  | 0, c => c
  | n+1, c => run n (next c)

def pairs : Nat → List Bool
  | 0 => []
  | n+1 => [false,true] ++ pairs n

def i (n : Nat) (suffix : List Bool) : Cfg :=
  ⟨[], false, List.replicate n true ++ suffix, 5⟩

def input : Cfg := i 7 (pairs 3 ++ [true])

def mid : Cfg := i 13 ([false] ++ List.replicate 6 true ++
  [false] ++ List.replicate 6 true)

def output : Cfg := i 33 (pairs 2 ++ [false] ++ List.replicate 3 true ++
  [false] ++ List.replicate 6 true)

#eval (run 129 input).left.length
#eval (run 129 input).right.length
#eval (run 129 input).state
#eval (run 129 input).read
#eval (run 129 input).right == mid.right
#eval (run 313 (run 129 input)).left.length
#eval (run 313 (run 129 input)).right == output.right
#eval (run 313 (run 129 input)).state
#eval (run 313 (run 129 input)).read

end BB6.Agent31Escape

namespace BB6.Agent31Escape

theorem first_return_129 : run 129 input = mid := by decide

theorem second_return_313 : run 313 mid = output := by decide

theorem two_returns_442 : run 442 input = output := by
  change run (313 + 129) input = output
  -- This finite exact raw-step equality is independently checked in the kernel.
  decide

#print axioms first_return_129
#print axioms second_return_313
#print axioms two_returns_442

end BB6.Agent31Escape

namespace BB6.Agent31Escape

/-- Physically blank-left F/0, where explicit zero cells count as blank. -/
def physicalF0 (c : Cfg) : Bool :=
  c.state == 5 && !c.read && c.left.all (fun b => !b)

/-- Checks every strictly positive time up to the given number of raw transitions. -/
def allBeforeSafe : Nat → Cfg → Bool
  | 0, _ => true
  | n+1, c =>
      let s := next c
      !physicalF0 s && allBeforeSafe n s

theorem first_strict : allBeforeSafe 128 input = true := by decide
theorem second_strict : allBeforeSafe 312 mid = true := by decide

#print axioms first_strict
#print axioms second_strict

end BB6.Agent31Escape
