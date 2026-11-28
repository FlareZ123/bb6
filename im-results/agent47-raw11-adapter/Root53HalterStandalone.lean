import Lean

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Root53HalterStandalone
structure Move where
  write : Bool
  right : Bool
  next : Fin 6
  deriving DecidableEq, Repr

def table (q : Fin 6) (b : Bool) : Option Move :=
  match q.val,b with
  | 0,false => some ⟨true,true,1⟩
  | 0,true  => some ⟨true,true,3⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true  => some ⟨true,true,4⟩
  | 2,false => some ⟨false,false,0⟩
  | 2,true  => some ⟨false,true,5⟩
  | 3,false => some ⟨true,false,0⟩
  | 3,true  => some ⟨true,false,3⟩
  | 4,false => none
  | 4,true  => some ⟨false,false,2⟩
  | 5,false => some ⟨false,false,0⟩
  | 5,true  => some ⟨false,true,1⟩
  | _,_ => none

structure Cfg where
  state : Fin 6
  head : Int
  ones : List Int
  deriving DecidableEq, Repr

def blank : Cfg := ⟨0,0,[]⟩
def read (c : Cfg) : Bool := c.ones.contains c.head
def step (c : Cfg) : Option Cfg := do
  let mv ← table c.state (read c)
  let xs := c.ones.filter (fun x => x != c.head)
  let ys := if mv.write then c.head :: xs else xs
  return ⟨mv.next, c.head + if mv.right then 1 else -1, ys⟩
def run : Nat → Cfg → Option Cfg
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

def c202 : Cfg := (run 202 blank).getD blank

theorem run202_some : run 202 blank = some c202 := by decide +kernel
theorem c202_state : c202.state.val = 4 := by decide +kernel
theorem c202_head : c202.head = 16 := by decide +kernel
theorem c202_read : read c202 = false := by decide +kernel
theorem halt_next : step c202 = none := by decide +kernel
theorem run203_none : run 203 blank = none := by decide +kernel

def root (q : Fin 6) (b : Bool) : Option (Option Move) :=
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true  => some (some ⟨true,false,3⟩)
  | _,_ => none

theorem compatible_root :
    ∀ q b v, root q b = some v → table q b = v := by decide +kernel

/-- One six-state full machine compatible with the five-hole Root53 cylinder
    executes 202 ordinary moves and halts at its next (203rd) query. -/
theorem attained_203 :
    (∀ q b v, root q b = some v → table q b = v) ∧
    (∃ c : Cfg, run 202 blank = some c ∧ step c = none) :=
  ⟨compatible_root, ⟨c202, run202_some, halt_next⟩⟩

#print axioms attained_203
end Root53HalterStandalone
