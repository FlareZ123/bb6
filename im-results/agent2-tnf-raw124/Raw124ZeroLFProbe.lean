import Raw124ZeroLFBlockGrowth

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw124ZeroLFProbe
open BB6Coverage BB6.Agent2Raw124ZeroLFBlockGrowth

def hard0 : PartialMachine := fromRows [
  some (some ⟨true,true,1⟩), some (some ⟨false,false,4⟩),
  some (some ⟨true,true,2⟩), some (some ⟨true,true,0⟩),
  some (some ⟨false,true,3⟩), some (some ⟨false,true,1⟩),
  some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
  none, some (some ⟨true,false,5⟩),
  some (some ⟨true,true,1⟩), some (some ⟨false,false,5⟩)
]

def hard1 : PartialMachine := fromRows [
  some (some ⟨true,true,1⟩), none,
  some (some ⟨true,true,2⟩), some (some ⟨true,true,5⟩),
  some (some ⟨false,true,3⟩), some (some ⟨false,true,1⟩),
  some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
  some (some ⟨false,false,0⟩), some (some ⟨true,false,5⟩),
  some (some ⟨true,true,1⟩), some (some ⟨false,false,5⟩)
]

def hard2 : PartialMachine := fromRows [
  some (some ⟨true,true,1⟩), none,
  some (some ⟨true,true,2⟩), some (some ⟨true,true,5⟩),
  some (some ⟨false,true,3⟩), some (some ⟨false,true,1⟩),
  some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
  some (some ⟨true,false,0⟩), some (some ⟨true,false,5⟩),
  some (some ⟨true,true,1⟩), some (some ⟨false,false,5⟩)
]

def hard3 : PartialMachine := fromRows [
  some (some ⟨true,true,1⟩), none,
  some (some ⟨true,true,2⟩), some (some ⟨true,true,0⟩),
  some (some ⟨false,true,3⟩), some (some ⟨false,false,4⟩),
  some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
  some (some ⟨false,true,1⟩), some (some ⟨true,false,5⟩),
  some (some ⟨true,true,1⟩), some (some ⟨false,false,5⟩)
]

def hard4 : PartialMachine := fromRows [
  some (some ⟨true,true,1⟩), some (some ⟨false,true,3⟩),
  some (some ⟨true,true,2⟩), none,
  some (some ⟨false,true,3⟩), some (some ⟨true,false,0⟩),
  some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
  some (some ⟨true,true,1⟩), some (some ⟨true,false,5⟩),
  some (some ⟨true,true,1⟩), some (some ⟨false,false,5⟩)
]

end BB6.Agent2Raw124ZeroLFProbe

/-- Diagnostic only: a true Boolean is a candidate transfer, not a theorem until
the corresponding Certificate.never adapter is exported and source-checked. -/
#eval ("hard0", BB6.Agent2Raw124ZeroLFBlockGrowth.c1539.check BB6.Agent2Raw124ZeroLFProbe.hard0,
               BB6.Agent2Raw124ZeroLFBlockGrowth.c1547.check BB6.Agent2Raw124ZeroLFProbe.hard0)
#eval ("hard1", BB6.Agent2Raw124ZeroLFBlockGrowth.c1539.check BB6.Agent2Raw124ZeroLFProbe.hard1,
               BB6.Agent2Raw124ZeroLFBlockGrowth.c1547.check BB6.Agent2Raw124ZeroLFProbe.hard1)
#eval ("hard2", BB6.Agent2Raw124ZeroLFBlockGrowth.c1539.check BB6.Agent2Raw124ZeroLFProbe.hard2,
               BB6.Agent2Raw124ZeroLFBlockGrowth.c1547.check BB6.Agent2Raw124ZeroLFProbe.hard2)
#eval ("hard3", BB6.Agent2Raw124ZeroLFBlockGrowth.c1539.check BB6.Agent2Raw124ZeroLFProbe.hard3,
               BB6.Agent2Raw124ZeroLFBlockGrowth.c1547.check BB6.Agent2Raw124ZeroLFProbe.hard3)
#eval ("hard4", BB6.Agent2Raw124ZeroLFBlockGrowth.c1539.check BB6.Agent2Raw124ZeroLFProbe.hard4,
               BB6.Agent2Raw124ZeroLFBlockGrowth.c1547.check BB6.Agent2Raw124ZeroLFProbe.hard4)


open BB6.Agent2Raw124ZeroLFBlockGrowth BB6.Agent2Raw124ZeroLFProbe
open BB6Coverage.Agent50Pump

def fin6 (n : Nat) : Fin 6 := ⟨n % 6, Nat.mod_lt _ (by decide)⟩

def renameShape (p : List Nat) (s : Shape) : Shape :=
  { s with q := fin6 (p.getD s.q.val s.q.val) }

def renameOp (p : List Nat) : Op → Op
  | .step => .step
  | .rewrite s => .rewrite (renameShape p s)
  | .right k c v => .right k c v
  | .left k c v => .left k c v

def renameCert (p : List Nat) (c : Certificate) : Certificate :=
  { c with shape := renameShape p c.shape, ops := c.ops.map (renameOp p) }

def reflectShape (s : Shape) : Shape := ⟨s.q, s.r, s.l⟩

def reflectOp : Op → Op
  | .step => .step
  | .rewrite s => .rewrite (reflectShape s)
  | .right k c v => .left k c v
  | .left k c v => .right k c v

def transformCert (p : List Nat) (mirror : Bool) (c : Certificate) : Certificate :=
  let c' := renameCert p c
  if mirror then
    { c' with shape := reflectShape c'.shape, ops := c'.ops.map reflectOp }
  else c'

def statePerms : List (List Nat) := [
  [0, 1, 2, 3, 4, 5],
  [0, 1, 2, 3, 5, 4],
  [0, 1, 2, 4, 3, 5],
  [0, 1, 2, 4, 5, 3],
  [0, 1, 2, 5, 3, 4],
  [0, 1, 2, 5, 4, 3],
  [0, 1, 3, 2, 4, 5],
  [0, 1, 3, 2, 5, 4],
  [0, 1, 3, 4, 2, 5],
  [0, 1, 3, 4, 5, 2],
  [0, 1, 3, 5, 2, 4],
  [0, 1, 3, 5, 4, 2],
  [0, 1, 4, 2, 3, 5],
  [0, 1, 4, 2, 5, 3],
  [0, 1, 4, 3, 2, 5],
  [0, 1, 4, 3, 5, 2],
  [0, 1, 4, 5, 2, 3],
  [0, 1, 4, 5, 3, 2],
  [0, 1, 5, 2, 3, 4],
  [0, 1, 5, 2, 4, 3],
  [0, 1, 5, 3, 2, 4],
  [0, 1, 5, 3, 4, 2],
  [0, 1, 5, 4, 2, 3],
  [0, 1, 5, 4, 3, 2],
  [0, 2, 1, 3, 4, 5],
  [0, 2, 1, 3, 5, 4],
  [0, 2, 1, 4, 3, 5],
  [0, 2, 1, 4, 5, 3],
  [0, 2, 1, 5, 3, 4],
  [0, 2, 1, 5, 4, 3],
  [0, 2, 3, 1, 4, 5],
  [0, 2, 3, 1, 5, 4],
  [0, 2, 3, 4, 1, 5],
  [0, 2, 3, 4, 5, 1],
  [0, 2, 3, 5, 1, 4],
  [0, 2, 3, 5, 4, 1],
  [0, 2, 4, 1, 3, 5],
  [0, 2, 4, 1, 5, 3],
  [0, 2, 4, 3, 1, 5],
  [0, 2, 4, 3, 5, 1],
  [0, 2, 4, 5, 1, 3],
  [0, 2, 4, 5, 3, 1],
  [0, 2, 5, 1, 3, 4],
  [0, 2, 5, 1, 4, 3],
  [0, 2, 5, 3, 1, 4],
  [0, 2, 5, 3, 4, 1],
  [0, 2, 5, 4, 1, 3],
  [0, 2, 5, 4, 3, 1],
  [0, 3, 1, 2, 4, 5],
  [0, 3, 1, 2, 5, 4],
  [0, 3, 1, 4, 2, 5],
  [0, 3, 1, 4, 5, 2],
  [0, 3, 1, 5, 2, 4],
  [0, 3, 1, 5, 4, 2],
  [0, 3, 2, 1, 4, 5],
  [0, 3, 2, 1, 5, 4],
  [0, 3, 2, 4, 1, 5],
  [0, 3, 2, 4, 5, 1],
  [0, 3, 2, 5, 1, 4],
  [0, 3, 2, 5, 4, 1],
  [0, 3, 4, 1, 2, 5],
  [0, 3, 4, 1, 5, 2],
  [0, 3, 4, 2, 1, 5],
  [0, 3, 4, 2, 5, 1],
  [0, 3, 4, 5, 1, 2],
  [0, 3, 4, 5, 2, 1],
  [0, 3, 5, 1, 2, 4],
  [0, 3, 5, 1, 4, 2],
  [0, 3, 5, 2, 1, 4],
  [0, 3, 5, 2, 4, 1],
  [0, 3, 5, 4, 1, 2],
  [0, 3, 5, 4, 2, 1],
  [0, 4, 1, 2, 3, 5],
  [0, 4, 1, 2, 5, 3],
  [0, 4, 1, 3, 2, 5],
  [0, 4, 1, 3, 5, 2],
  [0, 4, 1, 5, 2, 3],
  [0, 4, 1, 5, 3, 2],
  [0, 4, 2, 1, 3, 5],
  [0, 4, 2, 1, 5, 3],
  [0, 4, 2, 3, 1, 5],
  [0, 4, 2, 3, 5, 1],
  [0, 4, 2, 5, 1, 3],
  [0, 4, 2, 5, 3, 1],
  [0, 4, 3, 1, 2, 5],
  [0, 4, 3, 1, 5, 2],
  [0, 4, 3, 2, 1, 5],
  [0, 4, 3, 2, 5, 1],
  [0, 4, 3, 5, 1, 2],
  [0, 4, 3, 5, 2, 1],
  [0, 4, 5, 1, 2, 3],
  [0, 4, 5, 1, 3, 2],
  [0, 4, 5, 2, 1, 3],
  [0, 4, 5, 2, 3, 1],
  [0, 4, 5, 3, 1, 2],
  [0, 4, 5, 3, 2, 1],
  [0, 5, 1, 2, 3, 4],
  [0, 5, 1, 2, 4, 3],
  [0, 5, 1, 3, 2, 4],
  [0, 5, 1, 3, 4, 2],
  [0, 5, 1, 4, 2, 3],
  [0, 5, 1, 4, 3, 2],
  [0, 5, 2, 1, 3, 4],
  [0, 5, 2, 1, 4, 3],
  [0, 5, 2, 3, 1, 4],
  [0, 5, 2, 3, 4, 1],
  [0, 5, 2, 4, 1, 3],
  [0, 5, 2, 4, 3, 1],
  [0, 5, 3, 1, 2, 4],
  [0, 5, 3, 1, 4, 2],
  [0, 5, 3, 2, 1, 4],
  [0, 5, 3, 2, 4, 1],
  [0, 5, 3, 4, 1, 2],
  [0, 5, 3, 4, 2, 1],
  [0, 5, 4, 1, 2, 3],
  [0, 5, 4, 1, 3, 2],
  [0, 5, 4, 2, 1, 3],
  [0, 5, 4, 2, 3, 1],
  [0, 5, 4, 3, 1, 2],
  [0, 5, 4, 3, 2, 1]
]

def matches (p : PartialMachine) (c : Certificate) (mirror : Bool) : List (List Nat) :=
  statePerms.filter (fun sigma => (transformCert sigma mirror c).check p)

#eval ("control1539", (matches p1539 c1539 false).head?, (matches p1539 c1539 true).head?)
#eval ("control1547", (matches p1547 c1547 false).head?, (matches p1547 c1547 true).head?)
#eval ("hard0", (matches hard0 c1539 false).head?, (matches hard0 c1539 true).head?,
                 (matches hard0 c1547 false).head?, (matches hard0 c1547 true).head?)
#eval ("hard1", (matches hard1 c1539 false).head?, (matches hard1 c1539 true).head?,
                 (matches hard1 c1547 false).head?, (matches hard1 c1547 true).head?)
#eval ("hard2", (matches hard2 c1539 false).head?, (matches hard2 c1539 true).head?,
                 (matches hard2 c1547 false).head?, (matches hard2 c1547 true).head?)
#eval ("hard3", (matches hard3 c1539 false).head?, (matches hard3 c1539 true).head?,
                 (matches hard3 c1547 false).head?, (matches hard3 c1547 true).head?)
#eval ("hard4", (matches hard4 c1539 false).head?, (matches hard4 c1539 true).head?,
                 (matches hard4 c1547 false).head?, (matches hard4 c1547 true).head?)
