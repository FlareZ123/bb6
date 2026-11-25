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

/-- Diagnostic only: a true Boolean is a candidate transfer, not a theorem until
the corresponding Certificate.never adapter is exported and source-checked. -/
#eval ("hard0", c1539.check hard0, c1547.check hard0)
#eval ("hard1", c1539.check hard1, c1547.check hard1)
#eval ("hard2", c1539.check hard2, c1547.check hard2)
#eval ("hard3", c1539.check hard3, c1547.check hard3)
#eval ("hard4", c1539.check hard4, c1547.check hard4)

end BB6.Agent2Raw124ZeroLFProbe
