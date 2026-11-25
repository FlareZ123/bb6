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
