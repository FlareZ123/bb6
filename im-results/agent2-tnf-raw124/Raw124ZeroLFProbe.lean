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


open BB6Coverage.Agent50Pump BB6.Agent2Raw124ZeroLFBlockGrowth

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

/-- The 120 state permutations fixing the blank-start state A. -/
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

def validStatePerm (p : List Nat) : Bool :=
  decide (p.length = 6) && decide (p.head? = some 0) &&
  decide p.Nodup && p.all (fun n => decide (n < 6))

theorem statePerms_length : statePerms.length = 120 := by decide
theorem statePerms_nodup : statePerms.Nodup := by decide
theorem statePerms_valid : statePerms.all validStatePerm = true := by decide

def noTransfer (p : PartialMachine) (c : Certificate) (mirror : Bool) : Bool :=
  statePerms.all (fun sigma => !(transformCert sigma mirror c).check p)

theorem control1539 :
    (transformCert [0,1,2,3,4,5] false c1539).check p1539 = true := by decide
theorem control1547 :
    (transformCert [0,1,2,3,4,5] false c1547).check p1547 = true := by decide

theorem noTransferHard0 :
    noTransfer hard0 c1539 false = true ∧
    noTransfer hard0 c1539 true = true ∧
    noTransfer hard0 c1547 false = true ∧
    noTransfer hard0 c1547 true = true := by decide

theorem noTransferHard1 :
    noTransfer hard1 c1539 false = true ∧
    noTransfer hard1 c1539 true = true ∧
    noTransfer hard1 c1547 false = true ∧
    noTransfer hard1 c1547 true = true := by decide

theorem noTransferHard2 :
    noTransfer hard2 c1539 false = true ∧
    noTransfer hard2 c1539 true = true ∧
    noTransfer hard2 c1547 false = true ∧
    noTransfer hard2 c1547 true = true := by decide

theorem noTransferHard3 :
    noTransfer hard3 c1539 false = true ∧
    noTransfer hard3 c1539 true = true ∧
    noTransfer hard3 c1547 false = true ∧
    noTransfer hard3 c1547 true = true := by decide

theorem noTransferHard4 :
    noTransfer hard4 c1539 false = true ∧
    noTransfer hard4 c1539 true = true ∧
    noTransfer hard4 c1547 false = true ∧
    noTransfer hard4 c1547 true = true := by decide

#print axioms control1539
#print axioms control1547
#print axioms noTransferHard0
#print axioms noTransferHard1
#print axioms noTransferHard2
#print axioms noTransferHard3
#print axioms noTransferHard4

end BB6.Agent2Raw124ZeroLFProbe
