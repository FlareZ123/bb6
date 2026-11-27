import Raw36FirstCounters

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.Auto.Raw36FirstDescentBridge
open BB6Coverage Agent31Pump Auto Raw36FirstCounters

def p : PartialMachine := Raw36FirstOverflowA2.p
def rest (v : Nat) : List Bool := rep pair v ++ suffix

theorem inA (n v : Nat) :
    (OpenRight.attachZ Raw36FirstDescentA.source (rest v)).eval n =
      A (2*n+1) (10+v) := by
  have hu : 2*n+1-1=2*n := by omega
  simp [OpenRight.attachZ_eval,Raw36FirstDescentA.source,
        PZ.eval,Word.eval,A,rest,hu,rep_add,rep_two,pair,quad,mark,suffix,
        rep,List.append_assoc]

theorem outA (n v : Nat) :
    (OpenRight.attachZ Raw36FirstDescentA.target (rest v)).eval n =
      A (2*n+21) v := by
  have hu : 2*n+21-1=20+2*n := by omega
  simp [OpenRight.attachZ_eval,Raw36FirstDescentA.target,
        PZ.eval,Word.eval,A,rest,hu,rep_add,rep_two,pair,quad,mark,suffix,
        rep,List.append_assoc]

theorem descentA (n v : Nat) :
    run0 p (180*n+1270) (A (2*n+1) (10+v)) =
      some (A (2*n+21) v) := by
  rw [← inA n v,← outA n v]
  exact Raw36FirstDescentA.transport n (rest v)

theorem inB (n v : Nat) :
    (OpenRight.attachZ Raw36FirstDescentB.source (rest v)).eval n =
      B (2*n+3) (10+v) := by
  have hu : 2*n+3-1=2+2*n := by omega
  simp [OpenRight.attachZ_eval,Raw36FirstDescentB.source,
        PZ.eval,Word.eval,B,rest,hu,rep_add,rep_two,pair,quad,mark,suffix,
        rep,List.append_assoc]

theorem outB (n v : Nat) :
    (OpenRight.attachZ Raw36FirstDescentB.target (rest v)).eval n =
      B (2*n+23) v := by
  have hu : 2*n+23-1=22+2*n := by omega
  simp [OpenRight.attachZ_eval,Raw36FirstDescentB.target,
        PZ.eval,Word.eval,B,rest,hu,rep_add,rep_two,pair,quad,mark,suffix,
        rep,List.append_assoc]

theorem descentB (n v : Nat) :
    run0 p (180*n+1270) (B (2*n+3) (10+v)) =
      some (B (2*n+23) v) := by
  rw [← inB n v,← outB n v]
  exact Raw36FirstDescentB.transport n (rest v)

theorem inB1 (v : Nat) :
    (OpenRight.attachZ Raw36FirstDescentB1.source (rest v)).eval 0 =
      B 1 (10+v) := by
  simp [OpenRight.attachZ_eval,Raw36FirstDescentB1.source,
        PZ.eval,Word.eval,B,rest,rep_add,pair,quad,mark,suffix,rep,
        List.append_assoc]

theorem outB1 (v : Nat) :
    (OpenRight.attachZ Raw36FirstDescentB1.target (rest v)).eval 0 =
      B 21 v := by
  simp [OpenRight.attachZ_eval,Raw36FirstDescentB1.target,
        PZ.eval,Word.eval,B,rest,rep_add,pair,quad,mark,suffix,rep,
        List.append_assoc]

theorem descentB1 (v : Nat) :
    run0 p 1090 (B 1 (10+v)) = some (B 21 v) := by
  rw [← inB1 v,← outB1 v]
  exact Raw36FirstDescentB1.transport (rest v)

#print axioms descentA
#print axioms descentB
#print axioms descentB1
end BB6Coverage.Agent31Pump.Auto.Raw36FirstDescentBridge
