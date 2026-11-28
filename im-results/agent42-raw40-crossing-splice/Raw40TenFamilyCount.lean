import Raw40LocalCut
import Raw40A0LABase
import Raw40A0LBBase
import Raw40A0RBBase
import Raw40A0RCBase
import Raw40A0RDBase
import Raw40A1LABase
import Raw40A1LBBase
import Raw40A1LCBase
import Raw40A1RBBase
import Raw40A1RCBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40TenFamilyCount
open BB6Coverage BB6.Agent47CanonicalFrontier

def inA0LA (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A0LA.bounds.any fun x =>
    BB6.Agent19Raw40.A0LA.equalTable e.2 (BB6.Agent19Raw40.A0LA.child x.1)
def inA0LB (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A0LB.bounds.any fun x =>
    BB6.Agent19Raw40.A0LB.equalTable e.2 (BB6.Agent19Raw40.A0LB.child x.1)
def inA0RB (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A0RB.bounds.any fun x =>
    BB6.Agent19Raw40.A0RB.equalTable e.2 (BB6.Agent19Raw40.A0RB.child x.1)
def inA0RC (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A0RC.bounds.any fun x =>
    BB6.Agent19Raw40.A0RC.equalTable e.2 (BB6.Agent19Raw40.A0RC.child x.1)
def inA0RD (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A0RD.bounds.any fun x =>
    BB6.Agent19Raw40.A0RD.equalTable e.2 (BB6.Agent19Raw40.A0RD.child x.1)
def inA1LA (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A1LA.bounds.any fun x =>
    BB6.Agent19Raw40.A1LA.equalTable e.2 (BB6.Agent19Raw40.A1LA.child x.1)
def inA1LB (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A1LB.bounds.any fun x =>
    BB6.Agent19Raw40.A1LB.equalTable e.2 (BB6.Agent19Raw40.A1LB.child x.1)
def inA1LC (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A1LC.bounds.any fun x =>
    BB6.Agent19Raw40.A1LC.equalTable e.2 (BB6.Agent19Raw40.A1LC.child x.1)
def inA1RB (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A1RB.bounds.any fun x =>
    BB6.Agent19Raw40.A1RB.equalTable e.2 (BB6.Agent19Raw40.A1RB.child x.1)
def inA1RC (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A1RC.bounds.any fun x =>
    BB6.Agent19Raw40.A1RC.equalTable e.2 (BB6.Agent19Raw40.A1RC.child x.1)

def solved (e : List Move × PartialMachine) : Bool :=
  inA0LA e || inA0LB e || inA0RB e || inA0RC e || inA0RD e ||
  inA1LA e || inA1LB e || inA1LC e || inA1RB e || inA1RC e

def remaining : List (List Move × PartialMachine) :=
  BB6.Agent19Raw40.canonicalRemaining.filter fun e => ! solved e

/-- Exactly 114 of Raw40's 189 two-level canonical residuals belong to
    the ten deeply-developed six-hole first-query families; 75 remain
    outside their union. This theorem depends only on the canonical
    partial-machine tables, not on any child nonhalting certificate. -/
theorem count : remaining.length = 75 := by decide

/-- Equivalent cardinality statement for the ten-family union inside
    the canonical Raw40 frontier. -/
theorem solved_count :
    (BB6.Agent19Raw40.canonicalRemaining.filter solved).length = 114 := by decide

#print axioms count
#print axioms solved_count
end BB6.Agent42Raw40TenFamilyCount
