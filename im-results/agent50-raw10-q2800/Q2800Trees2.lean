import Q2800TreeCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Q2800
open BB6.Agent50RecursiveResidual
def chunk2 : List ClosedTree := [
  -- 1RB1RC_1LC---_1LC1RA_------_------_------
  ⟨[8,12,11,0,11,4,0,0,0,0,0,0], .side 2 3 true (0), by decide, by decide⟩,
  -- 1RB0RC_1LC---_0LA1RA_------_------_------
  ⟨[8,10,11,0,1,4,0,0,0,0,0,0], .side 0 5 true (0), by decide, by decide⟩,
  -- 1RB0RC_1LC---_1LB1RA_------_------_------
  ⟨[8,10,11,0,7,4,0,0,0,0,0,0], .side 0 9 true (0), by decide, by decide⟩,
  -- 1RB0RC_1LC---_1RB1RA_------_------_------
  ⟨[8,10,11,0,8,4,0,0,0,0,0,0], .side 1 4 true (0), by decide, by decide⟩,
  -- 1RB0RC_1LC---_0LC1RA_------_------_------
  ⟨[8,10,11,0,9,4,0,0,0,0,0,0], .side 0 7 true (0), by decide, by decide⟩,
  -- 1RB0RC_1LC---_1LC1RA_------_------_------
  ⟨[8,10,11,0,11,4,0,0,0,0,0,0], .side 0 9 true (0), by decide, by decide⟩,
  -- 1RB0RC_1LC---_1RC1RA_------_------_------
  ⟨[8,10,11,0,12,4,0,0,0,0,0,0], .side 4 1 true (2), by decide, by decide⟩,
  -- 1RB1LB_1LC1RC_---1RA_------_------_------
  ⟨[8,7,11,12,0,4,0,0,0,0,0,0], .side 0 6 true (0), by decide, by decide⟩,
  -- 1RB0RB_1LC---_1RA1RA_------_------_------
  ⟨[8,6,11,0,4,4,0,0,0,0,0,0], .side 3 3 true (1), by decide, by decide⟩,
  -- 1RB0RB_1LC---_1RC1RA_------_------_------
  ⟨[8,6,11,0,12,4,0,0,0,0,0,0], .side 0 7 true (0), by decide, by decide⟩,
  -- 1RB0LB_1LC1RA_---1RA_------_------_------
  ⟨[8,5,11,4,0,4,0,0,0,0,0,0], .side 0 5 true (0), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC1RA_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,4,2,23,7,0], .last 24 (5,true), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC1LB_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,7,2,23,7,0], .side 8 7 false (-2), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC0RC_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,10,2,23,7,0], .side 2 13 false (2), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC1RC_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,12,2,23,7,0], .last 20 (5,true), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC1LD_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,15,2,23,7,0], .side 21 6 true (-4), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC0LE_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,17,2,23,7,0], .side 0 26 true (-4), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC0RE_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,18,2,23,7,0], .side 6 9 false (0), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC1RF_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,24,2,23,7,0], .last 15 (5,true), by decide, by decide⟩
]
#print axioms chunk2
end BB6.Agent50Q2800
