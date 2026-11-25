import Q2800TreeCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Q2800
open BB6.Agent50RecursiveResidual
def chunk4 : List ClosedTree := [
  -- 1RB1LB_1LC0RC_---1RA_------_------_------
  ⟨[8,7,11,10,0,4,0,0,0,0,0,0], .side 0 6 true (0), by decide, by decide⟩,
  -- 1RB0LB_1LC0LA_---1RA_------_------_------
  ⟨[8,5,11,1,0,4,0,0,0,0,0,0], .side 0 5 false (1), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC0LB_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,5,2,23,7,0], .side 8 7 false (-2), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC1LC_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,11,2,23,7,0], .side 9 6 true (-4), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC0LD_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,13,2,23,7,0], .side 0 18 false (2), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC0RD_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,14,2,23,7,0], .side 0 20 true (-4), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC1RD_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,16,2,23,7,0], .last 26 (5,true), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC1LE_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,19,2,23,7,0], .side 0 26 true (-4), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC0LF_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,21,2,23,7,0], .side 7 8 false (-1), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC1LF_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,23,2,23,7,0], .side 7 8 false (-1), by decide, by decide⟩,
  -- 1RB0RD_1LC1LC_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,11,17,4,9,0,2,23,7,0], (branchList 15 (3,true) [.last 28 (5,true),
      .side 13 16 true (-3),
      .last 28 (5,true),
      .side 9 13 false (1),
      .side 1 15 false (2),
      .side 9 19 false (1),
      .side 13 4 true (-3),
      .side 9 15 false (1),
      .side 5 11 false (1),
      .last 24 (5,true),
      .side 5 11 false (1),
      .last 24 (5,true),
      .last 32 (5,true),
      .side 13 16 true (-3),
      .last 32 (5,true),
      .last 26 (5,true),
      .side 9 17 false (1),
      .side 13 6 true (-3),
      .side 13 20 true (-3),
      .last 17 (5,true),
      .side 9 9 false (-1),
      .last 16 (5,true),
      .side 9 9 false (-1),
      .last 16 (5,true)]), by decide, by decide⟩,
  -- 1RB0RD_1LC1RD_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,16,17,4,9,0,2,23,7,0], (branchList 13 (3,true) [.side 3 11 false (2),
      .side 12 14 true (-2),
      .last 32 (5,true),
      .last 18 (5,true),
      .last 28 (5,true),
      .last 24 (5,true),
      .side 12 2 true (-2),
      .last 24 (5,true),
      .last 26 (5,true),
      .last 22 (5,true),
      .last 19 (5,true),
      .last 22 (5,true),
      .side 0 19 false (2),
      .side 12 14 true (-2),
      .side 13 16 false (-1),
      .last 24 (5,true),
      .last 15 (5,true),
      .side 12 4 true (-2),
      .last 15 (5,true),
      .last 15 (5,true),
      .last 14 (5,true),
      .last 14 (5,true),
      .last 14 (5,true),
      .last 14 (5,true)]), by decide, by decide⟩,
  -- 1RB0RD_1LC1LE_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,19,17,4,9,0,2,23,7,0], .side 6 7 false (0), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_1LB1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,7,23,7,0], .side 8 3 false (-2), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_0RC1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,10,23,7,0], .side 9 2 true (-4), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_1RC1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,12,23,7,0], .side 5 6 false (1), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_0RE1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,18,23,7,0], .side 6 6 false (0), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_0LF1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,21,23,7,0], .side 7 4 false (-1), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_---1LF_0RE---
  ⟨[8,14,11,0,17,4,9,0,0,23,18,0], .side 6 2 true (-1), by decide, by decide⟩
]
#print axioms chunk4
end BB6.Agent50Q2800
