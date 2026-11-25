import Q2800TreeCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Q2800
open BB6.Agent50RecursiveResidual
def chunk1 : List ClosedTree := [
  -- 1RB0RD_1LC1LA_0LE1RA_0LC0RB_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,6,2,23,7,0], .side 21 7 true (-1), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC1RB_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,8,2,23,7,0], .side 1 20 true (-4), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC0LC_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,9,2,23,7,0], .side 5 17 false (1), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC1RE_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,20,2,23,7,0], .last 16 (5,true), by decide, by decide⟩,
  -- 1RB0RD_1LC1LA_0LE1RA_0LC0RF_0RA1LF_1LB---
  ⟨[8,14,11,3,17,4,9,22,2,23,7,0], .last 15 (5,true), by decide, by decide⟩,
  -- 1RB0RD_1LC1RA_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,4,17,4,9,0,2,23,7,0], (branchList 14 (3,true) [.last 22 (5,true),
      .side 15 16 true (-2),
      .last 24 (5,true),
      .last 22 (5,true),
      .last 21 (5,true),
      .last 27 (5,true),
      .side 13 4 true (-2),
      .side 12 10 true (-2),
      .last 17 (5,true),
      .last 37 (5,true),
      .last 17 (5,true),
      .side 12 6 true (-2),
      .last 24 (5,true),
      .side 12 14 true (-2),
      .last 26 (5,true),
      .last 24 (5,true),
      .side 12 12 true (-2),
      .last 27 (5,true),
      .side 12 16 true (-2),
      .side 12 12 true (-2),
      .last 21 (5,true),
      .last 19 (5,true),
      .side 12 4 true (-2),
      .side 12 10 true (-2)]), by decide, by decide⟩,
  -- 1RB0RD_1LC0LB_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,5,17,4,9,0,2,23,7,0], .side 8 6 false (-2), by decide, by decide⟩,
  -- 1RB0RD_1LC1LB_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,7,17,4,9,0,2,23,7,0], .side 8 6 false (-2), by decide, by decide⟩,
  -- 1RB0RD_1LC0RC_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,10,17,4,9,0,2,23,7,0], .side 2 18 false (2), by decide, by decide⟩,
  -- 1RB0RD_1LC1LD_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,15,17,4,9,0,2,23,7,0], (branchList 13 (3,true) [.last 36 (5,true),
      .side 0 20 true (-4),
      .side 11 3 false (-2),
      .last 39 (5,true),
      .side 8 6 false (-2),
      .side 4 20 false (2),
      .side 8 6 false (-2),
      .side 12 2 true (-3),
      .side 5 16 false (1),
      .last 39 (5,true),
      .side 9 5 false (-2),
      .side 12 8 true (-3),
      .side 0 17 false (2),
      .side 0 20 true (-4),
      .side 13 14 false (-3),
      .last 26 (5,true),
      .side 10 4 true (-4),
      .side 6 8 false (0),
      .side 0 28 true (-4),
      .last 15 (5,true),
      .side 7 7 false (-1),
      .last 14 (5,true),
      .side 7 7 false (-1),
      .last 14 (5,true)]), by decide, by decide⟩,
  -- 1RB0RD_1LC0RE_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,18,17,4,9,0,2,23,7,0], .side 6 10 false (0), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_0LB1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,5,23,7,0], .side 8 3 false (-2), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_0RB1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,6,23,7,0], .side 8 3 false (-2), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_0RD1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,14,23,7,0], .side 9 3 false (-3), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_0LE1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,17,23,7,0], .side 10 1 false (-4), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_1LE1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,19,23,7,0], .side 10 1 false (-4), by decide, by decide⟩,
  -- 1RB0LD_1LC---_---1RA_---0RA_------_------
  ⟨[8,13,11,0,0,4,0,2,0,0,0,0], .side 0 5 true (0), by decide, by decide⟩,
  -- 1RB1RC_1LC---_0LA1RA_------_------_------
  ⟨[8,12,11,0,1,4,0,0,0,0,0,0], .side 3 2 true (1), by decide, by decide⟩,
  -- 1RB1RC_1LC---_0LC1RA_------_------_------
  ⟨[8,12,11,0,9,4,0,0,0,0,0,0], .side 0 6 true (0), by decide, by decide⟩
]
#print axioms chunk1
end BB6.Agent50Q2800
