import Q2800TreeCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Q2800
open BB6.Agent50RecursiveResidual
def chunk3 : List ClosedTree := [
  -- 1RB0RD_1LC0LD_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,13,17,4,9,0,2,23,7,0], (branchList 13 (3,true) [.side 0 14 false (2),
      .side 0 20 true (-4),
      .side 11 3 false (-2),
      .last 27 (5,true),
      .side 8 6 false (-2),
      .side 8 6 true (-4),
      .side 8 6 false (-2),
      .side 0 31 false (2),
      .side 0 16 false (2),
      .side 0 26 true (-4),
      .side 9 5 false (-2),
      .side 5 9 false (1),
      .side 0 17 false (2),
      .side 18 16 true (-3),
      .side 13 14 false (-3),
      .last 33 (5,true),
      .side 0 37 false (2),
      .side 0 18 true (-4),
      .side 20 20 true (-3),
      .last 47 (5,true),
      .side 7 7 false (-1),
      .side 7 7 false (-1),
      .side 7 7 false (-1),
      .side 0 19 false (2)]), by decide, by decide⟩,
  -- 1RB0RD_1LC0LE_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,17,17,4,9,0,2,23,7,0], .side 6 7 false (0), by decide, by decide⟩,
  -- 1RB0RD_1LC0RF_0LE1RA_0LC---_0RA1LF_1LB---
  ⟨[8,14,11,22,17,4,9,0,2,23,7,0], (branchList 13 (5,true) [.last 18 (3,true),
      .last 29 (3,true),
      .last 23 (3,true),
      .side 3 18 false (2),
      .side 1 13 false (2),
      .last 31 (3,true),
      .last 17 (3,true),
      .last 19 (3,true),
      .side 5 9 false (1),
      .side 13 9 true (-1),
      .side 5 9 false (1),
      .side 13 9 true (-1),
      .last 20 (3,true),
      .last 14 (3,true),
      .last 27 (3,true),
      .last 14 (3,true),
      .last 21 (3,true),
      .last 19 (3,true),
      .last 16 (3,true),
      .side 13 2 true (-1),
      .side 7 10 false (-1),
      .last 54 (3,true),
      .side 7 10 false (-1),
      .side 14 3 true (0)]), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_0LC1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,9,23,7,0], .side 9 2 false (-3), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_1LC1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,11,23,7,0], .side 9 2 false (-3), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_0LD1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,13,23,7,0], .side 9 3 false (-3), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_1LD1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,15,23,7,0], .side 9 3 false (-3), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_0RF1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,22,23,7,0], .side 7 4 false (-1), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_1LF1LF_1LB---
  ⟨[8,14,11,0,17,4,9,0,23,23,7,0], .side 7 4 false (-1), by decide, by decide⟩,
  -- 1RB0RD_1LC---_0LE1RA_0LC---_---1LF_1LF---
  ⟨[8,14,11,0,17,4,9,0,0,23,23,0], .side 7 1 false (-1), by decide, by decide⟩,
  -- 1RB0RD_1LC---_---1RA_1RD---_------_------
  ⟨[8,14,11,0,0,4,16,0,0,0,0,0], .side 4 1 true (2), by decide, by decide⟩,
  -- 1RB0LD_1LC---_---1RA_---0LA_------_------
  ⟨[8,13,11,0,0,4,0,1,0,0,0,0], .side 0 5 false (1), by decide, by decide⟩,
  -- 1RB1RC_1LC---_0RA1RA_------_------_------
  ⟨[8,12,11,0,2,4,0,0,0,0,0,0], .side 0 5 true (0), by decide, by decide⟩,
  -- 1RB1RC_1LC---_1RB1RA_------_------_------
  ⟨[8,12,11,0,8,4,0,0,0,0,0,0], .side 1 4 true (0), by decide, by decide⟩,
  -- 1RB1RC_1LC---_0RC1RA_------_------_------
  ⟨[8,12,11,0,10,4,0,0,0,0,0,0], .side 4 1 true (2), by decide, by decide⟩,
  -- 1RB0RC_1LC---_0RA1RA_------_------_------
  ⟨[8,10,11,0,2,4,0,0,0,0,0,0], .side 0 5 true (0), by decide, by decide⟩,
  -- 1RB0RC_1LC---_0RC1RA_------_------_------
  ⟨[8,10,11,0,10,4,0,0,0,0,0,0], .side 4 1 true (2), by decide, by decide⟩,
  -- 1RB1LB_1LC0LA_---1RA_------_------_------
  ⟨[8,7,11,1,0,4,0,0,0,0,0,0], .side 0 5 false (1), by decide, by decide⟩,
  -- 1RB1LB_1LC1RB_---1RA_------_------_------
  ⟨[8,7,11,8,0,4,0,0,0,0,0,0], .side 1 5 true (0), by decide, by decide⟩
]
#print axioms chunk3
end BB6.Agent50Q2800
