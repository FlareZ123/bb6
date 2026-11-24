import SevenSideWitnesses
import RecursiveResidual

set_option maxRecDepth 40000
set_option maxHeartbeats 0
namespace BB6.Agent47SevenDeep
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent50RootFrontier BB6.Agent47SevenRoster BB6.Agent47SevenSideWitnesses BB6.Agent50RecursiveResidual
structure CheckedDeepTree where
  table : PackedTable
  tree : Tree
  checked : tree.check 7014 (unpackTable table) = true

def d88 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 9, 2, 12, 15, 5, 19, 21, 10, 0, 0], branchList 22 (5,true) [
    .side 0 23 false (2), .side 14 9 true (-2), .side 13 11 true (-3), .side 14 9 true (-2),
    .side 45 127 true (-6), .side 8 40 true (-4), .side 44 11 true (-2), .openLeaf,
    .side 158 42 true (-2), .last 27 (5,false), .last 27 (5,false), .side 8 38 true (-4),
    .openLeaf, .side 168 44 true (-2), .openLeaf, .side 12 11 true (-3),
    .last 24 (5,false), .last 24 (5,false), .last 24 (5,false), .side 21 2 true (-2),
    .last 23 (5,false), .last 23 (5,false), .last 23 (5,false), .last 23 (5,false)
  ], by decide⟩

def d89 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 9, 2, 12, 15, 5, 19, 22, 10, 0, 0], branchList 22 (5,true) [
    .side 47 7 true (-1), .side 16 7 true (-1), .side 14 9 true (-2), .openLeaf,
    .side 1 22 false (2), .side 0 24 true (-3), .openLeaf, .side 23 7 true (0),
    .side 6 17 true (-3), .side 1 24 false (2), .side 8 38 true (-4), .side 19 4 true (-1),
    .side 42 7 true (0), .side 28 1 true (0), .side 12 11 true (-3), .side 1 26 false (2),
    .last 24 (5,false), .side 24 1 true (2), .side 21 2 true (-1), .side 24 1 true (2),
    .last 23 (5,false), .last 24 (5,false), .last 23 (5,false), .last 24 (5,false)
  ], by decide⟩

def d90 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 9, 2, 12, 15, 5, 19, 24, 10, 0, 0], branchList 22 (5,true) [
    .side 24 7 true (0), .side 16 7 true (-1), .side 8 20 true (-3), .side 8 18 true (-3),
    .side 23 7 true (-1), .side 62 7 true (0), .openLeaf, .side 23 7 true (0),
    .side 43 7 true (-1), .side 23 7 true (-1), .openLeaf, .side 8 15 true (-3),
    .side 40 7 true (0), .side 1 53 false (2), .side 8 36 true (-4), .side 25 7 true (-1),
    .side 19 6 true (-1), .side 24 1 true (2), .side 10 13 true (-3), .side 24 1 true (2),
    .last 25 (5,false), .last 24 (5,false), .last 25 (5,false), .last 24 (5,false)
  ], by decide⟩

def d274 : CheckedDeepTree :=
  ⟨decodeRows [8, 6, 10, 13, 3, 24, 19, 15, 7, 0, 0, 4], branchList 15 (4,true) [
    .last 19 (5,false), .last 47 (5,false), .side 5 21 false (1), .side 12 12 true (-1),
    .last 25 (5,false), .side 5 27 false (1), .side 5 20 false (1), .side 4 12 false (2),
    .last 17 (5,false), .last 17 (5,false), .side 10 16 true (-2), .last 17 (5,false),
    .last 25 (5,false), .side 6 13 false (1), .side 6 10 false (1), .side 5 12 false (1),
    .last 20 (5,false), .last 20 (5,false), .side 8 9 false (1), .side 4 14 false (2),
    .side 3 14 false (2), .side 3 30 true (-3), .last 21 (5,false), .side 23 16 false (1)
  ], by decide⟩

def d277 : CheckedDeepTree :=
  ⟨decodeRows [8, 9, 10, 13, 3, 24, 19, 15, 7, 0, 0, 4], branchList 14 (5,false) [
    .side 6 16 false (0), .last 47 (4,true), .side 6 16 false (0), .openLeaf,
    .side 6 10 false (0), .last 17 (4,true), .side 6 10 false (0), .side 5 12 false (1),
    .side 13 2 true (-1), .last 23 (4,true), .openLeaf, .side 12 6 true (-1),
    .side 5 10 false (1), .last 17 (4,true), .side 5 10 false (1), .side 5 12 false (1),
    .last 15 (4,true), .last 15 (4,true), .last 15 (4,true), .last 15 (4,true),
    .side 5 14 false (1), .last 25 (4,true), .side 11 4 true (-1), .openLeaf
  ], by decide⟩

def d278 : CheckedDeepTree :=
  ⟨decodeRows [8, 10, 10, 13, 3, 24, 19, 15, 7, 0, 0, 4], branchList 14 (5,false) [
    .last 21 (4,true), .last 23 (4,true), .side 12 3 true (0), .last 25 (4,true),
    .last 17 (4,true), .last 21 (4,true), .last 17 (4,true), .last 23 (4,true),
    .side 13 2 true (1), .last 21 (4,true), .last 27 (4,true), .side 12 4 true (0),
    .last 17 (4,true), .last 19 (4,true), .last 17 (4,true), .last 16 (4,true),
    .last 15 (4,true), .side 13 4 true (1), .last 15 (4,true), .last 19 (4,true),
    .last 25 (4,true), .side 14 1 true (2), .last 23 (4,true), .side 14 1 true (2)
  ], by decide⟩

def d280 : CheckedDeepTree :=
  ⟨decodeRows [8, 12, 10, 13, 3, 24, 19, 15, 7, 0, 0, 4], branchList 14 (5,false) [
    .side 12 5 true (0), .last 23 (4,true), .side 12 3 true (0), .openLeaf,
    .openLeaf, .last 21 (4,true), .openLeaf, .openLeaf,
    .side 13 2 true (1), .openLeaf, .openLeaf, .side 12 4 true (0),
    .openLeaf, .openLeaf, .openLeaf, .last 16 (4,true),
    .last 15 (4,true), .side 13 4 true (1), .last 15 (4,true), .openLeaf,
    .openLeaf, .side 14 1 true (2), .side 12 6 true (0), .side 14 1 true (2)
  ], by decide⟩

def d282 : CheckedDeepTree :=
  ⟨decodeRows [8, 14, 10, 13, 3, 24, 19, 15, 7, 0, 0, 4], branchList 15 (4,true) [
    .side 7 10 true (-3), .side 5 24 false (1), .side 6 11 false (1), .side 12 4 true (-1),
    .side 37 10 false (-3), .last 28 (5,false), .side 5 20 false (1), .side 4 12 false (2),
    .last 17 (5,false), .side 29 25 false (4), .side 10 6 true (-2), .openLeaf,
    .side 16 10 false (-1), .side 6 13 false (1), .side 6 10 false (1), .side 5 12 false (1),
    .last 20 (5,false), .last 21 (5,false), .side 8 9 false (1), .openLeaf,
    .side 3 14 false (2), .side 3 21 false (2), .last 21 (5,false), .side 4 16 false (2)
  ], by decide⟩

def d285 : CheckedDeepTree :=
  ⟨decodeRows [8, 17, 10, 13, 3, 24, 19, 15, 7, 0, 0, 4], branchList 13 (4,true) [
    .last 18 (5,false), .last 23 (5,false), .last 18 (5,false), .side 5 12 false (1),
    .side 5 22 false (1), .last 16 (5,false), .side 5 18 false (1), .last 16 (5,false),
    .last 15 (5,false), .side 2 12 false (2), .side 5 14 false (1), .last 22 (5,false),
    .side 6 8 false (0), .side 5 20 false (1), .side 6 8 false (0), .side 5 12 false (1),
    .last 18 (5,false), .last 37 (5,false), .side 8 7 false (0), .side 6 10 false (0),
    .last 18 (5,false), .last 14 (5,false), .last 17 (5,false), .last 14 (5,false)
  ], by decide⟩

def d286 : CheckedDeepTree :=
  ⟨decodeRows [8, 18, 10, 13, 3, 24, 19, 15, 7, 0, 0, 4], branchList 13 (4,true) [
    .side 24 22 true (-5), .last 41 (5,false), .side 5 12 false (1), .side 12 14 true (-1),
    .side 5 14 false (1), .last 58 (5,false), .last 16 (5,false), .last 62 (5,false),
    .last 33 (5,false), .last 38 (5,false), .side 5 41 false (1), .side 12 3 true (0),
    .openLeaf, .side 40 69 false (2), .side 6 10 false (1), .side 15 14 false (2),
    .last 42 (5,false), .last 17 (5,false), .last 31 (5,false), .side 4 16 false (2),
    .last 14 (5,false), .last 14 (5,false), .last 14 (5,false), .last 14 (5,false)
  ], by decide⟩

def d287 : CheckedDeepTree :=
  ⟨decodeRows [8, 19, 10, 13, 3, 24, 19, 15, 7, 0, 0, 4], branchList 13 (4,true) [
    .side 5 17 false (1), .side 5 20 false (1), .side 8 7 false (0), .side 12 2 true (-1),
    .last 53 (5,false), .last 26 (5,false), .side 5 18 false (1), .side 4 10 false (2),
    .last 15 (5,false), .last 36 (5,false), .side 10 4 true (-2), .openLeaf,
    .side 6 8 false (0), .side 6 11 false (0), .side 6 8 false (0), .side 5 10 false (1),
    .last 18 (5,false), .last 19 (5,false), .side 8 7 false (0), .openLeaf,
    .side 3 12 false (2), .side 24 71 false (2), .last 17 (5,false), .openLeaf
  ], by decide⟩

def d288 : CheckedDeepTree :=
  ⟨decodeRows [8, 20, 10, 13, 3, 24, 19, 15, 7, 0, 0, 4], branchList 13 (4,true) [
    .side 4 12 false (2), .side 189 35 false (-3), .side 12 2 true (0), .openLeaf,
    .side 4 10 false (2), .side 19 31 false (1), .side 4 10 false (2), .side 19 12 false (1),
    .last 15 (5,false), .last 46 (5,false), .openLeaf, .side 12 3 true (0),
    .side 5 10 false (1), .side 4 12 false (2), .side 5 10 false (1), .side 15 12 false (2),
    .last 20 (5,false), .last 17 (5,false), .side 8 9 false (1), .openLeaf,
    .side 21 14 false (1), .last 14 (5,false), .openLeaf, .last 14 (5,false)
  ], by decide⟩

def d290 : CheckedDeepTree :=
  ⟨decodeRows [8, 22, 10, 13, 3, 24, 19, 15, 7, 0, 0, 4], branchList 23 (4,true) [
    .last 25 (5,false), .side 11 14 true (-1), .last 62 (5,false), .side 11 14 true (-1),
    .last 57 (5,false), .last 38 (5,false), .last 43 (5,false), .side 20 16 false (2),
    .last 25 (5,false), .side 10 14 true (-2), .last 48 (5,false), .side 10 14 true (-2),
    .last 31 (5,false), .last 38 (5,false), .openLeaf, .openLeaf,
    .last 28 (5,false), .last 31 (5,false), .last 34 (5,false), .last 45 (5,false),
    .side 20 18 false (2), .last 28 (5,false), .last 30 (5,false), .last 28 (5,false)
  ], by decide⟩

def d450 : CheckedDeepTree :=
  ⟨decodeRows [8, 6, 10, 17, 15, 24, 7, 0, 15, 19, 0, 4], branchList 23 (3,true) [
    .last 27 (5,false), .last 27 (5,false), .side 4 21 false (1), .last 27 (5,false),
    .last 33 (5,false), .side 13 25 false (-1), .side 4 20 false (1), .side 13 12 false (-1),
    .last 25 (5,false), .last 25 (5,false), .last 29 (5,false), .last 25 (5,false),
    .last 28 (5,false), .side 3 32 false (2), .side 16 9 false (-1), .side 13 14 false (-1),
    .last 33 (5,false), .side 14 13 false (-1), .side 14 10 false (-1), .side 12 12 false (0),
    .side 13 14 false (-1), .side 56 19 true (1), .last 29 (5,false), .side 12 16 false (0)
  ], by decide⟩

def d453 : CheckedDeepTree :=
  ⟨decodeRows [8, 9, 10, 17, 15, 24, 7, 0, 15, 19, 0, 4], branchList 22 (5,false) [
    .side 13 24 false (-1), .last 25 (3,true), .side 6 22 false (1), .openLeaf,
    .side 14 10 false (-2), .last 25 (3,true), .side 14 10 false (-2), .side 11 12 false (1),
    .side 21 2 true (-3), .last 31 (3,true), .openLeaf, .last 130 (3,true),
    .last 23 (3,true), .last 23 (3,true), .last 23 (3,true), .last 23 (3,true),
    .side 13 10 false (-1), .last 25 (3,true), .side 13 10 false (-1), .side 12 12 false (0),
    .side 9 14 false (1), .last 39 (3,true), .side 19 4 true (-3), .side 65 1 true (5)
  ], by decide⟩

def d454 : CheckedDeepTree :=
  ⟨decodeRows [8, 10, 10, 17, 15, 24, 7, 0, 15, 19, 0, 4], branchList 29 (3,true) [
    .last 54 (5,false), .side 3 36 false (2), .last 50 (5,false), .last 42 (5,false),
    .last 42 (5,false), .last 76 (5,false), .side 4 26 false (2), .last 40 (5,false),
    .last 31 (5,false), .last 34 (5,false), .last 46 (5,false), .last 34 (5,false),
    .last 34 (5,false), .last 37 (5,false), .last 40 (5,false), .last 51 (5,false),
    .side 30 10 false (-3), .last 44 (5,false), .last 68 (5,false), .last 74 (5,false),
    .last 42 (5,false), .last 46 (5,false), .last 36 (5,false), .last 46 (5,false)
  ], by decide⟩

def d456 : CheckedDeepTree :=
  ⟨decodeRows [8, 12, 10, 17, 15, 24, 7, 0, 15, 19, 0, 4], branchList 68 (5,false) [
    .last 71 (3,true), .last 78 (3,true), .last 74 (3,true), .openLeaf,
    .last 105 (3,true), .last 71 (3,true), .openLeaf, .last 175 (3,true),
    .side 67 2 true (1), .last 79 (3,true), .openLeaf, .last 108 (3,true),
    .last 69 (3,true), .last 69 (3,true), .last 69 (3,true), .last 69 (3,true),
    .last 95 (3,true), .last 71 (3,true), .last 98 (3,true), .last 100 (3,true),
    .last 181 (3,true), .last 72 (3,true), .last 110 (3,true), .last 72 (3,true)
  ], by decide⟩

def d457 : CheckedDeepTree :=
  ⟨decodeRows [8, 13, 10, 17, 15, 24, 7, 0, 15, 19, 0, 4], branchList 21 (3,true) [
    .last 26 (5,false), .last 31 (5,false), .last 26 (5,false), .side 10 12 false (1),
    .side 13 20 false (-1), .side 3 28 false (2), .side 4 18 false (1), .last 44 (5,false),
    .last 23 (5,false), .side 2 20 false (2), .side 8 14 false (1), .last 31 (5,false),
    .last 26 (5,false), .last 31 (5,false), .side 16 7 false (-2), .side 14 10 false (-2),
    .side 14 8 false (-2), .side 3 20 false (1), .side 14 8 false (-2), .side 12 12 false (0),
    .last 50 (5,false), .last 22 (5,false), .last 25 (5,false), .last 22 (5,false)
  ], by decide⟩

def d458 : CheckedDeepTree :=
  ⟨decodeRows [8, 14, 10, 17, 15, 24, 7, 0, 15, 19, 0, 4], branchList 21 (3,true) [
    .last 25 (5,false), .last 90 (5,false), .side 10 12 false (1), .last 47 (5,false),
    .last 74 (5,false), .last 41 (5,false), .side 4 28 false (2), .last 38 (5,false),
    .last 25 (5,false), .last 23 (5,false), .side 18 6 true (-4), .last 23 (5,false),
    .last 46 (5,false), .last 49 (5,false), .side 16 27 false (0), .side 11 20 false (1),
    .openLeaf, .last 48 (5,false), .side 14 10 false (-1), .side 12 14 false (0),
    .last 22 (5,false), .last 64 (5,false), .last 22 (5,false), .last 46 (5,false)
  ], by decide⟩

def d459 : CheckedDeepTree :=
  ⟨decodeRows [8, 15, 10, 17, 15, 24, 7, 0, 15, 19, 0, 4], branchList 21 (3,true) [
    .side 6 17 false (1), .side 3 20 false (1), .side 16 7 false (-2), .side 20 2 true (-3),
    .last 55 (5,false), .last 80 (5,false), .side 4 18 false (1), .side 13 10 false (-1),
    .last 23 (5,false), .last 27 (5,false), .side 18 4 true (-4), .last 27 (5,false),
    .last 26 (5,false), .last 55 (5,false), .side 16 7 false (-2), .openLeaf,
    .side 14 8 false (-2), .side 14 11 false (-2), .side 14 8 false (-2), .side 12 10 false (0),
    .side 13 12 false (-1), .side 49 71 false (1), .last 25 (5,false), .openLeaf
  ], by decide⟩

def d460 : CheckedDeepTree :=
  ⟨decodeRows [8, 16, 10, 17, 15, 24, 7, 0, 15, 19, 0, 4], branchList 21 (3,true) [
    .side 13 12 false (-1), .side 3 35 false (1), .side 20 2 true (-2), .openLeaf,
    .side 13 10 false (-1), .last 57 (5,false), .side 13 10 false (-1), .side 12 12 false (0),
    .last 23 (5,false), .last 23 (5,false), .openLeaf, .last 23 (5,false),
    .last 28 (5,false), .side 16 56 true (-7), .side 16 9 false (-1), .openLeaf,
    .side 12 10 false (0), .side 14 17 false (0), .side 12 10 false (0), .side 12 12 false (0),
    .side 12 14 false (0), .last 32 (5,false), .openLeaf, .last 68 (5,false)
  ], by decide⟩

def d462 : CheckedDeepTree :=
  ⟨decodeRows [8, 18, 10, 17, 15, 24, 7, 0, 15, 19, 0, 4], branchList 23 (3,true) [
    .side 15 10 true (-5), .side 3 24 false (1), .side 14 11 false (-1), .side 20 4 true (-3),
    .side 41 10 false (-5), .last 84 (5,false), .side 4 20 false (1), .side 13 12 false (-1),
    .last 25 (5,false), .side 8 25 false (1), .side 18 6 true (-4), .side 11 18 false (1),
    .last 28 (5,false), .last 86 (5,false), .side 16 9 false (-1), .openLeaf,
    .side 24 10 false (-3), .side 14 13 false (-1), .side 14 10 false (-1), .side 12 12 false (0),
    .side 13 14 false (-1), .side 3 32 false (1), .last 29 (5,false), .side 11 22 false (1)
  ], by decide⟩

def d466 : CheckedDeepTree :=
  ⟨decodeRows [8, 22, 10, 17, 15, 24, 7, 0, 15, 19, 0, 4], branchList 23 (5,false) [
    .last 36 (3,true), .last 45 (3,true), .last 29 (3,true), .last 33 (3,true),
    .last 29 (3,true), .last 29 (3,true), .last 35 (3,true), .last 27 (3,true),
    .last 25 (3,true), .last 33 (3,true), .last 25 (3,true), .last 27 (3,true),
    .last 27 (3,true), .last 24 (3,true), .last 27 (3,true), .last 24 (3,true),
    .last 25 (3,true), .last 29 (3,true), .last 25 (3,true), .last 27 (3,true),
    .last 38 (3,true), .last 35 (3,true), .last 41 (3,true), .last 33 (3,true)
  ], by decide⟩

def d468 : CheckedDeepTree :=
  ⟨decodeRows [8, 24, 10, 17, 15, 24, 7, 0, 15, 19, 0, 4], branchList 23 (5,false) [
    .side 22 2 true (0), .last 32 (3,true), .openLeaf, .openLeaf,
    .last 44 (3,true), .last 26 (3,true), .openLeaf, .openLeaf,
    .side 23 2 true (0), .last 30 (3,true), .openLeaf, .last 27 (3,true),
    .last 24 (3,true), .last 24 (3,true), .last 24 (3,true), .last 24 (3,true),
    .openLeaf, .last 26 (3,true), .openLeaf, .last 45 (3,true),
    .openLeaf, .last 32 (3,true), .side 54 3 true (4), .side 52 1 true (6)
  ], by decide⟩

def d604 : CheckedDeepTree :=
  ⟨decodeRows [8, 1, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 53 (3,true) [
    .openLeaf, .openLeaf, .last 157 (5,true), .last 85 (5,true),
    .openLeaf, .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .openLeaf, .openLeaf, .last 56 (5,true),
    .openLeaf, .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .openLeaf, .openLeaf, .side 49 6 true (-1),
    .last 54 (5,true), .last 82 (5,true), .last 54 (5,true), .openLeaf
  ], by decide⟩

def d607 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 57 (5,true) [
    .last 75 (3,true), .side 51 7 true (3), .side 49 9 true (1), .side 51 7 true (3),
    .side 31 35 true (-1), .side 33 25 true (0), .side 32 27 true (0), .side 19 59 true (-1),
    .last 59 (3,true), .last 61 (3,true), .last 59 (3,true), .last 59 (3,true),
    .last 58 (3,true), .last 58 (3,true), .last 58 (3,true), .last 58 (3,true),
    .side 31 39 true (-1), .side 47 11 true (1), .side 163 48 true (3), .side 56 2 true (3),
    .last 66 (3,true), .side 37 23 true (1), .side 114 33 true (2), .last 66 (3,true)
  ], by decide⟩

def d608 : CheckedDeepTree :=
  ⟨decodeRows [8, 5, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 52 (3,true) [
    .openLeaf, .openLeaf, .last 58 (5,true), .last 58 (5,true),
    .openLeaf, .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .openLeaf, .openLeaf, .openLeaf,
    .last 323 (5,true), .openLeaf, .openLeaf, .openLeaf
  ], by decide⟩

def d610 : CheckedDeepTree :=
  ⟨decodeRows [8, 7, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 52 (3,true) [
    .side 90 24 true (0), .side 53 24 true (-1), .last 58 (5,true), .side 53 24 true (-1),
    .side 92 24 true (0), .side 58 24 true (0), .side 80 24 true (0), .side 82 24 true (0),
    .side 88 24 true (0), .side 53 24 true (-2), .side 70 24 true (0), .side 70 24 true (0),
    .side 92 24 true (0), .side 58 24 true (0), .side 80 24 true (0), .side 82 24 true (0),
    .side 84 24 true (0), .side 60 24 true (0), .side 82 24 true (0), .side 84 24 true (0),
    .side 80 24 true (0), .side 56 24 true (0), .side 68 24 true (0), .side 78 24 true (0)
  ], by decide⟩

def d612 : CheckedDeepTree :=
  ⟨decodeRows [8, 10, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 54 (5,true) [
    .last 58 (3,true), .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .openLeaf, .openLeaf, .last 56 (3,true),
    .openLeaf, .last 55 (3,true), .openLeaf, .last 55 (3,true),
    .openLeaf, .openLeaf, .openLeaf, .side 53 2 true (-2),
    .openLeaf, .openLeaf, .openLeaf, .openLeaf
  ], by decide⟩

def d613 : CheckedDeepTree :=
  ⟨decodeRows [8, 11, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 52 (5,true) [
    .last 56 (3,true), .side 75 22 true (1), .side 61 22 true (1), .side 87 22 true (1),
    .side 85 22 true (1), .side 59 22 true (1), .side 81 22 true (1), .side 71 22 true (1),
    .side 87 22 true (1), .side 97 22 true (1), .side 71 22 true (1), .last 54 (3,true),
    .side 85 22 true (1), .last 53 (3,true), .side 81 22 true (1), .last 53 (3,true),
    .side 73 22 true (1), .side 63 22 true (1), .side 73 22 true (1), .side 51 2 true (-2),
    .side 71 22 true (1), .side 57 22 true (1), .side 67 22 true (1), .side 85 22 true (1)
  ], by decide⟩

def d614 : CheckedDeepTree :=
  ⟨decodeRows [8, 12, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 51 (3,true) [
    .openLeaf, .side 6 46 true (-4), .last 57 (5,true), .last 57 (5,true),
    .openLeaf, .side 31 24 true (-1), .openLeaf, .openLeaf,
    .last 54 (5,true), .side 4 48 true (-4), .last 54 (5,true), .last 60 (5,true),
    .openLeaf, .side 31 24 true (-1), .openLeaf, .openLeaf,
    .openLeaf, .side 28 26 true (-1), .openLeaf, .side 46 8 true (1),
    .last 56 (5,true), .side 30 22 true (-1), .last 56 (5,true), .side 48 4 true (1)
  ], by decide⟩

def d615 : CheckedDeepTree :=
  ⟨decodeRows [8, 13, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 52 (3,true) [
    .openLeaf, .openLeaf, .last 58 (5,true), .last 58 (5,true),
    .openLeaf, .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .openLeaf, .openLeaf, .openLeaf
  ], by decide⟩

def d616 : CheckedDeepTree :=
  ⟨decodeRows [8, 14, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 50 (3,true) [
    .openLeaf, .side 35 18 true (0), .side 31 20 true (-1), .side 9 44 true (-4),
    .last 54 (5,true), .side 33 18 true (0), .last 54 (5,true), .side 7 44 true (-4),
    .openLeaf, .openLeaf, .side 31 22 true (-1), .side 105 19 false (-1),
    .last 54 (5,true), .side 35 18 true (0), .last 54 (5,true), .last 60 (5,true),
    .side 5 46 true (-4), .side 29 22 true (-1), .side 35 22 true (0), .last 52 (5,true),
    .last 57 (5,true), .last 51 (5,true), .side 32 22 true (0), .last 51 (5,true)
  ], by decide⟩

def d617 : CheckedDeepTree :=
  ⟨decodeRows [8, 15, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 52 (3,true) [
    .side 90 24 true (0), .side 53 24 true (-1), .last 58 (5,true), .side 53 24 true (-1),
    .side 92 24 true (0), .side 58 24 true (0), .side 80 24 true (0), .side 82 24 true (0),
    .side 88 24 true (0), .side 53 24 true (-2), .side 70 24 true (0), .side 70 24 true (0),
    .side 92 24 true (0), .side 58 24 true (0), .side 80 24 true (0), .side 82 24 true (0),
    .side 84 24 true (0), .side 60 24 true (0), .side 82 24 true (0), .side 84 24 true (0),
    .side 80 24 true (0), .side 56 24 true (0), .side 68 24 true (0), .side 78 24 true (0)
  ], by decide⟩

def d618 : CheckedDeepTree :=
  ⟨decodeRows [8, 16, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 50 (3,true) [
    .openLeaf, .side 13 60 true (-3), .side 49 2 true (1), .side 37 18 true (1),
    .side 31 24 true (-1), .side 33 18 true (0), .side 32 20 true (0), .last 55 (5,true),
    .openLeaf, .side 4 72 true (-4), .openLeaf, .last 55 (5,true),
    .openLeaf, .side 35 18 true (0), .side 82 26 true (0), .openLeaf,
    .last 56 (5,true), .side 47 4 true (1), .last 56 (5,true), .last 52 (5,true),
    .last 51 (5,true), .last 51 (5,true), .last 51 (5,true), .last 51 (5,true)
  ], by decide⟩

def d622 : CheckedDeepTree :=
  ⟨decodeRows [8, 20, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 51 (5,true) [
    .last 55 (3,true), .side 31 98 true (-1), .side 32 22 true (0), .last 66 (3,true),
    .last 54 (3,true), .side 32 20 true (0), .last 54 (3,true), .side 32 20 true (0),
    .last 237 (3,true), .openLeaf, .side 73 24 true (1), .last 53 (3,true),
    .last 54 (3,true), .last 52 (3,true), .last 54 (3,true), .last 52 (3,true),
    .side 31 22 true (-1), .side 32 24 true (0), .side 49 4 true (0), .side 50 2 true (1),
    .openLeaf, .side 37 18 true (1), .side 68 24 true (0), .side 58 5 true (4)
  ], by decide⟩

def d623 : CheckedDeepTree :=
  ⟨decodeRows [8, 21, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 52 (5,true) [
    .last 56 (3,true), .openLeaf, .openLeaf, .last 64 (3,true),
    .openLeaf, .openLeaf, .openLeaf, .last 195 (3,true),
    .openLeaf, .openLeaf, .openLeaf, .last 112 (3,true),
    .openLeaf, .last 89 (3,true), .openLeaf, .last 113 (3,true),
    .last 201 (3,true), .openLeaf, .openLeaf, .side 97 2 true (-6),
    .openLeaf, .openLeaf, .openLeaf, .openLeaf
  ], by decide⟩

def d624 : CheckedDeepTree :=
  ⟨decodeRows [8, 22, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 50 (5,true) [
    .last 56 (3,true), .side 37 16 true (1), .side 31 20 true (-1), .side 37 16 true (1),
    .openLeaf, .side 33 18 true (0), .side 83 24 true (1), .side 7 44 true (-4),
    .last 58 (3,true), .openLeaf, .side 31 22 true (-1), .last 52 (3,true),
    .openLeaf, .last 51 (3,true), .side 83 24 true (1), .last 51 (3,true),
    .side 5 46 true (-4), .side 29 22 true (-1), .side 37 20 true (1), .side 50 2 true (2),
    .openLeaf, .side 37 16 true (1), .side 32 22 true (0), .side 55 3 true (5)
  ], by decide⟩

def d625 : CheckedDeepTree :=
  ⟨decodeRows [8, 23, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 52 (5,true) [
    .last 56 (3,true), .side 58 22 true (0), .side 56 22 true (0), .side 51 2 true (-2),
    .side 80 22 true (0), .side 54 22 true (0), .side 76 22 true (0), .side 54 22 true (0),
    .side 82 22 true (0), .side 72 22 true (0), .side 66 22 true (0), .last 54 (3,true),
    .side 80 22 true (0), .last 53 (3,true), .side 76 22 true (0), .last 53 (3,true),
    .side 56 22 true (0), .side 58 22 true (0), .side 64 22 true (0), .side 52 2 true (-2),
    .side 66 22 true (0), .side 59 22 true (1), .side 62 22 true (0), .side 61 5 true (3)
  ], by decide⟩

def d626 : CheckedDeepTree :=
  ⟨decodeRows [8, 24, 11, 6, 17, 13, 11, 0, 2, 23, 3, 0], branchList 50 (5,true) [
    .side 48 4 true (1), .last 70 (3,true), .side 49 2 true (1), .last 62 (3,true),
    .side 31 24 true (-1), .side 33 18 true (0), .side 32 20 true (0), .side 100 64 true (0),
    .last 54 (3,true), .last 56 (3,true), .last 54 (3,true), .last 52 (3,true),
    .last 51 (3,true), .last 51 (3,true), .last 51 (3,true), .last 51 (3,true),
    .openLeaf, .side 47 4 true (1), .side 72 24 true (0), .side 50 2 true (2),
    .side 55 32 false (-1), .side 37 16 true (1), .side 68 24 true (0), .side 55 3 true (5)
  ], by decide⟩

def d800 : CheckedDeepTree :=
  ⟨decodeRows [8, 2, 12, 9, 13, 21, 4, 19, 15, 5, 0, 0], branchList 15 (5,false) [
    .side 16 8 false (0), .openLeaf, .last 19 (5,true), .side 16 40 false (2),
    .side 1 15 false (2), .last 77 (5,true), .last 18 (5,true), .side 1 19 false (2),
    .side 16 34 false (0), .side 16 42 false (2), .side 6 10 false (1), .openLeaf,
    .side 25 8 false (-2), .last 37 (5,true), .side 23 8 false (0), .last 29 (5,true),
    .side 3 37 false (1), .last 49 (5,true), .openLeaf, .side 0 27 true (-5),
    .last 17 (5,true), .side 15 1 true (-1), .last 17 (5,true), .side 15 1 true (-1)
  ], by decide⟩

def d801 : CheckedDeepTree :=
  ⟨decodeRows [8, 2, 12, 9, 13, 22, 4, 19, 15, 5, 0, 0], branchList 15 (5,false) [
    .openLeaf, .side 0 16 true (-3), .side 12 4 true (0), .side 132 36 true (0),
    .side 93 26 false (-2), .side 10 27 true (-2), .side 14 3 true (0), .side 1 15 true (-3),
    .side 16 42 false (2), .side 144 40 true (0), .openLeaf, .side 38 26 true (-2),
    .side 41 14 true (0), .side 42 22 true (0), .openLeaf, .side 162 8 false (-2),
    .side 22 29 false (2), .side 10 47 true (-2), .side 36 24 true (-2), .side 0 23 true (-3),
    .last 19 (5,true), .side 15 1 true (1), .last 19 (5,true), .side 15 1 true (1)
  ], by decide⟩

def d802 : CheckedDeepTree :=
  ⟨decodeRows [8, 2, 12, 9, 13, 23, 4, 19, 15, 5, 0, 0], branchList 15 (5,false) [
    .last 19 (5,true), .side 0 17 true (-3), .last 19 (5,true), .last 45 (5,true),
    .side 1 15 false (2), .side 27 8 false (-2), .last 18 (5,true), .last 21 (5,true),
    .last 25 (5,true), .side 14 2 true (-1), .side 6 10 false (1), .last 17 (5,true),
    .last 20 (5,true), .last 69 (5,true), .last 61 (5,true), .side 1 17 false (2),
    .side 34 8 false (-4), .openLeaf, .side 0 25 true (-5), .side 16 36 false (0),
    .last 17 (5,true), .last 16 (5,true), .last 17 (5,true), .last 16 (5,true)
  ], by decide⟩

def d923 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 12, 0, 13, 2, 24, 19, 0, 23, 11, 1], branchList 22 (1,true) [
    .side 13 13 true (0), .side 23 10 true (2), .side 11 12 true (-1), .side 13 10 true (0),
    .last 30 (4,false), .last 27 (4,false), .openLeaf, .side 15 9 true (0),
    .side 0 50 true (-3), .side 40 10 true (4), .side 12 12 true (0), .side 11 20 true (-1),
    .side 95 25 true (2), .last 24 (4,false), .openLeaf, .side 17 6 true (0),
    .side 62 32 true (-2), .side 12 14 true (0), .side 9 28 true (-3), .last 28 (4,false),
    .side 11 24 true (-1), .side 14 10 true (0), .side 19 4 true (0), .side 13 11 true (0)
  ], by decide⟩

def d927 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 12, 0, 13, 2, 24, 19, 0, 23, 11, 5], branchList 20 (1,true) [
    .side 20 69 true (-2), .openLeaf, .side 11 14 true (-1), .side 13 10 true (0),
    .last 26 (4,false), .last 45 (4,false), .side 9 24 true (-3), .side 15 27 true (-1),
    .last 74 (4,false), .side 11 14 true (-1), .last 37 (4,false), .last 28 (4,false),
    .last 54 (4,false), .last 40 (4,false), .side 17 18 false (3), .side 11 41 true (-1),
    .last 26 (4,false), .last 21 (4,false), .last 26 (4,false), .last 21 (4,false),
    .side 84 30 false (1), .side 15 22 false (4), .side 19 14 false (1), .side 11 12 true (-1)
  ], by decide⟩

def d928 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 12, 0, 13, 2, 24, 19, 0, 23, 11, 6], branchList 20 (1,true) [
    .side 11 20 true (-1), .side 13 8 true (1), .side 11 12 true (-1), .side 13 8 true (1),
    .last 50 (4,false), .last 25 (4,false), .side 13 10 true (1), .side 15 7 true (1),
    .side 46 28 true (0), .side 0 22 true (-3), .last 47 (4,false), .side 11 18 true (-1),
    .side 12 12 true (0), .last 22 (4,false), .last 29 (4,false), .side 11 14 true (-1),
    .last 21 (4,false), .last 55 (4,false), .last 21 (4,false), .last 24 (4,false),
    .last 30 (4,false), .last 25 (4,false), .side 11 12 true (-1), .last 25 (4,false)
  ], by decide⟩

def d929 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 12, 0, 13, 2, 24, 19, 0, 23, 11, 7], branchList 20 (1,true) [
    .side 13 17 true (-1), .side 11 10 true (-1), .side 10 12 true (-2), .side 11 10 true (-1),
    .last 26 (4,false), .last 27 (4,false), .openLeaf, .side 15 9 true (0),
    .side 0 31 true (-3), .side 12 10 true (0), .side 9 12 true (-3), .side 12 10 true (0),
    .last 39 (4,false), .last 22 (4,false), .openLeaf, .openLeaf,
    .last 64 (4,false), .side 8 14 true (-3), .last 40 (4,false), .openLeaf,
    .side 95 35 true (-1), .side 12 12 true (0), .openLeaf, .side 19 2 true (0)
  ], by decide⟩

def d930 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 12, 0, 13, 2, 24, 19, 0, 23, 11, 8], branchList 20 (1,true) [
    .side 13 11 true (1), .side 13 8 true (1), .side 11 10 true (-1), .side 13 8 true (1),
    .last 28 (4,false), .last 25 (4,false), .openLeaf, .side 15 7 true (1),
    .last 64 (4,false), .last 54 (4,false), .side 12 10 true (0), .side 11 18 true (-1),
    .last 47 (4,false), .last 22 (4,false), .openLeaf, .side 17 4 true (1),
    .side 21 22 false (1), .side 12 12 true (0), .openLeaf, .last 24 (4,false),
    .side 11 20 true (-1), .side 11 17 true (-1), .side 19 2 true (1), .side 15 7 true (1)
  ], by decide⟩

def d931 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 12, 0, 13, 2, 24, 19, 0, 23, 11, 9], branchList 22 (1,true) [
    .side 13 13 true (0), .last 32 (4,false), .side 11 12 true (-1), .side 13 10 true (0),
    .last 41 (4,false), .last 27 (4,false), .side 12 14 true (0), .side 15 9 true (0),
    .side 0 27 true (-3), .last 32 (4,false), .side 12 12 true (0), .side 11 20 true (-1),
    .last 24 (4,false), .last 24 (4,false), .last 24 (4,false), .openLeaf,
    .last 39 (4,false), .side 12 14 true (0), .side 8 16 true (-3), .last 28 (4,false),
    .side 2 22 false (4), .last 26 (4,false), .openLeaf, .side 11 21 true (-1)
  ], by decide⟩

def d935 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 12, 0, 13, 2, 24, 19, 0, 23, 11, 13], branchList 30 (1,true) [
    .last 45 (4,false), .side 24 28 true (-3), .openLeaf, .openLeaf,
    .last 38 (4,false), .last 35 (4,false), .last 52 (4,false), .last 41 (4,false),
    .side 0 60 true (-3), .last 43 (4,false), .last 41 (4,false), .side 24 26 true (-3),
    .last 35 (4,false), .last 32 (4,false), .last 35 (4,false), .side 17 14 true (-3),
    .side 18 28 false (2), .last 43 (4,false), .side 18 28 false (2), .last 37 (4,false),
    .side 24 38 true (-3), .side 24 32 true (-3), .side 19 12 true (-3), .side 17 32 false (3)
  ], by decide⟩

def d936 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 12, 0, 13, 2, 24, 19, 0, 23, 11, 14], branchList 21 (4,false) [
    .last 24 (1,true), .side 12 10 true (0), .side 10 12 true (-2), .side 12 10 true (0),
    .last 22 (1,true), .last 22 (1,true), .last 22 (1,true), .last 22 (1,true),
    .last 24 (1,true), .side 13 10 true (1), .side 11 12 true (-1), .side 13 10 true (1),
    .last 34 (1,true), .side 20 2 true (1), .side 25 6 false (-1), .openLeaf,
    .last 36 (1,true), .side 11 14 true (-1), .openLeaf, .side 18 4 true (1),
    .last 50 (1,true), .side 13 16 true (1), .openLeaf, .side 13 16 true (1)
  ], by decide⟩

def d937 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 12, 0, 13, 2, 24, 19, 0, 23, 11, 15], branchList 26 (4,false) [
    .openLeaf, .openLeaf, .last 28 (1,true), .openLeaf,
    .side 25 4 false (-3), .last 27 (1,true), .openLeaf, .last 27 (1,true),
    .last 33 (1,true), .openLeaf, .openLeaf, .openLeaf,
    .openLeaf, .side 25 2 true (-4), .side 23 4 false (-2), .openLeaf,
    .side 26 1 false (-4), .openLeaf, .side 26 1 false (-4), .side 21 6 false (-1),
    .last 35 (1,true), .side 22 5 false (-2), .openLeaf, .side 24 3 false (-2)
  ], by decide⟩

def d939 : CheckedDeepTree :=
  ⟨decodeRows [8, 4, 12, 0, 13, 2, 24, 19, 0, 23, 11, 17], branchList 32 (1,true) [
    .last 44 (4,false), .last 42 (4,false), .openLeaf, .openLeaf,
    .last 40 (4,false), .last 42 (4,false), .side 27 52 true (-5), .last 42 (4,false),
    .last 44 (4,false), .last 48 (4,false), .side 34 16 true (0), .last 39 (4,false),
    .side 20 14 false (0), .last 52 (4,false), .side 20 14 false (0), .last 41 (4,false),
    .last 37 (4,false), .last 33 (4,false), .last 37 (4,false), .last 33 (4,false),
    .side 19 14 false (1), .last 50 (4,false), .side 19 14 false (1), .last 46 (4,false)
  ], by decide⟩

def d1071 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 1, 1], branchList 22 (0,true) [
    .last 27 (4,false), .side 7 17 true (-1), .side 26 10 false (0), .side 22 4 true (2),
    .side 20 25 false (4), .side 10 13 true (0), .side 10 15 true (0), .side 10 13 true (0),
    .openLeaf, .last 25 (4,false), .last 25 (4,false), .last 25 (4,false),
    .last 41 (4,false), .side 20 15 false (4), .openLeaf, .openLeaf,
    .last 23 (4,false), .last 23 (4,false), .last 23 (4,false), .last 23 (4,false),
    .last 43 (4,false), .side 9 15 true (-1), .openLeaf, .side 21 2 true (2)
  ], by decide⟩

def d1072 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 2, 1], branchList 22 (0,true) [
    .last 27 (4,false), .side 12 15 true (2), .side 26 14 false (2), .side 22 4 true (4),
    .side 1 38 true (-1), .side 12 11 true (2), .side 10 13 true (0), .side 12 11 true (2),
    .openLeaf, .last 25 (4,false), .last 25 (4,false), .last 25 (4,false),
    .side 23 17 false (3), .side 23 29 false (5), .openLeaf, .side 17 6 true (3),
    .last 23 (4,false), .last 23 (4,false), .last 23 (4,false), .last 23 (4,false),
    .side 12 13 true (2), .side 0 26 true (-1), .side 21 2 true (3), .side 0 26 true (-1)
  ], by decide⟩

def d1073 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 3, 1], branchList 22 (0,true) [
    .side 20 64 false (4), .side 12 17 true (2), .side 26 10 false (0), .side 24 4 true (4),
    .side 20 17 false (4), .side 42 14 false (2), .side 28 11 false (1), .side 26 8 true (1),
    .side 20 15 false (4), .side 54 21 false (2), .side 26 12 false (2), .side 20 4 true (2),
    .side 18 15 false (5), .side 33 18 false (0), .side 20 13 false (4), .last 33 (4,false),
    .last 23 (4,false), .last 27 (4,false), .last 23 (4,false), .openLeaf,
    .last 30 (4,false), .side 8 15 true (-1), .side 23 7 false (1), .side 21 4 true (2)
  ], by decide⟩

def d1074 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 4, 1], branchList 22 (0,true) [
    .side 20 30 false (4), .side 12 15 true (2), .side 28 12 false (0), .side 22 4 true (4),
    .last 31 (4,false), .side 12 11 true (2), .side 62 3 false (-2), .side 12 11 true (2),
    .last 27 (4,false), .last 25 (4,false), .side 20 4 true (3), .last 25 (4,false),
    .last 24 (4,false), .side 3 34 true (-1), .last 33 (4,false), .openLeaf,
    .side 23 15 false (3), .last 23 (4,false), .openLeaf, .last 23 (4,false),
    .last 91 (4,false), .side 21 15 true (3), .openLeaf, .side 21 15 true (3)
  ], by decide⟩

def d1078 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 8, 1], branchList 24 (0,true) [
    .last 29 (4,false), .side 7 19 true (-1), .side 26 12 false (2), .side 22 4 true (2),
    .side 20 29 false (4), .side 10 15 true (0), .side 10 17 true (0), .side 10 15 true (0),
    .openLeaf, .last 27 (4,false), .last 27 (4,false), .last 27 (4,false),
    .last 45 (4,false), .side 20 17 false (4), .openLeaf, .openLeaf,
    .last 25 (4,false), .last 25 (4,false), .last 25 (4,false), .last 25 (4,false),
    .last 29 (4,false), .side 7 19 true (-1), .openLeaf, .side 21 4 true (2)
  ], by decide⟩

def d1083 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 13, 1], branchList 23 (4,false) [
    .last 24 (0,true), .last 24 (0,true), .last 24 (0,true), .last 24 (0,true),
    .openLeaf, .side 20 4 true (2), .side 24 9 false (2), .last 26 (0,true),
    .side 10 15 true (0), .side 11 13 true (1), .side 18 19 false (5), .side 11 13 true (1),
    .side 22 2 true (2), .side 16 12 true (2), .openLeaf, .last 33 (0,true),
    .last 33 (0,true), .side 1 42 true (-1), .side 20 21 false (4), .side 33 1 true (7),
    .last 46 (0,true), .last 48 (0,true), .last 33 (0,true), .last 25 (0,true)
  ], by decide⟩

def d1084 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 14, 1], branchList 23 (4,false) [
    .last 24 (0,true), .last 24 (0,true), .last 24 (0,true), .last 24 (0,true),
    .side 20 4 true (3), .side 14 14 true (3), .side 18 8 true (3), .last 26 (0,true),
    .side 11 13 true (1), .side 13 11 true (3), .side 29 5 true (4), .side 13 11 true (3),
    .side 22 2 true (4), .side 16 10 true (3), .side 18 6 true (3), .last 31 (0,true),
    .side 1 42 true (-1), .side 1 24 true (-1), .side 31 5 true (4), .side 12 16 true (2),
    .last 40 (0,true), .last 34 (0,true), .side 12 22 true (2), .last 25 (0,true)
  ], by decide⟩

def d1086 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 16, 1], branchList 23 (4,false) [
    .last 24 (0,true), .last 24 (0,true), .last 24 (0,true), .last 24 (0,true),
    .last 26 (0,true), .side 14 14 true (3), .last 26 (0,true), .last 26 (0,true),
    .side 11 13 true (1), .side 13 11 true (3), .last 31 (0,true), .side 13 11 true (3),
    .side 22 2 true (4), .side 16 10 true (3), .last 28 (0,true), .last 31 (0,true),
    .side 1 34 true (-1), .last 33 (0,true), .side 6 30 true (-1), .last 27 (0,true),
    .last 25 (0,true), .last 34 (0,true), .last 25 (0,true), .last 25 (0,true)
  ], by decide⟩

def d1089 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 20, 1], branchList 31 (4,false) [
    .last 32 (0,true), .side 0 32 true (-1), .last 32 (0,true), .last 41 (0,true),
    .last 51 (0,true), .side 14 18 true (1), .side 6 28 true (-1), .last 40 (0,true),
    .last 61 (0,true), .last 69 (0,true), .last 55 (0,true), .side 2 30 true (-1),
    .side 30 2 true (6), .side 16 16 true (1), .last 53 (0,true), .last 51 (0,true),
    .side 1 32 true (-1), .side 31 1 true (7), .side 28 5 true (4), .side 31 1 true (7),
    .last 42 (0,true), .side 31 2 true (7), .last 47 (0,true), .side 31 2 true (7)
  ], by decide⟩

def d1090 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 21, 1], branchList 27 (4,false) [
    .last 28 (0,true), .last 28 (0,true), .last 28 (0,true), .last 28 (0,true),
    .last 31 (0,true), .side 14 22 true (1), .last 31 (0,true), .last 30 (0,true),
    .side 11 17 true (1), .last 48 (0,true), .last 33 (0,true), .last 38 (0,true),
    .side 26 2 true (4), .side 16 14 true (1), .last 33 (0,true), .last 35 (0,true),
    .last 37 (0,true), .side 1 28 true (-1), .last 36 (0,true), .last 43 (0,true),
    .last 44 (0,true), .last 38 (0,true), .last 35 (0,true), .last 29 (0,true)
  ], by decide⟩

def d1091 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 22, 1], branchList 27 (4,false) [
    .last 28 (0,true), .side 0 28 true (-1), .last 28 (0,true), .last 37 (0,true),
    .last 40 (0,true), .side 14 14 true (3), .side 12 20 true (2), .last 36 (0,true),
    .side 13 15 true (3), .last 54 (0,true), .side 0 32 true (-1), .side 2 26 true (-1),
    .side 26 2 true (6), .side 16 12 true (3), .last 42 (0,true), .side 12 22 true (2),
    .last 37 (0,true), .side 27 1 true (7), .side 24 5 true (4), .side 27 1 true (7),
    .last 38 (0,true), .side 28 1 true (8), .side 12 18 true (2), .side 28 1 true (8)
  ], by decide⟩

def d1092 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 23, 1], branchList 29 (0,true) [
    .side 20 64 false (4), .side 22 10 true (1), .side 20 30 false (4), .side 28 4 true (1),
    .side 18 19 false (5), .side 20 12 true (1), .side 54 1 false (-4), .side 24 6 true (1),
    .side 61 1 false (-1), .side 42 1 false (0), .last 43 (4,false), .side 40 13 false (2),
    .last 31 (4,false), .side 20 21 false (4), .side 18 21 false (5), .side 40 1 false (-2),
    .side 32 1 false (-2), .last 30 (4,false), .side 32 1 false (-2), .last 30 (4,false),
    .side 32 1 false (-2), .side 34 1 false (0), .side 32 1 false (-2), .side 33 9 false (1)
  ], by decide⟩

def d1093 : CheckedDeepTree :=
  ⟨decodeRows [8, 0, 12, 23, 14, 6, 15, 20, 0, 5, 24, 1], branchList 23 (0,true) [
    .side 20 30 false (4), .side 12 13 true (2), .side 28 12 false (0), .side 12 13 true (2),
    .side 24 15 false (3), .last 27 (4,false), .side 24 9 false (2), .last 27 (4,false),
    .side 98 1 false (-2), .side 25 35 false (5), .last 31 (4,false), .side 2 38 true (-1),
    .last 25 (4,false), .openLeaf, .side 24 17 false (3), .last 35 (4,false),
    .last 34 (4,false), .last 24 (4,false), .last 28 (4,false), .last 24 (4,false),
    .side 20 30 false (4), .side 28 1 true (6), .last 31 (4,false), .side 28 1 true (6)
  ], by decide⟩

def deepTrees : List CheckedDeepTree := [
  d88, d89, d90, d274, d277, d278, d280, d282,
  d285, d286, d287, d288, d290, d450, d453, d454,
  d456, d457, d458, d459, d460, d462, d466, d468,
  d604, d607, d608, d610, d612, d613, d614, d615,
  d616, d617, d618, d622, d623, d624, d625, d626,
  d800, d801, d802, d923, d927, d928, d929, d930,
  d931, d935, d936, d937, d939, d1071, d1072, d1073,
  d1074, d1078, d1083, d1084, d1086, d1089, d1090, d1091,
  d1092, d1093
]

/-- A matching checked tree replaces the cylinder by only its open leaves.
    Unmatched tables are retained unchanged. -/
def replaceDeep (t : PackedTable) : List PackedTable :=
  match deepTrees.find? (fun e => decide (e.table = t)) with
  | none => [t]
  | some e => e.tree.packedResiduals (unpackTable t)

theorem replaceDeep_sound (t : PackedTable) (m : Machine)
    (hm : compatible (unpackTable t) m) :
    WeightedBound 7014 m ∨ ∃ q ∈ replaceDeep t, compatible (unpackTable q) m := by
  cases he : deepTrees.find? (fun e => decide (e.table = t)) with
  | none => exact Or.inr ⟨t,by simp [replaceDeep,he],hm⟩
  | some e =>
    have hp : decide (e.table = t) = true :=
      List.find?_some (p := fun x : CheckedDeepTree => decide (x.table = t)) he
    have htable : e.table = t := of_decide_eq_true hp
    have hcheck : e.tree.check 7014 (unpackTable t) = true := by
      simpa only [htable] using e.checked
    simpa only [replaceDeep,he] using e.tree.packed_sound 7014 (unpackTable t) hcheck m hm

def deepSevenRoster : List PackedTable :=
  reducedSevenRoster.flatMap fun e => replaceDeep e.2

theorem deepSevenRoster_sound :
    ∀ m, compatible root m → WeightedBound 7014 m ∨
      ∃ q ∈ deepSevenRoster, compatible (unpackTable q) m := by
  intro m hm
  rcases reducedSevenRoster_sound m hm with hb | ⟨e,hmem,hcomp⟩
  · exact Or.inl hb
  · rcases replaceDeep_sound e.2 m hcomp with hb | ⟨q,hq,hqc⟩
    · exact Or.inl hb
    · exact Or.inr ⟨q,List.mem_flatMap.mpr ⟨e,hmem,hq⟩,hqc⟩

def deepOpenRoster : List PackedTable :=
  deepTrees.flatMap fun e => e.tree.packedResiduals (unpackTable e.table)
#eval deepTrees.length
#eval deepOpenRoster.length
#eval deepSevenRoster.length
#print axioms deepSevenRoster_sound
end BB6.Agent47SevenDeep
