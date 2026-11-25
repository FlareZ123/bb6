import Canonical78Roster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent5Q0ParentMembership
open BB6Coverage
open BB6.Agent47Canonical78

def tm (w r : Bool) (q : Nat) : Option Move :=
  some ⟨w, r, ⟨q, by omega⟩⟩

def fromMoves (xs : List (Option Move)) : PartialMachine :=
  fun s => (xs.getD (s.1.val * 2 + (if s.2 then 1 else 0)) none).map some

def totalize (p : PartialMachine) : Machine :=
  fun s => (p s).getD none

def directMatches (p : PartialMachine) : List Nat :=
  (List.range roster.length).filter fun i =>
    match roster[i]? with
    | none => false
    | some e => decide (compatible e.2 (totalize p))

def directMatchAddresses (p : PartialMachine) : List (List Move) :=
  (directMatches p).filterMap fun i => (roster[i]?).map Prod.fst

def q0_0 : PartialMachine := fromMoves [
  tm true true 1, tm true true 3,
  tm true true 2, tm false false 3,
  tm false false 0, tm false true 4,
  tm true false 0, tm true false 1,
  tm false true 5, none,
  tm false false 0, tm true true 0
]

def q0_300 : PartialMachine := fromMoves [
  tm true true 1, tm false false 2,
  tm true true 2, tm true true 4,
  tm true false 0, tm false false 3,
  tm false true 0, tm false false 1,
  tm false true 5, none,
  tm false true 1, tm true true 0
]

def q0_400a : PartialMachine := fromMoves [
  tm true true 1, none,
  tm true true 2, tm true true 3,
  tm false false 1, tm false true 5,
  tm false false 4, tm true false 3,
  tm false false 2, tm true false 1,
  tm false true 0, tm false true 5
]

def q0_400b : PartialMachine := fromMoves [
  tm true true 1, tm true false 0,
  tm true true 2, tm true true 3,
  tm false false 1, tm false true 4,
  tm false false 4, tm false true 5,
  none, tm true false 0,
  tm true true 0, tm true true 2
]

def q0_600 : PartialMachine := fromMoves [
  tm true true 1, tm true false 4,
  tm true true 2, tm false true 3,
  tm true false 1, tm false true 4,
  tm true true 5, tm false false 4,
  tm false false 0, tm false false 1,
  none, tm false true 0
]

def q0_700 : PartialMachine := fromMoves [
  tm true true 1, tm false true 0,
  tm true true 2, tm true false 1,
  tm true false 1, tm false false 3,
  tm false false 4, tm false false 3,
  tm true true 4, tm true true 5,
  none, tm true true 0
]

def q0_2700 : PartialMachine := fromMoves [
  tm true true 1, tm false false 3,
  tm true false 2, tm true true 0,
  tm true false 4, tm true false 0,
  none, tm false true 1,
  tm true true 4, tm false true 5,
  tm true true 5, tm false false 2
]

def q0_2800 : PartialMachine := fromMoves [
  tm true true 1, tm false false 3,
  tm true false 2, tm true false 1,
  tm false false 4, tm true true 0,
  tm false false 2, tm false true 0,
  tm true true 5, tm true false 3,
  tm true false 3, none
]

def q0_3500 : PartialMachine := fromMoves [
  tm true true 1, tm false true 2,
  tm true false 2, tm true true 3,
  none, tm true true 1,
  tm false false 3, tm false true 4,
  tm true false 4, tm false true 5,
  tm true true 0, tm true true 5
]

#eval directMatches q0_0
#eval directMatchAddresses q0_0
#eval directMatches q0_300
#eval directMatchAddresses q0_300
#eval directMatches q0_400a
#eval directMatchAddresses q0_400a
#eval directMatches q0_400b
#eval directMatchAddresses q0_400b
#eval directMatches q0_600
#eval directMatchAddresses q0_600
#eval directMatches q0_700
#eval directMatchAddresses q0_700
#eval directMatches q0_2700
#eval directMatchAddresses q0_2700
#eval directMatches q0_2800
#eval directMatchAddresses q0_2800
#eval directMatches q0_3500
#eval directMatchAddresses q0_3500

end BB6.Agent5Q0ParentMembership
