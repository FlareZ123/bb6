import Std

namespace BB6Ledger

/-- The 12 transition slots are ordered A0,A1,B0,B1,...,F0,F1.
    Code 0 means halt, code 1+4q+2r+w means (write w,dir r,next q). -/
def position (order : List Nat) (originalState : Nat) : Nat :=
  (order.findIdx? (fun x => x == originalState)).getD 6

def remapCode (code : Nat) (order : List Nat) (mirror : Bool) : Nat :=
  if code == 0 then 0 else
    let x := code - 1
    let q := x / 4
    let r := (x / 2) % 2
    let w := x % 2
    let d := if mirror then 1-r else r
    1 + 4 * position order q + 2 * d + w

def remapTable (original order : List Nat) (mirror : Bool) : List Nat :=
  (List.range 6).flatMap (fun newState =>
    let oldState := order.getD newState 99
    [remapCode (original.getD (2*oldState) 99) order mirror,
     remapCode (original.getD (2*oldState+1) 99) order mirror])

def validOrder (order : List Nat) : Bool :=
  order.length == 6 && (List.range 6).all (fun x => order.count x == 1)

def validCodeTable (codes : List Nat) : Bool :=
  codes.length == 12 && codes.all (fun x => x ≤ 24)

def checkLedgerRow (original canonical order : List Nat)
    (mirror : Bool) (root : Nat) : Bool :=
  validOrder order && validCodeTable original && validCodeTable canonical &&
    remapTable original order mirror == canonical && position order 0 == root

/-- The independent numeric table witness checker verifies a source machine,
    canonical machine, reflection bit, renaming order, and translated root. -/
example : checkLedgerRow
    [8,24,10,6,16,14,20,3,0,5,21,11]
    [0,5,10,6,16,14,4,19,8,24,21,11]
    [4,1,2,3,0,5] false 4 = true := by decide

#print axioms checkLedgerRow
end BB6Ledger
