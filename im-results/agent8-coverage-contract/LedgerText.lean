import LedgerCheck

namespace BB6Ledger

private def readState : Char → Option Nat
  | 'A' => some 0
  | 'B' => some 1
  | 'C' => some 2
  | 'D' => some 3
  | 'E' => some 4
  | 'F' => some 5
  | _ => none

private def readWrite : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | _ => none

private def readDir : Char → Option Nat
  | 'L' => some 0
  | 'R' => some 1
  | _ => none

def parseTriple : List Char → Option Nat
  | ['-', '-', '-'] => some 0
  | [w, d, q] => do
    let w ← readWrite w
    let d ← readDir d
    let q ← readState q
    some (1 + 4*q + 2*d + w)
  | _ => none

def parseStateRow : List Char → Option (List Nat)
  | [w0,d0,q0,w1,d1,q1] => do
    let a ← parseTriple [w0,d0,q0]
    let b ← parseTriple [w1,d1,q1]
    some [a,b]
  | _ => none

/-- A deliberately kernel-reducible implementation, unlike String.splitOn,
    which the kernel cannot reduce over literal String values in this build. -/
def splitRows : List Char → List (List Char)
  | [] => [[]]
  | c::xs =>
    let rest := splitRows xs
    if c == '_' then [] :: rest else
      match rest with
      | [] => [[c]]
      | head::tail => (c::head)::tail

def parseMachine (s : String) : Option (List Nat) := do
  let lines := splitRows s.toList
  if lines.length != 6 then none else do
    let tokens ← lines.mapM (fun line => parseStateRow line)
    some tokens.flatten

def parseOrder (s : String) : Option (List Nat) := do
  let order ← s.toList.mapM readState
  if order.length == 6 then some order else none

def parseRoot (c : Char) : Option Nat := readState c

/-- End-to-end check of literal six-state RLE strings in the archived CSV;
    parsing is computed inside Lean, not trusted to a JS preprocessing step. -/
def checkRowText (original canonical order : String)
    (mirror : Bool) (root : Char) : Bool :=
  match parseMachine original, parseMachine canonical,
    parseOrder order, parseRoot root with
  | some a, some b, some c, some d => checkLedgerRow a b c mirror d
  | _, _, _, _ => false

example : checkRowText
    "1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC"
    "---0LB_1LC1LB_1RD1LD_1RA0RE_1RB1RF_0LF0RC"
    "EBCDAF" false 'E' = true := by decide

#print axioms checkRowText
end BB6Ledger
