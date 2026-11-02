import DExactTimes

namespace BB6.Portfolio

/-- Parse the compact canonical two-symbol BB machine notation's target state. -/
def parseState : Char → Option State
  | 'A' => some 0
  | 'B' => some 1
  | 'C' => some 2
  | 'D' => some 3
  | 'E' => some 4
  | 'F' => some 5
  | _ => none

/-- Extract one 3-character RLE transition, including the undefined halt. -/
def parseCell : List Char → Option Instruction
  | ['0','L',q] => (parseState q).map fun s => (false,.L,s)
  | ['0','R',q] => (parseState q).map fun s => (false,.R,s)
  | ['1','L',q] => (parseState q).map fun s => (true,.L,s)
  | ['1','R',q] => (parseState q).map fun s => (true,.R,s)
  | _ => none

/-- Fully checked parser of the six underscore-separated, two-column RLE. -/
def parseRLE (code : String) : Machine := fun s bit => Id.run do
  let chars := code.toList
  let offset := s.val*7 + if bit then 3 else 0
  parseCell ((chars.drop offset).take 3)

/-- The four table definitions used by the general conjugacy are identical
    to decoding their full original snapshot RLE strings. -/
theorem D0_parseRLE : ∀ s : State, ∀ b : Bool,
    parseRLE "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---" s b = D0 s b := by
  decide

theorem D1_parseRLE : ∀ s : State, ∀ b : Bool,
    parseRLE "1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA" s b = D1 s b := by
  decide

theorem D2_parseRLE : ∀ s : State, ∀ b : Bool,
    parseRLE "1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---" s b = D2 s b := by
  decide

theorem D3_parseRLE : ∀ s : State, ∀ b : Bool,
    parseRLE "1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---" s b = D3 s b := by
  decide

#print axioms D0_parseRLE
#print axioms D1_parseRLE
#print axioms D2_parseRLE
#print axioms D3_parseRLE
end BB6.Portfolio
