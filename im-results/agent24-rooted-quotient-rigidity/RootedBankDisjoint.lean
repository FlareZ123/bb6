import RootedLiveQuotient
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Agent24BankDisjoint

/-- The format contains exactly six 2-symbol rows. Underscores are optional,
    so both source-backed q32 and compact q0 exports can be decoded. -/
def unpack (text : String) : List Char := text.toList.filter (· != '_')

def stateChar : Char → Option (Fin 6)
  | 'A' => some 0 | 'B' => some 1 | 'C' => some 2
  | 'D' => some 3 | 'E' => some 4 | 'F' => some 5
  | _ => none

def cell (raw : List Char) : Option (Option (RootedLiveQuotient.Move (Fin 6))) :=
  match raw with
  | ['-','-','-'] => none
  | [w,d,q] =>
      if (w == '0' || w == '1') && (d == 'L' || d == 'R') then
        (stateChar q).map (fun s => some ⟨w == '1', d == 'R', s⟩)
      else none
  | _ => none

def parse (text : String) : RootedLiveQuotient.PartialTable (Fin 6) :=
  let raw := unpack text
  fun q b => cell ((raw.drop (6*q.val + if b then 3 else 0)).take 3)

def stateToChar (q : Fin 6) : Char :=
  match q.val with
  | 0 => 'A' | 1 => 'B' | 2 => 'C'
  | 3 => 'D' | 4 => 'E' | _ => 'F'

def encodeCell : Option (Option (RootedLiveQuotient.Move (Fin 6))) → List Char
  | none => ['-','-','-']
  | some none => ['?','?','?']
  | some (some m) => [if m.write then '1' else '0',
                      if m.right then 'R' else 'L', stateToChar m.next]

def plainEncode (p : RootedLiveQuotient.PartialTable (Fin 6)) : List Char :=
  ([0,1,2,3,4,5] : List (Fin 6)).flatMap fun q =>
    (encodeCell (p q false) ++ encodeCell (p q true))

def rootThree (p : RootedLiveQuotient.PartialTable (Fin 6)) : Bool :=
  decide (p 0 false = some (some ⟨true,true,1⟩)) &&
  decide (p 1 false = some (some ⟨true,true,2⟩)) &&
  decide (p 2 false = some (some ⟨false,false,0⟩))

theorem rooted_of_rootThree (p : RootedLiveQuotient.PartialTable (Fin 6))
    (h : rootThree p = true) : RootedLiveQuotient.Extends RootedLiveQuotient.raw11Parent p := by
  have hA : p 0 false = some (some ⟨true,true,1⟩) := by
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  have hB : p 1 false = some (some ⟨true,true,2⟩) := by
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  have hC : p 2 false = some (some ⟨false,false,0⟩) := by
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  intro q b m hs
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by
    have hi := q.isLt
    omega
  have hslot : RootedLiveQuotient.raw11Parent q b = none ∨
      RootedLiveQuotient.raw11Parent q b = p q b := by
    rcases hq with h|h|h|h|h|h <;> subst q <;> cases b <;>
      simp [RootedLiveQuotient.raw11Parent, hA, hB, hC]
  rcases hslot with he | he
  · simp [he] at hs
  · rw [he] at hs
    exact hs

/-- Exact exported original-source leaf strings: 94 q0 open-automata and
    32 Q32SideLeafRoster. Source identities must be transported separately
    when consuming their parent Cover proofs. -/
def encodedTables : List String := [
  "1RB1RD1RC0RE0LA0RF1LA1LD1LE0LA---1LA",
  "1RB1RD1RC0RE0LA0RF1LA1LD1RA0LA---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0LB0LA---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD1RB0LA---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0LC0LA---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0RC0LA---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD1LC0LA---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0LD0LA---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD1LD0LA---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0LE0LA---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD1RA0LA---0RE",
  "1RB1RD1RC0RE0LA0RF1LA1LD1LD0LA---0RE",
  "1RB1RD1RC0RE0LA0RF1LA1LD1LE0LA---0RE",
  "1RB1RD1RC0RE0LA---1LA1LD0LF0RB1LF0LC",
  "1RB1RD1RC0RE0LA0RF1LA1LD1RA1LB---1RB",
  "1RB1RD1RC0RE0LA1RF1LA1LD1RB1LB---0LB",
  "1RB1RD1RC0RE0LA1RF1LA1LD1RC1LB---0RB",
  "1RB1RD1RC0RE0LA1RF1LA1LD1RD1LB---0RB",
  "1RB1RD1RC0RE0LA0RF1LA1LD---1RC---1RB",
  "1RB1RD1RC0RE0LA0RF1LA1LD1RA1RC---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0LB1RC---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD1RB1RC---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0LC1RC---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0RC1RC---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD1LC1RC---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0LD1RC---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD1LD1RC---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0LE1RC---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0RA1RC---0LE",
  "1RB1RD1RC0RE0LA0RF1LA1LD0RA1RC---1RE",
  "1RB1RD1RC0RE0LA0RF1LA1LD---1RC0RA0LF",
  "1RB1RD1RC0RE0LA1RF1LA1LD1RB1RC---0LB",
  "1RB1RD1RC0RE0LA1RF1LA1LD---1RC---0RC",
  "1RB1RD1RC0RE0LA1RF1LA1LD0RA1RC---1RE",
  "1RB1RD1RC0RE0LA0RF1LA1LD0RB0LE---1RB",
  "1RB1RD1RC0RE0LA1RF1LA1LD0RB0LE---0RC",
  "1RB1RD1RC0RE0LA0RF1LA1LD1RB0LE---0RD",
  "1RB1RD1RC0RE0LA0RF1LA1LD0RC0LE---0RD",
  "1RB1RD1RC0RE0LA1RF1LA1LD1LC0LE---0RC",
  "1RB1RD1RC0RE0LA1RF1LA1LD1RC1LE---0RB",
  "1RB1RD1RC0RE0LA1RE1LA1LD---0LF0RB0RA",
  "1RB1RD1RC0RE0LA0RF1LA1LD---0LF0RB1RB",
  "1RB1RD1RC0RE0LA0LB1LA1LD1RB0RF---0LA",
  "1RB1RD1RC0RE0LA0LE1LA1LD---0RF1RB0LA",
  "1RB1RD1RC0RE0LA0RE1LA1LD0RB0RF---0LA",
  "1RB1RD1RC0RE0LA1RE1LA1LD0RA0RF---0LA",
  "1RB1RD1RC0RE0LA1RE1LA1LD0RB0RF---0LA",
  "1RB1RD1RC0RE0LA0LD1LA1LD1RB0RF---0RC",
  "1RB1RD1RC0RE0LA0LB1LA1LD1RB0RF---1LC",
  "1RB1RD1RC0RE0LA0RB1LA1LD1LC0RF---1LC",
  "1RB1RD1RC0RE0LA0RB1LA1LD1RC0RF---1LC",
  "1RB1RD1RC0RE0LA0RB1LA1LD1RD0RF---1LC",
  "1RB1RD1RC0RE0LA0RB1LA1LD1LB0RF---0LD",
  "1RB1RD1RC0RE0LA1RB1LA1LD1LB0RF---0LD",
  "1RB1RD1RC0RE0LA---1LA1LD1RB0RF---0LD",
  "1RB1RD1RC0RE0LA1LA1LA1LD0RC0RF---0LD",
  "1RB1RD1RC0RE0LA0RB1LA1LD1RC0RF---0LD",
  "1RB1RD1RC0RE0LA0RB1LA1LD1LB0RF---0LE",
  "1RB1RD1RC0RE0LA0LB1LA1LD1RB0RF---0LE",
  "1RB1RD1RC0RE0LA0RB1LA1LD---0RF1LB0LF",
  "1RB1RD1RC0RE0LA0LE1LA1LD---0RF1RB0LF",
  "1RB1RD1RC0RE0LA0RB1LA1LD1LC1RF---0LB",
  "1RB1RD1RC0RE0LA0RA1LA1LD1LB1RF---1RB",
  "1RB1RD1RC0RE0LA0RB1LA1LD1LB1RF---1RB",
  "1RB1RD1RC0RE0LA1LA1LA1LD1RB1RF---0LC",
  "1RB1RD1RC0RE0LA1LA1LA1LD0RC1RF---0LC",
  "1RB1RD1RC0RE0LA1LE1LA1LD1RB1RF---0LC",
  "1RB1RD1RC0RE0LA1RE1LA1LD0RC1RF---0LC",
  "1RB1RD1RC0RE0LA1RB1LA1LD---1RF---0RC",
  "1RB1RD1RC0RE0LA0RD1LA1LD0LA1RF---0RC",
  "1RB1RD1RC0RE0LA0RD1LA1LD0RB1RF---0RC",
  "1RB1RD1RC0RE0LA0RD1LA1LD1RB1RF---0RC",
  "1RB1RD1RC0RE0LA0RD1LA1LD0LC1RF---0RC",
  "1RB1RD1RC0RE0LA0RD1LA1LD0RC1RF---0RC",
  "1RB1RD1RC0RE0LA0RD1LA1LD1RC1RF---0RC",
  "1RB1RD1RC0RE0LA0RD1LA1LD0LD1RF---0RC",
  "1RB1RD1RC0RE0LA0RD1LA1LD1RD1RF---0RC",
  "1RB1RD1RC0RE0LA0LE1LA1LD0RA1RF---0RC",
  "1RB1RD1RC0RE0LA1RE1LA1LD0RA1RF---0RC",
  "1RB1RD1RC0RE0LA1RE1LA1LD0RB1RF---0RC",
  "1RB1RD1RC0RE0LA1RE1LA1LD1RB1RF---0RC",
  "1RB1RD1RC0RE0LA1RE1LA1LD0RC1RF---0RC",
  "1RB1RD1RC0RE0LA1RE1LA1LD0LD1RF---0RC",
  "1RB1RD1RC0RE0LA1RE1LA1LD1LE1RF---0RC",
  "1RB1RD1RC0RE0LA0LB1LA1LD1RB1RF---1RC",
  "1RB1RD1RC0RE0LA0RE1LA1LD0RB1RF---1RC",
  "1RB1RD1RC0RE0LA1RE1LA1LD0RA1RF---1RC",
  "1RB1RD1RC0RE0LA1RE1LA1LD0RB1RF---1RC",
  "1RB1RD1RC0RE0LA1RB1LA1LD---1RF0RC0LE",
  "1RB1RD1RC0RE0LA0RB1LA1LD---1RF0LC1RE",
  "1RB1RD1RC0RE0LA0RA1LA1LD---1RF1LC1RE",
  "1RB1RD1RC0RE0LA0RF1LA1LD---1RF1RA0LF",
  "1RB1RD1RC0RE0LA0RD1LA1LD0RC0RF---0LD",
  "1RB1RD1RC0RE0LA0LC1LA1LD---0RF1LB0RE",
  "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LA_------",
  "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RA_------",
  "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LB_------",
  "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RB_------",
  "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LB_------",
  "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LC_------",
  "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RC_------",
  "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LD_------",
  "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RD_------",
  "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LD_------",
  "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RD_------",
  "1RB1RD_1RC1RB_0LA---_1LA0LB_------_------",
  "1RB1RD_1RC0RC_0LA---_1LA0LB_------_------",
  "1RB1RD_1RC1RC_0LA---_1LA0LB_------_------",
  "1RB1RD_1RC0LD_0LA---_1LA0LB_------_------",
  "1RB1RD_1RC0RD_0LA---_1LA0LB_------_------",
  "1RB1RD_1RC1LD_0LA---_1LA0LB_------_------",
  "1RB1RD_1RC1RD_0LA---_1LA0LB_------_------",
  "1RB1RD_1RC---_0LA---_1LA0RB_------_------",
  "1RB1RD_1RC---_0LA---_1LA1RB_------_------",
  "1RB1RD_1RC---_0LA---_1LA0RC_------_------",
  "1RB1RD_1RC---_0LA---_1LA1RC_------_------",
  "1RB1RD_1RC---_0LA---_1LA1RD_------_------",
  "1RB1RD_1RC---_0LA---_1RA---_------_------",
  "1RB1RD_1RC---_0LA---_0RB---_------_------",
  "1RB1RD_1RC---_0LA---_1RB---_------_------",
  "1RB1RD_1RC---_0LA---_0RC---_------_------",
  "1RB1RD_1RC---_0LA---_1RC---_------_------",
  "1RB1RD_1RC---_0LA---_0RD---_------_------",
  "1RB1RD_1RC---_0LA---_1RD---_------_------",
  "1RB1LD_1RC---_0LA---_---1RA_------_------",
  "1RB1LD_1RC---_0LA---_---0LC_------_------"
]

def bankAt (i : Nat) : RootedLiveQuotient.PartialTable (Fin 6) :=
  parse (encodedTables[i]?.getD "")

def roundtripCheck : Bool :=
  (List.range encodedTables.length).all fun i =>
    plainEncode (bankAt i) == unpack (encodedTables[i]?.getD "")

def rootedCheck : Bool :=
  (List.range encodedTables.length).all (fun i => rootThree (bankAt i))

def disjointCheck : Bool :=
  (List.range encodedTables.length).all fun i =>
    (List.range encodedTables.length).all fun j =>
      if i < j then !(RootedLiveQuotient.sixTailCheck (bankAt i) (bankAt j)) else true

theorem bank_count : encodedTables.length = 126 := by decide

theorem roundtripCheck_ok : roundtripCheck = true := by decide +kernel
theorem rootedCheck_ok : rootedCheck = true := by decide +kernel
theorem disjointCheck_ok : disjointCheck = true := by decide +kernel

theorem bankAt_extends (i : Nat) (hi : i < encodedTables.length) :
    RootedLiveQuotient.Extends RootedLiveQuotient.raw11Parent (bankAt i) := by
  apply rooted_of_rootThree
  exact List.all_eq_true.mp rootedCheck_ok i (List.mem_range.mpr hi)

theorem bankAt_disjoint (i j : Nat)
    (hi : i < encodedTables.length) (hj : j < encodedTables.length)
    (hij : i < j) :
    ¬ ∃ m : RootedLiveQuotient.Machine (Fin 6),
      RootedLiveQuotient.QuotientCompatible (bankAt i) m 0 ∧
      RootedLiveQuotient.QuotientCompatible (bankAt j) m 0 := by
  have hx := List.all_eq_true.mp disjointCheck_ok i (List.mem_range.mpr hi)
  have hy := List.all_eq_true.mp hx j (List.mem_range.mpr hj)
  have hfalse : RootedLiveQuotient.sixTailCheck (bankAt i) (bankAt j) = false := by
    cases htest : RootedLiveQuotient.sixTailCheck (bankAt i) (bankAt j) with
    | false => rfl
    | true => simp [hij,htest] at hy
  intro h
  have htrue := (RootedLiveQuotient.raw11_sixTailCheck_exact (bankAt i) (bankAt j)
    (bankAt_extends i hi) (bankAt_extends j hj)).mpr h
  rw [hfalse] at htrue
  contradiction

#print axioms bankAt_disjoint
end Agent24BankDisjoint