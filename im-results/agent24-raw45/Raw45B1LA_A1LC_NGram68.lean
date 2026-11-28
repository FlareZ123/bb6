import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45NGram
open BB6Coverage BB6.Agent1NGram

/-- 1RB0LC_1RC0LA_0RD0LE_1LD1RB_0RF1RB_0RA---, width 1, 27 abstract states. -/
def p0 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,true,5⟩)
  | (4, true) => some (some ⟨true,true,1⟩)
  | (5, false) => some (some ⟨false,true,0⟩)
  | (5, true) => none
  | _ => none
def c0 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty]⟩
theorem ok0 : check p0 c0 = true := by decide
theorem never0 (m : Machine) (hm : compatible p0 m) : NeverHalts m := never p0 c0 ok0 m hm
#print axioms never0

/-- 1RB0LC_1RC0LA_0RD0LE_1LD1RB_0RF1RB_1RA---, width 1, 28 abstract states. -/
def p1 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,true,5⟩)
  | (4, true) => some (some ⟨true,true,1⟩)
  | (5, false) => some (some ⟨true,true,0⟩)
  | (5, true) => none
  | _ => none
def c1 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty]⟩
theorem ok1 : check p1 c1 = true := by decide
theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m := never p1 c1 ok1 m hm
#print axioms never1

/-- 1RB0LC_1RC0LA_0RD0LE_1LD1RB_1RF1RB_0RA---, width 1, 27 abstract states. -/
def p2 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,5⟩)
  | (4, true) => some (some ⟨true,true,1⟩)
  | (5, false) => some (some ⟨false,true,0⟩)
  | (5, true) => none
  | _ => none
def c2 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty]⟩
theorem ok2 : check p2 c2 = true := by decide
theorem never2 (m : Machine) (hm : compatible p2 m) : NeverHalts m := never p2 c2 ok2 m hm
#print axioms never2

/-- 1RB0LC_1RC0LA_0RD0LE_1LD1RB_1RF1RB_1RA---, width 1, 28 abstract states. -/
def p3 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,5⟩)
  | (4, true) => some (some ⟨true,true,1⟩)
  | (5, false) => some (some ⟨true,true,0⟩)
  | (5, true) => none
  | _ => none
def c3 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty]⟩
theorem ok3 : check p3 c3 = true := by decide
theorem never3 (m : Machine) (hm : compatible p3 m) : NeverHalts m := never p3 c3 ok3 m hm
#print axioms never3

/-- 1RB0LC_1RC0LA_0RD0LE_1LD1RB_1RF1RA_1LB---, width 1, 28 abstract states. -/
def p4 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,5⟩)
  | (4, true) => some (some ⟨true,true,0⟩)
  | (5, false) => some (some ⟨true,false,1⟩)
  | (5, true) => none
  | _ => none
def c4 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty]⟩
theorem ok4 : check p4 c4 = true := by decide
theorem never4 (m : Machine) (hm : compatible p4 m) : NeverHalts m := never p4 c4 ok4 m hm
#print axioms never4

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LA0LB_------, width 1, 26 abstract states. -/
def p5 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨false,false,1⟩)
  | (5, false) => none
  | (5, true) => none
  | _ => none
def c5 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,.empty]⟩
theorem ok5 : check p5 c5 = true := by decide
theorem never5 (m : Machine) (hm : compatible p5 m) : NeverHalts m := never p5 c5 ok5 m hm
#print axioms never5

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LA1RD_------, width 1, 25 abstract states. -/
def p6 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨true,true,3⟩)
  | (5, false) => none
  | (5, true) => none
  | _ => none
def c6 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,.empty]⟩
theorem ok6 : check p6 c6 = true := by decide
theorem never6 (m : Machine) (hm : compatible p6 m) : NeverHalts m := never p6 c6 ok6 m hm
#print axioms never6

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LA0LF_---0LA, width 4, 36 abstract states. -/
def p7 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨false,false,5⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨false,false,0⟩)
  | _ => none
def c7 : Cert := ⟨3,0x4803045,0x40175,#[(.branch (.branch (.branch .leaf .leaf) .leaf) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty)),.empty,(.branch (.branch .empty .leaf) .empty)]⟩
theorem ok7 : check p7 c7 = true := by decide
theorem never7 (m : Machine) (hm : compatible p7 m) : NeverHalts m := never p7 c7 ok7 m hm
#print axioms never7

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LA0LF_---0RC, width 4, 39 abstract states. -/
def p8 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨false,false,5⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨false,true,2⟩)
  | _ => none
def c8 : Cert := ⟨3,0x4803045,0x40175,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty)),.empty,(.branch (.branch .empty .leaf) .empty)]⟩
theorem ok8 : check p8 c8 = true := by decide
theorem never8 (m : Machine) (hm : compatible p8 m) : NeverHalts m := never p8 c8 ok8 m hm
#print axioms never8

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LA1RF_---0RA, width 1, 28 abstract states. -/
def p9 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨true,true,5⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨false,true,0⟩)
  | _ => none
def c9 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem ok9 : check p9 c9 = true := by decide
theorem never9 (m : Machine) (hm : compatible p9 m) : NeverHalts m := never p9 c9 ok9 m hm
#print axioms never9

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LA1RF_---0RB, width 1, 30 abstract states. -/
def p10 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨true,true,5⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨false,true,1⟩)
  | _ => none
def c10 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem ok10 : check p10 c10 = true := by decide
theorem never10 (m : Machine) (hm : compatible p10 m) : NeverHalts m := never p10 c10 ok10 m hm
#print axioms never10

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LA1RF_---1RB, width 1, 26 abstract states. -/
def p11 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨true,true,5⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨true,true,1⟩)
  | _ => none
def c11 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem ok11 : check p11 c11 = true := by decide
theorem never11 (m : Machine) (hm : compatible p11 m) : NeverHalts m := never p11 c11 ok11 m hm
#print axioms never11

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LA1RF_---0RE, width 3, 65 abstract states. -/
def p12 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨true,true,5⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨false,true,4⟩)
  | _ => none
def c12 : Cert := ⟨2,0xf8f5,0x15d,#[(.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .leaf) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty)) (.branch (.branch (.branch .leaf (.branch .empty (.branch .leaf .leaf))) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty) .empty)]⟩
theorem ok12 : check p12 c12 = true := by decide
theorem never12 (m : Machine) (hm : compatible p12 m) : NeverHalts m := never p12 c12 ok12 m hm
#print axioms never12

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LF---_0LA0LA, width 4, 46 abstract states. -/
def p13 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,5⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨false,false,0⟩)
  | _ => none
def c13 : Cert := ⟨3,0x4803045,0xc00541f5,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),.empty,(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty)]⟩
theorem ok13 : check p13 c13 = true := by decide
theorem never13 (m : Machine) (hm : compatible p13 m) : NeverHalts m := never p13 c13 ok13 m hm
#print axioms never13

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LF---_0LA0LC, width 3, 24 abstract states. -/
def p14 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,5⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨false,false,2⟩)
  | _ => none
def c14 : Cert := ⟨2,0x18c5,0x15d,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),.empty,(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)]⟩
theorem ok14 : check p14 c14 = true := by decide
theorem never14 (m : Machine) (hm : compatible p14 m) : NeverHalts m := never p14 c14 ok14 m hm
#print axioms never14

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LF---_0LA1LD, width 4, 50 abstract states. -/
def p15 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,5⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨true,false,3⟩)
  | _ => none
def c15 : Cert := ⟨3,0x4803045,0xc00545f5,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),.empty,(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty)]⟩
theorem ok15 : check p15 c15 = true := by decide
theorem never15 (m : Machine) (hm : compatible p15 m) : NeverHalts m := never p15 c15 ok15 m hm
#print axioms never15

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LF---_0LA1RD, width 3, 24 abstract states. -/
def p16 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,5⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨true,true,3⟩)
  | _ => none
def c16 : Cert := ⟨2,0x18c5,0x15d,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),.empty,(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)]⟩
theorem ok16 : check p16 c16 = true := by decide
theorem never16 (m : Machine) (hm : compatible p16 m) : NeverHalts m := never p16 c16 ok16 m hm
#print axioms never16

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LF---_0LA0RE, width 4, 52 abstract states. -/
def p17 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,5⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨false,true,4⟩)
  | _ => none
def c17 : Cert := ⟨3,0x4a03055,0xc00541f5,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),(.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),.empty,(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty)]⟩
theorem ok17 : check p17 c17 = true := by decide
theorem never17 (m : Machine) (hm : compatible p17 m) : NeverHalts m := never p17 c17 ok17 m hm
#print axioms never17

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LF---_0LA1RF, width 3, 25 abstract states. -/
def p18 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,5⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨true,true,5⟩)
  | _ => none
def c18 : Cert := ⟨2,0x18c5,0x15d,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),.empty,(.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)]⟩
theorem ok18 : check p18 c18 = true := by decide
theorem never18 (m : Machine) (hm : compatible p18 m) : NeverHalts m := never p18 c18 ok18 m hm
#print axioms never18

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LF---_0RC0LC, width 3, 26 abstract states. -/
def p19 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,5⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨false,true,2⟩)
  | (5, true) => some (some ⟨false,false,2⟩)
  | _ => none
def c19 : Cert := ⟨2,0x18c5,0x15d,#[.leaf,(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),.empty,(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)]⟩
theorem ok19 : check p19 c19 = true := by decide
theorem never19 (m : Machine) (hm : compatible p19 m) : NeverHalts m := never p19 c19 ok19 m hm
#print axioms never19

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LF---_0RC1RD, width 3, 26 abstract states. -/
def p20 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,5⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨false,true,2⟩)
  | (5, true) => some (some ⟨true,true,3⟩)
  | _ => none
def c20 : Cert := ⟨2,0x18c5,0x15d,#[.leaf,(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),.empty,(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)]⟩
theorem ok20 : check p20 c20 = true := by decide
theorem never20 (m : Machine) (hm : compatible p20 m) : NeverHalts m := never p20 c20 ok20 m hm
#print axioms never20

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0LF---_1RE0LA, width 4, 49 abstract states. -/
def p21 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,5⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨true,true,4⟩)
  | (5, true) => some (some ⟨false,false,0⟩)
  | _ => none
def c21 : Cert := ⟨3,0x4803045,0xc00541f5,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),.empty,(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty)]⟩
theorem ok21 : check p21 c21 = true := by decide
theorem never21 (m : Machine) (hm : compatible p21 m) : NeverHalts m := never p21 c21 ok21 m hm
#print axioms never21

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0RF0RB_---0RA, width 1, 30 abstract states. -/
def p22 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,true,5⟩)
  | (4, true) => some (some ⟨false,true,1⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨false,true,0⟩)
  | _ => none
def c22 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,(.branch .leaf .leaf)]⟩
theorem ok22 : check p22 c22 = true := by decide
theorem never22 (m : Machine) (hm : compatible p22 m) : NeverHalts m := never p22 c22 ok22 m hm
#print axioms never22

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_0RF0RB_---1RA, width 1, 30 abstract states. -/
def p23 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,true,5⟩)
  | (4, true) => some (some ⟨false,true,1⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨true,true,0⟩)
  | _ => none
def c23 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,(.branch .leaf .leaf)]⟩
theorem ok23 : check p23 c23 = true := by decide
theorem never23 (m : Machine) (hm : compatible p23 m) : NeverHalts m := never p23 c23 ok23 m hm
#print axioms never23

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_1RF0RB_---0RA, width 1, 30 abstract states. -/
def p24 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,5⟩)
  | (4, true) => some (some ⟨false,true,1⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨false,true,0⟩)
  | _ => none
def c24 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem ok24 : check p24 c24 = true := by decide
theorem never24 (m : Machine) (hm : compatible p24 m) : NeverHalts m := never p24 c24 ok24 m hm
#print axioms never24

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_1RF0RB_---1RA, width 1, 30 abstract states. -/
def p25 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,5⟩)
  | (4, true) => some (some ⟨false,true,1⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨true,true,0⟩)
  | _ => none
def c25 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem ok25 : check p25 c25 = true := by decide
theorem never25 (m : Machine) (hm : compatible p25 m) : NeverHalts m := never p25 c25 ok25 m hm
#print axioms never25

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_1RF0LB_---1LB, width 1, 29 abstract states. -/
def p26 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,5⟩)
  | (4, true) => some (some ⟨false,false,1⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨true,false,1⟩)
  | _ => none
def c26 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem ok26 : check p26 c26 = true := by decide
theorem never26 (m : Machine) (hm : compatible p26 m) : NeverHalts m := never p26 c26 ok26 m hm
#print axioms never26

/-- 1RB0LC_1RC0LA_0RD1LE_1LD1RB_1RF1RD_---1LB, width 1, 28 abstract states. -/
def p27 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,5⟩)
  | (4, true) => some (some ⟨true,true,3⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨true,false,1⟩)
  | _ => none
def c27 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem ok27 : check p27 c27 = true := by decide
theorem never27 (m : Machine) (hm : compatible p27 m) : NeverHalts m := never p27 c27 ok27 m hm
#print axioms never27

/-- 1RB0LC_1RC0LA_0RD0RE_1LD1RB_1LB0RC_------, width 1, 26 abstract states. -/
def p28 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,true,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,false,1⟩)
  | (4, true) => some (some ⟨false,true,2⟩)
  | (5, false) => none
  | (5, true) => none
  | _ => none
def c28 : Cert := ⟨0,0xf,0xf,#[.leaf,(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf .leaf),(.branch .leaf .leaf),.empty,.empty]⟩
theorem ok28 : check p28 c28 = true := by decide
theorem never28 (m : Machine) (hm : compatible p28 m) : NeverHalts m := never p28 c28 ok28 m hm
#print axioms never28

/-- 1RB0LC_1RC0LA_0RD0RE_1LD1RB_1LB1RF_0RC---, width 4, 86 abstract states. -/
def p29 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,true,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,false,1⟩)
  | (4, true) => some (some ⟨true,true,5⟩)
  | (5, false) => some (some ⟨false,true,2⟩)
  | (5, true) => none
  | _ => none
def c29 : Cert := ⟨3,0x42513f5,0xc5a0ff55,#[.leaf,(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty))),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty))) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)))) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty)) (.branch .leaf (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty))) (.branch .leaf .leaf)))),(.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty)))),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty))) .empty))),.empty]⟩
theorem ok29 : check p29 c29 = true := by decide
theorem never29 (m : Machine) (hm : compatible p29 m) : NeverHalts m := never p29 c29 ok29 m hm
#print axioms never29

/-- 1RB0LC_1RC0LA_0RD0RE_1LD1RB_1LF0RC_1RC---, width 1, 27 abstract states. -/
def p30 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,true,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,false,5⟩)
  | (4, true) => some (some ⟨false,true,2⟩)
  | (5, false) => some (some ⟨true,true,2⟩)
  | (5, true) => none
  | _ => none
def c30 : Cert := ⟨0,0xf,0xf,#[.leaf,(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty (.branch .leaf .leaf)),.empty]⟩
theorem ok30 : check p30 c30 = true := by decide
theorem never30 (m : Machine) (hm : compatible p30 m) : NeverHalts m := never p30 c30 ok30 m hm
#print axioms never30

/-- 1RB0LC_1RC0LA_0RD0RE_1LD1RB_1RF0RC_1LB---, width 4, 116 abstract states. -/
def p31 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,true,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,5⟩)
  | (4, true) => some (some ⟨false,true,2⟩)
  | (5, false) => some (some ⟨true,false,1⟩)
  | (5, true) => none
  | _ => none
def c31 : Cert := ⟨3,0xed0a50cf,0xf2005155,#[(.branch (.branch .leaf (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) (.branch .empty (.branch .leaf (.branch .empty .leaf)))) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .leaf .leaf)))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))))),(.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .leaf .leaf))) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty (.branch .leaf (.branch .empty .leaf)))) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty))) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch .empty .leaf)))))),(.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .leaf .leaf))) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))))),.empty]⟩
theorem ok31 : check p31 c31 = true := by decide
theorem never31 (m : Machine) (hm : compatible p31 m) : NeverHalts m := never p31 c31 ok31 m hm
#print axioms never31

/-- 1RB0LC_1RC0LA_0RD1RE_1LD1RB_1LF1RB_---1LB, width 1, 28 abstract states. -/
def p32 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,true,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,false,5⟩)
  | (4, true) => some (some ⟨true,true,1⟩)
  | (5, false) => none
  | (5, true) => some (some ⟨true,false,1⟩)
  | _ => none
def c32 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok32 : check p32 c32 = true := by decide
theorem never32 (m : Machine) (hm : compatible p32 m) : NeverHalts m := never p32 c32 ok32 m hm
#print axioms never32

/-- 1RB0LC_1RC0LA_0RD1RE_1LD1RB_0RF---_1RC1RE, width 3, 59 abstract states. -/
def p33 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,true,4⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,true,5⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨true,true,2⟩)
  | (5, true) => some (some ⟨true,true,4⟩)
  | _ => none
def c33 : Cert := ⟨2,0x1cf5,0xc5f5,#[.leaf,(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch .leaf (.branch (.branch .leaf .leaf) .leaf))) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch .leaf (.branch (.branch .leaf .leaf) .leaf))) (.branch .leaf .leaf))),(.branch .empty (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty)) .empty)]⟩
theorem ok33 : check p33 c33 = true := by decide
theorem never33 (m : Machine) (hm : compatible p33 m) : NeverHalts m := never p33 c33 ok33 m hm
#print axioms never33

/-- 1RB0LC_1RC0LA_0RD0LF_1LD1RB_0RA---_0RE1RB, width 1, 27 abstract states. -/
def p34 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,true,0⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨false,true,4⟩)
  | (5, true) => some (some ⟨true,true,1⟩)
  | _ => none
def c34 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty)]⟩
theorem ok34 : check p34 c34 = true := by decide
theorem never34 (m : Machine) (hm : compatible p34 m) : NeverHalts m := never p34 c34 ok34 m hm
#print axioms never34

/-- 1RB0LC_1RC0LA_0RD0LF_1LD1RB_1RA---_0RE1RB, width 1, 28 abstract states. -/
def p35 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,0⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨false,true,4⟩)
  | (5, true) => some (some ⟨true,true,1⟩)
  | _ => none
def c35 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty)]⟩
theorem ok35 : check p35 c35 = true := by decide
theorem never35 (m : Machine) (hm : compatible p35 m) : NeverHalts m := never p35 c35 ok35 m hm
#print axioms never35

/-- 1RB0LC_1RC0LA_0RD0LF_1LD1RB_0RA---_1RE1RB, width 1, 27 abstract states. -/
def p36 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,true,0⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨true,true,4⟩)
  | (5, true) => some (some ⟨true,true,1⟩)
  | _ => none
def c36 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty)]⟩
theorem ok36 : check p36 c36 = true := by decide
theorem never36 (m : Machine) (hm : compatible p36 m) : NeverHalts m := never p36 c36 ok36 m hm
#print axioms never36

/-- 1RB0LC_1RC0LA_0RD0LF_1LD1RB_1RA---_1RE1RB, width 1, 28 abstract states. -/
def p37 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,0⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨true,true,4⟩)
  | (5, true) => some (some ⟨true,true,1⟩)
  | _ => none
def c37 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty)]⟩
theorem ok37 : check p37 c37 = true := by decide
theorem never37 (m : Machine) (hm : compatible p37 m) : NeverHalts m := never p37 c37 ok37 m hm
#print axioms never37

/-- 1RB0LC_1RC0LA_0RD0LF_1LD1RB_1LB---_1RE1RA, width 1, 28 abstract states. -/
def p38 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,false,1⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨true,true,4⟩)
  | (5, true) => some (some ⟨true,true,0⟩)
  | _ => none
def c38 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty)]⟩
theorem ok38 : check p38 c38 = true := by decide
theorem never38 (m : Machine) (hm : compatible p38 m) : NeverHalts m := never p38 c38 ok38 m hm
#print axioms never38

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_------_0LA0LB, width 1, 26 abstract states. -/
def p39 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => none
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨false,false,1⟩)
  | _ => none
def c39 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok39 : check p39 c39 = true := by decide
theorem never39 (m : Machine) (hm : compatible p39 m) : NeverHalts m := never p39 c39 ok39 m hm
#print axioms never39

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_------_0LA1RD, width 1, 25 abstract states. -/
def p40 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => none
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨true,true,3⟩)
  | _ => none
def c40 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok40 : check p40 c40 = true := by decide
theorem never40 (m : Machine) (hm : compatible p40 m) : NeverHalts m := never p40 c40 ok40 m hm
#print axioms never40

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---0LA_0LA0LE, width 4, 36 abstract states. -/
def p41 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨false,false,0⟩)
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨false,false,4⟩)
  | _ => none
def c41 : Cert := ⟨3,0x4803045,0x40175,#[(.branch (.branch (.branch .leaf .leaf) .leaf) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),.empty,(.branch (.branch .empty .leaf) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty))]⟩
theorem ok41 : check p41 c41 = true := by decide
theorem never41 (m : Machine) (hm : compatible p41 m) : NeverHalts m := never p41 c41 ok41 m hm
#print axioms never41

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---0RC_0LA0LE, width 4, 39 abstract states. -/
def p42 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨false,true,2⟩)
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨false,false,4⟩)
  | _ => none
def c42 : Cert := ⟨3,0x4803045,0x40175,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),.empty,(.branch (.branch .empty .leaf) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty))]⟩
theorem ok42 : check p42 c42 = true := by decide
theorem never42 (m : Machine) (hm : compatible p42 m) : NeverHalts m := never p42 c42 ok42 m hm
#print axioms never42

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---0RA_0LA1RE, width 1, 28 abstract states. -/
def p43 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨false,true,0⟩)
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨true,true,4⟩)
  | _ => none
def c43 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok43 : check p43 c43 = true := by decide
theorem never43 (m : Machine) (hm : compatible p43 m) : NeverHalts m := never p43 c43 ok43 m hm
#print axioms never43

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---0RB_0LA1RE, width 1, 30 abstract states. -/
def p44 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨false,true,1⟩)
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨true,true,4⟩)
  | _ => none
def c44 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok44 : check p44 c44 = true := by decide
theorem never44 (m : Machine) (hm : compatible p44 m) : NeverHalts m := never p44 c44 ok44 m hm
#print axioms never44

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---1RB_0LA1RE, width 1, 26 abstract states. -/
def p45 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨true,true,1⟩)
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨true,true,4⟩)
  | _ => none
def c45 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok45 : check p45 c45 = true := by decide
theorem never45 (m : Machine) (hm : compatible p45 m) : NeverHalts m := never p45 c45 ok45 m hm
#print axioms never45

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---0RF_0LA1RE, width 3, 65 abstract states. -/
def p46 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨false,true,5⟩)
  | (5, false) => some (some ⟨false,false,0⟩)
  | (5, true) => some (some ⟨true,true,4⟩)
  | _ => none
def c46 : Cert := ⟨2,0xf8f5,0x15d,#[(.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .leaf) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty)) (.branch (.branch (.branch .leaf (.branch .empty (.branch .leaf .leaf))) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem ok46 : check p46 c46 = true := by decide
theorem never46 (m : Machine) (hm : compatible p46 m) : NeverHalts m := never p46 c46 ok46 m hm
#print axioms never46

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_0LA0LA_0LE---, width 4, 46 abstract states. -/
def p47 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨false,false,0⟩)
  | (5, false) => some (some ⟨false,false,4⟩)
  | (5, true) => none
  | _ => none
def c47 : Cert := ⟨3,0x4803045,0xc00541f5,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),.empty]⟩
theorem ok47 : check p47 c47 = true := by decide
theorem never47 (m : Machine) (hm : compatible p47 m) : NeverHalts m := never p47 c47 ok47 m hm
#print axioms never47

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_0LA0LC_0LE---, width 3, 24 abstract states. -/
def p48 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨false,false,2⟩)
  | (5, false) => some (some ⟨false,false,4⟩)
  | (5, true) => none
  | _ => none
def c48 : Cert := ⟨2,0x18c5,0x15d,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),.empty]⟩
theorem ok48 : check p48 c48 = true := by decide
theorem never48 (m : Machine) (hm : compatible p48 m) : NeverHalts m := never p48 c48 ok48 m hm
#print axioms never48

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_0LA1LD_0LE---, width 4, 50 abstract states. -/
def p49 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨true,false,3⟩)
  | (5, false) => some (some ⟨false,false,4⟩)
  | (5, true) => none
  | _ => none
def c49 : Cert := ⟨3,0x4803045,0xc00545f5,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),.empty]⟩
theorem ok49 : check p49 c49 = true := by decide
theorem never49 (m : Machine) (hm : compatible p49 m) : NeverHalts m := never p49 c49 ok49 m hm
#print axioms never49

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_0LA1RD_0LE---, width 3, 24 abstract states. -/
def p50 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨true,true,3⟩)
  | (5, false) => some (some ⟨false,false,4⟩)
  | (5, true) => none
  | _ => none
def c50 : Cert := ⟨2,0x18c5,0x15d,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),.empty]⟩
theorem ok50 : check p50 c50 = true := by decide
theorem never50 (m : Machine) (hm : compatible p50 m) : NeverHalts m := never p50 c50 ok50 m hm
#print axioms never50

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_0LA1RE_0LE---, width 3, 25 abstract states. -/
def p51 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨true,true,4⟩)
  | (5, false) => some (some ⟨false,false,4⟩)
  | (5, true) => none
  | _ => none
def c51 : Cert := ⟨2,0x18c5,0x15d,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),.empty]⟩
theorem ok51 : check p51 c51 = true := by decide
theorem never51 (m : Machine) (hm : compatible p51 m) : NeverHalts m := never p51 c51 ok51 m hm
#print axioms never51

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_0LA0RF_0LE---, width 4, 52 abstract states. -/
def p52 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,false,0⟩)
  | (4, true) => some (some ⟨false,true,5⟩)
  | (5, false) => some (some ⟨false,false,4⟩)
  | (5, true) => none
  | _ => none
def c52 : Cert := ⟨3,0x4a03055,0xc00541f5,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),.empty]⟩
theorem ok52 : check p52 c52 = true := by decide
theorem never52 (m : Machine) (hm : compatible p52 m) : NeverHalts m := never p52 c52 ok52 m hm
#print axioms never52

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_0RC0LC_0LE---, width 3, 26 abstract states. -/
def p53 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,true,2⟩)
  | (4, true) => some (some ⟨false,false,2⟩)
  | (5, false) => some (some ⟨false,false,4⟩)
  | (5, true) => none
  | _ => none
def c53 : Cert := ⟨2,0x18c5,0x15d,#[.leaf,(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),.empty]⟩
theorem ok53 : check p53 c53 = true := by decide
theorem never53 (m : Machine) (hm : compatible p53 m) : NeverHalts m := never p53 c53 ok53 m hm
#print axioms never53

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_0RC1RD_0LE---, width 3, 26 abstract states. -/
def p54 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,true,2⟩)
  | (4, true) => some (some ⟨true,true,3⟩)
  | (5, false) => some (some ⟨false,false,4⟩)
  | (5, true) => none
  | _ => none
def c54 : Cert := ⟨2,0x18c5,0x15d,#[.leaf,(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),.empty]⟩
theorem ok54 : check p54 c54 = true := by decide
theorem never54 (m : Machine) (hm : compatible p54 m) : NeverHalts m := never p54 c54 ok54 m hm
#print axioms never54

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_1RF0LA_0LE---, width 4, 49 abstract states. -/
def p55 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,5⟩)
  | (4, true) => some (some ⟨false,false,0⟩)
  | (5, false) => some (some ⟨false,false,4⟩)
  | (5, true) => none
  | _ => none
def c55 : Cert := ⟨3,0x4803045,0xc00541f5,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty))),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty) .empty)),.empty]⟩
theorem ok55 : check p55 c55 = true := by decide
theorem never55 (m : Machine) (hm : compatible p55 m) : NeverHalts m := never p55 c55 ok55 m hm
#print axioms never55

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---0RA_0RE0RB, width 1, 30 abstract states. -/
def p56 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨false,true,0⟩)
  | (5, false) => some (some ⟨false,true,4⟩)
  | (5, true) => some (some ⟨false,true,1⟩)
  | _ => none
def c56 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,(.branch .leaf .leaf),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok56 : check p56 c56 = true := by decide
theorem never56 (m : Machine) (hm : compatible p56 m) : NeverHalts m := never p56 c56 ok56 m hm
#print axioms never56

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---1RA_0RE0RB, width 1, 30 abstract states. -/
def p57 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨true,true,0⟩)
  | (5, false) => some (some ⟨false,true,4⟩)
  | (5, true) => some (some ⟨false,true,1⟩)
  | _ => none
def c57 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,(.branch .leaf .leaf),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok57 : check p57 c57 = true := by decide
theorem never57 (m : Machine) (hm : compatible p57 m) : NeverHalts m := never p57 c57 ok57 m hm
#print axioms never57

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---0RA_1RE0RB, width 1, 30 abstract states. -/
def p58 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨false,true,0⟩)
  | (5, false) => some (some ⟨true,true,4⟩)
  | (5, true) => some (some ⟨false,true,1⟩)
  | _ => none
def c58 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok58 : check p58 c58 = true := by decide
theorem never58 (m : Machine) (hm : compatible p58 m) : NeverHalts m := never p58 c58 ok58 m hm
#print axioms never58

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---1RA_1RE0RB, width 1, 30 abstract states. -/
def p59 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨true,true,0⟩)
  | (5, false) => some (some ⟨true,true,4⟩)
  | (5, true) => some (some ⟨false,true,1⟩)
  | _ => none
def c59 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok59 : check p59 c59 = true := by decide
theorem never59 (m : Machine) (hm : compatible p59 m) : NeverHalts m := never p59 c59 ok59 m hm
#print axioms never59

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---1LB_1RE0LB, width 1, 29 abstract states. -/
def p60 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨true,false,1⟩)
  | (5, false) => some (some ⟨true,true,4⟩)
  | (5, true) => some (some ⟨false,false,1⟩)
  | _ => none
def c60 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok60 : check p60 c60 = true := by decide
theorem never60 (m : Machine) (hm : compatible p60 m) : NeverHalts m := never p60 c60 ok60 m hm
#print axioms never60

/-- 1RB0LC_1RC0LA_0RD1LF_1LD1RB_---1LB_1RE1RD, width 1, 28 abstract states. -/
def p61 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,false,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨true,false,1⟩)
  | (5, false) => some (some ⟨true,true,4⟩)
  | (5, true) => some (some ⟨true,true,3⟩)
  | _ => none
def c61 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf))]⟩
theorem ok61 : check p61 c61 = true := by decide
theorem never61 (m : Machine) (hm : compatible p61 m) : NeverHalts m := never p61 c61 ok61 m hm
#print axioms never61

/-- 1RB0LC_1RC0LA_0RD0RF_1LD1RB_------_1LB0RC, width 1, 26 abstract states. -/
def p62 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,true,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => none
  | (5, false) => some (some ⟨true,false,1⟩)
  | (5, true) => some (some ⟨false,true,2⟩)
  | _ => none
def c62 : Cert := ⟨0,0xf,0xf,#[.leaf,(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,.empty,(.branch .leaf .leaf),(.branch .leaf .leaf)]⟩
theorem ok62 : check p62 c62 = true := by decide
theorem never62 (m : Machine) (hm : compatible p62 m) : NeverHalts m := never p62 c62 ok62 m hm
#print axioms never62

/-- 1RB0LC_1RC0LA_0RD0RF_1LD1RB_0RC---_1LB1RE, width 4, 86 abstract states. -/
def p63 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,true,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨false,true,2⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨true,false,1⟩)
  | (5, true) => some (some ⟨true,true,4⟩)
  | _ => none
def c63 : Cert := ⟨3,0x42513f5,0xc5a0ff55,#[.leaf,(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty))),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty))) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)))) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty)) (.branch .leaf (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty))) (.branch .leaf .leaf)))),(.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty))) .empty))),.empty,(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty))) .empty)]⟩
theorem ok63 : check p63 c63 = true := by decide
theorem never63 (m : Machine) (hm : compatible p63 m) : NeverHalts m := never p63 c63 ok63 m hm
#print axioms never63

/-- 1RB0LC_1RC0LA_0RD0RF_1LD1RB_1RC---_1LE0RC, width 1, 27 abstract states. -/
def p64 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,true,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,2⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨true,false,4⟩)
  | (5, true) => some (some ⟨false,true,2⟩)
  | _ => none
def c64 : Cert := ⟨0,0xf,0xf,#[.leaf,(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),.empty,(.branch .leaf .leaf),(.branch .leaf .leaf)]⟩
theorem ok64 : check p64 c64 = true := by decide
theorem never64 (m : Machine) (hm : compatible p64 m) : NeverHalts m := never p64 c64 ok64 m hm
#print axioms never64

/-- 1RB0LC_1RC0LA_0RD0RF_1LD1RB_1LB---_1RE0RC, width 4, 116 abstract states. -/
def p65 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨false,true,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,false,1⟩)
  | (4, true) => none
  | (5, false) => some (some ⟨true,true,4⟩)
  | (5, true) => some (some ⟨false,true,2⟩)
  | _ => none
def c65 : Cert := ⟨3,0xed0a50cf,0xf2005155,#[(.branch (.branch .leaf (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) (.branch .empty (.branch .leaf (.branch .empty .leaf)))) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .leaf .leaf)))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))))),(.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .leaf .leaf))) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty (.branch .leaf (.branch .empty .leaf)))) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) .empty))) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch .empty .leaf)))))),(.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .leaf .leaf))) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty)))))]⟩
theorem ok65 : check p65 c65 = true := by decide
theorem never65 (m : Machine) (hm : compatible p65 m) : NeverHalts m := never p65 c65 ok65 m hm
#print axioms never65

/-- 1RB0LC_1RC0LA_0RD1RF_1LD1RB_---1LB_1LE1RB, width 1, 28 abstract states. -/
def p66 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,true,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => none
  | (4, true) => some (some ⟨true,false,1⟩)
  | (5, false) => some (some ⟨true,false,4⟩)
  | (5, true) => some (some ⟨true,true,1⟩)
  | _ => none
def c66 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem ok66 : check p66 c66 = true := by decide
theorem never66 (m : Machine) (hm : compatible p66 m) : NeverHalts m := never p66 c66 ok66 m hm
#print axioms never66

/-- 1RB0LC_1RC0LA_0RD1RF_1LD1RB_1RC1RF_0RE---, width 3, 59 abstract states. -/
def p67 : PartialMachine := fun s => match s with
  | (0, false) => some (some ⟨true,true,1⟩)
  | (0, true) => some (some ⟨false,false,2⟩)
  | (1, false) => some (some ⟨true,true,2⟩)
  | (1, true) => some (some ⟨false,false,0⟩)
  | (2, false) => some (some ⟨false,true,3⟩)
  | (2, true) => some (some ⟨true,true,5⟩)
  | (3, false) => some (some ⟨true,false,3⟩)
  | (3, true) => some (some ⟨true,true,1⟩)
  | (4, false) => some (some ⟨true,true,2⟩)
  | (4, true) => some (some ⟨true,true,5⟩)
  | (5, false) => some (some ⟨false,true,4⟩)
  | (5, true) => none
  | _ => none
def c67 : Cert := ⟨2,0x1cf5,0xc5f5,#[.leaf,(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch .leaf (.branch (.branch .leaf .leaf) .leaf))) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch .leaf (.branch (.branch .leaf .leaf) .leaf))) (.branch .leaf .leaf))),(.branch .empty (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) .empty)),.empty]⟩
theorem ok67 : check p67 c67 = true := by decide
theorem never67 (m : Machine) (hm : compatible p67 m) : NeverHalts m := never p67 c67 ok67 m hm
#print axioms never67
end BB6.Agent24Raw45NGram
