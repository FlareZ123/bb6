import SweepCert

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent47R3Grand
open BB6Coverage Agent50Zipper BB6Coverage.Agent47SweepCert

def bits (s : String) : List Bool := s.toList.map (· == '1')
def word (chunks : List (Bool × String)) : Word :=
  chunks.flatMap fun (r,s) => if r then [.repeat (bits s)] else lit (bits s)
def sw (left : Bool) (k : Nat) (P X Q Y : String) (L R : Word) : Instr :=
  .sweep ⟨left,k,bits P,bits X,bits Q,bits Y,L,R⟩

def table (a1 : Move) (d1 f0 : Option Move) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some a1)
  | 1,false => some (some ⟨false,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,1⟩)
  | 3,true => d1.map some
  | 4,false => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => f0.map some
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def v0LC_1LC : PartialMachine := table ⟨false,false,2⟩ none (some ⟨true,false,2⟩)
def v0LC_1LCCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"11111111"),(false,"01")])⟩,16,(-4),2,[
    sw false 40 "1111" "11111111" "1" "11111111" (word [(false,"01")]) (word [(false,"0")]),
    .atom 19,
    sw true 8 "111111" "11111111" "" "11111111" (word [(false,"0")]) (word [(false,"0")]),
    .atom 9,
    sw false 40 "1111111" "11111111" "1" "11111111" (word [(false,"0")]) (word [(false,"0")]),
    .atom 37,
    sw true 8 "11111111" "11111111" "" "11111111" (word [(false,"0")]) (word [(false,"011")]),
    .atom 11,
    sw false 40 "111111111" "11111111" "1" "11111111" (word [(false,"011")]) (word [(false,"0")]),
    .atom 44,
    sw true 8 "11111111111" "11111111" "" "11111111" (word [(false,"0")]) (word [(false,"01")]),
    .atom 12]⟩

theorem v0LC_1LC_defined : ∀ n, ∃ z, zrun v0LC_1LC n start = some z :=
  Cert.sound v0LC_1LC v0LC_1LCCert (by decide)
#print axioms v0LC_1LC_defined

def v0LC_1RA : PartialMachine := table ⟨false,false,2⟩ none (some ⟨true,true,0⟩)
def v0LC_1RACert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"11111111"),(false,"01")])⟩,16,(-4),4,[
    sw false 24 "11" "11111111" "11" "11111111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 11,
    sw true 8 "11111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"0")]),
    .atom 11,
    sw false 24 "11111" "11111111" "11" "11111111" (word [(false,"0")]) (word [(false,"10")]),
    .atom 23,
    sw true 8 "1111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"011")]),
    .atom 13,
    sw false 24 "1111111" "11111111" "11" "11111111" (word [(false,"011")]) (word [(false,"10")]),
    .atom 26,
    sw true 8 "1111111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 12]⟩

theorem v0LC_1RA_defined : ∀ n, ∃ z, zrun v0LC_1RA n start = some z :=
  Cert.sound v0LC_1RA v0LC_1RACert (by decide)
#print axioms v0LC_1RA_defined

def v0RD_0LE : PartialMachine := table ⟨false,true,3⟩ (some ⟨false,false,4⟩) none
def v0RD_0LECert : Cert :=
  ⟨⟨3,[],(word [(false,"1101"),(true,"101"),(false,"010"),(true,"0"),(false,"1")])⟩,26,(-6),2,[
    sw false 5 "1101" "101" "1" "011" (word [(false,"010"),(true,"0"),(false,"1")]) (word [(false,"0")]),
    .atom 11,
    sw true 3 "1011" "011" "" "011" (word [(false,"0")]) (word [(false,"1100"),(true,"0"),(false,"1")]),
    .atom 7,
    sw false 5 "11011" "011" "1" "011" (word [(false,"1100"),(true,"0"),(false,"1")]) (word [(false,"0")]),
    .atom 9,
    sw true 3 "011011" "011" "" "101" (word [(false,"0")]) (word [(false,"0100"),(true,"0"),(false,"1")]),
    .atom 7]⟩

theorem v0RD_0LE_defined : ∀ n, ∃ z, zrun v0RD_0LE n start = some z :=
  Cert.sound v0RD_0LE v0RD_0LECert (by decide)
#print axioms v0RD_0LE_defined

def v0RE_1RD : PartialMachine := table ⟨false,true,4⟩ (some ⟨true,true,3⟩) none
def v0RE_1RDCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"111"),(false,"01"),(true,"111")])⟩,16,(-4),7,[
    sw false 3 "111" "111" "1" "111" (word [(false,"01"),(true,"111")]) (word [(false,"10")]),
    .atom 6,
    sw true 3 "111" "111" "" "111" (word [(false,"10")]) (word [(false,"011"),(true,"111")]),
    .atom 12,
    sw false 3 "1111" "111" "1" "111" (word [(false,"011"),(true,"111")]) (word [(false,"10")]),
    .atom 7,
    sw true 3 "1111" "111" "" "111" (word [(false,"10")]) (word [(false,"0111"),(true,"111")]),
    .atom 13,
    sw false 3 "11111" "111" "1" "111" (word [(false,"0111"),(true,"111")]) (word [(false,"10")]),
    .atom 8,
    sw true 3 "11111" "111" "" "111" (word [(false,"10")]) (word [(false,"01111"),(true,"111")]),
    .atom 7]⟩

theorem v0RE_1RD_defined : ∀ n, ∃ z, zrun v0RE_1RD n start = some z :=
  Cert.sound v0RE_1RD v0RE_1RDCert (by decide)
#print axioms v0RE_1RD_defined

def v1LC : PartialMachine := table ⟨true,false,2⟩ none none
def v1LCCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"11111111"),(false,"01")])⟩,16,(-4),2,[
    sw false 24 "1111" "11111111" "1" "11111111" (word [(false,"01")]) (word [(false,"0")]),
    .atom 13,
    sw true 8 "111111" "11111111" "" "11111111" (word [(false,"0")]) (word [(false,"0")]),
    .atom 9,
    sw false 24 "1111111" "11111111" "1" "11111111" (word [(false,"0")]) (word [(false,"0")]),
    .atom 25,
    sw true 8 "11111111" "11111111" "" "11111111" (word [(false,"0")]) (word [(false,"011")]),
    .atom 11,
    sw false 24 "111111111" "11111111" "1" "11111111" (word [(false,"011")]) (word [(false,"0")]),
    .atom 28,
    sw true 8 "11111111111" "11111111" "" "11111111" (word [(false,"0")]) (word [(false,"01")]),
    .atom 12]⟩

theorem v1LC_defined : ∀ n, ∃ z, zrun v1LC n start = some z :=
  Cert.sound v1LC v1LCCert (by decide)
#print axioms v1LC_defined

def v1LD_1RD : PartialMachine := table ⟨true,false,3⟩ (some ⟨true,true,3⟩) none
def v1LD_1RDCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"111"),(false,"01"),(true,"111")])⟩,16,(-4),5,[
    sw false 3 "111" "111" "1" "111" (word [(false,"01"),(true,"111")]) (word [(false,"10")]),
    .atom 6,
    sw true 3 "111" "111" "" "111" (word [(false,"10")]) (word [(false,"011"),(true,"111")]),
    .atom 10,
    sw false 3 "1111" "111" "1" "111" (word [(false,"011"),(true,"111")]) (word [(false,"10")]),
    .atom 7,
    sw true 3 "1111" "111" "" "111" (word [(false,"10")]) (word [(false,"0111"),(true,"111")]),
    .atom 11,
    sw false 3 "11111" "111" "1" "111" (word [(false,"0111"),(true,"111")]) (word [(false,"10")]),
    .atom 8,
    sw true 3 "11111" "111" "" "111" (word [(false,"10")]) (word [(false,"01111"),(true,"111")]),
    .atom 7]⟩

theorem v1LD_1RD_defined : ∀ n, ∃ z, zrun v1LD_1RD n start = some z :=
  Cert.sound v1LD_1RD v1LD_1RDCert (by decide)
#print axioms v1LD_1RD_defined

def v1LD_1RF : PartialMachine := table ⟨true,false,3⟩ (some ⟨true,true,5⟩) none
def v1LD_1RFCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"11111111"),(false,"01")])⟩,16,(-4),3,[
    sw false 24 "111" "11111111" "1" "11111111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 12,
    sw true 8 "11111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"0")]),
    .atom 10,
    sw false 24 "111111" "11111111" "1" "11111111" (word [(false,"0")]) (word [(false,"10")]),
    .atom 24,
    sw true 8 "1111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"011")]),
    .atom 12,
    sw false 24 "11111111" "11111111" "1" "11111111" (word [(false,"011")]) (word [(false,"10")]),
    .atom 27,
    sw true 8 "1111111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 12]⟩

theorem v1LD_1RF_defined : ∀ n, ∃ z, zrun v1LD_1RF n start = some z :=
  Cert.sound v1LD_1RF v1LD_1RFCert (by decide)
#print axioms v1LD_1RF_defined

def v1RA : PartialMachine := table ⟨true,true,0⟩ none none
def v1RACert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"11111111"),(false,"01")])⟩,16,(-4),4,[
    sw false 8 "11" "11111111" "1" "11111111" (word [(false,"01")]) (word [(false,"110")]),
    .atom 5,
    sw true 8 "1111" "11111111" "" "11111111" (word [(false,"110")]) (word [(false,"0")]),
    .atom 11,
    sw false 8 "11111" "11111111" "1" "11111111" (word [(false,"0")]) (word [(false,"110")]),
    .atom 11,
    sw true 8 "111111" "11111111" "" "11111111" (word [(false,"110")]) (word [(false,"011")]),
    .atom 13,
    sw false 8 "1111111" "11111111" "1" "11111111" (word [(false,"011")]) (word [(false,"110")]),
    .atom 10,
    sw true 8 "111111111" "11111111" "" "11111111" (word [(false,"110")]) (word [(false,"01")]),
    .atom 12]⟩

theorem v1RA_defined : ∀ n, ∃ z, zrun v1RA n start = some z :=
  Cert.sound v1RA v1RACert (by decide)
#print axioms v1RA_defined

def v1RC_1LB : PartialMachine := table ⟨true,true,2⟩ none (some ⟨true,false,1⟩)
def v1RC_1LBCert : Cert :=
  ⟨⟨4,(word [(false,"0")]),(word [(false,"11111111"),(true,"111111111111"),(false,"011")])⟩,55,(-7),3,[
    sw false 12 "111111111" "111111111111" "1" "111111111111" (word [(false,"011")]) (word [(false,"0")]),
    .atom 12,
    sw true 12 "111111111" "111111111111" "" "111111111111" (word [(false,"0")]) (word [(false,"0111")]),
    .atom 12,
    sw false 12 "1111111111" "111111111111" "1" "111111111111" (word [(false,"0111")]) (word [(false,"0")]),
    .atom 13,
    sw true 12 "111111111111" "111111111111" "" "111111111111" (word [(false,"0")]) (word [(false,"011")]),
    .atom 15,
    sw false 12 "1111111111111" "111111111111" "1" "111111111111" (word [(false,"011")]) (word [(false,"0")]),
    .atom 16,
    sw true 12 "111111111111111" "111111111111" "" "111111111111" (word [(false,"0")]) (word [(false,"01")]),
    .atom 18,
    sw false 12 "1111111111111111" "111111111111" "1" "111111111111" (word [(false,"01")]) (word [(false,"0")]),
    .atom 19,
    sw true 12 "111111111111111111" "111111111111" "" "111111111111" (word [(false,"0")]) (word [(false,"0")]),
    .atom 21,
    sw false 12 "1111111111111111111" "111111111111" "1" "111111111111" (word [(false,"0")]) (word [(false,"0")]),
    .atom 25,
    sw true 12 "11111111111111111111" "111111111111" "" "111111111111" (word [(false,"0")]) (word [(false,"011")]),
    .atom 20]⟩

theorem v1RC_1LB_defined : ∀ n, ∃ z, zrun v1RC_1LB n start = some z :=
  Cert.sound v1RC_1LB v1RC_1LBCert (by decide)
#print axioms v1RC_1LB_defined

def v1RC_1LC : PartialMachine := table ⟨true,true,2⟩ none (some ⟨true,false,2⟩)
def v1RC_1LCCert : Cert :=
  ⟨⟨4,(word [(false,"0")]),(word [(false,"11111111"),(true,"111111"),(false,"011")])⟩,55,(-7),3,[
    sw false 6 "111111111" "111111" "1" "111111" (word [(false,"011")]) (word [(false,"0")]),
    .atom 23,
    sw true 6 "11111111111111" "111111" "" "111111" (word [(false,"0")]) (word [(false,"011")]),
    .atom 14]⟩

theorem v1RC_1LC_defined : ∀ n, ∃ z, zrun v1RC_1LC n start = some z :=
  Cert.sound v1RC_1LC v1RC_1LCCert (by decide)
#print axioms v1RC_1LC_defined

def v1RC_1RA : PartialMachine := table ⟨true,true,2⟩ none (some ⟨true,true,0⟩)
def v1RC_1RACert : Cert :=
  ⟨⟨4,(word [(false,"0")]),(word [(false,"11111111"),(true,"111111"),(false,"011")])⟩,55,(-7),3,[
    sw false 6 "111111111" "111111" "1" "111111" (word [(false,"011")]) (word [(false,"0")]),
    .atom 19,
    sw true 6 "11111111111111" "111111" "" "111111" (word [(false,"0")]) (word [(false,"011")]),
    .atom 14]⟩

theorem v1RC_1RA_defined : ∀ n, ∃ z, zrun v1RC_1RA n start = some z :=
  Cert.sound v1RC_1RA v1RC_1RACert (by decide)
#print axioms v1RC_1RA_defined

def v1RD_1LC : PartialMachine := table ⟨true,true,3⟩ (some ⟨true,false,2⟩) none
def v1RD_1LCCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"1111"),(false,"01")])⟩,16,(-4),2,[
    sw false 8 "1111" "1111" "1" "1111" (word [(false,"01")]) (word [(false,"0")]),
    .atom 9,
    sw true 4 "1111" "1111" "" "1111" (word [(false,"0")]) (word [(false,"011")]),
    .atom 7,
    sw false 8 "11111" "1111" "1" "1111" (word [(false,"011")]) (word [(false,"0")]),
    .atom 12,
    sw true 4 "1111111" "1111" "" "1111" (word [(false,"0")]) (word [(false,"01")]),
    .atom 8]⟩

theorem v1RD_1LC_defined : ∀ n, ∃ z, zrun v1RD_1LC n start = some z :=
  Cert.sound v1RD_1LC v1RD_1LCCert (by decide)
#print axioms v1RD_1LC_defined

def v1RD_1LF : PartialMachine := table ⟨true,true,3⟩ (some ⟨true,false,5⟩) none
def v1RD_1LFCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"111"),(false,"01"),(true,"111")])⟩,16,(-4),3,[
    sw false 9 "111" "111" "1" "111" (word [(false,"01"),(true,"111")]) (word [(false,"10")]),
    .atom 10,
    sw true 3 "111" "111" "" "111" (word [(false,"10")]) (word [(false,"011"),(true,"111")]),
    .atom 8,
    sw false 9 "1111" "111" "1" "111" (word [(false,"011"),(true,"111")]) (word [(false,"10")]),
    .atom 13,
    sw true 3 "1111" "111" "" "111" (word [(false,"10")]) (word [(false,"0111"),(true,"111")]),
    .atom 9,
    sw false 9 "11111" "111" "1" "111" (word [(false,"0111"),(true,"111")]) (word [(false,"10")]),
    .atom 16,
    sw true 3 "11111" "111" "" "111" (word [(false,"10")]) (word [(false,"01111"),(true,"111")]),
    .atom 7]⟩

theorem v1RD_1LF_defined : ∀ n, ∃ z, zrun v1RD_1LF n start = some z :=
  Cert.sound v1RD_1LF v1RD_1LFCert (by decide)
#print axioms v1RD_1LF_defined

def v1RD_1RA : PartialMachine := table ⟨true,true,3⟩ (some ⟨true,true,0⟩) none
def v1RD_1RACert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"1111"),(false,"01")])⟩,16,(-4),4,[
    sw false 4 "11" "1111" "1" "1111" (word [(false,"01")]) (word [(false,"110")]),
    .atom 5,
    sw true 4 "11" "1111" "" "1111" (word [(false,"110")]) (word [(false,"011")]),
    .atom 9,
    sw false 4 "111" "1111" "1" "1111" (word [(false,"011")]) (word [(false,"110")]),
    .atom 6,
    sw true 4 "11111" "1111" "" "1111" (word [(false,"110")]) (word [(false,"01")]),
    .atom 8]⟩

theorem v1RD_1RA_defined : ∀ n, ∃ z, zrun v1RD_1RA n start = some z :=
  Cert.sound v1RD_1RA v1RD_1RACert (by decide)
#print axioms v1RD_1RA_defined

def v1RD_1RD : PartialMachine := table ⟨true,true,3⟩ (some ⟨true,true,3⟩) none
def v1RD_1RDCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"111"),(false,"01"),(true,"111")])⟩,16,(-4),5,[
    sw false 3 "1" "111" "1" "111" (word [(false,"01"),(true,"111")]) (word [(false,"1110")]),
    .atom 4,
    sw true 3 "1" "111" "" "111" (word [(false,"1110")]) (word [(false,"011"),(true,"111")]),
    .atom 10,
    sw false 3 "11" "111" "1" "111" (word [(false,"011"),(true,"111")]) (word [(false,"1110")]),
    .atom 5,
    sw true 3 "11" "111" "" "111" (word [(false,"1110")]) (word [(false,"0111"),(true,"111")]),
    .atom 11,
    sw false 3 "111" "111" "1" "111" (word [(false,"0111"),(true,"111")]) (word [(false,"1110")]),
    .atom 6,
    sw true 3 "111" "111" "" "111" (word [(false,"1110")]) (word [(false,"01111"),(true,"111")]),
    .atom 7]⟩

theorem v1RD_1RD_defined : ∀ n, ∃ z, zrun v1RD_1RD n start = some z :=
  Cert.sound v1RD_1RD v1RD_1RDCert (by decide)
#print axioms v1RD_1RD_defined

def v1RF_0LE : PartialMachine := table ⟨true,true,5⟩ none (some ⟨false,false,4⟩)
def v1RF_0LECert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"111111"),(false,"01")])⟩,16,(-4),3,[
    sw false 6 "111" "111111" "1" "111111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 5,
    sw true 6 "1111" "111111" "" "111111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 9,
    sw false 6 "11111" "111111" "1" "111111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 7,
    sw true 6 "111111" "111111" "" "111111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 11,
    sw false 6 "1111111" "111111" "1" "111111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 9,
    sw true 6 "11111111" "111111" "" "111111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 10]⟩

theorem v1RF_0LE_defined : ∀ n, ∃ z, zrun v1RF_0LE n start = some z :=
  Cert.sound v1RF_0LE v1RF_0LECert (by decide)
#print axioms v1RF_0LE_defined

def v1RF_0LF : PartialMachine := table ⟨true,true,5⟩ none (some ⟨false,false,5⟩)
def v1RF_0LFCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"11111111"),(false,"01")])⟩,16,(-4),3,[
    sw false 8 "111" "11111111" "1" "11111111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 8,
    sw true 8 "11111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"0")]),
    .atom 10,
    sw false 8 "111111" "11111111" "1" "11111111" (word [(false,"0")]) (word [(false,"10")]),
    .atom 12,
    sw true 8 "1111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"011")]),
    .atom 12,
    sw false 8 "11111111" "11111111" "1" "11111111" (word [(false,"011")]) (word [(false,"10")]),
    .atom 11,
    sw true 8 "1111111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 12]⟩

theorem v1RF_0LF_defined : ∀ n, ∃ z, zrun v1RF_0LF n start = some z :=
  Cert.sound v1RF_0LF v1RF_0LFCert (by decide)
#print axioms v1RF_0LF_defined

def v1RF_1LA : PartialMachine := table ⟨true,true,5⟩ none (some ⟨true,false,0⟩)
def v1RF_1LACert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"11111111"),(false,"01")])⟩,16,(-4),3,[
    sw false 8 "111" "11111111" "1" "11111111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 16,
    sw true 8 "1111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"011")]),
    .atom 12,
    sw false 8 "11111111" "11111111" "1" "11111111" (word [(false,"011")]) (word [(false,"10")]),
    .atom 11,
    sw true 8 "1111111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 12]⟩

theorem v1RF_1LA_defined : ∀ n, ∃ z, zrun v1RF_1LA n start = some z :=
  Cert.sound v1RF_1LA v1RF_1LACert (by decide)
#print axioms v1RF_1LA_defined

def v1RF_1LB : PartialMachine := table ⟨true,true,5⟩ none (some ⟨true,false,1⟩)
def v1RF_1LBCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"1111"),(false,"01")])⟩,16,(-4),3,[
    sw false 4 "111" "1111" "1" "1111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 6,
    sw true 4 "111" "1111" "" "1111" (word [(false,"10")]) (word [(false,"011")]),
    .atom 8,
    sw false 4 "1111" "1111" "1" "1111" (word [(false,"011")]) (word [(false,"10")]),
    .atom 7,
    sw true 4 "111111" "1111" "" "1111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 8]⟩

theorem v1RF_1LB_defined : ∀ n, ∃ z, zrun v1RF_1LB n start = some z :=
  Cert.sound v1RF_1LB v1RF_1LBCert (by decide)
#print axioms v1RF_1LB_defined

def v1RF_1LC : PartialMachine := table ⟨true,true,5⟩ none (some ⟨true,false,2⟩)
def v1RF_1LCCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"11111111"),(false,"01")])⟩,16,(-4),3,[
    sw false 8 "111" "11111111" "1" "11111111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 16,
    sw true 8 "1111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"011")]),
    .atom 12,
    sw false 8 "11111111" "11111111" "1" "11111111" (word [(false,"011")]) (word [(false,"10")]),
    .atom 11,
    sw true 8 "1111111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 12]⟩

theorem v1RF_1LC_defined : ∀ n, ∃ z, zrun v1RF_1LC n start = some z :=
  Cert.sound v1RF_1LC v1RF_1LCCert (by decide)
#print axioms v1RF_1LC_defined

def v1RF_1LE : PartialMachine := table ⟨true,true,5⟩ none (some ⟨true,false,4⟩)
def v1RF_1LECert : Cert :=
  ⟨⟨1,[],(word [(false,"1111111"),(true,"111111111111"),(false,"11")])⟩,31,(-7),2,[
    sw false 12 "11111" "111111111111" "1" "111111111111" (word [(false,"11")]) (word [(false,"10")]),
    .atom 9,
    sw true 12 "11111111" "111111111111" "" "111111111111" (word [(false,"10")]) (word [(false,"1")]),
    .atom 13,
    sw false 12 "111111111" "111111111111" "1" "111111111111" (word [(false,"1")]) (word [(false,"10")]),
    .atom 16,
    sw true 12 "11111111111" "111111111111" "" "111111111111" (word [(false,"10")]) (word [(false,"011")]),
    .atom 16,
    sw false 12 "111111111111" "111111111111" "1" "111111111111" (word [(false,"011")]) (word [(false,"10")]),
    .atom 15,
    sw true 12 "11111111111111" "111111111111" "" "111111111111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 19,
    sw false 12 "111111111111111" "111111111111" "1" "111111111111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 17,
    sw true 12 "1111111111111111" "111111111111" "" "111111111111" (word [(false,"10")]) (word [(false,"11")]),
    .atom 19]⟩

theorem v1RF_1LE_defined : ∀ n, ∃ z, zrun v1RF_1LE n start = some z :=
  Cert.sound v1RF_1LE v1RF_1LECert (by decide)
#print axioms v1RF_1LE_defined

def v1RF_1RA : PartialMachine := table ⟨true,true,5⟩ none (some ⟨true,true,0⟩)
def v1RF_1RACert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"11111111"),(false,"01")])⟩,16,(-4),3,[
    sw false 8 "111" "11111111" "1" "11111111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 12,
    sw true 8 "1111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"011")]),
    .atom 12,
    sw false 8 "11111111" "11111111" "1" "11111111" (word [(false,"011")]) (word [(false,"10")]),
    .atom 11,
    sw true 8 "1111111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 12]⟩

theorem v1RF_1RA_defined : ∀ n, ∃ z, zrun v1RF_1RA n start = some z :=
  Cert.sound v1RF_1RA v1RF_1RACert (by decide)
#print axioms v1RF_1RA_defined

def v1RF_1RB : PartialMachine := table ⟨true,true,5⟩ none (some ⟨true,true,1⟩)
def v1RF_1RBCert : Cert :=
  ⟨⟨3,[],(word [(false,"1111"),(true,"11111111"),(false,"01")])⟩,16,(-4),3,[
    sw false 8 "111" "11111111" "1" "11111111" (word [(false,"01")]) (word [(false,"10")]),
    .atom 6,
    sw true 8 "11111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"0")]),
    .atom 10,
    sw false 8 "111111" "11111111" "1" "11111111" (word [(false,"0")]) (word [(false,"10")]),
    .atom 12,
    sw true 8 "1111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"011")]),
    .atom 12,
    sw false 8 "11111111" "11111111" "1" "11111111" (word [(false,"011")]) (word [(false,"10")]),
    .atom 11,
    sw true 8 "1111111111" "11111111" "" "11111111" (word [(false,"10")]) (word [(false,"01")]),
    .atom 12]⟩

theorem v1RF_1RB_defined : ∀ n, ∃ z, zrun v1RF_1RB n start = some z :=
  Cert.sound v1RF_1RB v1RF_1RBCert (by decide)
#print axioms v1RF_1RB_defined

end BB6Coverage.Agent47R3Grand
