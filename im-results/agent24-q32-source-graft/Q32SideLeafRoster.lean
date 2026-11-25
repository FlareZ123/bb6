import RootFrontier
import TranslatedCycler
import Q32SourceSideGraft

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent24Q32SideLeafRoster

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent32FiniteSource
open BB6.Agent50RootFrontier
open BB6.Agent50TranslatedCycler
open BB6.Agent24Q32SourceSideGraft

/-- Rows are ordered A0,A1,B0,B1,...,F0,F1. A missing row is a source
    cylinder hole, not an assigned halt. -/
def machineFromRows (rows : List (Option Move)) : Machine :=
  fun s => (rows[2 * s.1.val + (if s.2 then 1 else 0)]?).getD none

/-- Reusable adapter: a checked translated-cycle witness becomes a complete
    six-state TNF leaf for every completion of its source partial table. -/
def sourceSideLeafOfCheck (B : Nat) (m : Machine) (right : Bool)
    (entry period budget : Nat)
    (hcheck : translatedCyclerCheck m right entry period budget = true) :
    WeightedTNFCertificate B (sourcePartial m) 6 :=
  sourceSideLeaf
    (hroot := by decide)
    (hsupport := by
      intro s t _
      exact ⟨s.1.isLt, fun mv _ => mv.next.isLt⟩)
    (hnohalt := sourcePartial_noAssignedHalt m)
    m right entry period budget rfl hcheck

structure Q32QueueRecord where
  table : String
  holes : Nat
  cut : Nat
  deriving DecidableEq

structure Q32SideData where
  index : Nat
  table : String
  holes : Nat
  sourceCut : Nat
  right : Bool
  entry : Nat
  period : Nat
  budget : Nat
  deriving DecidableEq

structure Q32SideLeaf where
  data : Q32SideData
  partial : PartialMachine
  certificate : WeightedTNFCertificate 144 partial 6
  encoding : encodeTable partial = data.table

/-- Exact 84-row source checkpoint export from Agent8PackedChunk2_32_32.v. -/
def q32QueueData : List Q32QueueRecord :=
  [⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LA_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RA_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LB_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RB_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LB_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RB_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LC_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RC_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LC_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RC_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LD_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RD_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LD_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RD_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LE_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RE_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LE_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RE_------", 3, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LF_------", 3, 6⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RF_------", 3, 6⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LF_------", 3, 6⟩,
   ⟨"1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RF_------", 3, 6⟩,
   ⟨"1RB1RD_1RC1LB_0LA0RE_1LA0LB_------_------", 4, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA1LE_1LA0LB_------_------", 4, 5⟩,
   ⟨"1RB1RD_1RC1LB_0LA1RE_1LA0LB_------_------", 4, 5⟩,
   ⟨"1RB1RD_1RC1RB_0LA---_1LA0LB_------_------", 5, 4⟩,
   ⟨"1RB1RD_1RC0LC_0LA---_1LA0LB_------_------", 5, 4⟩,
   ⟨"1RB1RD_1RC0RC_0LA---_1LA0LB_------_------", 5, 4⟩,
   ⟨"1RB1RD_1RC1LC_0LA---_1LA0LB_------_------", 5, 4⟩,
   ⟨"1RB1RD_1RC1RC_0LA---_1LA0LB_------_------", 5, 4⟩,
   ⟨"1RB1RD_1RC0LD_0LA---_1LA0LB_------_------", 5, 4⟩,
   ⟨"1RB1RD_1RC0RD_0LA---_1LA0LB_------_------", 5, 4⟩,
   ⟨"1RB1RD_1RC1LD_0LA---_1LA0LB_------_------", 5, 4⟩,
   ⟨"1RB1RD_1RC1RD_0LA---_1LA0LB_------_------", 5, 4⟩,
   ⟨"1RB1RD_1RC0LE_0LA---_1LA0LB_------_------", 5, 5⟩,
   ⟨"1RB1RD_1RC0RE_0LA---_1LA0LB_------_------", 5, 5⟩,
   ⟨"1RB1RD_1RC1LE_0LA---_1LA0LB_------_------", 5, 5⟩,
   ⟨"1RB1RD_1RC1RE_0LA---_1LA0LB_------_------", 5, 5⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA0RB_------_------", 6, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA1LB_------_------", 6, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA1RB_------_------", 6, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA0LC_------_------", 6, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA0RC_------_------", 6, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA1LC_------_------", 6, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA1RC_------_------", 6, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA0LD_------_------", 6, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA0RD_------_------", 6, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA1LD_------_------", 6, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA1RD_------_------", 6, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA0LE_------_------", 6, 5⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA0RE_------_------", 6, 5⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA1LE_------_------", 6, 5⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LA1RE_------_------", 6, 5⟩,
   ⟨"1RB1RD_1RC---_0LA---_1RA---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_0LB---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_0RB---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LB---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1RB---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_0LC---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_0RC---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LC---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1RC---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_0LD---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_0RD---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LD---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_1RD---_------_------", 7, 4⟩,
   ⟨"1RB1RD_1RC---_0LA---_0LE---_------_------", 7, 5⟩,
   ⟨"1RB1RD_1RC---_0LA---_0RE---_------_------", 7, 5⟩,
   ⟨"1RB1RD_1RC---_0LA---_1LE---_------_------", 7, 5⟩,
   ⟨"1RB1RD_1RC---_0LA---_1RE---_------_------", 7, 5⟩,
   ⟨"1RB1LD_1RC---_0LA---_---0LA_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---0RA_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---1LA_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---1RA_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---0LB_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---0RB_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---1LB_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---1RB_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---0LC_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---0RC_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---1LC_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---1RC_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---0LD_------_------", 7, 4⟩,
   ⟨"1RB1LD_1RC---_0LA---_---0RD_------_------", 7, 4⟩]

theorem q32QueueData_length : q32QueueData.length = 84 := by decide

/-- The 32 SWside source witnesses from Agent47SourceChunk2.v, annotated with
    their exact indices and (holes, introduced-state-cut) metadata in q32. -/
def q32SideData : List Q32SideData :=
  [⟨0, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LA_------", 3, 5, false, 7, 6, 0⟩,
   ⟨1, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RA_------", 3, 5, false, 7, 7, 0⟩,
   ⟨2, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LB_------", 3, 5, false, 8, 10, 0⟩,
   ⟨3, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RB_------", 3, 5, true, 12, 10, 0⟩,
   ⟨4, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LB_------", 3, 5, false, 9, 3, 1⟩,
   ⟨6, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LC_------", 3, 5, false, 0, 13, 2⟩,
   ⟨9, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RC_------", 3, 5, false, 8, 9, 0⟩,
   ⟨10, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LD_------", 3, 5, false, 7, 7, 0⟩,
   ⟨11, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RD_------", 3, 5, false, 7, 7, 0⟩,
   ⟨12, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LD_------", 3, 5, false, 7, 7, 0⟩,
   ⟨13, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RD_------", 3, 5, false, 8, 7, 0⟩,
   ⟨25, "1RB1RD_1RC1RB_0LA---_1LA0LB_------_------", 5, 4, true, 1, 7, 0⟩,
   ⟨27, "1RB1RD_1RC0RC_0LA---_1LA0LB_------_------", 5, 4, true, 0, 9, 0⟩,
   ⟨29, "1RB1RD_1RC1RC_0LA---_1LA0LB_------_------", 5, 4, true, 2, 6, 1⟩,
   ⟨30, "1RB1RD_1RC0LD_0LA---_1LA0LB_------_------", 5, 4, false, 7, 11, 0⟩,
   ⟨31, "1RB1RD_1RC0RD_0LA---_1LA0LB_------_------", 5, 4, true, 7, 3, 0⟩,
   ⟨32, "1RB1RD_1RC1LD_0LA---_1LA0LB_------_------", 5, 4, false, 7, 11, 0⟩,
   ⟨33, "1RB1RD_1RC1RD_0LA---_1LA0LB_------_------", 5, 4, true, 4, 4, 1⟩,
   ⟨38, "1RB1RD_1RC---_0LA---_1LA0RB_------_------", 6, 4, true, 1, 6, 0⟩,
   ⟨40, "1RB1RD_1RC---_0LA---_1LA1RB_------_------", 6, 4, true, 1, 6, 0⟩,
   ⟨42, "1RB1RD_1RC---_0LA---_1LA0RC_------_------", 6, 4, true, 0, 8, 0⟩,
   ⟨44, "1RB1RD_1RC---_0LA---_1LA1RC_------_------", 6, 4, true, 2, 5, 1⟩,
   ⟨48, "1RB1RD_1RC---_0LA---_1LA1RD_------_------", 6, 4, true, 4, 3, 1⟩,
   ⟨53, "1RB1RD_1RC---_0LA---_1RA---_------_------", 7, 4, true, 0, 5, 0⟩,
   ⟨55, "1RB1RD_1RC---_0LA---_0RB---_------_------", 7, 4, true, 1, 4, 0⟩,
   ⟨57, "1RB1RD_1RC---_0LA---_1RB---_------_------", 7, 4, true, 1, 4, 0⟩,
   ⟨59, "1RB1RD_1RC---_0LA---_0RC---_------_------", 7, 4, true, 0, 6, 0⟩,
   ⟨61, "1RB1RD_1RC---_0LA---_1RC---_------_------", 7, 4, true, 2, 3, 1⟩,
   ⟨63, "1RB1RD_1RC---_0LA---_0RD---_------_------", 7, 4, true, 4, 1, 0⟩,
   ⟨65, "1RB1RD_1RC---_0LA---_1RD---_------_------", 7, 4, true, 4, 1, 0⟩,
   ⟨73, "1RB1LD_1RC---_0LA---_---1RA_------_------", 7, 4, true, 3, 2, 1⟩,
   ⟨78, "1RB1LD_1RC---_0LA---_---0LC_------_------", 7, 4, false, 0, 6, 2⟩]

theorem q32SideData_length : q32SideData.length = 32 := by decide

theorem q32SideData_indices_nodup :
    (q32SideData.map Q32SideData.index).Nodup := by decide

def q32SideDataMatches (d : Q32SideData) : Bool :=
  match q32QueueData[d.index]? with
  | some q => q.table == d.table && q.holes == d.holes && q.cut == d.sourceCut
  | none => false

theorem q32SideData_sourceExact :
    q32SideData.all q32SideDataMatches = true := by decide

def q32SideLeaf00 : Q32SideLeaf :=
  { data := ⟨0, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LA_------", 3, 5, false, 7, 6, 0⟩,
    partial := samplePartial,
    certificate := sampleSourceLeaf 144,
    encoding := sampleSourceEncoding }

def q32SideMachine01 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,false,1⟩, some ⟨false,false,0⟩, some ⟨false,false,4⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, some ⟨true,true,0⟩, none, none]

def q32SideLeaf01 : Q32SideLeaf :=
  { data := ⟨1, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RA_------", 3, 5, false, 7, 7, 0⟩,
    partial := sourcePartial q32SideMachine01,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine01 false 7 7 0 (by decide),
    encoding := by decide }

def q32SideMachine02 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,false,1⟩, some ⟨false,false,0⟩, some ⟨false,false,4⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, some ⟨false,false,1⟩, none, none]

def q32SideLeaf02 : Q32SideLeaf :=
  { data := ⟨2, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LB_------", 3, 5, false, 8, 10, 0⟩,
    partial := sourcePartial q32SideMachine02,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine02 false 8 10 0 (by decide),
    encoding := by decide }

def q32SideMachine03 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,false,1⟩, some ⟨false,false,0⟩, some ⟨false,false,4⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, some ⟨false,true,1⟩, none, none]

def q32SideLeaf03 : Q32SideLeaf :=
  { data := ⟨3, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RB_------", 3, 5, true, 12, 10, 0⟩,
    partial := sourcePartial q32SideMachine03,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine03 true 12 10 0 (by decide),
    encoding := by decide }

def q32SideMachine04 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,false,1⟩, some ⟨false,false,0⟩, some ⟨false,false,4⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, some ⟨true,false,1⟩, none, none]

def q32SideLeaf04 : Q32SideLeaf :=
  { data := ⟨4, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LB_------", 3, 5, false, 9, 3, 1⟩,
    partial := sourcePartial q32SideMachine04,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine04 false 9 3 1 (by decide),
    encoding := by decide }

def q32SideMachine05 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,false,1⟩, some ⟨false,false,0⟩, some ⟨false,false,4⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, some ⟨false,false,2⟩, none, none]

def q32SideLeaf05 : Q32SideLeaf :=
  { data := ⟨6, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LC_------", 3, 5, false, 0, 13, 2⟩,
    partial := sourcePartial q32SideMachine05,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine05 false 0 13 2 (by decide),
    encoding := by decide }

def q32SideMachine06 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,false,1⟩, some ⟨false,false,0⟩, some ⟨false,false,4⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, some ⟨true,true,2⟩, none, none]

def q32SideLeaf06 : Q32SideLeaf :=
  { data := ⟨9, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RC_------", 3, 5, false, 8, 9, 0⟩,
    partial := sourcePartial q32SideMachine06,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine06 false 8 9 0 (by decide),
    encoding := by decide }

def q32SideMachine07 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,false,1⟩, some ⟨false,false,0⟩, some ⟨false,false,4⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, some ⟨false,false,3⟩, none, none]

def q32SideLeaf07 : Q32SideLeaf :=
  { data := ⟨10, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0LD_------", 3, 5, false, 7, 7, 0⟩,
    partial := sourcePartial q32SideMachine07,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine07 false 7 7 0 (by decide),
    encoding := by decide }

def q32SideMachine08 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,false,1⟩, some ⟨false,false,0⟩, some ⟨false,false,4⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, some ⟨false,true,3⟩, none, none]

def q32SideLeaf08 : Q32SideLeaf :=
  { data := ⟨11, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RD_------", 3, 5, false, 7, 7, 0⟩,
    partial := sourcePartial q32SideMachine08,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine08 false 7 7 0 (by decide),
    encoding := by decide }

def q32SideMachine09 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,false,1⟩, some ⟨false,false,0⟩, some ⟨false,false,4⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, some ⟨true,false,3⟩, none, none]

def q32SideLeaf09 : Q32SideLeaf :=
  { data := ⟨12, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1LD_------", 3, 5, false, 7, 7, 0⟩,
    partial := sourcePartial q32SideMachine09,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine09 false 7 7 0 (by decide),
    encoding := by decide }

def q32SideMachine10 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,false,1⟩, some ⟨false,false,0⟩, some ⟨false,false,4⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, some ⟨true,true,3⟩, none, none]

def q32SideLeaf10 : Q32SideLeaf :=
  { data := ⟨13, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RD_------", 3, 5, false, 8, 7, 0⟩,
    partial := sourcePartial q32SideMachine10,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine10 false 8 7 0 (by decide),
    encoding := by decide }

def q32SideMachine11 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,true,1⟩, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, none, none, none]

def q32SideLeaf11 : Q32SideLeaf :=
  { data := ⟨25, "1RB1RD_1RC1RB_0LA---_1LA0LB_------_------", 5, 4, true, 1, 7, 0⟩,
    partial := sourcePartial q32SideMachine11,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine11 true 1 7 0 (by decide),
    encoding := by decide }

def q32SideMachine12 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨false,true,2⟩, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, none, none, none]

def q32SideLeaf12 : Q32SideLeaf :=
  { data := ⟨27, "1RB1RD_1RC0RC_0LA---_1LA0LB_------_------", 5, 4, true, 0, 9, 0⟩,
    partial := sourcePartial q32SideMachine12,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine12 true 0 9 0 (by decide),
    encoding := by decide }

def q32SideMachine13 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,true,2⟩, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, none, none, none]

def q32SideLeaf13 : Q32SideLeaf :=
  { data := ⟨29, "1RB1RD_1RC1RC_0LA---_1LA0LB_------_------", 5, 4, true, 2, 6, 1⟩,
    partial := sourcePartial q32SideMachine13,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine13 true 2 6 1 (by decide),
    encoding := by decide }

def q32SideMachine14 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨false,false,3⟩, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, none, none, none]

def q32SideLeaf14 : Q32SideLeaf :=
  { data := ⟨30, "1RB1RD_1RC0LD_0LA---_1LA0LB_------_------", 5, 4, false, 7, 11, 0⟩,
    partial := sourcePartial q32SideMachine14,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine14 false 7 11 0 (by decide),
    encoding := by decide }

def q32SideMachine15 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨false,true,3⟩, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, none, none, none]

def q32SideLeaf15 : Q32SideLeaf :=
  { data := ⟨31, "1RB1RD_1RC0RD_0LA---_1LA0LB_------_------", 5, 4, true, 7, 3, 0⟩,
    partial := sourcePartial q32SideMachine15,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine15 true 7 3 0 (by decide),
    encoding := by decide }

def q32SideMachine16 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,false,3⟩, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, none, none, none]

def q32SideLeaf16 : Q32SideLeaf :=
  { data := ⟨32, "1RB1RD_1RC1LD_0LA---_1LA0LB_------_------", 5, 4, false, 7, 11, 0⟩,
    partial := sourcePartial q32SideMachine16,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine16 false 7 11 0 (by decide),
    encoding := by decide }

def q32SideMachine17 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, some ⟨true,true,3⟩, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, none, none, none]

def q32SideLeaf17 : Q32SideLeaf :=
  { data := ⟨33, "1RB1RD_1RC1RD_0LA---_1LA0LB_------_------", 5, 4, true, 4, 4, 1⟩,
    partial := sourcePartial q32SideMachine17,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine17 true 4 4 1 (by decide),
    encoding := by decide }

def q32SideMachine18 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨false,true,1⟩, none, none, none, none]

def q32SideLeaf18 : Q32SideLeaf :=
  { data := ⟨38, "1RB1RD_1RC---_0LA---_1LA0RB_------_------", 6, 4, true, 1, 6, 0⟩,
    partial := sourcePartial q32SideMachine18,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine18 true 1 6 0 (by decide),
    encoding := by decide }

def q32SideMachine19 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨true,true,1⟩, none, none, none, none]

def q32SideLeaf19 : Q32SideLeaf :=
  { data := ⟨40, "1RB1RD_1RC---_0LA---_1LA1RB_------_------", 6, 4, true, 1, 6, 0⟩,
    partial := sourcePartial q32SideMachine19,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine19 true 1 6 0 (by decide),
    encoding := by decide }

def q32SideMachine20 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨false,true,2⟩, none, none, none, none]

def q32SideLeaf20 : Q32SideLeaf :=
  { data := ⟨42, "1RB1RD_1RC---_0LA---_1LA0RC_------_------", 6, 4, true, 0, 8, 0⟩,
    partial := sourcePartial q32SideMachine20,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine20 true 0 8 0 (by decide),
    encoding := by decide }

def q32SideMachine21 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨true,true,2⟩, none, none, none, none]

def q32SideLeaf21 : Q32SideLeaf :=
  { data := ⟨44, "1RB1RD_1RC---_0LA---_1LA1RC_------_------", 6, 4, true, 2, 5, 1⟩,
    partial := sourcePartial q32SideMachine21,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine21 true 2 5 1 (by decide),
    encoding := by decide }

def q32SideMachine22 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨true,false,0⟩, some ⟨true,true,3⟩, none, none, none, none]

def q32SideLeaf22 : Q32SideLeaf :=
  { data := ⟨48, "1RB1RD_1RC---_0LA---_1LA1RD_------_------", 6, 4, true, 4, 3, 1⟩,
    partial := sourcePartial q32SideMachine22,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine22 true 4 3 1 (by decide),
    encoding := by decide }

def q32SideMachine23 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨true,true,0⟩, none, none, none, none, none]

def q32SideLeaf23 : Q32SideLeaf :=
  { data := ⟨53, "1RB1RD_1RC---_0LA---_1RA---_------_------", 7, 4, true, 0, 5, 0⟩,
    partial := sourcePartial q32SideMachine23,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine23 true 0 5 0 (by decide),
    encoding := by decide }

def q32SideMachine24 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨false,true,1⟩, none, none, none, none, none]

def q32SideLeaf24 : Q32SideLeaf :=
  { data := ⟨55, "1RB1RD_1RC---_0LA---_0RB---_------_------", 7, 4, true, 1, 4, 0⟩,
    partial := sourcePartial q32SideMachine24,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine24 true 1 4 0 (by decide),
    encoding := by decide }

def q32SideMachine25 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨true,true,1⟩, none, none, none, none, none]

def q32SideLeaf25 : Q32SideLeaf :=
  { data := ⟨57, "1RB1RD_1RC---_0LA---_1RB---_------_------", 7, 4, true, 1, 4, 0⟩,
    partial := sourcePartial q32SideMachine25,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine25 true 1 4 0 (by decide),
    encoding := by decide }

def q32SideMachine26 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨false,true,2⟩, none, none, none, none, none]

def q32SideLeaf26 : Q32SideLeaf :=
  { data := ⟨59, "1RB1RD_1RC---_0LA---_0RC---_------_------", 7, 4, true, 0, 6, 0⟩,
    partial := sourcePartial q32SideMachine26,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine26 true 0 6 0 (by decide),
    encoding := by decide }

def q32SideMachine27 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨true,true,2⟩, none, none, none, none, none]

def q32SideLeaf27 : Q32SideLeaf :=
  { data := ⟨61, "1RB1RD_1RC---_0LA---_1RC---_------_------", 7, 4, true, 2, 3, 1⟩,
    partial := sourcePartial q32SideMachine27,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine27 true 2 3 1 (by decide),
    encoding := by decide }

def q32SideMachine28 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨false,true,3⟩, none, none, none, none, none]

def q32SideLeaf28 : Q32SideLeaf :=
  { data := ⟨63, "1RB1RD_1RC---_0LA---_0RD---_------_------", 7, 4, true, 4, 1, 0⟩,
    partial := sourcePartial q32SideMachine28,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine28 true 4 1 0 (by decide),
    encoding := by decide }

def q32SideMachine29 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, some ⟨true,true,3⟩, none, none, none, none, none]

def q32SideLeaf29 : Q32SideLeaf :=
  { data := ⟨65, "1RB1RD_1RC---_0LA---_1RD---_------_------", 7, 4, true, 4, 1, 0⟩,
    partial := sourcePartial q32SideMachine29,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine29 true 4 1 0 (by decide),
    encoding := by decide }

def q32SideMachine30 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,false,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, none, some ⟨true,true,0⟩, none, none, none, none]

def q32SideLeaf30 : Q32SideLeaf :=
  { data := ⟨73, "1RB1LD_1RC---_0LA---_---1RA_------_------", 7, 4, true, 3, 2, 1⟩,
    partial := sourcePartial q32SideMachine30,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine30 true 3 2 1 (by decide),
    encoding := by decide }

def q32SideMachine31 : Machine :=
  machineFromRows [some ⟨true,true,1⟩, some ⟨true,false,3⟩, some ⟨true,true,2⟩, none, some ⟨false,false,0⟩, none, none, some ⟨false,false,2⟩, none, none, none, none]

def q32SideLeaf31 : Q32SideLeaf :=
  { data := ⟨78, "1RB1LD_1RC---_0LA---_---0LC_------_------", 7, 4, false, 0, 6, 2⟩,
    partial := sourcePartial q32SideMachine31,
    certificate := sourceSideLeafOfCheck 144 q32SideMachine31 false 0 6 2 (by decide),
    encoding := by decide }

def q32SideLeaves : List Q32SideLeaf :=
  [q32SideLeaf00, q32SideLeaf01, q32SideLeaf02, q32SideLeaf03, q32SideLeaf04, q32SideLeaf05, q32SideLeaf06, q32SideLeaf07, q32SideLeaf08, q32SideLeaf09, q32SideLeaf10, q32SideLeaf11, q32SideLeaf12, q32SideLeaf13, q32SideLeaf14, q32SideLeaf15, q32SideLeaf16, q32SideLeaf17, q32SideLeaf18, q32SideLeaf19, q32SideLeaf20, q32SideLeaf21, q32SideLeaf22, q32SideLeaf23, q32SideLeaf24, q32SideLeaf25, q32SideLeaf26, q32SideLeaf27, q32SideLeaf28, q32SideLeaf29, q32SideLeaf30, q32SideLeaf31]

theorem q32SideLeaves_length : q32SideLeaves.length = 32 := by decide

theorem q32SideLeaves_data_exact :
    q32SideLeaves.map Q32SideLeaf.data = q32SideData := by decide

theorem q32SideLeaf_sound (leaf : Q32SideLeaf) (m : Machine)
    (hm : compatible leaf.partial m) : WeightedBound 144 m :=
  leaf.certificate.sound m hm

theorem q32SideLeaves_sound :
    ∀ leaf ∈ q32SideLeaves, ∀ m, compatible leaf.partial m → WeightedBound 144 m := by
  intro leaf hmem m hm
  exact q32SideLeaf_sound leaf m hm

#print axioms q32SideData_sourceExact
#print axioms q32SideLeaves_data_exact
#print axioms q32SideLeaves_sound

end BB6.Agent24Q32SideLeafRoster
