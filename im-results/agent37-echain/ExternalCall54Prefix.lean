import Lean.Elab.Tactic.Omega
import ExternalCall42Prefix
import E2AlternatingAll

set_option maxHeartbeats 80000000
set_option maxRecDepth 24000

namespace BB6.Agent37ExternalCall54

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChainBExit BB6.Agent37EChain169Split
open BB6.Agent37EChain169Split
open BB6.Agent37ExternalCall42

def k43 (z : Nat) : Nat :=
  6692424442727272325364842496*z+6155256915779191050628843867
def k44 (z : Nat) : Nat :=
  17846465180606059534306246656*z+16414018442077842801676916981
def k45 (z : Nat) : Nat :=
  47590573814949492091483324416*z+43770715845540914137805111952
def k46 (z : Nat) : Nat :=
  126908196839865312243955531776*z+116721908921442437700813631874
def k47 (z : Nat) : Nat :=
  338421858239640832650548084736*z+311258423790513167202169684999
def k48 (z : Nat) : Nat :=
  902458288639042220401461559296*z+830022463441368445872452493331
def k49 (z : Nat) : Nat :=
  2406555436370779254403897491456*z+2213393235843649188993206648885
def k50 (z : Nat) : Nat :=
  6417481163655411345077059977216*z+5902381962249731170648551063696
def k51 (z : Nat) : Nat :=
  17113283103081096920205493272576*z+15739685232665949788396136169858
def k52 (z : Nat) : Nat :=
  45635421608216258453881315393536*z+41972493953775866102389696452957
def k53 (z : Nat) : Nat :=
  121694457621910022543683507716096*z+111926650543402309606372523874554
def k54 (z : Nat) : Nat :=
  324518553658426726783156020576256*z+298471068115739492283660063665479

def call42InputA (z : Nat) : Nat :=
  20077273328181816976094527488*z+18465770747337573151886531605

def call54OutputA (z : Nat) : Nat :=
  2596148429267413814265248164610048*z+
    2387768544925915938269280509323837

def call54Tail : List Bool :=
  false :: List.replicate 8 true

def externalCall42To54Time (z : Nat) : Nat :=
  eTime (k43 z) 0 +
  (bTime (k44 z) +
  (bTime (k45 z) +
  (eTime (k46 z) 0 +
  ((12*(k47 z)*(k47 z)+49*(k47 z)+58) +
  (eTime (k48 z) 0 +
  (bTime (k49 z) +
  (bTime (k50 z) +
  (eTime (k51 z) 0 +
  (bTime (k52 z) +
  (eTime (k53 z) 1 +
    BB6.Agent37E2AlternatingAll.time (k54 z) 3 0))))))))))

theorem external_call42_to54 (z : Nat) :
    ObsEq
      (run (externalCall42To54Time z)
        (packet (call42InputA z) 0 6
          [false,true,false,true]))
      (packet (call54OutputA z) 0 8 call54Tail) := by
  have ha43 : call42InputA z = 3*k43 z+4 := by
    simp [call42InputA,k43]; omega
  have ha44 : 8*k43 z+9 = 3*k44 z+2 := by
    simp [k43,k44]; omega
  have ha45 : 8*k44 z+10 = 3*k45 z+2 := by
    simp [k44,k45]; omega
  have ha46 : 8*k45 z+10 = 3*k46 z+4 := by
    simp [k45,k46]; omega
  have ha47 : 8*k46 z+9 = 3*k47 z+4 := by
    simp [k46,k47]; omega
  have ha48 : 8*k47 z+5 = 3*k48 z+4 := by
    simp [k47,k48]; omega
  have ha49 : 8*k48 z+9 = 3*k49 z+2 := by
    simp [k48,k49]; omega
  have ha50 : 8*k49 z+10 = 3*k50 z+2 := by
    simp [k49,k50]; omega
  have ha51 : 8*k50 z+10 = 3*k51 z+4 := by
    simp [k50,k51]; omega
  have ha52 : 8*k51 z+9 = 3*k52 z+2 := by
    simp [k51,k52]; omega
  have ha53 : 8*k52 z+10 = 3*k53 z+4 := by
    simp [k52,k53]; omega
  have ha54 : 8*k53 z+9 = 3*k54 z+4 := by
    simp [k53,k54]; omega
  have hout : 8*k54 z+5 = call54OutputA z := by
    simp [k54,call54OutputA]; omega
  have he43 :
      run (eTime (k43 z) 0)
        (packet (3*k43 z+4) 0 6 [false,true,false,true]) =
      packet (8*k43 z+9) 2 3 [false,true,false,true] := by
    simpa using
      (BB6.Agent31PacketSource.e_packet
        (k43 z) 0 3 [false,true,false,true])
  have hb44 :=
    BB6.Agent31PacketSource.b_packet
      (k44 z) 1 3 [false,true,false,true]
  have hb45 :=
    BB6.Agent31PacketSource.b_packet
      (k45 z) 0 3 [false,true,false,true]
  have he46 :
      run (eTime (k46 z) 0)
        (packet (3*k46 z+4) 0 3 [false,true,false,true]) =
      packet (8*k46 z+9) 2 0 [false,true,false,true] := by
    simpa using
      (BB6.Agent31PacketSource.e_packet
        (k46 z) 0 0 [false,true,false,true])
  have he47 :=
    BB6.Agent37PacketBoundary.e_zero_drop_any
      (k47 z) 2 [false,true]
  have he48 :
      run (eTime (k48 z) 0)
        (packet (3*k48 z+4) 0 11 [false,true]) =
      packet (8*k48 z+9) 2 8 [false,true] := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k48 z) 0 8 [false,true])
  have hb49 :=
    BB6.Agent31PacketSource.b_packet (k49 z) 1 8 [false,true]
  have hb50 :=
    BB6.Agent31PacketSource.b_packet (k50 z) 0 8 [false,true]
  have he51 :
      run (eTime (k51 z) 0)
        (packet (3*k51 z+4) 0 8 [false,true]) =
      packet (8*k51 z+9) 2 5 [false,true] := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k51 z) 0 5 [false,true])
  have hb52 :=
    BB6.Agent31PacketSource.b_packet (k52 z) 1 5 [false,true]
  have he53 :
      run (eTime (k53 z) 1)
        (packet (3*k53 z+4) 1 5 [false,true]) =
      packet (8*k53 z+9) 3 2 [false,true] := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k53 z) 1 2 [false,true])
  have he54 :=
    BB6.Agent37E2AlternatingAll.all_implicit_blank (k54 z) 3 0
  unfold externalCall42To54Time
  rw [run_add,ha43,he43,ha44,
    run_add,hb44,ha45,
    run_add,hb45,ha46,
    run_add,he46,ha47,
    run_add,he47,ha48,
    run_add,he48,ha49,
    run_add,hb49,ha50,
    run_add,hb50,ha51,
    run_add,he51,ha52,
    run_add,hb52,ha53,
    run_add,he53,ha54]
  simpa [BB6.Agent37E2AlternatingAll.input,
    BB6.Agent37E2AlternatingAll.output,
    BB6.Agent37E2AlternatingAll.time,
    BB6.Agent37E2AlternatingPacket.longTail,
    BB6.Agent37E2AlternatingPacket.zeroTail,
    CryptidBoundary.oppairs,call54Tail,hout] using he54

/-- Source-connected authentic terminal cylinder through the q=3 E-two
    reset at call 54.  The arithmetic cylinder has modulus exactly 3^36. -/
theorem external169_call54_prefix (z : Nat) :
    ∃ T,
      ObsEq
        (run T
          (packet
            (3*(150094635296999121*z+138047287621930441)+4) 0 2
            (false :: List.replicate 6 true)))
        (packet (call54OutputA z) 0 8 call54Tail) := by
  let y := 531441*z+488784
  obtain ⟨t0,h0⟩ := external169_call42_prefix y
  have hk :
      282429536481*y+249062601337 =
        150094635296999121*z+138047287621930441 := by
    dsimp [y]; omega
  have ha :
      call42OutputA y = call42InputA z := by
    simp [y,BB6.Agent37ExternalCall42.call42OutputA,call42InputA]
    omega
  rw [hk] at h0
  rw [ha] at h0
  refine ⟨t0+externalCall42To54Time z,?_⟩
  exact BB6.BoundaryPadding.source_chain
    t0 (externalCall42To54Time z)
    (packet
      (3*(150094635296999121*z+138047287621930441)+4) 0 2
      (false :: List.replicate 6 true))
    (packet (call42InputA z) 0 6 [false,true,false,true])
    (packet (call54OutputA z) 0 8 call54Tail)
    h0 (external_call42_to54 z)

#print axioms external_call42_to54
#print axioms external169_call54_prefix

end BB6.Agent37ExternalCall54
