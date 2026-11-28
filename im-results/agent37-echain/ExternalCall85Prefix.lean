import Lean.Elab.Tactic.Omega
import ExternalCall75Prefix
import E2UnaryPhysical

set_option maxHeartbeats 80000000
set_option maxRecDepth 26000

namespace BB6.Agent37ExternalCall85

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChainBExit BB6.Agent37EChainBEEAReentry
open BB6.Agent37ExternalCall75

def k76 (y : Nat) : Nat :=
  471314214544738912485427258365617744705744408467810025472*y+
    282988741588555279714207072330384534488277925721823764499
def k77 (y : Nat) : Nat :=
  1256837905452637099961139355641647319215318422580826734592*y+
    754636644236147412571218859547692091968741135258196705333
def k78 (y : Nat) : Nat :=
  3351567747873698933229704948377726184574182460215537958912*y+
    2012364384629726433523250292127178911916643027355191214224
def k79 (y : Nat) : Nat :=
  8937513994329863821945879862340603158864486560574767890432*y+
    5366305025679270489395334112339143765111048072947176571266
def k80 (y : Nat) : Nat :=
  23833370651546303525189012966241608423638630828199381041152*y+
    14310146735144721305054224299571050040296128194525804190045
def k81 (y : Nat) : Nat :=
  63555655070790142733837367909977622463036348875198349443072*y+
    38160391293719256813477931465522800107456341852068811173456
def k82 (y : Nat) : Nat :=
  169481746855440380623566314426606993234763597000528931848192*y+
    101761043449918018169274483908060800286550244938850163129218
def k83 (y : Nat) : Nat :=
  451951324947841014996176838470951981959369592001410484928512*y+
    271362782533114715118065290421495467430800653170267101677917
def k84 (y : Nat) : Nat :=
  1205203533194242706656471569255871951891652245337094626476032*y+
    723634086754972573648174107790654579815468408454045604474448
def k85 (y : Nat) : Nat :=
  3213876088517980551083924184682325205044405987565585670602752*y+
    1929690898013260196395130954108412212841249089210788278598530

def call75InputA (y : Nat) : Nat :=
  1413942643634216737456281775096853234117233225403430076416*y+
    848966224765665839142621216991153603464833777165471293501

def call85OutputA (y : Nat) : Nat :=
  25711008708143844408671393477458601640355247900524685364822016*y+
    15437527184106081571161047632867297702729992713686306228788245

def call85Tail : List Bool :=
  [false,true,false,true,false,true,true]

def externalCall75To85Time (y : Nat) : Nat :=
  eTime (k76 y) 0 +
  (bTime (k77 y) +
  (bTime (k78 y) +
  (eTime (k79 y) 0 +
  (bTime (k80 y) +
  (bTime (k81 y) +
  (eTime (k82 y) 0 +
  (bTime (k83 y) +
  (bTime (k84 y) +
    (12*(k85 y)*(k85 y)+49*(k85 y)+68)))))))))

theorem external_call75_to85 (y : Nat) :
    run (externalCall75To85Time y)
      (packet (call75InputA y) 0 11 call75Tail) =
    packet (call85OutputA y) 0 6 call85Tail := by
  have ha76 : call75InputA y = 3*k76 y+4 := by
    simp [call75InputA,k76]; omega
  have ha77 : 8*k76 y+9 = 3*k77 y+2 := by
    simp [k76,k77]; omega
  have ha78 : 8*k77 y+10 = 3*k78 y+2 := by
    simp [k77,k78]; omega
  have ha79 : 8*k78 y+10 = 3*k79 y+4 := by
    simp [k78,k79]; omega
  have ha80 : 8*k79 y+9 = 3*k80 y+2 := by
    simp [k79,k80]; omega
  have ha81 : 8*k80 y+10 = 3*k81 y+2 := by
    simp [k80,k81]; omega
  have ha82 : 8*k81 y+10 = 3*k82 y+4 := by
    simp [k81,k82]; omega
  have ha83 : 8*k82 y+9 = 3*k83 y+2 := by
    simp [k82,k83]; omega
  have ha84 : 8*k83 y+10 = 3*k84 y+2 := by
    simp [k83,k84]; omega
  have ha85 : 8*k84 y+10 = 3*k85 y+4 := by
    simp [k84,k85]; omega
  have hout : 8*k85 y+5 = call85OutputA y := by
    simp [k85,call85OutputA]; omega
  have he76 :
      run (eTime (k76 y) 0)
        (packet (3*k76 y+4) 0 11 call75Tail) =
      packet (8*k76 y+9) 2 8 call75Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k76 y) 0 8 call75Tail)
  have hb77 :=
    BB6.Agent31PacketSource.b_packet (k77 y) 1 8 call75Tail
  have hb78 :=
    BB6.Agent31PacketSource.b_packet (k78 y) 0 8 call75Tail
  have he79 :
      run (eTime (k79 y) 0)
        (packet (3*k79 y+4) 0 8 call75Tail) =
      packet (8*k79 y+9) 2 5 call75Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k79 y) 0 5 call75Tail)
  have hb80 :=
    BB6.Agent31PacketSource.b_packet (k80 y) 1 5 call75Tail
  have hb81 :=
    BB6.Agent31PacketSource.b_packet (k81 y) 0 5 call75Tail
  have he82 :
      run (eTime (k82 y) 0)
        (packet (3*k82 y+4) 0 5 call75Tail) =
      packet (8*k82 y+9) 2 2 call75Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k82 y) 0 2 call75Tail)
  have hb83 :=
    BB6.Agent31PacketSource.b_packet (k83 y) 1 2 call75Tail
  have hb84 :=
    BB6.Agent31PacketSource.b_packet (k84 y) 0 2 call75Tail
  have he85 :=
    BB6.Agent37E2UnaryPhysical.e_two_unary_long (k85 y) 0 1 []
  unfold externalCall75To85Time
  rw [run_add,ha76,he76,ha77,
    run_add,hb77,ha78,
    run_add,hb78,ha79,
    run_add,he79,ha80,
    run_add,hb80,ha81,
    run_add,hb81,ha82,
    run_add,he82,ha83,
    run_add,hb83,ha84,
    run_add,hb84,ha85]
  simpa [call75Tail,call85Tail,hout,List.replicate] using he85

theorem external169_call85_prefix (y : Nat) :
    ∃ T,
      ObsEq
        (run T
          (packet
            (3*(92709463147897837085761925410587*y+
                55665060590027580113339888640532)+4)
            0 2 (false :: List.replicate 6 true)))
        (packet (call85OutputA y) 0 6 call85Tail) := by
  let x := 59049*y+35454
  obtain ⟨t0,h0⟩ := external169_call75_prefix x
  have hk :
      1570042899082081611640534563*x+
          759645971458654236376243930 =
        92709463147897837085761925410587*y+
          55665060590027580113339888640532 := by
    dsimp [x]; omega
  have ha :
      call75OutputA x = call75InputA y := by
    simp [x,BB6.Agent37ExternalCall75.call75OutputA,call75InputA]
    omega
  rw [hk] at h0
  rw [ha] at h0
  have h1 : ObsEq
      (run (externalCall75To85Time y)
        (packet (call75InputA y) 0 11 call75Tail))
      (packet (call85OutputA y) 0 6 call85Tail) := by
    rw [external_call75_to85]
    exact BB6.Padding.cfgEq_refl _
  refine ⟨t0+externalCall75To85Time y,?_⟩
  exact BB6.BoundaryPadding.source_chain
    t0 (externalCall75To85Time y)
    (packet
      (3*(92709463147897837085761925410587*y+
          55665060590027580113339888640532)+4)
      0 2 (false :: List.replicate 6 true))
    (packet (call75InputA y) 0 11 call75Tail)
    (packet (call85OutputA y) 0 6 call85Tail)
    h0 h1

#print axioms external_call75_to85
#print axioms external169_call85_prefix

end BB6.Agent37ExternalCall85
