import Lean.Elab.Tactic.Omega
import ExternalCall85Prefix

set_option maxHeartbeats 70000000
set_option maxRecDepth 24000

namespace BB6.Agent37ExternalCall91

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChainBExit BB6.Agent37EChain169Split
open BB6.Agent37ExternalCall85

def k86 (z : Nat) : Nat :=
  6247775116078954191307148615022440198606325239827498543651749888*z+
    5704419439366587537779212570047612462846323282187534024611809627
def k87 (z : Nat) : Nat :=
  16660733642877211176819062973393173862950200639539996116404666368*z+
    15211785171644233434077900186793633234256862085833424065631492341
def k88 (z : Nat) : Nat :=
  44428623047672563138184167929048463634533868372106656310412443648*z+
    40564760457717955824207733831449688624684965562222464175017312912
def k89 (z : Nat) : Nat :=
  118476328127126835035157781144129236358756982325617750161099849728*z+
    108172694553914548864553956883865836332493241499259904466712834434
def k90 (z : Nat) : Nat :=
  315936875005671560093754083051011296956685286201647333762932932608*z+
    288460518810438796972143885023642230219981977331359745244567558493
def k91 (z : Nat) : Nat :=
  842498333348457493583344221469363458551160763204392890034487820288*z+
    769228050161170125259050360063045947253285272883625987318846822650

def call85InputA (z : Nat) : Nat :=
  18743325348236862573921445845067320595818975719482495630955249664*z+
    17113258318099762613337637710142837388538969846562602073835428885

def call91OutputA (z : Nat) : Nat :=
  6739986666787659948666753771754907668409286105635143120275902562304*z+
    6153824401289361002072402880504367578026282183069007898550774581205

def call91Tail : List Bool :=
  [false,true,false,true,true]

def externalCall85To91Time (z : Nat) : Nat :=
  eTime (k86 z) 0 +
  (bTime (k87 z) +
  (bTime (k88 z) +
  (eTime (k89 z) 0 +
  (bTime (k90 z) +
    (12*(k91 z)*(k91 z)+49*(k91 z)+54)))))

theorem external_call85_to91 (z : Nat) :
    run (externalCall85To91Time z)
      (packet (call85InputA z) 0 6 call85Tail) =
    packet (call91OutputA z) 0 9 call91Tail := by
  have ha86 : call85InputA z = 3*k86 z+4 := by
    simp [call85InputA,k86]; omega
  have ha87 : 8*k86 z+9 = 3*k87 z+2 := by
    simp [k86,k87]; omega
  have ha88 : 8*k87 z+10 = 3*k88 z+2 := by
    simp [k87,k88]; omega
  have ha89 : 8*k88 z+10 = 3*k89 z+4 := by
    simp [k88,k89]; omega
  have ha90 : 8*k89 z+9 = 3*k90 z+2 := by
    simp [k89,k90]; omega
  have ha91 : 8*k90 z+10 = 3*k91 z+4 := by
    simp [k90,k91]; omega
  have hout : 8*k91 z+5 = call91OutputA z := by
    simp [k91,call91OutputA]; omega
  have he86 :
      run (eTime (k86 z) 0)
        (packet (3*k86 z+4) 0 6 call85Tail) =
      packet (8*k86 z+9) 2 3 call85Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k86 z) 0 3 call85Tail)
  have hb87 :=
    BB6.Agent31PacketSource.b_packet (k87 z) 1 3 call85Tail
  have hb88 :=
    BB6.Agent31PacketSource.b_packet (k88 z) 0 3 call85Tail
  have he89 :
      run (eTime (k89 z) 0)
        (packet (3*k89 z+4) 0 3 call85Tail) =
      packet (8*k89 z+9) 2 0 call85Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k89 z) 0 0 call85Tail)
  have hb90 :=
    BB6.Agent31PacketSource.b_packet (k90 z) 1 0 call85Tail
  have htail : call85Tail = false :: true :: call91Tail := by decide
  have he91 :=
    BB6.Agent37PacketBoundary.e_zero_drop_any
      (k91 z) 1 call91Tail
  unfold externalCall85To91Time
  rw [run_add,ha86,he86,ha87,
    run_add,hb87,ha88,
    run_add,hb88,ha89,
    run_add,he89,ha90,
    run_add,hb90,ha91,htail]
  simpa [hout] using he91

theorem external169_call91_prefix (z : Nat) :
    ∃ T,
      ObsEq
        (run T
          (packet
            (3*(67585198634817523235520443624317923*z+
                61707458053942089242145020286680887)+4)
            0 2 (false :: List.replicate 6 true)))
        (packet (call91OutputA z) 0 9 call91Tail) := by
  let y := 729*z+665
  obtain ⟨t0,h0⟩ := external169_call85_prefix y
  have hk :
      92709463147897837085761925410587*y+
          55665060590027580113339888640532 =
        67585198634817523235520443624317923*z+
          61707458053942089242145020286680887 := by
    dsimp [y]; omega
  have ha :
      call85OutputA y = call85InputA z := by
    simp [y,BB6.Agent37ExternalCall85.call85OutputA,call85InputA]
    omega
  rw [hk] at h0
  rw [ha] at h0
  have h1 : ObsEq
      (run (externalCall85To91Time z)
        (packet (call85InputA z) 0 6 call85Tail))
      (packet (call91OutputA z) 0 9 call91Tail) := by
    rw [external_call85_to91]
    exact BB6.Padding.cfgEq_refl _
  refine ⟨t0+externalCall85To91Time z,?_⟩
  exact BB6.BoundaryPadding.source_chain
    t0 (externalCall85To91Time z)
    (packet
      (3*(67585198634817523235520443624317923*z+
          61707458053942089242145020286680887)+4)
      0 2 (false :: List.replicate 6 true))
    (packet (call85InputA z) 0 6 call85Tail)
    (packet (call91OutputA z) 0 9 call91Tail)
    h0 h1

#print axioms external_call85_to91
#print axioms external169_call91_prefix

end BB6.Agent37ExternalCall91
