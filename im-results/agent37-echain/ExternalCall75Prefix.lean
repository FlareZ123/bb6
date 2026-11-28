import Lean.Elab.Tactic.Omega
import ExternalCall67Prefix

set_option maxHeartbeats 70000000
set_option maxRecDepth 24000

namespace BB6.Agent37ExternalCall75

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChainBExit BB6.Agent37EChainBEEAReentry
open BB6.Agent37ExternalCall67

def k68 (x : Nat) : Nat :=
  3121390703947934259874471415186045863269066866688*x+
    1510246551217692334621455551947859928746873340571
def k69 (x : Nat) : Nat :=
  8323708543861158026331923773829455635384178311168*x+
    4027324136580512892323881471860959809991662241525
def k70 (x : Nat) : Nat :=
  22196556116963088070218463396878548361024475496448*x+
    10739531030881367712863683924962559493311099310736
def k71 (x : Nat) : Nat :=
  59190816311901568187249235725009462296065267990528*x+
    28638749415683647234303157133233491982162931495298
def k72 (x : Nat) : Nat :=
  157842176831737515165997961933358566122840714641408*x+
    76369998441823059291475085688622645285767817320797
def k73 (x : Nat) : Nat :=
  420912471551300040442661231822289509660908572377088*x+
    203653329178194824777266895169660387428714179522128
def k74 (x : Nat) : Nat :=
  1122433257470133441180429951526105359095756193005568*x+
    543075544475186199406045053785761033143237812059010
def k75 (x : Nat) : Nat :=
  2993155353253689176481146537402947624255349848014848*x+
    1448201451933829865082786810095362755048634165490695

def call67InputA (x : Nat) : Nat :=
  9364172111843802779623414245558137589807200600064*x+
    4530739653653077003864366655843579786240620021717

def call75OutputA (x : Nat) : Nat :=
  23945242826029513411849172299223580994042798784118784*x+
    11585611615470638920662294480762902040389073323925565

def call75Tail : List Bool :=
  [false,true,true,true,true,true]

def externalCall67To75Time (x : Nat) : Nat :=
  eTime (k68 x) 0 +
  (bTime (k69 x) +
  (bTime (k70 x) +
  (eTime (k71 x) 0 +
  (bTime (k72 x) +
  (bTime (k73 x) +
  (eTime (k74 x) 0 +
    (12*(k75 x)*(k75 x)+49*(k75 x)+58)))))))

theorem external_call67_to75 (x : Nat) :
    run (externalCall67To75Time x)
      (packet (call67InputA x) 0 9 call67Tail) =
    packet (call75OutputA x) 0 11 call75Tail := by
  have ha68 : call67InputA x = 3*k68 x+4 := by
    simp [call67InputA,k68]; omega
  have ha69 : 8*k68 x+9 = 3*k69 x+2 := by
    simp [k68,k69]; omega
  have ha70 : 8*k69 x+10 = 3*k70 x+2 := by
    simp [k69,k70]; omega
  have ha71 : 8*k70 x+10 = 3*k71 x+4 := by
    simp [k70,k71]; omega
  have ha72 : 8*k71 x+9 = 3*k72 x+2 := by
    simp [k71,k72]; omega
  have ha73 : 8*k72 x+10 = 3*k73 x+2 := by
    simp [k72,k73]; omega
  have ha74 : 8*k73 x+10 = 3*k74 x+4 := by
    simp [k73,k74]; omega
  have ha75 : 8*k74 x+9 = 3*k75 x+4 := by
    simp [k74,k75]; omega
  have hout : 8*k75 x+5 = call75OutputA x := by
    simp [k75,call75OutputA]; omega
  have he68 :
      run (eTime (k68 x) 0)
        (packet (3*k68 x+4) 0 9 call67Tail) =
      packet (8*k68 x+9) 2 6 call67Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k68 x) 0 6 call67Tail)
  have hb69 :=
    BB6.Agent31PacketSource.b_packet (k69 x) 1 6 call67Tail
  have hb70 :=
    BB6.Agent31PacketSource.b_packet (k70 x) 0 6 call67Tail
  have he71 :
      run (eTime (k71 x) 0)
        (packet (3*k71 x+4) 0 6 call67Tail) =
      packet (8*k71 x+9) 2 3 call67Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k71 x) 0 3 call67Tail)
  have hb72 :=
    BB6.Agent31PacketSource.b_packet (k72 x) 1 3 call67Tail
  have hb73 :=
    BB6.Agent31PacketSource.b_packet (k73 x) 0 3 call67Tail
  have he74 :
      run (eTime (k74 x) 0)
        (packet (3*k74 x+4) 0 3 call67Tail) =
      packet (8*k74 x+9) 2 0 call67Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k74 x) 0 0 call67Tail)
  have htail : call67Tail = false :: true :: call75Tail := by decide
  have he75 :=
    BB6.Agent37PacketBoundary.e_zero_drop_any
      (k75 x) 2 call75Tail
  unfold externalCall67To75Time
  rw [run_add,ha68,he68,ha69,
    run_add,hb69,ha70,
    run_add,hb70,ha71,
    run_add,he71,ha72,
    run_add,hb72,ha73,
    run_add,hb73,ha74,
    run_add,he74,ha75,htail]
  simpa [hout] using he75

theorem external169_call75_prefix (x : Nat) :
    ∃ T,
      ObsEq
        (run T
          (packet
            (3*(1570042899082081611640534563*x+
                759645971458654236376243930)+4)
            0 2 (false :: List.replicate 6 true)))
        (packet (call75OutputA x) 0 11 call75Tail) := by
  let w := 6561*x+3174
  obtain ⟨t0,h0⟩ := external169_call67_prefix w
  have hk :
      239299329230617529590083*w+
          109900480674197457320488 =
        1570042899082081611640534563*x+
          759645971458654236376243930 := by
    dsimp [w]; omega
  have ha :
      call67OutputA w = call67InputA x := by
    simp [w,BB6.Agent37ExternalCall67.call67OutputA,call67InputA]
    omega
  rw [hk] at h0
  rw [ha] at h0
  have h1 : ObsEq
      (run (externalCall67To75Time x)
        (packet (call67InputA x) 0 9 call67Tail))
      (packet (call75OutputA x) 0 11 call75Tail) := by
    rw [external_call67_to75]
    exact BB6.Padding.cfgEq_refl _
  refine ⟨t0+externalCall67To75Time x,?_⟩
  exact BB6.BoundaryPadding.source_chain
    t0 (externalCall67To75Time x)
    (packet
      (3*(1570042899082081611640534563*x+
          759645971458654236376243930)+4)
      0 2 (false :: List.replicate 6 true))
    (packet (call67InputA x) 0 9 call67Tail)
    (packet (call75OutputA x) 0 11 call75Tail)
    h0 h1

#print axioms external_call67_to75
#print axioms external169_call75_prefix

end BB6.Agent37ExternalCall75
