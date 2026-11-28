import Lean.Elab.Tactic.Omega
import ExternalCall91Prefix

set_option maxHeartbeats 80000000
set_option maxRecDepth 26000

namespace BB6.Agent37ExternalCall99

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChainBExit BB6.Agent37EChainBEEAReentry
open BB6.Agent37ExternalCall91

def k92 (v : Nat) : Nat :=
  14740350840264612307734190498827983070811108713024058004043398903758848*v+
    2001580652614102238438494419914124064154096972066115461648034685010587
def k93 (v : Nat) : Nat :=
  39307602240705632820624507996874621522162956568064154677449063743356928*v+
    5337548406970939302502651786437664171077591925509641231061425826694901
def k94 (v : Nat) : Nat :=
  104820272641881687521665354658332324059101217514837745806530836648951808*v+
    14233462418589171473340404763833771122873578468025709949497135537853072
def k95 (v : Nat) : Nat :=
  279520727045017833391107612422219530824269913372900655484082231063871488*v+
    37955899782904457262241079370223389660996209248068559865325694767608194
def k96 (v : Nat) : Nat :=
  745388605453380889042953633125918748864719768994401747957552616170323968*v+
    101215732754411886032642878320595705762656557994849492974201852713621853
def k97 (v : Nat) : Nat :=
  1987702947875682370781209688335783330305919383985071327886806976454197248*v+
    269908620678431696087047675521588548700417487986265314597871607236324944
def k98 (v : Nat) : Nat :=
  5300541194335152988749892502228755547482451690626856874364818603877859328*v+
    719756321809151189565460468057569463201113301296707505594324285963533186
def k99 (v : Nat) : Nat :=
  14134776518227074636666380005943348126619871175004951664972849610340958208*v+
    1919350191491069838841227914820185235202968803457886681584864762569421831

def call91InputA (v : Nat) : Nat :=
  44221052520793836923202571496483949212433326139072174012130196711276544*v+
    6004741957842306715315483259742372192462290916198346384944104055031765

def call99OutputA (v : Nat) : Nat :=
  113078212145816597093331040047546785012958969400039613319782796882727665664*v+
    15354801531928558710729823318561481881623750427663093452678918100555374653

def call99Tail : List Bool :=
  [false,true,true]

def externalCall91To99Time (v : Nat) : Nat :=
  eTime (k92 v) 0 +
  (bTime (k93 v) +
  (bTime (k94 v) +
  (eTime (k95 v) 0 +
  (bTime (k96 v) +
  (bTime (k97 v) +
  (eTime (k98 v) 0 +
    (12*(k99 v)*(k99 v)+49*(k99 v)+58)))))))

theorem external_call91_to99 (v : Nat) :
    run (externalCall91To99Time v)
      (packet (call91InputA v) 0 9 call91Tail) =
    packet (call99OutputA v) 0 11 call99Tail := by
  have ha92 : call91InputA v = 3*k92 v+4 := by
    simp [call91InputA,k92]; omega
  have ha93 : 8*k92 v+9 = 3*k93 v+2 := by
    simp [k92,k93]; omega
  have ha94 : 8*k93 v+10 = 3*k94 v+2 := by
    simp [k93,k94]; omega
  have ha95 : 8*k94 v+10 = 3*k95 v+4 := by
    simp [k94,k95]; omega
  have ha96 : 8*k95 v+9 = 3*k96 v+2 := by
    simp [k95,k96]; omega
  have ha97 : 8*k96 v+10 = 3*k97 v+2 := by
    simp [k96,k97]; omega
  have ha98 : 8*k97 v+10 = 3*k98 v+4 := by
    simp [k97,k98]; omega
  have ha99 : 8*k98 v+9 = 3*k99 v+4 := by
    simp [k98,k99]; omega
  have hout : 8*k99 v+5 = call99OutputA v := by
    simp [k99,call99OutputA]; omega
  have he92 :
      run (eTime (k92 v) 0)
        (packet (3*k92 v+4) 0 9 call91Tail) =
      packet (8*k92 v+9) 2 6 call91Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k92 v) 0 6 call91Tail)
  have hb93 :=
    BB6.Agent31PacketSource.b_packet (k93 v) 1 6 call91Tail
  have hb94 :=
    BB6.Agent31PacketSource.b_packet (k94 v) 0 6 call91Tail
  have he95 :
      run (eTime (k95 v) 0)
        (packet (3*k95 v+4) 0 6 call91Tail) =
      packet (8*k95 v+9) 2 3 call91Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k95 v) 0 3 call91Tail)
  have hb96 :=
    BB6.Agent31PacketSource.b_packet (k96 v) 1 3 call91Tail
  have hb97 :=
    BB6.Agent31PacketSource.b_packet (k97 v) 0 3 call91Tail
  have he98 :
      run (eTime (k98 v) 0)
        (packet (3*k98 v+4) 0 3 call91Tail) =
      packet (8*k98 v+9) 2 0 call91Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k98 v) 0 0 call91Tail)
  have htail : call91Tail = false :: true :: call99Tail := by decide
  have he99 :=
    BB6.Agent37PacketBoundary.e_zero_drop_any
      (k99 v) 2 call99Tail
  unfold externalCall91To99Time
  rw [run_add,ha92,he92,ha93,
    run_add,hb93,ha94,
    run_add,hb94,ha95,
    run_add,he95,ha96,
    run_add,hb96,ha97,
    run_add,hb97,ha98,
    run_add,he98,ha99,htail]
  simpa [hout] using he99

theorem external169_call99_prefix (v : Nat) :
    ∃ T,
      ObsEq
        (run T
          (packet
            (3*(443426488243037769948249630619149892803*v+
                60212534243041537768855339845929632357)+4)
            0 2 (false :: List.replicate 6 true)))
        (packet (call99OutputA v) 0 11 call99Tail) := by
  let z := 6561*v+890
  obtain ⟨t0,h0⟩ := external169_call91_prefix z
  have hk :
      67585198634817523235520443624317923*z+
          61707458053942089242145020286680887 =
        443426488243037769948249630619149892803*v+
          60212534243041537768855339845929632357 := by
    dsimp [z]; omega
  have ha :
      call91OutputA z = call91InputA v := by
    simp [z,BB6.Agent37ExternalCall91.call91OutputA,call91InputA]
    omega
  rw [hk] at h0
  rw [ha] at h0
  have h1 : ObsEq
      (run (externalCall91To99Time v)
        (packet (call91InputA v) 0 9 call91Tail))
      (packet (call99OutputA v) 0 11 call99Tail) := by
    rw [external_call91_to99]
    exact BB6.Padding.cfgEq_refl _
  refine ⟨t0+externalCall91To99Time v,?_⟩
  exact BB6.BoundaryPadding.source_chain
    t0 (externalCall91To99Time v)
    (packet
      (3*(443426488243037769948249630619149892803*v+
          60212534243041537768855339845929632357)+4)
      0 2 (false :: List.replicate 6 true))
    (packet (call91InputA v) 0 9 call91Tail)
    (packet (call99OutputA v) 0 11 call99Tail)
    h0 h1

#print axioms external_call91_to99
#print axioms external169_call99_prefix

end BB6.Agent37ExternalCall99
