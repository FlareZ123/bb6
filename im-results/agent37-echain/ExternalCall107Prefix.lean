import Lean.Elab.Tactic.Omega
import ExternalCall99Prefix

set_option maxHeartbeats 90000000
set_option maxRecDepth 28000

namespace BB6.Agent37ExternalCall107

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChainBExit BB6.Agent37EChain169Split
open BB6.Agent37ExternalCall99

def k100 (r : Nat) : Nat :=
  247302049962900897843114984583984818823341266077886634330364976782525404807168*r+
    115307201918528299689070127109588058945507703715049613412889418194121494880275
def k101 (r : Nat) : Nat :=
  659472133234402394248306625557292850195576709541031024880973271420067746152448*r+
    307485871782742132504187005625568157188020543240132302434371781850990653014069
def k102 (r : Nat) : Nat :=
  1758592355291739717995484334819447600521537892109416066349262057120180656406528*r+
    819962324753979020011165348334848419168054781973686139824991418269308408037520
def k103 (r : Nat) : Nat :=
  4689579614111305914654624892851860268057434378958442843598032152320481750417408*r+
    2186566199343944053363107595559595784448146085263163039533310448718155754766722
def k104 (r : Nat) : Nat :=
  12505545637630149105745666380938294048153158343889180916261419072854618001113088*r+
    5830843198250517475634953588158922091861722894035101438755494529915082012711261
def k105 (r : Nat) : Nat :=
  33348121700347064281988443682502117461741755583704482443363784194278981336301568*r+
    15548915195334713268359876235090458911631261050760270503347985413106885367230032
def k106 (r : Nat) : Nat :=
  88928324534258838085302516486672313231311348223211953182303424518077283563470848*r+
    41463773854225902048959669960241223764350029468694054675594627768285027645946754
def k107 (r : Nat) : Nat :=
  237142198758023568227473377297792835283496928595231875152809132048206089502588928*r+
    110570063611269072130559119893976596704933411916517479134919007382093407055858013

def call99InputA (r : Nat) : Nat :=
  741906149888702693529344953751954456470023798233659902991094930347576214421504*r+
    345921605755584899067210381328764176836523111145148840238668254582364484640829

def call107OutputA (r : Nat) : Nat :=
  1897137590064188545819787018382342682267975428761855001222473056385648716020711424*r+
    884560508890152577044472959151812773639467295332139833079352059056747256446864114

def externalCall99To107Time (r : Nat) : Nat :=
  eTime (k100 r) 0 +
  (bTime (k101 r) +
  (bTime (k102 r) +
  (eTime (k103 r) 0 +
  (bTime (k104 r) +
  (bTime (k105 r) +
  (eTime (k106 r) 0 +
    bTime (k107 r))))))))

theorem external_call99_to107 (r : Nat) :
    run (externalCall99To107Time r)
      (packet (call99InputA r) 0 11 call99Tail) =
    packet (call107OutputA r) 1 2 call99Tail := by
  have ha100 : call99InputA r = 3*k100 r+4 := by
    simp [call99InputA,k100]; omega
  have ha101 : 8*k100 r+9 = 3*k101 r+2 := by
    simp [k100,k101]; omega
  have ha102 : 8*k101 r+10 = 3*k102 r+2 := by
    simp [k101,k102]; omega
  have ha103 : 8*k102 r+10 = 3*k103 r+4 := by
    simp [k102,k103]; omega
  have ha104 : 8*k103 r+9 = 3*k104 r+2 := by
    simp [k103,k104]; omega
  have ha105 : 8*k104 r+10 = 3*k105 r+2 := by
    simp [k104,k105]; omega
  have ha106 : 8*k105 r+10 = 3*k106 r+4 := by
    simp [k105,k106]; omega
  have ha107 : 8*k106 r+9 = 3*k107 r+2 := by
    simp [k106,k107]; omega
  have hout : 8*k107 r+10 = call107OutputA r := by
    simp [k107,call107OutputA]; omega
  have he100 :
      run (eTime (k100 r) 0)
        (packet (3*k100 r+4) 0 11 call99Tail) =
      packet (8*k100 r+9) 2 8 call99Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k100 r) 0 8 call99Tail)
  have hb101 :=
    BB6.Agent31PacketSource.b_packet (k101 r) 1 8 call99Tail
  have hb102 :=
    BB6.Agent31PacketSource.b_packet (k102 r) 0 8 call99Tail
  have he103 :
      run (eTime (k103 r) 0)
        (packet (3*k103 r+4) 0 8 call99Tail) =
      packet (8*k103 r+9) 2 5 call99Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k103 r) 0 5 call99Tail)
  have hb104 :=
    BB6.Agent31PacketSource.b_packet (k104 r) 1 5 call99Tail
  have hb105 :=
    BB6.Agent31PacketSource.b_packet (k105 r) 0 5 call99Tail
  have he106 :
      run (eTime (k106 r) 0)
        (packet (3*k106 r+4) 0 5 call99Tail) =
      packet (8*k106 r+9) 2 2 call99Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k106 r) 0 2 call99Tail)
  have hb107 :=
    BB6.Agent31PacketSource.b_packet (k107 r) 1 2 call99Tail
  unfold externalCall99To107Time
  rw [run_add,ha100,he100,ha101,
    run_add,hb101,ha102,
    run_add,hb102,ha103,
    run_add,he103,ha104,
    run_add,hb104,ha105,
    run_add,hb105,ha106,
    run_add,he106,ha107,hb107,hout]

theorem external169_call107_prefix (r : Nat) :
    ∃ T,
      ObsEq
        (run T
          (packet
            (3*(2909321189362570808630465826492242446680483*r+
                1356501840069695579809464475403825451716734)+4)
            0 2 (false :: List.replicate 6 true)))
        (packet (call107OutputA r) 1 2 call99Tail) := by
  let v := 6561*r+3059
  obtain ⟨t0,h0⟩ := external169_call99_prefix v
  have hk :
      443426488243037769948249630619149892803*v+
          60212534243041537768855339845929632357 =
        2909321189362570808630465826492242446680483*r+
          1356501840069695579809464475403825451716734 := by
    dsimp [v]; omega
  have ha :
      call99OutputA v = call99InputA r := by
    simp [v,BB6.Agent37ExternalCall99.call99OutputA,call99InputA]
    omega
  rw [hk] at h0
  rw [ha] at h0
  have h1 : ObsEq
      (run (externalCall99To107Time r)
        (packet (call99InputA r) 0 11 call99Tail))
      (packet (call107OutputA r) 1 2 call99Tail) := by
    rw [external_call99_to107]
    exact BB6.Padding.cfgEq_refl _
  refine ⟨t0+externalCall99To107Time r,?_⟩
  exact BB6.BoundaryPadding.source_chain
    t0 (externalCall99To107Time r)
    (packet
      (3*(2909321189362570808630465826492242446680483*r+
          1356501840069695579809464475403825451716734)+4)
      0 2 (false :: List.replicate 6 true))
    (packet (call99InputA r) 0 11 call99Tail)
    (packet (call107OutputA r) 1 2 call99Tail)
    h0 h1

#print axioms external_call99_to107
#print axioms external169_call107_prefix

end BB6.Agent37ExternalCall107
