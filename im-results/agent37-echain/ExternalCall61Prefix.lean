import Lean.Elab.Tactic.Omega
import ExternalCall54Prefix
import E2UnaryPhysical

set_option maxHeartbeats 70000000
set_option maxRecDepth 24000

namespace BB6.Agent37ExternalCall61

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChainBExit BB6.Agent37EChain169Split
open BB6.Agent37ExternalCall54

def k55 (u : Nat) : Nat :=
  1892592204935944670599365912000724992*u+
    1514350457111210892362729440137432595
def k56 (u : Nat) : Nat :=
  5046912546495852454931642432001933312*u+
    4038267885629895712967278507033153589
def k57 (u : Nat) : Nat :=
  13458433457322273213151046485338488832*u+
    10768714361679721901246076018755076240
def k58 (u : Nat) : Nat :=
  35889155886192728568402790627569303552*u+
    28716571631145925069989536050013536642
def k59 (u : Nat) : Nat :=
  95704415696513942849074108340184809472*u+
    76577524349722466853305429466702764381
def k60 (u : Nat) : Nat :=
  255211775190703847597530955573826158592*u+
    204206731599259911608814478577874038352
def k61 (u : Nat) : Nat :=
  680564733841876926926749214863536422912*u+
    544551284264693097623505276207664102274

def call54InputA (u : Nat) : Nat :=
  5677776614807834011798097736002174976*u+
    4543051371333632677088188320412297789

def call61OutputA (u : Nat) : Nat :=
  5444517870735015415413993718908291383296*u+
    4356410274117544780988042209661312818197

def call61Tail : List Bool :=
  [false,true,false,true,false,true,true,true,true,true]

def externalCall54To61Time (u : Nat) : Nat :=
  eTime (k55 u) 0 +
  (bTime (k56 u) +
  (bTime (k57 u) +
  (eTime (k58 u) 0 +
  (bTime (k59 u) +
  (bTime (k60 u) +
    (12*(k61 u)*(k61 u)+49*(k61 u)+68))))))

theorem external_call54_to61 (u : Nat) :
    run (externalCall54To61Time u)
      (packet (call54InputA u) 0 8 call54Tail) =
    packet (call61OutputA u) 0 6 call61Tail := by
  have ha55 : call54InputA u = 3*k55 u+4 := by
    simp [call54InputA,k55]; omega
  have ha56 : 8*k55 u+9 = 3*k56 u+2 := by
    simp [k55,k56]; omega
  have ha57 : 8*k56 u+10 = 3*k57 u+2 := by
    simp [k56,k57]; omega
  have ha58 : 8*k57 u+10 = 3*k58 u+4 := by
    simp [k57,k58]; omega
  have ha59 : 8*k58 u+9 = 3*k59 u+2 := by
    simp [k58,k59]; omega
  have ha60 : 8*k59 u+10 = 3*k60 u+2 := by
    simp [k59,k60]; omega
  have ha61 : 8*k60 u+10 = 3*k61 u+4 := by
    simp [k60,k61]; omega
  have hout : 8*k61 u+5 = call61OutputA u := by
    simp [k61,call61OutputA]; omega
  have he55 :
      run (eTime (k55 u) 0)
        (packet (3*k55 u+4) 0 8 call54Tail) =
      packet (8*k55 u+9) 2 5 call54Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k55 u) 0 5 call54Tail)
  have hb56 :=
    BB6.Agent31PacketSource.b_packet (k56 u) 1 5 call54Tail
  have hb57 :=
    BB6.Agent31PacketSource.b_packet (k57 u) 0 5 call54Tail
  have he58 :
      run (eTime (k58 u) 0)
        (packet (3*k58 u+4) 0 5 call54Tail) =
      packet (8*k58 u+9) 2 2 call54Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k58 u) 0 2 call54Tail)
  have hb59 :=
    BB6.Agent31PacketSource.b_packet (k59 u) 1 2 call54Tail
  have hb60 :=
    BB6.Agent31PacketSource.b_packet (k60 u) 0 2 call54Tail
  have he61 :=
    BB6.Agent37E2UnaryPhysical.e_two_unary_long
      (k61 u) 0 4 []
  unfold externalCall54To61Time
  rw [run_add,ha55,he55,ha56,
    run_add,hb56,ha57,
    run_add,hb57,ha58,
    run_add,he58,ha59,
    run_add,hb59,ha60,
    run_add,hb60,ha61]
  simpa [call54Tail,call61Tail,hout,List.replicate] using he61

/-- Source-connected authentic terminal cylinder through the call-61 E-two
    reset.  The arithmetic cylinder has modulus exactly 3^43. -/
theorem external169_call61_prefix (u : Nat) :
    ∃ T,
      ObsEq
        (run T
          (packet
            (3*(328256967394537077627*u+262653564422073393070)+4)
            0 2 (false :: List.replicate 6 true)))
        (packet (call61OutputA u) 0 6 call61Tail) := by
  let z := 2187*u+1749
  obtain ⟨t0,h0⟩ := external169_call54_prefix z
  have hk :
      150094635296999121*z+138047287621930441 =
        328256967394537077627*u+262653564422073393070 := by
    dsimp [z]; omega
  have ha :
      call54OutputA z = call54InputA u := by
    simp [z,BB6.Agent37ExternalCall54.call54OutputA,call54InputA]
    omega
  rw [hk] at h0
  rw [ha] at h0
  have h1 : ObsEq
      (run (externalCall54To61Time u)
        (packet (call54InputA u) 0 8 call54Tail))
      (packet (call61OutputA u) 0 6 call61Tail) := by
    rw [external_call54_to61]
    exact BB6.Padding.cfgEq_refl _
  refine ⟨t0+externalCall54To61Time u,?_⟩
  exact BB6.BoundaryPadding.source_chain
    t0 (externalCall54To61Time u)
    (packet
      (3*(328256967394537077627*u+262653564422073393070)+4)
      0 2 (false :: List.replicate 6 true))
    (packet (call54InputA u) 0 8 call54Tail)
    (packet (call61OutputA u) 0 6 call61Tail)
    h0 h1

#print axioms external_call54_to61
#print axioms external169_call61_prefix

end BB6.Agent37ExternalCall61
