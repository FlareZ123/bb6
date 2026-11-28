import Lean.Elab.Tactic.Omega
import ExternalCall61Prefix

set_option maxHeartbeats 60000000
set_option maxRecDepth 22000

namespace BB6.Agent37ExternalCall67

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChainBExit BB6.Agent37EChainBEEAReentry
open BB6.Agent37ExternalCall61

def k62 (w : Nat) : Nat :=
  1323017842588608745945600473694714806140928*w+
    607608459699870897843087314775010211613019
def k63 (w : Nat) : Nat :=
  3528047580236289989188267929852572816375808*w+
    1620289225866322394248232839400027230968053
def k64 (w : Nat) : Nat :=
  9408126880630106637835381146273527510335488*w+
    4320771268976859717995287571733405949248144
def k65 (w : Nat) : Nat :=
  25088338348346951034227683056729406694227968*w+
    11522056717271625914654100191289082531328386
def k66 (w : Nat) : Nat :=
  66902235595591869424607154817945084517941248*w+
    30725484579391002439077600510104220083542365
def k67 (w : Nat) : Nat :=
  178405961588244985132285746181186892047843328*w+
    81934625545042673170873601360277920222779642

def call61InputA (w : Nat) : Nat :=
  3969053527765826237836801421084144418422784*w+
    1822825379099612693529261944325030634839061

def call67OutputA (w : Nat) : Nat :=
  1427247692705959881058285969449495136382746624*w+
    655477004360341385366988810882223361782237141

def call67Tail : List Bool :=
  [false,true,false,true,true,true,true,true]

def externalCall61To67Time (w : Nat) : Nat :=
  eTime (k62 w) 0 +
  (bTime (k63 w) +
  (bTime (k64 w) +
  (eTime (k65 w) 0 +
  (bTime (k66 w) +
    (12*(k67 w)*(k67 w)+49*(k67 w)+54)))))

theorem external_call61_to67 (w : Nat) :
    run (externalCall61To67Time w)
      (packet (call61InputA w) 0 6 call61Tail) =
    packet (call67OutputA w) 0 9 call67Tail := by
  have ha62 : call61InputA w = 3*k62 w+4 := by
    simp [call61InputA,k62]; omega
  have ha63 : 8*k62 w+9 = 3*k63 w+2 := by
    simp [k62,k63]; omega
  have ha64 : 8*k63 w+10 = 3*k64 w+2 := by
    simp [k63,k64]; omega
  have ha65 : 8*k64 w+10 = 3*k65 w+4 := by
    simp [k64,k65]; omega
  have ha66 : 8*k65 w+9 = 3*k66 w+2 := by
    simp [k65,k66]; omega
  have ha67 : 8*k66 w+10 = 3*k67 w+4 := by
    simp [k66,k67]; omega
  have hout : 8*k67 w+5 = call67OutputA w := by
    simp [k67,call67OutputA]; omega
  have he62 :
      run (eTime (k62 w) 0)
        (packet (3*k62 w+4) 0 6 call61Tail) =
      packet (8*k62 w+9) 2 3 call61Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k62 w) 0 3 call61Tail)
  have hb63 :=
    BB6.Agent31PacketSource.b_packet (k63 w) 1 3 call61Tail
  have hb64 :=
    BB6.Agent31PacketSource.b_packet (k64 w) 0 3 call61Tail
  have he65 :
      run (eTime (k65 w) 0)
        (packet (3*k65 w+4) 0 3 call61Tail) =
      packet (8*k65 w+9) 2 0 call61Tail := by
    simpa using
      (BB6.Agent31PacketSource.e_packet (k65 w) 0 0 call61Tail)
  have hb66 :=
    BB6.Agent31PacketSource.b_packet (k66 w) 1 0 call61Tail
  have htail : call61Tail = false :: true :: call67Tail := by decide
  have he67 :=
    BB6.Agent37PacketBoundary.e_zero_drop_any
      (k67 w) 1 call67Tail
  unfold externalCall61To67Time
  rw [run_add,ha62,he62,ha63,
    run_add,hb63,ha64,
    run_add,hb64,ha65,
    run_add,he65,ha66,
    run_add,hb66,ha67,htail]
  simpa [hout] using he67

theorem external169_call67_prefix (w : Nat) :
    ∃ T,
      ObsEq
        (run T
          (packet
            (3*(239299329230617529590083*w+
                109900480674197457320488)+4)
            0 2 (false :: List.replicate 6 true)))
        (packet (call67OutputA w) 0 9 call67Tail) := by
  let u := 729*w+334
  obtain ⟨t0,h0⟩ := external169_call61_prefix u
  have hk :
      328256967394537077627*u+262653564422073393070 =
        239299329230617529590083*w+
          109900480674197457320488 := by
    dsimp [u]; omega
  have ha :
      call61OutputA u = call61InputA w := by
    simp [u,BB6.Agent37ExternalCall61.call61OutputA,call61InputA]
    omega
  rw [hk] at h0
  rw [ha] at h0
  have h1 : ObsEq
      (run (externalCall61To67Time w)
        (packet (call61InputA w) 0 6 call61Tail))
      (packet (call67OutputA w) 0 9 call67Tail) := by
    rw [external_call61_to67]
    exact BB6.Padding.cfgEq_refl _
  refine ⟨t0+externalCall61To67Time w,?_⟩
  exact BB6.BoundaryPadding.source_chain
    t0 (externalCall61To67Time w)
    (packet
      (3*(239299329230617529590083*w+
          109900480674197457320488)+4)
      0 2 (false :: List.replicate 6 true))
    (packet (call61InputA w) 0 6 call61Tail)
    (packet (call67OutputA w) 0 9 call67Tail)
    h0 h1

#print axioms external_call61_to67
#print axioms external169_call67_prefix

end BB6.Agent37ExternalCall67
