import Lean.Elab.Tactic.Omega
import BlankEighthRejoin
import EleventhPacketFive

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent25EleventhRoot
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed9 : DRegular.L := ⟨64*BB6.Agent2EighthRoot.t8+81,0,0⟩
def terminal6090 : DRegular.L :=
  (DRegular.run 6090 seed9).getD ⟨9,0,0⟩
def t9 : Nat := (terminal6090.a-4)/9

theorem terminal6090_exact :
    DRegular.run 6090 seed9 = some ⟨9*t9+4,9,1⟩ := by decide

def ninthExceptionTime : Nat :=
  BB6.Agent2EighthRoot.eighthReentryTime +
    DRegular.accumulated 6090 seed9

theorem ninth_exception_original :
    ObsEq (run ninthExceptionTime blank)
      (DRegularSource.sourceSection ⟨9*t9+4,9,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2EighthRoot.eighthReentryTime
    6090 seed9 ⟨9*t9+4,9,1⟩
  · constructor
    · change 64*BB6.Agent2EighthRoot.t8+81 ≥ 2
      omega
    · right
      change (0:Nat)=0
      rfl
  · exact terminal6090_exact
  · exact BB6.Agent2EighthRoot.eighthReentry_original

def ebCost (t p : Nat) : Nat :=
  BB6.Agent32EAll.duration (3*t) (p+1) +
    BB6.Agent25BGeneral.bCost t

def ninthReentryTime : Nat := ninthExceptionTime + ebCost t9 7

theorem ninth_reentry_original :
    ObsEq (run ninthReentryTime blank)
      (DRegularSource.sourceSection ⟨64*t9+35,1,5⟩) := by
  exact source_chain ninthExceptionTime (ebCost t9 7) blank
    (DRegularSource.sourceSection ⟨9*t9+4,9,1⟩)
    (DRegularSource.sourceSection ⟨64*t9+35,1,5⟩)
    ninth_exception_original
    (by simpa only [ebCost] using
      (BB6.Agent25BGeneral.exceptional_EB_general t9 7))

def seed10 : DRegular.L := ⟨64*t9+35,1,5⟩
def terminal41 : DRegular.L :=
  (DRegular.run 41 seed10).getD ⟨9,0,0⟩
def t10 : Nat := (terminal41.a-4)/9

theorem terminal41_exact :
    DRegular.run 41 seed10 = some ⟨9*t10+4,6,1⟩ := by decide

def tenthExceptionTime : Nat :=
  ninthReentryTime + DRegular.accumulated 41 seed10

theorem tenth_exception_original :
    ObsEq (run tenthExceptionTime blank)
      (DRegularSource.sourceSection ⟨9*t10+4,6,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    ninthReentryTime 41 seed10 ⟨9*t10+4,6,1⟩
  · constructor
    · change 64*t9+35 ≥ 2
      omega
    · left
      change (1:Nat) ≠ 0
      omega
  · exact terminal41_exact
  · exact ninth_reentry_original

def tenthReentryTime : Nat := tenthExceptionTime + ebCost t10 4

theorem tenth_reentry_original :
    ObsEq (run tenthReentryTime blank)
      (DRegularSource.sourceSection ⟨64*t10+29,1,5⟩) := by
  exact source_chain tenthExceptionTime (ebCost t10 4) blank
    (DRegularSource.sourceSection ⟨9*t10+4,6,1⟩)
    (DRegularSource.sourceSection ⟨64*t10+29,1,5⟩)
    tenth_exception_original
    (by simpa only [ebCost] using
      (BB6.Agent25BGeneral.exceptional_EB_general t10 4))

def seed11 : DRegular.L := ⟨64*t10+29,1,5⟩
def terminal1708 : DRegular.L :=
  (DRegular.run 1708 seed11).getD ⟨9,0,0⟩
def t11 : Nat := (terminal1708.a-7)/9

theorem terminal1708_exact :
    DRegular.run 1708 seed11 = some ⟨9*t11+7,6,1⟩ := by decide

theorem t11_mod27 : t11 % 27 = 4 := by decide

def eleventhExceptionTime : Nat :=
  tenthReentryTime + DRegular.accumulated 1708 seed11

theorem eleventh_exception_original :
    ObsEq (run eleventhExceptionTime blank)
      (DRegularSource.sourceSection ⟨9*t11+7,6,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    tenthReentryTime 1708 seed11 ⟨9*t11+7,6,1⟩
  · constructor
    · change 64*t10+29 ≥ 2
      omega
    · left
      change (1:Nat) ≠ 0
      omega
  · exact terminal1708_exact
  · exact tenth_reentry_original

private theorem entry_as_source (v : Nat) :
    BB6.Agent25EleventhPacket.entry v =
      DRegularSource.sourceSection ⟨9*(27*v+4)+7,6,1⟩ := by
  have hn : 9*(27*v+4)+7-2 = 3*(81*v+13)+2 := by omega
  simp [BB6.Agent25EleventhPacket.entry, DRegularSource.sourceSection,
    hn, oppairs, pairs, List.append_assoc]

private theorem exit_as_source (v : Nat) :
    BB6.Agent25EleventhPacket.regularExit v =
      DRegularSource.sourceSection ⟨32768*v+5493,0,0⟩ := by
  have hn : 32768*v+5493-2 = 32768*v+5491 := by omega
  have hr : List.replicate (32768*v+5493) true =
      true::true::List.replicate (32768*v+5491) true := by
    rw [show 32768*v+5493 = ((32768*v+5491)+1)+1 by omega]
    rw [List.replicate_succ, List.replicate_succ]
  simp only [BB6.Agent25EleventhPacket.regularExit,
    DRegularSource.sourceSection,init,hn]
  rw [hr]
  simp [oppairs, List.append_assoc]

/-- Authenticated original D blank-tape continuation through the ninth,
    tenth, and eleventh exceptional regular exits and the five-step
    E/E/E/E/A return to a pure-unary physical F/0 section. -/
theorem blank_eleventh_reentry :
    ∃ v : Nat, ObsEq
      (run (eleventhExceptionTime +
        BB6.Agent25EleventhPacket.fiveCost v) blank)
      (DRegularSource.sourceSection ⟨32768*v+5493,0,0⟩) := by
  let v := t11/27
  have hv : t11 = 27*v+4 := by
    dsimp [v]
    have h := t11_mod27
    omega
  have hin : ObsEq (run eleventhExceptionTime blank)
      (BB6.Agent25EleventhPacket.entry v) := by
    rw [entry_as_source]
    simpa only [hv] using eleventh_exception_original
  have hout : ObsEq
      (run (BB6.Agent25EleventhPacket.fiveCost v)
        (BB6.Agent25EleventhPacket.entry v))
      (DRegularSource.sourceSection ⟨32768*v+5493,0,0⟩) := by
    rw [←exit_as_source]
    exact BB6.Agent25EleventhPacket.five_return v
  refine ⟨v, ?_⟩
  exact source_chain eleventhExceptionTime
    (BB6.Agent25EleventhPacket.fiveCost v) blank
    (BB6.Agent25EleventhPacket.entry v)
    (DRegularSource.sourceSection ⟨32768*v+5493,0,0⟩)
    hin hout

#print axioms terminal6090_exact
#print axioms terminal41_exact
#print axioms terminal1708_exact
#print axioms t11_mod27
#print axioms ninth_reentry_original
#print axioms tenth_reentry_original
#print axioms eleventh_exception_original
#print axioms blank_eleventh_reentry
end BB6.Agent25EleventhRoot
