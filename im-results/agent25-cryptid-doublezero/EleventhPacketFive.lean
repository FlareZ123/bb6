import Lean.Elab.Tactic.Omega
import EAllDouble
import PacketPaths
import ShortTripleGate
import BoundaryPadding

set_option maxHeartbeats 100000000
set_option maxRecDepth 10000

namespace BB6.Agent25EleventhPacket
open CryptidBoundary BB6.BoundaryPadding

private def tail : List Bool := false :: List.replicate 6 true
private def words : List Bool := [false,false,false,false,false,false,true]
private def ys : List Bool := List.replicate 6 true

/-- A five-return E/E/E/E/A packet family with six alternating pairs. -/
def entry (v : Nat) : Cfg :=
  init (List.replicate (3*(81*v+13)+2) true ++
    false :: (pairs 5 ++ [true,true]))

def eCost (v : Nat) : Nat := BB6.Agent32EAll.duration (81*v+13) 5
private def c1 (v : Nat) : Nat :=
  12*(216*v+35)*(216*v+35)+49*(216*v+35)+58
private def c2 (v : Nat) : Nat :=
  12*(576*v+95)*(576*v+95)+49*(576*v+95)+70
private def c3 (v : Nat) : Nat :=
  12*(1536*v+255)*(1536*v+255)+49*(1536*v+255)+82
private def c4 (v : Nat) : Nat :=
  (12*(4096*v+682)*(4096*v+682)+41*(4096*v+682)+32) +
    (CryptidA.wordCost (4*(4096*v+682)+3) words +
      (2*((4*(4096*v+682)+3)+CryptidA.wordInc words)+6))

def fiveCost (v : Nat) : Nat := eCost v + (c1 v + (c2 v + (c3 v + c4 v)))

def regularExit (v : Nat) : Cfg :=
  ⟨[],false,List.replicate (32768*v+5493) true,5⟩

private theorem first (v : Nat) :
    ObsEq (run (eCost v) (entry v))
      (BB6.Agent31PacketSource.packet (648*v+109) 0 12 tail) := by
  have h := BB6.Agent32EAll.all_e_double_implicit_blank (81*v+13) 5
  have ho : BB6.Agent32EAll.output (81*v+13) 5 [] =
      BB6.Agent31PacketSource.packet (648*v+109) 0 12 tail := by
    have hn : 8*(81*v+13)+5=648*v+109 := by omega
    simp [BB6.Agent32EAll.output, BB6.Agent31PacketSource.packet,
      BB6.Agent31PacketSource.word, tail, hn, oppairs]
  rw [ho] at h
  simpa only [eCost, entry] using h

private theorem p1 (v : Nat) :
    run (c1 v) (BB6.Agent31PacketSource.packet (648*v+109) 0 12 tail) =
      BB6.Agent31PacketSource.packet (1728*v+289) 2 9 tail := by
  have h := BB6.Agent31PacketSource.e_packet (216*v+35) 0 9 tail
  have h1 : 3*(216*v+35)+4=648*v+109 := by omega
  have h2 : 8*(216*v+35)+9=1728*v+289 := by omega
  simpa only [c1, h1, h2] using h

private theorem p2 (v : Nat) :
    run (c2 v) (BB6.Agent31PacketSource.packet (1728*v+289) 2 9 tail) =
      BB6.Agent31PacketSource.packet (4608*v+769) 4 6 tail := by
  have h := BB6.Agent31PacketSource.e_packet (576*v+95) 2 6 tail
  have h1 : 3*(576*v+95)+4=1728*v+289 := by omega
  have h2 : 8*(576*v+95)+9=4608*v+769 := by omega
  simpa only [c2, h1, h2] using h

private theorem p3 (v : Nat) :
    run (c3 v) (BB6.Agent31PacketSource.packet (4608*v+769) 4 6 tail) =
      BB6.Agent31PacketSource.packet (12288*v+2049) 6 3 tail := by
  have h := BB6.Agent31PacketSource.e_packet (1536*v+255) 4 3 tail
  have h1 : 3*(1536*v+255)+4=4608*v+769 := by omega
  have h2 : 8*(1536*v+255)+9=12288*v+2049 := by omega
  simpa only [c3, h1, h2] using h

private theorem p4_input (v : Nat) :
    BB6.Agent31PacketSource.packet (12288*v+2049) 6 3 tail =
    init (List.replicate (3*(4096*v+682)+1) true ++
      false :: (CryptidA.wordCode words ++ (false :: ys))) := by
  have hn : 12288*v+2049=3*(4096*v+682)+3 := by omega
  have hr : List.replicate (3*(4096*v+682)+3) true =
      true::true::List.replicate (3*(4096*v+682)+1) true := by
    rw [show 3*(4096*v+682)+3 =
      ((3*(4096*v+682)+1)+1)+1 by omega]
    rw [List.replicate_succ, List.replicate_succ]
  simp [BB6.Agent31PacketSource.packet, BB6.Agent31PacketSource.word,
    hn, hr, init, tail, words, ys, oppairs, CryptidA.wordCode,
    List.append_assoc]

private theorem p4 (v : Nat) :
    run (c4 v) (BB6.Agent31PacketSource.packet (12288*v+2049) 6 3 tail) =
      regularExit v := by
  have h := BB6.Agent35.full_A_code (4096*v+682) words ys
  have hinc : CryptidA.wordInc words = 10 := by decide
  have hn : 2*(4*(4096*v+682)+3+10)+5+6=32768*v+5493 := by omega
  have hout : (⟨[],false,
      List.replicate (2*(4*(4096*v+682)+3+CryptidA.wordInc words)+5) true ++ ys, 5⟩ : Cfg) =
      regularExit v := by
    rw [hinc]
    simp only [regularExit, ys, List.replicate_append_replicate]
    congr 1
    omega
  rw [p4_input]
  simpa only [c4] using (Eq.trans h hout)

/-- Every v follows five exact original six-state source macros, returning
    to a pure-unary F/0 section. Physical terminal blank padding is respected. -/
theorem five_return (v : Nat) :
    ObsEq (run (fiveCost v) (entry v)) (regularExit v) := by
  have h0 := first v
  have h1 := p1 v
  have h2 := p2 v
  have h3 := p3 v
  have h4 := p4 v
  have hc : run (c1 v + (c2 v + (c3 v + c4 v)))
      (BB6.Agent31PacketSource.packet (648*v+109) 0 12 tail) = regularExit v := by
    rw [run_add, h1, run_add, h2, run_add, h3, h4]
  unfold fiveCost
  exact source_chain (eCost v) (c1 v+(c2 v+(c3 v+c4 v)))
    (entry v) (BB6.Agent31PacketSource.packet (648*v+109) 0 12 tail)
    (regularExit v) h0 (by rw [hc]; exact BB6.Padding.cfgEq_refl _)

#print axioms five_return
end BB6.Agent25EleventhPacket
