import Lean.Elab.Tactic.Omega
import EAllDouble
import PacketPaths
import ShortTripleGate
import BoundaryPadding

set_option maxHeartbeats 100000000
set_option maxRecDepth 10000

namespace BB6.Agent36SixthPacket
open CryptidBoundary BB6.BoundaryPadding

private def tail : List Bool := false :: List.replicate 6 true
private def words : List Bool := [false,false,false]
private def finalTail : List Bool := [true,true,true]

/-- Exactly the true-blank sixth exceptional input, when its index is 27*v+23. -/
def entry (v : Nat) : Cfg :=
  init (List.replicate (3*(81*v+70)+2) true ++
    false :: (pairs 3 ++ [true,true]))

def eCost (v : Nat) : Nat := BB6.Agent32EAll.duration (81*v+70) 3
private def c1 (v : Nat) : Nat :=
  12*(216*v+187)*(216*v+187)+49*(216*v+187)+58
private def c2 (v : Nat) : Nat :=
  12*(576*v+501)*(576*v+501)+49*(576*v+501)+40
private def c3 (v : Nat) : Nat :=
  12*(1536*v+1338)*(1536*v+1338)+49*(1536*v+1338)+64
private def c4 (v : Nat) : Nat :=
  (12*(4096*v+3570)*(4096*v+3570)+41*(4096*v+3570)+32) +
    (CryptidA.wordCost (4*(4096*v+3570)+3) words +
      (2*((4*(4096*v+3570)+3)+CryptidA.wordInc words)+24))

def fiveCost (v : Nat) : Nat := eCost v + (c1 v + (c2 v + (c3 v + c4 v)))

def regularExit (v : Nat) : Cfg :=
  ⟨[],false,List.replicate (32768*v+28577) true ++
    (oppairs 3 ++ [true,true]),5⟩

private theorem first (v : Nat) :
    ObsEq (run (eCost v) (entry v))
      (BB6.Agent31PacketSource.packet (648*v+565) 0 8 tail) := by
  have h := BB6.Agent32EAll.all_e_double_implicit_blank (81*v+70) 3
  have ho : BB6.Agent32EAll.output (81*v+70) 3 [] =
      BB6.Agent31PacketSource.packet (648*v+565) 0 8 tail := by
    have hn : 8*(81*v+70)+5=648*v+565 := by omega
    simp [BB6.Agent32EAll.output, BB6.Agent31PacketSource.packet,
      BB6.Agent31PacketSource.word, tail, hn, oppairs]
  rw [ho] at h
  simpa only [eCost, entry] using h

private theorem p1 (v : Nat) :
    run (c1 v) (BB6.Agent31PacketSource.packet (648*v+565) 0 8 tail) =
      BB6.Agent31PacketSource.packet (1728*v+1505) 2 5 tail := by
  have h := BB6.Agent31PacketSource.e_packet (216*v+187) 0 5 tail
  have h1 : 3*(216*v+187)+4=648*v+565 := by omega
  have h2 : 8*(216*v+187)+9=1728*v+1505 := by omega
  simpa only [c1, h1, h2] using h

private theorem p2 (v : Nat) :
    run (c2 v) (BB6.Agent31PacketSource.packet (1728*v+1505) 2 5 tail) =
      BB6.Agent31PacketSource.packet (4608*v+4018) 1 5 tail := by
  have h := BB6.Agent31PacketSource.b_packet (576*v+501) 1 5 tail
  have h1 : 3*(576*v+501)+2=1728*v+1505 := by omega
  have h2 : 8*(576*v+501)+10=4608*v+4018 := by omega
  simpa only [c2, h1, h2] using h

private theorem p3 (v : Nat) :
    run (c3 v) (BB6.Agent31PacketSource.packet (4608*v+4018) 1 5 tail) =
      BB6.Agent31PacketSource.packet (12288*v+10713) 3 2 tail := by
  have h := BB6.Agent31PacketSource.e_packet (1536*v+1338) 1 2 tail
  have h1 : 3*(1536*v+1338)+4=4608*v+4018 := by omega
  have h2 : 8*(1536*v+1338)+9=12288*v+10713 := by omega
  simpa only [c3, h1, h2] using h

private theorem p4_input (v : Nat) :
    BB6.Agent31PacketSource.packet (12288*v+10713) 3 2 tail =
    init (List.replicate (3*(4096*v+3570)+1) true ++
      false :: (CryptidA.wordCode words ++
        ([true,true,false] ++ ([true,true,true] ++ finalTail)))) := by
  have hn : 12288*v+10713=3*(4096*v+3570)+3 := by omega
  have hr : List.replicate (3*(4096*v+3570)+3) true =
      true::true::List.replicate (3*(4096*v+3570)+1) true := by
    rw [show 3*(4096*v+3570)+3 =
      ((3*(4096*v+3570)+1)+1)+1 by omega]
    rw [List.replicate_succ, List.replicate_succ]
  simp [BB6.Agent31PacketSource.packet,BB6.Agent31PacketSource.word,
    hn, hr, init,tail,words,finalTail,oppairs,CryptidA.wordCode,
    List.append_assoc]

private theorem p4 (v : Nat) :
    run (c4 v) (BB6.Agent31PacketSource.packet (12288*v+10713) 3 2 tail) =
      regularExit v := by
  have h := BB6.CryptidBridge.complete_A_word_short_three
    (4096*v+3570) words finalTail
  have hinc : CryptidA.wordInc words = 3 := by decide
  have hn : 2*((4*(4096*v+3570)+3)+CryptidA.wordInc words)+5 =
      32768*v+28577 := by rw [hinc]; omega
  have ht : CryptidBoundary.packetThree ++ finalTail =
      oppairs 3 ++ [true,true] := by decide
  have ho : (⟨[],false,
      List.replicate (2*((4*(4096*v+3570)+3)+CryptidA.wordInc words)+5) true ++
        (CryptidBoundary.packetThree ++ finalTail),5⟩ : Cfg) = regularExit v := by
    rw [hn, ht]
    rfl
  rw [p4_input]
  simpa only [c4] using (Eq.trans h ho)

/-- Five original-machine specified F/0 endpoints of the sixth-escape family,
    with implicit blank tape padding handled by observational equality. -/
theorem five_return (v : Nat) :
    ObsEq (run (fiveCost v) (entry v)) (regularExit v) := by
  have h0 := first v
  have h1 := p1 v
  have h2 := p2 v
  have h3 := p3 v
  have h4 := p4 v
  have hc : run (c1 v + (c2 v + (c3 v + c4 v)))
      (BB6.Agent31PacketSource.packet (648*v+565) 0 8 tail) = regularExit v := by
    rw [run_add, h1, run_add, h2, run_add, h3, h4]
  unfold fiveCost
  exact source_chain (eCost v) (c1 v+(c2 v+(c3 v+c4 v)))
    (entry v) (BB6.Agent31PacketSource.packet (648*v+565) 0 8 tail)
    (regularExit v) h0 (by rw [hc]; exact BB6.Padding.cfgEq_refl _)

#print axioms five_return
end BB6.Agent36SixthPacket
