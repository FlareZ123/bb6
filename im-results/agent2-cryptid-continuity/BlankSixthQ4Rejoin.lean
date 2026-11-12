import Lean.Elab.Tactic.Omega
import BlankSixthExceptional
import ExceptionalE7SecondSafe
import PacketSource
import A110111CodeFirst

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2SixthQ4Rejoin

open CryptidBoundary BB6.BoundaryPadding

private def fixedTail : List Bool := false :: List.replicate 6 true

/-- The second E return from the q=4 E/E section is exactly the
    q=2,p=5 packet with the fixed six-one tail. -/
private theorem secondOutput_packet (u : Nat) :
    BB6.Agent2E7SecondSafe.secondOutput u 4 =
      BB6.Agent31PacketSource.packet (192*u+161) 2 5 fixedTail := by
  have hlen : 8*(24*u+19)+9 = 192*u+161 := by omega
  simp [BB6.Agent2E7SecondSafe.secondOutput,
    BB6.Agent2E7SecondSafe.suffix2,
    BB6.Agent31PacketSource.packet,
    BB6.Agent31PacketSource.word,
    fixedTail,
    CryptidBoundary.packetThree,
    CryptidBoundary.oppairs,
    hlen]

/-- The q=3,p=2 fixed-tail packet is an A-code prefix followed by
    the 110111 first-return word. -/
private theorem packet_to_A110111_start (k : Nat) :
    BB6.Agent31PacketSource.packet (3*k+3) 3 2 fixedTail =
      CryptidBoundary.init
        (List.replicate (3*k+1) true ++ false ::
          (CryptidA.wordCode (List.replicate 3 false) ++
            BB6.CryptidA110111CodeFirst.packet (List.replicate 3 true))) := by
  have hcode :
      CryptidA.wordCode (List.replicate 3 false) =
        CryptidBoundary.pairs 3 := by decide
  simp [BB6.Agent31PacketSource.packet,
    BB6.Agent31PacketSource.word,
    BB6.CryptidA110111CodeFirst.packet,
    fixedTail,
    CryptidBoundary.init,
    CryptidBoundary.oppairs,
    CryptidBoundary.pairs,
    hcode,
    List.append_assoc]

private theorem a110111_tail_shape :
    BB6.CryptidA110111CodeFirst.tail (List.replicate 3 true) =
      CryptidBoundary.oppairs 3 ++ List.replicate 3 true := by
  decide

private def a110111Time (k : Nat) : Nat :=
  let ws := List.replicate 3 false
  let ys := List.replicate 3 true
  let m := 4*k+3+CryptidA.wordInc ws
  12*k*k+41*k+32 + CryptidA.wordCost (4*k+3) ws + (2*m+24)

/-- A source-certified A110111 return for the q=3,p=2 fixed-tail packet. -/
private theorem a110111_rejoin (k : Nat) :
    ObsEq
      (run (a110111Time k)
        (BB6.Agent31PacketSource.packet (3*k+3) 3 2 fixedTail))
      (DRegularSource.sourceSection ⟨8*k+17,3,2⟩) := by
  let ws := List.replicate 3 false
  let ys := List.replicate 3 true
  have hinc : CryptidA.wordInc ws = 3 := by decide
  have htail :
      BB6.CryptidA110111CodeFirst.tail ys =
        CryptidBoundary.oppairs 3 ++ List.replicate 3 true := by
    simpa [ws, ys] using a110111_tail_shape
  have hA :=
    BB6.CryptidA110111CodeFirst.full_A_code_110111_first_return k ws ys
  rw [packet_to_A110111_start k]
  simpa [a110111Time, ws, ys, hinc, htail,
    DRegularSource.sourceSection, CryptidBoundary.init] using hA.1

/-- Every q=4 E/E source section with unary parameter u = 7 mod 9
    returns to regular L by E/E, then B, E, and the A110111 first return. -/
theorem q4_mod9_rejoin (s : Nat) :
    ∃ T, ObsEq
      (run T (BB6.Agent2E7SecondSafe.sourceStart (9*s+7) 4))
      (DRegularSource.sourceSection ⟨32768*s+28577,3,2⟩) := by
  let u := 9*s+7
  let kb := 576*s+501
  let ke := 1536*s+1338
  let ka := 4096*s+3570
  let t0 := BB6.Agent2E7SecondSafe.eTime u 4 +
    BB6.Agent2E7SecondSafe.middleTime u
  let tB := 12*kb*kb+49*kb+40
  let tE := 12*ke*ke+49*ke+58+6
  let tA := a110111Time ka
  have hEE0 :=
    BB6.Agent2E7SecondSafe.exceptional_EE_packet u 4 (by omega)
  have houter := secondOutput_packet u
  have hEE : ObsEq
      (run t0 (BB6.Agent2E7SecondSafe.sourceStart u 4))
      (BB6.Agent31PacketSource.packet (192*u+161) 2 5 fixedTail) := by
    rw [houter] at hEE0
    simpa [t0] using hEE0
  have hBstart : 192*u+161 = 3*kb+2 := by
    dsimp [u, kb]
    omega
  have hB : ObsEq
      (run tB
        (BB6.Agent31PacketSource.packet (192*u+161) 2 5 fixedTail))
      (BB6.Agent31PacketSource.packet (8*kb+10) 1 5 fixedTail) := by
    rw [hBstart]
    exact BB6.Agent31PacketSource.b_packet kb 1 5 fixedTail
  have hEstart : 8*kb+10 = 3*ke+4 := by
    dsimp [kb, ke]
    omega
  have hE : ObsEq
      (run tE
        (BB6.Agent31PacketSource.packet (8*kb+10) 1 5 fixedTail))
      (BB6.Agent31PacketSource.packet (8*ke+9) 3 2 fixedTail) := by
    rw [hEstart]
    exact BB6.Agent31PacketSource.e_packet ke 1 2 fixedTail
  have hBE : ObsEq
      (run (tB+tE)
        (BB6.Agent31PacketSource.packet (192*u+161) 2 5 fixedTail))
      (BB6.Agent31PacketSource.packet (8*ke+9) 3 2 fixedTail) := by
    exact source_chain tB tE
      (BB6.Agent31PacketSource.packet (192*u+161) 2 5 fixedTail)
      (BB6.Agent31PacketSource.packet (8*kb+10) 1 5 fixedTail)
      (BB6.Agent31PacketSource.packet (8*ke+9) 3 2 fixedTail)
      hB hE
  have hAstart : 8*ke+9 = 3*ka+3 := by
    dsimp [ke, ka]
    omega
  have hA : ObsEq
      (run tA
        (BB6.Agent31PacketSource.packet (8*ke+9) 3 2 fixedTail))
      (DRegularSource.sourceSection ⟨8*ka+17,3,2⟩) := by
    rw [hAstart]
    exact a110111_rejoin ka
  have hfinal : 8*ka+17 = 32768*s+28577 := by
    dsimp [ka]
    omega
  refine ⟨t0+tB+tE+tA, ?_⟩
  have hfirst := source_chain t0 (tB+tE)
      (BB6.Agent2E7SecondSafe.sourceStart u 4)
      (BB6.Agent31PacketSource.packet (192*u+161) 2 5 fixedTail)
      (BB6.Agent31PacketSource.packet (8*ke+9) 3 2 fixedTail)
      hEE hBE
  have hlast := source_chain (t0+tB+tE) tA
      (BB6.Agent2E7SecondSafe.sourceStart u 4)
      (BB6.Agent31PacketSource.packet (8*ke+9) 3 2 fixedTail)
      (DRegularSource.sourceSection ⟨8*ka+17,3,2⟩)
      hfirst hA
  simpa [hfinal] using hlast

def u6 : Nat := (BB6.Agent25SixthRoot.t6-2)/3
def s6 : Nat := (u6-7)/9

/-- Exact 3-adic residue of the sixth blank-root q=4 exception:
    u6 = 484 (mod 2187), hence u6 = 7 (mod 9). -/
theorem u6_mod2187 : u6 % 2187 = 484 := by decide

theorem u6_form :
    BB6.Agent25SixthRoot.t6 = 3*u6+2 := by
  dsimp [u6]
  omega

theorem u6_eq : u6 = 9*s6+7 := by
  have hmod : u6 % 9 = 7 := by
    have := u6_mod2187
    omega
  dsimp [s6]
  omega

/-- The sixth source-certified blank-root q=4 E/E section closes through
    the previously uncovered u = 7 mod 9 B-E-A110111 corridor and
    returns to regular L at (32768*s6+28577, 3, 2). -/
theorem sixth_q4_root_rejoin_original :
    ∃ T, ObsEq
      (run (BB6.Agent25SixthRoot.sixthExceptionTime+T) blank)
      (DRegularSource.sourceSection ⟨32768*s6+28577,3,3⟩) := by
  obtain ⟨T,hclose⟩ := q4_mod9_rejoin s6
  have hroot : ObsEq
      (run BB6.Agent25SixthRoot.sixthExceptionTime blank)
      (BB6.Agent2E7SecondSafe.sourceStart (9*s6+7) 4) := by
    have hstate :
        DRegularSource.sourceSection
          ⟨9*BB6.Agent25SixthRoot.t6+7,4,1⟩ =
        BB6.Agent2E7SecondSafe.sourceStart (9*s6+7) 4 := by
      simp [BB6.Agent2E7SecondSafe.sourceStart,
        DRegularSource.sourceSection, u6_eq, u6_form]
    rw [hstate]
    exact BB6.Agent25SixthRoot.sixthException_original
  refine ⟨T, ?_⟩
  exact source_chain BB6.Agent25SixthRoot.sixthExceptionTime T
    blank
    (BB6.Agent2E7SecondSafe.sourceStart (9*s6+7) 4)
    (DRegularSource.sourceSection ⟨32768*s6+28577,3,3⟩)
    hroot hclose

#print axioms q4_mod9_rejoin
#print axioms sixth_q4_root_rejoin_original

end BB6.Agent2SixthQ4Rejoin
