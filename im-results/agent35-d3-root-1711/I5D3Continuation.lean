import I5ExceptionalRejoin
import DRegularFast
import DRegularSourceShift
import ESecondSource
import PacketSource
import ExceptionalBGeneral
import APacketGeneral
import APacketUnary
import EDouble
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 0

namespace BB6.Agent35I5Continuation

open CryptidBoundary
open DRegular
open BB6.BoundaryPadding
open BB6.Agent19.Physical
open BB6.Portfolio
open BB6.Agent31SecondSource
open BB6.Agent31PacketSource
open BB6.Agent25BGeneral
open BB6.Agent35APacketGeneral
open BB6.Agent35APacketUnary

def ys : List Bool := BB6.Agent35APacketGeneral.ys

/-- The already source-certified seed5 E/B/B return. -/
def s0 : DRegular.L :=
  BB6.Agent35I5Exceptional.pureReentry BB6.Agent35I5Exceptional.t5

/-- Six exact regular-orbit checkpoints, evaluated with the 512-step
    3-adic fast runner. The parameters are extracted from the computed
    states; the following certificates pin down each section and residue. -/
def raw1 : Option DRegular.L := BB6.DRegularFast.fastRun 4675 s0
def t1 : Nat := ((raw1.getD (⟨0,0,0⟩ : DRegular.L)).a - 7) / 9
def e1 : DRegular.L := ⟨9*t1+7,4,1⟩
theorem raw1_data : raw1 = some e1 ∧ t1 % 3 = 0 := by decide

def kA1 : Nat := (64*t1+30)/3
def s1 : DRegular.L := ⟨8*kA1+23,3,2⟩

def raw2 : Option DRegular.L := BB6.DRegularFast.fastRun 1085 s1
def t2 : Nat := ((raw2.getD (⟨0,0,0⟩ : DRegular.L)).a - 7) / 9
def e2 : DRegular.L := ⟨9*t2+7,5,1⟩
theorem raw2_data : raw2 = some e2 ∧ t2 % 3 = 0 := by decide

def kA2 : Nat := (64*t2+30)/3
def s2 : DRegular.L := ⟨8*kA2+49,0,0⟩

def raw3 : Option DRegular.L := BB6.DRegularFast.fastRun 611 s2
def t3 : Nat := ((raw3.getD (⟨0,0,0⟩ : DRegular.L)).a - 10) / 9
def e3 : DRegular.L := ⟨9*t3+10,8,1⟩
theorem raw3_data : raw3 = some e3 := by decide

def s3 : DRegular.L := ⟨64*t3+117,0,0⟩

def raw4 : Option DRegular.L := BB6.DRegularFast.fastRun 6911 s3
def t4 : Nat := ((raw4.getD (⟨0,0,0⟩ : DRegular.L)).a - 4) / 9
def e4 : DRegular.L := ⟨9*t4+4,5,1⟩
theorem raw4_data : raw4 = some e4 := by decide

def s4 : DRegular.L := ⟨64*t4+27,1,5⟩

/-- Executable probe only: binary-search the first departure from DRegular.
    Its output is not a source proof and must not be used as a theorem premise. -/
def locateExit : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if lo < hi then
      let mid := (lo+hi)/2
      if (BB6.DRegularFast.fastRun mid s4).isSome then
        locateExit fuel (mid+1) hi
      else
        locateExit fuel lo mid
    else lo

#eval ("first_none_after_s4", locateExit 13 0 2511)
#eval ("last_regular_before_exit",
  (BB6.DRegularFast.fastRun ((locateExit 13 0 2511)-1) s4).map
    (fun u => (u.a % 81, u.q, u.b)))
#eval ("first_none_confirmed",
  (BB6.DRegularFast.fastRun (locateExit 13 0 2511) s4).isNone)

theorem regular_source (n : Nat) (s t : DRegular.L)
    (hc : DRegular.Canon s)
    (hf : BB6.DRegularFast.fastRun n s = some t) :
    ObsEq (run (DRegular.accumulated n s) (DRegularSource.sourceSection s))
      (DRegularSource.sourceSection t) := by
  have hr : DRegular.run n s = some t := by
    rw [BB6.DRegularFast.fastRun_correct n s hc]
    exact hf
  exact (BB6.DRegularSourceShift.paired_original_run s t n 0 hc hr).1

private theorem second_start_eq_source (t h : Nat) :
    BB6.Agent31SecondSource.start t h =
      DRegularSource.sourceSection ⟨9*t+7,h+3,1⟩ := by
  let xs : List Bool :=
    List.replicate (9*t+5) true ++
      (CryptidBoundary.oppairs (h+3) ++ [true])
  have hlen : 9*t+7-2 = 9*t+5 := by omega
  have hq : h+3 = (h+2)+1 := by omega
  have hk : 3*(3*t+1)+2 = 9*t+5 := by omega
  have hsource :
      DRegularSource.sourceSection ⟨9*t+7,h+3,1⟩ =
        CryptidBoundary.init xs := by
    simp [DRegularSource.sourceSection,xs,hlen]
  have hstart :
      BB6.Agent31SecondSource.start t h =
        CryptidBoundary.init xs := by
    simp [BB6.Agent31SecondSource.start,xs,hq,hk,
      BB6.Agent25BGeneral.oppairs_last]
  exact hstart.trans hsource.symm

private theorem second_finish_eq_packet (t h : Nat) :
    BB6.Agent31SecondSource.finish t h =
      BB6.Agent31PacketSource.packet (64*t+33) 2 (2*h+3) ys := by
  have hlen : 8*(8*t+3)+9 = 64*t+33 := by omega
  simp [BB6.Agent31SecondSource.finish,BB6.Agent31PacketSource.packet,
    BB6.Agent31PacketSource.word,ys,BB6.Agent35APacketGeneral.ys,
    hlen,List.append_assoc]

/-- Two source-certified E returns, expressed directly at the regular
    source section and its exact packet endpoint. -/
private theorem two_return_packet (t h : Nat) :
    ObsEq
      (run (BB6.Agent31SecondSource.firstCost t h +
          BB6.Agent31SecondSource.secondCost t)
        (DRegularSource.sourceSection ⟨9*t+7,h+3,1⟩))
      (BB6.Agent31PacketSource.packet (64*t+33) 2 (2*h+3) ys) := by
  have hTwo := BB6.Agent31SecondSource.two_returns_source t h
  rw [second_start_eq_source t h, second_finish_eq_packet t h] at hTwo
  exact hTwo

private theorem a_packet_regular_obs (k q r : Nat) :
    ObsEq
      (run (BB6.Agent35APacketGeneral.duration k q r)
        (BB6.Agent31PacketSource.packet (3*k+3) q (3*r+2) ys))
      (DRegularSource.sourceSection ⟨8*k+11+2*q+8*r,3,2⟩) := by
  change ObsEq
    (run (BB6.Agent35APacketGeneral.duration k q r)
      (BB6.Agent31PacketSource.packet (3*k+3) q (3*r+2)
        BB6.Agent35APacketGeneral.ys))
    (DRegularSource.sourceSection ⟨8*k+11+2*q+8*r,3,2⟩)
  rw [BB6.Agent35APacketGeneral.source_a_packet_regular]
  exact BB6.Padding.cfgEq_refl _

private theorem a_packet_unary_obs (k q r : Nat) :
    ObsEq
      (run (BB6.Agent35APacketUnary.duration k q r)
        (BB6.Agent31PacketSource.packet (3*k+3) q (3*r+1) ys))
      (DRegularSource.sourceSection ⟨8*k+29+2*q+8*r,0,0⟩) := by
  change ObsEq
    (run (BB6.Agent35APacketUnary.duration k q r)
      (BB6.Agent31PacketSource.packet (3*k+3) q (3*r+1)
        BB6.Agent35APacketUnary.ys))
    (DRegularSource.sourceSection ⟨8*k+29+2*q+8*r,0,0⟩)
  rw [BB6.Agent35APacketUnary.source_a_packet_unary]
  exact BB6.Padding.cfgEq_refl _

private theorem e_packet_obs (k q p : Nat) :
    ObsEq
      (run (12*k*k+49*k+58+6*q)
        (BB6.Agent31PacketSource.packet (3*k+4) q (p+3) ys))
      (BB6.Agent31PacketSource.packet (8*k+9) (q+2) p ys) := by
  rw [BB6.Agent31PacketSource.e_packet]
  exact BB6.Padding.cfgEq_refl _

def q4K (t : Nat) : Nat := (64*t+30)/3
def q4Out (t : Nat) : DRegular.L := ⟨8*q4K t+23,3,2⟩
def q4Cost (t : Nat) : Nat :=
  BB6.Agent31SecondSource.firstCost t 1 +
    BB6.Agent31SecondSource.secondCost t +
    BB6.Agent35APacketGeneral.duration (q4K t) 2 1

/-- The q=4 E exception has a third source return to L(.,3,2). -/
private theorem q4_rejoin (t : Nat) (ht : t % 3 = 0) :
    ObsEq (run (q4Cost t)
      (DRegularSource.sourceSection ⟨9*t+7,4,1⟩))
      (DRegularSource.sourceSection (q4Out t)) := by
  have hTwo := two_return_packet t 1
  have ha : 64*t+33 = 3*q4K t+3 := by
    dsimp [q4K]
    have h := Nat.mod_add_div t 3
    omega
  have hA :
      ObsEq
        (run (BB6.Agent35APacketGeneral.duration (q4K t) 2 1)
          (BB6.Agent31PacketSource.packet (64*t+33) 2 5 ys))
        (DRegularSource.sourceSection (q4Out t)) := by
    rw [ha]
    simpa [q4Out] using a_packet_regular_obs (q4K t) 2 1
  simpa [q4Cost,Nat.add_assoc] using
    (source_chain
      (BB6.Agent31SecondSource.firstCost t 1 +
        BB6.Agent31SecondSource.secondCost t)
      (BB6.Agent35APacketGeneral.duration (q4K t) 2 1)
      (DRegularSource.sourceSection ⟨9*t+7,4,1⟩)
      (BB6.Agent31PacketSource.packet (64*t+33) 2 5 ys)
      (DRegularSource.sourceSection (q4Out t))
      hTwo hA)

def q5K (t : Nat) : Nat := (64*t+30)/3
def q5Out (t : Nat) : DRegular.L := ⟨8*q5K t+49,0,0⟩
def q5Cost (t : Nat) : Nat :=
  BB6.Agent31SecondSource.firstCost t 2 +
    BB6.Agent31SecondSource.secondCost t +
    BB6.Agent35APacketUnary.duration (q5K t) 2 2

/-- The q=5 E exception also closes to a pure-unary regular section. -/
private theorem q5_rejoin (t : Nat) (ht : t % 3 = 0) :
    ObsEq (run (q5Cost t)
      (DRegularSource.sourceSection ⟨9*t+7,5,1⟩))
      (DRegularSource.sourceSection (q5Out t)) := by
  have hTwo := two_return_packet t 2
  have ha : 64*t+33 = 3*q5K t+3 := by
    dsimp [q5K]
    have h := Nat.mod_add_div t 3
    omega
  have hA :
      ObsEq
        (run (BB6.Agent35APacketUnary.duration (q5K t) 2 2)
          (BB6.Agent31PacketSource.packet (64*t+33) 2 7 ys))
        (DRegularSource.sourceSection (q5Out t)) := by
    rw [ha]
    simpa [q5Out] using a_packet_unary_obs (q5K t) 2 2
  simpa [q5Cost,Nat.add_assoc] using
    (source_chain
      (BB6.Agent31SecondSource.firstCost t 2 +
        BB6.Agent31SecondSource.secondCost t)
      (BB6.Agent35APacketUnary.duration (q5K t) 2 2)
      (DRegularSource.sourceSection ⟨9*t+7,5,1⟩)
      (BB6.Agent31PacketSource.packet (64*t+33) 2 7 ys)
      (DRegularSource.sourceSection (q5Out t))
      hTwo hA)

def eDoublePacketCost (k q : Nat) : Nat :=
  12*k*k+49*k+64+4*(q-2)

/-- Original-source E-double packet extraction for any q≥2 on the
    k=3t+2 branch, with the two far-right blanks handled by source_init_pad. -/
private theorem e_double_packet_source (t q : Nat) (hq : 2 ≤ q) :
    ObsEq
      (run (eDoublePacketCost (3*t+2) q)
        (DRegularSource.sourceSection ⟨9*t+10,q,1⟩))
      (BB6.Agent31PacketSource.packet (8*(3*t+2)+5) 0 (2*q) ys) := by
  let k : Nat := 3*t+2
  let xs : List Bool :=
    List.replicate (9*t+8) true ++
      (CryptidBoundary.oppairs q ++ [true])
  have hstart :
      DRegularSource.sourceSection ⟨9*t+10,q,1⟩ =
        CryptidBoundary.init xs := by
    have hlen : 9*t+10-2 = 9*t+8 := by omega
    simp [DRegularSource.sourceSection,xs,hlen]
  have hinput :
      CryptidBoundary.init (xs ++ List.replicate 2 false) =
        CryptidBoundary.init
          (List.replicate (3*k+2) true ++
            false :: (CryptidBoundary.pairs (q-2+1) ++
              [true,true,false,false])) := by
    have hlen : 3*k+2 = 9*t+8 := by dsimp [k]; omega
    have hsub : q-2+1 = q-1 := by omega
    have hlast :
        CryptidBoundary.oppairs q ++ [true] =
          false :: (CryptidBoundary.pairs (q-1) ++ [true,true]) := by
      cases q with
      | zero => omega
      | succ n =>
        simpa using (BB6.Agent25BGeneral.oppairs_last n)
    dsimp only [xs]
    rw [hlast]
    simp [hlen,hsub,List.append_assoc]
  have hcost :
      eDoublePacketCost k q = 12*k*k+49*k+64+4*(q-2) := rfl
  have hlen2 : 2*((q-2)+1)+2 = 2*q := by omega
  have hraw :
      run (eDoublePacketCost k q)
        (CryptidBoundary.init (xs ++ List.replicate 2 false)) =
        BB6.Agent31PacketSource.packet (8*k+5) 0 (2*q) ys := by
    rw [hinput,hcost]
    simpa [BB6.Agent31PacketSource.packet,BB6.Agent31PacketSource.word,
      ys,BB6.Agent35APacketGeneral.ys,hlen2,
      CryptidBoundary.oppairs,List.append_assoc] using
      (BB6.Agent35.full_E_double k (q-2) [])
  have hp := BB6.BoundaryPadding.source_init_pad
    (eDoublePacketCost k q) 2 xs
  rw [hraw] at hp
  rw [hstart]
  simpa [k] using hp

def q8K (t : Nat) : Nat := 8*t+6
def q8Out (t : Nat) : DRegular.L := ⟨64*t+117,0,0⟩
def q8Cost (t : Nat) : Nat :=
  eDoublePacketCost (3*t+2) 8 +
    BB6.Agent35APacketUnary.duration (q8K t) 0 5

/-- The q=8, k=3t+2 exception closes through E-double and a 3r+1 A packet. -/
theorem q8_rejoin (t : Nat) :
    ObsEq (run (q8Cost t)
      (DRegularSource.sourceSection ⟨9*t+10,8,1⟩))
      (DRegularSource.sourceSection (q8Out t)) := by
  have hE := e_double_packet_source t 8 (by omega)
  have ha : 8*(3*t+2)+5 = 3*q8K t+3 := by
    dsimp [q8K]
    omega
  have hA :
      ObsEq
        (run (BB6.Agent35APacketUnary.duration (q8K t) 0 5)
          (BB6.Agent31PacketSource.packet (8*(3*t+2)+5) 0 16 ys))
        (DRegularSource.sourceSection (q8Out t)) := by
    rw [ha]
    have hout : 8*q8K t+29+2*0+8*5 = 64*t+117 := by
      dsimp [q8K]
      omega
    simpa only [q8Out,hout] using a_packet_unary_obs (q8K t) 0 5
  simpa [q8Cost,Nat.add_assoc] using
    (source_chain
      (eDoublePacketCost (3*t+2) 8)
      (BB6.Agent35APacketUnary.duration (q8K t) 0 5)
      (DRegularSource.sourceSection ⟨9*t+10,8,1⟩)
      (BB6.Agent31PacketSource.packet (8*(3*t+2)+5) 0 16 ys)
      (DRegularSource.sourceSection (q8Out t))
      hE hA)

def q5BOut (t : Nat) : DRegular.L := ⟨64*t+27,1,5⟩
def q5BCost (t : Nat) : Nat :=
  BB6.Agent32EAll.duration (3*t) 4 + BB6.Agent25BGeneral.bCost t

/-- The general E/B source theorem restores the q=5,k=3t branch. -/
private theorem q5B_rejoin (t : Nat) :
    ObsEq (run (q5BCost t)
      (DRegularSource.sourceSection ⟨9*t+4,5,1⟩))
      (DRegularSource.sourceSection (q5BOut t)) := by
  simpa [q5BCost,q5BOut] using
    (BB6.Agent25BGeneral.exceptional_EB_general t 3)

def q7AK (t : Nat) : Nat := 8*t+6
def q7AOut (t : Nat) : DRegular.L := ⟨64*t+91,3,2⟩
def q7ACost (t : Nat) : Nat :=
  eDoublePacketCost (3*t+2) 7 +
    BB6.Agent35APacketGeneral.duration (q7AK t) 0 4

/-- The q=7, k=3t+2 exception closes by E-double and the 3r+2 A code. -/
theorem q7A_rejoin (t : Nat) :
    ObsEq (run (q7ACost t)
      (DRegularSource.sourceSection ⟨9*t+10,7,1⟩))
      (DRegularSource.sourceSection (q7AOut t)) := by
  have hE := e_double_packet_source t 7 (by omega)
  have ha : 8*(3*t+2)+5 = 3*q7AK t+3 := by
    dsimp [q7AK]
    omega
  have hA :
      ObsEq
        (run (BB6.Agent35APacketGeneral.duration (q7AK t) 0 4)
          (BB6.Agent31PacketSource.packet (8*(3*t+2)+5) 0 14 ys))
        (DRegularSource.sourceSection (q7AOut t)) := by
    rw [ha]
    have hout : 8*q7AK t+11+2*0+8*4 = 64*t+91 := by
      dsimp [q7AK]
      omega
    simpa only [q7AOut,hout] using a_packet_regular_obs (q7AK t) 0 4
  simpa [q7ACost,Nat.add_assoc] using
    (source_chain
      (eDoublePacketCost (3*t+2) 7)
      (BB6.Agent35APacketGeneral.duration (q7AK t) 0 4)
      (DRegularSource.sourceSection ⟨9*t+10,7,1⟩)
      (BB6.Agent31PacketSource.packet (8*(3*t+2)+5) 0 14 ys)
      (DRegularSource.sourceSection (q7AOut t))
      hE hA)

def ePacketCost (k q : Nat) : Nat := 12*k*k+49*k+58+6*q
def q7K0 (t : Nat) : Nat := 576*(t/27)+95
def q7K1 (t : Nat) : Nat := 1536*(t/27)+255
def q7KA (t : Nat) : Nat := 4096*(t/27)+682
def q7EscapeOut (t : Nat) : DRegular.L := ⟨8*q7KA t+31,3,2⟩
def q7EscapeCost (t : Nat) : Nat :=
  BB6.Agent31SecondSource.firstCost t 4 +
    BB6.Agent31SecondSource.secondCost t +
    ePacketCost (q7K0 t) 2 +
    ePacketCost (q7K1 t) 4 +
    BB6.Agent35APacketGeneral.duration (q7KA t) 6 1

/-- Source-certified fourth return for the seed5 q=7 E exception:
    t≡4 (mod 27), i.e. k=3t+1≡13 (mod 27). -/
theorem q7_escape_rejoin (t : Nat) (ht : t % 27 = 4) :
    ObsEq (run (q7EscapeCost t)
      (DRegularSource.sourceSection ⟨9*t+7,7,1⟩))
      (DRegularSource.sourceSection (q7EscapeOut t)) := by
  have hdiv : t = 27*(t/27)+4 := by
    have h := Nat.mod_add_div t 27
    omega
  have h0 : 64*t+33 = 3*q7K0 t+4 := by
    dsimp [q7K0]
    rw [hdiv]
    omega
  have h1 : 8*q7K0 t+9 = 3*q7K1 t+4 := by
    dsimp [q7K0,q7K1]
    omega
  have h2 : 8*q7K1 t+9 = 3*q7KA t+3 := by
    dsimp [q7K1,q7KA]
    omega
  have hTwo := two_return_packet t 4
  have hE1 :
      ObsEq
        (run (ePacketCost (q7K0 t) 2)
          (BB6.Agent31PacketSource.packet (64*t+33) 2 11 ys))
        (BB6.Agent31PacketSource.packet (8*q7K0 t+9) 4 8 ys) := by
    rw [h0]
    exact e_packet_obs (q7K0 t) 2 8
  have hE2 :
      ObsEq
        (run (ePacketCost (q7K1 t) 4)
          (BB6.Agent31PacketSource.packet (8*q7K0 t+9) 4 8 ys))
        (BB6.Agent31PacketSource.packet (8*q7K1 t+9) 6 5 ys) := by
    rw [h1]
    exact e_packet_obs (q7K1 t) 4 5
  have hA :
      ObsEq
        (run (BB6.Agent35APacketGeneral.duration (q7KA t) 6 1)
          (BB6.Agent31PacketSource.packet (8*q7K1 t+9) 6 5 ys))
        (DRegularSource.sourceSection (q7EscapeOut t)) := by
    rw [h2]
    simpa [q7EscapeOut] using a_packet_regular_obs (q7KA t) 6 1
  have h01 := source_chain
    (BB6.Agent31SecondSource.firstCost t 4 +
      BB6.Agent31SecondSource.secondCost t)
    (ePacketCost (q7K0 t) 2)
    (DRegularSource.sourceSection ⟨9*t+7,7,1⟩)
    (BB6.Agent31PacketSource.packet (64*t+33) 2 11 ys)
    (BB6.Agent31PacketSource.packet (8*q7K0 t+9) 4 8 ys)
    hTwo hE1
  have h012 := source_chain
    (BB6.Agent31SecondSource.firstCost t 4 +
      BB6.Agent31SecondSource.secondCost t + ePacketCost (q7K0 t) 2)
    (ePacketCost (q7K1 t) 4)
    (DRegularSource.sourceSection ⟨9*t+7,7,1⟩)
    (BB6.Agent31PacketSource.packet (8*q7K0 t+9) 4 8 ys)
    (BB6.Agent31PacketSource.packet (8*q7K1 t+9) 6 5 ys)
    h01 hE2
  simpa [q7EscapeCost,Nat.add_assoc] using
    (source_chain
      (BB6.Agent31SecondSource.firstCost t 4 +
        BB6.Agent31SecondSource.secondCost t +
        ePacketCost (q7K0 t) 2 + ePacketCost (q7K1 t) 4)
      (BB6.Agent35APacketGeneral.duration (q7KA t) 6 1)
      (DRegularSource.sourceSection ⟨9*t+7,7,1⟩)
      (BB6.Agent31PacketSource.packet (8*q7K1 t+9) 6 5 ys)
      (DRegularSource.sourceSection (q7EscapeOut t))
      h012 hA)


/-- Fourth source return for the q=5, k≡25 (mod 27) E branch.
    For t≡8 (mod 9), two E events expose a B packet, followed by an
    A-code return to a pure-unary section. These are exact raw run costs. -/
def q5FourthK (t : Nat) : Nat := 192*(t/9)+181
def q5FourthA (t : Nat) : Nat := 512*(t/9)+485
def q5FourthOut (t : Nat) : DRegular.L :=
  ⟨8*q5FourthA t+47,0,0⟩
def q5FourthCost (t : Nat) : Nat :=
  BB6.Agent31SecondSource.firstCost t 2 +
  BB6.Agent31SecondSource.secondCost t +
  (12*q5FourthK t*q5FourthK t+49*q5FourthK t+40) +
  BB6.Agent35APacketUnary.duration (q5FourthA t) 1 2

theorem q5_fourth_source (t : Nat) (ht : t % 9 = 8) :
    ObsEq (run (q5FourthCost t)
      (DRegularSource.sourceSection ⟨9*t+7,5,1⟩))
      (DRegularSource.sourceSection (q5FourthOut t)) := by
  have htdiv : t = 9*(t/9)+8 := by
    have h := Nat.mod_add_div t 9
    omega
  have h0 : 64*t+33 = 3*q5FourthK t+2 := by
    dsimp [q5FourthK]
    omega
  have h1 : 8*q5FourthK t+10 = 3*q5FourthA t+3 := by
    dsimp [q5FourthK,q5FourthA]
    omega
  have hTwo := two_return_packet t 2
  have hB :
      ObsEq
        (run (12*q5FourthK t*q5FourthK t+49*q5FourthK t+40)
          (BB6.Agent31PacketSource.packet (64*t+33) 2 7 ys))
        (BB6.Agent31PacketSource.packet (8*q5FourthK t+10) 1 7 ys) := by
    rw [h0]
    rw [BB6.Agent31PacketSource.b_packet (q5FourthK t) 1 7 ys]
    exact BB6.Padding.cfgEq_refl _
  have hA :
      ObsEq
        (run (BB6.Agent35APacketUnary.duration (q5FourthA t) 1 2)
          (BB6.Agent31PacketSource.packet (8*q5FourthK t+10) 1 7 ys))
        (DRegularSource.sourceSection (q5FourthOut t)) := by
    rw [h1]
    have hout : 8*q5FourthA t+29+2*1+8*2 =
        8*q5FourthA t+47 := by omega
    simpa only [q5FourthOut,hout] using
      a_packet_unary_obs (q5FourthA t) 1 2
  have hThree := source_chain
    (BB6.Agent31SecondSource.firstCost t 2 +
      BB6.Agent31SecondSource.secondCost t)
    (12*q5FourthK t*q5FourthK t+49*q5FourthK t+40)
    (DRegularSource.sourceSection ⟨9*t+7,5,1⟩)
    (BB6.Agent31PacketSource.packet (64*t+33) 2 7 ys)
    (BB6.Agent31PacketSource.packet (8*q5FourthK t+10) 1 7 ys)
    hTwo hB
  simpa [q5FourthCost,Nat.add_assoc] using
    (source_chain
      (BB6.Agent31SecondSource.firstCost t 2 +
        BB6.Agent31SecondSource.secondCost t +
        (12*q5FourthK t*q5FourthK t+49*q5FourthK t+40))
      (BB6.Agent35APacketUnary.duration (q5FourthA t) 1 2)
      (DRegularSource.sourceSection ⟨9*t+7,5,1⟩)
      (BB6.Agent31PacketSource.packet (8*q5FourthK t+10) 1 7 ys)
      (DRegularSource.sourceSection (q5FourthOut t))
      hThree hA)

def regCost1 : Nat := DRegular.accumulated 4675 s0
def regCost2 : Nat := DRegular.accumulated 1085 s1
def regCost3 : Nat := DRegular.accumulated 611 s2
def regCost4 : Nat := DRegular.accumulated 6911 s3
private theorem reg1_obs :
    ObsEq (run regCost1 (DRegularSource.sourceSection s0))
      (DRegularSource.sourceSection e1) := by
  have hc : DRegular.Canon s0 := by
    refine ⟨?_, ?_⟩
    · simp [s0,BB6.Agent35I5Exceptional.pureReentry]
      omega
    · simp [s0,BB6.Agent35I5Exceptional.pureReentry]
  exact regular_source 4675 s0 e1 hc raw1_data.1

private theorem reg2_obs :
    ObsEq (run regCost2 (DRegularSource.sourceSection s1))
      (DRegularSource.sourceSection e2) := by
  have hc : DRegular.Canon s1 := by
    refine ⟨?_, ?_⟩
    · simp [s1]
    · simp [s1]
  exact regular_source 1085 s1 e2 hc raw2_data.1

private theorem reg3_obs :
    ObsEq (run regCost3 (DRegularSource.sourceSection s2))
      (DRegularSource.sourceSection e3) := by
  have hc : DRegular.Canon s2 := by
    refine ⟨?_, ?_⟩
    · simp [s2]
    · simp [s2]
  exact regular_source 611 s2 e3 hc raw3_data

private theorem reg4_obs :
    ObsEq (run regCost4 (DRegularSource.sourceSection s3))
      (DRegularSource.sourceSection e4) := by
  have hc : DRegular.Canon s3 := by
    refine ⟨?_, ?_⟩
    · simp [s3]
    · simp [s3]
  exact regular_source 6911 s3 e4 hc raw4_data

def continuationCost : Nat :=
  regCost1 + q4Cost t1 +
  regCost2 + q5Cost t2 +
  regCost3 + q8Cost t3 +
  regCost4 + q5BCost t4

/-- The authentic D3 root resumes four exact regular stretches and four
    exceptional source returns. The next hypothesized stretch is invalid:
    the regular model exits before return 2511 from s4. -/
theorem continuation_source :
    ObsEq (run continuationCost (DRegularSource.sourceSection s0))
      (DRegularSource.sourceSection s4) := by
  have h01 := source_chain regCost1 (q4Cost t1)
    (DRegularSource.sourceSection s0)
    (DRegularSource.sourceSection e1)
    (DRegularSource.sourceSection s1)
    reg1_obs (q4_rejoin t1 raw1_data.2)
  have h02 := source_chain
    (regCost1+q4Cost t1) regCost2
    (DRegularSource.sourceSection s0)
    (DRegularSource.sourceSection s1)
    (DRegularSource.sourceSection e2)
    h01 reg2_obs
  have h03 := source_chain
    (regCost1+q4Cost t1+regCost2) (q5Cost t2)
    (DRegularSource.sourceSection s0)
    (DRegularSource.sourceSection e2)
    (DRegularSource.sourceSection s2)
    h02 (q5_rejoin t2 raw2_data.2)
  have h04 := source_chain
    (regCost1+q4Cost t1+regCost2+q5Cost t2) regCost3
    (DRegularSource.sourceSection s0)
    (DRegularSource.sourceSection s2)
    (DRegularSource.sourceSection e3)
    h03 reg3_obs
  have h05 := source_chain
    (regCost1+q4Cost t1+regCost2+q5Cost t2+regCost3) (q8Cost t3)
    (DRegularSource.sourceSection s0)
    (DRegularSource.sourceSection e3)
    (DRegularSource.sourceSection s3)
    h04 (q8_rejoin t3)
  have h06 := source_chain
    (regCost1+q4Cost t1+regCost2+q5Cost t2+regCost3+q8Cost t3) regCost4
    (DRegularSource.sourceSection s0)
    (DRegularSource.sourceSection s3)
    (DRegularSource.sourceSection e4)
    h05 reg4_obs
  have h07 := source_chain
    (regCost1+q4Cost t1+regCost2+q5Cost t2+regCost3+q8Cost t3+regCost4)
    (q5BCost t4)
    (DRegularSource.sourceSection s0)
    (DRegularSource.sourceSection e4)
    (DRegularSource.sourceSection s4)
    h06 (q5B_rejoin t4)
  simpa [continuationCost,Nat.add_assoc] using h07

def sourceElapsedFinal : Nat :=
  BB6.Agent35I5Exceptional.sourceElapsed + continuationCost
def horizonFinal : Nat := 15 + sourceElapsedFinal

theorem root_source :
    ObsEq (run sourceElapsedFinal (sourceUnary 5))
      (DRegularSource.sourceSection s4) := by
  exact source_chain
    BB6.Agent35I5Exceptional.sourceElapsed continuationCost
    (sourceUnary 5)
    (DRegularSource.sourceSection s0)
    (DRegularSource.sourceSection s4)
    BB6.Agent35I5Exceptional.i5_three_exception_rejoin
    continuation_source

theorem obs_state {c d : CryptidBoundary.Cfg}
    (h : BB6.BoundaryPadding.ObsEq c d) : c.st = d.st := by
  change BB6.Padding.CfgEq
    (BB6.BoundaryPadding.represent c)
    (BB6.BoundaryPadding.represent d) at h
  exact h.2.2.2

/-- The new q=7 fourth-return endpoint and one further transition are live. -/
theorem final_next_live :
    (run (sourceElapsedFinal+1) (sourceUnary 5)).st ≠ 6 := by
  have hObs := BB6.BoundaryPadding.source_congr 1 root_source
  have hstate := obs_state hObs
  have hrun :
      run (sourceElapsedFinal+1) (sourceUnary 5) =
        run 1 (run sourceElapsedFinal (sourceUnary 5)) := by
    exact CryptidBoundary.run_add _ _ _
  rw [hrun]
  intro hbad
  have hright :
      (run 1 (DRegularSource.sourceSection s4)).st ≠ 6 := by
    simp [CryptidBoundary.run,CryptidBoundary.step,
      DRegularSource.sourceSection,CryptidBoundary.init,goL,s4]
  exact hright (hstate.symm.trans hbad)

private theorem frozen_step (c : CryptidBoundary.Cfg) (h : c.st = 6) :
    CryptidBoundary.step c = c := by
  cases c with
  | mk l bit r st =>
    change st = 6 at h
    subst st
    cases bit <;> rfl

private theorem frozen_run (c : CryptidBoundary.Cfg) (n : Nat)
    (h : c.st = 6) : CryptidBoundary.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CryptidBoundary.run n (CryptidBoundary.step c) = c
    rw [frozen_step c h]
    exact ih

theorem no_frozen_before_live_endpoint
    (c : CryptidBoundary.Cfg) (N n : Nat) (hn : n ≤ N)
    (hlive : (CryptidBoundary.run N c).st ≠ 6) :
    (CryptidBoundary.run n c).st ≠ 6 := by
  intro hst
  have ht : n + (N-n) = N := by omega
  have hrun :
      CryptidBoundary.run N c =
        CryptidBoundary.run (N-n) (CryptidBoundary.run n c) := by
    calc
      _ = CryptidBoundary.run (n+(N-n)) c :=
        congrArg (fun m => CryptidBoundary.run m c) ht.symm
      _ = _ := CryptidBoundary.run_add _ _ _
  have hfinal : (CryptidBoundary.run N c).st = 6 := by
    rw [hrun, frozen_run (CryptidBoundary.run n c) (N-n) hst]
    exact hst
  exact hlive hfinal

theorem no_frozen_through_final (n : Nat)
    (hn : n ≤ sourceElapsedFinal+1) :
    (run n (sourceUnary 5)).st ≠ 6 :=
  no_frozen_before_live_endpoint (sourceUnary 5)
    (sourceElapsedFinal+1) n hn final_next_live

/-- The literal parsed D3 blank-root machine cannot halt before the
    newly source-certified q=7 fourth-return re-entry. -/
theorem parsed_D3_no_halt_through_final (n : Nat)
    (hn : n ≤ horizonFinal) :
    ¬ BB6.Portfolio.haltsAt
      (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
      (0 : BB6.Portfolio.State) n := by
  by_cases hlt : n < 15
  · intro hh
    have hh' : BB6.Portfolio.haltsAt BB6.Portfolio.D3
        (0 : BB6.Portfolio.State) n := by
      simpa only [BB6.Portfolio.parsed_D3_eq] using hh
    have hd0 := BB6.Portfolio.D3_exact_halt_time n
    have hp := BB6.Portfolio.no_halt_before_prefix
      BB6.Portfolio.D0 (BB6.Portfolio.blank (1 : BB6.Portfolio.State))
      (BB6.Portfolio.F0Pure 5 (-3)) 15 n
      BB6.Portfolio.blank_root_B_to_I5 (hd0.mp hh')
    omega
  · have hge : 15 ≤ n := by omega
    let k := n-15
    have hk : k ≤ sourceElapsedFinal := by
      dsimp [k,horizonFinal,sourceElapsedFinal] at *
      omega
    have htime : 15+k=n := by omega
    intro hh
    have hh' : BB6.Portfolio.haltsAt
        (BB6.Portfolio.parseRLE BB6.Portfolio.rleD3)
        (0 : BB6.Portfolio.State) (15+k) := by
      simpa [htime] using hh
    have hfrozen :=
      (BB6.Agent19.Physical.parsed_D3_exact_source_time k).mp hh'
    exact (no_frozen_through_final (k+1) (by omega)) hfrozen.2

theorem horizonFinal_ge_10pow1458 : 10^1458 ≤ horizonFinal := by
  have hOld := BB6.Agent35I5Exceptional.horizon_ge_10pow1458
  have hMono :
      BB6.Agent35I5Exceptional.horizon ≤ horizonFinal := by
    dsimp [BB6.Agent35I5Exceptional.horizon,horizonFinal,
      sourceElapsedFinal,continuationCost]
    omega
  exact Nat.le_trans hOld hMono

#print axioms raw1_data
#print axioms raw2_data
#print axioms raw3_data
#print axioms raw4_data
#print axioms q7_escape_rejoin
#print axioms q5_fourth_source
#print axioms continuation_source
#print axioms root_source
#print axioms parsed_D3_no_halt_through_final
#print axioms horizonFinal_ge_10pow1458

end BB6.Agent35I5Continuation
