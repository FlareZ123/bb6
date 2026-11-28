import F421SecondaryProtected

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

def pSum (cs : List PC) : Nat := (cs.map Cell.p).sum

theorem physicalPSum (B : Nat) (xs : List Nat) :
    (physicalP B xs).sum = 2*B*mass xs := by
  induction xs generalizing B with
  | nil => simp [physicalP,mass]
  | cons x xs ih =>
    simp only [physicalP,List.sum_cons,mass]
    rw [ih (2*B)]
    rw [Nat.mul_add]
    ac_rfl

theorem pSumCons (c : PC) (cs : List PC) : pSum (c::cs)=c.p+pSum cs := by
  rfl

/-- For the protected far two rows, the exact total P mass grows by the
    original leading P-run plus three, independently of all Q data. -/
theorem secondaryPsumGrowth (b p0 q0 p1 q1 : Nat) (hs : List PC) (xs : List Nat)
    (h0 : 3≤p0) (h1 : 5≤p1) (hp : Positive xs)
    (hh : pProjection hs=physicalP 4 xs) :
    pSum (sNext b (⟨p0,q0⟩::⟨p1,q1⟩::hs)).2.2 =
      pSum (⟨p0,q0⟩::⟨p1,q1⟩::hs) + (8*2^xs.length-1)+3 := by
  obtain ⟨a',b',rest,he,hr⟩ := nextShapeFar b p0 q0 p1 q1 hs xs h0 h1 hp hh
  have hh' : pSum hs = (physicalP 4 xs).sum := by
    simpa [pSum,pProjection] using congrArg List.sum hh
  have hr' : pSum rest=(physicalP 4 (advance xs)).sum := by
    simpa [pSum,pProjection] using congrArg List.sum hr
  have hmass:=advance_mass xs hp
  have hs0:=physicalPSum 4 xs
  have hs1:=physicalPSum 4 (advance xs)
  have heq : p0-2+(p1-4)+8*(mass xs+2^xs.length+1)=
      (p0+p1+8*mass xs)+(8*2^xs.length-1)+3 := by
    have p0' : p0-2+2=p0 := by omega
    have p1' : p1-4+4=p1 := by omega
    have powpos : 0<8*2^xs.length := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    omega
  simp only [he,Prod.fst,Prod.snd,pSumCons]
  rw [hh',hr',hs0,hs1,hmass]
  simp only [show 2*4=8 by decide,Nat.mul_add]
  omega

#print axioms physicalPSum
#print axioms secondaryPsumGrowth
end F421SecondaryLifetimes
