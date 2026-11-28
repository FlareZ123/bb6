import F421SecondaryLifeMass
import F421SecondaryTelescopingGuard

namespace BB6Coverage.Agent41F421.EpochWords
open F421SecondaryLifetimes

theorem sPGoodWeak (k j B : Nat) (cs : List PC)
    (hk : k≤j) (hg : sPGood j B cs) : sPGood k B cs := by
  induction cs generalizing B with
  | nil => trivial
  | cons c cs ih =>
    rcases hg with ⟨h,ht⟩
    refine ⟨?_,ih (2*B) ht⟩
    rcases h with h|h
    · left
      have hb : 2*B*k≤2*B*j := Nat.mul_le_mul_left (2*B) hk
      omega
    · exact Or.inr h

theorem sPrimaryWeak (k j a b : Nat) (cs : List PC)
    (hk : k≤j) (hp : sPrimary j a b cs) : sPrimary k a b cs := by
  rcases hp with ⟨ha,hb,hp,hq,hlen⟩
  exact ⟨ha,hb,sPGoodWeak k j 1 cs hk hp,hq,hlen⟩

/-- General source-level potential invariant for an arbitrary protected
    two-cell prefix, any positive normalized lifetime suffix, and any
    guarded finite secondary countdown. No Q-run values are evaluated. -/
theorem secondaryPotentialProtected (k a b p0 q0 p1 q1 : Nat)
    (hs : List PC) (xs : List Nat)
    (hg : sPrimary k a b (⟨p0,q0⟩::⟨p1,q1⟩::hs))
    (h0 : 2*k+3≤p0) (h1 : 4*k+5≤p1)
    (hp : Positive xs) (hh : pProjection hs=physicalP 4 xs) :
    let e := sIter k (a,b,⟨p0,q0⟩::⟨p1,q1⟩::hs)
    prefixMass e.1 e.2.1 e.2.2+
      4*2^((⟨p0,q0⟩::⟨p1,q1⟩::hs).length)+24*mass xs+23*k =
      prefixMass a b (⟨p0,q0⟩::⟨p1,q1⟩::hs)+
        4*2^e.2.2.length+24*mass (lifeIter k xs) := by
  have htel := secondaryMassTelescoping k a b
    (⟨p0,q0⟩::⟨p1,q1⟩::hs) hg
  have hsum := lengthSumProtected k a b p0 q0 p1 q1 hs xs h0 h1 hp hh
  have hm := lengthSumMass k xs hp
  rcases he : sIter k (a,b,⟨p0,q0⟩::⟨p1,q1⟩::hs) with ⟨a',b',ds⟩
  rw [he] at htel
  simp only [Prod.fst,Prod.snd] at htel
  rw [hsum] at htel
  simp only [he,Prod.fst,Prod.snd]
  omega

/-- A machine-level scalar invariant at EVERY one of the 32,751
    original blank-linked secondary primary states, including deletions:
      prefixMass_k - 4*2^cellcount_k -24*weightedLifetimeMass_k +23*k
      = 14,024,306.
    This equality is rendered without subtraction so all intermediate terms
    are well-defined in Nat. -/
theorem firstSecondaryPotential (k : Nat) (hk : k≤32750) :
    let e := sIter k (2047,3071,firstPrimary)
    prefixMass e.1 e.2.1 e.2.2 +23*k =
      14024306+4*2^e.2.2.length+
        24*mass (lifeIter k firstLives) := by
  have hp := sPrimaryWeak k 32750 2047 3071 firstPrimary hk firstPrimaryGood
  have htel := secondaryMassTelescoping k 2047 3071 firstPrimary hp
  have hsum := lengthSumProtected k 2047 3071
    2883545 131073 7077811 2883586 firstHead firstLives
      (by omega) (by omega) (by simp [Positive,firstLives]) initialHeadEncoding
  have hm := lengthSumMass k firstLives (by simp [Positive,firstLives])
  have hseed : mass firstLives=328977 := by decide
  have hinit : prefixMass 2047 3071 firstPrimary=21923850 := by decide
  have hpow : 2^firstPrimary.length=1024 := by decide
  rcases he : sIter k (2047,3071,firstPrimary) with ⟨a',b',ds⟩
  rw [he] at htel
  simp only [Prod.fst,Prod.snd] at htel
  rw [hsum,hinit,hpow] at htel
  rw [hseed] at hm
  simp only [he,Prod.fst,Prod.snd]
  omega

#print axioms sPGoodWeak
#print axioms sPrimaryWeak
#print axioms firstSecondaryPotential
#print axioms secondaryPotentialProtected
end BB6Coverage.Agent41F421.EpochWords
