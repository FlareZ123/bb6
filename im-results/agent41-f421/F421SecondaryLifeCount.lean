import F421SecondaryFar
import F421SecondaryTelescoping

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

/-- Only the positional lifetime lengths, not all enormous primary state
    coordinates, contribute to aggregate Q mass. -/
def lifeLengthSum : Nat → List Nat → Nat
  | 0,_ => 0
  | k+1,xs => 2^(xs.length+2) + lifeLengthSum k (advance xs)

/-- The entire history of cell-count powers telescopes to the weighted
    mass of the final normalized lifetime list. -/
theorem lengthSumMass (k : Nat) (xs : List Nat) (hp : Positive xs) :
    lifeLengthSum k xs + 4*mass xs +4*k = 4*mass (lifeIter k xs) := by
  induction k generalizing xs with
  | zero => simp [lifeLengthSum,lifeIter]
  | succ k ih =>
    have hnext : Positive (advance xs) := advancePositive xs hp
    have h := ih (advance xs) hnext
    have hm := advance_mass xs hp
    have hpow : 2^(xs.length+2)=4*2^xs.length := by
      simp [Nat.pow_add, Nat.mul_comm]
    simp only [lifeLengthSum,lifeIter]
    rw [hm] at h
    rw [hpow]
    omega

/-- The source k-step length sum is completely represented by lifetimes. -/
theorem lengthSumProtected (k a b p0 q0 p1 q1 : Nat) (hs : List PC)
    (xs : List Nat) (h0 : 2*k+3≤p0) (h1 : 4*k+5≤p1)
    (hp : Positive xs) (hh : pProjection hs=physicalP 4 xs) :
    lengthSum k (a,b,⟨p0,q0⟩::⟨p1,q1⟩::hs) = lifeLengthSum k xs := by
  induction k generalizing a b p0 q0 p1 q1 hs xs with
  | zero => rfl
  | succ k ih =>
    have hstep := nextShapeFar b p0 q0 p1 q1 hs xs
      (by omega) (by omega) hp hh
    obtain ⟨a1,b1,hs1,he,hshape⟩ := hstep
    have hLen : hs.length=xs.length := by
      have h := congrArg List.length hh
      simpa [pProjection,physicalPLength] using h
    have hpos:=advancePositive xs hp
    have hinner := ih a1 b1 (p0-2) q0 (p1-4) q1 hs1 (advance xs)
      (by omega) (by omega) hpos hshape
    simp only [lengthSum,lifeLengthSum,List.length_cons]
    rw [he]
    have hpow : 2^(hs.length+2)=2^(xs.length+2) := by rw [hLen]
    rw [hpow]
    exact congrArg (fun t : Nat => 2^(xs.length+2)+t) hinner

theorem firstLengthSum :
    lengthSum 32750 (2047,3071,firstPrimary) =
      lifeLengthSum 32750 firstLives := by
  have h := lengthSumProtected 32750 2047 3071 2883545 131073 7077811 2883586
    firstHead firstLives (by decide) (by decide)
    (by simp [Positive,firstLives]) initialHeadEncoding
  have he : firstPrimary=⟨2883545,131073⟩::⟨7077811,2883586⟩::firstHead := rfl
  rw [←he] at h
  exact h

#print axioms lengthSumMass
#print axioms lengthSumProtected
#print axioms firstLengthSum
end F421SecondaryLifetimes
