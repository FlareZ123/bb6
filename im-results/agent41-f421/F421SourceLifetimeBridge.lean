import F421SecondaryLifetimes
import F421TertiaryGuard

namespace F421SecondaryLifetimes
open F421TertiaryGuard

def pProjection (cs : List Cell) : List Nat := cs.map Cell.p

/-- P projection of the original F421 all-marked drain depends only on
    physical P input; all incoming Q and merged carry parameters cancel. -/
theorem originalDrainPProjection (h carry : Nat) (cs : List Cell) :
    pProjection (drain h carry cs).1 = (sourcePDrain h (pProjection cs)).1 := by
  induction cs generalizing h carry with
  | nil => rfl
  | cons c cs ih =>
    by_cases hd : c.p≤2*h+1
    · simp only [drain,sourcePDrain,ite_eq_left hd,pProjection,List.map_cons]
      exact ih (h+(c.p+1)/2) (carry+c.q+(c.p+1)/2)
    · rcases he : drain (2*h+1) 0 cs with ⟨ys,H,r⟩
      have hp := ih (2*h+1) 0
      rw [he] at hp
      simp only [drain,sourcePDrain,ite_eq_right hd,he,pProjection,List.map_cons]
      exact congrArg (List.cons (c.p-(2*h+1))) hp

/-- Source-level projection onto normalized life, valid for arbitrary Q. -/
theorem originalDrainLifetime (B C d carry : Nat) (xs : List Nat) (cs : List Cell)
    (hB : 0<B) (he : B=C*2^d) (hp : Positive xs)
    (hcs : pProjection cs = markedPhysicalP B xs) :
    let (ys,D) := advanceAux d xs
    pProjection (drain (B-1) carry cs).1 = physicalP C ys := by
  rcases hstep : advanceAux d xs with ⟨ys,D⟩
  have hP := originalDrainPProjection (B-1) carry cs
  rw [hcs] at hP
  have hs := sourcePDrain_lifetime B C d xs hB he hp
  rw [hstep] at hs
  change sourcePDrain (B-1) (markedPhysicalP B xs) =
    (physicalP C ys,B*2^xs.length-1) at hs
  rw [hP,hs]

#print axioms originalDrainPProjection
#print axioms originalDrainLifetime

end F421SecondaryLifetimes
