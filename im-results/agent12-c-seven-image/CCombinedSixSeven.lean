import CSixthSixSeven
import CFifthSixSeven
import CFourthSixSeven
import CThirdSixSeven
import CSixSeventhStrict
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent12SevenCombined

open BB6.Agent46 BB6.Agent4Seven

/-- One-coordinate residue predicate for the currently proved strict
    sixth/seventh portion of the common target band. -/
def strictResidue26 (r : Nat) : Prop :=
  r%4=0 ∨ r%16=15 ∨ r%64=13 ∨ r%64=38 ∨
  r%32=21 ∨ r%32=25

instance (r : Nat) : Decidable (strictResidue26 r) := by
  unfold strictResidue26
  infer_instance

/-- The six separately proved sectors are exactly the residue predicate
    after the linear coordinate r=29u+v. -/
theorem strict_sector_iff_residue26 (u v : Nat) :
    ((u+v)%4=0 ∨
      (u+v)%16=(15+4*u)%16 ∨
      (29*u+v)%64=13 ∨
      (29*u+v)%64=38 ∨
      (29*u+v)%32=21 ∨
      (29*u+v)%32=25) ↔
    strictResidue26 (29*u+v) := by
  unfold strictResidue26
  constructor <;> intro h
  · rcases h with h0|h3|h13|h38|h21|h25
    · left; omega
    · right; left; omega
    · exact Or.inr (Or.inr (Or.inl h13))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h38)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h21))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h25))))
  · rcases h with h0|h3|h13|h38|h21|h25
    · left; omega
    · right; left; omega
    · exact Or.inr (Or.inr (Or.inl h13))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h38)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h21))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h25))))

/-- Consolidated strict image theorem: every target whose linear residue
    lies in the 26/64 proved set has exactly six incoming source returns
    and no seventh. -/
theorem exactly_six_not_seven_residue26 (u v : Nat)
    (h : strictResidue26 (29*u+v)) :
    Incoming 6 (641+1024*u,574+1024*v) ∧
    ¬ Incoming 7 (641+1024*u,574+1024*v) := by
  have hs := (strict_sector_iff_residue26 u v).2 h
  rcases hs with h0|h3|h13|h38|h21|h25
  · exact BB6.Agent4Seven.exactly_six_not_seven u v h0
  · exact BB6.Agent4Seven.exactly_six_not_seven_s3 u v h3
  · exact BB6.Agent12SevenSixth.exactly_six_not_seven_a12_sixth
      u v h13
  · exact BB6.Agent12Seven.exactly_six_not_seven_a12 u v h38
  · exact BB6.Agent12SevenFourth.exactly_six_not_seven_a12_fourth
      u v h21
  · exact BB6.Agent12SevenFifth.exactly_six_not_seven_a12_fifth
      u v h25

/-- A concrete finite certificate of the exact residue count: among
    0,...,63 the predicate contains 26 residues. -/
theorem strict_residue26_count :
    ((List.range 64).filter (fun r => decide (strictResidue26 r))).length = 26 := by
  decide

#print axioms strict_sector_iff_residue26
#print axioms exactly_six_not_seven_residue26
#print axioms strict_residue26_count

end BB6.Agent12SevenCombined
