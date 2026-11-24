import SpaceNeedleClosed
import TerminalAffineRotation

namespace BB6.Agent20.SpaceNeedleTerminalAffine
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open NeedleRotation.TerminalAffine

/-- Every exact original-source transition supplies the arithmetic inverse
parameter, with the actual predecessor valuation and positive odd part. -/
theorem source_parent_eq (p t : Nat)
    (hs : highLevelNext (.N p) = some (.N t)) :
    ∃ q w, p=oddTower q w ∧
      p+2=2^w*(2*q+3) ∧ NeedleRotation.Cancellation.parentEq (t+2) q w := by
  rcases (highLevelNext_iff_oddTower p t).mp hs with ⟨q,w,hp,ht⟩
  have hf := oddTower_factor q w
  rw [←hp] at hf
  refine ⟨q,w,hp,hf,?_⟩
  unfold NeedleRotation.Cancellation.parentEq
  rw [Nat.pow_succ,Nat.add_mul]
  rw [Nat.mul_add] at hf
  grind

/-- The all-depth affine invariant is preserved by the exact original
Space Needle reduction, and bounds every predecessor valuation. -/
theorem source_terminal_affine_parent (n L p t : Nat) (d : Int)
    (hf : TerminalForm n L (t+2) d)
    (hs : highLevelNext (.N p) = some (.N t)) :
    ∃ q w, p=oddTower q w ∧
      NeedleRotation.Cancellation.parentEq (t+2) q w ∧
      TerminalForm (n+w+1) (L*(2^(w+1)+3)) (p+2)
        ((2:Int)^(w+1)*(d+(L:Int)*(5-2*((w+1:Nat):Int)))) := by
  rcases source_parent_eq p t hs with ⟨q,w,hp,hfactor,hpar⟩
  exact ⟨q,w,hp,hpar,terminalForm_parent n L (t+2) (p+2) q w d hf hpar hfactor⟩

/-- Source-integrated bound for the first-level cancellation feeder. -/
theorem source_first_cancellation_cutoff (r P p t : Nat) (hr : 8≤r)
    (hP : (2^(NeedleRotation.Cancellation.a r)+3)*P+NeedleRotation.Cancellation.N r=(2^(NeedleRotation.Cancellation.a r))^(2*r))
    (hb : 2*(t+2)=2^(NeedleRotation.Cancellation.a r)*P)
    (hs : highLevelNext (.N p) = some (.N t)) :
    ∃ q w, p=oddTower q w ∧ (w+1)*(w+1)<16*r*NeedleRotation.Cancellation.a r := by
  rcases source_parent_eq p t hs with ⟨q,w,hp,_,hpar⟩
  exact ⟨q,w,hp,NeedleRotation.Cancellation.first_source_equation_cutoff r P (t+2) q w hr hP hb hpar⟩

/-- Source-integrated bound for the second-level progression. -/
theorem source_second_cancellation_cutoff (j P p t : Nat)
    (hP : (2^(NeedleRotation.Cancellation.a (110*j+50))+3)*P+NeedleRotation.Cancellation.N (110*j+50)=(2^(NeedleRotation.Cancellation.a (110*j+50)))^(2*(110*j+50)))
    (hb : 55*(t+2)=8*2^(NeedleRotation.Cancellation.a (110*j+50))*P+25)
    (hs : highLevelNext (.N p) = some (.N t)) :
    ∃ q w, p=oddTower q w ∧ (w+1)*(w+1)<16*(110*j+50)*NeedleRotation.Cancellation.a (110*j+50) := by
  rcases source_parent_eq p t hs with ⟨q,w,hp,_,hpar⟩
  exact ⟨q,w,hp,NeedleRotation.Cancellation.second_source_equation_cutoff j P (t+2) q w hP hb hpar⟩

#print axioms source_parent_eq
#print axioms source_terminal_affine_parent
#print axioms source_first_cancellation_cutoff
#print axioms source_second_cancellation_cutoff
end BB6.Agent20.SpaceNeedleTerminalAffine
