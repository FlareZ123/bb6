import Anti5Full
import ReturnScaled
set_option maxHeartbeats 0
namespace BB6.Agent9Anti5
open BB6.Agent9ReturnGCD

/-- Remove the power-of-two factor of the slope before applying the
    antiperiod-two determinant at odd slope five. -/
theorem no_scaled_five (q dir C g : Int) (L A r B : Nat)
    (a c w x : Nat→Int)
    (hdir : dir=1∨dir= -1)
    (hg : g=(2:Int)^r*5) (hL : A+r+2*B+2≤L)
    (hinit : -(2:Int)^(A+r)<a 0 ∧ a 0<g+(2:Int)^(A+r))
    (hx : ∀ j<L, x j=0∨x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : 5*(C+3)<(2:Int)^(2*B)) : False := by
  obtain ⟨b,_,hb,hinit'⟩ := scale_slope g 5 L r A a x hg ha (by omega) hinit
  apply no_small_five_slope q dir C A B (L-r) b c w x hdir (by omega)
    hinit' (fun j hj => hx j (by omega))
    (fun j hj => hb j (by omega))
    (fun j hj => hc j (by omega))
    (fun j hj => hw j (by omega))
    (fun j hj => hbound j (by omega)) hscale

#print axioms no_scaled_five
end BB6.Agent9Anti5
