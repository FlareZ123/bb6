import Anti3Full
import ReturnScaled
set_option maxHeartbeats 0
namespace BB6.Agent9Anti3
open BB6.Agent9ReturnGCD

/-- A dyadic multiple of the three-cycle induces an impossible
    affine-clock repeated word after its logarithmic transient. -/
theorem no_scaled_three (q dir C g : Int) (L A r B : Nat)
    (a c w x : Nat→Int)
    (hdir : dir=1∨dir= -1)
    (hg : g=(2:Int)^r*3) (hL : A+r+B+1≤L)
    (hinit : -(2:Int)^(A+r)<a 0 ∧ a 0<g+(2:Int)^(A+r))
    (hx : ∀ j<L, x j=0∨x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : 3*(C+1)<(2:Int)^B) : False := by
  obtain ⟨b,_,hb,hinit'⟩ := scale_slope g 3 L r A a x hg ha (by omega) hinit
  apply no_small_three_slope q dir C A B (L-r) b c w x hdir (by omega)
    hinit' (fun j hj => hx j (by omega))
    (fun j hj => hb j (by omega))
    (fun j hj => hc j (by omega))
    (fun j hj => hw j (by omega))
    (fun j hj => hbound j (by omega)) hscale

#print axioms no_scaled_three
end BB6.Agent9Anti3
