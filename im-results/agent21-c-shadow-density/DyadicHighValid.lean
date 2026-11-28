import ModularCone
import Lean.Elab.Tactic.Omega

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone

/-- On every proper valuation branch, the modular cone's explicit
    HighValid gate is automatic; it is not an extra pruning predicate.
    The parity/valuation requirements exactly ensure that both signed
    inverse coordinates are integral. -/
theorem high_valid_of_valuation (s : Pair) (n : Nat)
    (hq : I (n+2) ∣ q s)
    (hpar : (n:Int)%2=(s.x+1+odd s)%2) :
    HighValid s n := by
  obtain ⟨t,ht⟩ := hq
  have hI : I (n+1)≠0 := by
    have hp := I_pos (n+1)
    omega
  have htwo : I (n+2)=I (n+1)*2 := by
    unfold I P
    rw [show n+2=(n+1)+1 by omega,Nat.pow_succ,Int.natCast_mul]
    rfl
  have hdiv : q s / I (n+1)=2*t := by
    rw [ht,htwo]
    have he : (I (n+1)*2)*t=I (n+1)*(2*t) := by ac_rfl
    rw [he]
    exact Int.mul_ediv_cancel_left (2*t) hI
  have ha : (high s n).x=2*t-2-odd s := by
    change q s/I (n+1)-2-odd s=2*t-2-odd s
    rw [hdiv]
  have heven : (w s-(high s n).x-7-3*(n:Int))%2=0 := by
    rw [ha]
    unfold w
    omega
  have hydef : (high s n).y=(w s-(high s n).x-7-3*(n:Int))/2 := by
    rfl
  constructor
  · rw [ha,ht,htwo]
    have hmass : (2*t-2-odd s)+2+odd s=2*t := by omega
    rw [hmass]
    ac_rfl
  · rw [hydef]
    omega

#print axioms high_valid_of_valuation
end BB6.Agent21Duality
