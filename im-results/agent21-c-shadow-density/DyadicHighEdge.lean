import DyadicDirectEdge
import DyadicHighValid

namespace BB6.Agent21Dyadic

/-- Exact high inverse branch for arbitrary signed cone representatives.
    The high branch's integrality is forced by the valuation/parity guards:
    no nonnegativity hypotheses and no source-machine reachability axiom
    are needed. -/
theorem signed_high_edge
    (s : BB6.Agent42ModularCone.Pair) (n : Nat)
    (hq : BB6.Agent42ModularCone.I (n+2) ∣ BB6.Agent42ModularCone.q s)
    (hpar : (n:Int)%2=
      (s.x+1+BB6.Agent42ModularCone.odd s)%2) :
    signedS (BB6.Agent42ModularCone.high s n).x
        (BB6.Agent42ModularCone.high s n).y =
      signedS s.x s.y+shift (n+2) ∧
    P (n+2)*signedZ (BB6.Agent42ModularCone.high s n).x
        (BB6.Agent42ModularCone.high s n).y =
      signedZ s.x s.y+offset (signedS s.x s.y) (n+2) := by
  have hv := BB6.Agent21Duality.high_valid_of_valuation s n hq hpar
  have hs : signedS (BB6.Agent42ModularCone.high s n).x
          (BB6.Agent42ModularCone.high s n).y =
        signedS s.x s.y+shift (n+2) := by
    have hw := hv.2
    unfold signedS shift BB6.Agent42ModularCone.w at *
    omega
  have hc : ((n+2:Nat):Int)%2=(s.y+1)%2 := by
    unfold BB6.Agent42ModularCone.odd at hpar
    push_cast
    omega
  have hfirst : signedZ s.x s.y+offset (signedS s.x s.y) (n+2) =
      -(BB6.Agent42ModularCone.q s) := by
    rw [signed_one_numer,signed_parity_cost s.x s.y (n+2) hc]
    simp only [BB6.Agent42ModularCone.q,BB6.Agent42ModularCone.odd]
    omega
  have hchildpar : parity (signedS (BB6.Agent42ModularCone.high s n).x
          (BB6.Agent42ModularCone.high s n).y) =
      BB6.Agent42ModularCone.odd s := by
    rw [hs]
    simpa [BB6.Agent42ModularCone.odd] using
      signed_parity_cost s.x s.y (n+2) hc
  have hz := signed_twice_Z
    (BB6.Agent42ModularCone.high s n).x
    (BB6.Agent42ModularCone.high s n).y
  rw [hchildpar] at hz
  have hI : BB6.Agent42ModularCone.I (n+1)=P (n+1) := by
    simp [BB6.Agent42ModularCone.I,BB6.Agent42ModularCone.P,P]
  have hq' : BB6.Agent42ModularCone.q s =
      P (n+1)*((BB6.Agent42ModularCone.high s n).x+
        2+BB6.Agent42ModularCone.odd s) := by
    simpa only [hI] using hv.1
  have hpow : P (n+2)=P (n+1)*2 := by
    rw [show n+2=n+1+1 by omega,P_add]
    change P (n+1)*2=P (n+1)*2
    rfl
  have he : P (n+2)*signedZ
      (BB6.Agent42ModularCone.high s n).x
      (BB6.Agent42ModularCone.high s n).y =
      -(BB6.Agent42ModularCone.q s) := by
    rw [hpow]
    rw [show (P (n+1)*2)*
        signedZ (BB6.Agent42ModularCone.high s n).x
          (BB6.Agent42ModularCone.high s n).y =
      P (n+1)*(2*signedZ
        (BB6.Agent42ModularCone.high s n).x
        (BB6.Agent42ModularCone.high s n).y) by ac_rfl]
    rw [hz,hq']
    have hneg : -(BB6.Agent42ModularCone.high s n).x-
        2-BB6.Agent42ModularCone.odd s =
      -((BB6.Agent42ModularCone.high s n).x+
        2+BB6.Agent42ModularCone.odd s) := by omega
    rw [hneg,Int.mul_neg]
  exact ⟨hs,he.trans hfirst.symm⟩

#print axioms signed_high_edge
end BB6.Agent21Dyadic
