import LagBound
import MarginSource
namespace BB6.Agent45.DelayedCarry
open BB6.Agent1Quarter BB6.Agent47P1 BB6.P1Reduction
open BB6.P1CarryExact (criticalLeft source_to_micro pow2_ge_1100_mul)
open BB6.Agent43MarginSource (GateConditions cone_no_reach_of_conditions)

theorem conditions_of_lag (n K s : Nat) (hn : 14≤n) (heven : n%2=0)
    (hs : 1≤s) (hK : K=n+s) (hA : n+K+2≤2^n)
    (hgap : (n+K+2)*marginSize n K<6*2^n) (hcert : Cert n K s []) :
    GateConditions n K := by
  intro b d m h
  have hM := source_to_micro n b d m hn h
  obtain ⟨hcost,hv,hw⟩ := cert_micro_bounds n K s hn heven hs hK hA hgap hcert _ _ _ hM
  refine ⟨hcost,?_,?_⟩
  · intro hf
    subst d
    have hm : 0<m := by
      cases h with
      | parent _ _ _ _ _ _ _ _ _ _ _ _ _ => omega
    have hV := hv hm
    unfold marginSize at hV
    omega
  · unfold marginSize at hw
    omega

theorem critical_reset_no_reach_of_lag (n K s : Nat) (hn : 14≤n) (heven : n%2=0)
    (hs : 1≤s) (hK : K=n+s) (hA : n+K+2≤2^n)
    (hgap : (n+K+2)*marginSize n K<6*2^n) (hcert : Cert n K s []) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro h
  have hp := pow2_ge_1100_mul n hn
  have he : (2:Nat)^n%2=0 := by
    apply Nat.dvd_iff_mod_eq_zero.mp
    have hd := Nat.pow_dvd_pow 2 (show 1≤n by omega)
    simpa using hd
  let d := 14*2^n-2*n-10
  have hd : 10≤d := by dsimp [d]; omega
  have hmod : d%4=2 := by dsimp [d]; omega
  have hreach := BB6.Agent50P1.critical_target_implies_three d hd hmod h
  have heq : d-6=criticalLeft n := by dsimp [d,criticalLeft]; omega
  rw [heq] at hreach
  exact cone_no_reach_of_conditions n K K hn
    (conditions_of_lag n K s hn heven hs hK hA hgap hcert) _ _ 0 (by omega) OddCone.root hreach

#print axioms critical_reset_no_reach_of_lag
end BB6.Agent45.DelayedCarry
