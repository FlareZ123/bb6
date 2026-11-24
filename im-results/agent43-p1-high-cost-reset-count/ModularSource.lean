import MarginSource
import CarryProjection
import P1CarryWideSource
import CertCore

namespace BB6.Agent43ModularSource
open BB6.Agent43CarryCert BB6.Agent43MarginSource BB6.Agent28CarryBudget
open BB6.Agent28BitCarry (listRun)
open BB6.P1CarryExact BB6.P1CarryExtinction
open BB6WallCarry

/-- Early modular extinction alone suffices; no independent margin budget. -/
theorem width_zero_of_modular (n r k t : Nat)
    (hn : 14 ≤ n) (hk : k+1 ≤ n)
    (hN : n=r+2^(k+1)*t) (hr : r%2=0)
    (he : listRun r 1 [((r+2)/2)] k=[]) : width (k+1) n=0 := by
  have hp := pow2_ge_1100_mul n hn
  have hz := full_empty_of_modular_certificate n r k t (by omega) hk hN hr he
  by_cases hzero : width (k+1) n=0
  · exact hzero
  · exfalso
    have hw : 0<width (k+1) n := by omega
    obtain ⟨b,d,m,hm,hcone⟩ := (source_width_iff n (k+1) hn (by omega) hk).mp hw
    have hc := oddcone_endpoint n b d m hn hcone
    rw [← states_eq] at hc
    have hsplit : m=k+1+(m-(k+1)) := by omega
    rw [hsplit,states_add,hz,empty_forever] at hc
    simp at hc

theorem critical_reset_no_reach_modular (n r k t : Nat)
    (hn : 14 ≤ n) (hk : k+1 ≤ n)
    (hN : n=r+2^(k+1)*t) (hr : r%2=0)
    (he : listRun r 1 [((r+2)/2)] k=[]) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) :=
  critical_reset_no_reach_of_empty_full n (k+1) (by omega) hn hk
    (width_zero_of_modular n r k t hn hk hN hr he)

/-- Existing verified bitset certificates now transfer at every index in
their cylinder, provided the index reaches the certificate depth. -/
theorem critical_reset_no_reach_certificate (n r k t : Nat)
    (hn : 14 ≤ n) (hk : k+1 ≤ n)
    (hN : n=r+2^(k+1)*t)
    (hc : BB6.Agent28ModScreen.checkCert (r,k)=true) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  obtain ⟨hr,he⟩ := BB6.Agent28ModScreen.checkCert_sound (r,k) hc
  exact critical_reset_no_reach_modular n r k t hn hk hN hr he

#print axioms width_zero_of_modular
#print axioms critical_reset_no_reach_certificate
end BB6.Agent43ModularSource
