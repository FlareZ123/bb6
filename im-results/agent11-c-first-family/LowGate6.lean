import EvenTargetOrbit
import M8M16Composition
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent3

/-- A new globally quantified blank-reachability exclusion using
    the full exact high-target inverse grammar and a source-certified
    8-state residue barrier. -/
theorem low_gate_six_mod_sixteen_unreachable (t : Nat)
    (ht : 1≤t) (hmod : t%16=6) :
    ¬ CReach 1 (16*t+4) := by
  intro h
  obtain ⟨r,u,hu,hindex,hparent⟩ :=
    (low_gate_all_parents_iff t ht).mp h
  have hr0 : r=0 := by
    cases r with
    | zero => rfl
    | succ n =>
      have hfac : t=8*(4^n*u) := by
        calc
          t = 2*(4^(n+1)*u) := hindex
          _ = 2*((4^n*4)*u) := by rw [Nat.pow_succ]
          _ = (2*4)*(4^n*u) := by ac_rfl
          _ = 8*(4^n*u) := by rfl
      rw [hfac] at hmod
      omega
  subst r
  have hindex2 : t=2*u := by simpa using hindex
  have hu8 : u%8=3 := by omega
  have hsub : 32*u-(11*u+3)=21*u-3 := by omega
  have hsource : CReach (22*u-3) (21*u-3) := by
    simpa [hsub] using hparent
  have ha : 22*u-3=8*((22*u-3)/8)+7 := by omega
  have hk : 21*u-3=8*((21*u-3)/8)+4 := by omega
  rw [ha,hk] at hsource
  exact BB6.Agent15.blank_no_m8_cylinder _ _ hsource

/-- A previously residual infinite congruence class in Machine C's
    first parameterized stopping family. -/
theorem first_halt_m136_mod256_unreachable (m k : Nat)
    (hm : m%256=136)
    (hk : k+3*m+4=2^(2*m+3)) : ¬ CReach 1 k := by
  have hmpos : 1≤m := by omega
  have hpow : 256 ∣ 2^(2*m+3) := by
    have hh : 2^8 ∣ 2^(2*m+3) := Nat.pow_dvd_pow 2 (by omega)
    simpa using hh
  have hmod : (k+3*m+4)%256=0 := by
    rw [hk]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hk256 : k%256=100 := by omega
  let t : Nat := (k-4)/16
  have ht : k=16*t+4 := by dsimp [t]; omega
  have htpos : 1≤t := by dsimp [t]; omega
  have htm : t%16=6 := by dsimp [t]; omega
  intro hr
  rw [ht] at hr
  exact low_gate_six_mod_sixteen_unreachable t htpos htm hr

#print axioms low_gate_six_mod_sixteen_unreachable
#print axioms first_halt_m136_mod256_unreachable
end BB6.Agent11
