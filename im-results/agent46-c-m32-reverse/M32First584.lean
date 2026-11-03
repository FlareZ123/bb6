import M32ReverseCore
import EvenTargetOrbit
import M32SectionEmbedding
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 2000000

namespace BB6A46M32

/-- A first-family Machine C stopping class excluded by an original-source
    analytic backward core, independent of the incomplete 1600-row M32 BFS
    certificate. Previous Agent11 source result was conditional. -/
theorem first_halt_m584_unreachable (m k : Nat)
    (hm : m%2048=584)
    (hk : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hmpos : 584≤m := by omega
  have hpow : 2048 ∣ 2^(2*m+3) := by
    have hh : 2^11 ∣ 2^(2*m+3) := Nat.pow_dvd_pow 2 (by omega)
    simpa using hh
  have hmod : (k+3*m+4)%2048=0 := by
    rw [hk]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hkmod : k%2048=292 := by omega
  let u : Nat := (k-4)/32
  have hkform : k=32*u+4 := by dsimp [u]; omega
  have hu : u%64=9 := by dsimp [u]; omega
  have huodd : u%2=1 := by omega
  intro hreach
  have hgate : 32*u+4=16*(2*u)+4 := by omega
  have hlow : BB6.Agent3.CReach 1 (16*(2*u)+4) := by
    rw [←hgate]
    rw [←hkform]
    exact hreach
  obtain ⟨r,v,hv,hindex,hparent⟩ :=
    (BB6.Agent3.low_gate_all_parents_iff (2*u) (by omega)).mp hlow
  have hr0 : r=0 := by
    cases r with
    | zero => rfl
    | succ n =>
        have hfac : 2*u=8*(4^n*v) := by
          calc
            2*u = 2*(4^(n+1)*v) := hindex
            _ = 2*((4^n*4)*v) := by rw [Nat.pow_succ]
            _ = (2*4)*(4^n*v) := by ac_rfl
            _ = 8*(4^n*v) := by rfl
        omega
  subst r
  have huv : u=v := by omega
  subst v
  have hsub : 32*u-(11*u+3)=21*u-3 := by omega
  have hp : BB6.Agent15.CReach (22*u-3) (21*u-3) := by
    change BB6.Agent3.CReach (22*u-3) (21*u-3)
    simpa [hsub] using hparent
  have hka : 4≤21*u-3 := by omega
  have hke : (21*u-3)%2=0 := by omega
  have hsum : ((22*u-3)+(21*u-3))%4=1 := by omega
  have hpre :=
    (BB6.Agent15.blank_reach_iff_affine (22*u-3) (21*u-3) hka hke hsum).mp hp
  have haeq : (22*u-3)+(21*u-3)-2=43*u-8 := by omega
  have hbeq : ((21*u-3)-2)/2=(21*u-5)/2 := by omega
  rw [haeq,hbeq] at hpre
  have hcell : (43*u-8)%32=27 ∧ ((21*u-5)/2)%32=28 := by
    constructor <;> omega
  have hline : BB6CLine.Reach (43*u-8,(21*u-5)/2,0) :=
    BB6.Agent15.m32_section_reach_embeds hpre
  exact (target1_unreachable _ _ hcell.1 hcell.2) hline

#print axioms first_halt_m584_unreachable
end BB6A46M32
