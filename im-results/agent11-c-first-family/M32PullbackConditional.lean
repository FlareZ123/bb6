import ReachAffine
import EvenTargetOrbit
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 2000000

namespace BB6.Agent11

/-- Source-semantic pullback of two experimentally absent B8/M32
    section cylinders. The cylinder nonreachability hypotheses are
    EXPLICIT until Agent 43's full M32 kernel is available. -/
theorem first_halt_m32_conditional
    (hA : ∀ a b : Nat, a%32=27 → b%32=28 → ¬ BB6.Agent15.CReach a b)
    (hB : ∀ a b : Nat, a%32=19 → b%32=16 → ¬ BB6.Agent15.CReach a b)
    (m k : Nat)
    (hm : m%2048=584 ∨ m%2048=1864)
    (hk : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hmpos : 584≤m := by rcases hm with h|h <;> omega
  have hpow : 2048 ∣ 2^(2*m+3) := by
    have hh : 2^11 ∣ 2^(2*m+3) := Nat.pow_dvd_pow 2 (by omega)
    simpa using hh
  have hmod : (k+3*m+4)%2048=0 := by
    rw [hk]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hkmod : k%2048=292 ∨ k%2048=548 := by
    rcases hm with h|h
    · left; omega
    · right; omega
  let u : Nat := (k-4)/32
  have hkform : k=32*u+4 := by
    dsimp [u]
    rcases hkmod with h|h <;> omega
  have hu : u%64=9 ∨ u%64=17 := by
    dsimp [u]
    rcases hkmod with h|h
    · left; omega
    · right; omega
  have huodd : u%2=1 := by rcases hu with h|h <;> omega
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
  have hcell :
      ((43*u-8)%32=27 ∧ ((21*u-5)/2)%32=28) ∨
      ((43*u-8)%32=19 ∧ ((21*u-5)/2)%32=16) := by
    rcases hu with h|h
    · left; constructor <;> omega
    · right; constructor <;> omega
  rcases hcell with hcell|hcell
  · exact hA _ _ hcell.1 hcell.2 hpre
  · exact hB _ _ hcell.1 hcell.2 hpre

#print axioms first_halt_m32_conditional
end BB6.Agent11
