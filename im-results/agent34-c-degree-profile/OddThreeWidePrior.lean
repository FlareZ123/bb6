import OddThreeWideJoint
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34OddWidePrior
open BB6.Agent3ValSix

private theorem old_high_score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

private theorem mod128_to16 (z : Nat) : (z%128)%16=z%16 :=
  Nat.mod_mod_of_dvd z (by decide)

/-- Every member of the new entire infinite high-stopping parameter lattice
passes the historical exact `highAllowedValSixFull` sieve. In particular,
the added m=3 mod8 branch was not excluded by that prior filter. -/
theorem old_full_admits (j m : Nat)
    (hm : m%4=3) (hj : j%128=(15*m+2)%128) :
    highAllowedValSixFull j m := by
  have hmod := congrArg (fun z : Nat => z%16) hj
  rw [mod128_to16,mod128_to16] at hmod
  have hj4 : j%4=3 := by omega
  have hsum16 : (j+m)%16=2 := by omega
  have hx8 : (2*j+3)%8=1 := by omega
  have hjoint : BB6.Agent3.jointHighRectAllowed j m := by
    unfold BB6.Agent3.jointHighRectAllowed
    constructor
    · unfold BB6.Agent3.jointHighAllowed
      refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
    · omega
  have hdy : ∀ n, ¬
      (n+4≤2*m+2 ∧ (j+3*m+3)%2^(n+4)=2^(n+2) ∧
       (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,_,hres⟩
    by_cases hn : n%2=0
    · simp [hn] at hres
      omega
    · simp [hn] at hres
      omega
  have h19 : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    exact ⟨hjoint,hdy,by omega,by omega,by omega,by omega⟩
  have hplus : BB6.Agent29Joint.highAllowedPlus j m := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hval : highAllowedValSixThree j m := by
    unfold highAllowedValSixThree highAllowedValSix
    exact ⟨⟨hplus,by omega,by omega⟩,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j m := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by omega,by omega⟩
  have hfive : BB6.Agent19Five.highAllowed j m := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
    dsimp [k]
    have hc := Nat.sub_add_cancel
      (old_high_score_nonnegative j m)
    omega
  have hp2 : 2 ∣ (2:Nat)^(2*m+2) := by
    change (2:Nat)^1 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨p,hp⟩ := hp2
  have hmod2 : (2^(2*m+2)*(j+3))%2=0 := by
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨p*(j+3),?_⟩
    rw [hp]
    ac_rfl
  have hkodd : k%2=1 := by omega
  have hgate : ¬(4≤k ∧ k%2=0 ∧ (2*j+3+k)%4=1) := by omega
  have hnormal : BB6.Agent15.affineNormalize (2*j+3) k = (2*j+3,k) := by
    simp [BB6.Agent15.affineNormalize, hgate]
  have hright : (BB6.Agent15.affineNormalize (2*j+3) k).2 ≠ 4 := by
    rw [hnormal]
    omega
  unfold highAllowedValSixFull
  exact ⟨hval,hfive,by omega,by omega,by omega,by simpa [k] using hright⟩

/-- The integrated strict image filter removes infinitely many points
from the precise historical permitted high-stopping set. -/
theorem old_admitted_new_forbidden (j m : Nat)
    (hm : m%4=3) (hj : j%128=(15*m+2)%128) :
    highAllowedValSixFull j m ∧
      ¬BB6.Agent34OddWideJoint.highAllowed j m := by
  refine ⟨old_full_admits j m hm hj,?_⟩
  intro h
  exact h.2 ⟨hm,hj⟩

#print axioms old_full_admits
#print axioms old_admitted_new_forbidden
end BB6.Agent34OddWidePrior
