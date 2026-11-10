import OddThreeComplementJoint
import Lean.Elab.Tactic.Omega

/-! Universal, source-adjacent non-subsumption theorem for the second
complementary high-stopping lattice and the historical integrated high sieve. -/
namespace BB6.Agent34OddComplementPrior
open BB6.Agent3ValSix

private theorem high_score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ 2^(2*m+2)*(j+3) := by
  have hm : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ 2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  rw [Nat.mul_add]
  omega

private theorem dyadic_condition_false (j m : Nat)
    (hm : m%4=0) (hj : j%64=(15*m+62)%64)
    (n : Nat)
    (hres : (j+3*m+3)%2^(n+4)=2^(n+2)) : False := by
  have hmod4 : (j+3*m+3)%4=1 := by omega
  have hp4 : 4 ∣ (2:Nat)^(n+4) := by
    change (2:Nat)^2 ∣ 2^(n+4)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hinner := congrArg (fun a : Nat => a%4) hres
  rw [Nat.mod_mod_of_dvd _ hp4] at hinner
  have hp24 : 4 ∣ (2:Nat)^(n+2) := by
    change (2:Nat)^2 ∣ 2^(n+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpow4 : (2:Nat)^(n+2)%4=0 := Nat.mod_eq_zero_of_dvd hp24
  omega

/-- Every member of the new original-source complementary high stopping
parameter class survives *all* historical `highAllowedValSixFull` clauses. -/
theorem old_full_admits (j m : Nat)
    (hm4 : 4≤m) (hm : m%4=0) (hj3 : 3≤j)
    (hj : j%64=(15*m+62)%64) :
    highAllowedValSixFull j m := by
  have hj4 : j%4=2 := by omega
  have hsum32 : (j+m)%32=30 := by omega
  have hsum16 : (j+m)%16=14 := by omega
  have hx8 : (2*j+3)%8=7 := by omega
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
    rintro ⟨_,hres,_⟩
    exact dyadic_condition_false j m hm hj n hres
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
    have hc := Nat.sub_add_cancel (high_score_nonnegative j m)
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

/-- This complement strictly removes an entire infinite lattice that the
previous exact `ValSixJointFull` source criterion admitted. -/
theorem old_admitted_new_forbidden (j m : Nat)
    (hm4 : 4≤m) (hm : m%4=0) (hj3 : 3≤j)
    (hj : j%64=(15*m+62)%64) :
    highAllowedValSixFull j m ∧
      ¬BB6.Agent34OddComplementJoint.highAllowed j m := by
  refine ⟨old_full_admits j m hm4 hm hj3 hj,?_⟩
  intro h
  exact h.2 ⟨hm4,hm,hj3,hj⟩

#print axioms old_full_admits
#print axioms old_admitted_new_forbidden
end BB6.Agent34OddComplementPrior
