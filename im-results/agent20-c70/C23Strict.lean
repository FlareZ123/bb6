import C23Integration
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20C23

/-- A right-hand side divisible by four cannot be a residue of a number
    nonzero mod four modulo a power of two of depth at least two. -/
private theorem no_pow_two_residue (a e n : Nat)
    (ha : a%4≠0) (hn : 2≤n) (he : e%4=0)
    (h : a%2^n=e) : False := by
  have hpow : 4 ∣ (2:Nat)^n := by
    change (2:Nat)^2 ∣ (2:Nat)^n
    exact Nat.pow_dvd_pow 2 hn
  have hr := Nat.mod_mod_of_dvd a hpow
  rw [h] at hr
  omega

private theorem power_linear_strict (m : Nat) :
    4*m+4 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem high_size_strict (j m : Nat) (hm : 1≤m) :
    j+3*m+17 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 1 ≤ (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hpbound := power_linear_strict m
  have ht := Nat.mul_le_mul_left 3 hpbound
  rw [Nat.mul_add]
  omega

/-- Every candidate parameter in the new dense high family satisfies
    ALL historical exact filters. Therefore this is a strict improvement
    over the strongest combined dyadic plus affine sieve, not just an
    independent reproof of previously known excluded residues. -/
theorem previous_high_admits_sum23 (j m : Nat)
    (hm : 2≤m) (hj : j%4=0)
    (hpair : (j+7)%32=(3*m)%32) :
    BB6.Agent24Phase.highAllowed j m := by
  have hm4 : m%4=1 := by omega
  have hright2 : (j+3*m+3)%4=2 := by omega
  have hright3 : (j+9*m+14)%4=3 := by omega
  have hodd : ∀ n, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,hcongr,_⟩
    apply no_pow_two_residue (j+3*m+3) (2^(n+2)) (n+4)
      (by omega) (by omega) ?_ hcongr
    have hd : 4 ∣ (2:Nat)^(n+2) := by
      change (2:Nat)^2 ∣ (2:Nat)^(n+2)
      exact Nat.pow_dvd_pow 2 (by omega)
    exact Nat.mod_eq_zero_of_dvd hd
  have hjoint : BB6.Agent3.jointHighAllowed j m := by
    unfold BB6.Agent3.jointHighAllowed
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j m := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hjoint,by omega⟩
  have h19 : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    refine ⟨hrect,hodd,?_,?_,?_,?_⟩ <;> omega
  have h29 : BB6.Agent29Joint.highAllowedPlus j m := by
    unfold BB6.Agent29Joint.highAllowedPlus
    refine ⟨h19,?_,?_,?_,?_⟩ <;> omega
  have hval : BB6.Agent3ValSix.highAllowedValSixThree j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    refine ⟨⟨h29,?_,?_⟩,?_⟩ <;> omega
  have h11 : BB6.Agent11Joint.highAllowed j m := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by omega,by omega⟩
  have hfive : BB6.Agent19Five.highAllowed j m := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  have hstop : k+j+3*m+5=2^(2*m+2)*(j+3) := by
    dsimp [k]
    have hbound := high_size_strict j m (by omega)
    have hc := Nat.sub_add_cancel (by omega :
      j+3*m+5 ≤ 2^(2*m+2)*(j+3))
    omega
  have hk12 : 12≤k := by
    have hb := high_size_strict j m (by omega)
    omega
  have hdiv8 : 8 ∣ (2:Nat)^(2*m+2) := by
    change (2:Nat)^3 ∣ (2:Nat)^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨w,hw⟩ := hdiv8
  have hprod : 8 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    refine ⟨w*(j+3),?_⟩
    rw [hw]
    ac_rfl
  have hmod : (k+j+3*m+5)%8=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod
  have hk4 : k%8=4 := by omega
  have hx3 : (2*j+3)%4=3 := by omega
  have hnorm : BB6.Agent15.affineNormalize (2*j+3) k=(2*j+3,k) := by
    have hg : ¬(4≤k ∧ k%2=0 ∧ ((2*j+3)+k)%4=1) := by omega
    simp [BB6.Agent15.affineNormalize,hg]
  have hright : (BB6.Agent15.affineNormalize (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5))).2 ≠ 4 := by
    simpa only [show (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=k from rfl, hnorm] using
      (show k≠4 by omega)
  have hfull : BB6.Agent3ValSix.highAllowedValSixFull j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    refine ⟨hval,hfive,?_,?_,?_,hright⟩ <;> omega
  have hc58 : BB6.Agent11C58ValSix.highAllowed j m := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hfull,by omega⟩
  have hdepth : ∀ r : Nat, ¬(2≤r ∧ 3≤m ∧ r+4≤2*m+2 ∧
      m%4=(2*r+3)%4 ∧
      (j+9*m+14)%2^(r+4)=3*2^(r+2)) := by
    intro r
    rintro ⟨_,_,_,_,hr⟩
    apply no_pow_two_residue (j+9*m+14) (3*2^(r+2)) (r+4)
      (by omega) (by omega) ?_ hr
    have hpow : 4 ∣ (2:Nat)^(r+2) := by
      change (2:Nat)^2 ∣ (2:Nat)^(r+2)
      exact Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨w,hw⟩ := hpow
    have hd : 4 ∣ 3*2^(r+2) := by
      refine ⟨3*w,?_⟩
      rw [hw]
      omega
    exact Nat.mod_eq_zero_of_dvd hd
  have hall : BB6.Agent11C58AllDepth.highAllowed j m := by
    unfold BB6.Agent11C58AllDepth.highAllowed
    exact ⟨hc58,hdepth⟩
  have hphase : ¬BB6.Agent46.allPhaseExcluded j m := by
    rintro ⟨r,_,_,hr⟩
    rcases hr with ⟨_,ht⟩ | ⟨_,ht⟩
    · apply no_pow_two_residue (j+3*m+3) (9*2^r) (r+4)
        (by omega) (by omega) ?_ ht
      have hp : 4 ∣ (2:Nat)^r := by
        change (2:Nat)^2 ∣ (2:Nat)^r
        exact Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨w,hw⟩ := hp
      have hdiv : 4 ∣ 9*2^r := by
        refine ⟨9*w,?_⟩
        rw [hw]
        omega
      exact Nat.mod_eq_zero_of_dvd hdiv
    · apply no_pow_two_residue (j+3*m+3) (13*2^r) (r+4)
        (by omega) (by omega) ?_ ht
      have hp : 4 ∣ (2:Nat)^r := by
        change (2:Nat)^2 ∣ (2:Nat)^r
        exact Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨w,hw⟩ := hp
      have hdiv : 4 ∣ 13*2^r := by
        refine ⟨13*w,?_⟩
        rw [hw]
        omega
      exact Nat.mod_eq_zero_of_dvd hdiv
  unfold BB6.Agent24Phase.highAllowed
  exact ⟨hall,hphase⟩

/-- This strong 1-in-128 family lies in the previous source-high residual
    for every parameter, yet fails the new C23 high predicate. -/
theorem genuinely_new_high_sum23 (j m : Nat)
    (hm : 2≤m) (hj : j%4=0)
    (hpair : (j+7)%32=(3*m)%32) :
    BB6.Agent24Phase.highAllowed j m ∧ ¬highAllowedC23 j m := by
  refine ⟨previous_high_admits_sum23 j m hm hj hpair,?_⟩
  intro h
  exact h.2 ⟨hm,hj,hpair⟩

#print axioms previous_high_admits_sum23
#print axioms genuinely_new_high_sum23
end BB6.Agent20C23
