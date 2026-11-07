import C70Integration
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20C70

private theorem power_linear_own (m : Nat) :
    4*m+4 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [he, Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem high_size_own (j m : Nat) :
    j+3*m+12 ≤ 2^(2*m+2)*(j+3) := by
  have hp : 1 ≤ (2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hm : 4*m+4 ≤ 2^(2*m+2) := power_linear_own m
  have ht := Nat.mul_le_mul_left 3 hm
  rw [Nat.mul_add]
  omega

/-- The two high stopping families survived all earlier joint source filters,
    including both unbounded depth-indexed exclusions and the general
    affine-right-four gate. The new rectangle therefore removes infinite
    classes genuinely not cut by the previous strongest integrated sieve. -/
theorem previous_high_admits_rectangle (j m : Nat)
    (hres : (j%128=63 ∧ m%128=82) ∨
      (j%128=127 ∧ m%128=18)) :
    BB6.Agent24Phase.highAllowed j m := by
  have hj7 : j%8=7 := by rcases hres with ⟨h,_⟩|⟨h,_⟩ <;> omega
  have hj15 : j%16=15 := by rcases hres with ⟨h,_⟩|⟨h,_⟩ <;> omega
  have hm2 : m%4=2 := by rcases hres with ⟨_,h⟩|⟨_,h⟩ <;> omega
  have hm32 : m%32=18 := by rcases hres with ⟨_,h⟩|⟨_,h⟩ <;> omega
  have hj32 : j%32=31 := by rcases hres with ⟨h,_⟩|⟨h,_⟩ <;> omega
  have hodd : ∀ n, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,_,hr⟩
    have hx : (2*j+3)%8=1 := by omega
    by_cases hn : n%2=0
    · simp [hn] at hr
      omega
    · simp [hn] at hr
      omega
  have hjoint : BB6.Agent3.jointHighAllowed j m := by
    unfold BB6.Agent3.jointHighAllowed
    refine ⟨?_,?_,?_,?_,?_⟩ <;> rcases hres with ⟨hj,hm⟩ | ⟨hj,hm⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j m := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hjoint,by omega⟩
  have h19 : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    refine ⟨hrect,hodd,?_,?_,?_,?_⟩ <;> rcases hres with ⟨hj,hm⟩ | ⟨hj,hm⟩ <;> omega
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
    have hc := Nat.sub_add_cancel (by have hb := high_size_own j m; omega :
        j+3*m+5 ≤ 2^(2*m+2)*(j+3))
    omega
  have hk7 : 7 ≤ k := by
    have hs := high_size_own j m
    omega
  have hpow4 : 4 ∣ (2:Nat)^(2*m+2) := by
    have hh : (2:Nat)^2 ∣ (2:Nat)^(2*m+2) := Nat.pow_dvd_pow 2 (by omega)
    simpa using hh
  have hprod : 4 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    rcases hpow4 with ⟨w,hw⟩
    refine ⟨w*(j+3),?_⟩
    rw [hw]
    ac_rfl
  have hstop4 : (k+j+3*m+5)%4=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod
  have hk2 : k%4=2 := by omega
  have hx1 : (2*j+3)%4=1 := by omega
  have hnorm : BB6.Agent15.affineNormalize (2*j+3) k=(2*j+3,k) := by
    have hg : ¬(4≤k ∧ k%2=0 ∧ ((2*j+3)+k)%4=1) := by omega
    simp [BB6.Agent15.affineNormalize,hg]
  have hright : (BB6.Agent15.affineNormalize (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5))).2 ≠ 4 := by
    simpa only [show (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=k from rfl, hnorm] using
      (show k≠4 by omega)
  have hfull : BB6.Agent3ValSix.highAllowedValSixFull j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    refine ⟨hval,hfive,?_,?_,?_,hright⟩ <;> rcases hres with ⟨hj,hm⟩ | ⟨hj,hm⟩ <;> omega
  have hc58 : BB6.Agent11C58ValSix.highAllowed j m := by
    unfold BB6.Agent11C58ValSix.highAllowed
    refine ⟨hfull,?_⟩
    rcases hres with ⟨hj,hm⟩ | ⟨hj,hm⟩ <;> omega
  have hdepth : ∀ r : Nat, ¬(2≤r ∧ 3≤m ∧ r+4≤2*m+2 ∧
      m%4=(2*r+3)%4 ∧
      (j+9*m+14)%2^(r+4)=3*2^(r+2)) := by
    intro r
    rintro ⟨_,_,_,hfour,_⟩
    omega
  have hall : BB6.Agent11C58AllDepth.highAllowed j m := by
    unfold BB6.Agent11C58AllDepth.highAllowed
    exact ⟨hc58,hdepth⟩
  have hphase : ¬ BB6.Agent46.allPhaseExcluded j m := by
    rintro ⟨r,_,_,hbranch⟩
    rcases hbranch with ⟨hmatch,_⟩ | ⟨hmatch,_⟩ <;> omega
  unfold BB6.Agent24Phase.highAllowed
  exact ⟨hall,hphase⟩

/-- Each of the two classes lies fully inside the previous necessary high
    filter, while the new all-source rectangle forbids its parameters. -/
theorem genuinely_new_high_classes (j m : Nat)
    (hres : (j%128=63 ∧ m%128=82) ∨
      (j%128=127 ∧ m%128=18)) :
    BB6.Agent24Phase.highAllowed j m ∧ ¬highAllowedC70 j m := by
  refine ⟨previous_high_admits_rectangle j m hres,?_⟩
  intro h
  exact h.2 hres

#print axioms previous_high_admits_rectangle
#print axioms genuinely_new_high_classes
end BB6.Agent20C70
