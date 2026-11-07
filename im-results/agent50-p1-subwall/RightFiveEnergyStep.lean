import RightFiveEnergyNumeric

namespace BB6.Agent50Energy

private theorem two_mul_half (b : Nat) (hb : b % 4 = 0) :
    2*(b/2)=b := by omega

/-- Fundamental exact source-shape inverted mass/power identities,
parametrized only by the official inverseAt power/mass equations. -/
theorem energy_step_exact (n b d m t k c : Nat)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hb : b%4=0)
    (hpower : d+b/2+3=2^t*(c+3))
    (hinvMass : 2*k+c+2*t+2=b+d)
    (hk : 2≤k) :
    (b+4*m+4*n+20)+2^(t+1)*(c+3)=28*2^n ∧
    ((2*k-4)+4*(m+t+1)+4*n+20)+(c+3)=
       14*2^n+2*(m+n+t+4) := by
  have hh : 2*(b/2)=b := two_mul_half b hb
  have hpow : 2^(t+1)*(c+3)=2*(2^t*(c+3)) := by
    rw [Nat.pow_succ]
    ac_rfl
  constructor
  · rw [hpow]
    omega
  · omega

/-- Any source-shape inverse at t=0 or t=1 with modest total cost
falls by at least a full dyadic 2^n below the shifted twelve-power wall. -/
theorem shallow_step_deficit (n M b d m t k c : Nat)
    (hn : 128 ≤ n) (hM : 2*M≤n) (hcost : m+t+1≤M)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hb : b%4=0)
    (hpower : d+b/2+3=2^t*(c+3))
    (hinvMass : 2*k+c+2*t+2=b+d)
    (ht : t≤1) (hk : 2≤k) :
    ((2*k-4)+4*(m+t+1)+4*n+20)+2^n ≤ 12*2^n := by
  obtain ⟨hpowerExact,hout⟩ :=
    energy_step_exact n b d m t k c hmass hb hpower hinvMass hk
  have h100 : 100*n≤2^n :=
    BB6.Agent50RightFiveTwo.hundred_mul_le_pow n (by omega)
  have hsrcB : b≤14*2^n := by omega
  have hbefore : b+4*m+4*n+20 ≤14*2^n+2*m+2*n+7 := by omega
  have htp : 2^(t+1)≤4 := by
    by_cases hzero : t=0
    · simp [hzero]
    · have hone : t=1 := by omega
      simp [hone]
  have hmult : 2^(t+1)*(c+3)≤4*(c+3) :=
    Nat.mul_le_mul_right (c+3) htp
  have hclower : 14*2^n≤4*(c+3)+2*m+2*n+7 := by omega
  have hneed : 3*2^n+2*(m+n+t+4)≤c+3 := by omega
  omega

/-- Every t>=3 source-shape inverse ends strictly above the shifted
wall regardless of the prior sign. -/
theorem deep_high_step_above (n b d m t k c : Nat)
    (hn : 14≤n)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hb : b%4=0)
    (hpower : d+b/2+3=2^t*(c+3))
    (hinvMass : 2*k+c+2*t+2=b+d)
    (ht : 3≤t) (hk : 2≤k) :
    12*2^n < (2*k-4)+4*(m+t+1)+4*n+20 := by
  obtain ⟨hpowerExact,hout⟩ :=
    energy_step_exact n b d m t k c hmass hb hpower hinvMass hk
  have hpow : 16≤2^(t+1) := by
    have hmono := Nat.pow_le_pow_right (by decide : 0<(2:Nat))
      (show 4≤t+1 by omega)
    simpa using hmono
  have h16 : 16*(c+3) ≤ 2^(t+1)*(c+3) :=
    Nat.mul_le_mul_right (c+3) hpow
  have hsmall : c+3 <2*2^n := by
    have hp : 0<(2:Nat)^n := Nat.pow_pos (by decide)
    omega
  omega

/-- Exact dyadic contraction at depth two, with positive cost offset. -/
theorem two_step_cocycle (n b d m k c : Nat)
    (hmass : b+d+2*m+2*n+13=14*2^n)
    (hb : b%4=0)
    (hpower : d+b/2+3=2^2*(c+3))
    (hinvMass : 2*k+c+2*2+2=b+d) :
    8*((2*k-4)+4*(m+2+1)+4*n+20)=
      (b+4*m+4*n+20)+84*2^n+16*(m+n+6) := by
  have hpow : 2^2=4 := by decide
  rw [hpow] at hpower
  have hh : 2*(b/2)=b := two_mul_half b hb
  omega

#print axioms BB6.Agent50Energy.energy_step_exact
#print axioms BB6.Agent50Energy.shallow_step_deficit
#print axioms BB6.Agent50Energy.deep_high_step_above
#print axioms BB6.Agent50Energy.two_step_cocycle

end BB6.Agent50Energy
