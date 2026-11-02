import ShortConeGap
namespace BB6.Agent1ShortCone

private theorem growth15_succ : ∀ q : Nat, 2*(q+1) ≤ 2^(q+1) := by
  intro q
  induction q with
  | zero => decide
  | succ q ih =>
    have hp : 2^(q+1+1)=2*2^(q+1) := by
      rw [show q+1+1=(q+1)+1 by omega, Nat.pow_succ]
      omega
    rw [hp]
    omega

theorem growth15 (q:Nat) (hq:1≤q) : 2*q ≤2^q := by
  cases q with
  | zero => omega
  | succ q => simpa using growth15_succ q

theorem scale15 (q u:Nat) (hq:1≤q) (hu:u+4*q+3=7*2^(16*q)) :
    27*2^(16*q) ≤4*u+8 := by
  have hs : 256*q ≤2^(8*q) := growth q hq
  have hh : 2^(8*q) ≤2^(16*q) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem large_left15 (q u m t b:Nat) (hq:1≤q)
    (hu:u+4*q+3=7*2^(16*q))
    (ht:1≤t)
    (hcost:m+t+1≤15*q)
    (hleft:4*u+8≤2^m*(b+12)) :
    200*q≤b := by
  let P := 2^(15*q)
  let L := 2^q
  have hg : 2*q ≤L := growth15 q hq
  have hp : 0<P := by
    dsimp [P]
    have hh : 1≤2^(15*q) := Nat.one_le_pow _ _ (by decide)
    omega
  have hpow : 4*2^m ≤ P := by
    have hbound:m+2≤15*q := by omega
    have hh:=Nat.pow_le_pow_right (show 0<(2:Nat) by decide) hbound
    have he:2^(m+2)=4*2^m:=by rw [Nat.pow_add]; omega
    rw [he] at hh
    exact hh
  have hfact : 2^(16*q) = P*L := by
    have he:16*q=15*q+q := by omega
    simp [P,L,he,Nat.pow_add]
  have hsc : 27*P*L ≤4*u+8 := by
    have hs:=scale15 q u hq hu
    rw [hfact] at hs
    simpa [Nat.mul_assoc] using hs
  have hcross : P*(108*L) ≤P*(b+12) := by
    calc
      P*(108*L) =4*(27*P*L) := by
        have hh : (108:Nat)=4*27 := by decide
        rw [hh]
        ac_rfl
      _ ≤4*(4*u+8) := Nat.mul_le_mul_left 4 hsc
      _ ≤4*(2^m*(b+12)) := Nat.mul_le_mul_left 4 hleft
      _ ≤P*(b+12) := by
        calc
          4*(2^m*(b+12))=(4*2^m)*(b+12) := by ac_rfl
          _ ≤P*(b+12) := Nat.mul_le_mul_right (b+12) hpow
  have hh := Nat.le_of_mul_le_mul_left hcross hp
  omega

/-- Every even-right leaf within 15q total dyadic inversion cost lies
strictly between consecutive powers, uniformly across both P1 feeders. -/
theorem medium_even_power_gap
    (q u e m t b d k c : Nat)
    (hq:1≤q)
    (he:e=3 ∨ e=5)
    (hu:u+4*q+3=7*2^(16*q))
    (hmass:b+d+2*m=8*u+e)
    (hleft:4*u+8≤2^m*(b+12))
    (hcost:m+t+1≤15*q)
    (hb:b%4=0) (hd:d%2=1) (hc:c%2=0)
    (hpower:d+b/2+3=2^t*(c+3))
    (hback:2*k+c+2*t+1=b+d) :
    28*2^(16*q)<2*k+8 ∧ 2*k+8<56*2^(16*q) := by
  have heven : b%2=0 := by omega
  have hshift_even : (d+b/2+3)%2=0 := by omega
  have htpos : 1≤t := by
    cases t with
    | zero => simp at hpower; omega
    | succ t => omega
  have hlarge := large_left15 q u m t b hq hu htpos hcost hleft
  have htpow : 2 ≤ 2^t := by
    cases t with
    | zero => omega
    | succ t =>
      rw [Nat.pow_succ]
      have hp : 1≤2^t := Nat.one_le_pow _ _ (by decide)
      omega
  have hcupper : 2*(c+3) ≤d+b/2+3 := by
    have hh := Nat.mul_le_mul_right (c+3) htpow
    omega
  have hkey : 2*(2*k+8)+4*t ≥ b+d+b/2+17 := by omega
  constructor
  · omega
  · omega

#print axioms medium_even_power_gap
#print axioms large_left15
end BB6.Agent1ShortCone
