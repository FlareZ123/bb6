import Std
namespace BB6.Agent1ShortCone

theorem growth_succ : ∀ q : Nat, 256*(q+1) ≤ 2^(8*(q+1)) := by
  intro q
  induction q with
  | zero => decide
  | succ q ih =>
    have hh : 8*(q+1+1)=8*(q+1)+8 := by omega
    rw [hh, Nat.pow_add]
    have hn : (2:Nat)^8=256 := by decide
    rw [hn]
    omega

theorem growth (q:Nat) (hq:1≤q) : 256*q ≤ 2^(8*q) := by
  cases q with
  | zero => omega
  | succ q => simpa using growth_succ q

theorem scale (q u : Nat) (hq:1≤q) (hu:u+4*q+3=7*2^(16*q)) :
    20*2^(8*q)*2^(8*q) ≤ 4*u+8 := by
  let L := 2^(8*q)
  have hL: 256*q ≤ L := growth q hq
  have hpos: 1≤L := by omega
  have hsq : L ≤ L*L := by
    calc
      L = L*1 := by omega
      _ ≤ L*L := Nat.mul_le_mul_left L hpos
  have hpow : 2^(16*q)=L*L := by
    have he:16*q=8*q+8*q := by omega
    simp only [he, Nat.pow_add, L]
  rw [hpow] at hu
  have ht : 20*(L*L) ≤ 4*u+8 := by omega
  simpa [L, Nat.mul_assoc] using ht

theorem large_left (q u m t b : Nat) (hq:1≤q)
    (hu:u+4*q+3=7*2^(16*q))
    (hcost:m+t+1≤8*q)
    (hleft:4*u+8≤2^m*(b+12)) :
    200*q+30 ≤ b := by
  let L := 2^(8*q)
  have hg : 256*q ≤ L := growth q hq
  have hpos : 0<L := by omega
  have hpow: 2^m ≤L := Nat.pow_le_pow_right (by decide) (by omega)
  have hs : 20*L*L ≤4*u+8 := by simpa [L] using scale q u hq hu
  have hcross : L*(20*L) ≤ L*(b+12) := by
    calc
      L*(20*L) =20*L*L := by simp [Nat.mul_comm]
      _ ≤4*u+8 := hs
      _ ≤2^m*(b+12) := hleft
      _ ≤L*(b+12) := Nat.mul_le_mul_right (b+12) hpow
  have hn := Nat.le_of_mul_le_mul_left hcross hpos
  omega

/-- Every even-right candidate reached by a short positive-odd inverse cone
    sits in the strict gap between consecutive 14-times-powers-of-two. -/
theorem short_even_power_gap
    (q u e m t b d k c : Nat)
    (hq:1≤q)
    (he:e=3 ∨ e=5)
    (hu:u+4*q+3=7*2^(16*q))
    (hmass:b+d+2*m=8*u+e)
    (hleft:4*u+8≤2^m*(b+12))
    (hcost:m+t+1≤8*q)
    (hb:b%4=0) (hd:d%2=1) (hc:c%2=0)
    (hpower:d+b/2+3=2^t*(c+3))
    (hback:2*k+c+2*t+1=b+d) :
    28*2^(16*q)<2*k+8 ∧ 2*k+8<56*2^(16*q) := by
  have hlarge := large_left q u m t b hq hu hcost hleft
  have heven : b%2=0 := by omega
  have hshift_even : (d+b/2+3)%2=0 := by omega
  have htpos : 1≤t := by
    cases t with
    | zero => simp at hpower; omega
    | succ t => omega
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

#print axioms short_even_power_gap
#print axioms growth
#print axioms scale
#print axioms large_left
end BB6.Agent1ShortCone
