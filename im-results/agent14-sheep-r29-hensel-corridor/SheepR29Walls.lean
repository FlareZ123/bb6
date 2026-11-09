import Std
import SheepExitWall
import SheepChain2

namespace SheepR29Walls

private theorem two_period (p q n : Nat) (hq : 1 < q)
    (h : 2^p % q=1) : 2^(p*n)%q=1 := by
  induction n with
  | zero => simpa using (Nat.mod_eq_of_lt hq)
  | succ n ih =>
      have hh : 2^(p*(n+1))=2^(p*n)*2^p := by
        rw [show p*(n+1) = p*n+p by simp [Nat.mul_add], Nat.pow_add]
      rw [hh, Nat.mul_mod, ih, h]
      simp [Nat.mod_eq_of_lt hq]

private theorem pow_5 (n : Nat) : 2^(4*n+10)%5=4 := by
  rw [Nat.pow_add, Nat.mul_mod, two_period 4 5 n (by decide) (by decide)]

private theorem pow_13 (n : Nat) : 2^(12*n+10)%13=10 := by
  rw [Nat.pow_add, Nat.mul_mod, two_period 12 13 n (by decide) (by decide)]

private theorem pow_17 (n : Nat) : 2^(8*n+10)%17=4 := by
  rw [Nat.pow_add, Nat.mul_mod, two_period 8 17 n (by decide) (by decide)]

private theorem pow_5_special (n : Nat) : (2^(4*n+2)+1)%5=0 := by
  rw [Nat.add_mod, Nat.pow_add, Nat.mul_mod, two_period 4 5 n (by decide) (by decide)]

private theorem pow_13_special (n : Nat) : (2^(12*n+6)+1)%13=0 := by
  rw [Nat.add_mod, Nat.pow_add, Nat.mul_mod, two_period 12 13 n (by decide) (by decide)]

private theorem pow_17_special (n : Nat) : (2^(8*n+4)+1)%17=0 := by
  rw [Nat.add_mod, Nat.pow_add, Nat.mul_mod, two_period 8 17 n (by decide) (by decide)]

private theorem base5 {n y : Nat}
    (he : 3483*(y+12)=2^(4*n+10)+25220) : (y+12)%5=3 := by
  have hp := pow_5 n
  have hr : (3*((y+12)%5))%5=4 := by
    calc
      (3*((y+12)%5))%5 = (3483*(y+12))%5 := by
        rw [Nat.mul_mod]
        omega
      _ = (2^(4*n+10)+25220)%5 := by rw [he]
      _ = 4 := by rw [Nat.add_mod, hp]
  omega

private theorem base13 {n y : Nat}
    (he : 3483*(y+12)=2^(12*n+10)+25220) : (y+12)%13=3 := by
  have hp := pow_13 n
  have hr : (12*((y+12)%13))%13=10 := by
    calc
      (12*((y+12)%13))%13 = (3483*(y+12))%13 := by
        rw [Nat.mul_mod]
        omega
      _ = (2^(12*n+10)+25220)%13 := by rw [he]
      _ = 10 := by rw [Nat.add_mod, hp]
  omega

private theorem base17 {n y : Nat}
    (he : 3483*(y+12)=2^(8*n+10)+25220) : (y+12)%17=2 := by
  have hp := pow_17 n
  have hr : (15*((y+12)%17))%17=13 := by
    calc
      (15*((y+12)%17))%17 = (3483*(y+12))%17 := by
        rw [Nat.mul_mod]
        omega
      _ = (2^(8*n+10)+25220)%17 := by rw [he]
      _ = 13 := by rw [Nat.add_mod, hp]
  omega

/-- The exact r29 parent quotient is a unit modulo 5, 13, and 17. -/
theorem r29_base_coprime_5_13_17 {k y : Nat}
    (he : 3483*(y+12)=2^(17496*(29+63*k)+10)+25220) :
    ¬ 5 ∣ y+12 ∧ ¬ 13 ∣ y+12 ∧ ¬ 17 ∣ y+12 := by
  have hj4 : 17496*(29+63*k)=4*(4374*(29+63*k)) := by omega
  have hj12 : 17496*(29+63*k)=12*(1458*(29+63*k)) := by omega
  have hj8 : 17496*(29+63*k)=8*(2187*(29+63*k)) := by omega
  have h5 : (y+12)%5=3 := by
    apply base5 (n:=4374*(29+63*k))
    simpa only [hj4] using he
  have h13 : (y+12)%13=3 := by
    apply base13 (n:=1458*(29+63*k))
    simpa only [hj12] using he
  have h17 : (y+12)%17=2 := by
    apply base17 (n:=2187*(29+63*k))
    simpa only [hj8] using he
  constructor
  · intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    omega
  constructor
  · intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    omega
  · intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    omega

private theorem candidate20 (s : Nat) :
    5 ∣ 2^((20*s+1)+1)+1 ∧ 5 ∣ 2*(20*s+1)+23 := by
  have h : (20*s+1)+1=4*(5*s)+2 := by omega
  have hp := pow_5_special (5*s)
  rw [←h] at hp
  constructor
  · exact Nat.dvd_of_mod_eq_zero hp
  · omega

private theorem candidate156 (s : Nat) :
    13 ∣ 2^((156*s+125)+1)+1 ∧ 13 ∣ 2*(156*s+125)+23 := by
  have h : (156*s+125)+1=12*(13*s+10)+6 := by omega
  have hp := pow_13_special (13*s+10)
  rw [←h] at hp
  constructor
  · exact Nat.dvd_of_mod_eq_zero hp
  · omega

private theorem candidate136 (s : Nat) :
    17 ∣ 2^((136*s+99)+1)+1 ∧ 17 ∣ 2*(136*s+99)+23 := by
  have h : (136*s+99)+1=8*(17*s+12)+4 := by omega
  have hp := pow_17_special (17*s+12)
  rw [←h] at hp
  constructor
  · exact Nat.dvd_of_mod_eq_zero hp
  · omega

/-- Three infinite generic exit valuation progressions ruled out at *every*
    depth of a genuine h=0,a=2 predecessor corridor of the r29 terminal. -/
theorem r29_no_generic_side_exit
    {k n x y v a : Nat}
    (hbase : 3483*(y+12)=2^(17496*(29+63*k)+10)+25220)
    (hchain : 9^n*(x+12)=8^n*(y+12))
    (he : 2*x+1 = (2^(a+1)+1)*v+2*a) :
    (∀ s, a ≠ 20*s+1) ∧
    (∀ s, a ≠ 156*s+125) ∧
    (∀ s, a ≠ 136*s+99) := by
  obtain ⟨h5,h13,h17⟩ := r29_base_coprime_5_13_17 hbase
  constructor
  · intro s ha
    subst a
    obtain ⟨hm, hv⟩ := candidate20 s
    exact SheepExitWall.no_generic_exit (by decide : Nat.Coprime 5 2)
      hchain h5 hm hv he
  constructor
  · intro s ha
    subst a
    obtain ⟨hm, hv⟩ := candidate156 s
    exact SheepExitWall.no_generic_exit (by decide : Nat.Coprime 13 2)
      hchain h13 hm hv he
  · intro s ha
    subst a
    obtain ⟨hm, hv⟩ := candidate136 s
    exact SheepExitWall.no_generic_exit (by decide : Nat.Coprime 17 2)
      hchain h17 hm hv he

theorem r29_no_side_exit_after_genuine_chain
    {k n x y v a : Nat}
    (hbase : 3483*(y+12)=2^(17496*(29+63*k)+10)+25220)
    (hchain : SheepChain2.Chain2 n x y)
    (he : 2*x+1 = (2^(a+1)+1)*v+2*a) :
    (∀ s, a ≠ 20*s+1) ∧
    (∀ s, a ≠ 156*s+125) ∧
    (∀ s, a ≠ 136*s+99) := by
  exact r29_no_generic_side_exit hbase (SheepChain2.chain_offset hchain) he

#print axioms r29_no_side_exit_after_genuine_chain
#print axioms r29_base_coprime_5_13_17
#print axioms r29_no_generic_side_exit
end SheepR29Walls
