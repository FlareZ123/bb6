import Std
import SheepExitWall
import SheepChain2
set_option maxHeartbeats 2000000

namespace SheepXWalls

private theorem two_period (p q n : Nat) (hq : 1 < q)
    (h : 2^p % q=1) : 2^(p*n)%q=1 := by
  induction n with
  | zero => simpa using (Nat.mod_eq_of_lt hq)
  | succ n ih =>
      have hh : 2^(p*(n+1))=2^(p*n)*2^p := by
        rw [show p*(n+1) = p*n+p by simp [Nat.mul_add], Nat.pow_add]
      rw [hh, Nat.mul_mod, ih, h]
      simp [Nat.mod_eq_of_lt hq]

private theorem pow_5 (n : Nat) : 2^(4*n+11)%5=3 := by
  rw [Nat.pow_add, Nat.mul_mod, two_period 4 5 n (by decide) (by decide)]

private theorem pow_17 (n : Nat) : 2^(8*n+11)%17=8 := by
  rw [Nat.pow_add, Nat.mul_mod, two_period 8 17 n (by decide) (by decide)]

private theorem pow_5_special (n : Nat) : (2^(4*n+2)+1)%5=0 := by
  rw [Nat.add_mod, Nat.pow_add, Nat.mul_mod, two_period 4 5 n (by decide) (by decide)]

private theorem pow_17_special (n : Nat) : (2^(8*n+4)+1)%17=0 := by
  rw [Nat.add_mod, Nat.pow_add, Nat.mul_mod, two_period 8 17 n (by decide) (by decide)]

private theorem base5 {n y : Nat}
    (he : 59049*(y+12)=2^(4*n+11)+680296) : (y+12)%5=1 := by
  have hp := pow_5 n
  have hr : (4*((y+12)%5))%5=4 := by
    calc
      (4*((y+12)%5))%5 = (59049*(y+12))%5 := by
        rw [Nat.mul_mod]
        omega
      _ = (2^(4*n+11)+680296)%5 := by rw [he]
      _ = 4 := by rw [Nat.add_mod, hp]
  omega

private theorem base17 {n y : Nat}
    (he : 59049*(y+12)=2^(8*n+11)+680296) : (y+12)%17=4 := by
  have hp := pow_17 n
  have hr : (8*((y+12)%17))%17=15 := by
    calc
      (8*((y+12)%17))%17 = (59049*(y+12))%17 := by
        rw [Nat.mul_mod]
        omega
      _ = (2^(8*n+11)+680296)%17 := by rw [he]
      _ = 15 := by rw [Nat.add_mod, hp]
  omega

/-- Uniform in root exponent parameter: j=17496*m, any m. -/
theorem x_base_residues {m y : Nat}
    (he : 59049*(y+12)=2^(17496*m+11)+680296) :
    (y+12)%5=1 ∧ (y+12)%17=4 := by
  have hj4 : 17496*m=4*(4374*m) := by omega
  have hj8 : 17496*m=8*(2187*m) := by omega
  constructor
  · apply base5 (n:=4374*m)
    simpa only [hj4] using he
  · apply base17 (n:=2187*m)
    simpa only [hj8] using he

private theorem candidate20 (s : Nat) :
    5 ∣ 2^((20*s+1)+1)+1 ∧ 5 ∣ 2*(20*s+1)+23 := by
  have h : (20*s+1)+1=4*(5*s)+2 := by omega
  have hp := pow_5_special (5*s)
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

/-- All depths of seven h8,a2 authentic Sheep corridors obey this
    two-prime generic h0 side-exit barrier; indeed m is unrestricted. -/
theorem x_no_side_exit {m n x y v a : Nat}
    (hbase : 59049*(y+12)=2^(17496*m+11)+680296)
    (hchain : SheepChain2.Chain2 n x y)
    (he : 2*x+1=(2^(a+1)+1)*v+2*a) :
    (∀ s, a ≠ 20*s+1) ∧ (∀ s, a ≠ 136*s+99) := by
  obtain ⟨h5,h17⟩ := x_base_residues hbase
  have h5' : ¬ 5 ∣ y+12 := by
    intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    omega
  have h17' : ¬ 17 ∣ y+12 := by
    intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    omega
  constructor
  · intro s ha
    subst a
    obtain ⟨hm,hv⟩ := candidate20 s
    exact SheepExitWall.no_generic_exit (by decide : Nat.Coprime 5 2)
      (SheepChain2.chain_offset hchain) h5' hm hv he
  · intro s ha
    subst a
    obtain ⟨hm,hv⟩ := candidate136 s
    exact SheepExitWall.no_generic_exit (by decide : Nat.Coprime 17 2)
      (SheepChain2.chain_offset hchain) h17' hm hv he

private theorem parent_mod17_flip {x y : Nat} (h : SheepChain2.Parent2 x y) :
    (y % 17 = 9 → x % 17 = 1) ∧ (y % 17 = 1 → x % 17 = 9) := by
  obtain ⟨_, _, _, he⟩ := h
  have hm : (x%17+y%17)%17=10 := by omega
  constructor <;> omega

private theorem chain_mod17_flip {n x y : Nat} (c : SheepChain2.Chain2 n x y)
    (hy : y%17=9) : x%17=(if n%2=0 then 9 else 1) := by
  induction c with
  | nil z => simpa using hy
  | @cons n x y z edge tail ih =>
      have hn := parent_mod17_flip edge
      have hr := ih hy
      by_cases he : n%2=0
      · have hr' : y%17=9 := by simpa [he] using hr
        have hx : x%17=1 := hn.1 hr'
        simpa [Nat.add_mod, he] using hx
      · have hp : n%2=1 := by omega
        have hr' : y%17=1 := by simpa [hp] using hr
        have hx : x%17=9 := hn.2 hr'
        have hh : (n+1)%2=0 := by omega
        simpa [hh] using hx

/-- Stronger depth-parity restriction for a%8=3 side exits. -/
theorem x_side_val17_at_depth {m n x y v a : Nat}
    (hbase : 59049*(y+12)=2^(17496*m+11)+680296)
    (hchain : SheepChain2.Chain2 n x y)
    (he : 2*x+1=(2^(a+1)+1)*v+2*a)
    (ha : a%8=3) :
    a%17=(if n%2=0 then 1 else 10) := by
  have hy0 : (y+12)%17=4 := (x_base_residues hbase).2
  have hy : y%17=9 := by omega
  have hsrc := chain_mod17_flip hchain hy
  have hrepr : a=8*(a/8)+3 := by omega
  have hm : (2^(a+1)+1)%17=0 := by
    have hp := pow_17_special (a/8)
    have hh : a+1=8*(a/8)+4 := by omega
    simpa only [hh] using hp
  have hzero : ((2^(a+1)+1)*v)%17=0 := by
    rw [Nat.mul_mod, hm]
    simp
  by_cases hn : n%2=0
  · have hx : x%17=9 := by simpa [hn] using hsrc
    have hv : a%17=1 := by omega
    simpa [hn] using hv
  · have hn' : n%2=1 := by omega
    have hx : x%17=1 := by simpa [hn'] using hsrc
    have hv : a%17=10 := by omega
    simpa [hn'] using hv

#print axioms x_base_residues
#print axioms x_no_side_exit
#print axioms x_side_val17_at_depth
end SheepXWalls
