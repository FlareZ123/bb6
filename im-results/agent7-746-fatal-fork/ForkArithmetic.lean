import ForkRoot
set_option maxHeartbeats 0
namespace BB746Fork

/-- A purely linear congruence criterion for the exact two-layer fork.
The four residue pairs correspond to indices 40, 401, 1012, 1373
modulo 1458. -/
theorem residue_fork (n p x h y z : Nat)
    (hx : 9*x+17*n+39=56*p)
    (hh : 9*h+43*n+60=40*p)
    (hy : 243*y+515*n+507=410*p)
    (hz : 243*z+1273*n+42=334*p)
    (hr : (p%729=544 ∧ n%729=40) ∨
          (p%729=224 ∧ n%729=401) ∨
          (p%729=544 ∧ n%729=283) ∨
          (p%729=224 ∧ n%729=644)) :
    (2*x+5)%81≠0 ∧ h%3≠2 ∧ y%3≠2 ∧ z%3≠2 := by
  rcases hr with hr | hr | hr | hr
  all_goals omega

/-- Arithmetic transport of an exact inverse fork into the two-layer
blank-root closure obstruction. -/
theorem index_fork_root_exclusion (n k p x h y z : Nat)
    (hk : 4≤k) (hkn : k+2=n) (hp : p=2^k)
    (hgrowth : 100*n+200<p)
    (hx : 9*x+17*n+39=56*p)
    (hh : 9*h+43*n+60=40*p)
    (hy : 243*y+515*n+507=410*p)
    (hz : 243*z+1273*n+42=334*p)
    (hr : (p%729=544 ∧ n%729=40) ∨
          (p%729=224 ∧ n%729=401) ∨
          (p%729=544 ∧ n%729=283) ∨
          (p%729=224 ∧ n%729=644)) :
    ¬ResetChain 2 x := by
  obtain ⟨hx81,hhmod,hymod,hzmod⟩ := residue_fork n p x h y z hx hh hy hz hr
  have hpk : 2^k=p := hp.symm
  have hpow : p=4*2^(k-2) := by
    have he : k=(k-2)+2 := by omega
    rw [he, Nat.pow_add] at hp
    omega
  have hxhigh : 6*2^k≤x := by rw [hpk]; omega
  have hxguard : x+k+5<8*2^k := by rw [hpk]; omega
  have hxnarrow : 4*x+10<27*2^k := by rw [hpk]; omega
  have hxeven : 2*x=8*2^k+h+k := by rw [hpk]; omega
  have hxodd : 27*(2*2^k+y+k+3)=8*(2*x+5) := by rw [hpk]; omega
  have hxband : 6*2^k-1≤x ∧ x≤8*2^k-3 := by rw [hpk]; constructor <;> omega
  have hhgaplo : 4*2^k-3<h := by rw [hpk]; omega
  have hhgaphi : h<6*2^k-1 := by rw [hpk]; omega
  have hyband : 6*2^(k-2)-1≤y ∧ y≤8*2^(k-2)-3 := by
    constructor <;> omega
  have hyrel : 2*y=8*2^(k-2)+z+(k-2) := by omega
  have hzgaplo : 4*2^(k-2)-3<z := by omega
  have hzgaphi : z<6*2^(k-2)-1 := by omega
  exact two_layer_root_exclusion k x h y z hk hxhigh hxguard
    hxnarrow hx81 hxeven hxodd hxband hhgaplo hhgaphi hhmod
    hyband hyrel hymod hzgaplo hzgaphi hzmod

#print axioms residue_fork
#print axioms index_fork_root_exclusion
end BB746Fork
