import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 4096
namespace CascadeTranslatedRayDepth

/-- Arithmetic Nat-to-Int bridge from exact #746 ray-deficit and t=3 source equations. -/
theorem high_source_nat_bounds (n j D d q e r : Nat)
    (hn : 20 ≤ n)
    (hclosed : D+(n-1)=2^j*(2*n+3))
    (hm : 2048*D+16384*n+16384≤2^n)
    (hz : (8:Int)*(2:Int)^n+2*n+3-(2:Int)^(j+1)*(2*n+3)=81*(d:Int))
    (hrel : 16*d=2^n+q+(n-3)+5)
    (hgate : 2*q+5=81*e)
    (hrrel : 16*e=8*2^(n-6)+r+(n-6)+5) :
    10934*((2^(n-4):Nat):Int)-961*(n:Int)+18609≤6561*(r:Int) ∧
    6561*(r:Int)≤10942*((2^(n-4):Nat):Int)-10177*(n:Int)+6321 := by
  have hp1 : 2^n=16*2^(n-4) := by
    have he : n=(n-4)+4:=by omega
    calc
      2^n=2^((n-4)+4):=by rw [←he]
      _=2^(n-4)*16:=by simp [Nat.pow_add]
      _=16*2^(n-4):=by omega
  have hp2 : 2^(n-3)=8*2^(n-6) := by
    have he : n-3=(n-6)+3:=by omega
    calc
      2^(n-3)=2^((n-6)+3):=by rw [←he]
      _=2^(n-6)*8:=by simp [Nat.pow_add]
      _=8*2^(n-6):=by omega
  have hp3 : 2^(n-3)=2*2^(n-4) := by
    have he : n-3=(n-4)+1:=by omega
    calc
      2^(n-3)=2^((n-4)+1):=by rw [←he]
      _=2*2^(n-4):=by rw [Nat.pow_succ]; omega
  have hrel' : 16*d=2^n+q+n+2 := by omega
  have hrrel' : 16*e+1=2^(n-3)+r+n := by omega
  have hclosedNat : D+n=2^j*(2*n+3)+1 := by omega
  have hclosedI : (D:Int)+(n:Int)=((2:Int)^j)*(2*n+3)+1 := by
    exact_mod_cast hclosedNat
  have hmOrigI : (2048:Int)*(D:Int)+16384*(n:Int)+16384≤(2:Int)^n := by
    have hh : ((2048*D+16384*n+16384:Nat):Int) ≤ ((2^n:Nat):Int) := Int.ofNat_le.mpr hm
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at hh
    change (2048:Int)*(D:Int)+16384*(n:Int)+16384≤(2:Int)^n at hh
    exact hh
  have hmI : (2048:Int)*((2:Int)^j*(2*n+3))+14336*n+18432≤(2:Int)^n := by
    omega
  have hp1I : (2:Int)^n=16*((2^(n-4):Nat):Int) := by exact_mod_cast hp1
  have hp2I : (2:Int)^(n-3)=8*((2^(n-6):Nat):Int) := by exact_mod_cast hp2
  have hp3I : (2:Int)^(n-3)=2*((2^(n-4):Nat):Int) := by exact_mod_cast hp3
  have hrelI : (16:Int)*(d:Int)=(2:Int)^n+q+n+2 := by exact_mod_cast hrel'
  have hgateI : (2:Int)*q+5=81*(e:Int) := by exact_mod_cast hgate
  have hrrelI : (16:Int)*(e:Int)+1=(2:Int)^(n-3)+r+n := by exact_mod_cast hrrel'
  have hpowJ : (2:Int)^(j+1)=2*(2:Int)^j := by
    rw [Int.pow_succ]
    omega
  have hz2 : (8:Int)*(2:Int)^n+2*n+3 -2*((2:Int)^j*(2*n+3))=81*(d:Int) := by
    rw [hpowJ] at hz
    simpa only [Int.mul_assoc] using hz
  have hqlinear : (81:Int)*(q:Int)=752*((2^(n-4):Nat):Int)-49*n-114-32*((2:Int)^j*(2*n+3)) := by
    omega
  have hrformula : (81:Int)*(r:Int)=32*(q:Int)+80-162*((2^(n-4):Nat):Int)-81*n+81 := by
    omega
  have hA : (2:Int)*n+3 ≤ ((2:Int)^j*(2*n+3)) := by
    have hpos:1≤(2:Nat)^j:=Nat.one_le_pow j 2 (by decide)
    have hpos' :(2*n+3:Nat)≤2^j*(2*n+3) := by
      have hh:=Nat.mul_le_mul_right (2*n+3) hpos
      simpa [Nat.mul_comm] using hh
    exact_mod_cast hpos'
  have hmargin : 128*((2:Int)^j*(2*n+3))+896*n+1152≤((2^(n-4):Nat):Int) := by omega
  have hqLower : 324*(q:Int)≥3007*((2^(n-4):Nat):Int)+700*n+696 := by omega
  have hqUpper : 81*(q:Int)≤752*((2^(n-4):Nat):Int)-113*n-210 := by omega
  constructor <;> omega

#print axioms high_source_nat_bounds
end CascadeTranslatedRayDepth
