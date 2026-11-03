import TerminalMod1000
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace SpaceNeedleExp

def geo10 : Nat → Nat
  | 0 => 0
  | e+1 => 10 * geo10 e + 1

def geo2050 : Nat → Nat
  | 0 => 0
  | e+1 => 2050 * geo2050 e + 1

private theorem geo10_id (e : Nat) : 9*geo10 e+1=10^e := by
  induction e with
  | zero => decide
  | succ e ih =>
    simp only [geo10, Nat.pow_succ]
    omega

private theorem geo2050_id (e : Nat) : 2049*geo2050 e+1=2050^e := by
  induction e with
  | zero => decide
  | succ e ih =>
    simp only [geo2050, Nat.pow_succ]
    omega

private theorem pow_pos_two (e : Nat) : 1 ≤ 2^e := by
  have h := Nat.pow_pos (n:=e) (by omega : 0 < 2)
  omega

private theorem even_decimal (e r B : Nat)
    (hr : r < 2*10^e) (he : r%2=0) :
    (12+18*(geo10 e*(6+10^e-r/2)+10^e*B))%(2*10^e)=r := by
  let m := 10^e
  let a := geo10 e
  let t := 1
  let y := r/2
  let s := 6+m-y
  have hy : r=2*y := by dsimp [y]; omega
  have hsmall : y<m := by dsimp [y,m]; omega
  have hs : s+y=6+m := by dsimp [s]; omega
  have hp : 1≤t := by dsimp [t]; omega
  have hsm : 1≤s := by dsimp [s]; omega
  have hts : 1≤t*s := Nat.mul_le_mul hp hsm
  have hi : 9*a+1=m*t := by
    dsimp [a,m,t]
    simpa using geo10_id e
  have hbalanced : 9*a*s+s=m*(t*s) := by
    calc
      9*a*s+s = (9*a+1)*s := by simp [Nat.add_mul, Nat.mul_assoc]
      _ = (m*t)*s := by rw[hi]
      _ = m*(t*s) := by simp [Nat.mul_assoc]
  have heq : 12+18*(a*s+m*B) = r + (2*m)*(t*s-1+9*B) := by
    rw [hy]
    have hrew : t*s = (t*s-1)+1 := by omega
    calc
      12+18*(a*s+m*B) = 2*(6+9*a*s+9*m*B) := by simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]; omega
      _ = 2*(y+m*(t*s-1+9*B)) := by
        have hb : 6+9*a*s+9*m*B = y+m*(t*s-1+9*B) := by
          calc
            6+9*a*s+9*m*B = y+(9*a*s+s)-m+9*m*B := by omega
            _ = y+m*(t*s-1+9*B) := by
              rw [hbalanced]
              have hfac : m*(t*s)=m*(t*s-1)+m := by
                rw [hrew]
                simp [Nat.mul_add]
              have hB : 9*m*B=m*(9*B) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              have hadd : m*(t*s-1+9*B)=m*(t*s-1)+m*(9*B) := by
                rw [Nat.mul_add]
              omega
        rw [hb]
      _ = 2*y+(2*m)*(t*s-1+9*B) := by simp [Nat.mul_add, Nat.mul_assoc]
  have hrem : (r + 2*m*(t*s-1+9*B))%(2*m) = r := by
    rw [show 2*m*(t*s-1+9*B)=(t*s-1+9*B)*(2*m) by
      simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]]
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by simpa only [m] using hr)
  change (12+18*(a*s+m*B))%(2*m)=r
  rw [heq]
  exact hrem

private theorem pow_pos_twohundredfive (e : Nat) : 1 ≤ 205^e := by
  have h : 0 < 205^e := Nat.pow_pos (n:=e) (by omega : 0 < 205)
  omega

private theorem odd_decimal (e r B : Nat)
    (hr : r < 2*10^e) (ho : r%2=1) :
    (3669+4098*(geo2050 e*(1834+10^e-r/2)+10^e*B))%(2*10^e)=r := by
  let m := 10^e
  let a := geo2050 e
  let t := 205^e
  let y := r/2
  let s := 1834+m-y
  have hy : r=2*y+1 := by dsimp [y]; omega
  have hsmall : y<m := by dsimp [y,m]; omega
  have hs : s+y=1834+m := by dsimp [s]; omega
  have hp : 1≤t := pow_pos_twohundredfive e
  have hsm : 1≤s := by dsimp [s]; omega
  have hts : 1≤t*s := Nat.mul_le_mul hp hsm
  have hi : 2049*a+1=m*t := by
    dsimp [a,m,t]
    rw [geo2050_id]
    rw [show (2050:Nat)=10*205 by decide, Nat.mul_pow]
  have hbalanced : 2049*a*s+s=m*(t*s) := by
    calc
      2049*a*s+s = (2049*a+1)*s := by simp [Nat.add_mul, Nat.mul_assoc]
      _ = (m*t)*s := by rw[hi]
      _ = m*(t*s) := by simp [Nat.mul_assoc]
  have heq : 3669+4098*(a*s+m*B) = r + (2*m)*(t*s-1+2049*B) := by
    rw [hy]
    have hrew : t*s = (t*s-1)+1 := by omega
    calc
      3669+4098*(a*s+m*B) = 2*(1834+2049*a*s+2049*m*B)+1 := by simp [Nat.mul_add, Nat.mul_assoc]; omega
      _ = 2*(y+m*(t*s-1+2049*B))+1 := by
        have hb : 1834+2049*a*s+2049*m*B = y+m*(t*s-1+2049*B) := by
          calc
            1834+2049*a*s+2049*m*B = y+(2049*a*s+s)-m+2049*m*B := by omega
            _ = y+m*(t*s-1+2049*B) := by
              rw [hbalanced]
              have hfac : m*(t*s)=m*(t*s-1)+m := by
                rw [hrew]
                simp [Nat.mul_add]
              have hB : 2049*m*B=m*(2049*B) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              have hadd : m*(t*s-1+2049*B)=m*(t*s-1)+m*(2049*B) := by
                rw [Nat.mul_add]
              omega
        rw [hb]
      _ = 2*y+1+(2*m)*(t*s-1+2049*B) := by simp [Nat.mul_add, Nat.mul_assoc]; omega
  have hrem : (r + 2*m*(t*s-1+2049*B))%(2*m) = r := by
    rw [show 2*m*(t*s-1+2049*B)=(t*s-1+2049*B)*(2*m) by
      simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]]
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by simpa only [m] using hr)
  change (3669+4098*(a*s+m*B))%(2*m)=r
  rw [heq]
  exact hrem

/-- Every residue modulo 2*10^e contains arbitrarily high terminal
power-of-two exponents with an exact one-step predecessor. -/
theorem all_decimal_predecessors (e r bound : Nat) (hr : r < 2*10^e) :
    ∃ k q v, bound ≤ k ∧ k%(2*10^e)=r ∧
      ((2:Nat)^v*(2*q+3)-2+v+3*(q+1) = (2:Nat)^k-2) := by
  let m := 10^e
  have hm : 1≤m := by
    have h : 0 < 10^e := Nat.pow_pos (n:=e) (by omega : 0 < 10)
    dsimp [m]
    omega
  by_cases he : r%2=0
  · let n := geo10 e*(6+m-r/2)+m*bound
    refine ⟨evenKe n,e3Q n,3,?_,?_,?_⟩
    · have hmb : bound≤m*bound := by
        simpa using Nat.mul_le_mul_right bound hm
      dsimp [evenKe,n]
      omega
    · exact even_decimal e r bound hr he
    · exact even3Predecessor n
  · have ho : r%2=1 := by omega
    let n := geo2050 e*(1834+m-r/2)+m*bound
    refine ⟨K n,q n,11,?_,?_,?_⟩
    · have hmb : bound≤m*bound := by
        simpa using Nat.mul_le_mul_right bound hm
      dsimp [K,n]
      omega
    · exact odd_decimal e r bound hr ho
    · exact predecessor n

/-- Every decimal exponent suffix occurs arbitrarily high among terminal
powers with one-step sources in the abstract Space Needle high-level map. -/
theorem every_decimal_suffix (e r bound : Nat) (hr : r < 10^e) :
    ∃ k q v, bound ≤ k ∧ k%(10^e)=r ∧
      ((2:Nat)^v*(2*q+3)-2+v+3*(q+1) = (2:Nat)^k-2) := by
  obtain ⟨k,q,v,hb,hm,heq⟩ :=
    all_decimal_predecessors e r bound (by omega : r < 2*10^e)
  refine ⟨k,q,v,hb,?_,heq⟩
  have hd : 10^e ∣ 2*10^e := ⟨2, by omega⟩
  have hmod := Nat.mod_mod_of_dvd k hd
  rw [hm, Nat.mod_eq_of_lt hr] at hmod
  exact hmod.symm

end SpaceNeedleExp
#print axioms SpaceNeedleExp.geo10_id
#print axioms SpaceNeedleExp.geo2050_id
#print axioms SpaceNeedleExp.all_decimal_predecessors
#print axioms SpaceNeedleExp.every_decimal_suffix
