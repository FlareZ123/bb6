import Std

/-!
# Power-of-two residue gap modulo 2^(a+1)+1

Fully Lean-kernel-checked arithmetic theorem, reusable for unbounded inverse
preimage obstructions in BB(6) counter maps.

No external dependencies beyond Lean 4.36.0-rc2 Std; no sorry/admitted axioms.
The theorem is independent of any particular Turing machine reduction.
-/

namespace SheepResidueGap

theorem pow_period (k : Nat) :
    2^(2*k) % (2^k+1) = 1 := by
  have hpow : 2^(2*k) = (2^k)*(2^k) := by
    rw [show 2*k=k+k by omega, Nat.pow_add]
  let n := 2^k
  have hn : 0<n := Nat.pow_pos (by decide)
  have ht : n = (n-1)+1 := by omega
  have heq : n*n=(n-1)*(n+1)+1 := by
    rw [ht]
    simp only [Nat.add_sub_cancel_right]
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  rw [hpow]
  change n*n%(n+1)=1
  rw [heq]
  have hmod : 1<n+1 := by omega
  simp [Nat.mod_eq_of_lt hmod]

private theorem pow_half (a r : Nat) (hr : r ≤ a) :
    2^(a+1+r) % (2^(a+1)+1) = 2^(a+1)+1-2^r := by
  let b:=2^(a+1)
  let z:=2^r
  have hz:0<z := Nat.pow_pos (by decide)
  have hzb:z<b := Nat.pow_lt_pow_right (by decide) (by omega)
  have hz1:z=(z-1)+1 := by omega
  have heq : b*z=(b+1)*(z-1)+(b+1-z) := by
    calc
      b*z=b*((z-1)+1) := congrArg (fun q => b*q) hz1
      _=b*(z-1)+b := by simp [Nat.mul_add]
      _=(b+1)*(z-1)+(b+1-z) := by
        simp only [Nat.add_mul]
        omega
  rw [Nat.pow_add]
  change b*z%(b+1)=b+1-z
  rw [heq]
  have hlt : b+1-z < b+1 := by omega
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

private theorem pow_periodic (a r q : Nat) :
    2^(r + (2*(a+1))*q) % (2^(a+1)+1) = 2^r % (2^(a+1)+1) := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
  rw [Nat.pow_mod (2^(2*(a+1))) q (2^(a+1)+1), pow_period (a+1)]
  simp

/-- Every odd d strictly between 1 and 2^a is excluded from the residues of
powers of two modulo 2^(a+1)+1, uniformly for all natural a,e,d. -/
theorem gap (a e d : Nat) (hodd : d%2=1) (hgt : 1<d) (hlt : d<2^a) :
    2^e % (2^(a+1)+1) ≠ d := by
  let k := a+1
  let period := 2*k
  let r := e % period
  have hperiod : 0 < period := by dsimp [period,k]; omega
  have hrlt : r < period := Nat.mod_lt e hperiod
  have hsplit : e = r + period*(e/period) := by
    simpa [r, Nat.mul_comm] using (Nat.mod_add_div e period).symm
  have hred : 2^e % (2^(a+1)+1) = 2^r % (2^(a+1)+1) := by
    calc
      2^e % (2^(a+1)+1) = 2^(r+period*(e/period)) % (2^(a+1)+1) :=
        congrArg (fun n => 2^n % (2^(a+1)+1)) hsplit
      _ = 2^r % (2^(a+1)+1) := by
        simpa [period,k] using pow_periodic a r (e/period)
  by_cases hr : r < a+1
  · have hrle : r ≤ a := by omega
    have hpowlt : 2^r < 2^(a+1)+1 := by
      have hp : 2^r < 2^(a+1) := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    rw [Nat.mod_eq_of_lt hpowlt] at hred
    by_cases hrzero : r=0
    · have hrpow : 2^r = 1 := by simp [hrzero]
      intro heq
      have heq0 : 2^r = d := by omega
      rw [hrpow] at heq0
      omega
    · have hrpos : 0 < r := by omega
      have hrw : r=(r-1)+1 := by omega
      have heven : 2^r % 2 = 0 := by
        rw [hrw, Nat.pow_succ]
        simp
      intro heq
      have heq0 : d = 2^r := by omega
      rw [heq0] at hodd
      omega
  · let s := r-(a+1)
    have hs : s≤a := by dsimp [s,period,k] at *; omega
    have hre : r=(a+1)+s := by dsimp [s] at *; omega
    have hpowle : 2^s ≤ 2^a := Nat.pow_le_pow_right (by decide) hs
    have hdouble : 2^(a+1)=2*2^a := by rw [Nat.pow_succ]; omega
    have hlarge : 2^a < 2^(a+1)+1-2^s := by omega
    intro heq
    rw [hred, hre, pow_half a s hs] at heq
    omega

#print axioms gap
end SheepResidueGap
