import SuperlinearAll

namespace BB6.Agent48.SuperMod

/-- Exponential growth dominates five times a square at every n≥9. -/
theorem five_square_le_two_pow (n : Nat) (hn : 9 ≤ n) : 5*n*n ≤ (2:Nat)^n := by
  have h : ∀ k : Nat, 5*(9+k)*(9+k) ≤ (2:Nat)^(9+k) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      let m := 9+k
      have hm : 3≤m := by dsimp [m]; omega
      have h3m : 3*m ≤ m*m := Nat.mul_le_mul_right m hm
      have hsquare : (m+1)*(m+1)=m*m+2*m+1 := by
        simp [Nat.add_mul,Nat.mul_add]
        omega
      have hbig : (m+1)*(m+1)≤2*(m*m) := by omega
      have hb := Nat.mul_le_mul_left 5 hbig
      have hpow : (2:Nat)^(m+1)=2*(2:Nat)^m := by rw [Nat.pow_succ']
      have hstep : 9+(k+1)=m+1 := by dsimp [m]; omega
      rw [hstep,hpow]
      have ih' : 5*m*m ≤ (2:Nat)^m := ih
      have hh := Nat.mul_le_mul_left 2 ih'
      have hmul : 5*((m+1)*(m+1))=5*(m+1)*(m+1) := by ac_rfl
      rw [←hmul]
      have hm2 : 5*(2*(m*m))=2*(5*m*m) := by ac_rfl
      rw [hm2] at hb
      omega
  have h9 : 9+(n-9)=n := by omega
  simpa only [h9] using h (n-9)

theorem cutoff_pow_one (v A : Nat) (hA : 9≤A) (hv : A+1≤v) :
    (A+1)*(2*v+3*(A+1)) < (2:Nat)^(v+1)+3 := by
  let M := A+1
  have hM : M≤v := hv
  have hv9 : 9≤v := by omega
  have hsq := five_square_le_two_pow v hv9
  have hsum : 2*v+3*M≤5*v := by omega
  have hm := Nat.mul_le_mul hM hsum
  have hm2 : v*(5*v) = 5*v*v := by ac_rfl
  have hlt : M*(2*v+3*M)≤5*v*v := by omega
  have hpow : (2:Nat)^(v+1)=2*(2:Nat)^v := by rw [Nat.pow_succ']
  change M*(2*v+3*M)<(2:Nat)^(v+1)+3
  rw [hpow]
  omega

theorem small_quotient_first_one (v t r c : Nat) (m:Int)
    (ht : t≤c) (hr : r≤v) (hc2 : 2≤c) (hv : ((3:Nat)^c+1)≤v)
    (he : (-3:Int)^t*(2:Int)^r-(2*(v:Int)-3) =
       ((2:Int)^(v+1)+3)*m) : m.natAbs ≤ (3:Nat)^c+1 := by
  let A := (3:Nat)^c
  let D := (2:Nat)^(v+1)+3
  let Z := 2*v-3
  have hApos : 0≤A := Nat.zero_le A
  have hA9 : 9≤A := by
    dsimp [A]
    simpa using (Nat.pow_le_pow_right (by decide : 0<(3:Nat)) hc2 : (3:Nat)^2 ≤ 3^c)
  have hv4 : 4≤v := by omega
  have hsq := square_le_two_pow v hv4
  have h2v : 2*v ≤ (2:Nat)^v := by
    have hm := Nat.mul_le_mul_right v (by omega : 2≤v)
    omega
  have hz : (2*(v:Int)-3)=(Z:Int) := by
    dsimp [Z]
    rw [Int.natCast_sub (by omega : 3≤2*v)]
    omega
  have hD : ((2:Int)^(v+1)+3)=(D:Int) := by simp [D]
  have ha : ((-3:Int)^t).natAbs ≤ A := by
    rw [Int.natAbs_pow]
    have hh : (-3:Int).natAbs = 3 := by decide
    rw [hh]
    exact Nat.pow_le_pow_right (by decide : 0<(3:Nat)) ht
  have hb : ((2:Int)^r).natAbs ≤ (2:Nat)^v := by
    rw [Int.natAbs_pow]
    have hh : (2:Int).natAbs = 2 := by decide
    rw [hh]
    exact Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hr
  have hab : D*m.natAbs ≤ A*((2:Nat)^v)+Z :=
    quotient_abs_bound _ _ _ _ _ A ((2:Nat)^v) D Z ha hb hD hz he.symm
  have hbase : A*((2:Nat)^v)+Z ≤ (A+1)*((2:Nat)^v) := by
    dsimp [Z]
    rw [Nat.add_mul]
    omega
  have hdpos : (2:Nat)^v < D := by
    dsimp [D]
    rw [Nat.pow_succ']
    have hn : 0 < (2:Nat)^v := Nat.pow_pos (by decide)
    omega
  exact quotient_small m.natAbs ((2:Nat)^v) D (A+1) hdpos (by omega)

theorem small_quotient_final_one (v t r c : Nat) (m:Int)
    (ht : t≤c) (hr : r≤v) (hc2 : 2≤c) (hv : ((3:Nat)^c+1)≤v)
    (he : (-3:Int)^t*(2:Int)^r-(2*(v:Int)-3) =
       ((2:Int)^(v+1)+3)*m) : m=0 := by
  let A := (3:Nat)^c
  let M := A+1
  let Z := 2*v-3
  let D := (2:Nat)^(v+1)+3
  have hv4 : 4≤v := by
    have ha9 : 9≤A := by
      dsimp [A]
      simpa using (Nat.pow_le_pow_right (by decide : 0<(3:Nat)) hc2 : (3:Nat)^2 ≤ 3^c)
    omega
  have hz : (2*(v:Int)-3)=(Z:Int) := by
    dsimp [Z]
    rw [Int.natCast_sub (by omega : 3≤2*v)]
    omega
  have hZabs : (2*(v:Int)-3).natAbs=Z := by rw [hz]; simp
  have hD : ((2:Int)^(v+1)+3)=(D:Int) := by simp [D]
  have ha : ((-3:Int)^t).natAbs ≤ A := by
    rw [Int.natAbs_pow]
    have hh : (-3:Int).natAbs = 3 := by decide
    rw [hh]
    exact Nat.pow_le_pow_right (by decide : 0<(3:Nat)) ht
  have hb : ((2:Int)^r).natAbs = (2:Nat)^r := by simp [Int.natAbs_pow]
  have hsmall : m.natAbs ≤ M := small_quotient_first_one v t r c m ht hr hc2 hv he
  have hf := terminal_factor v t r (2*(v:Int)-3) m hr he
  have hfactorbound := remainder_exponent_bound t r (v+1-r) m (2*(v:Int)-3)
    (by omega) hf
  rw [hZabs] at hfactorbound
  have hru : (2:Nat)^r ≤ 2*v+3*M := by omega
  have hupper := quotient_abs_bound _ _ _ _ _ A ((2:Nat)^r) D Z
    ha (by omega) hD hz he.symm
  have hmul : A*(2:Nat)^r ≤ A*(2*v+3*M) := Nat.mul_le_mul_left A hru
  have hZ : Z≤2*v+3*M := by dsimp [Z]; omega
  have htotal : D*m.natAbs ≤ M*(2*v+3*M) := by
    have hadd : A*(2*v+3*M)+Z ≤ (A+1)*(2*v+3*M) := by
      rw [Nat.add_mul]
      omega
    dsimp [M] at *
    omega
  have hA9 : 9≤A := by
    dsimp [A]
    simpa using (Nat.pow_le_pow_right (by decide : 0<(3:Nat)) hc2 : (3:Nat)^2 ≤ 3^c)
  have hlimit : M*(2*v+3*M)<D := cutoff_pow_one v A hA9 hv
  have hlt : D*m.natAbs<D := by omega
  by_cases hm : m.natAbs=0
  · exact (Int.natAbs_eq_zero).mp hm
  · have hmn : 1≤m.natAbs := by omega
    have hmulbig := Nat.mul_le_mul_left D hmn
    omega

theorem no_small_terminal_remainder_one (t r c v : Nat)
    (ht : t≤c) (hc2 : 2≤c) (hv : ((3:Nat)^c+1)≤v)
    (he : (-3:Int)^t*(2:Int)^r = 2*(v:Int)-3) : False := by
  have hv4 : 4≤v := by
    have h9 : 9≤(3:Nat)^c := by
      simpa using (Nat.pow_le_pow_right (by decide : 0<(3:Nat)) hc2 : (3:Nat)^2 ≤ 3^c)
    omega
  by_cases hr : r=0
  · subst r
    have hNat : ((-3:Int)^t).natAbs = ((2*(v:Int)-3)).natAbs := by
      have hn : (2:Int)^0 = 1 := by decide
      rw [hn] at he
      simpa using congrArg Int.natAbs he
    rw [Int.natAbs_pow] at hNat
    have hneg : (-3:Int).natAbs=3 := by decide
    rw [hneg] at hNat
    have hz : (2*(v:Int)-3)=((2*v-3:Nat):Int) := by
      rw [Int.natCast_sub (by omega : 3≤2*v)]
      omega
    rw [hz,Int.natAbs_natCast] at hNat
    have hp : (3:Nat)^t ≤ 3^c := Nat.pow_le_pow_right (by decide) ht
    have hvm : 2*v-3 > (3:Nat)^c := by omega
    omega
  · have hrpos : 1≤r := by omega
    have hmod := congrArg (fun x:Int => x%2) he
    rw [Int.mul_emod,two_pow_even r hrpos] at hmod
    have hz : (2*(v:Int)-3)%2=1 := by omega
    rw [hz] at hmod
    simp at hmod

theorem terminal_superlinear_int_two (q v K c : Nat)
    (hc2 : 2≤c) (hv : ((3:Nat)^c+1)≤v)
    (he : equationInt q v K) : c*v<K := by
  by_cases hgoal : c*v<K
  · exact hgoal
  · have hK : K≤c*v := by omega
    let t := (K+1)/(v+1)
    let r := (K+1)%(v+1)
    have hsplit : K+1=t*(v+1)+r := by
      have hh := Nat.mod_add_div (K+1) (v+1)
      dsimp [t,r]
      rw [Nat.mul_comm ((K+1)/(v+1)) (v+1)]
      omega
    have hr : r≤v := by
      have hh := Nat.mod_lt (K+1) (by omega : 0<v+1)
      dsimp [r]
      omega
    have ht : t≤c := by
      by_cases hh : t≤c
      · exact hh
      · have hgte : c+1≤t := by omega
        have hmult := Nat.mul_le_mul_right (v+1) hgte
        have hmult' : c*(v+1) < (c+1)*(v+1) :=
          Nat.mul_lt_mul_of_pos_right (by omega : c<c+1) (by omega)
        have hbound : K+1 ≤ c*(v+1) := by
          have hdist : c*(v+1)=c*v+c := by rw [Nat.mul_add]; omega
          omega
        omega
    obtain ⟨m,hm⟩ := terminal_remainder_divisibility q v K t r he hsplit
    have hm0 : m=0 := small_quotient_final_one v t r c m ht hr hc2 hv hm
    subst m
    have heq : (-3:Int)^t*(2:Int)^r=2*(v:Int)-3 := by
      omega
    exact False.elim (no_small_terminal_remainder_one t r c v ht hc2 hv heq)

/-- Strict all-slope bound from the improved cutoff v≥3^c+1 (c≥1). -/
theorem terminal_superlinear_nat_one (q v K c : Nat)
    (hc : 1≤c) (hv : ((3:Nat)^c+1)≤v)
    (he : (2:Nat)^v*(2*q+3)+v+3*(q+1)=(2:Nat)^K) : c*v<K := by
  by_cases hc1 : c=1
  · subst c
    have hK : v<K := by
      by_cases hlt : v<K
      · exact hlt
      · have hp : (2:Nat)^K ≤ (2:Nat)^v :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hm : (2:Nat)^v < (2:Nat)^v*(2*q+3) := by
          have hmult := Nat.mul_lt_mul_of_pos_left (by omega : 1<2*q+3)
            (Nat.pow_pos (by decide : 0<(2:Nat)) : 0 < (2:Nat)^v)
          simpa using hmult
        omega
    simpa using hK
  · have hc2 : 2≤c := by omega
    exact terminal_superlinear_int_two q v K c hc2 hv (source_equation_cast q v K he)

#print axioms terminal_superlinear_nat_one
end BB6.Agent48.SuperMod
