import Lean

namespace BB6.Agent48.SuperMod

private theorem dvd_pow_sub_pow (d a b : Int) (h : d ∣ a-b) (t : Nat) :
    d ∣ a^t-b^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hid : a^(t+1)-b^(t+1) = a^t*(a-b)+(a^t-b^t)*b := by
      rw [show t+1=t.succ by omega, Int.pow_succ,Int.pow_succ]
      simp [Int.mul_sub, Int.sub_mul]
      omega
    rw [hid]
    rcases h with ⟨e,he⟩
    rcases ih with ⟨f,hf⟩
    refine ⟨a^t*e+f*b, ?_⟩
    rw [he,hf]
    simp [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem denominator_pow_congruence (v t : Nat) :
    ((2:Int)^(v+1)+3) ∣ (((2:Int)^(v+1))^t - (-3:Int)^t) := by
  apply dvd_pow_sub_pow
  show ((2:Int)^(v+1)+3) ∣ ((2:Int)^(v+1))-(-3:Int)
  have h : ((2:Int)^(v+1))-(-3:Int)=(2:Int)^(v+1)+3 := by omega
  rw [h]
  exact ⟨1, by simp⟩

def equationInt (q v K : Nat) : Prop :=
  (2:Int)^K = (2:Int)^v * (2*(q:Int)+3) + (v:Int) + 3*((q:Int)+1)

theorem equation_affine_doubled (q v K : Nat) (he : equationInt q v K) :
    (2:Int)^(K+1) = ((2:Int)^(v+1)+3)*(2*(q:Int)+3)+(2*(v:Int)-3) := by
  have hK : (2:Int)^(K+1)=2*(2:Int)^K := by rw [Int.pow_succ]; omega
  have hv : (2:Int)^(v+1)=2*(2:Int)^v := by rw [Int.pow_succ]; omega
  rw [hK,hv,he]
  simp [Int.mul_add,Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

theorem terminal_remainder_divisibility (q v K t r : Nat)
    (he : equationInt q v K) (hsplit : K+1=t*(v+1)+r) :
    ((2:Int)^(v+1)+3) ∣ (((-3:Int)^t)*((2:Int)^r) -(2*(v:Int)-3)) := by
  have hpow : (2:Int)^(K+1)=((2:Int)^(v+1))^t*(2:Int)^r := by
    rw [hsplit, Nat.mul_comm t (v+1), Int.pow_add, Int.pow_mul]
  have heq := equation_affine_doubled q v K he
  rw [hpow] at heq
  obtain ⟨w, hw⟩ := denominator_pow_congruence v t
  refine ⟨(2*(q:Int)+3)-w*(2:Int)^r, ?_⟩
  have ht : ((-3:Int)^t)*(2:Int)^r -(2*(v:Int)-3) =
      ((((2:Int)^(v+1))^t*(2:Int)^r)-(2*(v:Int)-3)) -
        (((2:Int)^(v+1))^t-(-3:Int)^t)*(2:Int)^r := by
    simp [Int.sub_mul]
    omega
  rw [ht, hw]
  simp [Int.mul_sub,Int.mul_add,Int.sub_mul, Int.add_mul, Int.mul_assoc,Int.mul_comm,Int.mul_left_comm] at *
  omega

theorem source_equation_cast (q v K : Nat)
    (h : (2:Nat)^v*(2*q+3)+v+3*(q+1)=(2:Nat)^K) : equationInt q v K := by
  unfold equationInt
  have ht : (2:Nat)^K=(2:Nat)^v*(2*q+3)+v+3*(q+1) := h.symm
  exact_mod_cast ht

theorem square_le_two_pow (n : Nat) (hn : 4 ≤ n) : n*n ≤ (2:Nat)^n := by
  have h : ∀ k : Nat, (4+k)*(4+k) ≤ (2:Nat)^(4+k) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      let m := 4+k
      have hm : 3≤m := by dsimp [m]; omega
      have h3m : 3*m ≤ m*m := Nat.mul_le_mul_right m hm
      have hsquare : (m+1)*(m+1)=m*m+2*m+1 := by
        simp [Nat.add_mul, Nat.mul_add]
        omega
      have hbig : (m+1)*(m+1)≤2*(m*m) := by omega
      have hpow : (2:Nat)^(m+1)=2*(2:Nat)^m := by
        rw [Nat.pow_succ']
      have hstep : 4+(k+1)=m+1 := by dsimp [m]; omega
      rw [hstep,hpow]
      have ih' : m*m ≤ (2:Nat)^m := ih
      have hh := Nat.mul_le_mul_left 2 ih'
      omega
  have h4 : 4+(n-4)=n := by omega
  simpa only [h4] using h (n-4)

theorem quotient_abs_bound (a b d z m : Int) (A B D Z : Nat)
    (ha : a.natAbs ≤ A) (hb : b.natAbs ≤ B)
    (hd : d=(D:Int)) (hz : z=(Z:Int))
    (he : d*m=a*b-z) : D*m.natAbs ≤ A*B+Z := by
  calc
    D*m.natAbs = (d*m).natAbs := by rw [hd, Int.natAbs_mul]; simp
    _ = (a*b-z).natAbs := by rw [he]
    _ ≤ (a*b).natAbs+z.natAbs := Int.natAbs_sub_le _ _
    _ = a.natAbs*b.natAbs+Z := by rw [Int.natAbs_mul,hz]; simp
    _ ≤ A*B+Z := Nat.add_le_add_right (Nat.mul_le_mul ha hb) _

theorem quotient_small (n b D M : Nat) (hD : b < D)
    (h : D*n ≤ M*b) : n ≤ M := by
  by_cases hn : n≤M
  · exact hn
  have hn' : M+1≤n := by omega
  have h1 := Nat.mul_le_mul_right D hn'
  have h2 := Nat.mul_le_mul_left M (Nat.le_of_lt hD)
  have hdpos : 0<D := by omega
  have h3 := Nat.mul_lt_mul_of_pos_right (show M<M+1 by omega) hdpos
  have h4 : n*D ≤ M*b := by simpa only [Nat.mul_comm D n] using h
  omega

theorem minus_three_pow_odd (t : Nat) : (-3:Int)^t % 2 = 1 := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [Int.pow_succ, Int.mul_emod, ih]
    decide

theorem two_pow_even (r : Nat) (hr : 1≤r) : (2:Int)^r % 2 = 0 := by
  have hn : r=(r-1)+1 := by omega
  rw [hn,Int.pow_succ,Int.mul_emod]
  simp

theorem bracket_nonzero (t s : Nat) (hs : 1≤s) (m:Int) :
    (-3:Int)^t - (2:Int)^s*m ≠ 0 := by
  intro he
  have hm := congrArg (fun x:Int => x%2) he
  rw [Int.sub_emod,minus_three_pow_odd,Int.mul_emod,two_pow_even s hs] at hm
  simp at hm

theorem remainder_exponent_bound (t r s : Nat) (m z : Int) (hs : 1≤s)
    (hfactor : ((2:Int)^r)*(((-3:Int)^t)-(2:Int)^s*m)=z+3*m) :
    (2:Nat)^r ≤ z.natAbs+3*m.natAbs := by
  let B : Int := (-3:Int)^t-(2:Int)^s*m
  have hnonzero : B ≠ 0 := bracket_nonzero t s hs m
  have hpos : 1≤B.natAbs := by have h := Int.natAbs_pos.mpr hnonzero; omega
  have habs : ((2:Int)^r).natAbs=(2:Nat)^r := by simp [Int.natAbs_pow]
  have he : (2:Nat)^r*B.natAbs=(z+3*m).natAbs := by
    rw [←hfactor]
    simp only [Int.natAbs_mul,habs,B]
  have hfirst : (2:Nat)^r ≤ (2:Nat)^r*B.natAbs := by
    have h := Nat.mul_le_mul_left ((2:Nat)^r) hpos
    simpa using h
  have hlast : (z+3*m).natAbs ≤ z.natAbs+3*m.natAbs := by
    calc
      _ ≤ z.natAbs+(3*m).natAbs := Int.natAbs_add_le z (3*m)
      _ = z.natAbs+3*m.natAbs := by simp [Int.natAbs_mul]
  omega

theorem terminal_factor (v t r : Nat) (z m:Int) (hr : r≤v)
    (he : (-3:Int)^t*(2:Int)^r-z= ((2:Int)^(v+1)+3)*m) :
    (2:Int)^r*((-3:Int)^t - (2:Int)^(v+1-r)*m)=z+3*m := by
  have hs : v+1=(v+1-r)+r := by omega
  have hp : (2:Int)^(v+1)=(2:Int)^r*(2:Int)^(v+1-r) := by
    rw [hs,Int.pow_add]
    simp [Int.mul_comm]
  have ht : (2:Int)^r*((-3:Int)^t - (2:Int)^(v+1-r)*m)=
      (-3:Int)^t*(2:Int)^r - (2:Int)^(v+1)*m := by
    rw [hp]
    simp [Int.mul_sub,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
  rw [ht]
  have hh : ((2:Int)^(v+1)+3)*m = (2:Int)^(v+1)*m+3*m := by rw [Int.add_mul]
  rw [hh] at he
  omega

theorem cutoff_pow (v A : Nat) (hv : 4*(A+1)≤v) :
    (A+1)*(2*v+3*(A+1)) < (2:Nat)^(v+1)+3 := by
  let M := A+1
  have hApos : 0≤A := Nat.zero_le A
  have hv4 : 4≤v := by omega
  have hsq := square_le_two_pow v hv4
  have h3M : 3*M < v := by dsimp [M]; omega
  have h2v : 2*v+3*M≤3*v := by omega
  have hm := Nat.mul_le_mul_left M h2v
  have hm2 : M*(3*v) = (3*M)*v := by ac_rfl
  have hm3 := Nat.mul_lt_mul_of_pos_right h3M (by omega : 0<v)
  have hlt : M*(2*v+3*M) < v*v := by
    calc
      _ ≤ M*(3*v) := hm
      _ = (3*M)*v := hm2
      _ < v*v := hm3
  have hpow : (2:Nat)^(v+1)=2*(2:Nat)^v := by rw [Nat.pow_succ']
  change M*(2*v+3*M)<(2:Nat)^(v+1)+3
  rw [hpow]
  omega

theorem small_quotient_first (v t r c : Nat) (m:Int)
    (ht : t≤c) (hr : r≤v) (hv : 4*((3:Nat)^c+1)≤v)
    (he : (-3:Int)^t*(2:Int)^r-(2*(v:Int)-3) =
       ((2:Int)^(v+1)+3)*m) : m.natAbs ≤ (3:Nat)^c+1 := by
  let A := (3:Nat)^c
  let D := (2:Nat)^(v+1)+3
  let Z := 2*v-3
  have hApos : 0≤A := Nat.zero_le A
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

theorem small_quotient_final (v t r c : Nat) (m:Int)
    (ht : t≤c) (hr : r≤v) (hv : 4*((3:Nat)^c+1)≤v)
    (he : (-3:Int)^t*(2:Int)^r-(2*(v:Int)-3) =
       ((2:Int)^(v+1)+3)*m) : m=0 := by
  let A := (3:Nat)^c
  let M := A+1
  let Z := 2*v-3
  let D := (2:Nat)^(v+1)+3
  have hv4 : 4≤v := by
    have ha0 : 0≤A := Nat.zero_le A
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
  have hsmall : m.natAbs ≤ M := small_quotient_first v t r c m ht hr hv he
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
  have hlimit : M*(2*v+3*M)<D := cutoff_pow v A hv
  have hlt : D*m.natAbs<D := by omega
  by_cases hm : m.natAbs=0
  · exact (Int.natAbs_eq_zero).mp hm
  · have hmn : 1≤m.natAbs := by omega
    have hmulbig := Nat.mul_le_mul_left D hmn
    omega

theorem no_small_terminal_remainder (t r c v : Nat)
    (ht : t≤c) (hv : 4*((3:Nat)^c+1)≤v)
    (he : (-3:Int)^t*(2:Int)^r = 2*(v:Int)-3) : False := by
  have hv4 : 4≤v := by
    have h0 : 0≤(3:Nat)^c := Nat.zero_le _
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

theorem terminal_superlinear (q v K c : Nat)
    (hc : 1≤c) (hv : 4*((3:Nat)^c+1)≤v)
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
    have hm0 : m=0 := small_quotient_final v t r c m ht hr hv hm
    subst m
    have heq : (-3:Int)^t*(2:Int)^r=2*(v:Int)-3 := by
      omega
    exact False.elim (no_small_terminal_remainder t r c v ht hv heq)

theorem terminal_superlinear_nat (q v K c : Nat)
    (hc : 1≤c) (hv : 4*((3:Nat)^c+1)≤v)
    (he : (2:Nat)^v*(2*q+3)+v+3*(q+1)=(2:Nat)^K) :
    c*v<K := terminal_superlinear q v K c hc hv (source_equation_cast q v K he)

#print axioms terminal_remainder_divisibility
#print axioms terminal_superlinear_nat

end BB6.Agent48.SuperMod
