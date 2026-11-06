import SignedRayPeriod
set_option maxHeartbeats 0

namespace CascadeRayDepthHensel
open CascadeRayPeriod

/-- The exact depth stride for divisibility by 3^(k+1). -/
def depthPeriod (k : Nat) : Nat := 2 * 3^k

/-- The unit coefficient in 2^(2*3^k) = 1 + 3^(k+1) * depthCoeff k.
    Cubing the preceding lift preserves the coefficient modulo three. -/
def depthCoeff : Nat → Nat
  | 0 => 1
  | k+1 =>
      depthCoeff k + 3^(k+1)*(depthCoeff k)^2 +
        3^(2*k+1)*(depthCoeff k)^3

theorem depthCoeff_unit (k : Nat) : depthCoeff k % 3 ≠ 0 := by
  induction k with
  | zero => decide
  | succ k ih =>
      simp only [depthCoeff]
      have h1 : (3^(k+1)*depthCoeff k^2)%3=0 := by
        rw [Nat.mul_mod]
        simp [Nat.pow_succ]
      have h2 : (3^(2*k+1)*depthCoeff k^3)%3=0 := by
        rw [show 2*k+1=(2*k)+1 by omega, Nat.pow_succ, Nat.mul_mod]
        simp
      have hsum :
          (depthCoeff k + 3^(k+1)*depthCoeff k^2 +
            3^(2*k+1)*depthCoeff k^3)%3 = depthCoeff k%3 := by
        simp [Nat.add_mod,h1,h2]
      rw [hsum]
      exact ih

/-- All-precision binomial lift of the order of two modulo powers of three. -/
theorem pow_depth_period (k : Nat) :
    2^depthPeriod k = 1 + 3^(k+1)*depthCoeff k := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hL :
          depthPeriod (k+1) =
            depthPeriod k + depthPeriod k + depthPeriod k := by
        simp [depthPeriod,Nat.pow_succ]
        omega
      calc
        2^depthPeriod (k+1) =
            2^(depthPeriod k + depthPeriod k + depthPeriod k) := by rw [hL]
        _ = (2^depthPeriod k)*(2^depthPeriod k)*(2^depthPeriod k) := by
          rw [Nat.pow_add,Nat.pow_add]
        _ = (1+3^(k+1)*depthCoeff k)^3 := by
          rw [ih]
          simp [Nat.pow_succ,Nat.mul_assoc]
        _ = 1+3^(k+2)*depthCoeff (k+1) := by
          have hp1 : 3^(k+2)=3^(k+1)*3 := by
            rw [show k+2=(k+1)+1 by omega,Nat.pow_succ]
          have hp2 : 3^(2*k+1)=3^(k+1)*3^k := by
            rw [show 2*k+1=(k+1)+k by omega,Nat.pow_add]
          simp only [depthCoeff]
          rw [hp1,hp2]
          simp [Nat.pow_succ,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,
            Nat.mul_comm,Nat.mul_left_comm]
          omega

/-- The signed ray numerator has period 2*3^k modulo 3^(k+1),
    uniformly in both the fatal index and the depth. -/
theorem signedZ_period (n j k : Nat) :
    signedZ n (j+depthPeriod k)%(3:Int)^(k+1) =
      signedZ n j%(3:Int)^(k+1) := by
  have he : j+depthPeriod k+1=(j+1)+depthPeriod k := by omega
  have hpowNat : (2:Nat)^(j+depthPeriod k+1) =
      (2:Nat)^(j+1)*(2:Nat)^(depthPeriod k) := by
    rw [he,Nat.pow_add]
  have hpowInt : (2:Int)^(j+depthPeriod k+1) =
      (2:Int)^(j+1)*(1+(3:Int)^(k+1)*depthCoeff k) := by
    have hh := congrArg (fun x : Nat => (2:Nat)^(j+1)*x)
      (pow_depth_period k)
    have hn : (2:Nat)^(j+1)*(2:Nat)^(depthPeriod k) =
        (2:Nat)^(j+1)*(1+3^(k+1)*depthCoeff k) := hh
    rw [←hpowNat] at hn
    exact_mod_cast hn
  have hz : signedZ n (j+depthPeriod k) =
      signedZ n j-(3:Int)^(k+1)*
        ((2*n+3:Int)*(2:Int)^(j+1)*depthCoeff k) := by
    dsimp [signedZ]
    rw [hpowInt]
    push_cast
    simp [Int.mul_add,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
    omega
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
  apply Int.emod_eq_zero_of_dvd
  refine ⟨-((2*n+3:Int)*(2:Int)^(j+1)*depthCoeff k),?_⟩
  rw [hz]
  have hneg :
      -((3:Int)^(k+1)*((2*n+3:Int)*(2:Int)^(j+1)*depthCoeff k)) =
        (3:Int)^(k+1)*-((2*n+3:Int)*(2:Int)^(j+1)*depthCoeff k) := by
    exact Int.neg_mul_eq_mul_neg _ _
  rw [Int.sub_eq_add_neg,Int.sub_eq_add_neg,hneg]
  omega

/-- Periodicity under every whole number of depth strides. -/
theorem signedZ_period_mul (n j k m : Nat) :
    signedZ n (j+m*depthPeriod k)%(3:Int)^(k+1) =
      signedZ n j%(3:Int)^(k+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hidx :
          j+(m+1)*depthPeriod k =
            (j+m*depthPeriod k)+depthPeriod k := by
        rw [Nat.succ_mul]
        omega
      rw [hidx]
      rw [signedZ_period n (j+m*depthPeriod k) k]
      exact ih

private theorem pow_two_mod_three (m : Nat) :
    2^m%3 = if m%2=0 then 1 else 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [Nat.pow_succ,Nat.mul_mod]
      by_cases hm : m%2=0
      · have hs : (m+1)%2=1 := by omega
        rw [ih,if_pos hm]
        simp [hs]
      · have hs : (m+1)%2=0 := by omega
        rw [ih,if_neg hm]
        simp [hs]

/-- In the surviving fatal-index sectors, 2^n and n have the same
    nonzero residue modulo three. -/
theorem pow_sector_mod_three (n : Nat)
    (hn : n%6=4 ∨ n%6=5) : 2^n%3=n%3 := by
  rcases hn with h|h
  · have h2 : n%2=0 := by omega
    have h3 : n%3=1 := by omega
    rw [pow_two_mod_three,h2]
    simp [h3]
  · have h2 : n%2=1 := by omega
    have h3 : n%3=2 := by omega
    rw [pow_two_mod_three,h2]
    simp [h3]

private theorem signedZ_zero_mod_three (n : Nat)
    (hn : n%6=4 ∨ n%6=5) : signedZ n 0%3=0 := by
  have hp := pow_sector_mod_three n hn
  have hpi : ((2:Int)^n)%3=(n:Int)%3 := by exact_mod_cast hp
  dsimp [signedZ]
  push_cast
  omega

private theorem signedZ_one_mod_three_ne (n : Nat)
    (hn : n%6=4 ∨ n%6=5) : signedZ n 1%3≠0 := by
  have hp := pow_sector_mod_three n hn
  have hpi : ((2:Int)^n)%3=(n:Int)%3 := by exact_mod_cast hp
  dsimp [signedZ]
  push_cast
  omega

/-- The initial mod-three zero occurs exactly at even ray depths. -/
theorem signedZ_mod_three_even_iff (n j : Nat)
    (hn : n%6=4 ∨ n%6=5) :
    signedZ n j%3=0 ↔ j%2=0 := by
  by_cases hj : j%2=0
  · have hsplit : j=2*(j/2) := by omega
    rw [hsplit]
    have hper := signedZ_period_mul n 0 0 (j/2)
    simpa [depthPeriod,Nat.mul_comm] using
      (hper.trans (signedZ_zero_mod_three n hn))
  · have hj1 : j%2=1 := by omega
    have hsplit : j=1+2*(j/2) := by omega
    rw [hsplit]
    have hper0 := signedZ_period_mul n 1 0 (j/2)
    have hper : signedZ n (1+2*(j/2))%3=signedZ n 1%3 := by
      simpa [depthPeriod,Nat.mul_comm] using hper0
    have hone := signedZ_one_mod_three_ne n hn
    constructor
    · intro hz
      have hz1 : signedZ n 1%3=0 := by rw [←hper]; exact hz
      exact False.elim (hone hz1)
    · intro hz
      omega


/-- The quadratic error in the three-digit shift expansion. -/
def depthError (k t : Nat) : Nat :=
  if t=2 then 3^k*(depthCoeff k)^2 else 0

/-- The exact three-candidate expansion of a depth-period shift. -/
theorem pow_period_digit (k t : Nat) (ht:t<3) :
    2^(t*depthPeriod k) =
      1+t*3^(k+1)*depthCoeff k+3^(k+2)*depthError k t := by
  have htcase:t=0 ∨ t=1 ∨ t=2 := by omega
  rcases htcase with h|h|h
  · subst t
    simp [depthPeriod,depthError]
  · subst t
    simpa [depthPeriod,depthError] using pow_depth_period k
  · subst t
    have htwo:2^(2*depthPeriod k)=(2^depthPeriod k)^2:=by
      rw [show 2*depthPeriod k=depthPeriod k+depthPeriod k by omega,
        Nat.pow_add,Nat.pow_two]
    rw [htwo,pow_depth_period]
    simp [depthError,Nat.pow_succ,Nat.mul_add,
      Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    omega

/-- Modulo the next power of three, the three depth candidates differ
    by the expected linear digit term. -/
theorem signedZ_shift_digit_mod (n b k t : Nat) (ht:t<3) :
    signedZ n (b+t*depthPeriod k)%(3:Int)^(k+2)=
      (signedZ n b-(3:Int)^(k+1)*
        ((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k*t))%(3:Int)^(k+2) := by
  have hidx:b+t*depthPeriod k+1=(b+1)+t*depthPeriod k:=by omega
  have hpowNat:(2:Nat)^(b+t*depthPeriod k+1)=
      (2:Nat)^(b+1)*(2:Nat)^(t*depthPeriod k):=by
    rw [hidx,Nat.pow_add]
  have hpowInt:(2:Int)^(b+t*depthPeriod k+1)=
      (2:Int)^(b+1)*(1+t*(3:Int)^(k+1)*depthCoeff k+
        (3:Int)^(k+2)*depthError k t):=by
    have hh:=congrArg (fun x:Nat=>(2:Nat)^(b+1)*x) (pow_period_digit k t ht)
    have hn:(2:Nat)^(b+1)*(2:Nat)^(t*depthPeriod k)=
        (2:Nat)^(b+1)*(1+t*3^(k+1)*depthCoeff k+3^(k+2)*depthError k t):=hh
    rw [←hpowNat] at hn
    exact_mod_cast hn
  have hz:signedZ n (b+t*depthPeriod k)=
      signedZ n b-(3:Int)^(k+1)*
        ((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k*t)-
        (3:Int)^(k+2)*((2*n+3:Int)*(2:Int)^(b+1)*depthError k t):=by
    dsimp [signedZ]
    rw [hpowInt]
    push_cast
    simp [Int.mul_add,Int.add_mul,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
    omega
  apply (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
  apply Int.emod_eq_zero_of_dvd
  refine ⟨-((2*n+3:Int)*(2:Int)^(b+1)*depthError k t),?_⟩
  have hneg2 : (3:Int)^(k+2)*
      (-((2*n+3:Int)*(2:Int)^(b+1)*depthError k t)) =
      -((3:Int)^(k+2)*((2*n+3:Int)*(2:Int)^(b+1)*depthError k t)) := by
    exact Int.mul_neg _ _
  rw [hz,hneg2]
  omega

/-- Divisibility at precision k+2 is reduced to one linear congruence
    for the next ternary digit. -/
theorem signedZ_lift_criterion (n b k t:Nat) (ht:t<3)
    (hbase:(3:Int)^(k+1)∣signedZ n b) :
    (3:Int)^(k+2)∣signedZ n (b+t*depthPeriod k) ↔
      (3:Int)∣(signedZ n b/(3:Int)^(k+1)-
        ((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)*t) := by
  let m:(Int):=(3:Int)^(k+1)
  have hmne:m≠0:=by
    change (3:Int)^(k+1)≠0
    exact_mod_cast (Nat.ne_of_gt (Nat.pow_pos (by decide : 0<3)))
  have hM:(3:Int)^(k+2)=(3:Int)*m:=by
    dsimp [m]
    rw [show k+2=(k+1)+1 by omega,Int.pow_succ]
    exact Int.mul_comm _ _
  have hmod:=signedZ_shift_digit_mod n b k t ht
  have hmod' : signedZ n (b+t*depthPeriod k)%(3:Int)^(k+2)=
      (signedZ n b-m*((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k*t))%(3:Int)^(k+2) := by
    simpa [m,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm] using hmod
  have hdiviff : (3:Int)^(k+2)∣signedZ n (b+t*depthPeriod k) ↔
      (3:Int)^(k+2)∣(signedZ n b-m*((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k*t)) := by
    rw [Int.dvd_iff_emod_eq_zero,Int.dvd_iff_emod_eq_zero,hmod']
  have hquot : m*(signedZ n b/m)=signedZ n b :=
    Int.mul_ediv_cancel_of_dvd hbase
  have hfactor : signedZ n b-m*((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k*t)=
      m*(signedZ n b/m-((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)*t) := by
    calc
      _ = m*(signedZ n b/m)-m*((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k*t) := by
        exact congrArg (fun x:Int => x-m*((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k*t)) hquot
      _ = m*(signedZ n b/m-((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k*t)) := by
        rw [Int.mul_sub]
  have hcomm:(3:Int)*m=m*3:=Int.mul_comm _ _
  rw [hdiviff,hfactor,hM,hcomm]
  exact Int.mul_dvd_mul_iff_left hmne

/-- The unique digit solving q-a*t = 0 modulo three, for a unit a. -/
def henselDigit (q a:Int):Nat :=
  Int.toNat (((q%3)*(a%3))%3)

theorem henselDigit_lt (q a:Int):henselDigit q a<3:=by
  have hnon:0≤((q%3)*(a%3))%3:=Int.emod_nonneg _ (by decide)
  have hcast:(henselDigit q a:Int)=((q%3)*(a%3))%3:=
    Int.toNat_of_nonneg hnon
  have hlt:((q%3)*(a%3))%3<3:=Int.emod_lt_of_pos _ (by decide)
  have hlt' : (henselDigit q a:Int)<3:=by rw [hcast]; exact hlt
  exact_mod_cast hlt'

theorem henselDigit_mod (q a:Int) (ha:a%3≠0) :
    (a*(henselDigit q a:Int))%3=q%3:=by
  have hA : a%3=1 ∨ a%3=2 := by
    have hnon:0≤a%3:=Int.emod_nonneg _ (by decide)
    have hlt:a%3<3:=Int.emod_lt_of_pos _ (by decide)
    by_cases hzero:a%3=0
    · omega
    · omega
  have hnon:0≤((q%3)*(a%3))%3:=Int.emod_nonneg _ (by decide)
  have htcast:(henselDigit q a:Int)=((q%3)*(a%3))%3:=
    Int.toNat_of_nonneg hnon
  have hqnon:0≤q%3:=Int.emod_nonneg _ (by decide)
  have hqlt:q%3<3:=Int.emod_lt_of_pos _ (by decide)
  rw [Int.mul_emod,htcast]
  rcases hA with h|h
  · rw [h]
    omega
  · rw [h]
    omega

theorem henselDigit_div (q a:Int) (ha:a%3≠0) (t:Nat)
    (ht:t<3) (hdiv:(3:Int)∣q-a*t) :
    t=henselDigit q a:=by
  have hA : a%3=1 ∨ a%3=2 := by
    have hnon:0≤a%3:=Int.emod_nonneg _ (by decide)
    have hlt:a%3<3:=Int.emod_lt_of_pos _ (by decide)
    omega
  have hzero:(q-a*t)%3=0:=Int.dvd_iff_emod_eq_zero.mp hdiv
  have hqmod : q%3=(a*(t:Int))%3 :=
    (Int.emod_eq_emod_iff_emod_sub_eq_zero).2 hzero
  have htarget : q%3=(a*(henselDigit q a:Int))%3 :=
    (henselDigit_mod q a ha).symm
  have hmul:(a*(t:Int))%3=(a*(henselDigit q a:Int))%3 :=
    hqmod.symm.trans htarget
  rcases hA with h|h
  · have hteq:(t:Int)%3=(henselDigit q a:Int)%3 := by
      simpa [Int.mul_emod,h] using hmul
    have htr : (t:Int)%3=t:=by
      have : (t:Int)≥0:=by omega
      have : (t:Int)<3:=by exact_mod_cast ht
      omega
    have hdr : (henselDigit q a:Int)%3=henselDigit q a:=by
      have : (henselDigit q a:Int)≥0:=by omega
      have : (henselDigit q a:Int)<3:=by exact_mod_cast henselDigit_lt q a
      omega
    exact_mod_cast (by omega)
  · have hteq:(2*(t:Int))%3=(2*(henselDigit q a:Int))%3:=by
      simpa [Int.mul_emod,h] using hmul
    have htr : (t:Int)%3=t:=by
      have : (t:Int)≥0:=by omega
      have : (t:Int)<3:=by exact_mod_cast ht
      omega
    have hdr : (henselDigit q a:Int)%3=henselDigit q a:=by
      have : (henselDigit q a:Int)≥0:=by omega
      have : (henselDigit q a:Int)<3:=by exact_mod_cast henselDigit_lt q a
      omega
    have hsmall : t=henselDigit q a:=by omega
    exact hsmall

theorem henselDigit_divides (q a:Int) (ha:a%3≠0) :
    (3:Int)∣q-a*(henselDigit q a:Int):=by
  have hmod:(a*(henselDigit q a:Int))%3=q%3:=henselDigit_mod q a ha
  have hzero:(q-a*(henselDigit q a:Int))%3=0:=
    (Int.emod_eq_emod_iff_emod_sub_eq_zero).1 hmod.symm
  exact Int.dvd_iff_emod_eq_zero.mpr hzero

private theorem int_two_pow_mod_three_ne (b:Nat):
    ((2:Int)^(b+1))%3≠0:=by
  induction b with
  | zero => decide
  | succ b ih =>
    have hp:(2:Int)^(b+2)=(2:Int)^(b+1)*2:=by
      rw [show b+2=(b+1)+1 by omega,Int.pow_succ]
    rw [hp,Int.mul_emod]
    have hrem:((2:Int)^(b+1))%3=1 ∨ ((2:Int)^(b+1))%3=2:=by
      have hnon:0≤((2:Int)^(b+1))%3:=Int.emod_nonneg _ (by decide)
      have hlt:((2:Int)^(b+1))%3<3:=Int.emod_lt_of_pos _ (by decide)
      omega
    rcases hrem with h|h <;> rw [h] <;> decide

/-- The coefficient of the lift digit is always a unit modulo three
    in the surviving n mod 6 sectors. -/
theorem rayCoeff_unit (n b k:Nat) (hn:n%6=4 ∨ n%6=5):
    ((2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k)%3≠0:=by
  have hn3:n%3=1 ∨ n%3=2:=by rcases hn with h|h <;> omega
  have hfirst:((2*n+3:Int)%3)=1 ∨ (2*n+3:Int)%3=2:=by
    rcases hn3 with h|h
    · have hnI:(n:Int)%3=1:=by exact_mod_cast h
      have hh:(2*n+3:Int)%3=2:=by omega
      exact Or.inr hh
    · have hnI:(n:Int)%3=2:=by exact_mod_cast h
      have hh:(2*n+3:Int)%3=1:=by omega
      exact Or.inl hh
  have hsecond:((2:Int)^(b+1))%3=1 ∨ ((2:Int)^(b+1))%3=2:=by
    have hnon:0≤((2:Int)^(b+1))%3:=Int.emod_nonneg _ (by decide)
    have hlt:((2:Int)^(b+1))%3<3:=Int.emod_lt_of_pos _ (by decide)
    have hne:=int_two_pow_mod_three_ne b
    omega
  have hthird:((depthCoeff k:Int)%3)=1 ∨ ((depthCoeff k:Int)%3)=2:=by
    have hcast:((depthCoeff k:Int)%3)=((depthCoeff k%3:Int)):=by
      simpa using (Int.natCast_emod (depthCoeff k) 3).symm
    rw [hcast]
    have hnon:0≤depthCoeff k%3:=Nat.zero_le _
    have hlt:depthCoeff k%3<3:=Nat.mod_lt _ (by decide)
    have hne:=depthCoeff_unit k
    omega
  rcases hfirst with h1|h1 <;> rcases hsecond with h2|h2 <;>
    rcases hthird with h3|h3 <;>
    simp [Int.mul_emod,h1,h2,h3]

/-- For every n in the surviving sectors and every already-divisible
    depth b, exactly one of the three next packets lifts divisibility
    from 3^(k+1) to 3^(k+2). This is the local Hensel step. -/
theorem signedZ_unique_lift (n b k:Nat)
    (hn:n%6=4 ∨ n%6=5)
    (hbase:(3:Int)^(k+1)∣signedZ n b):
    ∃ t:Nat, t<3 ∧ (3:Int)^(k+2)∣signedZ n (b+t*depthPeriod k) ∧
      ∀ t', t'<3 ∧ (3:Int)^(k+2)∣signedZ n (b+t'*depthPeriod k) → t'=t:=by
  let a:(Int):=(2*n+3:Int)*(2:Int)^(b+1)*depthCoeff k
  let q:(Int):=signedZ n b/(3:Int)^(k+1)
  have ha:a%3≠0:=by simpa [a] using rayCoeff_unit n b k hn
  let t:=henselDigit q a
  have ht:t<3:=by exact henselDigit_lt q a
  have hdiv:(3:Int)∣q-a*t:=by
    simpa [t,q,a] using henselDigit_divides q a ha
  have hcrit:=signedZ_lift_criterion n b k t ht hbase
  have hgood:(3:Int)^(k+2)∣signedZ n (b+t*depthPeriod k):=
    hcrit.mpr (by simpa [q,a] using hdiv)
  refine ⟨t,ht,hgood,?_⟩
  intro t' ht'
  have hcrit' := signedZ_lift_criterion n b k t' ht'.1 hbase
  have hdiv':(3:Int)∣q-a*t':=by
    exact hcrit'.mp ht'.2
  have heq:t'=t:=by
    simpa [t,q,a] using henselDigit_div q a ha t' ht'.1 hdiv'
  exact heq

#print axioms depthCoeff_unit
#print axioms pow_depth_period
#print axioms signedZ_period
#print axioms signedZ_period_mul
#print axioms signedZ_mod_three_even_iff
#print axioms signedZ_unique_lift
end CascadeRayDepthHensel
