import Std

namespace CascadeCylinder

def gate (n : Nat) : Int := 8*2^n - 2*(n:Int) - 3

/-- One extra ternary digit in the exponent of 4 supplies one extra
    digit of divisibility in the difference of powers. -/
theorem pow_two_lift (s : Nat) : ∃ z : Int, (2:Int)^(2*3^s) = 1+3^(s+1)*z := by
  induction s with
  | zero => exact ⟨1,by decide⟩
  | succ s ih =>
    obtain ⟨z,hz⟩ := ih
    refine ⟨z+3^(s+1)*z*z+3^(2*s+1)*z*z*z,?_⟩
    rw [Nat.pow_succ,show 2*(3^s*3)=(2*3^s)*3 by ac_rfl,Int.pow_mul,hz]
    have h1 : (3:Int)^(s+1)=3^s*3 := Int.pow_succ ..
    have h2 : (3:Int)^(s+1+1)=3^(s+1)*3 := Int.pow_succ ..
    have h3 : (3:Int)^(2*s+1)=3^s*3^s*3 := by
      rw [show 2*s+1=s+s+1 by omega,Int.pow_succ,Int.pow_add]
    rw [h2,h3,h1]
    grind

/-- Any nonnegative multiple of the lift stride preserves the
    higher-precision exponential residue. -/
theorem pow_two_lift_mul (s t : Nat) :
    ∃ z : Int, (2:Int)^(2*3^s*t)=1+3^(s+1)*z := by
  obtain ⟨z,hz⟩ := pow_two_lift s
  induction t with
  | zero => exact ⟨0,by simp⟩
  | succ t ih =>
    obtain ⟨w,hw⟩ := ih
    refine ⟨w+z+3^(s+1)*w*z,?_⟩
    rw [Nat.mul_succ,Int.pow_add,hw,hz]
    grind

/-- Strong exact quotient form of the gate Hensel shift. -/
theorem gate_shift (n s t : Nat) :
    ∃ z : Int, gate (n+2*3^s*t) = gate n - 4*3^s*(t:Int)+3^(s+1)*z := by
  obtain ⟨w,hw⟩ := pow_two_lift_mul s t
  refine ⟨8*2^n*w,?_⟩
  unfold gate
  rw [Int.pow_add,hw]
  simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow]
  grind

/-- A ternary digit makes the shifted quotient agree with any
    requested next ternary digit. -/
theorem gate_digit (n s : Nat) (q : Int) (hn : gate n=3^s*q)
    (target : Int) : ∃ t : Nat, t<3 ∧
      ∃ z : Int, gate (n+2*3^s*t)=3^s*target+3^(s+1)*z := by
  let t := ((q-target)%3).toNat
  have ht : (t:Int)=(q-target)%3 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have hlt : t<3 := by
    have h := Int.emod_lt_of_pos (q-target) (by decide : (0:Int)<3)
    omega
  obtain ⟨z,hz⟩ := gate_shift n s t
  refine ⟨t,hlt,z+(q-target)/3-(t:Int),?_⟩
  rw [hz,hn,Int.pow_succ]
  have hm : q-target=3*((q-target)/3)+(t:Int) := by omega
  grind

/-- A unit step modulo three can attain the next requested ternary digit. -/
theorem unit_digit (z : Int) (c : Nat) (hc : (c:Int)%3≠0) :
    ∃ t : Nat, t<3 ∧ ∃ w : Int, z-4*(c:Int)*(t:Int)=3*w := by
  have hc' : (c:Int)%3=1 ∨ (c:Int)%3=2 := by omega
  have hz : z%3=0 ∨ z%3=1 ∨ z%3=2 := by omega
  have hr : ∃ t : Nat, t<3 ∧ (z-4*(c:Int)*(t:Int))%3=0 := by
    rcases hc' with h1|h2 <;> rcases hz with h0|h0|h0
    · exact ⟨0,by decide,by omega⟩
    · exact ⟨1,by decide,by omega⟩
    · exact ⟨2,by decide,by omega⟩
    · exact ⟨0,by decide,by omega⟩
    · exact ⟨2,by decide,by omega⟩
    · exact ⟨1,by decide,by omega⟩
  obtain ⟨t,ht,hm⟩ := hr
  obtain ⟨w,hw⟩ := (Int.dvd_iff_emod_eq_zero).2 hm
  exact ⟨t,ht,w,hw⟩

/-- The full quotient-tuning lemma along a progression whose stride is
    2*3^a*c with c a ternary unit.  No finite precision cutoff. -/
theorem gate_quotient_tune (n a c e : Nat) (q target : Int)
    (hn : gate n=3^a*q) (hc : (c:Int)%3≠0) :
    ∃ t : Nat, t<3^e ∧ ∃ z : Int,
      gate (n+2*3^a*c*t)=3^a*(target+3^e*z) := by
  induction e with
  | zero => exact ⟨0,by decide,q-target,by simp [hn,show target+(q-target)=q by omega]⟩
  | succ e ih =>
    obtain ⟨t,ht,z,hz⟩ := ih
    obtain ⟨d,hd,v,hv⟩ := unit_digit z c hc
    obtain ⟨w,hw⟩ := gate_shift (n+2*3^a*c*t) (a+e) (c*d)
    refine ⟨t+3^e*d,?_,v+w,?_⟩
    · have hm := Nat.mul_le_mul_left (3^e) (show d≤2 by omega)
      rw [Nat.pow_succ]
      omega
    · have he : n+2*3^a*c*(t+3^e*d)=(n+2*3^a*c*t)+2*3^(a+e)*(c*d) := by
        rw [Nat.pow_add]
        grind
      rw [he,hw,hz,Int.pow_succ,Int.pow_add]
      simp only [Int.natCast_mul]
      grind

/-- Two gate values divisible at the next ternary precision cannot be
    separated by a nonzero next ternary digit. -/
theorem gate_lift_reflect (n s t : Nat)
    (hn : (3:Int)^(s+1) ∣ gate n)
    (hm : (3:Int)^(s+1) ∣ gate (n+2*3^s*t)) : t%3=0 := by
  obtain ⟨u,hu⟩ := hn
  obtain ⟨v,hv⟩ := hm
  obtain ⟨z,hz⟩ := gate_shift n s t
  rw [hu,hv,Int.pow_succ] at hz
  have he : (3:Int)^s*(3*v-3*u+4*(t:Int)-3*z)=0 := by grind
  have hne : (3:Int)^s≠0 := by
    have hpos : (0:Int)<3^s := Int.pow_pos (by decide)
    omega
  have he' := (Int.mul_eq_zero.mp he).resolve_left hne
  omega

private theorem ordered_lift (n m s : Nat) (hle : n≤m)
    (hmod : n%(2*3^s)=m%(2*3^s))
    (hn : (3:Int)^(s+1) ∣ gate n) (hm : (3:Int)^(s+1) ∣ gate m) :
    n%(2*3^(s+1))=m%(2*3^(s+1)) := by
  let p := 2*3^s
  let t := m/p-n/p
  have ht : n/p+t=m/p := by
    have h := Nat.div_le_div_right (c:=p) hle
    dsimp [t]
    omega
  have hnm : m=n+p*t := by
    have h1 := Nat.mod_add_div n p
    have h2 := Nat.mod_add_div m p
    change n%p=m%p at hmod
    have h3 : p*(n/p+t)=p*(m/p) := congrArg (p*·) ht
    rw [Nat.mul_add] at h3
    omega
  have hnm' : m=n+2*3^s*t := hnm
  rw [hnm'] at hm
  have hdiv := gate_lift_reflect n s t hn hm
  obtain ⟨v,hv⟩ := (Nat.dvd_iff_mod_eq_zero).2 hdiv
  have hnm'' : m=n+(2*3^(s+1))*v := by
    rw [hnm',hv,Nat.pow_succ]
    grind
  rw [hnm'',Nat.add_mul_mod_self_left]

/-- The parity and gate divisibility determine the full residue modulo
    2*3^a uniquely, for every precision a. -/
theorem gate_root_unique (a n m : Nat) (hpar : n%2=m%2)
    (hn : (3:Int)^a ∣ gate n) (hm : (3:Int)^a ∣ gate m) :
    n%(2*3^a)=m%(2*3^a) := by
  induction a with
  | zero => simpa using hpar
  | succ s ih =>
    have hdiv : (3:Int)^s ∣ (3:Int)^(s+1) := by
      rw [Int.pow_succ]
      exact Int.dvd_mul_right ..
    have hmod := ih (Int.dvd_trans hdiv hn) (Int.dvd_trans hdiv hm)
    by_cases hle : n≤m
    · exact ordered_lift n m s hle hmod hn hm
    · exact (ordered_lift m n s (by omega) hmod.symm hm hn).symm

/-- Every parity has a representative root in the fundamental period. -/
theorem gate_root_exists (a e : Nat) (he : e<2) :
    ∃ n : Nat, n<2*3^a ∧ n%2=e ∧ (3:Int)^a ∣ gate n := by
  obtain ⟨t,ht,z,hz⟩ := gate_quotient_tune e 0 1 a (gate e) 0 (by simp) (by decide)
  refine ⟨e+2*t,by omega,by omega,z,?_⟩
  simpa using hz

/-- Exact residue-class characterization, in both directions. -/
theorem gate_root_iff (a root n : Nat) (hr : root<2*3^a)
    (hroot : (3:Int)^a ∣ gate root) (hpar : n%2=root%2) :
    (3:Int)^a ∣ gate n ↔ n%(2*3^a)=root := by
  constructor
  · intro hn
    rw [gate_root_unique a n root hpar hn hroot,Nat.mod_eq_of_lt hr]
  · intro hn
    have he := Nat.mod_add_div n (2*3^a)
    rw [hn] at he
    obtain ⟨z,hz⟩ := gate_shift root a (n/(2*3^a))
    rw [he] at hz
    obtain ⟨q,hq⟩ := hroot
    refine ⟨q-4*((n/(2*3^a):Nat):Int)+3*z,?_⟩
    rw [hz,hq,Int.pow_succ]
    grind

/-- The even-parity gate root lies in the authentic n=4 mod 6 sector
    at every positive ternary precision. -/
theorem gate_even_sector (n a : Nat) (ha : 0<a) (he : n%2=0)
    (hr : (3:Int)^a ∣ gate n) : n%6=4 := by
  have hd : (3:Int) ∣ (3:Int)^a := by
    cases a with
    | zero => omega
    | succ a => rw [Int.pow_succ]; exact Int.dvd_mul_left ..
  obtain ⟨z,hz⟩ := Int.dvd_trans hd hr
  have hn : n=2*(n/2) := by omega
  obtain ⟨w,hw⟩ := pow_two_lift_mul 0 (n/2)
  simp at hw
  rw [←hn] at hw
  unfold gate at hz
  rw [hw] at hz
  omega

#print axioms gate_shift
#print axioms gate_quotient_tune
#print axioms gate_root_unique
#print axioms gate_root_exists
#print axioms gate_root_iff
#print axioms gate_even_sector
end CascadeCylinder
