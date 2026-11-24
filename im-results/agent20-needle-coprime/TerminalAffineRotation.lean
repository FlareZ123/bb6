import CancellationRotationBound

namespace NeedleRotation.TerminalAffine
open NeedleRotation

/-- A sharper two-term alternative for an arbitrary odd correction. This
is a bound on divisibility, independent of any machine model. -/
theorem two_term_cancellation (n m H : Nat) (C : Int)
    (hm : 0<m) (hH : 0<H) (hc : C%2=1) (hC : C.natAbs<2^H)
    (hsize : H+2*(n/m)+2≤m)
    (hd : denominator m ∣ (2:Int)^n+C) :
    n%m=0 ∧ C= -(-3:Int)^(n/m) := by
  let k:=n/m
  let t:=n%m
  have ht : t<m := Nat.mod_lt _ hm
  have hnt : n=m*k+t := (Nat.div_add_mod n m).symm
  have hpow3 (j : Nat) : (3:Nat)^j≤2^(2*j) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by decide : 3≤2^2) _
  have two_even (z : Nat) (hz : 0<z) : ((2:Int)^z)%2=0 := by
    obtain ⟨i,rfl⟩ : ∃ i : Nat, z=i+1 := ⟨z-1,by omega⟩
    rw [Int.pow_succ,Int.mul_emod]
    simp
  have hDabs : (denominator m).natAbs=2^m+3 := by
    simp [denominator, Int.natAbs_pow, Int.natAbs_add_of_nonneg, Int.pow_nonneg]
  have hD : denominator m ∣ (-3:Int)^k*2^t+C := by
    have h := rotated_divisibility m 0 [(1,n),(C,0)] (by simpa [value] using hd)
    simpa [rotate,rotateTerm,value,k,t] using h
  by_cases hlo : t≤H
  · have hpow : (3:Nat)^k*2^t≤2^(m-2) := by
      calc
        3^k*2^t ≤ 2^(2*k)*2^t := Nat.mul_le_mul_right _ (hpow3 k)
        _ = 2^(2*k+t) := (Nat.pow_add 2 _ _).symm
        _ ≤ 2^(m-2) := Nat.pow_le_pow_right (by decide) (by dsimp [k] at *; omega)
    have hcsmall : C.natAbs<2^(m-2) := Nat.lt_of_lt_of_le hC (Nat.pow_le_pow_right (by decide) (by omega))
    have habs := Int.natAbs_add_le ((-3:Int)^k*2^t) C
    simp only [Int.natAbs_mul, Int.natAbs_pow] at habs
    change ((-3:Int)^k*2^t+C).natAbs≤3^k*2^t+C.natAbs at habs
    have h2 : 2^(m-2)+2^(m-2)≤(2:Nat)^m := by
      have he : m-2+1≤m := by omega
      have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) he
      rw [Nat.pow_succ] at hp
      omega
    have hz : (-3:Int)^k*2^t+C=0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hD (by rw [hDabs]; omega)
    have ht0 : t=0 := by
      by_cases h : t=0
      · exact h
      have hmod := congrArg (fun x : Int => x%2) hz
      rw [Int.add_emod,Int.mul_emod, two_even t (by omega), hc] at hmod
      simp at hmod
    rw [ht0,Int.pow_zero,Int.mul_one] at hz
    exact ⟨ht0,by change C = -(-3:Int)^k; omega⟩
  · let h:=m-t
    have hh : h<m := by dsimp [h]; omega
    have hhpos : 0<h := by dsimp [h]; omega
    have he : n+h=m*(k+1) := by rw [hnt]; dsimp [h]; rw [Nat.mul_add]; omega
    have hquo : (n+h)/m=k+1 := by rw [he,Nat.mul_div_cancel_left _ hm]
    have hrem : (n+h)%m=0 := by rw [he,Nat.mul_mod_right]
    have hd2 : denominator m ∣ (-3:Int)^(k+1)+C*2^h := by
      have hx := rotated_divisibility m h [(1,n),(C,0)] (by simpa [value] using hd)
      simpa [rotate,rotateTerm,value,hquo,hrem,Nat.div_eq_of_lt hh,Nat.mod_eq_of_lt hh] using hx
    have hP : (3:Nat)^(k+1)≤2^(m-1) := Nat.le_trans (hpow3 _) (Nat.pow_le_pow_right (by decide) (by dsimp [k] at *; omega))
    have hCP : C.natAbs*2^h<2^(m-1) := by
      calc
        C.natAbs*2^h < 2^H*2^h := Nat.mul_lt_mul_of_pos_right hC (Nat.two_pow_pos _)
        _=2^(H+h) := (Nat.pow_add 2 _ _).symm
        _≤2^(m-1) := Nat.pow_le_pow_right (by decide) (by dsimp [h]; omega)
    have habs := Int.natAbs_add_le ((-3:Int)^(k+1)) (C*2^h)
    simp only [Int.natAbs_pow,Int.natAbs_mul] at habs
    change ((-3:Int)^(k+1)+C*2^h).natAbs≤3^(k+1)+C.natAbs*2^h at habs
    have h2 : 2^(m-1)+2^(m-1)=(2:Nat)^m := by
      have heq : m-1+1=m := by omega
      have hp : 2^(m-1+1)=(2:Nat)^(m-1)*2 := Nat.pow_succ 2 _
      rw [heq] at hp
      omega
    have hz : (-3:Int)^(k+1)+C*2^h=0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd2 (by rw [hDabs]; omega)
    have hmod := congrArg (fun x : Int => x%2) hz
    rw [Int.add_emod,odd_neg_three_pow,Int.mul_emod,two_even h hhpos] at hmod
    simp at hmod

/-- If exact signed-power cancellation is absent, m lies in a quadratic
range with linear dependence on the coefficient bit length. -/
theorem two_term_square_or_cancel (n m H : Nat) (C : Int)
    (hm : 0<m) (hH : 0<H) (hc : C%2=1) (hC : C.natAbs<2^H)
    (hd : denominator m ∣ (2:Int)^n+C) :
    m*m < (H+2)*m+2*n ∨ (n%m=0 ∧ C= -(-3:Int)^(n/m)) := by
  by_cases hs : H+2*(n/m)+2≤m
  · exact Or.inr (two_term_cancellation n m H C hm hH hc hC hs hd)
  · left
    have ht := Nat.mul_lt_mul_of_pos_right (show m<H+2*(n/m)+2 by omega) hm
    have hn := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self n m)
    rw [←Nat.mul_assoc] at hn
    have he : (H+2*(n/m)+2)*m=(H+2)*m+(2*(n/m))*m := by simp [Nat.add_mul]; omega
    rw [he] at ht
    omega

/-- An exact shifted counter with a compact terminal-power affine form.
The sign of d is unrestricted; denominators are positive and odd. -/
def Form (n L b : Nat) (d : Int) : Prop :=
  0<L ∧ L%2=1 ∧ d%2=0 ∧ 2*(L:Int)*(b:Int)=(2:Int)^n+d

theorem root_form (K : Nat) : Form (K+1) 1 (2^K) 0 := by
  simp [Form, Int.pow_succ, Int.mul_comm]

/-- Every legal inverse step retains a compact two-term numerator. -/
theorem form_parent (n L b p q w : Nat) (d : Int)
    (hf : Form n L b d) (hb : Cancellation.parentEq b q w)
    (hp : p=2^w*(2*q+3)) :
    Form (n+w+1) (L*(2^(w+1)+3)) p
      ((2:Int)^(w+1)*(d+(L:Int)*(5-2*((w+1:Nat):Int)))) := by
  rcases hf with ⟨hL,hLo,hde,hf⟩
  have hbI : (b:Int)=((2:Int)^(w+1)+3)*(q:Int)+3*(2:Int)^w+(w:Int)+3 := by
    exact_mod_cast hb
  have hpI : (p:Int)=(2:Int)^w*(2*(q:Int)+3) := by exact_mod_cast hp
  have hm : (2:Int)^(w+1)=2*(2:Int)^w := by rw [Int.pow_succ,Int.mul_comm]
  have hLpos : 0<L*(2^(w+1)+3) := Nat.mul_pos hL (Nat.add_pos_right _ (by decide))
  refine ⟨hLpos,?_,?_,?_⟩
  · rw [Nat.mul_mod,hLo,Nat.pow_succ,Nat.add_mod,Nat.mul_mod]
    simp
  · rw [Int.pow_succ,Int.mul_assoc,Int.mul_emod]
    have hzero : 2*(d+(L:Int)*(5-2*((w+1:Nat):Int)))%2=0 := by rw [Int.mul_emod]; simp
    rw [hzero,Int.mul_zero,Int.zero_emod]
  · push_cast
    rw [show n+w+1=n+(w+1) by omega,Int.pow_add]
    try simp only [Int.natCast_add,Int.natCast_one] at *
    rw [hm] at *
    grind

/-- The divisibility condition applies to every node of an affine reverse tree. -/
theorem form_parent_dvd (n L b q w : Nat) (d : Int)
    (hf : Form n L b d) (hb : Cancellation.parentEq b q w) :
    (L:Int)*denominator (w+1) ∣ (2:Int)^n+d+(L:Int)*(5-2*((w+1:Nat):Int)) := by
  rcases hf with ⟨hL,hLo,hde,hf⟩
  obtain ⟨z,hz⟩ := Cancellation.parent_int_dvd b q w hb
  refine ⟨z,?_⟩
  have h1 := congrArg (fun x : Int => (L:Int)*x) hz
  grind

theorem form_correction_odd (L m : Nat) (d : Int) (hL : L%2=1) (hd : d%2=0) :
    (d+(L:Int)*(5-2*(m:Int)))%2=1 := by
  have hLi : (L:Int)%2=1 := by exact_mod_cast hL
  rw [Int.add_emod,hd,Int.mul_emod,hLi,Int.sub_emod,Int.mul_emod]
  simp

/-- A universally quantified source-equation cutoff for every reverse node
with an affine terminal-power representation. -/
theorem form_parent_square_or_cancel (n L b q w H : Nat) (d : Int)
    (hf : Form n L b d) (hb : Cancellation.parentEq b q w)
    (hH : 0<H)
    (hC : (d+(L:Int)*(5-2*((w+1:Nat):Int))).natAbs<2^H) :
    (w+1)*(w+1)<(H+2)*(w+1)+2*n ∨
    (n%(w+1)=0 ∧ d+(L:Int)*(5-2*((w+1:Nat):Int))= -(-3:Int)^(n/(w+1))) := by
  have hd := form_parent_dvd n L b q w d hf hb
  have hD : denominator (w+1) ∣ (2:Int)^n+d+(L:Int)*(5-2*((w+1:Nat):Int)) :=
    Int.dvd_trans (Int.dvd_mul_left _ _) hd
  apply two_term_square_or_cancel n (w+1) H _ (by omega) hH (form_correction_odd L (w+1) d hf.2.1 hf.2.2.1) hC
  simpa [Int.add_assoc] using hD

/-- The normalized affine correction stays below 2 under every reverse
step. This sharp bound holds regardless of the history length. -/
theorem correction_upper_step (L m : Nat) (d : Int)
    (hL : 0<L) (hm : 0<m) (hd : d<2*(L:Int)) :
    (2:Int)^m*(d+(L:Int)*(5-2*(m:Int))) < 2*(L:Int)*((2:Int)^m+3) := by
  have hp : 0<(2:Int)^m := Int.pow_pos (by decide)
  have hLi : 0<(L:Int) := by exact_mod_cast hL
  have hsmall : (2:Int)^m*(5-2*(m:Int))≤6 := by
    by_cases h1 : m=1
    · subst m; decide
    by_cases h2 : m=2
    · subst m; decide
    have hnon : 5-2*(m:Int)≤0 := by omega
    have hh := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hp) hnon
    omega
  have hmul := Int.mul_le_mul_of_nonneg_right hsmall (Int.le_of_lt hLi)
  have hstrict := Int.mul_lt_mul_of_pos_left hd hp
  grind

theorem correction_negative (L m : Nat) (d : Int)
    (hL : 0<L) (hm : 4≤m) (hd : d<2*(L:Int)) :
    d+(L:Int)*(5-2*(m:Int))<0 := by
  have hLi : 0<(L:Int) := by exact_mod_cast hL
  have h2 : 5-2*(m:Int)≤ -3 := by omega
  have hmul := Int.mul_le_mul_of_nonneg_left h2 (Int.le_of_lt hLi)
  omega

/-- There is at most one exact cancellation valuation m>=4 for a fixed
terminal-power affine node with the invariant normalized correction <2. -/
theorem unique_large_cancellation (n L m₁ m₂ : Nat) (d : Int)
    (hn : 0<n) (hL : 0<L) (hd : d<2*(L:Int))
    (hm₁ : 4≤m₁) (hm₂ : 4≤m₂)
    (hdiv₁ : n%m₁=0) (hdiv₂ : n%m₂=0)
    (hcan₁ : d+(L:Int)*(5-2*(m₁:Int))= -(-3:Int)^(n/m₁))
    (hcan₂ : d+(L:Int)*(5-2*(m₂:Int))= -(-3:Int)^(n/m₂)) : m₁=m₂ := by
  let C (m : Nat) := d+(L:Int)*(5-2*(m:Int))
  have hLi : 0<(L:Int) := by exact_mod_cast hL
  have neg₁ : C m₁<0 := correction_negative L m₁ d hL hm₁ hd
  have neg₂ : C m₂<0 := correction_negative L m₂ d hL hm₂ hd
  have habs₁ : (C m₁).natAbs=3^(n/m₁) := by
    change (d+(L:Int)*(5-2*(m₁:Int))).natAbs=_
    rw [hcan₁,Int.natAbs_neg,Int.natAbs_pow]
    rfl
  have habs₂ : (C m₂).natAbs=3^(n/m₂) := by
    change (d+(L:Int)*(5-2*(m₂:Int))).natAbs=_
    rw [hcan₂,Int.natAbs_neg,Int.natAbs_pow]
    rfl
  have n₁ : m₁*(n/m₁)=n := by have hh:=Nat.div_add_mod n m₁; omega
  have n₂ : m₂*(n/m₂)=n := by have hh:=Nat.div_add_mod n m₂; omega
  have hmono (a b : Nat) (hab : a<b) : C b<C a := by
    have hI : (a:Int)<(b:Int) := by exact_mod_cast hab
    have hm := Int.mul_lt_mul_of_pos_left (show 5-2*(b:Int)<5-2*(a:Int) by omega) hLi
    dsimp [C]
    omega
  have order (a b : Nat) (hba : a<b) (ha : 0<a)
      (hnA : a*(n/a)=n) (hnB : b*(n/b)=n) : n/b<n/a := by
    have hq : 0<n/b := by
      by_cases h : n/b=0
      · rw [h,Nat.mul_zero] at hnB; omega
      · exact Nat.pos_of_ne_zero h
    have hprod := Nat.mul_lt_mul_of_pos_right hba hq
    rw [hnB] at hprod
    by_cases hh : n/b<n/a
    · exact hh
    have hbad := Nat.mul_le_mul_left a (show n/a≤n/b by omega)
    rw [hnA] at hbad
    omega
  by_cases hlt : m₁<m₂
  · have hltC := hmono m₁ m₂ hlt
    have habs : (C m₁).natAbs < (C m₂).natAbs := by omega
    have hq := order m₁ m₂ hlt (by omega) n₁ n₂
    have hp := Nat.pow_lt_pow_right (by decide : 1<(3:Nat)) hq
    rw [habs₁,habs₂] at habs
    omega
  by_cases hgt : m₂<m₁
  · have hltC := hmono m₂ m₁ hgt
    have habs : (C m₂).natAbs < (C m₁).natAbs := by omega
    have hq := order m₂ m₁ hgt (by omega) n₂ n₁
    have hp := Nat.pow_lt_pow_right (by decide : 1<(3:Nat)) hq
    rw [habs₁,habs₂] at habs
    omega
  omega

/-- The exact cancellation exponent quotient is bounded by the correction
bit length, so exceptional valuations can be enumerated without factoring n. -/
theorem cancellation_quotient_lt (n m H : Nat) (C : Int)
    (hC : C.natAbs<2^H) (hc : C= -(-3:Int)^(n/m)) : n/m<H := by
  rw [hc,Int.natAbs_neg,Int.natAbs_pow] at hC
  change 3^(n/m)<2^H at hC
  have hp := Nat.pow_le_pow_left (by decide : (2:Nat)≤3) (n/m)
  by_cases h : n/m<H
  · exact h
  have hmono := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show H≤n/m by omega)
  omega

/-- The divisibility test, including the positive quotient condition, is
sufficient as well as necessary for a genuine parent equation. -/
theorem exact_parent_iff (n L b w : Nat) (d : Int) (hf : Form n L b d) :
    (∃ q : Nat, Cancellation.parentEq b q w) ↔
    ∃ z : Nat, 3≤z ∧ z%2=1 ∧
      (2:Int)^n+d+(L:Int)*(5-2*((w+1:Nat):Int)) =
        (L:Int)*denominator (w+1)*(z:Int) := by
  rcases hf with ⟨hL,hLo,hde,hf⟩
  have hLi : 0<(L:Int) := by exact_mod_cast hL
  have hpow : (2:Int)^(w+1)=2*(2:Int)^w := by rw [Int.pow_succ,Int.mul_comm]
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨2*q+3,by omega,by omega,?_⟩
    have hqI : (b:Int)=((2:Int)^(w+1)+3)*(q:Int)+3*(2:Int)^w+(w:Int)+3 := by exact_mod_cast hq
    simp only [denominator,Int.natCast_add,Int.natCast_mul]
    rw [hpow] at *
    grind
  · rintro ⟨z,hz,ho,he⟩
    let q := (z-3)/2
    have hq : z=2*q+3 := by dsimp [q]; omega
    refine ⟨q,?_⟩
    rw [hq] at he
    simp only [denominator,Int.natCast_add,Int.natCast_mul] at he
    rw [hpow] at he
    have hmul : (L:Int)*(2*(b:Int)+5-2*((w+1:Nat):Int)) =
      (L:Int)*((2*(2:Int)^w+3)*(2*(q:Int)+3)) := by grind
    have hcancel : 2*(b:Int)+5-2*((w+1:Nat):Int)=(2*(2:Int)^w+3)*(2*(q:Int)+3) := by
      exact (Int.mul_eq_mul_left_iff (by omega : (L:Int)≠0)).mp hmul
    have hh : (b:Int)=((2:Int)^(w+1)+3)*(q:Int)+3*(2:Int)^w+(w:Int)+3 := by rw [hpow]; grind
    exact_mod_cast hh

/-- The invariant needed for the unique large cancellation theorem holds
at every depth starting at a terminal power. -/
def TerminalForm (n L b : Nat) (d : Int) : Prop :=
  Form n L b d ∧ 0<n ∧ d<2*(L:Int)

theorem terminalForm_root (K : Nat) : TerminalForm (K+1) 1 (2^K) 0 :=
  ⟨root_form K,by omega,by decide⟩

theorem terminalForm_parent (n L b p q w : Nat) (d : Int)
    (hf : TerminalForm n L b d) (hb : Cancellation.parentEq b q w)
    (hp : p=2^w*(2*q+3)) :
    TerminalForm (n+w+1) (L*(2^(w+1)+3)) p
      ((2:Int)^(w+1)*(d+(L:Int)*(5-2*((w+1:Nat):Int)))) := by
  refine ⟨form_parent n L b p q w d hf.1 hb hp,by omega,?_⟩
  push_cast
  have h := correction_upper_step L (w+1) d hf.1.1 (by omega) hf.2.2
  simp only [Int.natCast_add,Int.natCast_one] at *
  grind

theorem negative_three_pow_positive_even (k : Nat) : 0<(-3:Int)^k ↔ k%2=0 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    have hn : (-3:Int)^k≠0 := Int.pow_ne_zero (by decide)
    omega

theorem large_cancellation_even (n L m : Nat) (d : Int)
    (hL : 0<L) (hd : d<2*(L:Int)) (hm : 4≤m)
    (hc : d+(L:Int)*(5-2*(m:Int))= -(-3:Int)^(n/m)) : (n/m)%2=0 := by
  have hneg := correction_negative L m d hL hm hd
  rw [hc] at hneg
  exact (negative_three_pow_positive_even _).mp (by omega)

#print axioms exact_parent_iff
#print axioms terminalForm_parent
#print axioms large_cancellation_even
#print axioms correction_upper_step
#print axioms unique_large_cancellation
#print axioms cancellation_quotient_lt
#print axioms two_term_cancellation
#print axioms two_term_square_or_cancel
#print axioms form_parent
#print axioms form_parent_dvd
#print axioms form_parent_square_or_cancel
end NeedleRotation.TerminalAffine
