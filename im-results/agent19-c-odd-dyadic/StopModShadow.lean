import Root32ShadowArithmetic

namespace BB6.Agent19StopMod
open BB6.Agent19Shadow

/-- Padded nonnegative representatives of the exact signed stopping shadows.
    Their sizes do not enter the independent right-coordinate guard. -/
def seedU (p j : Nat) : Nat := C*2^p + (2^p-(C*(2*j+1))%2^p)
def seedV (p j m : Nat) : Nat := C*2^p + (C*(j+3*m+4))%2^p

def stopExcluded (f p j m : Nat) : Bool :=
  modExcluded f p (seedU p j) (seedV p j m)

private theorem seedU_lift (p j : Nat) : 2^p∣C*(2*j+1)+seedU p j := by
  let z := C*(2*j+1)
  let M := 2^p
  change M∣z+(C*M+(M-z%M))
  have h := Nat.mod_add_div z M
  have hr := Nat.mod_lt z (show 0<M from Nat.pow_pos (by decide))
  refine ⟨C+1+z/M,?_⟩
  simp only [Nat.mul_add,Nat.mul_one]
  rw [Nat.mul_comm M C]
  omega

private theorem seedV_lift (p j m k : Nat) (hp : p≤2*m+2)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) : 2^p∣C*k+seedV p j m := by
  let z := C*(j+3*m+4)
  have h1 : C*k+z=C*(2^(2*m+2)*(j+2)) := by
    dsimp [z]
    rw [←hstop]
    simp only [Nat.mul_add]
    omega
  have h2 : 2^p∣C*k+z := by
    rw [h1]
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hp) (Nat.dvd_trans (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))
  have h3 : 2^p∣2^p*(z/2^p) := Nat.dvd_mul_right _ _
  have h4 := Nat.mod_add_div z (2^p)
  have he : C*k+z=(C*k+z%2^p)+2^p*(z/2^p) := by omega
  rw [he] at h2
  have h5 := (Nat.dvd_add_iff_left h3).mpr h2
  have h6 : 2^p∣C*2^p := Nat.dvd_mul_left _ _
  unfold seedV
  change 2^p∣C*k+(C*2^p+z%2^p)
  rw [Nat.add_left_comm (C*k)]
  exact Nat.dvd_add h6 h5

theorem stop_lift (p j m k : Nat) (hp : p≤2*m+2)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) :
    lift p (seedU p j) (seedV p j m) (2*j+1) k :=
  ⟨seedU_lift p j,seedV_lift p j m k hp hstop⟩

private theorem exp_bound (m : Nat) : 4*m+4≤(2:Nat)^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2*(m+1)+2=2*m+2+2 by omega,Nat.pow_add]
    change 4*(m+1)+4≤2^(2*m+2)*4
    omega

/-- Actual size is available even when the negative shadow has a negative
    first coordinate or a negative signed sum. No wedge j≤3m+1 is required. -/
theorem stop_rightLarge (j m k : Nat)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) : RightLarge (2*m+2) k := by
  have h := exp_bound m
  have hj : j≤2^(2*m+2)*j := by
    simpa using Nat.mul_le_mul_right j (show 1≤2^(2*m+2) by omega)
  rw [Nat.mul_add] at hstop
  unfold RightLarge
  omega

private theorem mod_linear1 (j a b M : Nat) : (a*(j%M)+b)%M=(a*j+b)%M := by
  rw [Nat.add_mod, Nat.mul_mod]
  conv => rhs; rw [Nat.add_mod,Nat.mul_mod]
  rw [Nat.mod_mod]

private theorem mod_linear2 (j m a b c M : Nat) :
    (a*(j%M)+b*(m%M)+c)%M=(a*j+b*m+c)%M := by
  calc
    (a*(j%M)+b*(m%M)+c)%M = (a*(j%M)+(b*(m%M)+c))%M := by rw [Nat.add_assoc]
    _ = (a*j+(b*(m%M)+c))%M := mod_linear1 j a _ M
    _ = (b*(m%M)+(a*j+c))%M := by rw [Nat.add_left_comm]
    _ = (b*m+(a*j+c))%M := mod_linear1 m b _ M
    _ = (a*j+b*m+c)%M := by rw [Nat.add_left_comm,←Nat.add_assoc]

/-- Congruence periodicity of the padded seeds. -/
theorem stopExcluded_periodic (f p j m : Nat) :
    stopExcluded f p j m=stopExcluded f p (j%2^p) (m%2^p) := by
  have hu : seedU p j=seedU p (j%2^p) := by
    unfold seedU
    have he (z : Nat) : C*(2*z+1)=(2*C)*z+C := by simp only [C]; omega
    rw [he,he,mod_linear1]
  have hv : seedV p j m=seedV p (j%2^p) (m%2^p) := by
    unfold seedV
    have he (a b : Nat) : C*(a+3*b+4)=C*a+(3*C)*b+4*C := by simp only [C]; omega
    rw [he,he,mod_linear2]
  simp only [stopExcluded,←hu,←hv]

theorem stopExcluded_sound (reach : Nat→Nat→Prop)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (parent : ∀ x y w, 8≤y → (x+y+(x+y)%2)%2^(w+1)=2^w → 2^w<x+y+(x+y)%2 → reach x y →
      (∃ a k, reach a k ∧ y%2=0 ∧ a+2=x+y ∧ 2*k+2=y) ∨
      (∃ a k n, reach a k ∧ n+2≤w ∧ n%2=(x+1+(x+y)%2)%2 ∧
      x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2) ∧ 2*k+a+7+3*n=x+2*y))
    (f p j m k : Nat) (hp : p+4≤2*m+2)
    (hc : stopExcluded f p j m=true)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) : ¬reach (2*j+1) k :=
  modExcluded_sound reach forbid parent f p _ _ (2*m+2) _ _ hc
    (stop_lift p j m k (by omega) hstop) hp (stop_rightLarge j m k hstop)

/-- Examples with genuinely outside-wedge minimal seed indices. -/
theorem stop_examples : stopExcluded 6 6 22 4=true ∧ stopExcluded 5 5 23 4=true := by decide

#print axioms stop_lift
#print axioms stop_rightLarge
#print axioms stopExcluded_periodic
#print axioms stopExcluded_sound
#print axioms stop_examples

/-- Compute the exponential residue without evaluating the huge power
    when it is zero modulo the chosen precision. -/
def pow2Residue (p e : Nat) : Nat := if p≤e then 0 else 2^e

theorem pow2Residue_correct (p e : Nat) : pow2Residue p e=2^e%2^p := by
  unfold pow2Residue
  split
  · rename_i h
    exact (Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 h)).symm
  · rename_i h
    exact (Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))).symm

/-- Exact stop-right residue, including precision beyond the stop exponent. -/
def stopYResidue (p j m : Nat) : Nat :=
  (pow2Residue p (2*m+2)*(j+2)+(2^p-(j+3*m+4)%2^p))%2^p

theorem stopYResidue_correct (p j m k : Nat)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) : stopYResidue p j m=k%2^p := by
  let M := 2^p
  let z := j+3*m+4
  let P := 2^(2*m+2)*(j+2)
  have hz : z%M+(M-z%M)=M := Nat.add_sub_of_le (Nat.le_of_lt (Nat.mod_lt z (show 0<M from Nat.pow_pos (by decide))))
  have hp : k+z=P := by dsimp [z,P]; omega
  unfold stopYResidue
  rw [pow2Residue_correct]
  change ((2^(2*m+2)%M)*(j+2)+(M-z%M))%M=k%M
  have hprod : ((2^(2*m+2)%M)*(j+2))%M=P%M := by
    dsimp [P]
    rw [Nat.mul_comm (2^(2*m+2)%M),Nat.mul_mod_mod,Nat.mul_comm]
  calc
    _ = (P%M+(M-z%M))%M := by rw [←Nat.mod_add_mod _ M _,hprod]
    _ = (P+(M-z%M))%M := Nat.mod_add_mod _ _ _
    _ = k%M := by
      rw [←hp,Nat.add_assoc,←Nat.add_mod_mod k _ M,←Nat.mod_add_mod z M _,hz,Nat.mod_self,Nat.add_zero]

/-- General padded seed for an arbitrary actual coordinate. -/
def coordinateSeed (p z : Nat) : Nat := C*2^p+(2^p-(C*z)%2^p)

private theorem coordinateSeed_lift (p z : Nat) : 2^p∣C*z+coordinateSeed p z := by
  let Z := C*z
  let M := 2^p
  change M∣Z+(C*M+(M-Z%M))
  have h := Nat.mod_add_div Z M
  have hr := Nat.mod_lt Z (show 0<M from Nat.pow_pos (by decide))
  refine ⟨C+1+Z/M,?_⟩
  simp only [Nat.mul_add,Nat.mul_one]
  rw [Nat.mul_comm M C]
  omega

private theorem coordinateSeed_periodic (p z : Nat) : coordinateSeed p z=coordinateSeed p (z%2^p) := by
  unfold coordinateSeed
  rw [Nat.mul_mod_mod]

def generalExcluded (f p j m : Nat) : Bool :=
  modExcluded f p (seedU p j) (coordinateSeed p (stopYResidue p j m))

theorem general_lift (p j m k : Nat)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) :
    lift p (seedU p j) (coordinateSeed p (stopYResidue p j m)) (2*j+1) k := by
  rw [stopYResidue_correct _ _ _ _ hstop,←coordinateSeed_periodic]
  exact ⟨seedU_lift p j,coordinateSeed_lift p k⟩

/-- Right size can be supplied by the left stop index as well as the
    exponential. This covers fixed small m with unbounded j. -/
theorem stop_rightLarge_product (j m k q : Nat)
    (hq : 2^q≤j+2)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) : RightLarge (2*m+1+q) k := by
  have h := exp_bound m
  let A := 2^(2*m+1)
  have hhalf : A*2=2^(2*m+2) := by
    calc
      A*2 = 2^((2*m+1)+1) := (Nat.pow_succ 2 (2*m+1)).symm
      _ = 2^(2*m+2) := by congr 1
  have hpos : 1≤A := Nat.one_le_pow _ _ (by decide)
  have hj : j≤A*j := by simpa using Nat.mul_le_mul_right j hpos
  have hs : k+j+3*m+4=2*(A*j)+4*A := by
    rw [hstop,←hhalf,Nat.mul_add]
    ac_rfl
  have hA : A*(j+2)≤k+2 := by
    rw [Nat.mul_add,Nat.mul_comm A 2]
    omega
  unfold RightLarge
  rw [Nat.pow_add]
  exact Nat.le_trans (Nat.mul_le_mul_left _ hq) hA

theorem generalExcluded_sound (reach : Nat→Nat→Prop)
    (forbid : ∀ x y, 5≤y → y%2=1 → ((x+y)%4=1 ∨ (x+y)%4=2) → ¬reach x y)
    (parent : ∀ x y w, 8≤y → (x+y+(x+y)%2)%2^(w+1)=2^w → 2^w<x+y+(x+y)%2 → reach x y →
      (∃ a k, reach a k ∧ y%2=0 ∧ a+2=x+y ∧ 2*k+2=y) ∨
      (∃ a k n, reach a k ∧ n+2≤w ∧ n%2=(x+1+(x+y)%2)%2 ∧
      x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2) ∧ 2*k+a+7+3*n=x+2*y))
    (f p q j m k : Nat) (hp : p+4≤q)
    (hc : generalExcluded f p j m=true) (hsize : RightLarge q k)
    (hstop : k+j+3*m+4=2^(2*m+2)*(j+2)) : ¬reach (2*j+1) k :=
  modExcluded_sound reach forbid parent f p _ _ q _ _ hc (general_lift p j m k hstop) hp hsize

#print axioms stopYResidue_correct
#print axioms general_lift
#print axioms stop_rightLarge_product
#print axioms generalExcluded_sound
end BB6.Agent19StopMod
