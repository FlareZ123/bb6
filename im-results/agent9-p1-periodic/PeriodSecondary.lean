import Std
set_option linter.unusedSimpArgs false
namespace PeriodSecondary

/-- Base-a finite geometric sum, built recursively to avoid large constants. -/
def geom (a : Int) : Nat → Int
  | 0 => 0
  | n+1 => 1 + a*geom a n

/-- Weighted geometric sum Σ_(i<T) i*a^i. -/
def weighted (a : Int) : Nat → Int
  | 0 => 0
  | n+1 => a*(weighted a n+geom a n)

theorem geom_identity (a : Int) (T : Nat) :
    (a-1)*geom a T = a^T-1 := by
  induction T with
  | zero => simp [geom]
  | succ n ih =>
      simp only [geom, Int.pow_succ, Int.natCast_succ]
      simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.add_mul,
        Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at ih ⊢
      grind

theorem weighted_identity (a : Int) (T : Nat) :
    (a-1)*weighted a T = ((T:Int)-1)*a^T-geom a T+1 := by
  induction T with
  | zero => simp [weighted, geom]
  | succ n ih =>
      have hg := geom_identity a n
      simp only [weighted, geom, Int.natCast_succ, Int.pow_succ]
      simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.add_mul,
        Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at ih ⊢
      have hga := congrArg (fun x : Int => a*x) hg
      simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.add_mul,
        Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at hga
      grind

/-- An arbitrary repeated binary-block coefficient which passes the primary
    integral-slope condition must fail the secondary modular check, whenever
    its primitive base block has nonintegral slope. This is an all-length
    algebraic statement, conditional only on the exact repeated-block
    factorization of H and D. -/
theorem secondary_obstruction (a h r D0 : Int) (T : Nat)
    (J A D Q : Int)
    (hJ : J=geom a T) (hA : A=a^T)
    (hD : D=D0*J+h*r*weighted a T)
    (hSlope : (a-1)*Q=h*r*(T:Int))
    (hpos : 0<J)
    (hbase : ¬(a-1) ∣ h*r) :
    ¬ J ∣ A*Q-D := by
  intro hdiv
  rcases hdiv with ⟨k,hk⟩
  have hg : (a-1)*J=A-1 := by
    rw [hJ,hA]
    exact geom_identity a T
  have hw : (a-1)*weighted a T = ((T:Int)-1)*A-J+1 := by
    rw [hJ,hA]
    exact weighted_identity a T
  have hid : (a-1)*(A*Q-D) = J*(a*h*r-(a-1)*D0) := by
    calc
      (a-1)*(A*Q-D) = A*((a-1)*Q)-(a-1)*D := by
        simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.add_mul,
          Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        grind
      _ = A*(h*r*(T:Int)) - ((a-1)*D0*J + h*r*((a-1)*weighted a T)) := by
        rw [hSlope,hD]
        simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.add_mul,
          Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = A*(h*r*(T:Int)) - ((a-1)*D0*J + h*r*(((T:Int)-1)*A-J+1)) := by
        rw [hw]
      _ = J*(h*r-(a-1)*D0) + h*r*(A-1) := by
        simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.add_mul,
          Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        grind
      _ = J*(h*r-(a-1)*D0)+h*r*((a-1)*J) := by rw [hg]
      _ = J*(a*h*r-(a-1)*D0) := by
        simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.add_mul,
          Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        grind
  have he : J*((a-1)*k)=J*(a*h*r-(a-1)*D0) := by
    calc
      _ = (a-1)*(J*k) := by
        simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.add_mul,
          Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = (a-1)*(A*Q-D) := by rw [hk]
      _ = _ := hid
  have hc := Int.eq_of_mul_eq_mul_left (by omega : J ≠ 0) he
  have hgood : (a-1) ∣ h*r := by
    refine ⟨k+D0-h*r, ?_⟩
    calc
      h*r = a*h*r-(a-1)*(h*r) := by
        simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.add_mul,
          Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        grind
      _ = (a-1)*k+(a-1)*D0-(a-1)*(h*r) := by
        rw [hc]
        grind
      _ = (a-1)*(k+D0-h*r) := by
        simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.add_mul,
          Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        grind
  exact hbase hgood

/-- A long block built by repeating one primitive source block cannot have
    an integral affine orbit with nonnegative or arbitrary integer starts.
    The coefficient formulas encode exact repetitions; no finite-word
    decomposition is postulated here. -/
theorem repeated_affine_obstruction
    (a h r D0 : Int) (T : Nat) (J A H D S Q X Z : Int)
    (hJ : J=geom a T) (hA : A=a^T)
    (hH : H=h*J) (hS : S=r*(T:Int))
    (hD : D=D0*J+h*r*weighted a T)
    (hB : A-1=(a-1)*J)
    (hpos : 0<J)
    (hbase : ¬(a-1) ∣ h*r)
    (hSlope : (A-1)*Q=H*S)
    (hStart : (A-1)*Z=H*X+D-A*Q) : False := by
  have hscaled : J*((a-1)*Q)=J*(h*r*(T:Int)) := by
    calc
      J*((a-1)*Q) = (A-1)*Q := by rw [hB]; ac_rfl
      _ = H*S := hSlope
      _ = J*(h*r*(T:Int)) := by rw [hH,hS]; ac_rfl
  have hbaseSlope : (a-1)*Q=h*r*(T:Int) :=
    Int.eq_of_mul_eq_mul_left (by omega : J≠0) hscaled
  have hdiv : J ∣ A*Q-D := by
    refine ⟨h*X-(a-1)*Z, ?_⟩
    have he : A*Q-D=H*X-(A-1)*Z := by omega
    rw [he,hH,hB]
    simp only [Int.mul_add,Int.mul_sub,Int.sub_mul,Int.add_mul,
      Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
  exact secondary_obstruction a h r D0 T J A D Q hJ hA hD
    hbaseSlope hpos hbase hdiv

#print axioms repeated_affine_obstruction
#print axioms geom_identity
#print axioms weighted_identity
#print axioms secondary_obstruction
end PeriodSecondary
