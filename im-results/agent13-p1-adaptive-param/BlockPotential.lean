import Lean
namespace BB6.Agent13Block

/-- Integral affine-block potential for an exact fixed inverse-depth word. -/
def phi (A H S D L m z : Int) : Int :=
  (A-1)^2*z - H*(A-1)*(L+m) - D*(A-1) + A*H*S

/-- A fixed inverse-depth block of scaling A divides the potential by A. -/
theorem phi_step (A H S D L m z zp : Int)
    (hedge : A*zp=z+H*(L+m)+D) :
    A*phi A H S D L (m+S) zp = phi A H S D L m z := by
  have hh := congrArg (fun x : Int => (A-1)^2*x) hedge
  unfold phi
  simp only [Int.pow_succ', Int.pow_zero, Int.mul_one,
    Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul] at *
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at *
  simp only [Int.mul_one] at *
  omega

/-- Executable finite modular test proving the potential never vanishes. -/
theorem phi_nonzero (A H S D L m z : Int) (hA:2≤A)
    (hmod : ¬(A-1)∣H*S) : phi A H S D L m z ≠ 0 := by
  intro hp
  let d : Int := A-1
  have heq : A*H*S = d*(H*(L+m)+D-d*z) := by
    unfold phi at hp
    dsimp [d]
    simp only [Int.pow_succ', Int.pow_zero, Int.mul_one,
      Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul] at *
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at *
    simp only [Int.mul_one] at *
    omega
  have hdA : d ∣ A*H*S := ⟨H*(L+m)+D-d*z, heq⟩
  have hdhs : d ∣ H*S := by
    have hdpart : d ∣ d*(H*S) := Int.dvd_mul_right d (H*S)
    have hh : A*H*S-d*(H*S)=H*S := by
      have hAd : A=d+1 := by dsimp [d]; omega
      rw [hAd]
      simp only [Int.add_mul, Int.mul_assoc, Int.one_mul]
      omega
    rw [←hh]
    exact Int.dvd_sub hdA hdpart
  exact hmod hdhs

/-- N consecutive repetitions of the exact same affine inverse block. -/
inductive RunBlock (A H S D L : Nat) : Nat → Nat → Nat → Prop where
| zero (m z : Nat) : RunBlock A H S D L 0 m z
| more {N m z zp : Nat} : RunBlock A H S D L N (m+S) zp →
    A*zp=z+H*(L+m)+D → RunBlock A H S D L (N+1) m z

theorem run_block_divisibility (A H S D L N m z : Nat)
    (hr : RunBlock A H S D L N m z) :
    (↑A:Int)^N∣ phi (↑A) (↑H) (↑S) (↑D) (↑L) (↑m) (↑z) := by
  induction hr with
  | zero m z => simp
  | @more N m z zp hi hed ih =>
      rcases ih with ⟨u,hu⟩
      refine ⟨u, ?_⟩
      have hi' : (↑A:Int)*(↑zp:Int) = (↑z:Int)+
          (↑H:Int)*((↑L:Int)+(↑m:Int))+(↑D:Int) := by
        exact_mod_cast hed
      calc
        phi (↑A) (↑H) (↑S) (↑D) (↑L) (↑m) (↑z) =
          (↑A:Int)*phi (↑A) (↑H) (↑S) (↑D) (↑L) (↑(m+S)) (↑zp) := by
            have hstep := phi_step (↑A) (↑H) (↑S) (↑D) (↑L)
              (↑m) (↑z) (↑zp) hi'
            simpa using hstep.symm
        _ = (↑A:Int)*((↑A:Int)^N*u) := by rw [hu]
        _ = (↑A:Int)^(N+1)*u := by rw [Int.pow_succ']; ac_rfl

private theorem power_growth (A N:Nat) (hA:2≤A) : N < A^N := by
  induction N with
  | zero => simp
  | succ n ih =>
      have hp : 0<A^n := Nat.pow_pos (by omega)
      have he : 2*(A^n) ≤ (A^n)*A := by
        have h := Nat.mul_le_mul_left (A^n) hA
        omega
      rw [Nat.pow_succ]
      omega

/-- No infinite repetition of a concrete affine block passing its modular
    check. The theorem works for any starting integer shadow coordinates. -/
theorem no_infinite_block (A H S D L m z : Nat)
    (hA:2≤A)
    (hmod : ¬((↑A:Int)-1)∣(↑H:Int)*(↑S:Int))
    (hall : ∀ N : Nat, RunBlock A H S D L N m z) : False := by
  let p := phi (↑A) (↑H) (↑S) (↑D) (↑L) (↑m) (↑z)
  let N := p.natAbs
  have hd := run_block_divisibility A H S D L (N+1) m z (hall (N+1))
  have hn : (A^(N+1)) ∣ p.natAbs := by
    have hh := (Int.natAbs_dvd_natAbs).mpr hd
    simpa [p, Int.natAbs_pow, Int.natAbs_natCast] using hh
  have hp : 0 < p.natAbs := Int.natAbs_pos.mpr (phi_nonzero
    (↑A) (↑H) (↑S) (↑D) (↑L) (↑m) (↑z) (by exact_mod_cast hA) hmod)
  have hle := Nat.le_of_dvd hp hn
  have hg := power_growth A (N+1) hA
  omega

#print axioms phi_step
#print axioms phi_nonzero
#print axioms no_infinite_block
end BB6.Agent13Block
