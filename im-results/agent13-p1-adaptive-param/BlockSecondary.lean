import BlockPotential
namespace BB6.Agent13Block

/-- Secondary modular obstruction when the primary (A-1)∤HS test fails. -/
theorem phi_nonzero_secondary (A H S D L m z g c : Int)
    (hA : 2≤A) (hHS : H*S=(A-1)*c)
    (hgA : g∣A-1) (hgH : g∣H)
    (hmod : ¬g∣A*c-D) : phi A H S D L m z ≠ 0 := by
  intro hp
  let d : Int := A-1
  have hAS : A*H*S=A*(d*c) := by
    calc
      A*H*S = A*(H*S) := by ac_rfl
      _ = A*(d*c) := by rw [hHS]
  have hfact : d*(d*z-H*(L+m)-D+A*c)=0 := by
    unfold phi at hp
    rw [hAS] at hp
    dsimp [d] at *
    simp only [Int.pow_succ', Int.pow_zero, Int.mul_one,
      Int.mul_add, Int.mul_sub, Int.sub_mul] at *
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at *
    simp only [Int.mul_one] at *
    omega
  have hpos : 0<d := by dsimp [d]; omega
  have hlin : d*z-H*(L+m)-D+A*c=0 := by
    rcases Int.mul_eq_zero.mp hfact with hd0 | hh
    · omega
    · exact hh
  have hg1 : g∣H*(L+m) := Int.dvd_mul_of_dvd_left hgH
  have hg2 : g∣d*z := Int.dvd_mul_of_dvd_left (by simpa [d] using hgA)
  have hTarget : A*c-D=H*(L+m)-d*z := by omega
  apply hmod
  rw [hTarget]
  exact Int.dvd_sub hg1 hg2

/-- A secondary modular finite check certifies no unlimited repetition of
    the fixed affine predecessor block, regardless of source coordinates. -/
theorem no_infinite_block_secondary (A H S D L m z : Nat) (g c : Int)
    (hA:2≤A)
    (hHS : (↑H:Int)*(↑S:Int)=((↑A:Int)-1)*c)
    (hgA : g∣((↑A:Int)-1)) (hgH : g∣(↑H:Int))
    (hmod : ¬g∣(↑A:Int)*c-(↑D:Int))
    (hall : ∀ N : Nat, RunBlock A H S D L N m z) : False := by
  let p := phi (↑A) (↑H) (↑S) (↑D) (↑L) (↑m) (↑z)
  let N := p.natAbs
  have hd := run_block_divisibility A H S D L (N+1) m z (hall (N+1))
  have hn : (A^(N+1)) ∣ p.natAbs := by
    have hh := (Int.natAbs_dvd_natAbs).mpr hd
    simpa [p, Int.natAbs_pow, Int.natAbs_natCast] using hh
  have hp : 0 < p.natAbs := Int.natAbs_pos.mpr (phi_nonzero_secondary
    (↑A) (↑H) (↑S) (↑D) (↑L) (↑m) (↑z) g c
    (by exact_mod_cast hA) hHS hgA hgH hmod)
  have hle := Nat.le_of_dvd hp hn
  have hbase : (N+1) < A^(N+1) := by
    have hh : ∀ k : Nat, k < A^k := by
      intro k
      induction k with
      | zero => simp
      | succ n ih =>
          have hp : 0<A^n := Nat.pow_pos (by omega)
          have he : 2*(A^n)≤(A^n)*A := by
            have h := Nat.mul_le_mul_left (A^n) hA
            omega
          rw [Nat.pow_succ]
          omega
    exact hh (N+1)
  omega

#print axioms phi_nonzero_secondary
#print axioms no_infinite_block_secondary
end BB6.Agent13Block
