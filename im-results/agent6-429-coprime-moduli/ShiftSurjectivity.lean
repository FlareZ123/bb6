import Lean.Elab.Tactic.Omega

namespace ShiftSurjectivity

/-- An eventually valid affine shift, with a period that is nonzero mod m. -/
def HasShift (f : Nat → Int) (m : Nat) : Prop :=
  ∃ p C : Nat, 0 < p ∧ p % m ≠ 0 ∧
    ∀ n : Nat, C ≤ n →
      (f (n+p) + (p : Int)) % (m : Int) = f n % (m : Int)

private theorem shift_iter (f : Nat → Int) (m p C : Nat)
    (hs : ∀ n : Nat, C ≤ n →
      (f (n+p) + (p : Int)) % (m : Int) = f n % (m : Int))
    (n k : Nat) (hC : C ≤ n) :
    (f (n+k*p) + (k*p : Int)) % (m : Int) = f n % (m : Int) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := hs (n+k*p) (by omega)
    have hadd := (Int.emod_add_cancel_right ((k*p : Nat) : Int)).2 hstep
    simpa only [Nat.succ_mul, Int.natCast_add, Int.natCast_mul, Int.natCast_one,
      Int.add_mul, Int.one_mul, Nat.add_assoc, Int.add_assoc, Int.add_comm,
      Int.add_left_comm] using hadd.trans ih


private theorem shift_steer (f : Nat → Int) (m p C n : Nat) (target : Int)
    (hm : 0 < m) (hC : C ≤ n)
    (hs : ∀ n : Nat, C ≤ n →
      (f (n+p) + (p : Int)) % (m : Int) = f n % (m : Int))
    (hr : f n % ((p % m : Nat) : Int) =
      target % ((p % m : Nat) : Int)) :
    ∃ k : Nat, f (n+k*p) % (m : Int) = target % (m : Int) := by
  let r := p % m
  have hdiv : (r : Int) ∣ (f n-target) := by
    apply (Int.dvd_iff_emod_eq_zero).2
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).1 hr
  obtain ⟨q, hq⟩ := hdiv
  let k : Nat := (q % (m : Int)).toNat
  have hnonneg : 0 ≤ q % (m : Int) :=
    Int.emod_nonneg _ (by omega)
  have hk : (k : Int) = q % (m : Int) := by
    exact Int.toNat_of_nonneg hnonneg
  have hp : (p : Int) % (m : Int) = (r : Int) := by
    exact (Int.natCast_emod p m).symm
  have hmul : (((k*p : Nat) : Int)) % (m : Int) =
      (f n-target) % (m : Int) := by
    calc
      (((k*p : Nat) : Int)) % (m : Int) = ((k : Int)*(p : Int)) % (m : Int) := by simp
      _ = (((k : Int) % (m : Int)) * ((p : Int) % (m : Int))) % (m : Int) :=
        Int.mul_emod _ _ _
      _ = ((q % (m : Int)) * (r : Int)) % (m : Int) := by rw [hk, hp, Int.emod_emod]
      _ = (q*(r : Int)) % (m : Int) := by simp only [Int.mul_emod, Int.emod_emod]
      _ = (f n-target) % (m : Int) := by rw [Int.mul_comm, ← hq]
  have hit := shift_iter f m p C hs n k hC
  have heq : (f (n+k*p)+(f n-target)) % (m : Int) =
      (target+(f n-target)) % (m : Int) := by
    calc
      (f (n+k*p)+(f n-target)) % (m : Int)
          = (f (n+k*p)+((k*p : Nat):Int)) % (m : Int) := by
              calc
                _ = (f (n+k*p) % (m:Int) + (f n-target) % (m:Int)) % (m:Int) := Int.add_emod ..
                _ = (f (n+k*p) % (m:Int) + (((k*p:Nat):Int)) % (m:Int)) % (m:Int) := by rw [hmul]
                _ = _ := (Int.add_emod ..).symm
      _ = f n % (m : Int) := by simpa only [Int.natCast_mul] using hit
      _ = (target+(f n-target)) % (m : Int) := by congr 1 <;> omega
  exact ⟨k, (Int.emod_add_cancel_right (f n-target)).1 heq⟩


/-- A uniform eventually additive drift by a period not divisible by the modulus
    forces surjectivity modulo every modulus, with arbitrarily late witnesses.
    The induction reduces mod m to the nonzero remainder p mod m. -/
theorem dense_all_moduli (f : Nat → Int)
    (H : ∀ (m : Nat), 1 < m → HasShift f m) :
    ∀ (m : Nat), 0 < m → ∀ (target : Int) (L : Nat),
      ∃ n : Nat, L ≤ n ∧ f n % (m : Int) = target % (m : Int) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm target L
    by_cases h1 : m = 1
    · subst m
      exact ⟨L, by omega, by simp⟩
    · have hm1 : 1 < m := by omega
      obtain ⟨p, C, hp, hneq, hs⟩ := H m hm1
      let r := p % m
      have hrpos : 0 < r := Nat.pos_of_ne_zero hneq
      have hrlt : r < m := Nat.mod_lt p hm
      obtain ⟨n, hn, hmod⟩ := ih r hrlt hrpos target (max C L)
      have hC : C ≤ n := by omega
      obtain ⟨k, hk⟩ := shift_steer f m p C n target hm hC hs hmod
      refine ⟨n+k*p, ?_, hk⟩
      have hL : L ≤ n := by omega
      omega

#print axioms dense_all_moduli

end ShiftSurjectivity
