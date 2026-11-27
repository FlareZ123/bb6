import ValuationCyclic

namespace ValuationPacking

/-- The only possible boundary successor 3w=K under a weak-cone
    recurrence has exponent j=1 and predecessor also on the boundary. -/
theorem boundary_predecessor (K v j w : Nat)
    (hK : 0 < K) (hcone : 3*v ≤ K)
    (hj : 0 < j) (hnext : 3*w=K)
    (heq : 4^j*w=v+K) : j=1 ∧ 3*v=K := by
  have hw : 0 < w := by omega
  have hvw : v ≤ w := by omega
  have hjone : j=1 := by
    by_cases h1 : j = 1
    · exact h1
    · have htwo : 2 ≤ j := by omega
      have hp : 4^2 ≤ 4^j := Nat.pow_le_pow_right (by omega) htwo
      have hprod := Nat.mul_le_mul_right w hp
      have h16 : 16*w ≤ v+K := by
        simp only [show (4:Nat)^2=16 by decide] at hprod
        rwa [heq] at hprod
      omega
  constructor
  · exact hjone
  · rw [hjone] at heq
    change 4*w=v+K at heq
    omega

theorem boundary_infinite_backwards (K : Nat) (v j : Int → Nat)
    (hK : 0 < K)
    (h : ∀ i : Int,
        0 < j i ∧ 3*v i ≤ K ∧ 4^(j i)*(v (i+1))=v i+K)
    (a : Int) (ha : 3*v a=K) :
    ∀ k : Nat, 3*(v (a-(k:Int)))=K ∧
      (0<k → j (a-(k:Int))=1) := by
  intro k
  induction k with
  | zero =>
    constructor
    · simpa using ha
    · intro hk
      omega
  | succ k ih =>
    let i : Int := a-((k+1:Nat):Int)
    have hshift : i+1=a-(k:Int) := by dsimp [i]; omega
    have hi := h i
    have hsucc : 3*(v (i+1))=K := by rw [hshift]; exact ih.1
    have he := boundary_predecessor K (v i) (j i) (v (i+1))
      hK hi.2.1 hi.1 hsucc hi.2.2
    constructor
    · simpa only [i] using he.2
    · intro _
      simpa only [i] using he.1

/-- Full primitive-period slope no-go under the natural weak cone.
    Any boundary equality forces all exponents 1; a genuine F-run
    contradicts it. -/
theorem no_primitive_periodic_weak_cone (K n : Nat) (v j : Int → Nat)
    (hKpos : 0 < K)
    (h : ∀ i : Int, 0 < v i ∧ 0 < j i ∧ 3*v i ≤ K ∧
      4^(j i)*(v (i+1)) = v i+K)
    (hn : 0<n)
    (hper : ∀ i : Int, j (i+(n:Int))=j i)
    (hmin : MinimalPeriod n j)
    (hgap : ∃ i : Int, 1 < j i)
    (hbudget : K ≤ 6*((List.finRange n).map
      (fun s : Fin n => j (s.val:Int))).sum) : False := by
  have hstrict (i : Int) : 3*v i < K := by
    have hle := (h i).2.2.1
    by_cases heq : 3*v i=K
    · have hall := boundary_infinite_backwards K v j hKpos
        (by
          intro x
          exact ⟨(h x).2.1,(h x).2.2.1,(h x).2.2.2⟩)
        i heq
      have hconstant := periodic_past_constant n j hn hper i 1
        (fun k hk => (hall k).2 hk)
      obtain ⟨p,hp⟩ := hgap
      have h1 := hconstant p
      omega
    · omega
  have hWitness : ∀ i : Int, Witness K (v i) (j i) (v (i+1)) := by
    intro i
    exact ⟨(h i).1,hstrict i,(h i).2.1,(h i).2.2.2⟩
  exact no_primitive_periodic_slope K n v j hWitness hn hper hmin hbudget

#print axioms boundary_predecessor
#print axioms boundary_infinite_backwards
#print axioms no_primitive_periodic_weak_cone
end ValuationPacking
