import SharpPackingSmall

/-!
Sharp numerical four-adic upper capacity for all K>=15, in Lean 4.36.
F n is the finite sum n + floor(n/4) + floor(n/16) + ...
The edge-family injection from ValuationEdges is a separate proof edge.
-/
namespace SharpPackingUniversal

def F (n : Nat) : Nat :=
  if h : n=0 then 0 else n+F (n/4)
termination_by n
decreasing_by omega

theorem F_recur (n : Nat) : F n = n+F (n/4) := by
  by_cases hz : n=0
  · subst n
    simp [F]
  · simp [F, hz]

theorem F_ge_self (n : Nat) : n≤F n := by
  rw [F_recur]
  omega

theorem F_upper (n : Nat) : 3*F n≤4*n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n=0
    · subst n
      simp [F]
    · have hlt : n/4<n := by omega
      have hq := ih (n/4) hlt
      have hfloor : 4*(n/4)≤n := by omega
      rw [F_recur]
      omega

theorem F_lower_three (n : Nat) :
    n+n/4+n/16≤F n := by
  have h0 := F_recur n
  have h1 := F_recur (n/4)
  have hge := F_ge_self ((n/4)/4)
  have hdiv : (n/4)/4=n/16 := by omega
  rw [hdiv] at h1 hge
  omega

theorem F_three_of_lt64 (n : Nat) (h : n<64) :
    F n=n+n/4+n/16 := by
  have h0 := F_recur n
  have h1 := F_recur (n/4)
  have h2 := F_recur ((n/4)/4)
  have hdiv : (n/4)/4=n/16 := by omega
  have hdiv0 : ((n/4)/4)/4=0 := by omega
  have hFzero : F 0=0 := by simp [F]
  rw [hdiv0,hFzero] at h2
  rw [hdiv] at h1 h2
  omega

theorem large_bound (K : Nat) (h : 151≤K) :
    15*(F ((K-1)/3)-F (K/4))≤2*K := by
  have hu := F_upper ((K-1)/3)
  have hl := F_lower_three (K/4)
  have harith : 60*((K-1)/3) ≤
      6*K+45*(K/4+(K/4)/4+(K/4)/16) := by omega
  omega

theorem small_bound (K : Nat)
    (hlo : 15≤K) (hhi : K≤150) :
    15*(F ((K-1)/3)-F (K/4))≤2*K := by
  have hb : F ((K-1)/3) =
      SharpPackingSmall.truncatedF ((K-1)/3) := by
    simpa [SharpPackingSmall.truncatedF] using
      F_three_of_lt64 ((K-1)/3) (by omega)
  have ha : F (K/4) =
      SharpPackingSmall.truncatedF (K/4) := by
    simpa [SharpPackingSmall.truncatedF] using
      F_three_of_lt64 (K/4) (by omega)
  rw [hb,ha]
  exact SharpPackingSmall.small_range K hlo hhi

/-- Sharp numerical capacity inequality valid for every K>=15. -/
theorem sharp_capacity (K : Nat) (h : 15≤K) :
    15*(F ((K-1)/3)-F (K/4))≤2*K := by
  by_cases hsmall : K≤150
  · exact small_bound K h hsmall
  · exact large_bound K (by omega)

/-- Sum of base-four digits, defined by exact Euclidean division. -/
def digitSum4 (n : Nat) : Nat :=
  if h : n=0 then 0 else n%4+digitSum4 (n/4)
termination_by n
decreasing_by omega

theorem digitSum4_recur (n : Nat) :
    digitSum4 n=n%4+digitSum4 (n/4) := by
  by_cases hz : n=0
  · subst n
    simp [digitSum4]
  · simp [digitSum4,hz]

/-- Exact formula F(n)=(4*n-digitSum4(n))/3, without division
    in the proof statement. -/
theorem digit_identity (n : Nat) :
    3*F n+digitSum4 n=4*n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n=0
    · subst n
      simp [F,digitSum4]
    · have hlt : n/4<n := by omega
      have hi := ih (n/4) hlt
      have hr := F_recur n
      have hd := digitSum4_recur n
      have hdiv : 4*(n/4)+n%4=n := by omega
      omega

/-- Number of factors four in a strictly positive integer. -/
def fourVal (n : Nat) : Nat :=
  if hn : n=0 then 0
  else if hd : n%4=0 then 1+fourVal (n/4) else 0
termination_by n
decreasing_by omega

/-- Each finite difference of F is precisely one plus its four-adic
    exponent. This bridges the numerical capacity theorem to the
    exact optimal edge-family charging argument. -/
theorem F_jump : ∀ n : Nat, 0<n →
    F n = F (n-1)+1+fourVal n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hf := F_recur n
    have hfprev := F_recur (n-1)
    by_cases hmod : n%4=0
    · have hqpos : 0<n/4 := by omega
      have hlt : n/4<n := by omega
      have hi := ih (n/4) hlt hqpos
      have hdiv : (n-1)/4=n/4-1 := by omega
      have hv : fourVal n=1+fourVal(n/4) := by
        simp [fourVal, Nat.ne_of_gt hn, hmod]
      rw [hdiv] at hfprev
      omega
    · have hdiv : (n-1)/4=n/4 := by omega
      have hv : fourVal n=0 := by
        simp [fourVal, Nat.ne_of_gt hn, hmod]
      rw [hdiv] at hfprev
      omega

#print axioms F_recur
#print axioms F_upper
#print axioms F_lower_three
#print axioms F_three_of_lt64
#print axioms sharp_capacity
#print axioms digit_identity
#print axioms F_jump
end SharpPackingUniversal
