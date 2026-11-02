import GInverse

namespace BB6.Agent47P1
open BB6.P1Reduction

/-- Exactly the t-th positive-output inverse of the source G map, if it exists. -/
def inverseAt (b d : Nat) : Nat → Option (Nat × Nat)
  | 0 =>
      if 4 ≤ b ∧ b % 4 = 0 then
        some (b / 4 - 1, d + b / 2)
      else none
  | t+1 =>
      match inverseAt b d t with
      | none => none
      | some (k,c) =>
          if 3 ≤ c ∧ c % 2 = 1 then
            let v := (c - 3) / 2
            some (k + v / 2 + 1, v)
          else none

/-- Every computed inverse is an actual source-level GAncestor. -/
theorem inverseAt_sound (b d t k c : Nat)
    (h : inverseAt b d t = some (k,c)) : GAncestor b d k c := by
  induction t generalizing k c with
  | zero =>
      simp only [inverseAt] at h
      split at h
      · next hcond =>
        obtain ⟨hb,hmod⟩ := hcond
        have hk : b = 4 * (b/4-1) + 4 := by omega
        have hc : d + b/2 = d + 2*(b/4-1) + 2 := by omega
        cases (Option.some.inj h)
        have hroot := GAncestor.upper (b/4-1) d
        rw [←hk, ←hc] at hroot
        exact hroot
      · simp at h
  | succ t ih =>
      simp only [inverseAt] at h
      split at h
      · simp at h
      · next k0 c0 heq =>
        split at h
        · next hcond =>
          obtain ⟨hc3,hodd⟩ := hcond
          have hbase := ih k0 c0 heq
          have hs : GAncestor b d (k0+((c0-3)/2)/2+1) ((c0-3)/2) := by
            apply GAncestor.nest
            have hcv' : 2*((c0-3)/2)+3 = c0 := by omega
            rw [hcv']
            exact hbase
          obtain ⟨hk',hc'⟩ := Prod.mk.inj (Option.some.inj h)
          rw [←hk',←hc']
          exact hs
        · simp at h

/-- Every source ancestor occurs in the finite, executable inverse sequence. -/
theorem inverseAt_complete (b d k c : Nat)
    (h : GAncestor b d k c) :
    ∃ t, inverseAt b d t = some (k,c) ∧ c+t ≤ d+b/2 := by
  induction h with
  | upper k d =>
      refine ⟨0, ?_, ?_⟩
      · simp [inverseAt]
        omega
      · omega
  | nest b d k c h ih =>
      obtain ⟨t, ht, hbound⟩ := ih
      refine ⟨t+1, ?_, ?_⟩
      · simp [inverseAt, ht]
      · omega

/-- Converse to the source GAncestor_power lemma: all positive-output inverse
   branches have exactly the solutions of the shifted power-of-two equation. -/
theorem ancestor_exists_of_power (b d c t : Nat)
    (hb : 4 ≤ b) (hmod : b % 4 = 0)
    (heq : d + b/2 + 3 = 2^t * (c+3)) :
    ∃ k, GAncestor b d k c := by
  induction t generalizing c with
  | zero =>
      have hc : c = d + b/2 := by simpa using heq.symm
      let k := b/4-1
      have hk : b = 4*k+4 := by dsimp [k]; omega
      have hright : c = d+2*k+2 := by dsimp [k]; omega
      refine ⟨k, ?_⟩
      rw [hk, hright]
      exact GAncestor.upper k d
  | succ t ih =>
      have hshift : d+b/2+3 = 2^t*((2*c+3)+3) := by
        calc
          d+b/2+3 = 2^(t+1)*(c+3) := heq
          _ = (2^t*2)*(c+3) := by rw [Nat.pow_succ]
          _ = 2^t*(2*(c+3)) := by rw [Nat.mul_assoc]
          _ = 2^t*((2*c+3)+3) := by
            have hlin : 2*(c+3) = (2*c+3)+3 := by omega
            rw [hlin]
      obtain ⟨k,hk⟩ := ih (2*c+3) hshift
      exact ⟨k+c/2+1, GAncestor.nest b d k c hk⟩

theorem ancestor_exists_iff_power (b d c : Nat) (hb : 4 ≤ b)
    (hmod : b%4=0) :
    (∃ k, GAncestor b d k c) ↔
    ∃ t, d+b/2+3 = 2^t*(c+3) := by
  constructor
  · rintro ⟨k,hk⟩
    exact BB6.P1Reduction.GAncestor_power b d k c hk
  · rintro ⟨t,ht⟩
    exact ancestor_exists_of_power b d c t hb hmod ht

/-- The exceptional source input c=1 appears iff the shifted output counter
   is four times a power of two. -/
theorem exceptional_one_iff_power (b d : Nat)
    (hb : 4 ≤ b) (hmod : b%4=0) :
    (∃ k, GAncestor b d k 1) ↔
    ∃ t, d+b/2+3 = 4 * 2^t := by
  rw [ancestor_exists_iff_power b d 1 hb hmod]
  simp only [show 1+3=4 by omega]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t, by simpa [Nat.mul_comm] using ht⟩
  · rintro ⟨t,ht⟩
    exact ⟨t, by simpa [Nat.mul_comm] using ht⟩

theorem no_exceptional_one_iff (b d : Nat)
    (hb : 4 ≤ b) (hmod : b%4=0) :
    (∀ k, ¬GAncestor b d k 1) ↔
    ∀ t, d+b/2+3 ≠ 4 * 2^t := by
  constructor
  · intro h k heq
    have : ∃ k, GAncestor b d k 1 :=
      (exceptional_one_iff_power b d hb hmod).mpr ⟨k,heq⟩
    obtain ⟨j,hj⟩ := this
    exact h j hj
  · intro h k hk
    obtain ⟨t,ht⟩ := (exceptional_one_iff_power b d hb hmod).mp ⟨k,hk⟩
    exact h t ht

theorem inverse_iff_finite_search (b d k c : Nat) :
    GAncestor b d k c ↔ ∃ t ≤ d + b/2, inverseAt b d t = some (k,c) := by
  constructor
  · intro h
    obtain ⟨t,ht,hbound⟩ := inverseAt_complete b d k c h
    exact ⟨t,by omega,ht⟩
  · rintro ⟨t,_,ht⟩
    exact inverseAt_sound b d t k c ht

/-- Finite executable inverse list and its exact source-level membership proof. -/
def inverseList (b d : Nat) : List (Nat × Nat) :=
  ((List.range (d+b/2+1)).filterMap (inverseAt b d))

theorem inverse_iff_mem (b d k c : Nat) :
    GAncestor b d k c ↔ (k,c) ∈ inverseList b d := by
  rw [inverse_iff_finite_search]
  simp [inverseList, List.mem_filterMap]
  constructor
  · rintro ⟨t,ht,h⟩
    exact ⟨t,by simpa using (Nat.lt_succ_of_le ht), h⟩
  · rintro ⟨t,ht,h⟩
    exact ⟨t, by omega, h⟩

#print axioms inverseAt_sound
#print axioms inverseAt_complete
#print axioms ancestor_exists_iff_power
#print axioms no_exceptional_one_iff
#print axioms inverse_iff_mem
end BB6.Agent47P1
