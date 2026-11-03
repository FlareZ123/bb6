import L1AllPrefixBridge
import L0OneResetCoverage
import Init.Omega

namespace BB6.Agent50ResetCount
open BB6.Agent1Quarter
open BB6.Agent1UpperTail
open BB6.Agent47P1
open BB6.Agent45TwoRoot
open BB6.Agent1RootWall

/-- Source inversion with a faithful exact count of positive-depth edges. -/
inductive CountCone (b0 d0 : Nat) : Nat → Nat → Nat → Nat → Prop where
  | root : CountCone b0 d0 b0 d0 0 0
  | parent (b d m z t k c : Nat)
      (hprev : CountCone b0 d0 b d m z)
      (hb : 8≤b) (hb4 : b%4=0) (hd : d%2=1)
      (hi : inverseAt b d t = some (k,c))
      (hk : 2≤k) (hc : c%2=1) :
      CountCone b0 d0 (2*k-4) (c+4) (m+t+1)
        (z + if t=0 then 0 else 1)

/-- Every original odd cone carries an exact positive-depth edge count. -/
theorem odd_cone_has_count (b0 d0 b d m : Nat)
    (h:OddCone b0 d0 b d m) :
    ∃ z, CountCone b0 d0 b d m z := by
  induction h with
  | root => exact ⟨0,CountCone.root⟩
  | parent b d m t k c hprev hb hb4 hd hi hk hc ih =>
    obtain ⟨z,hz⟩ := ih
    exact ⟨z + if t=0 then 0 else 1,
       CountCone.parent b d m z t k c hz hb hb4 hd hi hk hc⟩

/-- Count-zero histories are upper tails; count-one histories decompose
    into an upper prefix, one true positive inverse and an upper suffix. -/
theorem cone_shape (b0 d0 b d m z : Nat)
    (h:CountCone b0 d0 b d m z) :
    (z=0 → ∃ n, UpperTail b0 d0 0 b d m n) ∧
    (z=1 → ∃ bp dp mp r t k c n,
      UpperTail b0 d0 0 bp dp mp r ∧
      8≤bp ∧ bp%4=0 ∧ dp%2=1 ∧
      inverseAt bp dp t = some (k,c) ∧
      2≤k ∧ c%2=1 ∧ 1≤t ∧
      UpperTail (2*k-4) (c+4) (mp+t+1) b d m n) := by
  induction h with
  | root =>
    constructor
    · intro _
      exact ⟨0,UpperTail.root⟩
    · intro hz
      omega
  | parent b d m z t k c hprev hb hb4 hd hi hk hc ih =>
    constructor
    · intro hzero
      have ht : t=0 := by
        by_cases ht0 : t=0
        · exact ht0
        · simp [ht0] at hzero
      have hz : z=0 := by simpa [ht] using hzero
      obtain ⟨n,htail⟩ := ih.1 hz
      have hstep := UpperTail.step b d m n k c htail hb hb4 hd
        (by simpa [ht] using hi) hk hc
      exact ⟨n+1, by simpa only [ht, Nat.zero_add] using hstep⟩
    · intro hone
      by_cases ht : t=0
      · have hz : z=1 := by simpa [ht] using hone
        obtain ⟨bp,dp,mp,r,tp,kp,cp,n,hpre,hbp,hbp4,hdp,hip,hkp,hcp,htp,hpost⟩ := ih.2 hz
        have hstep := UpperTail.step b d m n k c hpost hb hb4 hd
          (by simpa [ht] using hi) hk hc
        exact ⟨bp,dp,mp,r,tp,kp,cp,n+1,hpre,hbp,hbp4,hdp,
          hip,hkp,hcp,htp,by simpa only [ht, Nat.zero_add] using hstep⟩
      · have htpos : 1≤t := by omega
        have hz : z=0 := by
          simp [ht] at hone
          omega
        obtain ⟨r,hpre⟩ := ih.1 hz
        exact ⟨b,d,m,r,t,k,c,0,hpre,hb,hb4,hd,hi,hk,hc,htpos,
          UpperTail.root⟩

/-- The affine wall from either authentic critical feeder cannot be entered
    with fewer than two positive-depth inverse edges. -/
theorem wall_requires_two_resets
    (q b d m z : Nat) (root : Bool) (hq : 1≤q)
    (hcone : CountCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m z)
    (hwall : b=4*m+64*q+(if root then 12 else 16)) : 2≤z := by
  by_cases hlt : 2≤z
  · exact hlt
  have h01 : z=0 ∨ z=1 := by omega
  have hshape := cone_shape _ _ b d m z hcone
  rcases h01 with hz | hz
  · obtain ⟨n,htail⟩ := hshape.1 hz
    have heq := upper_tail_wall _ _ 0 b d m n q
       (if root then 12 else 16) htail hwall
    exact False.elim ((no_initial_upper_wall q n root hq) (by simpa using heq))
  · obtain ⟨bp,dp,mp,r,t,k,c,n,hpre,hbp,hbp4,hdp,hi,hk,hc,ht,hpost⟩ := hshape.2 hz
    cases root with
    | false =>
      exact False.elim (BB6.Agent50L1All.l1_one_reset_cone_no_wall q bp dp mp r t k c b d m n
        hq (by simpa using hpre) hbp hbp4 hdp hi ht hk hc hpost (by simpa using hwall))
    | true =>
      exact False.elim (BB6.Agent1OneReset.l0_one_reset_cone_no_wall q bp dp mp r t k c b d m n
        hq (by simpa using hpre) hbp hbp4 hdp hi ht hk hc hpost (by simpa using hwall))

/-- Original OddCone theorem with no hidden count premise: any wall history
    must possess a source-true annotation recording at least two resets. -/
theorem authentic_wall_history_needs_two
    (q b d m : Nat) (root : Bool) (hq : 1≤q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hwall : b=4*m+64*q+(if root then 12 else 16)) :
    ∃ z, CountCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m z ∧ 2≤z := by
  obtain ⟨z,hz⟩ := odd_cone_has_count _ _ b d m hcone
  exact ⟨z,hz,wall_requires_two_resets q b d m z root hq hz hwall⟩

#print axioms cone_shape
#print axioms wall_requires_two_resets
#print axioms authentic_wall_history_needs_two
end BB6.Agent50ResetCount
