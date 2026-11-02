import EvenThreeFamily

/-!
A full if-and-only-if for genuine blank-orbit reachability of the
(8z,4w+3) family when z>=3. The proof establishes both real T transitions
of the unique surviving inverse feeder.
-/

namespace BB6.Agent7EightThree

private theorem paired_first (z w : Nat) (hz : 3≤z) :
    BB6.Agent1.T (6*z+2*w-4) (2*z+2*w+4) =
      some (6*z+2*w-1,2*z+2*w+2) := by
  have h0 : 2*z+2*w+4 ≠ 0 := by omega
  have h1 : 2*z+2*w+4 ≠ 1 := by omega
  have he : (6*z+2*w-4)%2=0 := by omega
  simp [BB6.Agent1.T,h0,h1,he]
  omega

private theorem paired_second (z w : Nat) (hz : 3≤z) :
    BB6.Agent1.T (6*z+2*w-1) (2*z+2*w+2) =
      some (8*z,4*w+3) := by
  have h0 : 2*z+2*w+2 ≠ 0 := by omega
  have h1 : 2*z+2*w+2 ≠ 1 := by omega
  have h2 : 2*z+2*w+2 ≠ 2 := by omega
  have h3 : 2*z+2*w+2 ≠ 3 := by omega
  have he : (6*z+2*w-1)%2≠0 := by omega
  have hk : (6*z+2*w-1)/2+1=3*z+w := by omega
  have hc : 2*z+2*w+2-2=2*z+2*w := by omega
  have hg : BB6.Agent1.G (3*z+w) (2*z+2*w) =
      (8*z,4*w+3) := by
    have hlow : 2*z+2*w<2*(3*z+w) := by omega
    rw [BB6.Agent1.G]
    simp only [hlow, dite_true]
    have hk' : 3*z+w - ((2*z+2*w)/2+1)=2*z-1 := by omega
    have hv' : 2*(2*z+2*w)+3=4*z+4*w+3 := by omega
    rw [hk',hv',BB6.Agent1.G]
    have hlow2 : ¬ 4*z+4*w+3 < 2*(2*z-1) := by omega
    have hhigh2 : ¬ 4*z+4*w+3 ≤ 2*(2*z-1)+1 := by omega
    simp [hlow2,hhigh2]
    congr 1 <;> omega
  simp only [BB6.Agent1.T, if_neg h0, if_neg h1, if_neg he,
    if_neg h2, if_neg h3]
  rw [hk,hc,hg]

/-- A mathematically exact, global two-step gateway equivalence.
    The RHS even-counter sector admits separate power-of-two constraints. -/
theorem reachable_eight_fourw_three_iff_feeder (z w : Nat) (hz : 3≤z) :
    BB6.Agent1.Reach (8*z) (4*w+3) ↔
      BB6.Agent1.Reach (6*z+2*w-4) (2*z+2*w+4) := by
  constructor
  · intro hr
    obtain ⟨k,v,hanc,hv,hreach⟩ :=
      BB6.Agent50P1.positive_G_feeder (8*z) (4*w+3)
        (by omega) (by omega) (by omega)
        (exceptional_not_one_all z w (by omega)) hr
    obtain ⟨t,ht,hmass⟩ :=
      (BB6.Agent1Quarter.ancestor_iff_power_mass (8*z) (4*w+3) k v
        (by omega) (by omega) (by omega)).mp hanc
    have hp : 4*(z+w)+6=2^t*(v+3) := by omega
    have hdepth := depth_le_one (z+w) v t hp
    cases t with
    | zero =>
      have hh : 4*(z+w)+6=v+3 := by simpa using hp
      have hk : 2*k=4*z-2 := by omega
      have hpre : 2*k-4=4*z-6 := by omega
      rw [hpre] at hreach
      have hinv := BB6.Agent1.reachable_even_mod4 (4*z-6) (v+4)
        hreach (by omega) (by omega)
      rcases hinv with h | h
      · omega
      · omega
    | succ t =>
      have htzero : t=0 := by omega
      subst t
      have hvval : v=2*z+2*w := by
        have hh : 4*(z+w)+6=2*(v+3) := by simpa using hp
        omega
      have hpre : 2*k-4=6*z+2*w-4 := by omega
      rwa [hpre,hvval] at hreach
  · intro hr
    exact BB6.Agent1.Reach.next _ _ _ _
      (BB6.Agent1.Reach.next _ _ _ _ hr (paired_first z w hz))
      (paired_second z w hz)

#print axioms paired_first
#print axioms paired_second
#print axioms reachable_eight_fourw_three_iff_feeder
end BB6.Agent7EightThree
