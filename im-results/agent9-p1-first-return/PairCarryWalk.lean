import PairCarryCore
import BatchCarry

namespace BB6.Agent9PairCarry
open BB6.Agent9BatchCarry

/-- At every even clock with at least one remaining edge, the carry is even. -/
theorem even_start (r c k z : Nat) (h : Walk (2*r) c (k+1) z) :
    c=2*(c/2) ∧ 1≤c/2 ∧ c/2+2≤r := by
  cases h with
  | cons _ _ _ _ _ he _ =>
    have hi := he.1
    unfold Interior at hi
    rcases he.2.2 with h|h <;> omega

/-- An even-to-even two-edge preimage reduces to one scaled arithmetic map. -/
theorem pair_parent (r b w a : Nat) (h₁ : Edge (2*r) (2*b) w)
    (h₂ : Edge (2*r+1) w (2*a)) : ((4*a)%(2*r+1))%r=b := by
  have hp₁ := ((edge_iff_parent _ _ _ h₁.2.1).mp h₁).2
  have hp₂ := ((edge_iff_parent _ _ _ h₂.2.1).mp h₂).2
  rw [show 2*(2*a)=4*a by omega] at hp₂
  rw [←hp₂]
  rw [Nat.mul_mod_mul_left] at hp₁
  omega

/-- Transport a sound scaled bitset back by two clocks. -/
theorem pair_walk_step (L r k bits : Nat) (hcap : r<2^L)
    (hs : ∀ c z, Walk (2*r+2) c (k+1) z → bits.testBit (c/2)=true) :
    ∀ c z, Walk (2*r) c (k+3) z →
      (pairBack (spreadPlan L L) r bits).testBit (c/2)=true := by
  intro c z h
  obtain ⟨hc,hc₀,hc₁⟩ := even_start r c (k+2) z (by simpa [Nat.add_assoc] using h)
  cases h with
  | cons _ _ w _ _ he tail =>
    cases tail with
    | cons _ _ a _ _ he' tail' =>
      have ht : Walk (2*r+2) a (k+1) z := by simpa [Nat.add_assoc] using tail'
      obtain ⟨ha,_,ha₁⟩ := even_start (r+1) a k z (by simpa [Nat.mul_add] using ht)
      have hp := pair_parent r (c/2) w (a/2) (by rwa [←hc]) (by rwa [←ha])
      exact pairBack_sound L r bits (a/2) (c/2) (by omega) (by omega)
        ⟨hc₀,hc₁⟩ hp (hs a z ht)

/-- At a checked even-clock center, no path of the positive residual length survives. -/
theorem center_absent (r hi k n bits : Nat) (heq : n+4=2*r)
    (hhi : n≤hi) (hs : ∀ c z, Walk (2*r) c (k+1) z → bits.testBit (c/2)=true)
    (hcheck : checkPair r hi bits=true) :
    ¬ ∃ z, Walk (2*r) ((n+2)/2) (k+1) z := by
  rintro ⟨z,h⟩
  have hcenter : (n+2)/2=r-1 := by omega
  obtain ⟨he,_,_⟩ := even_start r ((n+2)/2) k z h
  have hpar : (r-1)%2=0 := by omega
  have hbit := hs _ _ h
  rw [hcenter] at hbit
  simp [checkPair,show 2*r-4≤hi by omega,hpar,hbit] at hcheck

/-- A paired sweep is sound for every even center in its checked interval.
It begins at an even clock with an odd positive residual horizon, which remains
positive at all lower paired clocks. -/
theorem pairScan_sound (L hi r d k n bits : Nat) (hlo : d+2≤r)
    (hcap : r<2^L) (hs : ∀ c z, Walk (2*r) c (2*k+1) z → bits.testBit (c/2)=true)
    (hcheck : pairScan (spreadPlan L L) hi r bits d=true)
    (hn₀ : 2*(r-d)≤n+4) (hn₁ : n+4≤2*r) (heven : n%2=0) (hnhi : n≤hi) :
    ¬ ∃ z, Walk (n+4) ((n+2)/2) (2*r+2*k+1-(n+4)) z := by
  induction d generalizing r k bits with
  | zero =>
    have heq : n+4=2*r := by omega
    have h := center_absent r hi (2*k) n bits heq hnhi hs (by simpa [pairScan] using hcheck)
    simpa [heq,show 2*r+2*k+1-2*r=2*k+1 by omega] using h
  | succ d ih =>
    simp only [pairScan,Bool.and_eq_true] at hcheck
    by_cases h : n+4=2*r
    · have hc := center_absent r hi (2*k) n bits h hnhi hs hcheck.1
      simpa [h,show 2*r+2*k+1-2*r=2*k+1 by omega] using hc
    · have hstep : ∀ c z, Walk (2*(r-1)) c (2*(k+1)+1) z →
          (pairBack (spreadPlan L L) (r-1) bits).testBit (c/2)=true := by
        intro c z hz
        exact pair_walk_step L (r-1) (2*k) bits (by omega)
          (by simpa [show 2*(r-1)+2=2*r by omega] using hs) c z
          (by simpa [show 2*(k+1)+1=2*k+3 by omega] using hz)
      have hh := ih (r-1) (k+1) (pairBack (spreadPlan L L) (r-1) bits)
        (by omega) (by omega) hstep hcheck.2 (by omega) (by omega)
      simpa [show 2*(r-1)+2*(k+1)+1=2*r+2*k+1 by omega] using hh

/-- Public walk-level consequence, starting with the full scaled interior. -/
theorem pairCheck_sound (L R lo hi n : Nat) (hcap : R<2^L) (hlo : lo≤n)
    (hloeven : lo%2=0) (hhi : n≤hi) (hR : n+4≤2*R) (he : n%2=0)
    (hcheck : pairCheck L R lo hi=true) :
    ¬ ∃ z, Walk (n+4) ((n+2)/2) (2*R+1-(n+4)) z := by
  have hs : ∀ c z, Walk (2*R) c (2*0+1) z → (halfMask R).testBit (c/2)=true := by
    intro c z h
    obtain ⟨_,h₁,h₂⟩ := even_start R c 0 z h
    exact halfMask_sound R (c/2) ⟨h₁,h₂⟩
  have hh := pairScan_sound L hi R (R-(lo+4)/2) 0 n (halfMask R)
    (by omega) hcap hs hcheck (by omega) hR he hhi
  simpa using hh

#print axioms even_start
#print axioms pair_parent
#print axioms pair_walk_step
#print axioms pairCheck_sound
end BB6.Agent9PairCarry
