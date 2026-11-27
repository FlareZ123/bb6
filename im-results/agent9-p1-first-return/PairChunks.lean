import PairCarrySource
namespace BB6.Agent9PairCarry
open BB6.Agent9BatchCarry

/-- Allow an explicit finite list of unexcluded centers; each may be
    discharged independently at its own full horizon. -/
def checkPairExcept (skip : List Nat) (r hi bits : Nat) : Bool :=
  skip.contains (2*r-4) || checkPair r hi bits

theorem center_absent_except (skip : List Nat) (r hi k n bits : Nat) (heq : n+4=2*r)
    (hhi : n≤hi) (hn : n∉skip)
    (hs : ∀ c z, Walk (2*r) c (k+1) z → bits.testBit (c/2)=true)
    (hcheck : checkPairExcept skip r hi bits=true) :
    ¬ ∃ z, Walk (2*r) ((n+2)/2) (k+1) z := by
  apply center_absent r hi k n bits heq hhi hs
  simpa [checkPairExcept,show 2*r-4=n by omega,hn] using hcheck

/-- Tail-recursive paired-clock checker, returning the lower checkpoint.
    False means a birth was not excluded, not a machine classification. -/
def pairChunk (plan : List (Nat × Nat)) (skip : List Nat) (hi r bits : Nat) : Nat → Bool × Nat
  | 0 => (checkPairExcept skip r hi bits,bits)
  | d+1 => if checkPairExcept skip r hi bits then
      pairChunk plan skip hi (r-1) (pairBack plan (r-1) bits) d
    else (false,bits)

/-- Each chunk carries forward both its live-set coverage and every
    center exclusion, without evaluating the entire sweep in one term. -/
theorem pairChunk_sound (L : Nat) (skip : List Nat) (hi r d k bits out : Nat) (hlo : d+2≤r)
    (hcap : r<2^L)
    (hs : ∀ c z, Walk (2*r) c (2*k+1) z → bits.testBit (c/2)=true)
    (hc : pairChunk (spreadPlan L L) skip hi r bits d=(true,out)) :
    (∀ c z, Walk (2*(r-d)) c (2*(k+d)+1) z → out.testBit (c/2)=true) ∧
    (∀ n, 2*(r-d)≤n+4 → n+4≤2*r → n%2=0 → n≤hi → n∉skip →
      ¬ ∃ z, Walk (n+4) ((n+2)/2) (2*r+2*k+1-(n+4)) z) := by
  induction d generalizing r k bits out with
  | zero =>
    simp only [pairChunk,Prod.mk.injEq] at hc
    obtain ⟨hgood,rfl⟩ := hc
    refine ⟨by simpa using hs,?_⟩
    intro n hn₀ hn₁ _ hnhi hn
    have heq : n+4=2*r := by omega
    have h := center_absent_except skip r hi (2*k) n bits heq hnhi hn hs hgood
    simpa [heq,show 2*r+2*k+1-2*r=2*k+1 by omega] using h
  | succ d ih =>
    by_cases hgood : checkPairExcept skip r hi bits=true
    · simp only [pairChunk,hgood,ite_true] at hc
      have hstep : ∀ c z, Walk (2*(r-1)) c (2*(k+1)+1) z →
          (pairBack (spreadPlan L L) (r-1) bits).testBit (c/2)=true := by
        intro c z hz
        exact pair_walk_step L (r-1) (2*k) bits (by omega)
          (by simpa [show 2*(r-1)+2=2*r by omega] using hs) c z
          (by simpa [show 2*(k+1)+1=2*k+3 by omega] using hz)
      obtain ⟨hnew,hex⟩ := ih (r-1) (k+1) (pairBack (spreadPlan L L) (r-1) bits) out
        (by omega) (by omega) hstep hc
      refine ⟨?_,?_⟩
      · simpa [show r-1-d=r-(d+1) by omega,show k+1+d=k+(d+1) by omega] using hnew
      · intro n hn₀ hn₁ he hnhi hn
        by_cases h : n+4=2*r
        · have he' := center_absent_except skip r hi (2*k) n bits h hnhi hn hs hgood
          simpa [h,show 2*r+2*k+1-2*r=2*k+1 by omega] using he'
        · have hh := hex n (by omega) (by omega) he hnhi hn
          simpa [show 2*(r-1)+2*(k+1)+1=2*r+2*k+1 by omega] using hh
    · simp [pairChunk,hgood] at hc

/-- A certificate is always relative to the original common final clock
    F=2R+1; all intermediate checkpoints retain the true Walk relation. -/
structure PairCertificate (skip : List Nat) (R hi r : Nat) (bits : Nat) : Prop where
  cover : ∀ c z, Walk (2*r) c (2*(R-r)+1) z → bits.testBit (c/2)=true
  excluded : ∀ n, 2*r≤n+4 → n+4≤2*R → n%2=0 → n≤hi → n∉skip →
    ¬ ∃ z, Walk (n+4) ((n+2)/2) (2*R+1-(n+4)) z

theorem pairCert_start (skip : List Nat) (R hi : Nat) (hhi : hi+4<2*R) :
    PairCertificate skip R hi R (halfMask R) := by
  refine ⟨?_,?_⟩
  · intro c z h
    have ht : Walk (2*R) c 1 z := by simpa using h
    obtain ⟨_,h₁,h₂⟩ := even_start R c 0 z ht
    exact halfMask_sound R (c/2) ⟨h₁,h₂⟩
  · intro n hn₀ hn₁ _ hnhi _
    omega

theorem pairCert_extend (L : Nat) (skip : List Nat) (R hi r d bits out : Nat) (hr : r≤R)
    (hlo : d+2≤r) (hcap : r<2^L) (cert : PairCertificate skip R hi r bits)
    (hc : pairChunk (spreadPlan L L) skip hi r bits d=(true,out)) :
    PairCertificate skip R hi (r-d) out := by
  obtain ⟨hnew,hex⟩ := pairChunk_sound L skip hi r d (R-r) bits out hlo hcap cert.cover hc
  have hsum : 2*r+2*(R-r)+1=2*R+1 := by omega
  refine ⟨?_,?_⟩
  · simpa [show R-(r-d)=R-r+d by omega] using hnew
  · intro n hn₀ hn₁ he hnhi hn
    by_cases h : n+4≤2*r
    · simpa [hsum] using hex n hn₀ h he hnhi hn
    · exact cert.excluded n (by omega) hn₁ he hnhi hn

/-- The actual critical reset is excluded by the completed chunk chain. -/
theorem pairCert_interval (skip : List Nat) (R hi lo r bits : Nat)
    (hr : 2*r≤lo+4) (hhi : hi+4≤2*R) (hK : 2*R+1≤2*lo+3)
    (hlo : 14≤lo) (cert : PairCertificate skip R hi r bits) :
    ∀ n, lo≤n → n≤hi → n%2=0 → n∉skip → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro n hnlo hnhi he hn
  apply critical_reset_no_reach_batch (2*R+1) lo n (by omega) hnlo (by omega) (by omega) he
  intro hm
  have hcenter := ((mem_batch (2*R+1) lo n (by omega)).mp hm).2.2.2
  exact cert.excluded n (by omega) (by omega) he hnhi hn ((mem_live _ _ _).mp hcenter)

#print axioms center_absent_except
#print axioms pairChunk_sound
#print axioms pairCert_start
#print axioms pairCert_extend
#print axioms pairCert_interval
end BB6.Agent9PairCarry
