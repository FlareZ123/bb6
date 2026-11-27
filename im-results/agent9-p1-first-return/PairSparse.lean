import PairChunks
import BatchCarryChunks

namespace BB6.Agent9PairCarry
open BB6.Agent9BatchCarry

/-- For sorted inputs these are monotone images of disjoint consecutive
    ranges. Invalid boundary predecessors may safely be discarded. -/
def pairBranch (r off : Nat) (xs : List Nat) : List Nat :=
  (xs.filter (fun a => decide (off+1≤4*a ∧ 4*a+2≤off+r))).map (fun a => 4*a-off)

def unionSorted (xs ys : List Nat) : List Nat := join (xs.length+ys.length) xs ys

def pairSparseBack (r : Nat) (xs : List Nat) : List Nat :=
  unionSorted (unionSorted (pairBranch r 0 xs) (pairBranch r r xs))
    (unionSorted (pairBranch r (2*r+1) xs) (pairBranch r (3*r+1) xs))

theorem mem_unionSorted (c : Nat) (xs ys : List Nat) :
    c∈unionSorted xs ys ↔ c∈xs ∨ c∈ys := mem_join c _ xs ys

theorem pairBranch_sound (r off a c : Nat) (xs : List Nat) (ha : a∈xs)
    (hc : 1≤c ∧ c+2≤r) (he : 4*a=c+off) : c∈pairBranch r off xs := by
  apply List.mem_map.mpr
  refine ⟨a,List.mem_filter.mpr ⟨ha,by simp; omega⟩,by omega⟩

theorem pairSparseBack_sound (r a c : Nat) (xs : List Nat) (ha : a∈xs)
    (har : a+1≤r) (hc : 1≤c ∧ c+2≤r) (h : ((4*a)%(2*r+1))%r=c) :
    c∈pairSparseBack r xs := by
  unfold pairSparseBack
  simp only [mem_unionSorted]
  rcases four_cases r a c har hc h with h0|h1|h2|h3
  · exact Or.inl (Or.inl (pairBranch_sound r 0 a c xs ha hc (by omega)))
  · exact Or.inl (Or.inr (pairBranch_sound r r a c xs ha hc h1))
  · exact Or.inr (Or.inl (pairBranch_sound r (2*r+1) a c xs ha hc h2))
  · exact Or.inr (Or.inr (pairBranch_sound r (3*r+1) a c xs ha hc h3))

theorem pairSparse_step (r k : Nat) (xs : List Nat)
    (hs : ∀ c z, Walk (2*r+2) c (k+1) z → c/2∈xs) :
    ∀ c z, Walk (2*r) c (k+3) z → c/2∈pairSparseBack r xs := by
  intro c z h
  obtain ⟨hc,hc₀,hc₁⟩ := even_start r c (k+2) z (by simpa [Nat.add_assoc] using h)
  cases h with
  | cons _ _ w _ _ he tail =>
    cases tail with
    | cons _ _ a _ _ he' tail' =>
      have ht : Walk (2*r+2) a (k+1) z := by simpa [Nat.add_assoc] using tail'
      obtain ⟨ha,_,ha₁⟩ := even_start (r+1) a k z (by simpa [Nat.mul_add] using ht)
      have hp := pair_parent r (c/2) w (a/2) (by rwa [←hc]) (by rwa [←ha])
      exact pairSparseBack_sound r (a/2) (c/2) xs (hs a z ht) (by omega) ⟨hc₀,hc₁⟩ hp

def checkSparse (skip : List Nat) (r hi : Nat) (xs : List Nat) : Bool :=
  skip.contains (2*r-4) || !(decide (2*r-4≤hi ∧ (r-1)%2=0) && xs.contains ((r-1)/2))

theorem center_absent_sparse (skip : List Nat) (r hi k n : Nat) (xs : List Nat)
    (heq : n+4=2*r) (hhi : n≤hi) (hn : n∉skip)
    (hs : ∀ c z, Walk (2*r) c (k+1) z → c/2∈xs)
    (hcheck : checkSparse skip r hi xs=true) :
    ¬ ∃ z, Walk (2*r) ((n+2)/2) (k+1) z := by
  rintro ⟨z,h⟩
  have hcenter : (n+2)/2=r-1 := by omega
  obtain ⟨he,_,_⟩ := even_start r ((n+2)/2) k z h
  have hpar : (r-1)%2=0 := by omega
  have hmem := hs _ _ h
  rw [hcenter] at hmem
  simp [checkSparse,show 2*r-4=n by omega,hhi,hpar,hmem,hn] at hcheck

def pairSparseChunk (skip : List Nat) (hi r : Nat) (xs : List Nat) : Nat → Bool × List Nat
  | 0 => (checkSparse skip r hi xs,xs)
  | d+1 => if checkSparse skip r hi xs then
      pairSparseChunk skip hi (r-1) (pairSparseBack (r-1) xs) d
    else (false,xs)

theorem pairSparseChunk_sound (skip : List Nat) (hi r d k : Nat) (xs out : List Nat)
    (hlo : d+2≤r)
    (hs : ∀ c z, Walk (2*r) c (2*k+1) z → c/2∈xs)
    (hc : pairSparseChunk skip hi r xs d=(true,out)) :
    (∀ c z, Walk (2*(r-d)) c (2*(k+d)+1) z → c/2∈out) ∧
    (∀ n, 2*(r-d)≤n+4 → n+4≤2*r → n%2=0 → n≤hi → n∉skip →
      ¬ ∃ z, Walk (n+4) ((n+2)/2) (2*r+2*k+1-(n+4)) z) := by
  induction d generalizing r k xs out with
  | zero =>
    simp only [pairSparseChunk,Prod.mk.injEq] at hc
    obtain ⟨hgood,rfl⟩ := hc
    refine ⟨by simpa using hs,?_⟩
    intro n hn₀ hn₁ _ hnhi hn
    have heq : n+4=2*r := by omega
    have h := center_absent_sparse skip r hi (2*k) n xs heq hnhi hn hs hgood
    simpa [heq,show 2*r+2*k+1-2*r=2*k+1 by omega] using h
  | succ d ih =>
    by_cases hgood : checkSparse skip r hi xs=true
    · simp only [pairSparseChunk,hgood,ite_true] at hc
      have hstep : ∀ c z, Walk (2*(r-1)) c (2*(k+1)+1) z →
          c/2∈pairSparseBack (r-1) xs := by
        intro c z hz
        exact pairSparse_step (r-1) (2*k) xs
          (by simpa [show 2*(r-1)+2=2*r by omega] using hs) c z
          (by simpa [show 2*(k+1)+1=2*k+3 by omega] using hz)
      obtain ⟨hnew,hex⟩ := ih (r-1) (k+1) (pairSparseBack (r-1) xs) out
        (by omega) hstep hc
      refine ⟨?_,?_⟩
      · simpa [show r-1-d=r-(d+1) by omega,show k+1+d=k+(d+1) by omega] using hnew
      · intro n hn₀ hn₁ he hnhi hn
        by_cases h : n+4=2*r
        · have he' := center_absent_sparse skip r hi (2*k) n xs h hnhi hn hs hgood
          simpa [h,show 2*r+2*k+1-2*r=2*k+1 by omega] using he'
        · have hh := hex n (by omega) (by omega) he hnhi hn
          simpa [show 2*(r-1)+2*(k+1)+1=2*r+2*k+1 by omega] using hh
    · simp [pairSparseChunk,hgood] at hc

structure PairSparseCertificate (skip : List Nat) (R hi r : Nat) (xs : List Nat) : Prop where
  cover : ∀ c z, Walk (2*r) c (2*(R-r)+1) z → c/2∈xs
  excluded : ∀ n, 2*r≤n+4 → n+4≤2*R → n%2=0 → n≤hi → n∉skip →
    ¬ ∃ z, Walk (n+4) ((n+2)/2) (2*R+1-(n+4)) z

/-- Switch from packed to sparse representation by one exact kernel equality.
    A sorted or duplicate-free premise is unnecessary for soundness. -/
theorem pairSparse_convert (skip : List Nat) (R hi r bits : Nat) (xs : List Nat)
    (cert : PairCertificate skip R hi r bits) (hc : bits=packList xs) :
    PairSparseCertificate skip R hi r xs := by
  refine ⟨?_,cert.excluded⟩
  intro c z h
  apply (packList_sound xs (c/2)).mp
  rw [←hc]
  exact cert.cover c z h

theorem pairSparse_extend (skip : List Nat) (R hi r d : Nat) (xs out : List Nat)
    (hr : r≤R) (hlo : d+2≤r) (cert : PairSparseCertificate skip R hi r xs)
    (hc : pairSparseChunk skip hi r xs d=(true,out)) :
    PairSparseCertificate skip R hi (r-d) out := by
  obtain ⟨hnew,hex⟩ := pairSparseChunk_sound skip hi r d (R-r) xs out hlo cert.cover hc
  have hsum : 2*r+2*(R-r)+1=2*R+1 := by omega
  refine ⟨?_,?_⟩
  · simpa [show R-(r-d)=R-r+d by omega] using hnew
  · intro n hn₀ hn₁ he hnhi hn
    by_cases h : n+4≤2*r
    · simpa [hsum] using hex n hn₀ h he hnhi hn
    · exact cert.excluded n (by omega) hn₁ he hnhi hn

theorem pairSparse_interval (skip : List Nat) (R hi lo r : Nat) (xs : List Nat)
    (hr : 2*r≤lo+4) (hhi : hi+4≤2*R) (hK : 2*R+1≤2*lo+3)
    (hlo : 14≤lo) (cert : PairSparseCertificate skip R hi r xs) :
    ∀ n, lo≤n → n≤hi → n%2=0 → n∉skip → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro n hnlo hnhi he hn
  apply critical_reset_no_reach_batch (2*R+1) lo n (by omega) hnlo (by omega) (by omega) he
  intro hm
  have hcenter := ((mem_batch (2*R+1) lo n (by omega)).mp hm).2.2.2
  exact cert.excluded n (by omega) (by omega) he hnhi hn ((mem_live _ _ _).mp hcenter)

#print axioms pairSparseBack_sound
#print axioms pairSparse_step
#print axioms pairSparseChunk_sound
#print axioms pairSparse_convert
#print axioms pairSparse_extend
#print axioms pairSparse_interval
end BB6.Agent9PairCarry
