import DyadicSignedGap
import DyadicStrip

namespace BB6.Agent21Dyadic

private theorem positive_tail (r : Nat) (w : List Nat)
    (hw : Positive (r::w)) : Positive w := by
  intro k hk
  exact hw k (by simp [hk])

/-- Once the leading gap is strictly below the bit budget, its exact
    2^r-divisible numerator admits a signed child. The completed/pending
    divisibility is equivalent at exactly b-r remaining bits. -/
theorem signed_strip_word (x y : Int) (r b : Nat) (w : List Nat)
    (hr : 0<r) (hrb : r<b)
    (hd : P b∣signedZ x y+acc (signedS x y) (r::w)) :
    ∃ z' : Int, (r:Int)%2=(y+1)%2 ∧
      P r*z'=signedZ x y+offset (signedS x y) r ∧
      P (b-r)∣z'+acc (signedS x y+shift r) w := by
  have hv := signed_first_gap x y r b w hr (by omega) hd
  have hone : signedZ x y+offset (signedS x y) r =
      -(x+y+(x+y)%2) := by
    rw [signed_one_numer,signed_parity_cost x y r hv.1]
    omega
  have hdiv : P r∣signedZ x y+offset (signedS x y) r := by
    rw [hone]
    exact hv.2
  obtain ⟨z',hz'⟩ := hdiv
  refine ⟨z',hv.1,hz'.symm,?_⟩
  have hdiv' : P (b-r+r)∣signedZ x y+acc (signedS x y) (r::w) := by
    simpa only [show b-r+r=b by omega] using hd
  exact (word_strip_dvd_iff
    (signedS x y) (signedZ x y) (signedS x y+shift r)
    z' r (b-r) w rfl hz'.symm).mp hdiv'

/-- Every genuinely nonzero b-bit adjusted sum with an OpenAt
    witness has an exact signed *child* OpenAt at strictly lower
    precision. The tail remains pending if and only if the original
    word was pending. -/
theorem signed_open_descends (x y : Int) (b : Nat)
    (hb : 0<b)
    (hnot : ¬P b∣-(x+y+(x+y)%2))
    (ho : OpenAt (signedS x y) (signedZ x y) b) :
    ∃ r : Nat, ∃ z' : Int, 0<r ∧ r<b ∧
      (r:Int)%2=(y+1)%2 ∧
      P r*z'=signedZ x y+offset (signedS x y) r ∧
      OpenAt (signedS x y+shift r) z' (b-r) := by
  rcases ho with ⟨w,hp,hc,hd⟩ | ⟨w,k,hk,hp,hc,hd⟩
  · cases w with
    | nil =>
        simp [cost] at hc
        omega
    | cons r tail =>
        have hr : 0<r := hp r (by simp)
        have hc' : r+cost tail=b := by simpa only [cost_cons] using hc
        have hrlt : r<b := signed_first_gap_strict x y r b tail
          hr (by omega) hd hnot
        obtain ⟨z',hpar,hprefix,hdiv⟩ :=
          signed_strip_word x y r b tail hr hrlt hd
        have htail : Positive tail := positive_tail r tail hp
        have hcost : cost tail=b-r := by omega
        refine ⟨r,z',hr,hrlt,hpar,hprefix,?_⟩
        exact Or.inl ⟨tail,htail,hcost,hdiv⟩
  · cases w with
    | nil =>
        have hc' : k=b+1 := by simpa [cost] using hc
        have hpos : 0<k := by omega
        have hgap := signed_first_gap_min x y k b [] hpos hb
          (by simpa only [List.nil_append] using hd)
        have hmin : min k b=b := Nat.min_eq_right (by omega)
        rw [hmin] at hgap
        exact (hnot hgap.2).elim
    | cons r tail =>
        have hr : 0<r := hp r (by simp)
        have hc' : r+cost (tail++[k])=b+1 := by
          simpa only [List.cons_append,cost_cons] using hc
        have ht : cost (tail++[k])=cost tail+k := by
          rw [cost_append]
          simp [cost]
        have hrlt : r<b := by omega
        have hd' : P b∣signedZ x y+
            acc (signedS x y) (r::(tail++[k])) := by
          simpa only [List.cons_append] using hd
        obtain ⟨z',hpar,hprefix,hdiv⟩ :=
          signed_strip_word x y r b (tail++[k]) hr hrlt hd'
        have htail : Positive (tail++[k]) := by
          simpa only [List.cons_append] using positive_tail r (tail++[k])
            (by simpa only [List.cons_append] using hp)
        have hcost : cost (tail++[k])=(b-r)+1 := by omega
        refine ⟨r,z',hr,hrlt,hpar,hprefix,?_⟩
        exact Or.inr ⟨tail,k,hk,htail,hcost,hdiv⟩

#print axioms signed_strip_word
#print axioms signed_open_descends
end BB6.Agent21Dyadic
