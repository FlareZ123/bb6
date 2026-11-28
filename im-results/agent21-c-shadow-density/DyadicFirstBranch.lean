import DyadicSignedOpen
import DyadicStrip

namespace BB6.Agent21Dyadic

/-- Every compatible word at a genuinely nonzero b-bit adjusted sum
    has a strict first gap, and the first gap is exactly one of the
    valuation-admissible inverse branches. The pending singleton case
    r=b+1 is handled rather than silently excluded. -/
theorem signed_open_strict_first_gap (x y : Int) (b : Nat)
    (hb : 0<b)
    (hnot : ¬P b∣-(x+y+(x+y)%2))
    (ho : OpenAt (signedS x y) (signedZ x y) b) :
    ∃ r : Nat, 0<r ∧ r<b ∧
      (r:Int)%2=(y+1)%2 ∧ P r∣-(x+y+(x+y)%2) := by
  rcases ho with ⟨w,hp,hc,hd⟩|⟨w,k,hk,hp,hc,hd⟩
  · cases w with
    | nil =>
        simp [cost] at hc
        omega
    | cons r tail =>
        have hr : 0<r := hp r (by simp)
        have hc' : r+cost tail=b := by simpa only [cost_cons] using hc
        have hrle : r≤b := by omega
        have hv := signed_first_gap x y r b tail hr hrle hd
        have hrlt := signed_first_gap_strict x y r b tail hr hrle hd hnot
        exact ⟨r,hr,hrlt,hv.1,hv.2⟩
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
        have hv := signed_first_gap x y r b (tail++[k])
          hr (by omega) (by simpa only [List.cons_append] using hd)
        exact ⟨r,hr,hrlt,hv.1,hv.2⟩

#print axioms signed_open_strict_first_gap
end BB6.Agent21Dyadic
