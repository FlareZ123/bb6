import ValuationOne
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34Valuation
open BB6.Agent46

/-- Exact if-and-only-if classification of every source predecessor in
    either valuation-one sector, including all exceptional section cases. -/
theorem val1_parent_iff (a k x y u : Nat)
    (hy : 5 ≤ y)
    (hval : x+y=2*(2*u+1) ∨ x+y+1=2*(2*u+1)) :
    secNext (a,k)=some (x,y) ↔ a=x+y-2 ∧ 2*k+2=y := by
  constructor
  · intro h
    rcases hval with he | ho
    · exact val1_even_sum_parent a k x y u hy he h
    · exact val1_odd_sum_parent a k x y u hy ho h
  · rintro ⟨ha,hk⟩
    have ha0 : a≠0 := by omega
    have ha1 : a≠1 := by omega
    have hk0 : k≠0 := by omega
    have hlow : 2*k≤a := by omega
    apply (section_preimage_all_iff a k x y).mpr
    simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
      if_neg hk0,if_pos hlow]
    constructor <;> omega

/-- Valuation-one targets with odd right counter have no incoming
    section edge from any source configuration. -/
theorem val1_odd_right_no_parent (a k x y u : Nat)
    (hy : 5 ≤ y)
    (hval : x+y=2*(2*u+1) ∨ x+y+1=2*(2*u+1))
    (hodd : y%2=1) : secNext (a,k)≠some (x,y) := by
  intro h
  have hh := (val1_parent_iff a k x y u hy hval).mp h
  omega

def CReach (a k : Nat) : Prop :=
  ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (a,k)

/-- All-time genuine blank-section reachability for a valuation-one
    target is equivalent to reachability of its forced direct parent. -/
theorem val1_blank_reach_iff (x y u : Nat)
    (hy : 5 ≤ y) (hyeven : y%2=0)
    (hval : x+y=2*(2*u+1) ∨ x+y+1=2*(2*u+1)) :
    CReach x y ↔ CReach (x+y-2) ((y-2)/2) := by
  have heqk : 2*((y-2)/2)+2=y := by omega
  have hstep : secNext (x+y-2,(y-2)/2)=some (x,y) :=
    (val1_parent_iff (x+y-2) ((y-2)/2) x y u hy hval).mpr
      ⟨rfl,heqk⟩
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero =>
      simp [BB6.Agent8Section.run] at hn
      omega
    | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hn
      | some p =>
        rcases p with ⟨a,k⟩
        have hedge : secNext (a,k)=some (x,y) := by
          simpa [BB6.Agent8Section.run,hp] using hn
        obtain ⟨ha,hk⟩ := (val1_parent_iff a k x y u hy hval).mp hedge
        have hk' : k=(y-2)/2 := by omega
        exact ⟨n,by simpa [ha,hk'] using hp⟩
  · rintro ⟨n,hn⟩
    exact ⟨n+1,by simp [BB6.Agent8Section.run,hn,hstep]⟩

#print axioms val1_parent_iff
#print axioms val1_odd_right_no_parent
#print axioms val1_blank_reach_iff
end BB6.Agent34Valuation
