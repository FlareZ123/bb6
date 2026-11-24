import FullSectionInverse
import Lean.Elab.Tactic.Omega

/-!
# Exact odd/even source-parent fan

This is the parity-dual companion to the even/odd complete source fan.
It isolates the only source-parent alternatives for an odd-left,
even-right target whose mass x+y+1 is not a power of two. The theorem
is about the unchanged original section edge relation `secNext`;
it is not a blank-root reachability assertion.
-/

namespace BB6.Agent3OddEvenFan
open BB6.Agent46

/-- Exact source-parent classification for a large odd/even target
    with non-power mass. There is one direct affine parent, together
    with precisely the odd-depth odd-left high-bounce parents. -/
theorem odd_even_nonpower_parent_iff
    (a k x y : Nat)
    (hx : 5 < x) (hxo : x%2=1)
    (hy : 6≤y) (hye : y%2=0)
    (hnp : ∀ n : Nat, x+y+1 ≠ 2^n) :
    secNext (a,k)=some (x,y) ↔
      (a=x+y-2 ∧ k=(y-2)/2) ∨
      (∃ n : Nat, n%2=1 ∧ a%2=1 ∧ 3≤a ∧ a<2*k ∧
        x+y+1=2^(n+1)*(a+3) ∧
        2*k+a+7+3*n=x+2*y) := by
  have hy5 : 5≤y := by omega
  constructor
  · intro hedge
    have hp := (complete_section_inverse a k x y hy5).mp hedge
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,hk0] at hp
      · by_cases hk1 : k=1
        · simp [sectionPreimageCriterion,ha0,hk0,hk1] at hp
          omega
        · simp only [sectionPreimageCriterion,if_pos ha0,
              if_neg hk0,if_neg hk1] at hp
          rcases hp with ⟨n,hpow,_⟩
          have heven : (x+y)%2=0 := by
            rw [hpow]
            simp [Nat.mul_mod]
          omega
    · by_cases ha1 : a=1
      · by_cases hk0 : k=0
        · simp [sectionPreimageCriterion,ha0,ha1,hk0] at hp
        · by_cases hk1 : k=1
          · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1] at hp
          · by_cases hk2 : k=2
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2] at hp
              omega
            · by_cases hk3 : k=3
              · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] at hp
                omega
              · simp only [sectionPreimageCriterion,if_neg ha0,
                    if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,
                    if_neg hk3] at hp
                rcases hp with ⟨n,hpow,_⟩
                have hpower : x+y+1=2^(n+4) := by
                  calc
                    x+y+1 = 2^n*16 := hpow
                    _ = 2^n*2^4 := by congr 1
                    _ = 2^(n+4) := by rw [← Nat.pow_add]
                exact (hnp (n+4) hpower).elim
      · have ha2 : 2≤a := by omega
        by_cases hk0 : k=0
        · simp [sectionPreimageCriterion,ha0,ha1,hk0] at hp
        · by_cases hlow : 2*k≤a
          · simp only [sectionPreimageCriterion,if_neg ha0,
                if_neg ha1,if_neg hk0,if_pos hlow] at hp
            rcases hp with ⟨hxx,hyy⟩
            left
            constructor <;> omega
          · by_cases hae : a%2=0
            · simp only [sectionPreimageCriterion,if_neg ha0,
                  if_neg ha1,if_neg hk0,if_neg hlow,if_pos hae] at hp
              rcases hp with ⟨n,hpow,_⟩
              have heven : (x+y)%2=0 := by
                rw [hpow]
                simp [Nat.mul_mod]
              omega
            · simp only [sectionPreimageCriterion,if_neg ha0,
                  if_neg ha1,if_neg hk0,if_neg hlow,if_neg hae] at hp
              rcases hp with ⟨n,hpow,hcost⟩
              have haodd : a%2=1 := by omega
              have hfactor : 2*(a-1)+8=2*(a+3) := by omega
              have hmass : x+y+1=2^(n+1)*(a+3) := by
                calc
                  x+y+1 = 2^n*(2*(a-1)+8) := hpow
                  _ = 2^n*(2*(a+3)) := by rw [hfactor]
                  _ = 2^(n+1)*(a+3) := by rw [Nat.pow_succ]; ac_rfl
              have hcost' : 2*k+a+7+3*n=x+2*y := by omega
              have hnodd : n%2=1 := by omega
              right
              exact ⟨n,hnodd,haodd,by omega,by omega,hmass,hcost'⟩
  · rintro (⟨ha,hk⟩ | ⟨n,hnodd,haodd,ha3,hlow,hmass,hcost⟩)
    · subst a
      subst k
      have ha0 : x+y-2≠0 := by omega
      have ha1 : x+y-2≠1 := by omega
      have hk0 : (y-2)/2≠0 := by omega
      have hlow' : 2*((y-2)/2)≤x+y-2 := by omega
      have hp : sectionPreimageCriterion (x+y-2) ((y-2)/2) x y := by
        simp only [sectionPreimageCriterion,if_neg ha0,
          if_neg ha1,if_neg hk0,if_pos hlow']
        omega
      exact (complete_section_inverse _ _ _ _ hy5).mpr hp
    · have ha0 : a≠0 := by omega
      have ha1 : a≠1 := by omega
      have hk0 : k≠0 := by omega
      have hhigh : ¬ 2*k≤a := by omega
      have hae : ¬ a%2=0 := by omega
      have hfactor : 2*(a-1)+8=2*(a+3) := by omega
      have hpow : x+y+1=2^n*(2*(a-1)+8) := by
        calc
          x+y+1 = 2^(n+1)*(a+3) := hmass
          _ = 2^n*(2*(a+3)) := by rw [Nat.pow_succ]; ac_rfl
          _ = 2^n*(2*(a-1)+8) := by rw [hfactor]
      have hcost' :
          (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2 := by omega
      have hp : sectionPreimageCriterion a k x y := by
        simp only [sectionPreimageCriterion,if_neg ha0,
          if_neg ha1,if_neg hk0,if_neg hhigh,if_neg hae]
        exact ⟨n,hpow,hcost'⟩
      exact (complete_section_inverse _ _ _ _ hy5).mpr hp

/-- Exact blank-root reachability decomposition for the same target.
    This is an equivalence, not an exclusion: every possible first
    predecessor is represented by one of the two source-parent branches. -/
theorem blank_reach_iff_odd_even_nonpower_parent_fan
    (x y : Nat)
    (hx : 5 < x) (hxo : x%2=1)
    (hy : 6≤y) (hye : y%2=0)
    (hnp : ∀ n : Nat, x+y+1 ≠ 2^n) :
    (∃ t, BB6.Agent8Section.run secNext t (some (5,1))=some (x,y)) ↔
      (∃ t, BB6.Agent8Section.run secNext t (some (5,1))=
        some (x+y-2,(y-2)/2)) ∨
      (∃ n a k t, n%2=1 ∧ a%2=1 ∧ 3≤a ∧ a<2*k ∧
        x+y+1=2^(n+1)*(a+3) ∧
        2*k+a+7+3*n=x+2*y ∧
        BB6.Agent8Section.run secNext t (some (5,1))=some (a,k)) := by
  constructor
  · rintro ⟨t,ht⟩
    cases t with
    | zero =>
        simp [BB6.Agent8Section.run] at ht
        omega
    | succ t =>
        cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
        | none => simp [BB6.Agent8Section.run,hp] at ht
        | some p =>
            rcases p with ⟨a,k⟩
            have hstep : secNext (a,k)=some (x,y) := by
              simpa [BB6.Agent8Section.run,hp] using ht
            rcases (odd_even_nonpower_parent_iff a k x y hx hxo hy hye hnp).mp hstep with
              hdirect | hhigh
            · left
              rcases hdirect with ⟨ha,hk⟩
              exact ⟨t,by simpa [ha,hk] using hp⟩
            · right
              rcases hhigh with ⟨n,hn,haodd,ha3,hlow,hmass,hcost⟩
              exact ⟨n,a,k,t,hn,haodd,ha3,hlow,hmass,hcost,by simpa using hp⟩
  · rintro (⟨t,ht⟩ | ⟨n,a,k,t,hn,haodd,ha3,hlow,hmass,hcost,ht⟩)
    · refine ⟨t+1,?_⟩
      have hedge : secNext (x+y-2,(y-2)/2)=some (x,y) :=
        (odd_even_nonpower_parent_iff (x+y-2) ((y-2)/2) x y hx hxo hy hye hnp).mpr
          (Or.inl ⟨rfl,rfl⟩)
      simpa [BB6.Agent8Section.run,ht,hedge]
    · refine ⟨t+1,?_⟩
      have hedge : secNext (a,k)=some (x,y) :=
        (odd_even_nonpower_parent_iff a k x y hx hxo hy hye hnp).mpr
          (Or.inr ⟨n,hn,haodd,ha3,hlow,hmass,hcost⟩)
      simpa [BB6.Agent8Section.run,ht,hedge]

#print axioms odd_even_nonpower_parent_iff
#print axioms blank_reach_iff_odd_even_nonpower_parent_fan

end BB6.Agent3OddEvenFan
