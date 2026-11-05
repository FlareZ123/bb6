import SectionFastInverseOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Fast
open BB6.Agent46

/-- Bounded exact-image arithmetic with no recursive section evaluation. -/
def arithmeticValid (a k x y:Nat) : Bool :=
  let powers := List.range (fastCap x y)
  if a=0 then
    if k=0 then false
    else if k=1 then decide (x=0 ∧ y=4)
    else powers.any (fun n => decide
      (x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y))
  else if a=1 then
    if k=0 then false
    else if k=1 then false
    else if k=2 then decide (x=2 ∧ y=5)
    else if k=3 then decide (x=0 ∧ y=7)
    else powers.any (fun n => decide
      (x+y+1=2^n*16 ∧ (2*k-3)+16+3*n=x+2*y+2))
  else if k=0 then false
  else if 2*k≤a then decide (x=a-2*k ∧ y=2*k+2)
  else if a%2=0 then powers.any (fun n => decide
    (x+y=2^n*(2*(a-1)+6) ∧
     (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y))
  else powers.any (fun n => decide
    (x+y+1=2^n*(2*(a-1)+8) ∧
     (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2))

private theorem bounded_pow (x y f n:Nat) (hf:0<f)
    (h:(x+y=2^n*f) ∨ (x+y+1=2^n*f)) : n<fastCap x y := by
  have hle : 2^n ≤ 2^n*f := Nat.le_mul_of_pos_right (2^n) hf
  apply pow_depth_bounded
  rcases h with h|h <;> omega

private theorem any_iff_bounded (x y:Nat) (P:Nat→Prop) [DecidablePred P] :
  ((List.range (fastCap x y)).any (fun n=>decide (P n)))=true ↔
    ∃ n<fastCap x y, P n := by
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]

private theorem bounded_iff (x y :Nat) (P:Nat→Prop) [DecidablePred P]
    (hpow : ∀ n, P n → ∃ f:Nat, 0<f ∧
      (x+y=2^n*f ∨ x+y+1=2^n*f)) :
  ((List.range (fastCap x y)).any (fun n=>decide (P n)))=true ↔
    ∃ n, P n := by
  rw [any_iff_bounded]
  constructor
  · rintro ⟨n,_,hn⟩
    exact ⟨n,hn⟩
  · rintro ⟨n,hn⟩
    obtain ⟨f,hf,h⟩:=hpow n hn
    exact ⟨n,bounded_pow x y f n hf h,hn⟩

/-- The bounded arithmetic test agrees with the original unbounded source
    preimage criterion for every output whose second coordinate is at least 5. -/
theorem arithmeticValid_criterion (a k x y:Nat) (hy:5≤y) :
  arithmeticValid a k x y = true ↔ sectionPreimageCriterion a k x y := by
  by_cases ha0:a=0
  · by_cases hk0:k=0
    · simp [arithmeticValid,sectionPreimageCriterion,ha0,hk0]
    · by_cases hk1:k=1
      · simp [arithmeticValid,sectionPreimageCriterion,ha0,hk0,hk1]
      · simp only [arithmeticValid,sectionPreimageCriterion,ha0,hk0,hk1,
          ite_true,ite_false]
        apply bounded_iff x y
          (fun n => x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y)
        intro n hn
        exact ⟨8,by decide,Or.inl hn.1⟩
  · by_cases ha1:a=1
    · by_cases hk0:k=0
      · simp [arithmeticValid,sectionPreimageCriterion,ha0,ha1,hk0]
      · by_cases hk1:k=1
        · simp [arithmeticValid,sectionPreimageCriterion,ha0,ha1,hk0,hk1]
        · by_cases hk2:k=2
          · simp [arithmeticValid,sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2]
          · by_cases hk3:k=3
            · simp [arithmeticValid,sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3]
            · simp only [arithmeticValid,sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3,
                ite_true,ite_false]
              apply bounded_iff x y
                (fun n => x+y+1=2^n*16 ∧ (2*k-3)+16+3*n=x+2*y+2)
              intro n hn
              exact ⟨16,by decide,Or.inr hn.1⟩
    · by_cases hk0:k=0
      · simp [arithmeticValid,sectionPreimageCriterion,ha0,ha1,hk0]
      · by_cases hregion:2*k≤a
        · simp [arithmeticValid,sectionPreimageCriterion,ha0,ha1,hk0,hregion]
        · by_cases heven:a%2=0
          · simp only [arithmeticValid,sectionPreimageCriterion,ha0,ha1,hk0,hregion,
              heven,ite_true,ite_false]
            apply bounded_iff x y (fun n => x+y=2^n*(2*(a-1)+6) ∧
              (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y)
            intro n hn
            exact ⟨2*(a-1)+6,by omega,Or.inl hn.1⟩
          · simp only [arithmeticValid,sectionPreimageCriterion,ha0,ha1,hk0,hregion,
              heven,ite_true,ite_false]
            apply bounded_iff x y (fun n => x+y+1=2^n*(2*(a-1)+8) ∧
              (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2)
            intro n hn
            exact ⟨2*(a-1)+8,by omega,Or.inr hn.1⟩

/-- Filter the logarithmically many candidates by bounded arithmetic only. -/
def arithmeticCandidates (x y:Nat) : List (Nat×Nat) :=
 (fastUnfiltered x y).filter (fun p => arithmeticValid p.1 p.2 x y)

theorem arithmeticCandidates_exact (a k x y:Nat) (hy:5≤y) :
  (a,k)∈arithmeticCandidates x y ↔ secNext (a,k)=some (x,y) := by
  simp only [arithmeticCandidates,List.mem_filter]
  constructor
  · rintro ⟨_,hvalid⟩
    apply (complete_section_inverse a k x y hy).mpr
    exact (arithmeticValid_criterion a k x y hy).mp hvalid
  · intro h
    refine ⟨fastUnfiltered_complete a k x y hy h,?_⟩
    exact (arithmeticValid_criterion a k x y hy).mpr
       ((complete_section_inverse a k x y hy).mp h)

#print axioms arithmeticValid_criterion
#print axioms arithmeticCandidates_exact
end BB6.Agent11Fast
