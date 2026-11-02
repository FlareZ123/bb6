import CRange
import Lean.Elab.Tactic.Omega

namespace BB6.CBack
open BB6.CReachBridge

/-- Every reachable middle-zero state has odd first counter. -/
theorem reached_kzero_odd (a c : Nat) (h : BB6CLine.Reach (a,0,c)) : a%2=1 := by
  cases h with
  | init => omega
  | next s t hs hn =>
      rcases s with ⟨x,k,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          omega
        · rcases k with _|k
          · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
            omega
          · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
            omega
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          omega
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _|x
        · by_cases hk:k%2=0
          · simp [BB6CLine.nextC,hk] at hn
          · simp only [BB6CLine.nextC,hk,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at hn
            omega
        · simp [BB6CLine.nextC] at hn

/-- Any reached high-sector state with k>=3 has its unique high-sector predecessor. -/
theorem reached_high_pred (a k c : Nat)
    (h:BB6CLine.Reach (a,k+3,c+4)) :
    BB6CLine.Reach (a+1,k+2,c+5) := by
  cases h with
  | next s t hs hn =>
      rcases s with ⟨x,m,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp [BB6CLine.nextC] at hn
        · rcases m with _|m <;> simp [BB6CLine.nextC] at hn
        · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _|x
        · by_cases hm:m%2=0 <;> simp [BB6CLine.nextC,hm] at hn
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          rcases hn with ⟨ha,hk,hc⟩
          have heq : (x+1,m,e+1+1+1+1) = (a+1,k+2,c+5) := by
            simp only [Prod.mk.injEq]
            omega
          exact heq ▸ hs

/-- Reversing an arbitrary run of high transitions to a high-sector hub. -/
theorem reverse_high (a k c q : Nat)
    (h : BB6CLine.Reach (a,k+q+3,c+4)) :
    BB6CLine.Reach (a+q,k+3,c+q+4) := by
  induction q generalizing a c with
  | zero => simpa using h
  | succ q ih =>
      have hp : BB6CLine.Reach (a+1,k+q+3,c+5) := by
        apply reached_high_pred a (k+q+1) c
        simpa only [Nat.add_assoc, Nat.succ_eq_add_one] using h
      have hh := ih (a+1) (c+1) hp
      have he : (a+1+q,k+3,(c+1)+q+4) = (a+(q+1),k+3,c+(q+1)+4) := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      exact he ▸ hh


/-- The only predecessor of a zero-right state with positive middle counter. -/
theorem reached_zero_prev (a k : Nat) (h : BB6CLine.Reach (a,k+1,0)) :
    BB6CLine.Reach (a,k,1) := by
  cases h with
  | next s t hs hn =>
      rcases s with ⟨x,m,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp [BB6CLine.nextC] at hn
        · rcases m with _|m <;> simp [BB6CLine.nextC] at hn
        · simp [BB6CLine.nextC] at hn
      · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
        rcases hn with ⟨ha,hk,hc⟩
        have heq : (x,m,1)=(a,k,1) := by
          simp only [Prod.mk.injEq]
          exact ⟨ha, by omega, trivial⟩
        exact heq ▸ hs
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _|x
        · by_cases hm:m%2=0 <;> simp [BB6CLine.nextC,hm] at hn
        · simp [BB6CLine.nextC] at hn

/-- The only predecessor of a right-counter-one state with middle>=3. -/
theorem reached_one_prev (a k : Nat) (h : BB6CLine.Reach (a,k+3,1)) :
    BB6CLine.Reach (a,k+1,3) := by
  cases h with
  | next s t hs hn =>
      rcases s with ⟨x,m,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp [BB6CLine.nextC] at hn
        · rcases m with _|m <;> simp [BB6CLine.nextC] at hn
        · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
        rcases hn with ⟨ha,hk,hc⟩
        have heq : (x,m,3)=(a,k+1,3) := by
          simp only [Prod.mk.injEq]
          exact ⟨ha, by omega, trivial⟩
        exact heq ▸ hs
      · rcases x with _|x
        · by_cases hm:m%2=0 <;> simp [BB6CLine.nextC,hm] at hn
        · simp [BB6CLine.nextC] at hn

/-- The only predecessor of a c=3 state with middle>=3. -/
theorem reached_three_prev (a k : Nat) (h : BB6CLine.Reach (a,k+3,3)) :
    BB6CLine.Reach (a+1,k+2,4) := by
  cases h with
  | next s t hs hn =>
      rcases s with ⟨x,m,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp [BB6CLine.nextC] at hn
        · rcases m with _|m <;> simp [BB6CLine.nextC] at hn
        · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _|x
        · by_cases hm:m%2=0 <;> simp [BB6CLine.nextC,hm] at hn
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          rcases hn with ⟨ha,hk,hc⟩
          have heq : (x+1,m,e+4)=(a+1,k+2,4) := by
            simp only [Prod.mk.injEq]
            omega
          exact heq ▸ hs


/-- Unique predecessor chain from any late c=0 reset to the k=2 high hub. -/
theorem reached_zero_hub (a q : Nat) (h: BB6CLine.Reach (a,q+7,0)) :
    BB6CLine.Reach (a+q+2,2,q+5) := by
  have h1 : BB6CLine.Reach (a,q+6,1) := by
    have heq : (a,(q+6)+1,0)=(a,q+7,0) := by
      simp only [Prod.mk.injEq]
    exact reached_zero_prev a (q+6) (heq.symm ▸ h)
  have h2 : BB6CLine.Reach (a,q+4,3) := by
    have heq : (a,(q+3)+3,1)=(a,q+6,1) := by
      simp only [Prod.mk.injEq]
    have hh := reached_one_prev a (q+3) (heq.symm ▸ h1)
    have heq2 : (a,(q+3)+1,3)=(a,q+4,3) := by
      simp only [Prod.mk.injEq]
    exact heq2 ▸ hh
  have h3 : BB6CLine.Reach (a+1,q+3,4) := by
    have heq : (a,(q+1)+3,3)=(a,q+4,3) := by
      simp only [Prod.mk.injEq]
    have hh := reached_three_prev a (q+1) (heq.symm ▸ h2)
    have heq2 : (a+1,(q+1)+2,4)=(a+1,q+3,4) := by
      simp only [Prod.mk.injEq]
    exact heq2 ▸ hh
  have h4 : BB6CLine.Reach (a+1+q,3,q+4) := by
    have hh := reverse_high (a+1) 0 0 q
    have heq : (a+1,0+q+3,0+4)=(a+1,q+3,4) := by
      simp [Nat.zero_add]
    have hi := hh (heq.symm ▸ h3)
    simpa [Nat.zero_add] using hi
  have h5 := reached_high_pred (a+1+q) 0 q h4
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h5


/-- A k=2 high hub with first counter not congruent to 2 modulo 4
    cannot originate in an even zero-left high branch. -/
theorem reached_hub_prev (a c:Nat)
    (h:BB6CLine.Reach (a,2,c+4)) (hm:a%4≠2) :
    BB6CLine.Reach (a+1,1,c+5) := by
  cases h with
  | next s t hs hn =>
      rcases s with ⟨x,m,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp [BB6CLine.nextC] at hn
        · rcases m with _|m
          · simp [BB6CLine.nextC] at hn
          · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
            omega
        · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _|x
        · by_cases hk:m%2=0
          · simp only [BB6CLine.nextC,hk,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at hn
            omega
          · simp [BB6CLine.nextC,hk] at hn
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          rcases hn with ⟨ha,hk,hc⟩
          have heq : (x+1,m,e+4)=(a+1,1,c+5) := by
            simp only [Prod.mk.injEq]
            omega
          exact heq ▸ hs


/-- Every k=1 high-sector state has either high predecessor at k=0,
    or a c=0 reset predecessor with exactly odd right counter. -/
theorem reached_one_high_or_reset (a c:Nat)
    (h:BB6CLine.Reach (a,1,c+4)) :
    BB6CLine.Reach (a+1,0,c+5) ∨
      ∃ k:Nat, c+4=2*k+1 ∧ BB6CLine.Reach (a+2,k,0) := by
  cases h with
  | next s t hs hn =>
      rcases s with ⟨x,m,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp [BB6CLine.nextC] at hn
        · rcases m with _|m <;> simp [BB6CLine.nextC] at hn
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          rcases hn with ⟨ha,hk,hc⟩
          right
          refine ⟨m,?_,?_⟩
          · omega
          · have heq : (x+2,m,0)=(a+2,m,0) := by
              simp only [Prod.mk.injEq]
              exact ⟨by omega, trivial⟩
            exact heq ▸ hs
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _|x
        · by_cases hm:m%2=0 <;> simp [BB6CLine.nextC,hm] at hn
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          rcases hn with ⟨ha,hk,hc⟩
          left
          have heq : (x+1,m,e+4)=(a+1,0,c+5) := by
            simp only [Prod.mk.injEq]
            omega
          exact heq ▸ hs


/-- Every reached k=0 high state with first counter >=7 must have come
    from the unique odd zero-left high branch. -/
theorem reached_high_kzero_prev (a c:Nat)
    (h:BB6CLine.Reach (a+7,0,c+4)) :
    ∃ k:Nat, k%2=1 ∧ a+7=2*k+3 ∧ BB6CLine.Reach (0,k,c+4) := by
  cases h with
  | next s t hs hn =>
      rcases s with ⟨x,m,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          omega
        · rcases m with _|m <;> simp [BB6CLine.nextC] at hn
        · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _|x
        · by_cases hm:m%2=0
          · simp [BB6CLine.nextC,hm] at hn
          · simp only [BB6CLine.nextC,hm,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at hn
            rcases hn with ⟨ha,hk,hc⟩
            refine ⟨m, by omega, ?_, ?_⟩
            · omega
            · have heq : (0,m,e+4)=(0,m,c+4) := by
                simp only [Prod.mk.injEq]
                exact ⟨trivial,trivial,by omega⟩
              exact heq ▸ hs
        · simp [BB6CLine.nextC] at hn

#print axioms reached_kzero_odd
#print axioms reached_high_pred
end BB6.CBack
