import CBack
import Lean.Elab.Tactic.Omega

namespace BB6.CHubSplit

private theorem eq3 {a b c d e f : Nat}
    (h1:a=d) (h2:b=e) (h3:c=f) :
    ((a,b,c):Nat×Nat×Nat)=(d,e,f) := by
  cases h1; cases h2; cases h3; rfl

/-- Every large reached k=2 high-sector hub has exactly two possible
predecessor branch families, including the zero-left even portal. -/
theorem reached_two_split (A C:Nat) (hA:5≤A)
    (h:BB6CLine.Reach (A,2,C+4)) :
    BB6CLine.Reach (A+1,1,C+5) ∨
      ∃k:Nat, k%2=0 ∧ A=2*k+2 ∧ BB6CLine.Reach (0,k,C+7) := by
  cases h with
  | next s t hs hn =>
      rcases s with ⟨x,m,d⟩
      rcases d with _|_|_|_|e
      · rcases x with _|_|x
        · simp [BB6CLine.nextC] at hn
        · rcases m with _|m
          · simp [BB6CLine.nextC] at hn
          · simp [BB6CLine.nextC] at hn
            omega
        · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _|x
        · by_cases hm:m%2=0
          · simp only [BB6CLine.nextC,hm,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at hn
            rcases hn with ⟨ha,hk,hc⟩
            right
            refine ⟨m,hm,?_,?_⟩
            · omega
            · have he : (0,m,e+4)=(0,m,C+7) := by apply eq3 <;> omega
              exact he ▸ hs
          · simp [BB6CLine.nextC,hm] at hn
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          rcases hn with ⟨ha,hk,hc⟩
          left
          have he : (x+1,m,e+4)=(A+1,1,C+5) := by apply eq3 <;> omega
          exact he ▸ hs

/-- Contract an arbitrary zero-left high sweep to its unique k=2 high hub. -/
theorem zero_high_hub (K C : Nat) (hK:3≤K) (hC:4≤C)
    (h:BB6CLine.Reach (0,K,C)) :
    BB6CLine.Reach (K-2,2,C+K-2) := by
  have hi : BB6CLine.Reach (0,0+(K-3)+3,(C-4)+4) := by
    have he : (0,0+(K-3)+3,(C-4)+4)=(0,K,C) := by apply eq3 <;> omega
    exact he.symm ▸ h
  have hh := BB6.CBack.reverse_high 0 0 (C-4) (K-3) hi
  have hj : BB6CLine.Reach (K-3,3,(C-4)+(K-3)+4) := by
    have he : (0+(K-3),0+3,(C-4)+(K-3)+4) =
      (K-3,3,(C-4)+(K-3)+4) := by apply eq3 <;> omega
    exact he ▸ hh
  have h2 := BB6.CBack.reached_high_pred (K-3) 0 ((C-4)+(K-3)) hj
  have he : (K-3+1,0+2,(C-4)+(K-3)+5) = (K-2,2,C+K-2) := by
    apply eq3 <;> omega
  exact he ▸ h2

/-- High-sector zero-middle states along the blank orbit have first counter 1 mod 4. -/
theorem high_zero_mod4 (a c:Nat) (ha:7≤a) (hc:4≤c)
    (h:BB6CLine.Reach (a,0,c)) : a%4=1 := by
  have hi : BB6CLine.Reach ((a-7)+7,0,(c-4)+4) := by
    have he : ((a-7)+7,0,(c-4)+4)=(a,0,c) := by apply eq3 <;> omega
    exact he.symm ▸ h
  rcases BB6.CBack.reached_high_kzero_prev (a-7) (c-4) hi with ⟨k,ho,hk,_⟩
  omega

#print axioms reached_two_split
end BB6.CHubSplit
