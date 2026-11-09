import ThreeShallowNumeric
import ThreeShallowFiniteBridge
namespace BB6.Agent43ThreeShallowAll
open BB6.Agent43TwoShallowFinite

private theorem profile_bounds (t alpha C L O : Nat)
 (ht : t≤1) (h : (alpha,C,L,O)=triple t) :
 1≤alpha ∧ 392≤C ∧ 56≤L ∧ L≤84 ∧ O≤232 := by
 have ht' : t=0 ∨ t=1 := by omega
 rcases ht' with he|he <;> subst t <;> simp [triple] at h <;> omega

/-- Any exact three-shallow scalar wall equation at a critical index n>=14
is inconsistent, irrespective of all three depth-two run lengths. -/
theorem no_three_shallow_numeric_all
 (n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E : Nat)
 (hn : 14≤n) (hs : 3*s≤n) (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1)
 (hprofile1 : (alpha,C1,L1,O1)=triple t1)
 (hprofile2 : (beta,C2,L2,O2)=triple t2)
 (hprofile3 : (gamma,C3,L3,O3)=triple t3)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*r))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+C3*(8^s*((2^alpha*8^u)*(2^beta*8^v))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*((2^gamma*8^r)*E+R3)+R2)+R1) : False := by
 by_cases hbig : 58≤n
 · obtain ⟨haPos,hc1,hl1min,hl1max,ho1⟩ := profile_bounds t1 alpha C1 L1 O1 ht1 hprofile1
   obtain ⟨hbPos,hc2,hl2min,hl2max,ho2⟩ := profile_bounds t2 beta C2 L2 O2 ht2 hprofile2
   obtain ⟨hcPos,hc3,hl3min,hl3max,ho3⟩ := profile_bounds t3 gamma C3 L3 O3 ht3 hprofile3
   exact BB6.Agent43ThreeLayer.no_three_shallow_numeric_58
     n s u v r p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E
     hbig hs haPos hbPos hcPos hP hD hc1 hc2 hc3 hl1min hl1max hl2min hl2max
     hl3min hl3max ho1 ho2 ho3 hR1 hR2 hR3 hE hK hEq
 · have hn58 : n<58 := by omega
   have hdPos : 0<d := by
     by_cases hz : d=0
     · rw [hz] at hD
       simp at hD
     · omega
   have hpowBound : 8^s≤14*n+92 := by
     have hh := Nat.mul_le_mul_left (8^s) hdPos
     have he : 8^s*d=14*n+92 := hD
     simpa [he] using hh
   have hs3 : s≤3 := by
     by_cases h : s≤3
     · exact h
     · exfalso
       have he : 4≤s := by omega
       have hqmin : (8:Nat)^4≤8^s := Nat.pow_le_pow_right (by decide) he
       have hdlim : 14*n+92<4096 := by omega
       have hqval : (8:Nat)^4=4096 := by decide
       omega
   exact BB6.Agent43ThreeShallowFinite.no_three_small_numeric
     n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E
     hn hn58 hs3 ht1 ht2 ht3 hprofile1 hprofile2 hprofile3 hP hD hR1 hR2 hR3 hE hK hEq

#print axioms no_three_shallow_numeric_all
end BB6.Agent43ThreeShallowAll
