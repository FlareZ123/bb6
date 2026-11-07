import TThreeHighTTwoZero
set_option maxHeartbeats 0
namespace CascadeHighTTwo

private theorem pow_two_mod9_six (k:Nat) : 2^(k+6)%9=2^k%9 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow_two_mod9_reduce (k:Nat):2^k%9=2^(k%6)%9 := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk:k<6
    · simp [Nat.mod_eq_of_lt hk]
    · have hsmall:k-6<k:=by omega
      have he:k=(k-6)+6:=by omega
      rw [he, pow_two_mod9_six, ih (k-6) hsmall]
      have hkmod:((k-6)+6)%6=(k-6)%6:=by omega
      rw [hkmod]

theorem offset_case_4 (n:Nat) (hn:20≤n) (hr:n%18=4):
 (8*2^(n-8)+(n-8))%9=1 := by
  have hk6:(n-8)%6=2:=by omega
  have hk9:(n-8)%9=5:=by omega
  have hp:=pow_two_mod9_reduce (n-8)
  rw [hk6] at hp
  simp at hp
  omega

theorem offset_case_5 (n:Nat) (hn:20≤n) (hr:n%18=5):
 (8*2^(n-8)+(n-8))%9=7 := by
  have hk6:(n-8)%6=3:=by omega
  have hk9:(n-8)%9=6:=by omega
  have hp:=pow_two_mod9_reduce (n-8)
  rw [hk6] at hp
  simp at hp
  omega

theorem offset_case_10 (n:Nat) (hn:20≤n) (hr:n%18=10):
 (8*2^(n-8)+(n-8))%9=7 := by
  have hk6:(n-8)%6=2:=by omega
  have hk9:(n-8)%9=2:=by omega
  have hp:=pow_two_mod9_reduce (n-8)
  rw [hk6] at hp
  simp at hp
  omega

theorem offset_case_11 (n:Nat) (hn:20≤n) (hr:n%18=11):
 (8*2^(n-8)+(n-8))%9=4 := by
  have hk6:(n-8)%6=3:=by omega
  have hk9:(n-8)%9=3:=by omega
  have hp:=pow_two_mod9_reduce (n-8)
  rw [hk6] at hp
  simp at hp
  omega

theorem offset_case_16 (n:Nat) (hn:20≤n) (hr:n%18=16):
 (8*2^(n-8)+(n-8))%9=4 := by
  have hk6:(n-8)%6=2:=by omega
  have hk9:(n-8)%9=8:=by omega
  have hp:=pow_two_mod9_reduce (n-8)
  rw [hk6] at hp
  simp at hp
  omega

theorem offset_case_17 (n:Nat) (hn:20≤n) (hr:n%18=17):
 (8*2^(n-8)+(n-8))%9=1 := by
  have hk6:(n-8)%6=3:=by omega
  have hk9:(n-8)%9=0:=by omega
  have hp:=pow_two_mod9_reduce (n-8)
  rw [hk6] at hp
  simp at hp
  omega

/-- Exact period-18 classification of the even-reset subtraction offset modulo nine. -/
theorem source_offset_mod9 (n:Nat) (hn:20≤n)
 (hsector:n%6=4∨n%6=5):
 ((n%18=4∨n%18=17)∧(8*2^(n-8)+(n-8))%9=1) ∨
 ((n%18=5∨n%18=10)∧(8*2^(n-8)+(n-8))%9=7) ∨
 ((n%18=11∨n%18=16)∧(8*2^(n-8)+(n-8))%9=4) := by
  have h18:n%18=4∨n%18=5∨n%18=10∨n%18=11∨n%18=16∨n%18=17 := by omega
  rcases h18 with h4|h5|h10|h11|h16|h17
  · exact Or.inl ⟨Or.inl h4,offset_case_4 n hn h4⟩
  · exact Or.inr (Or.inl ⟨Or.inl h5,offset_case_5 n hn h5⟩)
  · exact Or.inr (Or.inl ⟨Or.inr h10,offset_case_10 n hn h10⟩)
  · exact Or.inr (Or.inr ⟨Or.inl h11,offset_case_11 n hn h11⟩)
  · exact Or.inr (Or.inr ⟨Or.inr h16,offset_case_16 n hn h16⟩)
  · exact Or.inl ⟨Or.inr h17,offset_case_17 n hn h17⟩

private theorem d_from_K_1 (d K:Nat) (hd:d%3=0)
 (hcong:(128*d)%27=(30*K+75)%27) (hK:K%9=1):d%27=12 := by omega
private theorem d_from_K_7 (d K:Nat) (hd:d%3=0)
 (hcong:(128*d)%27=(30*K+75)%27) (hK:K%9=7):d%27=21 := by omega
private theorem d_from_K_4 (d K:Nat) (hd:d%3=0)
 (hcong:(128*d)%27=(30*K+75)%27) (hK:K%9=4):d%27=3 := by omega

open CascadeOddRay CascadeTranslatedRayDepth CascadeSweep
/-- For every high-q source t=2 parent rooted at C(2,0), the quotient-zero class is one of four residues mod 27, indexed by n mod18. -/
theorem high_ttwo_zero_period18_gate (n j d0 q e r d a:Nat)
 (hn:20≤n) (hsector:n%6=4∨n%6=5)
 (hm:2048*deficit n j+16384*n+16384≤2^n)
 (hz:2*ray n j+5=81*d0)
 (hrel:16*d0=2^n+q+(n-3)+5)
 (hgate:2*q+5=81*e)
 (hrrel:16*e=8*2^(n-6)+r+(n-6)+5)
 (htwo:2*r+5=27*d)
 (he0:8*d=8*2^(n-8)+a+(n-8)+5)
 (hdmod:d%3=0)
 (hroot:ReachC (2,0) (a,0)):
 d%9=6 ∨
 (((n%18=4∨n%18=17)∧d%27=12) ∨
  ((n%18=5∨n%18=10)∧d%27=21) ∨
  ((n%18=11∨n%18=16)∧d%27=3)) := by
  have hg:=high_ttwo_zero_quotient_residue n j d0 q e r d a hn hsector hm hz hrel hgate hrrel htwo he0 hdmod hroot
  rcases hg with h6|h27
  · exact Or.inl h6
  · right
    have hK:=source_offset_mod9 n hn hsector
    rcases hK with ⟨hn4,hK1⟩|⟨hn7,hK7⟩|⟨hn11,hK4⟩
    · exact Or.inl ⟨hn4, d_from_K_1 d (8*2^(n-8)+(n-8)) hdmod h27 hK1⟩
    · exact Or.inr (Or.inl ⟨hn7, d_from_K_7 d (8*2^(n-8)+(n-8)) hdmod h27 hK7⟩)
    · exact Or.inr (Or.inr ⟨hn11, d_from_K_4 d (8*2^(n-8)+(n-8)) hdmod h27 hK4⟩)

#print axioms source_offset_mod9
#print axioms high_ttwo_zero_period18_gate
end CascadeHighTTwo
