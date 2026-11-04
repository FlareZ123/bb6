import FirstOutcome
import ReturnInverseArithmetic
import ResetInverseWitnesses

namespace CascadeResetInverse
open CascadeSource

/-- The two *untruncated* exact reset predecessor classes. This relation
    describes genuine first resets, including every valuation length. -/
def ResetParent (h u : Nat) : Prop :=
  (∃k, (6*2^k-1≤u ∧ u≤8*2^k-3) ∧ 2*u=8*2^k+h+k) ∨
  (∃k t d, d%2=1 ∧
    (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
    2*u+5=3^(t+1)*d ∧
    2*(2^t*d)=8*2^k+h+k+5)

/-- Any exact source-C first reset necessarily belongs to one of the two
    direct reset-level inverse families, with no lost high sweep or drain case. -/
theorem reset_parent_necessary (h u : Nat)
  (hr : Outcome (h,0) (some u)) : ResetParent h u := by
  obtain ⟨k,hlow,hhigh,hnot,hcases⟩ := first_reset_classification h u hr
  rcases hcases with ⟨hpar,hu⟩ | ⟨t,d,hpar,hd,hfac,hu⟩
  · have hb := even_inverse_band h k hlow hhigh hnot hpar
    dsimp at hb
    rw [←hu] at hb
    exact Or.inl ⟨k,hb.1,hb.2⟩
  · have hb := odd_inverse_band h k hlow hhigh hnot hpar
    dsimp at hb
    have hq : 7≤2^t*d := by
      have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
      rw [←hfac]
      omega
    have hout : 2*u+5=3^(t+1)*d := by
      rw [hu]
      exact odd_output_equation t d hd hq
    rw [hfac] at hb
    exact Or.inr ⟨k,t,d,hd,hb.1,hout,hb.2⟩

/-- Every algebraically valid reset parent is exactly a genuine first reset
    of the source C-episode semantics. Both converse directions are kernel
    proved, so the inverse cases lose no branches at any dyadic size. -/
theorem reset_parent_sufficient (h u : Nat)
  (hc : ResetParent h u) : Outcome (h,0) (some u) := by
  rcases hc with ⟨k,hband,heq⟩ | ⟨k,t,d,hd,hband,hout,heq⟩
  · have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
    have hlow : 4*2^k≤h+k+4 := by omega
    have hhigh : h+k+5<8*2^k := by omega
    have hnot : h+k+4≠4*2^k := by omega
    have hpar : (h+k)%2=0 := by omega
    have hu : u=4*2^k+(h+k)/2 := by omega
    rw [hu]
    exact even_outcome h k (guards_from_low h k hlow) hlow hhigh hnot hpar
  · have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
    have hlow : 4*2^k≤h+k+4 := by omega
    have hhigh : h+k+5<8*2^k := by omega
    have hnot : h+k+4≠4*2^k := by omega
    have hpar : (h+k)%2=1 := by omega
    have hfac : 4*2^k+(h+k)/2+3=2^t*d := by omega
    have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
    have hq : 7≤2^t*d := by omega
    have heqout := odd_output_equation t d hd hq
    have hu : u=(3^(t+1)*d-5)/2 := by omega
    rw [hu]
    exact odd_outcome h k t d (guards_from_low h k hlow)
      hlow hhigh hnot hpar hfac hd

/-- Complete source-C first-reset inverse equivalence, all natural heights:
    every target parent matches exactly one even or odd dyadic grammar arm.
    No global halting or blank-root reachability conclusion follows. -/
theorem reset_parent_iff (h u : Nat) :
  Outcome (h,0) (some u) ↔ ResetParent h u := by
  constructor
  · exact reset_parent_necessary h u
  · exact reset_parent_sufficient h u

#print axioms reset_parent_sufficient
#print axioms reset_parent_iff
#print axioms reset_parent_necessary
end CascadeResetInverse
