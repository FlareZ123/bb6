import OddGroup
set_option maxHeartbeats 0
namespace CascadeAgent44
open CascadeResetInverse

/-- Witness of a real odd inverse parent, retaining the valuation exponent. -/
def OddParentAt (u h t : Nat) : Prop :=
  ∃ k d, d%2=1 ∧
    (6*2^k+1 ≤ 2^t*d ∧ 2^t*d ≤ 8*2^k-1) ∧
    2*u+5=3^(t+1)*d ∧
    2*(2^t*d)=8*2^k+h+k+5

private theorem k_four_bound (k : Nat) : k+4 ≤4*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
    omega

/-- Construct an actual first-return predecessor from an admissible
    high-valuation odd-band parameter. -/
theorem odd_param_exact_parent (u t : Nat) (hp:OddParam u t) :
    ∃h, OddParentAt u h t := by
  obtain ⟨k,d,hd,hband,hout⟩ := hp
  let q := 2^t*d
  let h := 2*q-8*2^k-k-5
  have hlarge : 8*2^k+k+5 ≤ 2*q := by
    have hk:=k_four_bound k
    dsimp [q]
    omega
  have heq : 2*q = 8*2^k+h+k+5 := by
    dsimp [h]
    omega
  exact ⟨h,k,d,hd,hband,hout,(by simpa [q] using heq)⟩

theorem odd_parent_at_reset (u h t : Nat) (hp : OddParentAt u h t) :
    ResetParent h u := by
  obtain ⟨k,d,hd,hband,hz,heq⟩ := hp
  exact Or.inr ⟨k,t,d,hd,hband,hz,heq⟩

/-- A positive odd factor has a unique 2-adic exponent. -/
private theorem two_adic_exponent_unique (t s a b : Nat)
    (ha : a%2=1) (hb : b%2=1)
    (h : 2^t*a=2^s*b) : t=s := by
  rcases Nat.lt_trichotomy t s with hlt | heq | hgt
  · have hs : s=t+(s-t) := by omega
    have hpos : 1≤s-t := by omega
    have hfactor : 2^(s-t)%2=0 := by
      obtain ⟨c,hc⟩ : ∃c, s-t=c+1 := ⟨s-t-1,by omega⟩
      rw [hc,Nat.pow_succ,Nat.mul_mod]
      simp
    have hrew : 2^t*a=2^t*(2^(s-t)*b) := by
      rw [←Nat.mul_assoc,←Nat.pow_add,←hs]
      exact h
    have heq2 : a=2^(s-t)*b :=
      Nat.mul_left_cancel (Nat.two_pow_pos t) hrew
    have heven : a%2=0 := by
      rw [heq2,Nat.mul_mod,hfactor]
      simp
    omega
  · exact heq
  · have hs : t=s+(t-s) := by omega
    have hpos : 1≤t-s := by omega
    have hfactor : 2^(t-s)%2=0 := by
      obtain ⟨c,hc⟩ : ∃c, t-s=c+1 := ⟨t-s-1,by omega⟩
      rw [hc,Nat.pow_succ,Nat.mul_mod]
      simp
    have hrew : 2^s*b=2^s*(2^(t-s)*a) := by
      rw [←Nat.mul_assoc,←Nat.pow_add,←hs]
      exact h.symm
    have heq2 : b=2^(t-s)*a :=
      Nat.mul_left_cancel (Nat.two_pow_pos s) hrew
    have heven : b%2=0 := by
      rw [heq2,Nat.mul_mod,hfactor]
      simp
    omega

/-- Distinct admissible odd valuation exponents cannot describe the same
    first-reset source height: the first failed sweep index and the exact
    2-adic drain valuation are both unique. -/
theorem odd_parent_valuation_unique (u h t s : Nat)
    (ha : OddParentAt u h t) (hb : OddParentAt u h s) : t=s := by
  obtain ⟨k,d,hd,hband,hz,heq⟩ := ha
  obtain ⟨k',d',hd',hband',hz',heq'⟩ := hb
  have hlow : 4*2^k ≤ h+k+4 := by omega
  have hhigh : h+k+5 < 8*2^k := by omega
  have hlow' : 4*2^k' ≤ h+k'+4 := by omega
  have hhigh' : h+k'+5 < 8*2^k' := by omega
  have hk : k=k' := by
    rcases Nat.lt_trichotomy k k' with hlt | heqk | hgt
    · have hg:=guards_from_low h k' hlow' k hlt
      omega
    · exact heqk
    · have hg:=guards_from_low h k hlow k' hgt
      omega
  have hq : 2^t*d=2^s*d' := by
    rw [←hk] at heq'
    omega
  exact two_adic_exponent_unique t s d d' hd hd' hq

#print axioms odd_param_exact_parent
#print axioms odd_parent_valuation_unique
end CascadeAgent44
