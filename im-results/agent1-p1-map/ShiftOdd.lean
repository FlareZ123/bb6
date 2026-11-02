import EightThree
namespace BB6.Agent1

private theorem pow_ge_linear (n:Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- All critical-adjacent, c=3 odd-index gateways with n=3 mod 4 are
    blank-unreachable, uniformly for every index n and all transition times.
    This is a shifted target B(n)-2 rather than the original halt gateway. -/
theorem blank_no_shifted_odd_three (n:Nat) (hn:3≤n) (hnmod:n%4=3) :
    ¬Reach (14*2^n-2*n-18) 3 := by
  intro hr
  have hpowlower:n+1≤2^n:=pow_ge_linear n
  have hpow8:(2^n)%8=0:=by
    have he:n=(n-3)+3:=by omega
    rw [he,Nat.pow_add]
    simp only [Nat.reducePow]
    omega
  let b:=14*2^n-2*n-18
  have hbsize : 24≤b := by dsimp [b]; omega
  have hbmod : b%8=0 := by dsimp [b]; omega
  let m:=b/8
  have hbval : b=8*m := by dsimp [m]; omega
  have hm:3≤m:=by omega
  have hrel : 8*m+2*n+18=14*2^n := by dsimp [b] at hbval; omega
  have hreach : Reach (8*m) 3 := by simpa only [←hbval,b] using hr
  obtain ⟨j,hpow⟩:=reachable_eight_three_requires_power m hm hreach
  have hpow2 : 2^n=2*2^(n-1) := by
    have he:n=(n-1)+1:=by omega
    calc
      2^n=2^((n-1)+1):=by congr 1
      _=2*2^(n-1):=by rw [Nat.pow_succ]; omega
  have hlinear : 3*n+11 < 7*2^n := by omega
  have hlo : 14*2^(n-1)<6*m+8 := by omega
  have hhi : 6*m+8<14*2^n := by omega
  by_cases hj:j<n
  · have hbound:j≤n-1:=by omega
    have hp:=Nat.pow_le_pow_right (show (2:Nat)>0 by decide) hbound
    omega
  · have hbound:n≤j:=by omega
    have hp:=Nat.pow_le_pow_right (show (2:Nat)>0 by decide) hbound
    omega

/-- Generic c=1 feeder constraint for every reset in class two mod four. -/
theorem reset_mod_four_two_implies_three (d:Nat) (hd:10≤d)
    (hmod:d%4=2) (hr:Reach 2 d) : Reach (d-6) 3 := by
  cases hr with
  | init => omega
  | next a c _ _ hpre ht =>
    obtain ⟨hc,ha⟩:=T_to_two_positive a c d ht (by omega)
    have haodd:a%2=1:=by omega
    subst c
    cases hpre with
    | next x y _ _ hpre2 ht2 =>
      rcases T_to_odd_zero x y a ht2 haodd with h1 | h2
      · obtain ⟨hy,hx⟩:=h1
        subst y
        have hxodd:x%2=1:=by omega
        obtain ⟨z,w,hrz,hze,hxz,hw⟩:=
          odd_parent_general x 1 hpre2 hxodd (by decide)
        have hz:z=d-6:=by omega
        have hw':w=3:=by omega
        simpa only [hz,hw'] using hrz
      · obtain ⟨hxe,hy,hx⟩:=h2
        subst y
        have hz:x=d-4:=by omega
        have hinv:=reachable_even_mod4 x 2 hpre2 (by decide) hxe
        rcases hinv with h | h <;> omega

/-- Every high enough odd-index near-critical reset at n=3(mod4) is
    blank-unreachable, two cells below the conventional critical counter. -/
theorem blank_no_shifted_odd_reset (n:Nat) (hn:3≤n) (hnmod:n%4=3) :
    ¬Reach 2 (14*2^n-2*n-12) := by
  intro hr
  let d:=14*2^n-2*n-12
  have hbound:n+1≤2^n:=pow_ge_linear n
  have hdge : 10≤d := by dsimp [d]; omega
  have hdmod : d%4=2 := by
    have hp4:(2^n)%4=0:=by
      have h3:n=(n-2)+2:=by omega
      rw [h3,Nat.pow_add]
      simp only [Nat.reducePow]
      omega
    dsimp [d]
    omega
  have hg : Reach (d-6) 3 := reset_mod_four_two_implies_three d hdge hdmod hr
  have heq : d-6=14*2^n-2*n-18 := by dsimp [d]; omega
  exact (blank_no_shifted_odd_three n hn hnmod) (heq ▸ hg)

#print axioms BB6.Agent1.blank_no_shifted_odd_three
#print axioms BB6.Agent1.blank_no_shifted_odd_reset
end BB6.Agent1
