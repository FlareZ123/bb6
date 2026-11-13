import FirstInverseComplete

namespace CascadeUParentBandEnvelope

/-- The exact scale relation for the 887-lift's parallel U/Q arm. -/
theorem pow2_split (n r : Nat) (hr : r ≤ n) :
    2^n = 2^r * 2^(n-r) := by
  calc
    2^n = 2^(r+(n-r)) := by congr 1 <;> omega
    _ = 2^r * 2^(n-r) := by rw [Nat.pow_add]

/-- The U numerator is trapped in a narrow dyadic envelope whenever its
    actual first-tier predecessor is in the scale-(n-2) even band. -/
theorem u_envelope_of_source_formula
    (n j p U z : Nat)
    (hn : 8 ≤ n)
    (hp : p = 2^(n-2))
    (hform : U + 2*n + 2^(j+4)*(2*n+3) = 112*p+15)
    (hU : U = 9*(2*z+5))
    (hzband : 6*p-1 ≤ z ∧ z ≤ 8*p-3) :
    27*2^n < U ∧ U < 28*2^n := by
  have hpow : 2^n = 4*p := by
    calc
      2^n = 2^((n-2)+2) := by congr 1 <;> omega
      _ = 2^(n-2)*2^2 := by rw [Nat.pow_add]
      _ = 4*p := by simp [hp, Nat.mul_comm]
  have hlowz : 12*p+3 ≤ 2*z+5 := by omega
  have hlowU : 108*p+27 ≤ U := by rw [hU]; omega
  have hterm : 0 < 2^(j+4)*(2*n+3) :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hupperU : U < 112*p := by omega
  constructor
  · calc
      27*2^n = 108*p := by rw [hpow]; omega
      _ < U := by omega
  · calc
      U < 112*p := hupperU
      _ = 28*2^n := by rw [hpow]; omega

/-- For t'=0 the U quotient is in the universal gap between bands n-3 and n-2. -/
theorem gap_t0 (n U d : Nat) (hn : 1 ≤ n)
    (hlo : 27*2^n < U) (hhi : U < 28*2^n)
    (hfac : U = 27*d) :
    2*2^(n-1) < d ∧ d < 3*2^(n-1) := by
  have hp := pow2_split n 1 (by omega)
  have hpow : 2^n = 2*2^(n-1) := by simpa using hp
  rw [hfac, hpow] at hlo hhi
  omega

/-- For t'=1 the U quotient is in the universal gap between bands n-4 and n-3. -/
theorem gap_t1 (n U d : Nat) (hn : 2 ≤ n)
    (hlo : 27*2^n < U) (hhi : U < 28*2^n)
    (hfac : U = 81*d) :
    2*2^(n-2) < 2*d ∧ 2*d < 3*2^(n-2) := by
  have hp := pow2_split n 2 (by omega)
  have hpow : 2^n = 4*2^(n-2) := by simpa using hp
  rw [hfac, hpow] at hlo hhi
  omega

/-- For t'=2 the U quotient is strictly inside the odd band at scale n-4. -/
theorem band_t2 (n U d : Nat) (hn : 4 ≤ n)
    (hlo : 27*2^n < U) (hhi : U < 28*2^n)
    (hfac : U = 243*d) :
    6*2^(n-4) < 4*d ∧ 4*d < 8*2^(n-4) := by
  have hp := pow2_split n 4 (by omega)
  have hpow : 2^n = 16*2^(n-4) := by simpa using hp
  rw [hfac, hpow] at hlo hhi
  omega

/-- For t'=3 the U quotient is in the universal gap between bands n-5 and n-4. -/
theorem gap_t3 (n U d : Nat) (hn : 3 ≤ n)
    (hlo : 27*2^n < U) (hhi : U < 28*2^n)
    (hfac : U = 729*d) :
    2*2^(n-3) < 8*d ∧ 8*d < 3*2^(n-3) := by
  have hp := pow2_split n 3 (by omega)
  have hpow : 2^n = 8*2^(n-3) := by simpa using hp
  rw [hfac, hpow] at hlo hhi
  omega

/-- For t'=4 the U quotient is strictly inside the odd band at scale n-5. -/
theorem band_t4 (n U d : Nat) (hn : 5 ≤ n)
    (hlo : 27*2^n < U) (hhi : U < 28*2^n)
    (hfac : U = 2187*d) :
    6*2^(n-5) < 16*d ∧ 16*d < 8*2^(n-5) := by
  have hp := pow2_split n 5 (by omega)
  have hpow : 2^n = 32*2^(n-5) := by simpa using hp
  rw [hfac, hpow] at hlo hhi
  omega

/-- For t'=5 the U quotient is in the universal gap between bands n-7 and n-6. -/
theorem gap_t5 (n U d : Nat) (hn : 4 ≤ n)
    (hlo : 27*2^n < U) (hhi : U < 28*2^n)
    (hfac : U = 6561*d) :
    2*2^(n-4) < 32*d ∧ 32*d < 3*2^(n-4) := by
  have hp := pow2_split n 4 (by omega)
  have hpow : 2^n = 16*2^(n-4) := by simpa using hp
  rw [hfac, hpow] at hlo hhi
  omega

/-- For t'=6 the U quotient is in the universal gap between bands n-8 and n-7. -/
theorem gap_t6 (n U d : Nat) (hn : 5 ≤ n)
    (hlo : 27*2^n < U) (hhi : U < 28*2^n)
    (hfac : U = 19683*d) :
    2*2^(n-5) < 64*d ∧ 64*d < 3*2^(n-5) := by
  have hp := pow2_split n 5 (by omega)
  have hpow : 2^n = 32*2^(n-5) := by simpa using hp
  rw [hfac, hpow] at hlo hhi
  omega

/-- For t'=7 the U quotient is strictly inside the odd band at scale n-7. -/
theorem band_t7 (n U d : Nat) (hn : 7 ≤ n)
    (hlo : 27*2^n < U) (hhi : U < 28*2^n)
    (hfac : U = 59049*d) :
    6*2^(n-7) < 128*d ∧ 128*d < 8*2^(n-7) := by
  have hp := pow2_split n 7 (by omega)
  have hpow : 2^n = 128*2^(n-7) := by simpa using hp
  rw [hfac, hpow] at hlo hhi
  omega

/-- For t'=8 the U quotient is in the universal gap between bands n-9 and n-8. -/
theorem gap_t8 (n U d : Nat) (hn : 6 ≤ n)
    (hlo : 27*2^n < U) (hhi : U < 28*2^n)
    (hfac : U = 177147*d) :
    2*2^(n-6) < 256*d ∧ 256*d < 3*2^(n-6) := by
  have hp := pow2_split n 6 (by omega)
  have hpow : 2^n = 64*2^(n-6) := by simpa using hp
  rw [hfac, hpow] at hlo hhi
  omega

/-- For t'=9 the U quotient is strictly inside the odd band at scale n-8. -/
theorem band_t9 (n U d : Nat) (hn : 8 ≤ n)
    (hlo : 27*2^n < U) (hhi : U < 28*2^n)
    (hfac : U = 531441*d) :
    6*2^(n-8) < 512*d ∧ 512*d < 8*2^(n-8) := by
  have hp := pow2_split n 8 (by omega)
  have hpow : 2^n = 256*2^(n-8) := by simpa using hp
  rw [hfac, hpow] at hlo hhi
  omega

/-- For t'=10 the U quotient is in the universal gap between bands n-10 and n-9. -/
theorem gap_t10 (n U d : Nat) (hn : 7 ≤ n)
    (hlo : 27*2^n < U) (hhi : U < 28*2^n)
    (hfac : U = 1594323*d) :
    2*2^(n-7) < 1024*d ∧ 1024*d < 3*2^(n-7) := by
  have hp := pow2_split n 7 (by omega)
  have hpow : 2^n = 128*2^(n-7) := by simpa using hp
  rw [hfac, hpow] at hlo hhi
  omega

end CascadeUParentBandEnvelope

namespace CascadeUParentBandEnvelope
open CascadeResetInverse

/-- A dyadic gap contains no odd first-reset image band. -/
private theorem odd_gap (k v : Nat) (hlo : 2*2^k < v)
    (hhi : v < 3*2^k) :
    ∀j, ¬(6*2^j+1≤v ∧ v≤8*2^j-1) := by
  intro j hb
  by_cases hj : j+2≤k
  · have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hj
    have he : 2^(j+2)=4*2^j := by rw [Nat.pow_add]; simp [Nat.mul_comm]
    rw [he] at hp
    omega
  · have hj' : k≤j+1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hj'
    have he : 2^(j+1)=2*2^j := by rw [Nat.pow_succ]; omega
    rw [he] at hp
    omega

/-- The odd image band has a unique dyadic scale. -/
private theorem odd_band_scale_unique (v k l : Nat)
    (hk : 6*2^k+1≤v ∧ v≤8*2^k-1)
    (hl : 6*2^l+1≤v ∧ v≤8*2^l-1) : k=l := by
  by_cases heq : k=l
  · exact heq
  · by_cases hlt : k<l
    · have hp : 2^(k+1)≤2^l := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
      have hpow : 2^(k+1)=2*2^k := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
      rw [hpow] at hp
      omega
    · have hp : 2^(l+1)≤2^k := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
      have hpow : 2^(l+1)=2*2^l := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
      rw [hpow] at hp
      omega

/-- Any source-shaped odd parent of the U state must avoid the listed
    dyadic gaps. The statement is uniform in n and in the first-tier depth. -/
theorem u_odd_parent_exponent_filter
    (n j p U z k t d : Nat)
    (hn : 13 ≤ n)
    (hp : p=2^(n-2))
    (hform : U + 2*n + 2^(j+4)*(2*n+3) = 112*p+15)
    (hU : U=9*(2*z+5))
    (hzband : 6*p-1≤z ∧ z≤8*p-3)
    (hband : 6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1)
    (hout : 2*z+5=3^(t+1)*d) :
    (t≠0 ∧ t≠1 ∧ t≠3 ∧ t≠5 ∧ t≠6 ∧ t≠8 ∧ t≠10) ∧
      (t=2 → k=n-4) ∧ (t=4 → k=n-5) ∧
      (t=7 → k=n-7) ∧ (t=9 → k=n-8) := by
  have henv := u_envelope_of_source_formula n j p U z (by omega) hp hform hU hzband
  have hfac : U=3^(t+3)*d := by
    calc
      U = 9*(2*z+5) := hU
      _ = 9*(3^(t+1)*d) := by rw [hout]
      _ = 3^(t+3)*d := by
        have hpow3 : 3^(t+3)=9*3^(t+1) := by
          calc
            3^(t+3) = 3^((t+1)+2) := by congr 1 <;> omega
            _ = 3^(t+1)*3^2 := by rw [Nat.pow_add]
            _ = 9*3^(t+1) := by simp [Nat.mul_comm]
        rw [hpow3]
        ac_rfl
  have hnot0 : t≠0 := by
    intro ht
    subst t
    have hfac' : U=27*d := by simpa using hfac
    have hg := gap_t0 n U d (by omega) henv.1 henv.2 hfac'
    exact odd_gap (n-1) d hg.1 hg.2 k (by simpa using hband)
  have hnot1 : t≠1 := by
    intro ht
    subst t
    have hfac' : U=81*d := by simpa using hfac
    have hg := gap_t1 n U d (by omega) henv.1 henv.2 hfac'
    exact odd_gap (n-2) (2*d) hg.1 hg.2 k (by simpa using hband)
  have hnot3 : t≠3 := by
    intro ht
    subst t
    have hfac' : U=729*d := by simpa using hfac
    have hg := gap_t3 n U d (by omega) henv.1 henv.2 hfac'
    exact odd_gap (n-3) (8*d) hg.1 hg.2 k (by simpa using hband)
  have hnot5 : t≠5 := by
    intro ht
    subst t
    have hfac' : U=6561*d := by simpa using hfac
    have hg := gap_t5 n U d (by omega) henv.1 henv.2 hfac'
    exact odd_gap (n-4) (32*d) hg.1 hg.2 k (by simpa using hband)
  have hnot6 : t≠6 := by
    intro ht
    subst t
    have hfac' : U=19683*d := by simpa using hfac
    have hg := gap_t6 n U d (by omega) henv.1 henv.2 hfac'
    exact odd_gap (n-5) (64*d) hg.1 hg.2 k (by simpa using hband)
  have hnot8 : t≠8 := by
    intro ht
    subst t
    have hfac' : U=177147*d := by simpa using hfac
    have hg := gap_t8 n U d (by omega) henv.1 henv.2 hfac'
    exact odd_gap (n-6) (256*d) hg.1 hg.2 k (by simpa using hband)
  have hnot10 : t≠10 := by
    intro ht
    subst t
    have hfac' : U=1594323*d := by simpa using hfac
    have hg := gap_t10 n U d (by omega) henv.1 henv.2 hfac'
    exact odd_gap (n-7) (1024*d) hg.1 hg.2 k (by simpa using hband)
  have hscale2 : t=2 → k=n-4 := by
    intro ht
    subst t
    have hfac' : U=243*d := by simpa using hfac
    have hb := band_t2 n U d (by omega) henv.1 henv.2 hfac'
    have hreal : 6*2^(n-4)+1≤4*d ∧ 4*d≤8*2^(n-4)-1 := by omega
    exact odd_band_scale_unique (4*d) k (n-4) (by simpa using hband) hreal
  have hscale4 : t=4 → k=n-5 := by
    intro ht
    subst t
    have hfac' : U=2187*d := by simpa using hfac
    have hb := band_t4 n U d (by omega) henv.1 henv.2 hfac'
    have hreal : 6*2^(n-5)+1≤16*d ∧ 16*d≤8*2^(n-5)-1 := by omega
    exact odd_band_scale_unique (16*d) k (n-5) (by simpa using hband) hreal
  have hscale7 : t=7 → k=n-7 := by
    intro ht
    subst t
    have hfac' : U=59049*d := by simpa using hfac
    have hb := band_t7 n U d (by omega) henv.1 henv.2 hfac'
    have hreal : 6*2^(n-7)+1≤128*d ∧ 128*d≤8*2^(n-7)-1 := by omega
    exact odd_band_scale_unique (128*d) k (n-7) (by simpa using hband) hreal
  have hscale9 : t=9 → k=n-8 := by
    intro ht
    subst t
    have hfac' : U=531441*d := by simpa using hfac
    have hb := band_t9 n U d (by omega) henv.1 henv.2 hfac'
    have hreal : 6*2^(n-8)+1≤512*d ∧ 512*d≤8*2^(n-8)-1 := by omega
    exact odd_band_scale_unique (512*d) k (n-8) (by simpa using hband) hreal
  exact ⟨⟨hnot0,hnot1,hnot3,hnot5,hnot6,hnot8,hnot10⟩,
    hscale2,hscale4,hscale7,hscale9⟩

end CascadeUParentBandEnvelope

namespace CascadeUParentBandEnvelope
open CascadeResetInverse

/-- Source-shaped parent classification for the U/Q arm. The even arm is
    preserved verbatim; every odd arm inherits the uniform band restrictions. -/
theorem resetParent_U_odd_band_filter
    (n j p U z q : Nat)
    (hn : 13 ≤ n)
    (hp : p=2^(n-2))
    (hform : U + 2*n + 2^(j+4)*(2*n+3) = 112*p+15)
    (hU : U=9*(2*z+5))
    (hzband : 6*p-1≤z ∧ z≤8*p-3)
    (hparent : ResetParent q z) :
    (∃ k, (6*2^k-1≤z ∧ z≤8*2^k-3) ∧
      2*z=8*2^k+q+k) ∨
    (∃ k t d, d%2=1 ∧
      (6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) ∧
      2*z+5=3^(t+1)*d ∧
      2*(2^t*d)=8*2^k+q+k+5 ∧
      (t≠0 ∧ t≠1 ∧ t≠3 ∧ t≠5 ∧ t≠6 ∧ t≠8 ∧ t≠10) ∧
      (t=2 → k=n-4) ∧ (t=4 → k=n-5) ∧
      (t=7 → k=n-7) ∧ (t=9 → k=n-8)) := by
  rcases hparent with heven | hodd
  · exact Or.inl heven
  · rcases hodd with ⟨k,t,d,hdodd,hband,hout,hq⟩
    have hf := u_odd_parent_exponent_filter n j p U z k t d
      hn hp hform hU hzband hband hout
    exact Or.inr ⟨k,t,d,hdodd,hband,hout,hq,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2⟩

#print axioms u_envelope_of_source_formula
#print axioms u_odd_parent_exponent_filter
#print axioms resetParent_U_odd_band_filter
end CascadeUParentBandEnvelope
