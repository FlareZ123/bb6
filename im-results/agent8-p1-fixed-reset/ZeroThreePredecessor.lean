import Std
namespace BB6.Agent8Zero

private theorem two_pow_succ_ge (t : Nat) : t+1 ≤ 2^t := by
  induction t with
  | zero => decide
  | succ t ih =>
      rw [Nat.pow_succ]
      omega

private theorem four_t_le_two_pow (t : Nat) (ht : 4 ≤ t) : 4*t ≤ 2^t := by
  have hh : ∀ v : Nat, 4*(v+4) ≤ (2:Nat)^(v+4) := by
    intro v
    induction v with
    | zero => decide
    | succ v ih =>
        have hidx : (v+1)+4=(v+4)+1 := by omega
        rw [hidx, Nat.pow_succ]
        omega
  have heq : (t-4)+4=t := by omega
  simpa only [heq] using hh (t-4)

theorem no_odd_parent_of_24_33 (b d t : Nat)
    (hb : 8 ≤ b) (hb4 : b%4=0)
    (hp : d+b/2+3=32*2^t)
    (hm : b+d=59+2*t) : False := by
  have hdiv : b/2 ≤ b := Nat.div_le_self b 2
  have hup : 32*2^t ≤ 62+2*t := by omega
  have hlower := two_pow_succ_ge t
  have ht : t ≤ 1 := by omega
  have hbeven : b=2*(b/2) := by omega
  have hcases : t=0 ∨ t=1 := by omega
  rcases hcases with h0 | h1
  · simp [h0] at hp hm
    omega
  · simp [h1] at hp hm
    omega

theorem only_odd_parent_of_44_71 (b d t : Nat)
    (hb : 8 ≤ b) (hb4 : b%4=0)
    (hp : d+b/2+3=70*2^t)
    (hm : b+d=117+2*t) :
    b=100 ∧ d=17 ∧ t=0 := by
  have hdiv : b/2 ≤ b := Nat.div_le_self b 2
  have hup : 70*2^t ≤ 120+2*t := by omega
  have hlower := two_pow_succ_ge t
  have ht : t=0 := by omega
  have hbeven : b=2*(b/2) := by omega
  subst t
  simp at hp hm
  omega

theorem no_odd_parent_of_100_17 (b d t : Nat)
    (hb : 8 ≤ b) (hb4 : b%4=0)
    (hp : d+b/2+3=16*2^t)
    (hm : b+d=119+2*t) : False := by
  have hdiv : b/2 ≤ b := Nat.div_le_self b 2
  have hup : 16*2^t ≤ 122+2*t := by omega
  have ht : t ≤ 3 := by
    by_cases ht : t ≤ 3
    · exact ht
    · have h4 : 4 ≤ t := by omega
      have hp4 := four_t_le_two_pow t h4
      omega
  have hbeven : b=2*(b/2) := by omega
  have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · simp [h0] at hp hm
    omega
  · simp [h1] at hp hm
    omega
  · simp [h2] at hp hm
    omega
  · simp [h3] at hp hm
    omega

#print axioms BB6.Agent8Zero.no_odd_parent_of_24_33
#print axioms BB6.Agent8Zero.only_odd_parent_of_44_71
#print axioms BB6.Agent8Zero.no_odd_parent_of_100_17
end BB6.Agent8Zero
