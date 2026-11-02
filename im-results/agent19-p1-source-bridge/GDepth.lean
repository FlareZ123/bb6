import GInverse
import HaltingFunnel

namespace BB6.Agent19.Depth

open BB6.P1Reduction (GAncestor)

/-- Exact identity of Agent 1's generic inverse model and Agent 4's
    machine-certified P1 drain, on every pair of natural counters. -/
theorem G_agree (k c : Nat) :
    BB6.P1Reduction.G k c = BB6.HaltingFunnel.G k c := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases hlow : c < 2*k
    · rw [BB6.P1Reduction.G, BB6.HaltingFunnel.G]
      simp only [hlow,dite_true]
      exact ih _ (by omega) _
    · by_cases hmid:c ≤ 2*k+1
      · rw [BB6.P1Reduction.G, BB6.HaltingFunnel.G]
        simp [hlow,hmid]
      · rw [BB6.P1Reduction.G, BB6.HaltingFunnel.G]
        simp [hlow,hmid]

theorem pow_bound : ∀ n:Nat, n+1≤2^n := by
  intro n
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem high_power_mod8 (n:Nat) (hn:3≤n) : (2^n)%8=0 := by
  have he : n=n-3+3 := by omega
  rw [he,Nat.pow_add]
  simp

/-- For n >= 10 congruent 2 mod 8, an inverse G path into the exact
    critical odd-sector (H(n)-6,3) can recurse at most twice.
    Quantifies over every possible input pair, without finite search. -/
theorem G_critical_inverse_depth_two
    (n k c : Nat) (hn:10≤n) (hmod:n%8=2)
    (h:BB6.HaltingFunnel.G k c = (14*2^n-2*n-16,3)) :
    ∃ t:Nat, t≤2 ∧
      7*2^n-n-2 = 2^t*(c+3) := by
  let b:=14*2^n-2*n-16
  have hb0 := pow_bound n
  have hbn : 0<b := by dsimp [b]; omega
  have hred : BB6.P1Reduction.G k c = (b,3) := by
    rw [G_agree k c]
    exact h
  obtain ⟨t,ht⟩ := BB6.P1Reduction.G_input_power k c b 3 hred hbn
  have hformula : 3+b/2+3=7*2^n-n-2 := by dsimp [b]; omega
  rw [hformula] at ht
  refine ⟨t,?_,ht⟩
  by_cases ht2 : t≤2
  · exact ht2
  · exfalso
    have hlarge:3≤t := by omega
    have hp : (2^t)%8=0 := by
      have he : t=t-3+3 := by omega
      rw [he,Nat.pow_add]
      simp
    have hzero : (2^t*(c+3))%8=0 := by
      rw [Nat.mul_mod,hp]
      simp
    have hh : (7*2^n-n-2)%8=4 := by
      have he := high_power_mod8 n (by omega)
      omega
    omega

/-- Exhaustive classification of all possible right input counters in
    the recursive inverse of the residual critical odd-sector for
    n congruent 2 mod 8: exactly three arithmetic candidates. -/
theorem G_critical_inverse_c_three
    (n k c : Nat) (hn:10≤n) (hmod:n%8=2)
    (h:BB6.HaltingFunnel.G k c = (14*2^n-2*n-16,3)) :
    c = (7*2^n-n-2)-3 ∨
    c = (7*2^n-n-2)/2-3 ∨
    c = (7*2^n-n-2)/4-3 := by
  obtain ⟨t,htbound,ht⟩ := G_critical_inverse_depth_two n k c hn hmod h
  have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
  rcases hcases with heq | heq | heq
  · subst t
    simp at ht
    left
    omega
  · subst t
    simp at ht
    right; left
    omega
  · subst t
    simp at ht
    right; right
    omega


/-- A complete, fixed-depth inverse normal form for any G output whose
    shifted weight is 4 modulo 8. The three disjuncts correspond to zero,
    one, or two recursive descent steps, respectively. -/
def ThreeShape (b d k c : Nat) : Prop :=
  ∃ K, b=4*K+4 ∧
    ((k=K ∧ c=d+2*K+2) ∨
     (2*c+3=d+2*K+2 ∧ k=K+c/2+1) ∨
     (2*(2*c+3)+3=d+2*K+2 ∧
       k=K+(2*c+3)/2+1+c/2+1))

theorem ancestor_shapes (b d k c : Nat) (h:GAncestor b d k c) :
    (d+b/2+3)%8=4 → ThreeShape b d k c := by
  induction h with
  | upper k d =>
    intro hm
    refine ⟨k, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | nest b d k c hh ih =>
    intro hm
    obtain ⟨K,hb,hs⟩ := ih hm
    refine ⟨K,hb,?_⟩
    rcases hs with ⟨hk,hc⟩ | ⟨hc,hk⟩ | ⟨hc,hk⟩
    · right; left
      constructor
      · exact hc
      · omega
    · right; right
      constructor
      · exact hc
      · omega
    · exfalso
      omega

theorem shape_sound (b d k c:Nat) (hshape:ThreeShape b d k c) :
    BB6.P1Reduction.G k c=(b,d) := by
  obtain ⟨K,hb,hs⟩ := hshape
  rcases hs with ⟨hk,hc⟩ | ⟨hc,hk⟩ | ⟨hc,hk⟩
  · have hanc : GAncestor (4*K+4) d K (d+2*K+2) := GAncestor.upper K d
    have h0 := BB6.P1Reduction.GAncestor_sound _ _ _ _ hanc
    simpa [hb,hk,hc] using h0
  · have hup : GAncestor (4*K+4) d K (2*c+3) := by
      simpa [hc] using (GAncestor.upper K d)
    have hanc : GAncestor (4*K+4) d (K+c/2+1) c :=
      GAncestor.nest (4*K+4) d K c hup
    have h0 := BB6.P1Reduction.GAncestor_sound _ _ _ _ hanc
    simpa [hb,hk] using h0
  · have hup : GAncestor (4*K+4) d K (2*(2*c+3)+3) := by
      simpa [hc] using (GAncestor.upper K d)
    have hone : GAncestor (4*K+4) d (K+(2*c+3)/2+1) (2*c+3) :=
      GAncestor.nest (4*K+4) d K (2*c+3) hup
    have hanc : GAncestor (4*K+4) d (K+(2*c+3)/2+1+c/2+1) c :=
      GAncestor.nest (4*K+4) d (K+(2*c+3)/2+1) c hone
    have h0 := BB6.P1Reduction.GAncestor_sound _ _ _ _ hanc
    simpa [hb,hk] using h0

/-- Exhaustive *if and only if* algebraic inverse fiber for the exact
    P1 G drain, valid uniformly for arbitrary positive first output. -/
theorem G_preimages_mod8_four (b d k c : Nat)
    (hb:0<b) (hmod:(d+b/2+3)%8=4) :
    BB6.HaltingFunnel.G k c = (b,d) ↔ ThreeShape b d k c := by
  constructor
  · intro h
    have hred : BB6.P1Reduction.G k c = (b,d) := by
      rw [G_agree k c]
      exact h
    exact ancestor_shapes b d k c
      (BB6.P1Reduction.GAncestor_complete k c b d hred hb) hmod
  · intro hh
    have hred := shape_sound b d k c hh
    rw [G_agree k c] at hred
    exact hred

/-- Complete three-form input classification for the infinite residual
    critical halting-gate family n congruent 2 modulo 8. -/
theorem G_critical_inverse_three_iff (n k c : Nat)
    (hn:10≤n) (hmod:n%8=2) :
    BB6.HaltingFunnel.G k c = (14*2^n-2*n-16,3) ↔
      ThreeShape (14*2^n-2*n-16) 3 k c := by
  let b:=14*2^n-2*n-16
  have hb0 := pow_bound n
  have hbn : 0<b := by dsimp [b]; omega
  have hformula : 3+b/2+3=7*2^n-n-2 := by dsimp [b]; omega
  have hm : (3+b/2+3)%8=4 := by
    rw [hformula]
    have hp := high_power_mod8 n (by omega)
    omega
  exact G_preimages_mod8_four b 3 k c hbn hm

#print axioms BB6.Agent19.Depth.ancestor_shapes
#print axioms BB6.Agent19.Depth.shape_sound
#print axioms BB6.Agent19.Depth.G_preimages_mod8_four
#print axioms BB6.Agent19.Depth.G_critical_inverse_three_iff

#print axioms BB6.Agent19.Depth.G_agree
#print axioms BB6.Agent19.Depth.G_critical_inverse_depth_two
#print axioms BB6.Agent19.Depth.G_critical_inverse_c_three

end BB6.Agent19.Depth
