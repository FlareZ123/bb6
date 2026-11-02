import GParity
namespace BB6.P1Reduction

/-- All positive-left-output preimages of the recursive drain G are generated
    by one terminal high branch followed by finitely many inverse recursions. -/
inductive GAncestor : Nat → Nat → Nat → Nat → Prop where
  | upper (k d : Nat) :
      GAncestor (4*k+4) d k (d+2*k+2)
  | nest (b d k c : Nat) :
      GAncestor b d k (2*c+3) →
      GAncestor b d (k+c/2+1) c

theorem GAncestor_sound (b d k c : Nat) (h:GAncestor b d k c) :
    G k c = (b,d) := by
  induction h with
  | upper k d =>
      rw [G]
      have hlow : ¬ d+2*k+2 < 2*k := by omega
      have hmid : ¬ d+2*k+2 ≤ 2*k+1 := by omega
      simp [hlow,hmid]
  | nest b d k c h ih =>
      have hlow : c < 2*(k+c/2+1) := by omega
      rw [G]
      simp only [hlow,dite_true]
      have hsub : k+c/2+1-(c/2+1)=k := by omega
      rw [hsub]
      exact ih

theorem GAncestor_complete (k c b d : Nat) (h:G k c=(b,d))
    (hb:0<b) : GAncestor b d k c := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
      by_cases hlow:c<2*k
      · rw [G] at h
        simp only [hlow,dite_true] at h
        have hchild : GAncestor b d (k-(c/2+1)) (2*c+3) :=
          ih _ (by omega) _ h
        have hk : k-(c/2+1)+c/2+1=k := by omega
        simpa only [hk] using GAncestor.nest b d (k-(c/2+1)) c hchild
      · by_cases hmid:c≤2*k+1
        · rw [G] at h
          simp only [hlow,dite_false,hmid,ite_true] at h
          have he : b=0 := (Prod.mk.inj h).1.symm
          omega
        · have hc : 2*k+2≤c := by omega
          rw [G] at h
          simp only [hlow,dite_false,hmid,ite_false] at h
          obtain ⟨hb',hd'⟩:=Prod.mk.inj h
          have hbval : b=4*k+4 := hb'.symm
          have hcval : c=d+2*k+2 := by omega
          subst b
          subst c
          exact GAncestor.upper k d

/-- Each inverse recursion exactly halves the shifted right counter.
    In particular its depth is constrained by the powers of two in the output. -/
theorem GAncestor_power (b d k c:Nat) (h:GAncestor b d k c) :
    ∃ t:Nat, d + b/2 + 3 = 2^t*(c+3) := by
  induction h with
  | upper k d =>
      refine ⟨0,?_⟩
      simp
      omega
  | nest b d k c h ih =>
      obtain ⟨t,ht⟩ := ih
      refine ⟨t+1,?_⟩
      rw [Nat.pow_succ]
      calc
        d+b/2+3 = 2^t*((2*c+3)+3) := ht
        _ = (2^t*2)*(c+3) := by
          have heq : (2*c+3)+3=2*(c+3) := by omega
          rw [heq,Nat.mul_assoc]

theorem G_input_power (k c b d:Nat) (h:G k c=(b,d)) (hb:0<b) :
    ∃ t:Nat, d + b/2+3 = 2^t*(c+3) :=
  GAncestor_power b d k c (GAncestor_complete k c b d h hb)

#print axioms BB6.P1Reduction.GAncestor_power
#print axioms BB6.P1Reduction.G_input_power
#print axioms BB6.P1Reduction.GAncestor_sound
#print axioms BB6.P1Reduction.GAncestor_complete
end BB6.P1Reduction
