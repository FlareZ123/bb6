import EvenFull
namespace BB6.Agent1

/-- Exhaustive two G-ancestors of output (8m,3), proved directly against
    the exact original drain function without any surrogate ancestor model. -/
theorem G_to_eight_three (k c m : Nat) (h : G k c = (8*m,3))
    (hm : 3≤m) :
    (k=2*m-1 ∧ c=4*m+3) ∨ (k=3*m ∧ c=2*m) := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases hlow:c<2*k
    · rw [G] at h
      simp only [hlow,dite_true] at h
      rcases ih (k-(c/2+1)) (by omega) (2*c+3) h with h1 | h2
      · right
        omega
      · omega
    · by_cases hmid:c≤2*k+1
      · rw [G] at h
        simp only [hlow,dite_false,hmid,ite_true] at h
        have hb:(0:Nat)=8*m:=(Prod.mk.inj h).1
        omega
      · rw [G] at h
        simp only [hlow,dite_false,hmid,ite_false] at h
        left
        have hb:4*k+4=8*m:=(Prod.mk.inj h).1
        have hd:c-(2*k+2)=3:=(Prod.mk.inj h).2
        omega

/-- The entire positive-eight-multiple, right-three gateway family can be
    reached only on a sparse 14-power residue set. -/
theorem reachable_eight_three_requires_power (m:Nat) (hm:3≤m)
    (hr:Reach (8*m) 3) : ∃ j:Nat, 6*m+8=14*2^j := by
  generalize hz : 8*m = z at hr
  cases hr with
  | next a c _ _ hpre ht =>
    rw [←hz] at ht
    unfold T at ht
    by_cases h0:c=0
    · simp [h0] at ht
      omega
    · by_cases h1:c=1
      · simp [h0,h1] at ht
      · by_cases he:a%2=0
        · simp [h0,h1,he] at ht
          omega
        · by_cases h2:c=2
          · simp [h0,h1,he,h2] at ht
          · by_cases h3:c=3
            · simp [h0,h1,he,h2,h3] at ht
              have hg:G (a/2) 1=(8*m,3):=by simpa using ht
              rcases G_to_eight_three (a/2) 1 m hg hm with h | h <;> omega
            · simp [h0,h1,he,h2,h3] at ht
              have hg:G (a/2+1) (c-2)=(8*m,3):=by simpa using ht
              obtain ⟨x,y,hrx,hxe,hax,hy⟩:=
                odd_parent_general a c hpre (by omega) (by omega)
              rcases G_to_eight_three (a/2+1) (c-2) m hg hm with h | h
              · obtain ⟨hk,hv⟩:=h
                have hx:x=4*m-6:=by omega
                have hyval:y=4*m+7:=by omega
                have hrx' : Reach (4*m-6) (4*m+7) := by
                  simpa only [hx,hyval] using hrx
                have hinv:=reachable_even_mod4 (4*m-6) (4*m+7) hrx' (by omega) (by omega)
                rcases hinv with h | h <;> omega
              · obtain ⟨hk,hv⟩:=h
                have hx:x=6*m-4:=by omega
                have hyval:y=2*m+4:=by omega
                have hrx' : Reach (6*m-4) (2*m+4) := by
                  simpa only [hx,hyval] using hrx
                obtain ⟨j,hj⟩:=even_left_power_shape (6*m-4) (2*m+4) hrx' (by omega) (by omega) (by omega)
                exact ⟨j,by omega⟩

#print axioms BB6.Agent1.G_to_eight_three
#print axioms BB6.Agent1.reachable_eight_three_requires_power
end BB6.Agent1
