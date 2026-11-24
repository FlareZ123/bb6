import Lean

namespace BB6.Agent19DirectBarrier

set_option maxHeartbeats 300000

def Congruent (M : Nat) (I : Nat → Nat → Prop) : Prop :=
  ∀ a k b l, 8≤a → 8≤k → 8≤b → 8≤l → a%M=b%M → k%M=l%M → I a k → I b l

def DirectClosed (I : Nat → Nat → Prop) : Prop :=
  ∀ a k, 8≤k → 2*k+8≤a → I a k → I (a-2*k) (2*k+2)

def Seeds (I : Nat → Nat → Prop) : Prop := I 12 10 ∧ I 17 11 ∧ I 18 16 ∧ I 23 17

private theorem add_div_mod (M a t : Nat) (ht : M∣t) : (a+t)%M=a%M := by
  obtain ⟨q,rfl⟩ := ht
  exact Nat.add_mul_mod_self_left a M q

private theorem residue_cancel (M a b c : Nat) (h : (a+c)%M=(b+c)%M) : a%M=b%M := by
  by_cases hz : M=0
  · subst M; simp at h ⊢; omega
  have hh : c%M+(M-c%M)=M := by have := Nat.mod_lt c (by omega : 0<M); omega
  have hc (z : Nat) : ((z+c)%M+(M-c%M))%M=z%M := by
    rw [←Nat.add_mod_mod z c M,Nat.mod_add_mod,Nat.add_assoc,hh,Nat.add_mod_right]
  exact (hc a).symm.trans ((congrArg (fun z => (z+(M-c%M))%M) h).trans (hc b))

private theorem lifted_direct (M : Nat) (I : Nat → Nat → Prop) (hM : 0<M) (h4 : 4∣M)
    (hc : Congruent M I) (hd : DirectClosed I) (a k : Nat) (ha : 8≤a) (hk : 8≤k) (hi : I a k) :
    ∃ b, 8≤b ∧ I b (2*k+2) ∧ (b+2*(2*k+2))%4=(a+2*k)%4 := by
  let t := 2*k+8
  let A := a+M*t
  have hA : t≤A := by
    have h := Nat.mul_le_mul_right t (show 1≤M by omega)
    simp [A] at *
    omega
  have hAm : A%M=a%M := Nat.add_mul_mod_self_left a M t
  have hI := hc a k A k ha hk (by omega) hk hAm.symm rfl hi
  let b := A-2*k
  refine ⟨b,by dsimp [b,t] at *; omega,hd A k hk (by dsimp [t] at hA; omega) hI,?_⟩
  have hmul : 4∣M*t := Nat.dvd_trans h4 (Nat.dvd_mul_right M t)
  have h4m : (M*t)%4=0 := Nat.mod_eq_zero_of_dvd hmul
  have hAm4 : A%4=a%4 := add_div_mod 4 a (M*t) hmul
  dsimp [b]
  omega

private theorem lifted_direct_n (M : Nat) (I : Nat → Nat → Prop) (hM : 0<M) (h4 : 4∣M)
    (hc : Congruent M I) (hd : DirectClosed I) (n a k : Nat) (ha : 8≤a) (hk : 8≤k) (hi : I a k) :
    ∃ b l, 8≤b ∧ 8≤l ∧ I b l ∧ l+2=2^n*(k+2) ∧ (b+2*l)%4=(a+2*k)%4 := by
  induction n with
  | zero => exact ⟨a,k,ha,hk,hi,by simp,rfl⟩
  | succ n ih =>
    obtain ⟨b,l,hb,hl,hi',hlpow,hmod⟩ := ih
    obtain ⟨b',hb',hi'',hm⟩ := lifted_direct M I hM h4 hc hd b l hb hl hi'
    refine ⟨b',2*l+2,hb',by omega,hi'',?_,hm.trans hmod⟩
    rw [Nat.pow_succ,Nat.mul_right_comm,←hlpow]
    omega

private theorem step_four (M : Nat) (I : Nat → Nat → Prop) (hc : Congruent M I) (hd : DirectClosed I)
    (a k : Nat) (ha : 8≤a) (hk : 8≤k) (hm : M∣k+2) (hi : I a k) : I (a+4) k := by
  have hdiv : M∣2*(k+2) := Nat.dvd_mul_left_of_dvd hm 2
  have he : a+4+2*k=a+2*(k+2) := by omega
  have ham : (a+4+2*k)%M=a%M := by rw [he]; exact add_div_mod _ _ _ hdiv
  have hs : I (a+4+2*k) k := hc a k _ _ ha hk (by omega) hk ham.symm rfl hi
  have ht := hd _ k hk (by omega) hs
  have ha4 : a+4+2*k-2*k=a+4 := by omega
  rw [ha4] at ht
  have hkm : (2*k+2)%M=k%M := by rw [show 2*k+2=k+(k+2) by omega]; exact add_div_mod _ _ _ hm
  exact hc (a+4) (2*k+2) (a+4) k (by omega) (by omega) (by omega) hk rfl hkm ht

private theorem step_four_n (M : Nat) (I : Nat → Nat → Prop) (hc : Congruent M I) (hd : DirectClosed I)
    (a k n : Nat) (ha : 8≤a) (hk : 8≤k) (hm : M∣k+2) (hi : I a k) : I (a+4*n) k := by
  induction n with
  | zero => simpa using hi
  | succ n ih =>
    have h := step_four M I hc hd (a+4*n) k (by omega) hk hm ih
    simpa [Nat.mul_succ,Nat.add_assoc] using h

private theorem seed_complete (I : Nat → Nat → Prop) (hs : Seeds I) (a : Nat) :
    ∃ b l, 8≤b ∧ 8≤l ∧ I b l ∧ (b+2*l)%4=a%4 := by
  have h : a%4=0 ∨ a%4=1 ∨ a%4=2 ∨ a%4=3 := by omega
  rcases h with h|h|h|h
  · exact ⟨12,10,by decide,by decide,hs.1,by omega⟩
  · exact ⟨23,17,by decide,by decide,hs.2.2.2,by omega⟩
  · exact ⟨18,16,by decide,by decide,hs.2.2.1,by omega⟩
  · exact ⟨17,11,by decide,by decide,hs.2.1,by omega⟩

/-- Every large/large residue cell with right coordinate -2 mod 2^p is
    forced by the four seeds and ordinary direct closure. -/
theorem direct_tail_forced (p : Nat) (hp : 2≤p) (I : Nat → Nat → Prop)
    (hc : Congruent (2^p) I) (hd : DirectClosed I) (hs : Seeds I)
    (a k : Nat) (ha : 8≤a) (hk : 8≤k) (hK : 2^p∣k+2) : I a k := by
  let M := 2^p
  have hM : 0<M := Nat.two_pow_pos p
  have h4 : 4∣M := by simpa [M] using Nat.pow_dvd_pow 2 hp
  obtain ⟨b,l,hb,hl,hi,hm⟩ := seed_complete I hs a
  obtain ⟨B,L,hB,hL,hI,hLp,hmod⟩ := lifted_direct_n M I hM h4 hc hd p b l hb hl hi
  have hLM : M∣L+2 := ⟨l+2,hLp⟩
  have hmodL : L%2=0 := by
    have h2 : 2∣M := by simpa [M] using Nat.pow_dvd_pow 2 (by omega : 1≤p)
    have h := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h2 hLM)
    omega
  have hBmod : B%4=a%4 := by omega
  have hlk : L%M=k%M := residue_cancel M L k 2 ((Nat.mod_eq_zero_of_dvd hLM).trans (Nat.mod_eq_zero_of_dvd hK).symm)
  have hiBk : I B k := hc B L B k hB hL hB hk rfl hlk hI
  let A := a+M*B
  have hAB : B≤A := by
    have h := Nat.mul_le_mul_right B (show 1≤M by omega)
    dsimp [A]; omega
  have hAmod : A%4=a%4 := add_div_mod 4 a _ (Nat.dvd_trans h4 (Nat.dvd_mul_right M B))
  let n := (A-B)/4
  have he : A=B+4*n := by dsimp [n]; omega
  have hIA : I A k := by rw [he]; exact step_four_n M I hc hd B k n hB hk hK hiBk
  exact hc A k a k (by omega) hk ha hk (Nat.add_mul_mod_self_left a M B) rfl hIA

#print axioms direct_tail_forced
end BB6.Agent19DirectBarrier
