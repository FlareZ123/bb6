import DirectQuotientSource
import MixedStripAlgebra

namespace BB6.Agent19MixedStrip
open BB6.Agent19DirectBarrier
set_option maxHeartbeats 500000

private theorem nat_int_mod (m a b : Nat) (h : a%m=b%m) : (a:Int)%m=(b:Int)%m := by exact_mod_cast h
private theorem int_nat_mod (m a b : Nat) (h : (a:Int)%m=(b:Int)%m) : a%m=b%m := by exact_mod_cast h

private theorem liftD (M L : Nat) (hM : 0<M) (hdiv : L∣M) (J : State → Prop)
    (hc : Closed J) (hcon : Congruent M (secPred J)) (a k : Nat) (ha : 8≤a) (hk : 8≤k)
    (hi : J (a,k,0)) (z h : Int) (hz : ((a:Int)+2*k)%M=z%M) (hh : ((k:Int)+2)%L=h%L) :
    ∃ b l : Nat, 8≤b ∧ 8≤l ∧ J (b,l,0) ∧ l+2=2*(k+2) ∧ ((b:Int)+2*l)%M=(z+4)%M ∧ ((l:Int)+2)%L=(2*h)%L := by
  let t := 2*k+8
  let A := a+M*t
  have hA : t≤A := by
    have h := Nat.mul_le_mul_right t (show 1≤M by omega)
    simp [A] at *; omega
  have hAm : A%M=a%M := Nat.add_mul_mod_self_left a M t
  have hI := hcon a k A k ha hk (by omega) hk hAm.symm rfl hi
  let b := A-2*k
  let l := 2*k+2
  have hb : 8≤b := by dsimp [b,t] at *; omega
  have hl : 8≤l := by dsimp [l]; omega
  have hnext := source_direct_closed J hc A k hk (by dsimp [t] at hA; omega) hI
  refine ⟨b,l,hb,hl,hnext,by dsimp [l]; omega,?_,?_⟩
  · have he : (b:Int)+2*l=(A:Int)+2*k+4 := by dsimp [b,l,t] at *; omega
    rw [he]
    have hAm' := nat_int_mod M A a hAm
    exact (mod_add_const M ((A:Int)+2*k) z 4).mpr ((mod_add_pair M A a (2*(k:Int)) (2*(k:Int)) hAm' rfl).trans hz)
  · have he : (l:Int)+2=2*((k:Int)+2) := by dsimp [l]; omega
    rw [he]
    exact mod_mul_const L _ _ 2 hh

private def P (M L p : Nat) (J : State → Prop) (z h : Int) : Prop :=
  ∃ a k : Nat, 8≤a ∧ 8≤k ∧ J (a,k,0) ∧ 2^p∣k+2 ∧ ((a:Int)+2*k)%M=z%M ∧ ((k:Int)+2)%L=h%L

private theorem Pperiod (M L p : Nat) (J : State → Prop) : Periodic M L (P M L p J) := by
  rintro z h z' h' hz hh ⟨a,k,ha,hk,hi,hd,hz',hh'⟩
  exact ⟨a,k,ha,hk,hi,hd,hz'.trans hz,hh'.trans hh⟩

private theorem Pd (M L p : Nat) (hM : 0<M) (hdiv : L∣M) (J : State → Prop)
    (hc : Closed J) (hcon : Congruent M (secPred J)) : DClosed (P M L p J) := by
  rintro z h ⟨a,k,ha,hk,hi,hd,hz,hh⟩
  obtain ⟨b,l,hb,hl,hj,he,hz',hh'⟩ := liftD M L hM hdiv J hc hcon a k ha hk hi z h hz hh
  exact ⟨b,l,hb,hl,hj,he ▸ Nat.dvd_mul_left_of_dvd hd 2,hz',hh'⟩

private theorem reset (M L p : Nat) (hM : 0<M) (hdiv : L∣M) (J : State → Prop)
    (hc : Closed J) (hcon : Congruent M (secPred J)) (hback : DBackward (P M L p J))
    (n a k : Nat) (ha : 8≤a) (hk : 8≤k) (hi : J (a,k,0)) (z h : Int)
    (hz : ((a:Int)+2*k)%M=z%M) (hh : ((k:Int)+2)%L=h%L)
    (hn : 2^p∣2^n*(k+2)) : P M L p J z h := by
  induction n generalizing a k z h with
  | zero => exact ⟨a,k,ha,hk,hi,by simpa using hn,hz,hh⟩
  | succ n ih =>
    obtain ⟨b,l,hb,hl,hj,he,hz',hh'⟩ := liftD M L hM hdiv J hc hcon a k ha hk hi z h hz hh
    apply hback z h
    apply ih b l hb hl hj (z+4) (2*h) hz' hh'
    rw [he,←Nat.mul_assoc,←Nat.pow_succ]
    exact hn

private theorem Ph (M L p : Nat) (hM : 0<M) (hdiv : L∣M) (h2 : 2∣M) (J : State → Prop)
    (hc : Closed J) (hcon : Congruent M (secPred J)) (hback : DBackward (P M L p J)) : HClosed (P M L p J) := by
  rintro z h ⟨a,k,ha,hk,hi,_,hz,hh⟩
  let t := a+2*k+16
  let A := a+M*t
  let K := k+M*t
  have hmt : t≤M*t := by simpa using Nat.mul_le_mul_right t (show 1≤M by omega)
  have hA : 8≤A := by dsimp [A]; omega
  have hK : 8≤K := by dsimp [K]; omega
  have h1 : A+8≤2*K := by dsimp [A,K,t] at *; omega
  have h3 : 2*K+8≤3*A := by dsimp [A,K,t] at *; omega
  have hAm : A%M=a%M := Nat.add_mul_mod_self_left a M t
  have hKm : K%M=k%M := Nat.add_mul_mod_self_left k M t
  have hj := hcon a k A K ha hk hA hK hAm.symm hKm.symm hi
  let b := 3*A-2*K+1+2*(A%2)
  let l := 2*K-A+3-A%2
  have hb : 8≤b := by dsimp [b]; omega
  have hl : 8≤l := by dsimp [l]; omega
  have hnext := source_high2_closed J hc A K hA hK h1 h3 hj
  have hZm : ((A:Int)+2*K)%M=z%M := (mod_add_pair M A a (2*(K:Int)) (2*(k:Int)) (nat_int_mod M A a hAm) (mod_mul_const M K k 2 (nat_int_mod M K k hKm))).trans hz
  have hHm : ((K:Int)+2)%L=h%L := ((mod_add_const L K k 2).mpr (mod_project M L K k (Int.natCast_dvd_natCast.mpr hdiv) (nat_int_mod M K k hKm))).trans hh
  have hpar : ((A%2:Nat):Int)=z%2 := by
    have he := mod_project M 2 ((A:Int)+2*K) z (Int.natCast_dvd_natCast.mpr h2) hZm
    omega
  have heZ : (b:Int)+2*l=(A:Int)+2*K+7 := by dsimp [b,l]; omega
  have heH : (l:Int)+2=4*((K:Int)+2)-((A:Int)+2*K)-3-z%2 := by dsimp [l]; omega
  apply reset M L p hM hdiv J hc hcon hback p b l hb hl hnext (z+7) (4*h-z-3-z%2)
  · rw [heZ]; exact (mod_add_const M _ _ 7).mpr hZm
  · rw [heH]
    have hZl := mod_project M L _ _ (Int.natCast_dvd_natCast.mpr hdiv) hZm
    rw [show 4*((K:Int)+2)-((A:Int)+2*K)-3-z%2=4*((K:Int)+2)-((A:Int)+2*K)+(-3-z%2) by omega,
      show 4*h-z-3-z%2=4*h-z+(-3-z%2) by omega]
    exact (mod_add_const L _ _ (-3-z%2)).mpr (mod_sub_pair L _ _ _ _ (mod_mul_const L _ _ 4 hHm) hZl)
  · exact Nat.dvd_mul_right _ _

private theorem strip_mod (p L : Nat) (ho : L%2=1) (k l : Nat)
    (hk : 2^p∣k+2) (hl : 2^p∣l+2) (h : ((k:Int)+2)%L=((l:Int)+2)%L) : k%(2^p*L)=l%(2^p*L) := by
  obtain ⟨u,hu⟩ := hk
  obtain ⟨v,hv⟩ := hl
  have he : ((2^p:Nat):Int)*(u:Int)%L=((2^p:Nat):Int)*(v:Int)%L := by
    have hu' : (k:Int)+2=((2^p:Nat):Int)*(u:Int) := by exact_mod_cast hu
    have hv' : (l:Int)+2=((2^p:Nat):Int)*(v:Int) := by exact_mod_cast hv
    rw [←hu',←hv']; exact h
  have hcancel (n : Nat) (u v : Int) (h : (((2^n:Nat):Int)*u)%L=(((2^n:Nat):Int)*v)%L) : u%L=v%L := by
    induction n with
    | zero => simpa using h
    | succ n ih =>
      simp only [Nat.pow_succ,Int.natCast_mul] at h
      change ((((2^n:Nat):Int)*2)*u)%L=((((2^n:Nat):Int)*2)*v)%L at h
      rw [Int.mul_comm ((2^n:Nat):Int) 2,Int.mul_assoc,Int.mul_assoc] at h
      exact ih (cancel_two L _ _ (by omega) h)
  have huv := hcancel p u v he
  obtain ⟨w,hw⟩ := (mod_sub L u v).mp huv
  apply int_nat_mod
  apply (mod_sub _ _ _).mpr
  refine ⟨w,?_⟩
  have hu' : (k:Int)+2=((2^p:Nat):Int)*(u:Int) := by exact_mod_cast hu
  have hv' : (l:Int)+2=((2^p:Nat):Int)*(v:Int) := by exact_mod_cast hv
  calc
    (k:Int)-(l:Int) = ((2^p:Nat):Int)*(u-v) := by rw [Int.mul_sub]; omega
    _ = ((2^p:Nat):Int)*((L:Int)*w) := by rw [hw]
    _ = ((2^p*L:Nat):Int)*w := by rw [Int.natCast_mul,Int.mul_assoc]

/-- Every finite mixed-modulus invariant closed under the genuine CLine
    source admits all large section pairs in the dyadic right=-2 strip. -/
theorem source_mixed_strip_forced (p L : Nat) (hp : 2≤p) (ho : L%2=1)
    (J : State → Prop) (hj : J (5,0,1)) (hc : Closed J)
    (hcon : Congruent (2^p*L) (secPred J)) (a k : Nat) (ha : 8≤a) (hk : 8≤k)
    (hK : 2^p∣k+2) : J (a,k,0) := by
  let M := 2^p*L
  have hL : 0<L := by omega
  have hM : 0<M := Nat.mul_pos (Nat.two_pow_pos p) hL
  have hdiv : L∣M := Nat.dvd_mul_left _ _
  have h4 : 4∣M := Nat.dvd_mul_right_of_dvd (show 4∣2^p from Nat.pow_dvd_pow 2 hp) L
  have h2 : 2∣M := Nat.dvd_trans (by decide : 2∣4) h4
  have hper := Pperiod M L p J
  have hd := Pd M L p hM hdiv J hc hcon
  have hdb := D_backward M L hM hL ho (P M L p J) hper hd
  have hh := Ph M L p hM hdiv h2 J hc hcon hdb
  have hs : J (12,10,0) := accepted_reach J hj hc _ seed12
  have hseed : P M L p J 32 12 := reset M L p hM hdiv J hc hcon hdb p 12 10 (by decide) (by decide) hs 32 12 rfl rfl (Nat.dvd_mul_right _ _)
  obtain ⟨b,l,hb,hl,hi,hld,hz,hH⟩ := mixed_transitive M L hM hL hdiv h4 ho (P M L p J) hper hd hh 32 12 hseed ((a:Int)+2*k) ((k:Int)+2)
  have hlk : l%M=k%M := strip_mod p L ho l k hld hK hH
  have hlk' := nat_int_mod M l k hlk
  have hba : b%M=a%M := int_nat_mod M b a ((mod_add_const M b a (2*(k:Int))).mp ((mod_add_pair M b b (2*(k:Int)) (2*(l:Int)) rfl (mod_mul_const M k l 2 hlk'.symm)).trans hz))
  exact hcon b l a k hb hl ha hk hba hlk hi

#print axioms source_mixed_strip_forced
end BB6.Agent19MixedStrip
