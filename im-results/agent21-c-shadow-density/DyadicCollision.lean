import DyadicAffine

namespace BB6.Agent21Dyadic

theorem P_dvd (m n : Nat) (h : m≤n) : P m∣P n := by
  refine ⟨P (n-m),?_⟩
  rw [←P_add, Nat.add_sub_of_le h]

theorem acc13 (S : Int) (he : S%2=0) : acc S [1,3]=3*(S/2+1)+4 := by
  simp [acc,offset,parity,shift,P]
  omega

theorem acc31 (S : Int) (he : S%2=0) : acc S [3,1]=9*(S/2+1)+40 := by
  simp [acc,offset,parity,shift,P]
  omega

theorem collision_mass (L : Nat) (S : Int) (h : P (L+4)∣S+14) :
    S%2=0 ∧ ∃ k : Int, S/2+7=P L*8*k := by
  obtain ⟨k,hk⟩ := h
  rw [P_add] at hk
  change S+14=P L*16*k at hk
  have he : S+14=16*(P L*k) := by rw [hk]; ac_rfl
  refine ⟨by omega,k,?_⟩
  have hhalf : S/2+7=8*(P L*k) := by omega
  rw [hhalf]; ac_rfl

theorem collision_numer (a : Affine) (L : Nat) (hs : P (L+4)∣a.s+14)
    (hσ : P (L+4)∣a.sigma) (b : Int) :
    ∃ k : Int, numer a [3,1] b-numer a [1,3] b=16*(P L*k) := by
  have hm : P (L+4)∣mass a b+14 := by
    unfold mass
    rw [show a.s+a.sigma*b+14=(a.s+14)+a.sigma*b by omega]
    exact Int.dvd_add hs (Int.dvd_trans hσ (Int.dvd_mul_right _ _))
  obtain ⟨he,k,hk⟩ := collision_mass L (mass a b) hm
  refine ⟨3*k,?_⟩
  unfold numer
  rw [acc13 _ he,acc31 _ he]
  have hdiff : 6*(mass a b/2+7)=16*(P L*(3*k)) := by
    rw [hk]; ac_rfl
  omega

theorem collision_compatible (a : Affine) (L : Nat) (hs : P (L+4)∣a.s+14)
    (hσ : P (L+4)∣a.sigma) (b : Int) (hb : Compatible a [1,3] b) :
    Compatible a [3,1] b := by
  obtain ⟨k,hk⟩ := collision_numer a L hs hσ b
  change (16:Int)∣numer a [1,3] b at hb
  change (16:Int)∣numer a [3,1] b
  have hd : (16:Int)∣16*(P L*k) := Int.dvd_mul_right _ _
  have hsum := Int.dvd_add hb hd
  rwa [show numer a [1,3] b+16*(P L*k)=numer a [3,1] b by omega] at hsum

theorem collision_sync (a : Affine) (L : Nat) (hs : P (L+4)∣a.s+14)
    (hσ : P (L+4)∣a.sigma) (b : Int) (h : Good a) (hb : Compatible a [1,3] b) :
    (∀ t, mass (follow a [1,3] b) t=mass (follow a [3,1] b) t) ∧
    (∀ t, P L∣norm (follow a [3,1] b) t-norm (follow a [1,3] b) t) := by
  have hb' := collision_compatible a L hs hσ b hb
  constructor
  · intro t
    rw [follow_mass,follow_mass]
    rfl
  · intro t
    have hA := follow_norm a [1,3] b t h hb
    have hB := follow_norm a [3,1] b t h hb'
    change 16*norm (follow a [1,3] b) t=numer a [1,3] (b+16*t) at hA
    change 16*norm (follow a [3,1] b) t=numer a [3,1] (b+16*t) at hB
    obtain ⟨k,hk⟩ := collision_numer a L hs hσ (b+16*t)
    exact ⟨k,by omega⟩

theorem sync_compatible (a b : Affine) (L : Nat)
    (hm : ∀ t, mass a t=mass b t) (hz : ∀ t, P L∣norm b t-norm a t)
    (w : List Nat) (hcost : cost w≤L) (t : Int) (ha : Compatible a w t) :
    Compatible b w t := by
  have h := Int.dvd_trans (P_dvd (cost w) L hcost) (hz t)
  unfold Compatible numer at *
  rw [hm t] at ha
  have h' := Int.dvd_add ha h
  rwa [show norm a t+acc (mass b t) w+(norm b t-norm a t)=norm b t+acc (mass b t) w by omega] at h'

def Positive (w : List Nat) : Prop := ∀ r∈w,0<r

theorem positive_append (w v : List Nat) (hw : Positive w) (hv : Positive v) : Positive (w++v) := by
  intro r hr
  rcases List.mem_append.mp hr with h|h
  · exact hw r h
  · exact hv r h

theorem positive_replicate (r n : Nat) (hr : 0<r) : Positive (List.replicate n r) := by
  intro x hx
  have he := (List.mem_replicate.mp hx).2
  rwa [he]

theorem cost_replicate (r n : Nat) : cost (List.replicate n r)=n*r := by
  induction n with
  | zero => simp [cost]
  | succ n ih => rw [List.replicate_succ,cost_cons,ih,Nat.succ_mul]; omega

theorem drift_replicate (r n : Nat) : drift (List.replicate n r)=(n:Int)*shift r := by
  induction n with
  | zero => simp [drift]
  | succ n ih => rw [List.replicate_succ,drift,ih,Int.natCast_succ,Int.add_mul,Int.one_mul]; omega

/-- A bounded two-stage steering construction. -/
theorem steer (a : Affine) (L : Nat) (h : Good a) :
    ∃ w b, Positive w ∧ 0≤b ∧ b<P (cost w) ∧ Compatible a w b ∧
      P (L+4)∣(follow a w b).s+14 ∧ P (L+4)∣(follow a w b).sigma ∧
      cost w≤L+4+2*(2^(L+4)-1) := by
  let w1 := List.replicate (L+4) 1
  have hw1 : cost w1=L+4 := by simp [w1,cost_replicate]
  obtain ⟨b1,hb10,hb11,hb1⟩ := word_exists a w1 h
  let a1 := follow a w1 b1
  have hg1 : Good a1 := follow_good _ _ _ h
  have hσ1 : P (L+4)∣a1.sigma := by
    change P (L+4)∣a.sigma*P (cost w1)
    rw [hw1]
    exact Int.dvd_mul_left _ _
  obtain ⟨q,hq0,hq1,hq⟩ := odd_affine_exists 7 (a1.s+14) (by decide) (L+4)
  let w2 := List.replicate q.toNat 2
  have hw2 : cost w2=2*q.toNat := by simp [w2,cost_replicate,Nat.mul_comm]
  have hd2 : drift w2=7*q := by
    dsimp only [w2]; rw [drift_replicate,Int.toNat_of_nonneg hq0]
    change q*7=7*q
    omega
  obtain ⟨b2,hb20,hb21,hb2⟩ := word_exists a1 w2 hg1
  let w := w1++w2
  let b := b1+P (cost w1)*b2
  refine ⟨w,b,positive_append _ _ (positive_replicate _ _ (by decide)) (positive_replicate _ _ (by decide)),?_,?_,?_,?_,?_,?_⟩
  · have := Int.mul_nonneg (Int.le_of_lt (P_pos (cost w1))) hb20
    dsimp [b]; omega
  · have hm := Int.mul_le_mul_of_nonneg_left (show b2+1≤P (cost w2) by omega) (Int.le_of_lt (P_pos (cost w1)))
    dsimp [b,w]
    rw [cost_append,P_add]
    rw [Int.mul_add,Int.mul_one] at hm
    omega
  · exact append_compatible a w1 w2 b1 b2 h hb1 hb2
  · change P (L+4)∣mass a b+drift w+14
    dsimp only [w]; rw [drift_append]
    rw [←Int.add_assoc (mass a b) (drift w1) (drift w2)]
    change P (L+4)∣mass a (b1+P (cost w1)*b2)+drift w1+drift w2+14
    rw [←follow_mass a w1 b1 b2,hd2]
    change P (L+4)∣mass a1 b2+7*q+14
    unfold mass
    rw [show a1.s+a1.sigma*b2+7*q+14=(a1.s+14+7*q)+a1.sigma*b2 by omega]
    exact Int.dvd_add hq (Int.dvd_trans hσ1 (Int.dvd_mul_right _ _))
  · change P (L+4)∣a.sigma*P (cost w)
    dsimp only [w]; rw [cost_append,hw1,P_add (L+4) (cost w2),Int.mul_left_comm a.sigma]
    exact Int.dvd_mul_right _ _
  · have hqN : q.toNat<2^(L+4) := by
      have he := Int.toNat_of_nonneg hq0
      have hp : P (L+4)=((2^(L+4):Nat):Int) := by simp [P]
      rw [hp,←he] at hq1
      exact Int.ofNat_lt.mp hq1
    dsimp only [w]; rw [cost_append,hw1,hw2]
    omega

#print axioms collision_sync
#print axioms steer
end BB6.Agent21Dyadic
