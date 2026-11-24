import Q0Aperiodic

namespace BB429Q0Macro
set_option maxHeartbeats 4000000

/-- A finite strict-interior path, with all indices through N included. -/
structure FiniteInterior (p y : Nat → Nat) (d : Nat → Digit) (N : Nat) : Prop where
  pstep : ∀ i, i<N → p (i+1)=p i+cost (d i)
  ystep : ∀ i, i<N → 16*y (i+1)=y i+digit (d i)*p i+offset (d i)
  interior : ∀ i, i≤N → 0<y i ∧ 3*y i<p i

def PeriodicOn {α : Type} (d : Nat → α) (k N : Nat) : Prop :=
  ∀ i, i+k<N → d (i+k)=d i

theorem finite_rank_mono {p y d N} (h : FiniteInterior p y d N) (i j : Nat)
    (hij : i≤j) (hj : j≤N) : p i≤p j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases he : i=j
    · simp [he]
    · have hprev := ih (j-1) (by omega) (by omega) (by omega)
      have hs := h.pstep (j-1) (by omega)
      rw [show j-1+1=j by omega] at hs
      omega

theorem finite_rank_drift {p y d N k} (h : FiniteInterior p y d N)
    (hd : PeriodicOn d k N) (i : Nat) (hi : i+k≤N) :
    p (i+k)=p i+(p k-p 0) := by
  induction i with
  | zero =>
    have h0 := finite_rank_mono h 0 k (by omega) (by omega)
    simp only [Nat.zero_add]
    omega
  | succ i ih =>
    have h1 := h.pstep (i+k) (by omega)
    have h2 := h.pstep i (by omega)
    rw [hd i (by omega)] at h1
    have hp := ih (by omega)
    rw [show i+1+k=i+k+1 by omega]
    omega

def heightDiff (y : Nat → Nat) (k i : Nat) : Int := (y (i+k):Int)-(y i:Int)

theorem finite_diff_step {p y d N k} (h : FiniteInterior p y d N)
    (hd : PeriodicOn d k N) (i : Nat) (hi : i+k<N) :
    16*heightDiff y k (i+1)=heightDiff y k i+
      (digit (d i):Int)*((p k-p 0:Nat):Int) := by
  have h1 := congrArg Int.ofNat (h.ystep (i+k) hi)
  have h2 := congrArg Int.ofNat (h.ystep i (by omega))
  rw [hd i hi,finite_rank_drift h hd i (by omega)] at h1
  unfold heightDiff
  rw [show i+1+k=i+k+1 by omega]
  cases he : d i <;> simp [he,digit,offset] at h1 h2 ⊢ <;> omega

private theorem mod_div_succ (i k : Nat) (hk : 0<k) :
    ((i%k+1<k) ∧ (i+1)%k=i%k+1 ∧ (i+1)/k=i/k) ∨
    (i%k+1=k ∧ (i+1)%k=0 ∧ (i+1)/k=i/k+1) := by
  have hr := Nat.mod_lt i hk
  have h1 := Nat.mod_add_div i k
  have h2 := Nat.mod_add_div (i+1) k
  have hm := (Nat.mod_add_mod i k 1).symm
  by_cases hc : i%k+1<k
  · rw [Nat.mod_eq_of_lt hc] at hm
    refine Or.inl ⟨hc,hm,?_⟩
    rw [hm] at h2
    exact Nat.eq_of_mul_eq_mul_left hk (by omega)
  · have he : i%k+1=k := by omega
    rw [he,Nat.mod_self] at hm
    refine Or.inr ⟨he,hm,?_⟩
    rw [hm] at h2
    apply Nat.eq_of_mul_eq_mul_left hk
    rw [Nat.mul_add,Nat.mul_one]
    omega

/-- Two equal block increments in height would extend the finite path
periodically for ever, contrary to strict-interior aperiodicity. -/
theorem unequal_block_increments {p y d N k} (h : FiniteInterior p y d N)
    (hd : PeriodicOn d k N) (hk : 0<k) (hn : 2*k≤N) :
    heightDiff y k k ≠ heightDiff y k 0 := by
  intro he
  let L := p k-p 0
  let f := heightDiff y k
  let F : Nat → Int := fun i => f (i%k)
  let D : Nat → Digit := fun i => d (i%k)
  have hL : 0≤(L:Int) := Int.natCast_nonneg _
  have hfstep (i : Nat) (hi : i<k) :
      16*f (i+1)=f i+(digit (d i):Int)*(L:Int) := finite_diff_step h hd i (by omega)
  have hFstep (i : Nat) : 16*F (i+1)=F i+(digit (D i):Int)*(L:Int) := by
    have hs := hfstep (i%k) (Nat.mod_lt i hk)
    rcases mod_div_succ i k hk with ⟨_,hm,_⟩|⟨hr,hm,_⟩
    · dsimp [F,D]; rw [hm]; exact hs
    · dsimp [F,D]; rw [hm]; rw [hr] at hs
      simpa [f,he] using hs
  have hFper : Periodic F k := by intro i; simp [F,Nat.add_mod_right]
  have hFnonneg : ∀ i, 0≤F i := by
    apply periodic_nonneg F k hk hFper
    intro i
    have hm : 0≤(digit (D i):Int)*(L:Int) := Int.mul_nonneg (Int.natCast_nonneg _) hL
    have hs := hFstep i
    omega
  let G : Nat → Int := fun i => (L:Int)-3*F i
  have hGper : Periodic G k := by intro i; simp [G,hFper i]
  have hGnonneg : ∀ i, 0≤G i := by
    apply periodic_nonneg G k hk hGper
    intro i
    have hs := hFstep i
    have hb := digit_bound (D i)
    have hb' : 0≤15-3*(digit (D i):Int) := by omega
    have hm := Int.mul_nonneg hb' hL
    rw [Int.sub_mul,Int.mul_assoc] at hm
    dsimp [G]
    omega
  have hF_eq (i : Nat) (hi : i≤k) : F i=f i := by
    by_cases hlt : i<k
    · simp [F,Nat.mod_eq_of_lt hlt]
    · have hik : i=k := by omega
      subst i
      simp [F,f,he]
  have hfnonneg (i : Nat) (hi : i≤k) : 0≤f i := by
    rw [←hF_eq i hi]; exact hFnonneg i
  let t : Nat → Nat := fun i => (f i).toNat
  have ht_cast (i : Nat) (hi : i≤k) : (t i:Int)=f i := Int.toNat_of_nonneg (hfnonneg i hi)
  have ht_bound (i : Nat) (hi : i≤k) : 3*t i≤L := by
    have hg := hGnonneg i
    dsimp [G] at hg
    rw [hF_eq i hi,←ht_cast i hi] at hg
    omega
  have ht_step (i : Nat) (hi : i<k) :
      16*t (i+1)=t i+digit (d i)*L := by
    have hs := hfstep i hi
    rw [←ht_cast i (by omega),←ht_cast (i+1) (by omega)] at hs
    omega
  have ht_k : t k=t 0 := by simp [t,f,he]
  have hp_k : p k=p 0+L := by
    have hp := finite_rank_mono h 0 k (by omega) (by omega)
    dsimp [L]; omega
  have hy_k : y k=y 0+t 0 := by
    have ht := ht_cast 0 (by omega)
    dsimp [f,heightDiff] at ht
    simp only [Nat.zero_add] at ht
    omega
  let p' : Nat → Nat := fun i => p (i%k)+(i/k)*L
  let y' : Nat → Nat := fun i => y (i%k)+(i/k)*t (i%k)
  have hp'_step (i : Nat) : p' (i+1)=p (i%k+1)+(i/k)*L := by
    rcases mod_div_succ i k hk with ⟨_,hm,hq⟩|⟨hr,hm,hq⟩
    · simp [p',hm,hq]
    · simp [p',hm,hq,hr,hp_k,Nat.add_mul]; omega
  have hy'_step (i : Nat) : y' (i+1)=y (i%k+1)+(i/k)*t (i%k+1) := by
    rcases mod_div_succ i k hk with ⟨_,hm,hq⟩|⟨hr,hm,hq⟩
    · simp [y',hm,hq]
    · simp [y',hm,hq,hr,hy_k,ht_k,Nat.add_mul]; omega
  have h_orbit : InteriorOrbit p' y' D := by
    constructor
    · intro i
      rw [hp'_step,h.pstep (i%k) (by have hh := Nat.mod_lt i hk; omega)]
      dsimp [p',D]; omega
    · intro i
      rw [hy'_step]
      have hr := Nat.mod_lt i hk
      have hs := h.ystep (i%k) (by omega)
      dsimp [p',y',D]
      calc
        16*(y (i%k+1)+(i/k)*t (i%k+1)) =
            16*y (i%k+1)+(i/k)*(16*t (i%k+1)) := by
          rw [Nat.mul_add]; ac_rfl
        _ = (y (i%k)+digit (d (i%k))*p (i%k)+offset (d (i%k)))+
            (i/k)*(t (i%k)+digit (d (i%k))*L) := by rw [hs,ht_step (i%k) hr]
        _ = y (i%k)+(i/k)*t (i%k)+digit (d (i%k))*(p (i%k)+(i/k)*L)+offset (d (i%k)) := by
          simp only [Nat.mul_add]; ac_rfl
    · intro i
      have hr := Nat.mod_lt i hk
      have hi := h.interior (i%k) (by omega)
      have hb := Nat.mul_le_mul_left (i/k) (ht_bound (i%k) (by omega))
      rw [←Nat.mul_assoc,Nat.mul_comm (i/k) 3,Nat.mul_assoc] at hb
      dsimp [p',y']; omega
  exact no_periodic_interior h_orbit ⟨k,hk,by intro i; simp [D,Nat.add_mod_right]⟩

/-- The second height difference contracts by 16 at every step during
a finite periodic segment. A nonzero integer cannot contract too far. -/
theorem finite_period_bound {p y d N k} (h : FiniteInterior p y d N)
    (hd : PeriodicOn d k N) (hk : 0<k) (hn : 2*k≤N) :
    16^(N-2*k)<p N := by
  let e : Nat → Int := fun i => heightDiff y k (i+k)-heightDiff y k i
  have hstep (i : Nat) (hi : i+2*k<N) : e i=16*e (i+1) := by
    have h1 := finite_diff_step h hd i (by omega)
    have h2 := finite_diff_step h hd (i+k) (by omega)
    rw [hd i (by omega)] at h2
    dsimp [e]
    rw [show i+1+k=i+k+1 by omega]
    omega
  have hp (m : Nat) (hm : m≤N-2*k) : e 0=(16:Int)^m*e m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [ih (by omega),hstep m (by omega),Int.pow_succ,Int.mul_assoc]
  have he : e 0≠0 := by
    have hh := unequal_block_increments h hd hk hn
    dsimp [e]; simp only [Nat.zero_add]; omega
  have hpow := congrArg Int.natAbs (hp (N-2*k) (by omega))
  rw [Int.natAbs_mul,Int.natAbs_pow] at hpow
  change (e 0).natAbs=16^(N-2*k)*(e (N-2*k)).natAbs at hpow
  have hpos : 0<(e (N-2*k)).natAbs := by
    by_cases hh : (e (N-2*k)).natAbs=0
    · rw [hh,Nat.mul_zero] at hpow
      have hz : e 0=0 := by omega
      contradiction
    · omega
  have hlo := Nat.le_mul_of_pos_right (16^(N-2*k)) hpos
  have hb0 := h.interior 0 (by omega)
  have hb1 := h.interior k (by omega)
  have hb2 := h.interior (k+k) (by omega)
  have hm0 := finite_rank_mono h 0 N (by omega) (by omega)
  have hm1 := finite_rank_mono h k N (by omega) (by omega)
  have hm2 := finite_rank_mono h (k+k) N (by omega) (by omega)
  have habs : (e 0).natAbs<p N := by
    dsimp [e,heightDiff]
    simp only [Nat.zero_add]
    omega
  omega

#print axioms unequal_block_increments
#print axioms finite_period_bound
end BB429Q0Macro
