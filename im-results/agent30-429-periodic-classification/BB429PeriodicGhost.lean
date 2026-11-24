import BB429PeriodicReverse
import BB429DyadicSource

namespace BB429.PeriodicHigh

/-- Exact affine relations, valid in the signed inverse grammar. -/
theorem signed_coordinates {k a b x y : _} (h : SignedInv k a b x y) :
    match k with
    | .first => 2*a+6=2*(2*x+6) ∧ 2*a+b=2*x+y+3
    | .evenGap => 2*a+6+2*x+y=2*(2*x+6)+9 ∧ 2*a+b=2*x+y+11 ∧ (2*x+y)%4=1
    | .oddGap => 2*a+6+2*x+y=2*(2*x+6)+1 ∧ 2*a+b=2*x+y+7 ∧ (2*x+y)%4=3 := by
  cases k <;> simp [SignedInv] at h <;> omega

theorem signed_flip {k a b x y : _} (h : SignedInv k a b x y) :
    (2*a+b)%2=(2*x+y+1)%2 := by
  cases k <;> simp [SignedInv] at h <;> omega

/-- Reversing a block from odd rank: the first inverse must be F,
    the second determines the exceptional digit. -/
theorem signed_block {k j a b x y v z : _}
    (h : SignedInv k a b x y) (g : SignedInv j x y v z)
    (hodd : (2*a+b)%2=1) :
    let e := decide (j≠Kind.first)
    k=Kind.first ∧
    (2*a+6=4*(2*v+6)-(if e then 2*(2*v+z) else 0)+blockConstant e (2*v+z)) ∧
    2*a+b=2*v+z+delta e (2*v+z) := by
  have hk : k=Kind.first := by
    cases k
    · rfl
    · simp [SignedInv] at h; omega
    · simp [SignedInv] at h; omega
  subst k
  have h1 := signed_coordinates h
  have h2 := signed_coordinates g
  cases j
  · simp [blockConstant,delta] at *; omega
  · have hm : (2*v+z)%4=1 := by dsimp at h2; omega
    simp [blockConstant,delta,hm] at *; omega
  · have hm : (2*v+z)%4=3 := by dsimp at h2; omega
    simp [blockConstant,delta,hm] at *; omega

/-- Signed negative paths with periodic inverse block labels start on the
    negative continuation of the escape corridor. -/
theorem signed_periodic_blocks (a b : Nat → Int) (k : Nat → Kind)
    (hs : ∀ n,SignedInv (k n) (a n) (b n) (a (n+1)) (b (n+1)))
    (hodd : b 0%2=1) (ha : a 0≤ -4)
    (hper : ∃ P,IsPeriod (fun n => decide (k (2*n+1)≠Kind.first)) P) :
    ∀ n,Corridor (a (2*n)) (b (2*n)) := by
  let A := fun n => 2*a (2*n)+6
  let R := fun n => 2*a (2*n)+b (2*n)
  let e := fun n => decide (k (2*n+1)≠Kind.first)
  have hodd' : ∀ n,R n%2=1 := by
    intro n
    induction n with
    | zero => simp [R]; omega
    | succ n ih =>
      have h1:=signed_flip (hs (2*n))
      have h2:=signed_flip (hs (2*n+1))
      dsimp [R] at ih ⊢
      rw [show 2*(n+1)=2*n+1+1 by omega]
      omega
  have hc : ∀ n,A n=4*A (n+1)-(if e n then 2*R (n+1) else 0)+blockConstant (e n) (R (n+1)) ∧
      R n=R (n+1)+delta (e n) (R (n+1)) := by
    intro n
    have hh := (signed_block (hs (2*n)) (hs (2*n+1)) (hodd' n)).2
    dsimp [A,R,e]
    simpa only [show 2*(n+1)=2*n+1+1 by omega] using hh
  have hne : A 0≠0 := by simp [A]; omega
  have hh := backward_periodic_corridor A R e hper hodd' hne (fun n => (hc n).1) (fun n => (hc n).2)
  intro n
  have h := hh.2 n
  dsimp [A,R] at h
  unfold Corridor
  omega

/-- If an infinite basic-filter-admissible inverse path starts on the
    negative ghost line, its labels cannot be ultimately periodic. -/
theorem ghost_inverse_aperiodic (K : Int) (hK : 1≤K)
    (a b : Nat → Int) (k : Nat → Kind)
    (ha : a 0= -8-3*K) (hb : b 0=5-6*K)
    (hs : ∀ n,SignedInv (k n) (a n) (b n) (a (n+1)) (b (n+1)))
    (hf : ∀ n,BB429DyadicSource.basicTest (a n) (b n)=true)
    (s P : Nat) (hP : 0<P) (hper : ∀ n,k (s+n+P)=k (s+n)) : False := by
  have hneg : ∀ n,a n≤ -4 ∧ b n<0 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have htest:=hf (n+1)
      have hpar : a (n+1)%2=0 → b (n+1)%2=0 := by
        unfold BB429DyadicSource.basicTest at htest
        simp only [decide_eq_true_eq] at htest
        omega
      exact signed_negative_closed (hs n) ih.1 ih.2 hpar
  have hodd : ∀ n,b (2*n)%2=1 := by
    intro n
    induction n with
    | zero => simp; omega
    | succ n ih =>
      have h1:=signed_flip (hs (2*n))
      have h2:=signed_flip (hs (2*n+1))
      rw [show 2*(n+1)=2*n+1+1 by omega]
      omega
  let aa := fun n => a (2*s+n)
  let bb := fun n => b (2*s+n)
  let kk := fun n => k (2*s+n)
  have hss : ∀ n,SignedInv (kk n) (aa n) (bb n) (aa (n+1)) (bb (n+1)) := by
    intro n; dsimp [aa,bb,kk]; rw [show 2*s+(n+1)=2*s+n+1 by omega]; exact hs _
  have hper' : ∃ Q,IsPeriod (fun n => decide (kk (2*n+1)≠Kind.first)) Q := by
    refine ⟨P,hP,?_⟩
    intro n
    apply congrArg (fun z : Kind => decide (z≠Kind.first))
    dsimp [kk]
    rw [show 2*s+(2*(n+P)+1)=s+(s+2*n+1+P)+P by omega,hper,show s+(s+2*n+1+P)=s+(s+2*n+1)+P by omega,hper]
    congr 1
    omega
  have ho : bb 0%2=1 := by simpa [bb] using hodd s
  have hsmall : aa 0≤ -4 := by simpa [aa] using (hneg (2*s)).1
  have htail := signed_periodic_blocks aa bb kk hss ho hsmall hper' 0
  simp [aa,bb] at htail
  have hprop : ∀ n,Corridor (a (2*n)) (b (2*n)) → Corridor (a 0) (b 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hc
      rw [show 2*(n+1)=2*n+1+1 by omega] at hc
      have h1:=hneg (2*n+1+1)
      have h2:=hneg (2*n+1)
      have h3:=hneg (2*n)
      exact ih (signed_corridor_forward (hs (2*n+1)) (hs (2*n)) h1.1 h1.2 h2.1 h2.2 h3.1 h3.2 hc)
  have hroot := hprop s htail
  rw [ha,hb] at hroot
  exact ghost_outside_corridor K hroot

#print axioms signed_periodic_blocks
#print axioms ghost_inverse_aperiodic

end BB429.PeriodicHigh
