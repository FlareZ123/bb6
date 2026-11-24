import BB429PeriodicClassification

namespace BB429.PeriodicHigh

/-- Source trace with branch tags. none denotes any of the nonordinary
    branches (resets); it cannot stand for a successful F,S,E step. -/
def Tagged (k : Option Kind) (u w v z : Nat) : Prop :=
  BB429.next (u,w)=some (v,z) ∧
  match k with
  | none => ¬ ∃ j,High j u w v z
  | some j => High j u w v z

theorem reset_small {u w v z : Nat} (h : Tagged none u w v z) : v≤11 := by
  rcases high_or_reset h.1 with hh|hh
  · exact False.elim (h.2 hh)
  · omega

theorem rank_index_bound (u w : Nat → Nat)
    (hs : ∀ n,BB429.next (u n,w n)=some (u (n+1),w (n+1))) :
    ∀ n,n≤R (u n) (w n) := by
  intro n
  induction n with
  | zero => omega
  | succ n ih => have hh:=next_rank_growth (hs n); omega

theorem first_bound_after (u w : Nat → Nat)
    (hs : ∀ n,BB429.next (u n,w n)=some (u (n+1),w (n+1)))
    (s : Nat) (hsmall : u s≤11) : ∀ k,u (s+k)+11≤22*2^k := by
  intro k
  induction k with
  | zero => simp; omega
  | succ k ih =>
    have hh := next_first_bound (hs (s+k))
    rw [show s+(k+1)=s+k+1 by omega,Nat.pow_succ]
    omega

/-- No periodic successful branch word contains a reset. This handles all
    reset types simultaneously, even if they are not distinguished by tag. -/
theorem periodic_no_reset (u w : Nat → Nat) (tag : Nat → Option Kind)
    (hs : ∀ n,Tagged (tag n) (u n) (w n) (u (n+1)) (w (n+1)))
    (P : Nat) (hP : 0<P) (hper : ∀ n,tag (n+P)=tag n) : ∀ n,tag n≠none := by
  intro s hreset
  have hrep : ∀ j,tag (s+P*j)=none := by
    intro j
    induction j with
    | zero => simpa using hreset
    | succ j ih => rw [Nat.mul_succ,← Nat.add_assoc,hper,ih]
  let B := 22*2^P
  let j := 4*B+3
  let a := s+P*j
  let b := a+P
  have ha : tag a=none := hrep j
  have hb : tag b=none := by dsimp [b]; rw [hper,ha]
  have htagA := hs a
  rw [ha] at htagA
  have hsmall := reset_small htagA
  have hbound := first_bound_after u w (fun n => (hs n).1) (a+1) hsmall (P-1)
  have hpow : (2:Nat)^(P-1)≤2^P := Nat.pow_le_pow_right (by decide) (by omega)
  have hB : u b ≤ B := by
    have hh : a+1+(P-1)=b := by dsimp [b]; omega
    rw [hh] at hbound
    dsimp [B]
    omega
  have hR := rank_index_bound u w (fun n => (hs n).1) b
  have hbig : 4*B+3≤b := by
    have hh := Nat.mul_le_mul_right j (show 1≤P by omega)
    simp at hh
    dsimp [b,a]
    have hj : j=4*B+3 := rfl
    omega
  have hf := force_first (u:=u b) (w:=w b) (by omega)
  have hsource := high_is_next hf
  have htag := hs b
  rw [hb] at htag
  have heq := htag.1.symm.trans hsource
  have hpair := Option.some.inj heq
  have hu := congrArg Prod.fst hpair
  have hw := congrArg Prod.snd hpair
  simp at hu hw
  exact htag.2 ⟨.first,by simpa only [hu,hw] using hf⟩

theorem rank_flip {k u w v z} (h : High k u w v z) :
    R v z%2=(R u w+1)%2 := by
  cases k <;> have hh:=high_coordinates h <;> dsimp at hh <;> omega

theorem high_block_affine {k j u w v z x y} (h : High k u w v z)
    (g : High j v z x y) (hr : R u w%2=1) :
    let e := decide (k≠Kind.first)
    (A x:Int)=4*(A u:Int)-(if e then 2*(R u w:Int) else 0)+blockConstant e (R u w:Int) ∧
    (R x y:Int)=(R u w:Int)+delta e (R u w:Int) := by
  cases k
  · have hh := (block_coordinates h g hr).2
    simp [blockConstant,delta] at *
    omega
  · have hh := (block_coordinates h g hr).2
    have hm : (R u w:Int)%4=1 := by dsimp at hh; omega
    simp [blockConstant,delta,hm] at *
    omega
  · have hh := (block_coordinates h g hr).2
    have hm : (R u w:Int)%4=3 := by dsimp at hh; omega
    simp [blockConstant,delta,hm] at *
    omega

/-- A source trajectory consisting of F,S,E steps with a periodic binary
    block word must eventually visit the already-known escape ray. -/
theorem high_periodic_enters_ray (u w : Nat → Nat) (k : Nat → Kind)
    (hs : ∀ n,High (k n) (u n) (w n) (u (n+1)) (w (n+1)))
    (hodd : R (u 0) (w 0)%2=1)
    (hper : ∃ P,IsPeriod (fun n => decide (k (2*n) ≠ .first)) P) :
    ∃ n,17≤u n ∧ u n%4=1 ∧ w n=u n+8 := by
  let aa := fun n => (A (u (2*n)):Int)
  let rr := fun n => (R (u (2*n)) (w (2*n)):Int)
  let e := fun n => decide (k (2*n) ≠ .first)
  have hoddNat : ∀ n,R (u (2*n)) (w (2*n))%2=1 := by
    intro n
    induction n with
    | zero => simpa using hodd
    | succ n ih =>
      have h1 := rank_flip (hs (2*n))
      have h2 := rank_flip (hs (2*n+1))
      rw [show 2*(n+1)=2*n+1+1 by omega]
      omega
  have hord : ∀ n,rr n%2=1 := by
    intro n
    have hh := hoddNat n
    dsimp [rr]
    omega
  have hcoords : ∀ n,
      aa (n+1)=4*aa n-(if e n then 2*rr n else 0)+blockConstant (e n) (rr n) ∧
      rr (n+1)=rr n+delta (e n) (rr n) := by
    intro n
    have hh := high_block_affine (hs (2*n)) (hs (2*n+1)) (hoddNat n)
    dsimp [aa,rr,e]
    simp only [show 2*(n+1)=2*n+1+1 by omega]
    exact hh
  have hR : ∀ n,rr (n+1)=rr n+delta (e n) (rr n) := fun n => (hcoords n).2
  have hA : LinearBound aa := by
    obtain ⟨B,G,hb⟩ := rank_linear rr e hR
    refine ⟨B+6,G,?_⟩
    intro n
    have hh := hb n
    have habs := Int.natAbs_of_nonneg (show 0≤aa n by simp [aa])
    have hrabs := Int.natAbs_of_nonneg (show 0≤rr n by simp [rr])
    dsimp [aa,rr,A,R] at *
    omega
  have hpos : 0<aa 0 := by simp [aa,A]; omega
  have hc := periodic_block_corridor aa rr e hper hord hA hpos (fun n=>(hcoords n).1) hR
  have hlow : ∀ n : Nat,6*(n:Int)≤rr n := by
    intro n
    induction n with
    | zero => simp [rr,R]; omega
    | succ n ih =>
      have hh := hR n
      have hd := delta_bounds (e n) (rr n)
      omega
  have hphase : ∃ n,20≤n ∧ rr n%4=3 := by
    by_cases hh : rr 20%4=3
    · exact ⟨20,by decide,hh⟩
    · have hm := rank_mod4 rr e hR 20 1
      change rr 21%4=(rr 20+2)%4 at hm
      have ho := hord 20
      exact ⟨21,by decide,by omega⟩
  obtain ⟨n,hn,hphase⟩ := hphase
  have hline := hc.2 n
  have hlarge := hlow n
  dsimp [aa,rr,A,R] at hline hphase hlarge
  refine ⟨2*n,?_⟩
  omega

/-- Every infinite source trajectory with an ultimately periodic branch
    itinerary must enter the four-step escape ray. This is the actual
    accelerator-level classification, with no assumption of blank entry. -/
theorem ultimately_periodic_enters_ray (u w : Nat → Nat) (tag : Nat → Option Kind)
    (hs : ∀ n,Tagged (tag n) (u n) (w n) (u (n+1)) (w (n+1)))
    (s P : Nat) (hP : 0<P) (hper : ∀ n,tag (s+n+P)=tag (s+n)) :
    ∃ n,17≤u n ∧ u n%4=1 ∧ w n=u n+8 := by
  let us := fun n => u (s+n)
  let ws := fun n => w (s+n)
  let ts := fun n => tag (s+n)
  have hss : ∀ n,Tagged (ts n) (us n) (ws n) (us (n+1)) (ws (n+1)) := by
    intro n; dsimp [ts,us,ws]; rw [show s+(n+1)=s+n+1 by omega]; exact hs _
  have htper : ∀ n,ts (n+P)=ts n := by intro n; dsimp [ts]; rw [show s+(n+P)=s+n+P by omega]; exact hper n
  have hnr := periodic_no_reset us ws ts hss P hP htper
  let ks := fun n => (ts n).getD Kind.first
  have hhigh : ∀ n,High (ks n) (us n) (ws n) (us (n+1)) (ws (n+1)) := by
    intro n
    have hh := hss n
    have hn := hnr n
    cases hk : ts n with
    | none => exact False.elim (hn hk)
    | some j => simpa [ks,hk,Tagged] using hh.2
  have hkper : ∀ n,ks (n+P)=ks n := by intro n; dsimp [ks]; rw [htper]
  let shift := if R (us 0) (ws 0)%2=1 then 0 else 1
  have hodd : R (us shift) (ws shift)%2=1 := by
    dsimp [shift]
    split
    · assumption
    · have hh := rank_flip (hhigh 0)
      change R (us 1) (ws 1)%2=(R (us 0) (ws 0)+1)%2 at hh
      omega
  let uf := fun n => us (shift+n)
  let wf := fun n => ws (shift+n)
  let kf := fun n => ks (shift+n)
  have hhf : ∀ n,High (kf n) (uf n) (wf n) (uf (n+1)) (wf (n+1)) := by
    intro n; dsimp [kf,uf,wf]; rw [show shift+(n+1)=shift+n+1 by omega]; exact hhigh _
  have hpf : ∃ Q,IsPeriod (fun n => decide (kf (2*n) ≠ .first)) Q := by
    refine ⟨P,hP,?_⟩
    intro n
    apply congrArg (fun z : Kind => decide (z≠Kind.first))
    dsimp [kf]
    rw [show shift+2*(n+P)=shift+2*n+P+P by omega,hkper,hkper]
  have hodd' : R (uf 0) (wf 0)%2=1 := by simpa [uf,wf] using hodd
  obtain ⟨n,h1,h2,h3⟩ := high_periodic_enters_ray uf wf kf hhf hodd' hpf
  exact ⟨s+(shift+n),h1,h2,h3⟩

#print axioms periodic_no_reset
#print axioms high_periodic_enters_ray
#print axioms ultimately_periodic_enters_ray

end BB429.PeriodicHigh
