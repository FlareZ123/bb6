import ForwardUnit
namespace BB6.Agent28Forward
open BB6.Agent1 BB6P1Unit

def decode (q v : Nat) : Nat × Nat := (2*(q-v-4),2*v+1)
def valid (q v : Nat) : Prop := v+4≤q

theorem coord_decode (q v : Nat) (h : valid q v) : coordPair (decode q v)=(q,v) := by
  unfold valid at h
  unfold coordPair coord decode
  congr 1 <;> omega

theorem decode_coord (p : Nat × Nat) (he : p.1%2=0) (ho : p.2%2=1) :
    decode (coordPair p).1 (coordPair p).2=p := by
  unfold decode coordPair coord
  congr 1 <;> omega

theorem valid_coord (p : Nat × Nat) : valid (coordPair p).1 (coordPair p).2 := by
  unfold valid coordPair coord
  omega

def trans (p : Nat × Nat) : Option (Nat × Nat) := T p.1 p.2

inductive Walk : (Nat × Nat) → Nat → (Nat × Nat) → Prop where
  | nil (p) : Walk p 0 p
  | cons (p r s : Nat × Nat) (n : Nat) : trans p=some r → Walk r n s → Walk p (n+1) s

theorem Walk.single (p r : Nat × Nat) (h : trans p=some r) : Walk p 1 r :=
  Walk.cons p r r 0 h (Walk.nil r)

theorem Walk.append {p r s : Nat × Nat} {n m : Nat} (h : Walk p n r) (h' : Walk r m s) :
    Walk p (n+m) s := by
  induction h with
  | nil => simpa using h'
  | cons p t r n h hw ih =>
    have hh := Walk.cons p t s (n+m) h (ih h')
    simpa only [show n+1+m=n+m+1 by omega] using hh

theorem Walk.reach {p r : Nat × Nat} {n : Nat} (h : Walk p n r) (hr : Reach p.1 p.2) : Reach r.1 r.2 := by
  induction h with
  | nil => exact hr
  | cons p t r n h hw ih =>
    exact ih (Reach.next p.1 p.2 t.1 t.2 hr h)

def Wrap (q v r w : Nat) : Prop := ∃ t, firstWrap q v t ∧ r=q+t ∧ w=run q v t

theorem firstWrap_unique (q v t s : Nat) (ht : firstWrap q v t) (hs : firstWrap q v s) : t=s := by
  by_cases hlt : t<s
  · have hh := hs.2.1 (t-1) (by have := ht.1; omega)
    rw [ht.2.2] at hh
    omega
  · by_cases hgt : s<t
    · have hh := ht.2.1 (s-1) (by have := hs.1; omega)
      rw [hs.2.2] at hh
      omega
    · omega

theorem Wrap.unique {q v r w r' w' : Nat} (h : Wrap q v r w) (h' : Wrap q v r' w') :
    r=r' ∧ w=w' := by
  obtain ⟨t,ht,rfl,rfl⟩ := h
  obtain ⟨s,hs,rfl,rfl⟩ := h'
  rw [firstWrap_unique q v t s ht hs]
  exact ⟨rfl,rfl⟩

theorem wrap_G (k v : Nat) (hv : 2≤v) :
    Wrap (k+v+2) v (coordPair (G k (2*v-3))).1 (coordPair (G k (2*v-3))).2 := by
  obtain ⟨t,ht,he⟩ := g_first_wrap k v hv
  exact ⟨t,ht,congrArg Prod.fst he,congrArg Prod.snd he⟩

theorem wrap_prepend_zero (q v r w : Nat) (hz : 2*v<q+1)
    (h : Wrap (q+1) (2*v) r w) : Wrap q v r w := by
  obtain ⟨t,hw,hr,hv⟩ := h
  have hu : unit q v=2*v := unit_low q v hz
  refine ⟨1+t,⟨by omega,?_,?_⟩,by omega,?_⟩
  · intro j hj
    cases j with
    | zero => change bit q v=0; simp [bit,show ¬q+1≤2*v by omega]
    | succ j =>
      have he : run q v (j+1)=run (q+1) (2*v) j := by rw [Nat.add_comm j 1,run_cons,hu]
      rw [he,show q+(j+1)=q+1+j by omega]
      exact hw.2.1 j (by omega)
  · have ht : 1≤t := hw.1
    have he : 1+t-1=1+(t-1) := by omega
    rw [he,run_cons,hu,show q+(1+(t-1))=q+1+(t-1) by omega]
    exact hw.2.2
  · rwa [run_cons,hu]

theorem wrap_drop_zero (q v r w : Nat) (hz : 2*v<q+1)
    (h : Wrap q v r w) : Wrap (q+1) (2*v) r w := by
  obtain ⟨t,hw,hr,hv⟩ := h
  have htwo : 2≤t := by
    by_cases h : t=1
    · subst t
      have he : bit q v=1 := by simpa [run] using hw.2.2
      simp [bit,show ¬q+1≤2*v by omega] at he
    · have := hw.1; omega
  have hu : unit q v=2*v := unit_low q v hz
  have hr' (j : Nat) : run (q+1) (2*v) j=run q v (1+j) := by rw [run_cons,hu]
  refine ⟨t-1,⟨by omega,?_,?_⟩,by omega,?_⟩
  · intro j hj
    rw [hr',show q+1+j=q+(1+j) by omega]
    exact hw.2.1 (1+j) (by omega)
  · rw [hr',show q+1+(t-1-1)=q+(t-1) by omega,show 1+(t-1-1)=t-1 by omega]
    exact hw.2.2
  · rwa [hr',show 1+(t-1)=t by omega]

theorem wrap_one (q v : Nat) (h1 : v<q) (h2 : q+1≤2*v) :
    Wrap q v (q+1) (2*v-(q+1)) := by
  refine ⟨1,⟨by decide,?_,?_⟩,rfl,?_⟩
  · intro j hj; omega
  · change bit q v=1; simp [bit,h2]
  · change 2*v-(q+1)=unit q v
    exact (unit_high q v h1 h2).symm

/-- Regular odd hubs (v≥3) take precisely two source T steps and one first-wrap block. -/
theorem regular_odd (q v : Nat) (hq : valid q v) (hv : 3≤v) :
    ∃ r w, Wrap q v r w ∧ valid r w ∧ Walk (decode q v) 2 (decode r w) := by
  unfold valid at hq
  let a:=2*(q-v-4)
  let k:=q-v-2
  let p:=G k (2*v-3)
  have hk : a/2+2=k := by dsimp [a,k]; omega
  have hq' : k+v+2=q := by dsimp [k]; omega
  have h1 : trans (a,2*v+1)=some (a+3,2*v-1) := by
    unfold trans T
    simp only [Prod.fst,Prod.snd]
    have h0 : 2*v+1≠0 := by omega
    have h1 : 2*v+1≠1 := by omega
    have ha : a%2=0 := by dsimp [a]; omega
    simp [h0,h1,ha]
    omega
  have h2 : trans (a+3,2*v-1)=some p := by
    unfold trans T
    simp only [Prod.fst,Prod.snd]
    have h0 : 2*v-1≠0 := by omega
    have h1 : 2*v-1≠1 := by omega
    have h2 : 2*v-1≠2 := by omega
    have h3 : 2*v-1≠3 := by omega
    have ha : (a+3)%2≠0 := by dsimp [a]; omega
    simp [h0,h1,h2,h3,ha,p]
    congr 1 <;> omega
  have hw := wrap_G k v (by omega)
  rw [hq'] at hw
  refine ⟨(coordPair p).1,(coordPair p).2,hw,valid_coord p,?_⟩
  rw [decode_coord p (G_first_even _ _) (G_second_odd _ _ (by omega))]
  exact Walk.cons _ _ _ 1 h1 (Walk.single _ _ h2)

/-- The exceptional right-five hub skips the clock increment on its first doubling. -/
theorem right_five (q : Nat) (hq : 6≤q) :
    ∃ r w, Wrap q 4 r w ∧ valid r w ∧ Walk (decode q 2) 2 (decode r w) := by
  let a:=2*(q-6)
  let k:=q-5
  let p:=G k 1
  have h1 : trans (a,5)=some (a+3,3) := by
    unfold trans T
    have ha : a%2=0 := by dsimp [a]; omega
    simp [ha]
  have h2 : trans (a+3,3)=some p := by
    unfold trans T
    have ha : (a+3)%2≠0 := by dsimp [a]; omega
    simp [ha,p]
    congr 1
    dsimp [a,k]
    omega
  have hw := wrap_G k 2 (by decide)
  have he : k+2+2=q-1 := by dsimp [k]; omega
  rw [he] at hw
  have hw' := wrap_drop_zero (q-1) 2 _ _ (by omega) hw
  have he' : q-1+1=q := by omega
  rw [he'] at hw'
  refine ⟨(coordPair p).1,(coordPair p).2,hw',valid_coord p,?_⟩
  rw [decode_coord p (G_first_even _ _) (G_second_odd _ _ (by decide))]
  have hd : decode q 2=(a,5) := by unfold decode; dsimp [a]; congr 1 <;> omega
  rw [hd]
  exact Walk.cons _ _ _ 1 h1 (Walk.single _ _ h2)

/-- Right-one restart: two source transitions, clock +2, new right half q-3. -/
theorem right_one (q : Nat) (hq : 4≤q) :
    Walk (decode q 0) 2 (decode (q+2) (q-3)) := by
  let a:=2*(q-4)
  have h1 : trans (a,1)=some (a+2,0) := by simp [trans,T]
  have h2 : trans (a+2,0)=some (2,a+3) := by simp [trans,T]
  have hd1 : decode q 0=(a,1) := by simp [decode,a]
  have hd2 : decode (q+2) (q-3)=(2,a+3) := by unfold decode; dsimp [a]; congr 1 <;> omega
  rw [hd1,hd2]
  exact Walk.cons _ _ _ 1 h1 (Walk.single _ _ h2)

/-- Right-three restart: three source transitions to a positive even phase. -/
theorem right_three (q : Nat) (hq : 5≤q) :
    Walk (decode q 1) 3 (2,2*(q-2)) := by
  let a:=2*(q-5)
  have ha : a%2=0 := by dsimp [a]; omega
  have h1 : trans (a,3)=some (a+3,1) := by simp [trans,T,ha]
  have h2 : trans (a+3,1)=some (a+5,0) := by simp [trans,T]
  have h3 : trans (a+5,0)=some (2,2*(q-2)) := by simp [trans,T,a]; omega
  have hd : decode q 1=(a,3) := by unfold decode; dsimp [a]; congr 1 <;> omega
  rw [hd]
  exact Walk.cons _ _ _ 2 h1 (Walk.cons _ _ _ 1 h2 (Walk.single _ _ h3))

#print axioms regular_odd
#print axioms right_five
#print axioms right_one
#print axioms right_three
end BB6.Agent28Forward
