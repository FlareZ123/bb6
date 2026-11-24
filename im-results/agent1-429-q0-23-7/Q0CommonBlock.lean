import Q0DifferencePacking
import Q0FinitePeriod

namespace BB429Q0Macro
set_option maxHeartbeats 4000000

private theorem finite_nonneg_after (f : Nat → Int) (N P t : Nat)
    (h0 : -(P:Int)<f 0) (hs : ∀ i, i<N → f i≤16*f (i+1))
    (hpow : P<16^t) (i : Nat) (hti : t≤i) (hi : i≤N) : 0≤f i := by
  have hg (j : Nat) (hj : j≤N) : f 0≤(16:Int)^j*f j := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        f 0≤(16:Int)^j*f j := ih (by omega)
        _≤(16:Int)^j*(16*f (j+1)) :=
          Int.mul_le_mul_of_nonneg_left (hs j (by omega)) (Int.pow_nonneg (by decide))
        _=(16:Int)^(j+1)*f (j+1) := by rw [Int.pow_succ,Int.mul_assoc]
  have hp : (P:Int)<(16:Int)^i := by
    have hh := Nat.lt_of_lt_of_le hpow (Nat.pow_le_pow_right (by decide) hti)
    have hc := Int.ofNat_lt.mpr hh
    simpa [Int.natCast_pow] using hc
  apply Classical.byContradiction
  intro hn
  have hneg : f i≤ -1 := by omega
  have hh := Int.mul_le_mul_of_nonneg_left hneg (Int.pow_nonneg (n:=16) (m:=i) (by decide))
  rw [Int.mul_neg,Int.mul_one] at hh
  have hgi := hg i hi
  omega

private theorem paired_rank_drift {p y q z d N} (h : FiniteInterior p y d N)
    (h' : FiniteInterior q z d N) (hgap : p 0<q 0) (i : Nat) (hi : i≤N) :
    q i=p i+(q 0-p 0) := by
  induction i with
  | zero => omega
  | succ i ih =>
    have h1 := h.pstep i (by omega)
    have h2 := h'.pstep i (by omega)
    have hh := ih (by omega)
    omega

private theorem paired_diff_step {p y q z d N} (h : FiniteInterior p y d N)
    (h' : FiniteInterior q z d N) (hgap : p 0<q 0) (i : Nat) (hi : i<N) :
    16*((z (i+1):Int)-(y (i+1):Int))=(z i:Int)-(y i:Int)+
      (digit (d i):Int)*((q 0-p 0:Nat):Int) := by
  have h1 := congrArg Int.ofNat (h.ystep i hi)
  have h2 := congrArg Int.ofNat (h'.ystep i hi)
  rw [paired_rank_drift h h' hgap i (by omega)] at h2
  cases he : d i <;> simp [he,digit,offset] at h1 h2 ⊢ <;> omega

private theorem finite_segment_walk {L : Nat} {s : Nat → Nat} {d : Nat → Digit}
    {t N : Nat} (hs : ∀ i, t≤i → i<N → 16*s (i+1)=s i+digit (d i)*L)
    (i n : Nat) (hi : t≤i) (hn : i+n≤N) :
    SlopeWalk L (segment d i n) (segment s (i+1) n) (s i) (s (i+n)) := by
  induction n generalizing i with
  | zero => simpa [segment] using SlopeWalk.nil (L:=L) (s i)
  | succ n ih =>
    rw [show i+(n+1)=(i+1)+n by omega]
    exact SlopeWalk.cons (hs i hi (by omega)) (ih (i+1) (by omega) (by omega))

private theorem finite_repeat_period {s : Nat → Nat} {d : Nat → Digit} {L t N : Nat}
    (hL : 0<L) (hb : ∀ i, t≤i → i≤N → 3*s i≤L)
    (hs : ∀ i, t≤i → i<N → 16*s (i+1)=s i+digit (d i)*L)
    (i j : Nat) (hi : t≤i) (hij : i<j) (hj : j≤N) (he : s i=s j) :
    PeriodicOn (fun a => d (t+a)) (j-i) (j-t) := by
  let gap := j-i
  have hgap : j=i+gap := by dsimp [gap]; omega
  have back (a : Nat) (ha : t≤a) (ha' : a+gap<N)
      (h : s (a+1)=s (a+1+gap)) : s a=s (a+gap) ∧ d a=d (a+gap) := by
    have h1 := hs a ha (by omega)
    have h2 := hs (a+gap) (by omega) ha'
    rw [show a+gap+1=a+1+gap by omega,←h] at h2
    exact slope_reverse_unique L _ _ _ _ _ hL (hb a ha (by omega)) (hb (a+gap) (by omega) (by omega)) h1 h2
  have down (a n : Nat) (ha : t≤a) (hn : a+n+gap≤N)
      (h : s (a+n)=s (a+n+gap)) : s a=s (a+gap) := by
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have hh : s (a+n+1)=s (a+n+1+gap) := by simpa [Nat.add_assoc] using h
      exact ih (by omega) (back (a+n) (by omega) (by omega) hh).1
  intro a ha
  change a+gap<j-t at ha
  change d (t+(a+gap))=d (t+a)
  have hsmall : t+a+1≤i := by omega
  have h0 : s (t+a+1)=s (t+a+1+gap) := by
    apply down (t+a+1) (i-(t+a+1)) (by omega) (by omega)
    rw [show t+a+1+(i-(t+a+1))=i by omega,←hgap]
    exact he
  have hh := (back (t+a) (by omega) (by omega) h0).2.symm
  simpa [Nat.add_assoc] using hh

theorem finite_shift {p y d N} (h : FiniteInterior p y d N) (a n : Nat) (ha : a+n≤N) :
    FiniteInterior (fun i => p (a+i)) (fun i => y (a+i)) (fun i => d (a+i)) n := by
  constructor
  · intro i hi; simpa [Nat.add_assoc] using h.pstep (a+i) (by omega)
  · intro i hi; simpa [Nat.add_assoc] using h.ystep (a+i) (by omega)
  · intro i hi; exact h.interior (a+i) (by omega)

/-- Matching length N at positive rank gap L. The two paths have the same
exact digit itinerary. Once their signed height difference has entered
[0,L/3], arbitrary-depth slope packing forces a repeated slope; reverse
uniqueness converts it into a long periodic segment of the original path. -/
theorem common_block_bound {p y q z d N P t hdepth} (h : FiniteInterior p y d N)
    (h' : FiniteInterior q z d N) (hgap : p 0<q 0)
    (hP : q N≤P) (hpow : P<16^t) :
    let L := q 0-p 0
    let B := 4^hdepth*(L/(3*16^hdepth)+1)
    N<max (t+hdepth+B) (2*t+3*B) := by
  let L := q 0-p 0
  let B := 4^hdepth*(L/(3*16^hdepth)+1)
  change N<max (t+hdepth+B) (2*t+3*B)
  have hL : 0<L := by dsimp [L]; omega
  have hpP (i : Nat) (hi : i≤N) : p i≤P := by
    have hh := paired_rank_drift h h' hgap i hi
    have hm := finite_rank_mono h' i N hi (by omega)
    omega
  have hqP (i : Nat) (hi : i≤N) : q i≤P := by
    have hm := finite_rank_mono h' i N hi (by omega)
    omega
  have htpos : 0<t := by
    by_cases he : t=0
    · subst t; simp at hpow
      have hi := h'.interior N (by omega)
      omega
    · omega
  by_cases hn : N<t+hdepth+B
  · exact Nat.lt_of_lt_of_le hn (Nat.le_max_left _ _)
  let f : Nat → Int := fun i => (z i:Int)-(y i:Int)
  have hf (i : Nat) (hi : i<N) : 16*f (i+1)=f i+(digit (d i):Int)*(L:Int) :=
    paired_diff_step h h' hgap i hi
  have hf0 : -(P:Int)<f 0 := by
    have hi := h.interior 0 (by omega)
    have hi' := h'.interior 0 (by omega)
    have hp := hpP 0 (by omega)
    dsimp [f]; omega
  have hfmono (i : Nat) (hi : i<N) : f i≤16*f (i+1) := by
    have hs := hf i hi
    have hm : 0≤(digit (d i):Int)*(L:Int) := Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    omega
  let g : Nat → Int := fun i => (L:Int)-3*f i
  have hg0 : -(P:Int)<g 0 := by
    have hi := h'.interior 0 (by omega)
    have hq := hqP 0 (by omega)
    dsimp [g,f]; omega
  have hgmono (i : Nat) (hi : i<N) : g i≤16*g (i+1) := by
    have hs := hf i hi
    have hb := digit_bound (d i)
    have hb' : 0≤15-3*(digit (d i):Int) := by omega
    have hm := Int.mul_nonneg hb' (Int.natCast_nonneg L)
    rw [Int.sub_mul,Int.mul_assoc] at hm
    dsimp [g]; omega
  let s : Nat → Nat := fun i => (f i).toNat
  have hscast (i : Nat) (hi : t≤i) (hi' : i≤N) : (s i:Int)=f i :=
    Int.toNat_of_nonneg (finite_nonneg_after f N P t hf0 hfmono hpow i hi hi')
  have hb (i : Nat) (hi : t≤i) (hi' : i≤N) : 3*s i≤L := by
    have hg := finite_nonneg_after g N P t hg0 hgmono hpow i hi hi'
    dsimp [g] at hg
    rw [←hscast i hi hi'] at hg
    omega
  have hs (i : Nat) (hi : t≤i) (hi' : i<N) : 16*s (i+1)=s i+digit (d i)*L := by
    have hh := hf i hi'
    rw [←hscast i hi (by omega),←hscast (i+1) (by omega) (by omega)] at hh
    omega
  let ts := segment s (N-B) (B+1)
  have hhist (b : Nat) (hmem : b∈ts) :
      ∃ ds ss a, ds.length=hdepth ∧ 3*a≤L ∧ SlopeWalk L ds ss a b := by
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hmem
    have hi' : i<B+1 := by simpa [ts] using hi
    have he' : s (N-B+i)=b := by
      change (segment s (N-B) (B+1))[i]'(by simpa using hi')=b at he
      rwa [get_segment] at he
    let a := N-B+i-hdepth
    have ha : t≤a := by dsimp [a]; omega
    have ha' : a+hdepth=N-B+i := by dsimp [a]; omega
    have hw := finite_segment_walk hs a hdepth ha (by omega)
    rw [ha',he'] at hw
    exact ⟨segment d a hdepth,segment s (a+1) hdepth,s a,by simp,hb a ha (by omega),hw⟩
  have hrep : ∃ i j, i<j ∧ j≤B ∧ s (N-B+i)=s (N-B+j) := by
    apply Classical.byContradiction
    intro he
    have hnodup : ts.Nodup := by
      rw [List.nodup_iff_eq_of_getElem_eq]
      intro i j hi hj he'
      have hi' : i<B+1 := by simpa [ts] using hi
      have hj' : j<B+1 := by simpa [ts] using hj
      change (segment s (N-B) (B+1))[i]'(by simpa using hi')=
        (segment s (N-B) (B+1))[j]'(by simpa using hj') at he'
      rw [get_segment s (N-B) (B+1) i hi',get_segment s (N-B) (B+1) j hj'] at he'
      rcases Nat.lt_trichotomy i j with hlt|heq|hgt
      · exact False.elim (he ⟨i,j,hlt,by omega,he'⟩)
      · exact heq
      · exact False.elim (he ⟨j,i,hgt,by omega,he'.symm⟩)
    have hpack := deep_slope_packing L hdepth ts hnodup hhist
    change ts.length≤B at hpack
    simp [ts] at hpack
    omega
  obtain ⟨i,j,hij,hj,he⟩ := hrep
  let a := N-B+i
  let b := N-B+j
  let gap := b-a
  have ha : t≤a := by dsimp [a]; omega
  have hbN : b≤N := by dsimp [b]; omega
  have hagap : 0<gap := by dsimp [gap,b,a]; omega
  have hgapB : gap≤B := by dsimp [gap,b,a]; omega
  have hper := finite_repeat_period hL hb hs a b ha (by dsimp [a,b]; omega) hbN he
  have hshift := finite_shift h t (b-t) (by omega)
  have hlen : b-t<2*gap+t := by
    by_cases hc : 2*gap≤b-t
    · have hh := finite_period_bound hshift hper hagap hc
      have hP' := hpP b hbN
      change 16^(b-t-2*gap)<p (t+(b-t)) at hh
      rw [show t+(b-t)=b by omega] at hh
      apply Classical.byContradiction
      intro hn'
      have hle := Nat.pow_le_pow_right (n:=16) (by decide) (show t≤b-t-2*gap by omega)
      omega
    · omega
  have hbmin : N-B+1≤b := by dsimp [b]; omega
  have hmain : N<2*t+3*B := by omega
  exact Nat.lt_of_lt_of_le hmain (Nat.le_max_right _ _)

/-- The rank grows by at most six per macro. -/
theorem finite_rank_upper {p y d N} (h : FiniteInterior p y d N) (i : Nat) (hi : i≤N) :
    p i≤p 0+6*i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hs := h.pstep i (by omega)
    have hc : cost (d i)≤6 := by cases d i <;> decide
    have hh := ih (by omega)
    omega

/-- No square can have a half-length beyond this logarithmic-rank bound.
The coefficient comes from depth-three slope packing. -/
theorem square_bound {p y d k t} (h : FiniteInterior p y d (2*k))
    (hk : 0<k) (hd : PeriodicOn d k (2*k)) (hpow : p (2*k)<16^t) :
    29*k<64*t+6144 := by
  have h1 := finite_shift h 0 k (by omega)
  simp only [Nat.zero_add] at h1
  have h2 := finite_shift h k k (by omega)
  have h2' : FiniteInterior (fun i => p (k+i)) (fun i => y (k+i)) d k := by
    constructor
    · intro i hi
      have hs := h2.pstep i hi
      have hd' := hd i (by omega)
      change p (k+(i+1))=p (k+i)+cost (d (k+i)) at hs
      rw [show d (k+i)=d i by simpa [Nat.add_comm] using hd'] at hs
      exact hs
    · intro i hi
      have hs := h2.ystep i hi
      have hd' := hd i (by omega)
      change 16*y (k+(i+1))=y (k+i)+digit (d (k+i))*p (k+i)+offset (d (k+i)) at hs
      rw [show d (k+i)=d i by simpa [Nat.add_comm] using hd'] at hs
      exact hs
    · exact h2.interior
  have hgap : p 0<p k := by
    have hs := h.pstep 0 (by omega)
    have hc : 0<cost (d 0) := by cases d 0 <;> decide
    have hm := finite_rank_mono h 1 k (by omega) (by omega)
    simp only [Nat.zero_add] at hs
    omega
  have hh := common_block_bound (hdepth:=3) h1 h2' (by simpa using hgap)
      (P:=p (2*k)) (by change p (k+k)≤p (2*k); rw [show k+k=2*k by omega]; exact Nat.le_refl _) hpow
  change k<max (t+3+64*((p k-p 0)/12288+1)) (2*t+3*(64*((p k-p 0)/12288+1))) at hh
  have hupper := finite_rank_upper h k (by omega)
  have hB : 32*(64*((p k-p 0)/12288+1))≤k+2048 := by omega
  have hBmin : 64≤64*((p k-p 0)/12288+1) := by omega
  have hmax : max (t+3+64*((p k-p 0)/12288+1)) (2*t+3*(64*((p k-p 0)/12288+1)))=
      2*t+3*(64*((p k-p 0)/12288+1)) := by apply Nat.max_eq_right; omega
  rw [hmax] at hh
  omega

/-- The inductive exact signed paths can be exposed as finite indexed
paths without imposing a deterministic branch selection. -/
theorem path_finite_interior {N p y : Nat} (h : Path N p y)
    (hy : 0<y) (hp : 3*y<p) :
    ∃ ps ys ds, FiniteInterior ps ys ds N ∧ ps 0=p ∧ ys 0=y := by
  induction h with
  | nil p y =>
    refine ⟨fun _ => p,fun _ => y,fun _ => .zero,?_,rfl,rfl⟩
    constructor
    · intro i hi; omega
    · intro i hi; omega
    · intro i hi; exact ⟨hy,hp⟩
  | @cons d m p y hdiv tail ih =>
    have hs := interior_step d p y hy hp hdiv
    obtain ⟨ps,ys,ds,hfin,hp0,hy0⟩ := ih hs.1 hs.2
    let pp : Nat → Nat := fun i => match i with | 0 => p | j+1 => ps j
    let yy : Nat → Nat := fun i => match i with | 0 => y | j+1 => ys j
    let dd : Nat → Digit := fun i => match i with | 0 => d | j+1 => ds j
    refine ⟨pp,yy,dd,?_,rfl,rfl⟩
    constructor
    · intro i hi
      cases i with
      | zero => simp [pp,dd,hp0,nextP]
      | succ i => exact hfin.pstep i (by omega)
    · intro i hi
      cases i with
      | zero =>
        have hnum := Nat.mod_add_div (num d p y) 16
        rw [hdiv,Nat.zero_add] at hnum
        simpa [pp,yy,dd,hy0,nextY,num] using hnum
      | succ i => exact hfin.ystep i (by omega)
    · intro i hi
      cases i with
      | zero => exact ⟨hy,hp⟩
      | succ i => exact hfin.interior i (by omega)

/-- If an authentic q0 target is reached, its forced signed path has an
itinerary satisfying the logarithmic square bound at every position.
No assumption about the choice among legal inverse branches is made. -/
theorem q0_word_constraint {Reach : Nat → Nat → Prop} (src : Source Reach)
    (u n a b t : Nat) (hn : n=23+32*u) (ha : a+24*u+19=13*2^n)
    (hb : b+13=2*a) (hr : Reach a b) (hpow : 72*u+52<16^t) :
    ∃ ps ys ds, FiniteInterior ps ys ds (8*u+5) ∧
      ps 0=24*u+22 ∧ ys 0=6*u+4 ∧
      ∀ i k, 0<k → i+2*k≤8*u+5 →
        PeriodicOn (fun j => ds (i+j)) k (2*k) → 29*k<64*t+6144 := by
  obtain ⟨ps,ys,ds,hfin,hp0,hy0⟩ := path_finite_interior
    (q0_path src u n a b hn ha hb hr) (by omega) (by omega)
  refine ⟨ps,ys,ds,hfin,hp0,hy0,?_⟩
  intro i k hk hik hper
  have hs := finite_shift hfin i (2*k) hik
  have hbound := finite_rank_upper hfin (i+2*k) hik
  apply square_bound hs hk hper
  change ps (i+2*k)<16^t
  omega

#print axioms common_block_bound
#print axioms square_bound
#print axioms q0_word_constraint
end BB429Q0Macro
