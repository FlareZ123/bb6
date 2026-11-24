import Q0SlopePacking
import Lean.Elab.Tactic.Omega

namespace BB429Q0Macro
set_option maxHeartbeats 4000000

def Periodic {α : Type} (f : Nat → α) (k : Nat) : Prop :=
  ∀ i, f (i+k)=f i

/-- Actual exact integer paths; this does not assume determinism. -/
structure InteriorOrbit (p y : Nat → Nat) (d : Nat → Digit) : Prop where
  pstep : ∀ i, p (i+1)=p i+cost (d i)
  ystep : ∀ i, 16*y (i+1)=y i+digit (d i)*p i+offset (d i)
  interior : ∀ i, 0<y i ∧ 3*y i<p i

theorem p_monotone {p y d} (h : InteriorOrbit p y d) (i n : Nat) :
    p i≤p (i+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := h.pstep (i+n)
    rw [show i+(n+1)=i+n+1 by omega]
    omega

theorem periodic_p_drift {p y d} (h : InteriorOrbit p y d) (k : Nat)
    (hp : Periodic d k) :
    ∀ i, p (i+k)=p i+(p k-p 0) := by
  intro i
  induction i with
  | zero =>
    have h0 := p_monotone h 0 k
    simp only [Nat.zero_add] at h0 ⊢
    omega
  | succ i ih =>
    have h1 := h.pstep (i+k)
    have h2 := h.pstep i
    rw [hp i] at h1
    rw [show i+1+k=i+k+1 by omega]
    omega

theorem pow_ge_succ (n : Nat) : n+1≤16^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- An integer which contracts by exactly 16 forever must vanish. -/
theorem contract_zero (f : Nat → Int) (h : ∀ i, f i=16*f (i+1)) :
    ∀ i, f i=0 := by
  intro i
  have hp (n : Nat) : f i=(16:Int)^n*f (i+n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        f i = (16:Int)^n*f (i+n) := ih
        _ = (16:Int)^n*(16*f (i+n+1)) := by rw [h (i+n)]
        _ = (16:Int)^(n+1)*f (i+(n+1)) := by
          rw [Int.pow_succ,Int.mul_assoc,Nat.add_assoc]
  apply Classical.byContradiction
  intro hn
  let n := (f i).natAbs+1
  have he := congrArg Int.natAbs (hp n)
  rw [Int.natAbs_mul,Int.natAbs_pow] at he
  change (f i).natAbs=16^n*(f (i+n)).natAbs at he
  have hpos : 0<(f (i+n)).natAbs := by
    apply Classical.byContradiction
    intro h0
    have hz : (f (i+n)).natAbs=0 := by omega
    simp [hz] at he
    exact hn he
  have hlo := Nat.le_mul_of_pos_right (16^n) hpos
  have hh := pow_ge_succ n
  have hnle : (f i).natAbs<n+1 := by dsimp [n]; omega
  omega

/-- A periodic sequence with f_i≤16f_{i+1} is nonnegative. -/
theorem periodic_nonneg (f : Nat → Int) (k : Nat) (hk : 0<k)
    (hp : Periodic f k) (h : ∀ i, f i≤16*f (i+1)) :
    ∀ i, 0≤f i := by
  intro i
  apply Classical.byContradiction
  intro hn
  have hstrict (n : Nat) : f i < f (i+n+1) := by
    induction n with
    | zero => have hs := h i; simp only [Nat.add_zero]; omega
    | succ n ih =>
      have hs := h (i+n+1)
      rw [show i+(n+1)+1=i+n+1+1 by omega]
      omega
  have h' := hstrict (k-1)
  have he : i+(k-1)+1=i+k := by omega
  rw [he,hp i] at h'
  omega

theorem periodic_lift {α : Type} {f : Nat → α} {k : Nat}
    (h : Periodic f k) (i n : Nat) :
    f (i+n*k)=f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul,←Nat.add_assoc,h,ih]

theorem digit_bound (d : Digit) : digit d≤5 := by
  cases d <;> decide

/-- Difference of two copies of a periodic exact orbit is an integer
constant-rank slope walk, itself periodic and in the closed slope interval. -/
theorem periodic_slopes {p y d} (h : InteriorOrbit p y d) (k : Nat)
    (hk : 0<k) (hd : Periodic d k) :
    ∃ t : Nat → Nat,
      Periodic t k ∧
      (∀ i, 3*t i≤p k-p 0) ∧
      (∀ i, 16*t (i+1)=t i+digit (d i)*(p k-p 0)) := by
  let L := p k-p 0
  let f : Nat → Int := fun i => (y (i+k):Int)-(y i:Int)
  have hpd := periodic_p_drift h k hd
  have hf (i : Nat) : 16*f (i+1)=f i+(digit (d i):Int)*(L:Int) := by
    have h1 := congrArg Int.ofNat (h.ystep (i+k))
    have h2 := congrArg Int.ofNat (h.ystep i)
    rw [hd i,hpd i] at h1
    dsimp [f,L]
    rw [show i+1+k=i+k+1 by omega]
    cases hdigit : d i <;> simp [hdigit,digit,offset] at h1 h2 ⊢ <;> omega
  let e : Nat → Int := fun i => f (i+k)-f i
  have he (i : Nat) : e i=16*e (i+1) := by
    have h1 := hf (i+k)
    have h2 := hf i
    rw [hd i] at h1
    dsimp [e]
    rw [show i+1+k=i+k+1 by omega]
    omega
  have he0 := contract_zero e he
  have hp : Periodic f k := by
    intro i
    have hi := he0 i
    dsimp [e] at hi
    omega
  have hL : 0≤(L:Int) := Int.natCast_nonneg _
  have hnonneg : ∀ i, 0≤f i := by
    apply periodic_nonneg f k hk hp
    intro i
    have hmul : 0≤(digit (d i):Int)*(L:Int) :=
      Int.mul_nonneg (Int.natCast_nonneg _) hL
    have hs := hf i
    omega
  let g : Nat → Int := fun i => (L:Int)-3*f i
  have hgper : Periodic g k := by
    intro i
    dsimp [g]
    rw [hp i]
  have hgnonneg : ∀ i, 0≤g i := by
    apply periodic_nonneg g k hk hgper
    intro i
    have hs := hf i
    have hb := digit_bound (d i)
    have hb' : 0≤15-3*(digit (d i):Int) := by omega
    have hm := Int.mul_nonneg hb' hL
    rw [Int.sub_mul,Int.mul_assoc] at hm
    dsimp [g]
    omega
  let t : Nat → Nat := fun i => (f i).toNat
  have ht (i : Nat) : (t i:Int)=f i := Int.toNat_of_nonneg (hnonneg i)
  refine ⟨t,?_,?_,?_⟩
  · intro i
    dsimp [t]
    rw [hp i]
  · intro i
    have hi := hgnonneg i
    dsimp [g] at hi
    have hti := ht i
    omega
  · intro i
    have hi := hf i
    rw [←ht i,←ht (i+1)] at hi
    change 16*t (i+1)=t i+digit (d i)*L
    omega

theorem slope_reverse_unique (L a b c : Nat) (d e : Digit)
    (hL : 0<L) (ha : 3*a≤L) (hc : 3*c≤L)
    (h1 : 16*b=a+digit d*L) (h2 : 16*b=c+digit e*L) :
    a=c ∧ d=e := by
  cases d <;> cases e <;> simp [digit] at * <;> omega

/-- A repeated slope inside one period forces a shorter digit period:
reverse slope steps are unique, and periodic lifting supplies as much
prehistory as needed. -/
theorem slope_repeat_shortens {t : Nat → Nat} {d : Nat → Digit} {k L : Nat}
    (hk : 0<k) (hL : 0<L) (ht : Periodic t k)
    (hb : ∀ i, 3*t i≤L)
    (hs : ∀ i, 16*t (i+1)=t i+digit (d i)*L)
    (i j : Nat) (hij : i<j) (he : t i=t j) :
    Periodic d (j-i) := by
  let gap := j-i
  have hg : j=i+gap := by dsimp [gap]; omega
  have back (a : Nat) (h : t (a+1)=t (a+1+gap)) :
      t a=t (a+gap) ∧ d a=d (a+gap) := by
    have h1 := hs a
    have h2 := hs (a+gap)
    rw [show a+gap+1=a+1+gap by omega,←h] at h2
    exact slope_reverse_unique L _ _ _ _ _ hL (hb a) (hb (a+gap)) h1 h2
  have down (a n : Nat) (h : t (a+n)=t (a+n+gap)) :
      t a=t (a+gap) := by
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have hh : t (a+n+1)=t (a+n+1+gap) := by simpa [Nat.add_assoc] using h
      exact ih (back (a+n) hh).1
  intro m
  let I := i+(m+1)*k
  have hI : m+1≤I := by
    have hh := Nat.le_mul_of_pos_right (m+1) hk
    dsimp [I]
    omega
  have h0 : t I=t (I+gap) := by
    dsimp [I]
    rw [periodic_lift ht i (m+1)]
    rw [show i+(m+1)*k+gap=(i+gap)+(m+1)*k by omega]
    rw [periodic_lift ht (i+gap) (m+1),←hg,he]
  have h1 : t (m+1)=t (m+1+gap) := by
    apply down (m+1) (I-(m+1))
    rw [show m+1+(I-(m+1))=I by omega]
    exact h0
  exact (back m h1).2.symm

def segment {α : Type} (f : Nat → α) (i : Nat) : Nat → List α
  | 0 => []
  | n+1 => f i::segment f (i+1) n

@[simp] theorem length_segment {α : Type} (f : Nat → α) (i n : Nat) :
    (segment f i n).length=n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [segment,ih]

theorem get_segment {α : Type} (f : Nat → α) (i n j : Nat)
    (hj : j<n) : (segment f i n)[j]'(by simpa using hj)=f (i+j) := by
  induction n generalizing i j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [segment]
    | succ j =>
      simp only [segment,List.getElem_cons_succ]
      rw [ih (i+1) j (by omega)]
      congr 1
      omega

theorem segment_mem {α : Type} (f : Nat → α) (i n j : Nat) (hj : j<n) :
    f (i+j)∈segment f i n := by
  rw [←get_segment f i n j hj]
  exact List.getElem_mem _

theorem segment_cost {p y d} (h : InteriorOrbit p y d) (i n : Nat) :
    p (i+n)=p i+costSum (segment d i n) := by
  induction n generalizing i with
  | zero => simp [segment,costSum]
  | succ n ih =>
    rw [show i+(n+1)=(i+1)+n by omega,ih (i+1),h.pstep i]
    simp [segment,costSum]
    omega

theorem segment_walk {L : Nat} {t : Nat → Nat} {d : Nat → Digit}
    (hs : ∀ i, 16*t (i+1)=t i+digit (d i)*L) (i n : Nat) :
    SlopeWalk L (segment d i n) (segment t (i+1) n) (t i) (t (i+n)) := by
  induction n generalizing i with
  | zero => simpa [segment] using SlopeWalk.nil (L:=L) (t i)
  | succ n ih =>
    rw [show i+(n+1)=(i+1)+n by omega]
    exact SlopeWalk.cons (hs i) (ih (i+1))

theorem periodic_constant {α : Type} {d : Nat → α} {k : Nat} (hk : 0<k)
    (hp : Periodic d k) (a : α) (h : ∀ i, i<k → d i=a) :
    ∀ i, d i=a := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases hi : i<k
    · exact h i hi
    · have hh : i-k+k=i := by omega
      have hs := hp (i-k)
      rw [hh] at hs
      exact hs.trans (ih (i-k) (by omega))

theorem exists_minimal (P : Nat → Prop) (hex : ∃ n,P n) :
    ∃ k, P k ∧ ∀ j,P j → k≤j := by
  obtain ⟨n,hn⟩ := hex
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : ∃ j, j<n ∧ P j
    · obtain ⟨j,hj,hp⟩ := h
      exact ih j hj hp
    · exact ⟨n,hn,fun j hj => by
        apply Classical.byContradiction
        intro hc
        exact h ⟨j,by omega,hj⟩⟩

/-- No infinite strict-interior orbit can have a periodic digit sequence. -/
theorem no_periodic_interior {p y d} (h : InteriorOrbit p y d) :
    ¬ ∃ k, 0<k ∧ Periodic d k := by
  intro hex
  classical
  obtain ⟨k,⟨hk,hd⟩,hminimal⟩ := exists_minimal (fun k => 0<k ∧ Periodic d k) hex
  have hmin (j : Nat) (hj : 0<j) (hper : Periodic d j) : k≤j :=
    hminimal j ⟨hj,hper⟩
  obtain ⟨t,ht,hb,hs⟩ := periodic_slopes h k hk hd
  let L := p k-p 0
  have hL : 0<L := by
    have hmono := p_monotone h 1 (k-1)
    have hstep := h.pstep 0
    simp only [Nat.zero_add] at hstep
    have hcost : 0<cost (d 0) := by cases d 0 <;> decide
    dsimp [L]
    rw [show 1+(k-1)=k by omega] at hmono
    omega
  let ds := segment d 0 k
  let ts := segment t 1 k
  have hnodup : ts.Nodup := by
    rw [List.nodup_iff_eq_of_getElem_eq]
    intro i j hi hj he
    have hi' : i<k := by simpa [ts] using hi
    have hj' : j<k := by simpa [ts] using hj
    change (segment t 1 k)[i]=(segment t 1 k)[j] at he
    rw [get_segment t 1 k i hi',get_segment t 1 k j hj'] at he
    rcases Nat.lt_trichotomy i j with hlt|heq|hgt
    · have hper := slope_repeat_shortens hk hL ht hb hs (1+i) (1+j) (by omega) he
      have hsmall := hmin (1+j-(1+i)) (by omega) hper
      omega
    · exact heq
    · have hper := slope_repeat_shortens hk hL ht hb hs (1+j) (1+i) (by omega) he.symm
      have hsmall := hmin (1+i-(1+j)) (by omega) hper
      omega
  have hw := segment_walk hs 0 k
  simp only [Nat.zero_add] at hw
  have ht0 : t k=t 0 := by simpa using ht 0
  rw [ht0] at hw
  have hc := segment_cost h 0 k
  simp only [Nat.zero_add] at hc
  have hcost : L=costSum ds := by dsimp [L,ds]; omega
  have hconst := simple_slope_cycle hw (hb 0) hnodup
      (by simpa [ds] using hk) hcost
  rcases hconst with hz|hf
  · have hzero : ∀ i, d i=Digit.zero := by
      apply periodic_constant hk hd .zero
      intro i hi
      exact hz (d i) (by simpa [ds] using segment_mem d 0 k i hi)
    have hycontract : ∀ i, (y i:Int)=16*(y (i+1):Int) := by
      intro i
      have hh := h.ystep i
      rw [hzero i] at hh
      simp [digit,offset] at hh
      omega
    have h0 := contract_zero (fun i => (y i:Int)) hycontract 0
    have hh := (h.interior 0).1
    omega
  · have hfive : ∀ i, d i=Digit.five := by
      apply periodic_constant hk hd .five
      intro i hi
      exact hf (d i) (by simpa [ds] using segment_mem d 0 k i hi)
    let z : Nat → Int := fun i => (p i:Int)-3*(y i:Int)
    have hzcontract : ∀ i, z i=16*z (i+1) := by
      intro i
      have h1 := h.ystep i
      have h2 := h.pstep i
      rw [hfive i] at h1 h2
      simp [digit,offset,cost] at h1 h2
      dsimp [z]
      omega
    have h0 := contract_zero z hzcontract 0
    have hh := (h.interior 0).2
    dsimp [z] at h0
    omega

/-- Every eventually periodic infinite word would have a periodic tail
which remains strictly interior. -/
theorem no_eventually_periodic_interior {p y d} (h : InteriorOrbit p y d)
    (start : Nat) : ¬ ∃ k, 0<k ∧ Periodic (fun i => d (start+i)) k := by
  have hshift : InteriorOrbit (fun i => p (start+i)) (fun i => y (start+i))
      (fun i => d (start+i)) := by
    constructor
    · intro i; simpa [Nat.add_assoc] using h.pstep (start+i)
    · intro i; simpa [Nat.add_assoc] using h.ystep (start+i)
    · intro i; exact h.interior (start+i)
  exact no_periodic_interior hshift

#print axioms contract_zero
#print axioms periodic_slopes
#print axioms slope_repeat_shortens
#print axioms no_periodic_interior
#print axioms no_eventually_periodic_interior
end BB429Q0Macro
