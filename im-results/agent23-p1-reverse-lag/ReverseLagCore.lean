import LagChecker
import BatchCarry

namespace BB6.Agent23ReverseLag

open BB6.Agent45.DelayedCarry
open BB6.Agent9BatchCarry

/-- A delayed-carry edge at clock q with target bit y.  The source and
    destination carries are both below q; the next clock is q+1. -/
def EdgeY (q y c z : Nat) : Prop :=
  c < q ∧ z < q ∧ y ≤ 1 ∧
    (2*z+y=c ∨ 2*z+y=c+q)

/-- The two monotone branches of the unique modular predecessor map. -/
def lowBranch (q y : Nat) (zs : List Nat) : List Nat :=
  ((zs.filter fun z => decide (z<q ∧ 2*z+y<q)).map fun z => 2*z+y)

def highBranch (q y : Nat) (zs : List Nat) : List Nat :=
  ((zs.filter fun z => decide (z<q ∧ q≤2*z+y)).map fun z => 2*z+y-q)

/-- Exact set of predecessor carries for one delayed target bit. -/
def backY (q y : Nat) (zs : List Nat) : List Nat :=
  BB6.Agent9BatchCarry.join
    ((lowBranch q y zs).length + (highBranch q y zs).length)
    (lowBranch q y zs) (highBranch q y zs)

theorem mem_lowBranch (q y c : Nat) (zs : List Nat) :
    c ∈ lowBranch q y zs ↔
      ∃ z∈zs, z<q ∧ 2*z+y<q ∧ c=2*z+y := by
  simp only [lowBranch, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨z,⟨hz,⟨hzq,hlo⟩⟩,rfl⟩
    exact ⟨z,hz,hzq,hlo,rfl⟩
  · rintro ⟨z,hz,hzq,hlo,rfl⟩
    exact ⟨z,⟨hz,⟨hzq,hlo⟩⟩,rfl⟩

theorem mem_highBranch (q y c : Nat) (zs : List Nat) :
    c ∈ highBranch q y zs ↔
      ∃ z∈zs, z<q ∧ q≤2*z+y ∧ c=2*z+y-q := by
  simp only [highBranch, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨z,⟨hz,⟨hzq,hhi⟩⟩,rfl⟩
    exact ⟨z,hz,hzq,hhi,rfl⟩
  · rintro ⟨z,hz,hzq,hhi,rfl⟩
    exact ⟨z,⟨hz,⟨hzq,hhi⟩⟩,rfl⟩

/-- The sorted-merge implementation has the exact predecessor relation.
    No assumption on list order is needed for membership soundness. -/
theorem mem_backY (q y c : Nat) (zs : List Nat) (hy : y≤1) :
    c ∈ backY q y zs ↔ ∃ z∈zs, EdgeY q y c z := by
  unfold backY
  rw [BB6.Agent9BatchCarry.mem_join]
  constructor
  · rintro (hlo|hhi)
    · obtain ⟨z,hz,hzq,hlt,rfl⟩ := (mem_lowBranch q y c zs).mp hlo
      refine ⟨z,hz,?_⟩
      exact ⟨by omega,hzq,hy,Or.inl rfl⟩
    · obtain ⟨z,hz,hzq,hge,rfl⟩ := (mem_highBranch q y c zs).mp hhi
      refine ⟨z,hz,?_⟩
      refine ⟨by omega,hzq,hy,Or.inr ?_⟩
      omega
  · rintro ⟨z,hz,⟨hc,hzq,hy,hbranch⟩⟩
    rcases hbranch with hlow|hhigh
    · left
      exact (mem_lowBranch q y c zs).mpr
        ⟨z,hz,hzq,by omega,by omega⟩
    · right
      exact (mem_highBranch q y c zs).mpr
        ⟨z,hz,hzq,by omega,by omega⟩

/-- For a fixed target bit, the predecessor is the unique residue
    (2*z+y) mod q in the strict range 0,...,q-1. -/
theorem edgeY_iff_mod (q y c z : Nat) (hy : y≤1) (hz : z<q) :
    EdgeY q y c z ↔ c<q ∧ c=(2*z+y)%q := by
  constructor
  · rintro ⟨hc,hz',_,hbranch⟩
    refine ⟨hc,?_⟩
    rcases hbranch with hlow|hhigh
    · rw [hlow,Nat.mod_eq_of_lt (by omega)]
    · rw [hhigh,Nat.add_mod_right,Nat.mod_eq_of_lt hc]
  · rintro ⟨hc,hmod⟩
    by_cases hlow : 2*z+y<q
    · have hrem : (2*z+y)%q = 2*z+y := Nat.mod_eq_of_lt hlow
      have heq : c=2*z+y := by rw [hrem] at hmod; exact hmod
      exact ⟨hc,hz,hy,Or.inl heq.symm⟩
    · have hge : q≤2*z+y := by omega
      have hrem : (2*z+y)%q = 2*z+y-q := by
        rw [Nat.mod_eq_sub_mod hge]
        exact Nat.mod_eq_of_lt (by omega)
      have heq : c=2*z+y-q := by rw [hrem] at hmod; exact hmod
      exact ⟨hc,hz,hy,Or.inr (by omega)⟩

/-- A forward delayed-carry path, with its target bits stored in reverse
    chronological order.  The last bit is therefore at the head of the list. -/
inductive DWalk : Nat → Nat → List Nat → Nat → Prop
  | nil (q c : Nat) : DWalk q c [] c
  | snoc (q c : Nat) (ys : List Nat) (z y w : Nat)
      (h : DWalk q c ys z)
      (he : EdgeY (q+ys.length) y z w) :
      DWalk q c (y::ys) w

/-- Rewind a reverse-chronological bit word from an arbitrary terminal set. -/
def reverseFold (q : Nat) : List Nat → List Nat → List Nat
  | [], acc => acc
  | y::ys, acc => reverseFold q ys (backY (q+ys.length) y acc)

/-- All starting carries that can reach some terminal carry after this word. -/
def reverseLive (q : Nat) (ys : List Nat) : List Nat :=
  reverseFold q ys (List.range (q+ys.length))

theorem mem_reverseFold (q c : Nat) (ys acc : List Nat)
    (hys : ∀ y∈ys, y≤1) :
    c ∈ reverseFold q ys acc ↔
      ∃ z, DWalk q c ys z ∧ z∈acc := by
  revert c acc hys
  induction ys with
  | nil =>
    intro c acc hys
    simp [reverseFold]
    constructor
    · intro hc
      exact ⟨c,DWalk.nil q c,hc⟩
    · rintro ⟨z,hwalk,hz⟩
      cases hwalk
      exact hz
  | cons y ys ih =>
    intro c acc hys
    have hy : y≤1 := hys y (by simp)
    have hys' : ∀ z∈ys, z≤1 := by
      intro z hz
      exact hys z (by simp [hz])
    simp only [reverseFold]
    rw [ih c (backY (q+ys.length) y acc) hys']
    constructor
    · rintro ⟨z,hwalk,hback⟩
      obtain ⟨w,hw,hedge⟩ := (mem_backY (q+ys.length) y z acc hy).mp hback
      exact ⟨w,DWalk.snoc q c ys z y w hwalk hedge,hw⟩
    · rintro ⟨w,hwalk,hw⟩
      cases hwalk with
      | snoc ys z y w hprev hedge =>
        exact ⟨z,hprev,(mem_backY (q+ys.length) y z acc hy).mpr ⟨w,hw,hedge⟩⟩

theorem mem_reverseLive (q c : Nat) (ys : List Nat)
    (hys : ∀ y∈ys, y≤1) :
    c ∈ reverseLive q ys ↔
      ∃ z, DWalk q c ys z ∧ z<q+ys.length := by
  unfold reverseLive
  rw [mem_reverseFold q c ys (List.range (q+ys.length)) hys]
  constructor
  · rintro ⟨z,hwalk,hz⟩
    have hz' : z∈List.range (q+ys.length) := hz
    exact ⟨z,hwalk,(List.mem_range.mp hz')⟩
  · rintro ⟨z,hwalk,hz⟩
    exact ⟨z,hwalk,(List.mem_range.mpr hz)⟩

/-- The reverse-chronological delayed target word determined by a prefix. -/
def targetsRev (n s B : Nat) : Nat → List Nat
  | 0 => []
  | k+1 => target n (s+k) B :: targetsRev n s B k

@[simp] theorem targetsRev_length (n s B k : Nat) :
    (targetsRev n s B k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [targetsRev,ih]


theorem targetsRev_bits (n s B k : Nat) :
    ∀ y∈targetsRev n s B k, y≤1 := by
  induction k with
  | zero => simp [targetsRev]
  | succ k ih =>
    intro y hy
    simp [targetsRev] at hy
    rcases hy with rfl|hy
    · exact target_bound n (s+k) B
    · exact ih y hy


/-- The first n delayed target bits depend only on the current low prefix. -/
theorem targetsRev_prefix_stable (n s B R : Nat) :
    ∀ k, k≤n →
      targetsRev n s (B+2^s*R) k = targetsRev n s B k := by
  intro k
  induction k with
  | zero =>
    intro hk
    rfl
  | succ k ih =>
    intro hk
    simp only [targetsRev]
    have hhead : target n (s+k) (B+2^s*R) = target n (s+k) B :=
      target_prefix n s (s+k) B R (by omega)
    have htail := ih (by omega)
    rw [hhead,htail]

/-- Future high bits do not alter target bits already fixed by the prefix. -/
theorem targetsRev_stable_of (n s B S R : Nat) (hn : 0<n) :
    ∀ k, s+k≤S →
      targetsRev n s (B+2^S*R) k = targetsRev n s B k := by
  intro k
  induction k with
  | zero =>
    intro hS
    rfl
  | succ k ih =>
    intro hS
    simp only [targetsRev]
    have hhead : target n (s+k) (B+2^S*R) = target n (s+k) B :=
      target_prefix n S (s+k) B R (by omega)
    have htail := ih (by omega)
    rw [hhead,htail]

/-- Any exact Extend segment gives a delayed-carry path.  The final word C
    determines every target bit in the segment, by target_prefix. -/
theorem extend_to_DWalk (n s B a k C c : Nat)
    (hn : 0<n) (hTrace : Trace n s B a)
    (hExt : Extend n s B a k C c) :
    DWalk (n+s+3) a (targetsRev n s C k) c := by
  revert hTrace
  induction hExt with
  | nil =>
    intro hTrace
    exact DWalk.nil (n+s+3) a
  | @step k C c x d h hx he ih =>
    intro hTrace
    have hTracePrev := extend_trace n s B a k C c hTrace h
    have hcarry : c<n+s+k+3 := by
      have hb := (trace_bounds n (s+k) C c hTracePrev).2.2.2
      omega
    have htail :
        targetsRev n s (C+2^(s+k)*x) k = targetsRev n s C k :=
      targetsRev_stable_of n s C (s+k) x hn k (by omega)
    have hhead :
        target n (s+k) (C+2^(s+k)*x) = target n (s+k) C :=
      target_prefix n (s+k) (s+k) C x (by omega)
    have he' :
        2*d+target n (s+k) (C+2^(s+k)*x) =
          c+x*(n+s+k+3) := by
      simpa [hhead,Nat.add_assoc] using he
    have hnext : d<n+s+k+3 := by
      have hy := target_bound n (s+k) (C+2^(s+k)*x)
      have hx' : x=0 ∨ x=1 := by omega
      rcases hx' with h0|h1 <;> subst x <;> omega
    have hedge :
        EdgeY (n+s+k+3) (target n (s+k) (C+2^(s+k)*x)) c d := by
      refine ⟨hcarry,hnext,target_bound n (s+k) (C+2^(s+k)*x),?_⟩
      rcases (show x=0 ∨ x=1 by omega) with h0|h1
      · left
        subst x
        simpa [Nat.add_assoc] using he'
      · right
        subst x
        simpa [Nat.add_assoc] using he'
    have hwalk : DWalk (n+s+3) a
        (targetsRev n s (C+2^(s+k)*x) k) c := by
      rw [htail]
      exact ih hTrace
    simpa [targetsRev,targetsRev_length,Nat.add_assoc] using
      DWalk.snoc (n+s+3) a
        (targetsRev n s (C+2^(s+k)*x) k) c
        (target n (s+k) (C+2^(s+k)*x)) d hwalk hedge

/-- The reverse-live set is a sound, exact Boolean lookahead for any
    delayed-carry extension of length k. -/
theorem reverseLookahead_sound (n s B a k C c : Nat)
    (hn : 0<n) (hTrace : Trace n s B a)
    (hExt : Extend n s B a k C c) :
    a ∈ reverseLive (n+s+3) (targetsRev n s C k) := by
  have hys := targetsRev_bits n s C k
  rw [mem_reverseLive (n+s+3) a (targetsRev n s C k) hys]
  refine ⟨c,extend_to_DWalk n s B a k C c hn hTrace hExt,?_⟩
  have htr := extend_trace n s B a k C c hTrace hExt
  have hb := (trace_bounds n (s+k) C c htr).2.2.2
  simp only [targetsRev_length]
  omega

/-- Executable Boolean form used by block prefix filters. -/
def reverseLookahead (n s B a k : Nat) : Bool :=
  decide (a ∈ reverseLive (n+s+3) (targetsRev n s B k))

def nextBlockReverse (n s h : Nat) (ps : List Prefix) : List Prefix :=
  (advance n s ps h).filter fun p =>
    reverseLookahead n (s+h) p.1 p.2 n

/-- The reverse-live filter preserves every authentic prefix that has an
    n-step continuation.  This is the replacement for lookahead_sound. -/
theorem covered_next_reverse (n s h : Nat) (ps : List Prefix)
    (hn : 0<n) (hS : 1≤s) (hcover : Covered n s ps) :
    Covered n (s+h) (nextBlockReverse n s h ps) := by
  intro B a C c htr hE
  obtain ⟨D,d,hpre,hExt⟩ :=
    trace_split n (s+h) B a s htr hS (by omega)
  have hExt' : Extend n s D d h B a := by
    simpa using hExt
  have hfull : Extend n s D d (h+n) C c :=
    extend_append n s D d h B a n C c hExt' hE
  obtain ⟨F,f,hshort⟩ :=
    extend_prefix n s D d (h+n) C c n hfull (by omega)
  have hm := hcover D d F f hpre hshort
  have hm' := extend_in_advance n s D d h B a ps hm hExt'
  obtain ⟨R,hR⟩ := extend_mod n (s+h) B a n C c hE
  have htargets :
      targetsRev n (s+h) C n = targetsRev n (s+h) B n := by
    rw [hR]
    exact targetsRev_prefix_stable n (s+h) B R n (by omega)
  have hrev := reverseLookahead_sound n (s+h) B a n C c hn htr hE
  rw [htargets] at hrev
  have hfilter : reverseLookahead n (s+h) B a n = true := by
    simp [reverseLookahead,hrev]
  simp [nextBlockReverse,hm',hfilter]

#print axioms mem_backY
#print axioms mem_reverseLive
#print axioms extend_to_DWalk
#print axioms reverseLookahead_sound
#print axioms covered_next_reverse

end BB6.Agent23ReverseLag
