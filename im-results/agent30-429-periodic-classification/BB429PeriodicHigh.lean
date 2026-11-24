import BB429Rank
import Lean

namespace BB429.PeriodicHigh

/-- Three ordinary branches, with all other successful transitions designated resets. -/
inductive Kind where
  | first | evenGap | oddGap
  deriving DecidableEq, Repr

/-- Guard and output of an ordinary branch, excluding the special odd-w=1 reset. -/
def High (k : Kind) (u w v z : Nat) : Prop :=
  match k with
  | .first => 2*u+3 ≤ w ∧ v=2*u+3 ∧ z=w-2*u-3
  | .evenGap => w % 2 = 1 ∧ 3 ≤ w ∧ w < 2*u ∧
      4 ≤ u-w/2 ∧ (u-w/2)%2=0 ∧ v=u-w/2+7 ∧ z=2*w-4
  | .oddGap => w % 2 = 1 ∧ w < 2*u ∧
      3 ≤ u-w/2 ∧ (u-w/2)%2=1 ∧ v=u-w/2+3 ∧ z=2*w

def A (u : Nat) : Nat := 2*u+6
def R (u w : Nat) : Nat := 2*u+w

theorem high_is_next {k u w v z} (h : High k u w v z) :
    BB429.next (u,w) = some (v,z) := by
  cases k <;> simp [High] at h
  · rcases h with ⟨hg,rfl,rfl⟩
    simp [BB429.next,hg]
  · rcases h with ⟨ho,hw,hl,hd,he,rfl,rfl⟩
    have h1 : ¬ w ≥ 2*u+3 := by omega
    have h2 : w ≠ 2*u+2 := by omega
    have h3 : w ≠ 2*u+1 := by omega
    have h4 : w ≠ 2*u := by omega
    have h5 : ¬ w%2=0 := by omega
    have h6 : u-w/2 ≠ 1 := by omega
    have h7 : u-w/2 ≠ 2 := by omega
    have h8 : w ≠ 1 := by omega
    simp [BB429.next,h1,h2,h3,h4,h5,h6,h7,he,h8]
  · rcases h with ⟨ho,hl,hd,he,rfl,rfl⟩
    have h1 : ¬ w ≥ 2*u+3 := by omega
    have h2 : w ≠ 2*u+2 := by omega
    have h3 : w ≠ 2*u+1 := by omega
    have h4 : w ≠ 2*u := by omega
    have h5 : ¬ w%2=0 := by omega
    have h6 : u-w/2 ≠ 1 := by omega
    have h7 : u-w/2 ≠ 2 := by omega
    have h8 : ¬ (u-w/2)%2=0 := by omega
    simp [BB429.next,h1,h2,h3,h4,h5,h6,h7,h8]

/-- An ordinary step on an even rank must be F. -/
theorem even_rank_first {k u w v z} (h : High k u w v z)
    (hr : R u w % 2 = 0) : k = .first := by
  cases k <;> simp [High,R] at * <;> omega

/-- Exact source-derived affine coordinates for the three branches. -/
theorem high_coordinates {k u w v z} (h : High k u w v z) :
    match k with
    | .first => A v = 2*A u ∧ R v z = R u w+3
    | .evenGap => A v + R u w = 2*A u+9 ∧ R v z=R u w+11 ∧ R u w%4=1
    | .oddGap => A v + R u w = 2*A u+1 ∧ R v z=R u w+7 ∧ R u w%4=3 := by
  cases k <;> simp [High] at h <;> simp [A,R] <;> omega

/-- Every two-step high-only block at an odd rank has its second branch F. -/
theorem block_coordinates {k j u w v z x y} (h : High k u w v z)
    (g : High j v z x y) (hr : R u w % 2 = 1) :
    j = .first ∧
    match k with
    | .first => A x = 4*A u ∧ R x y = R u w+6
    | .evenGap => A x+2*R u w = 4*A u+18 ∧ R x y=R u w+14 ∧ R u w%4=1
    | .oddGap => A x+2*R u w = 4*A u+2 ∧ R x y=R u w+10 ∧ R u w%4=3 := by
  have h0 := high_coordinates h
  have hg : R v z % 2 = 0 := by
    cases k <;> simp at h0 <;> omega
  have hj := even_rank_first g hg
  subst j
  have h1 := high_coordinates g
  cases k <;> simp at h0 h1 ⊢ <;> omega

/-- Positive rank growth on every successful transition, including resets. -/
theorem next_rank_growth {u w v z : Nat} (h : BB429.next (u,w) = some (v,z)) :
    R u w < R v z := by
  simp only [BB429.next] at h
  repeat' split at h
  all_goals simp_all [R]
  all_goals omega

/-- Every successful transition outside the three high branches resets u
    to one of the two constant values. -/
theorem high_or_reset {u w v z : Nat} (h : BB429.next (u,w) = some (v,z)) :
    (∃ k, High k u w v z) ∨ v=0 ∨ v=11 := by
  simp only [BB429.next] at h
  repeat' split at h
  all_goals simp_all
  all_goals first
    | omega
    | left; exact ⟨.first, by simp [High]; omega⟩
    | left; exact ⟨.evenGap, by simp [High]; omega⟩
    | left; exact ⟨.oddGap, by simp [High]; omega⟩

/-- Uniform one-step first-coordinate bound; resets can never enlarge it
    above 2u+11. -/
theorem next_first_bound {u w v z : Nat} (h : BB429.next (u,w) = some (v,z)) :
    v ≤ 2*u+11 := by
  obtain ⟨k,hk⟩ | hh := high_or_reset h
  · cases k <;> simp [High] at hk <;> omega
  · omega

/-- If the rank is large relative to the current first coordinate, the
    next step is necessarily F, and cannot reset the first coordinate. -/
theorem force_first {u w : Nat} (h : 4*u+3 ≤ R u w) :
    High .first u w (2*u+3) (w-2*u-3) := by
  simp [High,R] at *
  omega

/-- Allowed positive, even numerators in a mixed periodic base-4 expansion.
    Its digits are 0,2 and all rotations are strictly between 0 and 2/3. -/
def Low (m p : Nat) : Prop := 0 < p ∧ p%2=0 ∧ 6*p<m
def HighDigit (m p : Nat) : Prop := p%2=0 ∧ m<2*p ∧ 3*p<2*m

def lowList (m : Nat) : List Nat := List.range' 2 ((m-1)/12) 2
def highList (m : Nat) : List Nat :=
  List.range' (2*(m/4+1)) ((2*m-1)/6-m/4) 2

theorem low_mem {m p} (h : Low m p) : p ∈ lowList m := by
  apply List.mem_range'.2
  refine ⟨p/2-1, ?_, ?_⟩ <;> unfold Low at h <;> omega

theorem high_mem {m p} (h : HighDigit m p) : p ∈ highList m := by
  apply List.mem_range'.2
  refine ⟨p/2-(m/4+1), ?_, ?_⟩ <;> unfold HighDigit at h <;> omega

theorem mixed_count {m : Nat} (hm : 0<m) (ps : List Nat) (hn : ps.Nodup)
    (h : ∀ p ∈ ps, Low m p ∨ HighDigit m p) : 6*ps.length < m+6 := by
  have hs : ps ⊆ lowList m ++ highList m := by
    intro p hp
    rcases h p hp with hl|hh
    · exact List.mem_append_left _ (low_mem hl)
    · exact List.mem_append_right _ (high_mem hh)
  have hc := hn.length_le_of_subset hs
  simp [lowList,highList] at hc
  omega

theorem high_count {m : Nat} (hm : 0<m) (ps : List Nat) (hn : ps.Nodup)
    (h : ∀ p ∈ ps, HighDigit m p) : 12*ps.length < m+12 := by
  have hs : ps ⊆ highList m := fun p hp => high_mem (h p hp)
  have hc := hn.length_le_of_subset hs
  simp [highList] at hc
  omega

/-- A nonzero sequence that at least doubles cannot obey any linear bound. -/
theorem geometric_zero (x : Nat → Nat) (B G : Nat)
    (hg : ∀ n, 2*x n ≤ x (n+1)) (hb : ∀ n, x n ≤ B+G*n) : x 0=0 := by
  by_cases h : x 0=0
  · exact h
  exfalso
  have hn : ∀ n, n+1 ≤ x n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have hg' := hg n; omega
  let n := G+1
  have hj : ∀ j, (G+1)*j ≤ x (n+j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hp := hn (n+j)
      have hstep := hg (n+j)
      rw [Nat.mul_succ]
      have he : n+(j+1)=n+j+1 := by omega
      rw [he]
      have hp' : G+1 ≤ x (n+j) := Nat.le_trans (by dsimp [n]; omega) hp
      omega
  let j := B+G*n+1
  have hupper := hb (n+j)
  have hlower := hj j
  rw [Nat.mul_add] at hupper
  rw [Nat.add_mul, Nat.one_mul] at hlower
  dsimp [j] at hupper hlower
  omega

/-- An expansive affine integer recurrence with linearly bounded values
    must be at its fixed point. This is used on differences of a repeated
    affine block word, so it makes no analytic-limit assumption. -/
theorem affine_rigidity (q c : Int) (D : Nat → Int) (hq : 2≤q)
    (hrec : ∀ n, D (n+1)=q*D n-c)
    (B G : Nat) (hb : ∀ n, (D n).natAbs ≤ B+G*n) :
    (q-1)*D 0=c := by
  let E := fun n => (q-1)*D n-c
  have hE : ∀ n, E (n+1)=q*E n := by
    intro n
    dsimp [E]
    rw [hrec, Int.mul_sub, Int.mul_sub, ← Int.mul_assoc, Int.mul_comm (q-1) q,
        Int.mul_assoc]
    have hc : (q-1)*c=q*c-c := by rw [Int.sub_mul,Int.one_mul]
    rw [hc]
    omega
  have hEg : ∀ n, 2*(E n).natAbs ≤ (E (n+1)).natAbs := by
    intro n
    rw [hE, Int.natAbs_mul]
    apply Nat.mul_le_mul_right
    have hqa := Int.natAbs_of_nonneg (show 0≤q by omega)
    omega
  have hEb : ∀ n, (E n).natAbs ≤ ((q-1).natAbs*B+c.natAbs)+((q-1).natAbs*G)*n := by
    intro n
    have ha := Int.natAbs_sub_le ((q-1)*D n) c
    rw [Int.natAbs_mul] at ha
    have hd := Nat.mul_le_mul_left (q-1).natAbs (hb n)
    rw [Nat.mul_add, ← Nat.mul_assoc] at hd
    dsimp [E]
    omega
  have hzero := geometric_zero (fun n => (E n).natAbs) _ _ hEg hEb
  have he0 : E 0=0 := Int.natAbs_eq_zero.mp hzero
  dsimp [E] at he0
  omega

/-- A contracting inverse recurrence on the integer lattice cannot keep
    a nonzero geometric error for infinitely many steps. -/
theorem reverse_geometric_zero (q : Int) (x : Nat → Int) (hq : 2≤q)
    (h : ∀ n, x n=q*x (n+1)) : x 0=0 := by
  by_cases hzero : x 0=0
  · exact hzero
  exfalso
  have hnonzero : ∀ n, x n≠0 := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
      intro hz
      apply ih
      rw [h,hz,Int.mul_zero]
  have hdecrease : ∀ n, (x (n+1)).natAbs < (x n).natAbs := by
    intro n
    have he := congrArg Int.natAbs (h n)
    rw [Int.natAbs_mul] at he
    have hpos := Int.natAbs_pos.mpr (hnonzero (n+1))
    have hqa := Int.natAbs_of_nonneg (show 0≤q by omega)
    have hmul := Nat.mul_le_mul_right (x (n+1)).natAbs (show 2≤q.natAbs by omega)
    omega
  have hbound : ∀ n, (x n).natAbs+n ≤ (x 0).natAbs := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have hh := hdecrease n; omega
  have hh := hbound ((x 0).natAbs+1)
  omega

/-- Signed inverse grammar used by the dyadic ghost checker. -/
def SignedInv (k : Kind) (a b x y : Int) : Prop :=
  match k with
  | .first => a%2=1 ∧ 2*x=a-3 ∧ y=a+b
  | .evenGap => a%2=1 ∧ b%4=2 ∧ 4*x=4*a+b-26 ∧ 2*y=b+4
  | .oddGap => a%2=0 ∧ b%4=2 ∧ 4*x=4*a+b-14 ∧ 2*y=b

/-- In the strictly negative quadrant, every inverse edge stays there,
    except an S edge from b=-2. That exception has an even a and odd b
    at the predecessor and is rejected by the basic root filter. -/
theorem signed_negative_closed {k a b x y} (h : SignedInv k a b x y)
    (ha : a≤ -4) (hb : b<0) (hAllowed : x%2=0 → y%2=0) : x≤ -4 ∧ y<0 := by
  cases k <;> simp [SignedInv] at h <;> omega

/-- Despite the signed checker omitting positive-domain inequalities,
    in the negative quadrant its forward edges are deterministic. -/
theorem signed_forward_unique {k j a b x y v z}
    (h : SignedInv k x y a b) (g : SignedInv j v z a b)
    (_ha : a≤ -4) (_hb : b<0) (hx : x≤ -4) (hy : y<0)
    (hv : v≤ -4) (hz : z<0) : k=j ∧ x=v ∧ y=z := by
  cases k <;> cases j <;> simp [SignedInv] at h g ⊢ <;> omega

/-- The two odd-rank phases of the unique periodic signed corridor. -/
def Corridor (a b : Int) : Prop :=
  (a%4=1 ∧ b=a+8) ∨ (a%4=3 ∧ b=a+12)

/-- Any two negative forward steps from an odd corridor phase are the
    next odd corridor phase. This uses only inverse grammar, not positivity. -/
theorem signed_corridor_forward {k j a b x y v z}
    (h : SignedInv k x y a b) (g : SignedInv j v z x y)
    (ha : a≤ -4) (hb : b<0) (_hx : x≤ -4) (hy : y<0)
    (_hv : v≤ -4) (_hz : z<0) (hc : Corridor a b) : Corridor v z := by
  cases k <;> cases j <;> simp [SignedInv,Corridor] at * <;> omega

theorem ghost_outside_corridor (K : Int) : ¬ Corridor (-8-3*K) (5-6*K) := by
  simp [Corridor]
  omega

#print axioms reverse_geometric_zero
#print axioms signed_negative_closed
#print axioms signed_forward_unique
#print axioms signed_corridor_forward
#print axioms ghost_outside_corridor
#print axioms affine_rigidity
#print axioms high_is_next
#print axioms high_coordinates
#print axioms block_coordinates
#print axioms next_rank_growth
#print axioms high_or_reset
#print axioms mixed_count
#print axioms high_count

end BB429.PeriodicHigh
