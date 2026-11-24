import BB429PeriodicCycle

namespace BB429.PeriodicHigh

def LinearBound (f : Nat → Int) : Prop :=
  ∃ B G : Nat, ∀ n, (f n).natAbs≤B+G*n

theorem linear_shift {f : Nat → Int} (h : LinearBound f) (s : Nat) :
    LinearBound (fun n => f (n+s)) := by
  obtain ⟨B,G,hb⟩ := h
  refine ⟨B+G*s,G,?_⟩
  intro n
  have hh := hb (n+s)
  rw [Nat.mul_add] at hh
  dsimp only
  omega

theorem linear_sub {f g : Nat → Int} (hf : LinearBound f) (hg : LinearBound g) :
    LinearBound (fun n => f n-g n) := by
  obtain ⟨B,G,hb⟩ := hf
  obtain ⟨B',G',hb'⟩ := hg
  refine ⟨B+B',G+G',?_⟩
  intro n
  have h := Int.natAbs_sub_le (f n) (g n)
  have h1 := hb n
  have h2 := hb' n
  dsimp only
  rw [Nat.add_mul]
  omega

theorem linear_geometric_zero {f : Nat → Int} (h : LinearBound f)
    (hr : ∀ n, f (n+1)=4*f n) : ∀ n, f n=0 := by
  intro s
  let g := fun n => f (n+s)
  obtain ⟨B,G,hg⟩ := linear_shift h s
  have hrec : ∀ n, g (n+1)=4*g n-0 := by
    intro n
    dsimp [g]
    rw [show n+1+s=n+s+1 by omega, hr, Int.sub_zero]
  have hh := affine_rigidity 4 0 g (by decide) hrec B G hg
  dsimp [g] at hh
  simp at hh
  omega

/-- Exact integer cycle induced by taking differences over a full labelled
    period. The factor four is removed using congruence, not division of an
    approximate real slope. -/
theorem periodic_difference_forward (A R : Nat → Int) (e : Nat → Bool)
    (c : Nat → Int) (L l m : Nat) (hl : 0<l)
    (hs : ∀ n, A (n+1)=4*A n-(if e n then 2*R n else 0)+c n)
    (hR : ∀ n, R (n+L)=R n+4*(m:Int))
    (hL : ∀ n, e (n+L)=e n) (hc : ∀ n, c (n+L)=c n)
    (he : ∀ n, e (n+l)=e n) (hA : LinearBound A) :
    ∃ p : Nat → Int, (∀ n, p (n+l)=p n) ∧
      (∀ n, p (n+1)=4*p n-(if e n then 2*(m:Int) else 0)) := by
  let D := fun n => A (n+L)-A n
  have hD : ∀ n, D (n+1)=4*D n-(if e n then 8*(m:Int) else 0) := by
    intro n
    have h1 := hs (n+L)
    have h2 := hs n
    rw [hL,hR,hc] at h1
    dsimp [D]
    rw [show n+1+L=n+L+1 by omega]
    cases h : e n <;> simp [h] at h1 h2 ⊢ <;> omega
  have hbD : LinearBound D := linear_sub (linear_shift hA L) hA
  let E := fun n => D (n+l)-D n
  have hE : ∀ n, E (n+1)=4*E n := by
    intro n
    have h1 := hD (n+l)
    have h2 := hD n
    rw [he] at h1
    dsimp [E]
    rw [show n+1+l=n+l+1 by omega]
    omega
  have hEb : LinearBound E := linear_sub (linear_shift hbD l) hbD
  have hper : ∀ n, D (n+l)=D n := by
    intro n
    have hh := linear_geometric_zero hEb hE n
    dsimp [E] at hh
    omega
  have hmod : ∀ n, D n%4=0 := by
    intro n
    have hh := hD (n+l-1)
    rw [show n+l-1+1=n+l by omega,hper] at hh
    cases h : e (n+l-1) <;> simp [h] at hh <;> omega
  refine ⟨fun n => D n/4, ?_, ?_⟩
  · intro n; dsimp only; rw [hper]
  · intro n
    have hh := hD n
    have h1 := hmod n
    have h2 := hmod (n+1)
    dsimp only
    cases h : e n <;> simp [h] at hh ⊢ <;> omega

/-- Backward version: integrality replaces the forward growth bound. -/
theorem periodic_difference_backward (A R : Nat → Int) (e : Nat → Bool)
    (c : Nat → Int) (L l m : Nat)
    (hs : ∀ n, A n=4*A (n+1)-(if e n then 2*R (n+1) else 0)+c n)
    (hR : ∀ n, R (n+L)=R n-4*(m:Int))
    (hL : ∀ n, e (n+L)=e n) (hc : ∀ n, c (n+L)=c n)
    (he : ∀ n, e (n+l)=e n) :
    ∃ p : Nat → Int, (∀ n, p (n+l)=p n) ∧
      (∀ n, p n=4*p (n+1)-(if e n then 2*(m:Int) else 0)) := by
  let D := fun n => A n-A (n+L)
  have hD : ∀ n, D n=4*D (n+1)-(if e n then 8*(m:Int) else 0) := by
    intro n
    have h1 := hs (n+L)
    have h2 := hs n
    rw [hL,hc,show n+L+1=n+1+L by omega,hR] at h1
    dsimp [D]
    cases h : e n <;> simp [h] at h1 h2 ⊢ <;> omega
  let E := fun n => D (n+l)-D n
  have hE : ∀ n, E n=4*E (n+1) := by
    intro n
    have h1 := hD (n+l)
    have h2 := hD n
    rw [he] at h1
    dsimp [E]
    rw [show n+1+l=n+l+1 by omega]
    omega
  have hper : ∀ n, D (n+l)=D n := by
    intro n
    let X := fun k => E (n+k)
    have hx : ∀ k, X k=4*X (k+1) := by
      intro k; dsimp [X]; rw [show n+(k+1)=n+k+1 by omega,hE]
    have h0 := reverse_geometric_zero 4 X (by decide) hx
    dsimp [X,E] at h0
    simpa using Int.sub_eq_zero.mp h0
  refine ⟨fun n => D n/4, ?_, ?_⟩
  · intro n; dsimp only; rw [hper]
  · intro n
    have hh := hD n
    have hnext := hD (n+1)
    have hmod : D (n+1)%4=0 := by cases h : e (n+1) <;> simp [h] at hnext <;> omega
    dsimp only
    cases h : e n <;> simp [h] at hh ⊢ <;> omega

/-- Rank increments and constant terms of two-step high-only blocks. -/
def delta (e : Bool) (r : Int) : Int :=
  if e then (if r%4=1 then 14 else 10) else 6

def blockConstant (e : Bool) (r : Int) : Int :=
  if e then (if r%4=1 then 18 else 2) else 0

theorem delta_bounds (e : Bool) (r : Int) : 6≤delta e r ∧ delta e r≤14 ∧ delta e r%4=2 := by
  cases e <;> simp [delta] <;> split <;> decide

theorem rank_mod4 (R : Nat → Int) (e : Nat → Bool)
    (hR : ∀ n,R (n+1)=R n+delta (e n) (R n)) :
    ∀ n k, R (n+k)%4=(R n+2*(k:Int))%4 := by
  intro n k
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := hR (n+k)
    have hd := (delta_bounds (e (n+k)) (R (n+k))).2.2
    rw [show n+(k+1)=n+k+1 by omega,hh]
    omega

theorem highCount_succ (e : Nat → Bool) (n : Nat) :
    highCount e (n+1)=highCount e n+(if e n then 1 else 0) := by
  simp only [highCount,List.range_succ,List.filter_append,List.length_append]
  cases h : e n <;> simp [h]

/-- If rank is odd and one shifts by an odd number of blocks, the two
    exceptional labels are complementary. -/
theorem complementary_delta (e : Bool) (r s : Int)
    (hr : r%2=1) (hs : s%4=(r+2)%4) :
    delta e r+delta e s=12+(if e then 12 else 0) := by
  cases e <;> simp [delta]
  split <;> split <;> omega

/-- Exact full labelled-period drift. The integer m=Delta/4 meets the
    mixed-cycle bounds for both parities of primitive period l. -/
theorem period_drift (R : Nat → Int) (e : Nat → Bool) (l : Nat) (hl : 0<l)
    (hodd : ∀ n,R n%2=1) (he : ∀ n,e (n+l)=e n)
    (hR : ∀ n,R (n+1)=R n+delta (e n) (R n)) :
    let L := if l%2=0 then l else 2*l
    ∃ m : Nat, 0<m ∧
      (∀ n,e (n+L)=e n) ∧
      (∀ n,R (n+L)=R n+4*(m:Int)) ∧
      (∀ n,blockConstant (e (n+L)) (R (n+L))=blockConstant (e n) (R n)) ∧
      (l%2=0 → 2*m≤7*l) ∧ (l%2=1 → m≤3*(l+highCount e l)) := by
  dsimp only
  let L := if l%2=0 then l else 2*l
  change ∃ m : Nat, 0<m ∧ (∀ n,e (n+L)=e n) ∧
    (∀ n,R (n+L)=R n+4*(m:Int)) ∧
    (∀ n,blockConstant (e (n+L)) (R (n+L))=blockConstant (e n) (R n)) ∧
    (l%2=0 → 2*m≤7*l) ∧ (l%2=1 → m≤3*(l+highCount e l))
  have hL : 0<L ∧ L%2=0 := by dsimp [L]; split <;> omega
  have heL : ∀ n,e (n+L)=e n := by
    intro n
    dsimp [L]
    split
    · exact he n
    · rw [show n+2*l=n+l+l by omega,he,he]
  have hmodL : ∀ n,R (n+L)%4=R n%4 := by
    intro n; have hh := rank_mod4 R e hR n L; omega
  have hdeltaL : ∀ n,delta (e (n+L)) (R (n+L))=delta (e n) (R n) := by
    intro n; unfold delta; rw [heL,hmodL]
  have hcL : ∀ n,blockConstant (e (n+L)) (R (n+L))=blockConstant (e n) (R n) := by
    intro n; unfold blockConstant; rw [heL,hmodL]
  have hconst : ∀ n,R (n+L)-R n=R L-R 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show n+1+L=n+L+1 by omega,hR (n+L),hR n,hdeltaL]
      omega
  have hrbound : ∀ n : Nat,R 0+6*(n:Int)≤R n ∧ R n≤R 0+14*(n:Int) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hR n
      have hd := delta_bounds (e n) (R n)
      omega
  have hpos : 0<R L-R 0 := by have hh:=hrbound L; omega
  have hmod : (R L-R 0)%4=0 := by have hh:=hmodL 0; simp at hh; omega
  let m := ((R L-R 0)/4).toNat
  have hm : (4*(m:Int))=R L-R 0 := by
    have h := Int.toNat_of_nonneg (show 0≤(R L-R 0)/4 by omega)
    dsimp [m]
    omega
  refine ⟨m,by omega,heL,?_,hcL,?_,?_⟩
  · intro n; have hh:=hconst n; omega
  · intro h
    have hLeq : L=l := by simp [L,h]
    have hh := hrbound L
    omega
  · intro h
    have hLeq : L=2*l := by simp [L,show l%2≠0 by omega]
    have hpair : ∀ n : Nat,R (n+l)+R n=R l+R 0+12*(n:Int)+12*(highCount e n:Int) := by
      intro n
      induction n with
      | zero => simp [highCount]
      | succ n ih =>
        have hmod' : R (n+l)%4=(R n+2)%4 := by
          have hh := rank_mod4 R e hR n l
          omega
        have hd := complementary_delta (e n) (R n) (R (n+l)) (hodd n) hmod'
        rw [show n+1+l=n+l+1 by omega,hR (n+l),hR n,he,highCount_succ]
        cases h' : e n <;> simp [h'] at hd ⊢ <;> omega
    have hh := hpair l
    rw [show l+l=L by omega] at hh
    omega

/-- A primitive mixed periodic word is impossible for any linearly bounded
    high-only block trajectory with odd rank. All steps are kernel checked. -/
theorem forward_no_mixed (A R : Nat → Int) (e : Nat → Bool) (l : Nat)
    (hl : 2≤l) (hodd : ∀ n,R n%2=1)
    (he : ∀ n,e (n+l)=e n)
    (hlo : ∃ n<l,e n=false) (hhi : ∃ n<l,e n=true)
    (hprim : ∀ i j,i<l → j<l → i≠j → ∃ k,e (i+k)≠e (j+k))
    (hA : LinearBound A)
    (hs : ∀ n,A (n+1)=4*A n-(if e n then 2*R n else 0)+blockConstant (e n) (R n))
    (hR : ∀ n,R (n+1)=R n+delta (e n) (R n)) : False := by
  let L := if l%2=0 then l else 2*l
  obtain ⟨m,hm,hL,hdrift,hc,hEven,hOdd⟩ := period_drift R e l (by omega) hodd he hR
  obtain ⟨p,hp,hrec⟩ := periodic_difference_forward A R e (fun n => blockConstant (e n) (R n)) L l m
    (by omega) hs hdrift hL hc he hA
  exact no_mixed_cycle p e m l hm hl hp he hlo hhi hprim hrec hEven hOdd

#print axioms periodic_difference_forward
#print axioms periodic_difference_backward
#print axioms period_drift
#print axioms forward_no_mixed

end BB429.PeriodicHigh
