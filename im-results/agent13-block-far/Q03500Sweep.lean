import BlockMacro

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Q03500
open BB6BlockFAR

/-- Original (unreflected) q0 offset 3500, with C0 unassigned. -/
def machine : Table := fun q b =>
  match q.val,b with
  | 0,false => some ⟨true,true,1⟩
  | 0,true  => some ⟨false,true,2⟩
  | 1,false => some ⟨true,false,2⟩
  | 1,true  => some ⟨true,true,3⟩
  | 2,false => none
  | 2,true  => some ⟨true,true,1⟩
  | 3,false => some ⟨false,false,3⟩
  | 3,true  => some ⟨false,true,4⟩
  | 4,false => some ⟨true,false,4⟩
  | 4,true  => some ⟨false,false,5⟩
  | 5,false => some ⟨true,true,0⟩
  | 5,true  => some ⟨true,false,5⟩
  | _,_ => none

abbrev Z := cons false
abbrev I := cons true

def O : Nat → Ray → Ray
  | 0,r => r
  | n+1,r => I (O n r)

@[simp] theorem O_zero (r : Ray) : O 0 r = r := rfl
@[simp] theorem O_succ (n : Nat) (r : Ray) : O (n+1) r = I (O n r) := rfl

theorem O_add (a b : Nat) (r : Ray) : O (a+b) r = O a (O b r) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add, O_succ, ih, O_succ]

theorem O_push (n : Nat) (r : Ray) : O n (I r) = O (n+1) r := by
  rw [O_add n 1]; rfl

def B (l r : Ray) : Prim := ⟨1,l,r⟩
def F (l r : Ray) : Prim := ⟨5,l,r⟩
def FL (l r : Ray) : Prim := F (tail l) (cons (l 0) r)

/-- Arbitrary finite, fully defined execution; no claim about maximal time. -/
def Reaches (c d : Prim) : Prop := ∃ t, run machine t c = some d

theorem Reaches.refl (c : Prim) : Reaches c c := ⟨0,rfl⟩
theorem Reaches.trans {c d e : Prim} (h : Reaches c d) (g : Reaches d e) : Reaches c e := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨b,hb⟩ := g
  exact ⟨a+b, by rw [run_add,ha]; exact hb⟩

-- Local primitives. Arbitrary exterior rays ensure these are genuine identities.
theorem B_triplet (l r : Ray) : run machine 5 (B l (I (I (I r)))) = some (B (I (I (I l))) r) := by rfl

theorem F_open (l r : Ray) : run machine 3 (F l (Z (I (I r)))) = some (B (I (Z (I l))) r) := by rfl

theorem F_adjacent (l r : Ray) : run machine 2 (F l (Z (Z r))) = some (B (I (I l)) r) := by rfl

theorem B_D0 (l r : Ray) : run machine 6 (B (I l) (I (Z r))) = some (FL l (Z (I (I r)))) := by rfl

theorem B_E0 (l : Ray) : run machine 5 (B l (I (I blankRay))) = some (FL l (Z (I (I blankRay)))) := by
  change some (FL l (Z (I (I (tail blankRay))))) = _
  rfl

theorem B_hole (l : Ray) : run machine 7 (B (I l) (Z (I (I blankRay)))) = some (B (I (I (I (I l)))) blankRay) := by rfl

theorem B_boundary (l : Ray) : run machine 8 (B (I l) blankRay) = some (FL l (Z (I (I blankRay)))) := by rfl

theorem FL_one (l r : Ray) : run machine 1 (FL (I l) r) = some (FL l (I r)) := by rfl

/-- Right sweep through n groups of three ones. -/
theorem B_sweep (n : Nat) (l r : Ray) : run machine (5*n) (B l (O (3*n) r)) = some (B (O (3*n) l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 5*(n+1)=5+5*n by omega,run_add,show 3*(n+1)=3+3*n by omega,O_add 3 (3*n) r]
    change (run machine 5 (B l (I (I (I (O (3*n) r)))))).bind _ = _
    rw [B_triplet]
    change run machine (5*n) (B (I (I (I l))) (O (3*n) r)) = _
    rw [ih, O_add 3 (3*n) l]
    congr 2
    change O (3*n) (O 3 l) = O 3 (O (3*n) l)
    rw [← O_add (3*n) 3 l, ← O_add 3 (3*n) l]
    congr 1
    omega

/-- F moves left over exactly n ones and stops on a prescribed zero. -/
theorem F_sweep (n : Nat) (l r : Ray) : run machine n (FL (O n (Z l)) r) = some (F l (Z (O n r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=1+n by omega,run_add]
    rw [show 1+n=n+1 by omega]
    change (run machine 1 (FL (I (O n (Z l))) r)).bind _ = _
    rw [FL_one]
    change run machine n (FL (O n (Z l)) (I r)) = _
    rw [ih,O_push]

/-- F scanning the left of two zeroes separated by `a` ones. The left
    prefix contains `p` ones; the suffix contains `s` ones. -/
def sandwich (p a s : Nat) : Prim :=
  F (O p blankRay) (Z (O a (Z (O s blankRay))))

/-- B at the blank immediately to the right of a solid block of n ones. -/
def solid (n : Nat) : Prim := B (O n blankRay) blankRay

/-- B at the blank after a run of n+1 ones, preceded by a zero and p ones. -/
theorem boundary_to_sandwich (p n : Nat) :
    run machine (8+n) (B (O (n+1) (Z (O p blankRay))) blankRay) = some (sandwich p n 2) := by
  rw [run_add,O_succ,B_boundary]
  change run machine n (FL (O n (Z (O p blankRay))) (Z (I (I blankRay)))) = _
  rw [F_sweep]
  rfl

/-- One sweep when the separating run consists of 3(m+1) ones. -/
theorem sandwich_reduce (p m s : Nat) : Reaches (sandwich p (3*(m+1)) s) (sandwich (p+1) (3*m) (s+2)) := by
  unfold sandwich
  rw [show 3*(m+1)=2+(3*m+1) by omega,O_add 2 (3*m+1)]
  apply Reaches.trans (d := B (I (Z (I (O p blankRay)))) (O (3*m+1) (Z (O s blankRay))))
  · exact ⟨3,F_open _ _⟩
  rw [O_add (3*m) 1]
  apply Reaches.trans (d := B (O (3*m) (I (Z (I (O p blankRay))))) (I (Z (O s blankRay))))
  · exact ⟨5*m,B_sweep m _ _⟩
  have hl : O (3*m) (I (Z (I (O p blankRay)))) = I (O (3*m) (Z (I (O p blankRay)))) := by rw [O_push,O_succ]
  rw [hl]
  apply Reaches.trans (d := FL (O (3*m) (Z (I (O p blankRay)))) (Z (I (I (O s blankRay)))))
  · exact ⟨6,B_D0 _ _⟩
  refine ⟨3*m,?_⟩
  rw [F_sweep]
  rfl

/-- Iterate the reduction down to adjacent zeroes. -/
theorem sandwich_adjacent (p m s : Nat) : Reaches (sandwich p (3*m) s) (sandwich (p+m) 0 (s+2*m)) := by
  induction m generalizing p s with
  | zero => simp; exact Reaches.refl _
  | succ m ih =>
    apply Reaches.trans (sandwich_reduce p m s)
    have h := ih (p+1) (s+2)
    rw [show p+1+m=p+(m+1) by omega,show s+2+2*m=s+2*(m+1) by omega] at h
    exact h

/-- If the gap has 3m+2 ones and the final suffix has exactly two ones,
    the right-hand zero is crossed and a new right boundary is swept. -/
theorem sandwich_cross (p m : Nat) :
    Reaches (sandwich p (3*m+2) 2) (sandwich (p+1) (3*m+3) 2) := by
  unfold sandwich
  rw [show 3*m+2=2+3*m by omega,O_add 2 (3*m)]
  apply Reaches.trans (d := B (I (Z (I (O p blankRay)))) (O (3*m) (Z (O 2 blankRay))))
  · exact ⟨3,F_open _ _⟩
  apply Reaches.trans (d := B (O (3*m) (I (Z (I (O p blankRay))))) (Z (O 2 blankRay)))
  · exact ⟨5*m,B_sweep m _ _⟩
  have hl : O (3*m) (I (Z (I (O p blankRay)))) = I (O (3*m) (Z (I (O p blankRay)))) := by rw [O_push,O_succ]
  rw [hl]
  apply Reaches.trans (d := B (I (I (I (I (O (3*m) (Z (I (O p blankRay)))))))) blankRay)
  · exact ⟨7,B_hole _⟩
  change Reaches (B (O 4 (O (3*m) (Z (O (p+1) blankRay)))) blankRay) _
  rw [← O_add,show 4+3*m=3*m+3+1 by omega]
  exact ⟨8+(3*m+3),boundary_to_sandwich (p+1) (3*m+3)⟩

/-- Filling adjacent zeroes and sweeping a multiple of three ones returns
    directly to a solid block. -/
theorem adjacent_solid (p m : Nat) : Reaches (sandwich p 0 (3*m)) (solid (p+2+3*m)) := by
  unfold sandwich solid
  apply Reaches.trans (d := B (O 2 (O p blankRay)) (O (3*m) blankRay))
  · exact ⟨2,F_adjacent _ _⟩
  refine ⟨5*m,?_⟩
  rw [B_sweep,← O_add,← O_add,show 3*m+2+p=p+2+3*m by omega]

/-- Adjacent zeroes, suffix 1 modulo 3: the D0 detour creates a new
    right-hand zero, followed by the sweep to the blank at the far left. -/
theorem adjacent_one (p m : Nat) : Reaches (sandwich p 0 (3*m+1)) (sandwich 0 (p+3*m+1) 2) := by
  unfold sandwich
  rw [O_add (3*m) 1]
  apply Reaches.trans (d := B (O 2 (O p blankRay)) (O (3*m) (I blankRay)))
  · exact ⟨2,F_adjacent _ _⟩
  apply Reaches.trans (d := B (O (3*m) (O 2 (O p blankRay))) (I blankRay))
  · exact ⟨5*m,B_sweep m _ _⟩
  rw [← O_add,← O_add,show 3*m+2+p=(p+3*m+1)+1 by omega,O_succ]
  apply Reaches.trans (d := FL (O (p+3*m+1) blankRay) (Z (I (I blankRay))))
  · refine ⟨6,?_⟩
    simpa only [blank_cons] using B_D0 (O (p+3*m+1) blankRay) blankRay
  refine ⟨p+3*m+1,?_⟩
  have h := F_sweep (p+3*m+1) blankRay (Z (I (I blankRay)))
  simp only [blank_cons] at h
  exact h

/-- Adjacent zeroes, suffix 2 modulo 3: the E0 detour has the same
    net gap update, with a different bounded primitive prefix. -/
theorem adjacent_two (p m : Nat) : Reaches (sandwich p 0 (3*m+2)) (sandwich 0 (p+3*m+2) 2) := by
  unfold sandwich
  rw [O_add (3*m) 2]
  apply Reaches.trans (d := B (O 2 (O p blankRay)) (O (3*m) (I (I blankRay))))
  · exact ⟨2,F_adjacent _ _⟩
  apply Reaches.trans (d := B (O (3*m) (O 2 (O p blankRay))) (I (I blankRay)))
  · exact ⟨5*m,B_sweep m _ _⟩
  rw [← O_add,← O_add,show 3*m+2+p=p+3*m+2 by omega]
  apply Reaches.trans (d := FL (O (p+3*m+2) blankRay) (Z (I (I blankRay))))
  · exact ⟨5,B_E0 _⟩
  refine ⟨p+3*m+2,?_⟩
  have h := F_sweep (p+3*m+2) blankRay (Z (I (I blankRay)))
  simp only [blank_cons] at h
  exact h

/-- The seven stages after the initial right-boundary detour. -/
theorem full_sweep (k : Nat) : Reaches (sandwich 0 (9*k) 2) (solid (9*(k+1)+1)) := by
  have h1 := sandwich_adjacent 0 (3*k) 2
  have h2 := adjacent_two (3*k) (2*k)
  have h3 := sandwich_cross 0 (3*k)
  have h4 := sandwich_adjacent 1 (3*k+1) 2
  have h5 := adjacent_one (3*k+2) (2*k+1)
  have h6 := sandwich_adjacent 0 (3*k+2) 2
  have h7 := adjacent_solid (3*k+2) (2*k+2)
  rw [show 3*(3*k)=9*k by omega,show 0+3*k=3*k by omega,show 2+2*(3*k)=6*k+2 by omega] at h1
  rw [show 3*(2*k)+2=6*k+2 by omega,show 3*k+3*(2*k)+2=9*k+2 by omega] at h2
  rw [show 3*(3*k)+2=9*k+2 by omega,show 0+1=1 by omega,show 3*(3*k)+3=9*k+3 by omega] at h3
  rw [show 3*(3*k+1)=9*k+3 by omega,show 1+(3*k+1)=3*k+2 by omega,show 2+2*(3*k+1)=6*k+4 by omega] at h4
  rw [show 3*(2*k+1)+1=6*k+4 by omega,show 3*k+2+3*(2*k+1)+1=9*k+6 by omega] at h5
  rw [show 3*(3*k+2)=9*k+6 by omega,show 0+(3*k+2)=3*k+2 by omega,show 2+2*(3*k+2)=6*k+6 by omega] at h6
  rw [show 3*(2*k+2)=6*k+6 by omega,show 3*k+2+2+(6*k+6)=9*(k+1)+1 by omega] at h7
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

/-- Every main return increases the solid block by nine, in a positive
    number of primitive steps. This is an unbounded symbolic certificate. -/
theorem solid_grows (k : Nat) : ∃ t, 0 < t ∧
    run machine t (solid (9*k+1)) = some (solid (9*(k+1)+1)) := by
  have h := boundary_to_sandwich 0 (9*k)
  simp only [O_zero,blank_cons] at h
  obtain ⟨t,ht⟩ := full_sweep k
  refine ⟨8+9*k+t,by omega,?_⟩
  rw [run_add,show solid (9*k+1)=B (O (9*k+1) blankRay) blankRay from rfl,h]
  exact ht

theorem solid_live (n k : Nat) : ∃ c, run machine n (solid (9*k+1)) = some c := by
  induction n using Nat.strongRecOn generalizing k with
  | ind n ih =>
    obtain ⟨t,hpos,ht⟩ := solid_grows k
    by_cases hle : t ≤ n
    · obtain ⟨c,hc⟩ := ih (n-t) (by omega) (k+1)
      refine ⟨c,?_⟩
      rw [show n=t+(n-t) by omega,run_add,ht]
      exact hc
    · rw [show t=n+(t-n) by omega,run_add] at ht
      cases hh : run machine n (solid (9*k+1)) with
      | none => simp [hh] at ht
      | some c => exact ⟨c,rfl⟩

theorem blank_start : run machine 1 primBlank = some (solid 1) := by rfl
theorem never : ∀ n, ∃ c, run machine n primBlank = some c := by
  intro n
  cases n with
  | zero => exact ⟨primBlank,rfl⟩
  | succ n =>
    obtain ⟨c,hc⟩ := solid_live n 0
    refine ⟨c,?_⟩
    rw [show n+1=1+n by omega,run_add,blank_start]
    exact hc

#print axioms solid_grows
#print axioms never
end BB6Q03500
