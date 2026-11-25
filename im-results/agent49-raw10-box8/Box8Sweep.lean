import BlockMacro

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49Box8Sweep
open BB6BlockFAR

/-- F0 is 0LA for false, 0RD for true. F1 is unassigned. -/
def machine (mode : Bool) : Table := fun q b =>
  match q.val,b with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨false,true,3⟩
  | 1,false => some ⟨true,false,2⟩
  | 1,true => some ⟨true,false,1⟩
  | 2,false => some ⟨false,false,4⟩
  | 2,true => some ⟨true,true,0⟩
  | 3,false => some ⟨false,false,2⟩
  | 3,true => some ⟨false,true,0⟩
  | 4,false => some ⟨true,false,5⟩
  | 4,true => some ⟨true,false,3⟩
  | 5,false => if mode then some ⟨false,true,3⟩ else some ⟨false,false,0⟩
  | _,_ => none

abbrev Z := cons false
abbrev I := cons true
abbrev L (r : Ray) := Z (Z (I r))
abbrev R (r : Ray) := I (Z (Z r))

def ls : Nat → Ray → Ray
  | 0,r => r
  | n+1,r => L (ls n r)
def rs : Nat → Ray → Ray
  | 0,r => r
  | n+1,r => R (rs n r)

theorem ls_push (n : Nat) (r : Ray) : ls n (L r) = ls (n+1) r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ls, ih]
theorem rs_push (n : Nat) (r : Ray) : rs n (R r) = rs (n+1) r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rs, ih]
theorem shift_pattern (n : Nat) (r : Ray) : rs n (I r) = I (ls n r) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rs,ls,ih]

def A (l r : Ray) : Prim := ⟨0,l,r⟩
def DL (l r : Ray) : Prim := ⟨3,tail l,cons (l 0) r⟩
def F (n : Nat) : Prim := ⟨5,blankRay,Z (rs n (I blankRay))⟩

theorem A_triplet (mode : Bool) (l r : Ray) :
    run (machine mode) 5 (A l (L r)) = some (A (L l) r) := by rfl
theorem A_boundary (mode : Bool) (l : Ray) :
    run (machine mode) 7 (A l blankRay) = some (DL l (I blankRay)) := by
  change some (DL l (I (Z (Z blankRay)))) = _
  simp only [blank_cons]
theorem D_triplet (mode : Bool) (l r : Ray) :
    run (machine mode) 3 (DL (L l) r) = some (DL l (R r)) := by rfl
theorem D_boundary (mode : Bool) (r : Ray) :
    run (machine mode) 3 (DL blankRay r) = some ⟨5,blankRay,Z (R r)⟩ := by rfl

theorem A_sweep (mode : Bool) (n : Nat) (l r : Ray) :
    run (machine mode) (5*n) (A l (ls n r)) = some (A (ls n l) r) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [show 5*(n+1)=5+5*n by omega,run_add]
    change (run (machine mode) 5 (A l (L (ls n r)))).bind _ = _
    rw [A_triplet]
    change run (machine mode) (5*n) (A (L l) (ls n r)) = _
    rw [ih,ls_push]

theorem D_sweep (mode : Bool) (n : Nat) (l r : Ray) :
    run (machine mode) (3*n) (DL (ls n l) r) = some (DL l (rs n r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega,run_add]
    change (run (machine mode) 3 (DL (L (ls n l)) r)).bind _ = _
    rw [D_triplet]
    change run (machine mode) (3*n) (DL (ls n l) (R r)) = _
    rw [ih,rs_push]

theorem right_left (mode : Bool) (n : Nat) :
    run (machine mode) (5*n+7+3*n+3) (A blankRay (ls n blankRay)) = some (F (n+1)) := by
  rw [run_add,run_add,run_add,A_sweep]
  change ((run (machine mode) 7 (A (ls n blankRay) blankRay)).bind (run (machine mode) (3*n))).bind (run (machine mode) 3) = _
  rw [A_boundary]
  change (run (machine mode) (3*n) (DL (ls n blankRay) (I blankRay))).bind (run (machine mode) 3) = _
  rw [D_sweep]
  exact D_boundary mode (rs n (I blankRay))

theorem F_start_left (n : Nat) :
    run (machine false) 1 (F n) = some (A blankRay (ls (n+1) blankRay)) := by
  unfold F
  rw [shift_pattern]
  rfl

theorem F_start_right (n : Nat) :
    run (machine true) 2 (F n) = some (A blankRay (ls n blankRay)) := by
  unfold F
  rw [shift_pattern]
  change some (A (Z (Z blankRay)) (ls n blankRay)) = _
  simp only [blank_cons]

theorem return_left (n : Nat) : run (machine false) (8*n+19) (F n) = some (F (n+2)) := by
  rw [show 8*n+19=1+(5*(n+1)+7+3*(n+1)+3) by omega,run_add,F_start_left]
  exact right_left false (n+1)

theorem return_right (n : Nat) : run (machine true) (8*n+12) (F n) = some (F (n+1)) := by
  rw [show 8*n+12=2+(5*n+7+3*n+3) by omega,run_add,F_start_right]
  exact right_left true n

theorem initial (mode : Bool) : run (machine mode) 10 primBlank = some (F 1) := by
  change some (⟨5,blankRay,Z (R (I (Z (Z blankRay))))⟩ : Prim) = _
  simp only [blank_cons]
  rfl

theorem grows (mode : Bool) (n : Nat) : ∃ t k, 0 < t ∧ run (machine mode) t (F n) = some (F k) := by
  cases mode
  · exact ⟨8*n+19,n+2,by omega,return_left n⟩
  · exact ⟨8*n+12,n+1,by omega,return_right n⟩

theorem live (mode : Bool) (t n : Nat) : ∃ c, run (machine mode) t (F n) = some c := by
  induction t using Nat.strongRecOn generalizing n with
  | ind t ih =>
    obtain ⟨s,k,hpos,hs⟩ := grows mode n
    by_cases h : s ≤ t
    · obtain ⟨c,hc⟩ := ih (t-s) (by omega) k
      exact ⟨c, by rw [show t=s+(t-s) by omega,run_add,hs]; exact hc⟩
    · rw [show s=t+(s-t) by omega,run_add] at hs
      cases ht : run (machine mode) t (F n) with
      | none => simp [ht] at hs
      | some c => exact ⟨c,rfl⟩

theorem never (mode : Bool) (t : Nat) : ∃ c, run (machine mode) t primBlank = some c := by
  by_cases h : 10 ≤ t
  · obtain ⟨c,hc⟩ := live mode (t-10) 1
    exact ⟨c, by rw [show t=10+(t-10) by omega,run_add,initial]; exact hc⟩
  · have hs := initial mode
    rw [show 10=t+(10-t) by omega,run_add] at hs
    cases ht : run (machine mode) t primBlank with
    | none => simp [ht] at hs
    | some c => exact ⟨c,rfl⟩

#print axioms return_left
#print axioms return_right
#print axioms never
end BB6.Agent49Box8Sweep
