import SparseZipper

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent50AlternatingSweep
open BB6Coverage Agent50Zipper

/-- Two previously open depth-nine residuals (F0=0LB or F0=1LD).
    A1 and E0 are unconstrained and never queried. -/
def table (w : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some (if w then ⟨true,false,3⟩ else ⟨false,false,1⟩))
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def P : List Bool := [false,true]
def Q : List Bool := [true,false]
def K : List Bool := [true,true]
def rep (p : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => p ++ rep p n

theorem rep_snoc (p : List Bool) (n : Nat) : rep p n ++ p = p ++ rep p n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih]

def family (n : Nat) (h : Int) : Z := ⟨0,h,[],rep P n⟩

theorem first0 (w : Bool) : zrun (table w) 9 (family 0 0) = some (family 2 (-1)) := by
  cases w <;> rfl

theorem first (w : Bool) (h : Int) : zrun (table w) 9 (family 0 h) = some (family 2 (h-1)) := by
  have H := zrun_shift (table w) h 9 (family 0 0)
  rw [first0] at H
  simpa [family,shift,show -1+h=h-1 by omega] using H

theorem prelude0 (w : Bool) (R : List Bool) :
    zrun (table w) 2 ⟨0,0,[],P++R⟩ = some ⟨2,2,true::K,R⟩ := by rfl

theorem prelude (w : Bool) (h : Int) (R : List Bool) :
    zrun (table w) 2 ⟨0,h,[],P++R⟩ = some ⟨2,h+2,true::K,R⟩ := by
  have H := zrun_shift (table w) h 2 ⟨0,0,[],P++R⟩
  rw [prelude0] at H
  simpa [shift,Int.add_comm] using H

theorem rightOne0 (w : Bool) (L R : List Bool) :
    zrun (table w) 2 ⟨2,0,true::L,P++R⟩ = some ⟨2,2,true::(Q++L),R⟩ := by rfl

theorem rightOne (w : Bool) (h : Int) (L R : List Bool) :
    zrun (table w) 2 ⟨2,h,true::L,P++R⟩ = some ⟨2,h+2,true::(Q++L),R⟩ := by
  have H := zrun_shift (table w) h 2 ⟨2,0,true::L,P++R⟩
  rw [rightOne0] at H
  simpa [shift,Int.add_comm] using H

theorem rightSweep (w : Bool) (n : Nat) (h : Int) (L R : List Bool) :
    zrun (table w) (2*n) ⟨2,h,true::L,rep P n++R⟩ =
      some ⟨2,h+2*(n:Int),true::(rep Q n++L),R⟩ := by
  induction n generalizing h L with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (rightOne w h L (rep P n++R)) (ih (h+2) (Q++L))
    rw [show 2*(n+1)=2+2*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Q n) Q L,rep_snoc Q n,
      Int.natCast_succ,show h+2+2*(n:Int)=h+2*((n:Int)+1) by omega] using H

theorem turn0 (w : Bool) (L : List Bool) :
    zrun (table w) 5 ⟨2,0,true::L,[]⟩ = some ⟨3,1,Q++L,K⟩ := by rfl

theorem turn (w : Bool) (h : Int) (L : List Bool) :
    zrun (table w) 5 ⟨2,h,true::L,[]⟩ = some ⟨3,h+1,Q++L,K⟩ := by
  have H := zrun_shift (table w) h 5 ⟨2,0,true::L,[]⟩
  rw [turn0] at H
  simpa [shift,Int.add_comm] using H

-- 1LD: D1-E1-B1-F0 consumes one 10 block and preserves the 11 cap.
theorem leftD0 (L R : List Bool) :
    zrun (table true) 4 ⟨3,0,Q++L,K++R⟩ = some ⟨3,-2,L,K++P++R⟩ := by rfl

theorem leftD (h : Int) (L R : List Bool) :
    zrun (table true) 4 ⟨3,h,Q++L,K++R⟩ = some ⟨3,h-2,L,K++P++R⟩ := by
  have H := zrun_shift (table true) h 4 ⟨3,0,Q++L,K++R⟩
  rw [leftD0] at H
  simpa [shift,show -2+h=h-2 by omega] using H

theorem leftDSweep (n : Nat) (h : Int) (L R : List Bool) :
    zrun (table true) (4*n) ⟨3,h,rep Q n++L,K++R⟩ =
      some ⟨3,h-2*(n:Int),L,K++rep P n++R⟩ := by
  induction n generalizing h R with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (leftD h (rep Q n++L) R) (ih (h-2) (P++R))
    rw [show 4*(n+1)=4+4*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep P n) P R,rep_snoc P n,
      Int.natCast_succ,show h-2-2*(n:Int)=h-2*((n:Int)+1) by omega] using H

theorem finishD0 (R : List Bool) :
    zrun (table true) 4 ⟨3,0,K,K++R⟩ = some ⟨0,-2,[],P++P++R⟩ := by rfl

theorem finishD (h : Int) (R : List Bool) :
    zrun (table true) 4 ⟨3,h,K,K++R⟩ = some ⟨0,h-2,[],P++P++R⟩ := by
  have H := zrun_shift (table true) h 4 ⟨3,0,K,K++R⟩
  rw [finishD0] at H
  simpa [shift,show -2+h=h-2 by omega] using H

-- 0LB: the first left block enters B; subsequent blocks take two moves.
theorem leftFirst0 (L R : List Bool) :
    zrun (table false) 4 ⟨3,0,Q++L,K++R⟩ = some ⟨1,-2,L,P++P++R⟩ := by rfl

theorem leftFirst (h : Int) (L R : List Bool) :
    zrun (table false) 4 ⟨3,h,Q++L,K++R⟩ = some ⟨1,h-2,L,P++P++R⟩ := by
  have H := zrun_shift (table false) h 4 ⟨3,0,Q++L,K++R⟩
  rw [leftFirst0] at H
  simpa [shift,show -2+h=h-2 by omega] using H

theorem leftB0 (L R : List Bool) :
    zrun (table false) 2 ⟨1,0,Q++L,R⟩ = some ⟨1,-2,L,P++R⟩ := by rfl

theorem leftB (h : Int) (L R : List Bool) :
    zrun (table false) 2 ⟨1,h,Q++L,R⟩ = some ⟨1,h-2,L,P++R⟩ := by
  have H := zrun_shift (table false) h 2 ⟨1,0,Q++L,R⟩
  rw [leftB0] at H
  simpa [shift,show -2+h=h-2 by omega] using H

theorem leftBSweep (n : Nat) (h : Int) (L R : List Bool) :
    zrun (table false) (2*n) ⟨1,h,rep Q n++L,R⟩ =
      some ⟨1,h-2*(n:Int),L,rep P n++R⟩ := by
  induction n generalizing h R with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (leftB h (rep Q n++L) R) (ih (h-2) (P++R))
    rw [show 2*(n+1)=2+2*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep P n) P R,rep_snoc P n,
      Int.natCast_succ,show h-2-2*(n:Int)=h-2*((n:Int)+1) by omega] using H

theorem finishB0 (R : List Bool) :
    zrun (table false) 2 ⟨1,0,K,R⟩ = some ⟨0,-2,[],P++R⟩ := by rfl

theorem finishB (h : Int) (R : List Bool) :
    zrun (table false) 2 ⟨1,h,K,R⟩ = some ⟨0,h-2,[],P++R⟩ := by
  have H := zrun_shift (table false) h 2 ⟨1,0,K,R⟩
  rw [finishB0] at H
  simpa [shift,show -2+h=h-2 by omega] using H

theorem growthD (n : Nat) (h : Int) :
    zrun (table true) (15+6*n) (family (n+1) h) = some (family (n+3) (h-1)) := by
  have h1 := prelude true h (rep P n)
  have h2 := rightSweep true n (h+2) K []
  simp only [List.append_nil] at h2
  have h3 := turn true (h+2+2*(n:Int)) (rep Q n++K)
  have h4 := leftDSweep (n+1) (h+2+2*(n:Int)+1) K []
  simp only [rep,List.append_assoc,List.append_nil] at h4
  have h5 := finishD (h+2+2*(n:Int)+1-2*((n+1:Nat):Int)) (rep P (n+1))
  have H := join (join h1 h2) h3
  have H' := join (join H h4) h5
  simpa only [family,rep,List.append_assoc,show 2+2*n+5+4*(n+1)+4=15+6*n by omega,
    show h+2+2*(n:Int)+1-2*((n+1:Nat):Int)-2=h-1 by omega] using H'

theorem growthB (n : Nat) (h : Int) :
    zrun (table false) (13+4*n) (family (n+1) h) = some (family (n+3) (h-1)) := by
  have h1 := prelude false h (rep P n)
  have h2 := rightSweep false n (h+2) K []
  simp only [List.append_nil] at h2
  have h3 := turn false (h+2+2*(n:Int)) (rep Q n++K)
  have h4 := leftFirst (h+2+2*(n:Int)+1) (rep Q n++K) []
  simp only [List.append_nil] at h4
  have h5 := leftBSweep n (h+2+2*(n:Int)+1-2) K (P++P)
  have h6 := finishB (h+2+2*(n:Int)+1-2-2*(n:Int)) (rep P n++(P++P))
  have H := join (join (join (join (join h1 h2) h3) h4) h5) h6
  have hw : P++(rep P n++(P++P))=rep P (n+3) := by
    rw [← List.append_assoc (rep P n) P P,rep_snoc P n]
    rw [List.append_assoc P (rep P n) P,rep_snoc P n]
    simp only [rep]
  simpa only [family,rep,List.append_assoc,hw,show 2+2*n+5+4+2*n+2=13+4*n by omega,
    show h+2+2*(n:Int)+1-2-2*(n:Int)-2=h-1 by omega] using H

theorem grows (w : Bool) (n : Nat) (h : Int) :
    ∃ t, 0 < t ∧ zrun (table w) t (family n h) = some (family (n+2) (h-1)) := by
  cases n with
  | zero => exact ⟨9,by decide,first w h⟩
  | succ n =>
    cases w with
    | false => exact ⟨13+4*n,by omega,growthB n h⟩
    | true => exact ⟨15+6*n,by omega,growthD n h⟩

theorem arbitraryRun (w : Bool) (n : Nat) : ∃ t k h, n ≤ t ∧
    zrun (table w) t (family 0 0) = some (family k h) := by
  induction n with
  | zero => exact ⟨0,0,0,by omega,rfl⟩
  | succ n ih =>
    obtain ⟨t,k,h,ht,hr⟩ := ih
    obtain ⟨u,hu,hg⟩ := grows w k h
    exact ⟨t+u,k+2,h-1,by omega,join hr hg⟩

theorem initial_embed : embed (family 0 0) = blank := by
  unfold embed family blank
  congr 1
  funext x
  simp [atCell,rep]

theorem never (w : Bool) (m : Machine) (hm : compatible (table w) m) : NeverHalts m := by
  intro n
  obtain ⟨t,k,h,ht,hr⟩ := arbitraryRun w n
  have H := zrun_sound (table w) m hm t _ _ hr
  rw [initial_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some c => rfl

#print axioms growthB
#print axioms growthD
#print axioms never
end BB6Coverage.Agent50AlternatingSweep
