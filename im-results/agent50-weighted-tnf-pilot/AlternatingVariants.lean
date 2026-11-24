import AlternatingResidualSweep

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent50AlternatingVariants
open BB6Coverage Agent50Zipper Agent50AlternatingSweep

def tab (f : Move) (a e : Option Move) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,true => a.map some
  | 4,false => e.map some
  | 5,false => some (some f)
  | _,_ => table true s

structure Spec where
  f : Move
  a : Option Move
  e : Option Move
  q : Fin 6
  cap : List Bool
  firstCost : Nat
  loopCost : Nat
  finishCost : Nat

def spec : Fin 17 → Spec := fun i => match i.val with
  | 0 => ⟨⟨false,false,0⟩,(some ⟨false,false,2⟩),none,0,[false,true,false,true],4,8,8⟩
  | 1 => ⟨⟨false,false,0⟩,(some ⟨true,false,3⟩),none,0,[false,true,false,true],4,6,6⟩
  | 2 => ⟨⟨false,false,0⟩,(some ⟨true,true,3⟩),none,0,[false,true,false,true],4,12,12⟩
  | 3 => ⟨⟨false,false,0⟩,(some ⟨true,false,5⟩),none,0,[false,true,false,true],4,4,4⟩
  | 4 => ⟨⟨false,true,0⟩,(some ⟨false,false,2⟩),none,3,[true,true,false,true],8,16,12⟩
  | 5 => ⟨⟨false,true,0⟩,(some ⟨true,false,3⟩),none,3,[true,true,false,true],6,12,10⟩
  | 6 => ⟨⟨true,false,0⟩,(some ⟨true,true,4⟩),none,0,[true,true,false,true],4,8,8⟩
  | 7 => ⟨⟨true,true,0⟩,(some ⟨true,true,3⟩),none,0,[false,true,false,true],10,24,18⟩
  | 8 => ⟨⟨true,true,0⟩,(some ⟨true,false,4⟩),none,1,[false,true,false,true],6,8,6⟩
  | 9 => ⟨⟨true,true,0⟩,(some ⟨true,false,5⟩),none,0,[false,true,false,true],6,8,6⟩
  | 10 => ⟨⟨true,true,1⟩,(some ⟨false,false,2⟩),none,0,[false,true,false,true],6,10,8⟩
  | 11 => ⟨⟨true,true,1⟩,(some ⟨true,false,3⟩),none,0,[false,true,false,true],6,8,6⟩
  | 12 => ⟨⟨true,true,1⟩,(some ⟨true,true,3⟩),none,0,[false,true,false,true],6,16,14⟩
  | 13 => ⟨⟨true,true,1⟩,(some ⟨true,false,5⟩),none,0,[false,true,false,true],6,8,6⟩
  | 14 => ⟨⟨false,false,3⟩,none,(some ⟨false,false,1⟩),3,[false,true,false,true],4,8,8⟩
  | 15 => ⟨⟨false,false,3⟩,none,(some ⟨true,false,3⟩),3,[false,true,false,true],4,12,12⟩
  | _ => ⟨⟨true,true,5⟩,(some ⟨false,true,3⟩),none,3,[true,true,false,true],8,16,12⟩

def vt (i : Fin 17) : PartialMachine := tab (spec i).f (spec i).a (spec i).e

/-- Symbolic tape-tail atoms; the arbitrary lists are never read. -/
theorem atoms (i : Fin 17) (L R : List Bool) :
    zrun (vt i) (spec i).firstCost ⟨3,0,Q++L,K++R⟩ = some ⟨(spec i).q,-2,L,(spec i).cap++R⟩ ∧
    zrun (vt i) (spec i).loopCost ⟨(spec i).q,0,Q++Q++L,(spec i).cap++R⟩ = some ⟨(spec i).q,-4,L,(spec i).cap++P++P++R⟩ ∧
    zrun (vt i) (spec i).finishCost ⟨(spec i).q,0,Q++K,(spec i).cap++R⟩ = some ⟨0,-4,[],P++P++P++P++R⟩ := by
  rcases i with ⟨i,hi⟩
  have H : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 := by omega
  rcases H with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> exact ⟨rfl,rfl,rfl⟩

theorem first0 (i : Fin 17) : zrun (vt i) 9 (family 0 0) = some (family 2 (-1)) := by
  rfl

theorem first (i : Fin 17) (h : Int) : zrun (vt i) 9 (family 0 h) = some (family 2 (h-1)) := by
  have H := zrun_shift (vt i) h 9 (family 0 0)
  rw [first0] at H
  simpa [family,shift,show -1+h=h-1 by omega] using H

theorem prelude0 (i : Fin 17) (R : List Bool) :
    zrun (vt i) 2 ⟨0,0,[],P++R⟩ = some ⟨2,2,true::K,R⟩ := by rfl

theorem prelude (i : Fin 17) (h : Int) (R : List Bool) :
    zrun (vt i) 2 ⟨0,h,[],P++R⟩ = some ⟨2,h+2,true::K,R⟩ := by
  have H := zrun_shift (vt i) h 2 ⟨0,0,[],P++R⟩
  rw [prelude0] at H
  simpa [shift,Int.add_comm] using H

theorem rightOne0 (i : Fin 17) (L R : List Bool) :
    zrun (vt i) 2 ⟨2,0,true::L,P++R⟩ = some ⟨2,2,true::(Q++L),R⟩ := by rfl

theorem rightOne (i : Fin 17) (h : Int) (L R : List Bool) :
    zrun (vt i) 2 ⟨2,h,true::L,P++R⟩ = some ⟨2,h+2,true::(Q++L),R⟩ := by
  have H := zrun_shift (vt i) h 2 ⟨2,0,true::L,P++R⟩
  rw [rightOne0] at H
  simpa [shift,Int.add_comm] using H

theorem rightSweep (i : Fin 17) (n : Nat) (h : Int) (L R : List Bool) :
    zrun (vt i) (2*n) ⟨2,h,true::L,rep P n++R⟩ =
      some ⟨2,h+2*(n:Int),true::(rep Q n++L),R⟩ := by
  induction n generalizing h L with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H := join (rightOne i h L (rep P n++R)) (ih (h+2) (Q++L))
    rw [show 2*(n+1)=2+2*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Q n) Q L,rep_snoc Q n,
      Int.natCast_succ,show h+2+2*(n:Int)=h+2*((n:Int)+1) by omega] using H

theorem turn0 (i : Fin 17) (L : List Bool) :
    zrun (vt i) 5 ⟨2,0,true::L,[]⟩ = some ⟨3,1,Q++L,K⟩ := by rfl

theorem turn (i : Fin 17) (h : Int) (L : List Bool) :
    zrun (vt i) 5 ⟨2,h,true::L,[]⟩ = some ⟨3,h+1,Q++L,K⟩ := by
  have H := zrun_shift (vt i) h 5 ⟨2,0,true::L,[]⟩
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

theorem grows (i : Fin 17) (n : Nat) (h : Int) :
    ∃ t, 0 < t ∧ zrun (vt i) t (family n h) = some (family (n+2) (h-1)) := by
  cases n with
  | zero => exact ⟨9,by decide,first w h⟩
  | succ n =>
    cases w with
    | false => exact ⟨13+4*n,by omega,growthB n h⟩
    | true => exact ⟨15+6*n,by omega,growthD n h⟩

theorem arbitraryRun (i : Fin 17) (n : Nat) : ∃ t k h, n ≤ t ∧
    zrun (vt i) t (family 0 0) = some (family k h) := by
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

theorem never (i : Fin 17) (m : Machine) (hm : compatible (vt i) m) : NeverHalts m := by
  intro n
  obtain ⟨t,k,h,ht,hr⟩ := arbitraryRun w n
  have H := zrun_sound (vt i) m hm t _ _ hr
  rw [initial_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some c => rfl

#print axioms growthB
#print axioms growthD
#print axioms never
end BB6Coverage.Agent50AlternatingSweep
theorem firstLeft (i : Fin 17) (h : Int) (L R : List Bool) :
    zrun (vt i) (spec i).firstCost ⟨3,h,Q++L,K++R⟩ = some ⟨(spec i).q,h-2,L,(spec i).cap++R⟩ := by
  have H := zrun_shift (vt i) h (spec i).firstCost ⟨3,0,Q++L,K++R⟩
  rw [(atoms i L R).1] at H
  simpa [shift,show -2+h=h-2 by omega] using H

theorem loopLeft (i : Fin 17) (h : Int) (L R : List Bool) :
    zrun (vt i) (spec i).loopCost ⟨(spec i).q,h,Q++Q++L,(spec i).cap++R⟩ = some ⟨(spec i).q,h-4,L,(spec i).cap++P++P++R⟩ := by
  have H := zrun_shift (vt i) h (spec i).loopCost ⟨(spec i).q,0,Q++Q++L,(spec i).cap++R⟩
  rw [(atoms i L R).2.1] at H
  simpa [shift,show -4+h=h-4 by omega] using H

theorem finishLeft (i : Fin 17) (h : Int) (R : List Bool) :
    zrun (vt i) (spec i).finishCost ⟨(spec i).q,h,Q++K,(spec i).cap++R⟩ = some ⟨0,h-4,[],P++P++P++P++R⟩ := by
  have H := zrun_shift (vt i) h (spec i).finishCost ⟨(spec i).q,0,Q++K,(spec i).cap++R⟩
  rw [(atoms i [] R).2.2] at H
  simpa [shift,show -4+h=h-4 by omega] using H

theorem rep_double (p : List Bool) (n : Nat) : rep p (2*n) = rep (p++p) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2*n+2 by omega]; simp only [rep,List.append_assoc,ih]

theorem sweepLeft (i : Fin 17) (n : Nat) (h : Int) (L R : List Bool) :
    zrun (vt i) ((spec i).loopCost*n) ⟨(spec i).q,h,rep (Q++Q) n++L,(spec i).cap++R⟩ =
    some ⟨(spec i).q,h-4*(n:Int),L,(spec i).cap++rep (P++P) n++R⟩ := by
  induction n generalizing h R with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have H0 := loopLeft i h (rep (Q++Q) n++L) R
    simp only [List.append_assoc] at H0
    have H := join H0 (ih (h-4) (P++P++R))
    rw [Nat.mul_succ, Nat.add_comm]
    have hw := congrArg (fun x : List Bool => x ++ R) (rep_snoc (P++P) n)
    simp only [List.append_assoc] at hw
    simpa only [rep,List.append_assoc,hw,
      Int.natCast_succ,show h-4-4*(n:Int)=h-4*((n:Int)+1) by omega] using H

theorem growth (i : Fin 17) (n : Nat) (h : Int) :
    ∃ t, 0 < t ∧ zrun (vt i) t (family (2*n+2) h) = some (family (2*n+4) (h-1)) := by
  let m := 2*n+1
  have h1 := prelude i h (rep P m)
  have h2 := rightSweep i m (h+2) K []
  simp only [List.append_nil] at h2
  have h3 := turn i (h+2+2*(m:Int)) (rep Q m++K)
  have h4 := firstLeft i (h+2+2*(m:Int)+1) (rep Q m++K) []
  simp only [List.append_nil] at h4
  have h5 := sweepLeft i n (h+2+2*(m:Int)+1-2) (Q++K) []
  simp only [← rep_double,List.append_nil] at h5
  have hr : rep Q m++K = rep Q (2*n)++(Q++K) := by
    dsimp [m]; simp only [rep]; rw [← rep_snoc Q (2*n),List.append_assoc]
  rw [hr] at h4 h3 h2
  have h6 := finishLeft i (h+2+2*(m:Int)+1-2-4*(n:Int)) (rep P (2*n))
  have H := join (join (join (join (join h1 h2) h3) h4) h5) h6
  refine ⟨2+2*m+5+(spec i).firstCost+(spec i).loopCost*n+(spec i).finishCost,by omega,?_⟩
  simpa only [family,rep,List.append_assoc,show m=2*n+1 by rfl,show 2*n+2=(2*n)+1+1 by omega,show 2*n+4=(2*n)+4 by omega,
    show h+2+2*((2*n+1:Nat):Int)+1-2-4*(n:Int)-4=h-1 by omega] using H

theorem arbitraryRun (i : Fin 17) (n : Nat) :
    ∃ t h, n ≤ t ∧ zrun (vt i) t (family 0 0) = some (family (2*n+2) h) := by
  induction n with
  | zero => exact ⟨9,-1,by decide,first0 i⟩
  | succ n ih =>
    obtain ⟨t,h,ht,hr⟩ := ih
    obtain ⟨u,hu,hg⟩ := growth i n h
    exact ⟨t+u,h-1,by omega,by simpa only [show 2*(n+1)+2=2*n+4 by omega] using join hr hg⟩

theorem never (i : Fin 17) (m : Machine) (hm : compatible (vt i) m) : NeverHalts m := by
  intro n
  obtain ⟨t,h,ht,hr⟩ := arbitraryRun i n
  have H := zrun_sound (vt i) m hm t _ _ hr
  rw [initial_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some c => rfl

#print axioms atoms
#print axioms growth
#print axioms never
end BB6Coverage.Agent50AlternatingVariants
