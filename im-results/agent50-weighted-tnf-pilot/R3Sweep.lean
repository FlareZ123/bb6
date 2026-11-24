import SparseZipper

namespace BB6Coverage.Agent50R3Sweep
open BB6Coverage Agent50Zipper

def r3Table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨false,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,1⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

def B : List Bool := [false,true,true]
def P : List Bool := B++B

def rep : Nat → List Bool
  | 0 => []
  | n+1 => P ++ rep n

theorem rep_snoc (n : Nat) : rep n ++ P = P ++ rep n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih]

theorem rep_B_comm (n : Nat) : rep n ++ B = B ++ rep n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,P,List.append_assoc,ih]

def family (n : Nat) (h : Int) : Z := ⟨0,h,false::(rep n++[false]),[]⟩

theorem prefix0 (L : List Bool) :
    zrun r3Table 5 ⟨0,0,false::L,[]⟩ = some ⟨4,-1,L,B⟩ := by rfl

theorem leftPair0 (L R : List Bool) :
    zrun r3Table 6 ⟨4,0,P++L,R⟩ = some ⟨4,-6,L,P++R⟩ := by rfl

theorem turn0 (R : List Bool) :
    zrun r3Table 27 ⟨4,0,[false],B++R⟩ = some ⟨0,3,false::(P++[false]),R⟩ := by rfl

theorem rightPair0 (L R : List Bool) :
    zrun r3Table 26 ⟨0,0,false::false::L,P++R⟩ = some ⟨0,6,false::(P++false::L),R⟩ := by rfl

theorem prelude (h : Int) (L : List Bool) :
    zrun r3Table 5 ⟨0,h,false::L,[]⟩ = some ⟨4,h-1,L,B⟩ := by
  have hh := zrun_shift r3Table h 5 ⟨0,0,false::L,[]⟩
  rw [prefix0] at hh
  simpa [shift,show -1+h=h-1 by omega] using hh

theorem leftPair (h : Int) (L R : List Bool) :
    zrun r3Table 6 ⟨4,h,P++L,R⟩ = some ⟨4,h-6,L,P++R⟩ := by
  have hh := zrun_shift r3Table h 6 ⟨4,0,P++L,R⟩
  rw [leftPair0] at hh
  simpa [shift,show -6+h=h-6 by omega] using hh

theorem turn (h : Int) (R : List Bool) :
    zrun r3Table 27 ⟨4,h,[false],B++R⟩ = some ⟨0,h+3,false::(P++[false]),R⟩ := by
  have hh := zrun_shift r3Table h 27 ⟨4,0,[false],B++R⟩
  rw [turn0] at hh
  simpa [shift,show 3+h=h+3 by omega] using hh

theorem rightPair (h : Int) (L R : List Bool) :
    zrun r3Table 26 ⟨0,h,false::false::L,P++R⟩ = some ⟨0,h+6,false::(P++false::L),R⟩ := by
  have hh := zrun_shift r3Table h 26 ⟨0,0,false::false::L,P++R⟩
  rw [rightPair0] at hh
  simpa [shift,show 6+h=h+6 by omega] using hh

theorem leftSweep (n : Nat) (h : Int) (L R : List Bool) :
    zrun r3Table (6*n) ⟨4,h,rep n++L,R⟩ = some ⟨4,h-6*(n:Int),L,rep n++R⟩ := by
  induction n generalizing h R with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have h1 := leftPair h (rep n++L) R
    have h2 := ih (h-6) (P++R)
    have H := join h1 h2
    rw [show 6*(n+1)=6+6*n by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep n) P R,rep_snoc n,
      Int.natCast_succ,show h-6-6*(n:Int)=h-6*((n:Int)+1) by omega] using H

theorem rightPairFamily (a : Nat) (h : Int) (R : List Bool) :
    zrun r3Table 26 ⟨0,h,false::(rep a++[false]),P++R⟩ =
    some ⟨0,h+6,false::(rep (a+1)++[false]),R⟩ := by
  cases a with
  | zero => exact rightPair h [] R
  | succ a =>
    have H := rightPair h (true::true::B++rep a++[false]) R
    simpa [rep,P,B,List.append_assoc] using H

theorem rightSweep (n a : Nat) (h : Int) (R : List Bool) :
    zrun r3Table (26*n) ⟨0,h,false::(rep a++[false]),rep n++R⟩ =
    some ⟨0,h+6*(n:Int),false::(rep (a+n)++[false]),R⟩ := by
  induction n generalizing a h with
  | zero => simp [rep,zrun]
  | succ n ih =>
    have h1 := rightPairFamily a h (rep n++R)
    have h2 := ih (a+1) (h+6)
    have H := join h1 h2
    rw [show 26*(n+1)=26+26*n by omega]
    simpa only [rep,List.append_assoc,Int.natCast_succ,
      show h+6+6*(n:Int)=h+6*((n:Int)+1) by omega,show a+1+n=a+(n+1) by omega] using H

theorem growth (n : Nat) (h : Int) :
    zrun r3Table (32+32*n) (family n h) = some (family (n+1) (h+2)) := by
  have h1 := prelude h (rep n++[false])
  have h2 := leftSweep n (h-1) [false] B
  have h3 := turn (h-1-6*(n:Int)) (rep n)
  have h4 := rightSweep n 1 (h-1-6*(n:Int)+3) []
  rw [rep_B_comm] at h2
  have H := join (join h1 h2) h3
  have h4' : zrun r3Table (26*n) ⟨0,h-1-6*(n:Int)+3,false::(P++[false]),rep n⟩ =
      some (family (n+1) (h+2)) := by
    simpa [family,rep,List.append_assoc,show 1+n=n+1 by omega,
      show h-1-6*(n:Int)+3+6*(n:Int)=h+2 by omega] using h4
  have H' := join H h4'
  simpa only [family,show 5+6*n+27+26*n=32+32*n by omega] using H'

theorem initial_embed : embed (family 0 0) = blank := by
  unfold embed family blank
  congr 1
  funext x
  by_cases hx : x ≤ 0
  · simp only [atCell,hx,ite_true,rep,List.nil_append]
    cases (0-x).toNat with
    | zero => rfl
    | succ n => cases n <;> rfl
  · simp [atCell,hx]

theorem arbitraryRun (n : Nat) : ∃ t h, n ≤ t ∧
    zrun r3Table t (family 0 0) = some (family n h) := by
  induction n with
  | zero => exact ⟨0,0,by omega,rfl⟩
  | succ n ih =>
    obtain ⟨t,h,ht,hr⟩ := ih
    exact ⟨t+(32+32*n),h+2,by omega,join hr (growth n h)⟩

theorem r3_never (m : Machine) (hm : compatible r3Table m) : NeverHalts m := by
  intro n
  obtain ⟨t,h,ht,hr⟩ := arbitraryRun n
  have H := zrun_sound r3Table m hm t _ _ hr
  rw [initial_embed] at H
  rw [show t=n+(t-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some c => rfl

#print axioms r3_never
end BB6Coverage.Agent50R3Sweep
