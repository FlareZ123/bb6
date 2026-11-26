import SweepPumping
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent8Raw54.ZeroLFGrowth13
open BB6Coverage BB6Coverage.Agent31Pump

inductive V | m13 | m16 | m18

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => match v with
    | .m13 => some (some ⟨true,true,2⟩)
    | .m16 => some (some ⟨false,true,2⟩)
    | .m18 => none
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => match v with
    | .m13 => some (some ⟨false,true,0⟩)
    | .m16 => some (some ⟨true,true,0⟩)
    | .m18 => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def zz : List Bool := [false,false]
def oo : List Bool := [true,true]
def O (v : V) : List Bool := match v with
  | .m13 => [true,false]
  | _ => [false,true]
def quartet : List Bool := [true,false,true,false]
def four : List Bool := [true,true,true,true]
def anchor (v : V) : List Bool := match v with
  | .m13 => [true,false,true,false,true,true,false]
  | _ => [true,false,true,true,true,false]
def marker (v : V) : List Bool := match v with
  | .m13 => [true,true]
  | _ => [true,true,true]
def dCost (v : V) : Nat := match v with | .m13 => 3 | _ => 4
def endCost (v : V) : Nat := match v with | .m13 => 12 | _ => 11

def A (n : Nat) : Z0 := ⟨0,zz,zz ++ List.replicate (4*n+2) true⟩

theorem rep_oo (n : Nat) : rep oo n = List.replicate (2*n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 2*(n+1)=2+2*n by omega,← List.replicate_append_replicate]
    rfl

theorem rep_four (n : Nat) : rep four n = List.replicate (4*n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 4*(n+1)=4+4*n by omega,← List.replicate_append_replicate]
    rfl

theorem entryPhase (v : V) (T : List Bool) :
    run0 (table v) 15 ⟨0,zz,[false,false,true,true] ++ T⟩ =
      some ⟨2,[true,true,true,false],[true,true,true] ++ T⟩ := by cases v <;> rfl

theorem transfer (v : V) (L R : List Bool) :
    run0 (table v) 2 ⟨2,[true] ++ L,oo ++ R⟩ =
      some ⟨2,[true] ++ O v ++ L,R⟩ := by cases v <;> rfl

theorem lastPair (v : V) (L : List Bool) :
    run0 (table v) 2 ⟨2,[true] ++ L,[true]⟩ =
      some ⟨2,[false] ++ O v ++ L,[]⟩ := by cases v <;> rfl

theorem blockShape (v : V) (n : Nat) :
    run0 (table v) (dCost v) ⟨2,[false] ++ (rep (O v) (2*n+2) ++ [true,true,false]),[]⟩ =
      some ⟨3,rep quartet n ++ anchor v,marker v⟩ := by
  cases v
  · have h : rep (O V.m13) (2*n+2) = rep quartet n ++ [true,false,true,false] := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [show 2*(n+1)+2 = 2*n+2+1+1 by omega,rep,rep,ih]
        rfl
    rw [h]
    cases n <;> simp only [List.append_assoc] <;> rfl
  · have h : rep (O V.m16) (2*n+2) = [false] ++ rep quartet n ++ [true,false,true] := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [show 2*(n+1)+2 = 2*n+2+1+1 by omega,rep,rep,ih]
        rfl
    rw [h]
    cases n <;> simp only [List.append_assoc] <;> rfl
  · have h : rep (O V.m18) (2*n+2) = [false] ++ rep quartet n ++ [true,false,true] := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [show 2*(n+1)+2 = 2*n+2+1+1 by omega,rep,rep,ih]
        rfl
    rw [h]
    cases n <;> simp only [List.append_assoc] <;> rfl

theorem drain (v : V) (L R : List Bool) :
    run0 (table v) 8 ⟨3,quartet ++ L,marker v ++ R⟩ =
      some ⟨3,L,marker v ++ four ++ R⟩ := by cases v <;> rfl

theorem finish (v : V) (R : List Bool) :
    run0 (table v) (endCost v) ⟨3,anchor v,marker v ++ R⟩ =
      some ⟨0,zz,[false,false,true,true,true,true,true,true] ++ R⟩ := by cases v <;> rfl

theorem entry (v : V) : run0 (table v) 9 ⟨0,[],[]⟩ = some (A 0) := by cases v <;> rfl

theorem epoch (v : V) (n : Nat) : run0 (table v) (12*n+34) (A n) = some (A (n+1)) := by
  have h1 := entryPhase v (List.replicate (4*n) true)
  have h2 := sweepR (table v) 2 [true] [] oo (O v) 2 (by
    intro L R
    simpa only [List.append_assoc,List.nil_append] using transfer v L R) (2*n+1) [true,true,false] [true]
  have h1' : run0 (table v) 15 (A n) = some ⟨2,[true] ++ [true,true,false],[] ++ rep oo (2*n+1) ++ [true]⟩ := by
    have hi : A n = ⟨0,zz,[false,false,true,true] ++ List.replicate (4*n) true⟩ := by
      unfold A
      rw [show 4*n+2=2+4*n by omega,← List.replicate_append_replicate]
      rfl
    rw [hi, rep_oo, List.nil_append, show [true] = List.replicate 1 true by rfl,
        List.replicate_append_replicate, show 2*(2*n+1)+1=3+4*n by omega,
        ← List.replicate_append_replicate]
    exact h1
  have h3 := lastPair v (rep (O v) (2*n+1) ++ [true,true,false])
  have h2' : run0 (table v) (2*(2*n+1)) ⟨2,[true] ++ [true,true,false],[] ++ rep oo (2*n+1) ++ [true]⟩ =
      some ⟨2,[true] ++ (rep (O v) (2*n+1) ++ [true,true,false]),[true]⟩ := by
    simpa only [List.nil_append,List.append_assoc] using h2
  have h3' : run0 (table v) 2 ⟨2,[true] ++ (rep (O v) (2*n+1) ++ [true,true,false]),[true]⟩ =
      some ⟨2,[false] ++ (rep (O v) (2*n+2) ++ [true,true,false]),[]⟩ := by
    simpa only [rep,List.append_assoc] using h3
  have h4 := blockShape v n
  have h5 := sweepL (table v) 3 [] (marker v) quartet four 8 (by
    intro L R
    simpa only [List.nil_append,List.append_assoc] using drain v L R) n (anchor v) []
  have h5' : run0 (table v) (8*n) ⟨3,rep quartet n ++ anchor v,marker v⟩ =
      some ⟨3,anchor v,marker v ++ rep four n⟩ := by
    simpa only [List.nil_append,List.append_nil] using h5
  have h6 : run0 (table v) (endCost v) ⟨3,anchor v,marker v ++ rep four n⟩ = some (A (n+1)) := by
    have ho : A (n+1) = ⟨0,zz,[false,false,true,true,true,true,true,true] ++ rep four n⟩ := by
      unfold A
      rw [rep_four,show 4*(n+1)+2=6+4*n by omega,← List.replicate_append_replicate]
      rfl
    rw [ho]
    exact finish v (rep four n)
  have h := join0 (join0 (join0 (join0 (join0 h1' h2') h3') h4) h5') h6
  rw [show 15+2*(2*n+1)+2+dCost v+8*n+endCost v=12*n+34 by cases v <;> simp [dCost,endCost] <;> omega] at h
  exact h

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) A 9 (fun n => 12*n+34) (entry v) (by intro n; omega) (epoch v) m hm

#print axioms epoch
#print axioms never
end BB6.Agent8Raw54.ZeroLFGrowth13
