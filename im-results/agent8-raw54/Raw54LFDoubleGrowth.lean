import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.LFDoubleGrowth
open BB6Coverage BB6Coverage.Agent31Pump

def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some (if v then ⟨true,false,2⟩ else ⟨false,false,4⟩))
  | _,_ => none

def P : List Bool := [true,false,true,false]
def X : List Bool := [true,false,true]
def Y : List Bool := [true,false,false,true,true]
def cfg (n : Nat) : Z0 := ⟨5,[],rep P (n+1) ++ X⟩
def cfg2 (n : Nat) : Z0 := ⟨5,[],rep P (n+2) ++ Y⟩
def aCfg (n : Nat) (R : List Bool) : Z0 := ⟨0,[false,false] ++ rep P n ++ X,R⟩
def fCfg (n : Nat) (R : List Bool) : Z0 := ⟨5,rep P n ++ X,R⟩
def k (v : Bool) : Nat := if v then 8 else 4

theorem scan (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) (4+4*n) ⟨5,[],rep P (n+1) ++ R⟩ = some (aCfg n R) := by
  have h : run0 (table v) 4 ⟨5,[],rep P (n+1) ++ R⟩ = some ⟨0,[false,false] ++ X,rep P n ++ R⟩ := by cases v <;> rfl
  have hs := sweepR (table v) 0 [false,false] [] P P 4 (by intro L R; cases v <;> rfl) n X R
  simpa only [aCfg,List.append_assoc,List.nil_append] using join0 h hs

theorem drain (v : Bool) (n : Nat) (R : List Bool) :
    run0 (table v) (k v*n+k v) (fCfg n R) = some ⟨5,[],rep P (n+1) ++ R⟩ := by
  have h := sweepL (table v) 5 [] [] P P (k v) (by intro L R; cases v <;> rfl) n X R
  have h2 : run0 (table v) (k v) ⟨5,X,rep P n ++ R⟩ = some ⟨5,[],P ++ (rep P n ++ R)⟩ := by cases v <;> rfl
  simpa only [fCfg,List.nil_append,rep,List.append_assoc] using join0 h h2

theorem phase1 (v : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (cfg n) = some (cfg2 n) := by
  have a := scan v n X
  have b : run0 (table v) 12 (aCfg n X) = some (fCfg (n+1) Y) := by cases v <;> rfl
  have c := drain v (n+1) Y
  exact ⟨_,by omega,join0 (join0 a b) c⟩

theorem phase2 (v : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (cfg2 n) = some (cfg (n+2)) := by
  have a := scan v (n+1) Y
  have b : run0 (table v) 6 (aCfg (n+1) Y) = some (fCfg (n+2) X) := by cases v <;> rfl
  have c := drain v (n+2) X
  exact ⟨_,by omega,join0 (join0 a b) c⟩

def family (n : Nat) : Z0 := cfg (2*n)
def entry (v : Bool) : Nat := if v then 22 else 18
theorem first (v : Bool) : run0 (table v) (entry v) ⟨0,[],[]⟩ = some (family 0) := by cases v <;> rfl
theorem family_next (v : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (family n) = some (family (n+1)) := by
  obtain ⟨t,ht,h⟩ := phase1 v (2*n)
  obtain ⟨u,hu,g⟩ := phase2 v (2*n)
  refine ⟨t+u,by omega,?_⟩
  unfold family
  rw [show 2*(n+1)=2*n+2 by omega]
  exact join0 h g
theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns (table v) family (entry v) (first v) (family_next v) m hm
#print axioms never
end BB6.Agent8Raw54.LFDoubleGrowth
