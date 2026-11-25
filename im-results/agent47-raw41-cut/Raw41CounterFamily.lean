import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.CounterFamily
open BB6Coverage BB6Coverage.Agent31Pump

/-- A reachable invariant whose every member has a strictly positive defined
return proves nonhalting for every compatible completion. -/
theorem never_of_returns (p : PartialMachine) (Inv : Z0 → Prop)
    (e : Nat) (z0 : Z0) (first : run0 p e ⟨0,[],[]⟩ = some z0)
    (hz0 : Inv z0)
    (progress : ∀ z, Inv z → ∃ t z', 0 < t ∧ run0 p t z = some z' ∧ Inv z')
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t z, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some z ∧ Inv z := by
    intro k
    induction k with
    | zero => exact ⟨e,z0,by omega,first,hz0⟩
    | succ k ih =>
      obtain ⟨t,z,ht,hr,hz⟩ := ih
      obtain ⟨s,z',hs,he,hz'⟩ := progress z hz
      exact ⟨t+s,z',by omega,join0 hr he,hz'⟩
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := arbitrary n
  have hz : (Agent50Zipper.zrun p t BB6Coverage.Agent31Pump.start).map project = some z :=
    (run_project p t BB6Coverage.Agent31Pump.start).trans hr
  cases h : Agent50Zipper.zrun p t BB6Coverage.Agent31Pump.start with
  | none => simp [h] at hz
  | some z =>
    have H := Agent50Zipper.zrun_sound p m hm t BB6Coverage.Agent31Pump.start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

abbrev zeros (n : Nat) := List.replicate n false
abbrev ones (n : Nat) := List.replicate n true

theorem rep_singleton (a : Bool) (n : Nat) : rep [a] n = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,ih,List.replicate_succ]

/-- Common E-return machine, indexed by the variant of the A1/B1/C1 turns.
0 = triple counter; 1 and 2 = paired-bit counters with the same return map. -/
def table (v : Fin 3) : PartialMachine := fun s => match s.1.val,s.2 with
 | 0,false => some (some ⟨true,true,1⟩)
 | 0,true => some (some (if v.val = 0 then ⟨false,false,3⟩ else if v.val = 1 then ⟨false,true,2⟩ else ⟨true,true,2⟩))
 | 1,false => some (some ⟨true,true,2⟩)
 | 1,true => some (some (if v.val = 0 then ⟨true,false,2⟩ else ⟨false,true,4⟩))
 | 2,false => some (some ⟨false,true,3⟩)
 | 2,true => some (some (if v.val = 0 then ⟨false,true,4⟩ else ⟨true,false,1⟩))
 | 3,false => some (some ⟨true,false,3⟩)
 | 3,true => some (some ⟨true,true,0⟩)
 | 4,true => some (some ⟨false,true,5⟩)
 | 5,false => some (some ⟨false,true,2⟩)
 | 5,true => some (some ⟨false,false,3⟩)
 | _,_ => none

def cfg (k : Nat) (r : List Bool) : Z0 := ⟨4,true :: (zeros k ++ [true,true]),r⟩

theorem dStep (v : Fin 3) (L R : List Bool) :
    run0 (table v) 1 ⟨3,false::L,R⟩ = some ⟨3,L,true::R⟩ := by rfl

theorem dFill (v : Fin 3) (n : Nat) (R : List Bool) :
    run0 (table v) n ⟨3,zeros n ++ [true,true],R⟩ =
    some ⟨3,[true,true],ones n ++ R⟩ := by
  simpa only [List.nil_append, Nat.one_mul, rep_singleton] using
    sweepL (table v) 3 [] [] [false] [true] 1 (dStep v) n [true,true] R

-- These two transitions enter D without examining the suffix.
theorem startOne (v : Fin 3) (k : Nat) (R : List Bool) :
    run0 (table v) 2 (cfg k (true::R)) =
    some ⟨3,zeros (k+1) ++ [true,true],false::R⟩ := by
  rfl

theorem startEmpty (v : Fin 3) (k : Nat) :
    run0 (table v) 3 (cfg k []) =
    some ⟨3,zeros (k+4) ++ [true,true],[]⟩ := by rfl

theorem startZero (v : Fin 3) (k : Nat) :
    run0 (table v) 3 (cfg k [false]) =
    some ⟨3,zeros (k+4) ++ [true,true],[]⟩ := by rfl

def turnCost (v : Fin 3) : Nat := if v.val = 2 then 4 else 6

theorem dTurn (v : Fin 3) (R : List Bool) :
    run0 (table v) (turnCost v) ⟨3,[true,true],true::true::R⟩ = some (cfg 1 R) := by
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
  rcases hv with h|h|h
  · have he : v = 0 := Fin.ext h; subst v; rfl
  · have he : v = 1 := Fin.ext h; subst v; rfl
  · have he : v = 2 := Fin.ext h; subst v; rfl

theorem oneReturn (v : Fin 3) (k : Nat) (R : List Bool) :
    run0 (table v) (2+(k+2)+turnCost v) (cfg (k+1) (true::R)) =
    some (cfg 1 (ones k ++ false::R)) := by
  have a := startOne v (k+1) R
  have b := dFill v (k+2) (false::R)
  have c := dTurn v (ones k ++ false::R)
  exact join0 (join0 a b) c

theorem emptyReturn (v : Fin 3) (k : Nat) :
    run0 (table v) (3+(k+4)+turnCost v) (cfg k []) = some (cfg 1 (ones (k+2))) := by
  have a := startEmpty v k
  have b := dFill v (k+4) []
  rw [List.append_nil] at b
  exact join0 (join0 a b) (dTurn v (ones (k+2)))

theorem zeroReturn (v : Fin 3) (k : Nat) :
    run0 (table v) (3+(k+4)+turnCost v) (cfg k [false]) = some (cfg 1 (ones (k+2))) := by
  have a := startZero v k
  have b := dFill v (k+4) []
  rw [List.append_nil] at b
  exact join0 (join0 a b) (dTurn v (ones (k+2)))

-- The carry consumes an entire zero digit and extends the left zero run.
theorem carry3 (k : Nat) (R : List Bool) :
    run0 (table 0) 3 (cfg k (false::true::true::R)) = some (cfg (k+3) R) := by rfl

theorem carry2 (v : Fin 3) (hv : v.val ≠ 0) (k : Nat) (R : List Bool) :
    run0 (table v) 6 (cfg k (false::true::R)) = some (cfg (k+2) R) := by
  have h : v.val = 1 ∨ v.val = 2 := by omega
  rcases h with h|h
  · have he : v = 1 := Fin.ext h; subst v; rfl
  · have he : v = 2 := Fin.ext h; subst v; rfl

/-- Right word of the triple-digit binary counter. -/
inductive Triple : List Bool → Prop
 | nil : Triple []
 | cons (b : Bool) (R : List Bool) : Triple R → Triple (b::true::true::R)

theorem tripleOnes (n : Nat) (R : List Bool) (hR : Triple R) : Triple (ones (3*n) ++ R) := by
  induction n with
  | zero => exact hR
  | succ n ih =>
    rw [show 3*(n+1)=3*n+3 by omega]
    exact Triple.cons true _ ih

def Inv3 (z : Z0) : Prop := ∃ n R, Triple R ∧ z = cfg (3*n+1) R

theorem progress3 (z : Z0) (hz : Inv3 z) :
    ∃ t z', 0 < t ∧ run0 (table 0) t z = some z' ∧ Inv3 z' := by
  obtain ⟨n,R,hR,rfl⟩ := hz
  cases hR with
  | nil =>
    refine ⟨_,_,by omega,emptyReturn 0 (3*n+1),0,_,?_,rfl⟩
    rw [show 3*n+1+2=3*(n+1) by omega]
    simpa using tripleOnes (n+1) [] Triple.nil
  | cons b R h =>
    cases b with
    | false =>
      refine ⟨3,_,by decide,carry3 (3*n+1) R,n+1,R,h,?_⟩
      rw [show 3*n+1+3=3*(n+1)+1 by omega]
    | true =>
      exact ⟨_,_,by omega,oneReturn 0 (3*n) (true::true::R),0,_,tripleOnes n _ (Triple.cons false R h),rfl⟩

theorem entry3 : run0 (table 0) 11 ⟨0,[],[]⟩ = some (cfg 1 []) := by rfl

theorem never3 (m : Machine) (hm : compatible (table 0) m) : NeverHalts m :=
  never_of_returns _ Inv3 11 _ entry3 ⟨0,[],Triple.nil,rfl⟩ progress3 m hm

/-- A paired digit followed by a terminal bit, or the initial empty word. -/
inductive PairWord : List Bool → Prop
 | nil : PairWord []
 | terminal (b : Bool) : PairWord [b]
 | cons (b : Bool) (R : List Bool) : PairWord R → PairWord (b::true::R)

theorem pairOnes (n : Nat) (R : List Bool) (hR : PairWord R) : PairWord (ones (2*n) ++ R) := by
  induction n with
  | zero => exact hR
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega]
    exact PairWord.cons true _ ih

def Inv2 (z : Z0) : Prop := ∃ n R, PairWord R ∧ z = cfg (2*n+1) R

theorem progress2 (v : Fin 3) (hv : v.val ≠ 0) (z : Z0) (hz : Inv2 z) :
    ∃ t z', 0 < t ∧ run0 (table v) t z = some z' ∧ Inv2 z' := by
  obtain ⟨n,R,hR,rfl⟩ := hz
  cases hR with
  | nil =>
    refine ⟨_,_,by omega,emptyReturn v (2*n+1),0,_,?_,rfl⟩
    rw [show 2*n+1+2=2*(n+1)+1 by omega]
    simpa only [← List.replicate_succ'] using pairOnes (n+1) [true] (PairWord.terminal true)
  | terminal b =>
    cases b with
    | false =>
      refine ⟨_,_,by omega,zeroReturn v (2*n+1),0,_,?_,rfl⟩
      rw [show 2*n+1+2=2*(n+1)+1 by omega]
      simpa only [← List.replicate_succ'] using pairOnes (n+1) [true] (PairWord.terminal true)
    | true => exact ⟨_,_,by omega,oneReturn v (2*n) [],0,_,pairOnes n [false] (PairWord.terminal false),rfl⟩
  | cons b R h =>
    cases b with
    | false =>
      refine ⟨6,_,by decide,carry2 v hv (2*n+1) R,n+1,R,h,?_⟩
      rw [show 2*n+1+2=2*(n+1)+1 by omega]
    | true => exact ⟨_,_,by omega,oneReturn v (2*n) (true::R),0,_,pairOnes n _ (PairWord.cons false R h),rfl⟩

theorem entry21 : run0 (table 1) 11 ⟨0,[],[]⟩ = some (cfg 1 []) := by rfl
theorem entry22 : run0 (table 2) 9 ⟨0,[],[]⟩ = some (cfg 1 []) := by rfl

theorem never21 (m : Machine) (hm : compatible (table 1) m) : NeverHalts m :=
  never_of_returns _ Inv2 11 _ entry21 ⟨0,[],PairWord.nil,rfl⟩ (progress2 1 (by decide)) m hm

theorem never22 (m : Machine) (hm : compatible (table 2) m) : NeverHalts m :=
  never_of_returns _ Inv2 9 _ entry22 ⟨0,[],PairWord.nil,rfl⟩ (progress2 2 (by decide)) m hm

#print axioms never_of_returns
#print axioms never3
#print axioms never21
#print axioms never22
end BB6.Agent47Raw41.CounterFamily
