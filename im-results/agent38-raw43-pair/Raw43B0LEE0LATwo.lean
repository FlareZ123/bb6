import SweepPumping
set_option maxHeartbeats 0
namespace BB6.Agent38Raw43B0LEE0LATwo
open BB6Coverage BB6Coverage.Agent31Pump

-- false: M113, true: M34
def table (v : Bool) : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some (if v then ⟨false,false,1⟩ else ⟨false,true,0⟩))
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none

def w : Nat → List Bool
  | 0 => []
  | n+1 => true::false::true::false::w n

def tailWord (v : Bool) : List Bool :=
  if v then [true,true,true,false,false,false,false,true] else [true,true,true,true]

def k (v : Bool) : Nat := if v then 50 else 32

def family (v : Bool) (n : Nat) : Z0 := ⟨0,[],false::false::(w n ++ tailWord v)⟩

theorem replicateAdd (a b : Nat) : List.replicate (a+b) true = List.replicate a true ++ List.replicate b true := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a+1+b=(a+b)+1 by omega]; simp only [List.replicate_succ,ih,List.cons_append]

theorem forward (v : Bool) (n : Nat) (L : List Bool) :
    ∃ t, run0 (table v) t ⟨0,false::L,false::false::(w n ++ tailWord v)⟩ =
      some ⟨1,List.replicate (4*n+5) true ++ L,tailWord v⟩ := by
  induction n generalizing L with
  | zero => exact ⟨k v,by cases v <;> rfl⟩
  | succ n ih =>
    have h1 : run0 (table v) 16 ⟨0,false::L,false::false::(w (n+1) ++ tailWord v)⟩ =
      some ⟨0,false::true::true::true::true::L,false::false::(w n ++ tailWord v)⟩ := by cases v <;> rfl
    obtain ⟨t,h2⟩ := ih (true::true::true::true::L)
    refine ⟨16+t,?_⟩
    have h := join0 h1 h2
    simpa [Nat.mul_succ,show 4*n+4+5=4*n+5+4 by omega,replicateAdd,List.append_assoc] using h

theorem forward0 (v : Bool) (n : Nat) :
    ∃ t, run0 (table v) t (family v n) = some ⟨1,List.replicate (4*n+5) true,tailWord v⟩ := by
  cases n with
  | zero => exact ⟨k v,by cases v <;> rfl⟩
  | succ n =>
    have h1 : run0 (table v) 16 (family v (n+1)) = some ⟨0,[false,true,true,true,true],false::false::(w n ++ tailWord v)⟩ := by cases v <;> rfl
    obtain ⟨t,h2⟩ := forward v n [true,true,true,true]
    refine ⟨16+t,?_⟩
    simpa [Nat.mul_succ,show 4*n+4+5=4*n+5+4 by omega,replicateAdd] using join0 h1 h2

theorem backward (v : Bool) (n : Nat) (R : List Bool) :
    ∃ t, 0<t ∧ run0 (table v) t ⟨1,List.replicate (4*n+5) true,R⟩ =
      some ⟨0,[],false::false::(w (n+1) ++ R)⟩ := by
  induction n generalizing R with
  | zero => exact ⟨6,by decide,by cases v <;> rfl⟩
  | succ n ih =>
    have h1 : run0 (table v) 4 ⟨1,List.replicate (4*(n+1)+5) true,R⟩ = some ⟨1,List.replicate (4*n+5) true,true::false::true::false::R⟩ := by
      rw [show 4*(n+1)+5=4+(4*n+5) by omega,replicateAdd]
      cases v <;> rfl
    obtain ⟨t,ht,h2⟩ := ih (true::false::true::false::R)
    refine ⟨4+t,by omega,?_⟩
    have hw (m : Nat) : w m ++ (true::false::true::false::R) = w (m+1) ++ R := by
      induction m with
      | zero => rfl
      | succ m ih => simp only [w,List.cons_append,ih]
    have h := join0 h1 h2
    rw [hw] at h
    exact h

theorem epoch (v : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (family v n) = some (family v (n+1)) := by
  obtain ⟨t,h⟩ := forward0 v n
  obtain ⟨u,hu,h'⟩ := backward v n (tailWord v)
  exact ⟨t+u,by omega,join0 h h'⟩

theorem live_prefix (v : Bool) (n : Nat) :
    ∃ t j, n≤t ∧ run0 (table v) t ⟨0,[],[]⟩ = some (family v j) := by
  induction n with
  | zero => cases v
            · exact ⟨22,0,by decide,rfl⟩
            · exact ⟨51,0,by decide,rfl⟩
  | succ n ih =>
    obtain ⟨t,j,ht,h⟩ := ih
    obtain ⟨u,hu,h'⟩ := epoch v j
    exact ⟨t+u,j+1,by omega,join0 h h'⟩

open BB6Coverage.Agent50Zipper

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,j,ht,hr⟩ := live_prefix v n
  have hz : (zrun (table v) t start).map project = some (family v j) :=
    (run_project (table v) t start).trans hr
  cases h : zrun (table v) t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound (table v) m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent38Raw43B0LEE0LATwo
