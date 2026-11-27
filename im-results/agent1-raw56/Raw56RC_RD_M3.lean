import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent1Raw56RCRDM3
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

abbrev Z := Z0
abbrev P := [false,true]
abbrev Q := [true,false]
abbrev H := [true,true]
abbrev S := [false,true,true,true]

theorem oneR (L R : List Bool) :
    run0 table 12 ⟨0,[false] ++ L,S ++ P ++ R⟩ =
    some ⟨0,[false] ++ H ++ L,S ++ R⟩ := by rfl

theorem mid (L R : List Bool) :
    run0 table 12 ⟨0,[false] ++ L,S ++ [false,false] ++ R⟩ =
    some ⟨0,[false] ++ H ++ L,[false,true,true,false] ++ R⟩ := by rfl

theorem mid2 (L R : List Bool) :
    run0 table 9 ⟨0,[false] ++ L,[false,true,true,false] ++ R⟩ =
    some ⟨0,H ++ L,[false,true,true] ++ R⟩ := by rfl

theorem oneL (L R : List Bool) :
    run0 table 2 ⟨0,H ++ L,R⟩ = some ⟨0,L,Q ++ R⟩ := by rfl

theorem start (R : List Bool) :
    run0 table 21 ⟨0,[],Q ++ Q ++ R⟩ =
    some ⟨0,[false,true,true],S ++ [false] ++ R⟩ := by rfl

theorem rot (n : Nat) : [false] ++ rep Q n = rep P n ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep, rep]
    change [false,true,false] ++ rep Q n = P ++ rep P n ++ [false]
    change P ++ ([false] ++ rep Q n) = P ++ rep P n ++ [false]
    rw [ih,List.append_assoc]

def cfg (n : Nat) (R : List Bool) : Z :=
  ⟨0,[false,true,true], S ++ rep P n ++ [false,false] ++ R⟩

theorem grow (n : Nat) (R : List Bool) :
    run0 table (48+14*n) (cfg n R) = some (cfg (n+1) (H ++ R)) := by
  have h1 := sweepR table 0 [false] S P H 12 oneR n H ([false,false] ++ R)
  have h2 := mid (rep H n ++ H) R
  have h3 := mid2 (H ++ rep H n ++ H) R
  have h4 := sweepL table 0 [] [] H Q 2 oneL (n+3) [] ([false,true,true] ++ R)
  have h5 := start (rep Q (n+1) ++ [false,true,true] ++ R)
  have h1' : run0 table (12*n) (cfg n R) = some ⟨0,[false] ++ (rep H n ++ H),S ++ [false,false] ++ R⟩ := by
    simpa [cfg,List.append_assoc] using h1
  have h2' : run0 table 12 ⟨0,[false] ++ (rep H n ++ H),S ++ [false,false] ++ R⟩ =
      some ⟨0,[false] ++ (H ++ rep H n ++ H),[false,true,true,false] ++ R⟩ := by
    simpa [List.append_assoc] using h2
  have h3' : run0 table 9 ⟨0,[false] ++ (H ++ rep H n ++ H),[false,true,true,false] ++ R⟩ =
      some ⟨0,rep H (n+3),[false,true,true] ++ R⟩ := by
    have e : rep H (n+3) = H ++ (H ++ (rep H n ++ H)) := by
      calc
        rep H (n+3) = H ++ (H ++ (H ++ rep H n)) := rfl
        _ = _ := by rw [rep_snoc]
    rw [e]
    simpa [List.append_assoc] using h3
  have h4' : run0 table (2*(n+3)) ⟨0,rep H (n+3),[false,true,true] ++ R⟩ =
      some ⟨0,[],Q ++ Q ++ (rep Q (n+1) ++ [false,true,true] ++ R)⟩ := by
    have e : rep Q (n+3) = Q ++ (Q ++ rep Q (n+1)) := rfl
    simpa only [List.nil_append,List.append_nil,List.append_assoc,e] using h4
  have h5' : run0 table 21 ⟨0,[],Q ++ Q ++ (rep Q (n+1) ++ [false,true,true] ++ R)⟩ =
      some (cfg (n+1) (H ++ R)) := by
    unfold cfg
    simp only [List.append_assoc] at h5 ⊢
    rw [← List.append_assoc [false] (rep Q (n+1)), rot] at h5
    simpa [List.append_assoc] using h5
  have h := join0 (join0 (join0 (join0 h1' h2') h3') h4') h5'
  rw [show 48+14*n = 12*n+12+9+2*(n+3)+21 by omega]
  exact h

def family (n : Nat) : Z := cfg n (rep H (n+2))
theorem entry : run0 table 83 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (48+14*n) (family n) = some (family (n+1)) := by
  unfold family
  rw [show n+1+2 = (n+2)+1 by omega, rep]
  exact grow n _

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 83 (fun n => 48+14*n) entry (by intro n; omega) growth m hm
#print axioms grow
#print axioms never
end BB6Coverage.Agent1Raw56RCRDM3
