import SweepPumping
namespace BB6.Agent10Raw108LA1100
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none
abbrev W := [true,false,false]
abbrev G := [false,false,true]
abbrev R0 := [true,false,true,true]
abbrev S0 := [false,true,true]
def coreCost : Nat → Nat
  | 0 => 7
  | n+1 => 2*coreCost n+9
theorem wordRotate (n : Nat) : true :: (rep G n ++ S0) = rep W n ++ R0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.append_assoc,List.cons_append,W,G] at *; simp only [← ih]; rfl

theorem core (n : Nat) (L : List Bool) :
    run0 table (coreCost n) ⟨2,false::L,rep W n++R0⟩ =
      some ⟨0,true::false::L,rep G n++S0⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 table 3 ⟨2,false::L,rep W (n+1)++R0⟩ =
        some ⟨2,false::[false,true,false]++L,rep W n++R0⟩ := by cases n <;> rfl
    have h2 := ih ([false,true,false]++L)
    have h3 : run0 table 3 ⟨0,true::false::[false,true,false]++L,rep G n++S0⟩ =
        some ⟨2,false::[true,true,false]++L,true::(rep G n++S0)⟩ := by cases n <;> rfl
    rw [wordRotate n] at h3
    have h4 := ih ([true,true,false]++L)
    have h5 : run0 table 3 ⟨0,true::false::[true,true,false]++L,rep G n++S0⟩ =
        some ⟨0,true::false::L,rep G (n+1)++S0⟩ := by rfl
    have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
    simpa only [coreCost,show 3+coreCost n+3+coreCost n+3=2*coreCost n+9 by omega] using h

def family (n : Nat) : Z0 := ⟨5,[],rep W n++R0⟩
def cost (n : Nat) := 2*coreCost n+11
theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 : run0 table 2 (family n) = some ⟨2,[false,true],rep W n++R0⟩ := by cases n <;> rfl
  have h2 := core n [true]
  have h3 : run0 table 3 ⟨0,[true,false,true],rep G n++S0⟩ = some ⟨0,[],rep G (n+1)++S0⟩ := by rfl
  have h4 : run0 table 2 ⟨0,[],rep G (n+1)++S0⟩ = some ⟨2,[false,true,true],true::(rep G n++S0)⟩ := by rfl
  rw [wordRotate n] at h4
  have h5 := core n [true,true]
  have h6 : run0 table 4 ⟨0,[true,false,true,true],rep G n++S0⟩ = some ⟨5,[],true::(rep G (n+1)++S0)⟩ := by rfl
  rw [wordRotate (n+1)] at h6
  have h := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
  simpa only [cost,family,show 2+coreCost n+3+2+coreCost n+4=2*coreCost n+11 by omega] using h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 cost entry (by intro n; unfold cost; omega) growth m hm
#print axioms never
end BB6.Agent10Raw108LA1100
