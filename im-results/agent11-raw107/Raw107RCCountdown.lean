import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw107RCCountdown
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

abbrev Z := [false,false,false]
abbrev O := [true,true,true]
abbrev B := [false,true,true]
abbrev leftTail := [false,false,false,false,true,true]
abbrev Dbase (R : List Bool) : Z0 := ⟨3,[true,true],[true,true,true,true]++R⟩
abbrev Fcfg (n : Nat) (R : List Bool) : Z0 := ⟨5,R.headD false :: (rep Z n ++ leftTail),R.tail⟩
def family (n : Nat) : Z0 := ⟨3,rep Z n ++ leftTail,[]⟩

theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem enter (R : List Bool) : run0 table 5 (Dbase R) = some (Fcfg 0 R) := by rfl

theorem skip_one (k : Nat) (R : List Bool) :
    run0 table 3 (Fcfg k (B++R)) = some (Fcfg (k+1) R) := by rfl

theorem skip_all (n k : Nat) (R : List Bool) :
    run0 table (3*n) (Fcfg k (rep B n++R)) = some (Fcfg (k+n) R) := by
  induction n generalizing k with
  | zero => simp [rep,run0]
  | succ n ih =>
    have h := join0 (skip_one k (rep B n++R)) (ih (k+1))
    simpa only [rep,List.append_assoc,show k+1+n=k+(n+1) by omega,show 3+3*n=3*(n+1) by omega] using h

theorem triple (L R : List Bool) : run0 table 3 ⟨3,Z++L,R⟩ = some ⟨3,L,O++R⟩ := by rfl

theorem restore3 (n : Nat) (R : List Bool) :
    run0 table (3*n) ⟨3,rep Z n++leftTail,R⟩ = some ⟨3,leftTail,rep O n++R⟩ := by
  simpa only [List.nil_append] using sweepL table 3 [] [] Z O 3 triple n leftTail R

theorem restore4 (R : List Bool) : run0 table 4 ⟨3,leftTail,R⟩ = some (Dbase R) := by rfl

theorem hit (n : Nat) (R : List Bool) :
    run0 table 1 (Fcfg n (true::R)) = some ⟨3,rep Z n++leftTail,false::R⟩ := by rfl

theorem decrement (n : Nat) (R : List Bool) :
    run0 table (10+6*n) (Dbase (rep B n++true::R)) =
      some (Dbase (rep O n++false::R)) := by
  have h := join0 (enter (rep B n++true::R)) (skip_all n 0 (true::R))
  simp only [Nat.zero_add] at h
  have h := join0 (join0 (join0 h (hit n R)) (restore3 n (false::R))) (restore4 (rep O n++false::R))
  simpa only [show 5+3*n+1+3*n+4=10+6*n by omega] using h

def clearCost : Nat → Nat
  | 0 => 0
  | n+1 => clearCost n + (10+6*n) + clearCost n

theorem clear (n : Nat) (R : List Bool) :
    run0 table (clearCost n) (Dbase (rep O n++R)) = some (Dbase (rep B n++R)) := by
  induction n generalizing R with
  | zero => simp [clearCost,rep,run0]
  | succ n ih =>
    have h1 := ih (O++R)
    have h2 := decrement n (true::true::R)
    have h3 := ih (B++R)
    have h2' : run0 table (10+6*n) (Dbase (rep B n++(O++R))) = some (Dbase (rep O n++(B++R))) := h2
    have h := join0 (join0 h1 h2') h3
    rw [← List.append_assoc,rep_snoc O n,← List.append_assoc,rep_snoc B n] at h
    simpa only [clearCost,rep] using h

theorem overflow (n : Nat) : run0 table 2 (Fcfg n []) = some (family (n+1)) := by rfl

def cost (n : Nat) := 3*n+4+clearCost n+5+3*n+2

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := join0 (restore3 n []) (restore4 (rep O n++[]))
  have h2 := clear n []
  have h3 := enter (rep B n++[])
  have h4 := skip_all n 0 []
  simp only [Nat.zero_add] at h4
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) (overflow n)
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 cost entry (by intro n; unfold cost; omega) growth m hm
#print axioms entry
#print axioms growth
#print axioms never
end BB6.Agent11Raw107RCCountdown
