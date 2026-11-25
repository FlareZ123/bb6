import Raw41CounterFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41.LongSweep
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent47Raw41.CounterFamily
-- 1RB1LB_1RC0RC_0RD1LE_1LD1RA_0LF---_1LA0LB
def table : PartialMachine := fun s => match s.1.val,s.2 with
 | 0,false => some (some ⟨true,true,1⟩)
 | 0,true => some (some ⟨true,false,1⟩)
 | 1,false => some (some ⟨true,true,2⟩)
 | 1,true => some (some ⟨false,true,2⟩)
 | 2,false => some (some ⟨false,true,3⟩)
 | 2,true => some (some ⟨true,false,4⟩)
 | 3,false => some (some ⟨true,false,3⟩)
 | 3,true => some (some ⟨true,true,0⟩)
 | 4,false => some (some ⟨false,false,5⟩)
 | 5,false => some (some ⟨true,false,0⟩)
 | 5,true => some (some ⟨false,false,1⟩)
 | _,_ => none

def family (n : Nat) : Z0 := ⟨0,[],[true,false]++ones (6*n+4)⟩
theorem entry : run0 table 21 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem start (R : List Bool) :
    run0 table 9 ⟨0,[],[true,false,true,true,true]++R⟩ =
    some ⟨0,[false,true],[true,false,true,true]++R⟩ := by rfl

theorem rightOne (L R : List Bool) :
    run0 table 9 ⟨0,[false]++L,[true,false,true,true]++[true]++R⟩ =
    some ⟨0,[false]++[true]++L,[true,false,true,true]++R⟩ := by rfl

-- Only one final 1 remains; a fixed boundary macro begins the return sweep.
theorem rightLast (L : List Bool) :
    run0 table 9 ⟨0,[false]++L,[true,false,true,true]⟩ =
    some ⟨0,[false,true]++L,[true,false,true]⟩ := by rfl

theorem turn (L : List Bool) :
    run0 table 17 ⟨0,[false]++L,[true,false,true]⟩ =
    some ⟨3,[false,false,false,false,false,true]++L,[true,true]⟩ := by rfl

theorem dFinish (L : List Bool) :
    run0 table 6 ⟨3,[false,false,false,false,false,true]++L,[true,true]⟩ =
    some ⟨0,[true,true]++L,[true,true,true,true,true,true]⟩ := by rfl

theorem leftOne (L R : List Bool) :
    run0 table 11 ⟨0,[true,true]++[true,true,true]++L,[true]++R⟩ =
    some ⟨0,[true,true]++L,[true]++[true,true,true]++R⟩ := by rfl

theorem finish (R : List Bool) :
    run0 table 5 ⟨0,[true,true],[true]++R⟩ =
    some ⟨0,[],[true,false,true,true]++R⟩ := by rfl

theorem tripleRep (n : Nat) : rep [true,true,true] n = ones (3*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3*n+3 by omega]
    simp only [rep,ih]
    rfl

theorem growth (n : Nat) : run0 table (76*n+66) (family n) = some (family (n+1)) := by
  have h1 := start (ones (6*n+1))
  have h2 := sweepR table 0 [false] [true,false,true,true] [true] [true] 9 rightOne (6*n+1) [true] []
  simp only [rep_singleton,List.append_nil] at h2
  have e1 : ones (6*n+1) ++ [true] = ones (6*n+1+1) := by
    exact (List.replicate_succ').symm
  rw [List.append_assoc,e1] at h2
  have h3 := rightLast (ones (6*n+1+1))
  have h4 := turn (ones (6*n+3))
  have h5 := dFinish (ones (6*n+3))
  have h6 := sweepL table 0 [true,true] [true] [true,true,true] [true,true,true] 11 leftOne (2*n+1) [] [true,true,true,true,true]
  simp only [tripleRep,List.append_nil] at h6
  rw [show 3*(2*n+1)=6*n+3 by omega] at h6
  have e2 : [true] ++ ones (6*n+3) ++ [true,true,true,true,true] = [true] ++ ones (6*n+3+5) := by
    rw [List.append_assoc]
    congr 1
    exact List.replicate_append_replicate (n := 6*n+3) (m := 5) (a := true)
  rw [e2] at h6
  have h7 := finish (ones (6*n+3+5))
  have H := join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6) h7
  rw [show 9+9*(6*n+1)+9+17+6+11*(2*n+1)+5 = 76*n+66 by omega] at H
  unfold family
  rw [show 6*n+4 = 6*n+1+3 by omega]
  have eq : [true,false]++ones (6*n+1+3) = [true,false,true,true,true]++ones (6*n+1) := by rfl
  rw [eq]
  have e3 : 6*(n+1)+4 = 6*n+3+5+2 := by omega
  rw [e3]
  change _ = some (⟨0,[],[true,false,true,true]++ones (6*n+3+5)⟩ : Z0)
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 21 (fun n => 76*n+66) entry (by omega) growth m hm
#print axioms never
end BB6.Agent47Raw41.LongSweep
