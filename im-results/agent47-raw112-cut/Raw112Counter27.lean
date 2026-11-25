import Raw115CounterBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw112Counter27
open BB6Coverage BB6Coverage.Agent31Pump.Raw115CounterBase

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

abbrev pairs (n : Nat) := rep [true,true] n

def fromF (n : Nat) (X : List Bool) : Z0 := ⟨5,[false],pairs (n+1) ++ X⟩
def toA (n : Nat) (X : List Bool) : Z0 := ⟨0,[false,true] ++ pairs n ++ [false],X⟩

theorem clearPair (X : List Bool) : run0 table 4 (fromF 0 X) = some ⟨5,[false],[true,false] ++ X⟩ := by rfl

theorem consumePair (X : List Bool) : run0 table 2 ⟨5,[false],[true,false] ++ X⟩ = some (toA 0 X) := by rfl

theorem carryStart (n : Nat) (X : List Bool) : run0 table 3 (toA n ([true,true] ++ X)) = some ⟨5,[true,true,true] ++ pairs n ++ [false],[false] ++ X⟩ := by rfl

theorem FPair (L R : List Bool) : run0 table 2 ⟨5,[true,true] ++ L,R⟩ = some ⟨5,L,[true,true] ++ R⟩ := by rfl

theorem carryEnd (n : Nat) (X : List Bool) : run0 table 2 (toA n ([true,false] ++ X)) = some (toA (n+1) X) := by rfl

theorem carrySweep (n : Nat) (X : List Bool) : run0 table (3+2*n) ⟨5,[true,true,true] ++ pairs n ++ [false],[false] ++ X⟩ = some (fromF n ([true,false] ++ X)) := by
  have first : run0 table 3 ⟨5,[true,true,true] ++ pairs n ++ [false],[false] ++ X⟩ = some ⟨5,pairs n ++ [false],[true,true,true,false] ++ X⟩ := by rfl
  have sw := sweepL table 5 [] [] [true,true] [true,true] 2 (by simpa using FPair) n [false] ([true,true,true,false] ++ X)
  have h := join0 first (by simpa only [List.nil_append] using sw)
  simpa only [fromF,rep_add,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h

theorem exhaust (n : Nat) (X : List Bool) : ∃ t, 0<t ∧ run0 table t (fromF n X) = some (toA n X) := by
  induction n generalizing X with
  | zero => exact ⟨6,by decide,join0 (clearPair X) (consumePair X)⟩
  | succ n ih =>
    have h0 : fromF (n+1) X = fromF n ([true,true] ++ X) := by
      unfold fromF pairs
      rw [rep_add [true,true] (n+1) 1]
      simp only [rep,List.append_nil,List.append_assoc]
    obtain ⟨a,ha,h1⟩ := ih ([true,true] ++ X)
    obtain ⟨b,hb,h2⟩ := ih ([true,false] ++ X)
    have h3 := join0 (join0 (join0 h1 (carryStart n X)) (carrySweep n X)) h2
    have h4 := join0 h3 (carryEnd n X)
    refine ⟨a+3+(3+2*n)+b+2,by omega,?_⟩
    rw [h0]
    exact h4

def fam (n : Nat) : Z0 := ⟨3,[false,false,true,true,true] ++ pairs (n+1) ++ [false],[]⟩

theorem enterPrefix (n : Nat) : run0 table 9 (fam n) = some ⟨5,[true,true,true,true] ++ pairs (n+1) ++ [false],[false]⟩ := by rfl

theorem enter (n : Nat) : run0 table (2*(n+3)) ⟨5,[true,true,true,true] ++ pairs (n+1) ++ [false],[false]⟩ = some (fromF (n+2) [false]) := by
  have h := sweepL table 5 [] [] [true,true] [true,true] 2 (by simpa using FPair) (n+3) [false] [false]
  simpa only [fromF,rep,List.nil_append,List.cons_append,List.append_assoc] using h

theorem finish (n : Nat) : run0 table 3 (toA (n+2) [false]) = some (fam (n+1)) := by rfl

theorem growth (n : Nat) : ∃ t, 0<t ∧ run0 table t (fam n) = some (fam (n+1)) := by
  obtain ⟨t,ht,h⟩ := exhaust (n+2) [false]
  exact ⟨9+2*(n+3)+t+3,by omega,join0 (join0 (join0 (enterPrefix n) (enter n)) h) (finish n)⟩

theorem entry : run0 table 26 ⟨0,[],[]⟩ = some (fam 0) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table fam (fun _ => True) 0 trivial 26 entry
    (fun n _ => by obtain ⟨t,ht,h⟩ := growth n; exact ⟨n+1,t,trivial,ht,h⟩) m hm
end BB6Coverage.Agent31Pump.Raw112Counter27
