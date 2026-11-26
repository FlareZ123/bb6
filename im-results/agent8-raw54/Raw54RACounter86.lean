import Raw54RACounterCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RA.M86
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RACounter
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (A mark) := by rfl
theorem inc (T : List Bool) : run0 table 8 (A (zero ++ T)) = some (A (mark ++ T)) := by rfl
theorem carryStop (n : Nat) (T : List Bool) : run0 table (8*n+22) ⟨0,[false,false],([false,true,true] ++ (rep [true,true,true] n ++ ([false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false] ++ (rep [false,false,false] n ++ ([true,true,true] ++ T)))⟩ := by
  have h0 : run0 table (5*n) ⟨0,[false,false],([false,true,true] ++ (rep [true,true,true] n ++ ([false,false,false] ++ T)))⟩ = some ⟨0,([false] ++ (rep [true,true,true] n ++ [false])),([false,true,true,false,false,false] ++ T)⟩ := by
    exact sweepR table 0 [false] [false,true,true] [true,true,true] [true,true,true] 5 (fun _ _ => rfl) n [false] ([false,false,false] ++ T)
  have h1 : run0 table 18 ⟨0,([false] ++ (rep [true,true,true] n ++ [false])),([false,true,true,false,false,false] ++ T)⟩ = some ⟨4,([true,true,true] ++ (rep [true,true,true] n ++ [false])),([false,true,true,true] ++ T)⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (3*n) ⟨4,([true,true,true] ++ (rep [true,true,true] n ++ [false])),([false,true,true,true] ++ T)⟩ = some ⟨4,[true,true,true,false],([] ++ (rep [false,false,false] n ++ ([false,true,true,true] ++ T)))⟩ := by
    exact sweepL table 4 [true,true,true] [] [true,true,true] [false,false,false] 3 (fun _ _ => rfl) n [false] ([false,true,true,true] ++ T)
  have g2 := join0 g1 h2
  have h3 : run0 table 4 ⟨4,[true,true,true,false],([] ++ (rep [false,false,false] n ++ ([false,true,true,true] ++ T)))⟩ = some ⟨0,[false,false],([false,false] ++ (rep [false,false,false] n ++ ([false,true,true,true] ++ T)))⟩ := by rfl
  have g3 := join0 g2 h3
  have e4 : (⟨0,[false,false],([false,false] ++ (rep [false,false,false] n ++ ([false,true,true,true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([false,false,false] ++ (rep [false,false,false] n ++ ([true,true,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) ((moveCut [false,false] ([true,true,true] ++ T) [false,false] false n).symm)
  rw [e4] at g3
  rw [show (5*n)+18+(3*n)+4=8*n+22 by omega] at g3
  exact g3
theorem carryEnd (n : Nat) : run0 table (8*n+22) ⟨0,[false,false],([false,true,true] ++ (rep [true,true,true] n ++ []))⟩ = some ⟨0,[false,false],([false,false,false] ++ (rep [false,false,false] n ++ [true,true,true]))⟩ := by
  have h0 : run0 table (5*n) ⟨0,[false,false],([false,true,true] ++ (rep [true,true,true] n ++ []))⟩ = some ⟨0,([false] ++ (rep [true,true,true] n ++ [false])),[false,true,true]⟩ := by
    exact sweepR table 0 [false] [false,true,true] [true,true,true] [true,true,true] 5 (fun _ _ => rfl) n [false] []
  have h1 : run0 table 18 ⟨0,([false] ++ (rep [true,true,true] n ++ [false])),[false,true,true]⟩ = some ⟨4,([true,true,true] ++ (rep [true,true,true] n ++ [false])),[false,true,true,true]⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (3*n) ⟨4,([true,true,true] ++ (rep [true,true,true] n ++ [false])),[false,true,true,true]⟩ = some ⟨4,[true,true,true,false],([] ++ (rep [false,false,false] n ++ [false,true,true,true]))⟩ := by
    exact sweepL table 4 [true,true,true] [] [true,true,true] [false,false,false] 3 (fun _ _ => rfl) n [false] [false,true,true,true]
  have g2 := join0 g1 h2
  have h3 : run0 table 4 ⟨4,[true,true,true,false],([] ++ (rep [false,false,false] n ++ [false,true,true,true]))⟩ = some ⟨0,[false,false],([false,false] ++ (rep [false,false,false] n ++ [false,true,true,true]))⟩ := by rfl
  have g3 := join0 g2 h3
  have e4 : (⟨0,[false,false],([false,false] ++ (rep [false,false,false] n ++ [false,true,true,true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false] ++ (rep [false,false,false] n ++ [true,true,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) ((moveCut [false,false] [true,true,true] [false,false] false n).symm)
  rw [e4] at g3
  rw [show (5*n)+18+(3*n)+4=8*n+22 by omega] at g3
  exact g3
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  RACounter.never table 8 22 8 22 entry inc carryStop (by intro k; simpa only [A,mark,zero,one,List.append_nil] using carryEnd k) m hm
#print axioms never
end BB6.Agent8Raw54.RA.M86
