import Raw54RADigitCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RA.M93
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RACounter BB6.Agent8Raw54.RADigit
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (A [false,true,true]) := by rfl
theorem inc (T : List Bool) : run0 table 8 (A ([false,false,false] ++ T)) = some (A ([false,true,true] ++ T)) := by rfl
theorem carryStop (n : Nat) (T : List Bool) : run0 table (8*n+16) ⟨0,[false,false],([false,true,true] ++ (rep [false,true] n ++ ([false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false] ++ (rep [false,false] n ++ ([false,true] ++ T)))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([false,true,true] ++ (rep [false,true] n ++ ([false,false] ++ T)))⟩ = some ⟨1,[false,true,false],([true,true] ++ (rep [false,true] n ++ ([false,false] ++ T)))⟩ := by rfl
  have h1 : run0 table (6*n) ⟨1,[false,true,false],([true,true] ++ (rep [false,true] n ++ ([false,false] ++ T)))⟩ = some ⟨1,([false] ++ (rep [true,true] n ++ [true,false])),([true,true,false,false] ++ T)⟩ := by
    exact sweepR table 1 [false] [true,true] [false,true] [true,true] 6 (fun _ _ => rfl) n [true,false] ([false,false] ++ T)
  have g1 := join0 h0 h1
  have h2 : run0 table 9 ⟨1,([false] ++ (rep [true,true] n ++ [true,false])),([true,true,false,false] ++ T)⟩ = some ⟨4,([true,true,true,true] ++ (rep [true,true] n ++ [true,false])),([true] ++ T)⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (2*n) ⟨4,([true,true,true,true] ++ (rep [true,true] n ++ [true,false])),([true] ++ T)⟩ = some ⟨4,[true,true,true,true,true,false],([] ++ (rep [false,false] n ++ ([true] ++ T)))⟩ := by
    exact sweepL table 4 [true,true,true,true] [] [true,true] [false,false] 2 (fun _ _ => rfl) n [true,false] ([true] ++ T)
  have g3 := join0 g2 h3
  have h4 : run0 table 6 ⟨4,[true,true,true,true,true,false],([] ++ (rep [false,false] n ++ ([true] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false] ++ (rep [false,false] n ++ ([true] ++ T)))⟩ := by rfl
  have g4 := join0 g3 h4
  have e5 : (⟨0,[false,false],([false,false,false,false] ++ (rep [false,false] n ++ ([true] ++ T)))⟩ : Z0) = ⟨0,[false,false],([false,false,false] ++ (rep [false,false] n ++ ([false,true] ++ T)))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false] ([true] ++ T) [false] false n)
  rw [e5] at g4
  rw [show 1+(6*n)+9+(2*n)+6=8*n+16 by omega] at g4
  exact g4
theorem carryEnd (n : Nat) : run0 table (8*n+16) ⟨0,[false,false],([false,true,true] ++ (rep [false,true] n ++ []))⟩ = some ⟨0,[false,false],([false,false,false] ++ (rep [false,false] n ++ [false,true]))⟩ := by
  have h0 : run0 table 1 ⟨0,[false,false],([false,true,true] ++ (rep [false,true] n ++ []))⟩ = some ⟨1,[false,true,false],([true,true] ++ (rep [false,true] n ++ []))⟩ := by rfl
  have h1 : run0 table (6*n) ⟨1,[false,true,false],([true,true] ++ (rep [false,true] n ++ []))⟩ = some ⟨1,([false] ++ (rep [true,true] n ++ [true,false])),[true,true]⟩ := by
    exact sweepR table 1 [false] [true,true] [false,true] [true,true] 6 (fun _ _ => rfl) n [true,false] []
  have g1 := join0 h0 h1
  have h2 : run0 table 9 ⟨1,([false] ++ (rep [true,true] n ++ [true,false])),[true,true]⟩ = some ⟨4,([true,true,true,true] ++ (rep [true,true] n ++ [true,false])),[true]⟩ := by rfl
  have g2 := join0 g1 h2
  have h3 : run0 table (2*n) ⟨4,([true,true,true,true] ++ (rep [true,true] n ++ [true,false])),[true]⟩ = some ⟨4,[true,true,true,true,true,false],([] ++ (rep [false,false] n ++ [true]))⟩ := by
    exact sweepL table 4 [true,true,true,true] [] [true,true] [false,false] 2 (fun _ _ => rfl) n [true,false] [true]
  have g3 := join0 g2 h3
  have h4 : run0 table 6 ⟨4,[true,true,true,true,true,false],([] ++ (rep [false,false] n ++ [true]))⟩ = some ⟨0,[false,false],([false,false,false,false] ++ (rep [false,false] n ++ [true]))⟩ := by rfl
  have g4 := join0 g3 h4
  have e5 : (⟨0,[false,false],([false,false,false,false] ++ (rep [false,false] n ++ [true]))⟩ : Z0) = ⟨0,[false,false],([false,false,false] ++ (rep [false,false] n ++ [false,true]))⟩ := congrArg (fun x => (⟨0,[false,false],x⟩ : Z0)) (moveCut [false,false,false] [true] [false] false n)
  rw [e5] at g4
  rw [show 1+(6*n)+9+(2*n)+6=8*n+16 by omega] at g4
  exact g4
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  neverPrefix table [false,false] [false,true] [false,false,false] [false,true,true] 8 16 8 16 entry inc carryStop (by intro k; simpa only [A,List.append_nil] using carryEnd k) m hm
#print axioms never
end BB6.Agent8Raw54.RA.M93
