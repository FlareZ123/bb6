import Raw54RADigitCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RA.M88
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RACounter BB6.Agent8Raw54.RADigit
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (A [false,true,true]) := by rfl
theorem inc (T : List Bool) : run0 table 8 (A ([false,false,false,false,false,false,false,false] ++ T)) = some (A ([false,true,true,false,false,false,false,false] ++ T)) := by rfl
theorem empty : run0 table 36 (A [false,true,true]) = some (A ([false,false,false,false,false,false,false,false] ++ [false,true,true])) := by rfl
theorem carryStop (n : Nat) (T : List Bool) : run0 table (28*n+36) ⟨0,[false,false],([false,true,true,false,false,false,false,false] ++ (rep [false,true,true,false,false,false,false,false] n ++ ([false,false,false,false,false,false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ := by
  have h0 : run0 table (20*n) ⟨0,[false,false],([false,true,true,false,false,false,false,false] ++ (rep [false,true,true,false,false,false,false,false] n ++ ([false,false,false,false,false,false,false,false] ++ T)))⟩ = some ⟨0,([false] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false])),([false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ T)⟩ := by
    exact sweepR table 0 [false] [false,true,true,false,false,false,false,false] [false,true,true,false,false,false,false,false] [true,true,true,true,true,true,true,true] 20 (fun _ _ => rfl) n [false] ([false,false,false,false,false,false,false,false] ++ T)
  have h1 : run0 table 26 ⟨0,([false] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false])),([false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ T)⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false])),([false,true,true,false,false,false,false,false] ++ T)⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (8*n) ⟨4,([true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false])),([false,true,true,false,false,false,false,false] ++ T)⟩ = some ⟨4,[true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,false,false,false,false,false,false,false] 8 (fun _ _ => rfl) n [false] ([false,true,true,false,false,false,false,false] ++ T)
  have g2 := join0 g1 h2
  have h3 : run0 table 10 ⟨4,[true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ ([false,true,true,false,false,false,false,false] ++ T)))⟩ := by rfl
  have g3 := join0 g2 h3
  rw [show (20*n)+26+(8*n)+10=28*n+36 by omega] at g3
  exact g3
theorem carryEnd (n : Nat) : run0 table (28*n+64) ⟨0,[false,false],([false,true,true,false,false,false,false,false] ++ (rep [false,true,true,false,false,false,false,false] n ++ [false,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ := by
  have h0 : run0 table (20*n) ⟨0,[false,false],([false,true,true,false,false,false,false,false] ++ (rep [false,true,true,false,false,false,false,false] n ++ [false,true,true]))⟩ = some ⟨0,([false] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false])),[false,true,true,false,false,false,false,false,false,true,true]⟩ := by
    exact sweepR table 0 [false] [false,true,true,false,false,false,false,false] [false,true,true,false,false,false,false,false] [true,true,true,true,true,true,true,true] 20 (fun _ _ => rfl) n [false] [false,true,true]
  have h1 : run0 table 46 ⟨0,([false] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false])),[false,true,true,false,false,false,false,false,false,true,true]⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false])),[false,true,true]⟩ := by rfl
  have g1 := join0 h0 h1
  have h2 : run0 table (8*n) ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ (rep [true,true,true,true,true,true,true,true] n ++ [false])),[false,true,true]⟩ = some ⟨4,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ := by
    exact sweepL table 4 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,false,false,false,false,false,false,false] 8 (fun _ _ => rfl) n [false] [false,true,true]
  have g2 := join0 g1 h2
  have h3 : run0 table 18 ⟨4,[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false],([] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ = some ⟨0,[false,false],([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ (rep [false,false,false,false,false,false,false,false] n ++ [false,true,true]))⟩ := by rfl
  have g3 := join0 g2 h3
  rw [show (20*n)+46+(8*n)+18=28*n+64 by omega] at g3
  exact g3
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  neverGrow table [false,false,false,false,false,false,false,false] [false,true,true,false,false,false,false,false] [false,true,true] 28 36 64 8 36 (by decide) (by decide) (by decide) (by decide) entry inc empty carryStop carryEnd m hm
#print axioms never
end BB6.Agent8Raw54.RA.M88
