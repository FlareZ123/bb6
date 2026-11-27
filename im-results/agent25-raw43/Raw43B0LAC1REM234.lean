import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0LAC1REM234
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none
def P : List Bool := [true,true,true,true,true]
def T : List Bool := [true,true,true]
def S (n : Nat) : Z0 := ⟨0,[],[false]++rep P (n+2)++T⟩
def cost (n : Nat) : Nat := 7+7*(n+1)+20+6+15*(n+3)
private theorem first : run0 table 100 ⟨0,[],[]⟩ = some (S 0) := by rfl
private theorem enter (R : List Bool) :
  run0 table 7 ⟨0,[],[false]++P++R⟩ = some ⟨0,[false]++P,[false]++R⟩ := by rfl
private theorem push (L R : List Bool) :
  run0 table 7 ⟨0,[false]++L,[false]++P++R⟩ = some ⟨0,[false]++P++L,[false]++R⟩ := by rfl
private theorem turn (L : List Bool) :
  run0 table 20 ⟨0,[false]++L,[false]++T⟩ = some ⟨0,[true,true]++P++L,[false,true]⟩ := by rfl
private theorem popTwo (L R : List Bool) :
  run0 table 6 ⟨0,[true,true]++L,[false]++R⟩ = some ⟨0,L,[false]++[true,true]++R⟩ := by rfl
private theorem pop (L R : List Bool) :
  run0 table 15 ⟨0,[]++P++L,[false]++R⟩ = some ⟨0,[]++L,[false]++P++R⟩ := by rfl
theorem growth (n : Nat) : run0 table (cost n) (S n) = some (S (n+1)) := by
  have h1 : run0 table 7 (S n) = some ⟨0,[false]++P,[false]++rep P (n+1)++T⟩ := by
    simpa only [S,rep,List.append_assoc] using enter (rep P (n+1)++T)
  have hL : rep P (n+1)++P = rep P (n+2) := rep_snoc P (n+1)
  have h2 := sweepR table 0 [false] [false] P P 7 push (n+1) P T
  have h2' : run0 table (7*(n+1)) ⟨0,[false]++P,[false]++rep P (n+1)++T⟩ =
      some ⟨0,[false]++rep P (n+2),[false]++T⟩ := by
    simpa only [List.append_assoc,hL] using h2
  have h3 := turn (rep P (n+2))
  have h4 := popTwo (P++rep P (n+2)) [true]
  have h4' : run0 table 6 ⟨0,[true,true]++P++rep P (n+2),[false,true]⟩ =
      some ⟨0,rep P (n+3),[false]++T⟩ := h4
  have h5 := sweepL table 0 [] [false] P P 15 pop (n+3) [] T
  have h5' : run0 table (15*(n+3)) ⟨0,rep P (n+3),[false]++T⟩ = some (S (n+1)) := by
    simpa only [S,List.nil_append,List.append_nil,Nat.add_assoc] using h5
  exact join0 (join0 (join0 (join0 h1 h2') h3) h4') h5'
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table S 100 cost first (fun n => by unfold cost; omega) growth m hm
#print axioms growth
#print axioms never
end BB6.Agent25Raw43B0LAC1REM234
