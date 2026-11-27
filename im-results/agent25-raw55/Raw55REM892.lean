import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent31Raw55REM892
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none
def I : List Bool := [false,false,true]
def O : List Bool := [true,true,false]
def family (k : Nat) : Z0 := ⟨0,[false,false,false,true]++rep I (3*k+2),[]⟩
def cost (k : Nat) := 18*k+46
theorem first : run0 table 28 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  let n := 3*k+2
  have a : run0 table 9 (family k) = some ⟨0,[false,false,false,true]++rep I (n+1),[true]⟩ := by rfl
  have b : run0 table 4 ⟨0,[false,false,false,true]++rep I (n+1),[true]⟩ = some ⟨0,[true]++rep I (n+2),[true,true]⟩ := by rfl
  have c := sweepL table 0 [true] [] I O 3 (fun _ _ => rfl) (n+2) [] [true,true]
  simp only [List.nil_append,List.append_nil] at c
  have d : run0 table 3 ⟨0,[true],rep O (n+2)++[true,true]⟩ = some ⟨0,[],rep O (n+3)++[true,true]⟩ := by rfl
  have e : run0 table 3 ⟨0,[],rep O (n+3)++[true,true]⟩ = some ⟨0,[false,false,false,true],rep O (n+2)++[true,true]⟩ := by rfl
  have f := sweepR table 0 [false] [] O I 3 (fun _ _ => rfl) (n+2) I [true,true]
  simp only [List.nil_append] at f
  have f' : run0 table (3*(n+2)) ⟨0,[false,false,false,true],rep O (n+2)++[true,true]⟩ = some ⟨0,[false,false,false,true]++rep I (n+2),[true,true]⟩ := by
    change run0 table (3*(n+2)) ⟨0,[false]++I,rep O (n+2)++[true,true]⟩ = some ⟨0,[false]++I++rep I (n+2),[true,true]⟩
    simpa only [List.append_assoc,rep_snoc] using f
  have g : run0 table 3 ⟨0,[false,false,false,true]++rep I (n+2),[true,true]⟩ = some (family (k+1)) := by
    unfold family n
    rw [show 3*(k+1)+2=3*k+2+2+1 by omega]
    rfl
  have h := join0 (join0 (join0 (join0 (join0 (join0 a b) c) d) e) f') g
  unfold cost
  dsimp only [n] at h
  rw [show 9+4+3*(3*k+2+2)+3+3+3*(3*k+2+2)+3=18*k+46 by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 28 cost first (by intro k; unfold cost; omega) growth m hm
#print axioms never
end BB6.Agent31Raw55REM892
