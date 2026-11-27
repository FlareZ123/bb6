import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent31Raw55REM459
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def z (n : Nat) := rep [false] n
def o (n : Nat) := rep [true] n
def family (k : Nat) : Z0 := ⟨0,[false,false]++o (k+1),false::o (k+6)⟩
def cost (k : Nat) := 2*k+23
theorem first : run0 table 36 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (k : Nat) : run0 table (cost k) (family k) = some (family (k+1)) := by
  have a : run0 table 3 (family k) = some ⟨4,[true,false,true,true,false]++o (k+1),o (k+4)⟩ := by rfl
  have b := sweepR table 4 [true,false] [] [true] [false] 1 (fun _ _ => rfl) (k+4) ([true,true,false]++o (k+1)) []
  simp only [Nat.one_mul,List.append_nil,List.nil_append] at b
  have c : run0 table 2 ⟨4,[true,false]++z (k+4)++([true,true,false]++o (k+1)),[]⟩ =
      some ⟨5,z (k+8)++([true,true,false]++o (k+1)),[]⟩ := by
    simp only [z,rep,List.append_assoc,List.cons_append,List.nil_append]
    rfl
  have d := sweepL table 5 [] [] [false] [true] 1 (fun _ _ => rfl) (k+8) ([true,true,false]++o (k+1)) []
  simp only [Nat.one_mul,List.nil_append,List.append_nil] at d
  have e : run0 table 6 ⟨5,[true,true,false]++o (k+1),o (k+8)⟩ = some (family (k+1)) := by rfl
  have h := join0 (join0 (join0 (join0 a b) c) d) e
  unfold cost
  rw [show 3+(k+4)+2+(k+8)+6=2*k+23 by omega] at h
  exact h
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 36 cost first (by intro k; unfold cost; omega) growth m hm
#print axioms never
end BB6.Agent31Raw55REM459
