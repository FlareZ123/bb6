import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.E1RE.M290
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨5,[],([true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [false,true] ++ rep [false,true] n)⟩
theorem entry : run0 table 48 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (12*n+46) (family n) = some (family (n+1)) := by
  unfold family
  have h1 : run0 table (1) ⟨5,[],([true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [false,true] ++ rep [false,true] n)⟩ = some ⟨0,([true,true]),([false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [false,true] ++ rep [false,true] n)⟩ := by rfl
  have h2 : run0 table (4*n) ⟨0,([true,true]),([false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [false,true] ++ rep [false,true] n)⟩ = some ⟨0,([true] ++ rep [true,false,true,false] n ++ [true]),([false,true,false,true,false,true,false,true,false,false,true] ++ rep [false,true] n)⟩ := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using (sweepR table 0 [true] [false,true,false,true,false,true,false,true,false] [true,false,true,false] [true,false,true,false] 4 (fun _ _ => rfl) n ([true]) ([false,true] ++ rep [false,true] n))
  have g2 := join0 h1 h2
  have h3 : run0 table (10) ⟨0,([true] ++ rep [true,false,true,false] n ++ [true]),([false,true,false,true,false,true,false,true,false,false,true] ++ rep [false,true] n)⟩ = some ⟨0,([false,true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),([true] ++ rep [false,true] n)⟩ := by rfl
  have g3 := join0 g2 h3
  have h4 : run0 table (2*n) ⟨0,([false,true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),([true] ++ rep [false,true] n)⟩ = some ⟨0,([false] ++ rep [false,true] n ++ [true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),([true])⟩ := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using (sweepR table 0 [false] [true] [false,true] [false,true] 2 (fun _ _ => rfl) n ([true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]) [])
  have g4 := join0 g3 h4
  have h5 : run0 table (12) ⟨0,([false] ++ rep [false,true] n ++ [true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),([true])⟩ = some ⟨5,([true,false,true,false,true] ++ rep [false,true] n ++ [true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),([true])⟩ := by rfl
  have g5 := join0 g4 h5
  have h6 : run0 table (2*n) ⟨5,([true,false,true,false,true] ++ rep [false,true] n ++ [true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),([true])⟩ = some ⟨5,([true,false,true,false,true,true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),(rep [true,false] n ++ [true])⟩ := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using (sweepL table 5 [true,false,true,false,true] [] [false,true] [true,false] 2 (fun _ _ => rfl) n ([true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]) ([true]))
  have g6 := join0 g5 h6
  have h7 : run0 table (9) ⟨5,([true,false,true,false,true,true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),(rep [true,false] n ++ [true])⟩ = some ⟨5,([true,false,true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),([false,true,false] ++ rep [true,false] n ++ [true])⟩ := by rfl
  have g7 := join0 g6 h7
  have h8 : run0 table (4*n) ⟨5,([true,false,true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),([false,true,false] ++ rep [true,false] n ++ [true])⟩ = some ⟨5,([true,false,true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false] n ++ [false,true,false] ++ rep [true,false] n ++ [true])⟩ := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using (sweepL table 5 [true,false,true,false,true,false,true,false,true,false,true,false] [] [true,false,true,false] [true,false,true,false] 4 (fun _ _ => rfl) n ([true]) ([false,true,false] ++ rep [true,false] n ++ [true]))
  have g8 := join0 g7 h8
  have h9 : run0 table (14) ⟨5,([true,false,true,false,true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false] n ++ [false,true,false] ++ rep [true,false] n ++ [true])⟩ = some ⟨5,[],([true,false,true,false,true,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [false,true,false] ++ rep [true,false] n ++ [true])⟩ := by rfl
  have g9 := join0 g8 h9
  rw [show 1+4*n+10+2*n+12+2*n+9+4*n+14 = 12*n+46 by omega] at g9
  have rot (k : Nat) : [false] ++ rep [true,false] k ++ [true] = [false,true] ++ rep [false,true] k := by
    calc
      _ = (rep [false,true] k ++ [false]) ++ [true] := congrArg (fun x => x ++ [true]) (rotate false [true] k)
      _ = rep [false,true] k ++ [false,true] := by rw [List.append_assoc]; rfl
      _ = _ := rep_snoc [false,true] k
  have tail : ([false,true,false] ++ rep [true,false] n ++ [true]) = [false,true,false,true] ++ rep [false,true] n := by
    change [false,true] ++ ([false] ++ rep [true,false] n ++ [true]) = _
    rw [rot]
    rfl
  simp only [List.append_assoc] at g9 ⊢
  simp only [rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] at g9 ⊢
  have rt := tail
  simp only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] at rt
  rw [rt] at g9
  exact g9
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := never_of_growth table family 48 (fun n => 12*n+46) entry (by intro n; omega) growth m hm
#print axioms never
end BB6.Agent8Raw54.E1RE.M290
