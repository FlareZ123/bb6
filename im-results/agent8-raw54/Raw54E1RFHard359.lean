import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.E1RF.M359
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none
def family (n m : Nat) : Z0 := ⟨5,[true,false,true,false] ++ rep [true,false,true,false] n ++ rep [false,true] m,[]⟩
theorem stepEpoch (n m : Nat) : run0 table (16*n+24) (family n (m+1)) = some (family (n+1) m) := by
  unfold family
  have h1 : run0 table (7) ⟨5,([true,false,true,false] ++ rep [true,false,true,false] n ++ [false,true] ++ rep [false,true] m),[]⟩ = some ⟨4,([false] ++ rep [true,false,true,false] n ++ [false,true] ++ rep [false,true] m),([false,true,true,true,true])⟩ := by rfl
  have h2 : run0 table (4*n) ⟨4,([false] ++ rep [true,false,true,false] n ++ [false,true] ++ rep [false,true] m),([false,true,true,true,true])⟩ = some ⟨4,([false,false,true] ++ rep [false,true] m),(rep [false,true,false,true] n ++ [false,true,true,true,true])⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepL table 4 [false] [] [true,false,true,false] [false,true,false,true] 4 (fun _ _ => rfl) n ([false,true] ++ rep [false,true] m) ([false,true,true,true,true]))
  have g2 := join0 h1 h2
  have h3 : run0 table (1) ⟨4,([false,false,true] ++ rep [false,true] m),(rep [false,true,false,true] n ++ [false,true,true,true,true])⟩ = some ⟨0,([false,true] ++ rep [false,true] m),([true] ++ rep [false,true,false,true] n ++ [false,true,true,true,true])⟩ := by rfl
  have g3 := join0 g2 h3
  have h4 : run0 table (4*n) ⟨0,([false,true] ++ rep [false,true] m),([true] ++ rep [false,true,false,true] n ++ [false,true,true,true,true])⟩ = some ⟨0,([false] ++ rep [false,true,false,true] n ++ [true] ++ rep [false,true] m),([true,false,true,true,true,true])⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepR table 0 [false] [true] [false,true,false,true] [false,true,false,true] 4 (fun _ _ => rfl) n ([true] ++ rep [false,true] m) ([false,true,true,true,true]))
  have g4 := join0 g3 h4
  have h5 : run0 table (4) ⟨0,([false] ++ rep [false,true,false,true] n ++ [true] ++ rep [false,true] m),([true,false,true,true,true,true])⟩ = some ⟨0,([true,false,true,false,true] ++ rep [false,true,false,true] n ++ [true] ++ rep [false,true] m),([true,true])⟩ := by rfl
  have g5 := join0 g4 h5
  have h6 : run0 table (4*n) ⟨0,([true,false,true,false,true] ++ rep [false,true,false,true] n ++ [true] ++ rep [false,true] m),([true,true])⟩ = some ⟨0,([true,false,true,false,true,true] ++ rep [false,true] m),(rep [true,false,true,false] n ++ [true,true])⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepL table 0 [true,false,true,false,true] [] [false,true,false,true] [true,false,true,false] 4 (fun _ _ => rfl) n ([true] ++ rep [false,true] m) ([true,true]))
  have g6 := join0 g5 h6
  have h7 : run0 table (5) ⟨0,([true,false,true,false,true,true] ++ rep [false,true] m),(rep [true,false,true,false] n ++ [true,true])⟩ = some ⟨4,([true] ++ rep [false,true] m),([false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true,true])⟩ := by rfl
  have g7 := join0 g6 h7
  have h8 : run0 table (4*n) ⟨4,([true] ++ rep [false,true] m),([false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true,true])⟩ = some ⟨4,([true] ++ rep [true,false,true,false] n ++ rep [false,true] m),([false,true,false,true,false,true,true])⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepR table 4 [true] [false,true,false,true,false] [true,false,true,false] [true,false,true,false] 4 (fun _ _ => rfl) n (rep [false,true] m) ([true,true]))
  have g8 := join0 g7 h8
  have h9 : run0 table (7) ⟨4,([true] ++ rep [true,false,true,false] n ++ rep [false,true] m),([false,true,false,true,false,true,true])⟩ = some ⟨5,([true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ rep [false,true] m),[]⟩ := by rfl
  have g9 := join0 g8 h9
  rw [show 7+4*n+1+4*n+4+4*n+5+4*n+7 = 16*n+24 by omega] at g9
  simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using g9
theorem repAdd (p : List Bool) (a b : Nat) : rep p (a+b) = rep p a ++ rep p b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [show a+1+b = (a+b)+1 by omega]
    simp only [rep, ih, List.append_assoc]
theorem repDouble (n : Nat) : rep [false,true,false,true] n = rep [false,true] (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = 2+2*n by omega, repAdd [false,true] 2 (2*n)]
    simp only [rep,ih,List.append_assoc]
    rfl
theorem resetEpoch (n : Nat) : run0 table (24*n+55) (family n 0) = some (family 0 (2*n+5)) := by
  unfold family
  have h1 : run0 table (7) ⟨5,([true,false,true,false] ++ rep [true,false,true,false] n),[]⟩ = some ⟨4,([false] ++ rep [true,false,true,false] n),([false,true,true,true,true])⟩ := by rfl
  have h2 : run0 table (4*n) ⟨4,([false] ++ rep [true,false,true,false] n),([false,true,true,true,true])⟩ = some ⟨4,([false]),(rep [false,true,false,true] n ++ [false,true,true,true,true])⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepL table 4 [false] [] [true,false,true,false] [false,true,false,true] 4 (fun _ _ => rfl) n [] ([false,true,true,true,true]))
  have g2 := join0 h1 h2
  have h3 : run0 table (2) ⟨4,([false]),(rep [false,true,false,true] n ++ [false,true,true,true,true])⟩ = some ⟨1,([true,true]),(rep [false,true,false,true] n ++ [false,true,true,true,true])⟩ := by rfl
  have g3 := join0 g2 h3
  have h4 : run0 table (4*n) ⟨1,([true,true]),(rep [false,true,false,true] n ++ [false,true,true,true,true])⟩ = some ⟨1,([true] ++ rep [true,false,true,false] n ++ [true]),([false,true,true,true,true])⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepR table 1 [true] [] [false,true,false,true] [true,false,true,false] 4 (fun _ _ => rfl) n ([true]) ([false,true,true,true,true]))
  have g4 := join0 g3 h4
  have h5 : run0 table (3) ⟨1,([true] ++ rep [true,false,true,false] n ++ [true]),([false,true,true,true,true])⟩ = some ⟨0,([true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),([true,true])⟩ := by rfl
  have g5 := join0 g4 h5
  have h6 : run0 table (4*n) ⟨0,([true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),([true,true])⟩ = some ⟨0,([true,false,true,false,true]),(rep [true,false,true,false] n ++ [true,true])⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepL table 0 [true,false,true,false] [] [true,false,true,false] [true,false,true,false] 4 (fun _ _ => rfl) n ([true]) ([true,true]))
  have g6 := join0 g5 h6
  have h7 : run0 table (7) ⟨0,([true,false,true,false,true]),(rep [true,false,true,false] n ++ [true,true])⟩ = some ⟨1,([true,true]),([false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true,true])⟩ := by rfl
  have g7 := join0 g6 h7
  have h8 : run0 table (4*n) ⟨1,([true,true]),([false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true,true])⟩ = some ⟨1,([true] ++ rep [true,false,true,false] n ++ [true]),([false,true,false,true,false,true,true])⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepR table 1 [true] [false,true,false,true,false] [true,false,true,false] [true,false,true,false] 4 (fun _ _ => rfl) n ([true]) ([true,true]))
  have g8 := join0 g7 h8
  have h9 : run0 table (7) ⟨1,([true] ++ rep [true,false,true,false] n ++ [true]),([false,true,false,true,false,true,true])⟩ = some ⟨0,([true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),[]⟩ := by rfl
  have g9 := join0 g8 h9
  have h10 : run0 table (4*n) ⟨0,([true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),[]⟩ = some ⟨0,([true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false] n)⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepL table 0 [true,false,true,false,true,false,true,false] [] [true,false,true,false] [true,false,true,false] 4 (fun _ _ => rfl) n ([true]) [])
  have g10 := join0 g9 h10
  have h11 : run0 table (11) ⟨0,([true,false,true,false,true,false,true,false,true]),(rep [true,false,true,false] n)⟩ = some ⟨1,([true,true]),([false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n)⟩ := by rfl
  have g11 := join0 g10 h11
  have h12 : run0 table (4*n) ⟨1,([true,true]),([false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n)⟩ = some ⟨1,([true] ++ rep [true,false,true,false] n ++ [true]),([false,true,false,true,false,true,false,true,false])⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using (sweepR table 1 [true] [false,true,false,true,false,true,false,true,false] [true,false,true,false] [true,false,true,false] 4 (fun _ _ => rfl) n ([true]) [])
  have g12 := join0 g11 h12
  have h13 : run0 table (18) ⟨1,([true] ++ rep [true,false,true,false] n ++ [true]),([false,true,false,true,false,true,false,true,false])⟩ = some ⟨5,([true,false,true,false,false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true]),[]⟩ := by rfl
  have g13 := join0 g12 h13
  rw [show 7+4*n+2+4*n+3+4*n+7+4*n+7+4*n+11+4*n+18 = 24*n+55 by omega] at g13
  have rot : [false] ++ rep [true,false,true,false] n ++ [true] = rep [false,true,false,true] n ++ [false,true] := by
    calc
      _ = (rep [false,true,false,true] n ++ [false]) ++ [true] := congrArg (fun x => x ++ [true]) (rotate false [true,false,true] n)
      _ = _ := by rw [List.append_assoc]; rfl
  have tail : [false,true,false,true,false,true,false,true,false] ++ rep [true,false,true,false] n ++ [true] = rep [false,true] (2*n+5) := by
    change [false,true,false,true,false,true,false,true] ++ ([false] ++ rep [true,false,true,false] n ++ [true]) = _
    rw [rot,repDouble]
    rw [show 2*n+5 = 4+(2*n+1) by omega, repAdd,repAdd]
    rfl
  simp only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] at tail g13
  rw [tail] at g13
  simpa only [rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using g13
def next (s : Nat × Nat) : Nat × Nat :=
  match s.2 with
  | 0 => (0,2*s.1+5)
  | m+1 => (s.1+1,m)
def cost (s : Nat × Nat) : Nat := if s.2=0 then 24*s.1+55 else 16*s.1+24
def orbit : Nat → Nat × Nat
  | 0 => (0,5)
  | n+1 => next (orbit n)
def states (k : Nat) : Z0 := family (orbit k).1 (orbit k).2
theorem orbitEntry : run0 table 64 ⟨0,[],[]⟩ = some (states 0) := by rfl
theorem epoch (s : Nat × Nat) : run0 table (cost s) (family s.1 s.2) = some (family (next s).1 (next s).2) := by
  rcases s with ⟨n,m⟩
  cases m with
  | zero => exact resetEpoch n
  | succ m => exact stepEpoch n m
theorem growth (k : Nat) : run0 table (cost (orbit k)) (states k) = some (states (k+1)) := epoch (orbit k)
theorem positive (s : Nat × Nat) : 0 < cost s := by unfold cost; split <;> omega
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table states 64 (fun k => cost (orbit k)) orbitEntry (fun k => positive (orbit k)) growth m hm
#print axioms never
end BB6.Agent8Raw54.E1RF.M359
