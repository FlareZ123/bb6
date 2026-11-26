import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.ZeroRF13
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => none
  | _,_ => none
abbrev z : List Bool := [false,false,false,false,false,false,false,false,false,false,true,true]
abbrev p : List Bool := [false,false,false,false,false,false,false,true,true]
abbrev q : List Bool := [false,false,true,true]
abbrev w : List Bool := [false,true,true,true,true,true,true,true,true]
abbrev v : List Bool := [false,true,true,true]
abbrev u : List Bool := [false,true,true,true,true,true,true]
abbrev s : List Bool := [false,true,true,true,true,true]
abbrev j : List Bool := [false,false,false,false,false,true,true]
abbrev h : List Bool := [false,true,true,true,true,true,true,true,true,true,true]
abbrev k : List Bool := [false,false,false,false,false,false,false,false,true,true]
abbrev a : List Bool := [true,true,true,true,true,true,true]
abbrev b : List Bool := [true,true,true,true]
abbrev i : List Bool := [false,false,false,true,true]
abbrev one : List Bool := [true]
abbrev two : List Bool := [true,true]
abbrev base : List Bool := [false,true,true]
theorem prep (R : List Bool) : run0 table 21 ⟨0, base, z ++ R⟩ = some ⟨0, a, p ++ R⟩ := by rfl
theorem pStep (L R : List Bool) : run0 table 19 ⟨0, a ++ L, p ++ R⟩ = some ⟨0, a ++ w ++ L, R⟩ := by rfl
theorem qFirst (L R : List Bool) : run0 table 8 ⟨0, a ++ L, q ++ R⟩ = some ⟨0, b ++ u ++ L, R⟩ := by rfl
theorem qStep (L R : List Bool) : run0 table 8 ⟨0, b ++ L, q ++ R⟩ = some ⟨0, b ++ v ++ L, R⟩ := by rfl
theorem endEven (L : List Bool) : run0 table 8 ⟨0, b ++ L, two⟩ = some ⟨0, s ++ L, []⟩ := by rfl
theorem vFirst (L : List Bool) : run0 table 16 ⟨0, s ++ v ++ L, []⟩ = some ⟨0, s ++ L, j⟩ := by rfl
theorem vStep (L R : List Bool) : run0 table 16 ⟨0, s ++ v ++ L, j ++ R⟩ = some ⟨0, s ++ L, j ++ q ++ R⟩ := by rfl
theorem uStep (L R : List Bool) : run0 table 16 ⟨0, s ++ u ++ L, j ++ R⟩ = some ⟨0, w ++ L, j ++ q ++ R⟩ := by rfl
theorem wPrep (L R : List Bool) : run0 table 19 ⟨0, w ++ w ++ L, j ++ R⟩ = some ⟨0, h ++ L, k ++ q ++ R⟩ := by rfl
theorem wFirst (L R : List Bool) : run0 table 21 ⟨0, h ++ w ++ L, k ++ R⟩ = some ⟨0, h ++ L, z ++ j ++ R⟩ := by rfl
theorem wStep (L R : List Bool) : run0 table 21 ⟨0, h ++ w ++ L, z ++ R⟩ = some ⟨0, h ++ L, z ++ p ++ R⟩ := by rfl
theorem wLast (R : List Bool) : run0 table 21 ⟨0, h, z ++ R⟩ = some ⟨0, base, z ++ p ++ R⟩ := by rfl
theorem jFirst (L R : List Bool) : run0 table 16 ⟨0, a ++ L, j ++ R⟩ = some ⟨0, b ++ w ++ L, one ++ R⟩ := by rfl
theorem qStepOdd (L R : List Bool) : run0 table 6 ⟨0, b ++ L, one ++ q ++ R⟩ = some ⟨0, b ++ v ++ L, one ++ R⟩ := by rfl
theorem endOdd (L : List Bool) : run0 table 6 ⟨0, b ++ L, one⟩ = some ⟨0, v ++ v ++ L, []⟩ := by rfl
theorem vPrepOdd (L : List Bool) : run0 table 14 ⟨0, v ++ v ++ L, []⟩ = some ⟨0, s ++ L, i⟩ := by rfl
theorem vFirstOdd (L : List Bool) : run0 table 16 ⟨0, s ++ v ++ L, i⟩ = some ⟨0, s ++ L, j ++ two⟩ := by rfl
theorem wPrepOdd (L R : List Bool) : run0 table 16 ⟨0, s ++ w ++ L, j ++ R⟩ = some ⟨0, h ++ L, j ++ q ++ R⟩ := by rfl
theorem wFirstOdd (L R : List Bool) : run0 table 21 ⟨0, h ++ w ++ L, j ++ R⟩ = some ⟨0, h ++ L, z ++ q ++ R⟩ := by rfl
def even (n : Nat) : Z0 := ⟨0, base, z ++ (rep p (n+2)) ++ (rep q (n+2)) ++ two⟩
def odd (n : Nat) : Z0 := ⟨0, base, z ++ (rep p (n+2)) ++ j ++ (rep q (n+2))⟩
theorem entry : run0 table 664 ⟨0,[],[]⟩ = some (even 0) := by rfl
theorem evenToOdd (n : Nat) : run0 table (64*n+216) (even n) = some (odd n) := by
  have e0 : run0 table (21) ⟨0, base, z ++ (rep p (n+2)) ++ (rep q (n+2)) ++ two⟩ = some ⟨0, a, (rep p (n+3)) ++ (rep q (n+2)) ++ two⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (prep (rep p (n+2) ++ rep q (n+2) ++ two))
  have e1 : run0 table (19*(n+3)) ⟨0, a, (rep p (n+3)) ++ (rep q (n+2)) ++ two⟩ = some ⟨0, a ++ (rep w (n+3)), (rep q (n+2)) ++ two⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (sweepR table 0 a [] p w 19 (by intro L R; simpa only [List.nil_append] using pStep L R) (n+3) [] (rep q (n+2) ++ two))
  have e2 : run0 table (8) ⟨0, a ++ (rep w (n+3)), (rep q (n+2)) ++ two⟩ = some ⟨0, b ++ u ++ (rep w (n+3)), (rep q (n+1)) ++ two⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (qFirst (rep w (n+3)) (rep q (n+1) ++ two))
  have e3 : run0 table (8*(n+1)) ⟨0, b ++ u ++ (rep w (n+3)), (rep q (n+1)) ++ two⟩ = some ⟨0, b ++ (rep v (n+1)) ++ u ++ (rep w (n+3)), two⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (sweepR table 0 b [] q v 8 (by intro L R; simpa only [List.nil_append] using qStep L R) (n+1) (u ++ rep w (n+3)) two)
  have e4 : run0 table (8) ⟨0, b ++ (rep v (n+1)) ++ u ++ (rep w (n+3)), two⟩ = some ⟨0, s ++ (rep v (n+1)) ++ u ++ (rep w (n+3)), []⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (endEven (rep v (n+1) ++ u ++ rep w (n+3)))
  have e5 : run0 table (16) ⟨0, s ++ (rep v (n+1)) ++ u ++ (rep w (n+3)), []⟩ = some ⟨0, s ++ (rep v n) ++ u ++ (rep w (n+3)), j⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (vFirst (rep v n ++ u ++ rep w (n+3)))
  have e6 : run0 table (16*n) ⟨0, s ++ (rep v n) ++ u ++ (rep w (n+3)), j⟩ = some ⟨0, s ++ u ++ (rep w (n+3)), j ++ (rep q n)⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (sweepL table 0 s j v q 16 (by intro L R; simpa only [List.append_assoc] using vStep L R) n (u ++ rep w (n+3)) [])
  have e7 : run0 table (16) ⟨0, s ++ u ++ (rep w (n+3)), j ++ (rep q n)⟩ = some ⟨0, w ++ (rep w (n+3)), j ++ (rep q (n+1))⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (uStep (rep w (n+3)) (rep q n))
  have e8 : run0 table (19) ⟨0, w ++ (rep w (n+3)), j ++ (rep q (n+1))⟩ = some ⟨0, h ++ (rep w (n+2)), k ++ (rep q (n+2))⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (wPrep (rep w (n+2)) (rep q (n+1)))
  have e9 : run0 table (21) ⟨0, h ++ (rep w (n+2)), k ++ (rep q (n+2))⟩ = some ⟨0, h ++ (rep w (n+1)), z ++ j ++ (rep q (n+2))⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (wFirst (rep w (n+1)) (rep q (n+2)))
  have e10 : run0 table (21*(n+1)) ⟨0, h ++ (rep w (n+1)), z ++ j ++ (rep q (n+2))⟩ = some ⟨0, h, z ++ (rep p (n+1)) ++ j ++ (rep q (n+2))⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (sweepL table 0 h z w p 21 (by intro L R; simpa only [List.append_assoc] using wStep L R) (n+1) [] (j ++ rep q (n+2)))
  have e11 : run0 table (21) ⟨0, h, z ++ (rep p (n+1)) ++ j ++ (rep q (n+2))⟩ = some ⟨0, base, z ++ (rep p (n+2)) ++ j ++ (rep q (n+2))⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (wLast (rep p (n+1) ++ j ++ rep q (n+2)))
  have res := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 e0 e1) e2) e3) e4) e5) e6) e7) e8) e9) e10) e11
  have cost : ((21) + (19*(n+3)) + (8) + (8*(n+1)) + (8) + (16) + (16*n) + (16) + (19) + (21) + (21*(n+1)) + (21)) = 64*n+216 := by omega
  rw [cost] at res
  simpa only [even, odd, rep, List.append_assoc, List.nil_append, List.append_nil] using res
theorem oddToEven (n : Nat) : run0 table (62*n+258) (odd n) = some (even (n+1)) := by
  have e0 : run0 table (21) ⟨0, base, z ++ (rep p (n+2)) ++ j ++ (rep q (n+2))⟩ = some ⟨0, a, (rep p (n+3)) ++ j ++ (rep q (n+2))⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (prep (rep p (n+2) ++ j ++ rep q (n+2)))
  have e1 : run0 table (19*(n+3)) ⟨0, a, (rep p (n+3)) ++ j ++ (rep q (n+2))⟩ = some ⟨0, a ++ (rep w (n+3)), j ++ (rep q (n+2))⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (sweepR table 0 a [] p w 19 (by intro L R; simpa only [List.nil_append] using pStep L R) (n+3) [] (j ++ rep q (n+2)))
  have e2 : run0 table (16) ⟨0, a ++ (rep w (n+3)), j ++ (rep q (n+2))⟩ = some ⟨0, b ++ (rep w (n+4)), one ++ (rep q (n+2))⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (jFirst (rep w (n+3)) (rep q (n+2)))
  have e3 : run0 table (6*(n+2)) ⟨0, b ++ (rep w (n+4)), one ++ (rep q (n+2))⟩ = some ⟨0, b ++ (rep v (n+2)) ++ (rep w (n+4)), one⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (sweepR table 0 b one q v 6 (by intro L R; simpa only [List.append_assoc] using qStepOdd L R) (n+2) (rep w (n+4)) [])
  have e4 : run0 table (6) ⟨0, b ++ (rep v (n+2)) ++ (rep w (n+4)), one⟩ = some ⟨0, v ++ v ++ (rep v (n+2)) ++ (rep w (n+4)), []⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (endOdd (rep v (n+2) ++ rep w (n+4)))
  have e5 : run0 table (14) ⟨0, v ++ v ++ (rep v (n+2)) ++ (rep w (n+4)), []⟩ = some ⟨0, s ++ (rep v (n+2)) ++ (rep w (n+4)), i⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (vPrepOdd (rep v (n+2) ++ rep w (n+4)))
  have e6 : run0 table (16) ⟨0, s ++ (rep v (n+2)) ++ (rep w (n+4)), i⟩ = some ⟨0, s ++ (rep v (n+1)) ++ (rep w (n+4)), j ++ two⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (vFirstOdd (rep v (n+1) ++ rep w (n+4)))
  have e7 : run0 table (16*(n+1)) ⟨0, s ++ (rep v (n+1)) ++ (rep w (n+4)), j ++ two⟩ = some ⟨0, s ++ (rep w (n+4)), j ++ (rep q (n+1)) ++ two⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (sweepL table 0 s j v q 16 (by intro L R; simpa only [List.append_assoc] using vStep L R) (n+1) (rep w (n+4)) two)
  have e8 : run0 table (16) ⟨0, s ++ (rep w (n+4)), j ++ (rep q (n+1)) ++ two⟩ = some ⟨0, h ++ (rep w (n+3)), j ++ (rep q (n+2)) ++ two⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (wPrepOdd (rep w (n+3)) (rep q (n+1) ++ two))
  have e9 : run0 table (21) ⟨0, h ++ (rep w (n+3)), j ++ (rep q (n+2)) ++ two⟩ = some ⟨0, h ++ (rep w (n+2)), z ++ (rep q (n+3)) ++ two⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (wFirstOdd (rep w (n+2)) (rep q (n+2) ++ two))
  have e10 : run0 table (21*(n+2)) ⟨0, h ++ (rep w (n+2)), z ++ (rep q (n+3)) ++ two⟩ = some ⟨0, h, z ++ (rep p (n+2)) ++ (rep q (n+3)) ++ two⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (sweepL table 0 h z w p 21 (by intro L R; simpa only [List.append_assoc] using wStep L R) (n+2) [] (rep q (n+3) ++ two))
  have e11 : run0 table (21) ⟨0, h, z ++ (rep p (n+2)) ++ (rep q (n+3)) ++ two⟩ = some ⟨0, base, z ++ (rep p (n+3)) ++ (rep q (n+3)) ++ two⟩ := by
    simpa only [rep, List.append_assoc, List.nil_append, List.append_nil] using (wLast (rep p (n+2) ++ rep q (n+3) ++ two))
  have res := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 e0 e1) e2) e3) e4) e5) e6) e7) e8) e9) e10) e11
  have cost : ((21) + (19*(n+3)) + (16) + (6*(n+2)) + (6) + (14) + (16) + (16*(n+1)) + (16) + (21) + (21*(n+2)) + (21)) = 62*n+258 := by omega
  rw [cost] at res
  simpa only [odd, even, rep, List.append_assoc, List.nil_append, List.append_nil] using res
theorem epoch (n : Nat) : run0 table (126*n+474) (even n) = some (even (n+1)) := by
  have H := join0 (evenToOdd n) (oddToEven n)
  rw [show (64*n+216)+(62*n+258)=126*n+474 by omega] at H
  exact H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table even 664 (fun n => 126*n+474) entry (by intro n; omega) epoch m hm
#print axioms never
end BB6.Agent8Raw54.ZeroRF13
