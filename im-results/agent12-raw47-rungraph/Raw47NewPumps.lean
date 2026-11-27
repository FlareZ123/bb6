import SweepPumping
import FAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent12Raw47Pumps
open BB6Coverage BB6Coverage.Agent31Pump
namespace H13006
def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨2, [true,false,false,true,true], rep [true,true,true,true,true] n⟩
theorem entry : run0 ctr 13 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (40*n+35) (family n) = some (family (n+1)) := by
  have h0 : run0 ctr (25*n) ⟨2, [true,false,false,true,true], rep [true,true,true,true,true] n⟩ = some ⟨2, [true,false,false,true,true] ++ rep [true,true,true,true,true] n, []⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 2 [true,false,false,true,true] [] [true,true,true,true,true] [true,true,true,true,true] 25 (by intro L R; rfl) n ([]) ([])
  have h1 : run0 ctr 6 ⟨2, [true,false,false,true,true] ++ rep [true,true,true,true,true] n, []⟩ = some ⟨3, [false,false,false,false,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ := rfl
  have h2 : run0 ctr (15*n) ⟨3, [false,false,false,false,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ = some ⟨3, [false,false,false,false,true,true,true], rep [true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 3 [false,false,false,false,true,true,true] [] [true,true,true,true,true] [true,true,true,true,true] 15 (by intro L R; rfl) n ([]) ([])
  have h3 : run0 ctr 29 ⟨3, [false,false,false,false,true,true,true], rep [true,true,true,true,true] n⟩ = some ⟨2, [true,false,false,true,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ := rfl
  have H := join0 h0 h1
  have H := join0 H h2
  have H := join0 H h3
  have hcost : 25*n+6+15*n+29 = 40*n+35 := by omega
  rw [hcost] at H
  have hlast : (⟨2, [true,false,false,true,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ : Z0) = ⟨2, [true,false,false,true,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ := by
    congr 1
  rw [hlast] at H
  simpa only [family, rep, List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 13 (fun n => 40*n+35) entry (fun k => by omega) growth m hm
#print axioms never
end H13006
namespace H13224
def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨3, [false,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩
theorem entry : run0 ctr 3 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (160*n+98) (family n) = some (family (n+1)) := by
  have h0 : run0 ctr 22 ⟨3, [false,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨2, [false,false,false,true,true], [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := rfl
  have h1 : run0 ctr (50*n) ⟨2, [false,false,false,true,true], [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨2, [false] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,false,true,true], [true,true]⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 2 [false] [true,true] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 50 (by intro L R; rfl) n ([false,false,true,true]) ([])
  have h2 : run0 ctr 8 ⟨2, [false] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,false,true,true], [true,true]⟩ = some ⟨3, [false,false,false,false,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,false,true,true], []⟩ := rfl
  have h3 : run0 ctr (30*n) ⟨3, [false,false,false,false,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,false,true,true], []⟩ = some ⟨3, [false,false,false,false,true,false,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 3 [false,false,false,false,true] [] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 30 (by intro L R; rfl) n ([false,false,true,true]) ([])
  have h4 : run0 ctr 4 ⟨3, [false,false,false,false,true,false,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨3, [true,false,false,true,true], [true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := rfl
  have h5 : run0 ctr (50*n) ⟨3, [true,false,false,true,true], [true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨3, [true,false] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,true,true], [true,true,true,true]⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 3 [true,false] [true,true,true,true] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 50 (by intro L R; rfl) n ([false,true,true]) ([])
  have h6 : run0 ctr 22 ⟨3, [true,false] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,true,true], [true,true,true,true]⟩ = some ⟨3, [false,false,false,false,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,true,true], []⟩ := rfl
  have h7 : run0 ctr (30*n) ⟨3, [false,false,false,false,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,true,true], []⟩ = some ⟨3, [false,false,false,false,true,true,true,true,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 3 [false,false,false,false,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 30 (by intro L R; rfl) n ([false,true,true]) ([])
  have h8 : run0 ctr 42 ⟨3, [false,false,false,false,true,true,true,true,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨3, [false,false,true,true], [true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := rfl
  have H := join0 h0 h1
  have H := join0 H h2
  have H := join0 H h3
  have H := join0 H h4
  have H := join0 H h5
  have H := join0 H h6
  have H := join0 H h7
  have H := join0 H h8
  have hcost : 22+50*n+8+30*n+4+50*n+22+30*n+42 = 160*n+98 := by omega
  rw [hcost] at H
  have hlast : (⟨3, [false,false,true,true], [true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ : Z0) = ⟨3, [false,false,true,true], [true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := by
    congr 1
  rw [hlast] at H
  simpa only [family, rep, List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 3 (fun n => 160*n+98) entry (fun k => by omega) growth m hm
#print axioms never
end H13224
namespace H16274
def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨3, [false,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩
theorem entry : run0 ctr 3 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (160*n+98) (family n) = some (family (n+1)) := by
  have h0 : run0 ctr 22 ⟨3, [false,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨2, [false,false,false,true,true], [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := rfl
  have h1 : run0 ctr (50*n) ⟨2, [false,false,false,true,true], [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨2, [false] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,false,true,true], [true,true]⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 2 [false] [true,true] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 50 (by intro L R; rfl) n ([false,false,true,true]) ([])
  have h2 : run0 ctr 8 ⟨2, [false] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,false,true,true], [true,true]⟩ = some ⟨3, [false,false,false,false,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,false,true,true], []⟩ := rfl
  have h3 : run0 ctr (30*n) ⟨3, [false,false,false,false,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,false,true,true], []⟩ = some ⟨3, [false,false,false,false,true,false,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 3 [false,false,false,false,true] [] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 30 (by intro L R; rfl) n ([false,false,true,true]) ([])
  have h4 : run0 ctr 4 ⟨3, [false,false,false,false,true,false,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨3, [true,false,false,true,true], [true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := rfl
  have h5 : run0 ctr (50*n) ⟨3, [true,false,false,true,true], [true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨3, [true,false] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,true,true], [true,true,true,true]⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 3 [true,false] [true,true,true,true] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 50 (by intro L R; rfl) n ([false,true,true]) ([])
  have h6 : run0 ctr 22 ⟨3, [true,false] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,true,true], [true,true,true,true]⟩ = some ⟨3, [false,false,false,false,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,true,true], []⟩ := rfl
  have h7 : run0 ctr (30*n) ⟨3, [false,false,false,false,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n ++ [false,true,true], []⟩ = some ⟨3, [false,false,false,false,true,true,true,true,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 3 [false,false,false,false,true,true,true,true] [] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 30 (by intro L R; rfl) n ([false,true,true]) ([])
  have h8 : run0 ctr 42 ⟨3, [false,false,false,false,true,true,true,true,false,true,true], rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨3, [false,false,true,true], [true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := rfl
  have H := join0 h0 h1
  have H := join0 H h2
  have H := join0 H h3
  have H := join0 H h4
  have H := join0 H h5
  have H := join0 H h6
  have H := join0 H h7
  have H := join0 H h8
  have hcost : 22+50*n+8+30*n+4+50*n+22+30*n+42 = 160*n+98 := by omega
  rw [hcost] at H
  have hlast : (⟨3, [false,false,true,true], [true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ : Z0) = ⟨3, [false,false,true,true], [true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := by
    congr 1
  rw [hlast] at H
  simpa only [family, rep, List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 3 (fun n => 160*n+98) entry (fun k => by omega) growth m hm
#print axioms never
end H16274
namespace H16326
def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨5, [true,false] ++ rep [true,true,true,true,true] n ++ [true,true,true,true], []⟩
theorem entry : run0 ctr 27 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (26*n+55) (family n) = some (family (n+1)) := by
  have h0 : run0 ctr 10 ⟨5, [true,false] ++ rep [true,true,true,true,true] n ++ [true,true,true,true], []⟩ = some ⟨5, [true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true], [false,true,true]⟩ := rfl
  have h1 : run0 ctr (5*n) ⟨5, [true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true], [false,true,true]⟩ = some ⟨5, [true,true,true,true,true,true], [false] ++ rep [false,false,false,false,false] n ++ [true,true]⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 5 [true,true] [false] [true,true,true,true,true] [false,false,false,false,false] 5 (by intro L R; rfl) n ([true,true,true,true]) ([true,true])
  have h2 : run0 ctr 18 ⟨5, [true,true,true,true,true,true], [false] ++ rep [false,false,false,false,false] n ++ [true,true]⟩ = some ⟨0, [false,true], [false,false,true,true,false,false,false] ++ rep [false,false,false,false,false] n ++ [true,true]⟩ := rfl
  have h3 : run0 ctr (21*n) ⟨0, [false,true], [false,false,true,true,false,false,false] ++ rep [false,false,false,false,false] n ++ [true,true]⟩ = some ⟨0, [false,true] ++ rep [true,true,true,true,true] n, [false,false,true,true,false,false,false,true,true]⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 0 [false,true] [false,false,true,true,false,false,false] [false,false,false,false,false] [true,true,true,true,true] 21 (by intro L R; rfl) n ([]) ([true,true])
  have h4 : run0 ctr 27 ⟨0, [false,true] ++ rep [true,true,true,true,true] n, [false,false,true,true,false,false,false,true,true]⟩ = some ⟨5, [true,false,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ := rfl
  have H := join0 h0 h1
  have H := join0 H h2
  have H := join0 H h3
  have H := join0 H h4
  have hcost : 10+5*n+18+21*n+27 = 26*n+55 := by omega
  rw [hcost] at H
  have hlast : (⟨5, [true,false,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ : Z0) = ⟨5, [true,false,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true], []⟩ := by
    congr 1
    ·
      calc
        [true,false,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n = [true,false,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true,true,true,true,true,true,true,true]) ([]) [true,true,true,true] true n)
        [true,false,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true] = [true,false,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true,true,true,true,true,true,true]) ([true]) [true,true,true,true] true n)
        [true,false,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true] = [true,false,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true,true,true,true,true,true]) ([true,true]) [true,true,true,true] true n)
        [true,false,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true] = [true,false,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true,true,true,true,true]) ([true,true,true]) [true,true,true,true] true n)
        [true,false,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true] = [true,false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true,true,true,true]) ([true,true,true,true]) [true,true,true,true] true n)
        [true,false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true] = [true,false,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true,true,true]) ([true,true,true,true,true]) [true,true,true,true] true n)
        [true,false,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true] = [true,false,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true,true]) ([true,true,true,true,true,true]) [true,true,true,true] true n)
        [true,false,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true,true] = [true,false,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true,true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true]) ([true,true,true,true,true,true,true]) [true,true,true,true] true n)
        [true,false,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true,true,true] = [true,false] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true,true,true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false]) ([true,true,true,true,true,true,true,true]) [true,true,true,true] true n)
        [true,false] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true,true,true,true] = [true,false,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true,true,true] := by
          symm; simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false]) ([true,true,true,true,true,true,true,true]) [true,true,true,true] true n)
        [true,false,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true,true,true] = [true,false,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true,true] := by
          symm; simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true]) ([true,true,true,true,true,true,true]) [true,true,true,true] true n)
        [true,false,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true,true] = [true,false,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true] := by
          symm; simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true,true]) ([true,true,true,true,true,true]) [true,true,true,true] true n)
        [true,false,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true] = [true,false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true] := by
          symm; simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true,true,true]) ([true,true,true,true,true]) [true,true,true,true] true n)
        [true,false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true] = [true,false,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true] := by
          symm; simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([true,false,true,true,true,true]) ([true,true,true,true]) [true,true,true,true] true n)
  rw [hlast] at H
  simpa only [family, rep, List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 27 (fun n => 26*n+55) entry (fun k => by omega) growth m hm
#print axioms never
end H16326
namespace H19433
def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨0, rep [true,true,true,true,true,true,true,true,true,true] n, [true,true,true,true,true]⟩
theorem entry : run0 ctr 10 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (204*n+142) (family n) = some (family (n+1)) := by
  have h0 : run0 ctr (18*n) ⟨0, rep [true,true,true,true,true,true,true,true,true,true] n, [true,true,true,true,true]⟩ = some ⟨0, [], [true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 0 [] [true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 18 (by intro L R; rfl) n ([]) ([])
  have h1 : run0 ctr 1 ⟨0, [], [true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨1, [true,true], [true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := rfl
  have h2 : run0 ctr (50*n) ⟨1, [true,true], [true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨1, [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true,true,true]⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 1 [true,true] [true,true,true,true] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 50 (by intro L R; rfl) n ([]) ([])
  have h3 : run0 ctr 20 ⟨1, [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true,true,true]⟩ = some ⟨3, [false,false,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true]⟩ := rfl
  have h4 : run0 ctr (18*n) ⟨3, [false,false,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true]⟩ = some ⟨3, [false,false,true,true,true,true], [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 3 [false,false,true,true,true,true] [true,true] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 18 (by intro L R; rfl) n ([]) ([])
  have h5 : run0 ctr 10 ⟨3, [false,false,true,true,true,true], [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨3, [true,false,true], [true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := rfl
  have h6 : run0 ctr (50*n) ⟨3, [true,false,true], [true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨3, [true,false,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true,true,true,true,true]⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 3 [true,false,true] [true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 50 (by intro L R; rfl) n ([]) ([])
  have h7 : run0 ctr 34 ⟨3, [true,false,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true,true,true,true,true]⟩ = some ⟨3, [false,false,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true]⟩ := rfl
  have h8 : run0 ctr (18*n) ⟨3, [false,false,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true]⟩ = some ⟨3, [false,false,true,true,true,true,true,true,true], [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 3 [false,false,true,true,true,true,true,true,true] [true,true] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 18 (by intro L R; rfl) n ([]) ([])
  have h9 : run0 ctr 17 ⟨3, [false,false,true,true,true,true,true,true,true], [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨1, [true,true], [true,true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ := rfl
  have h10 : run0 ctr (50*n) ⟨1, [true,true], [true,true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n⟩ = some ⟨1, [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true,true,true,true,true,true,true,true,true,true]⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 1 [true,true] [true,true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] [true,true,true,true,true,true,true,true,true,true] 50 (by intro L R; rfl) n ([]) ([])
  have h11 : run0 ctr 60 ⟨1, [true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true,true,true,true,true,true,true,true,true,true]⟩ = some ⟨0, [true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true,true,true,true]⟩ := rfl
  have H := join0 h0 h1
  have H := join0 H h2
  have H := join0 H h3
  have H := join0 H h4
  have H := join0 H h5
  have H := join0 H h6
  have H := join0 H h7
  have H := join0 H h8
  have H := join0 H h9
  have H := join0 H h10
  have H := join0 H h11
  have hcost : 18*n+1+50*n+20+18*n+10+50*n+34+18*n+17+50*n+60 = 204*n+142 := by omega
  rw [hcost] at H
  have hlast : (⟨0, [true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true,true,true,true]⟩ : Z0) = ⟨0, [true,true,true,true,true,true,true,true,true,true] ++ rep [true,true,true,true,true,true,true,true,true,true] n, [true,true,true,true,true]⟩ := by
    congr 1
  rw [hlast] at H
  simpa only [family, rep, List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 10 (fun n => 204*n+142) entry (fun k => by omega) growth m hm
#print axioms never
end H19433
namespace H19504
def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨1, [false] ++ rep [true,true,true,true,true] n ++ [true], []⟩
theorem entry : run0 ctr 1 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (16*n+15) (family n) = some (family (n+1)) := by
  have h0 : run0 ctr 2 ⟨1, [false] ++ rep [true,true,true,true,true] n ++ [true], []⟩ = some ⟨3, [false,false,true] ++ rep [true,true,true,true,true] n ++ [true], []⟩ := rfl
  have h1 : run0 ctr (11*n) ⟨3, [false,false,true] ++ rep [true,true,true,true,true] n ++ [true], []⟩ = some ⟨3, [false,false,true,true], rep [true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 3 [false,false,true] [] [true,true,true,true,true] [true,true,true,true,true] 11 (by intro L R; rfl) n ([true]) ([])
  have h2 : run0 ctr 8 ⟨3, [false,false,true,true], rep [true,true,true,true,true] n⟩ = some ⟨1, [true,true], [true,true,true,true] ++ rep [true,true,true,true,true] n⟩ := rfl
  have h3 : run0 ctr (5*n) ⟨1, [true,true], [true,true,true,true] ++ rep [true,true,true,true,true] n⟩ = some ⟨1, [true,true] ++ rep [true,true,true,true,true] n, [true,true,true,true]⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 1 [true,true] [true,true,true,true] [true,true,true,true,true] [true,true,true,true,true] 5 (by intro L R; rfl) n ([]) ([])
  have h4 : run0 ctr 5 ⟨1, [true,true] ++ rep [true,true,true,true,true] n, [true,true,true,true]⟩ = some ⟨1, [false,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ := rfl
  have H := join0 h0 h1
  have H := join0 H h2
  have H := join0 H h3
  have H := join0 H h4
  have hcost : 2+11*n+8+5*n+5 = 16*n+15 := by omega
  rw [hcost] at H
  have hlast : (⟨1, [false,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ : Z0) = ⟨1, [false,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true], []⟩ := by
    congr 1
    ·
      calc
        [false,true,true,true,true,true,true] ++ rep [true,true,true,true,true] n = [false,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([false,true,true,true,true,true]) ([]) [true,true,true,true] true n)
        [false,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true] = [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([false,true,true,true,true]) ([true]) [true,true,true,true] true n)
        [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true] = [false,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([false,true,true,true]) ([true,true]) [true,true,true,true] true n)
        [false,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true] = [false,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([false,true,true]) ([true,true,true]) [true,true,true,true] true n)
        [false,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true] = [false,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([false,true]) ([true,true,true,true]) [true,true,true,true] true n)
        [false,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true] = [false] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true] := by
          simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([false]) ([true,true,true,true,true]) [true,true,true,true] true n)
        [false] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true,true] = [false,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true] := by
          symm; simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([false]) ([true,true,true,true,true]) [true,true,true,true] true n)
        [false,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true,true] = [false,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true] := by
          symm; simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([false,true]) ([true,true,true,true]) [true,true,true,true] true n)
        [false,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true,true] = [false,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true] := by
          symm; simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([false,true,true]) ([true,true,true]) [true,true,true,true] true n)
        [false,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true,true] = [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true] := by
          symm; simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([false,true,true,true]) ([true,true]) [true,true,true,true] true n)
        [false,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true,true] = [false,true,true,true,true,true] ++ rep [true,true,true,true,true] n ++ [true] := by
          symm; simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using (moveCut ([false,true,true,true,true]) ([true]) [true,true,true,true] true n)
  rw [hlast] at H
  simpa only [family, rep, List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 1 (fun n => 16*n+15) entry (fun k => by omega) growth m hm
#print axioms never
end H19504
namespace H25862
def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨1, [false,true], rep [true,true,true,true,true] n⟩
theorem entry : run0 ctr 1 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (22*n+31) (family n) = some (family (n+1)) := by
  have h0 : run0 ctr (7*n) ⟨1, [false,true], rep [true,true,true,true,true] n⟩ = some ⟨1, [false,true] ++ rep [true,true,true,true,true] n, []⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 1 [false,true] [] [true,true,true,true,true] [true,true,true,true,true] 7 (by intro L R; rfl) n ([]) ([])
  have h1 : run0 ctr 16 ⟨1, [false,true] ++ rep [true,true,true,true,true] n, []⟩ = some ⟨4, [false,true,true,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ := rfl
  have h2 : run0 ctr (15*n) ⟨4, [false,true,true,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ = some ⟨4, [false,true,true,true,true,true], rep [true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 4 [false,true,true,true,true,true] [] [true,true,true,true,true] [true,true,true,true,true] 15 (by intro L R; rfl) n ([]) ([])
  have h3 : run0 ctr 15 ⟨4, [false,true,true,true,true,true], rep [true,true,true,true,true] n⟩ = some ⟨1, [false,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ := rfl
  have H := join0 h0 h1
  have H := join0 H h2
  have H := join0 H h3
  have hcost : 7*n+16+15*n+15 = 22*n+31 := by omega
  rw [hcost] at H
  have hlast : (⟨1, [false,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ : Z0) = ⟨1, [false,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ := by
    congr 1
  rw [hlast] at H
  simpa only [family, rep, List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 1 (fun n => 22*n+31) entry (fun k => by omega) growth m hm
#print axioms never
end H25862
namespace H25895
def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨1, [false,true], rep [true,true,true,true,true] n⟩
theorem entry : run0 ctr 1 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (24*n+31) (family n) = some (family (n+1)) := by
  have h0 : run0 ctr (9*n) ⟨1, [false,true], rep [true,true,true,true,true] n⟩ = some ⟨1, [false,true] ++ rep [true,true,true,true,true] n, []⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 1 [false,true] [] [true,true,true,true,true] [true,true,true,true,true] 9 (by intro L R; rfl) n ([]) ([])
  have h1 : run0 ctr 16 ⟨1, [false,true] ++ rep [true,true,true,true,true] n, []⟩ = some ⟨4, [false,true,true,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ := rfl
  have h2 : run0 ctr (15*n) ⟨4, [false,true,true,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ = some ⟨4, [false,true,true,true,true,true], rep [true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 4 [false,true,true,true,true,true] [] [true,true,true,true,true] [true,true,true,true,true] 15 (by intro L R; rfl) n ([]) ([])
  have h3 : run0 ctr 15 ⟨4, [false,true,true,true,true,true], rep [true,true,true,true,true] n⟩ = some ⟨1, [false,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ := rfl
  have H := join0 h0 h1
  have H := join0 H h2
  have H := join0 H h3
  have hcost : 9*n+16+15*n+15 = 24*n+31 := by omega
  rw [hcost] at H
  have hlast : (⟨1, [false,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ : Z0) = ⟨1, [false,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ := by
    congr 1
  rw [hlast] at H
  simpa only [family, rep, List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 1 (fun n => 24*n+31) entry (fun k => by omega) growth m hm
#print axioms never
end H25895
namespace H25918
def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def family (n : Nat) : Z0 := ⟨1, [false,true], rep [true,true,true,true,true] n⟩
theorem entry : run0 ctr 1 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (22*n+31) (family n) = some (family (n+1)) := by
  have h0 : run0 ctr (7*n) ⟨1, [false,true], rep [true,true,true,true,true] n⟩ = some ⟨1, [false,true] ++ rep [true,true,true,true,true] n, []⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepR ctr 1 [false,true] [] [true,true,true,true,true] [true,true,true,true,true] 7 (by intro L R; rfl) n ([]) ([])
  have h1 : run0 ctr 16 ⟨1, [false,true] ++ rep [true,true,true,true,true] n, []⟩ = some ⟨4, [false,true,true,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ := rfl
  have h2 : run0 ctr (15*n) ⟨4, [false,true,true,true,true,true] ++ rep [true,true,true,true,true] n, []⟩ = some ⟨4, [false,true,true,true,true,true], rep [true,true,true,true,true] n⟩ := by
    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweepL ctr 4 [false,true,true,true,true,true] [] [true,true,true,true,true] [true,true,true,true,true] 15 (by intro L R; rfl) n ([]) ([])
  have h3 : run0 ctr 15 ⟨4, [false,true,true,true,true,true], rep [true,true,true,true,true] n⟩ = some ⟨1, [false,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ := rfl
  have H := join0 h0 h1
  have H := join0 H h2
  have H := join0 H h3
  have hcost : 7*n+16+15*n+15 = 22*n+31 := by omega
  rw [hcost] at H
  have hlast : (⟨1, [false,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ : Z0) = ⟨1, [false,true], [true,true,true,true,true] ++ rep [true,true,true,true,true] n⟩ := by
    congr 1
  rw [hlast] at H
  simpa only [family, rep, List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using H
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 1 (fun n => 22*n+31) entry (fun k => by omega) growth m hm
#print axioms never
end H25918
end BB6.Agent12Raw47Pumps
