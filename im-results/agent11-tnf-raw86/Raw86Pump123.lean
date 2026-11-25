import SweepPumping
set_option maxRecDepth 100000
namespace BB6.Agent11Raw86Pump123
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun (q,s) =>
  match q.val,s with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true  => some (some ⟨false,false,1⟩)
  | 5,false => none
  | 5,true  => some (some ⟨false,false,1⟩)
  | _,_ => none
abbrev B (l r : List Bool) : Z0 := ⟨1,l,r⟩
abbrev C (l r : List Bool) : Z0 := ⟨2,l,r⟩
abbrev D (l r : List Bool) : Z0 := ⟨3,l,r⟩
abbrev Zs := rep [false]
abbrev Os := rep [true]
def family (n : Nat) : Z0 := B [] ([false,true,false]++Os (3*n+1))
theorem first : run0 table 9 ⟨0,[],[]⟩ = some (family 0) := by decide
theorem enter (R : List Bool) :
    run0 table 6 (B [] ([false,true,false,true]++R)) = some (C [true,true,true] ([true,true]++R)) := by rfl
theorem right_one (L R : List Bool) :
    run0 table 1 (C ([true]++L) ([true]++R)) = some (C ([true,false]++L) R) := by rfl
theorem turn (L : List Bool) :
    run0 table 2 (C ([true]++L) []) = some (D ([false,false,false]++L) []) := by rfl
theorem left_one (L R : List Bool) :
    run0 table 1 (D ([false]++L) R) = some (D L ([true]++R)) := by rfl
theorem finish (R : List Bool) :
    run0 table 4 (D [true,true] ([true,true]++R)) = some (B [] ([false,true,false]++[true]++R)) := by rfl
theorem growth (n : Nat) : run0 table (6*n+19) (family n) = some (family (n+1)) := by
  have h0 := enter (Os (3*n))
  have h1 := sweepR table 2 [true] [] [true] [false] 1 right_one (3*n+2) [true,true] []
  have h2 := turn (Zs (3*n+2)++[true,true])
  have h3 := sweepL table 3 [] [] [false] [true] 1 left_one (3*n+5) [true,true] []
  have h4 := finish (Os (3*n+3))
  simp only [List.nil_append,List.append_nil,Nat.one_mul] at h1 h3
  have a0 : run0 table 6 (family n) = some (C [true,true,true] (Os (3*n+2))) := by simpa only [family,rep,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,show 3*n+2=(3*n+1)+1 by omega] using h0
  have a2 : run0 table 2 (C ([true]++Zs (3*n+2)++[true,true]) []) = some (D (Zs (3*n+5)++[true,true]) []) := by simpa only [rep,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,show 3*n+5=(3*n+4)+1 by omega,show 3*n+4=(3*n+3)+1 by omega,show 3*n+3=(3*n+2)+1 by omega] using h2
  have a4 : run0 table 4 (D [true,true] (Os (3*n+5))) = some (family (n+1)) := by simpa only [family,rep,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,show 3*n+5=(3*n+4)+1 by omega,show 3*n+4=(3*n+3)+1 by omega,show 3*(n+1)+1=3*n+4 by omega] using h4
  have H := join0 (join0 (join0 (join0 a0 h1) a2) h3) a4
  rw [show 6*n+19=6+(3*n+2)+2+(3*n+5)+4 by omega]
  exact H
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 9 (fun n => 6*n+19)
    first (by intro n; omega) growth m hm
#print axioms first
#print axioms growth
#print axioms never
end BB6.Agent11Raw86Pump123
