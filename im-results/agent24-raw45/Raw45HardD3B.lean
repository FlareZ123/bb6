import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45HardD3B
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- The B1=0RE/C1=0RE/E1=0RC Raw45 depth-three residual.
    A1, E0, F0, F1 remain arbitrary. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,1⟩)
  | 4,true  => some (some ⟨false,true,2⟩)
  | _,_ => none

def phase (n : Nat) : Z0 :=
  ⟨3,rep [false,false] (n+2) ++ [true,true],[]⟩

private theorem dblock (L R : List Bool) :
    run0 table 2 ⟨3,[false,false]++L,R⟩ =
      some ⟨3,L,[true,true]++R⟩ := by rfl

private theorem turn (R : List Bool) :
    run0 table 2 ⟨3,[true,true],[true,true]++R⟩ =
      some ⟨4,[true,false,true,true],R⟩ := by rfl

private theorem epair (L R : List Bool) :
    run0 table 2 ⟨4,[true]++L,[true,true]++R⟩ =
      some ⟨4,[true,false,false]++L,R⟩ := by rfl

private theorem finish (L : List Bool) :
    run0 table 2 ⟨4,[true]++L,[]⟩ =
      some ⟨3,[false,false,false]++L,[]⟩ := by rfl

private theorem commute_zero (n : Nat) :
    [false]++rep [false,false] n =
      rep [false,false] n++[false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      [false]++rep [false,false] (n+1) =
        [false,false]++([false]++rep [false,false] n) := by rfl
      _ = [false,false]++(rep [false,false] n++[false]) := by rw [ih]
      _ = rep [false,false] (n+1)++[false] := by rfl

/-- Moving the last zero through a pair-block makes two more blocks. -/
private theorem finish_shape (n : Nat) :
    [false,false,false]++rep [false,false] (n+1)++[false,true,true] =
      rep [false,false] ((n+1)+2)++[true,true] := by
  have hc := commute_zero (n+1)
  have hs := rep_snoc [false,false] (n+1)
  calc
    [false,false,false]++rep [false,false] (n+1)++[false,true,true] =
      [false,false]++([false]++rep [false,false] (n+1))++[false]++[true,true] := by
        simp only [List.append_assoc,List.cons_append,List.nil_append]
    _ = [false,false]++(rep [false,false] (n+1)++[false])++[false]++[true,true] := by rw [hc]
    _ = [false,false]++(rep [false,false] (n+1)++[false,false])++[true,true] := by
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    _ = [false,false]++([false,false]++rep [false,false] (n+1))++[true,true] := by rw [hs]
    _ = rep [false,false] ((n+1)+2)++[true,true] := by
      rfl

theorem entry : run0 table 9 ⟨0,[],[]⟩ = some (phase 0) := by rfl

/-- D0 paired left sweep, D1/B1 turn, E1/C1 paired right sweep,
    and E1/C0 turn add two permanent zeros per epoch. -/
theorem growth (n : Nat) :
    run0 table (4*n+10) (phase n) = some (phase (n+1)) := by
  have h1 : run0 table (2*(n+2)) (phase n) =
      some ⟨3,[true,true],rep [true,true] (n+2)⟩ := by
    simpa only [phase,List.nil_append,List.append_nil,List.append_assoc] using
      sweepL table 3 [] [] [false,false] [true,true] 2 dblock
        (n+2) [true,true] []
  have h2 : run0 table 2
      ⟨3,[true,true],rep [true,true] (n+2)⟩ =
      some ⟨4,[true,false,true,true],rep [true,true] (n+1)⟩ := by
    have hp : rep [true,true] (n+2) =
        [true,true]++rep [true,true] (n+1) := by
      rfl
    simpa only [hp] using turn (rep [true,true] (n+1))
  have h3 : run0 table (2*(n+1))
      ⟨4,[true,false,true,true],rep [true,true] (n+1)⟩ =
      some ⟨4,[true]++rep [false,false] (n+1)++[false,true,true],[]⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc,
                List.cons_append] using
      sweepR table 4 [true] [] [true,true] [false,false] 2 epair
        (n+1) [false,true,true] []
  have h4 : run0 table 2
      ⟨4,[true]++rep [false,false] (n+1)++[false,true,true],[]⟩ =
      some (phase (n+1)) := by
    have hf := finish (rep [false,false] (n+1)++[false,true,true])
    have hs := finish_shape n
    simpa only [phase,← List.append_assoc,hs] using hf
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have ht : ((2*(n+2)+2)+2*(n+1))+2=4*n+10 := by omega
  simpa only [ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 9 (fun n => 4*n+10) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent24Raw45HardD3B
