import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45M4
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw45's B1=1LB and C1=0RC child: leftward unary, rightward erasing. -/
def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true  => some (some ⟨true, false, 1⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 2, true  => some (some ⟨false, true, 2⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨true, true, 1⟩)
  | _, _ => none

def zeros (n : Nat) : List Bool := rep [false] n
def ones (n : Nat) : List Bool := rep [true] n
def phase (n : Nat) : Z0 := ⟨3,zeros (3*n+6)++[true],[]⟩

private theorem dstep (L R : List Bool) :
    run0 table 1 ⟨3,[false]++L,R⟩ =
      some ⟨3,L,[true]++R⟩ := by rfl

private theorem dturn (R : List Bool) :
    run0 table 1 ⟨3,[true],[true]++R⟩ =
      some ⟨1,[true,true],R⟩ := by rfl

private theorem bstep (L R : List Bool) :
    run0 table 1 ⟨1,[true]++L,R⟩ =
      some ⟨1,L,[true]++R⟩ := by rfl

private theorem bturn (R : List Bool) :
    run0 table 1 ⟨1,[],[true]++R⟩ =
      some ⟨2,[true,true],R⟩ := by rfl

private theorem cstep (L R : List Bool) :
    run0 table 1 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,[true,false]++L,R⟩ := by rfl

private theorem finish (L : List Bool) :
    run0 table 2 ⟨2,[true]++L,[]⟩ =
      some ⟨3,[false,false,false]++L,[]⟩ := by rfl

/-- The first 15 blank steps enter the stabilized one-left-marker phase. -/
theorem entry : run0 table 15 ⟨0,[],[]⟩ = some (phase 0) := by rfl

theorem growth (n : Nat) :
    run0 table (6*n+18) (phase n) = some (phase (n+1)) := by
  have h1 : run0 table (3*n+6) (phase n) =
      some ⟨3,[true],ones (3*n+6)⟩ := by
    simpa only [phase,zeros,ones,Nat.one_mul,List.nil_append,
                List.append_nil] using
      sweepL table 3 [] [] [false] [true] 1 dstep
        (3*n+6) [true] []
  have h2 : run0 table 1 ⟨3,[true],ones (3*n+6)⟩ =
      some ⟨1,[true,true],ones (3*n+5)⟩ := by
    have ha : ones (3*n+6) = [true]++ones (3*n+5) := by
      rfl
    simpa only [ha] using dturn (ones (3*n+5))
  have h3 : run0 table 2 ⟨1,[true,true],ones (3*n+5)⟩ =
      some ⟨1,[],[true,true]++ones (3*n+5)⟩ := by
    simpa only [ones,rep,Nat.one_mul,List.cons_append,List.nil_append,List.append_nil] using
      sweepL table 1 [] [] [true] [true] 1 bstep 2 [] (ones (3*n+5))
  have h4 : run0 table 1 ⟨1,[],[true,true]++ones (3*n+5)⟩ =
      some ⟨2,[true,true],ones (3*n+6)⟩ := by
    have ha : ones (3*n+6) = [true]++ones (3*n+5) := by
      rfl
    simpa only [ha,List.append_assoc,List.cons_append,List.nil_append] using bturn ([true]++ones (3*n+5))
  have h5 : run0 table (3*n+6) ⟨2,[true,true],ones (3*n+6)⟩ =
      some ⟨2,[true]++zeros (3*n+6)++[true],[]⟩ := by
    simpa only [ones,zeros,Nat.one_mul,List.nil_append,
                List.append_nil,List.cons_append] using
      sweepR table 2 [true] [] [true] [false] 1 cstep
        (3*n+6) [true] []
  have h6 : run0 table 2 ⟨2,[true]++zeros (3*n+6)++[true],[]⟩ =
      some (phase (n+1)) := by
    have ha : zeros (3*(n+1)+6) =
        [false,false,false]++zeros (3*n+6) := by
      rw [show 3*(n+1)+6=(3*n+6)+3 by omega]
      rfl
    simpa only [phase,ha,List.append_assoc,List.cons_append,List.nil_append] using
      finish (zeros (3*n+6)++[true])
  have H := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
  have ht : (3*n+6+1+2+1+(3*n+6)+2) = 6*n+18 := by omega
  simpa only [ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 15 (fun n => 6*n+18) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent24Raw45M4
