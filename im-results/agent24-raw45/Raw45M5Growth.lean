import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45M5
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw45's B1=1LB, C1=1RC child; the other five rows remain arbitrary. -/
def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true  => some (some ⟨true, false, 1⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 2, true  => some (some ⟨true, true, 2⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨true, true, 1⟩)
  | _, _ => none

def ones (n : Nat) : List Bool := rep [true] n
def phase (n : Nat) : Z0 := ⟨3,[false,false]++ones (3*n+2),[]⟩

private theorem ones_snoc (n : Nat) : ones n ++ [true] = ones (n+1) := by
  change rep [true] n ++ [true] = rep [true] (n+1)
  calc
    rep [true] n ++ [true] = [true] ++ rep [true] n := rep_snoc [true] n
    _ = rep [true] (n+1) := by
      rfl

private theorem dstart (L : List Bool) :
    run0 table 2 ⟨3,[false,false]++L,[]⟩ =
      some ⟨3,L,[true,true]⟩ := by rfl

private theorem dturn (L : List Bool) :
    run0 table 1 ⟨3,[true]++L,[true,true]⟩ =
      some ⟨1,[true,true]++L,[true]⟩ := by rfl

private theorem bstep (L R : List Bool) :
    run0 table 1 ⟨1,[true]++L,R⟩ =
      some ⟨1,L,[true]++R⟩ := by rfl

private theorem bturn (R : List Bool) :
    run0 table 1 ⟨1,[],[true]++R⟩ =
      some ⟨2,[true,true],R⟩ := by rfl

private theorem cstep (L R : List Bool) :
    run0 table 1 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,[true,true]++L,R⟩ := by rfl

private theorem finish (L : List Bool) :
    run0 table 2 ⟨2,[true]++L,[]⟩ =
      some ⟨3,[false,false]++[true]++L,[]⟩ := by rfl

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (phase 0) := by rfl

/-- The two-sided scan adds three permanent 1 cells per epoch. -/
theorem growth (n : Nat) :
    run0 table (6*n+12) (phase n) = some (phase (n+1)) := by
  have h1 : run0 table 2 (phase n) =
      some ⟨3,ones (3*n+2),[true,true]⟩ := by
    exact dstart (ones (3*n+2))
  have h2 : run0 table 1 ⟨3,ones (3*n+2),[true,true]⟩ =
      some ⟨1,ones (3*n+3),[true]⟩ := by
    have ha : ones (3*n+2) = [true]++ones (3*n+1) := by
      rfl
    have hb : ones (3*n+3) = [true,true]++ones (3*n+1) := by
      rfl
    simpa only [ha,hb] using dturn (ones (3*n+1))
  have h3 : run0 table (3*n+3) ⟨1,ones (3*n+3),[true]⟩ =
      some ⟨1,[],ones (3*n+4)⟩ := by
    have H := sweepL table 1 [] [] [true] [true] 1 bstep (3*n+3) [] [true]
    have hs : rep [true] (3*n+3)++[true] = ones (3*n+4) := by
      change ones (3*n+3)++[true] = ones (3*n+4)
      simpa only [show (3*n+3)+1=3*n+4 by omega] using
        ones_snoc (3*n+3)
    simpa only [Nat.one_mul,List.nil_append,List.append_nil,hs] using H
  have h4 : run0 table 1 ⟨1,[],ones (3*n+4)⟩ =
      some ⟨2,[true,true],ones (3*n+3)⟩ := by
    have ha : ones (3*n+4) = [true]++ones (3*n+3) := by
      rfl
    simpa only [ha] using bturn (ones (3*n+3))
  have h5 : run0 table (3*n+3) ⟨2,[true,true],ones (3*n+3)⟩ =
      some ⟨2,ones (3*n+5),[]⟩ := by
    have hp : [true]++ones (3*n+3)++[true] = ones (3*n+5) := by
      calc
        [true]++ones (3*n+3)++[true] =
          [true]++ones ((3*n+3)+1) := by rw [List.append_assoc,ones_snoc]
        _ = ones (3*n+5) := by
          simp only [show (3*n+3)+1=3*n+4 by omega]
          rfl
    have H := sweepR table 2 [true] [] [true] [true] 1 cstep
      (3*n+3) [true] []
    have H' : run0 table (3*n+3) ⟨2,[true,true],ones (3*n+3)⟩ =
        some ⟨2,[true]++ones (3*n+3)++[true],[]⟩ := by
      simpa only [ones,Nat.one_mul,List.nil_append,List.append_nil,List.cons_append] using H
    simpa only [hp] using H'
  have h6 : run0 table 2 ⟨2,ones (3*n+5),[]⟩ =
      some (phase (n+1)) := by
    have ha : ones (3*n+5) = [true]++ones (3*n+4) := by
      rfl
    have hb : phase (n+1) =
        ⟨3,[false,false]++[true]++ones (3*n+4),[]⟩ := by
      unfold phase
      rw [show 3*(n+1)+2=3*n+5 by omega,ha]
      simp only [List.append_assoc]
    simpa only [ha,hb,List.append_assoc] using finish (ones (3*n+4))
  have H := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
  have ht : (2+1+(3*n+3)+1+(3*n+3)+2) = 6*n+12 := by omega
  simpa only [ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 3 (fun n => 6*n+12) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent24Raw45M5
