import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45M3
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw45 B1=1LB, C1=0LD: two sweeps with a three-step right packet. -/
def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true  => some (some ⟨true, false, 1⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 2, true  => some (some ⟨false, false, 3⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨true, true, 1⟩)
  | _, _ => none

def ones (n : Nat) : List Bool := rep [true] n
def phase (n : Nat) : Z0 := ⟨3,[false,false]++ones (3*n+2),[]⟩

private theorem ones_snoc (n : Nat) : ones n ++ [true] = ones (n+1) := by
  change rep [true] n ++ [true] = rep [true] (n+1)
  calc
    rep [true] n ++ [true] = [true]++rep [true] n := rep_snoc [true] n
    _ = rep [true] (n+1) := by
      rw [show n+1=1+n by omega]
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

/-- C1,D1,B0 move one 1 to the left stack in exactly three steps. -/
private theorem ctoken (L R : List Bool) :
    run0 table 3 ⟨2,[true,true]++L,[true]++R⟩ =
      some ⟨2,[true,true,true]++L,R⟩ := by rfl

/-- C1,D1,B0,C0 close the right sweep at an implicit blank. -/
private theorem finish (L : List Bool) :
    run0 table 4 ⟨2,[true,true]++L,[]⟩ =
      some ⟨3,[false,false]++[true,true]++L,[]⟩ := by rfl

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (phase 0) := by rfl

/-- Recurrence cost 12n+20 with 3 extra 1s, for all n. -/
theorem growth (n : Nat) :
    run0 table (12*n+20) (phase n) = some (phase (n+1)) := by
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
    have hs : ones (3*n+3)++[true] = ones (3*n+4) := by
      rw [ones_snoc,show (3*n+3)+1=3*n+4 by omega]
    simpa only [ones,Nat.one_mul,List.nil_append,List.append_nil,hs] using H
  have h4 : run0 table 1 ⟨1,[],ones (3*n+4)⟩ =
      some ⟨2,[true,true],ones (3*n+3)⟩ := by
    have ha : ones (3*n+4) = [true]++ones (3*n+3) := by
      rfl
    simpa only [ha] using bturn (ones (3*n+3))
  have h5 : run0 table (3*(3*n+3)) ⟨2,[true,true],ones (3*n+3)⟩ =
      some ⟨2,[true,true]++ones (3*n+3),[]⟩ := by
    simpa only [ones,Nat.one_mul,List.nil_append,List.append_nil] using
      sweepR table 2 [true,true] [] [true] [true] 3 ctoken
        (3*n+3) [] []
  have h6 : run0 table 4 ⟨2,[true,true]++ones (3*n+3),[]⟩ =
      some (phase (n+1)) := by
    have ha : ones (3*n+5) = [true,true]++ones (3*n+3) := by
      rfl
    have hb : phase (n+1) =
        ⟨3,[false,false]++[true,true]++ones (3*n+3),[]⟩ := by
      unfold phase
      rw [show 3*(n+1)+2=3*n+5 by omega,ha]
    simpa only [hb] using finish (ones (3*n+3))
  have H := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
  have ht : ((((2+1)+(3*n+3))+1+3*(3*n+3))+4 = 12*n+20 := by omega
  simpa only [ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 3 (fun n => 12*n+20) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent24Raw45M3
