import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45M1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw45: B1 = 0LD, C1 = 0RC, with five independent undefined rows. -/
def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true  => some (some ⟨false, false, 3⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 2, true  => some (some ⟨false, true, 2⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨true, true, 1⟩)
  | _, _ => none

def zeros (n : Nat) : List Bool := rep [false] n
def ones (n : Nat) : List Bool := rep [true] n

def phase (n : Nat) : Z0 := ⟨3,zeros (n+2)++ones (n+2),[]⟩

private theorem dstep (L R : List Bool) :
    run0 table 1 ⟨3,[false]++L,R⟩ =
      some ⟨3,L,[true]++R⟩ := by rfl

/-- D1 B1 D1 B0: the first right 1 is temporarily erased and restored. -/
private theorem turn (L R : List Bool) :
    run0 table 4 ⟨3,[true,true]++L,[true,true]++R⟩ =
      some ⟨2,[true,true,true,true]++L,R⟩ := by rfl

private theorem cstep (L R : List Bool) :
    run0 table 1 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,[true,false]++L,R⟩ := by rfl

private theorem finish (L : List Bool) :
    run0 table 2 ⟨2,[true]++L,[]⟩ =
      some ⟨3,[false,false,false]++L,[]⟩ := by rfl

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (phase 0) := by rfl

/-- Exact positive epoch length 2n+8, for every n. -/
theorem growth (n : Nat) :
    run0 table (2*n+8) (phase n) = some (phase (n+1)) := by
  have h1 : run0 table (n+2) (phase n) =
      some ⟨3,ones (n+2),ones (n+2)⟩ := by
    simpa only [phase,ones,zeros,List.nil_append,List.append_nil,Nat.one_mul] using
      sweepL table 3 [] [] [false] [true] 1 dstep (n+2) (ones (n+2)) []
  have h2 : run0 table 4 ⟨3,ones (n+2),ones (n+2)⟩ =
      some ⟨2,ones (n+4),ones n⟩ := by
    have ha : ones (n+2) = [true,true]++ones n := by
      rfl
    have hb : ones (n+4) = [true,true,true,true]++ones n := by
      rfl
    simpa only [ha,hb] using turn (ones n) (ones n)
  have h3 : run0 table n ⟨2,ones (n+4),ones n⟩ =
      some ⟨2,[true]++zeros n++ones (n+3),[]⟩ := by
    have ha : ones (n+4) = [true]++ones (n+3) := by
      rfl
    simpa only [ha,ones,zeros,List.nil_append,List.append_nil,
                Nat.one_mul,List.append_assoc] using
      sweepR table 2 [true] [] [true] [false] 1 cstep n (ones (n+3)) []
  have h4 : run0 table 2 ⟨2,[true]++zeros n++ones (n+3),[]⟩ =
      some (phase (n+1)) := by
    simpa only [phase,zeros,ones,rep,List.append_assoc,List.cons_append,List.nil_append] using
      finish (zeros n++ones (n+3))
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have ht : ((n+2)+4+n)+2=2*n+8 := by omega
  simpa only [ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 3 (fun n => 2*n+8) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent24Raw45M1
