import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45M2
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Raw45: B1 = 0RC and C1 = 0RC; all other five unknown rows stay holes. -/
def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true  => some (some ⟨false, true, 2⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 2, true  => some (some ⟨false, true, 2⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true  => some (some ⟨true, true, 1⟩)
  | _, _ => none

def zeros (n : Nat) : List Bool := rep [false] n
def ones (n : Nat) : List Bool := rep [true] n
def phase (n : Nat) : Z0 := ⟨3,zeros (2*n+2)++[true,true],[]⟩

private theorem dstep (L R : List Bool) :
    run0 table 1 ⟨3,[false]++L,R⟩ =
      some ⟨3,L,[true]++R⟩ := by rfl

private theorem turn (R : List Bool) :
    run0 table 2 ⟨3,[true,true],[true,true]++R⟩ =
      some ⟨2,[true,false,true,true],R⟩ := by rfl

private theorem cstep (L R : List Bool) :
    run0 table 1 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,[true,false]++L,R⟩ := by rfl

private theorem finish (L : List Bool) :
    run0 table 2 ⟨2,[true]++L,[]⟩ =
      some ⟨3,[false,false,false]++L,[]⟩ := by rfl

theorem entry : run0 table 3 ⟨0,[],[]⟩ = some (phase 0) := by rfl

/-- Exact source recurrence with cost 4n+6 for every natural n. -/
theorem growth (n : Nat) :
    run0 table (4*n+6) (phase n) = some (phase (n+1)) := by
  have h1 : run0 table (2*n+2) (phase n) =
      some ⟨3,[true,true],ones (2*n+2)⟩ := by
    simpa only [phase,ones,zeros,List.nil_append,List.append_nil,Nat.one_mul] using
      sweepL table 3 [] [] [false] [true] 1 dstep (2*n+2) [true,true] []
  have h2 : run0 table 2 ⟨3,[true,true],ones (2*n+2)⟩ =
      some ⟨2,[true,false,true,true],ones (2*n)⟩ := by
    have ha : ones (2*n+2) = [true,true]++ones (2*n) := by
      rw [show 2*n+2=2+(2*n) by omega]
      rfl
    simpa only [ha] using turn (ones (2*n))
  have h3 : run0 table (2*n) ⟨2,[true,false,true,true],ones (2*n)⟩ =
      some ⟨2,[true]++zeros (2*n)++[false,true,true],[]⟩ := by
    simpa only [ones,zeros,List.nil_append,List.append_nil,
                Nat.one_mul,List.append_assoc] using
      sweepR table 2 [true] [] [true] [false] 1 cstep
        (2*n) [false,true,true] []
  have h4 : run0 table 2 ⟨2,[true]++zeros (2*n)++[false,true,true],[]⟩ =
      some (phase (n+1)) := by
    have hz : zeros (2*(n+1)+2) =
        [false,false,false,false]++zeros (2*n) := by
      rw [show 2*(n+1)+2=4+(2*n) by omega]
      rfl
    simpa only [phase,hz,List.append_assoc] using
      finish (zeros (2*n)++[false,true,true])
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have ht : ((2*n+2)+2+2*n)+2=4*n+6 := by omega
  simpa only [ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 3 (fun n => 4*n+6) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent24Raw45M2
