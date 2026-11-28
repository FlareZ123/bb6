import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45HardD3A
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- The A1=0LE/B1=1RA/E1=1LA Raw45 depth-three residual.
    C1, E0, F0, F1 remain genuinely arbitrary. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,1⟩)
  | 4,true  => some (some ⟨true,false,0⟩)
  | _,_ => none

def rightWord (n : Nat) : List Bool :=
  rep [false,true] (2*n+1) ++ [false]
def phase (n : Nat) : Z0 := ⟨4,[true],rightWord n⟩

private theorem start (R : List Bool) :
    run0 table 2 ⟨4,[true],R⟩ =
      some ⟨1,[true,true],R⟩ := by rfl

private theorem bpair (L R : List Bool) :
    run0 table 2 ⟨1,[true]++L,[false,true]++R⟩ =
      some ⟨1,[true,true,true]++L,R⟩ := by rfl

private theorem bturn (L : List Bool) :
    run0 table 9 ⟨1,[true,true,true,true]++L,[false]⟩ =
      some ⟨4,[true,true,true,true,true,true,true]++L,[false]⟩ := by rfl

private theorem epair (L R : List Bool) :
    run0 table 2 ⟨4,[true,true,true]++L,R⟩ =
      some ⟨4,[true]++L,[false,true]++R⟩ := by rfl

private theorem commute_one (n : Nat) :
    rep [true,true] n ++ [true] = [true] ++ rep [true,true] n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      rep [true,true] (n+1) ++ [true] =
        [true,true] ++ (rep [true,true] n ++ [true]) := by rfl
      _ = [true,true] ++ ([true] ++ rep [true,true] n) := by rw [ih]
      _ = [true] ++ rep [true,true] (n+1) := by rfl

/-- Genuine blank entrance, at 10 original machine steps. -/
theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (phase 0) := by rfl

/-- Each orbit traverses two expanding alternating-word sweeps. -/
theorem growth (n : Nat) :
    run0 table (8*n+19) (phase n) = some (phase (n+1)) := by
  have h1 : run0 table 2 (phase n) =
      some ⟨1,[true,true],rightWord n⟩ := by
    exact start (rightWord n)
  have h2 : run0 table (2*(2*n+1))
      ⟨1,[true,true],rightWord n⟩ =
      some ⟨1,[true]++rep [true,true] (2*n+1)++[true],[false]⟩ := by
    simpa only [rightWord,List.nil_append,List.append_nil,
                List.append_assoc] using
      sweepR table 1 [true] [] [false,true] [true,true] 2 bpair
        (2*n+1) [true] [false]
  have hleft : [true]++rep [true,true] (2*n+1)++[true] =
      [true,true,true,true]++rep [true,true] (2*n) := by
    have hh : rep [true,true] (2*n+1) =
      [true,true]++rep [true,true] (2*n) := by
      rw [show 2*n+1=(2*n)+1 by omega]
      rfl
    rw [hh]
    have hc := commute_one (2*n)
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      congrArg (fun v : List Bool => [true,true,true]++v) hc
  have hright : [true]++rep [true,true] (2*n+3) =
      [true,true,true,true,true,true,true]++rep [true,true] (2*n) := by
    rw [show 2*n+3=3+(2*n) by omega]
    rfl
  have h3 : run0 table 9
      ⟨1,[true]++rep [true,true] (2*n+1)++[true],[false]⟩ =
      some ⟨4,[true]++rep [true,true] (2*n+3),[false]⟩ := by
    rw [hleft]
    simpa only [hright] using bturn (rep [true,true] (2*n))
  have h4 : run0 table (2*(2*n+3))
      ⟨4,[true]++rep [true,true] (2*n+3),[false]⟩ =
      some (phase (n+1)) := by
    have hw : rightWord (n+1) =
      rep [false,true] (2*n+3)++[false] := by
      unfold rightWord
      simp only [show 2*(n+1)+1=2*n+3 by omega]
    simpa only [phase,hw,List.nil_append,List.append_nil,
                List.append_assoc] using
      sweepL table 4 [true] [] [true,true] [false,true] 2 epair
        (2*n+3) [] [false]
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have ht : ((2+2*(2*n+1))+9)+2*(2*n+3)=8*n+19 := by omega
  simpa only [ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table phase 10 (fun n => 8*n+19) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent24Raw45HardD3A
