import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45B1LA_A1LC_L1
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

/-- Exact one-hole Raw45 child, B1=0LA and A1=0LC.  E1 is the sole hole.
    Its E/F state conjugate has the hole at F1. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨true,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true  => some (some ⟨false,false,5⟩)
  | _,_ => none

/-- Three-bit tape tokens in head-nearest order. -/
def P : List Bool := [false,false,true]       -- 001
def B : List Bool := [false,true,false]       -- 010
def I : List Bool := [false,true,true]        -- 011
def Q : List Bool := [true,false,true]        -- 101
def C : List Bool := [false,false,false,false]
def U : List Bool := [false,false,false]
def V : List Bool := [false,false,false,false,true]
def ones (n : Nat) : List Bool := rep [true] n

/-- Odd and even sections at the leftmost E0 marker, with blank to the left. -/
def odd (n : Nat) : Z0 :=
  ⟨4,[false,true],rep P (n+1)++B++ones (n+1)⟩

def even (n : Nat) : Z0 :=
  ⟨4,[false,true],rep P (n+1)++C++ones (n+2)⟩

/-- From E0 with only one left marker, a four-step blank-frontier reset. -/
private theorem front (R : List Bool) :
    run0 table 4 ⟨4,[false,true],R⟩ =
      some ⟨1,[false,true],[false,true]++R⟩ := by rfl

/-- B0 C0 D1 consumes a 010 packet and leaves 101 behind the head. -/
private theorem bpacket (L R : List Bool) :
    run0 table 3 ⟨1,[false]++L,B++R⟩ =
      some ⟨1,[false]++Q++L,R⟩ := by rfl

/-- B0 C1 turns the odd right edge into E0. -/
private theorem bfinishOdd (L R : List Bool) :
    run0 table 2 ⟨1,[false]++L,[true,false]++R⟩ =
      some ⟨4,[false,true,true]++L,R⟩ := by rfl

/-- B0 C0 D0 D0 D1 B1 A1 C1 turns the even right edge into E0. -/
private theorem bfinishEven (L R : List Bool) :
    run0 table 8 ⟨1,[false,true]++L,U++R⟩ =
      some ⟨4,[false,true]++L,B++R⟩ := by rfl

/-- Seven-step left-turn on the odd 0111011 prefix, all tails preserved. -/
private theorem eprefix (L R : List Bool) :
    run0 table 7 ⟨4,[false,true,true,true,false,true,true]++L,R⟩ =
      some ⟨4,[false,true]++L,V++R⟩ := by rfl

/-- E0 F1 F0 A1 C1 exchanges each left 011 for right 001. -/
private theorem etoken (L R : List Bool) :
    run0 table 5 ⟨4,[false,true]++I++L,R⟩ =
      some ⟨4,[false,true]++L,P++R⟩ := by rfl

/-- Cyclic rotation, checked by a finite leading 01/001 = 010/01 identity. -/
private theorem bridgeOdd (m : Nat) :
    [false,true]++rep P m++B = rep B (m+1)++[true,false] := by
  induction m with
  | zero => rfl
  | succ m ih =>
      calc
        [false,true]++rep P (m+1)++B =
            B++([false,true]++rep P m++B) := by rfl
        _ = B++(rep B (m+1)++[true,false]) := by rw [ih]
        _ = rep B ((m+1)+1)++[true,false] := by rfl

private theorem bridgeEven (m : Nat) :
    [false,true]++rep P m++C = rep B (m+1)++U := by
  induction m with
  | zero => rfl
  | succ m ih =>
      calc
        [false,true]++rep P (m+1)++C =
            B++([false,true]++rep P m++C) := by rfl
        _ = B++(rep B (m+1)++U) := by rw [ih]
        _ = rep B ((m+1)+1)++U := by rfl

private theorem rightOdd (m : Nat) :
    [false,true]++(rep P m++B++ones m) =
      rep B (m+1)++[true,false]++ones m := by
  simpa only [List.append_assoc] using
    congrArg (fun l : List Bool => l++ones m) (bridgeOdd m)

private theorem rightEven (m : Nat) :
    [false,true]++(rep P m++C++ones (m+1)) =
      rep B (m+1)++U++ones (m+1) := by
  simpa only [List.append_assoc] using
    congrArg (fun l : List Bool => l++ones (m+1)) (bridgeEven m)

/-- Sweep rotation 101^m 1 = 1 011^m. -/
private theorem leftRotate (m : Nat) :
    rep Q m ++ [true] = [true] ++ rep I m := by
  exact (rotate true [false,true] m).symm

private theorem leftOdd (m : Nat) :
    [false,true,true]++rep Q (m+1)++[true] =
      [false,true,true,true,false,true,true]++rep I m := by
  rw [List.append_assoc,leftRotate]
  rfl

private theorem leftEven (m : Nat) :
    [false]++rep Q m++[true] = [false,true]++rep I m := by
  rw [List.append_assoc,leftRotate]
  rfl

/-- Real blank execution, not a shifted/oracle entrance. -/
theorem entry : run0 table 45 ⟨0,[],[]⟩ = some (odd 0) := by rfl

/-- Odd section -> even section: B right sweep, seven-step turn, E left sweep. -/
theorem odd_to_even (n : Nat) :
    run0 table (8*n+24) (odd n) = some (even n) := by
  have h1 : run0 table 4 (odd n) =
      some ⟨1,[false,true],rep B (n+2)++[true,false]++ones (n+1)⟩ := by
    have hb : [false,true]++(rep P (n+1)++B++ones (n+1)) =
        rep B (n+2)++[true,false]++ones (n+1) := by
      simpa only [show (n+1)+1=n+2 by omega] using rightOdd (n+1)
    simpa only [odd,hb] using front (rep P (n+1)++B++ones (n+1))
  have h2 : run0 table (3*(n+2))
      ⟨1,[false,true],rep B (n+2)++[true,false]++ones (n+1)⟩ =
      some ⟨1,[false]++rep Q (n+2)++[true],[true,false]++ones (n+1)⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using
      sweepR table 1 [false] [] B Q 3 bpacket
        (n+2) [true] ([true,false]++ones (n+1))
  have h3 : run0 table 2
      ⟨1,[false]++rep Q (n+2)++[true],[true,false]++ones (n+1)⟩ =
      some ⟨4,[false,true,true,true,false,true,true]++rep I (n+1),ones (n+1)⟩ := by
    have hl : [false,true,true]++rep Q (n+2)++[true] =
        [false,true,true,true,false,true,true]++rep I (n+1) := by
      simpa only [show (n+1)+1=n+2 by omega] using leftOdd (n+1)
    simpa only [hl,List.append_assoc] using
      bfinishOdd (rep Q (n+2)++[true]) (ones (n+1))
  have h4 : run0 table 7
      ⟨4,[false,true,true,true,false,true,true]++rep I (n+1),ones (n+1)⟩ =
      some ⟨4,[false,true]++rep I (n+1),V++ones (n+1)⟩ := by
    exact eprefix (rep I (n+1)) (ones (n+1))
  have h5 : run0 table (5*(n+1))
      ⟨4,[false,true]++rep I (n+1),V++ones (n+1)⟩ =
      some (even n) := by
    have hv : V++ones (n+1) = C++ones (n+2) := by rfl
    simpa only [even,hv,List.nil_append,List.append_nil,List.append_assoc] using
      sweepL table 4 [false,true] [] I P 5 etoken
        (n+1) [] (V++ones (n+1))
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  have ht : (((4+3*(n+2))+2)+7)+5*(n+1)=8*n+24 := by omega
  simpa only [ht] using H

/-- Even -> next odd: the fixed eight-step turnaround replaces odd prefix. -/
theorem even_to_odd (n : Nat) :
    run0 table (8*n+28) (even n) = some (odd (n+1)) := by
  have h1 : run0 table 4 (even n) =
      some ⟨1,[false,true],rep B (n+2)++U++ones (n+2)⟩ := by
    have hb : [false,true]++(rep P (n+1)++C++ones (n+2)) =
        rep B (n+2)++U++ones (n+2) := by
      simpa only [show (n+1)+1=n+2 by omega] using rightEven (n+1)
    simpa only [even,hb] using front (rep P (n+1)++C++ones (n+2))
  have h2 : run0 table (3*(n+2))
      ⟨1,[false,true],rep B (n+2)++U++ones (n+2)⟩ =
      some ⟨1,[false]++rep Q (n+2)++[true],U++ones (n+2)⟩ := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using
      sweepR table 1 [false] [] B Q 3 bpacket (n+2) [true] (U++ones (n+2))
  have h3 : run0 table 8
      ⟨1,[false]++rep Q (n+2)++[true],U++ones (n+2)⟩ =
      some ⟨4,[false,true]++rep I (n+2),B++ones (n+2)⟩ := by
    have hl := leftEven (n+2)
    simpa only [hl,List.append_assoc] using bfinishEven (rep I (n+2)) (ones (n+2))
  have h4 : run0 table (5*(n+2))
      ⟨4,[false,true]++rep I (n+2),B++ones (n+2)⟩ =
      some (odd (n+1)) := by
    simpa only [odd,show (n+1)+1=n+2 by omega,
                List.nil_append,List.append_nil,List.append_assoc] using
      sweepL table 4 [false,true] [] I P 5 etoken (n+2) [] (B++ones (n+2))
  have H := join0 (join0 (join0 h1 h2) h3) h4
  have ht : ((4+3*(n+2))+8)+5*(n+2)=8*n+28 := by omega
  simpa only [ht] using H

/-- Two alternating phases produce linear positive epoch cost and unbounded time. -/
theorem growth (n : Nat) :
    run0 table (16*n+52) (odd n) = some (odd (n+1)) := by
  have H := join0 (odd_to_even n) (even_to_odd n)
  have ht : (8*n+24)+(8*n+28)=16*n+52 := by omega
  simpa only [ht] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table odd 45 (fun n => 16*n+52) entry
    (fun n => by omega) growth m hm

theorem literal_cover (bound : Nat) : Cover (DecidedBelow bound) table :=
  Cover.leaf table (fun m hm => Or.inl (never m hm))

#print axioms entry
#print axioms odd_to_even
#print axioms even_to_odd
#print axioms growth
#print axioms never
#print axioms literal_cover
end BB6.Agent24Raw45B1LA_A1LC_L1
