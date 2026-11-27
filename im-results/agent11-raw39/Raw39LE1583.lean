import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39LE1583
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def ones (n : Nat) := rep [true] n
def zeros (n : Nat) := rep [false] n

theorem cStep (L R : List Bool) :
    run0 table 1 ⟨2,true::L,true::R⟩ = some ⟨2,true::false::L,R⟩ := by rfl

theorem cSweep (k : Nat) (L : List Bool) :
    run0 table k ⟨2,true::L,ones k⟩ = some ⟨2,true::(zeros k ++ L),[]⟩ := by
  simpa only [ones,zeros,List.nil_append,List.append_nil,List.cons_append,Nat.one_mul] using
    sweepR table 2 [true] [] [true] [false] 1 cStep k L []

theorem dStep (L R : List Bool) :
    run0 table 1 ⟨3,false::L,R⟩ = some ⟨3,L,true::R⟩ := by rfl

theorem dSweep (k : Nat) (L : List Bool) :
    run0 table k ⟨3,zeros k ++ L,[]⟩ = some ⟨3,L,ones k⟩ := by
  simpa only [ones,zeros,List.nil_append,List.append_nil,Nat.one_mul] using
    sweepL table 3 [] [] [false] [true] 1 dStep k L []

theorem big (k : Nat) (L : List Bool) :
    run0 table (2*k+8) ⟨0,false::L,false::ones (k+1)⟩ =
      some ⟨0,true::false::true::L,ones (k+2)⟩ := by
  have h0 : run0 table 2 ⟨0,false::L,false::ones (k+1)⟩ =
      some ⟨2,true::true::true::L,ones k⟩ := by rfl
  have h1 := cSweep k (true::true::L)
  have h2 : run0 table 2 ⟨2,true::(zeros k ++ (true::true::L)),[]⟩ =
      some ⟨3,zeros (k+3) ++ (true::true::L),[]⟩ := by rfl
  have h3 := dSweep (k+3) (true::true::L)
  have h4 : run0 table 1 ⟨3,true::true::L,ones (k+3)⟩ =
      some ⟨0,true::false::true::L,ones (k+2)⟩ := by rfl
  have H := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  rw [show 2+k+2+(k+3)+1=2*k+8 by omega] at H
  exact H

theorem short0 (n : Nat) (L : List Bool) :
    run0 table 9 ⟨0,([true,false,true,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L),ones (8*n+37)⟩ =
      some ⟨0,([false,false,false,true,true,false,false,false,false,false,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L),false::ones (8*n+37)⟩ := by rfl

theorem short1 (n : Nat) (L : List Bool) :
    run0 table 35 ⟨0,([true,false,true,false,false,true,true,false,false,false,false,false,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L),ones (8*n+38)⟩ =
      some ⟨0,([false,false,false,false,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L),false::ones (8*n+38)⟩ := by rfl

theorem short2 (n : Nat) (L : List Bool) :
    run0 table 9 ⟨0,([true,false,true,false,false,false,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L),ones (8*n+39)⟩ =
      some ⟨0,([false,false,false,true,true,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L),false::ones (8*n+39)⟩ := by rfl

theorem short3 (n : Nat) (L : List Bool) :
    run0 table 123 ⟨0,([true,false,true,false,false,true,true,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L),ones (8*n+40)⟩ =
      some ⟨0,([false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L),false::ones (8*n+40)⟩ := by rfl

theorem short4 (n : Nat) (L : List Bool) :
    run0 table 9 ⟨0,([true,false,true,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L),ones (8*n+41)⟩ =
      some ⟨0,([false,false,false,true,true,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L),false::ones (8*n+41)⟩ := by rfl

theorem short5 (n : Nat) (L : List Bool) :
    run0 table 35 ⟨0,([true,false,true,false,false,true,true,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L),ones (8*n+42)⟩ =
      some ⟨0,([false,false,false,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L),false::ones (8*n+42)⟩ := by rfl

theorem short6 (n : Nat) (L : List Bool) :
    run0 table 9 ⟨0,([true,false,true,false,false,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L),ones (8*n+43)⟩ =
      some ⟨0,([false,false,false,true,true,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L),false::ones (8*n+43)⟩ := by rfl

theorem short7 (n : Nat) (L : List Bool) :
    run0 table 119 ⟨0,([true,false,true,false,false,true,true,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L),ones (8*n+44)⟩ =
      some ⟨0,([false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,true,true,false,false,false,true,false,false,false,true,false,false,false] ++ L),false::ones (8*n+44)⟩ := by rfl

theorem return_cycle (n : Nat) (L : List Bool) :
    run0 table (1028+128*n) ⟨0,([false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L),false::ones (8*n+36)⟩ =
      some ⟨0,([false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,true,true,false,false,false,true,false,false,false,true,false,false,false] ++ L),false::ones (8*n+44)⟩ := by
  have h0 := big (8*n+35) ([false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L)
  have h1 := short0 n L
  have h2 := big (8*n+36) ([false,false,true,true,false,false,false,false,false,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L)
  have h3 := short1 n L
  have h4 := big (8*n+37) ([false,false,false,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L)
  have h5 := short2 n L
  have h6 := big (8*n+38) ([false,false,true,true,false,true,true,false,false,true,true,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ L)
  have h7 := short3 n L
  have h8 := big (8*n+39) ([false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L)
  have h9 := short4 n L
  have h10 := big (8*n+40) ([false,false,true,true,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L)
  have h11 := short5 n L
  have h12 := big (8*n+41) ([false,false,false,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L)
  have h13 := short6 n L
  have h14 := big (8*n+42) ([false,false,true,true,false,true,true,false,false,true,true,false,false,true,true,false,false,true,true,false,true,true,false,false,false,true,false,false,false] ++ L)
  have h15 := short7 n L
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15
  rw [show (2*(8*n+35)+8) + 9 + (2*(8*n+36)+8) + 35 + (2*(8*n+37)+8) + 9 + (2*(8*n+38)+8) + 123 + (2*(8*n+39)+8) + 9 + (2*(8*n+40)+8) + 35 + (2*(8*n+41)+8) + 9 + (2*(8*n+42)+8) + 119 = 1028+128*n by omega] at H
  exact H

def family (n : Nat) : Z0 :=
  ⟨0,[false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,false,false,true,true,false,false,false] ++ rep [true,false,false,false,true,false,false,false] n ++ [true,false,false,false,true,false,false,false,true,false,false,false,true,false,false,true,true,false,false,true,true,false,false,false,false,false,false,true,true,false,false,false,false,false,false,true,true,false,false,true,true],false::ones (8*n+36)⟩

theorem entry : run0 table 3210 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : run0 table (1028+128*n) (family n) = some (family (n+1)) := by
  have H := return_cycle n (rep [true,false,false,false,true,false,false,false] n ++ [true,false,false,false,true,false,false,false,true,false,false,false,true,false,false,true,true,false,false,true,true,false,false,false,false,false,false,true,true,false,false,false,false,false,false,true,true,false,false,true,true])
  unfold family
  rw [show 8*(n+1)+36 = 8*n+44 by omega]
  simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3210 (fun n => 1028+128*n) entry (by intro n; omega) growth m hm

#print axioms return_cycle
#print axioms never
end BB6.Agent11Raw39LE1583
