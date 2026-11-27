import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LEE0RAM69
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

/-- Blocks P=001, U=010010010100101001, V=010010100100101001.
    V and P rotate one cell to the left before the return sweep. -/
def P0 : List Bool := [false,true]
def V0 : List Bool := [true,false,false,true,false,true,false,false,true,false,false,true,false,true,false,false,true]
def P : List Bool := false::P0
def V : List Bool := false::V0
def U : List Bool := [false,true,false,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true]
def Pp : List Bool := P0++[false]
def Vp : List Bool := V0++[false]

inductive Phase where
  | p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8
  deriving DecidableEq

def next : Phase → Phase
  | .p0 => .p1
  | .p1 => .p2
  | .p2 => .p3
  | .p3 => .p4
  | .p4 => .p5
  | .p5 => .p6
  | .p6 => .p7
  | .p7 => .p8
  | .p8 => .p0

def tail : Phase → List Bool
  | .p0 => [false,false,true,false,false,true,false,true,false,true]
  | .p1 => [false,false,true,false,false,true,false,false,true,false]
  | .p2 => [false,false,true,false,true,false,false,true,false,true,false,false,true,false,false,true,false]
  | .p3 => [false,false,true,false,true,false,false,true,false,true,false,true,false,false,true,false,true,false,false,true,false,false,true,false]
  | .p4 => [false,false,true,false,true,false,false,true,false,false,true,false,false,false,true,false,true,false,false,true,false,false,true,false]
  | .p5 => [false,false,true,false,true,false,true,false,false,true,false,false,true,false,false,true,true,false,false,true,false,false,true,false]
  | .p6 => [false,false,true,false,false,true,false,false,false,true,false,false,true,false,false,true,true,false,false,true,false,false,true,false]
  | .p7 => [false,true,false,false,true,false,false,true,false,false,true,false,true,false,false,true,true,false,false,true,false,false,true,false]
  | .p8 => [false,true,false,false,true,false,false,true,false,false,true,false,true,false,false,true,false,false,false,true,false,false,true,false]

def turnCost : Phase → Nat
  | .p0 => 40
  | .p1 => 108
  | .p2 => 134
  | .p3 => 48
  | .p4 => 90
  | .p5 => 30
  | .p6 => 72
  | .p7 => 68
  | .p8 => 164

def extra (i : Phase) : List Bool := if i = .p8 then U else []
def advanceJ (j : Nat) (i : Phase) : Nat := if i = .p8 then j+1 else j

def sect (k j : Nat) (i : Phase) : Z0 :=
  ⟨0,[true,false],[false,true]++rep P k++rep U j++tail i⟩
def cost (k j : Nat) (i : Phase) : Nat := 8+3*k+30*j+turnCost i+34*j+7*k+7

private theorem enter (R : List Bool) :
    run0 table 8 ⟨0,[true,false],[false,true]++R⟩ =
      some ⟨1,[false]++P,[false,true]++R⟩ := by rfl
private theorem forwardP (L R : List Bool) :
    run0 table 3 ⟨1,[false]++L,[false,true]++P++R⟩ =
      some ⟨1,[false]++P++L,[false,true]++R⟩ := by rfl
private theorem forwardU (L R : List Bool) :
    run0 table 30 ⟨1,[false]++L,[false,true]++U++R⟩ =
      some ⟨1,[false]++V++L,[false,true]++R⟩ := by rfl
private theorem turn (i : Phase) (L : List Bool) :
    run0 table (turnCost i) ⟨1,[false,false]++L,[false,true]++tail i⟩ =
      some ⟨0,[true,false]++L,[false,true]++extra i++tail (next i)⟩ := by
  cases i <;> rfl
private theorem backV (L R : List Bool) :
    run0 table 34 ⟨0,[true,false]++Vp++L,[false,true]++R⟩ =
      some ⟨0,[true,false]++L,[false,true]++U++R⟩ := by rfl
private theorem backP (L R : List Bool) :
    run0 table 7 ⟨0,[true,false]++Pp++L,[false,true]++R⟩ =
      some ⟨0,[true,false]++L,[false,true]++P++R⟩ := by rfl
private theorem finish (R : List Bool) :
    run0 table 7 ⟨0,[true,false]++P0,[false,true]++R⟩ =
      some ⟨0,[true,false],[false,true]++P++R⟩ := by rfl

private theorem frame (k j : Nat) :
    [false]++rep V j++rep P k++P = [false,false]++rep Vp j++rep Pp k++P0 := by
  have hp : rep P k ++ [false] = [false] ++ rep Pp k :=
    (rotate false P0 k).symm
  have hv : rep V j ++ [false] = [false] ++ rep Vp j :=
    (rotate false V0 j).symm
  calc
    _ = [false]++rep V j++(rep P k++[false])++P0 := by
      simp only [P,List.append_assoc]; rfl
    _ = [false]++rep V j++([false]++rep Pp k)++P0 := by rw [hp]
    _ = [false]++(rep V j++[false])++rep Pp k++P0 := by simp only [List.append_assoc]
    _ = [false]++([false]++rep Vp j)++rep Pp k++P0 := by rw [hv]
    _ = _ := by simp only [List.append_assoc]; rfl

private theorem jappend (j : Nat) (i : Phase) :
    rep U j ++ extra i = rep U (advanceJ j i) := by
  cases i <;> simp [extra,advanceJ,rep_snoc,rep]

theorem growth (k j : Nat) (i : Phase) :
    run0 table (cost k j i) (sect k j i) =
      some (sect (k+1) (advanceJ j i) (next i)) := by
  have h1 := enter (rep P k++rep U j++tail i)
  have h2 := sweepR table 1 [false] [false,true] P P 3 forwardP k P (rep U j++tail i)
  have h3 := sweepR table 1 [false] [false,true] U V 30 forwardU j (rep P k++P) (tail i)
  have h12 := join0 (by simpa only [sect,List.append_assoc] using h1 :
      run0 table 8 (sect k j i) = some ⟨1,[false]++P,[false,true]++rep P k++rep U j++tail i⟩) (by simpa only [List.append_assoc] using h2 :
      run0 table (3*k) ⟨1,[false]++P,[false,true]++rep P k++rep U j++tail i⟩ =
        some ⟨1,[false]++rep P k++P,[false,true]++rep U j++tail i⟩)
  have h123 := join0 h12 (by simpa only [List.append_assoc] using h3 :
      run0 table (30*j) ⟨1,[false]++rep P k++P,[false,true]++rep U j++tail i⟩ =
        some ⟨1,[false]++rep V j++rep P k++P,[false,true]++tail i⟩)
  have h123' : run0 table (8+3*k+30*j) (sect k j i) =
      some ⟨1,[false,false]++rep Vp j++rep Pp k++P0,[false,true]++tail i⟩ := by
    simpa only [← List.append_assoc,frame] using h123
  have h4 := turn i (rep Vp j++rep Pp k++P0)
  have h4' : run0 table (turnCost i) ⟨1,[false,false]++rep Vp j++rep Pp k++P0,[false,true]++tail i⟩ =
      some ⟨0,[true,false]++rep Vp j++rep Pp k++P0,[false,true]++extra i++tail (next i)⟩ := by
    simpa only [List.append_assoc] using h4
  have h5 := sweepL table 0 [true,false] [false,true] Vp U 34 backV j (rep Pp k++P0) (extra i++tail (next i))
  have h5' : run0 table (34*j) ⟨0,[true,false]++rep Vp j++rep Pp k++P0,[false,true]++extra i++tail (next i)⟩ =
      some ⟨0,[true,false]++rep Pp k++P0,[false,true]++rep U j++extra i++tail (next i)⟩ := by
    simpa only [List.append_assoc] using h5
  have h6 := sweepL table 0 [true,false] [false,true] Pp P 7 backP k P0 (rep U j++extra i++tail (next i))
  have h6' : run0 table (7*k) ⟨0,[true,false]++rep Pp k++P0,[false,true]++rep U j++extra i++tail (next i)⟩ =
      some ⟨0,[true,false]++P0,[false,true]++rep P k++rep U j++extra i++tail (next i)⟩ := by
    simpa only [List.append_assoc] using h6
  have h7 := finish (rep P k++rep U j++extra i++tail (next i))
  have h7' : run0 table 7 ⟨0,[true,false]++P0,[false,true]++rep P k++rep U j++extra i++tail (next i)⟩ =
      some (sect (k+1) (advanceJ j i) (next i)) := by
    simpa only [sect,rep,List.append_assoc,← List.append_assoc (rep U j) (extra i) (tail (next i)),jappend] using h7
  exact join0 (join0 (join0 (join0 h123' h4') h5') h6') h7'

private theorem first : run0 table 989 ⟨0,[],[]⟩ = some (sect 6 1 .p0) := by rfl

def params : Nat → Nat × Nat × Phase
  | 0 => (6,1,.p0)
  | n+1 => let (k,j,i) := params n; (k+1,advanceJ j i,next i)
def family (n : Nat) : Z0 := let (k,j,i) := params n; sect k j i
def familyCost (n : Nat) : Nat := let (k,j,i) := params n; cost k j i

private theorem family_growth (n : Nat) :
    run0 table (familyCost n) (family n) = some (family (n+1)) := by
  unfold family familyCost
  rw [params]
  rcases h : params n with ⟨k,j,i⟩
  exact growth k j i

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 989 familyCost first
    (fun n => by unfold familyCost; rcases h : params n with ⟨k,j,i⟩; simp only [cost]; omega)
    family_growth m hm
#print axioms growth
#print axioms never
end BB6.Agent25Raw43B1LEE0RAM69
