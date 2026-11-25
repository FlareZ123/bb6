import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4BlockCases.M1391
open BB6Coverage Agent31Pump
-- 1RB0RC_1RC---_0RD0LB_1LD1RE_1LF0RA_1LC1LE
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def ones (n : Nat) := rep [true] n
def alt (n : Nat) := rep [true,false] n
def alt0 (n : Nat) := rep [false,true] n
def A (L R : List Bool) : Z0 := ⟨0,true::false::L,R⟩
def C (j n : Nat) : Z0 := ⟨2,alt j,ones n⟩
def E (j n : Nat) : Z0 := ⟨4,alt j,ones n⟩

theorem repAdd (x : List Bool) (a b : Nat) : rep x (a+b) = rep x a ++ rep x b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=(a+b)+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem repDouble (x : List Bool) (k : Nat) : rep (x++x) k = rep x (2*k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep,ih,show 2*(k+1)=2+2*k by omega,repAdd]; simp only [rep,List.append_assoc,List.append_nil]

theorem repQuad (x : List Bool) (k : Nat) : rep (x++x++x++x) k = rep x (4*k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rep,ih,show 4*(k+1)=4+4*k by omega,repAdd]; simp only [rep,List.append_assoc,List.append_nil]

theorem onesAdd (a b : Nat) : ones (a+b) = ones a ++ ones b := repAdd _ _ _
theorem altAdd (a b : Nat) : alt (a+b) = alt a ++ alt b := repAdd _ _ _
theorem alt0Add (a b : Nat) : alt0 (a+b) = alt0 a ++ alt0 b := repAdd _ _ _

theorem rotateAlt (k : Nat) : false::alt k = alt0 k ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change false::true::false::alt k = false::true::(alt0 k ++ [false])
    rw [ih]

theorem aSweep (k : Nat) (L R : List Bool) :
    run0 table (6*k) (A L (ones (4*k) ++ R)) = some (A (alt (2*k) ++ L) R) := by
  have h := sweepR table 0 [true,false] [] [true,true,true,true] [true,false,true,false] 6 (by intro L R; rfl) k L R
  have h1 : rep [true,true,true,true] k = ones (4*k) := repQuad [true] k
  have h2 : rep [true,false,true,false] k = alt (2*k) := repDouble [true,false] k
  rw [h1,h2] at h
  simpa only [A,List.nil_append,List.cons_append,List.append_assoc] using h

theorem aEnd (L : List Bool) : run0 table 21 (A L [true]) = some ⟨4,[false,true,false,true,false,true,false]++L,[]⟩ := by rfl
theorem aEnd3 (L : List Bool) : run0 table 26 (A L [true,true,true]) = some ⟨4,[false,true,false,true,false,true,true,false,true,false,true,false]++L,[]⟩ := by rfl

theorem eSweep (k : Nat) (L R : List Bool) : run0 table (2*k) ⟨4,alt0 k++L,R⟩ = some ⟨4,L,ones (2*k)++R⟩ := by
  have h := sweepL table 4 [] [] [false,true] [true,true] 2 (by intro L R; rfl) k L R
  simpa only [alt0,ones,List.nil_append,show ([true,true] : List Bool)=[true]++[true] by rfl,repDouble] using h

theorem cPhase (j k : Nat) : ∃ t, 0<t ∧ run0 table t (C (j+1) (4*k+4)) = some (E j (4*k+10)) := by
  have h1 : run0 table 5 (C (j+1) (4*k+4)) = some (A ([true,false,true]++alt j) (ones (4*k)++[true])) := by
    unfold C; rw [show 4*k+4=3+(4*k+1) by omega,onesAdd 3 (4*k+1),onesAdd (4*k) 1]
    rfl
  have h2 := aSweep k ([true,false,true]++alt j) [true]
  have h3 := aEnd (alt (2*k)++([true,false,true]++alt j))
  have h := join0 (join0 h1 h2) h3
  have hw : [false,true,false,true,false,true,false]++(alt (2*k)++([true,false,true]++alt j)) = alt0 (2*k+5)++alt j := by
    rw [show 2*k+5=3+(2*k+2) by omega,alt0Add,show 2*k+2=(2*k)+2 by omega,alt0Add]
    simp only [alt0,rep,List.cons_append,List.nil_append,List.append_assoc]
    have hh := rotateAlt (2*k)
    simpa only [alt0,List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun x => [false,true,false,true,false,true]++x++[true,false,true]++alt j) hh
  rw [hw] at h
  have h4 := eSweep (2*k+5) (alt j) []
  have h5 := join0 h h4
  simp only [List.append_nil,show 2*(2*k+5)=4*k+10 by omega] at h5
  exact ⟨_,by omega,h5⟩

theorem ePhase (j k : Nat) : ∃ t, 0<t ∧ run0 table t (E (j+1) (4*k+2)) = some (C j (4*k+8)) := by
  have h1 : run0 table 1 (E (j+1) (4*k+2)) = some (A ([false]++alt j) (ones (4*k)++[true])) := by
    unfold E; rw [show 4*k+2=1+(4*k+1) by omega,onesAdd 1 (4*k+1),onesAdd (4*k) 1]
    rfl
  have h2 := aSweep k ([false]++alt j) [true]
  have h3 := aEnd (alt (2*k)++([false]++alt j))
  have h := join0 (join0 h1 h2) h3
  have hw : [false,true,false,true,false,true,false]++(alt (2*k)++([false]++alt j)) = alt0 (2*k+3)++([false,false]++alt j) := by
    rw [show 2*k+3=3+2*k by omega,alt0Add]
    simpa only [alt0,rep,List.cons_append,List.nil_append,List.append_assoc] using congrArg (fun x => [false,true,false,true,false,true]++x++[false]++alt j) (rotateAlt (2*k))
  rw [hw] at h
  have h4 := eSweep (2*k+3) ([false,false]++alt j) []
  have h5 := join0 h h4
  simp only [List.append_nil,show 2*(2*k+3)=4*k+6 by omega] at h5
  have h6 : run0 table 2 ⟨4,[false,false]++alt j,ones (4*k+6)⟩ = some (C j (4*k+8)) := by
    unfold C; rw [show 4*k+8=2+(4*k+6) by omega,onesAdd 2 _]; rfl
  exact ⟨_,by omega,join0 h5 h6⟩

theorem cEven (k : Nat) : ∃ t, 0<t ∧ run0 table t (C 0 (4*k+4)) = some (C 0 (4*k+10)) := by
  have h1 : run0 table 3 (C 0 (4*k+4)) = some (A [true,false] (ones (4*k)++[true])) := by
    unfold C; rw [show 4*k+4=3+(4*k+1) by omega,onesAdd 3 (4*k+1),onesAdd (4*k) 1]; rfl
  have h2 := aSweep k [true,false] [true]
  have h3 := aEnd (alt (2*k)++[true,false])
  have h := join0 (join0 h1 h2) h3
  have hw : [false,true,false,true,false,true,false]++(alt (2*k)++[true,false]) = alt0 (2*k+4)++[false] := by
    rw [show 2*k+4=3+(2*k+1) by omega,alt0Add,show 2*k+1=2*k+1 by rfl,alt0Add]
    simpa only [alt0,rep,List.cons_append,List.nil_append,List.append_assoc] using congrArg (fun x => [false,true,false,true,false,true]++x++[true,false]) (rotateAlt (2*k))
  rw [hw] at h
  have h4 := eSweep (2*k+4) [false] []
  have h5 := join0 h h4
  simp only [List.append_nil,show 2*(2*k+4)=4*k+8 by omega] at h5
  have h6 : run0 table 2 ⟨4,[false],ones (4*k+8)⟩ = some (C 0 (4*k+10)) := by
    unfold C; rw [show 4*k+10=2+(4*k+8) by omega,onesAdd 2 _]; rfl
  exact ⟨_,by omega,join0 h5 h6⟩

theorem cOddStart (k : Nat) : ∃ t, 0<t ∧ run0 table t (C 0 (4*k+2)) = some (E (2*k+2) 6) := by
  cases k with
  | zero => exact ⟨29,by decide,by rfl⟩
  | succ k =>
    have h1 : run0 table 3 (C 0 (4*(k+1)+2)) = some (A [true,false] (ones (4*k)++[true,true,true])) := by
      unfold C; rw [show 4*(k+1)+2=3+(4*k+3) by omega,onesAdd 3 (4*k+3),onesAdd (4*k) 3]; rfl
    have h2 := aSweep k [true,false] [true,true,true]
    have h3 := aEnd3 (alt (2*k)++[true,false])
    have h := join0 (join0 h1 h2) h3
    have hw : [false,true,false,true,false,true,true,false,true,false,true,false]++(alt (2*k)++[true,false]) = alt0 3 ++ alt (2*(k+1)+2) := by
      rw [show 2*(k+1)+2=3+(2*k+1) by omega,altAdd,altAdd]
      simp only [alt,alt0,rep,List.cons_append,List.nil_append,List.append_assoc]
    rw [hw] at h
    have h4 := eSweep 3 (alt (2*(k+1)+2)) []
    have h5 := join0 h h4
    simp only [List.append_nil] at h5
    exact ⟨_,by omega,h5⟩

theorem reduce (j k : Nat) : ∃ t, 0<t ∧ run0 table t (E (2*j) (4*k+2)) = some (C 0 (4*k+12*j+4)) := by
  induction j generalizing k with
  | zero =>
    have h : run0 table 2 (E 0 (4*k+2)) = some (C 0 (4*k+4)) := by
      unfold C E; rw [show 4*k+4=2+(4*k+2) by omega,onesAdd 2 _]; rfl
    exact ⟨2,by decide,by simpa using h⟩
  | succ j ih =>
    obtain ⟨t,ht,h1⟩ := ePhase (2*j+1) k
    obtain ⟨u,hu,h2⟩ := cPhase (2*j) (k+1)
    obtain ⟨v,hv,h3⟩ := ih (k+3)
    rw [show 2*j+1+1=2*(j+1) by omega] at h1
    rw [show 4*(k+1)+4=4*k+8 by omega] at h2
    rw [show 4*(k+3)+2=4*(k+1)+10 by omega,show 4*(k+3)+12*j+4=4*k+12*(j+1)+4 by omega] at h3
    exact ⟨t+u+v,by omega,join0 (join0 h1 h2) h3⟩

theorem cOdd (k : Nat) : ∃ t, 0<t ∧ run0 table t (C 0 (4*k+2)) = some (C 0 (12*k+20)) := by
  obtain ⟨t,ht,h1⟩ := cOddStart k
  obtain ⟨u,hu,h2⟩ := reduce (k+1) 1
  rw [show 2*(k+1)=2*k+2 by omega,show 4*1+2=6 by decide,show 4*1+12*(k+1)+4=12*k+20 by omega] at h2
  exact ⟨t+u,by omega,join0 h1 h2⟩

theorem grow (k : Nat) : ∃ t, 0<t ∧ run0 table t (C 0 (4*k+4)) = some (C 0 (4*(3*k+10)+4)) := by
  obtain ⟨t,ht,h1⟩ := cEven k
  obtain ⟨u,hu,h2⟩ := cOdd (k+2)
  rw [show 4*(k+2)+2=4*k+10 by omega,show 12*(k+2)+20=4*(3*k+10)+4 by omega] at h2
  exact ⟨t+u,by omega,join0 h1 h2⟩

theorem arbitrary (n : Nat) : ∃ t k, n≤t ∧ run0 table t ⟨0,[],[]⟩ = some (C 0 (4*k+4)) := by
  induction n with
  | zero => exact ⟨66,2,by decide,by rfl⟩
  | succ n ih =>
    obtain ⟨t,k,ht,hh⟩ := ih
    obtain ⟨u,hu,hg⟩ := grow k
    exact ⟨t+u,3*k+10,by omega,join0 hh hg⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table (fun n => by
    obtain ⟨t,k,ht,hr⟩ := arbitrary n
    exact ⟨t,C 0 (4*k+4),ht,hr⟩) m hm
#print axioms never
end BB6Coverage.Agent4BlockCases.M1391
