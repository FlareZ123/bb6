import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4LF11336
open BB6Coverage Agent31Pump
-- 1RB1LF_1RC0RB_0RD0LA_1LD1RE_---0RA_1LC1RF
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def P : List Bool := [true,false]
def PP : List Bool := P++P
def H : List Bool := [false,true,true]
def W : List Bool := [false,true,true,true]
def M : List Bool := [true,false,false,true,false]
def A (l r : List Bool) : Z0 := ⟨0,l,r⟩
def C (r : List Bool) : Z0 := ⟨2,[],r⟩
def G (a b : Nat) : Z0 := C ([true,true]++rep W a++H++rep W b)

theorem pComm (n : Nat) : P++rep PP n = rep PP n++P := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change P ++ ((P++P)++rep PP n) = ((P++P)++rep PP n)++P
    simp only [List.append_assoc]
    rw [ih]

theorem shortSweep (n : Nat) (L R : List Bool) :
    run0 table (10*n) (A ([false,false]++L) ([true,true]++rep W n++R)) =
      some (A ([false,false]++rep PP n++L) ([true,true]++R)) := by
  exact sweepR table 0 [false,false] [true,true] W PP 10 (by intro l r; rfl) n L R

theorem shortEnd (L : List Bool) :
    run0 table 12 (A ([false,false]++L) [true,true]) =
      some (A ([false,false]++P++L) H) := by rfl

theorem longSweep (k : Nat) (L S : List Bool) :
    run0 table (11+10*k) (A ([false,false]++L) ([true,true,true]++rep W k++H++S)) =
      some (A ([false,false]++rep PP k++M++L) (true::S)) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h1 : run0 table 11 (A ([false,false]++L) ([true,true,true]++W++(rep W k++H++S))) =
      some (A ([false,false]++M++L) ([true,true]++(rep W k++H++S))) := by rfl
    have h2 := shortSweep k (M++L) (H++S)
    have h3 : run0 table 10 (A ([false,false]++rep PP k++(M++L)) ([true,true]++(H++S))) =
      some (A ([false,false]++PP++(rep PP k++(M++L))) (true::S)) := by rfl
    have h := join0 (join0 (by simpa only [List.append_assoc] using h1) h2) h3
    rw [show 11+10*k+10=11+10*(k+1) by omega] at h
    simpa only [rep,List.append_assoc] using h

theorem backSweep (k : Nat) (L S : List Bool) :
    run0 table (16*k) (A ([false]++rep PP k++L) (H++S)) =
      some (A (false::L) (H++rep W k++S)) := by
  exact sweepL table 0 [false] H PP W 16 (by intro l r; rfl) k L S

theorem outerStep (k : Nat) (L S : List Bool) :
    run0 table (25+16*k) (A ([false,false]++rep PP k++M++L) (true::(W++S))) =
      some (A ([false,false]++PP++L) ([true,true,true]++rep W k++H++S)) := by
  have h1 : run0 table 7 (A ([false,false]++rep PP k++M++L) (true::(W++S))) =
    some (A ([false]++rep PP k++M++L) (H++H++S)) := by cases k <;> rfl
  have h2 := backSweep k (M++L) (H++S)
  have h3 : run0 table 18 (A (false::(M++L)) (H++(rep W k++H++S))) =
    some (A ([false,false]++PP++L) ([true,true,true]++(rep W k++H++S))) := by rfl
  have h := join0 (join0 (by simpa only [List.append_assoc] using h1) h2) (by simpa only [List.append_assoc] using h3)
  rw [show 7+16*k+18=25+16*k by omega] at h
  simpa only [List.append_assoc] using h

theorem outerEnd (k : Nat) (L : List Bool) :
    run0 table (27+16*k) (A ([false,false]++rep PP k++M++L) [true]) =
      some (A ([false,false]++P++L) (H++rep W (k+1))) := by
  have h1 : run0 table 11 (A ([false,false]++rep PP k++M++L) [true]) =
    some (A ([false]++rep PP k++P++M++L) H) := by
      rw [show [false]++rep PP k++P++M++L = [false]++P++rep PP k++M++L by
        simp only [List.append_assoc]; rw [← List.append_assoc (rep PP k) P, ← pComm]; simp only [List.append_assoc]]
      cases k <;> rfl
  have h2 := backSweep k (P++M++L) []
  have h3 : run0 table 16 (A (false::(P++M++L)) (H++rep W k)) =
    some (A ([false,false]++P++L) (H++W++rep W k)) := by rfl
  simp only [List.append_nil,List.append_assoc] at h1 h2 h3
  have h := join0 (join0 h1 h2) h3
  rw [show 11+16*k+16=27+16*k by omega] at h
  simpa only [rep,List.append_assoc] using h

theorem finalSweep (j : Nat) (S : List Bool) :
    run0 table (26+16*j) (A ([false,false]++rep PP (j+1)) (H++S)) =
      some (C ([true,true]++rep W (j+1)++H++S)) := by
  have h1 : run0 table 11 (A ([false,false]++rep PP (j+1)) (H++S)) =
    some (A ([false]++rep PP j++P) (H++H++S)) := by
      rw [show [false]++rep PP j++P = [false]++P++rep PP j by rw [List.append_assoc,←pComm,List.append_assoc]]
      rfl
  have h2 := backSweep j P (H++S)
  have h3 : run0 table 15 (A (false::P) (H++(rep W j++H++S))) =
    some (C ([true,true]++W++(rep W j++H++S))) := by rfl
  simp only [List.append_assoc] at h1 h2 h3
  have h := join0 (join0 h1 h2) h3
  rw [show 11+16*j+15=26+16*j by omega] at h
  simpa only [rep,List.append_assoc] using h

theorem longResolve (b k j : Nat) : ∃ t, 0<t ∧
    run0 table t (A ([false,false]++rep PP j++P) ([true,true,true]++rep W k++H++rep W b)) =
      some (A ([false,false]++rep PP (j+b+1)) (H++rep W (k+1))) := by
  induction b generalizing j with
  | zero =>
    have h1 := longSweep k (rep PP j++P) []
    have h2 := outerEnd k (rep PP j++P)
    simp only [rep,List.append_nil,List.append_assoc] at h1 h2
    have h := join0 h1 h2
    have hl : [false,false]++(P++(rep PP j++P)) = [false,false]++rep PP (j+1) := by
      change [false,false]++(P++(rep PP j++P)) = [false,false]++((P++P)++rep PP j)
      simp only [List.append_assoc]; rw [← pComm j]
    rw [hl] at h
    exact ⟨11+10*k+(27+16*k),by omega,by simpa only [rep,List.append_nil,List.append_assoc,Nat.add_zero] using h⟩
  | succ b ih =>
    have h1 := longSweep k (rep PP j++P) (rep W (b+1))
    have h2 := outerStep k (rep PP j++P) (rep W b)
    have h := join0 (by simpa only [rep,List.append_assoc] using h1) (by simpa only [List.append_assoc] using h2)
    obtain ⟨u,hu,h3⟩ := ih (j+1)
    rw [show j+1+b+1=j+(b+1)+1 by omega] at h3
    have h' := join0 h (by simpa only [rep,List.append_assoc] using h3)
    exact ⟨11+10*k+(25+16*k)+u,by omega,by simpa only [rep,List.append_assoc] using h'⟩

theorem grow (a b : Nat) : ∃ t, 0<t ∧ run0 table t (G a b) = some (G (b+1) a) := by
  cases a with
  | zero =>
    have h1 : run0 table 3 (G 0 b) = some (A ([false,false]++P) ([true,true]++rep W b)) := by rfl
    have h2 := shortSweep b P []
    have h3 := shortEnd (rep PP b++P)
    have h := join0 (join0 h1 (by simpa only [List.append_nil,List.append_assoc] using h2)) h3
    have hl : [false,false]++P++(rep PP b++P) = [false,false]++rep PP (b+1) := by
      change [false,false]++P++(rep PP b++P) = [false,false]++((P++P)++rep PP b)
      simp only [List.append_assoc]; rw [← pComm b]
    rw [hl] at h
    have h4 := finalSweep b []
    exact ⟨3+10*b+12+(26+16*b),by omega,by simpa only [G,rep,List.append_nil,List.append_assoc] using join0 h h4⟩
  | succ a =>
    have h1 : run0 table 3 (G (a+1) b) =
        some (A ([false,false]++P) ([true,true,true]++rep W a++H++rep W b)) := by rfl
    obtain ⟨u,hu,h2⟩ := longResolve b a 0
    simp only [rep,List.nil_append,Nat.zero_add] at h2
    have h3 := finalSweep b (rep W (a+1))
    exact ⟨_,by omega,join0 (join0 h1 h2) h3⟩

theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k : Nat, ∃ t a b, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (G a b) := by
    intro k
    induction k with
    | zero => exact ⟨12,0,0,by omega,by rfl⟩
    | succ k ih =>
      obtain ⟨t,a,b,ht,h1⟩ := ih
      obtain ⟨u,hu,h2⟩ := grow a b
      exact ⟨_,_,_,by omega,join0 h1 h2⟩
  obtain ⟨t,a,b,ht,h1⟩ := h n
  exact ⟨t,G a b,ht,h1⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
#print axioms grow
#print axioms arbitrary
end BB6Coverage.Agent4LF11336
