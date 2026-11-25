import F0SiblingCover
import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48CounterRC
open BB6Coverage BB6Coverage.Agent31Pump

inductive Choice where | ld | le | re

def action : Choice → Move
  | .ld => ⟨true,false,3⟩
  | .le => ⟨false,false,4⟩
  | .re => ⟨true,true,4⟩
def ctr (a : Choice) : PartialMachine :=
  refine (BB6.Agent6F0.parent ⟨false,true,2⟩) (0,true) (some (action a))
def delay : Choice → Nat | .ld => 4 | .le => 6 | .re => 8
def pad : Choice → List Bool | .re => [false] | _ => []
abbrev P : List Bool := [false,true,true,true]
abbrev Q : List Bool := [true,false,false,true]
abbrev O : List Bool := [true,true,true]
abbrev Z : List Bool := [true,false,false]
abbrev J : List Bool := [false,false,true]
abbrev U : List Bool := [false,false,false]
abbrev h : List Bool := [true]
abbrev f : List Bool := [false]
abbrev t : List Bool := [true,false]
def A (m : Nat) (W : List Bool) : Z0 := ⟨5,f++rep P m++W++P,[]⟩
def B (m : Nat) (W : List Bool) : Z0 := ⟨5,f++rep P m++f++Z++W++P,[]⟩

theorem enter (a : Choice) (L : List Bool) :
  run0 (ctr a) (delay a) ⟨5,f++P++L,[]⟩ = some ⟨3,h++P++L,h++pad a⟩ := by cases a <;> rfl
theorem microP (a : Choice) (L R : List Bool) :
  run0 (ctr a) 8 ⟨3,h++P++L,h++R⟩ = some ⟨3,h++L,h++Q++R⟩ := by cases a <;> rfl
theorem microD (a : Choice) (L R : List Bool) :
  run0 (ctr a) 9 ⟨3,h++O++L,R⟩ = some ⟨3,h++L,O++R⟩ := by cases a <;> rfl
theorem microF (a : Choice) (L R : List Bool) :
  run0 (ctr a) 3 ⟨5,t++L,O++R⟩ = some ⟨5,t++Z++L,R⟩ := by cases a <;> rfl
theorem microQ (a : Choice) (L R : List Bool) :
  run0 (ctr a) 6 ⟨5,h++L,J++Q++R⟩ = some ⟨5,h++P++L,J++R⟩ := by cases a <;> rfl
theorem finishQ (a : Choice) (L : List Bool) :
  run0 (ctr a) 6 ⟨5,h++L,J++pad a⟩ = some ⟨5,f++P++L,[]⟩ := by cases a <;> rfl
theorem zeroTurn (a : Choice) (L R : List Bool) :
  run0 (ctr a) 9 ⟨3,h++Z++L,h++R⟩ = some ⟨5,t++O++L,R⟩ := by cases a <;> rfl
theorem overTurn (a : Choice) (R : List Bool) :
  run0 (ctr a) 20 ⟨3,h++P,[true,true]++R⟩ = some ⟨5,t++O++P,R⟩ := by cases a <;> rfl
theorem queueTurn (a : Choice) (L R : List Bool) :
  run0 (ctr a) 11 ⟨5,t++L,Q++h++R⟩ = some ⟨5,h++U++O++L,R⟩ := by cases a <;> rfl
theorem transientTurn (a : Choice) (L R : List Bool) :
  run0 (ctr a) 6 ⟨3,h++U++L,h++Q++R⟩ = some ⟨5,h++P++f++L,J++R⟩ := by cases a <;> rfl
theorem bEnter (a : Choice) (L R : List Bool) :
  run0 (ctr a) 14 ⟨3,h++f++Z++L,h++R⟩ = some ⟨3,h++L,[true,true,true,false,true]++R⟩ := by cases a <;> rfl
theorem bTurn (a : Choice) (L R : List Bool) :
  run0 (ctr a) 3 ⟨5,t++L,[true,true,false,true]++R⟩ = some ⟨5,f++f++Z++L,h++R⟩ := by cases a <;> rfl
theorem bQueue (a : Choice) (L R : List Bool) :
  run0 (ctr a) 2 ⟨5,f++f++L,h++Q++R⟩ = some ⟨5,h++U++L,J++R⟩ := by cases a <;> rfl
theorem bOver (a : Choice) (L R : List Bool) :
  run0 (ctr a) 9 ⟨5,t++L,[true,false,true]++R⟩ = some ⟨5,t++O++L,R⟩ := by cases a <;> rfl

theorem shiftO (k : Nat) : rep O k ++ h = h ++ rep O k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep,List.append_assoc,ih]; rfl

theorem shiftO2 (k : Nat) : rep O k ++ [true,true] = [true,true] ++ rep O k := by
  calc
    _ = (rep O k ++ h) ++ h := by simp only [List.append_assoc]; rfl
    _ = _ := by rw [shiftO,List.append_assoc,shiftO,← List.append_assoc]; rfl

theorem scanP (a : Choice) (n : Nat) (L : List Bool) :
  run0 (ctr a) (delay a+8*(n+1)) ⟨5,f++rep P (n+1)++L,[]⟩ = some ⟨3,h++L,h++rep Q (n+1)++pad a⟩ := by
  have H1 := enter a (rep P n++L)
  have H2 := sweepL (ctr a) 3 h h P Q 8 (microP a) (n+1) L (pad a)
  have H := join0 H1 (by simpa only [List.append_nil,rep,List.append_assoc] using H2)
  simpa only [rep,List.append_assoc] using H

theorem scanD (a : Choice) (k : Nat) (L R : List Bool) :
  run0 (ctr a) (9*k) ⟨3,h++rep O k++L,R⟩ = some ⟨3,h++L,rep O k++R⟩ := by
  simpa only [List.nil_append,List.append_assoc] using sweepL (ctr a) 3 h [] O O 9 (by intro L R; simpa only [List.nil_append] using microD a L R) k L R

theorem scanF (a : Choice) (k : Nat) (L R : List Bool) :
  run0 (ctr a) (3*k) ⟨5,t++L,rep O k++R⟩ = some ⟨5,t++rep Z k++L,R⟩ := by
  simpa only [List.nil_append,List.append_assoc] using sweepR (ctr a) 5 t [] O Z 3 (by intro L R; simpa only [List.nil_append] using microF a L R) k L R

theorem restoreQ (a : Choice) (n : Nat) (L : List Bool) :
  run0 (ctr a) (6*(n+1)) ⟨5,h++L,J++rep Q n++pad a⟩ = some ⟨5,f++rep P (n+1)++L,[]⟩ := by
  have H1 := sweepR (ctr a) 5 h J Q P 6 (microQ a) n L (pad a)
  have H1' : run0 (ctr a) (6*n) ⟨5,h++L,J++rep Q n++pad a⟩ = some ⟨5,h++rep P n++L,J++pad a⟩ := by simpa only [List.append_nil] using H1
  have H := join0 H1' (finishQ a (rep P n++L))
  rw [show 6*n+6=6*(n+1) by omega] at H
  simpa only [rep,List.append_assoc] using H

theorem aQueue (a : Choice) (n : Nat) (L : List Bool) :
  run0 (ctr a) (11+6*(n+1)) ⟨5,t++L,rep Q (n+2)++pad a⟩ = some ⟨5,f++rep P (n+1)++U++O++L,[]⟩ := by
  have H1 := queueTurn a L (J++rep Q n++pad a)
  have H1' : run0 (ctr a) 11 ⟨5,t++L,rep Q (n+2)++pad a⟩ = some ⟨5,h++(U++O++L),J++rep Q n++pad a⟩ := by simpa only [rep,Q,h,J,List.append_assoc,List.cons_append,List.nil_append] using H1
  have H := join0 H1' (restoreQ a n (U++O++L))
  simpa only [List.append_assoc] using H

theorem transient (a : Choice) (n : Nat) (L : List Bool) :
  run0 (ctr a) (delay a+14*(n+1)+6) ⟨5,f++rep P (n+1)++U++L,[]⟩ = some ⟨5,f++rep P (n+2)++f++L,[]⟩ := by
  have H1 := scanP a n (U++L)
  have H2 := transientTurn a L (rep Q n++pad a)
  have H2' : run0 (ctr a) 6 ⟨3,h++(U++L),h++rep Q (n+1)++pad a⟩ = some ⟨5,h++(P++f++L),J++rep Q n++pad a⟩ := by simpa only [rep,List.append_assoc] using H2
  have H3 := restoreQ a n (P++f++L)
  have H := join0 (join0 H1 H2') H3
  rw [show delay a+8*(n+1)+6+6*(n+1)=delay a+14*(n+1)+6 by omega] at H
  have he : rep P (n+1) ++ P = rep P (n+2) := by rw [rep_snoc]; rfl
  simpa only [← List.append_assoc (rep P (n+1)) P (f++L),he,List.append_assoc] using H

-- Exact first-stage common carry; R is the suffix following the initial run of ones.
theorem carryCore (a : Choice) (k : Nat) (L R : List Bool) :
  run0 (ctr a) (12*k+9) ⟨3,h++rep O k++Z++L,h++R⟩ = some ⟨5,t++rep Z k++O++L,R⟩ := by
  have H1 := scanD a k (Z++L) (h++R)
  have H1' : run0 (ctr a) (9*k) ⟨3,h++rep O k++Z++L,h++R⟩ = some ⟨3,h++Z++L,h++rep O k++R⟩ := by
    simpa only [← List.append_assoc (rep O k) h R,shiftO,List.append_assoc] using H1
  have H2 := zeroTurn a L (rep O k++R)
  have H3 := scanF a k (O++L) R
  have H := join0 (join0 H1' (by simpa only [List.append_assoc] using H2)) H3
  rw [show 9*k+9+3*k=12*k+9 by omega] at H
  simpa only [List.append_assoc] using H

theorem overCore (a : Choice) (k : Nat) (R : List Bool) :
  run0 (ctr a) (12*k+20) ⟨3,h++rep O k++P,[true,true]++R⟩ = some ⟨5,t++rep Z k++O++P,R⟩ := by
  have H1 := scanD a k P ([true,true]++R)
  have H1' : run0 (ctr a) (9*k) ⟨3,h++rep O k++P,[true,true]++R⟩ = some ⟨3,h++P,[true,true]++rep O k++R⟩ := by
    simpa only [← List.append_assoc (rep O k) [true,true] R,shiftO2,List.append_assoc] using H1
  have H2 := overTurn a (rep O k++R)
  have H3 := scanF a k (O++P) R
  have H := join0 (join0 H1' (by simpa only [List.append_assoc] using H2)) H3
  rw [show 9*k+20+3*k=12*k+20 by omega] at H
  simpa only [List.append_assoc] using H

-- A positive-width counter word; its most significant digit is one.
inductive Word : List Bool → Prop
  | last : Word O
  | zero {L : List Bool} : Word L → Word (Z++L)
  | one {L : List Bool} : Word L → Word (O++L)
theorem zeros (k : Nat) {L : List Bool} (H : Word L) : Word (rep Z k++L) := by
  induction k with
  | zero => simpa only [rep,List.nil_append] using H
  | succ k ih => simpa only [rep,List.append_assoc] using Word.zero ih

theorem classify {L : List Bool} (H : Word L) :
  (∃ k T, Word T ∧ L = rep O k++Z++T) ∨ (∃ k, L = rep O (k+1)) := by
  induction H with
  | last => exact Or.inr ⟨0,rfl⟩
  | @zero L H ih => exact Or.inl ⟨0,L,H,rfl⟩
  | @one L H ih =>
    rcases ih with ⟨k,T,hT,he⟩ | ⟨k,he⟩
    · exact Or.inl ⟨k+1,T,hT,by rw [he]; simp only [rep,List.append_assoc]⟩
    · exact Or.inr ⟨k+1,by rw [he]; rfl⟩

-- All four cases of the two-phase counter, with arbitrary queue length >= 2.
theorem aCarry (a : Choice) (n k : Nat) (T : List Bool) :
  run0 (ctr a) (2*delay a+28*n+12*k+62) (A (n+2) (rep O k++Z++T)) =
    some (A (n+3) (rep Z k++O++T)) := by
  have H1 := scanP a (n+1) (rep O k++Z++T++P)
  have H2 := carryCore a k (T++P) (rep Q (n+2)++pad a)
  have H3 := aQueue a n (rep Z k++O++T++P)
  have H4 := transient a n (O++rep Z k++O++T++P)
  have H12 := join0 H1 (by simpa only [List.append_assoc] using H2)
  have H123 := join0 H12 (by simpa only [List.append_assoc] using H3)
  have H := join0 H123 (by simpa only [t,O,List.append_assoc,List.cons_append,List.nil_append] using H4)
  have hc : delay a+8*(n+1+1)+(12*k+9)+(11+6*(n+1))+(delay a+14*(n+1)+6)=2*delay a+28*n+12*k+62 := by omega
  rw [hc] at H
  have eq : rep P (n+2) ++ (f ++ (O ++ (rep Z k ++ (O ++ (T ++ P))))) = rep P (n+3) ++ (rep Z k ++ (O ++ (T ++ P))) := by
    change rep P (n+2) ++ (P ++ _) = _
    rw [← List.append_assoc,rep_snoc]
    rfl
  simp only [A,List.append_assoc] at H ⊢
  simp only [f,O,P,List.cons_append,List.nil_append] at eq H ⊢
  rw [eq] at H
  exact H

theorem aOverflow (a : Choice) (n k : Nat) :
  run0 (ctr a) (delay a+14*(n+2)+12*(k+1)+20) (A (n+2) (rep O (k+1))) =
    some (B (n+2) (rep Z k++O)) := by
  have H1 := scanP a (n+1) (rep O (k+1)++P)
  have H2 := overCore a (k+1) (J++rep Q (n+1)++pad a)
  have H2' : run0 (ctr a) (12*(k+1)+20) ⟨3,h++(rep O (k+1)++P),h++rep Q (n+2)++pad a⟩ = some ⟨5,t++rep Z (k+1)++O++P,J++rep Q (n+1)++pad a⟩ := by
    simpa only [rep,Q,J,h,List.append_assoc,List.cons_append,List.nil_append] using H2
  have H3 := restoreQ a (n+1) (f++rep Z (k+1)++O++P)
  have H := join0 (join0 H1 H2') (by simpa only [t,h,f,List.append_assoc,List.cons_append,List.nil_append] using H3)
  rw [show delay a+8*(n+1+1)+(12*(k+1)+20)+6*(n+1+1)=delay a+14*(n+2)+12*(k+1)+20 by omega] at H
  simpa only [A,B,rep,f,O,Z,List.append_assoc,List.cons_append,List.nil_append] using H

theorem bCarry (a : Choice) (n k : Nat) (T : List Bool) :
  run0 (ctr a) (2*delay a+28*(n+2)+12*k+34) (B (n+2) (rep O k++Z++T)) =
    some (B (n+3) (rep Z k++O++T)) := by
  have H1 := scanP a (n+1) (f++Z++rep O k++Z++T++P)
  have H2 := bEnter a (rep O k++Z++T++P) (rep Q (n+2)++pad a)
  have H12 := join0 H1 (by simpa only [List.append_assoc] using H2)
  have H3 := carryCore a k (T++P) ([true,true,false,true]++rep Q (n+2)++pad a)
  have H123 := join0 H12 (by simpa only [h,List.append_assoc,List.cons_append,List.nil_append] using H3)
  have H4 := bTurn a (rep Z k++O++T++P) (rep Q (n+2)++pad a)
  have H1234 := join0 H123 (by simpa only [t,O,List.append_assoc,List.cons_append,List.nil_append] using H4)
  have H5 := bQueue a (Z++rep Z k++O++T++P) (rep Q (n+1)++pad a)
  have H12345 := join0 H1234 (by simpa only [rep,f,h,Z,O,List.append_assoc,List.cons_append,List.nil_append] using H5)
  have H6 := restoreQ a (n+1) (U++Z++rep Z k++O++T++P)
  have H123456 := join0 H12345 (by simpa only [rep,h,U,Z,O,J,Q,List.append_assoc,List.cons_append,List.nil_append] using H6)
  have H7 := transient a (n+1) (Z++rep Z k++O++T++P)
  have H := join0 H123456 (by simpa only [rep,f,P,U,Z,O,List.append_assoc,List.cons_append,List.nil_append] using H7)
  rw [show delay a+8*(n+1+1)+14+(12*k+9)+3+2+6*(n+1+1)+(delay a+14*(n+1+1)+6)=2*delay a+28*(n+2)+12*k+34 by omega] at H
  simpa only [B,rep,f,P,Z,O,List.append_assoc,List.cons_append,List.nil_append] using H

theorem bOverflow (a : Choice) (n k : Nat) :
  run0 (ctr a) (2*delay a+28*n+12*(k+1)+96) (B (n+2) (rep O (k+1))) =
    some (A (n+3) (O++rep Z (k+1)++O)) := by
  have H1 := scanP a (n+1) (f++Z++rep O (k+1)++P)
  have H2 := bEnter a (rep O (k+1)++P) (rep Q (n+2)++pad a)
  have H12 := join0 H1 (by simpa only [List.append_assoc] using H2)
  have H3 := overCore a (k+1) ([true,false,true]++rep Q (n+2)++pad a)
  have H123 := join0 H12 (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using H3)
  have H4 := bOver a (rep Z (k+1)++O++P) (rep Q (n+2)++pad a)
  have H1234 := join0 H123 (by simpa only [t,O,List.append_assoc,List.cons_append,List.nil_append] using H4)
  have H5 := aQueue a n (O++rep Z (k+1)++O++P)
  have H12345 := join0 H1234 (by simpa only [t,O,List.append_assoc,List.cons_append,List.nil_append] using H5)
  have H6 := transient a n (O++O++rep Z (k+1)++O++P)
  have H := join0 H12345 (by simpa only [f,U,O,List.append_assoc,List.cons_append,List.nil_append] using H6)
  rw [show delay a+8*(n+1+1)+14+(12*(k+1)+20)+9+(11+6*(n+1))+(delay a+14*(n+1)+6)=2*delay a+28*n+12*(k+1)+96 by omega] at H
  have eq : rep P (n+2) ++ (f ++ (O ++ (O ++ (rep Z (k+1) ++ (O ++ P))))) = rep P (n+3) ++ (O ++ (rep Z (k+1) ++ (O ++ P))) := by
    change rep P (n+2) ++ (P ++ _) = _
    rw [← List.append_assoc,rep_snoc]
    rfl
  simp only [A,B,List.append_assoc] at H ⊢
  simp only [f,O,P,List.cons_append,List.nil_append] at eq H ⊢
  rw [eq] at H
  exact H

inductive Phase where | a | b
abbrev State := Phase × Nat × {W : List Bool // Word W}
def atState (s : State) : Z0 := match s.1 with
  | .a => A (s.2.1+2) s.2.2.val
  | .b => B (s.2.1+2) s.2.2.val

theorem next_exists (a : Choice) (s : State) :
    ∃ p : Nat × State, 0 < p.1 ∧ run0 (ctr a) p.1 (atState s) = some (atState p.2) := by
  rcases s with ⟨ph,n,⟨W,hW⟩⟩
  rcases classify hW with ⟨k,T,hT,he⟩ | ⟨k,he⟩
  · have hw : Word (rep Z k++O++T) := by simpa only [List.append_assoc] using zeros k (Word.one hT)
    cases ph
    · refine ⟨(2*delay a+28*n+12*k+62,.a,n+1,⟨_,hw⟩),by omega,?_⟩
      simpa only [atState,he] using aCarry a n k T
    · refine ⟨(2*delay a+28*(n+2)+12*k+34,.b,n+1,⟨_,hw⟩),by omega,?_⟩
      simpa only [atState,he] using bCarry a n k T
  · cases ph
    · refine ⟨(delay a+14*(n+2)+12*(k+1)+20,.b,n,⟨_,zeros k Word.last⟩),by omega,?_⟩
      simpa only [atState,he] using aOverflow a n k
    · have hw : Word (O++rep Z (k+1)++O) := by simpa only [List.append_assoc] using Word.one (zeros (k+1) Word.last)
      refine ⟨(2*delay a+28*n+12*(k+1)+96,.a,n+1,⟨_,hw⟩),by omega,?_⟩
      simpa only [atState,he] using bOverflow a n k

noncomputable def next (a : Choice) (s : State) : Nat × State := Classical.choose (next_exists a s)
theorem next_spec (a : Choice) (s : State) : 0 < (next a s).1 ∧ run0 (ctr a) (next a s).1 (atState s) = some (atState (next a s).2) := Classical.choose_spec (next_exists a s)
noncomputable def states (a : Choice) : Nat → State
  | 0 => (.a,0,⟨O++Z++O,by exact Word.one (Word.zero Word.last)⟩)
  | n+1 => (next a (states a n)).2

def entryCost (a : Choice) := 179+3*delay a
theorem entry (a : Choice) : run0 (ctr a) (entryCost a) ⟨0,[],[]⟩ = some (atState (states a 0)) := by cases a <;> rfl

theorem growth (a : Choice) (k : Nat) : run0 (ctr a) (next a (states a k)).1 (atState (states a k)) = some (atState (states a (k+1))) := (next_spec a (states a k)).2

theorem arbitrary_live_prefix (a : Choice) (k : Nat) : ∃ t, k ≤ t ∧ run0 (ctr a) t ⟨0,[],[]⟩ = some (atState (states a k)) := by
  induction k with
  | zero => exact ⟨entryCost a,by omega,entry a⟩
  | succ k ih =>
    obtain ⟨t,ht,hr⟩ := ih
    have hp := (next_spec a (states a k)).1
    exact ⟨t+(next a (states a k)).1,by omega,join0 hr (growth a k)⟩

#print axioms aCarry
#print axioms aOverflow
#print axioms bCarry
#print axioms bOverflow
#print axioms entry
#print axioms arbitrary_live_prefix
open BB6.Agent13BlankDelay BB6.Agent47WeightedHalt

theorem never (a : Choice) (m : Machine) (hm : compatible (ctr a) m) : NeverHalts m :=
  never_of_growth (ctr a) (fun k => atState (states a k)) (entryCost a)
    (fun k => (next a (states a k)).1) (entry a) (fun k => (next_spec a (states a k)).1) (growth a) m hm

theorem cover_zeroRC (B : Nat) (a : Choice) : Cover (WeightedBound B) (ctr a) :=
  .leaf _ (fun m hm => weighted_never B m (never a m hm))

#print axioms never
#print axioms cover_zeroRC
end BB6.Agent48CounterRC
