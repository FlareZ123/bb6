import F0Counter0LE

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! F0=1RB, B1=0RD. The right boundary stores the parity of the
    left word and a variable-length all-one suffix. -/
namespace BB6.Agent6F0.Counter1RB
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt
open BB6.Agent6F0.Counter0LC (one zero stop shift_one Word push_zeros classify)

def ctr : PartialMachine := BB6.Agent6F0.child ⟨true,true,1⟩ ⟨false,true,3⟩
theorem shift_two (k : Nat) : rep one k ++ [true,true] = [true,true] ++ rep one k := by
  calc
    rep one k ++ [true,true] = (rep one k ++ [true]) ++ [true] := by rw [List.append_assoc]; rfl
    _ = _ := by rw [shift_one,List.append_assoc,shift_one,← List.append_assoc]; rfl

theorem d_one (L R : List Bool) : run0 ctr 9 ⟨3,[true]++one++L,R⟩ = some ⟨3,[true]++L,one++R⟩ := rfl
theorem c_one (L R : List Bool) : run0 ctr 3 ⟨2,[true]++L,one++R⟩ = some ⟨2,[true]++zero++L,R⟩ := rfl
theorem turn_zero (L R : List Bool) : run0 ctr 5 ⟨3,zero++L,[true]++R⟩ = some ⟨2,[true]++one++L,R⟩ := rfl
theorem turn_overflow (R : List Bool) : run0 ctr 25 ⟨3,one++stop,[true]++R⟩ = some ⟨2,[true]++one++stop,[true,true]++R⟩ := rfl
theorem d_scan (k : Nat) (L R : List Bool) :
    run0 ctr (9*k) ⟨3,rep one k++[true]++L,R⟩ = some ⟨3,[true]++L,rep one k++R⟩ := by
  have H := sweepL ctr 3 [true] [] one one 9 (by intro L R; simpa only [List.nil_append] using d_one L R) k L R
  rw [shift_one]
  simpa only [List.nil_append] using H

theorem core (k : Nat) (L R : List Bool) :
    run0 ctr (12*k+14) ⟨3,rep one (k+1)++zero++L,R⟩ =
      some ⟨2,[true]++rep zero k++one++L,[true,true]++R⟩ := by
  have h1 := d_scan (k+1) ([false,false]++L) R
  have h1' : run0 ctr (9*(k+1)) ⟨3,rep one (k+1)++zero++L,R⟩ =
      some ⟨3,zero++L,rep one (k+1)++R⟩ := by
    simpa only [zero,List.append_assoc,List.cons_append,List.nil_append] using h1
  have h2 := turn_zero L ([true,true]++rep one k++R)
  have h2' : run0 ctr 5 ⟨3,zero++L,rep one (k+1)++R⟩ =
      some ⟨2,[true]++one++L,rep one k++([true,true]++R)⟩ := by
    rw [rep]
    have hEq : [true,true]++rep one k++R = rep one k++([true,true]++R) := by rw [← shift_two,List.append_assoc]
    rw [← hEq]
    simpa only [List.append_assoc,one,List.cons_append,List.nil_append] using h2
  have h3 := sweepR ctr 2 [true] [] one zero 3 (by intro L R; simpa only [List.nil_append] using c_one L R) k (one++L) ([true,true]++R)
  have h3' : run0 ctr (3*k) ⟨2,[true]++one++L,rep one k++([true,true]++R)⟩ =
      some ⟨2,[true]++rep zero k++one++L,[true,true]++R⟩ := by
    simpa only [List.nil_append,List.append_assoc] using h3
  have H := join0 (join0 h1' h2') h3'
  rw [show 9*(k+1)+5+3*k=12*k+14 by omega] at H
  exact H

theorem overflow_core (k : Nat) (R : List Bool) :
    run0 ctr (12*k+37) ⟨3,rep one (k+2)++stop,R⟩ =
      some ⟨2,[true]++rep zero (k+1)++one++stop,[true]++R⟩ := by
  have h1 := d_scan (k+1) ([true,true]++stop) R
  have h1' : run0 ctr (9*(k+1)) ⟨3,rep one (k+2)++stop,R⟩ =
      some ⟨3,one++stop,rep one (k+1)++R⟩ := by
    have heq : rep one (k+2)++stop = rep one (k+1)++[true]++([true,true]++stop) := by
      calc
        rep one (k+2)++stop = (rep one (k+1)++one)++stop := by rw [rep,rep_snoc]
        _ = _ := by simp only [List.append_assoc]; rfl
    rw [heq]
    exact h1
  have h2 := turn_overflow ([true,true]++rep one k++R)
  have h2' : run0 ctr 25 ⟨3,one++stop,rep one (k+1)++R⟩ =
      some ⟨2,[true]++one++stop,rep one (k+1)++([true]++R)⟩ := by
    rw [rep]
    have heq : [true,true]++([true,true]++rep one k++R) = one++(rep one k++([true]++R)) := by
      calc
        _ = one++([true]++rep one k++R) := by simp only [List.append_assoc]; rfl
        _ = _ := by rw [← shift_one,List.append_assoc]
    simp only [List.append_assoc]
    rw [← heq]
    simpa only [one,List.append_assoc,List.cons_append,List.nil_append] using h2
  have h3 := sweepR ctr 2 [true] [] one zero 3 (by intro L R; simpa only [List.nil_append] using c_one L R) (k+1) (one++stop) ([true]++R)
  have h3' : run0 ctr (3*(k+1)) ⟨2,[true]++one++stop,rep one (k+1)++([true]++R)⟩ =
      some ⟨2,[true]++rep zero (k+1)++one++stop,[true]++R⟩ := by
    simpa only [List.nil_append,List.append_assoc] using h3
  have H := join0 (join0 h1' h2') h3'
  rw [show 9*(k+1)+25+3*(k+1)=12*k+37 by omega] at H
  exact H


def digit (b : Bool) : List Bool := if b then one else zero
def rprefix (b : Bool) : List Bool := if b then [true,true,true] else [false,false,true]
def suffix (g : Bool) (n : Nat) : List Bool :=
  (if g then [] else [false,true]) ++ List.replicate n true

def entryCost (g b : Bool) : Nat := (if g then 6 else 12) + (if b then 0 else 2)
def entryR (g b : Bool) : List Bool :=
  match g,b with
  | true,true => [false,false,false,false,true]
  | true,false => [false,false,true,true,true]
  | false,true => [true,false,false,false,true]
  | false,false => [true,false,true,true,true]

def finishCost (g : Bool) : Nat := if g then 10 else 4

theorem enter (g b : Bool) (L R : List Bool) :
    run0 ctr (entryCost g b) ⟨5,[false,false]++digit g++L,rprefix b++R⟩ =
      some ⟨3,one++L,entryR g b++R⟩ := by
  cases g <;> cases b <;> rfl

theorem finishCarry (g b : Bool) (L R : List Bool) :
    run0 ctr (finishCost g) ⟨2,[true]++L,[true,true]++entryR g b++R⟩ =
      some ⟨5,[false,false]++digit g++L,rprefix (!b)++R⟩ := by
  cases g <;> cases b <;> rfl

def config (g b : Bool) (W : List Bool) (n : Nat) : Z0 :=
  ⟨5,[false,false]++digit g++W++stop,rprefix b++suffix g n⟩

theorem carry (g b : Bool) (k n : Nat) (L : List Bool) :
    run0 ctr (entryCost g b+12*k+14+finishCost g)
      (config g b (rep one k++zero++L) n) =
      some (config g (!b) (rep zero k++one++L) n) := by
  have h1 := enter g b (rep one k++zero++L++stop) (suffix g n)
  have h1' : run0 ctr (entryCost g b) (config g b (rep one k++zero++L) n) =
      some ⟨3,rep one (k+1)++zero++(L++stop),entryR g b++suffix g n⟩ := by
    simpa only [config,rep,List.append_assoc] using h1
  have h2 := core k (L++stop) (entryR g b++suffix g n)
  have h3 := finishCarry g b (rep zero k++one++L++stop) (suffix g n)
  have h3' : run0 ctr (finishCost g)
      ⟨2,[true]++rep zero k++one++(L++stop),[true,true]++(entryR g b++suffix g n)⟩ =
      some (config g (!b) (rep zero k++one++L) n) := by
    simpa only [config,List.append_assoc] using h3
  have H := join0 (join0 h1' h2) h3'
  rw [show entryCost g b+(12*k+14)+finishCost g=entryCost g b+12*k+14+finishCost g by omega] at H
  exact H

theorem overflow_prefix (g : Bool) (k n : Nat) :
    run0 ctr (entryCost g true+12*(k+1)+37)
      (config g true (rep one (k+2)) n) =
      some ⟨2,[true]++rep zero (k+2)++one++stop,
        [true]++(entryR g true++suffix g n)⟩ := by
  have h1 := enter g true (rep one (k+2)++stop) (suffix g n)
  have h1' : run0 ctr (entryCost g true) (config g true (rep one (k+2)) n) =
      some ⟨3,rep one (k+3)++stop,entryR g true++suffix g n⟩ := by
    simpa only [config,rep,List.append_assoc] using h1
  have h2 := overflow_core (k+1) (entryR g true++suffix g n)
  have H := join0 h1' h2
  rw [show entryCost g true+(12*(k+1)+37)=entryCost g true+12*(k+1)+37 by omega] at H
  exact H

theorem finishPOverflow (L R : List Bool) :
    run0 ctr 39 ⟨2,[true]++zero++zero++L,[true,false,false,false,false,true]++R⟩ =
      some ⟨5,[false,false]++zero++one++L,[true,true,true,false,true]++R⟩ := rfl

theorem finishQEmpty (L : List Bool) :
    run0 ctr 142 ⟨2,[true]++zero++zero++L,[true,true,false,false,false,true,false,true]⟩ =
      some ⟨5,[false,false]++one++one++one++L,[true,true,true,true,true,true,true,true]⟩ := rfl

theorem finishQNonempty (L R : List Bool) :
    run0 ctr 132 ⟨2,[true]++zero++zero++L,[true,true,false,false,false,true,false,true,true]++R⟩ =
      some ⟨5,[false,false]++one++one++one++L,[true,true,true,true,true]++R⟩ := rfl

theorem overflowP (k n : Nat) :
    run0 ctr (12*k+94) (config true true (rep one (k+2)) n) =
      some (config false true (one++rep zero k++one) n) := by
  have h := overflow_prefix true k n
  have hf := finishPOverflow (rep zero k++one++stop) (List.replicate n true)
  have h' : run0 ctr (6+12*(k+1)+37) (config true true (rep one (k+2)) n) =
      some ⟨2,[true]++zero++zero++(rep zero k++one++stop),
        [true,false,false,false,false,true]++List.replicate n true⟩ := by
    simpa only [entryCost,entryR,suffix,ite_true,List.nil_append,rep,List.append_assoc,
      List.cons_append,Nat.add_zero] using h
  have H := join0 h' hf
  rw [show 6+12*(k+1)+37+39=12*k+94 by omega] at H
  simpa only [config,digit,rprefix,suffix,ite_true,ite_false,Bool.false_eq_true,List.append_assoc,List.nil_append,List.cons_append] using H

def nextN (n : Nat) : Nat := if n=0 then 5 else n+1
def overQCost (n : Nat) : Nat := if n=0 then 203 else 193

theorem overflowQ (k n : Nat) :
    run0 ctr (12*k+overQCost n) (config false true (rep one (k+2)) n) =
      some (config true true (one++one++rep zero k++one) (nextN n)) := by
  have h := overflow_prefix false k n
  have h' : run0 ctr (12+12*(k+1)+37) (config false true (rep one (k+2)) n) =
      some ⟨2,[true]++zero++zero++(rep zero k++one++stop),
        [true,true,false,false,false,true,false,true]++List.replicate n true⟩ := by
    simpa only [entryCost,entryR,suffix,ite_true,ite_false,Bool.false_eq_true,rep,List.append_assoc,
      List.cons_append,List.nil_append,Nat.add_zero] using h
  cases n with
  | zero =>
    have H := join0 h' (finishQEmpty (rep zero k++one++stop))
    rw [show 12+12*(k+1)+37+142=12*k+203 by omega] at H
    simpa only [overQCost,nextN,ite_true,config,digit,rprefix,suffix,List.append_assoc,
      List.cons_append,List.nil_append,List.replicate_succ,List.replicate_zero] using H
  | succ n =>
    have H := join0 h' (finishQNonempty (rep zero k++one++stop) (List.replicate n true))
    rw [show 12+12*(k+1)+37+132=12*k+193 by omega] at H
    simpa only [overQCost,nextN,Nat.succ_ne_zero,ite_false,Bool.false_eq_true,ite_true,config,digit,rprefix,suffix,
      List.append_assoc,List.cons_append,List.nil_append,List.replicate_succ] using H

abbrev State := Bool × Bool × {L : List Bool // Word L} × Nat
def atState (s : State) : Z0 := config s.1 s.2.1 (digit s.2.1++s.2.2.1.val) s.2.2.2

theorem step (s : State) : ∃ p : Nat × State,
    0 < p.1 ∧ run0 ctr p.1 (atState s) = some (atState p.2) := by
  rcases s with ⟨g,b,⟨L,hL⟩,n⟩
  cases b
  · refine ⟨(entryCost g false+14+finishCost g,g,true,⟨L,hL⟩,n),by omega,?_⟩
    simpa only [atState,digit,ite_false,Bool.false_eq_true,ite_true,rep,List.nil_append,Bool.not_false,Nat.mul_zero,Nat.add_zero] using carry g false 0 n L
  · rcases classify hL with ⟨k,T,hT,he⟩ | ⟨k,he⟩
    · refine ⟨(entryCost g true+12*(k+1)+14+finishCost g,g,false,
        ⟨rep zero k++one++T,?_⟩,n),by omega,?_⟩
      · simpa only [List.append_assoc] using push_zeros k (Word.pushOne hT)
      · simpa only [atState,digit,ite_false,Bool.false_eq_true,ite_true,he,rep,List.append_assoc,Bool.not_true] using carry g true (k+1) n T
    · cases g
      · refine ⟨(12*k+overQCost n,true,true,⟨one++rep zero k++one,?_⟩,nextN n),?_ ,?_⟩
        · simpa only [List.append_assoc] using Word.pushOne (push_zeros k Word.last)
        · unfold overQCost; split <;> omega
        · simpa only [atState,digit,ite_true,ite_false,Bool.false_eq_true,he,rep,List.append_assoc] using overflowQ k n
      · refine ⟨(12*k+94,false,true,⟨rep zero k++one,push_zeros k Word.last⟩,n),by omega,?_⟩
        simpa only [atState,digit,ite_true,he,rep,List.append_assoc] using overflowP k n

noncomputable def next (s : State) : Nat × State := Classical.choose (step s)
theorem next_spec (s : State) : 0 < (next s).1 ∧ run0 ctr (next s).1 (atState s) = some (atState (next s).2) := Classical.choose_spec (step s)
noncomputable def states : Nat → State
  | 0 => (true,true,⟨zero++one,Word.pushZero Word.last⟩,0)
  | n+1 => (next (states n)).2

theorem entry : run0 ctr 189 ⟨0,[],[]⟩ = some (atState (states 0)) := rfl
theorem growth (k : Nat) : run0 ctr (next (states k)).1 (atState (states k)) = some (atState (states (k+1))) := (next_spec (states k)).2
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr (fun k => atState (states k)) 189
    (fun k => (next (states k)).1) entry (fun k => (next_spec (states k)).1) growth m hm
theorem cover_oneRB_zeroRD (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))

#print axioms carry
#print axioms overflowP
#print axioms overflowQ
#print axioms step
#print axioms never
#print axioms cover_oneRB_zeroRD
end BB6.Agent6F0.Counter1RB
