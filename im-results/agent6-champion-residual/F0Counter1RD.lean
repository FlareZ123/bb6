import F0Counter0LE

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! F0=1RD: a fixed Q guard, binary counter word, and three right-tape phases. -/
namespace BB6.Agent6F0.Counter1RD
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt
open BB6.Agent6F0.Counter0LC (one zero stop shift_one Word push_zeros classify)

def ctr : PartialMachine := BB6.Agent6F0.parent ⟨true,true,3⟩

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


theorem enterQ (L R : List Bool) :
    run0 ctr 12 ⟨5,[false,false]++zero++L,[true]++R⟩ =
      some ⟨3,one++L,[true,false,true]++R⟩ := rfl

theorem enterEmpty (L : List Bool) :
    run0 ctr 22 ⟨5,[false,false]++zero++L,[]⟩ =
      some ⟨3,one++L,[true,false,true,true,true,true]⟩ := rfl

theorem finishCarry (L R : List Bool) :
    run0 ctr 4 ⟨2,[true]++L,[true,true,true,false]++R⟩ =
      some ⟨5,[false,false]++zero++L,R⟩ := rfl

theorem finishThree (L : List Bool) :
    run0 ctr 13 ⟨2,[true]++zero++L,[true,true,false,true,true,true]⟩ =
      some ⟨5,[false,false]++zero++one++zero++L,[]⟩ := rfl

theorem finishFour (L : List Bool) :
    run0 ctr 63 ⟨2,[true]++zero++L,[true,true,false,true,true,true,true]⟩ =
      some ⟨5,[false,false]++zero++zero++one++L,[true,true,true]⟩ := rfl

inductive Phase where
  | empty | three | four

def right : Phase → List Bool
  | .empty => []
  | .three => [true,true,true]
  | .four => [true,true,true,true]

def nextCarry : Phase → Phase
  | .empty => .four
  | p => p

def entryCost : Phase → Nat
  | .empty => 22
  | _ => 12

def config (ph : Phase) (L : List Bool) : Z0 :=
  ⟨5,[false,false]++zero++L++stop,right ph⟩

theorem enter_phase (ph : Phase) (L : List Bool) :
    run0 ctr (entryCost ph) ⟨5,[false,false]++zero++L,right ph⟩ =
      some ⟨3,one++L,[true,false]++right (nextCarry ph)⟩ := by
  cases ph <;> rfl

theorem carry_phase (ph : Phase) (k : Nat) (L : List Bool) :
    run0 ctr (entryCost ph+12*k+18) (config ph (rep one k++zero++L)) =
      some (config (nextCarry ph) (rep zero k++one++L)) := by
  have h1 := enter_phase ph (rep one k++zero++L++stop)
  have h1' : run0 ctr (entryCost ph) (config ph (rep one k++zero++L)) =
      some ⟨3,rep one (k+1)++zero++(L++stop),[true,false]++right (nextCarry ph)⟩ := by
    simpa only [config,rep,List.append_assoc] using h1
  have h2 := core k (L++stop) ([true,false]++right (nextCarry ph))
  have h3 := finishCarry (rep zero k++one++L++stop) (right (nextCarry ph))
  have h3' : run0 ctr 4
      ⟨2,[true]++rep zero k++one++(L++stop),[true,true]++([true,false]++right (nextCarry ph))⟩ =
      some (config (nextCarry ph) (rep zero k++one++L)) := by
    simpa only [config,List.append_assoc,List.cons_append,List.nil_append] using h3
  have H := join0 (join0 h1' h2) h3'
  rw [show entryCost ph+(12*k+14)+4=entryCost ph+12*k+18 by omega] at H
  exact H

theorem overflow_phase_core (ph : Phase) (k : Nat) :
    run0 ctr (entryCost ph+12*k+37) (config ph (rep one (k+1))) =
      some ⟨2,[true]++rep zero (k+1)++one++stop,[true,true,false]++right (nextCarry ph)⟩ := by
  have h1 := enter_phase ph (rep one (k+1)++stop)
  have h1' : run0 ctr (entryCost ph) (config ph (rep one (k+1))) =
      some ⟨3,rep one (k+2)++stop,[true,false]++right (nextCarry ph)⟩ := by
    simpa only [config,rep,List.append_assoc] using h1
  have h2 := overflow_core k ([true,false]++right (nextCarry ph))
  have H := join0 h1' h2
  rw [show entryCost ph+(12*k+37)=entryCost ph+12*k+37 by omega] at H
  exact H

def nextOverflow : Phase → Phase
  | .three => .empty
  | _ => .three

def overflowWord (ph : Phase) (k : Nat) : List Bool :=
  match ph with
  | .three => one++rep zero (k+1)++one
  | _ => zero++one++rep zero k++one

def finishCost : Phase → Nat
  | .three => 13
  | _ => 63

theorem overflow_phase (ph : Phase) (k : Nat) :
    run0 ctr (entryCost ph+12*k+37+finishCost ph) (config ph (rep one (k+1))) =
      some (config (nextOverflow ph) (overflowWord ph k)) := by
  have h := overflow_phase_core ph k
  cases ph
  · have hf := finishFour (rep zero k++one++stop)
    exact join0 h hf
  · have hf := finishThree (rep zero k++one++stop)
    exact join0 h hf
  · have hf := finishFour (rep zero k++one++stop)
    exact join0 h hf

abbrev State := Phase × {L : List Bool // Word L}
def atState (s : State) : Z0 := config s.1 s.2.val

theorem overflowWord_good (ph : Phase) (k : Nat) : Word (overflowWord ph k) := by
  cases ph
  · simpa only [overflowWord,List.append_assoc] using Word.pushZero (Word.pushOne (push_zeros k Word.last))
  · simpa only [overflowWord,List.append_assoc] using Word.pushOne (push_zeros (k+1) Word.last)
  · simpa only [overflowWord,List.append_assoc] using Word.pushZero (Word.pushOne (push_zeros k Word.last))

theorem step (s : State) : ∃ p : Nat × State,
    0 < p.1 ∧ run0 ctr p.1 (atState s) = some (atState p.2) := by
  rcases s with ⟨ph,⟨L,hword⟩⟩
  rcases classify hword with ⟨k,T,hT,he⟩ | ⟨k,he⟩
  · refine ⟨(entryCost ph+12*k+18,nextCarry ph,⟨rep zero k++one++T,?_⟩),by omega,?_⟩
    · simpa only [List.append_assoc] using push_zeros k (Word.pushOne hT)
    · simpa only [atState,he] using carry_phase ph k T
  · refine ⟨(entryCost ph+12*k+37+finishCost ph,nextOverflow ph,
      ⟨overflowWord ph k,overflowWord_good ph k⟩),by omega,?_⟩
    simpa only [atState,he] using overflow_phase ph k

noncomputable def next (s : State) : Nat × State := Classical.choose (step s)
theorem next_spec (s : State) : 0 < (next s).1 ∧ run0 ctr (next s).1 (atState s) = some (atState (next s).2) := Classical.choose_spec (step s)
noncomputable def states : Nat → State
  | 0 => (.four,⟨zero++one++zero++one,Word.pushZero (Word.pushOne (Word.pushZero Word.last))⟩)
  | n+1 => (next (states n)).2

theorem entry : run0 ctr 214 ⟨0,[],[]⟩ = some (atState (states 0)) := rfl
theorem growth (k : Nat) : run0 ctr (next (states k)).1 (atState (states k)) = some (atState (states (k+1))) := (next_spec (states k)).2
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr (fun k => atState (states k)) 214
    (fun k => (next (states k)).1) entry (fun k => (next_spec (states k)).1) growth m hm
theorem cover_oneRD (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))

#print axioms carry_phase
#print axioms overflow_phase
#print axioms step
#print axioms never
#print axioms cover_oneRD
end BB6.Agent6F0.Counter1RD
