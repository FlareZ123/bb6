import F0Counter0LC

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Three-phase growing binary counter for F0=0LE. -/
namespace BB6.Agent6F0.Counter0LE
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt
open BB6.Agent6F0.Counter0LC (one zero stop shift_one Word push_zeros classify)

def ctr : PartialMachine := BB6.Agent6F0.parent ⟨false,false,4⟩

theorem shift_two (k : Nat) : rep one k ++ [true,true] = [true,true] ++ rep one k := by
  calc
    rep one k ++ [true,true] = (rep one k ++ [true]) ++ [true] := by rw [List.append_assoc]; rfl
    _ = _ := by rw [shift_one,List.append_assoc,shift_one,← List.append_assoc]; rfl

theorem enter (L R : List Bool) : run0 ctr 2 ⟨5,[false,false]++L,R⟩ = some ⟨3,L,[false,false]++R⟩ := rfl
theorem enterQ (L R : List Bool) : run0 ctr 8 ⟨5,[false,false]++zero++L,R⟩ = some ⟨3,one++L,[true,false]++R⟩ := rfl
theorem d_one (L R : List Bool) : run0 ctr 9 ⟨3,[true]++one++L,R⟩ = some ⟨3,[true]++L,one++R⟩ := rfl
theorem c_one (L R : List Bool) : run0 ctr 3 ⟨2,[true]++L,one++R⟩ = some ⟨2,[true]++zero++L,R⟩ := rfl
theorem turn_zero (L R : List Bool) : run0 ctr 5 ⟨3,zero++L,[true]++R⟩ = some ⟨2,[true]++one++L,R⟩ := rfl
theorem turn_overflow (R : List Bool) : run0 ctr 25 ⟨3,one++stop,[true]++R⟩ = some ⟨2,[true]++one++stop,[true,true]++R⟩ := rfl
theorem finishP (L R : List Bool) : run0 ctr 10 ⟨2,[true]++L,[true,true,false,false]++R⟩ = some ⟨5,[false,false]++one++L,R⟩ := rfl
theorem finishQ (L R : List Bool) : run0 ctr 4 ⟨2,[true]++L,[true,true,true,false]++R⟩ = some ⟨5,[false,false]++zero++L,R⟩ := rfl
theorem finishPoverflow (L : List Bool) : run0 ctr 39 ⟨2,[true]++zero++zero++L,[true,false,false]⟩ = some ⟨5,[false,false]++zero++one++L,[true,true,true]⟩ := rfl
theorem tailTurn (L R : List Bool) : run0 ctr 3 ⟨2,[true]++L,[true,true,false]++R⟩ = some ⟨2,[false]++zero++L,R⟩ := rfl
theorem turnC (L R : List Bool) : run0 ctr 6 ⟨2,[false]++zero++L,R⟩ = some ⟨2,[true]++one++L,R⟩ := rfl
theorem finish1 (L : List Bool) : run0 ctr 1 ⟨2,[true]++L,[]⟩ = some ⟨5,[false,false]++L,[]⟩ := rfl
theorem finish4 (L : List Bool) : run0 ctr 4 ⟨2,[true]++L,[true,true,true]⟩ = some ⟨5,[false,false]++zero++L,[]⟩ := rfl

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

theorem carryP (k : Nat) (L R : List Bool) :
    run0 ctr (12*k+26) ⟨5,[false,false]++one++rep one k++zero++L,R⟩ =
      some ⟨5,[false,false]++one++rep zero k++one++L,R⟩ := by
  have h1 := enter (rep one (k+1)++zero++L) R
  have h2 := core k L ([false,false]++R)
  have h3 := finishP (rep zero k++one++L) R
  have h3' : run0 ctr 10 ⟨2,[true]++rep zero k++one++L,[true,true]++([false,false]++R)⟩ =
      some ⟨5,[false,false]++one++rep zero k++one++L,R⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using h3
  have H := join0 (join0 h1 h2) h3'
  rw [show 2+(12*k+14)+10=12*k+26 by omega] at H
  simpa only [rep,List.append_assoc] using H

theorem carryQ (k : Nat) (L R : List Bool) :
    run0 ctr (12*k+26) ⟨5,[false,false]++zero++rep one k++zero++L,R⟩ =
      some ⟨5,[false,false]++zero++rep zero k++one++L,R⟩ := by
  have h1 := enterQ (rep one k++zero++L) R
  have h1' : run0 ctr 8 ⟨5,[false,false]++zero++rep one k++zero++L,R⟩ =
      some ⟨3,rep one (k+1)++zero++L,[true,false]++R⟩ := by simpa only [rep,List.append_assoc] using h1
  have h2 := core k L ([true,false]++R)
  have h3 := finishQ (rep zero k++one++L) R
  have h3' : run0 ctr 4 ⟨2,[true]++rep zero k++one++L,[true,true]++([true,false]++R)⟩ =
      some ⟨5,[false,false]++zero++rep zero k++one++L,R⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using h3
  have H := join0 (join0 h1' h2) h3'
  rw [show 8+(12*k+14)+4=12*k+26 by omega] at H
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

theorem overflowQ_core (k : Nat) (R : List Bool) :
    run0 ctr (12*k+54) ⟨5,[false,false]++zero++rep one (k+1)++stop,R⟩ =
      some ⟨2,[true]++one++rep zero (k+1)++one++stop,R⟩ := by
  have h1 := enterQ (rep one (k+1)++stop) R
  have h1' : run0 ctr 8 ⟨5,[false,false]++zero++rep one (k+1)++stop,R⟩ =
      some ⟨3,rep one (k+2)++stop,[true,false]++R⟩ := by
    simpa only [rep,List.append_assoc] using h1
  have h2 := overflow_core k ([true,false]++R)
  have h3 := tailTurn (rep zero (k+1)++one++stop) R
  have h3' : run0 ctr 3 ⟨2,[true]++rep zero (k+1)++one++stop,[true]++([true,false]++R)⟩ =
      some ⟨2,[false]++zero++(rep zero (k+1)++one++stop),R⟩ := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using h3
  have h4 := turnC (rep zero (k+1)++one++stop) R
  have H := join0 (join0 (join0 h1' h2) h3') h4
  rw [show 8+(12*k+37)+3+6=12*k+54 by omega] at H
  simpa only [List.append_assoc] using H

theorem overflowQempty (k : Nat) :
    run0 ctr (12*k+55) ⟨5,[false,false]++zero++rep one (k+1)++stop,[]⟩ =
      some ⟨5,[false,false]++one++rep zero (k+1)++one++stop,[]⟩ := by
  have h1 := overflowQ_core k []
  have h2 := finish1 (one++rep zero (k+1)++one++stop)
  have h2' : run0 ctr 1 ⟨2,[true]++one++rep zero (k+1)++one++stop,[]⟩ =
      some ⟨5,[false,false]++one++rep zero (k+1)++one++stop,[]⟩ := by simpa only [List.append_assoc] using h2
  have H := join0 h1 h2'
  exact H

theorem overflowQright (k : Nat) :
    run0 ctr (12*k+58) ⟨5,[false,false]++zero++rep one (k+1)++stop,[true,true,true]⟩ =
      some ⟨5,[false,false]++zero++one++rep zero (k+1)++one++stop,[]⟩ := by
  have h1 := overflowQ_core k [true,true,true]
  have h2 := finish4 (one++rep zero (k+1)++one++stop)
  have h2' : run0 ctr 4 ⟨2,[true]++one++rep zero (k+1)++one++stop,[true,true,true]⟩ =
      some ⟨5,[false,false]++zero++one++rep zero (k+1)++one++stop,[]⟩ := by simpa only [List.append_assoc] using h2
  have H := join0 h1 h2'
  rw [show 12*k+54+4=12*k+58 by omega] at H
  exact H

theorem overflowPempty (k : Nat) :
    run0 ctr (12*k+90) ⟨5,[false,false]++one++rep one (k+2)++stop,[]⟩ =
      some ⟨5,[false,false]++zero++one++rep zero k++one++stop,[true,true,true]⟩ := by
  have h1 := enter (rep one (k+3)++stop) []
  have h1' : run0 ctr 2 ⟨5,[false,false]++one++rep one (k+2)++stop,[]⟩ =
      some ⟨3,rep one (k+3)++stop,[false,false]⟩ := by simpa only [rep,List.append_assoc,List.append_nil] using h1
  have h2 := overflow_core (k+1) [false,false]
  have h3 := finishPoverflow (rep zero k++one++stop)
  have h3' : run0 ctr 39 ⟨2,[true]++rep zero (k+2)++one++stop,[true]++[false,false]⟩ =
      some ⟨5,[false,false]++zero++one++rep zero k++one++stop,[true,true,true]⟩ := by
    simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using h3
  have H := join0 (join0 h1' h2) h3'
  rw [show 2+(12*(k+1)+37)+39=12*k+90 by omega] at H
  exact H

inductive Phase where
  | Pempty | Qempty | Qright

def guard : Phase → List Bool
  | .Pempty => one
  | _ => zero

def right : Phase → List Bool
  | .Qright => [true,true,true]
  | _ => []

def config (ph : Phase) (L : List Bool) : Z0 := ⟨5,[false,false]++guard ph++L++stop,right ph⟩
def Good (L : List Bool) : Prop := Word L ∧ 6 ≤ L.length

theorem rep_len (P : List Bool) (k : Nat) : (rep P k).length = P.length*k := by
  induction k with
  | zero => simp [rep]
  | succ k ih => simp [rep,List.length_append,ih,Nat.mul_succ,Nat.add_comm]

theorem carry_phase (ph : Phase) (k : Nat) (L : List Bool) :
    run0 ctr (12*k+26) (config ph (rep one k++zero++L)) =
      some (config ph (rep zero k++one++L)) := by
  cases ph
  · simpa only [config,guard,right,List.append_assoc] using carryP k (L++stop) []
  · simpa only [config,guard,right,List.append_assoc] using carryQ k (L++stop) []
  · simpa only [config,guard,right,List.append_assoc] using carryQ k (L++stop) [true,true,true]

abbrev State := Phase × {L : List Bool // Good L}
def atState (s : State) : Z0 := config s.1 s.2.val

theorem step (s : State) : ∃ p : Nat × State,
    0 < p.1 ∧ run0 ctr p.1 (atState s) = some (atState p.2) := by
  rcases s with ⟨ph,⟨L,hword,hlen⟩⟩
  rcases classify hword with ⟨k,T,hT,he⟩ | ⟨k,he⟩
  · refine ⟨(12*k+26,ph,⟨rep zero k++one++T,?_,?_⟩),by simp,?_⟩
    · simpa only [List.append_assoc] using push_zeros k (Word.pushOne hT)
    · rw [he] at hlen
      simp only [List.length_append,rep_len,one,zero,List.length_cons,List.length_nil] at hlen ⊢
      omega
    · simpa only [atState,he] using carry_phase ph k T
  · cases ph
    · have hk : 1 ≤ k := by
        rw [he,rep_len] at hlen
        change 6 ≤ 3*(k+1) at hlen
        omega
      obtain ⟨j,hj⟩ : ∃ j, k=j+1 := ⟨k-1,by omega⟩
      refine ⟨(12*j+90,.Qright,⟨one++rep zero j++one,?_,?_⟩),by simp,?_⟩
      · simpa only [List.append_assoc] using Word.pushOne (push_zeros j Word.last)
      · simp [List.length_append,rep_len,one,zero]
      · simpa only [atState,config,guard,right,he,hj,List.append_assoc] using overflowPempty j
    · refine ⟨(12*k+55,.Pempty,⟨rep zero (k+1)++one,?_,?_⟩),by simp,?_⟩
      · exact push_zeros (k+1) Word.last
      · simp [List.length_append,rep_len,one,zero]; omega
      · simpa only [atState,config,guard,right,he,List.append_assoc] using overflowQempty k
    · refine ⟨(12*k+58,.Qempty,⟨one++rep zero (k+1)++one,?_,?_⟩),by simp,?_⟩
      · simpa only [List.append_assoc] using Word.pushOne (push_zeros (k+1) Word.last)
      · simp [List.length_append,rep_len,one,zero]
      · simpa only [atState,config,guard,right,he,List.append_assoc] using overflowQright k

noncomputable def next (s : State) : Nat × State := Classical.choose (step s)
theorem next_spec (s : State) : 0 < (next s).1 ∧ run0 ctr (next s).1 (atState s) = some (atState (next s).2) := Classical.choose_spec (step s)
noncomputable def states : Nat → State
  | 0 => (.Qempty,⟨one++zero++one, by exact ⟨Word.pushOne (Word.pushZero Word.last),by decide⟩⟩)
  | n+1 => (next (states n)).2

theorem entry : run0 ctr 163 ⟨0,[],[]⟩ = some (atState (states 0)) := rfl
theorem growth (k : Nat) : run0 ctr (next (states k)).1 (atState (states k)) = some (atState (states (k+1))) := (next_spec (states k)).2
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr (fun k => atState (states k)) 163
    (fun k => (next (states k)).1) entry (fun k => (next_spec (states k)).1) growth m hm
theorem cover_zeroLE (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))
#print axioms carry_phase
#print axioms overflowPempty
#print axioms overflowQempty
#print axioms overflowQright
#print axioms step
#print axioms never
#print axioms cover_zeroLE
end BB6.Agent6F0.Counter0LE
