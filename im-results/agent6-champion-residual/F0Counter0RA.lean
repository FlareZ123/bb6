import F0Counter0LC
import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Shared two-phase counter invariant for F0=0RA with A1=0LB or 1LD. -/
namespace BB6.Agent6F0.CounterRA
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt
open BB6.Agent6F0.Counter0LC (one zero stop shift_one Word push_zeros classify)
def ctr (a : Bool) : PartialMachine := refine (BB6.Agent6F0.parent ⟨false,true,0⟩) (0,true) (some (if a then ⟨true,false,3⟩ else ⟨false,false,1⟩))
def guard (ph : Bool) : List Bool := if ph then one else zero
def right (ph : Bool) : List Bool := if ph then [true,true,true] else [true,true,true,true,true,true,true,true,false,false,true,true,true]
def rest (ph : Bool) : List Bool := if ph then [false,false,true,true,true] else [true,false,true,true,true,true,true,true,true,true,false,false,true,true,true]
def enterCost (ph : Bool) : Nat := if ph then 15 else 21
def config (ph : Bool) (L : List Bool) : Z0 := ⟨5,[false,false]++guard ph++L++stop,right ph⟩

theorem enter (a ph : Bool) (L : List Bool) : run0 (ctr a) (enterCost ph) ⟨5,[false,false]++guard ph++[true]++L,right ph⟩ = some ⟨3,[true]++L,one++rest ph⟩ := by
  cases a <;> cases ph <;> rfl

theorem d_scan (a : Bool) (L R : List Bool) : run0 (ctr a) 9 ⟨3,[true]++one++L,R⟩ = some ⟨3,[true]++L,one++R⟩ := by
  cases a <;> rfl

theorem f_scan (a : Bool) (L R : List Bool) : run0 (ctr a) 3 ⟨5,[true,false]++L,one++R⟩ = some ⟨5,[true,false]++zero++L,R⟩ := by
  cases a <;> rfl

theorem scanD (a : Bool) (k : Nat) (L R : List Bool) : run0 (ctr a) (9*k) ⟨3,rep one k++[true]++L,R⟩ = some ⟨3,[true]++L,rep one k++R⟩ := by
  have H := sweepL (ctr a) 3 [true] [] one one 9 (d_scan a) k L R
  simpa only [shift_one k,List.append_assoc,List.cons_append,List.nil_append] using H

theorem scanF (a : Bool) (k : Nat) (L R : List Bool) : run0 (ctr a) (3*k) ⟨5,[true,false]++L,rep one k++R⟩ = some ⟨5,[true,false]++rep zero k++L,R⟩ := by
  simpa only [List.nil_append,List.append_assoc] using sweepR (ctr a) 5 [true,false] [] one zero 3 (f_scan a) k L R

theorem turn (a : Bool) (L R : List Bool) : run0 (ctr a) 6 ⟨3,zero++L,[true,true]++R⟩ = some ⟨5,[true,false]++one++L,R⟩ := by
  cases a <;> rfl

theorem finishCarry (a ph : Bool) (L : List Bool) : run0 (ctr a) (if ph then 9 else 3) ⟨5,[true,false]++L,[true]++rest ph⟩ = some ⟨5,[false,false]++guard ph++L,right ph⟩ := by
  cases a <;> cases ph <;> rfl

theorem carry (a ph : Bool) (k : Nat) (L : List Bool) : run0 (ctr a) (12*k+30) (config ph (rep one k++zero++L)) = some (config ph (rep zero k++one++L)) := by
  have h1 := enter a ph (rep one k++zero++L++stop).tail
  have h1' : run0 (ctr a) (enterCost ph) (config ph (rep one k++zero++L)) = some ⟨3,rep one k++zero++L++stop,one++rest ph⟩ := by
    cases k <;> simpa only [config,rep,zero,one,List.append_assoc,List.cons_append,List.nil_append,List.tail_cons] using h1
  have h2 := scanD a k ([false,false]++L++stop) (one++rest ph)
  have h2' : run0 (ctr a) (9*k) ⟨3,rep one k++zero++L++stop,one++rest ph⟩ = some ⟨3,zero++L++stop,rep one k++one++rest ph⟩ := by
    simpa only [zero,List.append_assoc,List.cons_append,List.nil_append] using h2
  have h3 := turn a (L++stop) (rep one k++[true]++rest ph)
  have h3' : run0 (ctr a) 6 ⟨3,zero++L++stop,rep one k++one++rest ph⟩ = some ⟨5,[true,false]++one++L++stop,rep one k++[true]++rest ph⟩ := by
    have he : rep one k ++ one ++ rest ph = [true,true] ++ (rep one k ++ [true] ++ rest ph) := by
      rw [rep_snoc one k]
      simp only [one,List.append_assoc,List.cons_append,List.nil_append]
      have hs := shift_one k
      change rep [true,true,true] k ++ [true] = [true] ++ rep [true,true,true] k at hs
      congr 2
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using congrArg (· ++ rest ph) hs.symm
    rw [he]
    simpa only [List.append_assoc] using h3
  have h4 := scanF a k (one++L++stop) ([true]++rest ph)
  have h5 := finishCarry a ph (rep zero k++one++L++stop)
  have h4' : run0 (ctr a) (3*k) ⟨5,[true,false]++one++L++stop,rep one k++[true]++rest ph⟩ = some ⟨5,[true,false]++rep zero k++one++L++stop,[true]++rest ph⟩ := by
    simpa only [List.append_assoc] using h4
  have h5' : run0 (ctr a) (if ph then 9 else 3) ⟨5,[true,false]++rep zero k++one++L++stop,[true]++rest ph⟩ = some (config ph (rep zero k++one++L)) := by
    simpa only [config,List.append_assoc] using h5
  have H := join0 (join0 (join0 (join0 h1' h2') h3') h4') h5'
  have he : enterCost ph + 9*k + 6 + 3*k + (if ph then 9 else 3) = 12*k+30 := by cases ph <;> simp [enterCost] <;> omega
  rw [he] at H
  exact H

theorem turnOver (a : Bool) (R : List Bool) : run0 (ctr a) 26 ⟨3,one++stop,[true,true,true]++R⟩ = some ⟨5,[true,false]++one++stop,[true,true,true]++R⟩ := by
  cases a <;> rfl

theorem finishP (a : Bool) (L : List Bool) : run0 (ctr a) 92 ⟨5,[true,false]++zero++zero++L,rest true⟩ = some ⟨5,[false,false]++zero++one++L,right false⟩ := by
  cases a <;> rfl

theorem finishQ (a : Bool) (L : List Bool) : run0 (ctr a) 24 ⟨5,[true,false]++L,rest false⟩ = some ⟨5,[false,false]++one++zero++zero++one++L,right true⟩ := by
  cases a <;> rfl

theorem overflowCore (a ph : Bool) (k : Nat) : run0 (ctr a) (enterCost ph+12*k+29) (config ph (rep one (k+1))) = some ⟨5,[true,false]++rep zero (k+1)++one++stop,rest ph⟩ := by
  have h1 := enter a ph ([true,true]++rep one k++stop)
  have h1' : run0 (ctr a) (enterCost ph) (config ph (rep one (k+1))) = some ⟨3,rep one (k+1)++stop,one++rest ph⟩ := by
    simpa only [config,rep,one,List.append_assoc,List.cons_append,List.nil_append] using h1
  have h2 := scanD a k ([true,true]++stop) (one++rest ph)
  have h2' : run0 (ctr a) (9*k) ⟨3,rep one (k+1)++stop,one++rest ph⟩ = some ⟨3,one++stop,rep one (k+1)++rest ph⟩ := by
    have he : rep one (k+1) = rep one k ++ one := by rw [rep,rep_snoc]
    rw [he]
    simpa only [one,List.append_assoc,List.cons_append,List.nil_append] using h2
  have h3 := turnOver a (rep one k++rest ph)
  have h3' : run0 (ctr a) 26 ⟨3,one++stop,rep one (k+1)++rest ph⟩ = some ⟨5,[true,false]++one++stop,rep one (k+1)++rest ph⟩ := by
    simpa only [rep,one,List.append_assoc] using h3
  have h4 := scanF a (k+1) (one++stop) (rest ph)
  have H := join0 (join0 (join0 h1' h2') h3') h4
  rw [show enterCost ph+9*k+26+3*(k+1)=enterCost ph+12*k+29 by omega] at H
  simpa only [List.append_assoc] using H

theorem overflowP (a : Bool) (k : Nat) : run0 (ctr a) (12*k+148) (config true (rep one (k+2))) = some (config false (one++rep zero k++one)) := by
  have H := join0 (overflowCore a true (k+1)) (finishP a (rep zero k++one++stop))
  simp only [enterCost,ite_true] at H
  rw [show 15+12*(k+1)+29+92=12*k+148 by omega] at H
  simpa [config,guard,rep,List.append_assoc] using H

theorem overflowQ (a : Bool) (k : Nat) : run0 (ctr a) (12*k+74) (config false (rep one (k+1))) = some (config true (zero++zero++one++rep zero (k+1)++one)) := by
  have H := join0 (overflowCore a false k) (finishQ a (rep zero (k+1)++one++stop))
  simp [enterCost] at H
  rw [show 21+12*k+29+24=12*k+74 by omega] at H
  simpa [config,guard,List.append_assoc] using H

-- The word has at least two digits, avoiding the exceptional single-digit overflow.
abbrev State := Bool × {L : List Bool // Word L ∧ 6 ≤ L.length}
def atState (s : State) : Z0 := config s.1 s.2.val

theorem len_rep (P : List Bool) (k : Nat) : (rep P k).length = P.length*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rep,ih,Nat.mul_succ,Nat.add_comm]

theorem step (a : Bool) (s : State) : ∃ p : Nat × State, 0 < p.1 ∧ run0 (ctr a) p.1 (atState s) = some (atState p.2) := by
  rcases s with ⟨ph,⟨L,hword,hlen⟩⟩
  rcases classify hword with ⟨k,T,hT,he⟩ | ⟨k,he⟩
  · refine ⟨(12*k+30,ph,⟨rep zero k++one++T,?_,?_⟩),by omega,?_⟩
    · simpa only [List.append_assoc] using push_zeros k (Word.pushOne hT)
    · simp only [he,List.length_append,len_rep,zero,one,List.length_cons,List.length_nil] at hlen ⊢
      omega
    · simpa only [atState,he] using carry a ph k T
  · cases ph
    · refine ⟨(12*k+74,true,⟨zero++zero++one++rep zero (k+1)++one,?_,?_⟩),by omega,?_⟩
      · simpa only [List.append_assoc] using Word.pushZero (Word.pushZero (Word.pushOne (push_zeros (k+1) Word.last)))
      · simp [List.length_append,len_rep,zero,one]
      · simpa only [atState,he] using overflowQ a k
    · cases k with
      | zero => simp [he,rep,one] at hlen
      | succ k =>
        refine ⟨(12*k+148,false,⟨one++rep zero k++one,?_,?_⟩),by omega,?_⟩
        · simpa only [List.append_assoc] using Word.pushOne (push_zeros k Word.last)
        · simp [List.length_append,len_rep,zero,one]
        · simpa only [atState,he,Nat.succ_eq_add_one,Nat.add_assoc] using overflowP a k
noncomputable def next (a : Bool) (s : State) : Nat × State := Classical.choose (step a s)
theorem next_spec (a : Bool) (s : State) : 0 < (next a s).1 ∧ run0 (ctr a) (next a s).1 (atState s) = some (atState (next a s).2) := Classical.choose_spec (step a s)
noncomputable def states (a : Bool) : Nat → State
  | 0 => (true,⟨zero++zero++one++zero++zero++one,by exact Word.pushZero (Word.pushZero (Word.pushOne (Word.pushZero (Word.pushZero Word.last)))),by decide⟩)
  | n+1 => (next a (states a n)).2

theorem entry (a : Bool) : run0 (ctr a) 308 ⟨0,[],[]⟩ = some (atState (states a 0)) := by cases a <;> rfl
theorem growth (a : Bool) (k : Nat) : run0 (ctr a) (next a (states a k)).1 (atState (states a k)) = some (atState (states a (k+1))) := (next_spec a (states a k)).2
theorem never (a : Bool) (m : Machine) (hm : compatible (ctr a) m) : NeverHalts m :=
  never_of_growth (ctr a) (fun k => atState (states a k)) 308
    (fun k => (next a (states a k)).1) (entry a) (fun k => (next_spec a (states a k)).1) (growth a) m hm
theorem cover_zeroRA_pair (B : Nat) (a : Bool) : Cover (WeightedBound B) (ctr a) :=
  .leaf _ (fun m hm => weighted_never B m (never a m hm))
#print axioms carry
#print axioms overflowP
#print axioms overflowQ
#print axioms cover_zeroRA_pair
end BB6.Agent6F0.CounterRA
