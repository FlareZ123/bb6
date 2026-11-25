import F0SiblingCover
import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! F0=1LD, A1=0LD implements a growing little-endian binary counter. -/
namespace BB6.Agent6F0.Counter1LD
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt

def ctr : PartialMachine := refine (BB6.Agent6F0.parent ⟨true,false,3⟩) (0,true) (some ⟨false,false,3⟩)
def one : List Bool := [true,true,true]
def zero : List Bool := [true,false,false]
def stop : List Bool := [false,true,true,true]
def cfg (L : List Bool) : Z0 := ⟨5,[false,false] ++ L ++ stop,[]⟩

theorem shift_one (k : Nat) : rep one k ++ [true] = [true] ++ rep one k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change one ++ rep one k ++ [true] = [true] ++ (one ++ rep one k)
    rw [List.append_assoc,ih]
    rfl

theorem enter (L : List Bool) (h : L.headD false = true) :
    run0 ctr 6 ⟨5,[false,false]++L,[]⟩ = some ⟨3,L,[true,false]⟩ := by
  cases L with
  | nil => simp at h
  | cons b L => cases b <;> simp_all <;> rfl
theorem d_one (L R : List Bool) :
    run0 ctr 9 ⟨3,[true]++one++L,[true]++R⟩ =
      some ⟨3,[true]++L,[true]++one++R⟩ := rfl
theorem c_one (L R : List Bool) :
    run0 ctr 3 ⟨2,[true]++L,one++R⟩ =
      some ⟨2,[true]++zero++L,R⟩ := rfl
theorem c_one_two (L R : List Bool) :
    run0 ctr 3 ⟨2,[true]++L,[true,true]++one++R⟩ =
      some ⟨2,[true]++zero++L,[true,true]++R⟩ := rfl
theorem turn_zero (L R : List Bool) :
    run0 ctr 5 ⟨3,zero++L,[true]++R⟩ =
      some ⟨2,[true]++one++L,R⟩ := rfl
theorem finish_zero (L : List Bool) :
    run0 ctr 1 ⟨2,[true]++L,[false]⟩ =
      some ⟨5,[false,false]++L,[]⟩ := rfl
theorem turn_overflow (R : List Bool) :
    run0 ctr 25 ⟨3,one++stop,[true]++R⟩ =
      some ⟨2,[true]++one++stop,[true,true]++R⟩ := rfl
theorem finish_overflow (L : List Bool) :
    run0 ctr 10 ⟨2,[true]++L,[true,true,false]⟩ =
      some ⟨5,[false,false]++one++L,[]⟩ := rfl

theorem carry (k : Nat) (L : List Bool) :
    run0 ctr (12*k+12) ⟨5,[false,false]++rep one k++zero++L,[]⟩ =
      some ⟨5,[false,false]++rep zero k++one++L,[]⟩ := by
  have h1 := enter (rep one k++zero++L) (by cases k <;> rfl)
  have h2 := sweepL ctr 3 [true] [true] one one 9 d_one k ([false,false]++L) [false]
  have h2' : run0 ctr (9*k) ⟨3,rep one k++zero++L,[true,false]⟩ =
      some ⟨3,zero++L,[true]++rep one k++[false]⟩ := by
    simpa only [zero, List.append_assoc, ← shift_one k, List.cons_append, List.nil_append] using h2
  have h3 := turn_zero L (rep one k++[false])
  have h3' : run0 ctr 5 ⟨3,zero++L,[true]++rep one k++[false]⟩ =
      some ⟨2,[true]++(one++L),rep one k++[false]⟩ := by simpa only [List.append_assoc] using h3
  have h4 := sweepR ctr 2 [true] [] one zero 3 c_one k (one++L) [false]
  have h4' : run0 ctr (3*k) ⟨2,[true]++(one++L),rep one k++[false]⟩ =
      some ⟨2,[true]++(rep zero k++one++L),[false]⟩ := by
    simpa only [List.nil_append,List.append_assoc] using h4
  have h5 := finish_zero (rep zero k++one++L)
  have H := join0 (join0 (join0 (join0 h1 h2') h3') h4') h5
  have ht : 6+9*k+5+3*k+1=12*k+12 := by omega
  rw [ht] at H
  simpa only [List.append_assoc] using H

theorem overflow (k : Nat) :
    run0 ctr (12*k+41) (cfg (rep one (k+1))) =
      some (cfg (one++rep zero k++one)) := by
  have h1 := enter (rep one (k+1)++stop) rfl
  have h2 := sweepL ctr 3 [true] [true] one one 9 d_one k ([true,true]++stop) [false]
  have h2' : run0 ctr (9*k) ⟨3,rep one (k+1)++stop,[true,false]⟩ =
      some ⟨3,one++stop,[true]++rep one k++[false]⟩ := by
    have heq : rep one (k+1) ++ stop = [true] ++ rep one k ++ ([true,true]++stop) := by
      calc
        rep one (k+1) ++ stop = (rep one k ++ one) ++ stop := by rw [rep, rep_snoc]
        _ = (rep one k ++ [true]) ++ ([true,true]++stop) := by simp only [List.append_assoc]; rfl
        _ = _ := by rw [shift_one]
    rw [heq]
    exact h2
  have h3 := turn_overflow (rep one k++[false])
  have h3' : run0 ctr 25 ⟨3,one++stop,[true]++rep one k++[false]⟩ =
      some ⟨2,[true]++(one++stop),[true,true]++rep one k++[false]⟩ := by
    simpa only [List.append_assoc] using h3
  have h4 := sweepR ctr 2 [true] [true,true] one zero 3 c_one_two k (one++stop) [false]
  have h4' : run0 ctr (3*k) ⟨2,[true]++(one++stop),[true,true]++rep one k++[false]⟩ =
      some ⟨2,[true]++(rep zero k++one++stop),[true,true,false]⟩ := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h4
  have h5 := finish_overflow (rep zero k++one++stop)
  have H := join0 (join0 (join0 (join0 h1 h2') h3') h4') h5
  have ht : 6+9*k+25+3*k+10=12*k+41 := by omega
  rw [ht] at H
  simpa only [cfg,List.append_assoc] using H

inductive Word : List Bool → Prop
  | last : Word one
  | pushZero {L : List Bool} : Word L → Word (zero++L)
  | pushOne {L : List Bool} : Word L → Word (one++L)

theorem push_zeros (k : Nat) {L : List Bool} (h : Word L) : Word (rep zero k++L) := by
  induction k with
  | zero => simpa [rep] using h
  | succ k ih => simpa only [rep,List.append_assoc] using Word.pushZero ih

theorem classify {L : List Bool} (h : Word L) :
    (∃ k T, Word T ∧ L = rep one k++zero++T) ∨
      (∃ k, L = rep one (k+1)) := by
  induction h with
  | last => exact Or.inr ⟨0,rfl⟩
  | @pushZero L h ih => exact Or.inl ⟨0,L,h,rfl⟩
  | @pushOne L h ih =>
    rcases ih with ⟨k,T,hT,he⟩ | ⟨k,he⟩
    · exact Or.inl ⟨k+1,T,hT,by rw [he]; simp only [rep,List.append_assoc]⟩
    · exact Or.inr ⟨k+1,by rw [he]; rfl⟩

theorem step_word (w : {L : List Bool // Word L}) :
    ∃ p : Nat × {L : List Bool // Word L},
      0 < p.1 ∧ run0 ctr p.1 (cfg w.val) = some (cfg p.2.val) := by
  rcases w with ⟨L,hL⟩
  rcases classify hL with ⟨k,T,hT,he⟩ | ⟨k,he⟩
  · refine ⟨(12*k+12,⟨rep zero k++one++T,?_⟩),by simp,?_⟩
    · simpa only [List.append_assoc] using push_zeros k (Word.pushOne hT)
    · simpa only [cfg,he,List.append_assoc] using carry k (T++stop)
  · refine ⟨(12*k+41,⟨one++rep zero k++one,?_⟩),by simp,?_⟩
    · simpa only [List.append_assoc] using Word.pushOne (push_zeros k Word.last)
    · simpa only [he] using overflow k

noncomputable def next (w : {L : List Bool // Word L}) : Nat × {L : List Bool // Word L} :=
  Classical.choose (step_word w)
theorem next_spec (w : {L : List Bool // Word L}) :
    0 < (next w).1 ∧ run0 ctr (next w).1 (cfg w.val) = some (cfg (next w).2.val) :=
  Classical.choose_spec (step_word w)
noncomputable def words : Nat → {L : List Bool // Word L}
  | 0 => ⟨one++one, Word.pushOne Word.last⟩
  | n+1 => (next (words n)).2
theorem entry : run0 ctr 53 ⟨0,[],[]⟩ = some (cfg (words 0).val) := rfl
theorem growth (k : Nat) :
    run0 ctr (next (words k)).1 (cfg (words k).val) = some (cfg (words (k+1)).val) :=
  (next_spec (words k)).2
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr (fun k => cfg (words k).val) 53
    (fun k => (next (words k)).1) entry (fun k => (next_spec (words k)).1) growth m hm
theorem cover_oneLD_zeroLD (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))

#print axioms carry
#print axioms overflow
#print axioms step_word
#print axioms entry
#print axioms growth
#print axioms never
#print axioms cover_oneLD_zeroLD
end BB6.Agent6F0.Counter1LD
