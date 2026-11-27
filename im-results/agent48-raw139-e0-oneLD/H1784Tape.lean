import SweepPumping
import FastFAR
import WeightedNonhaltLeafAdapter

namespace BB6Coverage.Agent48.H1784
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4096
set_option maxHeartbeats 0

def ctr : PartialMachine := FAR.fromCodes [7,24,11,13,14,23,20,16,14,11,5,1]

-- Zipper words have implicit infinite zero continuation.
def cell : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: L, k+1 => cell L k

def Same (L R : List Bool) : Prop := ∀ k, cell L k = cell R k

theorem same_refl (L : List Bool) : Same L L := fun _ => rfl
theorem same_symm {L R : List Bool} (h : Same L R) : Same R L :=
  fun k => (h k).symm
theorem same_trans {L M R : List Bool} (h : Same L M) (g : Same M R) : Same L R :=
  fun k => (h k).trans (g k)

theorem same_cons (b : Bool) {L R : List Bool} (h : Same L R) :
    Same (b::L) (b::R) := by
  intro k
  cases k with
  | zero => rfl
  | succ k => exact h k

theorem same_head {L R : List Bool} (h : Same L R) :
    L.headD false = R.headD false := by
  cases L <;> cases R <;> exact h 0

theorem same_tail {L R : List Bool} (h : Same L R) : Same L.tail R.tail := by
  intro k
  cases L <;> cases R <;> exact h (k+1)

theorem same_append (P : List Bool) {L R : List Bool} (h : Same L R) :
    Same (P++L) (P++R) := by
  induction P with
  | nil => exact h
  | cons b P ih => exact same_cons b ih

theorem same_nil_zero : Same [] [false] := by
  intro k
  cases k <;> rfl

theorem same_zero (L : List Bool) : Same L (L++[false]) := by
  have h := same_append L same_nil_zero
  simpa only [List.append_nil] using h

def EqZ (x y : Z0) : Prop := x.q = y.q ∧ Same x.l y.l ∧ Same x.r y.r

theorem eq_refl (x : Z0) : EqZ x x := ⟨rfl,same_refl _,same_refl _⟩
theorem eq_symm {x y : Z0} (h : EqZ x y) : EqZ y x :=
  ⟨h.1.symm,same_symm h.2.1,same_symm h.2.2⟩
theorem eq_trans {x y z : Z0} (h : EqZ x y) (g : EqZ y z) : EqZ x z :=
  ⟨h.1.trans g.1,same_trans h.2.1 g.2.1,same_trans h.2.2 g.2.2⟩

theorem move_eq (mv : Move) {x y : Z0} (h : EqZ x y) :
    EqZ (move0 mv x) (move0 mv y) := by
  unfold move0
  split
  · refine ⟨rfl,?_,same_tail h.2.2⟩
    rw [same_head h.2.2]
    exact same_cons _ (same_cons _ (same_tail h.2.1))
  · exact ⟨rfl,same_tail h.2.1,same_cons _ h.2.2⟩

theorem step_eq (p : PartialMachine) {x y z : Z0} (h : EqZ x y)
    (hx : step0 p x = some z) :
    ∃ w, step0 p y = some w ∧ EqZ z w := by
  have hk : (x.q,x.l.headD false) = (y.q,y.l.headD false) :=
    Prod.ext h.1 (same_head h.2.1)
  unfold step0 at hx ⊢
  rw [← hk]
  cases hv : (p (x.q,x.l.headD false)).bind id with
  | none =>
    have bad : (none : Option Z0) = some z := by
      simpa only [hv,Option.map_none] using hx
    contradiction
  | some mv =>
    simp only [hv,Option.map_some,Option.some.injEq] at hx
    refine ⟨move0 mv y,?_,?_⟩
    · simp [hv]
    · rw [← hx]
      exact move_eq mv h

theorem run_eq (p : PartialMachine) (n : Nat) {x y z : Z0} (h : EqZ x y)
    (hx : run0 p n x = some z) :
    ∃ w, run0 p n y = some w ∧ EqZ z w := by
  induction n generalizing x y z with
  | zero =>
    have e : x = z := by simpa only [run0,Option.some.injEq] using hx
    subst z
    exact ⟨y,rfl,h⟩
  | succ n ih =>
    cases hs : step0 p x with
    | none => simp [run0,hs] at hx
    | some u =>
      have hu : run0 p n u = some z := by simpa [run0,hs] using hx
      obtain ⟨v,hv,he⟩ := step_eq p h hs
      obtain ⟨w,hw,her⟩ := ih he hu
      exact ⟨w,by simp [run0,hv,hw],her⟩

def RRun (n : Nat) (x y : Z0) : Prop :=
  ∃ z, run0 ctr n x = some z ∧ EqZ z y

theorem exactR {n : Nat} {x y : Z0} (h : run0 ctr n x = some y) :
    RRun n x y := ⟨y,h,eq_refl _⟩

theorem rjoin {n k : Nat} {x y z : Z0} (h : RRun n x y) (g : RRun k y z) :
    RRun (n+k) x z := by
  obtain ⟨u,hu,he⟩ := h
  obtain ⟨v,hv,hf⟩ := g
  obtain ⟨w,hw,hi⟩ := run_eq ctr k (eq_symm he) hv
  exact ⟨w,join0 hu hw,eq_trans (eq_symm hi) hf⟩

theorem reframe {n : Nat} {x y z : Z0} (h : RRun n x y) (he : EqZ y z) :
    RRun n x z := by
  obtain ⟨u,hu,hf⟩ := h
  exact ⟨u,hu,eq_trans hf he⟩

theorem rstart {n : Nat} {x y z : Z0} (he : EqZ x y) (h : RRun n y z) :
    RRun n x z := by
  obtain ⟨u,hu,hf⟩ := h
  obtain ⟨v,hv,hi⟩ := run_eq ctr n (eq_symm he) hu
  exact ⟨v,hv,eq_trans (eq_symm hi) hf⟩

def Live (x y : Z0) : Prop := ∃ n : Nat, 0<n ∧ RRun n x y

theorem live_join {x y z : Z0} (h : Live x y) (g : Live y z) : Live x z := by
  obtain ⟨n,hn,hr⟩ := h
  obtain ⟨k,hk,hs⟩ := g
  exact ⟨n+k,by omega,rjoin hr hs⟩

def A (L R : List Bool) : Z0 := ⟨0,false::L,R⟩
def F (L R : List Bool) : Z0 := ⟨5,false::L,R⟩
def D (L R : List Bool) : Z0 := ⟨3,true::L,R⟩
abbrev P : List Bool := [false,true,true,false,true]
abbrev Q : List Bool := [true,false,true,true,false]
abbrev U : List Bool := [false,true,true,false]
abbrev K : List Bool := [true,true,false,false]
abbrev V : List Bool := [true,false,true,false]
abbrev W : List Bool := [false,true]
abbrev H : List Bool := [true,false]
abbrev E0 : List Bool := [false,false,true,true]
abbrev E1 : List Bool := [false,true,false,true]

theorem q_one (L R : List Bool) : run0 ctr 7 (A L (Q++R)) = some (A (P++L) R) := rfl
theorem af_one (L R : List Bool) : run0 ctr 6 (A L (V++R)) = some (F ([true,true,false,true]++L) R) := rfl
theorem f_one (L R : List Bool) : run0 ctr 6 (F L (V++R)) = some (F (K++L) R) := rfl
theorem fa_one (L R : List Bool) : run0 ctr 7 (F L (Q++R)) = some (A ([false,true,true,false,false]++L) R) := rfl
theorem turn1 (L : List Bool) : run0 ctr 8 (A L [true]) = some (D L [true,false,true]) := rfl
theorem turn110 (L R : List Bool) : run0 ctr 4 (A L ([true,true,false]++R)) = some (D L ([true,false,false]++R)) := rfl
theorem turn0 (L : List Bool) : run0 ctr 6 (A L []) = some (D L [true,true]) := rfl
theorem turn101 (L : List Bool) : run0 ctr 16 (A L [true,false,true]) = some (D L (Q++[true])) := rfl
theorem turn100 (L R : List Bool) : run0 ctr 8 (A L ([true,false,false]++R)) = some (D L ([true,false,true]++R)) := rfl
theorem turn11 (L : List Bool) : RRun 4 (A L [true,true]) (D L [true]) := by
  refine ⟨D L [true,false],rfl,?_⟩
  exact ⟨rfl,same_refl _,same_symm (same_zero [true])⟩

theorem p_one (L R : List Bool) : run0 ctr 7 (D (P++L) R) = some (D L (Q++R)) := rfl
theorem x_finish (L R : List Bool) : run0 ctr 9 (D ([false,true,true,false,false,true,true]++L) R) = some (A (W++L) (Q++R)) := rfl
theorem w_one (L R : List Bool) : run0 ctr 2 (D (W++L) R) = some (D L (H++R)) := rfl
theorem b_finish (L R : List Bool) : run0 ctr 4 (D (E0++L) R) = some (A (W++L) (H++R)) := rfl
theorem over_turn (R : List Bool) : RRun 6 (D [] R) (F [true,true] R) := by
  refine ⟨F [true,true,false] R,rfl,?_⟩
  exact ⟨rfl,same_symm (same_zero [false,true,true]),same_refl _⟩

theorem over_finish (L R : List Bool) : run0 ctr 6 (F (true::L) ([true,true,false]++R)) = some (A (false::L) ([true,false,false]++R)) := rfl

theorem q_sweep (n : Nat) (L R : List Bool) :
    run0 ctr (7*n) (A L (rep Q n++R)) = some (A (rep P n++L) R) := by
  simpa only [A,List.nil_append,List.cons_append] using
    sweepR ctr 0 [false] [] Q P 7 (by intro L R; rfl) n L R

theorem f_sweep (n : Nat) (L R : List Bool) :
    run0 ctr (6*n) (F L (rep V n++R)) = some (F (rep K n++L) R) := by
  simpa only [F,List.nil_append,List.cons_append] using
    sweepR ctr 5 [false] [] V K 6 (by intro L R; rfl) n L R

theorem p_sweep (n : Nat) (L R : List Bool) :
    run0 ctr (7*n) (D (rep P n++L) R) = some (D L (rep Q n++R)) := by
  simpa only [D,List.nil_append,List.cons_append] using
    sweepL ctr 3 [true] [] P Q 7 (by intro L R; rfl) n L R

theorem w_sweep (n : Nat) (L R : List Bool) :
    run0 ctr (2*n) (D (rep W n++L) R) = some (D L (rep H n++R)) := by
  simpa only [D,List.nil_append,List.cons_append] using
    sweepL ctr 3 [true] [] W H 2 (by intro L R; rfl) n L R

#print axioms run_eq
#print axioms rjoin
#print axioms over_turn
end BB6Coverage.Agent48.H1784
