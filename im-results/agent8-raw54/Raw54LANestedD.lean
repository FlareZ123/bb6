import SweepPumping
import Raw54RAClosedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace BB6.Agent8Raw54.LA.NestedD
open BB6Coverage BB6Coverage.Agent31Pump
inductive Variant where | m76 | m77 | m144 | m145 | m161 | m162
  deriving DecidableEq, Repr

def a1 : Variant → Move
  | .m76 | .m144 | .m161 => ⟨false,true,1⟩
  | _ => ⟨false,true,2⟩
def b1 : Variant → Move
  | .m76 | .m77 => ⟨false,true,5⟩
  | _ => ⟨true,true,5⟩
def f0 : Variant → Move
  | .m76 | .m77 => ⟨false,false,0⟩
  | .m144 | .m145 => ⟨false,false,2⟩
  | _ => ⟨true,true,2⟩
def table (v : Variant) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some (a1 v))
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some (b1 v))
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some (f0 v))
  | _,_ => none

def ones : List Bool := [true,true,true]
def zeros : List Bool := [false,false,false]
def stop : List Bool := [false,true,true]
def D (n : Nat) (b : Bool) (L R : List Bool) : Z0 :=
  ⟨3,[false,false,true]++rep ones n++[false,true,b]++L,R⟩
def B (n : Nat) (b : Bool) (L R : List Bool) : Z0 :=
  ⟨1,rep ones (n+1)++[false,true,b]++L,R⟩
def C (b : Bool) (L R : List Bool) : Z0 :=
  ⟨2,[true,true,true,false,true,b]++L,R⟩
def prepCost (v : Variant) (b : Bool) : Nat :=
  match v with
  | .m76 | .m144 => 24
  | .m77 | .m145 => if b then 18 else 20
  | _ => 18
def bCost : Variant → Nat
  | .m161 | .m162 => 3
  | _ => 5

theorem prep (v : Variant) (n : Nat) (b : Bool) (L R : List Bool) :
    run0 (table v) (3+3*(n+1)+1+prepCost v b) (D (n+1) b L R) =
      some (C (!b) L (rep zeros n++stop++R)) := by
  have h0 : run0 (table v) 3 (D (n+1) b L R) =
    some ⟨4,rep ones (n+1)++[false,true,b]++L,stop++R⟩ := by rfl
  have h1 : run0 (table v) (3*(n+1)) ⟨4,rep ones (n+1)++[false,true,b]++L,stop++R⟩ =
    some ⟨4,[false,true,b]++L,rep zeros (n+1)++stop++R⟩ := by
    simpa only [List.nil_append,List.append_assoc] using sweepL (table v) 4 [] [] ones zeros 3
      (by intro X Y; rfl) (n+1) ([false,true,b]++L) (stop++R)
  have h2 : run0 (table v) 1 ⟨4,[false,true,b]++L,rep zeros (n+1)++stop++R⟩ =
    some ⟨0,true::b::L,true::(rep zeros (n+1)++stop++R)⟩ := by rfl
  have h3 : run0 (table v) (prepCost v b) ⟨0,true::b::L,true::(rep zeros (n+1)++stop++R)⟩ =
    some (C (!b) L (rep zeros n++stop++R)) := by
    cases n <;> cases v <;> cases b <;> rfl
  exact join0 (join0 (join0 h0 h1) h2) h3

theorem cStop (v : Variant) (b : Bool) (L R : List Bool) :
    run0 (table v) 3 (C b L (stop++R)) = some (B 1 b L R) := by rfl
theorem cMore (v : Variant) (b : Bool) (L R : List Bool) :
    run0 (table v) 3 (C b L (zeros++R)) = some (D 1 b L R) := by rfl

theorem bStop (v : Variant) (n : Nat) (b : Bool) (L R : List Bool) :
    run0 (table v) (bCost v) (B n b L (stop++R)) = some (B (n+1) b L R) := by
  cases v <;> rfl
theorem bMore (v : Variant) (n : Nat) (b : Bool) (L R : List Bool) :
    run0 (table v) (bCost v) (B n b L (zeros++R)) = some (D (n+1) b L R) := by
  cases v <;> rfl

def Returns (v : Variant) (n : Nat) : Prop :=
  ∀ b L R, ∃ t b', run0 (table v) t (D n b L R) = some (B n b' L R)

theorem drain (v : Variant) (N j k : Nat) (b : Bool) (L R : List Bool)
    (lower : ∀ i, 0 < i → i < N → Returns v i) (hj : 0 < j) (bound : j+k < N) :
    ∃ t b', run0 (table v) t (B j b L (rep zeros k++stop++R)) =
      some (B (j+k+1) b' L R) := by
  induction k generalizing j b with
  | zero => exact ⟨bCost v,b,bStop v j b L R⟩
  | succ k ih =>
    have h := bMore v j b L (rep zeros k++stop++R)
    obtain ⟨u,b',hu⟩ := lower (j+1) (by omega) (by omega) b L (rep zeros k++stop++R)
    obtain ⟨t,b'',ht⟩ := ih (j+1) b' (by omega) (by omega)
    have H := join0 (join0 h hu) ht
    rw [show j+1+k+1=j+(k+1)+1 by omega] at H
    exact ⟨bCost v+u+t,b'',H⟩

theorem returns (v : Variant) (N : Nat) (hN : 0 < N) : Returns v N := by
  induction N using Nat.strongRecOn with
  | ind N ih =>
    cases N with
    | zero => omega
    | succ n =>
      intro b L R
      have hp := prep v n b L R
      cases n with
      | zero => exact ⟨_,!b,join0 hp (cStop v (!b) L R)⟩
      | succ k =>
        have h0 := cMore v (!b) L (rep zeros k++stop++R)
        have lower : ∀ i, 0 < i → i < k+2 → Returns v i := fun i hi hil => ih i hil hi
        obtain ⟨u,b',hu⟩ := lower 1 (by omega) (by omega) (!b) L (rep zeros k++stop++R)
        obtain ⟨t,b'',ht⟩ := drain v (k+2) 1 k b' L R lower (by omega) (by omega)
        have H := join0 (join0 (join0 hp h0) hu) ht
        rw [show 1+k+1=k+1+1 by omega] at H
        exact ⟨_,b'',H⟩

theorem sectionReturn (v : Variant) (n : Nat) (b : Bool) :
    ∃ t b', 0 < t ∧ run0 (table v) t (D (n+1) b [] []) = some (D (n+2) b' [] []) := by
  obtain ⟨t,b',h⟩ := returns v (n+1) (by omega) b [] []
  have h' : run0 (table v) (bCost v) (B (n+1) b' [] []) = some (D (n+2) b' [] []) := by cases v <;> rfl
  exact ⟨t+bCost v,b',by cases v <;> simp [bCost] <;> omega,join0 h h'⟩

def entryCost : Variant → Nat
  | .m76 | .m144 => 63
  | .m77 | .m145 => 55
  | _ => 51

theorem entry (v : Variant) : run0 (table v) (entryCost v) ⟨0,[],[]⟩ = some (D 2 false [] []) := by
  cases v <;> rfl

theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  apply BB6.Agent8Raw54.RAClosed.neverOfSection (table v) (Nat × Bool)
    (fun w => D (w.1+1) w.2 [] []) (1,false) (entryCost v) (entry v) _ m hm
  intro w
  obtain ⟨t,b',hp,h⟩ := sectionReturn v w.1 w.2
  exact ⟨t,(w.1+1,b'),hp,h⟩
#print axioms returns
#print axioms never
end BB6.Agent8Raw54.LA.NestedD
