import FastFAR
import SweepPumping
import WeightedTNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1Stack
open BB6Coverage BB6Coverage.Agent31Pump

def ctr (b : Bool) : PartialMachine := FAR.fromCodes [7,21,11,24,14,10,3,16,12,11,if b then 17 else 3,9]
abbrev P : List Bool := [true,false]
abbrev h : List Bool := [true]
abbrev f : List Bool := [false]
abbrev Z2 : List Bool := [false,false]
abbrev Z4 : List Bool := [false,false,false,false]
def mark (b : Bool) : List Bool := if b then f else [false,true,false]
def gap (b : Bool) : List Bool := if b then Z2 else Z4
def d (b : Bool) : Nat := if b then 2 else 0
def crossCost (b : Bool) : Nat := if b then 11 else 6
def crossWidth (b : Bool) : Nat := if b then 2 else 1
def u (n : Nat) : List Bool := List.replicate n true
theorem u_succ (n : Nat) : u (n+1) = true :: u n := rfl
theorem u_add (a b : Nat) : u (a+b) = u a ++ u b := by
  induction a with
  | zero => simp [u]
  | succ a ih => rw [show a+1+b=a+b+1 by omega,u_succ,u_succ,ih]; rfl

theorem e_one (b : Bool) (L R : List Bool) :
    run0 (ctr b) 3 ⟨4,h++L,f++R⟩ = some ⟨4,L,f++h++R⟩ := by cases b <;> rfl

theorem e_sweep (b : Bool) (n : Nat) (L R : List Bool) :
    run0 (ctr b) (3*n) ⟨4,u n++L,f++R⟩ = some ⟨4,L,f++u n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have H := join0 (e_one b (u n++L) R) (ih (h++R))
    rw [show 3+3*n=3*(n+1) by omega] at H
    change run0 (ctr b) (3*(n+1)) ⟨4,u (n+1)++L,f++R⟩ = some ⟨4,L,f++u n++(u 1++R)⟩ at H
    simp only [List.append_assoc] at H ⊢
    rw [← List.append_assoc (u n) (u 1) R,←u_add] at H
    exact H

theorem f_one (b : Bool) (L R : List Bool) :
    run0 (ctr b) 5 ⟨5,P++L,h++R⟩ = some ⟨5,P++h++L,R⟩ := by cases b <;> rfl

theorem f_sweep (b : Bool) (n : Nat) (L R : List Bool) :
    run0 (ctr b) (5*n) ⟨5,P++L,u n++R⟩ = some ⟨5,P++u n++L,R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have H := join0 (f_one b L (u n++R)) (ih (h++L))
    rw [show 5+5*n=5*(n+1) by omega] at H
    change run0 (ctr b) (5*(n+1)) ⟨5,P++L,u (n+1)++R⟩ = some ⟨5,P++u n++(u 1++L),R⟩ at H
    simp only [List.append_assoc] at H ⊢
    rw [← List.append_assoc (u n) (u 1) L,←u_add] at H
    exact H

theorem cross (b : Bool) (L R : List Bool) :
    run0 (ctr b) (crossCost b) ⟨5,P++h++L,Z2++u 3++R⟩ =
      some ⟨5,P++u (crossWidth b)++mark b++h++L,u (crossWidth b)++R⟩ := by cases b <;> rfl

theorem four (b : Bool) (L R : List Bool) :
    run0 (ctr b) (15+d b) ⟨5,P++h++L,Z4++u 3++R⟩ = some ⟨4,L,f++Z2++u 7++R⟩ := by cases b <;> rfl

theorem finish (b : Bool) (L : List Bool) :
    run0 (ctr b) (19+d b) ⟨5,P++h++L,[]⟩ = some ⟨4,L,f++Z4++u 3⟩ := by cases b <;> rfl

theorem pop (b : Bool) (L R : List Bool) :
    run0 (ctr b) (4-d b) ⟨4,mark b++h++L,f++R⟩ = some ⟨4,L,f++gap b++R⟩ := by cases b <;> rfl

theorem turn (b : Bool) (R : List Bool) :
    run0 (ctr b) 11 ⟨4,[],f++u 3++R⟩ = some ⟨5,P++h,u 5++R⟩ := by cases b <;> rfl

-- The first width is the current unary block minus its one-cell guard.
-- Every saved block has an extra guard and the variant-specific delimiter.
inductive Active (b : Bool) : Nat → List Bool → Prop
  | root (n : Nat) : Active b (n+4) []
  | push (n : Nat) {m : Nat} {L : List Bool} : Active b m L →
      Active b (n+5+d b) (mark b++u (m+1)++L)

inductive Tail : List Bool → Prop
  | nil : Tail []
  | two (n : Nat) {R : List Bool} : Tail R → Tail (Z2++u (n+7)++R)
  | four (n : Nat) {R : List Bool} : Tail R → Tail (Z4++u (n+3)++R)

def fc (m : Nat) (L R : List Bool) : Z0 := ⟨5,P++u (m+1)++L,R⟩
def ec (m : Nat) (L R : List Bool) : Z0 := ⟨4,u m++L,f++R⟩

inductive Inv (b : Bool) : Z0 → Prop
  | f {m L R} : Active b m L → Tail R → Inv b (fc m L R)
  | e {m L R} : Active b m L → Tail R → Inv b (ec m L R)

theorem cross_sweep (b : Bool) (m n : Nat) (L R : List Bool) :
    run0 (ctr b) (crossCost b+5*(n+4+crossWidth b)) (fc m L (Z2++u (n+7)++R)) =
      some (fc (n+5+d b) (mark b++u (m+1)++L) R) := by
  have H1 := cross b (u m++L) (u (n+4)++R)
  have H1' : run0 (ctr b) (crossCost b) (fc m L (Z2++u (n+7)++R)) =
      some ⟨5,P++u (crossWidth b)++(mark b++u (m+1)++L),u (n+4+crossWidth b)++R⟩ := by
    have e1 : u 3++u (n+4)=u (n+7) := by rw [←u_add]; congr 1; omega
    have e2 : u (crossWidth b)++u (n+4)=u (n+4+crossWidth b) := by rw [←u_add,Nat.add_comm]
    simp only [fc,List.append_assoc] at H1 ⊢
    rw [←List.append_assoc (u 3) (u (n+4)) R,e1,←List.append_assoc (u (crossWidth b)) (u (n+4)) R,e2] at H1
    simpa only [u_succ,List.cons_append,List.append_assoc,List.nil_append] using H1
  have H2 := f_sweep b (n+4+crossWidth b) (u (crossWidth b)++(mark b++u (m+1)++L)) R
  have H2' : run0 (ctr b) (5*(n+4+crossWidth b)) ⟨5,P++u (crossWidth b)++(mark b++u (m+1)++L),u (n+4+crossWidth b)++R⟩ =
      some (fc (n+5+d b) (mark b++u (m+1)++L) R) := by
    have e : u (n+4+crossWidth b)++u (crossWidth b) = u (n+5+d b+1) := by
      rw [←u_add]; congr 1; cases b <;> simp [crossWidth,d] <;> omega
    simp only [fc,List.append_assoc] at H2 ⊢
    rw [←List.append_assoc (u (n+4+crossWidth b)) (u (crossWidth b)),e] at H2
    exact H2
  exact join0 H1' H2'

theorem four_run (b : Bool) (m n : Nat) (L R : List Bool) :
    run0 (ctr b) (15+d b) (fc m L (Z4++u (n+3)++R)) = some (ec m L (Z2++u (n+7)++R)) := by
  have H := four b (u m++L) (u n++R)
  simp only [fc,ec,List.append_assoc] at H ⊢
  rw [←List.append_assoc (u 3) (u n),←u_add,show 3+n=n+3 by omega,←List.append_assoc (u 7) (u n),←u_add,show 7+n=n+7 by omega] at H
  simpa only [u_succ,List.cons_append,List.append_assoc,List.nil_append] using H

theorem finish_run (b : Bool) (m : Nat) (L : List Bool) :
    run0 (ctr b) (19+d b) (fc m L []) = some (ec m L (Z4++u 3)) := by
  simpa only [fc,ec,List.append_assoc,u_succ,List.cons_append,List.nil_append] using finish b (u m++L)

theorem root_run (b : Bool) (n : Nat) (R : List Bool) :
    run0 (ctr b) (8*(n+4)+21) (ec (n+4) [] R) = some (fc (n+6) [] R) := by
  have H1 : run0 (ctr b) (3*(n+4)) (ec (n+4) [] R) = some ⟨4,[],f++u (n+4)++R⟩ := e_sweep b _ [] R
  have H2 : run0 (ctr b) 11 ⟨4,[],f++u (n+4)++R⟩ = some ⟨5,P++h,u (n+6)++R⟩ := by
    have H := turn b (u (n+1)++R)
    simp only [List.append_assoc] at H ⊢
    rw [←List.append_assoc (u 3) (u (n+1)),←u_add,show 3+(n+1)=n+4 by omega,←List.append_assoc (u 5) (u (n+1)),←u_add,show 5+(n+1)=n+6 by omega] at H
    exact H
  have H3 : run0 (ctr b) (5*(n+6)) ⟨5,P++h,u (n+6)++R⟩ = some (fc (n+6) [] R) := by
    have H := f_sweep b (n+6) h R
    change run0 (ctr b) (5*(n+6)) ⟨5,P++h,u (n+6)++R⟩ = some ⟨5,P++u (n+6)++u 1,R⟩ at H
    rw [List.append_assoc P,←u_add] at H
    simpa only [fc,List.append_nil] using H
  have H := join0 (join0 H1 H2) H3
  rwa [show 3*(n+4)+11+5*(n+6)=8*(n+4)+21 by omega] at H

theorem pop_run (b : Bool) (m n : Nat) (L R : List Bool) :
    run0 (ctr b) (3*(n+5+d b)+(4-d b)) (ec (n+5+d b) (mark b++u (m+1)++L) R) =
      some (ec m L (gap b++u (n+5+d b)++R)) := by
  have H1 := e_sweep b (n+5+d b) (mark b++u (m+1)++L) R
  have H2 := pop b (u m++L) (u (n+5+d b)++R)
  have H2' : run0 (ctr b) (4-d b) ⟨4,mark b++u (m+1)++L,f++u (n+5+d b)++R⟩ = some (ec m L (gap b++u (n+5+d b)++R)) := by
    simpa only [ec,List.append_assoc,u_succ,List.cons_append,List.nil_append] using H2
  exact join0 H1 H2'

theorem tail_pop (b : Bool) (n : Nat) {R : List Bool} (hR : Tail R) : Tail (gap b++u (n+5+d b)++R) := by
  cases b
  · change Tail (Z4++u (n+5)++R)
    exact Tail.four (n+2) hR
  · change Tail (Z2++u (n+7)++R)
    exact Tail.two n hR

theorem progress (b : Bool) {z : Z0} (hz : Inv b z) : ∃ n z', 0<n ∧ run0 (ctr b) n z = some z' ∧ Inv b z' := by
  cases hz with
  | @f m L R ha ht =>
    cases ht with
    | nil => exact ⟨_,_,by omega,finish_run b m L,Inv.e ha (by simpa only [List.append_nil] using Tail.four 0 Tail.nil)⟩
    | @two n R ht => exact ⟨_,_,by cases b <;> simp [crossCost,crossWidth] <;> omega,cross_sweep b m n L R,Inv.f (Active.push n ha) ht⟩
    | @four n R ht => exact ⟨_,_,by omega,four_run b m n L R,Inv.e ha (Tail.two n ht)⟩
  | @e m L R ha ht =>
    cases ha with
    | root n => exact ⟨_,_,by omega,root_run b n R,Inv.f (Active.root (n+2)) ht⟩
    | @push n m L ha => exact ⟨_,_,by cases b <;> simp [d] <;> omega,pop_run b m n L R,Inv.e ha (tail_pop b n ht)⟩

theorem entry (b : Bool) : run0 (ctr b) 38 ⟨0,[],[]⟩ = some (fc 4 [] []) := by cases b <;> rfl

theorem initial (b : Bool) : Inv b (fc 4 [] []) := Inv.f (Active.root 0) Tail.nil

theorem next_exists (b : Bool) (z : {z : Z0 // Inv b z}) :
    ∃ p : Nat × {z : Z0 // Inv b z}, 0<p.1 ∧ run0 (ctr b) p.1 z.val = some p.2.val := by
  obtain ⟨n,t,hn,hr,ht⟩ := progress b z.property
  exact ⟨(n,⟨t,ht⟩),hn,hr⟩
noncomputable def next (b : Bool) (z : {z : Z0 // Inv b z}) := Classical.choose (next_exists b z)
theorem next_sound (b : Bool) (z : {z : Z0 // Inv b z}) :
    0<(next b z).1 ∧ run0 (ctr b) (next b z).1 z.val = some (next b z).2.val := Classical.choose_spec (next_exists b z)
noncomputable def orbit (b : Bool) : Nat → {z : Z0 // Inv b z}
  | 0 => ⟨fc 4 [] [],initial b⟩
  | n+1 => (next b (orbit b n)).2

open BB6.Agent13BlankDelay
theorem never (b : Bool) (m : Machine) (hm : compatible (ctr b) m) : NeverHalts m :=
  never_of_growth (ctr b) (fun k => (orbit b k).val) 38 (fun k => (next b (orbit b k)).1) (entry b)
    (fun k => (next_sound b (orbit b k)).1) (fun k => (next_sound b (orbit b k)).2) m hm
theorem cover (b : Bool) (B : Nat) : Cover (WeightedBound B) (ctr b) :=
  .leaf _ (fun m hm => weighted_never B m (never b m hm))

#print axioms progress
#print axioms entry
#print axioms next_sound
#print axioms never
#print axioms cover
end BB6.Agent6C1Stack
