import ClosedGrowth
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace BB6.Agent28Raw36D101Odometer
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent29ClosedGrowth

/-- First unresolved literal of the direct Raw36 D1=0LB frontier:
    1RB1LB_1RC1LE_0RD0RF_0LD0LB_1LF---_0LA0RF.
    The sole undefined row is E1. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true  => some (some ⟨false,false,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true  => some (some ⟨false,true,5⟩)
  | _,_ => none

abbrev H  : List Bool := [false,false,true]
abbrev Z  : List Bool := [false,false,false]
abbrev R0 : List Bool := [false,true,true,false,false,false]
abbrev RT : List Bool := [true,true,false,false,false]

/-- Little-endian radix-four digit encodings. -/
abbrev D0 : List Bool := [true,false,false,true]
abbrev D1 : List Bool := [true,true,false,true]
abbrev D2 : List Bool := [true,false,false,false]
abbrev D3 : List Bool := [true,true,false,false]

/-- Blocks used while a carry sweeps left and then returns right. -/
abbrev S : List Bool := [false,true,true,true]
abbrev I : List Bool := [true,true,true,false]
abbrev C : List Bool := [false,false,true,true]

abbrev T0 : List Bool := [true]
abbrev T1 : List Bool := [true,true]

def frame (L : List Bool) : Z0 := ⟨0,H++L,Z⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (frame T0) := by rfl

theorem prelude (L : List Bool) :
    run0 table 21 (frame L) = some ⟨0,L,R0⟩ := by rfl

theorem scanOne (L R : List Bool) :
    run0 table 4 ⟨0,D3++L,R⟩ = some ⟨0,L,S++R⟩ := by rfl

theorem scanMany (k : Nat) (L : List Bool) :
    run0 table (4*k) ⟨0,rep D3 k++L,R0⟩ =
      some ⟨0,L,rep S k++R0⟩ := by
  simpa only [List.nil_append,List.append_assoc] using
    (sweepL table 0 [] [] D3 S 4 scanOne k L R0)

theorem boundary0 (L R : List Bool) :
    run0 table 4 ⟨0,D0++L,[false,true,true]++R⟩ =
      some ⟨0,[false,true,false,true]++L,[false,true,true]++R⟩ := by rfl

theorem boundary1 (L R : List Bool) :
    run0 table 8 ⟨0,D1++L,[false,true,true]++R⟩ =
      some ⟨0,[false,false,false,false]++L,[false,true,true]++R⟩ := by rfl

theorem boundary2 (L R : List Bool) :
    run0 table 4 ⟨0,D2++L,[false,true,true]++R⟩ =
      some ⟨0,[false,true,false,false]++L,[false,true,true]++R⟩ := by rfl

theorem boundaryT0 (R : List Bool) :
    run0 table 4 ⟨0,T0,[false,true,true]++R⟩ =
      some ⟨0,[false,true],[false,true,true]++R⟩ := by rfl

theorem boundaryT1 (R : List Bool) :
    run0 table 10 ⟨0,T1,[false,true,true]++R⟩ =
      some ⟨0,[false,false,false,true,true],[false,true,true]++R⟩ := by rfl

theorem returnOne (L R : List Bool) :
    run0 table 6 ⟨0,[false]++L,[false]++I++R⟩ =
      some ⟨0,[false]++C++L,[false]++R⟩ := by rfl

theorem returnMany (k : Nat) (L R : List Bool) :
    run0 table (6*k) ⟨0,[false]++L,[false]++rep I k++R⟩ =
      some ⟨0,[false]++rep C k++L,[false]++R⟩ := by
  simpa only [List.append_assoc] using
    (sweepR table 0 [false] [false] I C 6 returnOne k L R)

theorem finish (L : List Bool) :
    run0 table 5 ⟨0,[false]++L,R0⟩ = some (frame ([true]++L)) := by rfl

theorem rightLayout (k : Nat) :
    rep S k++R0 = [false]++rep I k++RT := by
  have h := rotate false [true,true,true] k
  have h' := congrArg (fun x : List Bool => x++RT) h.symm
  simpa only [S,I,R0,RT,List.append_assoc,List.cons_append,List.nil_append] using h'

theorem leftLayout (k : Nat) :
    [true]++rep C k = rep D0 k++[true] := by
  simpa only [C,D0,List.cons_append,List.nil_append] using
    (rotate true [false,false,true] k)

def scanTail : Nat → List Bool
  | 0 => [false,false,false]
  | k+1 => [true]++rep S k++R0

theorem scanPrefix (k : Nat) :
    rep S k++R0 = [false,true,true]++scanTail k := by
  cases k <;> rfl

private theorem return0 (k : Nat) (L : List Bool) :
    run0 table (6*k)
      ⟨0,[false,true,false,true]++L,rep S k++R0⟩ =
      some ⟨0,[false]++rep C k++[true,false,true]++L,R0⟩ := by
  rw [rightLayout k]
  simpa only [R0,RT,List.append_assoc,List.cons_append,List.nil_append] using
    (returnMany k ([true,false,true]++L) RT)

private theorem return1 (k : Nat) (L : List Bool) :
    run0 table (6*k)
      ⟨0,[false,false,false,false]++L,rep S k++R0⟩ =
      some ⟨0,[false]++rep C k++[false,false,false]++L,R0⟩ := by
  rw [rightLayout k]
  simpa only [R0,RT,List.append_assoc,List.cons_append,List.nil_append] using
    (returnMany k ([false,false,false]++L) RT)

private theorem return2 (k : Nat) (L : List Bool) :
    run0 table (6*k)
      ⟨0,[false,true,false,false]++L,rep S k++R0⟩ =
      some ⟨0,[false]++rep C k++[true,false,false]++L,R0⟩ := by
  rw [rightLayout k]
  simpa only [R0,RT,List.append_assoc,List.cons_append,List.nil_append] using
    (returnMany k ([true,false,false]++L) RT)

private theorem returnT0 (k : Nat) :
    run0 table (6*k) ⟨0,[false,true],rep S k++R0⟩ =
      some ⟨0,[false]++rep C k++[true],R0⟩ := by
  rw [rightLayout k]
  simpa only [R0,RT,List.append_assoc,List.cons_append,List.nil_append] using
    (returnMany k [true] RT)

private theorem returnT1 (k : Nat) :
    run0 table (6*k) ⟨0,[false,false,false,true,true],rep S k++R0⟩ =
      some ⟨0,[false]++rep C k++[false,false,true,true],R0⟩ := by
  rw [rightLayout k]
  simpa only [R0,RT,List.append_assoc,List.cons_append,List.nil_append] using
    (returnMany k [false,false,true,true] RT)

theorem carry0 (k : Nat) (L : List Bool) :
    run0 table (30+10*k) (frame (rep D3 k++D0++L)) =
      some (frame (rep D0 k++D1++L)) := by
  have h1 := prelude (rep D3 k++D0++L)
  have h2 := scanMany k (D0++L)
  simp only [List.append_assoc] at h1 h2
  have h3 := boundary0 L (scanTail k)
  rw [← scanPrefix k] at h3
  have h4 := return0 k L
  have h5 := finish (rep C k++[true,false,true]++L)
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [leftLayout k] at H
  simpa only [frame,D0,D1,List.append_assoc,
    show 21+4*k+4+6*k+5=30+10*k by omega] using H

theorem carry1 (k : Nat) (L : List Bool) :
    run0 table (34+10*k) (frame (rep D3 k++D1++L)) =
      some (frame (rep D0 k++D2++L)) := by
  have h1 := prelude (rep D3 k++D1++L)
  have h2 := scanMany k (D1++L)
  simp only [List.append_assoc] at h1 h2
  have h3 := boundary1 L (scanTail k)
  rw [← scanPrefix k] at h3
  have h4 := return1 k L
  have h5 := finish (rep C k++[false,false,false]++L)
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [leftLayout k] at H
  simpa only [frame,D0,D2,List.append_assoc,
    show 21+4*k+8+6*k+5=34+10*k by omega] using H

theorem carry2 (k : Nat) (L : List Bool) :
    run0 table (30+10*k) (frame (rep D3 k++D2++L)) =
      some (frame (rep D0 k++D3++L)) := by
  have h1 := prelude (rep D3 k++D2++L)
  have h2 := scanMany k (D2++L)
  simp only [List.append_assoc] at h1 h2
  have h3 := boundary2 L (scanTail k)
  rw [← scanPrefix k] at h3
  have h4 := return2 k L
  have h5 := finish (rep C k++[true,false,false]++L)
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [leftLayout k] at H
  simpa only [frame,D0,D3,List.append_assoc,
    show 21+4*k+4+6*k+5=30+10*k by omega] using H

theorem carryT0 (k : Nat) :
    run0 table (30+10*k) (frame (rep D3 k++T0)) =
      some (frame (rep D0 k++T1)) := by
  have h1 := prelude (rep D3 k++T0)
  have h2 := scanMany k T0
  have h3 := boundaryT0 (scanTail k)
  rw [← scanPrefix k] at h3
  have h4 := returnT0 k
  have h5 := finish (rep C k++[true])
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  simp only [← List.append_assoc] at H
  rw [leftLayout k] at H
  simpa only [frame,D0,T0,T1,List.append_assoc,
    show 21+4*k+4+6*k+5=30+10*k by omega] using H

theorem carryT1 (k : Nat) :
    run0 table (36+10*k) (frame (rep D3 k++T1)) =
      some (frame (rep D0 k++D0++T0)) := by
  have h1 := prelude (rep D3 k++T1)
  have h2 := scanMany k T1
  have h3 := boundaryT1 (scanTail k)
  rw [← scanPrefix k] at h3
  have h4 := returnT1 k
  have h5 := finish (rep C k++[false,false,true,true])
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  simp only [← List.append_assoc] at H
  rw [leftLayout k] at H
  simpa only [frame,D0,T0,T1,List.append_assoc,
    show 21+4*k+10+6*k+5=36+10*k by omega] using H

inductive Digits where
  | t0 : Digits
  | t1 : Digits
  | d0 : Digits → Digits
  | d1 : Digits → Digits
  | d2 : Digits → Digits
  | d3 : Digits → Digits
  deriving DecidableEq, Repr

def encode : Digits → List Bool
  | .t0 => T0
  | .t1 => T1
  | .d0 r => D0++encode r
  | .d1 r => D1++encode r
  | .d2 r => D2++encode r
  | .d3 r => D3++encode r

def pad0 : Nat → Digits → Digits
  | 0,r => r
  | k+1,r => .d0 (pad0 k r)

theorem pad0_encode (k : Nat) (r : Digits) :
    encode (pad0 k r) = rep D0 k++encode r := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pad0,encode,rep,ih,List.append_assoc]

theorem classify (d : Digits) :
    (∃ k r, encode d = rep D3 k++D0++encode r) ∨
    (∃ k r, encode d = rep D3 k++D1++encode r) ∨
    (∃ k r, encode d = rep D3 k++D2++encode r) ∨
    (∃ k, encode d = rep D3 k++T0) ∨
    (∃ k, encode d = rep D3 k++T1) := by
  induction d with
  | t0 => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨0,rfl⟩)))
  | t1 => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0,rfl⟩)))
  | d0 r ih => exact Or.inl ⟨0,r,rfl⟩
  | d1 r ih => exact Or.inr (Or.inl ⟨0,r,rfl⟩)
  | d2 r ih => exact Or.inr (Or.inr (Or.inl ⟨0,r,rfl⟩))
  | d3 r ih =>
    rcases ih with ⟨k,u,h⟩ | ⟨k,u,h⟩ | ⟨k,u,h⟩ | ⟨k,h⟩ | ⟨k,h⟩
    · exact Or.inl ⟨k+1,u,by simp [encode,h,rep,List.append_assoc]⟩
    · exact Or.inr (Or.inl ⟨k+1,u,by simp [encode,h,rep,List.append_assoc]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨k+1,u,by simp [encode,h,rep,List.append_assoc]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k+1,by simp [encode,h,rep,List.append_assoc]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k+1,by simp [encode,h,rep,List.append_assoc]⟩)))

theorem progress (d : Digits) :
    ∃ cost next, 0 < cost ∧
      run0 table cost (frame (encode d)) = some (frame (encode next)) := by
  rcases classify d with ⟨k,r,h⟩ | ⟨k,r,h⟩ | ⟨k,r,h⟩ | ⟨k,h⟩ | ⟨k,h⟩
  · refine ⟨30+10*k,pad0 k (.d1 r),by omega,?_⟩
    simpa only [h,pad0_encode,encode,List.append_assoc] using carry0 k (encode r)
  · refine ⟨34+10*k,pad0 k (.d2 r),by omega,?_⟩
    simpa only [h,pad0_encode,encode,List.append_assoc] using carry1 k (encode r)
  · refine ⟨30+10*k,pad0 k (.d3 r),by omega,?_⟩
    simpa only [h,pad0_encode,encode,List.append_assoc] using carry2 k (encode r)
  · refine ⟨30+10*k,pad0 k .t1,by omega,?_⟩
    simpa only [h,pad0_encode,encode,List.append_assoc] using carryT0 k
  · refine ⟨36+10*k,pad0 k (.d0 .t0),by omega,?_⟩
    simpa only [h,pad0_encode,encode,List.append_assoc] using carryT1 k

def inv (z : Z0) : Prop := ∃ d : Digits, z = frame (encode d)

theorem next (z : Z0) (hz : inv z) :
    ∃ cost z', 0 < cost ∧ run0 table cost z = some z' ∧ inv z' := by
  obtain ⟨d,rfl⟩ := hz
  obtain ⟨cost,d',hc,hr⟩ := progress d
  exact ⟨cost,frame (encode d'),hc,hr,⟨d',rfl⟩⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_invariant table inv 14 (frame T0) entry
  · exact ⟨.t0,rfl⟩
  · exact next
  · exact hm

/-- Direct Cover adapter for the Raw36 parent proof. Nonhalting satisfies
    every finite weighted threshold. -/
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf table (fun m hm => weighted_never B m (never m hm))

#print axioms entry
#print axioms scanMany
#print axioms carry0
#print axioms carry1
#print axioms carry2
#print axioms carryT0
#print axioms carryT1
#print axioms progress
#print axioms never
#print axioms cover
end BB6.Agent28Raw36D101Odometer
