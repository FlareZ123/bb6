import Lean.Elab.Tactic.Omega
import EDouble
import BoundaryPadding

namespace BB6.Agent26EDoubleThenB

open CryptidBoundary
open BB6.BoundaryPadding

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def sixTail (ys : List Bool) : List Bool :=
  false :: List.replicate 6 true ++ ys

private theorem first_to_B (t r : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t)+5) true ++
      (false :: List.replicate (2*(r+1)+2) true ++ sixTail ys),5⟩ : Cfg) =
    init (List.replicate (3*(8*t+1)) true ++
      false :: (List.replicate (2*(r+1)+2) true ++ sixTail ys)) := by
  have hrep : List.replicate (8*(3*t)+5) true =
      true :: true :: List.replicate (3*(8*t+1)) true := by
    have hn : 8*(3*t)+5=2+3*(8*t+1) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(8*t+1)) true := by
        rw [List.replicate_append_replicate]
      _ = _ := by rfl
  rw [hrep]
  rfl

theorem two_section (t r : Nat) (ys : List Bool) :
    run ((12*(3*t)*(3*t)+49*(3*t)+64+4*r) +
      (12*(8*t+1)*(8*t+1)+49*(8*t+1)+40))
      (init (List.replicate (3*(3*t)+2) true ++
        false :: (pairs (r+1) ++ ([true,true,false,false] ++ ys)))) =
      ⟨[],false,List.replicate (8*(8*t+1)+9) true ++
        (List.replicate (2*(r+1)+2) true ++ sixTail ys),5⟩ := by
  rw [run_add, BB6.Agent35.full_E_double (3*t) r ys]
  change run _ (⟨[],false,List.replicate (8*(3*t)+5) true ++
      (false :: List.replicate (2*(r+1)+2) true ++ sixTail ys),5⟩ : Cfg) = _
  rw [first_to_B]
  exact full_B (8*t+1) (List.replicate (2*(r+1)+2) true ++ sixTail ys)

/-- Every k divisible by three and every q>=2 returns to the L language
    after two original-machine F/0 sections, for any finite further tail. -/
theorem two_section_polynomial (t r : Nat) (ys : List Bool) :
    run (876*t*t+731*t+165+4*r)
      (init (List.replicate (9*t+2) true ++
        false :: (pairs (r+1) ++ ([true,true,false,false] ++ ys)))) =
      ⟨[],false,List.replicate (64*t+2*r+21) true ++ sixTail ys,5⟩ := by
  have ht :
      (12*(3*t)*(3*t)+49*(3*t)+64+4*r) +
      (12*(8*t+1)*(8*t+1)+49*(8*t+1)+40) =
      876*t*t+731*t+165+4*r := by
    have h1 : 12*(3*t)*(3*t)=108*(t*t) := by
      calc
        _ = (12*3*3)*(t*t) := by ac_rfl
        _ = _ := by rfl
    have h2 : 12*(8*t+1)*(8*t+1)=768*(t*t)+192*t+12 := by
      calc
        _ = 12*(8*t)*(8*t)+2*12*(8*t)+12 := by
          simp only [Nat.mul_add,Nat.add_mul]
          omega
        _ = (12*8*8)*(t*t)+(2*12*8)*t+12 := by ac_rfl
        _ = _ := by rfl
    rw [h1,h2]
    simp only [Nat.mul_add,Nat.mul_assoc]
    omega
  have hrep : List.replicate (8*(8*t+1)+9) true ++
      (List.replicate (2*(r+1)+2) true ++ sixTail ys) =
      List.replicate (64*t+2*r+21) true ++ sixTail ys := by
    rw [←List.append_assoc,List.replicate_append_replicate]
    congr 1
    omega
  rw [←ht]
  simpa only [show 9*t+2=3*(3*t)+2 by omega,hrep] using two_section t r ys

/-- In the genuine infinite-blank tape, the source input needs only
    (01)^(r+2)1; the extra two terminal zeros are observationally irrelevant. -/
theorem two_section_physical (t r : Nat) :
    ObsEq
      (run (876*t*t+731*t+165+4*r)
        (init (List.replicate (9*t+2) true ++
          false :: (pairs (r+1) ++ [true,true]))))
      (⟨[],false,List.replicate (64*t+2*r+21) true ++
        sixTail ([] : List Bool),5⟩ : Cfg) := by
  let xs := List.replicate (9*t+2) true ++
    false :: (pairs (r+1) ++ [true,true])
  have hp := source_init_pad (876*t*t+731*t+165+4*r) 2 xs
  have hpad : xs ++ List.replicate 2 false =
    List.replicate (9*t+2) true ++
      false :: (pairs (r+1) ++ ([true,true,false,false] ++ ([] : List Bool))) := by
    simp [xs,List.append_assoc]
  rw [hpad, two_section_polynomial t r ([] : List Bool)] at hp
  exact hp

#print axioms two_section
#print axioms two_section_polynomial
#print axioms two_section_physical

end BB6.Agent26EDoubleThenB
