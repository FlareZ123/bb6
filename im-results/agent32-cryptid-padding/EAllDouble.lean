import Lean.Elab.Tactic.Omega
import EZeroPair
import EDouble
import BoundaryPadding

set_option maxHeartbeats 5000000

namespace BB6.Agent32EAll

open CryptidBoundary

def start (k q : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+2) true ++
    false :: (pairs q ++ ([true,true,false,false] ++ ys)))

def duration (k q : Nat) : Nat :=
  match q with
  | 0 => 12*k*k+49*k+96
  | r+1 => 12*k*k+49*k+64+4*r

def output (k q : Nat) (ys : List Bool) : Cfg :=
  match q with
  | 0 =>
      ⟨[],false,List.replicate (8*k+3) true ++
        (BB6.Agent32EZero.packetZero ++ ys),5⟩
  | r+1 =>
      ⟨[],false,List.replicate (8*k+5) true ++
        (false :: List.replicate (2*(r+1)+2) true ++
          (false :: List.replicate 6 true ++ ys)),5⟩

/-- All q>=0 E-(10)^q1100 returns, with the crucial distinct q=0 case. -/
theorem all_e_double (k q : Nat) (ys : List Bool) :
    run (duration k q) (start k q ys) = output k q ys := by
  cases q with
  | zero =>
    simpa [duration,start,output,pairs] using
      (BB6.Agent32EZero.full_E_zero_pairs k ys)
  | succ r =>
    simpa [duration,start,output] using
      (BB6.Agent35.full_E_double k r ys)

/-- The same full q>=0 formula with two final implicit blank cells.
    The exact conclusion must use the physically meaningful ObsEq relation. -/
theorem all_e_double_implicit_blank (k q : Nat) :
    BB6.BoundaryPadding.ObsEq
      (run (duration k q)
        (init (List.replicate (3*k+2) true ++
          false :: (pairs q ++ [true,true]))))
      (output k q []) := by
  let xs := List.replicate (3*k+2) true ++
      false :: (pairs q ++ [true,true])
  have hp := BB6.BoundaryPadding.source_init_pad
    (duration k q) 2 xs
  have heq : run (duration k q) (init (xs ++ [false,false])) =
      output k q [] := by
    simpa [start,xs,List.append_assoc] using (all_e_double k q [])
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append] at hp
  rw [heq] at hp
  simpa [xs,List.append_assoc] using hp

#print axioms all_e_double
#print axioms all_e_double_implicit_blank
end BB6.Agent32EAll
