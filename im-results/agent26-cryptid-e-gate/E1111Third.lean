import Lean.Elab.Tactic.Omega
import E1111ThenE
import CryptidTriplePairs

namespace BB6.Agent26ETriple

open CryptidBoundary
open BB6.Agent26EFour
open BB6.Agent26E1101010111
open BB6.Agent26EThenB

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- The second E return of the k=3t+1 exceptional family, at t=3v+1,
    reaches the all-q original-source E triple-pair scanner grammar. -/
theorem next_triple (v q : Nat) (ys : List Bool) :
    (⟨[],false,
      [true,true,true,true] ++
        (List.replicate (2*((4*(8*(3*v+1)+3)+1)+1)) true ++
         restTail (List.replicate (2*q+2) true ++ tail ys)),5⟩ : Cfg) =
    init (List.replicate (3*(64*v+31)+2) true ++
      false :: (pairs 2 ++
        ([true,true,true] ++ (List.replicate (2*q) true ++ tail ys)))) := by
  have hones :
      [true,true,true,true] ++
        (List.replicate (2*((4*(8*(3*v+1)+3)+1)+1)) true ++
          [true]) =
       [true,true] ++ List.replicate (3*(64*v+31)+2) true := by
    have hc : 4 + 2*((4*(8*(3*v+1)+3)+1)+1)+1 =
         2+(3*(64*v+31)+2) := by omega
    calc
      _ = List.replicate (4 + 2*((4*(8*(3*v+1)+3)+1)+1)+1) true := by
        simp [←List.replicate_append_replicate,List.append_assoc]
      _ = List.replicate (2+(3*(64*v+31)+2)) true := by rw [hc]
      _ = [true,true] ++ List.replicate (3*(64*v+31)+2) true := by
        rw [←List.replicate_append_replicate]
        rfl
  have htwos : List.replicate (2*q+2) true =
      [true,true] ++ List.replicate (2*q) true := by
    have hn : 2*q+2=2+2*q := by omega
    rw [hn, ←List.replicate_append_replicate]
    rfl
  have hr :
    [true,true,true,true] ++
        (List.replicate (2*((4*(8*(3*v+1)+3)+1)+1)) true ++
         restTail (List.replicate (2*q+2) true ++ tail ys)) =
    [true,true] ++ (List.replicate (3*(64*v+31)+2) true ++
      (false :: (pairs 2 ++
        ([true,true,true] ++ (List.replicate (2*q) true ++ tail ys))))) := by
    calc
      _ = ([true,true,true,true] ++
          (List.replicate (2*((4*(8*(3*v+1)+3)+1)+1)) true ++ [true])) ++
         ([false,true,false,true,false,true] ++
            (List.replicate (2*q+2) true ++ tail ys)) := by
            simp [restTail,List.append_assoc]
      _ = ([true,true] ++ List.replicate (3*(64*v+31)+2) true) ++
         ([false,true,false,true,false,true] ++
            (List.replicate (2*q+2) true ++ tail ys)) := by rw [hones]
      _ = _ := by simp [htwos,pairs,List.append_assoc]
  exact congrArg (fun r : List Bool => (⟨[],false,r,5⟩ : Cfg)) hr

/-- Three consecutive exact original-source F/0 endpoints:
    E exceptional, E1111, and the E triple-pair return. -/
theorem e_three_returns (v q : Nat) (ys : List Bool) :
    run (
      ((12*(3*(3*v+1)+1)*(3*(3*v+1)+1)+
         49*(3*(3*v+1)+1)+80+4*q) +
       (12*(8*(3*v+1)+3)*(8*(3*v+1)+3)+
         49*(8*(3*v+1)+3)+58)) +
      (12*(64*v+31)*(64*v+31)+49*(64*v+31)+58+6*2))
      (init (List.replicate (3*(3*(3*v+1)+1)+2) true ++
        false :: (pairs q ++ wordE ys))) =
      ⟨[],false,List.replicate (8*(64*v+31)+9) true ++
        (oppairs (2+2) ++
          (false :: (List.replicate (2*q) true ++ tail ys))),5⟩ := by
  rw [run_add,e_then_e (3*v+1) q ys]
  rw [next_triple]
  exact full_E_triple_pairs (64*v+31) 2
    (List.replicate (2*q) true ++ tail ys)

/-- All-natural polynomial primitive duration, arbitrary physical suffix. -/
theorem e_three_polynomial (v q : Nat) (ys : List Bool) :
    run (57036*v*v+59569*v+15638+4*q)
      (init (List.replicate (27*v+14) true ++
        false :: (pairs q ++ wordE ys))) =
      ⟨[],false,List.replicate (512*v+257) true ++
        (oppairs 4 ++
          (false :: (List.replicate (2*q) true ++ tail ys))),5⟩ := by
  have ht :
      ((12*(3*(3*v+1)+1)*(3*(3*v+1)+1)+
         49*(3*(3*v+1)+1)+80+4*q) +
       (12*(8*(3*v+1)+3)*(8*(3*v+1)+3)+
         49*(8*(3*v+1)+3)+58)) +
      (12*(64*v+31)*(64*v+31)+49*(64*v+31)+58+6*2) =
      57036*v*v+59569*v+15638+4*q := by
    have h3 : v*(3*(3*v)) = 9*(v*v) := by ac_rfl
    have h8 : v*(8*(3*v)) = 24*(v*v) := by ac_rfl
    have h64 : v*(64*v)=64*(v*v) := by ac_rfl
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,h3,h8,h64]
    omega
  rw [←ht]
  simpa only [
    show 3*(3*(3*v+1)+1)+2=27*v+14 by omega,
    show 8*(64*v+31)+9=512*v+257 by omega,
    show 2+2=4 by omega] using e_three_returns v q ys

#print axioms next_triple
#print axioms e_three_returns
#print axioms e_three_polynomial

end BB6.Agent26ETriple
