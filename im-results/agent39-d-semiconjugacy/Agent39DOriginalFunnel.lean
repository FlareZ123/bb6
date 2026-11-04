import ABridgeCode

/-!
Original-source strengthening of Agent39DCodeFunnel.lean.
The shared primitive interpreter is the unmodified, SHA-256-pinned
CryptidBoundary six-state D0 machine. The inputs and outputs are full
physical tape configurations, not quotient or counter states.
-/

namespace BB6.Agent39Source

open CryptidBoundary

def bTime (k : Nat) : Nat := 12*k*k+49*k+40

def aTime (k : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+6))

def aDelay (k : Nat) (ws : List Bool) : Nat :=
  4 + CryptidA.wordCost (4*k+3) ws + 2*CryptidA.wordInc ws

theorem exact_delay (k : Nat) (ws : List Bool) :
    aTime k ws = bTime k + aDelay k ws := by
  simp only [aTime, bTime, aDelay]
  omega

/--
All mixed 10/111 code words yield two synthetic inputs whose primitive
Turing-machine trajectories meet at exactly the same F/0 configuration.

The B arm begins at I_(3k+2)(0 1^(2d+2) ys).
The A arm begins at I_(3k+3)(0 Code(ws) 0 ys).
Here d=wordInc ws, and I_n has n physical ones to the right.
The B/A time offset is exactly 4+wordCost(4k+3,ws)+2d.
-/
theorem original_coded_funnel (k : Nat) (ws ys : List Bool) :
    run (bTime k)
      (init (List.replicate (3*k) true ++
        false :: (List.replicate (2*CryptidA.wordInc ws+2) true ++ ys))) =
    run (aTime k ws)
      (init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++ (false::ys)))) := by
  change
    run (12*k*k+49*k+40)
      (init (List.replicate (3*k) true ++
        false :: (List.replicate (2*CryptidA.wordInc ws+2) true ++ ys))) =
    run ((12*k*k+41*k+32)+(CryptidA.wordCost (4*k+3) ws +
      (2*((4*k+3)+CryptidA.wordInc ws)+6)))
      (init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++ (false::ys))))
  rw [CryptidBoundary.full_B k, BB6.Agent35.full_A_code k]
  congr 1
  rw [← List.append_assoc, List.replicate_append_replicate]
  have hn : 8*k+9+(2*CryptidA.wordInc ws+2) =
      2*(4*k+3+CryptidA.wordInc ws)+5 := by omega
  rw [hn]

/-- The full future trajectories coincide after the two return times. -/
theorem original_coded_funnel_future (k : Nat) (ws ys : List Bool)
    (j : Nat) :
    run (bTime k+j)
      (init (List.replicate (3*k) true ++
        false :: (List.replicate (2*CryptidA.wordInc ws+2) true ++ ys))) =
    run (aTime k ws+j)
      (init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++ (false::ys)))) := by
  rw [CryptidBoundary.run_add (bTime k) j,
    CryptidBoundary.run_add (aTime k ws) j]
  exact congrArg (run j) (original_coded_funnel k ws ys)

#print axioms exact_delay
#print axioms original_coded_funnel
#print axioms original_coded_funnel_future

end BB6.Agent39Source
