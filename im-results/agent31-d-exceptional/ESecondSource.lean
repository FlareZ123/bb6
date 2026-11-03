import Lean.Elab.Tactic.Omega
import EDouble
import CryptidTriplePairs
import BoundaryPadding

set_option maxHeartbeats 5000000
set_option maxRecDepth 2048

namespace BB6.Agent31SecondSource

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def firstCost (t h : Nat) : Nat :=
  let k := 3*t+1
  12*k*k + 49*k + 64 + 4*(h+1)

def secondCost (t : Nat) : Nat :=
  let K := 8*t+3
  12*K*K + 49*K + 58

/-- Literal E input, with the last two blank cells left implicit. -/
def start (t h : Nat) : Cfg :=
  let k := 3*t+1
  init (List.replicate (3*k+2) true ++
    false :: (pairs (h+2) ++ [true,true]))

def middle (t h : Nat) : Cfg :=
  let k := 3*t+1
  ⟨[], false, List.replicate (8*k+5) true ++
    (false :: List.replicate (2*h+6) true ++
    (false :: List.replicate 6 true)), 5⟩

def finish (t h : Nat) : Cfg :=
  let K := 8*t+3
  ⟨[], false, List.replicate (8*K+9) true ++
    (oppairs 2 ++ false :: (List.replicate (2*h+3) true ++
    (false :: List.replicate 6 true))), 5⟩

/-- Original-machine source E double applied after physically null padding. -/
theorem first_source (t h : Nat) :
    ObsEq (run (firstCost t h) (start t h)) (middle t h) := by
  let k := 3*t+1
  let p := h+1
  let xs := List.replicate (3*k+2) true ++
    false :: (pairs (p+1) ++ [true,true])
  have hp := source_init_pad (12*k*k+49*k+64+4*p) 2 xs
  have hl : 2*(p+1)+2 = 2*h+6 := by dsimp [p]; omega
  have heq :
      run (12*k*k+49*k+64+4*p)
        (init (xs ++ List.replicate 2 false)) = middle t h := by
    have hx := BB6.Agent35.full_E_double k p []
    rw [hl] at hx
    simpa [xs, middle, k, p, List.append_assoc] using hx
  rw [heq] at hp
  simpa [start, firstCost, k, p, xs] using hp

/-- Original-machine source E triple branch on the exact first output. -/
theorem second_source (t h : Nat) :
    run (secondCost t) (middle t h) = finish t h := by
  let K := 8*t+3
  let ys := List.replicate (2*h+3) true ++
    (false :: List.replicate 6 true)
  have hmid : middle t h =
      init (List.replicate (3*K+2) true ++
        false :: (pairs 0 ++ ([true,true,true] ++ ys))) := by
    have hnum : 8*(3*t+1)+5 = 3*K+4 := by dsimp [K]; omega
    have hones : 2*h+6 = 3+(2*h+3) := by omega
    have hrepl : List.replicate (3*K+4) true =
        true::true::List.replicate (3*K+2) true := by
      have hv : 3*K+4 = 2+(3*K+2) := by omega
      rw [hv]
      calc
        _ = List.replicate 2 true ++ List.replicate (3*K+2) true :=
          (List.replicate_append_replicate).symm
        _ = _ := rfl
    dsimp [middle]
    rw [hnum, hones, hrepl]
    have hthree : List.replicate (3+(2*h+3)) true =
        [true,true,true] ++ List.replicate (2*h+3) true := by
      calc
        _ = List.replicate 3 true ++ List.replicate (2*h+3) true :=
          (List.replicate_append_replicate).symm
        _ = _ := rfl
    rw [hthree]
    rfl
  rw [hmid]
  simpa [secondCost, finish, K, ys, pairs, oppairs,
    List.append_assoc] using (full_E_triple_pairs K 0 ys)

/-- Two exact original source-macro returns, all t,h; the start has an
    implicit blank tail. No first-return minimality is asserted here. -/
theorem two_returns_source (t h : Nat) :
    ObsEq (run (firstCost t h + secondCost t) (start t h))
      (finish t h) := by
  have hs : ObsEq (run (secondCost t) (middle t h)) (finish t h) := by
    rw [second_source t h]
    exact cfgEq_refl _
  exact source_chain (firstCost t h) (secondCost t)
    (start t h) (middle t h) (finish t h) (first_source t h) hs

#print axioms first_source
#print axioms second_source
#print axioms two_returns_source
end BB6.Agent31SecondSource
