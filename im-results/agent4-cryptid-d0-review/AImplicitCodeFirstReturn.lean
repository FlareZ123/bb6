import Lean.Elab.Tactic.Omega
import ACodeFirstReturn
import BoundaryPadding

/-!
# Every finite mixed 10 / 111 A-word followed by implicit blank

Agent2's exact raw code cost and genuine NoF interval are extended to the
original unpadded right-infinite-blank source.  The model-independent source
padding bisimulation transports both endpoints and every intermediate state.
The statement is quantified over arbitrary finite A-code words.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent4AImplicitCode

open CryptidBoundary
open BB6.BoundaryPadding
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn
open BB6.CryptidATenFirstReturn
open BB6.CryptidACodeFirstReturn
open BB6.Agent35

def codeCost (k : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32)+
    (CryptidA.wordCost (4*k+3) ws +
      (2*(4*k+3+CryptidA.wordInc ws)+6))

def implicitStart (k : Nat) (ws : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    (false :: CryptidA.wordCode ws))

/-- Even on the explicitly terminated code, the first F visit is at the
exact final return: the old full_A_mixed_code_first_return asserts only the
weaker physical predicate, but its two component proofs establish NoF. -/
theorem mixed_explicit_noF (k : Nat) (ws ys : List Bool) (t : Nat)
    (htpos : 0<t) (ht : t<codeCost k ws) :
    (run t (mixedStart k ws ys)).st ≠ 5 := by
  by_cases hpref : t<12*k*k+41*k+32
  · change (run t (init (List.replicate (3*k+1) true ++
      false::(CryptidA.wordCode ws ++ false::ys)))).st ≠ 5
    exact prefixA_positive_noF k
      (CryptidA.wordCode ws ++ false::ys) t htpos hpref
  · have hprefix :
      run (12*k*k+41*k+32) (mixedStart k ws ys) =
        aBoundary (4*k+3) (CryptidA.wordCode ws ++ false::ys) := by
      change run (12*k*k+41*k+32)
        (init (List.replicate (3*k+1) true ++
          false::(CryptidA.wordCode ws ++ false::ys))) = _
      rw [prefix_A]
      rfl
    have htime : t=(12*k*k+41*k+32)+(t-(12*k*k+41*k+32)) := by omega
    rw [htime,run_add,hprefix]
    exact (aCodeClose_first (4*k+3) ws ys).2
      (t-(12*k*k+41*k+32))
      (by dsimp [codeCost] at ht; omega)

/-- Padded and canonical initial states are physically indistinguishable
for all t, not just for the endpoint. -/
theorem code_pad (k : Nat) (ws : List Bool) (t : Nat) :
    ObsEq (run t (implicitStart k ws))
      (run t (mixedStart k ws [])) := by
  let xs := List.replicate (3*k+1) true ++
    (false::CryptidA.wordCode ws)
  have hp := source_init_pad t 1 xs
  simp only [List.replicate_one] at hp
  have hx : init (xs ++ [false]) = mixedStart k ws [] := by
    simp [xs,mixedStart,List.append_assoc]
  rw [hx] at hp
  simpa only [implicitStart, xs] using hp

/-- The exact source endpoint for every *unpadded* mixed 10/111 code
including empty and arbitrarily long code words. -/
theorem code_endpoint (k : Nat) (ws : List Bool) :
    ObsEq (run (codeCost k ws) (implicitStart k ws))
      (mixedEnd k ws []) := by
  have hp := code_pad k ws (codeCost k ws)
  have he : run (codeCost k ws) (mixedStart k ws []) =
      mixedEnd k ws [] := by
    simpa only [codeCost] using
      (full_A_mixed_code_first_return k ws []).1
  rw [he] at hp
  exact hp

/-- Exact unpadded first return with a strong no-prior-F statement,
uniform in every finite mixed A code word (10/111 tokens). -/
theorem code_unpadded_strict_first (k : Nat) (ws : List Bool) :
    ObsEq (run (codeCost k ws) (implicitStart k ws))
      (mixedEnd k ws []) ∧
    ∀ t, 0<t → t<codeCost k ws →
      (run t (implicitStart k ws)).st ≠ 5 := by
  constructor
  · exact code_endpoint k ws
  · intro t htpos ht
    have hp := (code_pad k ws t).2.2.2
    change (run t (implicitStart k ws)).st =
      (run t (mixedStart k ws [])).st at hp
    rw [hp]
    exact mixed_explicit_noF k ws [] t htpos ht

#print axioms mixed_explicit_noF
#print axioms code_pad
#print axioms code_endpoint
#print axioms code_unpadded_strict_first

end BB6.Agent4AImplicitCode
