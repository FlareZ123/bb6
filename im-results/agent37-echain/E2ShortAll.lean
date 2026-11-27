import Lean.Elab.Tactic.Omega
import BoundaryPadding
import E2ShortPositive
import E2ShortZero

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

namespace BB6.Agent37ShortEAll

open CryptidBoundary BB6.Agent31PacketSource
open BB6.BoundaryPadding
open BB6.Agent37ShortEPositive
open BB6.Agent37ShortEZero

/-- One unified packet input for E,p=2 with a physical 0100 marker. -/
def shortInput (k q : Nat) (ys : List Bool) : Cfg :=
  packet (3*k+4) q 2 (false :: true :: false :: false :: ys)

/-- The q=0 branch uses B and the q>0 branch uses D; these are genuinely
    distinct physical outputs, not an artifact of packet normalization. -/
def shortOutput (k q : Nat) (ys : List Bool) : Cfg :=
  match q with
  | 0 => packet (8*k+3) 0 4
      ([false,true,false,true,false,true,false,true,true] ++ ys)
  | q+1 => packet (8*k+5) 0 (2*(q+1)+2)
      (false :: List.replicate 8 true ++ ys)

/-- Exact primitive source time; the exceptional zero-pair branch takes
    36 more steps than the q=0 extrapolation of the positive-q formula. -/
def shortTime (k q : Nat) : Nat :=
  match q with
  | 0 => 12*k*k+49*k+100
  | q+1 => 12*k*k+49*k+64+4*(q+1)

/-- A single all-q, all-k, all-binary-suffix source lemma for the guarded
    E-two cylinder. -/
theorem short_all_raw (k q : Nat) (ys : List Bool) :
    run (shortTime k q) (shortInput k q ys) =
      shortOutput k q ys := by
  cases q with
  | zero =>
      exact BB6.Agent37ShortEZero.e_two_short_zero k ys
  | succ q =>
      exact BB6.Agent37ShortEPositive.e_two_short_positive k q ys

/-- Finite-list 01 and 0100 define the same physical infinite blank
    suffix; this is the only observational-equivalence step. -/
private theorem inputPad (k q n : Nat) :
    ObsEq (run n (packet (3*k+4) q 2 [false,true]))
      (run n (shortInput k q [])) := by
  simpa [shortInput,packet,word,List.append_assoc,List.replicate] using
    (source_pad n 0 2 (packet (3*k+4) q 2 [false,true]))

/-- Fully unpadded source theorem, quantifying all k,q with no gap at q=0.
    Observational equality is essential: the finite input carries no
    syntactic trailing zeros but represents the same infinite tape. -/
theorem short_all_implicit_blank (k q : Nat) :
    ObsEq (run (shortTime k q)
      (packet (3*k+4) q 2 [false,true]))
      (shortOutput k q []) := by
  have h := inputPad k q (shortTime k q)
  rw [short_all_raw] at h
  exact h

#print axioms short_all_raw
#print axioms short_all_implicit_blank

end BB6.Agent37ShortEAll
