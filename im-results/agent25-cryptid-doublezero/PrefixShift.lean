import Lean.Elab.Tactic.Omega
import ShiftMany

set_option maxHeartbeats 5000000

namespace BB6.Agent25Shift
open CryptidBoundary

/-- Uniform first-delimiter phase cost, for state B/A/E suffix residues. -/
def prefixTime (k phase : Nat) : Nat := 12*k*k+41*k+31+phase

theorem prefixTime_succ (k phase : Nat) :
    prefixTime (k+1) phase = prefixTime k phase + (24*k+53) := by
  unfold prefixTime
  simp only [Nat.mul_add, Nat.add_mul]
  omega

/-- The three original-machine delimiter boundaries differ only in the
    number (0, 1 or 2) of leading zero markers on the left stack. -/
def boundary (z m st : Nat) (ys : List Bool) : Cfg :=
  ⟨List.replicate z false ++ (pairs m ++ [true,true]),false,ys,st⟩

/-- Insert four alternating pairs just after z leading zero markers,
    preserving the scanned bit, entire right tape and control state. -/
def liftStack (z : Nat) (c : Cfg) : Cfg :=
  ⟨List.replicate z false ++ pairs 4 ++ c.l.drop z,c.h,c.r,c.st⟩

/-- Exactly four new left-stack pairs are the common effect of increasing
    the initial F-section unary length by three. -/
theorem pairs_prefix4 (m : Nat) :
    pairs (m+4) = pairs 4 ++ pairs m := by
  rfl

theorem lift_boundary (z m st : Nat) (ys : List Bool) :
    liftStack z (boundary z m st ys) = boundary z (m+4) st ys := by
  unfold liftStack boundary
  have hd :
      (List.replicate z false ++ (pairs m ++ [true,true])).drop z =
        pairs m ++ [true,true] := by simp
  rw [hd]
  rw [pairs_prefix4 m]
  simp only [List.append_assoc]

/-- Generic exact raw source prefix conjugacy: a +3 initial unary lift
    entails an additional 24k+53 primitive steps and four more left pairs.
    This applies even to suffixes whose eventual return or halt is unknown. -/
theorem source_prefix_shift
    (z phase st : Nat) (start : Nat → Cfg) (k : Nat) (ys : List Bool)
    (h : ∀ u, run (prefixTime u phase) (start u) =
      boundary z (4*u+3) st ys) :
    run (prefixTime k phase + (24*k+53)) (start (k+1)) =
      liftStack z (run (prefixTime k phase) (start k)) := by
  rw [←prefixTime_succ, h (k+1), h k]
  have hm : 4*(k+1)+3 = (4*k+3)+4 := by omega
  rw [hm]
  exact (lift_boundary z (4*k+3) st ys).symm

/-- All finite suffixes, B residue (unary length 3k+2). -/
theorem prefixB_shift (k : Nat) (ys : List Bool) :
    run (prefixTime k 0 + (24*k+53))
      (init (List.replicate (3*(k+1)) true ++ false::ys)) =
    liftStack 0 (run (prefixTime k 0)
      (init (List.replicate (3*k) true ++ false::ys))) := by
  apply source_prefix_shift 0 0 1
    (fun u => init (List.replicate (3*u) true ++ false::ys)) k ys
  intro u
  simpa only [prefixTime, Nat.add_zero, boundary,
    List.replicate_zero, List.nil_append] using prefix_B u ys

/-- All finite suffixes, A residue (unary length 3k+3). -/
theorem prefixA_shift (k : Nat) (ys : List Bool) :
    run (prefixTime k 1 + (24*k+53))
      (init (List.replicate (3*(k+1)+1) true ++ false::ys)) =
    liftStack 1 (run (prefixTime k 1)
      (init (List.replicate (3*k+1) true ++ false::ys))) := by
  apply source_prefix_shift 1 1 0
    (fun u => init (List.replicate (3*u+1) true ++ false::ys)) k ys
  intro u
  simpa [prefixTime, boundary] using prefix_A u ys

/-- All finite suffixes, E residue (unary length 3k+4). -/
theorem prefixE_shift (k : Nat) (ys : List Bool) :
    run (prefixTime k 2 + (24*k+53))
      (init (List.replicate (3*(k+1)+2) true ++ false::ys)) =
    liftStack 2 (run (prefixTime k 2)
      (init (List.replicate (3*k+2) true ++ false::ys))) := by
  apply source_prefix_shift 2 2 4
    (fun u => init (List.replicate (3*u+2) true ++ false::ys)) k ys
  intro u
  simpa [prefixTime, boundary] using prefix_E u ys

#print axioms source_prefix_shift
#print axioms prefixB_shift
#print axioms prefixA_shift
#print axioms prefixE_shift

end BB6.Agent25Shift
