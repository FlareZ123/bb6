import Lean.Elab.Tactic.Omega
import PrefixShift

set_option maxHeartbeats 5000000

namespace BB6.Agent25Shift
open CryptidBoundary

/-- Arbitrary-length left alternating-pair insertion beyond z marker zeros. -/
def liftStackN (z j : Nat) (c : Cfg) : Cfg :=
  ⟨List.replicate z false ++ pairs (4*j) ++ c.l.drop z,
    c.h,c.r,c.st⟩

theorem pairs_append (u v : Nat) :
    pairs (u+v) = pairs u ++ pairs v := by
  induction u with
  | zero => simp [pairs]
  | succ u ih =>
    have h : u+1+v=(u+v)+1 := by omega
    rw [h]
    simp [pairs,ih]

theorem lift_boundaryN (z m st j : Nat) (ys : List Bool) :
    liftStackN z j (boundary z m st ys) =
      boundary z (m+4*j) st ys := by
  unfold liftStackN boundary
  have hd :
      (List.replicate z false ++ (pairs m ++ [true,true])).drop z =
        pairs m ++ [true,true] := by simp
  rw [hd, show m+4*j=4*j+m by omega,pairs_append]
  simp only [List.append_assoc]

/-- Exact source primitive-time cost for lifting any initial unary length
    by 3j, independent of the first-delimiter phase and arbitrary suffix. -/
theorem prefixTime_multi (k phase j : Nat) :
    prefixTime (k+j) phase =
      prefixTime k phase + (12*j*j+(24*k+41)*j) := by
  unfold prefixTime
  have hx : 12*j*k = 12*k*j := by ac_rfl
  have hy : 24*k*j = 12*k*j + 12*k*j := by
    calc
      24*k*j = (12*k+12*k)*j := by congr 1 <;> omega
      _ = (12*k)*j+(12*k)*j := Nat.add_mul _ _ _
  simp only [Nat.mul_add,Nat.add_mul]
  omega

/-- Source-level all-j lift through the complete first-delimiter scan,
    without any condition on later B/A/E exceptional suffixes or halting. -/
theorem source_prefix_shift_many
    (z phase st : Nat) (start : Nat → Cfg) (k j : Nat)
    (ys : List Bool)
    (h : ∀ u, run (prefixTime u phase) (start u) =
      boundary z (4*u+3) st ys) :
    run (prefixTime k phase + (12*j*j+(24*k+41)*j))
      (start (k+j)) =
      liftStackN z j (run (prefixTime k phase) (start k)) := by
  rw [←prefixTime_multi, h (k+j), h k]
  have hm : 4*(k+j)+3 = (4*k+3)+4*j := by omega
  rw [hm]
  exact (lift_boundaryN z (4*k+3) st j ys).symm

theorem prefixB_shift_many (k j : Nat) (ys : List Bool) :
    run (prefixTime k 0 + (12*j*j+(24*k+41)*j))
      (init (List.replicate (3*(k+j)) true ++ false::ys)) =
      liftStackN 0 j (run (prefixTime k 0)
        (init (List.replicate (3*k) true ++ false::ys))) := by
  apply source_prefix_shift_many 0 0 1
    (fun u => init (List.replicate (3*u) true ++ false::ys)) k j ys
  intro u
  simpa only [prefixTime, Nat.add_zero, boundary,
    List.replicate_zero, List.nil_append] using prefix_B u ys

theorem prefixA_shift_many (k j : Nat) (ys : List Bool) :
    run (prefixTime k 1 + (12*j*j+(24*k+41)*j))
      (init (List.replicate (3*(k+j)+1) true ++ false::ys)) =
      liftStackN 1 j (run (prefixTime k 1)
        (init (List.replicate (3*k+1) true ++ false::ys))) := by
  apply source_prefix_shift_many 1 1 0
    (fun u => init (List.replicate (3*u+1) true ++ false::ys)) k j ys
  intro u
  simpa [prefixTime, boundary] using prefix_A u ys

theorem prefixE_shift_many (k j : Nat) (ys : List Bool) :
    run (prefixTime k 2 + (12*j*j+(24*k+41)*j))
      (init (List.replicate (3*(k+j)+2) true ++ false::ys)) =
      liftStackN 2 j (run (prefixTime k 2)
        (init (List.replicate (3*k+2) true ++ false::ys))) := by
  apply source_prefix_shift_many 2 2 4
    (fun u => init (List.replicate (3*u+2) true ++ false::ys)) k j ys
  intro u
  simpa [prefixTime, boundary] using prefix_E u ys

#print axioms prefixTime_multi
#print axioms source_prefix_shift_many
#print axioms prefixB_shift_many
#print axioms prefixA_shift_many
#print axioms prefixE_shift_many

end BB6.Agent25Shift
