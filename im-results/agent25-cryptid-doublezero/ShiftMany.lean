import Lean.Elab.Tactic.Omega
import ShiftCylinders

set_option maxHeartbeats 5000000

namespace BB6.Agent25Shift

open CryptidBoundary

/-- The exact cumulative primitive-time skew for j successive 3-cell
    parameter lifts, counting a fixed number of triple-one code packets. -/
def skew (k triplePackets : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => skew k triplePackets j +
      (24*(k+j)+61+24*triplePackets)

/-- Elementary but fully universal cocycle lemma for any transition family. -/
theorem costShift (f : Nat → Nat) (k extra j : Nat)
    (h : ∀ u, f (u+1) = f u + (24*u+61+24*extra)) :
    f (k+j) = f k + skew k extra j := by
  induction j with
  | zero => simp [skew]
  | succ j ih =>
      rw [show k+(j+1)=(k+j)+1 by omega, h (k+j), ih]
      simp only [skew]
      omega

/-- Add an arbitrary unary right prefix to the original raw head-relative
    configuration, retaining both sides and the original control state. -/
def prependN (d : Nat) (c : Cfg) : Cfg :=
  ⟨c.l,c.h,List.replicate d true ++ c.r,c.st⟩

theorem prependN_finish (d n : Nat) (ys : List Bool) :
    prependN d (⟨[],false,List.replicate n true ++ ys,5⟩ : Cfg) =
      (⟨[],false,List.replicate (n+d) true ++ ys,5⟩ : Cfg) := by
  unfold prependN
  rw [←List.append_assoc, List.replicate_append_replicate]
  rw [Nat.add_comm d n]

/-- Generic original-machine soundness of any affine unary lift family,
    provided its exact source transitions, time cocycle and output shift
    have been established. Unlike a conjectured first-return map, this
    states equality of actual raw machine configurations. -/
theorem sourceShiftMany
    (f : Nat → Nat) (src dst : Nat → Cfg) (k j extra : Nat)
    (hexact : ∀ u, run (f u) (src u) = dst u)
    (hcost : ∀ u, f (u+1) = f u + (24*u+61+24*extra))
    (houtput : ∀ u r, dst (u+r) = prependN (8*r) (dst u)) :
    run (f k + skew k extra j) (src (k+j)) =
      prependN (8*j) (run (f k) (src k)) := by
  rw [←costShift f k extra j hcost, hexact, hexact, houtput]

/-- An arbitrary lift by 3j unary cells transforms B-cylinder output by
    exactly 8j cells, with a kernel-checked primitive-time skew. -/
theorem B_shift_many (k j : Nat) (ys : List Bool) :
    run (costB k + skew k 0 j)
      (init (List.replicate (3*(k+j)) true ++ false::ys)) =
    prependN (8*j) (run (costB k)
      (init (List.replicate (3*k) true ++ false::ys))) := by
  have ht : costB (k+j) = costB k + skew k 0 j :=
    costShift costB k 0 j (by
      intro u
      simpa using costB_succ u)
  rw [←ht]
  simp only [costB]
  rw [full_B (k+j) ys, full_B k ys, prependN_finish]
  have hr : 8*(k+j)+9 = (8*k+9)+8*j := by omega
  rw [hr]

/-- Universal E-zero-after-pairs branch, simultaneously lifted by 3j. -/
theorem Epair_shift_many (k j q : Nat) (ys : List Bool) :
    run (costEpair k q + skew k 0 j)
      (init (List.replicate (3*(k+j)+2) true ++
        false :: (pairs q ++ (false::ys)))) =
    prependN (8*j) (run (costEpair k q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (false::ys))))) := by
  have ht : costEpair (k+j) q = costEpair k q + skew k 0 j :=
    costShift (fun u => costEpair u q) k 0 j (by
      intro u
      simpa using costEpair_succ u q)
  rw [←ht]
  simp only [costEpair]
  rw [full_E_pairs (k+j) q ys, full_E_pairs k q ys, prependN_finish]
  have hr : 8*(k+j)+5 = (8*k+5)+8*j := by omega
  rw [hr]

/-- Universal E-three-one-after-pairs branch, lifted by 3j. -/
theorem Etriple_shift_many (k j q : Nat) (ys : List Bool) :
    run (costEtriple k q + skew k 0 j)
      (init (List.replicate (3*(k+j)+2) true ++
        false :: (pairs q ++ ([true,true,true] ++ ys)))) =
    prependN (8*j) (run (costEtriple k q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ ([true,true,true] ++ ys))))) := by
  have ht : costEtriple (k+j) q = costEtriple k q + skew k 0 j :=
    costShift (fun u => costEtriple u q) k 0 j (by
      intro u
      simpa using costEtriple_succ u q)
  rw [←ht]
  simp only [costEtriple]
  rw [full_E_triple_pairs (k+j) q ys,
    full_E_triple_pairs k q ys, prependN_finish]
  have hr : 8*(k+j)+9 = (8*k+9)+8*j := by omega
  rw [hr]

/-- Universal original-source 3j -> 8j covariance on every finite binary
    10/111 token word. The exact time skew depends only on its triple count. -/
theorem Acode_shift_many (k j : Nat) (ws ys : List Bool) :
    run (costA k ws + skew k (BB6.Parikh.triplesN ws) j)
      (init (List.replicate (3*(k+j)+1) true ++
        false :: (CryptidA.wordCode ws ++ (false::ys)))) =
    prependN (8*j) (run (costA k ws)
      (init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++ (false::ys))))) := by
  have ht : costA (k+j) ws =
      costA k ws + skew k (BB6.Parikh.triplesN ws) j :=
    costShift (fun u => costA u ws) k (BB6.Parikh.triplesN ws) j
      (fun u => costA_succ u ws)
  rw [←ht]
  simp only [costA]
  rw [BB6.Agent35.full_A_code (k+j) ws ys,
      BB6.Agent35.full_A_code k ws ys, prependN_finish]
  have hr : 2*(4*(k+j)+3+CryptidA.wordInc ws)+5 =
      (2*(4*k+3+CryptidA.wordInc ws)+5)+8*j := by omega
  rw [hr]

#print axioms costShift
#print axioms sourceShiftMany
#print axioms B_shift_many
#print axioms Epair_shift_many
#print axioms Etriple_shift_many
#print axioms Acode_shift_many

end BB6.Agent25Shift
