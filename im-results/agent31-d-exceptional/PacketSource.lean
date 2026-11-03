import Lean.Elab.Tactic.Omega
import CryptidTriplePairs

set_option maxHeartbeats 5000000
namespace BB6.Agent31PacketSource
open CryptidBoundary

def word (q p : Nat) (ys : List Bool) : List Bool :=
  oppairs q ++ false :: (List.replicate p true ++ ys)

def packet (a q p : Nat) (ys : List Bool) : Cfg :=
  ⟨[], false, List.replicate a true ++ word q p ys, 5⟩

private theorem swap (q : Nat) (ys : List Bool) :
    oppairs q ++ false :: ys = false :: (pairs q ++ ys) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs, pairs, List.append_assoc] using
      congrArg (List.cons false ∘ List.cons true) ih

private theorem ones_append (n : Nat) (ys : List Bool) :
    List.replicate n true ++ true :: ys =
      List.replicate (n+1) true ++ ys := by
  calc
    _ = (List.replicate n true ++ [true]) ++ ys := by
      simp [List.append_assoc]
    _ = List.replicate (n+1) true ++ ys := by
      simpa only [List.replicate_one] using
        congrArg (fun zs : List Bool => zs ++ ys)
          (List.replicate_append_replicate (n:=n) (m:=1) (a:=true))

/-- Exact original six-state raw B packet step for arbitrary binary tails. -/
theorem b_packet (k q p : Nat) (ys : List Bool) :
    run (12*k*k+49*k+40) (packet (3*k+2) (q+1) p ys) =
      packet (8*k+10) q p ys := by
  have hin : packet (3*k+2) (q+1) p ys =
      init (List.replicate (3*k) true ++ false :: (true :: word q p ys)) := by
    have hn : List.replicate (3*k+2) true =
        true :: true :: List.replicate (3*k) true := by
      calc
        _ = List.replicate (2+3*k) true := by congr 1; omega
        _ = List.replicate 2 true ++ List.replicate (3*k) true :=
          (List.replicate_append_replicate).symm
        _ = _ := rfl
    simp only [packet, word, init, oppairs, hn, List.cons_append]
  have hout :
      (⟨[], false, List.replicate (8*k+9) true ++ true :: word q p ys, 5⟩ : Cfg) =
        packet (8*k+10) q p ys := by
    simp [packet, ones_append]
  rw [hin]
  rw [full_B k (true :: word q p ys), hout]

/-- Exact original six-state raw E packet step for arbitrary binary tails. -/
theorem e_packet (k q p : Nat) (ys : List Bool) :
    run (12*k*k+49*k+58+6*q) (packet (3*k+4) q (p+3) ys) =
      packet (8*k+9) (q+2) p ys := by
  have hin : packet (3*k+4) q (p+3) ys =
      init (List.replicate (3*k+2) true ++ false ::
        (pairs q ++ ([true,true,true] ++ (List.replicate p true ++ ys)))) := by
    have hn : List.replicate (3*k+4) true =
        true :: true :: List.replicate (3*k+2) true := by
      calc
        _ = List.replicate (2+(3*k+2)) true := by congr 1; omega
        _ = List.replicate 2 true ++ List.replicate (3*k+2) true :=
          (List.replicate_append_replicate).symm
        _ = _ := rfl
    have hp : List.replicate (p+3) true =
        [true,true,true] ++ List.replicate p true := by
      calc
        _ = List.replicate (3+p) true := by congr 1; omega
        _ = List.replicate 3 true ++ List.replicate p true :=
          (List.replicate_append_replicate).symm
        _ = _ := rfl
    simp [packet, word, init, hn, hp, swap]
  rw [hin]
  simpa [packet, word] using
    (full_E_triple_pairs k q (List.replicate p true ++ ys))

#print axioms b_packet
#print axioms e_packet
end BB6.Agent31PacketSource
