import Lean.Elab.Tactic.Omega
import CryptidPairs
import PacketSource
import DObsSourceCandidate

namespace BB6.Agent35PacketEZero
open CryptidBoundary BB6.Agent31PacketSource
set_option maxHeartbeats 15000000
def ys : List Bool := false :: List.replicate 6 true

private theorem swap (q : Nat) (zs : List Bool) :
    oppairs q ++ false :: zs = false :: (pairs q ++ zs) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (List.cons false ∘ List.cons true) ih

private theorem input (k q : Nat) :
    packet (3*k+4) q 0 ys =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (false :: List.replicate 6 true))) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    have h : 3*k+4=2+(3*k+2) := by omega
    calc
      _ = List.replicate (2+(3*k+2)) true :=
        congrArg (fun n : Nat => List.replicate n true) h
      _ = List.replicate 2 true ++ List.replicate (3*k+2) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  have hs : word q 0 ys =
      false :: (pairs q ++ (false :: List.replicate 6 true)) := by
    simpa [word,ys] using swap q ys
  unfold packet
  rw [hn,hs]
  simp [init,List.append_assoc]

private theorem output (k q : Nat) :
    (⟨[],false,List.replicate (8*k+5) true ++
      (false :: List.replicate (2*q+6) true ++
        List.replicate 6 true),5⟩ : Cfg) =
      DRegularSource.sourceSection ⟨8*k+5,1,2*q+11⟩ := by
  have hn : List.replicate (8*k+5) true =
      true :: true :: List.replicate (8*k+3) true := by
    have h : 8*k+5=2+(8*k+3) := by omega
    calc
      _ = List.replicate (2+(8*k+3)) true :=
        congrArg (fun n : Nat => List.replicate n true) h
      _ = List.replicate 2 true ++ List.replicate (8*k+3) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  have hones : List.replicate (2*q+6) true ++ List.replicate 6 true =
      true :: List.replicate (2*q+11) true := by
    calc
      _ = List.replicate (2*q+12) true := by
        rw [List.replicate_append_replicate]
        congr 1
        omega
      _ = List.replicate (1+(2*q+11)) true := by congr 1; omega
      _ = List.replicate 1 true ++ List.replicate (2*q+11) true :=
          (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [hn,hones]
  simp [DRegularSource.sourceSection,init,oppairs,
    show (8*k+5)-2=8*k+3 by omega,List.append_assoc]

/-- All E-terminal p=0 packet branches source-return directly to L. -/
theorem source_e_packet_zero (k q : Nat) :
    run (12*k*k+49*k+50+4*q)
      (packet (3*k+4) q 0 ys) =
      DRegularSource.sourceSection ⟨8*k+5,1,2*q+11⟩ := by
  rw [input]
  exact Eq.trans (full_E_pairs k q (List.replicate 6 true))
    (output k q)

#print axioms source_e_packet_zero
end BB6.Agent35PacketEZero
