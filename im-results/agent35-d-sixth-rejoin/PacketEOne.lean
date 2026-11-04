import Lean.Elab.Tactic.Omega
import PacketEZero

namespace BB6.Agent35PacketEOne
open CryptidBoundary BB6.Agent31PacketSource
set_option maxHeartbeats 15000000

private def ys : List Bool := false :: List.replicate 6 true

private theorem swap (q : Nat) (zs : List Bool) :
    oppairs q ++ false :: zs = false :: (pairs q ++ zs) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (List.cons false ∘ List.cons true) ih

private theorem add_pair (q : Nat) (zs : List Bool) :
    oppairs q ++ false :: true :: zs = oppairs (q+1) ++ zs := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change false :: true :: (oppairs q ++ false :: true :: zs) =
      false :: true :: (oppairs (q+1) ++ zs)
    rw [ih]

private theorem input (k q : Nat) :
    packet (3*k+4) q 1 ys =
      init (List.replicate (3*k+2) true ++
        false :: (pairs (q+1) ++
          ([true,true,true] ++ List.replicate 3 true))) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    have h : 3*k+4=2+(3*k+2) := by omega
    calc
      _ = List.replicate (2+(3*k+2)) true :=
        congrArg (fun n : Nat => List.replicate n true) h
      _ = List.replicate 2 true ++ List.replicate (3*k+2) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  have hs : word q 1 ys =
      false :: (pairs (q+1) ++
        ([true,true,true] ++ List.replicate 3 true)) := by
    calc
      word q 1 ys = oppairs q ++
          false :: true :: (false :: List.replicate 6 true) := rfl
      _ = oppairs (q+1) ++ (false :: List.replicate 6 true) :=
        add_pair q (false :: List.replicate 6 true)
      _ = false :: (pairs (q+1) ++ List.replicate 6 true) :=
        swap (q+1) (List.replicate 6 true)
      _ = _ := by rfl
  unfold packet
  rw [hn,hs]
  simp [init,List.append_assoc]

private theorem append_pair (q : Nat) :
    oppairs q ++ (false :: List.replicate 3 true) =
      oppairs (q+1) ++ List.replicate 2 true := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change false :: true :: (oppairs q ++ (false :: List.replicate 3 true)) =
      false :: true :: (oppairs (q+1) ++ List.replicate 2 true)
    rw [ih]

private theorem output (k q : Nat) :
    (⟨[],false,List.replicate (8*k+9) true ++
      (oppairs (q+3) ++
        (false :: List.replicate 3 true)),5⟩ : Cfg) =
      DRegularSource.sourceSection ⟨8*k+9,q+4,2⟩ := by
  have hn : List.replicate (8*k+9) true =
      true :: true :: List.replicate (8*k+7) true := by
    have h : 8*k+9=2+(8*k+7) := by omega
    calc
      _ = List.replicate (2+(8*k+7)) true :=
        congrArg (fun n : Nat => List.replicate n true) h
      _ = List.replicate 2 true ++ List.replicate (8*k+7) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [hn,append_pair]
  simp [DRegularSource.sourceSection,init,
    show (8*k+9)-2=8*k+7 by omega,List.append_assoc]

/-- All E-terminal p=1 packet branches source-return directly to L. -/
theorem source_e_packet_one (k q : Nat) :
    run (12*k*k+49*k+58+6*(q+1))
      (packet (3*k+4) q 1 ys) =
      DRegularSource.sourceSection ⟨8*k+9,q+4,2⟩ := by
  rw [input]
  exact Eq.trans (full_E_triple_pairs k (q+1) (List.replicate 3 true))
    (output k q)

#print axioms source_e_packet_one
end BB6.Agent35PacketEOne
