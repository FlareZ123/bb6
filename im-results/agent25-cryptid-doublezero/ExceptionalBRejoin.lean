import Lean.Elab.Tactic.Omega
import EAllDouble
import DObsSourceCandidate

set_option maxHeartbeats 3000000
namespace BB6.Agent25Rejoin
open CryptidBoundary

private def K (t : Nat) : Nat := 8*t+1
private def bCost (t : Nat) : Nat := 12*(K t)*(K t)+49*(K t)+40

private theorem special_input (t : Nat) :
    BB6.Agent32EAll.output (3*t) 5 [] =
      init (List.replicate (3*(K t)) true ++
        (false :: (List.replicate 12 true ++ (false :: List.replicate 6 true)))) := by
  have h : 8*(3*t)+5 = 2+3*(K t) := by unfold K; omega
  have hrep : List.replicate (8*(3*t)+5) true =
      true::true::List.replicate (3*(K t)) true := by
    calc
      _ = List.replicate (2+3*(K t)) true := by rw [h]
      _ = List.replicate 2 true ++ List.replicate (3*(K t)) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  simp [BB6.Agent32EAll.output, init, hrep]

private theorem special_target (t : Nat) :
    (⟨[], false, List.replicate (8*(K t)+9) true ++
      (List.replicate 12 true ++ (false :: List.replicate 6 true)),5⟩ : Cfg) =
      DRegularSource.sourceSection ⟨64*t+29,1,5⟩ := by
  have hn : 8*(K t)+9+12 = 64*t+29 := by unfold K; omega
  have hrep : List.replicate (8*(K t)+9) true ++ List.replicate 12 true =
      List.replicate (64*t+29) true := by
    rw [List.replicate_append_replicate, hn]
  have hfront : List.replicate (64*t+29) true =
      true :: true :: List.replicate (64*t+27) true := by
    calc
      _ = List.replicate (2+(64*t+27)) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (64*t+27) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  simp only [DRegularSource.sourceSection, init, oppairs,
    show 64*t+29-2=64*t+27 by omega]
  rw [← List.append_assoc, hrep, hfront]
  simp [List.append_assoc]

/-- Original six-state raw B return immediately following an E exceptional
    output in the k=0 (mod 3), q=6 sector, uniformly for all t.
    This is a specified endpoint; earliest-return minimality is not asserted. -/
theorem exceptional_B_rejoins_regular (t : Nat) :
    run (bCost t) (BB6.Agent32EAll.output (3*t) 5 []) =
      DRegularSource.sourceSection ⟨64*t+29,1,5⟩ := by
  rw [special_input]
  simpa only [bCost,K] using
    (Eq.trans (full_B (K t) (List.replicate 12 true ++
      (false :: List.replicate 6 true))) (special_target t))

#print axioms exceptional_B_rejoins_regular
end BB6.Agent25Rejoin
