import Lean.Elab.Tactic.Omega
import EAllDouble
import ABridgeCode
import DObsSourceCandidate

set_option maxHeartbeats 20000000
set_option maxRecDepth 8192

namespace BB6.EARegularRejoin
open CryptidBoundary BB6.BoundaryPadding

private def word6 : List Bool := [true,true,true,true]
private def aIndex (t : Nat) := 8*t+6
private def aCost (t : Nat) :=
  (12*(aIndex t)*(aIndex t)+41*(aIndex t)+32) +
    (CryptidA.wordCost (4*(aIndex t)+3) word6 +
      (2*((4*(aIndex t)+3)+CryptidA.wordInc word6)+6))

private theorem word6_code :
    CryptidA.wordCode word6 = List.replicate 12 true := by decide
private theorem word6_inc :
    CryptidA.wordInc word6 = 16 := by decide

private theorem start_E (t : Nat) :
    DRegularSource.sourceSection ⟨9*t+10,6,1⟩ =
      init (List.replicate (3*(3*t+2)+2) true ++
        (false :: (pairs 5 ++ [true,true]))) := by
  have hn : (9*t+10)-2=3*(3*t+2)+2 := by omega
  have hl : oppairs 6 ++ List.replicate 1 true =
      false::(pairs 5 ++ [true,true]) := by decide
  simp only [DRegularSource.sourceSection,hn,
    List.append_nil,List.replicate_one]
  simp only [List.replicate_one] at hl
  rw [List.append_assoc,hl]

private theorem after_E (t : Nat) :
    BB6.Agent32EAll.output (3*t+2) 5 [] =
      init (List.replicate (3*(aIndex t)+1) true ++
        (false :: (CryptidA.wordCode word6 ++
          (false :: List.replicate 6 true)))) := by
  have hn : 8*(3*t+2)+5 = 2+(3*(aIndex t)+1) := by
    dsimp [aIndex]
    omega
  have hrep : List.replicate (8*(3*t+2)+5) true =
      true::true::List.replicate (3*(aIndex t)+1) true := by
    calc
      _ = List.replicate (2+(3*(aIndex t)+1)) true := by rw [hn]
      _ = List.replicate 2 true ++
          List.replicate (3*(aIndex t)+1) true :=
          (List.replicate_append_replicate).symm
      _ = _ := rfl
  change (⟨[],false,List.replicate (8*(3*t+2)+5) true ++
    (false :: List.replicate 12 true ++
      (false :: List.replicate 6 true)),5⟩ : Cfg) = _
  rw [hrep]
  simp [init,word6_code,List.append_assoc]

private theorem after_A (t : Nat) :
    run (aCost t)
      (BB6.Agent32EAll.output (3*t+2) 5 []) =
        DRegularSource.sourceSection ⟨64*t+97,0,0⟩ := by
  rw [after_E]
  let p := aIndex t
  have hA := BB6.Agent35.full_A_code p word6 (List.replicate 6 true)
  have hcost : aCost t =
      (12*p*p+41*p+32) +
        (CryptidA.wordCost (4*p+3) word6 +
          (2*((4*p+3)+CryptidA.wordInc word6)+6)) := rfl
  rw [hcost]
  rw [hA]
  have hlen : 2*((4*p+3)+CryptidA.wordInc word6)+5+6 =
      64*t+97 := by
    rw [word6_inc]
    dsimp [p,aIndex]
    omega
  have hrep :
      List.replicate (2*((4*p+3)+CryptidA.wordInc word6)+5) true ++
        List.replicate 6 true = List.replicate (64*t+97) true := by
    rw [List.replicate_append_replicate,hlen]
  rw [hrep]
  have hf : List.replicate (64*t+97) true =
      true::true::List.replicate (64*t+95) true := by
    calc
      _ = List.replicate (2+(64*t+95)) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (64*t+95) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [hf]
  simp [DRegularSource.sourceSection,init,oppairs,
    show (64*t+97)-2=64*t+95 by omega]

/-- Original unmodified six-state D machine: for every t, an exceptional
    E(10)^5 input whose E-index is 2 mod 3 returns after two source macro
    endpoints to the canonical pure-unary regular section. This connects
    the genuine seed9 orbit's q=6, k=2 mod 3 escape sector. -/
theorem q6_EA_two_source (t : Nat) :
    ObsEq
      (run (BB6.Agent32EAll.duration (3*t+2) 5 + aCost t)
        (DRegularSource.sourceSection ⟨9*t+10,6,1⟩))
      (DRegularSource.sourceSection ⟨64*t+97,0,0⟩) := by
  have hE : ObsEq
      (run (BB6.Agent32EAll.duration (3*t+2) 5)
        (DRegularSource.sourceSection ⟨9*t+10,6,1⟩))
      (BB6.Agent32EAll.output (3*t+2) 5 []) := by
    rw [start_E]
    exact BB6.Agent32EAll.all_e_double_implicit_blank (3*t+2) 5
  have hnext := source_congr (aCost t) hE
  rw [after_A] at hnext
  simpa only [run_add] using hnext

#print axioms q6_EA_two_source
end BB6.EARegularRejoin
