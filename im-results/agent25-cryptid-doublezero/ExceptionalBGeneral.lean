import Lean.Elab.Tactic.Omega
import ExceptionalBRejoin

set_option maxHeartbeats 5000000
namespace BB6.Agent25BGeneral
open CryptidBoundary BB6.BoundaryPadding

def K (t : Nat) : Nat := 8*t+1
def bCost (t : Nat) : Nat := 12*(K t)*(K t)+49*(K t)+40

theorem oppairs_last (n : Nat) :
    oppairs (n+1) ++ [true] = false :: (pairs n ++ [true,true]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false :: true :: (oppairs (n+1) ++ [true]) =
      false :: true :: false :: (pairs n ++ [true,true])
    rw [ih]

theorem output_input (t p : Nat) :
    BB6.Agent32EAll.output (3*t) (p+1) [] =
      init (List.replicate (3*(K t)) true ++
        false :: (List.replicate (2*p+4) true ++
          (false :: List.replicate 6 true))) := by
  have h : 8*(3*t)+5 = 2+3*(K t) := by unfold K; omega
  have hr : List.replicate (8*(3*t)+5) true =
      true :: true :: List.replicate (3*(K t)) true := by
    rw [h]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(K t)) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  simp only [BB6.Agent32EAll.output, List.append_nil]
  rw [hr]
  have hn : 2*(p+1)+2 = 2*p+4 := by omega
  rw [hn]
  simp [init, List.append_assoc]

theorem output_target (t p : Nat) :
    (⟨[],false,List.replicate (8*(K t)+9) true ++
      (List.replicate (2*p+4) true ++
        (false :: List.replicate 6 true)),5⟩ : Cfg) =
      DRegularSource.sourceSection ⟨64*t+21+2*p,1,5⟩ := by
  have hn : 8*(K t)+9+(2*p+4)=64*t+21+2*p := by unfold K; omega
  have hrep : List.replicate (8*(K t)+9) true ++
      List.replicate (2*p+4) true =
      List.replicate (64*t+21+2*p) true := by
    rw [List.replicate_append_replicate,hn]
  have hfront : List.replicate (64*t+21+2*p) true =
      true::true::List.replicate (64*t+19+2*p) true := by
    calc
      _ = List.replicate (2+(64*t+19+2*p)) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (64*t+19+2*p) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  simp only [DRegularSource.sourceSection,init,oppairs,List.replicate_one,
    show (64*t+21+2*p)-2=64*t+19+2*p by omega]
  rw [←List.append_assoc,hrep,hfront]
  simp [List.append_assoc]

theorem rejoin (t p : Nat) :
    run (bCost t) (BB6.Agent32EAll.output (3*t) (p+1) []) =
      DRegularSource.sourceSection ⟨64*t+21+2*p,1,5⟩ := by
  rw [output_input]
  exact Eq.trans (full_B (K t) (List.replicate (2*p+4) true ++
    (false :: List.replicate 6 true))) (output_target t p)

theorem e_input (t p : Nat) :
    DRegularSource.sourceSection ⟨9*t+4,p+2,1⟩ =
      init (List.replicate (3*(3*t)+2) true ++
        false :: (pairs (p+1) ++ [true,true])) := by
  have hn : (9*t+4)-2=3*(3*t)+2 := by omega
  have hp : p+2=(p+1)+1 := by omega
  simp only [DRegularSource.sourceSection,init,hn,hp,List.replicate_one]
  rw [List.append_assoc,oppairs_last]

/-- Genuine original-source two-return reentry for every k≡0 (mod3)
    E-exception with q=p+2>=2 alternating pairs and b=1. -/
theorem exceptional_EB_general (t p : Nat) :
    ObsEq
      (run (BB6.Agent32EAll.duration (3*t) (p+1) + bCost t)
        (DRegularSource.sourceSection ⟨9*t+4,p+2,1⟩))
      (DRegularSource.sourceSection ⟨64*t+21+2*p,1,5⟩) := by
  have hi : ObsEq
      (run (BB6.Agent32EAll.duration (3*t) (p+1))
        (DRegularSource.sourceSection ⟨9*t+4,p+2,1⟩))
      (BB6.Agent32EAll.output (3*t) (p+1) []) := by
    rw [e_input]
    exact BB6.Agent32EAll.all_e_double_implicit_blank (3*t) (p+1)
  have hB := source_congr (bCost t) hi
  rw [rejoin] at hB
  simpa only [run_add] using hB

#print axioms exceptional_EB_general
end BB6.Agent25BGeneral
