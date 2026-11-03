import Lean.Elab.Tactic.Omega
import DObsSourceCandidate
import BoundaryExtra

set_option maxHeartbeats 2000000
namespace BB6.Agent31RegularB
open CryptidBoundary DRegularSource

private theorem append_one (n : Nat) (xs : List Bool) :
    List.replicate (n+1) true ++ true :: xs =
      true :: true :: (List.replicate n true ++ xs) := by
  have h : List.replicate (n+1) true ++ true :: xs =
       List.replicate (n+2) true ++ xs := by
    rw [List.append_cons, ← List.replicate_succ']
  rw [h]
  rw [show n+2 = (n+1)+1 by omega, List.replicate_succ, List.replicate_succ]
  simp only [List.cons_append]

/-- B with at least two alternating pairs, arbitrary terminal unary suffix. -/
theorem b_many (k q b : Nat) :
  run (12*k*k+49*k+40) (sourceSection ⟨3*k+2,q+2,b⟩) =
      sourceSection ⟨8*k+10,q+1,b⟩ := by
  have h := full_B k (true :: (oppairs (q+1) ++ List.replicate b true))
  have hout : (⟨[],false,
     List.replicate (8*k+9) true ++ true ::
      (oppairs (q+1) ++ List.replicate b true),5⟩ : Cfg) =
      sourceSection ⟨8*k+10,q+1,b⟩ := by
    simp [sourceSection,init, append_one, List.append_assoc]
  rw [← hout]
  simpa [sourceSection, init, oppairs, List.append_assoc] using h

/-- B with one pair merges every remaining trailing one into the unary prefix. -/
theorem b_one (k b : Nat) :
  run (12*k*k+49*k+40) (sourceSection ⟨3*k+2,1,b⟩) =
      sourceSection ⟨8*k+10+b,0,0⟩ := by
  have h := full_B k (true::List.replicate b true)
  have hh : List.replicate (8*k+9) true ++ true :: List.replicate b true =
      List.replicate (8*k+10+b) true := by
    calc
      _ = (List.replicate (8*k+9) true ++ [true]) ++
          List.replicate b true := by simp [List.append_assoc]
      _ = List.replicate (8*k+10) true ++ List.replicate b true := by
        rw [← List.replicate_succ', show 8*k+9+1=8*k+10 by omega]
      _ = _ := by rw [List.replicate_append_replicate]
  have hh2 : List.replicate (8*k+10+b) true =
      true :: true :: List.replicate (8*k+8+b) true := by
    rw [show 8*k+10+b = ((8*k+8+b)+1)+1 by omega,
      List.replicate_succ, List.replicate_succ]
  have hout : (⟨[],false,
     List.replicate (8*k+9) true ++ true :: List.replicate b true,5⟩ : Cfg) =
      sourceSection ⟨8*k+10+b,0,0⟩ := by
    simp only [sourceSection,init,oppairs,List.replicate_zero,
      List.append_nil]
    rw [hh,hh2]
    rw [show 8*k+10+b-2=8*k+8+b by omega]
  rw [← hout]
  simpa [sourceSection, init, oppairs, List.append_assoc] using h

/-- B with an entirely unary input. -/
theorem b_zero (k : Nat) :
  run (12*k*k+49*k+40) (sourceSection ⟨3*k+2,0,0⟩) =
      sourceSection ⟨8*k+9,0,0⟩ := by
  have h := full_B_nil k
  have hout : (⟨[],false,List.replicate (8*k+9) true,5⟩ : Cfg) =
    sourceSection ⟨8*k+9,0,0⟩ := by
    simp only [sourceSection,init,oppairs,List.replicate_zero,List.append_nil]
    rw [show 8*k+9 = ((8*k+7)+1)+1 by omega,
      List.replicate_succ, List.replicate_succ]
    rw [show 8*k+7+1+1-2=8*k+7 by omega]
  rw [← hout]
  simpa [sourceSection, init, oppairs] using h

/-- All canonical B-branch modeled transitions are exact source machine moves. -/
theorem b_contract_exact (s t : DRegular.L)
    (hc : DRegular.Canon s) (hb : s.a % 3 = 2)
    (hn : DRegular.next s = some t) :
    run (DRegular.duration s) (sourceSection s) = sourceSection t := by
  rcases s with ⟨a,q,b⟩
  change a%3=2 at hb
  change a >= 2 ∧ (q ≠ 0 ∨ b=0) at hc
  have ha : a = 3*(a/3)+2 := by omega
  cases q with
  | zero =>
    have hb0 : b = 0 := by
      rcases hc.2 with hx | hx
      · contradiction
      · exact hx
    simp [DRegular.next, hb] at hn
    cases hn
    subst b
    have hsrc := congrArg (fun n : Nat => sourceSection (DRegular.L.mk n 0 0)) ha
    have hdur : DRegular.duration ⟨a,0,0⟩ =
        12*(a/3)*(a/3)+49*(a/3)+40 := by simp [DRegular.duration, hb]
    rw [hdur, hsrc]
    exact b_zero (a/3)
  | succ q =>
    cases q with
    | zero =>
      simp [DRegular.next, hb] at hn
      cases hn
      have hsrc := congrArg (fun n : Nat => sourceSection (DRegular.L.mk n 1 b)) ha
      have hdur : DRegular.duration ⟨a,1,b⟩ =
          12*(a/3)*(a/3)+49*(a/3)+40 := by simp [DRegular.duration, hb]
      rw [hdur, hsrc]
      exact b_one (a/3) b
    | succ q =>
      simp [DRegular.next, hb] at hn
      cases hn
      have hsrc := congrArg (fun n : Nat => sourceSection (DRegular.L.mk n (q+2) b)) ha
      have hdur : DRegular.duration ⟨a,q+2,b⟩ =
          12*(a/3)*(a/3)+49*(a/3)+40 := by simp [DRegular.duration, hb]
      rw [show q+1+1=q+2 by omega, hdur, hsrc]
      exact b_many (a/3) q b

theorem b_contract_obs (s t : DRegular.L)
    (hc : DRegular.Canon s) (hb : s.a % 3 = 2)
    (hn : DRegular.next s = some t) :
    BB6.BoundaryPadding.ObsEq
      (run (DRegular.duration s) (sourceSection s)) (sourceSection t) := by
  rw [b_contract_exact s t hc hb hn]
  exact BB6.Padding.cfgEq_refl _

#print axioms b_contract_exact
#print axioms b_contract_obs
#print axioms b_many
#print axioms b_one
#print axioms b_zero
end BB6.Agent31RegularB
