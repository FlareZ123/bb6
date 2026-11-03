import Lean.Elab.Tactic.Omega
import DObsSourceCandidate
import CryptidTriplePairs

set_option maxHeartbeats 3000000
namespace BB6.Agent31RegularE
open CryptidBoundary DRegularSource

private theorem pairs_one (q : Nat) :
    pairs q ++ [true] = true :: oppairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp [pairs,oppairs,List.append_assoc,ih]

private theorem oppairs_succ_right (q : Nat) :
    oppairs (q+1) = oppairs q ++ [false,true] := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change false :: true :: oppairs (q+1) =
      (false :: true :: oppairs q) ++ [false,true]
    rw [ih]
    rfl

private theorem shift_word (q : Nat) (ys : List Bool) :
    true :: (oppairs q ++ (true::true::ys)) =
      pairs q ++ ([true,true,true] ++ ys) := by
  calc
    _ = (true::oppairs q) ++ (true::true::ys) := rfl
    _ = (pairs q ++ [true]) ++ (true::true::ys) := by rw [pairs_one]
    _ = _ := by simp [List.append_assoc]

private theorem output_word (q p : Nat) :
  oppairs (q+2) ++ false :: List.replicate (p+1) true =
  oppairs (q+3) ++ List.replicate p true := by
  rw [show q+3=(q+2)+1 by omega]
  rw [oppairs_succ_right (q+2)]
  rw [List.replicate_succ]
  simp only [List.cons_append, List.append_assoc, List.nil_append]

/-- E with at least one alternating pair and at least three trailing ones. -/
theorem e_many (k q p : Nat) :
    run (12*k*k+49*k+58+6*q) (sourceSection ⟨3*k+4,q+1,p+3⟩) =
      sourceSection ⟨8*k+9,q+3,p⟩ := by
  have h := full_E_triple_pairs k q (List.replicate (p+1) true)
  have hp : List.replicate (p+3) true =
      true :: true :: List.replicate (p+1) true := by
    rw [show p+3=(p+1)+1+1 by omega, List.replicate_succ, List.replicate_succ]
  have hword : oppairs (q+1) ++ List.replicate (p+3) true =
      false :: (pairs q ++ ([true,true,true] ++ List.replicate (p+1) true)) := by
    rw [show oppairs (q+1) = false :: true :: oppairs q by rfl, hp]
    simpa only [List.cons_append] using
      congrArg (List.cons false) (shift_word q (List.replicate (p+1) true))
  have hin : sourceSection ⟨3*k+4,q+1,p+3⟩ =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ ([true,true,true] ++ List.replicate (p+1) true))) := by
    unfold sourceSection
    simp only [List.append_assoc]
    change init (List.replicate (3*k+4-2) true ++
      (oppairs (q+1) ++ List.replicate (p+3) true)) = _
    rw [show 3*k+4-2=3*k+2 by omega, hword]
  have hn : List.replicate (8*k+9) true =
      true :: true :: List.replicate (8*k+7) true := by
    rw [show 8*k+9=(8*k+7)+1+1 by omega,
      List.replicate_succ,List.replicate_succ]
  have hout : (⟨[],false,List.replicate (8*k+9) true ++
      (oppairs (q+2) ++ false :: List.replicate (p+1) true),5⟩ : Cfg) =
      sourceSection ⟨8*k+9,q+3,p⟩ := by
    unfold sourceSection
    simp only [List.append_assoc]
    change (⟨[],false,List.replicate (8*k+9) true ++
      (oppairs (q+2) ++ false :: List.replicate (p+1) true),5⟩ : Cfg) =
      ⟨[],false,true::true::(List.replicate (8*k+9-2) true ++
        (oppairs (q+3) ++ List.replicate p true)),5⟩
    rw [show 8*k+9-2=8*k+7 by omega, hn, output_word]
    rfl
  rw [hin, ←hout]
  exact h

/-- All canonical E transitions with q>0, b>=3 are exact source returns. -/
theorem e_contract_many (s t : DRegular.L)
    (hc : DRegular.Canon s) (he : s.a % 3 = 1)
    (hq : s.q > 0) (hb : s.b >= 3)
    (hn : DRegular.next s = some t) :
    run (DRegular.duration s) (sourceSection s) = sourceSection t := by
  rcases s with ⟨a,q,b⟩
  change a % 3 = 1 at he
  change a >= 2 ∧ (q ≠ 0 ∨ b=0) at hc
  change q > 0 at hq
  change b >= 3 at hb
  have ha : a = 3*((a-4)/3)+4 := by omega
  have hk : a/3-1=(a-4)/3 := by omega
  have h2 : a%3≠2 := by omega
  have h0 : a%3≠0 := by omega
  have hb0 : b≠0 := by omega
  have hb1 : b≠1 := by omega
  have hb2 : b≠2 := by omega
  cases q with
  | zero => omega
  | succ q =>
    simp [DRegular.next,h2,h0,hb0,hb1,hb2,hk] at hn
    cases hn
    have hin : sourceSection ⟨a,q+1,b⟩ =
        sourceSection ⟨3*((a-4)/3)+4,q+1,(b-3)+3⟩ := by
      rw [←ha, show b-3+3=b by omega]
    have hdur : DRegular.duration ⟨a,q+1,b⟩ =
        12*((a-4)/3)*((a-4)/3)+49*((a-4)/3)+58+6*q := by
      simp [DRegular.duration,h2,h0,hb0,hb1,hk]
      omega
    rw [hdur,hin]
    exact e_many ((a-4)/3) q (b-3)

#print axioms e_contract_many
#print axioms e_many
end BB6.Agent31RegularE
