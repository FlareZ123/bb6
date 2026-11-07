import S4SharpCensus
import S4EarlyCompletion
import Lean.Elab.Tactic.Omega

/-! Structural compression of the finite S4 root six-phase sharpness
certificate: 67 of 68 exceptional phases are handled by the general
early-drain completion theorems, with one literal special completion. -/
namespace S4EarlyRoot
open S4Power S4Octet S4Toggle S4PrefixCausal S4PrefixGate64
open S4SharpCensus S4EarlyCompletion
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def covered (xs : List Nat) : Bool :=
  decide ((W xs+509)%64=0) ||
  (earlyG 509 xs && decide ((W (gp 509 xs)+290)%64=0)) ||
  (earlyG 509 xs && earlyG 290 (gp 509 xs) &&
     decide ((W (gp 290 (gp 509 xs))+219)%64=0))

/-- A single kernel computation on the already checked 68-pair census.
    Only phase 279 fails the general structural early-stop criterion. -/
theorem bad_early_or_279 (r : Nat × List Nat) (hr : r∈badCases) :
    r.1=279 ∨ covered r.2=true := by
  have hc : badCases.all (fun p => decide (p.1=279 ∨ covered p.2=true)) = true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp hc) r hr)

/-- General early-drain completion handles every `covered` finite prefix. -/
theorem covered_completion
  (xs : List Nat) (hl : xs.length=6) (hc : covered xs=true) :
  ∃ t : Nat, P (xs++[t])=none := by
  simp only [covered,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at hc
  rcases hc with (h0 | ⟨he0,h1⟩) | ⟨⟨he0,he1⟩,h2⟩
  · obtain ⟨t,ht⟩ := terminal_completion 509 6 xs (by omega) hl (by simpa using h0)
    exact ⟨t, by simp [P,ht]⟩
  · exact second_completion 6 xs hl he0 (by simpa using h1)
  · exact third_completion 6 xs hl he0 he1 (by simpa using h2)

/-- All 68 cyclic bad phases have a synthetic one-digit halting completion.
    This proof invokes general structural lemmas for 67, and the exceptional
    source-certified literal phase 279 for the remaining one. -/
theorem root_bad_has_witness
  (i : Nat) (hi : i<1024) (hb : guard6 (prefixRun i phase)=false) :
  ∃ t : Nat, P (prefixRun i phase ++ [t])=none := by
  have hl : (prefixRun i phase).length=6 := by
    simpa [prefixRun_length,phase]
  have hm : (i,prefixRun i phase)∈badCases := by
    have hs := scan_contains 1024 0 phase i hi hb
    simpa only [scanExact,Nat.zero_add] using hs
  rcases bad_early_or_279 _ hm with he | he
  · have hphase : prefixRun 279 phase = [282,967,2129,1857,9553,13781] := by decide
    rcases he with rfl
    exact ⟨104, by simpa [hphase] using S4Sharp6.bad_0279⟩
  · exact covered_completion _ hl he

#print axioms bad_early_or_279
#print axioms covered_completion
#print axioms root_bad_has_witness
end S4EarlyRoot
