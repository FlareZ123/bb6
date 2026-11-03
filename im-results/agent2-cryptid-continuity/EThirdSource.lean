import Lean.Elab.Tactic.Omega
import ESecondSource
import CryptidTriplePairs

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.EThirdSource
open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31SecondSource

/-- Third E-branch duration after a two-return exception with t ≡ 1 mod 3. -/
def thirdCost (v : Nat) : Nat :=
  let K := 64*v+31
  12*K*K+49*K+58+6*2

/-- Full physical third checkpoint, including the unchanged six-one packet. -/
def thirdFinish (v h : Nat) : Cfg :=
  ⟨[],false,
    List.replicate (512*v+257) true ++
      (oppairs 4 ++ false :: (List.replicate (2*h) true ++
        (false :: List.replicate 6 true))),5⟩

/-- Direct exact primitive-step run for the previously source-pending third
    checkpoint in the residue t = 3v+1, with arbitrary h. -/
theorem third_source (v h : Nat) :
    run (thirdCost v) (finish (3*v+1) h) = thirdFinish v h := by
  let K := 64*v+31
  let ys := List.replicate (2*h) true ++ (false :: List.replicate 6 true)
  have hlen : 8*(8*(3*v+1)+3)+9 = 3*K+4 := by
    dsimp [K]
    omega
  have hone : List.replicate (3*K+4) true =
      [true,true] ++ List.replicate (3*K+2) true := by
    rw [show 3*K+4=2+(3*K+2) by omega]
    rw [← List.replicate_append_replicate]
    rfl
  have hthree : List.replicate (2*h+3) true =
      [true,true,true] ++ List.replicate (2*h) true := by
    rw [show 2*h+3=3+2*h by omega]
    rw [← List.replicate_append_replicate]
    rfl
  have hinput :
      finish (3*v+1) h =
        init (List.replicate (3*K+2) true ++
          false :: (pairs 2 ++ ([true,true,true] ++ ys))) := by
    change (⟨[],false,
      List.replicate (8*(8*(3*v+1)+3)+9) true ++
        (oppairs 2 ++ false :: (List.replicate (2*h+3) true ++
          (false :: List.replicate 6 true))),5⟩ : Cfg) = _
    rw [hlen,hthree,hone]
    simp [init,ys,pairs,oppairs,List.append_assoc]
  rw [hinput]
  change run (12*K*K+49*K+58+6*2)
      (init (List.replicate (3*K+2) true ++
        false :: (pairs 2 ++ ([true,true,true] ++ ys)))) = _
  rw [full_E_triple_pairs]
  have hnum : 8*K+9 = 512*v+257 := by
    dsimp [K]
    omega
  rw [hnum]
  simp [thirdFinish,K,ys,oppairs]

/-- The first two source-macro endpoints have physical ObsEq semantics;
    the third E endpoint is an exact source-equality, hence these compose
    without treating implicit trailing blank zeros as literal list equality. -/
theorem three_returns_source (v h : Nat) :
    ObsEq
      (run (firstCost (3*v+1) h + secondCost (3*v+1) + thirdCost v)
        (start (3*v+1) h))
      (thirdFinish v h) := by
  have hthird : ObsEq
      (run (thirdCost v) (finish (3*v+1) h))
      (thirdFinish v h) := by
    rw [third_source]
    exact cfgEq_refl _
  exact source_chain
    (firstCost (3*v+1) h + secondCost (3*v+1))
    (thirdCost v)
    (start (3*v+1) h)
    (finish (3*v+1) h)
    (thirdFinish v h)
    (two_returns_source (3*v+1) h)
    hthird

#print axioms third_source
#print axioms three_returns_source
end BB6.EThirdSource
