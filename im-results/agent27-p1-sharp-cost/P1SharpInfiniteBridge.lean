import P1SharpInfinite
import InverseIff

namespace BB6.Agent27Budget
open BB6.Agent47P1
open BB6.Agent1Quarter

/-- An unbounded family of numerically tight terminal inverse edges,
using the authentic source inverseAt function. This theorem makes no claim
of an OddCone path from any critical root or any blank-orbit reachability. -/
theorem infinite_sharp_source_terminal (k : Nat) :
    let u := exactU k
    let n := 2*(k+1)
    let m := 14*u+7-n
    inverseAt 8 (56*u+21) 2 = some (21*u+10,14*u+4) ∧
    8+(56*u+21)+2*m+2*n+13=14*2^n ∧
    2*(21*u+10)+8=14*2^(2*k+1) ∧
    7*2^n=3*m+3*n+7 := by
  have h := infinite_exact_terminal k
  dsimp at h ⊢
  rcases h with ⟨hroot,hdyad,hlinear,hpow,hsharp⟩
  have hinverse : inverseAt 8 (56*exactU k+21) 2 =
      some (21*exactU k+10,14*exactU k+4) := by
    apply (inverseAt_iff_power_mass 8 (56*exactU k+21) 2
      (21*exactU k+10) (14*exactU k+4)
      (by decide) (by decide) (by omega)).mpr
    constructor
    · exact hdyad
    · have hc : (14*exactU k+4)%2=0 := by omega
      omega
  exact ⟨hinverse,hroot,hpow,hsharp⟩

#print axioms infinite_sharp_source_terminal
end BB6.Agent27Budget
