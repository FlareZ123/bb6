import ValSixC58
import HighThreeAffine
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11C58LatePrior

/-- The genuine original-source old ValSixFull+C58 high sieve admits
    the entire late-depth-seven class j=372 mod512, m=3. The new
    odd-part-three cone therefore adds a strictly stronger gate. -/
theorem old_sieve_admits_late_high (t : Nat) :
    BB6.Agent11C58ValSix.highAllowed (372+512*t) 3 := by
  let j := 372+512*t
  have hbase : BB6.Agent3.jointHighAllowed j 3 := by
    unfold BB6.Agent3.jointHighAllowed
    dsimp [j]
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j 3 := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase,by dsimp [j]; omega⟩
  have hdy : ∀ n, ¬(n+4≤2*3+2 ∧
      (j+3*3+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨hn,hres,_⟩
    have hcases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 := by omega
    rcases hcases with h|h|h|h|h <;> subst n <;> dsimp [j] at hres <;> omega
  have h19 : BB6.Agent19Joint.highAllowed j 3 := by
    unfold BB6.Agent19Joint.highAllowed
    refine ⟨hrect,hdy,?_,?_,?_,?_⟩ <;> dsimp [j] <;> omega
  have h29 : BB6.Agent29Joint.highAllowedPlus j 3 := by
    unfold BB6.Agent29Joint.highAllowedPlus
    refine ⟨h19,?_,?_,?_,?_⟩ <;> dsimp [j] <;> omega
  have hval : BB6.Agent3ValSix.highAllowedValSixThree j 3 := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
      BB6.Agent3ValSix.highAllowedValSix
    refine ⟨⟨h29,?_,?_⟩,?_⟩ <;> dsimp [j] <;> omega
  have h11 : BB6.Agent11Joint.highAllowed j 3 := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by dsimp [j]; omega,by dsimp [j]; omega⟩
  have hfive : BB6.Agent19Five.highAllowed j 3 := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  let k := 2^(2*3+2)*(j+3)-(j+3*3+5)
  have hk : k=95614+130560*t := by
    dsimp [k,j]
    omega
  let u := 747+1020*t
  have hu : 7≤u := by dsimp [u]; omega
  have hu4 : u%4=3 := by dsimp [u]; omega
  have hb : k+2=2^7*u := by dsimp [u]; rw [hk]; omega
  have hmass : (2*j+3+2*k+4*7)%8=3 := by
    rw [hk]
    dsimp [j]
    omega
  have hright : (BB6.Agent15.affineNormalize (2*j+3) k).2≠4 :=
    BB6.Agent11ThreeAffine.dyadic_three_affine_right_ne_four
      7 (2*j+3) k u hu hu4 hb hmass
  have hall : BB6.Agent3ValSix.highAllowedValSixFull j 3 := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    refine ⟨hval,hfive,?_,?_,?_,?_⟩
    · dsimp [j]; omega
    · dsimp [j]; omega
    · omega
    · simpa [k] using hright
  have hnot58 : ¬(3≤3 ∧ j%32=31 ∧ (j+3*3+5)%256=198) := by
    dsimp [j]
    omega
  exact ⟨hall,hnot58⟩

#print axioms old_sieve_admits_late_high
end BB6.Agent11C58LatePrior
