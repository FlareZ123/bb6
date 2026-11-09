import FatalOddFeederCriterion
import FatalFeederResidueArithmetic
set_option maxHeartbeats 0

namespace CascadeFastReturn
open CascadeBitSweep CascadeResetInverse CascadeSweep CascadeFirstFork
open CascadeUniformFatal CascadeManyShield

/-- For each sufficiently high fatal index in any of 46 explicitly
    decidable residue classes modulo 486, the genuine valuation-one
    source odd predecessor exists and is unreachable from C(2,0).
    The finite cardinality 46 is separately certified by
    CascadeFatal46.exact_good_residue_count. -/
theorem fatal_odd_feeder_46_residue_exclusion (n : Nat)
    (hn : 22≤n)
    (hg : CascadeFatal46.good (n%486)) :
    ResetParent (oddPre n (fatal n)) (fatal n) ∧
    ¬ReachC (2,0) (oddPre n (fatal n),0) := by
  let k := n-2
  let p := 2^k
  let u := fatal n
  let d := (2*u+5)/9
  let x := oddPre n u
  let h := 2*x-8*p-k
  have hres : n%18=4 ∨ n%18=5 := by
    have hr : n%18=(n%486)%18 := by omega
    rw [hr]
    exact hg.1
  have hfdiv : (2*fatal n+5)%9=0 :=
    fatal_divnine n (by omega) hres
  have hk : 20≤k := by dsimp [k]; omega
  have hpbound : 12*n+40<p := by
    have he : n=k+2 := by dsimp [k]; omega
    rw [he]
    exact feeder_growth k hk
  have hpow : 2^n=4*p := by
    have he : n=k+2 := by dsimp [k]; omega
    rw [he,Nat.pow_add]
    simp only [show 2^2=4 by decide]
    dsimp [p]
    omega
  have hclose : u+n+4=16*p := by dsimp [u,fatal]; omega
  have hnum : 2*u+5=32*p-2*n-3 := by omega
  have hd : 9*d=2*u+5 := by dsimp [d,u]; omega
  have hdx : x+8*p+n+3=4*d := by
    dsimp [x,oddPre,d]
    have he : n-2=k := by dsimp [k]
    rw [he]
    dsimp [p]
    omega
  have hx : 9*x+17*n+39=56*p := by omega
  have hh : h+8*p+k=2*x := by dsimp [h]; omega
  have hlin : 9*h+43*n+60=40*p := by omega
  have hrelx : 9*x+17*n+39=56*2^(n-2) := hx
  have hrelh : 9*h+43*n+60=40*2^(n-2) := hlin
  obtain ⟨hxdiv,hhdiv⟩ :=
    CascadeFatal46.source_bridge n x h hrelx hrelh hn hg
  have hxdiv' : (2*oddPre n (fatal n)+5)%27≠0 := by
    change (2*x+5)%27≠0
    exact hxdiv
  have hhdiv' :
      (2*(2*oddPre n (fatal n)-8*2^(n-2)-(n-2))+5)%9≠0 := by
    change (2*h+5)%9≠0
    exact hhdiv
  exact fatal_odd_feeder_modular_root_exclusion n hn hfdiv hxdiv' hhdiv'

#print axioms fatal_odd_feeder_46_residue_exclusion
end CascadeFastReturn
