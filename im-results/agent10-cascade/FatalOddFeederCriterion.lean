import FatalOddFeederGap
set_option maxHeartbeats 0

namespace CascadeFastReturn
open CascadeBitSweep CascadeResetInverse CascadeSweep CascadeFirstFork
open CascadeUniformFatal CascadeManyShield

/-- An all-index modular source criterion excluding the genuine valuation-one
    odd predecessor of a fatal target from the authentic blank-root orbit.
    The two tests are on that candidate (mod 27) and its forced even parent
    (mod 9). This applies to arbitrary n≥22, not only the periodic family. -/
theorem fatal_odd_feeder_modular_root_exclusion
    (n : Nat)
    (hn : 22≤n)
    (hfdiv : (2*fatal n+5)%9=0)
    (hxdiv : (2*oddPre n (fatal n)+5)%27≠0)
    (hhdiv :
      (2*(2*oddPre n (fatal n)-8*2^(n-2)-(n-2))+5)%9≠0) :
    ResetParent (oddPre n (fatal n)) (fatal n) ∧
    ¬ReachC (2,0) (oddPre n (fatal n),0) := by
  let k := n-2
  let p := 2^k
  let u := fatal n
  let d := (2*u+5)/9
  let x := oddPre n u
  let h := 2*x-8*p-k
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
  have hxlo : 6*p≤x := by omega
  have hxband : 4*x+10<27*p := by omega
  have hxindexlo : 4*p≤x+k+4 := by omega
  have hxindexhi : x+k+5<8*p := by omega
  have hxlower : 12*p+k+4≤2*x := by omega
  have hi : firstFailIndex x=k :=
    firstFailIndex_unique x k hxindexhi
      (guards_from_low x k hxindexlo)
  have hhlin : h+8*p+k=2*x := by dsimp [h]; omega
  have hh4 : 4*p≤h := by omega
  have hhtop : 2*h+5<9*p := by omega
  have heqh : 2*x-8*p-k=h := by omega
  have hdx27 : (2*x+5)%27≠0 := by simpa only [x,u] using hxdiv
  have hdh9 : (2*h+5)%9≠0 := by
    have hh' : 2*(2*x-8*p-k)+5=2*h+5 := by omega
    have hh'' : (2*(2*x-8*p-k)+5)%9≠0 := by
      simpa only [x,u,p,k] using hhdiv
    rw [hh'] at hh''
    exact hh''
  have hno : ¬ReachC (2,0) (x,0) :=
    narrow_27_middle9_root_exclusion k x
      (by omega) hi hxlower hxband hdx27
      (by simpa only [heqh] using hhtop)
      (by simpa only [heqh] using hdh9)
  have hp : ResetParent (oddPre n u) u :=
    odd_parent_near_top n u (n+4) (by omega) (by omega)
      (by simpa only [u] using fatal_close n (by omega))
      (by simpa only [u] using fatal_size n (by omega)) hfdiv
  exact ⟨hp,by simpa only [x,u] using hno⟩

#print axioms fatal_odd_feeder_modular_root_exclusion
end CascadeFastReturn
