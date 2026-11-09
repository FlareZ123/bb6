import DoubleOddGapRoot
import FirstFork
set_option maxHeartbeats 0

namespace CascadeFastReturn
open CascadeBitSweep CascadeResetInverse CascadeSweep CascadeFirstFork
open CascadeUniformFatal CascadeManyShield

private theorem feeder_pow243 (t : Nat) :
    2^(20+486*t)%243=31 := by
  induction t with
  | zero => decide
  | succ t ih =>
    have heq : 20+486*(t+1)=(20+486*t)+486 := by omega
    rw [heq, Nat.pow_add, Nat.mul_mod, ih]
    decide

private theorem feeder_growth (k : Nat) (hk : 20≤k) :
    12*(k+2)+40<2^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 20≤k
    · have hp := ih h
      rw [Nat.pow_succ]
      omega
    · have he : k=19 := by omega
      subst k
      decide

/-- Closed arithmetic of the first odd predecessor of F_(22+486t).
    The predecessor lies in the narrow high 27-adic band, and its
    even parent lies inside the 9-adic no-image gap. -/
private theorem feeder_arithmetic (t : Nat) :
  let n := 22+486*t
  let k := n-2
  let p := 2^k
  let d := (32*p-2*n-3)/9
  let x := 4*d-8*p-n-3
  let h := 2*x-8*p-k
  (9*d=32*p-2*n-3) ∧
  (x+8*p+n+3=4*d) ∧
  (9*x+17*n+39=56*p) ∧
  (h+8*p+k=2*x) ∧
  (9*h+43*n+60=40*p) ∧
  (x%27=12) ∧ (h%9=8) ∧
  (6*p≤x) ∧ (4*x+10<27*p) ∧
  (4*p≤h) ∧ (2*h+5<9*p) ∧
  (4*p≤x+k+4) ∧ (x+k+5<8*p) ∧
  (12*p+k+4≤2*x) := by
  let n := 22+486*t
  let k := n-2
  let p := 2^k
  let d := (32*p-2*n-3)/9
  let x := 4*d-8*p-n-3
  let h := 2*x-8*p-k
  have heqk : k=20+486*t := by dsimp [k,n]; omega
  have hn : n=k+2 := by dsimp [n,k]; omega
  have hk : 20≤k := by dsimp [k,n]; omega
  have hpbound : 12*n+40 < p := by rw [hn]; exact feeder_growth k hk
  have hpmod : p%243=31 := by simpa only [p,heqk] using feeder_pow243 t
  have hnmod : n%243=22 := by dsimp [n]; omega
  have hbase : 32*p-2*n-3+2*n+3=32*p := by omega
  have hqmod : (32*p-2*n-3)%9=0 := by omega
  have hd : 9*d=32*p-2*n-3 := by dsimp [d]; omega
  have hdx : x+8*p+n+3=4*d := by dsimp [x]; omega
  have hx : 9*x+17*n+39=56*p := by omega
  have hx6 : 6*p≤x := by omega
  have hxband : 4*x+10<27*p := by omega
  have hxindexlo : 4*p≤x+k+4 := by omega
  have hxindexhi : x+k+5<8*p := by omega
  have hh : h+8*p+k=2*x := by dsimp [h]; omega
  have hlin : 9*h+43*n+60=40*p := by omega
  have hh4 : 4*p≤h := by omega
  have hhtop : 2*h+5<9*p := by omega
  have hxmod : x%27=12 := by omega
  have hhmod : h%9=8 := by omega
  have hxlower : 12*p+k+4≤2*x := by omega
  exact ⟨hd,hdx,hx,hh,hlin,hxmod,hhmod,
    hx6,hxband,hh4,hhtop,hxindexlo,hxindexhi,hxlower⟩

/-- Unfolding the original-source fatal height and exact valuation-one
    odd inverse gives the closed arithmetic feeder x. -/
private theorem feeder_candidate_eq (t : Nat) :
  let n := 22+486*t
  let k := n-2
  let p := 2^k
  let d := (32*p-2*n-3)/9
  let x := 4*d-8*p-n-3
  oddPre n (fatal n)=x := by
  let n := 22+486*t
  let k := n-2
  let p := 2^k
  let d := (32*p-2*n-3)/9
  let x := 4*d-8*p-n-3
  have hn : n=k+2 := by dsimp [n,k]; omega
  have hk : 20≤k := by dsimp [n,k]; omega
  have hg : 12*n+40<p := by rw [hn]; exact feeder_growth k hk
  have hpow : 2^n=4*p := by
    rw [hn,Nat.pow_add]
    simp only [show 2^2=4 by decide]
    dsimp [p]
    omega
  have hf : fatal n+n+4=16*p := by dsimp [fatal]; omega
  have hnum : 2*fatal n+5=32*p-2*n-3 := by omega
  have hd : (2*fatal n+5)/9 =d := by rw [hnum]
  have hodd : oddPre n (fatal n) = x := by
    dsimp [oddPre,x]
    rw [hd]
    change 4*d-8*2^k-k-5=4*d-8*p-n-3
    dsimp [p]
    omega
  exact hodd

/-- Every fatal index n=22+486t has a genuine odd first-reset parent,
    but that specific parent is completely unreachable from the
    authentic blank reset root C(2,0). This is an infinite, source-backed
    fatal-feeder exclusion; the OTHER even parent remains unclassified. -/
theorem fatal_odd_feeder_unreachable (t : Nat) :
  let n := 22+486*t
  ResetParent (oddPre n (fatal n)) (fatal n) ∧
  ¬ReachC (2,0) (oddPre n (fatal n),0) := by
  let n := 22+486*t
  let k := n-2
  let p := 2^k
  let d := (32*p-2*n-3)/9
  let x := 4*d-8*p-n-3
  let h := 2*x-8*p-k
  have hn : 22≤n := by dsimp [n]; omega
  have hres : n%18=4 := by dsimp [n]; omega
  have hp : ResetParent (oddPre n (fatal n)) (fatal n) :=
    fatal_has_odd_parent n (by omega) (Or.inl hres)
  obtain ⟨hd,hdx,hx,hh,hlin,hxmod,hhmod,hxlo,hxtop,hhlo,hhtop,hindexlo,
    hindexhi,hentrylo⟩ := feeder_arithmetic t
  have hi : firstFailIndex x=k :=
    firstFailIndex_unique x k hindexhi
      (guards_from_low x k hindexlo)
  have heq : oddPre n (fatal n)=x := feeder_candidate_eq t
  have hdiv27 : (2*x+5)%27≠0 := by omega
  have hmiddle : 2*(2*x-8*p-k)+5<9*p := by
    have he : 2*x-8*p-k=h := by omega
    rw [he]
    exact hhtop
  have hdiv9 : (2*(2*x-8*p-k)+5)%9≠0 := by
    have he : 2*x-8*p-k=h := by omega
    rw [he]
    omega
  have hno : ¬ReachC (2,0) (x,0) :=
    narrow_27_middle9_root_exclusion k x
      (by dsimp [k,n]; omega) hi hentrylo hxtop
      hdiv27 hmiddle hdiv9
  refine ⟨hp, ?_⟩
  change ¬ReachC (2,0) (oddPre n (fatal n),0)
  rw [heq]
  exact hno

#print axioms feeder_arithmetic
#print axioms feeder_candidate_eq
#print axioms fatal_odd_feeder_unreachable
end CascadeFastReturn
