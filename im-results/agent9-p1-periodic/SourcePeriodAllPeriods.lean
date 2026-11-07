import PeriodAllPeriods
import UniformPrecisionPath
import ShadowAlgebra

/-!
# Original-source extraction of periodic depth tails

A genuine infinite ShadowReach trajectory determines a scalar Run on every
finite interval. Consequently an eventually periodic inverse-depth sequence
would give a repeated fixed-word Run, which the all-period theorem excludes
when the period contains positive depth. If the period is all zero, the
preserved source margin forces an impossible strictly descending sequence.

This excludes eventually periodic depth tails. It does not assert that every
infinite source trajectory must be eventually periodic.
-/

namespace BB6.Precision

open PeriodWord

/-- A coherent infinite trajectory in the original scalar ShadowReach step
relation, with the exact inverse-depth witnesses retained at each time. -/
structure InfiniteShadowPath (L root : Nat) where
  m : Nat → Nat
  z : Nat → Nat
  depth : Nat → Nat
  quotient : Nat → Nat
  hroot : ShadowReach L root (m 0) (z 0)
  hdiv : ∀ n, z n = 2^(depth n) * quotient n
  hnext : ∀ n, 2 * z (n+1) + 1 =
    L + m n + depth n + quotient n
  hm : ∀ n, m (n+1) = m n + depth n + 1

namespace InfiniteShadowPath

/-- Every state on the trajectory remains reachable from its original
ShadowReach root. -/
theorem reach_all {L root : Nat} (p : InfiniteShadowPath L root) :
    ∀ n, ShadowReach L root (p.m n) (p.z n) := by
  intro n
  induction n with
  | zero => exact p.hroot
  | succ n ih =>
      have h := ShadowReach.step ih (p.depth n) (p.quotient n)
        (p.z (n+1)) (p.hdiv n) (p.hnext n)
      simpa [p.hm n] using h

/-- Read any finite segment of a genuine source trajectory as the exact
PeriodWord.Run over its list of inverse depths. -/
theorem run_of_list_segment {L root : Nat}
    (p : InfiniteShadowPath L root) (N : Nat) (w : List Nat)
    (hdepth : ∀ i (hi : i < w.length),
      p.depth (N+i) = w.get ⟨i,hi⟩) :
    Run L w (p.m N) (p.z N)
      (p.m (N+w.length)) (p.z (N+w.length)) := by
  induction w generalizing N with
  | nil =>
      simpa using Run.nil (p.m N) (p.z N)
  | cons t ts ih =>
      have ht : p.depth N = t := by
        have h := hdepth 0 (by simp)
        simpa using h
      have htail : ∀ i (hi : i < ts.length),
          p.depth (N+1+i) = ts.get ⟨i,hi⟩ := by
        intro i hi
        have hi' : i+1 < (t::ts).length := by
          simpa using Nat.succ_lt_succ hi
        have h := hdepth (i+1) hi'
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hrest := ih (N+1) htail
      have hdiv : p.z N = 2^t * p.quotient N := by
        simpa [ht] using p.hdiv N
      have hn : 2*p.z (N+1)+1 =
          L+p.m N+t+p.quotient N := by
        simpa [ht] using p.hnext N
      have hm : p.m (N+1) = p.m N+t+1 := by
        simpa [ht] using p.hm N
      have hrest' : Run L ts (p.m N+t+1) (p.z (N+1))
          (p.m (N+1+ts.length)) (p.z (N+1+ts.length)) := by
        simpa [hm] using hrest
      have hend : N+(t::ts).length = N+1+ts.length := by
        simp [Nat.add_comm, Nat.add_left_comm]
      rw [hend]
      exact Run.cons t (p.quotient N) hdiv hn hrest'

/-- A positive-depth word cannot recur as the exact depth block forever,
even when the recurrence begins after an arbitrary finite prefix. -/
theorem no_eventually_periodic_positive_depth
    {L root : Nat} (p : InfiniteShadowPath L root)
    (N d : Nat) (w : List Nat) (hlen : w.length = d)
    (hperiod : ∀ (n i : Nat) (hi : i < d),
      p.depth (N+n*d+i) =
        w.get ⟨i, by simpa [hlen] using hi⟩)
    (hp : ∃ t ∈ w, 0<t) : False := by
  let m' : Nat → Nat := fun n => p.m (N+n*d)
  let z' : Nat → Nat := fun n => p.z (N+n*d)
  have hrun : ∀ n, Run L w (m' n) (z' n)
      (m' (n+1)) (z' (n+1)) := by
    intro n
    have hdepth : ∀ i (hi : i < w.length),
        p.depth (N+n*d+i) = w.get ⟨i,hi⟩ := by
      intro i hi
      exact hperiod n i (by simpa [hlen] using hi)
    have h := p.run_of_list_segment (N+n*d) w hdepth
    have hend : N+n*d+w.length = N+(n+1)*d := by
      rw [hlen]
      calc
        N+n*d+d = N+(n*d+d) := by ac_rfl
        _ = N+(n+1)*d := by rw [Nat.add_mul]; simp
    rw [hend] at h
    simpa [m',z'] using h
  exact PeriodWord.no_infinite_positive_depth_periodic_ray L w hp m' z' hrun

/-- The original ShadowReach transition preserves positivity and the
four-unit source margin whenever the root has that margin and L≥8. -/
theorem shadowreach_margin {L root m z : Nat}
    (hL : 8≤L) (hrootpos : 0<root) (hrootmargin : root+4≤L)
    (hreach : ShadowReach L root m z) :
    0<z ∧ z+4≤L+m := by
  induction hreach with
  | root => exact ⟨hrootpos,hrootmargin⟩
  | @step m z hreach t v zp hdiv hnext ih =>
      simpa [Nat.add_assoc] using
        BB6.Shadow.shadow_step_preserves_offset
          L m z t v zp hL ih.1 ih.2 hdiv hnext

/-- The root margin propagates to every state on the infinite trajectory. -/
theorem margin_all {L root : Nat} (p : InfiniteShadowPath L root)
    (hL : 8≤L) (hrootpos : 0<root) (hrootmargin : root+4≤L) :
    ∀ n, 0<p.z n ∧ p.z n+4≤L+p.m n := by
  have hstart := shadowreach_margin hL hrootpos hrootmargin p.hroot
  intro n
  induction n with
  | zero => exact hstart
  | succ n ih =>
      have h := BB6.Shadow.shadow_step_preserves_offset
        L (p.m n) (p.z n) (p.depth n) (p.quotient n) (p.z (n+1))
        hL ih.1 ih.2 (p.hdiv n) (p.hnext n)
      simpa [p.hm n, Nat.add_assoc] using h

/-- The source margin makes an all-zero depth tail impossible: its gap
D=L+m-z would satisfy 2D'=D+3 and hence decrease strictly forever. -/
theorem no_eventually_zero_depth {L root : Nat}
    (p : InfiniteShadowPath L root)
    (hmargin : ∀ n, 0<p.z n ∧ p.z n+4≤L+p.m n)
    (N : Nat) (hzero : ∀ n, N≤n → p.depth n=0) : False := by
  let gap : Nat → Nat := fun n => L+p.m n-p.z n
  have hgap : ∀ n, N≤n → 4≤gap n := by
    intro n hn
    have hmarg := (hmargin n).2
    dsimp [gap]
    omega
  have hstep : ∀ n, N≤n → 2*gap (n+1)=gap n+3 := by
    intro n hn
    have ht : p.depth n=0 := hzero n hn
    have hv : p.quotient n=p.z n := by
      simpa [ht] using (p.hdiv n).symm
    have hnext : 2*p.z (n+1)+1=L+p.m n+p.z n := by
      simpa [ht,hv] using p.hnext n
    have hm : p.m (n+1)=p.m n+1 := by
      simpa [ht] using p.hm n
    have hmn := hmargin n
    have hmn1 := hmargin (n+1)
    dsimp [gap]
    omega
  have hlt : ∀ n, N≤n → gap (n+1)<gap n := by
    intro n hn
    have hg := hgap n hn
    have hs := hstep n hn
    omega
  have hdesc : ∀ k, gap (N+k)+k≤gap N := by
    intro k
    induction k with
    | zero => simp [gap]
    | succ k ih =>
        have hs := hlt (N+k) (by omega)
        have hs' : gap (N+(k+1))<gap (N+k) := by
          simpa [Nat.add_assoc] using hs
        omega
  have hcontr := hdesc (gap N+1)
  omega

/-- No genuine source ShadowReach trajectory with a positive root margin can
have an eventually periodic inverse-depth sequence. The positive-period
case follows from the all-period theorem; the all-zero case follows from the
strictly descending source gap. -/
theorem no_eventually_periodic_shadow_path
    {L root : Nat} (p : InfiniteShadowPath L root)
    (hL : 8≤L) (hrootpos : 0<root) (hrootmargin : root+4≤L)
    (N d : Nat) (hd : 0<d) (w : List Nat) (hlen : w.length=d)
    (hperiod : ∀ (n i : Nat) (hi : i<d),
      p.depth (N+n*d+i) =
        w.get ⟨i, by simpa [hlen] using hi⟩) : False := by
  have hmargin := p.margin_all hL hrootpos hrootmargin
  by_cases hp : ∃ t∈w,0<t
  · exact p.no_eventually_periodic_positive_depth N d w hlen hperiod hp
  · have hwzero : ∀ t∈w,t=0 := by
      intro t ht
      by_cases ht0 : t=0
      · exact ht0
      · have htpos : 0<t := by omega
        exact False.elim (hp ⟨t,ht,htpos⟩)
    have hzero : ∀ n, N≤n → p.depth n=0 := by
      intro n hn
      let k := n-N
      let q := k/d
      let r := k%d
      have hr : r<d := Nat.mod_lt _ hd
      have hmod : r+d*q=k := by
        dsimp [r,q,k]
        exact Nat.mod_add_div _ _
      have hidx : N+q*d+r=n := by
        calc
          N+q*d+r=N+(r+d*q) := by ac_rfl
          _=N+k := by rw [hmod]
          _=n := by dsimp [k]; omega
      have hgetzero : w.get ⟨r,by simpa [hlen] using hr⟩=0 :=
        hwzero _ (List.get_mem w ⟨r,by simpa [hlen] using hr⟩)
      have h := hperiod q r hr
      rw [hidx,hgetzero] at h
      exact h
    exact p.no_eventually_zero_depth hmargin N hzero

#print axioms no_eventually_periodic_positive_depth
#print axioms shadowreach_margin
#print axioms margin_all
#print axioms no_eventually_zero_depth


/-- Cumulative source depth cost through the first n inverse steps. -/
def depthPrefix {L root : Nat} (p : InfiniteShadowPath L root) : Nat → Nat
  | 0 => 0
  | n+1 => depthPrefix p n + p.depth n + 1

/-- The exact weighted prefix sum in the recentered recurrence. -/
def recenteredPrefixSum {L root : Nat}
    (p : InfiniteShadowPath L root) : Nat → Int
  | 0 => 0
  | n+1 => recenteredPrefixSum p n +
      (2:Int)^(depthPrefix p n) *
        ((p.m 0:Int)+(depthPrefix p n:Int)+(L:Int)-2)

/-- The source cost coordinate is the initial cost plus cumulative depth. -/
theorem m_eq_depthPrefix {L root : Nat}
    (p : InfiniteShadowPath L root) :
    ∀ n, p.m n = p.m 0 + depthPrefix p n := by
  intro n
  induction n with
  | zero => simp [depthPrefix]
  | succ n ih =>
      rw [p.hm n, ih]
      simp [depthPrefix, Nat.add_assoc]

/-- Every infinite source path satisfies an exact prefix identity, with no
    periodicity, bounded-depth, or bounded-step assumption. The identity is
    the telescoped form of PeriodWord.recentered_step. -/
theorem recentered_prefix_identity {L root : Nat}
    (p : InfiniteShadowPath L root) :
    ∀ n,
      (2:Int)^(depthPrefix p n) *
          PeriodWord.recentered L (p.m n) (p.z n) =
        PeriodWord.recentered L (p.m 0) (p.z 0) +
          recenteredPrefixSum p n := by
  intro n
  induction n with
  | zero =>
      simp [depthPrefix, recenteredPrefixSum]
  | succ n ih =>
      have hrec := PeriodWord.recentered_step L (p.m n) (p.z n)
        (p.m (n+1)) (p.z (n+1)) (p.depth n) (p.quotient n)
        (p.hdiv n) (p.hnext n) (p.hm n)
      have hM : depthPrefix p (n+1) =
          depthPrefix p n + (p.depth n+1) := by
        simp [depthPrefix, Nat.add_assoc]
      have hmeq := m_eq_depthPrefix p n
      rw [hM, Int.pow_add]
      calc
        (2:Int)^depthPrefix p n * (2:Int)^(p.depth n+1) *
            PeriodWord.recentered L (p.m (n+1)) (p.z (n+1)) =
          (2:Int)^depthPrefix p n *
            ((2:Int)^(p.depth n+1) *
              PeriodWord.recentered L (p.m (n+1)) (p.z (n+1))) := by
                ac_rfl
        _ = (2:Int)^depthPrefix p n *
              (PeriodWord.recentered L (p.m n) (p.z n) +
                (p.m n:Int)+(L:Int)-2) := by
                rw [hrec]
        _ = (2:Int)^depthPrefix p n *
              PeriodWord.recentered L (p.m n) (p.z n) +
            (2:Int)^depthPrefix p n *
              ((p.m n:Int)+(L:Int)-2) := by
                simp only [Int.mul_add, Int.mul_sub]
                omega
        _ = (2:Int)^depthPrefix p n *
              PeriodWord.recentered L (p.m n) (p.z n) +
            (2:Int)^depthPrefix p n *
              ((p.m 0:Int)+(depthPrefix p n:Int)+(L:Int)-2) := by
                have hcoef : (p.m n:Int)+(L:Int)-2 =
                    (p.m 0:Int)+(depthPrefix p n:Int)+(L:Int)-2 := by
                  rw [hmeq]
                  simp only [Int.natCast_add]
                rw [hcoef]
        _ = PeriodWord.recentered L (p.m 0) (p.z 0) +
              recenteredPrefixSum p (n+1) := by
                rw [ih]
                simp [recenteredPrefixSum, Int.add_assoc]

#print axioms m_eq_depthPrefix
#print axioms recentered_prefix_identity


/-- The recentered coordinate at the next state is exactly the current
    dyadic quotient. -/
theorem recentered_eq_quotient {L root : Nat}
    (p : InfiniteShadowPath L root) (n : Nat) :
    PeriodWord.recentered L (p.m (n+1)) (p.z (n+1)) =
      (p.quotient n:Int) := by
  dsimp [PeriodWord.recentered]
  rw [p.hm n]
  have hs := congrArg (fun x : Nat => (x:Int)) (p.hnext n)
  omega

/-- Every source-path recentered quotient is positive and bounded by the
    source margin. Combined with recentered_prefix_identity, this bounds the
    positive integer quotient of every prefix divisibility relation. -/
theorem recentered_quotient_bounds {L root : Nat}
    (p : InfiniteShadowPath L root)
    (hL : 8≤L) (hrootpos : 0<root) (hrootmargin : root+4≤L) :
    ∀ n,
      0 < PeriodWord.recentered L (p.m (n+1)) (p.z (n+1)) ∧
      PeriodWord.recentered L (p.m (n+1)) (p.z (n+1)) ≤
        (p.m (n+1):Int)+(L:Int)-6 := by
  intro n
  have hz := (p.margin_all hL hrootpos hrootmargin n).1
  have hdiv := p.hdiv n
  have hqne : p.quotient n≠0 := by
    intro hzero
    rw [hzero] at hdiv
    simp at hdiv
    omega
  have hqpos : 0<p.quotient n := by omega
  have hcenter := p.recentered_eq_quotient n
  have hmarginNext := (p.margin_all hL hrootpos hrootmargin (n+1)).2
  have hmI : (p.z (n+1):Int)+4 ≤
      (L:Int)+(p.m (n+1):Int) := by
    exact_mod_cast hmarginNext
  constructor
  · rw [hcenter]
    exact_mod_cast hqpos
  · rw [hcenter]
    have hcenterI : (p.quotient n:Int) =
        2*(p.z (n+1):Int)-(p.m (n+1):Int)-(L:Int)+2 := by
      simpa [PeriodWord.recentered] using hcenter.symm
    omega

#print axioms recentered_quotient_bounds

#print axioms no_eventually_periodic_shadow_path

end InfiniteShadowPath
end BB6.Precision
