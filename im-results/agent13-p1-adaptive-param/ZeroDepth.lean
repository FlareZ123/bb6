import Lean
namespace BB6.Agent13ZeroDepth

/-- Exact scalar shadow reach with the original inverse-edge arithmetic. -/
inductive ShadowReach (L z0 : Nat) : Nat → Nat → Prop where
| root : ShadowReach L z0 0 z0
| step {m z} : ShadowReach L z0 m z → (t v zp : Nat) →
    z=2^t*v → 2*zp+1=L+m+t+v →
    ShadowReach L z0 (m+t+1) zp

/-- All shadow successors preserve margin four from the linear wall. -/
theorem shadow_slack_four (L z0 m z : Nat)
    (hroot:z0+4≤L)
    (h : ShadowReach L z0 m z) : z+4≤L+m := by
  induction h with
  | root => simpa using hroot
  | @step m z hi t v zp hdiv hn ih =>
      have hpow : 1≤(2:Nat)^t := Nat.one_le_pow t 2 (by decide)
      have hv : v≤z := by
        rw [hdiv]
        have hmul : (1:Nat)*v ≤ (2:Nat)^t*v := Nat.mul_le_mul_right v hpow
        simpa using hmul
      by_cases ht:t=0
      · subst t
        have hvz : v=z := by simpa using hdiv.symm
        omega
      · omega

/-- Exact integer margin for dyadic inverse depth zero. -/
def margin (L m z : Nat) : Int := (↑L)+(↑m)-(↑z)-3

theorem margin_step (L m z zp : Nat) (hn:2*zp+1=L+m+z) :
    2*margin L (m+1) zp = margin L m z := by
  unfold margin
  omega

theorem margin_pos (L m z : Nat) (h:z+4≤L+m) : 0<margin L m z := by
  unfold margin
  omega

/-- N consecutive scalar predecessor edges all of inverse depth zero. -/
inductive RunZero (L : Nat) : Nat → Nat → Nat → Prop where
| zero (m z : Nat) : RunZero L 0 m z
| more {N m z zp : Nat} : RunZero L N (m+1) zp →
    2*zp+1=L+m+z → RunZero L (N+1) m z

theorem pow_dvd_margin (L N m z : Nat) (h:RunZero L N m z) :
    (2:Int)^N ∣ margin L m z := by
  induction h with
  | zero m z => simp
  | @more N m z zp hi he ih =>
      rcases ih with ⟨u,hu⟩
      refine ⟨u, ?_⟩
      calc
        margin L m z = 2*margin L (m+1) zp :=
          (margin_step L m z zp he).symm
        _ = 2*((2:Int)^N*u) := by rw [hu]
        _ = (2:Int)^(N+1)*u := by rw [Int.pow_succ']; ac_rfl

theorem run_zero_length_bound (L N m z : Nat)
    (hmargin:z+4≤L+m) (hr:RunZero L N m z) :
    (2:Nat)^N≤(margin L m z).natAbs := by
  have h := pow_dvd_margin L N m z hr
  have hd : (2:Nat)^N ∣ (margin L m z).natAbs := by
    have hcast := (Int.natAbs_dvd_natAbs).mpr h
    simpa [Int.natAbs_pow, Int.natAbs_natCast] using hcast
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr (by
      have hp:=margin_pos L m z hmargin
      omega)) hd

private theorem growth_two (N:Nat) : N < (2:Nat)^N := by
  induction N with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have hp : 0<(2:Nat)^n := Nat.pow_pos (by decide)
    omega

/-- From every scalar node satisfying margin four, a perpetual homogeneous
    depth-zero inverse ray is arithmetically impossible. -/
theorem no_infinite_zero_depth (L m z : Nat)
    (hmargin:z+4≤L+m)
    (hall:∀ N : Nat, RunZero L N m z) : False := by
  let N := (margin L m z).natAbs
  have hp := run_zero_length_bound L (N+1) m z hmargin (hall (N+1))
  have hg := growth_two (N+1)
  omega

#print axioms shadow_slack_four
#print axioms margin_step
#print axioms run_zero_length_bound
#print axioms no_infinite_zero_depth
end BB6.Agent13ZeroDepth
