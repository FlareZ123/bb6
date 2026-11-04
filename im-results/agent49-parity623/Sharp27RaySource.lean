import Agent8FirstSource
import Agent49LowStepSource

/-!
An infinite exact equality family for the conditional 27-unit two-return
theorem for Cryptids #623. Original source imports, no copied machine rules,
no sorry, and no axioms beyond Lean's standard foundations. Does not imply
blank-origin nonhalting.
-/

namespace BB6.Agent49SharpRaySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8FirstSource

/-- An exact source affine ray, strengthening the 20-unit d=7 gain lemma. -/
theorem ray_seven_exact (a : Nat) (ha : 23≤a) :
    highLevelNext (.D a 7)=some (.D (a-12) 39) := by
  let t := a-23
  have ht : 23+t=a := by dsimp [t]; omega
  have hr : 11+t=a-12 := by dsimp [t]; omega
  have hb : highLevelNext (.D 23 7)=some (.D 11 39) := by decide +kernel
  have hs := highLevel_far_odd_shift 23 7 t (by decide) (by decide)
  rw [hb] at hs
  simpa only [ht,hr,Option.map_some,liftFirstState] using hs

/-- An infinite exact sharp family: every even d>=24 starting with a=0
returns twice, gaining exactly 27 units of first+second counter mass. -/
theorem zero_even_ray_two_returns (d : Nat) (hd : d%2=0) (hl : 24≤d) :
    highLevelNext (.D 0 d)=some (.D d 7) ∧
    highLevelNext (.D d 7)=some (.D (d-12) 39) := by
  exact ⟨BB6.Agent49LowStepSource.low_zero_even d hd, ray_seven_exact d (by omega)⟩

theorem zero_even_ray_sharp (d : Nat) (hd : d%2=0) (hl : 24≤d) :
    ((d-12)+39)-(0+d)=27 := by omega

#print axioms ray_seven_exact
#print axioms zero_even_ray_two_returns
#print axioms zero_even_ray_sharp

/-- The second exact affine ray accounting for all large even-d equality
states with first counter 2. -/
theorem ray_nine_exact (a : Nat) (ha : 27≤a) :
    highLevelNext (.D a 9)=some (.D (a-12) 41) := by
  let t := a-27
  have ht : 27+t=a := by dsimp [t]; omega
  have hr : 15+t=a-12 := by dsimp [t]; omega
  have hb : highLevelNext (.D 27 9)=some (.D 15 41) := by decide +kernel
  have hs := highLevel_far_odd_shift 27 9 t (by decide) (by decide)
  rw [hb] at hs
  simpa only [ht,hr,Option.map_some,liftFirstState] using hs

/-- The third exact affine ray for all large odd-d equality states with
first counter 2. -/
theorem ray_ten_exact (a : Nat) (ha : 25≤a) :
    highLevelNext (.D a 10)=some (.D (a-10) 38) := by
  let t := a-25
  have ht : 25+t=a := by dsimp [t]; omega
  have hr : 15+t=a-10 := by dsimp [t]; omega
  have hb : highLevelNext (.D 25 10)=some (.D 15 38) := by decide +kernel
  have hs := highLevel_far_even_shift 25 10 t (by decide) (by decide)
  rw [hb] at hs
  simpa only [ht,hr,Option.map_some,liftFirstState] using hs

/-- A second source-exact infinite 27-unit family, a=2 and d even. -/
theorem two_even_ray_two_returns (d : Nat) (hd : d%2=0) (hl : 28≤d) :
    highLevelNext (.D 2 d)=some (.D d 9) ∧
    highLevelNext (.D d 9)=some (.D (d-12) 41) := by
  exact ⟨BB6.Agent49LowStepSource.low_two_even d hd (by omega),
    ray_nine_exact d (by omega)⟩

/-- A third source-exact infinite 27-unit family, a=2 and d odd. -/
theorem two_odd_ray_two_returns (d : Nat) (hd : d%2=1) (hl : 25≤d) :
    highLevelNext (.D 2 d)=some (.D (d+1) 10) ∧
    highLevelNext (.D (d+1) 10)=some (.D (d-9) 38) := by
  constructor
  · exact BB6.Agent49LowStepSource.low_two_odd d hd (by omega)
  · have hs := ray_ten_exact (d+1) (by omega)
    have heq : d+1-10=d-9 := by omega
    simpa only [heq] using hs

#print axioms ray_nine_exact
#print axioms ray_ten_exact
#print axioms two_even_ray_two_returns
#print axioms two_odd_ray_two_returns

end BB6.Agent49SharpRaySource
