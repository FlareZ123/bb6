import Agent8FirstSource

/-!
Exact mass gain on five far-left arithmetic rays of the original Cryptids
#623 accelerator. Reuses the source-connected first-coordinate transport
theorem from Agent 8; the five finite base configurations are checked by
kernel reduction, and all input sizes follow by induction-free transport.
These are conditional one-step statements, not a halting decision.
-/

namespace BB6.Agent49FixedRaysSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8FirstSource

theorem odd_ray_gain (a0 d b0 e0 g a b e : Nat)
    (hd : d%2=1) (hfar : 2*d+8<a0)
    (hbase : highLevelNext (.D a0 d)=some (.D b0 e0))
    (hgain : a0+d+g≤b0+e0) (ha : a0≤a)
    (h : highLevelNext (.D a d)=some (.D b e)) :
    a+d+g≤b+e := by
  let t := a-a0
  have ht : a0+t=a := by dsimp [t]; omega
  have hs := highLevel_far_odd_shift a0 d t hd hfar
  rw [ht,hbase] at hs
  simp only [Option.map_some,liftFirstState] at hs
  rw [hs] at h
  cases h
  omega

theorem even_ray_gain (a0 d b0 e0 g a b e : Nat)
    (hd : d%2=0) (hfar : 2*d+4<a0)
    (hbase : highLevelNext (.D a0 d)=some (.D b0 e0))
    (hgain : a0+d+g≤b0+e0) (ha : a0≤a)
    (h : highLevelNext (.D a d)=some (.D b e)) :
    a+d+g≤b+e := by
  let t := a-a0
  have ht : a0+t=a := by dsimp [t]; omega
  have hs := highLevel_far_even_shift a0 d t hd hfar
  rw [ht,hbase] at hs
  simp only [Option.map_some,liftFirstState] at hs
  rw [hs] at h
  cases h
  omega

/-- Every sufficiently far-left d=7 state gains at least 20 mass. -/
theorem ray_7_gain20 (a b e : Nat) (ha : 23≤a)
    (h : highLevelNext (.D a 7)=some (.D b e)) :
    a+7+20≤b+e :=
  odd_ray_gain 23 7 11 39 20 a b e
    (by decide) (by decide) (by decide +kernel) (by decide) ha h

theorem ray_9_gain20 (a b e : Nat) (ha : 27≤a)
    (h : highLevelNext (.D a 9)=some (.D b e)) :
    a+9+20≤b+e :=
  odd_ray_gain 27 9 15 41 20 a b e
    (by decide) (by decide) (by decide +kernel) (by decide) ha h

theorem ray_10_gain18 (a b e : Nat) (ha : 25≤a)
    (h : highLevelNext (.D a 10)=some (.D b e)) :
    a+10+18≤b+e :=
  even_ray_gain 25 10 15 38 18 a b e
    (by decide) (by decide) (by decide +kernel) (by decide) ha h

theorem ray_12_gain24 (a b e : Nat) (ha : 29≤a)
    (h : highLevelNext (.D a 12)=some (.D b e)) :
    a+12+24≤b+e :=
  even_ray_gain 29 12 11 54 24 a b e
    (by decide) (by decide) (by decide +kernel) (by decide) ha h

theorem ray_14_gain28 (a b e : Nat) (ha : 33≤a)
    (h : highLevelNext (.D a 14)=some (.D b e)) :
    a+14+28≤b+e :=
  even_ray_gain 33 14 13 62 28 a b e
    (by decide) (by decide) (by decide +kernel) (by decide) ha h

#print axioms ray_7_gain20
#print axioms ray_9_gain20
#print axioms ray_10_gain18
#print axioms ray_12_gain24
#print axioms ray_14_gain28
end BB6.Agent49FixedRaysSource
