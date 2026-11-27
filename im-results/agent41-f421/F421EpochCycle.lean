import F421EpochWords
import F421PrimaryEvents

namespace BB6Coverage.Agent41F421.EpochWords
open Agent31Pump
open Regular (P Q Z R)
open F421TertiaryGuard (drain QBudget Marked8 Survives8)

abbrev guarded := MergedDrain.guarded

theorem drainReach (a b : Nat) (cs ds : List PC) (H r : Nat) (U : List Bool)
    (hb : 2≤b) (hg : guarded 0 cs) (he : drain 0 0 cs=(ds,H,r)) :
    reaches H (rep P a++rep Q b++pw true cs++U)
      (rep P (a+2*H)++rep Q (b+H+r)++pw false ds++U) := by
  have h := MergedDrain.mergedDrain cs a b U hb hg
  rw [he] at h
  exact h

/-- The entire three-drain positive tertiary transition at the source-machine level. -/
theorem cycleSource (a b x y : Nat) (cs as bs ds : List PC) (cB : PC)
    (lo hi : List TC) (c : TC) (U : List Bool) (A B C rA rB rC : Nat)
    (ha : 1≤a) (hb : 2≤b) (hx : 1≤x) (hy : 2≤y) (hv : valid cs)
    (hlo : tailValid lo) (hclear : clear lo) (hc : c.f=true) (hz : 1≤c.z)
    (gA : guarded 0 (crossFar b x cs))
    (eA : drain 0 0 (crossFar b x cs)=(as,A,rA)) (vA : valid as)
    (gB : guarded 0 (dec as)) (eB : drain 0 0 (dec as)=(cB::bs,B,rB))
    (vB : valid (cB::bs))
    (gC : guarded 0 (crossFar (a+1+A+rA+1+B+rB) cB.p bs))
    (eC : drain 0 0 (crossFar (a+1+A+rA+1+B+rB) cB.p bs)=(ds,C,rC)) :
    reaches (1+A+1+B+1+C) (body a b x y cs (lo++c::hi) U)
      (body (1+2*C) (1+2*A+2+2*B+1+C+rC) cB.q (y-1) ds (touch lo++target c::hi) U) := by
  have h1 := firstCross a b x y cs (lo++c::hi) U hb hx (by omega) hv
  have h2 := drainReach 1 (a+1) (crossFar b x cs) as A rA
    (P++rep Q y++shifted (lo++c::hi)++[true]++U) (by omega) gA eA
  have h3 := carryTertiary (1+2*A) (a+1+A+rA) y as lo hi c U (by omega) hy vA hlo hclear hc hz
  have h4 := drainReach (1+2*A+2) (a+1+A+rA+1) (dec as) (cB::bs) B rB
    (Z++rep Q y++shifted (touch lo++target c::hi)++[true]++U) (by omega) gB eB
  have hcB := vB cB (by simp)
  have h5 := thirdCross (1+2*A+2+2*B) (a+1+A+rA+1+B+rB) y cB bs (touch lo++target c::hi) U
    (by omega) (by omega) hcB.1 (by omega) (fun z hz => vB z (by simp [hz]))
  have h6 := drainReach 1 (1+2*A+2+2*B+1) _ ds C rC
    (rep P cB.q++Q++rep P (y-1)++R++tail (touch lo++target c::hi) U) (by omega) gC eC
  simp only [rep, List.nil_append, List.append_nil, List.append_assoc] at h1 h2 h3 h4 h5 h6
  -- rep P 1 is definitional P; preserve symbolic repetitions elsewhere.
  unfold body at h1 ⊢
  simp only [List.append_assoc] at h1 ⊢
  exact reachesTrans (reachesTrans (reachesTrans (reachesTrans (reachesTrans h1 h2) h3) h4) h5) h6

#print axioms cycleSource
end BB6Coverage.Agent41F421.EpochWords
