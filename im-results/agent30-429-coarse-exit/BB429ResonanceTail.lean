import BB429ResonanceErrorBand
import BB429LowBoundary

namespace BB429.CoarseExit

open BB429.LowReturnBand

private theorem tail_stepF (u w : Nat) (h : 2*u+3 ≤ w) :
    next (u,w) = some (2*u+3,w-2*u-3) := by
  simp [next,h]

private theorem tail_stepOo (u w : Nat) (h : w+1 < 2*u)
    (hw : w%2=1) (hd : 3 ≤ u-w/2) (he : (u-w/2)%2=1) :
    next (u,w) = some (u-w/2+3,2*w) := by
  have h0 : ¬ w ≥ 2*u+3 := by omega
  have h1 : w ≠ 2*u+2 := by omega
  have h2 : w ≠ 2*u+1 := by omega
  have h3 : w ≠ 2*u := by omega
  have h4 : w%2 ≠ 0 := by omega
  have h5 : u-w/2 ≠ 1 := by omega
  have h6 : u-w/2 ≠ 2 := by omega
  have h7 : (u-w/2)%2 ≠ 0 := by omega
  simp [next,h0,h1,h2,h3,h4,h5,h6,h7]

private theorem tail_stepEe (u w : Nat) (h : w < 2*u)
    (hw : w%2=0) (hd : 2 ≤ u-w/2) (he : (u-w/2)%2=0) :
    next (u,w) = some (11,2*u+w-2) := by
  have h0 : ¬ w ≥ 2*u+3 := by omega
  have h1 : w ≠ 2*u+2 := by omega
  have h2 : w ≠ 2*u+1 := by omega
  have h3 : w ≠ 2*u := by omega
  have h5 : u-w/2 ≠ 1 := by omega
  simp [next,h0,h1,h2,h3,hw,h5,he]

/-- A false-phase resonant state rotates in two accelerator moves into the
    canonical Oe/F/Oo/F low-side coordinate system. -/
theorem phase_false_rotate (u d : Nat)
    (he : d%2=0) (hmod : (u-d)%4=1) (hu : d+17≤u) :
    run 2 (phase u d)=some (phase (u-d-2) (4*d+16)) := by
  have hw : (u+12+d)%2=1 := by omega
  have hg : 3≤u-(u+12+d)/2 := by omega
  have hgo : (u-(u+12+d)/2)%2=1 := by omega
  have h1 : next (phase u d)=some ((u-d-5)/2,2*u+24+2*d) := by
    unfold phase
    rw [tail_stepOo _ _ (by omega) hw hg hgo]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h2 : next ((u-d-5)/2,2*u+24+2*d)=
      some (phase (u-d-2) (4*d+16)) := by
    rw [tail_stepF _ _ (by omega)]
    unfold phase
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  simp [run,h1,h2]

/-- Once a canonical low phase has crossed below its geometric cycle guard,
    the narrow band d+7 ≤ 5u and u ≤ d+9 returns immediately by F,E-even. -/
theorem phase_direct_return (u d : Nat)
    (he : d%2=0) (hp : (u+1)%4=d%4)
    (hlo : d+7≤5*u) (hhi : u≤d+9) :
    run 2 (phase u d)=some (11,3*u+d+13) := by
  have h1 : next (phase u d)=some (2*u+3,d+9-u) := by
    unfold phase
    rw [tail_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have hz : (d+9-u)%2=0 := by omega
  have hgap : 2≤(2*u+3)-(d+9-u)/2 := by omega
  have hge : ((2*u+3)-(d+9-u)/2)%2=0 := by omega
  have h2 : next (2*u+3,d+9-u)=some (11,3*u+d+13) := by
    rw [tail_stepEe _ _ (by omega) hz hgap hge]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  simp [run,h1,h2]

/-- Complete geometric evacuation lemma.  C is the cycle invariant
    3u₀+d₀+24J and D=d₀*16^J.  The three displayed scalar inequalities
    are sufficient for J exact Oe,F,Oo,F cycles followed by F,E-even.
    No branch-word search remains. -/
theorem phase_cycles_direct_return
    (J u0 d0 X C : Nat)
    (hJ : 1≤J)
    (hd : 6≤d0) (he : d0%2=0)
    (hp : (u0+1)%4=d0%4)
    (hC : C=3*u0+d0+24*J)
    (hX : 2≤X)
    (hDhi : d0*16^J≤36*X)
    (hClo : 72*X≤C)
    (hChi : C≤4*(d0*16^J)+27)
    (hClow : 8*(d0*16^J)+21≤5*C) :
    run (4*J+2) (phase u0 d0)=some
      (11, C-(d0*16^J)+d0*16^J+13) := by
  let D := d0*16^J
  have hD : D≤36*X := by simpa [D] using hDhi
  have hCD : D≤C := by omega
  have hmod16 : 16^J%3=1 := by
    rw [Nat.pow_mod]
    simp
  have hmod : (C-D)%3=0 := by
    have hh := congrArg (fun n : Nat => n%3) hC
    dsimp [D]
    rw [Nat.sub_mod]
    omega
  let u := (C-D)/3
  have hcoordU : 3*u+D=C := by
    have hdiv := Nat.mod_add_div (C-D) 3
    dsimp [u]
    omega
  have hu15 : 15≤u := by
    dsimp [u]
    omega
  have hcoord : 3*u0+d0+24*J=3*u+d0*16^J := by
    rw [←hC]
    simpa [D] using hcoordU.symm
  obtain ⟨hcycles,hphase,heven⟩ :=
    BB429.LowBoundary.cycles_to_boundary J u0 d0 u hd he hp hcoord hu15
  have hhi : u≤D+9 := by omega
  have hlo : D+7≤5*u := by omega
  have hret := phase_direct_return u D heven hphase hlo hhi
  rw [show 4*J+2=4*J+2 by rfl,run_add,hcycles]
  simp only [Option.bind_some]
  rw [hret]
  simp only [Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · rw [hcoordU]
    omega

#print axioms phase_false_rotate
#print axioms phase_direct_return
#print axioms phase_cycles_direct_return

end BB429.CoarseExit
