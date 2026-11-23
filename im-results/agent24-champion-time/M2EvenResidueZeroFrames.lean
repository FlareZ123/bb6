import CountedRst1Prime
import M2EvenResidueZeroFinite
import CountedLBinDecHRun
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000

/-!
# Full-tape frame lifts for the finite m=2, n=8*k bridge kernels

The finite setup and postlude kernels are exact computations.  These
wrappers lift them to arbitrary infinite tapes using the existing
head-window frame theorem, with no assumption that the surrounding tape
is blank.
-/

namespace BB6Coverage.Agent24M2EvenFrames

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8M2EvenResidueZero
open BB6Coverage.Agent24LBinDecHRun

/-- Lift the fixed 44-step setup from its exact finite window to any
surrounding tape agreeing with the setup input on [-13,0]. -/
theorem m2ZeroSetup_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, m2ZeroSetupInside x = true →
      T (h+x) = decide (x ∈ m2ZeroSetupStart.marked)) :
    run tm2 44 ⟨3,h,T⟩ =
      some (frameAt T h m2ZeroSetupInside m2ZeroSetupEnd) := by
  exact bridgeAt T h m2ZeroSetupInside
    m2ZeroSetupStart m2ZeroSetupEnd 44 rfl
    m2ZeroSetup_exact m2ZeroSetup_heads hmatch

/-- Lift the fixed 14-step postlude from its exact finite window to any
surrounding tape agreeing with thirteen ones followed by a zero. -/
theorem m2ZeroPostlude_at (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, m2ZeroPostludeInside x = true →
      T (h+x) = decide (x ∈ m2ZeroPostludeStart.marked)) :
    run tm2 14 ⟨1,h,T⟩ =
      some (frameAt T h m2ZeroPostludeInside m2ZeroPostludeEnd) := by
  exact bridgeAt T h m2ZeroPostludeInside
    m2ZeroPostludeStart m2ZeroPostludeEnd 14 rfl
    m2ZeroPostlude_exact m2ZeroPostlude_heads hmatch

/-- The setup's output window is exactly zero at its left boundary and
one on the remaining thirteen cells. -/
theorem m2ZeroSetupAt_window (T : Int → Bool) (h : Int)
    (x : Int) (hx : m2ZeroSetupInside x = true) :
    (frameAt T h m2ZeroSetupInside m2ZeroSetupEnd).tape (h+x) =
      decide (x ∈ m2ZeroSetupEnd.marked) := by
  rw [frameAt_tape]
  have hcoord : h+x-h=x := by omega
  simp [hcoord,hx]

/-- The postlude's output window is exactly the finite word
00100100100101. -/
theorem m2ZeroPostludeAt_window (T : Int → Bool) (h : Int)
    (x : Int) (hx : m2ZeroPostludeInside x = true) :
    (frameAt T h m2ZeroPostludeInside m2ZeroPostludeEnd).tape (h+x) =
      decide (x ∈ m2ZeroPostludeEnd.marked) := by
  rw [frameAt_tape]
  have hcoord : h+x-h=x := by omega
  simp [hcoord,hx]


/-- The H-run preserves the setup's thirteen output ones and its
following zero, so its output is a valid input to the fixed postlude. -/
theorem m2ZeroPostlude_match_after_HRun (n : Nat) (T : Int → Bool)
    (hN : Int) (hr : T (hN+1) = false) :
    ∀ x, m2ZeroPostludeInside x = true →
      lbinDecHRunTape n
        (frameAt T hN m2ZeroSetupInside m2ZeroSetupEnd).tape
        (hN-14) (hN-12+x) =
        decide (x ∈ m2ZeroPostludeStart.marked) := by
  let Tsetup : Int → Bool :=
    (frameAt T hN m2ZeroSetupInside m2ZeroSetupEnd).tape
  let Thrun : Int → Bool := lbinDecHRunTape n Tsetup (hN-14)
  have hpres (y : Int) (hy : hN-12 ≤ y) : Thrun y = Tsetup y := by
    apply lbinDecHRunTape_preserves_right
    omega
  have hframeOutside : Tsetup (hN+1) = T (hN+1) := by
    change (frameAt T hN m2ZeroSetupInside m2ZeroSetupEnd).tape
      (hN+1) = T (hN+1)
    rw [frameAt_tape]
    have hrel : hN+1-hN=1 := by omega
    have hout : m2ZeroSetupInside 1 = false := by
      simp [m2ZeroSetupInside]
    simp [hrel,hout]
  intro x hx
  have hxrange : 0 ≤ x ∧ x ≤ 13 := by
    simpa [m2ZeroPostludeInside] using hx
  by_cases h13 : x=13
  · subst x
    have harg : hN-12+(13:Int)=hN+1 := by omega
    have hp : Thrun (hN+1)=Tsetup (hN+1) := by
      simpa [Thrun,harg] using hpres (hN+1) (by omega)
    have hzero : Thrun (hN+1)=false := by
      calc
        Thrun (hN+1) = Tsetup (hN+1) := hp
        _ = T (hN+1) := hframeOutside
        _ = false := hr
    have hnot : (13:Int) ∉ m2ZeroPostludeStart.marked := by
      simp [m2ZeroPostludeStart] <;> omega
    simpa [harg,hzero,hnot]
  · have hxle12 : x≤12 := by omega
    have hyinside : m2ZeroSetupInside (-12+x)=true := by
      simp [m2ZeroSetupInside]
      omega
    have hsetup := m2ZeroSetupAt_window T hN (-12+x) hyinside
    have hcoord : hN+(-12+x)=hN-12+x := by omega
    rw [hcoord] at hsetup
    change Tsetup (hN-12+x) =
      decide ((-12+x) ∈ m2ZeroSetupEnd.marked) at hsetup
    have hmemSetup : (-12+x) ∈ m2ZeroSetupEnd.marked := by
      simp [m2ZeroSetupEnd]
      omega
    have hsetupTrue : Tsetup (hN-12+x)=true := by
      rw [hsetup]
      simp [hmemSetup]
    have hfinalTrue : Thrun (hN-12+x)=true := by
      calc
        Thrun (hN-12+x) = Tsetup (hN-12+x) :=
          hpres (hN-12+x) (by omega)
        _ = true := hsetupTrue
    have hmemPost : x ∈ m2ZeroPostludeStart.marked := by
      change x ∈ (List.range 13).map Int.ofNat
      rw [List.mem_map]
      have hxnat : (x.toNat : Int)=x := Int.toNat_of_nonneg (by omega)
      have hxNat : x.toNat < 13 := by omega
      exact ⟨x.toNat, List.mem_range.mpr hxNat, hxnat⟩
    simpa [hfinalTrue,hmemPost]

/-- Compose the 44-step finite setup, the universal 12*n+4 H-run, and
the 14-step finite postlude on a full infinite tape. Only the setup's
finite input window and the H-run's left counter boundary are assumed;
the surrounding tape is preserved exactly. -/
theorem m2ZeroSetup_HRun_Postlude (n : Nat) (T : Int → Bool)
    (hN : Int)
    (hmatch : ∀ x, m2ZeroSetupInside x = true →
      T (hN+x) = decide (x ∈ m2ZeroSetupStart.marked))
    (hon : leftOnes T (hN-14) (3*n))
    (h0 : T (hN-14-(3*n:Int)) = false)
    (hm1 : T (hN-14-(3*n:Int)-1) = false)
    (hr : T (hN+1) = false) :
    run tm2 (44+(12*n+4)+14) ⟨3,hN,T⟩ =
      some (frameAt
        (lbinDecHRunTape n
          (frameAt T hN m2ZeroSetupInside m2ZeroSetupEnd).tape
          (hN-14))
        (hN-12) m2ZeroPostludeInside m2ZeroPostludeEnd) := by
  let Tsetup : Int → Bool :=
    (frameAt T hN m2ZeroSetupInside m2ZeroSetupEnd).tape
  let Thrun : Int → Bool := lbinDecHRunTape n Tsetup (hN-14)
  have houtside (x : Int) (hx : x-hN < -13) : Tsetup x = T x := by
    change (frameAt T hN m2ZeroSetupInside m2ZeroSetupEnd).tape x = T x
    rw [frameAt_tape]
    have hout : m2ZeroSetupInside (x-hN) = false := by
      simp [m2ZeroSetupInside]
      omega
    simp [hout]
  have honSetup : leftOnes Tsetup (hN-14) (3*n) := by
    intro i hi
    have hs := houtside (hN-14-(i:Int)) (by omega)
    rw [hs]
    exact hon i hi
  have h0Setup : Tsetup (hN-14-(3*n:Int)) = false := by
    exact (houtside (hN-14-(3*n:Int)) (by omega)).trans h0
  have hm1Setup : Tsetup (hN-14-(3*n:Int)-1) = false := by
    exact (houtside (hN-14-(3*n:Int)-1) (by omega)).trans hm1
  have hwindow := m2ZeroSetupAt_window T hN (-13) (by decide)
  have hcoord : hN+(-13)=hN-13 := by omega
  rw [hcoord] at hwindow
  change Tsetup (hN-13) =
    decide ((-13:Int) ∈ m2ZeroSetupEnd.marked) at hwindow
  have hnot : (-13:Int) ∉ m2ZeroSetupEnd.marked := by
    simp [m2ZeroSetupEnd]
  have hrSetup : Tsetup (hN-13)=false := by
    simpa [hnot] using hwindow
  have hsetup := m2ZeroSetup_at T hN hmatch
  have hsetupFrame :
      frameAt T hN m2ZeroSetupInside m2ZeroSetupEnd =
        ⟨3,hN-14,Tsetup⟩ := by
    apply config_ext
    · simp [frameAt,frame,embed,m2ZeroSetupEnd]
    · simp [frameAt,frame,shiftConfig,embed,m2ZeroSetupEnd]
      omega
    · rfl
  have hsetupRun :
      run tm2 44 ⟨3,hN,T⟩ = some ⟨3,hN-14,Tsetup⟩ := by
    rw [← hsetupFrame] at hsetup
    exact hsetup
  have hrSetup' : Tsetup (hN-14+1)=false := by
    have hcoord' : hN-14+1 = hN-13 := by omega
    simpa [hcoord'] using hrSetup
  have hrun := counted_LBinDec_HRun n Tsetup (hN-14)
    honSetup h0Setup hm1Setup hrSetup'
  have hrun' :
      run tm2 (12*n+4) ⟨3,hN-14,Tsetup⟩ =
        some ⟨1,hN-12,Thrun⟩ := by
    have hhead : hN-14+2 = hN-12 := by omega
    simpa [Thrun,hhead] using hrun
  have hpostmatch := m2ZeroPostlude_match_after_HRun n T hN hr
  have hpost := m2ZeroPostlude_at Thrun (hN-12) hpostmatch
  have hfirst :
      run tm2 (44+(12*n+4)) ⟨3,hN,T⟩ =
        some ⟨1,hN-12,Thrun⟩ := by
    rw [run_append,hsetupRun]
    simp only [Option.bind_some]
    exact hrun'
  rw [run_append,hfirst]
  simp only [Option.bind_some]
  exact hpost

#print axioms m2ZeroSetup_at
#print axioms m2ZeroPostlude_at
#print axioms m2ZeroSetupAt_window
#print axioms m2ZeroPostludeAt_window

end BB6Coverage.Agent24M2EvenFrames
