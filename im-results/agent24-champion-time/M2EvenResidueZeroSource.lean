import S1Encoder
import CountedSweep
import M2EvenResidueZeroFrames
import CountedQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Source-side initial sweep and setup-window proof for m=2, n=8*k

The first 9*a+6 transitions are the counted left sweep over d1^a and
the first two bits of markerWord 2.  Its left exterior exposes the exact
14-cell finite setup window, independently of the surrounding tape.
-/

namespace BB6Coverage.Agent24M2EvenSource

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8M2EvenResidueZero
open BB6Coverage.Agent24LBinDecHRun
open BB6Coverage.Agent24M2EvenFrames
open BB6Coverage.Agent6Q4Prefix

set_option maxHeartbeats 1000000

/-- sideBit distributes over list append at the exact list boundary. -/
private theorem sideBit_append (xs ys : List Bool) (i : Nat) :
    sideBit (xs ++ ys) i =
      if i < xs.length then sideBit xs i
      else sideBit ys (i-xs.length) := by
  induction xs generalizing i with
  | nil => simp [sideBit]
  | cons x xs ih =>
      cases i with
      | zero => simp [sideBit]
      | succ i => simp [sideBit,ih]

/-- Every cell in a repeated d1 block is one. -/
private theorem sideBit_d1pow (n i : Nat) (hi : i<3*n) :
    sideBit (d1pow n) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      change sideBit (d1 ++ d1pow n) i = true
      rw [sideBit_append]
      by_cases hi3 : i<3
      · have hcases : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases hcases with h|h|h <;> subst i <;> simp [d1,sideBit]
      · have hi' : i-3<3*n := by omega
        simp [hi3,d1,sideBit]
        exact ih (i-3) hi'

/-- The fourteen cells immediately beyond the first 3*a+2 input ones
are, in head-facing order, [0,1] ++ d0 ++ d1^3. -/
private theorem s1M2Setup_suffix (L k a : Nat)
    (hL : 3≤L) (hk : k<2^(L-3)) :
    ∀ i : Nat, i≤13 →
      sideBit (s1LeftFacing L (8*k) 2 a 0) (3*a+2+i) =
        sideBit ([false,true] ++ d0 ++ d1pow 3) i := by
  have hmul := binDec_mulpow2 (L-3) k 3 hk
  have hlen : L-3+3=L := by omega
  have hnum : k*2^3=8*k := by
    rw [show (2:Nat)^3 = 8 by decide]
    exact Nat.mul_comm _ _
  have hbin : binDec L (8*k) =
      d1pow 3 ++ binDec (L-3) k := by
    simpa [hlen,hnum] using hmul
  have hleft :
      s1LeftFacing L (8*k) 2 a 0 =
        d1pow a ++ markerWord 2 ++ d0 ++ d1pow 3 ++
          binDec (L-3) k ++ lh := by
    simp [s1LeftFacing,binDec_zero,hbin,List.append_assoc]
  intro i hi
  let R : List Bool :=
    markerWord 2 ++ d0 ++ d1pow 3 ++ binDec (L-3) k ++ lh
  have hfirst :
      sideBit (d1pow a ++ R) (3*a+2+i) = sideBit R (2+i) := by
    rw [sideBit_append]
    rw [d1pow_length]
    have hnot : ¬ (3*a+2+i < 3*a) := by omega
    have hsub : 3*a+2+i-3*a = 2+i := by omega
    simp [hnot,hsub]
  have hsecond :
      sideBit R (2+i) = sideBit ([false,true] ++ d0 ++ d1pow 3) i := by
    have hcases :
        i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨
        i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 |
      h8 | h9 | h10 | h11 | h12 | h13 <;> subst i <;>
      simp [R,sideBit_append,markerWord,d0,d1pow,d1,sideBit,d1pow_length]
  rw [hleft]
  simpa [R] using hfirst.trans hsecond

/-- The setup's marked cells encode the same fourteen head-facing bits. -/
private theorem m2SetupBits_marker (i : Nat) (hi : i≤13) :
    sideBit ([false,true] ++ d0 ++ d1pow 3) i =
      decide (-(i:Int) ∈ m2ZeroSetupStart.marked) := by
  have hcases :
      i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨
      i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 |
    h8 | h9 | h10 | h11 | h12 | h13 <;> subst i <;>
    simp [sideBit,d0,d1pow,d1,m2ZeroSetupStart]

/-- The first 3*a+2 cells read by the D-state left sweep are all ones:
the unary d1^a followed by the first two ones of markerWord 2. -/
theorem s1M2InitialLeftOnes (L k a b : Nat) (h : Int) :
    leftOnes (s1Config L (8*k) 2 a 0 b h).tape h (3*a+2) := by
  intro i hi
  have hcell := s1Config_left_cell L (8*k) 2 a 0 b h i
  have hleft :
      s1LeftFacing L (8*k) 2 a 0 =
        d1pow a ++ markerWord 2 ++ d0 ++ binDec L (8*k) ++ lh := by
    simp [s1LeftFacing,binDec_zero,List.append_assoc]
  rw [hleft] at hcell
  let R : List Bool := markerWord 2 ++ d0 ++ binDec L (8*k) ++ lh
  have hside : sideBit (d1pow a ++ R) i = true := by
    by_cases hiA : i<3*a
    · have hiLen : i < (d1pow a).length := by
        simpa [d1pow_length] using hiA
      rw [Agent6Q4Prefix.sideBit_append_left (d1pow a) R i hiLen]
      exact sideBit_d1pow a i hiA
    · have hcases : i = 3*a ∨ i = 3*a+1 := by omega
      rcases hcases with h | h
      · subst i
        rw [Agent6Q4Prefix.sideBit_append_right (d1pow a) R
          (3*a) (by simp [d1pow_length])]
        simp [R,markerWord,sideBit,d1pow_length]
      · subst i
        rw [Agent6Q4Prefix.sideBit_append_right (d1pow a) R
          (3*a+1) (by simp [d1pow_length])]
        simp [R,markerWord,sideBit,d1pow_length]
  rw [hcell]
  simpa [R,List.append_assoc] using hside

/-- The original S1 right stream begins with a blank cell. -/
theorem s1M2RightZero (L k a b : Nat) (h : Int) :
    (s1Config L (8*k) 2 a 0 b h).tape (h+1) = false := by
  have hc := s1Config_right_cell L (8*k) 2 a 0 b h 0
  simpa [s1PhysicalRight_source,sideBit] using hc

/-- The 14-cell setup input window is already present in the source S1
left stream after the first 3*a+2 ones.  The counted sweep itself preserves
this window because every one of its cells lies strictly to the left of
the sweep's final head. -/
theorem m2ZeroSetup_match_after_initial_sweep
    (L k a b : Nat) (h : Int)
    (hL : 3≤L) (hk : k<2^(L-3)) :
    ∀ x, m2ZeroSetupInside x = true →
      sweptLeft (3*a+2) (s1Config L (8*k) 2 a 0 b h).tape h
        (h-(3*a+2)+x) =
        decide (x ∈ m2ZeroSetupStart.marked) := by
  intro x hx
  have hxrange : -13≤x ∧ x≤0 := by
    simpa [m2ZeroSetupInside] using hx
  let i : Nat := (-x).toNat
  have hcast : (i:Int) = -x := by
    dsimp [i]
    exact Int.toNat_of_nonneg (by omega)
  have hi : i≤13 := by omega
  have hcoord : h-(3*a+2)+x = h-((3*a+2+i):Int) := by omega
  have hpres := Agent24LBinDecHRun.sweptLeft_preserves_left (3*a+2)
    (s1Config L (8*k) 2 a 0 b h).tape h
    (h-(3*a+2)+x) (by omega)
  rw [hpres,hcoord]
  have hcell := s1Config_left_cell L (8*k) 2 a 0 b h (3*a+2+i)
  have hcellCoord : h-((3*a+2+i:Nat):Int) =
      h-(3*(a:Int)+2+(i:Int)) := by omega
  rw [hcellCoord] at hcell
  rw [hcell]
  have hsuffix := s1M2Setup_suffix L k a hL hk i hi
  have hmarker := m2SetupBits_marker i hi
  rw [hsuffix,hmarker]
  have htarget : -(i:Int)=x := by omega
  simpa [htarget]

/-- Exact original-TM2 initial left sweep for every valid source
m=2, n=8*k configuration. -/
theorem m2ZeroInitialSweep (L k a b : Nat) (h : Int)
    (hL : 3≤L) (hk : k<2^(L-3)) :
    run tm2 (9*a+6) (s1Config L (8*k) 2 a 0 b h) =
      some ⟨3,h-(3*a+2),
        sweptLeft (3*a+2) (s1Config L (8*k) 2 a 0 b h).tape h⟩ := by
  have hon := s1M2InitialLeftOnes L k a b h
  have hr := s1M2RightZero L k a b h
  have hs := counted_left_sweep (3*a+2)
    (s1Config L (8*k) 2 a 0 b h).tape h hon hr
  have hnum : 3*(3*a+2)=9*a+6 := by omega
  change run tm2 (9*a+6) ⟨3,h,(s1Config L (8*k) 2 a 0 b h).tape⟩ =
    some ⟨3,h-(3*a+2),sweptLeft (3*a+2) (s1Config L (8*k) 2 a 0 b h).tape h⟩
  have hcoord : ((3*a+2:Nat):Int) = 3*(a:Int)+2 := by omega
  simpa only [hnum,hcoord] using hs

/-- Compose the source-level 9*a+6 left sweep with the framed 44-step
setup.  This is the first two phases of the m=2, n=8*k candidate. -/
theorem m2ZeroInitialSweep_Setup (L k a b : Nat) (h : Int)
    (hL : 3≤L) (hk : k<2^(L-3)) :
    run tm2 (9*a+6+44) (s1Config L (8*k) 2 a 0 b h) =
      some (Agent8Rst1Prime.frameAt
        (sweptLeft (3*a+2) (s1Config L (8*k) 2 a 0 b h).tape h)
        (h-(3*a+2)) m2ZeroSetupInside m2ZeroSetupEnd) := by
  let T : Int → Bool := (s1Config L (8*k) 2 a 0 b h).tape
  let hN : Int := h-(3*a+2)
  let T1 : Int → Bool := sweptLeft (3*a+2) T h
  have hfirst := m2ZeroInitialSweep L k a b h hL hk
  have hmatch := m2ZeroSetup_match_after_initial_sweep L k a b h hL hk
  have hsetup := m2ZeroSetup_at T1 hN hmatch
  have hfirst' :
      run tm2 (9*a+6) (s1Config L (8*k) 2 a 0 b h) =
        some ⟨3,hN,T1⟩ := by
    simpa [T,hN,T1] using hfirst
  rw [run_append,hfirst']
  simp only [Option.bind_some]
  simpa [T1,hN] using hsetup

#print axioms s1M2InitialLeftOnes
#print axioms s1M2RightZero
#print axioms m2ZeroSetup_match_after_initial_sweep
#print axioms m2ZeroInitialSweep
#print axioms m2ZeroInitialSweep_Setup

end BB6Coverage.Agent24M2EvenSource
