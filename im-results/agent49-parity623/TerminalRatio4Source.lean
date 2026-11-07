import Agent49DrainLinearTerminalSource
import Agent49TerminalRatio4Arithmetic

/-!
Source-level composition of the authentic #623 root-ray bridge, the joint-mass
terminal output bound, and the integer cancellation lemmas.  The even-near
branch uses a sharper evaluator/drain joint-mass envelope than the earlier
componentwise estimate.
-/

namespace BB6.Agent49TerminalRatio4Source

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49DrainLinearTerminalSource
open BB6.Agent49JointMassSource
open BB6.Agent49TerminalRatio4Arithmetic

/-- An evalA result followed by a complete B-drain has total output mass at
most y+2*x+5+3*n when the evaluator's initial counter x is below 3^n. -/
theorem evalA_drain_joint_mass (n x y p q r aa dd : Nat)
    (hpos : 0<x)
    (hx : x<3^n)
    (hEval : evalA (y+1-x) x (2*x+5) = some (p,q,r))
    (hDrain : drainB p q r = some (.D aa dd)) :
    aa+dd ≤ y+2*x+5+3*n := by
  by_cases hq : q=0
  · have hEval0 : evalA (y+1-x) x (2*x+5) = some (p,0,r) := by
      simpa [hq] using hEval
    have hzero := evalA_joint_zero n (y+1-x) x (2*x+5) p r hx hEval0
    have hn : 1≤n := by
      by_contra h
      have hn0 : n=0 := by omega
      subst n
      simp at hx
      omega
    have hrec : some (HighLevelState.D p r) = some (HighLevelState.D aa dd) := by
      simpa [drainB, hq] using hDrain
    have hstate : HighLevelState.D p r = HighLevelState.D aa dd := Option.some.inj hrec
    have hMass : aa+dd=p+r := by
      injection hstate with hp hd
      subst p
      subst r
      rfl
    have hzero' : aa+dd≤y+2*x+n+7 := by
      rw [hMass]
      omega
    omega
  · have hqpos : 0<q := by omega
    obtain ⟨r0,s,hrs,hrpos,hqsmall,hpot⟩ :=
      evalA_joint_positive n (y+1-x) x (2*x+5) p q r hx hEval hqpos
    have hpot' : p+r+3*q≤y+6+2*x+r0 := by
      have := hpot
      omega
    have hrecMass := drainB_joint_mass s p q r aa dd hqsmall hDrain
    calc
      aa+dd ≤ p+r+3*q+3*s+1 := hrecMass
      _ ≤ y+7+2*x+r0+3*s := by omega
      _ ≤ y+2*x+5+3*n := by omega

/-- Odd far-left predecessor: the terminal ratio-four window is source-certified. -/
theorem oddFar_terminal_ratio4_source
    (x y n K aa dd cR cL : Nat)
    (hxy : y+5≤x)
    (hcR : cR=1 ∨ cR=2)
    (hcL : cL=5 ∨ cL=9)
    (hDrain : drainB (x-y-5) (y+3) 5 = some (.D aa dd))
    (hb : y+3<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd)=none)
    (hK : 2*(x+2*y+10+3*n)+5<3^K) :
    4*y≤x+K+5*n+29 ∧ x≤4*y+K+5*n+29 := by
  have hK' : 2*((x-y-5)+5+3*(y+3)+3*n+1)+5<3^K := by omega
  have hbal := terminal_output_balance_joint (x-y-5) (y+3) 5 n K aa dd
    hDrain hb he hhalt hK'
  obtain ⟨hBridgeR,hBridgeL⟩ := oddFarGap x y aa dd n cR cL hxy hcR hcL hDrain hb
  obtain ⟨hRlo,hRhi⟩ := hBridgeR
  obtain ⟨hLlo,hLhi⟩ := hBridgeL
  have hratio := far_ratio4_gap_bound x y aa dd cR cL K
    (8*n+39) (17*n+79) hbal.1 hbal.2 hcR hcL
    (by simpa [gapR] using hRlo)
    (by simpa [gapR] using hRhi)
    (by simpa [gapL] using hLlo)
    (by simpa [gapL] using hLhi)
  omega

/-- Even far-left predecessor: the terminal ratio-four window is source-certified. -/
theorem evenFar_terminal_ratio4_source
    (x y n K aa dd cR cL : Nat)
    (hxy : y+3≤x)
    (hcR : cR=1 ∨ cR=2)
    (hcL : cL=5 ∨ cL=9)
    (hDrain : drainB (x-y-2) (y+2) 2 = some (.D aa dd))
    (hb : y+2<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd)=none)
    (hK : 2*(x+2*y+7+3*n)+5<3^K) :
    4*y≤x+K+5*n+20 ∧ x≤4*y+K+5*n+20 := by
  have hK' : 2*((x-y-2)+2+3*(y+2)+3*n+1)+5<3^K := by omega
  have hbal := terminal_output_balance_joint (x-y-2) (y+2) 2 n K aa dd
    hDrain hb he hhalt hK'
  obtain ⟨hBridgeR,hBridgeL⟩ := evenFarGap x y aa dd n cR cL hxy hcR hcL hDrain hb
  obtain ⟨hRlo,hRhi⟩ := hBridgeR
  obtain ⟨hLlo,hLhi⟩ := hBridgeL
  have hratio := far_ratio4_gap_bound x y aa dd cR cL K
    (8*n+21) (17*n+52) hbal.1 hbal.2 hcR hcL
    (by simpa [gapR] using hRlo)
    (by simpa [gapR] using hRhi)
    (by simpa [gapL] using hLlo)
    (by simpa [gapL] using hLhi)
  omega

/-- Odd near-right predecessor: the terminal ratio-four window is source-certified. -/
theorem oddNear_terminal_ratio4_source
    (x y n K aa dd cR cL : Nat)
    (hpos : 0<x)
    (hxy : x≤y+4)
    (hcR : cR=1 ∨ cR=2)
    (hcL : cL=5 ∨ cL=9)
    (hDrain : drainB (y+4-x) (x-1) 3 = some (.D aa dd))
    (hb : x-1<3^n)
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd)=none)
    (hK : 2*(y+2*x+5+3*n)+5<3^K) :
    4*x≤y+K+5*n+12 ∧ y≤4*x+K+5*n+12 := by
  have hK' : 2*((y+4-x)+3+3*(x-1)+3*n+1)+5<3^K := by omega
  have hbal := terminal_output_balance_joint (y+4-x) (x-1) 3 n K aa dd
    hDrain hb he hhalt hK'
  obtain ⟨hBridgeR,hBridgeL⟩ := oddNearGap x y aa dd n cR cL hpos hxy hcR hcL hDrain hb
  obtain ⟨hRlo,hRhi⟩ := hBridgeR
  obtain ⟨hLlo,hLhi⟩ := hBridgeL
  have hratio := near_ratio4_gap_bound x y aa dd cR cL K
    (8*n+18) (17*n+14) hbal.1 hbal.2 hcR hcL
    (by simpa [gapR] using hRlo)
    (by simpa [gapR] using hRhi)
    (by simpa [gapL] using hLlo)
    (by simpa [gapL] using hLhi)
  omega

/-- Even near-right predecessor: compose the evaluator and drain joint-mass
bounds before applying the source terminal-output balance. -/
theorem evenNear_terminal_ratio4_source
    (x y p q r n K aa dd cR cL : Nat)
    (hpos : 0<x)
    (hxy : x≤y)
    (hx : x<3^n)
    (hcR : cR=1 ∨ cR=2)
    (hcL : cL=5 ∨ cL=9)
    (hEval : evalA (y+1-x) x (2*x+5) = some (p,q,r))
    (hDrain : drainB p q r = some (.D aa dd))
    (he : aa%2=0)
    (hhalt : highLevelNext (.D aa dd)=none)
    (hK : 2*(y+5+3*n)+5<3^K) :
    4*x≤y+K+8*n+17 ∧ y≤4*x+K+8*n+17 := by
  have hmass := evalA_drain_joint_mass n x y p q r aa dd hpos hx hEval hDrain
  have hbal := terminal_output_balance_of_mass aa dd K (y+2*x+5+3*n) hmass hK he hhalt
  obtain ⟨hBridgeR,hBridgeL⟩ := evenNearGap x y p q r aa dd n cR cL
    hpos hxy hx hcR hcL hEval hDrain
  obtain ⟨hRlo,hRhi⟩ := hBridgeR
  obtain ⟨hLlo,hLhi⟩ := hBridgeL
  have hratio := near_ratio4_gap_bound x y aa dd cR cL K
    (14*n+12) (26*n+46) hbal.1 hbal.2 hcR hcL
    (by simpa [gapR] using hRlo)
    (by simpa [gapR] using hRhi)
    (by simpa [gapL] using hLlo)
    (by simpa [gapL] using hLhi)
  omega

#print axioms evalA_drain_joint_mass
#print axioms oddFar_terminal_ratio4_source
#print axioms evenFar_terminal_ratio4_source
#print axioms oddNear_terminal_ratio4_source
#print axioms evenNear_terminal_ratio4_source

end BB6.Agent49TerminalRatio4Source
