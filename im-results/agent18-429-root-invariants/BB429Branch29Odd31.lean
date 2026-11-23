import BB429Branch29Mod128
import Lean.Elab.Tactic.Omega

/-!
# Elimination of the full odd q=31(mod64) #429 reset cylinder

The 29(mod32) odd-reset line's q=31(mod64) family admits no actual
blank-root path. The first odd ancestors are forced, and their only
two possible final inverse paths contradict the rooted (3 mod8, odd)
row or the all-time BB429Mod8.Allowed invariant. No time horizon.
-/

namespace BB429Branch29Odd31
open BB429Reset31
set_option maxHeartbeats 16000000
set_option maxRecDepth 30000

theorem no_q_31_mod64 (q : Nat) (hq : 21≤q)
    (hq64 : q%64=31) :
    ¬Reach (32*q+29) (64*q+55) := by
  intro hroot
  let r := q/16
  have hqeq : q=16*r+15 := by dsimp [r]; omega
  have hrmod : r%4=1 := by omega
  have h5 :=
    BB429Branch29.to_q_minus_two q hq
      (BB429Branch29.first_three q hroot)
  have hx5 : q-2=16*r+13 := by omega
  have hy5 : 126*q+102=2016*r+1992 := by omega
  rw [hx5,hy5] at h5
  obtain ⟨x1,y1,hp1,hs1⟩ :=
    pred (16*r+13) (2016*r+1992) (by omega) h5
  rcases BB429Reset31.odd_inverse x1 y1
      (16*r+13) (2016*r+1992)
      (by omega) (by omega) hs1 with hF | hS
  · obtain ⟨h1a,h1b⟩ := hF
    have hx1 : x1=8*r+5 := by omega
    have hy1 : y1=2032*r+2005 := by omega
    rw [hx1,hy1] at hp1
    obtain ⟨x2,y2,hp2,hs2⟩ :=
      pred (8*r+5) (2032*r+2005) (by omega) hp1
    obtain ⟨h2a,h2b⟩ :=
      BB429OddResetGate.incoming_odd_second x2 y2
        (8*r+5) (2032*r+2005) hs2 (by omega)
    have hx2 : x2=4*r+1 := by omega
    have hy2 : y2=2040*r+2010 := by omega
    rw [hx2,hy2] at hp2
    obtain ⟨x3,y3,hp3,hs3⟩ :=
      pred (4*r+1) (2040*r+2010) (by omega) hp2
    rcases BB429Branch29Mod16.odd_inverse_except_eleven
        x3 y3 (4*r+1) (2040*r+2010)
        (by omega) (by omega) (by omega) hs3 with hF3 | hS3
    · obtain ⟨h3a,h3b⟩ := hF3
      have hx3 : x3=2*r-1 := by omega
      have hy3 : y3=2044*r+2011 := by omega
      rw [hx3,hy3] at hp3
      obtain ⟨x4,y4,hp4,hs4⟩ :=
        pred (2*r-1) (2044*r+2011) (by omega) hp3
      obtain ⟨h4a,h4b⟩ :=
        BB429OddResetGate.incoming_odd_second x4 y4
          (2*r-1) (2044*r+2011) hs4 (by omega)
      have hx4 : x4=r-2 := by omega
      have hy4 : y4=2046*r+2010 := by omega
      rw [hx4,hy4] at hp4
      obtain ⟨n,hn⟩ := hp4
      have hall :=
        BB429Mod8.all_blank_returns_allowed n
          (r-2) (2046*r+2010) hn
      unfold BB429Mod8.Allowed at hall
      omega
    · obtain ⟨h3a,h3b,_⟩ := hS3
      have hx3 : x3=514*r+497 := by omega
      have hy3 : y3=1020*r+1007 := by omega
      rw [hx3,hy3] at hp3
      have hseven :=
        BB429Branch29Mod128.rooted_three_odd_seven
          (514*r+497) (1020*r+1007)
          (by omega) (by omega) (by omega) hp3
      omega
  · obtain ⟨_,_,hmod⟩ := hS
    omega

/-- Uniform source-root 29(mod32) odd reset restriction:
after removing the entire q=31(mod64) family, only seven
classes mod64 survive. -/
theorem rooted_29_q_seven_mod64 (q : Nat) (hq : 21≤q)
    (hroot : Reach (32*q+29) (64*q+55)) :
    q%64=2 ∨ q%64=10 ∨ q%64=15 ∨ q%64=18 ∨
    q%64=47 ∨ q%64=58 ∨ q%64=63 := by
  have h64 := BB429Branch29Mod64.rooted_29_q_eight_mod64 q hq hroot
  have h31 : q%64≠31 := by
    intro hh
    exact no_q_31_mod64 q hq hh hroot
  omega

/-- The currently surviving 12 residue classes modulo128.
The reduction is uniform and source-rooted, not a finite scan. -/
theorem rooted_29_q_twelve_mod128 (q : Nat) (hq : 21≤q)
    (hroot : Reach (32*q+29) (64*q+55)) :
    q%128=2 ∨ q%128=10 ∨ q%128=15 ∨ q%128=47 ∨
    q%128=58 ∨ q%128=63 ∨ q%128=74 ∨ q%128=79 ∨
    q%128=82 ∨ q%128=111 ∨ q%128=122 ∨ q%128=127 := by
  have h128 := BB429Branch29Mod128.rooted_29_q_fourteen_mod128 q hq hroot
  have h31 : q%64≠31 := by
    intro hh
    exact no_q_31_mod64 q hq hh hroot
  omega

#print axioms no_q_31_mod64
#print axioms rooted_29_q_seven_mod64
#print axioms rooted_29_q_twelve_mod128
end BB429Branch29Odd31
