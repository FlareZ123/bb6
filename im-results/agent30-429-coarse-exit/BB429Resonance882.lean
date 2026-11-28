import BB429CoarseExitExtended

namespace BB429.CoarseExit

set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

open BB429.LowReturnBand

private theorem r882_stepF (u w : Nat) (h : 2*u+3 ≤ w) :
    next (u,w) = some (2*u+3,w-2*u-3) := by
  simp [next,h]

private theorem r882_stepOe (u w : Nat) (h : w+1 < 2*u)
    (hw : w%2=1) (hd : 4 ≤ u-w/2) (he : (u-w/2)%2=0)
    (hw1 : 1 < w) :
    next (u,w) = some (u-w/2+7,2*w-4) := by
  have h0 : ¬ w ≥ 2*u+3 := by omega
  have h1 : w ≠ 2*u+2 := by omega
  have h2 : w ≠ 2*u+1 := by omega
  have h3 : w ≠ 2*u := by omega
  have h4 : w%2 ≠ 0 := by omega
  have h5 : u-w/2 ≠ 1 := by omega
  have h6 : u-w/2 ≠ 2 := by omega
  have h7 : w ≠ 1 := by omega
  simp [next,h0,h1,h2,h3,h4,h5,h6,he,h7]

private theorem r882_stepOo (u w : Nat) (h : w+1 < 2*u)
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

def d882PhaseU (j : Nat) : Nat := 98010*16^j+8*j+291

/-- Exact entry phase for the next positive first-burst Cantor resonance
    d=882 = 18+216*4.  The minimal scale is s=3. -/
theorem d882_phase (j : Nat) :
    run (8*j+15) (prepared (j+3) 882) =
      some (phase (d882PhaseU j) (882*16^j)) := by
  have hc :
      3*(24*16^(j+3)-3)+882+24*j =
        3*(d882PhaseU j)+882*16^j := by
    dsimp [d882PhaseU]
    rw [Nat.pow_add]
    rw [show 16^3=4096 by decide]
    grind +ring
  have hg : 5*(882*16^j)+7 ≤ d882PhaseU j := by
    dsimp [d882PhaseU]
    omega
  have h := prepared_phase 3 j 882 (d882PhaseU j)
    (by decide) (by decide) hc hg
  rw [show 8*j+15=4*(j+3)+3+4*j by omega]
  exact h.1

/-- The next Cantor resonance has a second exact cancellation tail.  Its
    branch word is
      Oe F Oo F Oe F Oo F F F Oo F Oe.
    After thirteen accelerator moves the entire leading 16^j term in the
    first counter has vanished. -/
theorem d882_tail (j : Nat) :
    run 13 (phase (d882PhaseU j) (882*16^j)) =
      some (196*j+7571,294912*16^j-368*j-14182) := by
  let P := 16^j
  have hP : 1 ≤ P := Nat.pow_pos (by decide)
  have hs : 16*j ≤ P := by simpa [P] using scale_ge j
  have hphase :
      phase (d882PhaseU j) (882*16^j) =
        (98010*P+8*j+291,98892*P+8*j+303) := by
    dsimp [phase,d882PhaseU,P]
    grind +ring
  rw [hphase]
  change run 13 (98010*P+8*j+291,98892*P+8*j+303) =
    some (196*j+7571,294912*P-368*j-14182)
  have h1 : next (98010*P+8*j+291,98892*P+8*j+303) =
      some (48564*P+4*j+147,197784*P+16*j+602) := by
    rw [r882_stepOe _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h2 : next (48564*P+4*j+147,197784*P+16*j+602) =
      some (97128*P+8*j+297,100656*P+8*j+305) := by
    rw [r882_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h3 : next (97128*P+8*j+297,100656*P+8*j+305) =
      some (46800*P+4*j+148,201312*P+16*j+610) := by
    rw [r882_stepOo _ _ (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h4 : next (46800*P+4*j+148,201312*P+16*j+610) =
      some (93600*P+8*j+299,107712*P+8*j+311) := by
    rw [r882_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h5 : next (93600*P+8*j+299,107712*P+8*j+311) =
      some (39744*P+4*j+151,215424*P+16*j+618) := by
    rw [r882_stepOe _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h6 : next (39744*P+4*j+151,215424*P+16*j+618) =
      some (79488*P+8*j+305,135936*P+8*j+313) := by
    rw [r882_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h7 : next (79488*P+8*j+305,135936*P+8*j+313) =
      some (11520*P+4*j+152,271872*P+16*j+626) := by
    rw [r882_stepOo _ _ (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h8 : next (11520*P+4*j+152,271872*P+16*j+626) =
      some (23040*P+8*j+307,248832*P+8*j+319) := by
    rw [r882_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h9 : next (23040*P+8*j+307,248832*P+8*j+319) =
      some (46080*P+16*j+617,202752*P-8*j-298) := by
    rw [r882_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h10 : next (46080*P+16*j+617,202752*P-8*j-298) =
      some (92160*P+32*j+1237,110592*P-40*j-1535) := by
    rw [r882_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h11 : next (92160*P+32*j+1237,110592*P-40*j-1535) =
      some (36864*P+52*j+2008,221184*P-80*j-3070) := by
    rw [r882_stepOo _ _ (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h12 : next (36864*P+52*j+2008,221184*P-80*j-3070) =
      some (73728*P+104*j+4019,147456*P-184*j-7089) := by
    rw [r882_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h13 : next (73728*P+104*j+4019,147456*P-184*j-7089) =
      some (196*j+7571,294912*P-368*j-14182) := by
    rw [r882_stepOe _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  simp [run,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13]

/-- Exact prepared-state transfer for d=882.  In m=j+3 notation the post
    state is reached at the same 8m+4 time that appears throughout the
    resonance hierarchy. -/
theorem d882_post (j : Nat) :
    run (8*j+28) (prepared (j+3) 882) =
      some (196*j+7571,294912*16^j-368*j-14182) := by
  rw [show 8*j+28=(8*j+15)+13 by omega,run_add,d882_phase]
  exact d882_tail j

theorem d882_post_Uc (j : Nat) :
    Uc (196*j+7571,294912*16^j-368*j-14182) =
      1176*j+45444 := by
  simp [Uc]
  omega

#print axioms d882_phase
#print axioms d882_tail
#print axioms d882_post
#print axioms d882_post_Uc

end BB429.CoarseExit
