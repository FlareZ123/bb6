import BB429Resonance

namespace BB429.CoarseExit

open BB429.LowReturnBand
private theorem r234_stepF (u w : Nat) (h : 2*u+3 ≤ w) :
    next (u,w) = some (2*u+3,w-2*u-3) := by
  simp [next,h]

private theorem r234_stepOe (u w : Nat) (h : w+1 < 2*u)
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

private theorem r234_stepOo (u w : Nat) (h : w+1 < 2*u)
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

def d234PhaseU (j : Nat) : Nat := 6066*16^j+8*j+75

/-- After the initial burst and j low-side cycles, the first nonzero Cantor
    resonance d=234 reaches a completely explicit phase. -/
theorem d234_phase (j : Nat) :
    run (8*j+11) (prepared (j+2) 234) =
      some (phase (d234PhaseU j) (234*16^j)) := by
  have hc :
      3*(24*16^(j+2)-3)+234+24*j =
        3*(d234PhaseU j)+234*16^j := by
    dsimp [d234PhaseU]
    rw [Nat.pow_add]
    rw [show 16^2=256 by decide]
    omega
  have hg : 5*(234*16^j)+7 ≤ d234PhaseU j := by
    dsimp [d234PhaseU]
    omega
  have h := prepared_phase 2 j 234 (d234PhaseU j)
    (by decide) (by decide) hc hg
  rw [show 8*j+11=4*(j+2)+3+4*j by omega]
  exact h.1

/-- The six resonant ordinary blocks after the d=234 phase are exact.
    Their branch word is
      Oe F Oo F Oe F F F Oe F F F.
    Crucially the leading 16^j contribution to the first counter cancels. -/
set_option maxHeartbeats 5000000 in
theorem d234_tail (j : Nat) :
    run 12 (phase (d234PhaseU j) (234*16^j)) =
      some (416*j+4797,18432*16^j-808*j-9293) := by
  let P := 16^j
  have hP : 1 ≤ P := Nat.pow_pos (by decide)
  have hs : 16*j ≤ P := by simpa [P] using scale_ge j
  change run 12 (6066*P+8*j+75,6300*P+8*j+87) =
    some (416*j+4797,18432*P-808*j-9293)
  have h1 : next (6066*P+8*j+75,6300*P+8*j+87) =
      some (2916*P+4*j+39,12600*P+16*j+170) := by
    rw [r234_stepOe _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h2 : next (2916*P+4*j+39,12600*P+16*j+170) =
      some (5832*P+8*j+81,6768*P+8*j+89) := by
    rw [r234_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h3 : next (5832*P+8*j+81,6768*P+8*j+89) =
      some (2448*P+4*j+40,13536*P+16*j+178) := by
    rw [r234_stepOo _ _ (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h4 : next (2448*P+4*j+40,13536*P+16*j+178) =
      some (4896*P+8*j+83,8640*P+8*j+95) := by
    rw [r234_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h5 : next (4896*P+8*j+83,8640*P+8*j+95) =
      some (576*P+4*j+43,17280*P+16*j+186) := by
    rw [r234_stepOe _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h6 : next (576*P+4*j+43,17280*P+16*j+186) =
      some (1152*P+8*j+89,16128*P+8*j+97) := by
    rw [r234_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h7 : next (1152*P+8*j+89,16128*P+8*j+97) =
      some (2304*P+16*j+181,13824*P-8*j-84) := by
    rw [r234_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h8 : next (2304*P+16*j+181,13824*P-8*j-84) =
      some (4608*P+32*j+365,9216*P-40*j-449) := by
    rw [r234_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h9 : next (4608*P+32*j+365,9216*P-40*j-449) =
      some (52*j+597,18432*P-80*j-902) := by
    rw [r234_stepOe _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h10 : next (52*j+597,18432*P-80*j-902) =
      some (104*j+1197,18432*P-184*j-2099) := by
    rw [r234_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h11 : next (104*j+1197,18432*P-184*j-2099) =
      some (208*j+2397,18432*P-392*j-4496) := by
    rw [r234_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h12 : next (208*j+2397,18432*P-392*j-4496) =
      some (416*j+4797,18432*P-808*j-9293) := by
    rw [r234_stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  simp [run,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12]

/-- Exact first nonzero-resonance transfer from the prepared zero section.
    At scale m=j+2, the trajectory has lost its leading first-counter term
    after exactly 8j+23 accelerator moves. -/
theorem d234_post (j : Nat) :
    run (8*j+23) (prepared (j+2) 234) =
      some (416*j+4797,18432*16^j-808*j-9293) := by
  rw [show 8*j+23=(8*j+11)+12 by omega,run_add,d234_phase]
  exact d234_tail j

/-- The transformed U-coordinate coefficient at the d=234 post-resonance
    state.  In m=j+2 notation this is 2496m+23808. -/
theorem d234_post_Uc (j : Nat) :
    Uc (416*j+4797,18432*16^j-808*j-9293) = 2496*(j+2)+23808 := by
  simp [Uc]
  omega

/-- Any second exact-burst resonance of the d=234 coefficient forces the
    original scale into the single residue m=2 (mod 9). -/
theorem d234_second_resonance_mod9 (m I : Nat) (e : Nat → Bool)
    (h : (2496:Int)*m+23808 = 18+54*word4 e I) :
    m%9=2 := by
  have hw := word4_bound e I
  omega

/-- After writing m=9q+2, the second resonance parameter is the explicit
    affine Cantor target 416q+533. -/
theorem d234_second_resonance_word (q I : Nat) (e : Nat → Bool)
    (h : (2496:Int)*(9*q+2)+23808 = 18+54*word4 e I) :
    word4 e I = 416*q+533 := by
  omega

theorem d234_second_nonresonant_mod9 (m I : Nat) (hm : m%9≠2) :
    ∀ e : Nat → Bool,
      (2496:Int)*m+23808 ≠ 18+54*word4 e I := by
  intro e h
  exact hm (d234_second_resonance_mod9 m I e h)

#print axioms d234_phase
#print axioms d234_tail
#print axioms d234_post
#print axioms d234_second_resonance_mod9
#print axioms d234_second_resonance_word
#print axioms d234_second_nonresonant_mod9

end BB429.CoarseExit
