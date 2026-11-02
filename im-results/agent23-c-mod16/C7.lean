import CM16
namespace BB6.Agent23

/-- A second uniform all-time Machine C reset exclusion: j=64t+7. -/
theorem reset_seven_mod_sixtyfour_unreachable (t : Nat) :
    ¬Reach (128*t+15,192*t+25,0) := by
  intro hr
  have h0 : Reach (128*t+15,(192*t+19)+6,0) := by
    simpa [Nat.add_assoc] using hr
  have hx := reset_pull (128*t+15) (192*t+19) h0
  have h1 : Reach (320*t+35,2,192*t+23) := by
    simpa only [show (128*t+15)+(192*t+19)+1=320*t+35 by omega,
                show (192*t+19)+4=192*t+23 by omega] using hx
  have h2 : Reach (320*t+36,1,192*t+24) := by
    have hh := reached_two_parent (320*t+35) (192*t+19)
      (by simpa [Nat.add_assoc] using h1) (by omega)
    simpa [Nat.add_assoc] using hh
  rcases reached_one_parent (320*t+36) (192*t+20)
      (by simpa [Nat.add_assoc] using h2) with h3 | ⟨k,_,hk⟩
  · have h4 : Reach (0,160*t+17,192*t+25) := by
      obtain ⟨q,hqodd,hq,hqeq⟩ := zero_high_parent (320*t+37) (192*t+21)
        (by omega) (by simpa [Nat.add_assoc] using h3)
      have hqval : q=160*t+17 := by omega
      simpa [hqval,Nat.add_assoc] using hq
    have h5 : Reach (160*t+15,2,352*t+40) := by
      have hh := pull_high 0 (160*t+15) (192*t+21)
        (by simpa [Nat.add_assoc] using h4)
      simpa only [show 0+(160*t+15)=160*t+15 by omega,
                  show 192*t+21+(160*t+15)+4=352*t+40 by omega] using hh
    have h6 : Reach (160*t+16,1,352*t+41) := by
      have hh := reached_two_parent (160*t+15) (352*t+36)
        (by simpa [Nat.add_assoc] using h5) (by omega)
      simpa [Nat.add_assoc] using hh
    rcases reached_one_parent (160*t+16) (352*t+37)
        (by simpa [Nat.add_assoc] using h6) with hz | ⟨k,hrk,heq⟩
    · have h7 : Reach (0,80*t+7,352*t+42) := by
        obtain ⟨q,hqodd,hq,hqeq⟩ := zero_high_parent (160*t+17) (352*t+38)
          (by omega) (by simpa [Nat.add_assoc] using hz)
        have hqval : q=80*t+7 := by omega
        simpa [hqval,Nat.add_assoc] using hq
      have h8 : Reach (80*t+5,2,432*t+47) := by
        have hh := pull_high 0 (80*t+5) (352*t+38)
          (by simpa [Nat.add_assoc] using h7)
        simpa only [show 0+(80*t+5)=80*t+5 by omega,
                    show 352*t+38+(80*t+5)+4=432*t+47 by omega] using hh
      have h9 : Reach (80*t+6,1,432*t+48) := by
        have hh := reached_two_parent (80*t+5) (432*t+43)
          (by simpa [Nat.add_assoc] using h8) (by omega)
        simpa [Nat.add_assoc] using hh
      rcases reached_one_parent (80*t+6) (432*t+44)
          (by simpa [Nat.add_assoc] using h9) with hbad | ⟨q,hq,hqe⟩
      · have hh := reached_zero_high (80*t+7) (432*t+45)
          (by simpa [Nat.add_assoc] using hbad)
        omega
      · omega
    · have hval : k=176*t+20 := by omega
      subst k
      have hs : Reach (160*t+18,(176*t+14)+6,0) := by
        simpa [Nat.add_assoc] using hrk
      have hhub := reset_pull (160*t+18) (176*t+14) hs
      have h10 : Reach (336*t+33,2,176*t+18) := by
        simpa only [show 160*t+18+(176*t+14)+1=336*t+33 by omega,
                    show 176*t+14+4=176*t+18 by omega] using hhub
      have h11 : Reach (336*t+34,1,176*t+19) := by
        have hh := reached_two_parent (336*t+33) (176*t+14)
          (by simpa [Nat.add_assoc] using h10) (by omega)
        simpa [Nat.add_assoc] using hh
      rcases reached_one_parent (336*t+34) (176*t+15)
          (by simpa [Nat.add_assoc] using h11) with hbad | ⟨q,hq,hqe⟩
      · have hh := reached_zero_high (336*t+35) (176*t+16)
          (by simpa [Nat.add_assoc] using hbad)
        omega
      · have hqval : q=88*t+9 := by omega
        subst q
        have hh := reached_odd_zero_mod4_hole (336*t+36) (88*t+9)
          (by simpa [Nat.add_assoc] using hq) (by omega) (by omega)
        omega
  · omega

#print axioms BB6.Agent23.reset_seven_mod_sixtyfour_unreachable
end BB6.Agent23
