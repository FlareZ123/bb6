import BB429Branch29Mod64
import Lean.Elab.Tactic.Omega

/-!
# Source-root #429: 29-mod32 odd-reset, deeper dyadic exclusion

Two further infinite q-cylinders are impossible: q=18 or 66 (mod128).
The new short general rooted row (a=3 mod8,b odd) forces b=7 mod8
for every a>=13 and rests directly on the source's exact first inverse
and the proven positive-even-input blank invariant.
-/

namespace BB429Branch29Mod128
open BB429Reset31
set_option maxHeartbeats 16000000
set_option maxRecDepth 30000

/-- A genuine blank-root state with sufficiently large odd first
counter 3(mod8), odd second counter, must have second counter 7(mod8).
Its unique predecessor has a positive even first counter and second
counter exactly 2(mod8). -/
theorem rooted_three_odd_seven
    (a b : Nat) (ha : 13≤a)
    (h3 : a%8=3) (hb : b%2=1)
    (hr : Reach a b) : b%8=7 := by
  obtain ⟨x,y,hp,hs⟩ := pred a b (by omega) hr
  obtain ⟨hxa,hyb⟩ :=
    BB429OddResetGate.incoming_odd_second x y a b hs hb
  obtain ⟨n,hn⟩ := hp
  have heven :=
    BB429RootEven8.rooted_positive_even_eight n x y hn
      (by omega) (by omega)
  omega

/-- q=66 mod128 is incompatible with the genuine blank root.
After a forced F predecessor, the alternative S inverse is
positive-even/odd and the F route forces a parent in the
(7 mod8,5 mod8) or (3 mod8,5 mod8) forbidden rooted section. -/
theorem no_q_66_mod128 (q : Nat) (hq : 21≤q)
    (hq128 : q%128=66) :
    ¬Reach (32*q+29) (64*q+55) := by
  intro hroot
  let t := q/64
  have hqeq : q=64*t+2 := by dsimp [t]; omega
  have htodd : t%2=1 := by omega
  have h5 :=
    BB429Branch29.to_q_minus_two q hq
      (BB429Branch29.first_three q hroot)
  obtain ⟨x,y,hp,hs⟩ :=
    pred (q-2) (126*q+102) (by omega) h5
  obtain ⟨hxa,hyb,_⟩ :=
    BB429OddResetGate.incoming_even x y
      (q-2) (126*q+102) hs (by omega) (by omega)
  have hx : x=2080*t+85 := by omega
  have hy : y=4032*t+177 := by omega
  rw [hx,hy] at hp
  obtain ⟨x2,y2,hp2,hs2⟩ :=
    pred (2080*t+85) (4032*t+177) (by omega) hp
  obtain ⟨h2a,h2b⟩ :=
    BB429OddResetGate.incoming_odd_second x2 y2
      (2080*t+85) (4032*t+177) hs2 (by omega)
  have hx2 : x2=1040*t+41 := by omega
  have hy2 : y2=6112*t+262 := by omega
  rw [hx2,hy2] at hp2
  obtain ⟨x3,y3,hp3,hs3⟩ :=
    pred (1040*t+41) (6112*t+262) (by omega) hp2
  rcases BB429Reset31.odd_inverse x3 y3
      (1040*t+41) (6112*t+262)
      (by omega) (by omega) hs3 with hF | hS
  · obtain ⟨h3a,h3b⟩ := hF
    have hx3 : x3=520*t+19 := by omega
    have hy3 : y3=7152*t+303 := by omega
    rw [hx3,hy3] at hp3
    obtain ⟨x4,y4,hp4,hs4⟩ :=
      pred (520*t+19) (7152*t+303) (by omega) hp3
    obtain ⟨h4a,h4b⟩ :=
      BB429OddResetGate.incoming_odd_second x4 y4
        (520*t+19) (7152*t+303) hs4 (by omega)
    have hx4 : x4=260*t+8 := by omega
    have hy4 : y4=7672*t+322 := by omega
    rw [hx4,hy4] at hp4
    obtain ⟨x5,y5,hp5,hs5⟩ :=
      pred (260*t+8) (7672*t+322) (by omega) hp4
    obtain ⟨h5a,h5b,_⟩ :=
      BB429OddResetGate.incoming_even x5 y5
        (260*t+8) (7672*t+322) hs5 (by omega) (by omega)
    have hx5 : x5=2178*t+85 := by omega
    have hy5 : y5=3836*t+161 := by omega
    rw [hx5,hy5] at hp5
    have hcase : t%4=1 ∨ t%4=3 := by omega
    rcases hcase with h1 | h3
    · obtain ⟨n,hn⟩ := hp5
      have hbad :=
        BB429SevenStrong.rooted_seven_strong n
          (2178*t+85) (3836*t+161) hn (by omega)
      omega
    · exact False.elim (by
        have hodd :=
          rooted_three_odd_seven (2178*t+85) (3836*t+161)
            (by omega) (by omega) (by omega) hp5
        omega)
  · obtain ⟨h3a,h3b,_⟩ := hS
    have hx3 : x3=2568*t+100 := by omega
    have hy3 : y3=3056*t+133 := by omega
    rw [hx3,hy3] at hp3
    obtain ⟨n,hn⟩ := hp3
    have he :=
      BB429NoThree.reachable_even_positive n
        (2568*t+100) (3056*t+133) hn
        (by omega) (by omega)
    omega

/-- q=18 mod128 is incompatible with the genuine blank root.
One two-branch inverse collapses because the S predecessor is
even/odd. The remaining odd inverse has an even output divisible by
four and must be F; its final ancestor violates either rooted row
3/7 or the strong seven-sector invariant. -/
theorem no_q_18_mod128 (q : Nat) (hq : 21≤q)
    (hq128 : q%128=18) :
    ¬Reach (32*q+29) (64*q+55) := by
  intro hroot
  let t := q/64
  have hqeq : q=64*t+18 := by dsimp [t]; omega
  have hteven : t%2=0 := by omega
  have h5 :=
    BB429Branch29.to_q_minus_two q hq
      (BB429Branch29.first_three q hroot)
  obtain ⟨x,y,hp,hs⟩ :=
    pred (q-2) (126*q+102) (by omega) h5
  obtain ⟨hxa,hyb,_⟩ :=
    BB429OddResetGate.incoming_even x y
      (q-2) (126*q+102) hs (by omega) (by omega)
  have hx : x=2080*t+605 := by omega
  have hy : y=4032*t+1185 := by omega
  rw [hx,hy] at hp
  obtain ⟨x2,y2,hp2,hs2⟩ :=
    pred (2080*t+605) (4032*t+1185) (by omega) hp
  obtain ⟨h2a,h2b⟩ :=
    BB429OddResetGate.incoming_odd_second x2 y2
      (2080*t+605) (4032*t+1185) hs2 (by omega)
  have hx2 : x2=1040*t+301 := by omega
  have hy2 : y2=6112*t+1790 := by omega
  rw [hx2,hy2] at hp2
  obtain ⟨x3,y3,hp3,hs3⟩ :=
    pred (1040*t+301) (6112*t+1790) (by omega) hp2
  rcases BB429Reset31.odd_inverse x3 y3
      (1040*t+301) (6112*t+1790)
      (by omega) (by omega) hs3 with hF | hS
  · obtain ⟨h3a,h3b⟩ := hF
    have hx3 : x3=520*t+149 := by omega
    have hy3 : y3=7152*t+2091 := by omega
    rw [hx3,hy3] at hp3
    obtain ⟨x4,y4,hp4,hs4⟩ :=
      pred (520*t+149) (7152*t+2091) (by omega) hp3
    obtain ⟨h4a,h4b⟩ :=
      BB429OddResetGate.incoming_odd_second x4 y4
        (520*t+149) (7152*t+2091) hs4 (by omega)
    have hx4 : x4=260*t+73 := by omega
    have hy4 : y4=7672*t+2240 := by omega
    rw [hx4,hy4] at hp4
    obtain ⟨x5,y5,hp5,hs5⟩ :=
      pred (260*t+73) (7672*t+2240) (by omega) hp4
    rcases BB429Reset31.odd_inverse x5 y5
      (260*t+73) (7672*t+2240)
      (by omega) (by omega) hs5 with hF2 | hS2
    · obtain ⟨h5a,h5b⟩ := hF2
      have hx5 : x5=130*t+35 := by omega
      have hy5 : y5=7932*t+2313 := by omega
      rw [hx5,hy5] at hp5
      have hcase : t%4=0 ∨ t%4=2 := by omega
      rcases hcase with h0 | h2
      · have hbad :=
          rooted_three_odd_seven (130*t+35) (7932*t+2313)
            (by omega) (by omega) (by omega) hp5
        omega
      · obtain ⟨n,hn⟩ := hp5
        have hbad :=
          BB429SevenStrong.rooted_seven_strong n
            (130*t+35) (7932*t+2313) hn (by omega)
        omega
    · obtain ⟨_,_,hmod⟩ := hS2
      omega
  · obtain ⟨h3a,h3b,_⟩ := hS
    have hx3 : x3=2568*t+742 := by omega
    have hy3 : y3=3056*t+897 := by omega
    rw [hx3,hy3] at hp3
    obtain ⟨n,hn⟩ := hp3
    have he :=
      BB429NoThree.reachable_even_positive n
        (2568*t+742) (3056*t+897) hn
        (by omega) (by omega)
    omega

/-- For q>=21 on the genuine blank orbit, the first counter
32q+29's odd-reset family admits only fourteen classes modulo128
(instead of sixteen after the eight/mod64 theorem). -/
theorem rooted_29_q_fourteen_mod128 (q : Nat) (hq : 21≤q)
    (hroot : Reach (32*q+29) (64*q+55)) :
    q%128=2 ∨ q%128=10 ∨ q%128=15 ∨ q%128=31 ∨
    q%128=47 ∨ q%128=58 ∨ q%128=63 ∨ q%128=74 ∨
    q%128=79 ∨ q%128=82 ∨ q%128=95 ∨ q%128=111 ∨
    q%128=122 ∨ q%128=127 := by
  have h64 := BB429Branch29Mod64.rooted_29_q_eight_mod64 q hq hroot
  have h18 : q%128≠18 := by
    intro hh
    exact no_q_18_mod128 q hq hh hroot
  have h66 : q%128≠66 := by
    intro hh
    exact no_q_66_mod128 q hq hh hroot
  omega

#print axioms rooted_three_odd_seven
#print axioms no_q_66_mod128
#print axioms no_q_18_mod128
#print axioms rooted_29_q_fourteen_mod128
end BB429Branch29Mod128
