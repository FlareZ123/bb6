import BB429Branch7
import Lean.Elab.Tactic.Omega

/-!
# A uniform rooted restriction on #429's odd-reset 29 mod 32 family

All paths are for the actual blank-start local accelerator `BB429.run`.
The main result is a necessary condition, NOT a halt/nonhalt decision.
It eliminates six of eight q-residues on the remaining family
(u,w)=(32q+29,64q+55), for q>=21, by explicit exact preimages.
-/

namespace BB429Branch29
open BB429Reset31
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

/-- The first three inverse source steps are forced. The possible second
preimage of (16q+13,96q+84) contradicts b = 2 (mod 4). -/
theorem first_three (q : Nat)
    (hr : Reach (32*q+29) (64*q+55)) :
    Reach (4*q+1) (120*q+102) := by
  obtain ⟨x1,y1,hp1,hs1⟩ :=
    pred (32*q+29) (64*q+55) (by omega) hr
  obtain ⟨h1a,h1b⟩ :=
    BB429OddResetGate.incoming_odd_second x1 y1
      (32*q+29) (64*q+55) hs1 (by omega)
  have hx1 : x1=16*q+13 := by omega
  have hy1 : y1=96*q+84 := by omega
  rw [hx1,hy1] at hp1
  obtain ⟨x2,y2,hp2,hs2⟩ :=
    pred (16*q+13) (96*q+84) (by omega) hp1
  rcases odd_inverse x2 y2 (16*q+13) (96*q+84)
      (by omega) (by omega) hs2 with hF | hS
  · obtain ⟨h2a,h2b⟩ := hF
    have hx2 : x2=8*q+5 := by omega
    have hy2 : y2=112*q+97 := by omega
    rw [hx2,hy2] at hp2
    obtain ⟨x3,y3,hp3,hs3⟩ :=
      pred (8*q+5) (112*q+97) (by omega) hp2
    obtain ⟨h3a,h3b⟩ :=
      BB429OddResetGate.incoming_odd_second x3 y3
        (8*q+5) (112*q+97) hs3 (by omega)
    have hx3 : x3=4*q+1 := by omega
    have hy3 : y3=120*q+102 := by omega
    simpa only [hx3,hy3] using hp3
  · obtain ⟨_,_,hmod⟩ := hS
    omega

/-- The next pair of inverse steps is forced for q>=21: the alternative
source preimage has a positive even first counter and an odd second
counter, violating the actual-root even-counter theorem. -/
theorem to_q_minus_two (q : Nat) (hq : 21≤q)
    (hr : Reach (4*q+1) (120*q+102)) :
    Reach (q-2) (126*q+102) := by
  obtain ⟨x4,y4,hp4,hs4⟩ :=
    pred (4*q+1) (120*q+102) (by omega) hr
  rcases odd_inverse x4 y4 (4*q+1) (120*q+102)
      (by omega) (by omega) hs4 with hF | hS
  · obtain ⟨h4a,h4b⟩ := hF
    have hx4 : x4=2*q-1 := by omega
    have hy4 : y4=124*q+103 := by omega
    rw [hx4,hy4] at hp4
    obtain ⟨x5,y5,hp5,hs5⟩ :=
      pred (2*q-1) (124*q+103) (by omega) hp4
    obtain ⟨h5a,h5b⟩ :=
      BB429OddResetGate.incoming_odd_second x5 y5
        (2*q-1) (124*q+103) hs5 (by omega)
    have hx5 : x5=q-2 := by omega
    have hy5 : y5=126*q+102 := by omega
    simpa only [hx5,hy5] using hp5
  · obtain ⟨h4a,h4b,_⟩ := hS
    have hx4 : x4=34*q+20 := by omega
    have hy4 : y4=60*q+53 := by omega
    rw [hx4,hy4] at hp4
    obtain ⟨n,hn⟩ := hp4
    have he :=
      BB429NoThree.reachable_even_positive n
        (34*q+20) (60*q+53) hn (by omega) (by omega)
    omega

/-- On an odd q, the (q-2,126q+102) ancestor has its own forced
first-branch parent. This includes the genuinely rooted small-state
exception only when q>=21, where all counters exceed 11. -/
theorem odd_q_parent (q : Nat) (hq : 21≤q) (hodd : q%2=1)
    (hr : Reach (q-2) (126*q+102)) :
    ∃ x y, Reach x y ∧ 2*x+5=q ∧ y=127*q+100 := by
  obtain ⟨x,y,hp,hs⟩ :=
    pred (q-2) (126*q+102) (by omega) hr
  rcases odd_inverse x y (q-2) (126*q+102)
      (by omega) (by omega) hs with hF | hS
  · obtain ⟨ha,hb⟩ := hF
    exact ⟨x,y,hp,by omega,by omega⟩
  · obtain ⟨_,_,hmod⟩ := hS
    omega

/-- For all q>=21, at most the residue classes q=2,7 (mod 8)
can be reached on this true-blank odd-reset line. No finite trace
assumption or periodicity assumption is used. -/
theorem rooted_29_q_two_of_eight (q : Nat) (hq : 21≤q)
    (hr : Reach (32*q+29) (64*q+55)) :
    q%8=2 ∨ q%8=7 := by
  have h3 := first_three q hr
  have hnot04 : q%4≠0 := by
    intro hc
    obtain ⟨n,hn⟩ := h3
    have hs := BB429SevenStrong.rooted_one_strong n
      (4*q+1) (120*q+102) hn (by omega)
    omega
  have hnot1 : q%8≠1 := by
    intro hc
    obtain ⟨n,hn⟩ := h3
    have hs := BB429SevenStrong.rooted_five_strong n
      (4*q+1) (120*q+102) hn (by omega)
    omega
  have h5 := to_q_minus_two q hq h3
  have hnot6 : q%8≠6 := by
    intro hc
    obtain ⟨n,hn⟩ := h5
    have hs := BB429Even16.rooted_even_sixteen n
      (q-2) (126*q+102) hn (by omega) (by omega)
    have hs0 := hs.1 (by omega)
    omega
  have hnot3 : q%8≠3 := by
    intro hc
    have hcase : q%16=3 ∨ q%16=11 := by omega
    rcases hcase with h3mod | h11mod
    · obtain ⟨n,hn⟩ := h5
      have hs := BB429SevenStrong.rooted_one_strong n
        (q-2) (126*q+102) hn (by omega)
      omega
    · obtain ⟨x,y,hp,hx,hy⟩ :=
        odd_q_parent q hq (by omega) h5
      obtain ⟨n,hn⟩ := hp
      have hs := BB429Even16.rooted_odd_three_one n
        x y hn (by omega) (by omega)
      omega
  have hnot5 : q%8≠5 := by
    intro hc
    obtain ⟨x,y,hp,hx,hy⟩ :=
      odd_q_parent q hq (by omega) h5
    obtain ⟨n,hn⟩ := hp
    have hs := BB429NoThree.reachable_even_positive n
      x y hn (by omega) (by omega)
    omega
  omega

#print axioms rooted_29_q_two_of_eight
end BB429Branch29
