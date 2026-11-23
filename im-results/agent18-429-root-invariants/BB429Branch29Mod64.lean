import BB429Branch29Mod16
import Lean.Elab.Tactic.Omega

/-!
# Further all-time inverse exclusions in #429 odd-reset 29 mod32 family

The 29 mod32 family parameter q is already restricted to {2,10,15}
modulo 16. The exact predecessor of the even ancestor q-2 supplies
two more disjoint q classes modulo 64, using a rooted 5(mod32) gate
and a two-generation odd-target 13(mod32),1(mod8) obstruction.
-/

namespace BB429Branch29Mod64
open BB429Reset31
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

/-- All-time true-root obstruction for sufficiently large odd first
counter 13 (mod32) and second counter 1 (mod8). The two-step exact
inverse leads either to forbidden (1 mod8,3 mod4) or to positive even
first counter with odd second counter. -/
theorem rooted_not_thirteen_one
    (a b : Nat) (hr : Reach a b) (ha : 33≤a)
    (ha32 : a%32=13) (hb8 : b%8=1) : False := by
  obtain ⟨x,y,hp,hs⟩ := pred a b (by omega) hr
  rcases BB429Reset31.odd_inverse x y a b
      (by omega) (by omega) hs with hF | hS
  · obtain ⟨hxa,hyb⟩ := hF
    have hx5 : x%16=5 := by omega
    have hy6 : y%8=6 := by omega
    have hxbig : 13≤x := by omega
    obtain ⟨z,v,hpp,hss⟩ := pred x y (by omega) hp
    rcases BB429Reset31.odd_inverse z v x y
        hxbig (by omega) hss with hf2 | hs2
    · obtain ⟨hza,hvb⟩ := hf2
      obtain ⟨n,hn⟩ := hpp
      have hall := BB429Mod8.all_blank_returns_allowed n z v hn
      unfold BB429Mod8.Allowed at hall
      omega
    · obtain ⟨hza,hvb,hmod⟩ := hs2
      obtain ⟨n,hn⟩ := hpp
      have hpmod :=
        BB429NoThree.reachable_even_positive n z v hn
          (by omega) (by omega)
      omega
  · obtain ⟨_,_,hmod⟩ := hS
    omega

/-- The q=34(mod64) cylinder is globally unreachable: the forced
even-input ancestor lies in the rooted (5 mod32,1 mod8) obstruction. -/
theorem no_q_34_mod64 (q : Nat) (hq : 21≤q)
    (hq64 : q%64=34) :
    ¬Reach (32*q+29) (64*q+55) := by
  intro hroot
  let r := q/64
  have hqeq : q=64*r+34 := by dsimp [r]; omega
  have h5 :=
    BB429Branch29.to_q_minus_two q hq
      (BB429Branch29.first_three q hroot)
  obtain ⟨x,y,hp,hs⟩ :=
    pred (q-2) (126*q+102) (by omega) h5
  obtain ⟨hxa,hyb,_⟩ :=
    BB429OddResetGate.incoming_even x y
      (q-2) (126*q+102) hs (by omega) (by omega)
  have hx : x=2080*r+1125 := by omega
  have hy : y=4032*r+2193 := by omega
  rw [hx,hy] at hp
  obtain ⟨n,hn⟩ := hp
  have hg :=
    BB429SevenStrong.rooted_five_strong n
      (2080*r+1125) (4032*r+2193) hn (by omega)
  omega

/-- The q=50(mod64) cylinder is globally unreachable: its forced
even-input ancestor is (13 mod32,1 mod8), and its exact two-step
backward cone is incompatible with root reachability. -/
theorem no_q_50_mod64 (q : Nat) (hq : 21≤q)
    (hq64 : q%64=50) :
    ¬Reach (32*q+29) (64*q+55) := by
  intro hroot
  let r := q/64
  have hqeq : q=64*r+50 := by dsimp [r]; omega
  have h5 :=
    BB429Branch29.to_q_minus_two q hq
      (BB429Branch29.first_three q hroot)
  obtain ⟨x,y,hp,hs⟩ :=
    pred (q-2) (126*q+102) (by omega) h5
  obtain ⟨hxa,hyb,_⟩ :=
    BB429OddResetGate.incoming_even x y
      (q-2) (126*q+102) hs (by omega) (by omega)
  have hx : x=2080*r+1645 := by omega
  have hy : y=4032*r+3201 := by omega
  rw [hx,hy] at hp
  exact rooted_not_thirteen_one
    (2080*r+1645) (4032*r+3201) hp
    (by omega) (by omega) (by omega)

/-- With positive-parameter true blank-root source reachability, the
29(mod32) odd-reset family admits at most ten q classes modulo 64,
rather than the preceding 12. -/
theorem rooted_29_q_ten_mod64 (q : Nat) (hq : 21≤q)
    (hroot : Reach (32*q+29) (64*q+55)) :
    q%64=2 ∨ q%64=10 ∨ q%64=15 ∨ q%64=18 ∨
    q%64=26 ∨ q%64=31 ∨ q%64=42 ∨ q%64=47 ∨
    q%64=58 ∨ q%64=63 := by
  have h16 := BB429Branch29Mod16.rooted_29_q_three_mod16 q hq hroot
  have h34 : q%64≠34 := by
    intro hh
    exact no_q_34_mod64 q hq hh hroot
  have h50 : q%64≠50 := by
    intro hh
    exact no_q_50_mod64 q hq hh hroot
  omega


/-- The q=26 or 42 (mod64) cylinders are impossible on the genuine
blank root. The mandatory F inverse of the even-parent's odd target
has an even second output; its F parent is even/odd, while its S
parent violates either the rooted seven-sector restriction (q=26)
or the allowed one-sector restriction (q=42). -/
theorem no_q_26_or_42_mod64 (q : Nat) (hq : 21≤q)
    (hq64 : q%64=26 ∨ q%64=42) :
    ¬Reach (32*q+29) (64*q+55) := by
  intro hroot
  let r := q/16
  have hqeq : q=16*r+10 := by dsimp [r]; omega
  have hrcase : r%4=1 ∨ r%4=2 := by omega
  have h5 :=
    BB429Branch29.to_q_minus_two q hq
      (BB429Branch29.first_three q hroot)
  obtain ⟨x,y,hp,hs⟩ :=
    pred (q-2) (126*q+102) (by omega) h5
  obtain ⟨hxa,hyb,_⟩ :=
    BB429OddResetGate.incoming_even x y
      (q-2) (126*q+102) hs (by omega) (by omega)
  have hx : x=520*r+345 := by omega
  have hy : y=1008*r+681 := by omega
  rw [hx,hy] at hp
  obtain ⟨x2,y2,hp2,hs2⟩ :=
    pred (520*r+345) (1008*r+681) (by omega) hp
  obtain ⟨h2a,h2b⟩ :=
    BB429OddResetGate.incoming_odd_second x2 y2
      (520*r+345) (1008*r+681) hs2 (by omega)
  have hx2 : x2=260*r+171 := by omega
  have hy2 : y2=1528*r+1026 := by omega
  rw [hx2,hy2] at hp2
  obtain ⟨x3,y3,hp3,hs3⟩ :=
    pred (260*r+171) (1528*r+1026) (by omega) hp2
  rcases BB429Reset31.odd_inverse x3 y3
      (260*r+171) (1528*r+1026)
      (by omega) (by omega) hs3 with hF | hS
  · obtain ⟨h3a,h3b⟩ := hF
    have hx3 : x3=130*r+84 := by omega
    have hy3 : y3=1788*r+1197 := by omega
    rw [hx3,hy3] at hp3
    obtain ⟨n,hn⟩ := hp3
    have hbad :=
      BB429NoThree.reachable_even_positive n
        (130*r+84) (1788*r+1197) hn
        (by omega) (by omega)
    omega
  · obtain ⟨h3a,h3b,_⟩ := hS
    have hx3 : x3=642*r+421 := by omega
    have hy3 : y3=764*r+515 := by omega
    rw [hx3,hy3] at hp3
    rcases hrcase with h1 | h2
    · obtain ⟨n,hn⟩ := hp3
      have hbad :=
        BB429SevenStrong.rooted_seven_strong n
          (642*r+421) (764*r+515) hn (by omega)
      omega
    · obtain ⟨n,hn⟩ := hp3
      have hbad :=
        BB429Mod8.all_blank_returns_allowed n
          (642*r+421) (764*r+515) hn
      unfold BB429Mod8.Allowed at hbad
      omega

/-- A stronger necessary finite-residue summary: only eight
out of 64 q residues survive the exact rooted inverse tests. -/
theorem rooted_29_q_eight_mod64 (q : Nat) (hq : 21≤q)
    (hroot : Reach (32*q+29) (64*q+55)) :
    q%64=2 ∨ q%64=10 ∨ q%64=15 ∨ q%64=18 ∨
    q%64=31 ∨ q%64=47 ∨ q%64=58 ∨ q%64=63 := by
  have hten := rooted_29_q_ten_mod64 q hq hroot
  have h2642 : ¬(q%64=26 ∨ q%64=42) := by
    intro hh
    exact no_q_26_or_42_mod64 q hq hh hroot
  omega

#print axioms no_q_26_or_42_mod64
#print axioms rooted_29_q_eight_mod64

#print axioms rooted_not_thirteen_one
#print axioms no_q_34_mod64
#print axioms no_q_50_mod64
#print axioms rooted_29_q_ten_mod64

end BB429Branch29Mod64
