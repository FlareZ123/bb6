import DyadicFirstBranch
import ModularCone

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone
open BB6.Agent21Dyadic

private theorem bad_q_two_mod_four (s : Pair) (hb : Bad s) :
    (s.x+s.y+(s.x+s.y)%2)%4=2 := by
  rcases hb with ⟨hy,hxy⟩
  rcases hxy with h | h
  · omega
  · omega

private theorem bad_not_full_divisible (b : Nat) (s : Pair)
    (hb : 2≤b) (hd : Bad s) :
    ¬ BB6.Agent21Dyadic.P b ∣ -(s.x+s.y+(s.x+s.y)%2) := by
  intro h
  have he : BB6.Agent21Dyadic.P 2 ∣ BB6.Agent21Dyadic.P b :=
    BB6.Agent21Dyadic.P_dvd 2 b hb
  have hc := Int.dvd_trans he h
  have hm := Int.emod_eq_zero_of_dvd hc
  have hq := bad_q_two_mod_four s hd
  change (-(s.x+s.y+(s.x+s.y)%2))%4=0 at hm
  omega

/-- A bad modular cone is *exactly* a 2-adic dead-end for the
    positive inverse-word language. In particular no completed or
    pending word can rescue a bad residue at precision >=2. -/
theorem bad_implies_not_open (b : Nat) (s : Pair)
    (hb : 2≤b) (hd : Bad s) :
    ¬ OpenAt (signedS s.x s.y) (signedZ s.x s.y) b := by
  intro ho
  have hn : 0<b := by omega
  have hq := bad_q_two_mod_four s hd
  have hnot := bad_not_full_divisible b s hb hd
  obtain ⟨r,hr,hrb,hpar,hdiv⟩ :=
    signed_open_strict_first_gap s.x s.y b hn hnot ho
  have hy : s.y%2=1 := hd.1
  have hre : (r:Int)%2=0 := by rw [hpar]; omega
  have hr2 : 2≤r := by omega
  have h2 : BB6.Agent21Dyadic.P 2 ∣ BB6.Agent21Dyadic.P r :=
    BB6.Agent21Dyadic.P_dvd 2 r hr2
  have hc := Int.dvd_trans h2 hdiv
  have hm := Int.emod_eq_zero_of_dvd hc
  change (-(s.x+s.y+(s.x+s.y)%2))%4=0 at hm
  omega

#print axioms bad_implies_not_open
end BB6.Agent21Duality
