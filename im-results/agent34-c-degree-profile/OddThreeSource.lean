import OddThreeArithmetic
import SectionAllInverse
import Agent3CImage
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34OddThree
open BB6.Agent46

/-- The local arithmetic grammar is definitionally the literal original
section's complete predecessor grammar, not a weakened abstraction. -/
private theorem source_preimage (a k x y : Nat)
    (h : secNext (a,k)=some (x,y)) :
    P a k x y := by
  exact (section_preimage_all_iff a k x y).mp h

private theorem source_edge (a k x y : Nat)
    (h : P a k x y) :
    secNext (a,k)=some (x,y) := by
  exact (section_preimage_all_iff a k x y).mpr h

/-- The odd-right positive-density cone is in the genuine two-step image
of the unchanged original Machine C return map. -/
theorem two_edges (x y : Nat)
    (hx : 8≤x) (hy : 256≤y)
    (hs : (x+y)%128=84) (hr : y%64=59) :
    ∃ a k b l,
      secNext (b,l)=some (a,k) ∧ secNext (a,k)=some (x,y) := by
  obtain ⟨a,k,h1,ha,hk,heven⟩ := first_exists x y hx hy hs hr
  obtain ⟨b,l,h2⟩ := second_exists a k ha hk heven
  exact ⟨a,k,b,l,source_edge b l a k h2,source_edge a k x y h1⟩

/-- Every actual chain of three source transitions ending in the odd-right
cone contradicts the original odd-image parity theorem. -/
theorem no_three_edges (u v b l a k x y : Nat)
    (hx : 8≤x) (hy : 256≤y)
    (hs : (x+y)%128=84) (hr : y%64=59)
    (hthird : secNext (u,v)=some (b,l))
    (hsecond : secNext (b,l)=some (a,k))
    (hfirst : secNext (a,k)=some (x,y)) : False := by
  obtain ⟨ha32,hk32,haeq,hkeq⟩ :=
    first_forced a k x y (by omega) hs hr (source_preimage a k x y hfirst)
  have ha : 128≤a := by omega
  have hk : 128≤k := by omega
  obtain ⟨hlbound,hodd,hbad⟩ :=
    second_forced a k b l ha hk ha32 hk32 (source_preimage b l a k hsecond)
  have himage := BB6.Agent3.section_odd_image u v b l hthird hlbound hodd
  omega

/-- The entire cone is absent after three section transitions from any
start, with no bound on run length or counter magnitude. -/
theorem all_source_no_three (start : Nat×Nat) (n x y : Nat)
    (hx : 8≤x) (hy : 256≤y)
    (hs : (x+y)%128=84) (hr : y%64=59) :
    BB6.Agent8Section.run secNext (n+3) (some start) ≠ some (x,y) := by
  intro ht
  have htime : n+3=((n+1)+1)+1 := by omega
  rw [htime] at ht
  change (BB6.Agent8Section.run secNext ((n+1)+1) (some start)).bind secNext =
    some (x,y) at ht
  cases hp : BB6.Agent8Section.run secNext ((n+1)+1) (some start) with
  | none => simp [hp] at ht
  | some p =>
      rcases p with ⟨a,k⟩
      have hfirst : secNext (a,k)=some (x,y) := by simpa [hp] using ht
      change (BB6.Agent8Section.run secNext (n+1) (some start)).bind secNext =
        some (a,k) at hp
      cases hq : BB6.Agent8Section.run secNext (n+1) (some start) with
      | none => simp [hq] at hp
      | some q =>
          rcases q with ⟨b,l⟩
          have hsecond : secNext (b,l)=some (a,k) := by simpa [hq] using hp
          change (BB6.Agent8Section.run secNext n (some start)).bind secNext =
            some (b,l) at hq
          cases h0 : BB6.Agent8Section.run secNext n (some start) with
          | none => simp [h0] at hq
          | some p =>
              rcases p with ⟨u,v⟩
              have hthird : secNext (u,v)=some (b,l) := by simpa [h0] using hq
              exact no_three_edges u v b l a k x y hx hy hs hr hthird hsecond hfirst

/-- A new odd-right cylinder is unreachable from the genuine Machine C
blank-derived first section seed at every time, including 0,1,2. -/
theorem blank_unreachable (time x y : Nat)
    (hx : 8≤x) (hy : 256≤y)
    (hs : (x+y)%128=84) (hr : y%64=59) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  cases time with
  | zero =>
      intro h
      simp [BB6.Agent8Section.run] at h
      omega
  | succ n =>
      cases n with
      | zero =>
          intro h
          have hfirst : secNext (5,1)=some (3,4) := by decide
          simp [BB6.Agent8Section.run,hfirst] at h
          omega
      | succ n =>
          cases n with
          | zero =>
              intro h
              have hfirst : secNext (5,1)=some (3,4) := by decide
              have hsecond : secNext (3,4)=some (4,7) := by
                simp [secNext,exactSection,bounce]
              simp [BB6.Agent8Section.run,hfirst,hsecond] at h
              omega
          | succ n =>
              simpa only [show n+1+1+1=n+3 by omega] using
                all_source_no_three (5,1) n x y hx hy hs hr

/-- Pullback of the odd-right original-source cone to the genuine high
stopping equation. The stopping right counter itself is a hypothesis. -/
theorem high_stop_sector (j m k : Nat)
    (hm : m%32=7) (hpair : (j+42)%128=(3*m)%128)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3+k)%128=84 ∧ k%64=59 := by
  have hm3 : 3≤m := by omega
  have hp128 : 128 ∣ (2:Nat)^(2*m+2) := by
    change (2:Nat)^7 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hp128
  have hmod : (k+j+3*m+5)%128=0 := by
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨u*(j+3),?_⟩
    calc
      k+j+3*m+5=2^(2*m+2)*(j+3) := hgate
      _=(128*u)*(j+3) := by rw [hu]
      _=128*(u*(j+3)) := by ac_rfl
  omega

private theorem high_power_linear (m : Nat) (hm : 2≤m) :
    16*m+16 ≤ (2:Nat)^(2*m+2) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hbase : m≤1
      · have heq : m=1 := by omega
        subst m
        decide
      · have hprev : 2≤m := by omega
        have hh := ih hprev
        have heq : 2*(m+1)+2=(2*m+2)+2 := by omega
        rw [heq,Nat.pow_add]
        simp only [show (2:Nat)^2=4 by decide]
        omega

/-- Every high stopping state in this cylinder automatically meets the
large-coordinate hypotheses required by the source three-edge obstruction. -/
theorem high_stop_bounds (j m k : Nat)
    (hm : m%32=7) (hpair : (j+42)%128=(3*m)%128)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    8≤2*j+3 ∧ 256≤k := by
  have hm7 : 7≤m := by omega
  have hj3 : 3≤j := by omega
  have hp : 16*m+16 ≤ 2^(2*m+2) := high_power_linear m (by omega)
  have h1 : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j h1
  have hbound : 3*(16*m+16) ≤ 3*2^(2*m+2) :=
    Nat.mul_le_mul_left 3 hp
  have hmul : 2^(2*m+2)*(j+3)=2^(2*m+2)*j+3*2^(2*m+2) := by
    rw [Nat.mul_add]
    omega
  rw [hmul] at hgate
  constructor <;> omega

/-- Infinite lattice of Machine C high halting parameter candidates
excluded at all genuine blank-section times, without a finite cutoff. -/
theorem high_stop_blank_unreachable (j m k time : Nat)
    (hm : m%32=7) (hpair : (j+42)%128=(3*m)%128)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  obtain ⟨hx,hy⟩ := high_stop_bounds j m k hm hpair hgate
  obtain ⟨hs,hr⟩ := high_stop_sector j m k hm hpair hgate
  exact blank_unreachable time (2*j+3) k hx hy hs hr

#print axioms two_edges
#print axioms no_three_edges
#print axioms blank_unreachable
#print axioms high_stop_blank_unreachable
end BB6.Agent34OddThree
