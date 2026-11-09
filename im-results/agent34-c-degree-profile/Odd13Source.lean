import ValuationOneOrbit
import OddFourExactOriginal
import Agent3CImage
import GenericSection
import Lean.Elab.Tactic.Omega

/-! Original-source, genuinely three-transition Machine C inverse cone.
This source lifts exact original proofs of valuation-one direct uniqueness,
odd-odd sum-four exact uniqueness, and odd-right missing-image congruences. -/
namespace BB6.Agent34Odd13
open BB6.Agent46

/-- The sole first predecessor in the sum-13/right-4 sector is direct. -/
theorem first_direct (a k x y : Nat)
    (hy : 36≤y) (hs : (x+y)%16=13) (hy32 : y%32=4)
    (h : secNext (a,k)=some (x,y)) :
    a=x+y-2 ∧ 2*k+2=y := by
  let u : Nat := (x+y)/4
  have hval : x+y+1=2*(2*u+1) := by
    dsimp [u]
    omega
  exact (BB6.Agent34Valuation.val1_parent_iff a k x y u
    (by omega) (Or.inr hval)).mp h

/-- The first predecessor has an odd-odd sum-four exact inverse. -/
theorem second_odd_four (a k x y : Nat)
    (hy : 36≤y) (hs : (x+y)%16=13) (hy32 : y%32=4)
    (h : secNext (a,k)=some (x,y)) :
    a%2=1 ∧ k%2=1 ∧ 5≤k ∧ (a+k)%8=4 := by
  obtain ⟨ha,hk⟩ := first_direct a k x y hy hs hy32 h
  omega

/-- The uniquely forced second predecessor has no possible predecessor,
because its odd right counter is >=5 and its sum is 1 mod 4. -/
theorem forced_second_bad (a k b l x y : Nat)
    (hy : 36≤y) (hs : (x+y)%16=13) (hy32 : y%32=4)
    (hfirst : secNext (a,k)=some (x,y))
    (hsecond : secNext (b,l)=some (a,k)) :
    5≤l ∧ l%2=1 ∧ (b+l)%4=1 := by
  obtain ⟨ha,hk⟩ := first_direct a k x y hy hs hy32 hfirst
  obtain ⟨hao,hko,hk5,hsum⟩ :=
    second_odd_four a k x y hy hs hy32 hfirst
  obtain ⟨hb,hl⟩ :=
    (BB6Agent34.section_odd_four_exact b l a k hao hko hk5 hsum).mp hsecond
  omega

/-- Three successful section transitions can never end at such a target. -/
theorem no_three_edges (u v b l a k x y : Nat)
    (hy : 36≤y) (hs : (x+y)%16=13) (hy32 : y%32=4)
    (hthird : secNext (u,v)=some (b,l))
    (hsecond : secNext (b,l)=some (a,k))
    (hfirst : secNext (a,k)=some (x,y)) : False := by
  obtain ⟨hsize,hodd,hmod⟩ :=
    forced_second_bad a k b l x y hy hs hy32 hfirst hsecond
  have himage := BB6.Agent3.section_odd_image u v b l hthird hsize hodd
  omega

theorem all_source_no_three (start : Nat×Nat) (n x y : Nat)
    (hy : 36≤y) (hs : (x+y)%16=13) (hy32 : y%32=4) :
    BB6.Agent8Section.run secNext (n+3) (some start) ≠ some (x,y) := by
  intro ht
  rw [show n+3=((n+1)+1)+1 by omega] at ht
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
          cases hr : BB6.Agent8Section.run secNext n (some start) with
          | none => simp [hr] at hq
          | some r =>
              rcases r with ⟨u,v⟩
              have hthird : secNext (u,v)=some (b,l) := by simpa [hr] using hq
              exact no_three_edges u v b l a k x y hy hs hy32 hthird hsecond hfirst

theorem blank_unreachable (time x y : Nat)
    (hy : 36≤y) (hs : (x+y)%16=13) (hy32 : y%32=4) :
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
          have he : secNext (5,1)=some (3,4) := by decide
          simp [BB6.Agent8Section.run,he] at h
          omega
      | succ n =>
          cases n with
          | zero =>
              intro h
              have he : secNext (5,1)=some (3,4) := by decide
              have hf : secNext (3,4)=some (4,7) := by
                simp [secNext,exactSection,bounce]
              simp [BB6.Agent8Section.run,he,hf] at h
              omega
          | succ n =>
              simpa only [show n+1+1+1=n+3 by omega] using
                all_source_no_three (5,1) n x y hy hs hy32

private theorem power_linear (m:Nat) : 4*m+4 ≤ (2:Nat)^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have he : 2*(m+1)+2=(2*m+2)+2 := by omega
    rw [he,Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    omega

/-- Raw stopping equation pullback: an exact 1/256 parameter lattice. -/
theorem high_sector (j m k:Nat)
    (hm8:m%8=4) (hp:(j+3*m)%32=23)
    (hgate:k+j+3*m+5=2^(2*m+2)*(j+3)) :
    36≤k ∧ ((2*j+3+k)%16=13) ∧ k%32=4 := by
  have hm:4≤m := by omega
  have hp32 : 32∣(2:Nat)^(2*m+2) := by
    change (2:Nat)^5 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hp32
  have hprod : (k+j+3*m+5)%32=0 := by
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨u*(j+3),?_⟩
    calc
      k+j+3*m+5=2^(2*m+2)*(j+3):=hgate
      _=(32*u)*(j+3):=by rw [hu]
      _=32*(u*(j+3)):=by ac_rfl
  have hbound := power_linear m
  have hpos : 1≤2^(2*m+2) := Nat.pow_pos (by decide)
  have hj : j ≤ 2^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpos
  have ht := hgate
  rw [Nat.mul_add] at ht
  constructor
  · omega
  constructor <;> omega

/-- Original machine: all genuine blank-origin returns exclude the
entire infinite family m=4 mod 8 and j+3m=23 mod 32. -/
theorem high_stop_blank_unreachable (j m k time:Nat)
    (hm8:m%8=4) (hp:(j+3*m)%32=23)
    (hgate:k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  obtain ⟨hy,hs,hy32⟩ := high_sector j m k hm8 hp hgate
  exact blank_unreachable time (2*j+3) k hy hs hy32

#print axioms first_direct
#print axioms second_odd_four
#print axioms forced_second_bad
#print axioms no_three_edges
#print axioms all_source_no_three
#print axioms blank_unreachable
#print axioms high_sector
#print axioms high_stop_blank_unreachable
end BB6.Agent34Odd13
