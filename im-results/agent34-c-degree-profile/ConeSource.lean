import ConeArithmetic
import SectionAllInverse
import Agent3CImage
import GenericSection
import Lean.Elab.Tactic.Omega

/-! Source-connected all-time Machine C halting-cylinder exclusion.
Imports the original unmodified SectionAllInverse, Agent3CImage and
FastSectionDef source graph. Compile by the manual Agent34 source workflow. -/
namespace BB6.Agent34Cone
open BB6.Agent46

/-- Transfer the separately compiled exact-grammar arithmetic to the
literal original section transition relation. -/
theorem source_parent_residue (a k x y : Nat)
    (hx : x%64=5) (hy : y%64=43)
    (h : secNext (a,k)=some (x,y)) :
    k%2=1 ∧ (a+k)%4=1 ∧ 5≤k := by
  have hsrc := (BB6.Agent46.section_preimage_all_iff a k x y).mp h
  have hcopy : BB6.Agent34Cone.sectionPreimageAll a k x y := by
    exact hsrc
  exact all_parent_residue a k x y hx hy hcopy

/-- No state of the cone can have two true incoming section edges,
regardless of the section source. -/
theorem no_two_edges (u v a k x y : Nat)
    (hx : x%64=5) (hy : y%64=43)
    (hprev : secNext (u,v)=some (a,k))
    (hnext : secNext (a,k)=some (x,y)) : False := by
  obtain ⟨hk,hm,hbound⟩ := source_parent_residue a k x y hx hy hnext
  have hh := BB6.Agent3.section_odd_image u v a k hprev hbound hk
  omega

/-- This cone is absent after any two section transitions from ANY
source. This is stronger than exclusion from the blank start. -/
theorem all_source_no_two (start : Nat×Nat) (n x y : Nat)
    (hx : x%64=5) (hy : y%64=43) :
    BB6.Agent8Section.run secNext (n+2) (some start) ≠ some (x,y) := by
  intro ht
  rw [show n+2=(n+1)+1 by omega] at ht
  change (BB6.Agent8Section.run secNext (n+1) (some start)).bind secNext =
    some (x,y) at ht
  cases hp : BB6.Agent8Section.run secNext (n+1) (some start) with
  | none => simp [hp] at ht
  | some p =>
      rcases p with ⟨a,k⟩
      have hstep : secNext (a,k)=some (x,y) := by
        simpa [hp] using ht
      change (BB6.Agent8Section.run secNext n (some start)).bind secNext =
        some (a,k) at hp
      cases hr : BB6.Agent8Section.run secNext n (some start) with
      | none => simp [hr] at hp
      | some r =>
          rcases r with ⟨u,v⟩
          have hprev : secNext (u,v)=some (a,k) := by
            simpa [hr] using hp
          exact no_two_edges u v a k x y hx hy hprev hstep

/-- Every state in the cone is inaccessible at every positive or
zero blank-origin section time. -/
theorem cone_blank_unreachable (time x y : Nat)
    (hx : x%64=5) (hy : y%64=43) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  cases time with
  | zero =>
      intro ht
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      cases n with
      | zero =>
          intro ht
          have hfirst : BB6.Agent8Section.run secNext 1 (some (5,1)) =
              some (3,4) := by
            have hstep : secNext (5,1)=some (3,4) := by decide
            simpa [BB6.Agent8Section.run] using hstep
          rw [hfirst] at ht
          have heq := Option.some.inj ht
          have hx' := congrArg Prod.snd heq
          omega
      | succ n =>
          simpa only [show n+1+1=n+2 by omega] using
            all_source_no_two (5,1) n x y hx hy

/-- The genuine high-stopping parametrization enters exactly this
two-step impossible rectangle whenever j=1 and m=5 modulo 64. -/
theorem high_stop_cone (j m k : Nat)
    (hj : j%64=1) (hm : m%64=5)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (2*j+3)%64=5 ∧ k%64=43 := by
  have hm5 : 5≤m := by omega
  have hpow : 64 ∣ (2:Nat)^(2*m+2) := by
    change (2:Nat)^6 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hpow
  have hdiv : 64 ∣ k+j+3*m+5 := by
    refine ⟨u*(j+3),?_⟩
    calc
      k+j+3*m+5=2^(2*m+2)*(j+3) := hgate
      _=(64*u)*(j+3) := by rw [hu]
      _=64*(u*(j+3)) := by ac_rfl
  have hz : (k+j+3*m+5)%64=0 := Nat.mod_eq_zero_of_dvd hdiv
  omega

/-- Full-time authentic blank Machine C exclusion of an infinite
source-certified high stopping input cylinder, all parameters. -/
theorem high_stop_blank_unreachable (j m k time : Nat)
    (hj : j%64=1) (hm : m%64=5)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  obtain ⟨hx,hy⟩ := high_stop_cone j m k hj hm hgate
  exact cone_blank_unreachable time (2*j+3) k hx hy

#print axioms source_parent_residue
#print axioms no_two_edges
#print axioms all_source_no_two
#print axioms high_stop_blank_unreachable
end BB6.Agent34Cone
