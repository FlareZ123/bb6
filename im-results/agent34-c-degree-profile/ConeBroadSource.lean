import ConeBroadArithmetic
import SectionAllInverse
import Agent3CImage
import GenericSection
import Lean.Elab.Tactic.Omega

/-! Source-connected all-time Machine C halting-cylinder exclusion.
Imports the original unmodified SectionAllInverse, Agent3CImage and
FastSectionDef source graph. Compile by the manual Agent34 source workflow. -/
namespace BB6.Agent34Broad
open BB6.Agent46

/-- Transfer the separately compiled exact-grammar arithmetic to the
literal original section transition relation. -/
theorem source_parent_residue (a k x y : Nat)
    (hsum : (x+y)%64=48) (hy : y%8=3)
    (h : secNext (a,k)=some (x,y)) :
    k%2=1 ∧ (a+k)%4=1 ∧ 5≤k := by
  have hsrc := (BB6.Agent46.section_preimage_all_iff a k x y).mp h
  have hcopy : BB6.Agent34Broad.sectionPreimageAll a k x y := by
    exact hsrc
  exact all_parent_residue a k x y hsum hy hcopy

/-- No state of the cone can have two true incoming section edges,
regardless of the section source. -/
theorem no_two_edges (u v a k x y : Nat)
    (hsum : (x+y)%64=48) (hy : y%8=3)
    (hprev : secNext (u,v)=some (a,k))
    (hnext : secNext (a,k)=some (x,y)) : False := by
  obtain ⟨hk,hm,hbound⟩ := source_parent_residue a k x y hsum hy hnext
  have hh := BB6.Agent3.section_odd_image u v a k hprev hbound hk
  omega

/-- This cone is absent after any two section transitions from ANY
source. This is stronger than exclusion from the blank start. -/
theorem all_source_no_two (start : Nat×Nat) (n x y : Nat)
    (hsum : (x+y)%64=48) (hy : y%8=3) :
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
          exact no_two_edges u v a k x y hsum hy hprev hstep

/-- Every state in the cone is inaccessible at every positive or
zero blank-origin section time. -/
theorem cone_blank_unreachable (time x y : Nat)
    (hsum : (x+y)%64=48) (hy : y%8=3) :
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
            all_source_no_two (5,1) n x y hsum hy

/-- All high halting targets in the strengthened modular cylinder. -/
theorem high_stop_cone (j m k : Nat)
    (hm : m%4=1) (hpair : (j+14)%64=(3*m)%64)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ((2*j+3)+k)%64=48 ∧ k%8=3 := by
  have hm1 : 1≤m := by omega
  have hj4 : j%4=1 := by omega
  have hp16 : 16∣(2:Nat)^(2*m+2) := by
    change (2:Nat)^4 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hp16
  have hp4 : 4∣j+3 := by omega
  obtain ⟨v,hv⟩ := hp4
  have hp64 : 64∣k+j+3*m+5 := by
    refine ⟨u*v,?_⟩
    calc
      k+j+3*m+5=2^(2*m+2)*(j+3) := hgate
      _=(16*u)*(4*v) := by rw [hu,hv]
      _=64*(u*v) := by
        calc
          (16*u)*(4*v)=(16*4)*(u*v):=by ac_rfl
          _=64*(u*v):=by simp
  have hz : (k+j+3*m+5)%64=0 := Nat.mod_eq_zero_of_dvd hp64
  omega

/-- Full-time authentic blank Machine C exclusion of an infinite
source-certified high stopping input cylinder, all parameters. -/
theorem high_stop_blank_unreachable (j m k time : Nat)
    (hm : m%4=1) (hpair : (j+14)%64=(3*m)%64)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  obtain ⟨hsum,hy⟩ := high_stop_cone j m k hm hpair hgate
  exact cone_blank_unreachable time (2*j+3) k hsum hy

#print axioms source_parent_residue
#print axioms no_two_edges
#print axioms all_source_no_two
#print axioms high_stop_blank_unreachable
end BB6.Agent34Broad
