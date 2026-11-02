import CSourceBridge8
import Mod8SevenFour
import Mod16First
import NormalizedGateway
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

/-- Every point on the exact two-counter blank section is a genuine
    reachable point of the unchanged original three-counter CLine map. -/
private theorem line_reach_of_run (n : Nat) :
    ∀ {s t : Nat × Nat × Nat},
      BB6CLine.Reach s →
      BB6.Agent8Section.run BB6CLine.nextC n (some s) = some t →
      BB6CLine.Reach t := by
  induction n with
  | zero =>
      intro s t hs hr
      have hst : s=t := by
        simpa [BB6.Agent8Section.run] using hr
      subst t
      exact hs
  | succ n ih =>
      intro s t hs hr
      change
        (BB6.Agent8Section.run BB6CLine.nextC n (some s)).bind
          BB6CLine.nextC = some t at hr
      cases hp : BB6.Agent8Section.run BB6CLine.nextC n (some s) with
      | none =>
          simp [hp] at hr
      | some u =>
          have hu : BB6CLine.Reach u := ih hs hp
          have hstep : BB6CLine.nextC u = some t := by
            simpa [hp] using hr
          exact BB6CLine.Reach.next u t hu hstep

/-- The Agent 46 exact section-return simulation transports every
    Agent 15 section-reachable pair into the original CLine reachability
    relation, preserving the full blank-origin start. -/
theorem section_reach_embeds {a k : Nat} (h : CReach a k) :
    BB6CLine.Reach (a,k,0) := by
  rcases h with ⟨n,hn⟩
  have hstart : BB6CLine.Reach (5,1,0) := by
    exact BB6CLine.Reach.next (5,0,1) (5,1,0)
      BB6CLine.Reach.init (by decide)
  have aux : ∀ n a k,
      BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) = some (a,k) →
      BB6CLine.Reach (a,k,0) := by
    intro n
    induction n with
    | zero =>
        intro a k hr
        simp only [BB6.Agent8Section.run, Option.some.injEq, Prod.mk.injEq] at hr
        rcases hr with ⟨ha,hk⟩
        subst a
        subst k
        exact hstart
    | succ n ih =>
        intro a k hr
        change
          (BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1))).bind
            BB6.Agent46.secNext = some (a,k) at hr
        cases hp : BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) with
        | none =>
            simp [hp] at hr
        | some p =>
            have hprev : BB6CLine.Reach (p.1,p.2,0) :=
              ih p.1 p.2 hp
            have hstep : BB6.Agent46.secNext p = some (a,k) := by
              simpa [hp] using hr
            have hexact := BB6.Agent46.section_exact p.1 p.2
            rw [hstep] at hexact
            have hrun :
                BB6.Agent8Section.run BB6CLine.nextC
                  (BB6.Agent46.secTime p) (some (p.1,p.2,0)) =
                  some (a,k,0) := by
              rw [BB6.Agent46.run_eq] at hexact
              simpa [BB6.Agent46.embed0] using hexact
            exact line_reach_of_run (BB6.Agent46.secTime p) hprev hrun
  exact aux n a k hn

/-- The M8 (7,4) cylinder is excluded in the exact blank section. -/
theorem blank_no_m8_cylinder (u v : Nat) :
    ¬ CReach (8*u+7) (8*v+4) := by
  intro h
  exact CCert.published_no_seven_four u v (section_reach_embeds h)

/-- The M16 (1,2) cylinder is excluded in the exact blank section. -/
theorem blank_no_m16_one_two_cylinder (u v : Nat) :
    ¬ CReach (8*u+1) (16*v+2) := by
  intro h
  exact CCert16.published_no_one_two u v (section_reach_embeds h)

/-- The M16 (9,15) cylinder is excluded in the exact blank section. -/
theorem blank_no_m16_nine_fifteen_cylinder (u v : Nat) :
    ¬ CReach (16*u+9) (16*v+15) := by
  intro h
  exact CCert16.published_no_nine_fifteen u v (section_reach_embeds h)

/-- The M16 (1,7) cylinder is excluded except for its explicit base point. -/
theorem blank_no_m16_one_seven_cylinder (u v : Nat)
    (hpos : 0<u ∨ 0<v) :
    ¬ CReach (16*u+1) (16*v+7) := by
  intro h
  exact CCert16.published_no_one_seven_except u v hpos (section_reach_embeds h)

/-- The M8 forbidden cylinder pulls back through the exact all-input
    affine predecessor theorem to another infinite section cylinder. -/
theorem blank_no_m8_affine_cylinder (u v : Nat) :
    ¬ CReach (8*u+7) (16*v+10) := by
  intro h
  have hpreRaw := (blank_reach_iff_affine (8*u+7) (16*v+10)
    (by omega) (by omega) (by omega)).mp h
  have hfirst : (8*u+7)+(16*v+10)-2 = 8*u+16*v+15 := by omega
  have hsecond : (16*v+10-2)/2 = 8*v+4 := by omega
  rw [hfirst,hsecond] at hpreRaw
  have hpre : CReach (8*u+16*v+15) (8*v+4) := hpreRaw
  have hline := section_reach_embeds hpre
  apply CCert.published_no_seven_four (u+2*v+1) v
  have hfirst : 8*(u+2*v+1)+7 = 8*u+16*v+15 := by omega
  rw [hfirst]
  exact hline

/-- The two M8 odd-first-counter stopping-parameter cylinders are
    excluded in Agent 15's exact blank section semantics. -/
theorem blank_no_m8_odd_halting_parameter_pair
    (j m k : Nat)
    (hj : (j%8=2 ∧ m%8=7) ∨ (j%8=6 ∧ m%8=3))
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ CReach (2*j+3) k := by
  intro h
  exact CCert.published_no_odd_halting_parameter_pair j m k hj hk
    (section_reach_embeds h)

/-- Four additional M8 parameter classes reduce by the exact affine
    predecessor to the forbidden (8u+7,8v+4,0) cylinder. -/
theorem blank_no_m8_affine_halting_parameter_pair
    (j m k : Nat)
    (hj :
      (j%16=2 ∧ m%16=5) ∨
      (j%16=6 ∧ m%16=9) ∨
      (j%16=10 ∧ m%16=13) ∨
      (j%16=14 ∧ m%16=1))
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ CReach (2*j+3) k := by
  have hmpos : 0<m := by
    rcases hj with h|h|h|h <;> omega
  have hpow : 16 ∣ 2^(2*m+2) := by
    obtain ⟨r,hr⟩ : ∃ r, 2*m+2=4+r := ⟨2*m-2,by omega⟩
    rw [hr,Nat.pow_add]
    change 16 ∣ 16*2^r
    exact ⟨2^r,rfl⟩
  have hproduct : 16 ∣ 2^(2*m+2)*(j+3) := by
    rcases hpow with ⟨z,hz⟩
    refine ⟨z*(j+3),?_⟩
    rw [hz]
    simp only [Nat.mul_assoc]
  have hmod : (k+j+3*m+5)%16=0 := by
    rw [hk]
    exact Nat.mod_eq_zero_of_dvd hproduct
  have hj4 : j%4=2 := by
    rcases hj with h|h|h|h <;> omega
  have hk16 : k%16=10 := by
    rcases hj with h|h|h|h <;> omega
  have ha : 2*j+3=8*(j/4)+7 := by omega
  have hK : k=16*(k/16)+10 := by omega
  intro hreach
  rw [ha,hK] at hreach
  exact blank_no_m8_affine_cylinder (j/4) (k/16) hreach

/-- Agent 41's source-verified M16 even/odd stopping classes, transported
    to the exact Agent 15 blank section. -/
theorem blank_no_m16_even_odd_halt_params
    (j m k : Nat) (hj : j%4=3) (hmj : (m+1)%16=j%16)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ CReach (2*j+3) k := by
  intro h
  exact CCert16.published_no_even_odd_halt_params j m k hj hmj hk
    (section_reach_embeds h)

/-- Agent 41's source-verified M16 (9,15) stopping classes, transported
    to the exact Agent 15 blank section. -/
theorem blank_no_m16_nine_fifteen_halt_params
    (j m k : Nat) (hj : j%8=3) (hmj : m%16=j%16)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ CReach (2*j+3) k := by
  intro h
  exact CCert16.published_no_nine_fifteen_halt_params j m k hj hmj hk
    (section_reach_embeds h)

/-- Agent 41's source-verified M16 (1,7) stopping classes, transported
    to the exact Agent 15 blank section. -/
theorem blank_no_m16_one_seven_halt_params
    (j m k : Nat) (hj : j%8=7) (hmj : (m+8)%16=j%16)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ CReach (2*j+3) k := by
  intro h
  exact CCert16.published_no_one_seven_halt_params j m k hj hmj hk
    (section_reach_embeds h)

/-- Agent 41's two source-verified M16 first-family stopping classes,
    transported to the exact Agent 15 blank section. -/
theorem blank_no_m16_first_halt_m7_or_14
    (m k : Nat) (hm : m%16=7 ∨ m%16=14)
    (hk : k+3*m+4=2^(2*m+3)) :
    ¬ CReach 1 k := by
  intro h
  exact CCert16.published_no_first_halt_m7_or_14 m k hm hk
    (section_reach_embeds h)

#print axioms section_reach_embeds
#print axioms blank_no_m8_affine_cylinder
#print axioms blank_no_m8_odd_halting_parameter_pair
#print axioms blank_no_m8_affine_halting_parameter_pair
#print axioms blank_no_m16_even_odd_halt_params
#print axioms blank_no_m16_nine_fifteen_halt_params
#print axioms blank_no_m16_one_seven_halt_params
#print axioms blank_no_m16_first_halt_m7_or_14

end BB6.Agent15
