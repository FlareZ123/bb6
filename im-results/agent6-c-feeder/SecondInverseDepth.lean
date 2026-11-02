import COneFiveDepth
import BounceEvenGrammar
import BounceOddGrammar
import Lean.Elab.Tactic.Omega

namespace BB6.Agent6
open BB6.Agent3 BB6.Agent46

#check BB6Agent38.bounce_odd_four_direct
#check BB6Agent38.blank_section_no_11
#check BB6Agent38.blank_section_no_33

/-- A source-independent exact inverse arithmetic certificate for every
    EvenBack grammar branch, including arbitrary recursion depth. -/
theorem evenBack_depth_cost (x y k c : Nat) (hy : 5≤y)
    (h : EvenBack x y k c) :
    ∃ n : Nat,
      x+y+1 = 2^n*(2*k+8) ∧
      c+(2*k+8)+3*n=x+2*y+2 := by
  induction h with
  | small k hk hx hyeq => omega
  | large k hk hylarge hbd hx =>
      refine ⟨0, ?_, ?_⟩
      · simp
        omega
      · omega
  | step k c hk hc h ih =>
      obtain ⟨n,hpow,hcost⟩ := ih
      refine ⟨n+1, ?_, ?_⟩
      · rw [Nat.pow_succ]
        have hfactor : 2*(2*k+4)+8 = 2*(2*k+8) := by omega
        calc
          x+y+1 = 2^n*(2*(2*k+8)) := by rw [← hfactor]; exact hpow
          _ = (2^n*2)*(2*k+8) := by rw [Nat.mul_assoc]
      · omega

/-- The specific 2-adic family has only two possible source parity classes
    at the beginning of its genuine even-bounce inverse grammar. -/
theorem even_back_target_restricted (q kin c a k : Nat)
    (hkn : kin%2=0) (hc : c%2=0)
    (h : EvenBack (24*(16*q+4)) (20*(16*q+4)-1) kin c)
    (ha : a=kin+1) (hrelation : c+a=2*k+3) :
    (a%4=1 ∧ k%4=1) ∨ (a%4=3 ∧ k%4=3) := by
  have hy : 5≤20*(16*q+4)-1 := by omega
  obtain ⟨n,hpow,hcost⟩ := evenBack_depth_cost _ _ _ _ hy h
  have hformula : 44*(16*q+4) = 2^n*(2*kin+8) := by omega
  have hcost2 : c+(2*kin+8)+3*n=64*(16*q+4) := by omega
  have hn2 : n≤2 := by
    by_cases hn : n≤2
    · exact hn
    have hp8 : 8 ∣ 2^n := by
      change 2^3 ∣ 2^n
      exact Nat.pow_dvd_pow 2 (by omega)
    have hk4 : 4 ∣ 2*kin+8 := by
      refine ⟨kin/2+2,?_⟩
      omega
    obtain ⟨u,hu⟩ := hp8
    obtain ⟨v,hv⟩ := hk4
    have hd32 : 32 ∣ 2^n*(2*kin+8) := by
      refine ⟨u*v,?_⟩
      rw [hu,hv]
      calc
        (8*u)*(4*v) = (8*4)*(u*v) := by ac_rfl
        _ = 32*(u*v) := by rfl
    have hmod : (44*(16*q+4))%32=0 := by
      rw [hformula]
      exact Nat.mod_eq_zero_of_dvd hd32
    omega
  have hneven : n%2=0 := by omega
  have hh : n=0 ∨ n=2 := by omega
  rcases hh with h0 | h2
  · rw [h0] at hformula hcost2
    simp at hformula
    left
    omega
  · rw [h2] at hformula hcost2
    have heq : (2:Nat)^2=4 := by decide
    rw [heq] at hformula
    right
    omega


/-- Odd-bounce grammar outputs always have even sum, at arbitrary depth. -/
theorem oddBack_sum_even (x y k c : Nat) (h : OddBack x y k c) :
    (x+y)%2=0 := by
  induction h with
  | terminal k hk hy hbd hx => omega
  | step k c hk hc h ih => exact ih

/-- The entire affine image family has *only* globally forbidden
    modulo-four predecessor classes. The proof uses the original exact
    section definition and the complete genuine odd/even bounce grammars. -/
theorem section_twostep_target_parent_residues (q a k : Nat)
    (h : secNext (a,k)=some (24*(16*q+4),20*(16*q+4)-1)) :
    (a%4=1 ∧ k%4=1) ∨ (a%4=3 ∧ k%4=3) := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
      · have hb : (bounce 1 (2*k+1)).2=some (24*(16*q+4),20*(16*q+4)-1) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have hodd : OddBack (24*(16*q+4)) (20*(16*q+4)-1) 1 (2*k+1) :=
          (oddBack_iff_bounce _ _ _ _ (by decide)).mpr hb
        have hsum := oddBack_sum_even _ _ _ _ hodd
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
          omega
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
            omega
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
            · have hb : (bounce 4 (2*k-3)).2=some (24*(16*q+4),20*(16*q+4)-1) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              have heven : EvenBack (24*(16*q+4)) (20*(16*q+4)-1) 4 (2*k-3) :=
                (evenBack_iff_bounce _ _ _ _ (by decide)).mpr hb
              obtain ⟨n,hpow,_⟩ := evenBack_depth_cost _ _ _ _ (by omega) heven
              have hformula : 44*(16*q+4) = 2^n*16 := by omega
              cases n with
              | zero => simp at hformula; omega
              | succ n =>
                  rw [Nat.pow_succ] at hformula
                  omega
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (24*(16*q+4),20*(16*q+4)-1) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          by_cases hodd : (a-1)%2=1
          · have ho : OddBack (24*(16*q+4)) (20*(16*q+4)-1) (a-1) (2*k-a+3) :=
              (oddBack_iff_bounce _ _ _ _ hodd).mpr hb
            have hsum := oddBack_sum_even _ _ _ _ ho
            omega
          · have heven : (a-1)%2=0 := by omega
            have hback : EvenBack (24*(16*q+4)) (20*(16*q+4)-1) (a-1) (2*k-a+3) :=
              (evenBack_iff_bounce _ _ _ _ heven).mpr hb
            have hc : (2*k-a+3)%2=0 := by omega
            have ha : a=(a-1)+1 := by omega
            have hrel : (2*k-a+3)+a=2*k+3 := by omega
            exact even_back_target_restricted q (a-1) (2*k-a+3) a k heven hc hback ha hrel


/-- The authentic blank section never visits the entire affine feeder-line
    that can precede the new 128q+33 family. -/
theorem blank_no_twostep_target_line (q : Nat) :
    ¬ CReach (24*(16*q+4)) (20*(16*q+4)-1) := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
      omega
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
          rcases p with ⟨a,k⟩
          have ht : secNext (a,k)=some (24*(16*q+4),20*(16*q+4)-1) := by
            simpa [BB6.Agent8Section.run,hp] using hr
          have hres := section_twostep_target_parent_residues q a k ht
          have hodd : k%2=1 := by
            rcases hres with ⟨_,hk⟩ | ⟨_,hk⟩ <;> omega
          have hsum : (a+k)%4=2 := by
            rcases hres with ⟨ha,hk⟩ | ⟨ha,hk⟩ <;> omega
          have he := BB6Agent38.blank_section_mod4 t a k hp hodd hsum
          have ha5 : a=5 := (Prod.mk.inj he).1
          have hk1 : k=1 := (Prod.mk.inj he).2
          have hbase : secNext (5,1)=some (3,4) := by decide
          have hh : secNext (5,1)=some (24*(16*q+4),20*(16*q+4)-1) := by
            simpa only [ha5,hk1] using ht
          rw [hbase] at hh
          omega

#print axioms blank_no_twostep_target_line

#print axioms oddBack_sum_even
#print axioms section_twostep_target_parent_residues

#print axioms evenBack_depth_cost
#print axioms even_back_target_restricted

end BB6.Agent6
