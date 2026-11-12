import SectionAllInverse
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11SevenForced
open BB6.Agent46

/-- If a target (x,3) has x=6 mod 8, an odd-bounce inverse depth
    must be zero: every positive depth would make x+6 divisible by 8. -/
private theorem three_depth_zero (x a n : Nat)
    (hx : x%8=6) (ha : a%2=1)
    (hpow : x+6=2^n*(2*a+6)) : n=0 := by
  cases n with
  | zero => rfl
  | succ n =>
      have h2 : 2 ∣ (2:Nat)^(n+1) := by
        refine ⟨2^n, ?_⟩
        rw [Nat.pow_succ]
        ring
      have h4 : 4 ∣ 2*a+6 := by
        refine ⟨(a+3)/2, ?_⟩
        omega
      have h8 : 8 ∣ (2:Nat)^(n+1)*(2*a+6) := by
        rcases h2 with ⟨u,hu⟩
        rcases h4 with ⟨v,hv⟩
        refine ⟨u*v, ?_⟩
        rw [hu,hv]
        ring
      have hdiv : 8 ∣ x+6 := by
        rw [hpow]
        exact h8
      have hzero : (x+6)%8=0 := Nat.mod_eq_zero_of_dvd hdiv
      omega

/-- Exact original-source inverse of every even/odd target (x,3)
    with x=6 mod 8: there is exactly one predecessor, (x/2,(x+2)/4).
    The exceptional a=1 source and every positive bounce depth are excluded. -/
theorem evenodd_three_parent_iff (a k x : Nat) (hx : x%8=6) :
    secNext (a,k)=some (x,3) ↔
      a=x/2 ∧ k=(x+2)/4 := by
  constructor
  · intro hedge
    have hp := (section_preimage_all_iff a k x 3).mp hedge
    by_cases ha0 : a=0
    · simp [sectionPreimageAll,ha0] at hp
    · by_cases ha1 : a=1
      · subst a
        by_cases hk0 : k=0
        · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        · by_cases hk1 : k=1
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp
            omega
          · by_cases hk2 : k=2
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp
            · by_cases hk3 : k=3
              · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp
              · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                    if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
                rcases hp with ⟨_,n,hpow,_⟩ | ⟨h5,_⟩
                · have hdiv : 8 ∣ x+6 := by
                    refine ⟨2^n*2, ?_⟩
                    calc
                      x+6 = 2^n*16 := hpow
                      _ = 8*(2^n*2) := by ring
                  have hzero : (x+6)%8=0 :=
                    Nat.mod_eq_zero_of_dvd hdiv
                  omega
                · omega
      · by_cases hk0 : k=0
        · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
        · by_cases hlow : 2*k≤a
          · simp [sectionPreimageAll,ha0,ha1,hk0,hlow] at hp
            omega
          · by_cases heven : a%2=0
            · simp [sectionPreimageAll,ha0,ha1,hk0,hlow,heven] at hp
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
                  if_neg hk0,if_neg hlow,if_neg heven] at hp
              rcases hp with ⟨_,n,hpow,hcost⟩ | ⟨h5,_⟩
              · have hbase : 2*(a-1)+8=2*a+6 := by omega
                rw [hbase] at hpow
                have hn := three_depth_zero x a n hx (by omega) hpow
                subst n
                have hax : x=2*a := by omega
                have hkc : 2*k=a+1 := by omega
                omega
              · omega
  · rintro ⟨rfl,rfl⟩
    have hx6 : 6≤x := by omega
    have ha : x/2%2=1 := by omega
    have hk2 : 2*((x+2)/4)=x/2+1 := by omega
    have ha0 : x/2≠0 := by omega
    have ha1 : x/2≠1 := by omega
    have hk0 : (x+2)/4≠0 := by omega
    have hlow : ¬2*((x+2)/4)≤x/2 := by omega
    have heven : ¬x/2%2=0 := by omega
    have hbase : 2*(x/2-1)+8=x+6 := by omega
    apply (section_preimage_all_iff (x/2) ((x+2)/4) x 3).mpr
    simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
      if_neg hk0,if_neg hlow,if_neg heven]
    left
    refine ⟨rfl,0,?_,?_⟩
    · simp [hbase]
    · omega

/-- The target has one genuine predecessor, so blank reachability is
    equivalent to blank reachability of that predecessor at an earlier time. -/
private theorem unique_parent_reach_iff
    (start target parent : Nat × Nat)
    (hneq : target ≠ start)
    (hedge : secNext parent=some target)
    (hunique : ∀ s, secNext s=some target → s=parent) :
    (∃ n, BB6.Agent8Section.run secNext n (some start)=some target) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some start)=some parent) := by
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero =>
        simp [BB6.Agent8Section.run] at hn
        exact False.elim (hneq hn.symm)
    | succ n =>
        cases hr : BB6.Agent8Section.run secNext n (some start) with
        | none => simp [BB6.Agent8Section.run,hr] at hn
        | some s =>
            have hs : secNext s=some target := by
              simpa [BB6.Agent8Section.run,hr] using hn
            have hp : s=parent := hunique s hs
            exact ⟨n,by simpa [hp] using hr⟩
  · rintro ⟨n,hn⟩
    exact ⟨n+1,by simp [BB6.Agent8Section.run,hn,hedge]⟩

/-- Genuine blank-root reachability iff for the new y=3 unique-parent
    sector. This is an unbounded source theorem, not a finite trace test. -/
theorem evenodd_three_blank_reach_iff (x : Nat) (hx : x%8=6) :
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (x,3)) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (x/2,(x+2)/4)) := by
  let a := x/2
  let k := (x+2)/4
  have hedge : secNext (a,k)=some (x,3) :=
    (evenodd_three_parent_iff a k x hx).mpr ⟨rfl,rfl⟩
  have hneq : (x,3) ≠ (5,1) := by
    intro h
    have hy := congrArg Prod.snd h
    omega
  have hunique : ∀ s, secNext s=some (x,3) → s=(a,k) := by
    intro s hs
    rcases s with ⟨b,c⟩
    have hbc := (evenodd_three_parent_iff b c x hx).mp hs
    simp [a,k,hbc.1,hbc.2]
  have hiff := unique_parent_reach_iff (5,1) (x,3) (a,k)
    hneq hedge hunique
  simpa [a,k] using hiff

#print axioms evenodd_three_parent_iff
#print axioms evenodd_three_blank_reach_iff

end BB6.Agent11SevenForced
