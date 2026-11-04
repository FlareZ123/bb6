import SectionAllInverse
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A four-divisible bounce mass cannot arise after a positive number of
    doubling recursions when the target mass has exact 2-adic valuation 2. -/
private theorem evenodd_four_depth_zero (x y n b : Nat)
    (hmod : (x+y+1)%8=4) (hb : 4∣b)
    (hpow : x+y+1=2^n*b) : n=0 := by
  cases n with
  | zero => rfl
  | succ n =>
      obtain ⟨v,hv⟩ := hb
      have hd : 8∣x+y+1 := by
        refine ⟨2^n*v,?_⟩
        calc
          x+y+1=2^(n+1)*b := hpow
          _=(2^n*2)*(4*v) := by rw [Nat.pow_succ,hv]
          _=8*(2^n*v) := by
            change (2^n*2)*(4*v)=(2*4)*(2^n*v)
            ac_rfl
      omega

/-- Universal original section inverse for even first / odd second outputs
    with (x+y+1) mod 8 = 4: exactly one actual source, from the terminal
    even-bounce branch, including all large and exceptional cases. -/
theorem evenodd_four_parent_iff (a k x y : Nat)
    (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (hmod : (x+y+1)%8=4) :
    secNext (a,k)=some (x,y) ↔
      x+y=2*a+5 ∧ x+3*y=4*k+9 := by
  constructor
  · intro hedge
    have hp := (section_preimage_all_iff a k x y).mp hedge
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,hk0] at hp
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
          omega
        · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at hp
          obtain ⟨_,n,hpow,_⟩ := hp
          have heven : 2∣x+y := by
            refine ⟨2^n*4,?_⟩
            calc
              x+y=2^n*8 := hpow
              _=2*(2^n*4) := by
                change 2^n*(2*4)=2*(2^n*4)
                ac_rfl
          omega
    · by_cases ha1 : a=1
      · by_cases hk0 : k=0
        · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
          omega
        · by_cases hk1 : k=1
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp
            omega
          · by_cases hk2 : k=2
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp
              omega
            · by_cases hk3 : k=3
              · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp
                omega
              · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                  if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at hp
                rcases hp with ⟨h3,_⟩ | ⟨_,n,hpow,_⟩
                · omega
                · have hd : 8∣x+y+1 := by
                    refine ⟨2^n*2,?_⟩
                    calc
                      x+y+1=2^n*16 := hpow
                      _=8*(2^n*2) := by
                        change 2^n*(8*2)=8*(2^n*2)
                        ac_rfl
                  omega
      · by_cases hk0 : k=0
        · simp [sectionPreimageAll,ha0,ha1,hk0] at hp
          omega
        · by_cases hlow : 2*k≤a
          · simp [sectionPreimageAll,ha0,ha1,hk0,hlow] at hp
            omega
          · by_cases heven : a%2=0
            · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
                if_neg hk0,if_neg hlow,if_pos heven] at hp
              obtain ⟨_,n,hpow,_⟩ := hp
              have htwo : 2∣x+y := by
                refine ⟨2^n*((a-1)+3),?_⟩
                calc
                  x+y=2^n*(2*(a-1)+6) := hpow
                  _=2*(2^n*((a-1)+3)) := by
                    have hz : 2*(a-1)+6=2*((a-1)+3) := by omega
                    rw [hz]
                    ac_rfl
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
                if_neg hk0,if_neg hlow,if_neg heven] at hp
              rcases hp with ⟨h3,_⟩ | ⟨_,n,hpow,hcost⟩
              · omega
              · have hbase : 4∣2*(a-1)+8 := by
                  refine ⟨(a-1)/2+2,?_⟩
                  omega
                have hn0 := evenodd_four_depth_zero x y n _ hmod hbase hpow
                subst n
                simp at hpow hcost
                omega
  · rintro ⟨hsum,hcost⟩
    have hsize : 11≤x+y := by omega
    have ha0 : a≠0 := by omega
    have ha1 : a≠1 := by omega
    have hk0 : k≠0 := by omega
    have hlow : ¬2*k≤a := by omega
    have hodd : a%2≠0 := by omega
    apply (section_preimage_all_iff a k x y).mpr
    simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_neg hodd]
    right
    refine ⟨hy5,0,?_,?_⟩ <;> simp <;> omega

/-- Every output in this entire infinite val-2 even/odd sector has exactly
    one actual original section predecessor. -/
theorem evenodd_four_unique_parent (x y : Nat)
    (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (hmod : (x+y+1)%8=4) :
    ∃ a k, secNext (a,k)=some (x,y) ∧
      ∀ b c, secNext (b,c)=some (x,y) → b=a ∧ c=k := by
  let a := (x+y-5)/2
  let k := (x+3*y-9)/4
  have hsum : x+y=2*a+5 := by dsimp [a]; omega
  have hcost : x+3*y=4*k+9 := by dsimp [k]; omega
  have hedge : secNext (a,k)=some (x,y) :=
    (evenodd_four_parent_iff a k x y hx hy hy5 hmod).mpr ⟨hsum,hcost⟩
  refine ⟨a,k,hedge,?_⟩
  intro b c hbc
  have hh := (evenodd_four_parent_iff b c x y hx hy hy5 hmod).mp hbc
  omega

/-- A generic deterministic predecessor lift, valid for an arbitrary fixed
    starting section when the target differs from the start. -/
private theorem unique_predecessor_reach_iff
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
            have hparent : s=parent := hunique s hs
            exact ⟨n,by simpa [hparent] using hr⟩
  · rintro ⟨n,hn⟩
    exact ⟨n+1,by simp [BB6.Agent8Section.run,hn,hedge]⟩

/-- The entire even/odd valuation-two output quadrant is truly blank-reached
    if and only if its forced parent is. The result is unbounded in time. -/
theorem evenodd_four_blank_reach_iff (x y : Nat)
    (hx : x%2=0) (hy : y%2=1) (hy5 : 5≤y)
    (hmod : (x+y+1)%8=4) :
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some ((x+y-5)/2,(x+3*y-9)/4)) := by
  obtain ⟨a,k,hedge,hun⟩ := evenodd_four_unique_parent x y hx hy hy5 hmod
  have ha : a=(x+y-5)/2 := by
    have hh := (evenodd_four_parent_iff a k x y hx hy hy5 hmod).mp hedge
    omega
  have hk : k=(x+3*y-9)/4 := by
    have hh := (evenodd_four_parent_iff a k x y hx hy hy5 hmod).mp hedge
    omega
  have hneq : (x,y) ≠ (5,1) := by intro hh; have h:=congrArg Prod.snd hh; omega
  have hiff := unique_predecessor_reach_iff (5,1) (x,y) (a,k)
    hneq hedge (by intro s hs; rcases s with ⟨b,c⟩; obtain ⟨h1,h2⟩ := hun b c hs; simp [h1,h2])
  simpa only [ha,hk] using hiff

#print axioms evenodd_four_parent_iff
#print axioms evenodd_four_unique_parent
#print axioms evenodd_four_blank_reach_iff
end BB6.Agent3
