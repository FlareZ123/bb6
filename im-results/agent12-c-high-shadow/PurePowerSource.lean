import PurePowerPhases
import DirectBlocksSource
import ModularConeSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12PureFan
open BB6.Agent46

/-- Rewrite the already exact source criterion into a disjoint arithmetic
    fan suitable for pure-power targets. The guard removes the exceptional
    small outputs but retains every special zero/one source. -/
theorem raw_parent_iff (a k x y : Nat) (hy : 8≤y) :
    RawParent a k x y ↔ sectionPreimageCriterion a k x y := by
  constructor
  · intro h
    rcases h with h|h|h|h|h
    · obtain ⟨hpar,ha,hk⟩ := h
      have hreg : 2*k≤a := by omega
      simp [sectionPreimageCriterion,show a≠0 by omega,show a≠1 by omega,
        show k≠0 by omega,hreg]
      omega
    · obtain ⟨rfl,hk,n,hs,hw⟩ := h
      simp [sectionPreimageCriterion,show k≠0 by omega,show k≠1 by omega]
      exact ⟨n,hs,by omega⟩
    · obtain ⟨rfl,hk,n,hs,hw⟩ := h
      simp [sectionPreimageCriterion,show k≠0 by omega,show k≠1 by omega,
        show k≠2 by omega,show k≠3 by omega]
      exact ⟨n,hs,by omega⟩
    · obtain ⟨ha,hak,hpar,n,hs,hw⟩ := h
      simp [sectionPreimageCriterion,show a≠0 by omega,show a≠1 by omega,
        show k≠0 by omega,show ¬2*k≤a by omega,hpar]
      have hs' : 2^(n+1)*(a+2)=2^n*(2*(a-1)+6) := by
        rw [Nat.pow_succ,Nat.mul_assoc]
        congr 1
        omega
      exact ⟨n,hs.trans hs',by omega⟩
    · obtain ⟨ha,hak,hpar,n,hs,hw⟩ := h
      simp [sectionPreimageCriterion,show a≠0 by omega,show a≠1 by omega,
        show k≠0 by omega,show ¬2*k≤a by omega,show a%2≠0 by omega]
      have hs' : 2^(n+1)*(a+3)=2^n*(2*(a-1)+8) := by
        rw [Nat.pow_succ,Nat.mul_assoc]
        congr 1
        omega
      exact ⟨n,hs.trans hs',by omega⟩
  · intro h
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [sectionPreimageCriterion,ha0,hk0] at h
      · by_cases hk1 : k=1
        · simp [sectionPreimageCriterion,ha0,hk0,hk1] at h
          omega
        · simp [sectionPreimageCriterion,ha0,hk0,hk1] at h
          obtain ⟨n,hs,hw⟩ := h
          exact Or.inr (Or.inl ⟨ha0,by omega,n,hs,by omega⟩)
    · by_cases ha1 : a=1
      · by_cases hk0 : k=0
        · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
        · by_cases hk1 : k=1
          · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1] at h
          · by_cases hk2 : k=2
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2] at h
              omega
            · by_cases hk3 : k=3
              · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] at h
                omega
              · simp [sectionPreimageCriterion,ha0,ha1,hk0,hk1,hk2,hk3] at h
                obtain ⟨n,hs,hw⟩ := h
                exact Or.inr (Or.inr (Or.inl ⟨ha1,by omega,n,hs,by omega⟩))
      · by_cases hk0 : k=0
        · simp [sectionPreimageCriterion,ha0,ha1,hk0] at h
        · by_cases hreg : 2*k≤a
          · simp [sectionPreimageCriterion,ha0,ha1,hk0,hreg] at h
            exact Or.inl ⟨by omega,by omega,by omega⟩
          · by_cases hpar : a%2=0
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hreg,hpar] at h
              obtain ⟨n,hs,hw⟩ := h
              have hs' : 2^n*(2*(a-1)+6)=2^(n+1)*(a+2) := by
                rw [Nat.pow_succ,Nat.mul_assoc]
                congr 1
                omega
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,hpar,n,hs.trans hs',by omega⟩)))
            · simp [sectionPreimageCriterion,ha0,ha1,hk0,hreg,hpar] at h
              obtain ⟨n,hs,hw⟩ := h
              have hs' : 2^n*(2*(a-1)+8)=2^(n+1)*(a+3) := by
                rw [Nat.pow_succ,Nat.mul_assoc]
                congr 1
                omega
              exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,by omega,by omega,n,hs.trans hs',by omega⟩)))

open BB6.Agent42ModularCone
open BB6.Agent42DirectBlocks

/-- The complete pure-power predecessor fan is an iff for the actual
    section transition, not merely an overapproximation. -/
theorem source_fan_iff (a k x y v : Nat) (hy : 8≤y) (hx : x%2=1)
    (hQ : x+y+(x+y)%2=2^v) (hv : v%2=1-(x+y)%2) :
    secNext (a,k)=some (x,y) ↔ Fan a k x y v :=
  (complete_section_inverse a k x y (by omega)).trans
    ((raw_parent_iff a k x y hy).symm.trans (fan_exact a k x y v hx hQ hv))

def bounceGuard (b m v o d : Nat) : Bool :=
  excluded b ⟨phaseA b o d,phaseK b (powResidue b (v%(2*m+2)):Int) o d ((v-1-2*d)/2)⟩

def zeroGuard (b m v : Nat) : Bool :=
  excluded b ⟨0,-((powResidue b (v%(2*m+2)):Int)+3*(v/2%2^b:Nat))⟩

/-- Exact branch-level exclusion with precision up to r+2m+2, limited only
    by the height needed by the already-certified modular cone checker. -/
theorem source_bounce_guard (b j m y v d a k : Nat) (hm : 1≤m)
    (hs : y+j+3*m+5=2^(2*m+2)*(j+3))
    (hQ : 2*j+3+y+(2*j+3+y)%2=2^v)
    (hb : b≤v%(2*m+2)+(2*m+2)) (hbv : b+4≤v)
    (hd : 1≤d) (hdv : 2*d+1≤v)
    (ha : a+2+(2*j+3+y)%2=4^d)
    (hw : 2*k+a+7+3*(v-1-2*d)=2*j+3+2*y)
    (hc : bounceGuard b m v ((2*j+3+y)%2) d=true) : ¬BB6.Agent3.CReach a k := by
  have hv := (high_pure_data j m y v hm hs hQ).2.2.2.2.1
  obtain ⟨hJ,hY⟩ := high_shift b j m y v hm hs hQ hb hbv
  have hphase := bounce_phase b j y v d a k (powResidue b (v%(2*m+2)):Int)
    hQ hv hd hdv ha hw (by omega) hJ
  have hk := (bounce_geometry j y v d a k hQ hv hd hdv ha hw).2
  apply BB6.Agent42ModularCone.source_excluded b _ hc a k
  · unfold Large P
    omega
  · exact hphase

theorem source_zero_guard (b j m y v k : Nat) (hm : 1≤m)
    (hs : y+j+3*m+5=2^(2*m+2)*(j+3))
    (hQ : 2*j+3+y+(2*j+3+y)%2=2^v)
    (hb : b≤v%(2*m+2)+(2*m+2)) (hbv : b+4≤v)
    (ho : (2*j+3+y)%2=0) (hw : 2*k+3*v=2*j+3+2*y)
    (hc : zeroGuard b m v=true) : ¬BB6.Agent3.CReach 0 k := by
  have hv := (high_pure_data j m y v hm hs hQ).2.2.2.2.1
  obtain ⟨hJ,hY⟩ := high_shift b j m y v hm hs hQ hb hbv
  have hphase := zero_phase b j y v k (powResidue b (v%(2*m+2)):Int)
    (by omega) (by omega) (by omega) hw (by omega) hJ
  apply BB6.Agent42ModularCone.source_excluded b _ hc 0 k
  · unfold Large P
    omega
  · constructor
    · simp [Matches,Cong]
    · change ((2^b:Nat):Int)∣(k:Int)-(-((powResidue b (v%(2*m+2)):Int)+3*(v/2%2^b:Nat)))
      have he : (k:Int)-(-((powResidue b (v%(2*m+2)):Int)+3*(v/2%2^b:Nat)))=(k:Int)+(powResidue b (v%(2*m+2)):Int)+3*(v/2%2^b:Nat) := by omega
      rw [he]
      exact hphase.1

/-- The direct parent of every positive-index pure-power stop is impossible
    when the rounded target is odd, so the reduced fan needs only bounce
    parents and the exceptional zero-left parent. -/
theorem source_pure_direct (j m y v a k : Nat) (hm : 1≤m)
    (hs : y+j+3*m+5=2^(2*m+2)*(j+3))
    (hQ : 2*j+3+y+(2*j+3+y)%2=2^v)
    (ho : (2*j+3+y)%2=1) (ha : a+3=2^v) (hk : 2*k+2=y) : ¬BB6.Agent3.CReach a k := by
  obtain ⟨hr,hv,hJ,hy,_,_,_,_⟩ := high_pure_data j m y v hm hs hQ
  have hr3 : 8≤2^(v%(2*m+2)) := Nat.pow_le_pow_right (by decide : 0<2) hr
  have hJ8 : 8∣j+3 := Nat.dvd_trans (Nat.pow_dvd_pow 2 hr) hJ
  have hj := Nat.mod_eq_zero_of_dvd hJ8
  exact even_pure_direct_excluded BB6.Agent3.CReach BB6.Agent42DirectBlocks.source_direct
    BB6.Agent42DirectBlocks.source_forbidden a k (2*j+3) y v (by omega) (by omega)
    (by omega) (by omega) ha hk

/-- Exact reachability reduction of every positive-index pure-power stop.
    The surviving fan excludes the impossible direct branch and all
    certificate-positive zero/bounce phases. -/
theorem source_high_pure_pruned_iff (b j m y v : Nat) (hm : 1≤m)
    (hs : y+j+3*m+5=2^(2*m+2)*(j+3))
    (hQ : 2*j+3+y+(2*j+3+y)%2=2^v)
    (hb : b≤v%(2*m+2)+(2*m+2)) (hbv : b+4≤v) :
    BB6.Agent3.CReach (2*j+3) y ↔
      ∃ a k, BB6.Agent3.CReach a k ∧ Fan a k (2*j+3) y v ∧
        (((2*j+3+y)%2=0 ∧ a=0 ∧ zeroGuard b m v=false) ∨
          ∃ d, 1≤d ∧ 2*d+1≤v ∧ a+2+(2*j+3+y)%2=4^d ∧
            bounceGuard b m v ((2*j+3+y)%2) d=false) := by
  obtain ⟨hr,hv,hJ,hy,hpar,_,_,_⟩ := high_pure_data j m y v hm hs hQ
  have hr3 : 8≤2^(v%(2*m+2)) := Nat.pow_le_pow_right (by decide : 0<2) hr
  have hy8 : 8≤y := by omega
  constructor
  · intro hreach
    obtain ⟨a,k,hreach',hp⟩ := BB6.Agent13UnifiedShadow.source_parent_of_right_ge8 (2*j+3) y hy8 hreach
    have hf := (fan_exact a k (2*j+3) y v (by omega) hQ hpar).mp ((raw_parent_iff a k (2*j+3) y hy8).mpr hp)
    refine ⟨a,k,hreach',hf,?_⟩
    rcases hf with h|h|h
    · obtain ⟨ho,ha,hk⟩ := h
      exact False.elim ((source_pure_direct j m y v a k hm hs hQ ho ha hk) hreach')
    · obtain ⟨ho,ha,_,_,hw⟩ := h
      refine Or.inl ⟨ho,ha,?_⟩
      cases hc : zeroGuard b m v with
      | false => rfl
      | true => subst a; exact False.elim ((source_zero_guard b j m y v k hm hs hQ hb hbv ho hw hc) hreach')
    · obtain ⟨d,hd,hdv,ha,hw,_⟩ := h
      refine Or.inr ⟨d,hd,hdv,ha,?_⟩
      cases hc : bounceGuard b m v ((2*j+3+y)%2) d with
      | false => rfl
      | true => exact False.elim ((source_bounce_guard b j m y v d a k hm hs hQ hb hbv hd hdv ha hw hc) hreach')
  · rintro ⟨a,k,⟨n,hn⟩,hf,_⟩
    have he := (source_fan_iff a k (2*j+3) y v hy8 (by omega) hQ hpar).mpr hf
    refine ⟨n+1,?_⟩
    simp [BB6.Agent8Section.run,hn,he]

/-- Bounded census of large-d residue phases; no huge actual counters. -/
def tailSurvivorCount (b : Nat) (J : Int) (o : Nat) : Nat :=
  ((List.range (2^b)).filter (fun (h : Nat) => !(excluded b ⟨-2-(o:Int),-(J+1+2*(o:Int)+3*(h:Int))⟩))).length

#print axioms raw_parent_iff
#print axioms source_fan_iff
#print axioms source_bounce_guard
#print axioms source_zero_guard
#print axioms source_pure_direct
#print axioms source_high_pure_pruned_iff
#eval tailSurvivorCount 12 0 0
#eval tailSurvivorCount 12 0 1
end BB6.Agent12PureFan
