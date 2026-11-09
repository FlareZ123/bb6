import SectionAllInverse
import Std
import Lean.Elab.Tactic.Omega
namespace BB6.Agent4Seven
open BB6.Agent46

private theorem base4_odd (a : Nat) (ha : a%2=1) :
    4 ∣ 2*(a-1)+8 := by
  refine ⟨(a-1)/2+2,?_⟩
  omega

private theorem base4_even (a : Nat) (ha : a%2=0) (hpos : 2≤a) :
    4 ∣ 2*(a-1)+6 := by
  refine ⟨a/2+1,?_⟩
  omega

private theorem powodd_bound (a n q : Nat) (ha : a%2=1)
    (hq : q%128=64)
    (hp : q=(2:Nat)^n*(2*(a-1)+8)) : n≤4 := by
  by_cases hn : n≤4
  · exact hn
  have hn5 : 5≤n := by omega
  have hpow : 32∣(2:Nat)^n := Nat.pow_dvd_pow 2 hn5
  have hbase := base4_odd a ha
  obtain ⟨v,hv⟩ := hpow
  obtain ⟨z,hz⟩ := hbase
  have hdiv : 128∣q := by
    refine ⟨v*z,?_⟩
    calc
      q = (2:Nat)^n*(2*(a-1)+8) := hp
      _ = (32*v)*(4*z) := by rw [←hv,←hz]
      _ = 128*(v*z) := by
        simp only [show (128:Nat)=32*4 by decide]
        ac_rfl
  have hzmod : q%128=0 := Nat.mod_eq_zero_of_dvd hdiv
  omega

private theorem poweven_bound (a n q : Nat) (ha : a%2=0) (hpos : 2≤a)
    (hq : q%32=16)
    (hp : q=(2:Nat)^n*(2*(a-1)+6)) : n≤2 := by
  by_cases hn : n≤2
  · exact hn
  have hn3 : 3≤n := by omega
  have hpow : 8∣(2:Nat)^n := Nat.pow_dvd_pow 2 hn3
  have hbase := base4_even a ha hpos
  obtain ⟨v,hv⟩ := hpow
  obtain ⟨z,hz⟩ := hbase
  have hdiv : 32∣q := by
    refine ⟨v*z,?_⟩
    calc
      q = (2:Nat)^n*(2*(a-1)+6) := hp
      _ = (8*v)*(4*z) := by rw [←hv,←hz]
      _ = 32*(v*z) := by
        simp only [show (32:Nat)=8*4 by decide]
        ac_rfl
  have hzmod : q%32=0 := Nat.mod_eq_zero_of_dvd hdiv
  omega

/-- Exact three source parents of the candidate sixth-seventh image band. -/
theorem target_three_parents (a k u v : Nat)
    (h : sectionPreimageAll a k (641+1024*u) (574+1024*v)) :
    (a=1213+1024*u+1024*v ∧ k=286+512*v) ∨
    (a=301+256*u+256*v ∧ k=739+384*u+896*v) ∨
    (a=73+64*u+64*v ∧ k=850+480*u+992*v) := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at h <;> omega
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at h <;> omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at h
        obtain ⟨_,n,hs,_⟩ := h
        have hd : 8 ∣ 641+1024*u+574+1024*v := by
          refine ⟨(2:Nat)^n,?_⟩
          omega
        have hm := Nat.mod_eq_zero_of_dvd hd
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h <;> omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at h <;> omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at h <;> omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at h <;> omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with h3 | ⟨_,n,hs,_⟩
              · omega
              · have hn : n≤2 := by
                  by_cases hnn : n≤2
                  · exact hnn
                  have hn3 : 3≤n := by omega
                  have hp : 8∣(2:Nat)^n := Nat.pow_dvd_pow 2 hn3
                  obtain ⟨z,hz⟩ := hp
                  have hd : 128∣641+1024*u+574+1024*v+1 := by
                    refine ⟨z,?_⟩
                    calc
                      641+1024*u+574+1024*v+1=(2:Nat)^n*16 := by omega
                      _=(8*z)*16 := by rw [←hz]
                      _=128*z := by omega
                  have hm := Nat.mod_eq_zero_of_dvd hd
                  omega
                rcases (show n=0 ∨ n=1 ∨ n=2 by omega) with hz|h1|h2
                · subst n; simp at hs; omega
                · subst n; simp at hs; omega
                · subst n; simp only [show (2:Nat)^2=4 by decide] at hs; omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h <;> omega
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
            if_neg hk0,if_pos hlow] at h
          left
          omega
        · by_cases haeven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos haeven] at h
            obtain ⟨_,n,hs,_⟩ := h
            have hd : 2∣641+1024*u+574+1024*v := by
              refine ⟨(2:Nat)^n*((a-1)+3),?_⟩
              calc
                641+1024*u+574+1024*v=(2:Nat)^n*(2*(a-1)+6) := by omega
                _=(2:Nat)^n*(2*((a-1)+3)) := by congr 1
                _=2*((2:Nat)^n*((a-1)+3)) := by ac_rfl
            have hm := Nat.mod_eq_zero_of_dvd hd
            omega
          · have haodd : a%2=1 := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
                if_neg hk0,if_neg hlow,if_neg haeven] at h
            rcases h with ⟨h3,_⟩ | ⟨_,n,hs,hc⟩
            · omega
            · have hn : n≤4 := powodd_bound a n _ haodd (by omega) hs
              have hnodd : n%2=1 := by omega
              have hn13 : n=1 ∨ n=3 := by omega
              rcases hn13 with hn1|hn3
              · subst n
                simp only [Nat.pow_one] at hs
                right; left; omega
              · subst n
                simp only [show (2:Nat)^3=8 by decide] at hs
                right; right; omega

/-- Two exact source parents of the high odd-right branch. -/
theorem high_one_two_parents (a k u v : Nat)
    (h : sectionPreimageAll a k (301+256*u+256*v) (739+384*u+896*v)) :
    (a=518+320*u+576*v ∧ k=627+352*u+736*v) ∨
    (a=128+80*u+144*v ∧ k=819+472*u+952*v) := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at h <;> omega
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at h <;> omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at h
        obtain ⟨_,n,hs,_⟩ := h
        have hn : n≤1 := by
          by_cases hn : n≤1
          · exact hn
          have hp : 4∣(2:Nat)^n := by
            change (2:Nat)^2∣2^n
            exact Nat.pow_dvd_pow 2 (by omega)
          obtain ⟨z,hz⟩ := hp
          have hd : 32∣301+256*u+256*v+739+384*u+896*v := by
            refine ⟨z,?_⟩
            calc
              301+256*u+256*v+739+384*u+896*v=(2:Nat)^n*8 := by omega
              _=(4*z)*8 := by rw [←hz]
              _=32*z := by omega
          have hm := Nat.mod_eq_zero_of_dvd hd
          omega
        rcases (show n=0 ∨ n=1 by omega) with hz|h1
        · subst n; simp at hs; omega
        · subst n; simp at hs; omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h <;> omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at h <;> omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at h <;> omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at h <;> omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with h3 | ⟨_,n,hs,_⟩
              · omega
              · have hd : 2∣301+256*u+256*v+739+384*u+896*v+1 := by
                  refine ⟨(2:Nat)^n*8,?_⟩
                  calc
                    301+256*u+256*v+739+384*u+896*v+1=(2:Nat)^n*16 := by omega
                    _=2*((2:Nat)^n*8) := by omega
                have hm := Nat.mod_eq_zero_of_dvd hd
                omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h <;> omega
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
            if_neg hk0,if_pos hlow] at h
          omega
        · by_cases haeven : a%2=0
          · have ha2 : 2≤a := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos haeven] at h
            obtain ⟨_,n,hs,hc⟩ := h
            have hn : n≤2 := poweven_bound a n _ haeven ha2 (by omega) hs
            have hn_even : n%2=0 := by omega
            have hn02 : n=0 ∨ n=2 := by omega
            rcases hn02 with hn0|hn2
            · subst n
              simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_zero,
                Nat.add_zero] at hs hc
              left; omega
            · subst n
              simp only [show (2:Nat)^2=4 by decide] at hs
              right; omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at h
            rcases h with ⟨h3,_⟩ | ⟨_,n,hs,_⟩
            · omega
            · have hd : 2∣301+256*u+256*v+739+384*u+896*v+1 := by
                refine ⟨(2:Nat)^n*((a-1)+4),?_⟩
                calc
                  301+256*u+256*v+739+384*u+896*v+1=(2:Nat)^n*(2*(a-1)+8) := by omega
                  _=(2:Nat)^n*(2*((a-1)+4)) := by congr 1
                  _=2*((2:Nat)^n*((a-1)+4)) := by ac_rfl
              have hm := Nat.mod_eq_zero_of_dvd hd
              omega

/-- Source predecessor of the intermediate odd-right branch is uniquely forced. -/
theorem high_two_unique (a k u v : Nat)
    (h : sectionPreimageAll a k (128+80*u+144*v) (819+472*u+952*v)) :
    a=471+276*u+548*v ∧ k=644+374*u+750*v := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at h <;> omega
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at h <;> omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at h
        obtain ⟨_,n,hs,_⟩ := h
        have hd : 2∣128+80*u+144*v+819+472*u+952*v := by
          refine ⟨(2:Nat)^n*4,?_⟩
          calc
            128+80*u+144*v+819+472*u+952*v=(2:Nat)^n*8 := by omega
            _=2*((2:Nat)^n*4) := by omega
        have hm := Nat.mod_eq_zero_of_dvd hd
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h <;> omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at h <;> omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at h <;> omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at h <;> omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with h3 | ⟨_,n,hs,_⟩
              · omega
              · have hd : 8∣128+80*u+144*v+819+472*u+952*v+1 := by
                  refine ⟨(2:Nat)^n*2,?_⟩
                  calc
                    128+80*u+144*v+819+472*u+952*v+1=(2:Nat)^n*16 := by omega
                    _=8*((2:Nat)^n*2) := by omega
                have hm := Nat.mod_eq_zero_of_dvd hd
                omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h <;> omega
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
            if_neg hk0,if_pos hlow] at h
          omega
        · by_cases haeven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_pos haeven] at h
            obtain ⟨_,n,hs,_⟩ := h
            have hd : 2∣128+80*u+144*v+819+472*u+952*v := by
              refine ⟨(2:Nat)^n*((a-1)+3),?_⟩
              calc
                128+80*u+144*v+819+472*u+952*v=(2:Nat)^n*(2*(a-1)+6) := by omega
                _=(2:Nat)^n*(2*((a-1)+3)) := by congr 1
                _=2*((2:Nat)^n*((a-1)+3)) := by ac_rfl
            have hm := Nat.mod_eq_zero_of_dvd hd
            omega
          · have haodd : a%2=1 := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at h
            rcases h with ⟨h3,_⟩ | ⟨_,n,hs,hc⟩
            · omega
            · have hn : n=0 := by
                by_cases hnn : n=0
                · exact hnn
                have hn1 : 1≤n := by omega
                have hp : 2∣(2:Nat)^n := Nat.pow_dvd_pow 2 hn1
                have hb := base4_odd a haodd
                obtain ⟨z,hz⟩ := hp
                obtain ⟨w,hw⟩ := hb
                have hd : 8∣128+80*u+144*v+819+472*u+952*v+1 := by
                  refine ⟨z*w,?_⟩
                  calc
                    128+80*u+144*v+819+472*u+952*v+1=(2:Nat)^n*(2*(a-1)+8) := by omega
                    _=(2*z)*(4*w) := by rw [←hz,←hw]
                    _=8*(z*w) := by simp only [show (8:Nat)=2*4 by decide]; ac_rfl
                have hm := Nat.mod_eq_zero_of_dvd hd
                omega
              subst n
              simp only [Nat.pow_zero, Nat.one_mul,Nat.mul_zero,Nat.add_zero] at hs hc
              omega

#print axioms target_three_parents
#print axioms high_one_two_parents
#print axioms high_two_unique
end BB6.Agent4Seven
