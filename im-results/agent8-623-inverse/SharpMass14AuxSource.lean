import Agent8SharpMass12Source
namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

theorem evalA_mass_nontrivial (a k m aa bb dd : Nat)
    (hk : 2≤k) (h : evalA a k m = some (aa,bb,dd)) :
    a+m+1≤aa+bb+dd := by
  by_cases ha : a=0
  · subst a
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp only [if_pos h2] at h
      cases h
      omega
    · simp only [if_neg h2, if_pos (by decide : (0:Nat)=0)] at h
      by_cases h0 : k%3=0
      · simp [h0] at h
      · simp only [if_neg h0] at h
        cases h
        omega
  · exact evalA_mass_positive a k m aa bb dd (by omega) h

theorem evalA_mass_zero_odd7 (a k m aa dd : Nat)
    (ha : 0<a) (hodd : k%2=1) (hk : 3≤k)
    (h : evalA a k m = some (aa,0,dd)) :
    a+m+7≤aa+dd := by
  rw [evalA] at h
  have hn : a≠0 := by omega
  by_cases h2 : k%3=2
  · simp only [if_pos h2] at h
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    omega
  · simp only [if_neg h2,if_neg hn] at h
    by_cases h0 : k%3=0
    · simp only [if_pos h0] at h
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      omega
    · simp only [if_neg h0] at h
      have hq : 2≤k/3 := by omega
      have hm:=evalA_mass_nontrivial (a-1) (k/3) (m+2*(k/3)+3)
        aa 0 dd hq h
      omega

theorem drainB_mass_b5 (b a d aa dd : Nat) (hb : 0<b)
    (h : drainB a b d = some (.D aa dd)) :
    a+d+b+5≤aa+dd := by
  by_cases hb1 : b=1
  · subst b
    have ha : a ≠ 0 := by
      intro hz
      subst a
      have hh : drainB 0 1 d = none := by
        rw [drainB]
        simp only [if_neg (by decide : (1:Nat)≠0)]
        have hv : evalA 0 0 (d+5) = none := by
          rw [evalA]
          simp only [if_neg (by decide : (0:Nat)%3≠2),
            if_pos (by decide : (0:Nat)=0), if_pos (by decide : (0:Nat)%3=0), ite_true]
        have hm : d+2*1+3=d+5 := by omega
        rw [hm,hv]
        rfl
      rw [hh] at h
      contradiction
    have he : evalA a 0 (d+5) = some (a-1,0,d+7) := by
      rw [evalA]
      simp only [if_neg (by decide : (0:Nat)%3≠2), if_neg ha,
        if_pos (by decide : (0:Nat)%3=0)]
      congr 1 <;> omega
    have hd : drainB a 1 d = some (.D (a-1) (d+7)) := by
      rw [drainB]
      simp only [if_neg (by decide : (1:Nat)≠0)]
      have hm : d+2*1+3=d+5 := by omega
      rw [hm,he]
      simp only [Option.bind_some, if_pos (by decide : (0:Nat)<1)]
      rw [drainB]
      simp only [if_true]
    rw [hd] at h
    cases h
    omega
  · have h2 : 2≤b := by omega
    have hm := (drainB_mass b a d aa dd h).2 hb
    omega

theorem drainB_mass_even_big_pos10 (b : Nat) (hb : 4≤b)
    (hbeven : b%2=0) (a d aa dd : Nat) (ha : 0<a)
    (h : drainB a b d = some (.D aa dd)) :
    a+d+2*b+10≤aa+dd := by
  rw [drainB] at h
  simp only [if_neg (by omega : b ≠ 0)] at h
  cases he : evalA a (b-1) (d+2*b+3) with
  | none => simp [he] at h
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [he,Option.bind_some] at h
    by_cases hlt : b1<b
    · simp only [if_pos hlt] at h
      by_cases hz : b1=0
      · subst b1
        have hm:=evalA_mass_zero_odd7 a (b-1) (d+2*b+3) a1 d1
          ha (by omega) (by omega) he
        have hr:=(drainB_mass 0 a1 d1 aa dd h).1
        omega
      · have hm:=evalA_mass_odd a (b-1) (d+2*b+3) a1 b1 d1 ha (by omega) he
        have hr:=drainB_mass_b5 b1 a1 d1 aa dd (by omega) h
        omega
    · simp [hlt] at h

end BB6.Agent8SharpSource
