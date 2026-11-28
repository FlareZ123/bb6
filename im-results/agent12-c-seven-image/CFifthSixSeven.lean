import CSixSeventhRoot
import OddOddVal3Source
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent12SevenFifth

open BB6.Agent46 BB6.Agent4Seven

private theorem incoming_drop (n : Nat) (p : Nat × Nat) :
    Incoming (n+1) p → Incoming n p := by
  induction n generalizing p with
  | zero => simp [Incoming]
  | succ n ih =>
      rintro ⟨q,hq,hedge⟩
      exact ⟨q,ih q hq,hedge⟩

private theorem incoming_shrink (n m : Nat) (p : Nat × Nat) :
    Incoming (n+m) p → Incoming n p := by
  induction m with
  | zero => simpa using id
  | succ m ih =>
      intro h
      have h' : Incoming (n+m) p := incoming_drop (n+m) p (by
        simpa only [Nat.add_succ] using h)
      exact ih h'

/-- On the residue-25 slice the H1 grandparent has exactly its direct
    affine parent. All exceptional and unbounded bounce branches are
    excluded by the target's 32-adic residues. -/
private theorem p_unique_parent_25 (a k u v : Nat)
    (hsector : (29*u+v)%32=25)
    (h : sectionPreimageAll a k
      (1113+650*u+1298*v) (321+187*u+375*v)) :
    a=(1113+650*u+1298*v)+(321+187*u+375*v)-2 ∧
    k=((321+187*u+375*v)-2)/2 := by
  have hS32 :
      ((1113+650*u+1298*v)+(321+187*u+375*v))%32=27 := by
    omega
  have hS1 :
      ((1113+650*u+1298*v)+(321+187*u+375*v)+1)%32=28 := by
    omega
  have hy32 : (321+187*u+375*v)%32=0 := by omega
  unfold sectionPreimageAll at h
  by_cases ha0 : a=0
  · simp only [if_pos ha0] at h
    by_cases hk0 : k=0
    · simp [hk0] at h
    by_cases hk1 : k=1
    · simp only [if_neg hk0,if_pos hk1] at h
      omega
    simp only [if_neg hk0,if_neg hk1] at h
    obtain ⟨_,n,hs,_⟩ := h
    have hd : 8 ∣
        (1113+650*u+1298*v)+(321+187*u+375*v) := by
      refine ⟨2^n,?_⟩
      calc
        (1113+650*u+1298*v)+(321+187*u+375*v) = 2^n*8 := hs
        _ = 8*2^n := by ac_rfl
    have hm := Nat.mod_eq_zero_of_dvd hd
    omega
  · by_cases ha1 : a=1
    · simp only [if_neg ha0,if_pos ha1] at h
      by_cases hk0 : k=0
      · simp [hk0] at h
        omega
      by_cases hk1 : k=1
      · simp [hk0,hk1] at h
        omega
      by_cases hk2 : k=2
      · simp [hk0,hk1,hk2] at h
        omega
      by_cases hk3 : k=3
      · simp [hk0,hk1,hk2,hk3] at h
        omega
      simp only [if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
      rcases h with h3 | ⟨_,n,hs,_⟩
      · omega
      · have hd : 16 ∣
            (1113+650*u+1298*v)+(321+187*u+375*v)+1 := by
          refine ⟨2^n,?_⟩
          calc
            (1113+650*u+1298*v)+(321+187*u+375*v)+1 = 2^n*16 := hs
            _ = 16*2^n := by ac_rfl
        have hm := Nat.mod_eq_zero_of_dvd hd
        omega
    · by_cases hk0 : k=0
      · simp [ha0,ha1,hk0] at h
        omega
      · by_cases hlow : 2*k≤a
        · simp only [if_neg ha0,if_neg ha1,if_neg hk0,if_pos hlow] at h
          exact h
        · by_cases haeven : a%2=0
          · simp only [if_neg ha0,if_neg ha1,if_neg hk0,
              if_neg hlow,if_pos haeven] at h
            obtain ⟨_,n,hs,_⟩ := h
            have hd : 2 ∣
                (1113+650*u+1298*v)+(321+187*u+375*v) := by
              refine ⟨2^n*((a-1)+3),?_⟩
              calc
                (1113+650*u+1298*v)+(321+187*u+375*v) =
                    2^n*(2*(a-1)+6) := hs
                _ = 2^n*(2*((a-1)+3)) := by omega
                _ = 2*(2^n*((a-1)+3)) := by ac_rfl
            have hm := Nat.mod_eq_zero_of_dvd hd
            omega
          · have haodd : a%2=1 := by omega
            have ha2 : 2≤a := by omega
            simp only [if_neg ha0,if_neg ha1,if_neg hk0,
              if_neg hlow,if_neg haeven] at h
            rcases h with h3 | ⟨_,n,hs,hc⟩
            · omega
            · by_cases hn0 : n=0
              · subst n
                simp at hs hc
                omega
              · have hn1 : 1≤n := by omega
                have hp2 : 2 ∣ (2:Nat)^n := by
                  have hp := Nat.pow_dvd_pow 2 hn1
                  simpa only [show (2:Nat)^1=2 by decide] using hp
                have hbmod : (2*(a-1)+8)%4=0 := by omega
                have hb4 : 4 ∣ 2*(a-1)+8 :=
                  Nat.dvd_of_mod_eq_zero hbmod
                obtain ⟨p,hp⟩ := hp2
                obtain ⟨q,hq⟩ := hb4
                have h8 : 8 ∣
                    (1113+650*u+1298*v)+(321+187*u+375*v)+1 := by
                  refine ⟨p*q,?_⟩
                  calc
                    (1113+650*u+1298*v)+(321+187*u+375*v)+1 =
                        2^n*(2*(a-1)+8) := hs
                    _ = (2*p)*(4*q) := by rw [hp,hq]
                    _ = (2*4)*(p*q) := by ac_rfl
                    _ = 8*(p*q) := by rfl
                have hm := Nat.mod_eq_zero_of_dvd h8
                omega

/-- The unique direct parent Q of P is in Agent 2's exact odd-odd
    valuation-three cone, so P cannot have three incoming section edges. -/
private theorem no_three_P_25 (u v : Nat)
    (hsector : (29*u+v)%32=25) :
    ¬ Incoming 3
      (1113+650*u+1298*v,321+187*u+375*v) := by
  rintro ⟨⟨a,k⟩,h2,hstep⟩
  have hinv : sectionPreimageAll a k _ _ :=
    (section_preimage_all_iff a k _ _).mp hstep
  obtain ⟨ha,hk⟩ := p_unique_parent_25 a k u v hsector hinv
  rcases h2 with ⟨⟨b,l⟩,h1,hqedge⟩
  have hcrit : BB6.Agent46.sectionPreimageCriterion b l a k :=
    (BB6.Agent46.complete_section_inverse b l a k (by omega)).mp hqedge
  have hx : a%8=1 := by omega
  have hy : k%8=7 := by omega
  have hs : (a+k)%16=8 := by omega
  have hk8 : 8≤k := by omega
  obtain ⟨hl5,hlodd,hbad⟩ :=
    BB6.Agent2COddOddVal3.all_parent_forbidden b l a k
      hx hy hs hk8 hcrit
  rcases h1 with ⟨⟨c,d⟩,_,hprev⟩
  have himage := BB6.Agent3.section_odd_image c d b l
    hprev hl5 hlodd
  omega

private theorem no_four_R_25 (u v : Nat)
    (hsector : (29*u+v)%32=25) :
    ¬ Incoming 4
      (471+276*u+548*v,644+374*u+750*v) := by
  rintro ⟨⟨a,k⟩,h3,hstep⟩
  have hy : 4≤644+374*u+750*v := by omega
  have heven : (644+374*u+750*v)%2=0 := by omega
  have hs :
      ((471+276*u+548*v)+(644+374*u+750*v))%4=1 := by omega
  have hinv := (BB6.Agent15.section_sum_one_even_iff_affine
    a k (471+276*u+548*v) (644+374*u+750*v) hy heven hs).mp hstep
  rcases hinv with ⟨ha,hk⟩
  have hax :
      (471+276*u+548*v)+(644+374*u+750*v)-2 =
        1113+650*u+1298*v := by omega
  have hky :
      (644+374*u+750*v-2)/2=321+187*u+375*v := by omega
  rw [ha,hk,hax,hky] at h3
  exact no_three_P_25 u v hsector h3

private theorem no_five_P2_25 (u v : Nat)
    (hsector : (29*u+v)%32=25) :
    ¬ Incoming 5
      (128+80*u+144*v,819+472*u+952*v) := by
  rintro ⟨⟨a,k⟩,h4,hstep⟩
  have hinv : sectionPreimageAll a k _ _ :=
    (section_preimage_all_iff a k _ _).mp hstep
  obtain ⟨ha,hk⟩ := high_two_unique a k u v hinv
  rw [ha,hk] at h4
  exact no_four_R_25 u v hsector h4

private theorem no_one_P0 (u v : Nat) :
    ¬ Incoming 1
      (518+320*u+576*v,627+352*u+736*v) := by
  rintro ⟨⟨a,b⟩,_,hedge⟩
  have hr := BB6.Agent3.section_odd_image a b
    (518+320*u+576*v) (627+352*u+736*v)
    hedge (by omega) (by omega)
  omega

private theorem no_six_H1_25 (u v : Nat)
    (hsector : (29*u+v)%32=25) :
    ¬ Incoming 6
      (301+256*u+256*v,739+384*u+896*v) := by
  rintro ⟨⟨a,k⟩,h5,hstep⟩
  have hinv : sectionPreimageAll a k _ _ :=
    (section_preimage_all_iff a k _ _).mp hstep
  rcases high_one_two_parents a k u v hinv with hp|hq
  · rw [hp.1,hp.2] at h5
    exact no_one_P0 u v (incoming_shrink 1 4 _ h5)
  · rw [hq.1,hq.2] at h5
    exact no_five_P2_25 u v hsector h5

private theorem no_two_P3 (u v : Nat) :
    ¬ Incoming 2
      (921+544*u+1056*v,424+240*u+496*v) := by
  rintro ⟨⟨a,b⟩,⟨⟨c,d⟩,_,h0⟩,h1⟩
  exact BB6.Agent34Three.all_source_no_two_new c d a b
    (921+544*u+1056*v) (424+240*u+496*v)
    (by omega) (Or.inl (by omega)) h0 h1

private theorem no_three_H3 (u v : Nat) :
    ¬ Incoming 3
      (73+64*u+64*v,850+480*u+992*v) := by
  rintro ⟨⟨a,k⟩,h2,hstep⟩
  have hinv : sectionPreimageAll a k _ _ :=
    (section_preimage_all_iff a k _ _).mp hstep
  obtain ⟨ha,hk⟩ := BB6.Agent34Three.only_direct a k
    (73+64*u+64*v) (850+480*u+992*v)
    (by omega) (by omega) (Or.inr (by omega)) hinv
  have hx : a=921+544*u+1056*v := by omega
  have hy : k=424+240*u+496*v := by omega
  rw [hx,hy] at h2
  exact no_two_P3 u v h2

/-- Fifth strict sixth/seventh sector: a second slice of the u+v=1 mod4
    class, one inverse layer deeper than the residue-21 sector. -/
theorem exactly_six_not_seven_a12_fifth (u v : Nat)
    (hsector : (29*u+v)%32=25) :
    Incoming 6 (641+1024*u,574+1024*v) ∧
    ¬ Incoming 7 (641+1024*u,574+1024*v) := by
  refine ⟨six_incoming_exist u v,?_⟩
  rintro ⟨⟨a,k⟩,h6,hstep⟩
  have hinv : sectionPreimageAll a k _ _ :=
    (section_preimage_all_iff a k _ _).mp hstep
  rcases target_three_parents a k u v hinv with hd|hh|hj
  · rw [hd.1,hd.2] at h6
    exact no_six_D_public u v h6
  · rw [hh.1,hh.2] at h6
    exact no_six_H1_25 u v hsector h6
  · rw [hj.1,hj.2] at h6
    exact no_three_H3 u v (incoming_shrink 3 3 _ h6)

private theorem root_run_incoming (n : Nat) (s p : Nat × Nat)
    (h : BB6.Agent8Section.run secNext n (some s) = some p) :
    Incoming n p := by
  induction n generalizing p with
  | zero => trivial
  | succ n ih =>
      change (BB6.Agent8Section.run secNext n (some s)).bind secNext =
        some p at h
      cases hp : BB6.Agent8Section.run secNext n (some s) with
      | none => simp [hp] at h
      | some q =>
          have he : secNext q=some p := by simpa [hp] using h
          exact ⟨q,ih q hp,he⟩

theorem blank_ne_band_a12_fifth (u v time : Nat)
    (hsector : (29*u+v)%32=25) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (641+1024*u,574+1024*v) := by
  intro ht
  by_cases hshort : time<7
  · have hex : time=0 ∨ time=1 ∨ time=2 ∨ time=3 ∨
        time=4 ∨ time=5 ∨ time=6 := by omega
    rcases hex with h0|h1|h2|h3|h4|h5|h6
    all_goals subst time
    all_goals simp [BB6.Agent8Section.run,secNext,exactSection,bounce] at ht
    all_goals omega
  · have hlong : 7+(time-7)=time := by omega
    have hh : Incoming time (641+1024*u,574+1024*v) :=
      root_run_incoming time (5,1) _ ht
    rw [←hlong] at hh
    exact (exactly_six_not_seven_a12_fifth u v hsector).2
      (incoming_shrink 7 (time-7) _ hh)

#print axioms exactly_six_not_seven_a12_fifth
#print axioms blank_ne_band_a12_fifth

end BB6.Agent12SevenFifth
