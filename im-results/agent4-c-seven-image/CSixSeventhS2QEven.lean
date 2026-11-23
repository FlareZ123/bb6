import CSixSeventhS2
import S2QEvenResidue
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192

namespace BB6.Agent4SevenS2QEven
open BB6.Agent46
open BB6.Agent4Seven

/-- Exact source-parent alternatives for the complementary q-even lift.
    Here v=12+11*t (mod 32), so t+v=0 (mod 4) and
    v2(x+y+1)=4. The surviving parents are the direct P and odd-bounce Q. -/
theorem q_even_R_parents (u v t a k : Nat)
    (ht : u+v=2+4*t)
    (hv : v%32=(12+11*t)%32)
    (h : sectionPreimageAll a k
      (471+276*u+548*v) (644+374*u+750*v)) :
    (a=1113+650*u+1298*v ∧ k=321+187*u+375*v) ∨
    (a=601+650*t+162*v ∧ k=1598+1723*t+431*v) := by
  let x := 471+276*u+548*v
  let y := 644+374*u+750*v
  change sectionPreimageAll a k x y at h
  have hsumodd : (x+y)%2=1 := by
    dsimp [x,y]
    omega
  have hlarge : 24≤x+y := by
    dsimp [x,y]
    omega
  have htv : (t+v)%4=0 := by
    have hv' : v%4=(12+11*t)%4 := by omega
    omega
  have hT : 558+325*u+649*v=1208+1300*t+324*v := by
    omega
  have hTmod : (558+325*u+649*v)%16=8 := by
    rw [hT]
    omega
  have hval : (x+y+1)%32=16 := by
    have hT' : x+y+1=2*(558+325*u+649*v) := by
      dsimp [x,y]
      omega
    rw [hT']
    omega
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at h <;> omega
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at h <;> omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at h
        obtain ⟨_,n,hs,_⟩ := h
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
              rcases h with ⟨h3,_⟩ | ⟨_,n,hs,_⟩
              · omega
              · by_cases hn0 : n=0
                · subst n
                  simp at hs
                  omega
                · have hn1 : 1≤n := by omega
                  have hp : 2∣(2:Nat)^n := by
                    have hh : (2:Nat)^1∣(2:Nat)^n :=
                      Nat.pow_dvd_pow 2 hn1
                    simpa using hh
                  obtain ⟨z',hz⟩ := hp
                  have hdiv : 32∣x+y+1 := by
                    refine ⟨z',?_⟩
                    calc
                      x+y+1=(2:Nat)^n*16 := hs
                      _=(2*z')*16 := by rw [hz]
                      _=(2*16)*z' := by ac_rfl
                      _=32*z' := by simp
                  have hmod := Nat.mod_eq_zero_of_dvd hdiv
                  rw [hval] at hmod
                  omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
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
            have hfactor : 2*(a-1)+6=2*(a+2) := by omega
            have hdiv : 2∣x+y := by
              refine ⟨(2:Nat)^n*(a+2),?_⟩
              calc
                x+y=(2:Nat)^n*(2*(a-1)+6) := hs
                _=(2:Nat)^n*(2*(a+2)) := by rw [hfactor]
                _=2*((2:Nat)^n*(a+2)) := by ac_rfl
            have hmod := Nat.mod_eq_zero_of_dvd hdiv
            omega
          · have haodd : a%2=1 := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at h
            rcases h with ⟨h3,_⟩ | ⟨_,n,hs,hc⟩
            · omega
            · have hnodd : n%2=1 := by
                have hxodd : x%2=1 := by dsimp [x]; omega
                have hyEven : y%2=0 := by dsimp [y]; omega
                have hmodEq := congrArg (fun q : Nat => q%2) hc
                have hleft :
                    (2*k-a+3+(2*(a-1)+8)+3*n)%2=n%2 := by omega
                have hright : (x+2*y+2)%2=1 := by omega
                rw [hleft,hright] at hmodEq
                omega
              have hnle : n≤2 := by
                by_cases hn : n≤2
                · exact hn
                · have hn3 : 3≤n := by omega
                  have hp : 8∣(2:Nat)^n := by
                    have hh : (2:Nat)^3∣(2:Nat)^n :=
                      Nat.pow_dvd_pow 2 hn3
                    simpa only [show (2:Nat)^3=8 by decide] using hh
                  have hf : 4∣2*(a-1)+8 := by
                    refine ⟨(a-1)/2+2,?_⟩
                    omega
                  obtain ⟨p,hp⟩ := hp
                  obtain ⟨q,hq⟩ := hf
                  have hdiv : 32∣x+y+1 := by
                    refine ⟨p*q,?_⟩
                    calc
                      x+y+1=(2:Nat)^n*(2*(a-1)+8) := hs
                      _=(8*p)*(4*q) := by rw [hp,hq]
                      _=(8*4)*(p*q) := by ac_rfl
                      _=32*(p*q) := by simp
                  have hmod := Nat.mod_eq_zero_of_dvd hdiv
                  rw [hval] at hmod
                  omega
              have hn1 : n=1 := by omega
              subst n
              simp only [show (2:Nat)^1=2 by decide] at hs
              right
              constructor <;> omega

private theorem q_even_zero_not_initial (x y : Nat) (hx : 5<x)
    (h : BB6.Agent8Section.run secNext 0 (some (5,1))=some (x,y)) : False := by
  have heq : (5,1)=(x,y) := by
    apply Option.some.inj
    simpa [BB6.Agent8Section.run] using h
  have hfirst := congrArg Prod.fst heq
  omega

private theorem q_even_p_blank_unreachable (t z : Nat)
    (hlo : 7*t+10≤32*z) (hhi : 32*z≤12+11*t)
    (hcong : (2*t-z)%8=1) :
    ¬ BB6.Agent3.CReach
      (1113+650*(32*z-7*t-10)+1298*(12+11*t-32*z))
      (321+187*(32*z-7*t-10)+375*(12+11*t-32*z)) := by
  let u := 32*z-7*t-10
  let v := 12+11*t-32*z
  let px := 1113+650*u+1298*v
  let py := 321+187*u+375*v
  let A := 6568+6272*t-13376*z
  let B := 4758+4544*t-9696*z
  let W := 595+568*t-1212*z
  let F1x := A+8*W-4
  let F1y := 4*W-2
  let F2x := A+12*W-8
  let F2y := 2*W-2
  have hsum : u+v=2+4*t := by dsimp [u,v]; omega
  have hAeq : (px+py-4)/2=A := by
    dsimp [px,py,A,u,v]
    omega
  have hBeq : (px+3*py-10)/4=B := by
    dsimp [px,py,B,u,v]
    omega
  have hW : B+2=8*W := by dsimp [B,W]; omega
  have hhi418 : 418*(32*z)≤418*(12+11*t) :=
    Nat.mul_le_mul_left 418 hhi
  have hhi303 : 303*(32*z)≤303*(12+11*t) :=
    Nat.mul_le_mul_left 303 hhi
  have hhi38 : 38*(32*z)≤38*(12+11*t) :=
    Nat.mul_le_mul_left 38 hhi
  have hAmin : 5<A := by dsimp [A]; omega
  have hBmin : 6≤B := by dsimp [B]; omega
  have hWmin : 5≤W := by dsimp [W]; omega
  have hWmod : W%4=3 := by dsimp [W]; omega
  have hBmod : B%8=6 := by omega
  have hsum0 : (A+B)%8=6 := by dsimp [A,B]; omega
  have hF1x : A+B-2=F1x := by dsimp [F1x]; omega
  have hF1y : (B-2)/2=F1y := by dsimp [F1y]; omega
  have hF1sum : (F1x+F1y)%8=6 := by dsimp [F1x,F1y]; omega
  have hF1min : 6≤F1y := by dsimp [F1y]; omega
  have hF2x : F1x+F1y-2=F2x := by dsimp [F1x,F1y,F2x]; omega
  have hF2y : (F1y-2)/2=F2y := by dsimp [F1y,F2y]; omega
  have hF2min : 6≤F2y := by dsimp [F2y]; omega
  have hF2sum : (F2x+F2y)%8=0 := by dsimp [F2x,F2y]; omega
  have hAreach : ¬ BB6.Agent3.CReach A B := by
    intro hp
    have hgate0 := (six_even_right_blank_reach_iff A B
      (by omega) (by omega) (by omega) (by omega)).mp hp
    have hF1reach : BB6.Agent3.CReach F1x F1y := by
      simpa only [hF1x,hF1y] using hgate0
    have hgate1 := (six_even_right_blank_reach_iff F1x F1y
      (by omega) (by omega) (by omega) (by omega)).mp hF1reach
    have hF2reach : BB6.Agent3.CReach F2x F2y := by
      simpa only [hF2x,hF2y] using hgate1
    have hF2xeq : F2x=13700+13088*t-27920*z := by
      dsimp [F2x,A,W]
      omega
    have hF2yeq : F2y=1188+1136*t-2424*z := by
      dsimp [F2y,W]
      omega
    have hF2reach' : BB6.Agent3.CReach
        (13700+13088*t-27920*z) (1188+1136*t-2424*z) := by
      simpa only [hF2xeq,hF2yeq] using hF2reach
    exact (BB6.Agent4SevenS2QEven.q_even_normalizer_residual_unreachable
      t z hhi hcong) hF2reach'
  intro hp
  have hiff := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    px py (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).mp hp
  rcases hiff with ⟨time,htime⟩
  exact hAreach ⟨time,by simpa only [hAeq,hBeq] using htime⟩

private theorem q_even_q_blank_unreachable (t z : Nat)
    (hlo : 7*t+10≤32*z) (hhi : 32*z≤12+11*t) :
    ¬ BB6.Agent3.CReach
      (601+650*t+162*(12+11*t-32*z))
      (1598+1723*t+431*(12+11*t-32*z)) := by
  intro hq
  rcases hq with ⟨time,htime⟩
  have hsector :
      (((601+650*t+162*(12+11*t-32*z))+
        (1598+1723*t+431*(12+11*t-32*z)))%8=1 ∧
        (1598+1723*t+431*(12+11*t-32*z))%16=10) ∨
      (((601+650*t+162*(12+11*t-32*z))+
        (1598+1723*t+431*(12+11*t-32*z)))%8=3 ∧
        (1598+1723*t+431*(12+11*t-32*z))%16=2) := by
    right
    constructor <;> omega
  exact BB6.Agent34Three.cone_blank_unreachable time
    (601+650*t+162*(12+11*t-32*z))
    (1598+1723*t+431*(12+11*t-32*z))
    (by omega) hsector htime

private theorem q_even_r_blank_unreachable (t z : Nat)
    (hlo : 7*t+10≤32*z) (hhi : 32*z≤12+11*t)
    (hcong : (2*t-z)%8=1) :
    ¬ BB6.Agent3.CReach
      (471+276*(32*z-7*t-10)+548*(12+11*t-32*z))
      (644+374*(32*z-7*t-10)+750*(12+11*t-32*z)) := by
  let u := 32*z-7*t-10
  let v := 12+11*t-32*z
  have hsum : u+v=2+4*t := by dsimp [u,v]; omega
  have hv : v%32=(12+11*t)%32 := by dsimp [v]; omega
  intro hr
  rcases hr with ⟨time,hrun⟩
  cases time with
  | zero =>
      exact q_even_zero_not_initial _ _ (by omega) hrun
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at hrun
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (471+276*u+548*v,644+374*u+750*v) := by
            simpa [BB6.Agent8Section.run,hp] using hrun
          have hpre : sectionPreimageAll a k
              (471+276*u+548*v) (644+374*u+750*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases q_even_R_parents u v t a k hsum hv hpre with hP|hQ
          · have hPreach : BB6.Agent3.CReach
                (1113+650*u+1298*v) (321+187*u+375*v) := by
              refine ⟨n,?_⟩
              simpa [hP.1,hP.2] using hp
            exact q_even_p_blank_unreachable t z hlo hhi hcong hPreach
          · have hQreach : BB6.Agent3.CReach
                (601+650*t+162*v) (1598+1723*t+431*v) := by
              refine ⟨n,?_⟩
              simpa [hQ.1,hQ.2] using hp
            exact q_even_q_blank_unreachable t z hlo hhi hQreach

private theorem q_even_zero_not_initial_target (x y : Nat) (hx : 5<x)
    (h : BB6.Agent8Section.run secNext 0 (some (5,1))=some (x,y)) : False :=
  q_even_zero_not_initial x y hx h

private theorem q_even_p0_blank_unreachable (u v : Nat) :
    ¬ BB6.Agent3.CReach (518+320*u+576*v) (627+352*u+736*v) := by
  intro hr
  rcases hr with ⟨time,htime⟩
  cases time with
  | zero =>
      exact q_even_zero_not_initial_target _ _ (by omega) htime
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at htime
      | some p =>
          rcases p with ⟨a,b⟩
          have hstep : secNext (a,b)=some
              (518+320*u+576*v,627+352*u+736*v) := by
            simpa [BB6.Agent8Section.run,hp] using htime
          have himage := BB6.Agent3.section_odd_image a b
            (518+320*u+576*v) (627+352*u+736*v)
            hstep (by omega) (by omega)
          omega

private theorem q_even_p2_blank_unreachable (t z : Nat)
    (hlo : 7*t+10≤32*z) (hhi : 32*z≤12+11*t)
    (hcong : (2*t-z)%8=1) :
    ¬ BB6.Agent3.CReach
      (128+80*(32*z-7*t-10)+144*(12+11*t-32*z))
      (819+472*(32*z-7*t-10)+952*(12+11*t-32*z)) := by
  let u := 32*z-7*t-10
  let v := 12+11*t-32*z
  intro hr
  rcases hr with ⟨time,htime⟩
  cases time with
  | zero =>
      exact q_even_zero_not_initial_target _ _ (by omega) htime
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at htime
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some (128+80*u+144*v,819+472*u+952*v) := by
            simpa [BB6.Agent8Section.run,hp] using htime
          have hpre : sectionPreimageAll a k (128+80*u+144*v) (819+472*u+952*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          obtain ⟨ha,hk⟩ := high_two_unique a k u v hpre
          have hR : BB6.Agent3.CReach
              (471+276*u+548*v) (644+374*u+750*v) := by
            refine ⟨n,?_⟩
            simpa [ha,hk] using hp
          exact q_even_r_blank_unreachable t z hlo hhi hcong hR

private theorem q_even_h1_blank_unreachable (t z : Nat)
    (hlo : 7*t+10≤32*z) (hhi : 32*z≤12+11*t)
    (hcong : (2*t-z)%8=1) :
    ¬ BB6.Agent3.CReach
      (301+256*(32*z-7*t-10)+256*(12+11*t-32*z))
      (739+384*(32*z-7*t-10)+896*(12+11*t-32*z)) := by
  let u := 32*z-7*t-10
  let v := 12+11*t-32*z
  intro hr
  rcases hr with ⟨time,htime⟩
  cases time with
  | zero =>
      exact q_even_zero_not_initial_target _ _ (by omega) htime
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at htime
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (301+256*u+256*v,739+384*u+896*v) := by
            simpa [BB6.Agent8Section.run,hp] using htime
          have hpre : sectionPreimageAll a k (301+256*u+256*v) (739+384*u+896*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases high_one_two_parents a k u v hpre with hP0|hP2
          · have hP0reach : BB6.Agent3.CReach
                (518+320*u+576*v) (627+352*u+736*v) := by
              refine ⟨n,?_⟩
              simpa [hP0.1,hP0.2] using hp
            exact q_even_p0_blank_unreachable u v hP0reach
          · have hP2reach : BB6.Agent3.CReach
                (128+80*u+144*v) (819+472*u+952*v) := by
              refine ⟨n,?_⟩
              simpa [hP2.1,hP2.2] using hp
            exact q_even_p2_blank_unreachable t z hlo hhi hcong hP2reach

private theorem q_even_h3_blank_unreachable (u v : Nat) :
    ¬ BB6.Agent3.CReach (73+64*u+64*v) (850+480*u+992*v) := by
  intro hr
  rcases hr with ⟨time,htime⟩
  have hsector :
      (((73+64*u+64*v)+(850+480*u+992*v))%8=1 ∧
        (850+480*u+992*v)%16=10) ∨
      (((73+64*u+64*v)+(850+480*u+992*v))%8=3 ∧
        (850+480*u+992*v)%16=2) := by
    right
    constructor <;> omega
  exact BB6.Agent34Three.cone_blank_unreachable time
    (73+64*u+64*v) (850+480*u+992*v) (by omega) hsector htime

private theorem q_even_root_run_incoming (n : Nat) (s p : Nat × Nat)
    (h : BB6.Agent8Section.run secNext n (some s)=some p) :
    Incoming n p := by
  induction n generalizing p with
  | zero => trivial
  | succ n ih =>
      change (BB6.Agent8Section.run secNext n (some s)).bind secNext=some p at h
      cases hp : BB6.Agent8Section.run secNext n (some s) with
      | none => simp [hp] at h
      | some q =>
          have he : secNext q=some p := by simpa [hp] using h
          exact ⟨q,ih q hp,he⟩

private theorem q_even_incoming_drop (n : Nat) (p : Nat × Nat) :
    Incoming (n+1) p → Incoming n p := by
  induction n generalizing p with
  | zero => simp [Incoming]
  | succ n ih =>
      rintro ⟨q,hq,hedge⟩
      exact ⟨q,ih q hq,hedge⟩

private theorem q_even_incoming_shrink (n m : Nat) (p : Nat × Nat) :
    Incoming (n+m) p → Incoming n p := by
  induction m with
  | zero => simpa using id
  | succ m ih =>
      intro h
      have h' : Incoming (n+m) p :=
        q_even_incoming_drop (n+m) p (by
          simpa only [Nat.add_succ] using h)
      exact ih h'

private theorem q_even_d_blank_unreachable (u v : Nat) :
    ¬ BB6.Agent3.CReach (1213+1024*u+1024*v) (286+512*v) := by
  intro hr
  rcases hr with ⟨time,htime⟩
  by_cases hshort : time<6
  · have hcases : time=0 ∨ time=1 ∨ time=2 ∨
        time=3 ∨ time=4 ∨ time=5 := by omega
    rcases hcases with h0|h1|h2|h3|h4|h5
    · subst time
      have he : BB6.Agent8Section.run secNext 0 (some (5,1))=some (5,1) := by
        simp [BB6.Agent8Section.run]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 1 (some (5,1))=some (3,4) := by
        simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 2 (some (5,1))=some (4,7) := by
        simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 3 (some (5,1))=some (20,4) := by
        simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 4 (some (5,1))=some (12,10) := by
        simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 5 (some (5,1))=some (17,11) := by
        simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
  · have hlong : 6+(time-6)=time := by omega
    have hh : Incoming time (1213+1024*u+1024*v,286+512*v) :=
      q_even_root_run_incoming time (5,1) _ htime
    rw [←hlong] at hh
    exact no_six_D_public u v
      (q_even_incoming_shrink 6 (time-6) _ hh)

/-- The complementary q-even affine slice is absent from the genuine
    blank-origin Machine C section orbit at every time. This closes the
    residual after two six-even-right inverse steps, without using the
    invalid third-step odd-sum-one claim in the scratch derivation. -/
theorem blank_ne_s2q_even_image (t z time : Nat)
    (hlo : 7*t+10≤32*z)
    (hhi : 32*z≤12+11*t)
    (hcong : (2*t-z)%8=1) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (641+1024*(32*z-7*t-10),
            574+1024*(12+11*t-32*z)) := by
  let u := 32*z-7*t-10
  let v := 12+11*t-32*z
  have hsum : u+v=2+4*t := by dsimp [u,v]; omega
  intro hrun
  cases time with
  | zero =>
      exact q_even_zero_not_initial _ _ (by omega) hrun
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at hrun
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (641+1024*u,574+1024*v) := by
            simpa [BB6.Agent8Section.run,hp] using hrun
          have hpre : sectionPreimageAll a k (641+1024*u) (574+1024*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases target_three_parents a k u v hpre with hD|hH1|hH3
          · have hDreach : BB6.Agent3.CReach
                (1213+1024*u+1024*v) (286+512*v) := by
              refine ⟨n,?_⟩
              simpa [hD.1,hD.2] using hp
            exact q_even_d_blank_unreachable u v hDreach
          · have hH1reach : BB6.Agent3.CReach
                (301+256*u+256*v) (739+384*u+896*v) := by
              refine ⟨n,?_⟩
              simpa [hH1.1,hH1.2] using hp
            exact q_even_h1_blank_unreachable t z hlo hhi hcong hH1reach
          · have hH3reach : BB6.Agent3.CReach
                (73+64*u+64*v) (850+480*u+992*v) := by
              refine ⟨n,?_⟩
              simpa [hH3.1,hH3.2] using hp
            exact q_even_h3_blank_unreachable u v hH3reach

/-- A concrete nonempty progression in the complementary q-even slice. -/
theorem blank_ne_s2q_even_image_progression (n : Nat) (hn : 1≤n) :
    BB6.Agent8Section.run secNext n (some (5,1)) ≠
      some (641+1024*(32*n+72),574+1024*(96*n-62)) := by
  have hlo : 7*(32*n+2)+10≤32*(8*n+3) := by omega
  have hhi : 32*(8*n+3)≤12+11*(32*n+2) := by omega
  have hcong : (2*(32*n+2)-(8*n+3))%8=1 := by omega
  have h := blank_ne_s2q_even_image (32*n+2) (8*n+3) n hlo hhi hcong
  have hu : 32*(8*n+3)-7*(32*n+2)-10=32*n+72 := by omega
  have hv : 12+11*(32*n+2)-32*(8*n+3)=96*n-62 := by omega
  simpa only [hu,hv] using h


/-!
A complementary h5 progression.  It is deliberately narrower than the full
h5 cylinder: the extra 2-adic restrictions make every source-parent branch
terminate in one of the already-proved odd-right sum-one/two obstructions.
-/

private def qEvenH5T (d b : Nat) : Nat := 12+2048*(d+b)
private def qEvenH5Z (d b : Nat) : Nat := 3+704*d+448*b
private def qEvenH5U (d : Nat) : Nat := 2+8192*d
private def qEvenH5V (b : Nat) : Nat := 48+8192*b

private theorem q_even_h5_residual_unreachable (d b : Nat) :
    ¬ BB6.Agent3.CReach
      (86996+7148544*d+14296064*b)
      (7548+620032*d+1240576*b) := by
  let t := qEvenH5T d b
  let z := qEvenH5Z d b
  let x := 86996+7148544*d+14296064*b
  let y := 7548+620032*d+1240576*b
  let S := 11818+971072*d+1942080*b
  let Dpx := 94542+7768576*d+15536640*b
  let Dpy := 3773+310016*d+620288*b
  let D1x := 49155+4039296*d+8078464*b
  let D1y := 26463+2174656*d+4349376*b
  let Ex := 23634+1942144*d+3884160*b
  let Ey := 39224+3223232*d+6446528*b
  let Erx := 62856+5165376*d+10330688*b
  let Ery := 19611+1611616*d+3223264*b
  let Eax := 41231+3388496*d+6776976*b
  let Eay := 30420+2500056*d+5000120*b
  let Ebx := 71649+5888552*d+11777096*b
  let Eby := 15209+1250028*d+2500060*b
  have hxy : x+y=8*S := by dsimp [x,y,S]; omega
  have hS4 : S%4=2 := by dsimp [S]; omega
  have hSgt : 2<S := by dsimp [S]; omega
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    intro h
    have hDx : x+y-2=Dpx := by dsimp [x,y,Dpx]; omega
    have hDy : (y-2)/2=Dpy := by dsimp [y,Dpy]; omega
    have hDreach : BB6.Agent3.CReach Dpx Dpy := by
      simpa only [hDx,hDy] using h
    have hgate := (BB6.Agent3.evenodd_four_blank_reach_iff Dpx Dpy
      (by dsimp [Dpx]; omega) (by dsimp [Dpy]; omega)
      (by dsimp [Dpy]; omega) (by dsimp [Dpx,Dpy]; omega)).mp hDreach
    have hD1x : (Dpx+Dpy-5)/2=D1x := by
      dsimp [Dpx,Dpy,D1x]; omega
    have hD1y : (Dpx+3*Dpy-9)/4=D1y := by
      dsimp [Dpx,Dpy,D1y]; omega
    have hD1reach : BB6.Agent3.CReach D1x D1y := by
      simpa only [hD1x,hD1y] using hgate
    exact BB6.Agent11High.blank_no_odd_sum_two D1x D1y
      (by dsimp [D1y]; omega) (by dsimp [D1y]; omega)
      (by dsimp [D1x,D1y]; omega) hD1reach
  have hE : ¬ BB6.Agent3.CReach (2*S-2) ((x+2*y-2*S-8)/2) := by
    intro h
    have hEx : 2*S-2=Ex := by dsimp [S,Ex]; omega
    have hEy : (x+2*y-2*S-8)/2=Ey := by
      dsimp [x,y,S,Ey]; omega
    have hEreach : BB6.Agent3.CReach Ex Ey := by
      simpa only [hEx,hEy] using h
    have hgate0 := (six_even_right_blank_reach_iff Ex Ey
      (by dsimp [Ex]; omega) (by dsimp [Ey]; omega)
      (by dsimp [Ey]; omega) (by dsimp [Ex,Ey]; omega)).mp hEreach
    have hErx : Ex+Ey-2=Erx := by dsimp [Ex,Ey,Erx]; omega
    have hEry : (Ey-2)/2=Ery := by dsimp [Ey,Ery]; omega
    have hErreach : BB6.Agent3.CReach Erx Ery := by
      simpa only [hErx,hEry] using hgate0
    have hgate1 := (BB6.Agent3.evenodd_four_blank_reach_iff Erx Ery
      (by dsimp [Erx]; omega) (by dsimp [Ery]; omega)
      (by dsimp [Ery]; omega) (by dsimp [Erx,Ery]; omega)).mp hErreach
    have hEax : (Erx+Ery-5)/2=Eax := by
      dsimp [Erx,Ery,Eax]; omega
    have hEay : (Erx+3*Ery-9)/4=Eay := by
      dsimp [Erx,Ery,Eay]; omega
    have hEareach : BB6.Agent3.CReach Eax Eay := by
      simpa only [hEax,hEay] using hgate1
    have hgate2 := (six_even_right_blank_reach_iff Eax Eay
      (by dsimp [Eax]; omega) (by dsimp [Eay]; omega)
      (by dsimp [Eay]; omega) (by dsimp [Eax,Eay]; omega)).mp hEareach
    have hEbx : Eax+Eay-2=Ebx := by dsimp [Eax,Eay,Ebx]; omega
    have hEby : (Eay-2)/2=Eby := by dsimp [Eay,Eby]; omega
    have hEbreach : BB6.Agent3.CReach Ebx Eby := by
      simpa only [hEbx,hEby] using hgate2
    exact BB6.Agent11High.blank_no_odd_sum_two Ebx Eby
      (by dsimp [Eby]; omega) (by dsimp [Eby]; omega)
      (by dsimp [Ebx,Eby]; omega) hEbreach
  exact BB6.Agent11M0SumZeroVerified.blank_no_v2one_target x y S
    (by dsimp [x]; omega) (by dsimp [x]; omega)
    (by dsimp [y]; omega) (by dsimp [y]; omega)
    hxy hS4 hSgt hD hE

private theorem q_even_p_blank_unreachable_h5 (d b : Nat) :
    ¬ BB6.Agent3.CReach
      (1113+650*qEvenH5U d+1298*qEvenH5V b)
      (321+187*qEvenH5U d+375*qEvenH5V b) := by
  let u := qEvenH5U d
  let v := qEvenH5V b
  let t := qEvenH5T d b
  let z := qEvenH5Z d b
  let px := 1113+650*u+1298*v
  let py := 321+187*u+375*v
  let A := 6568+6272*t-13376*z
  let B := 4758+4544*t-9696*z
  let W := 595+568*t-1212*z
  let F1x := A+8*W-4
  let F1y := 4*W-2
  let F2x := A+12*W-8
  let F2y := 2*W-2
  have hlo : 7*t+10≤32*z := by
    dsimp [t,z,qEvenH5T,qEvenH5Z]; omega
  have hhi : 32*z≤12+11*t := by
    dsimp [t,z,qEvenH5T,qEvenH5Z]; omega
  have hsum : u+v=2+4*t := by
    dsimp [u,v,t,qEvenH5U,qEvenH5V,qEvenH5T]; omega
  have hAeq : (px+py-4)/2=A := by
    dsimp [px,py,A,u,v,t,z,qEvenH5U,qEvenH5V,qEvenH5T,qEvenH5Z]
    omega
  have hBeq : (px+3*py-10)/4=B := by
    dsimp [px,py,B,u,v,t,z,qEvenH5U,qEvenH5V,qEvenH5T,qEvenH5Z]
    omega
  have hW : B+2=8*W := by dsimp [B,W,t,z]; omega
  have hhi418 : 418*(32*z)≤418*(12+11*t) :=
    Nat.mul_le_mul_left 418 hhi
  have hhi303 : 303*(32*z)≤303*(12+11*t) :=
    Nat.mul_le_mul_left 303 hhi
  have hhi38 : 38*(32*z)≤38*(12+11*t) :=
    Nat.mul_le_mul_left 38 hhi
  have hAmin : 5<A := by dsimp [A]; omega
  have hBmin : 6≤B := by dsimp [B]; omega
  have hWmin : 5≤W := by dsimp [W]; omega
  have hWmod : W%4=3 := by dsimp [W]; omega
  have hBmod : B%8=6 := by omega
  have hsum0 : (A+B)%8=6 := by dsimp [A,B]; omega
  have hF1x : A+B-2=F1x := by dsimp [F1x]; omega
  have hF1y : (B-2)/2=F1y := by dsimp [F1y]; omega
  have hF1sum : (F1x+F1y)%8=6 := by dsimp [F1x,F1y]; omega
  have hF1min : 6≤F1y := by dsimp [F1y]; omega
  have hF2x : F1x+F1y-2=F2x := by dsimp [F1x,F1y,F2x]; omega
  have hF2y : (F1y-2)/2=F2y := by dsimp [F1y,F2y]; omega
  have hF2min : 6≤F2y := by dsimp [F2y]; omega
  have hF2sum : (F2x+F2y)%8=0 := by dsimp [F2x,F2y]; omega
  have hAreach : ¬ BB6.Agent3.CReach A B := by
    intro hp
    have hgate0 := (six_even_right_blank_reach_iff A B
      (by omega) (by omega) (by omega) (by omega)).mp hp
    have hF1reach : BB6.Agent3.CReach F1x F1y := by
      simpa only [hF1x,hF1y] using hgate0
    have hgate1 := (six_even_right_blank_reach_iff F1x F1y
      (by omega) (by omega) (by omega) (by omega)).mp hF1reach
    have hF2reach : BB6.Agent3.CReach F2x F2y := by
      simpa only [hF2x,hF2y] using hgate1
    have hF2xeq : F2x=86996+7148544*d+14296064*b := by
      dsimp [F2x,A,W,t,z,qEvenH5T,qEvenH5Z]
      omega
    have hF2yeq : F2y=7548+620032*d+1240576*b := by
      dsimp [F2y,W,t,z,qEvenH5T,qEvenH5Z]
      omega
    have hF2reach' : BB6.Agent3.CReach
        (86996+7148544*d+14296064*b)
        (7548+620032*d+1240576*b) := by
      simpa only [hF2xeq,hF2yeq] using hF2reach
    exact q_even_h5_residual_unreachable d b hF2reach'
  intro hp
  have hiff := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    px py (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).mp hp
  rcases hiff with ⟨time,htime⟩
  exact hAreach ⟨time,by simpa only [hAeq,hBeq] using htime⟩

private theorem q_even_r_blank_unreachable_h5 (d b : Nat) :
    ¬ BB6.Agent3.CReach
      (471+276*qEvenH5U d+548*qEvenH5V b)
      (644+374*qEvenH5U d+750*qEvenH5V b) := by
  let u := qEvenH5U d
  let v := qEvenH5V b
  let t := qEvenH5T d b
  let z := qEvenH5Z d b
  have hlo : 7*t+10≤32*z := by
    dsimp [t,z,qEvenH5T,qEvenH5Z]; omega
  have hhi : 32*z≤12+11*t := by
    dsimp [t,z,qEvenH5T,qEvenH5Z]; omega
  have hsum : u+v=2+4*t := by
    dsimp [u,v,t,qEvenH5U,qEvenH5V,qEvenH5T]; omega
  have hv : v%32=(12+11*t)%32 := by
    dsimp [v,t,qEvenH5V,qEvenH5T]; omega
  have hvdef : v=12+11*t-32*z := by
    dsimp [v,t,z,qEvenH5V,qEvenH5T,qEvenH5Z]; omega
  intro hr
  rcases hr with ⟨time,hrun⟩
  cases time with
  | zero =>
      exact q_even_zero_not_initial_target _ _ (by omega) hrun
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at hrun
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (471+276*u+548*v,644+374*u+750*v) := by
            simpa [BB6.Agent8Section.run,hp] using hrun
          have hpre : sectionPreimageAll a k
              (471+276*u+548*v) (644+374*u+750*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases q_even_R_parents u v t a k hsum hv hpre with hP|hQ
          · have hPreach : BB6.Agent3.CReach
                (1113+650*u+1298*v) (321+187*u+375*v) := by
              refine ⟨n,?_⟩
              simpa [hP.1,hP.2] using hp
            exact q_even_p_blank_unreachable_h5 d b hPreach
          · have hQreach : BB6.Agent3.CReach
                (601+650*t+162*v) (1598+1723*t+431*v) := by
              refine ⟨n,?_⟩
              simpa [hQ.1,hQ.2] using hp
            exact q_even_q_blank_unreachable t z hlo hhi
              (by simpa only [hvdef] using hQreach)

private theorem q_even_p2_blank_unreachable_h5 (d b : Nat) :
    ¬ BB6.Agent3.CReach
      (128+80*qEvenH5U d+144*qEvenH5V b)
      (819+472*qEvenH5U d+952*qEvenH5V b) := by
  let u := qEvenH5U d
  let v := qEvenH5V b
  intro hr
  rcases hr with ⟨time,htime⟩
  cases time with
  | zero =>
      exact q_even_zero_not_initial_target _ _ (by omega) htime
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at htime
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some (128+80*u+144*v,819+472*u+952*v) := by
            simpa [BB6.Agent8Section.run,hp] using htime
          have hpre : sectionPreimageAll a k
              (128+80*u+144*v) (819+472*u+952*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          obtain ⟨ha,hk⟩ := high_two_unique a k u v hpre
          have hR : BB6.Agent3.CReach
              (471+276*u+548*v) (644+374*u+750*v) := by
            refine ⟨n,?_⟩
            simpa [ha,hk] using hp
          exact q_even_r_blank_unreachable_h5 d b hR

private theorem q_even_h1_blank_unreachable_h5 (d b : Nat) :
    ¬ BB6.Agent3.CReach
      (301+256*qEvenH5U d+256*qEvenH5V b)
      (739+384*qEvenH5U d+896*qEvenH5V b) := by
  let u := qEvenH5U d
  let v := qEvenH5V b
  intro hr
  rcases hr with ⟨time,htime⟩
  cases time with
  | zero =>
      exact q_even_zero_not_initial_target _ _ (by omega) htime
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at htime
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (301+256*u+256*v,739+384*u+896*v) := by
            simpa [BB6.Agent8Section.run,hp] using htime
          have hpre : sectionPreimageAll a k
              (301+256*u+256*v) (739+384*u+896*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases high_one_two_parents a k u v hpre with hP0|hP2
          · have hP0reach : BB6.Agent3.CReach
                (518+320*u+576*v) (627+352*u+736*v) := by
              refine ⟨n,?_⟩
              simpa [hP0.1,hP0.2] using hp
            exact q_even_p0_blank_unreachable u v hP0reach
          · have hP2reach : BB6.Agent3.CReach
                (128+80*u+144*v) (819+472*u+952*v) := by
              refine ⟨n,?_⟩
              simpa [hP2.1,hP2.2] using hp
            exact q_even_p2_blank_unreachable_h5 d b hP2reach

/-- Exact source-parent exclusion for the h5 complementary q-even image
    progression \(u=2+2^{13}d,\ v=48+2^{13}b\). -/
theorem blank_ne_s2q_even_image_h5_progression (d b time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (641+1024*(2+8192*d),574+1024*(48+8192*b)) := by
  intro hr
  cases time with
  | zero =>
      exact q_even_zero_not_initial_target _ _ (by omega) hr
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (641+1024*qEvenH5U d,574+1024*qEvenH5V b) := by
            simpa [BB6.Agent8Section.run,hp] using hr
          have hpre : sectionPreimageAll a k
              (641+1024*qEvenH5U d) (574+1024*qEvenH5V b) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases target_three_parents a k (qEvenH5U d) (qEvenH5V b) hpre
              with hD|hH1|hH3
          · have hDreach : BB6.Agent3.CReach
                (1213+1024*qEvenH5U d+1024*qEvenH5V b)
                (286+512*qEvenH5V b) := by
              refine ⟨n,?_⟩
              simpa [hD.1,hD.2] using hp
            exact q_even_d_blank_unreachable (qEvenH5U d) (qEvenH5V b) hDreach
          · have hH1reach : BB6.Agent3.CReach
                (301+256*qEvenH5U d+256*qEvenH5V b)
                (739+384*qEvenH5U d+896*qEvenH5V b) := by
              refine ⟨n,?_⟩
              simpa [hH1.1,hH1.2] using hp
            exact q_even_h1_blank_unreachable_h5 d b hH1reach
          · have hH3reach : BB6.Agent3.CReach
                (73+64*qEvenH5U d+64*qEvenH5V b)
                (850+480*qEvenH5U d+992*qEvenH5V b) := by
              refine ⟨n,?_⟩
              simpa [hH3.1,hH3.2] using hp
            exact q_even_h3_blank_unreachable (qEvenH5U d) (qEvenH5V b) hH3reach


#print axioms q_even_R_parents
#print axioms blank_ne_s2q_even_image
#print axioms blank_ne_s2q_even_image_progression

end BB6.Agent4SevenS2QEven
