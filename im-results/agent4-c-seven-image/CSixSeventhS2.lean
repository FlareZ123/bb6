import CSixSeventhRoot
import EvenRightSixOrbit
import OddOddLowVal
import ThreeConeSource
import Agent3COrbitIff
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192

namespace BB6.Agent4SevenS2
open BB6.Agent46
open BB6.Agent4Seven

/-- The S2 image cylinder is equivalently the two affine residue
    conditions u+v=2+4t and v=28+11t (mod 32). -/
theorem s2_sector_decompose (u v : Nat)
    (hsector : (v+93*u)%128=42) :
    ∃ t, u+v=2+4*t ∧ v%32=(28+11*t)%32 := by
  have hsum : (u+v)%4=2 := by omega
  let t := (u+v-2)/4
  have ht : u+v=2+4*t := by
    dsimp [t]
    omega
  have hv : (v+11*t)%32=28 := by omega
  refine ⟨t,ht,?_⟩
  omega

/-- The direct parent of the odd/odd P branch is excluded by the
    source-exact six-right normalizer.  Its three gate residues are
    6, 6, and 4 modulo eight, and the terminal odd-right sum is 1 mod 4. -/
private theorem s2_normalizer_excluded (u v t : Nat)
    (ht : u+v=2+4*t)
    (hv : v%32=(28+11*t)%32) :
    sixEvenRightExcluded (1552+1674*t+418*v)
                         (1122+1211*t+303*v) = true := by
  let A := 1552+1674*t+418*v
  let B := 1122+1211*t+303*v
  have hAmod16 : A%16=8 := by
    dsimp [A]
    omega
  have hBmod32 : B%32=6 := by
    dsimp [B]
    omega
  have hBmin : 1122≤B := by
    dsimp [B]
    omega
  have hBplusmod : (B+2)%32=8 := by omega
  let W := (B+2)/8
  have hW : B+2=8*W := by
    dsimp [W]
    omega
  have hWmod4 : W%4=1 := by omega
  have hWmin : 141≤W := by omega
  have hsum0 : (A+B)%8=6 := by omega
  have hg0 : sixEvenRightGate A B := by
    unfold sixEvenRightGate
    refine ⟨?_,?_,?_,?_⟩ <;> omega
  have hF1x : A+B-2=A+8*W-4 := by omega
  have hF1y : (B-2)/2=4*W-2 := by omega
  have hsum1 : ((A+8*W-4)+(4*W-2))%8=6 := by omega
  have hg1 : sixEvenRightGate (A+8*W-4) (4*W-2) := by
    unfold sixEvenRightGate
    refine ⟨?_,?_,?_,?_⟩ <;> omega
  have hF2x :
      (A+8*W-4)+(4*W-2)-2=A+12*W-8 := by omega
  have hF2y : ((4*W-2)-2)/2=2*W-2 := by omega
  have hsum2 : ((A+12*W-8)+(2*W-2))%8=4 := by omega
  have hg2 : sixEvenRightGate (A+12*W-8) (2*W-2) := by
    unfold sixEvenRightGate
    refine ⟨?_,?_,?_,?_⟩ <;> omega
  have hF3x :
      (A+12*W-8)+(2*W-2)-2=A+14*W-12 := by omega
  have hF3y : ((2*W-2)-2)/2=W-2 := by omega
  have hF3odd : (W-2)%2=1 := by omega
  have hg3 : ¬ sixEvenRightGate (A+14*W-12) (W-2) := by
    intro h
    unfold sixEvenRightGate at h
    omega
  have hnorm :
      sixEvenRightNormalize A B=(A+14*W-12,W-2) := by
    simp [sixEvenRightNormalize,hg0,hg1,hg2,hg3,
      hF1x,hF1y,hF2x,hF2y,hF3x,hF3y]
  have hfinal :
      5≤W-2 ∧ (W-2)%2=1 ∧
        ((A+14*W-12)+(W-2))%4=1 := by
    refine ⟨?_,hF3odd,?_⟩ <;> omega
  simp [sixEvenRightExcluded,hnorm,hfinal]

/-- The complete original-source parent classification of R.  The
    first parent is the direct P branch; the second is the unique
    one-bounce Q branch.  No other inverse-grammar branch survives. -/
theorem s2_R_parents (u v t a k : Nat)
    (ht : u+v=2+4*t)
    (hv : v%32=(28+11*t)%32)
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
  have hTmod : (558+325*u+649*v)%16=8 := by
    have htv : (t+v)%4=0 := by omega
    have hT : 558+325*u+649*v=1208+1300*t+324*v := by omega
    rw [hT]
    omega
  have hval : (x+y+1)%32=16 := by
    have hT : x+y+1=2*(558+325*u+649*v) := by
      dsimp [x,y]
      omega
    rw [hT]
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
                  obtain ⟨z,hz⟩ := hp
                  have hdiv : 32∣x+y+1 := by
                    refine ⟨z,?_⟩
                    calc
                      x+y+1=(2:Nat)^n*16 := hs
                      _=(2*z)*16 := by rw [hz]
                      _=(2*16)*z := by ac_rfl
                      _=32*z := by simp
                  have hmod := Nat.mod_eq_zero_of_dvd hdiv
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
            omega
          · have haodd : a%2=1 := by omega
            simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,
              if_neg hk0,if_neg hlow,if_neg haeven] at h
            rcases h with ⟨h3,_⟩ | ⟨_,n,hs,hc⟩
            · omega
            · have hnodd : n%2=1 := by omega
              have hnle : n≤2 := by
                by_contra hn
                have hn3 : 3≤n := by omega
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
                omega
              have hn1 : n=1 := by omega
              subst n
              simp only [show (2:Nat)^1=2 by decide] at hs
              right
              constructor <;> omega

private theorem s2_p_blank_unreachable (u v t : Nat)
    (ht : u+v=2+4*t)
    (hv : v%32=(28+11*t)%32) :
    ¬ BB6.Agent3.CReach (1113+650*u+1298*v)
                         (321+187*u+375*v) := by
  let px := 1113+650*u+1298*v
  let py := 321+187*u+375*v
  let ax := 1552+1674*t+418*v
  let byy := 1122+1211*t+303*v
  have hAeq : (px+py-4)/2=ax := by
    dsimp [px,py,ax]
    omega
  have hBeq : (px+3*py-10)/4=byy := by
    dsimp [px,py,byy]
    omega
  have hExcluded := s2_normalizer_excluded u v t ht hv
  have hAnot : ¬ BB6.Agent3.CReach ax byy := by
    intro hr
    rcases hr with ⟨time,htime⟩
    exact (sixEvenRightExcluded_sound ax byy hExcluded time) htime
  intro hp
  have hiff := (BB6.Agent3.oddodd_lowval_blank_reach_iff
    px py (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).mp hp
  rcases hiff with ⟨time,htime⟩
  exact hAnot ⟨time,by simpa only [hAeq,hBeq] using htime⟩

private theorem s2_q_blank_unreachable (u v t : Nat)
    (ht : u+v=2+4*t)
    (hv : v%32=(28+11*t)%32) :
    ¬ BB6.Agent3.CReach (601+650*t+162*v)
                         (1598+1723*t+431*v) := by
  intro hq
  rcases hq with ⟨time,htime⟩
  have hsector :
      (( (601+650*t+162*v)+(1598+1723*t+431*v))%8=1 ∧
        (1598+1723*t+431*v)%16=10) ∨
      (((601+650*t+162*v)+(1598+1723*t+431*v))%8=3 ∧
        (1598+1723*t+431*v)%16=2) := by
    right
    constructor <;> omega
  exact BB6.Agent34Three.cone_blank_unreachable time
    (601+650*t+162*v) (1598+1723*t+431*v) (by omega) hsector htime

/-- The odd-bounce parent P is excluded by the six-right normalizer,
    while the one-bounce parent Q is excluded by Agent 34's three-edge
    source cone.  Therefore R itself is blank-root unreachable. -/
private theorem s2_r_blank_unreachable (u v t : Nat)
    (ht : u+v=2+4*t)
    (hv : v%32=(28+11*t)%32) :
    ¬ BB6.Agent3.CReach (471+276*u+548*v)
                         (644+374*u+750*v) := by
  intro hr
  rcases hr with ⟨time,hrun⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hrun
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at hrun
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some (471+276*u+548*v)
              (644+374*u+750*v) := by
            simpa [BB6.Agent8Section.run,hp] using hrun
          have hpre : sectionPreimageAll a k
              (471+276*u+548*v) (644+374*u+750*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases s2_R_parents u v t a k ht hv hpre with hP|hQ
          · have hpreach : BB6.Agent3.CReach
                (1113+650*u+1298*v) (321+187*u+375*v) := by
              refine ⟨n,?_⟩
              simpa [hP.1,hP.2] using hp
            exact s2_p_blank_unreachable u v t ht hv hpreach
          · have hqreach : BB6.Agent3.CReach
                (601+650*t+162*v) (1598+1723*t+431*v) := by
              refine ⟨n,?_⟩
              simpa [hQ.1,hQ.2] using hp
            exact s2_q_blank_unreachable u v t ht hv hqreach

private theorem s2_p0_blank_unreachable (u v : Nat) :
    ¬ BB6.Agent3.CReach (518+320*u+576*v)
                         (627+352*u+736*v) := by
  intro hr
  rcases hr with ⟨time,htime⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at htime
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at htime
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (518+320*u+576*v) (627+352*u+736*v) := by
            simpa [BB6.Agent8Section.run,hp] using htime
          have himage := BB6.Agent3.section_odd_image a k
            (518+320*u+576*v) (627+352*u+736*v)
            hstep (by omega) (by omega)
          omega

private theorem s2_p2_blank_unreachable (u v t : Nat)
    (ht : u+v=2+4*t)
    (hv : v%32=(28+11*t)%32) :
    ¬ BB6.Agent3.CReach (128+80*u+144*v)
                         (819+472*u+952*v) := by
  intro hr
  rcases hr with ⟨time,htime⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at htime
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at htime
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (128+80*u+144*v) (819+472*u+952*v) := by
            simpa [BB6.Agent8Section.run,hp] using htime
          have hpre : sectionPreimageAll a k
              (128+80*u+144*v) (819+472*u+952*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          obtain ⟨ha,hk⟩ := high_two_unique a k u v hpre
          have hR : BB6.Agent3.CReach
              (471+276*u+548*v) (644+374*u+750*v) := by
            refine ⟨n,?_⟩
            simpa [ha,hk] using hp
          exact s2_r_blank_unreachable u v t ht hv hR

private theorem s2_h1_blank_unreachable (u v t : Nat)
    (ht : u+v=2+4*t)
    (hv : v%32=(28+11*t)%32) :
    ¬ BB6.Agent3.CReach (301+256*u+256*v)
                         (739+384*u+896*v) := by
  intro hr
  rcases hr with ⟨time,htime⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at htime
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at htime
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (301+256*u+256*v) (739+384*u+896*v) := by
            simpa [BB6.Agent8Section.run,hp] using htime
          have hpre : sectionPreimageAll a k
              (301+256*u+256*v) (739+384*u+896*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases high_one_two_parents a k u v hpre with hP0|hP2
          · have hP0reach : BB6.Agent3.CReach
                (518+320*u+576*v) (627+352*u+736*v) := by
              refine ⟨n,?_⟩
              simpa [hP0.1,hP0.2] using hp
            exact s2_p0_blank_unreachable u v hP0reach
          · have hP2reach : BB6.Agent3.CReach
                (128+80*u+144*v) (819+472*u+952*v) := by
              refine ⟨n,?_⟩
              simpa [hP2.1,hP2.2] using hp
            exact s2_p2_blank_unreachable u v t ht hv hP2reach

private theorem s2_h3_blank_unreachable (u v : Nat) :
    ¬ BB6.Agent3.CReach (73+64*u+64*v)
                         (850+480*u+992*v) := by
  intro hr
  rcases hr with ⟨time,htime⟩
  have hsector :
      (( (73+64*u+64*v)+(850+480*u+992*v))%8=1 ∧
        (850+480*u+992*v)%16=10) ∨
      (((73+64*u+64*v)+(850+480*u+992*v))%8=3 ∧
        (850+480*u+992*v)%16=2) := by
    right
    constructor <;> omega
  exact BB6.Agent34Three.cone_blank_unreachable time
    (73+64*u+64*v) (850+480*u+992*v) (by omega) hsector htime

private theorem s2_root_run_incoming (n : Nat) (s p : Nat × Nat)
    (h : BB6.Agent8Section.run secNext n (some s)=some p) :
    Incoming n p := by
  induction n generalizing p with
  | zero =>
      trivial
  | succ n ih =>
      change (BB6.Agent8Section.run secNext n (some s)).bind secNext=some p at h
      cases hp : BB6.Agent8Section.run secNext n (some s) with
      | none =>
          simp [hp] at h
      | some q =>
          have he : secNext q=some p := by simpa [hp] using h
          exact ⟨q,ih q hp,he⟩

private theorem s2_incoming_drop (n : Nat) (p : Nat × Nat) :
    Incoming (n+1) p → Incoming n p := by
  induction n generalizing p with
  | zero =>
      simp [Incoming]
  | succ n ih =>
      rintro ⟨q,hq,hedge⟩
      exact ⟨q,ih q hq,hedge⟩

private theorem s2_incoming_shrink (n m : Nat) (p : Nat × Nat) :
    Incoming (n+m) p → Incoming n p := by
  induction m with
  | zero =>
      simpa using id
  | succ m ih =>
      intro h
      have h' : Incoming (n+m) p :=
        s2_incoming_drop (n+m) p (by
          simpa only [Nat.add_succ] using h)
      exact ih h'

private theorem s2_d_blank_unreachable (u v : Nat) :
    ¬ BB6.Agent3.CReach (1213+1024*u+1024*v) (286+512*v) := by
  intro hr
  rcases hr with ⟨time,htime⟩
  by_cases hshort : time<6
  · have hcases : time=0 ∨ time=1 ∨ time=2 ∨
        time=3 ∨ time=4 ∨ time=5 := by omega
    rcases hcases with h0|h1|h2|h3|h4|h5
    · subst time
      have he : BB6.Agent8Section.run secNext 0 (some (5,1))=
          some (5,1) := by simp [BB6.Agent8Section.run]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 1 (some (5,1))=
          some (3,4) := by
        simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 2 (some (5,1))=
          some (4,7) := by
        simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 3 (some (5,1))=
          some (20,4) := by
        simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 4 (some (5,1))=
          some (12,10) := by
        simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
    · subst time
      have he : BB6.Agent8Section.run secNext 5 (some (5,1))=
          some (17,11) := by
        simp [BB6.Agent8Section.run,secNext,exactSection,bounce]
      rw [he] at htime
      have heq := Option.some.inj htime
      have hx := congrArg Prod.fst heq
      omega
  · have hlong : 6+(time-6)=time := by omega
    have hh : Incoming time (1213+1024*u+1024*v,286+512*v) :=
      s2_root_run_incoming time (5,1) _ htime
    rw [← hlong] at hh
    exact no_six_D_public u v
      (s2_incoming_shrink 6 (time-6) _ hh)

/-- The third strict sixth/seventh image family is absent from the
    genuine blank-origin Machine C section orbit at every time. -/
theorem blank_ne_s2_image (u v t time : Nat)
    (ht : u+v=2+4*t)
    (hv : v%32=(28+11*t)%32) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (641+1024*u,574+1024*v) := by
  intro hrun
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hrun
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at hrun
      | some p =>
          rcases p with ⟨a,k⟩
          have hstep : secNext (a,k)=some
              (641+1024*u) (574+1024*v) := by
            simpa [BB6.Agent8Section.run,hp] using hrun
          have hpre : sectionPreimageAll a k
              (641+1024*u) (574+1024*v) :=
            (section_preimage_all_iff a k _ _).mp hstep
          rcases target_three_parents a k u v hpre with hD|hH1|hH3
          · have hDreach : BB6.Agent3.CReach
                (1213+1024*u+1024*v) (286+512*v) := by
              refine ⟨n,?_⟩
              simpa [hD.1,hD.2] using hp
            exact s2_d_blank_unreachable u v hDreach
          · have hH1reach : BB6.Agent3.CReach
                (301+256*u+256*v) (739+384*u+896*v) := by
              refine ⟨n,?_⟩
              simpa [hH1.1,hH1.2] using hp
            exact s2_h1_blank_unreachable u v t ht hv hH1reach
          · have hH3reach : BB6.Agent3.CReach
                (73+64*u+64*v) (850+480*u+992*v) := by
              refine ⟨n,?_⟩
              simpa [hH3.1,hH3.2] using hp
            exact s2_h3_blank_unreachable u v hH3reach

#print axioms s2_sector_decompose
#print axioms s2_R_parents
#print axioms blank_ne_s2_image

end BB6.Agent4SevenS2
