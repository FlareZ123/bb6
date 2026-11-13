import OddOddVal3Orbit
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192

namespace BB6.Agent11M0SumZero
open BB6.Agent46

/-- A number greater than two whose residue modulo four is nonzero
    cannot be a power of two. -/
private theorem no_pow_two_of_mod4_ne_zero (S : Nat)
    (hS4 : S % 4 ≠ 0) (hSgt : 2 < S) :
    ∀ n : Nat, S ≠ 2^n := by
  intro n heq
  cases n with
  | zero =>
      simp at heq
      omega
  | succ n =>
      cases n with
      | zero =>
          simp at heq
          omega
      | succ n =>
          change S = 2^(n+2) at heq
          have hp : 2^(n+2) = 4*2^n := by
            rw [show n+2=2+n by omega, Nat.pow_add]
            rfl
          rw [hp] at heq
          omega

/-- Forward-only exact parent necessity for the previously untreated
    even-even, sum-zero-mod-eight source sector. The complete source
    grammar leaves only the direct parent and one even-a bounce parent
    whenever S>2 and S is not divisible by four. No converse is needed. -/
theorem even_even_sumzero_parent (a k x y S : Nat)
    (hx : 0 < x) (hxe : x % 2 = 0)
    (hy : 6 ≤ y) (hye : y % 2 = 0)
    (hsum : x+y = 8*S)
    (hS4 : S % 4 ≠ 0) (hSgt : 2 < S)
    (hedge : secNext (a,k) = some (x,y)) :
    (a = x+y-2 ∧ k = (y-2)/2) ∨
    (a = 2*S-2 ∧ k = (x+2*y-2*S-8)/2) := by
  have hp := (section_preimage_all_iff a k x y).mp hedge
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at hp
        omega
      · have hcase : 4≤y ∧ ∃ n : Nat,
            x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y := by
          simpa [sectionPreimageAll,ha0,hk0,hk1] using hp
        rcases hcase with ⟨_,n,hxy,_⟩
        have hS : S=2^n := by omega
        have hnot := no_pow_two_of_mod4_ne_zero S hS4 hSgt n
        exact False.elim (hnot hS)
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at hp <;> omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at hp <;> omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at hp <;> omega
            · have hcase :
                  (y=3 ∧ ∃ n : Nat, x+6=2^n*16 ∧
                    (2*k-3)+16+3*n=x+10) ∨
                  (5≤y ∧ ∃ n : Nat, x+y+1=2^n*16 ∧
                    (2*k-3)+16+3*n=x+2*y+2) := by
                simpa [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] using hp
              rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hodd,_⟩
              · omega
              · have hdiv : 2 ∣ 2^n*16 := by
                  refine ⟨2^n*8, ?_⟩
                  omega
                have hdiv' : 2 ∣ x+y+1 := by
                  rw [hodd]
                  exact hdiv
                omega
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hp <;> omega
      · by_cases hlow : 2*k≤a
        · have hcase : x=a-2*k ∧ y=2*k+2 := by
            simpa [sectionPreimageAll,ha0,ha1,hk0,hlow] using hp
          rcases hcase with ⟨hx',hy'⟩
          left
          constructor <;> omega
        · by_cases haeven : a%2=0
          · have hcase : 4≤y ∧ ∃ n : Nat,
                x+y=2^n*(2*(a-1)+6) ∧
                (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨_,n,hxy,hcost⟩
            have hnodd : n%2=1 := by omega
            have hn1 : n=1 := by
              by_contra hne
              have hn3 : 3≤n := by omega
              have hdivA : 2∣a := Nat.dvd_of_mod_eq_zero haeven
              rcases hdivA with ⟨b,hb⟩
              have hn' : n=3+(n-3) := by omega
              have hpow : 2^n=8*2^(n-3) := by
                rw [hn',Nat.pow_add]
                rfl
              have hfactor : 2*(a-1)+6=4*(b+1) := by
                rw [hb]
                omega
              have hdivEq : 8*S=32*(2^(n-3)*(b+1)) := by
                calc
                  8*S = x+y := hsum.symm
                  _ = 2^n*(2*(a-1)+6) := hxy
                  _ = (8*2^(n-3))*(4*(b+1)) := by rw [hpow,hfactor]
                  _ = 32*(2^(n-3)*(b+1)) := by
                    simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
              omega
            have hpow1 : 2^n=2 := by rw [hn1]; rfl
            have hxy' : x+y=2*(2*(a-1)+6) := by
              simpa [hpow1] using hxy
            have haEq : a=2*S-2 := by omega
            have hcost' := hcost
            rw [hn1] at hcost'
            have hkEq : k=(x+2*y-2*S-8)/2 := by omega
            right
            exact ⟨haEq,hkEq⟩
          · have hcase :
                (y=3 ∧ ∃ n : Nat, x+6=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
                (5≤y ∧ ∃ n : Nat, x+y+1=2^n*(2*(a-1)+8) ∧
                  (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) := by
              simpa [sectionPreimageAll,ha0,ha1,hk0,hlow,haeven] using hp
            rcases hcase with ⟨hy3,_⟩ | ⟨_,n,hodd,_⟩
            · omega
            · have hdiv : 2∣2^n*(2*(a-1)+8) := by
                refine ⟨2^n*(a+3), ?_⟩
                omega
              have hdiv' : 2∣x+y+1 := by
                rw [hodd]
                exact hdiv
              omega

/-- Every genuine blank-section return to a non-seed state has an
    immediate original-section predecessor that is itself blank-reachable. -/
theorem cReach_parent_of_left_gt5 (x y : Nat)
    (hx : 5<x) (hr : BB6.Agent3.CReach x y) :
    ∃ a k, BB6.Agent3.CReach a k ∧ secNext (a,k)=some (x,y) := by
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          refine ⟨a,k,⟨n,hp⟩,?_⟩
          simpa [BB6.Agent8Section.run,hp] using ht

/-- The source-proved odd-image invariant excludes every positive-time
    blank return with odd right counter and sum one modulo four. -/
theorem blank_no_odd_sum_one (x y : Nat)
    (hx : 5<x) (hy : 5≤y) (ho : y%2=1)
    (hsum : (x+y)%4=1) :
    ¬ BB6.Agent3.CReach x y := by
  intro hr
  rcases hr with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n x y ht hy ho
      omega

/-- Specialization of the complete source grammar to the odd-parameter
    residual A_s=(130+208s,94+152s): exactly the direct and n=1
    even-a bounce parents are possible. -/
theorem m0_odd_ray_parent (s a k : Nat) (hs : s%2=1)
    (hedge : secNext (a,k)=some (130+208*s,94+152*s)) :
    (a=222+360*s ∧ k=46+76*s) ∨
    (a=54+90*s ∧ k=127+211*s) := by
  let S := 28+45*s
  have hx : 0<130+208*s := by omega
  have hxe : (130+208*s)%2=0 := by omega
  have hy : 6≤94+152*s := by omega
  have hye : (94+152*s)%2=0 := by omega
  have hsum : (130+208*s)+(94+152*s)=8*S := by
    dsimp [S]
    omega
  have hS4 : S%4≠0 := by
    dsimp [S]
    omega
  have hSgt : 2<S := by
    dsimp [S]
    omega
  have hp := even_even_sumzero_parent a k
    (130+208*s) (94+152*s) S hx hxe hy hye hsum hS4 hSgt hedge
  rcases hp with ⟨ha,hk⟩ | ⟨ha,hk⟩
  · left
    constructor <;> dsimp [S] at ha hk <;> omega
  · right
    constructor <;> dsimp [S] at ha hk <;> omega

/-- The first two exact inverse edges of the high m=0 stopping target
    apply for every t, not only the t%4=0 subfamily handled by M0FourRoot. -/
theorem mzero_first_two_reach (t : Nat)
    (hr : BB6.Agent3.CReach (17+64*t) (28+96*t)) :
    BB6.Agent3.CReach (26+104*t) (18+76*t) := by
  have hp1 := (six_even_right_blank_reach_iff
    (17+64*t) (28+96*t)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have h1 : BB6.Agent3.CReach (43+160*t) (13+48*t) := by
    have hx : (17+64*t)+(28+96*t)-2=43+160*t := by omega
    have hy : ((28+96*t)-2)/2=13+48*t := by omega
    simpa only [hx,hy] using hp1
  have hp2 := (BB6.Agent3.oddodd_val3_blank_reach_iff
    (43+160*t) (13+48*t)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (26+104*t) (18+76*t) := by
    have hx : ((43+160*t)+(13+48*t)-4)/2=26+104*t := by omega
    have hy : ((43+160*t)+3*(13+48*t)-10)/4=18+76*t := by omega
    change (∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (26+104*t,18+76*t))
    simpa only [hx,hy] using hp2
  exact h2

/-- A sum-zero target with quotient S=2 mod 4 is blank-unreachable
    once both of its only possible source parents are excluded. -/
theorem blank_no_v2one_target (x y S : Nat)
    (hx : 5<x) (hxe : x%2=0)
    (hy : 6≤y) (hye : y%2=0)
    (hsum : x+y=8*S) (hS4 : S%4=2) (hSgt : 2<S)
    (hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2))
    (hE : ¬ BB6.Agent3.CReach (2*S-2) ((x+2*y-2*S-8)/2)) :
    ¬ BB6.Agent3.CReach x y := by
  intro hr
  obtain ⟨a,k,hprev,hstep⟩ :=
    cReach_parent_of_left_gt5 x y hx hr
  have hparents := even_even_sumzero_parent a k x y S
    hx hxe hy hye hsum (by omega) hSgt hstep
  rcases hparents with hDparent | hEparent
  · rcases hDparent with ⟨ha,hk⟩
    subst a
    subst k
    exact hD hprev
  · rcases hEparent with ⟨ha,hk⟩
    subst a
    subst k
    exact hE hprev

/-- The L parent in the j=1895 (mod 2048) candidate has only two
    source parents. Its direct parent takes one six-of-eight edge to an
    odd-image forbidden state; its bounce parent is already forbidden. -/
theorem blank_no_L_t59 (v : Nat) :
    ¬ BB6.Agent3.CReach (10662+11520*v) (2250+2432*v) := by
  let x := 10662+11520*v
  let y := 2250+2432*v
  let S := 1614+1744*v
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    intro hr
    have hDx : x+y-2=12910+13952*v := by dsimp [x,y]; omega
    have hDy : (y-2)/2=1124+1216*v := by dsimp [y]; omega
    have hDreach : BB6.Agent3.CReach (12910+13952*v) (1124+1216*v) := by
      simpa only [hDx,hDy] using hr
    have hp := (six_even_right_blank_reach_iff
      (12910+13952*v) (1124+1216*v)
      (by omega) (by omega) (by omega) (by omega)).mp hDreach
    have hDprime : BB6.Agent3.CReach (14032+15168*v) (561+608*v) := by
      have hx' : (12910+13952*v)+(1124+1216*v)-2=14032+15168*v := by omega
      have hy' : ((1124+1216*v)-2)/2=561+608*v := by omega
      simpa only [hx',hy'] using hp
    exact blank_no_odd_sum_one (14032+15168*v) (561+608*v)
      (by omega) (by omega) (by omega) (by omega) hDprime
  have hE : ¬ BB6.Agent3.CReach (2*S-2) ((x+2*y-2*S-8)/2) := by
    intro hr
    have hEx : 2*S-2=3226+3488*v := by dsimp [S]; omega
    have hEy : (x+2*y-2*S-8)/2=5963+6448*v := by
      dsimp [x,y,S]
      omega
    have hEreach : BB6.Agent3.CReach (3226+3488*v) (5963+6448*v) := by
      simpa only [hEx,hEy] using hr
    exact blank_no_odd_sum_one (3226+3488*v) (5963+6448*v)
      (by omega) (by omega) (by omega) (by omega) hEreach
  change ¬ BB6.Agent3.CReach x y
  exact blank_no_v2one_target x y S
    (by omega) (by omega) (by omega) (by omega)
    (by dsimp [x,y,S]; omega)
    (by dsimp [S]; omega) (by dsimp [S]; omega) hD hE

/-- The second L parent, for j=359 (mod 8192), has the same exact
    two-parent closure, with a distinct affine parameterization. -/
theorem blank_no_L_t11 (w : Nat) :
    ¬ BB6.Agent3.CReach (2022+46080*w) (426+9728*w) := by
  let x := 2022+46080*w
  let y := 426+9728*w
  let S := 306+6976*w
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    intro hr
    have hDx : x+y-2=2446+55808*w := by dsimp [x,y]; omega
    have hDy : (y-2)/2=212+4864*w := by dsimp [y]; omega
    have hDreach : BB6.Agent3.CReach (2446+55808*w) (212+4864*w) := by
      simpa only [hDx,hDy] using hr
    have hp := (six_even_right_blank_reach_iff
      (2446+55808*w) (212+4864*w)
      (by omega) (by omega) (by omega) (by omega)).mp hDreach
    have hDprime : BB6.Agent3.CReach (2656+60672*w) (105+2432*w) := by
      have hx' : (2446+55808*w)+(212+4864*w)-2=2656+60672*w := by omega
      have hy' : ((212+4864*w)-2)/2=105+2432*w := by omega
      simpa only [hx',hy'] using hp
    exact blank_no_odd_sum_one (2656+60672*w) (105+2432*w)
      (by omega) (by omega) (by omega) (by omega) hDprime
  have hE : ¬ BB6.Agent3.CReach (2*S-2) ((x+2*y-2*S-8)/2) := by
    intro hr
    have hEx : 2*S-2=610+13952*w := by dsimp [S]; omega
    have hEy : (x+2*y-2*S-8)/2=1127+25792*w := by
      dsimp [x,y,S]
      omega
    have hEreach : BB6.Agent3.CReach (610+13952*w) (1127+25792*w) := by
      simpa only [hEx,hEy] using hr
    exact blank_no_odd_sum_one (610+13952*w) (1127+25792*w)
      (by omega) (by omega) (by omega) (by omega) hEreach
  change ¬ BB6.Agent3.CReach x y
  exact blank_no_v2one_target x y S
    (by omega) (by omega) (by omega) (by omega)
    (by dsimp [x,y,S]; omega)
    (by dsimp [S]; omega) (by dsimp [S]; omega) hD hE

/-- The B parent in the j=1895 (mod 2048) candidate has three forced
    six-of-eight inverse edges to an odd-image forbidden state. -/
theorem blank_no_B_t59 (v : Nat) :
    ¬ BB6.Agent3.CReach (2664+2880*v) (6246+6752*v) := by
  intro hr
  have hp1 := (six_even_right_blank_reach_iff
    (2664+2880*v) (6246+6752*v)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have h1 : BB6.Agent3.CReach (8908+9632*v) (3122+3376*v) := by
    have hx : (2664+2880*v)+(6246+6752*v)-2=8908+9632*v := by omega
    have hy : ((6246+6752*v)-2)/2=3122+3376*v := by omega
    simpa only [hx,hy] using hp1
  have hp2 := (six_even_right_blank_reach_iff
    (8908+9632*v) (3122+3376*v)
    (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (12028+13008*v) (1560+1688*v) := by
    have hx : (8908+9632*v)+(3122+3376*v)-2=12028+13008*v := by omega
    have hy : ((3122+3376*v)-2)/2=1560+1688*v := by omega
    simpa only [hx,hy] using hp2
  have hp3 := (six_even_right_blank_reach_iff
    (12028+13008*v) (1560+1688*v)
    (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach (13586+14696*v) (779+844*v) := by
    have hx : (12028+13008*v)+(1560+1688*v)-2=13586+14696*v := by omega
    have hy : ((1560+1688*v)-2)/2=779+844*v := by omega
    simpa only [hx,hy] using hp3
  exact blank_no_odd_sum_one (13586+14696*v) (779+844*v)
    (by omega) (by omega) (by omega) (by omega) h3

/-- The B parent in the j=359 (mod 8192) candidate has five forced
    six-of-eight inverse edges to an odd-image forbidden state. -/
theorem blank_no_B_t11 (w : Nat) :
    ¬ BB6.Agent3.CReach (504+11520*w) (1182+27008*w) := by
  intro hr
  have hp1 := (six_even_right_blank_reach_iff
    (504+11520*w) (1182+27008*w)
    (by omega) (by omega) (by omega) (by omega)).mp hr
  have h1 : BB6.Agent3.CReach (1684+38528*w) (590+13504*w) := by
    have hx : (504+11520*w)+(1182+27008*w)-2=1684+38528*w := by omega
    have hy : ((1182+27008*w)-2)/2=590+13504*w := by omega
    simpa only [hx,hy] using hp1
  have hp2 := (six_even_right_blank_reach_iff
    (1684+38528*w) (590+13504*w)
    (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach (2272+52032*w) (294+6752*w) := by
    have hx : (1684+38528*w)+(590+13504*w)-2=2272+52032*w := by omega
    have hy : ((590+13504*w)-2)/2=294+6752*w := by omega
    simpa only [hx,hy] using hp2
  have hp3 := (six_even_right_blank_reach_iff
    (2272+52032*w) (294+6752*w)
    (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach (2564+58784*w) (146+3376*w) := by
    have hx : (2272+52032*w)+(294+6752*w)-2=2564+58784*w := by omega
    have hy : ((294+6752*w)-2)/2=146+3376*w := by omega
    simpa only [hx,hy] using hp3
  have hp4 := (six_even_right_blank_reach_iff
    (2564+58784*w) (146+3376*w)
    (by omega) (by omega) (by omega) (by omega)).mp h3
  have h4 : BB6.Agent3.CReach (2708+62160*w) (72+1688*w) := by
    have hx : (2564+58784*w)+(146+3376*w)-2=2708+62160*w := by omega
    have hy : ((146+3376*w)-2)/2=72+1688*w := by omega
    simpa only [hx,hy] using hp4
  have hp5 := (six_even_right_blank_reach_iff
    (2708+62160*w) (72+1688*w)
    (by omega) (by omega) (by omega) (by omega)).mp h4
  have h5 : BB6.Agent3.CReach (2778+63848*w) (35+844*w) := by
    have hx : (2708+62160*w)+(72+1688*w)-2=2778+63848*w := by omega
    have hy : ((72+1688*w)-2)/2=35+844*w := by omega
    simpa only [hx,hy] using hp5
  exact blank_no_odd_sum_one (2778+63848*w) (35+844*w)
    (by omega) (by omega) (by omega) (by omega) h5

/-- The odd-parameter A_s residual is blank-unreachable on the two
    disjoint progressions that close its direct and bounce parents. -/
theorem blank_no_A_t59 (v : Nat) :
    ¬ BB6.Agent3.CReach (6162+6656*v) (4502+4864*v) := by
  have hL : ¬ BB6.Agent3.CReach
      (222+360*(32*v+29)) (46+76*(32*v+29)) := by
    have hx : 222+360*(32*v+29)=10662+11520*v := by omega
    have hy : 46+76*(32*v+29)=2250+2432*v := by omega
    simpa only [hx,hy] using blank_no_L_t59 v
  have hB : ¬ BB6.Agent3.CReach
      (54+90*(32*v+29)) (127+211*(32*v+29)) := by
    have hx : 54+90*(32*v+29)=2664+2880*v := by omega
    have hy : 127+211*(32*v+29)=6246+6752*v := by omega
    simpa only [hx,hy] using blank_no_B_t59 v
  have hA := blank_no_A_from_two_parents (32*v+29) (by omega) hL hB
  have hx : 130+208*(32*v+29)=6162+6656*v := by omega
  have hy : 94+152*(32*v+29)=4502+4864*v := by omega
  simpa only [hx,hy] using hA
where
  blank_no_A_from_two_parents (s : Nat) (hs : s%2=1)
      (hL : ¬ BB6.Agent3.CReach (222+360*s) (46+76*s))
      (hB : ¬ BB6.Agent3.CReach (54+90*s) (127+211*s)) :
      ¬ BB6.Agent3.CReach (130+208*s) (94+152*s) := by
    intro hr
    obtain ⟨a,k,hprev,hstep⟩ :=
      cReach_parent_of_left_gt5 (130+208*s) (94+152*s) (by omega) hr
    have hp := m0_odd_ray_parent s a k hs hstep
    rcases hp with ⟨ha,hk⟩ | ⟨ha,hk⟩
    · subst a
      subst k
      exact hL hprev
    · subst a
      subst k
      exact hB hprev

/-- The second odd-parameter A_s progression closes the disjoint
    high-stop family j=359+8192w. -/
theorem blank_no_A_t11 (w : Nat) :
    ¬ BB6.Agent3.CReach (1170+26624*w) (854+19456*w) := by
  have hL : ¬ BB6.Agent3.CReach
      (222+360*(128*w+5)) (46+76*(128*w+5)) := by
    have hx : 222+360*(128*w+5)=2022+46080*w := by omega
    have hy : 46+76*(128*w+5)=426+9728*w := by omega
    simpa only [hx,hy] using blank_no_L_t11 w
  have hB : ¬ BB6.Agent3.CReach
      (54+90*(128*w+5)) (127+211*(128*w+5)) := by
    have hx : 54+90*(128*w+5)=504+11520*w := by omega
    have hy : 127+211*(128*w+5)=1182+27008*w := by omega
    simpa only [hx,hy] using blank_no_B_t11 w
  have hA := blank_no_A_from_two_parents (128*w+5) (by omega) hL hB
  have hx : 130+208*(128*w+5)=1170+26624*w := by omega
  have hy : 94+152*(128*w+5)=854+19456*w := by omega
  simpa only [hx,hy] using hA
where
  blank_no_A_from_two_parents (s : Nat) (hs : s%2=1)
      (hL : ¬ BB6.Agent3.CReach (222+360*s) (46+76*s))
      (hB : ¬ BB6.Agent3.CReach (54+90*s) (127+211*s)) :
      ¬ BB6.Agent3.CReach (130+208*s) (94+152*s) := by
    intro hr
    obtain ⟨a,k,hprev,hstep⟩ :=
      cReach_parent_of_left_gt5 (130+208*s) (94+152*s) (by omega) hr
    have hp := m0_odd_ray_parent s a k hs hstep
    rcases hp with ⟨ha,hk⟩ | ⟨ha,hk⟩
    · subst a
      subst k
      exact hL hprev
    · subst a
      subst k
      exact hB hprev

/-- Original high m=0 stopping targets with j=1895+2048v are
    genuinely blank-unreachable for every v. -/
theorem blank_no_high_m0_j1895 (v : Nat) :
    ¬ BB6.Agent3.CReach (2*(1895+2048*v)+3) (5692+6144*v) := by
  intro hr
  have hroot : BB6.Agent3.CReach
      (17+64*(64*v+59)) (28+96*(64*v+59)) := by
    have hx : 2*(1895+2048*v)+3=17+64*(64*v+59) := by omega
    have hy : 5692+6144*v=28+96*(64*v+59) := by omega
    simpa only [hx,hy] using hr
  have hA := mzero_first_two_reach (64*v+59) hroot
  have hx : 26+104*(64*v+59)=6162+6656*v := by omega
  have hy : 18+76*(64*v+59)=4502+4864*v := by omega
  have hA' : BB6.Agent3.CReach (6162+6656*v) (4502+4864*v) := by
    simpa only [hx,hy] using hA
  exact blank_no_A_t59 v hA'

/-- Original high m=0 stopping targets with j=359+8192w are
    genuinely blank-unreachable for every w. -/
theorem blank_no_high_m0_j359 (w : Nat) :
    ¬ BB6.Agent3.CReach (2*(359+8192*w)+3) (1084+24576*w) := by
  intro hr
  have hroot : BB6.Agent3.CReach
      (17+64*(256*w+11)) (28+96*(256*w+11)) := by
    have hx : 2*(359+8192*w)+3=17+64*(256*w+11) := by omega
    have hy : 1084+24576*w=28+96*(256*w+11) := by omega
    simpa only [hx,hy] using hr
  have hA := mzero_first_two_reach (256*w+11) hroot
  have hx : 26+104*(256*w+11)=1170+26624*w := by omega
  have hy : 18+76*(256*w+11)=854+19456*w := by omega
  have hA' : BB6.Agent3.CReach (1170+26624*w) (854+19456*w) := by
    simpa only [hx,hy] using hA
  exact blank_no_A_t11 w hA'

#print axioms even_even_sumzero_parent
#print axioms m0_odd_ray_parent
#print axioms blank_no_A_t59
#print axioms blank_no_A_t11
#print axioms blank_no_high_m0_j1895
#print axioms blank_no_high_m0_j359

end BB6.Agent11M0SumZero
