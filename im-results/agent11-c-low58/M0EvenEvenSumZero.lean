import OddOddVal3Orbit
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 16384

namespace BB6.Agent11M0SumZeroVerified
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
              · have hoddxy : (x+y+1)%2=1 := by omega
                have hprod : (2^n*16)%2=0 := by simp [Nat.mul_mod]
                rw [hodd] at hoddxy
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
              by_cases h : n=1
              · exact h
              · have hn3 : 3≤n := by omega
                have hdivA : 2∣a := Nat.dvd_of_mod_eq_zero haeven
                rcases hdivA with ⟨b,hb⟩
                have hpow : 2^n=8*2^(n-3) := by
                  calc
                    2^n = 2^(3+(n-3)) := by
                      congr 1
                      omega
                    _ = 2^3*2^(n-3) := by rw [Nat.pow_add]
                    _ = 8*2^(n-3) := by rfl
                have hfactor : 2*(a-1)+6=4*(b+1) := by
                  rw [hb]
                  omega
                have hdiv32 : 32∣x+y := by
                  refine ⟨2^(n-3)*(b+1), ?_⟩
                  calc
                    x+y = 2^n*(2*(a-1)+6) := hxy
                    _ = (8*2^(n-3))*(4*(b+1)) := by rw [hpow,hfactor]
                    _ = 32*(2^(n-3)*(b+1)) := by
                      simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
                rcases hdiv32 with ⟨q,hq⟩
                have hSdiv : S=4*q := by omega
                have hSzero : S%4=0 := by rw [hSdiv]; simp
                exact (hS4 hSzero).elim
            have hpow1 : 2^n=2 := by rw [hn1]
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
            · have hoddxy : (x+y+1)%2=1 := by omega
              have hfac : (2*(a-1)+8)%2=0 := by omega
              have hprod : (2^n*(2*(a-1)+8))%2=0 := by
                simp [Nat.mul_mod,hfac]
              rw [hodd] at hoddxy
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
    constructor <;> omega
  · right
    constructor <;> omega

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
  have hx0 : 0<x := by omega
  have hparents := even_even_sumzero_parent a k x y S
    hx0 hxe hy hye hsum (by omega) hSgt hstep
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
    have hx : 222+360*(32*v+29)=10662+11520*v := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    have hy : 46+76*(32*v+29)=2250+2432*v := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    simpa only [hx,hy] using blank_no_L_t59 v
  have hB : ¬ BB6.Agent3.CReach
      (54+90*(32*v+29)) (127+211*(32*v+29)) := by
    have hx : 54+90*(32*v+29)=2664+2880*v := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    have hy : 127+211*(32*v+29)=6246+6752*v := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    simpa only [hx,hy] using blank_no_B_t59 v
  have hA := blank_no_A_from_two_parents (32*v+29) (by omega) hL hB
  have hx : 130+208*(32*v+29)=6162+6656*v := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
  have hy : 94+152*(32*v+29)=4502+4864*v := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
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
    have hx : 222+360*(128*w+5)=2022+46080*w := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    have hy : 46+76*(128*w+5)=426+9728*w := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    simpa only [hx,hy] using blank_no_L_t11 w
  have hB : ¬ BB6.Agent3.CReach
      (54+90*(128*w+5)) (127+211*(128*w+5)) := by
    have hx : 54+90*(128*w+5)=504+11520*w := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    have hy : 127+211*(128*w+5)=1182+27008*w := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    simpa only [hx,hy] using blank_no_B_t11 w
  have hA := blank_no_A_from_two_parents (128*w+5) (by omega) hL hB
  have hx : 130+208*(128*w+5)=1170+26624*w := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
  have hy : 94+152*(128*w+5)=854+19456*w := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
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
    have hx : 2*(1895+2048*v)+3=17+64*(64*v+59) := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    have hy : 5692+6144*v=28+96*(64*v+59) := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    simpa only [hx,hy] using hr
  have hA := mzero_first_two_reach (64*v+59) hroot
  have hx : 26+104*(64*v+59)=6162+6656*v := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
  have hy : 18+76*(64*v+59)=4502+4864*v := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
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
    have hx : 2*(359+8192*w)+3=17+64*(256*w+11) := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    have hy : 1084+24576*w=28+96*(256*w+11) := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
    simpa only [hx,hy] using hr
  have hA := mzero_first_two_reach (256*w+11) hroot
  have hx : 26+104*(256*w+11)=1170+26624*w := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
  have hy : 18+76*(256*w+11)=854+19456*w := by simp [Nat.mul_add, ← Nat.mul_assoc] <;> omega
  have hA' : BB6.Agent3.CReach (1170+26624*w) (854+19456*w) := by
    simpa only [hx,hy] using hA
  exact blank_no_A_t11 w hA'


/-- A general source-parent exclusion for an even-even sum-zero target
    when S is not divisible by four. This allows both residues 2 and 3
    modulo four, not only the valuation-one case. -/
theorem blank_no_sumzero_target (x y S : Nat)
    (hx : 5<x) (hxe : x%2=0)
    (hy : 6≤y) (hye : y%2=0)
    (hsum : x+y=8*S) (hS4 : S%4≠0) (hSgt : 2<S)
    (hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2))
    (hE : ¬ BB6.Agent3.CReach (2*S-2) ((x+2*y-2*S-8)/2)) :
    ¬ BB6.Agent3.CReach x y := by
  intro hr
  obtain ⟨a,k,hprev,hstep⟩ :=
    cReach_parent_of_left_gt5 x y hx hr
  have hx0 : 0<x := by omega
  have hparents := even_even_sumzero_parent a k x y S
    hx0 hxe hy hye hsum hS4 hSgt hstep
  rcases hparents with hDparent | hEparent
  · rcases hDparent with ⟨ha,hk⟩
    subst a
    subst k
    exact hD hprev
  · rcases hEparent with ⟨ha,hk⟩
    subst a
    subst k
    exact hE hprev

/-- Every L_s branch is excluded when s=5 modulo eight. Its direct
    parent has a forced six-of-eight inverse, and its bounce parent is
    itself an odd-image forbidden state. -/
theorem blank_no_L_s_mod8_five (s : Nat) (hs : s%8=5) :
    ¬ BB6.Agent3.CReach (222+360*s) (46+76*s) := by
  let q := s/8
  have hsform : s=8*q+5 := by
    dsimp [q]
    omega
  let x := 2022+2880*q
  let y := 426+608*q
  let S := 306+436*q
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    intro hD0
    have hxD : x+y-2=2446+3488*q := by dsimp [x,y]; omega
    have hyD : (y-2)/2=212+304*q := by dsimp [y]; omega
    have hDreach : BB6.Agent3.CReach
        (2446+3488*q) (212+304*q) := by
      simpa only [hxD,hyD] using hD0
    have hp := (six_even_right_blank_reach_iff
      (2446+3488*q) (212+304*q)
      (by omega) (by omega) (by omega) (by omega)).mp hDreach
    have hDprime : BB6.Agent3.CReach
        (2656+3792*q) (105+152*q) := by
      have hx' : (2446+3488*q)+(212+304*q)-2=2656+3792*q := by omega
      have hy' : ((212+304*q)-2)/2=105+152*q := by omega
      simpa only [hx',hy'] using hp
    exact blank_no_odd_sum_one (2656+3792*q) (105+152*q)
      (by omega) (by omega) (by omega) (by omega) hDprime
  have hE : ¬ BB6.Agent3.CReach (2*S-2)
      ((x+2*y-2*S-8)/2) := by
    intro hE0
    have hxE : 2*S-2=610+872*q := by dsimp [S]; omega
    have hyE : (x+2*y-2*S-8)/2=1127+1612*q := by
      dsimp [x,y,S]
      omega
    have hEreach : BB6.Agent3.CReach
        (610+872*q) (1127+1612*q) := by
      simpa only [hxE,hyE] using hE0
    exact blank_no_odd_sum_one (610+872*q) (1127+1612*q)
      (by omega) (by omega) (by omega) (by omega) hEreach
  have hnot : ¬ BB6.Agent3.CReach x y :=
    blank_no_sumzero_target x y S
      (by dsimp [x]; omega) (by dsimp [x]; omega)
      (by dsimp [y]; omega) (by dsimp [y]; omega)
      (by dsimp [x,y,S]; omega)
      (by dsimp [S]; omega) (by dsimp [S]; omega) hD hE
  change ¬ BB6.Agent3.CReach (222+360*s) (46+76*s)
  simpa only [show 222+360*s=x by dsimp [x]; rw [hsform]; omega,
              show 46+76*s=y by dsimp [y]; rw [hsform]; omega] using hnot

/-- The bounce branch B_(0,s), for s=256w+85, has three forced
    six-of-eight inverses to a second even-even sum-zero target. -/
theorem blank_no_B_s85 (w : Nat) :
    ¬ BB6.Agent3.CReach (7704+23040*w) (18062+54016*w) := by
  intro hB
  have hp1 := (six_even_right_blank_reach_iff
    (7704+23040*w) (18062+54016*w)
    (by omega) (by omega) (by omega) (by omega)).mp hB
  have h1 : BB6.Agent3.CReach
      (25764+77056*w) (9030+27008*w) := by
    have hx : (7704+23040*w)+(18062+54016*w)-2=25764+77056*w := by omega
    have hy : ((18062+54016*w)-2)/2=9030+27008*w := by omega
    simpa only [hx,hy] using hp1
  have hp2 := (six_even_right_blank_reach_iff
    (25764+77056*w) (9030+27008*w)
    (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach
      (34792+104064*w) (4514+13504*w) := by
    have hx : (25764+77056*w)+(9030+27008*w)-2=34792+104064*w := by omega
    have hy : ((9030+27008*w)-2)/2=4514+13504*w := by omega
    simpa only [hx,hy] using hp2
  have hp3 := (six_even_right_blank_reach_iff
    (34792+104064*w) (4514+13504*w)
    (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach
      (39304+117568*w) (2256+6752*w) := by
    have hx : (34792+104064*w)+(4514+13504*w)-2=39304+117568*w := by omega
    have hy : ((4514+13504*w)-2)/2=2256+6752*w := by omega
    simpa only [hx,hy] using hp3
  let x := 39304+117568*w
  let y := 2256+6752*w
  let S := 5195+15540*w
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    intro hD0
    have hxD : x+y-2=41558+124320*w := by dsimp [x,y]; omega
    have hyD : (y-2)/2=1127+3376*w := by dsimp [y]; omega
    have hDreach : BB6.Agent3.CReach
        (41558+124320*w) (1127+3376*w) := by
      simpa only [hxD,hyD] using hD0
    exact blank_no_odd_sum_one (41558+124320*w) (1127+3376*w)
      (by omega) (by omega) (by omega) (by omega) hDreach
  have hE : ¬ BB6.Agent3.CReach (2*S-2)
      ((x+2*y-2*S-8)/2) := by
    intro hE0
    have hxE : 2*S-2=10388+31080*w := by dsimp [S]; omega
    have hyE : (x+2*y-2*S-8)/2=16709+49996*w := by
      dsimp [x,y,S]
      omega
    have hEreach : BB6.Agent3.CReach
        (10388+31080*w) (16709+49996*w) := by
      simpa only [hxE,hyE] using hE0
    exact blank_no_odd_sum_one (10388+31080*w) (16709+49996*w)
      (by omega) (by omega) (by omega) (by omega) hEreach
  have hnot : ¬ BB6.Agent3.CReach x y :=
    blank_no_sumzero_target x y S
      (by dsimp [x]; omega) (by dsimp [x]; omega)
      (by dsimp [y]; omega) (by dsimp [y]; omega)
      (by dsimp [x,y,S]; omega)
      (by dsimp [S]; omega) (by dsimp [S]; omega) hD hE
  exact hnot h3

/-- The odd-parameter residual A_(256w+85) has both source-parent
    branches excluded: L_s by the general s=5 mod 8 lemma, and B_s by
    three forced six-of-eight edges followed by the generic sum-zero
    parent lemma. -/
theorem blank_no_A_s85 (w : Nat) :
    ¬ BB6.Agent3.CReach (17810+53248*w) (13014+38912*w) := by
  let s := 256*w+85
  have hx : 130+208*s=17810+53248*w := by dsimp [s]; omega
  have hy : 94+152*s=13014+38912*w := by
    dsimp [s]
    rw [Nat.mul_add, ← Nat.mul_assoc,
      show 152*256=38912 by decide,
      show 152*85=12920 by decide]
    calc
      94 + (38912*w + 12920) = 94 + (12920 + 38912*w) := by
        rw [Nat.add_comm (38912*w) 12920]
      _ = (94+12920) + 38912*w := by
        rw [← Nat.add_assoc]
      _ = 13014 + 38912*w := by
        rw [show 94+12920=13014 by decide]
  intro hA
  have hA' : BB6.Agent3.CReach (130+208*s) (94+152*s) := by
    simpa only [hx,hy] using hA
  obtain ⟨a,k,hprev,hstep⟩ :=
    cReach_parent_of_left_gt5 (130+208*s) (94+152*s) (by omega) hA'
  have hp := m0_odd_ray_parent s a k (by dsimp [s]; omega) hstep
  rcases hp with ⟨ha,hk⟩ | ⟨ha,hk⟩
  · subst a
    subst k
    exact blank_no_L_s_mod8_five s (by dsimp [s]; omega) hprev
  · subst a
    subst k
    have hxB : 54+90*s=7704+23040*w := by dsimp [s]; omega
    have hyB : 127+211*s=18062+54016*w := by
      dsimp [s]
      rw [Nat.mul_add, ← Nat.mul_assoc,
        show 211*256=54016 by decide,
        show 211*85=17935 by decide]
      calc
        127 + (54016*w + 17935) = 127 + (17935 + 54016*w) := by
          rw [Nat.add_comm (54016*w) 17935]
        _ = (127+17935) + 54016*w := by
          rw [← Nat.add_assoc]
        _ = 18062 + 54016*w := by
          rw [show 127+17935=18062 by decide]
    have hB : BB6.Agent3.CReach
        (7704+23040*w) (18062+54016*w) := by
      simpa only [hxB,hyB] using hprev
    exact blank_no_B_s85 w hB

/-- Original-blank high stopping targets with j=5479 modulo 16384
    are unreachable for every parameter w. -/
theorem blank_no_high_m0_j5479 (w : Nat) :
    ¬ BB6.Agent3.CReach
      (2*(5479+16384*w)+3) (16444+49152*w) := by
  let t := 512*w+171
  have hx : 2*(5479+16384*w)+3=17+64*t := by dsimp [t]; omega
  have hy : 16444+49152*w=28+96*t := by dsimp [t]; omega
  intro hr
  have hroot : BB6.Agent3.CReach (17+64*t) (28+96*t) := by
    simpa only [hx,hy] using hr
  have hA := mzero_first_two_reach t hroot
  have hxA : 26+104*t=17810+53248*w := by dsimp [t]; omega
  have hyA : 18+76*t=13014+38912*w := by
    dsimp [t]
    rw [Nat.mul_add, ← Nat.mul_assoc,
      show 76*512=38912 by decide,
      show 76*171=12996 by decide]
    calc
      18 + (38912*w + 12996) = 18 + (12996 + 38912*w) := by
        rw [Nat.add_comm (38912*w) 12996]
      _ = (18+12996) + 38912*w := by
        rw [← Nat.add_assoc]
      _ = 13014 + 38912*w := by
        rw [show 18+12996=13014 by decide]
  have hA' : BB6.Agent3.CReach
      (17810+53248*w) (13014+38912*w) := by
    simpa only [hxA,hyA] using hA
  exact blank_no_A_s85 w hA'

/-- The high m=0 stopping equation and j=5479 (mod 16384) fix k,
    so the preceding root exclusion removes this whole stop family. -/
theorem high_stop_mzero_5479 (j k : Nat)
    (hj : j%16384=5479)
    (hstop : k+j+3*0+5=(2:Nat)^(2*0+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let w := (j-5479)/16384
  have hjform : j=5479+16384*w := by dsimp [w]; omega
  have hp : (2:Nat)^(2*0+2)=4 := by decide
  rw [hp] at hstop
  have hkform : k=16444+49152*w := by rw [hjform] at hstop; omega
  have hxform : 2*j+3=2*(5479+16384*w)+3 := by rw [hjform]
  intro hr
  have hr' : BB6.Agent3.CReach
      (2*(5479+16384*w)+3) (16444+49152*w) := by
    simpa only [hxform,hkform] using hr
  exact blank_no_high_m0_j5479 w hr'


/-- The B_s branch for s=512w+165 is forced through five
    six-of-eight inverses to an even-even sum-zero target. -/
theorem blank_no_B_s165 (w : Nat) :
    ¬ BB6.Agent3.CReach (20664+92160*w) (48446+216064*w) := by
  intro h0
  have hp1 := (six_even_right_blank_reach_iff
    (20664+92160*w) (48446+216064*w)
    (by omega) (by omega) (by omega) (by omega)).mp h0
  have h1 : BB6.Agent3.CReach
      (69108+308224*w) (24222+108032*w) := by
    have hx : (20664+92160*w)+(48446+216064*w)-2=69108+308224*w := by omega
    have hy : ((48446+216064*w)-2)/2=24222+108032*w := by omega
    simpa only [hx,hy] using hp1
  have hp2 := (six_even_right_blank_reach_iff
    (69108+308224*w) (24222+108032*w)
    (by omega) (by omega) (by omega) (by omega)).mp h1
  have h2 : BB6.Agent3.CReach
      (93328+416256*w) (12110+54016*w) := by
    have hx : (69108+308224*w)+(24222+108032*w)-2=93328+416256*w := by omega
    have hy : ((24222+108032*w)-2)/2=12110+54016*w := by omega
    simpa only [hx,hy] using hp2
  have hp3 := (six_even_right_blank_reach_iff
    (93328+416256*w) (12110+54016*w)
    (by omega) (by omega) (by omega) (by omega)).mp h2
  have h3 : BB6.Agent3.CReach
      (105436+470272*w) (6054+27008*w) := by
    have hx : (93328+416256*w)+(12110+54016*w)-2=105436+470272*w := by omega
    have hy : ((12110+54016*w)-2)/2=6054+27008*w := by omega
    simpa only [hx,hy] using hp3
  have hp4 := (six_even_right_blank_reach_iff
    (105436+470272*w) (6054+27008*w)
    (by omega) (by omega) (by omega) (by omega)).mp h3
  have h4 : BB6.Agent3.CReach
      (111488+497280*w) (3026+13504*w) := by
    have hx : (105436+470272*w)+(6054+27008*w)-2=111488+497280*w := by omega
    have hy : ((6054+27008*w)-2)/2=3026+13504*w := by omega
    simpa only [hx,hy] using hp4
  have hp5 := (six_even_right_blank_reach_iff
    (111488+497280*w) (3026+13504*w)
    (by omega) (by omega) (by omega) (by omega)).mp h4
  have h5 : BB6.Agent3.CReach
      (114512+510784*w) (1512+6752*w) := by
    have hx : (111488+497280*w)+(3026+13504*w)-2=114512+510784*w := by omega
    have hy : ((3026+13504*w)-2)/2=1512+6752*w := by omega
    simpa only [hx,hy] using hp5
  let x := 114512+510784*w
  let y := 1512+6752*w
  let S := 14503+64692*w
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    intro hD0
    have hxD : x+y-2=116022+517536*w := by dsimp [x,y]; omega
    have hyD : (y-2)/2=755+3376*w := by dsimp [y]; omega
    have hDreach : BB6.Agent3.CReach
        (116022+517536*w) (755+3376*w) := by
      simpa only [hxD,hyD] using hD0
    exact blank_no_odd_sum_one (116022+517536*w) (755+3376*w)
      (by omega) (by omega) (by omega) (by omega) hDreach
  have hE : ¬ BB6.Agent3.CReach (2*S-2)
      ((x+2*y-2*S-8)/2) := by
    intro hE0
    have hxE : 2*S-2=29004+129384*w := by dsimp [S]; omega
    have hyE : (x+2*y-2*S-8)/2=44261+197452*w := by
      dsimp [x,y,S]
      omega
    have hEreach : BB6.Agent3.CReach
        (29004+129384*w) (44261+197452*w) := by
      simpa only [hxE,hyE] using hE0
    exact blank_no_odd_sum_one (29004+129384*w) (44261+197452*w)
      (by omega) (by omega) (by omega) (by omega) hEreach
  have hnot : ¬ BB6.Agent3.CReach x y :=
    blank_no_sumzero_target x y S
      (by dsimp [x]; omega) (by dsimp [x]; omega)
      (by dsimp [y]; omega) (by dsimp [y]; omega)
      (by dsimp [x,y,S]; omega)
      (by dsimp [S]; omega) (by dsimp [S]; omega) hD hE
  exact hnot h5

/-- A_(512w+165) has its two source parents excluded: L_s by the
    all-s=5 mod 8 lemma, and B_s by the five-step inverse chain above. -/
theorem blank_no_A_s165 (w : Nat) :
    ¬ BB6.Agent3.CReach (34450+106496*w) (25174+77824*w) := by
  let s := 512*w+165
  have hx : 130+208*s=34450+106496*w := by
    dsimp [s]
    rw [Nat.mul_add, ← Nat.mul_assoc,
      show 208*512=106496 by decide,
      show 208*165=34320 by decide]
    calc
      130 + (106496*w + 34320) = 130 + (34320 + 106496*w) := by
        rw [Nat.add_comm (106496*w) 34320]
      _ = (130+34320) + 106496*w := by
        rw [← Nat.add_assoc]
      _ = 34450 + 106496*w := by
        rw [show 130+34320=34450 by decide]
  have hy : 94+152*s=25174+77824*w := by
    dsimp [s]
    rw [Nat.mul_add, ← Nat.mul_assoc,
      show 152*512=77824 by decide,
      show 152*165=25080 by decide]
    calc
      94 + (77824*w + 25080) = 94 + (25080 + 77824*w) := by
        rw [Nat.add_comm (77824*w) 25080]
      _ = (94+25080) + 77824*w := by
        rw [← Nat.add_assoc]
      _ = 25174 + 77824*w := by
        rw [show 94+25080=25174 by decide]
  intro hA
  have hA' : BB6.Agent3.CReach (130+208*s) (94+152*s) := by
    simpa only [hx,hy] using hA
  obtain ⟨a,k,hprev,hstep⟩ :=
    cReach_parent_of_left_gt5 (130+208*s) (94+152*s) (by omega) hA'
  have hp := m0_odd_ray_parent s a k (by dsimp [s]; omega) hstep
  rcases hp with ⟨ha,hk⟩ | ⟨ha,hk⟩
  · subst a
    subst k
    exact blank_no_L_s_mod8_five s (by dsimp [s]; omega) hprev
  · subst a
    subst k
    have hxB : 54+90*s=14904+46080*w := by
      dsimp [s]
      rw [Nat.mul_add, ← Nat.mul_assoc,
        show 90*512=46080 by decide,
        show 90*165=14850 by decide]
      calc
        54 + (46080*w + 14850) = 54 + (14850 + 46080*w) := by
          rw [Nat.add_comm (46080*w) 14850]
        _ = (54+14850) + 46080*w := by
          rw [← Nat.add_assoc]
        _ = 14904 + 46080*w := by
          rw [show 54+14850=14904 by decide]
    have hyB : 127+211*s=34942+108032*w := by
      dsimp [s]
      rw [Nat.mul_add, ← Nat.mul_assoc,
        show 211*512=108032 by decide,
        show 211*165=34815 by decide]
      calc
        127 + (108032*w + 34815) = 127 + (34815 + 108032*w) := by
          rw [Nat.add_comm (108032*w) 34815]
        _ = (127+34815) + 108032*w := by
          rw [← Nat.add_assoc]
        _ = 34942 + 108032*w := by
          rw [show 127+34815=34942 by decide]
    have hB : BB6.Agent3.CReach
        (14904+46080*w) (34942+108032*w) := by
      simpa only [hxB,hyB] using hprev
    exact blank_no_B_s165 w hB

/-- Original-blank high stopping targets with j=10599 modulo 32768
    are unreachable for every parameter w. -/
theorem blank_no_high_m0_j10599 (w : Nat) :
    ¬ BB6.Agent3.CReach
      (2*(10599+32768*w)+3) (31804+98304*w) := by
  let t := 1024*w+331
  have hx : 2*(10599+32768*w)+3=17+64*t := by dsimp [t]; omega
  have hy : 31804+98304*w=28+96*t := by dsimp [t]; omega
  intro hr
  have hroot : BB6.Agent3.CReach (17+64*t) (28+96*t) := by
    simpa only [hx,hy] using hr
  have hA := mzero_first_two_reach t hroot
  have hxA : 26+104*t=34450+106496*w := by dsimp [t]; omega
  have hyA : 18+76*t=25174+77824*w := by
    dsimp [t]
    rw [Nat.mul_add, ← Nat.mul_assoc,
      show 76*1024=77824 by decide,
      show 76*331=25156 by decide]
    calc
      18 + (77824*w + 25156) = 18 + (25156 + 77824*w) := by
        rw [Nat.add_comm (77824*w) 25156]
      _ = (18+25156) + 77824*w := by
        rw [← Nat.add_assoc]
      _ = 25174 + 77824*w := by
        rw [show 18+25156=25174 by decide]
  have hA' : BB6.Agent3.CReach
      (34450+106496*w) (25174+77824*w) := by
    simpa only [hxA,hyA] using hA
  exact blank_no_A_s165 w hA'

/-- The high m=0 stopping equation and j=10599 (mod 32768) fix k,
    so the preceding root exclusion removes this whole stop family. -/
theorem high_stop_mzero_10599 (j k : Nat)
    (hj : j%32768=10599)
    (hstop : k+j+3*0+5=(2:Nat)^(2*0+2)*(j+3)) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  let w := (j-10599)/32768
  have hjform : j=10599+32768*w := by dsimp [w]; omega
  have hp : (2:Nat)^(2*0+2)=4 := by decide
  rw [hp] at hstop
  have hkform : k=31804+98304*w := by rw [hjform] at hstop; omega
  have hxform : 2*j+3=2*(10599+32768*w)+3 := by rw [hjform]
  intro hr
  have hr' : BB6.Agent3.CReach
      (2*(10599+32768*w)+3) (31804+98304*w) := by
    simpa only [hxform,hkform] using hr
  exact blank_no_high_m0_j10599 w hr'

#print axioms blank_no_B_s165
#print axioms blank_no_A_s165
#print axioms blank_no_high_m0_j10599
#print axioms high_stop_mzero_10599


#print axioms blank_no_L_s_mod8_five
#print axioms blank_no_B_s85
#print axioms blank_no_A_s85
#print axioms blank_no_high_m0_j5479
#print axioms high_stop_mzero_5479


#print axioms even_even_sumzero_parent
#print axioms m0_odd_ray_parent
#print axioms blank_no_A_t59
#print axioms blank_no_A_t11
#print axioms blank_no_high_m0_j1895
#print axioms blank_no_high_m0_j359

end BB6.Agent11M0SumZeroVerified
