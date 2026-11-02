import CBack
import Lean.Elab.Tactic.Omega

namespace BB6.CMod128Six
open BB6.CBack BB6.CRange

private theorem eq3 {a b c d e f : Nat}
    (h1:a=d) (h2:b=e) (h3:c=f) :
    ((a,b,c):Nat×Nat×Nat)=(d,e,f) := by
  cases h1; cases h2; cases h3; rfl

/-- A previously unhandled k=2 hub congruent to six modulo eight
has no zero-left predecessor along the actual blank-entry orbit. -/
theorem hub_six_forced (u v:Nat)
    (h:BB6CLine.Reach (8*u+6,2,4*v+4)) :
    BB6CLine.Reach (8*u+7,1,4*v+5) := by
  cases h with
  | next s t hs hn =>
      rcases s with ⟨a,k,c⟩
      rcases c with _ | _ | _ | _ | d
      · rcases a with _ | _ | a
        · simp [BB6CLine.nextC] at hn
        · rcases k with _ | k
          · simp [BB6CLine.nextC] at hn
          · simp [BB6CLine.nextC] at hn
        · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases a with _ | a
        · by_cases he:k%2=0
          · simp only [BB6CLine.nextC,he,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at hn
            have hg := reached_good (0,k,d+4) hs
            simp only [good] at hg
            have hb := hg.1 (by omega)
            omega
          · simp [BB6CLine.nextC,he] at hn
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          rcases hn with ⟨ha,hk,hc⟩
          have he : (a+1,k,d+4) = (8*u+7,1,4*v+5) := by
            apply eq3 <;> omega
          exact he ▸ hs

/-- A uniform inverse move across an even zero-right return with a
forced high hub. Assumes the first-plus-middle sum is odd. -/
theorem even_backward (A K : Nat) (hK:7≤K) (hpar:(A+K)%2=1)
    (h:BB6CLine.Reach (A,K,0))
    (hub : BB6CLine.Reach (A+K-5,2,K-2) →
           BB6CLine.Reach (A+K-4,1,K-1)) :
    BB6CLine.Reach (A+K-2,K/2-1,0) := by
  have hr : BB6CLine.Reach (A+(K-7)+2,2,(K-7)+5) := by
    apply reached_zero_hub A (K-7)
    have he : (A,(K-7)+7,0)=(A,K,0) := by apply eq3 <;> omega
    exact he.symm ▸ h
  have hhub : BB6CLine.Reach (A+K-5,2,K-2) := by
    have he : (A+(K-7)+2,2,(K-7)+5)=(A+K-5,2,K-2) := by
      apply eq3 <;> omega
    exact he ▸ hr
  have h1 := hub hhub
  have h2 : BB6CLine.Reach (A+K-4,1,(K-5)+4) := by
    have he : (A+K-4,1,K-1)=(A+K-4,1,(K-5)+4) := by apply eq3 <;> omega
    exact he ▸ h1
  rcases reached_one_high_or_reset (A+K-4) (K-5) h2 with hp | ⟨k,hk,hr⟩
  · have hi : BB6CLine.Reach (A+K-3,0,K) := by
      have he : (A+K-4+1,0,K-5+5)=(A+K-3,0,K) := by apply eq3 <;> omega
      exact he ▸ hp
    have hh := reached_kzero_odd (A+K-3) K hi
    omega
  · have he : (A+K-4+2,k,0)=(A+K-2,K/2-1,0) := by
      apply eq3 <;> omega
    exact he ▸ hr

/-- First even-indexed inverse section for reset j = 128*t + 6. -/
theorem first_ancestor (t:Nat)
    (h:BB6CLine.Reach (256*t+13,384*t+22,0)) :
    BB6CLine.Reach (640*t+33,192*t+10,0) := by
  have hb : BB6CLine.Reach (256*t+13+ (384*t+22)-5,2,(384*t+22)-2) →
            BB6CLine.Reach (256*t+13+ (384*t+22)-4,1,(384*t+22)-1) := by
    intro hh
    have he : (256*t+13+ (384*t+22)-5,2,(384*t+22)-2) =
              (8*(80*t+3)+6,2,4*(96*t+4)+4) := by apply eq3 <;> omega
    have hp := hub_six_forced (80*t+3) (96*t+4) (he ▸ hh)
    have he2 : (8*(80*t+3)+7,1,4*(96*t+4)+5) =
               (256*t+13+ (384*t+22)-4,1,(384*t+22)-1) := by apply eq3 <;> omega
    exact he2 ▸ hp
  have h1 := even_backward (256*t+13) (384*t+22) (by omega) (by omega) h hb
  have he : (256*t+13+ (384*t+22)-2,(384*t+22)/2-1,0) =
            (640*t+33,192*t+10,0) := by apply eq3 <;> omega
  exact he ▸ h1

/-- Second independent even section preserves the forced zero-left exclusion. -/
theorem second_ancestor (t:Nat)
    (h:BB6CLine.Reach (640*t+33,192*t+10,0)) :
    BB6CLine.Reach (832*t+41,96*t+4,0) := by
  have hb : BB6CLine.Reach (640*t+33+(192*t+10)-5,2,(192*t+10)-2) →
            BB6CLine.Reach (640*t+33+(192*t+10)-4,1,(192*t+10)-1) := by
    intro hh
    have he : (640*t+33+(192*t+10)-5,2,(192*t+10)-2) =
              (8*(104*t+4)+6,2,4*(48*t+1)+4) := by apply eq3 <;> omega
    have hp := hub_six_forced (104*t+4) (48*t+1) (he ▸ hh)
    have he2 : (8*(104*t+4)+7,1,4*(48*t+1)+5) =
               (640*t+33+(192*t+10)-4,1,(192*t+10)-1) := by apply eq3 <;> omega
    exact he2 ▸ hp
  have h1 := even_backward (640*t+33) (192*t+10) (by omega) (by omega) h hb
  have he : (640*t+33+(192*t+10)-2,(192*t+10)/2-1,0) =
            (832*t+41,96*t+4,0) := by apply eq3 <;> omega
  exact he ▸ h1

/-- Third inverse section for t>=1, when the remaining middle counter
is high enough for the universal high-hub calculus. -/
theorem third_ancestor (s:Nat)
    (h:BB6CLine.Reach (832*s+873,96*s+100,0)) :
    BB6CLine.Reach (928*s+971,48*s+49,0) := by
  have hb : BB6CLine.Reach (832*s+873+(96*s+100)-5,2,(96*s+100)-2) →
            BB6CLine.Reach (832*s+873+(96*s+100)-4,1,(96*s+100)-1) := by
    intro hh
    have he : (832*s+873+(96*s+100)-5,2,(96*s+100)-2) =
              (928*s+968,2,(96*s+94)+4) := by apply eq3 <;> omega
    have hp := reached_hub_prev (928*s+968) (96*s+94) (he ▸ hh) (by omega)
    have he2 : (928*s+969,1,96*s+99) =
               (832*s+873+(96*s+100)-4,1,(96*s+100)-1) := by apply eq3 <;> omega
    exact he2 ▸ hp
  have h1 := even_backward (832*s+873) (96*s+100) (by omega) (by omega) h hb
  have he : (832*s+873+(96*s+100)-2,(96*s+100)/2-1,0) =
            (928*s+971,48*s+49,0) := by apply eq3 <;> omega
  exact he ▸ h1

/-- The odd middle-counter ancestor after three even descents, at all t>=1. -/
theorem fourth_ancestor (s:Nat)
    (h:BB6CLine.Reach (928*s+971,48*s+49,0)) :
    BB6CLine.Reach (488*s+508,268*s+277,0) := by
  have hhub : BB6CLine.Reach (976*s+1015,2,48*s+47) := by
    have hi : BB6CLine.Reach (928*s+971,(48*s+42)+7,0) := by
      have he : (928*s+971,(48*s+42)+7,0)=(928*s+971,48*s+49,0) := by
        apply eq3 <;> omega
      exact he.symm ▸ h
    have hp := reached_zero_hub (928*s+971) (48*s+42) hi
    have he : (928*s+971+(48*s+42)+2,2,(48*s+42)+5) =
              (976*s+1015,2,48*s+47) := by apply eq3 <;> omega
    exact he ▸ hp
  have h1 : BB6CLine.Reach (976*s+1016,1,48*s+48) := by
    have hi : BB6CLine.Reach (976*s+1015,2,(48*s+43)+4) := by
      have he : (976*s+1015,2,(48*s+43)+4)=(976*s+1015,2,48*s+47) := by
        apply eq3 <;> omega
      exact he.symm ▸ hhub
    have hp := reached_hub_prev (976*s+1015) (48*s+43) hi (by omega)
    have he : (976*s+1015+1,1,(48*s+43)+5) =
              (976*s+1016,1,48*s+48) := by apply eq3 <;> omega
    exact he ▸ hp
  have h2 : BB6CLine.Reach (976*s+1017,0,48*s+49) := by
    have hi : BB6CLine.Reach (976*s+1016,1,(48*s+44)+4) := by
      have he : (976*s+1016,1,(48*s+44)+4) =
                (976*s+1016,1,48*s+48) := by apply eq3 <;> omega
      exact he.symm ▸ h1
    rcases reached_one_high_or_reset (976*s+1016) (48*s+44) hi with hp | ⟨k,hk,hr⟩
    · have he : (976*s+1016+1,0,(48*s+44)+5) =
                (976*s+1017,0,48*s+49) := by apply eq3 <;> omega
      exact he ▸ hp
    · omega
  have h3 : BB6CLine.Reach (0,488*s+507,48*s+49) := by
    have hi : BB6CLine.Reach ((976*s+1010)+7,0,(48*s+45)+4) := by
      have he : ((976*s+1010)+7,0,(48*s+45)+4) =
                (976*s+1017,0,48*s+49) := by apply eq3 <;> omega
      exact he.symm ▸ h2
    rcases reached_high_kzero_prev (976*s+1010) (48*s+45) hi with ⟨k,ho,heq,hr⟩
    have he : (0,k,(48*s+45)+4)=(0,488*s+507,48*s+49) := by
      apply eq3 <;> omega
    exact he ▸ hr
  have h4 : BB6CLine.Reach (488*s+504,3,536*s+553) := by
    have hi : BB6CLine.Reach (0,0+(488*s+504)+3,(48*s+45)+4) := by
      have he : (0,0+(488*s+504)+3,(48*s+45)+4) =
                (0,488*s+507,48*s+49) := by apply eq3 <;> omega
      exact he.symm ▸ h3
    have hp := reverse_high 0 0 (48*s+45) (488*s+504) hi
    have he : (0+(488*s+504),0+3,(48*s+45)+(488*s+504)+4) =
              (488*s+504,3,536*s+553) := by apply eq3 <;> omega
    exact he ▸ hp
  have h5 : BB6CLine.Reach (488*s+505,2,536*s+554) := by
    have hi : BB6CLine.Reach (488*s+504,0+3,(536*s+549)+4) := by
      have he : (488*s+504,0+3,(536*s+549)+4) =
                (488*s+504,3,536*s+553) := by apply eq3 <;> omega
      exact he.symm ▸ h4
    have hp := reached_high_pred (488*s+504) 0 (536*s+549) hi
    have he : (488*s+504+1,0+2,(536*s+549)+5) =
              (488*s+505,2,536*s+554) := by apply eq3 <;> omega
    exact he ▸ hp
  have h6 : BB6CLine.Reach (488*s+506,1,536*s+555) := by
    have hi : BB6CLine.Reach (488*s+505,2,(536*s+550)+4) := by
      have he : (488*s+505,2,(536*s+550)+4) =
                (488*s+505,2,536*s+554) := by apply eq3 <;> omega
      exact he.symm ▸ h5
    have hp := reached_hub_prev (488*s+505) (536*s+550) hi (by omega)
    have he : (488*s+505+1,1,(536*s+550)+5) =
              (488*s+506,1,536*s+555) := by apply eq3 <;> omega
    exact he ▸ hp
  have hi : BB6CLine.Reach (488*s+506,1,(536*s+551)+4) := by
    have he : (488*s+506,1,(536*s+551)+4) =
              (488*s+506,1,536*s+555) := by apply eq3 <;> omega
    exact he.symm ▸ h6
  rcases reached_one_high_or_reset (488*s+506) (536*s+551) hi with hp | ⟨k,hk,hr⟩
  · have hs : BB6CLine.Reach ((488*s+500)+7,0,(536*s+552)+4) := by
      have he : (488*s+506+1,0,(536*s+551)+5) =
                ((488*s+500)+7,0,(536*s+552)+4) := by apply eq3 <;> omega
      exact he ▸ hp
    rcases reached_high_kzero_prev (488*s+500) (536*s+552) hs with ⟨k,ho,heq,_⟩
    omega
  · have he : (488*s+506+2,k,0)=(488*s+508,268*s+277,0) := by
      apply eq3 <;> omega
    exact he ▸ hr

/-- The only reached high-first-counter state with k=0,c=1 is the
initial (5,0,1) itself. -/
theorem reached_kzero_one (a:Nat) (h:BB6CLine.Reach (a,0,1)) : a=5 := by
  cases h with
  | init => rfl
  | next s t hs hn =>
      rcases s with ⟨x,k,c⟩
      rcases c with _ | _ | _ | _ | d
      · rcases x with _ | _ | x
        · simp [BB6CLine.nextC] at hn
        · rcases k with _ | k
          · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
            omega
          · simp [BB6CLine.nextC] at hn
        · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases x with _ | x
        · by_cases hk:k%2=0 <;> simp [BB6CLine.nextC,hk] at hn
        · simp [BB6CLine.nextC] at hn

/-- Small leftover index six has a forbidden zero-middle predecessor. -/
theorem small_four_unreachable : ¬ BB6CLine.Reach (41,4,0) := by
  intro h
  have hp0 : BB6CLine.Reach (41,3,1) := reached_zero_prev 41 3 h
  have hp1 : BB6CLine.Reach (41,1,3) := reached_one_prev 41 0 hp0
  have hp2 : BB6CLine.Reach (43,1,0) := by
    cases hp1 with
    | next s t hs hn =>
      rcases s with ⟨a,k,c⟩
      rcases c with _ | _ | _ | _ | d
      · rcases a with _ | _ | a
        · simp [BB6CLine.nextC] at hn
        · rcases k with _ | k <;> simp [BB6CLine.nextC] at hn
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          rcases hn with ⟨ha,hk,hc⟩
          have he : (a+2,k,0)=(43,1,0) := by apply eq3 <;> omega
          exact he ▸ hs
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · simp [BB6CLine.nextC] at hn
      · rcases a with _ | a
        · by_cases hk:k%2=0 <;> simp [BB6CLine.nextC,hk] at hn
        · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at hn
          rcases hn with ⟨ha,hk,hc⟩
          have he : (a+1,k,d+4)=(42,0,4) := by apply eq3 <;> omega
          have hf := reached_kzero_odd 42 4 (he ▸ hs)
          omega
  have hp3 : BB6CLine.Reach (43,0,1) := reached_zero_prev 43 0 hp2
  have heq := reached_kzero_one 43 hp3
  omega

/-- A full infinite, previously undecided reset residue family. -/
theorem reset_mod128_six_unreachable (t:Nat) :
    ¬ BB6CLine.Reach (256*t+13,384*t+22,0) := by
  intro h
  have h1 := first_ancestor t h
  have h2 := second_ancestor t h1
  cases t with
  | zero =>
      have hs : BB6CLine.Reach (41,4,0) := by simpa using h2
      exact small_four_unreachable hs
  | succ s =>
      have hs : BB6CLine.Reach (832*s+873,96*s+100,0) := by
        have he : (832*(s+1)+41,96*(s+1)+4,0) = (832*s+873,96*s+100,0) := by
          apply eq3 <;> omega
        exact he ▸ h2
      have h3 := third_ancestor s hs
      have h4 := fourth_ancestor s h3
      have bad := reached_odd_zero_mod4_hole (488*s+508) (268*s+277) h4 (by omega) (by omega)
      omega

#print axioms hub_six_forced
#print axioms reset_mod128_six_unreachable

end BB6.CMod128Six
