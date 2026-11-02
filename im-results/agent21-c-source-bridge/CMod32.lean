import CBack
import Lean.Elab.Tactic.Omega

namespace BB6.CMod32
open BB6.CBack BB6.CRange

/-- A complete, all-natural inverse reset step for the 16 mod32 family. -/
theorem first_ancestor (t:Nat)
    (h:BB6CLine.Reach (64*t+33,96*t+52,0)) :
    BB6CLine.Reach (160*t+83,48*t+25,0) := by
  have hhub : BB6CLine.Reach (160*t+80,2,96*t+50) := by
    have hh : BB6CLine.Reach (64*t+33,(96*t+45)+7,0) := by
      have heq : (64*t+33,(96*t+45)+7,0)=(64*t+33,96*t+52,0) := by
        simp only [Prod.mk.injEq] <;> omega
      exact heq.symm ▸ h
    have hh2 := reached_zero_hub (64*t+33) (96*t+45) hh
    have heq : (64*t+33+(96*t+45)+2,2,(96*t+45)+5)=(160*t+80,2,96*t+50) := by
      simp only [Prod.mk.injEq]
      exact ⟨by omega, trivial⟩
    exact heq ▸ hh2
  have hh : BB6CLine.Reach (160*t+81,1,96*t+51) := by
    have hb : BB6CLine.Reach (160*t+80,2,(96*t+46)+4) := by
      have heq : (160*t+80,2,(96*t+46)+4)=(160*t+80,2,96*t+50) := by
        simp only [Prod.mk.injEq] <;> omega
      exact heq.symm ▸ hhub
    have hm : (160*t+80)%4 ≠ 2 := by omega
    have hv := reached_hub_prev (160*t+80) (96*t+46) hb hm
    have heq : (160*t+80+1,1,(96*t+46)+5)=(160*t+81,1,96*t+51) := by
      simp only [Prod.mk.injEq] <;> omega
    exact heq ▸ hv
  have hc : BB6CLine.Reach (160*t+81,1,(96*t+47)+4) := by
    have heq : (160*t+81,1,(96*t+47)+4)=(160*t+81,1,96*t+51) := by
      simp only [Prod.mk.injEq] <;> omega
    exact heq.symm ▸ hh
  rcases reached_one_high_or_reset (160*t+81) (96*t+47) hc with hp|⟨k,hk,hr⟩
  · have hd := reached_kzero_odd (160*t+82) (96*t+52) (by
      have heq : (160*t+81+1,0,(96*t+47)+5)=(160*t+82,0,96*t+52) := by
        simp only [Prod.mk.injEq] <;> omega
      exact heq ▸ hp)
    omega
  · have heq : (160*t+81+2,k,0)=(160*t+83,48*t+25,0) := by
      simp only [Prod.mk.injEq]
      exact ⟨trivial, by omega, trivial⟩
    exact heq ▸ hr


private theorem triple_congr {a b c d e f : Nat}
    (ha:a=d) (hb:b=e) (hc:c=f) :
    ((a,b,c):BB6.CReachBridge.S)=(d,e,f) := by
  cases ha; cases hb; cases hc; rfl

/-- A second forced inverse section, from the odd gate ancestor. -/
theorem second_ancestor (t:Nat)
    (h:BB6CLine.Reach (160*t+83,48*t+25,0)) :
    BB6CLine.Reach (104*t+52,76*t+37,0) := by
  have hhub : BB6CLine.Reach (208*t+103,2,48*t+23) := by
    have hi : BB6CLine.Reach (160*t+83,(48*t+18)+7,0) := by
      have heq : (160*t+83,(48*t+18)+7,0)=(160*t+83,48*t+25,0) := by
        apply triple_congr <;> omega
      exact heq.symm ▸ h
    have hh := reached_zero_hub (160*t+83) (48*t+18) hi
    have heq : (160*t+83+(48*t+18)+2,2,(48*t+18)+5)=(208*t+103,2,48*t+23) := by
      apply triple_congr <;> omega
    exact heq ▸ hh
  have hh1 : BB6CLine.Reach (208*t+104,1,48*t+24) := by
    have hi : BB6CLine.Reach (208*t+103,2,(48*t+19)+4) := by
      have heq : (208*t+103,2,(48*t+19)+4)=(208*t+103,2,48*t+23) := by
        apply triple_congr <;> omega
      exact heq.symm ▸ hhub
    have hh := reached_hub_prev (208*t+103) (48*t+19) hi (by omega)
    have heq : (208*t+103+1,1,(48*t+19)+5)=(208*t+104,1,48*t+24) := by
      apply triple_congr <;> omega
    exact heq ▸ hh
  have hh2 : BB6CLine.Reach (208*t+105,0,48*t+25) := by
    have hi : BB6CLine.Reach (208*t+104,1,(48*t+20)+4) := by
      have heq : (208*t+104,1,(48*t+20)+4)=(208*t+104,1,48*t+24) := by
        apply triple_congr <;> omega
      exact heq.symm ▸ hh1
    rcases reached_one_high_or_reset (208*t+104) (48*t+20) hi with hp | ⟨k,hk,hr⟩
    · have heq : (208*t+104+1,0,(48*t+20)+5)=(208*t+105,0,48*t+25) := by
        apply triple_congr <;> omega
      exact heq ▸ hp
    · omega
  have hh3 : BB6CLine.Reach (0,104*t+51,48*t+25) := by
    have hi : BB6CLine.Reach ((208*t+98)+7,0,(48*t+21)+4) := by
      have heq : ((208*t+98)+7,0,(48*t+21)+4)=(208*t+105,0,48*t+25) := by
        apply triple_congr <;> omega
      exact heq.symm ▸ hh2
    rcases reached_high_kzero_prev (208*t+98) (48*t+21) hi with ⟨k,hodd,hk,hr⟩
    have heq : (0,k,(48*t+21)+4)=(0,104*t+51,48*t+25) := by
      apply triple_congr <;> omega
    exact heq ▸ hr
  have hh4 : BB6CLine.Reach (104*t+48,3,152*t+73) := by
    have hi : BB6CLine.Reach (0,0+(104*t+48)+3,(48*t+21)+4) := by
      have heq : (0,0+(104*t+48)+3,(48*t+21)+4)=(0,104*t+51,48*t+25) := by
        apply triple_congr <;> omega
      exact heq.symm ▸ hh3
    have hh := reverse_high 0 0 (48*t+21) (104*t+48) hi
    have heq : (0+(104*t+48),0+3,(48*t+21)+(104*t+48)+4)=(104*t+48,3,152*t+73) := by
      apply triple_congr <;> omega
    exact heq ▸ hh
  have hhub2 : BB6CLine.Reach (104*t+49,2,152*t+74) := by
    have hi : BB6CLine.Reach (104*t+48,0+3,(152*t+69)+4) := by
      have heq : (104*t+48,0+3,(152*t+69)+4)=(104*t+48,3,152*t+73) := by
        apply triple_congr <;> omega
      exact heq.symm ▸ hh4
    have hh := reached_high_pred (104*t+48) 0 (152*t+69) hi
    have heq : (104*t+48+1,0+2,(152*t+69)+5)=(104*t+49,2,152*t+74) := by
      apply triple_congr <;> omega
    exact heq ▸ hh
  have hh5 : BB6CLine.Reach (104*t+50,1,152*t+75) := by
    have hi : BB6CLine.Reach (104*t+49,2,(152*t+70)+4) := by
      have heq : (104*t+49,2,(152*t+70)+4)=(104*t+49,2,152*t+74) := by
        apply triple_congr <;> omega
      exact heq.symm ▸ hhub2
    have hh := reached_hub_prev (104*t+49) (152*t+70) hi (by omega)
    have heq : (104*t+49+1,1,(152*t+70)+5)=(104*t+50,1,152*t+75) := by
      apply triple_congr <;> omega
    exact heq ▸ hh
  have hi : BB6CLine.Reach (104*t+50,1,(152*t+71)+4) := by
    have heq : (104*t+50,1,(152*t+71)+4)=(104*t+50,1,152*t+75) := by
      apply triple_congr <;> omega
    exact heq.symm ▸ hh5
  rcases reached_one_high_or_reset (104*t+50) (152*t+71) hi with hp | ⟨k,hk,hr⟩
  · have hs : BB6CLine.Reach ((104*t+44)+7,0,(152*t+72)+4) := by
      have heq : (104*t+50+1,0,(152*t+71)+5)=((104*t+44)+7,0,(152*t+72)+4) := by
        apply triple_congr <;> omega
      exact heq ▸ hp
    rcases reached_high_kzero_prev (104*t+44) (152*t+72) hs with ⟨k,hodd,hk2,_⟩
    omega
  · have heq : (104*t+50+2,k,0)=(104*t+52,76*t+37,0) := by
      apply triple_congr <;> omega
    exact heq ▸ hr

/-- New excluded infinite reset family in the previously surviving j=0 mod8 class. -/
theorem reset_mod32_sixteen_unreachable (t:Nat) :
    ¬ BB6CLine.Reach (64*t+33,96*t+52,0) := by
  intro h
  have h1 := first_ancestor t h
  have h2 := second_ancestor t h1
  have hb := reached_odd_zero_mod4_hole (104*t+52) (76*t+37) h2 (by omega) (by omega)
  omega

#print axioms second_ancestor
#print axioms reset_mod32_sixteen_unreachable
#print axioms first_ancestor
end BB6.CMod32
