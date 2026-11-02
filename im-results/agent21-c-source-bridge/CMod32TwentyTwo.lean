import CMod128Six
import Lean.Elab.Tactic.Omega

namespace BB6.CMod32TwentyTwo
open BB6.CBack

private theorem eq3 {a b c d e f : Nat}
    (h1:a=d) (h2:b=e) (h3:c=f) :
    ((a,b,c):Nat×Nat×Nat)=(d,e,f) := by
  cases h1; cases h2; cases h3; rfl

/-- Uniform first reset inversion for indices j=16s+6. -/
theorem first_ancestor (s:Nat)
    (h:BB6CLine.Reach (32*s+13,48*s+22,0)) :
    BB6CLine.Reach (80*s+33,24*s+10,0) := by
  have hub : BB6CLine.Reach (32*s+13+(48*s+22)-5,2,(48*s+22)-2) →
      BB6CLine.Reach (32*s+13+(48*s+22)-4,1,(48*s+22)-1) := by
    intro hh
    have he : (32*s+13+(48*s+22)-5,2,(48*s+22)-2) =
        (8*(10*s+3)+6,2,4*(12*s+4)+4) := by apply eq3 <;> omega
    have hp := BB6.CMod128Six.hub_six_forced (10*s+3) (12*s+4) (he ▸ hh)
    have he2 : (8*(10*s+3)+7,1,4*(12*s+4)+5) =
        (32*s+13+(48*s+22)-4,1,(48*s+22)-1) := by apply eq3 <;> omega
    exact he2 ▸ hp
  have h1 := BB6.CMod128Six.even_backward (32*s+13) (48*s+22) (by omega) (by omega) h hub
  have he : (32*s+13+(48*s+22)-2,(48*s+22)/2-1,0) =
      (80*s+33,24*s+10,0) := by apply eq3 <;> omega
  exact he ▸ h1

/-- The second sweep can also be uniformly inverted in every 16s+6 class. -/
theorem second_ancestor (s:Nat)
    (h:BB6CLine.Reach (80*s+33,24*s+10,0)) :
    BB6CLine.Reach (104*s+41,12*s+4,0) := by
  have hub : BB6CLine.Reach (80*s+33+(24*s+10)-5,2,(24*s+10)-2) →
      BB6CLine.Reach (80*s+33+(24*s+10)-4,1,(24*s+10)-1) := by
    intro hh
    have he : (80*s+33+(24*s+10)-5,2,(24*s+10)-2) =
        (8*(13*s+4)+6,2,4*(6*s+1)+4) := by apply eq3 <;> omega
    have hp := BB6.CMod128Six.hub_six_forced (13*s+4) (6*s+1) (he ▸ hh)
    have he2 : (8*(13*s+4)+7,1,4*(6*s+1)+5) =
        (80*s+33+(24*s+10)-4,1,(24*s+10)-1) := by apply eq3 <;> omega
    exact he2 ▸ hp
  have h1 := BB6.CMod128Six.even_backward (80*s+33) (24*s+10) (by omega) (by omega) h hub
  have he : (80*s+33+(24*s+10)-2,(24*s+10)/2-1,0) =
      (104*s+41,12*s+4,0) := by apply eq3 <;> omega
  exact he ▸ h1

/-- Third inverse section if s>=1, using the previous universal hub lemma. -/
theorem third_ancestor (s:Nat) (hs:1≤s)
    (h:BB6CLine.Reach (104*s+41,12*s+4,0)) :
    BB6CLine.Reach (116*s+43,6*s+1,0) := by
  have hub : BB6CLine.Reach (104*s+41+(12*s+4)-5,2,(12*s+4)-2) →
      BB6CLine.Reach (104*s+41+(12*s+4)-4,1,(12*s+4)-1) := by
    intro hh
    have he : (104*s+41+(12*s+4)-5,2,(12*s+4)-2) =
        (116*s+40,2,(12*s-2)+4) := by apply eq3 <;> omega
    have hp := reached_hub_prev (116*s+40) (12*s-2) (he ▸ hh) (by omega)
    have he2 : (116*s+41,1,(12*s-2)+5) =
        (104*s+41+(12*s+4)-4,1,(12*s+4)-1) := by apply eq3 <;> omega
    exact he2 ▸ hp
  have h1 := BB6.CMod128Six.even_backward (104*s+41) (12*s+4) (by omega) (by omega) h hub
  have he : (104*s+41+(12*s+4)-2,(12*s+4)/2-1,0) =
      (116*s+43,6*s+1,0) := by apply eq3 <;> omega
  exact he ▸ h1

/-- The odd reset after three forced even contractions is impossible
when the original index is 22 modulo 32. -/
theorem last_unreachable (u:Nat) :
    ¬ BB6CLine.Reach (232*u+159,12*u+7,0) := by
  intro h
  have hhub : BB6CLine.Reach (244*u+161,2,12*u+5) := by
    have hi : BB6CLine.Reach (232*u+159,(12*u)+7,0) := by simpa using h
    have hp := reached_zero_hub (232*u+159) (12*u) hi
    have he : (232*u+159+12*u+2,2,12*u+5) = (244*u+161,2,12*u+5) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have h1 : BB6CLine.Reach (244*u+162,1,12*u+6) := by
    have hi : BB6CLine.Reach (244*u+161,2,(12*u+1)+4) := by simpa using hhub
    have hp := reached_hub_prev (244*u+161) (12*u+1) hi (by omega)
    have he : (244*u+161+1,1,12*u+1+5) = (244*u+162,1,12*u+6) := by
      apply eq3 <;> omega
    exact he ▸ hp
  have hi : BB6CLine.Reach (244*u+162,1,(12*u+2)+4) := by simpa using h1
  rcases reached_one_high_or_reset (244*u+162) (12*u+2) hi with hp | ⟨k,hk,hr⟩
  · have hh : BB6CLine.Reach ((244*u+156)+7,0,(12*u+3)+4) := by
      have he : (244*u+162+1,0,(12*u+2)+5) =
            ((244*u+156)+7,0,(12*u+3)+4) := by apply eq3 <;> omega
      exact he ▸ hp
    rcases reached_high_kzero_prev (244*u+156) (12*u+3) hh with ⟨k,ho,hk,_⟩
    omega
  · omega

/-- A new complete symbolic reset-gateway exclusion: j=32u+22. -/
theorem reset_mod32_twentytwo_unreachable (u:Nat) :
    ¬ BB6CLine.Reach (64*u+45,96*u+70,0) := by
  intro h
  have h0 := first_ancestor (2*u+1) (by
    have he : (32*(2*u+1)+13,48*(2*u+1)+22,0) = (64*u+45,96*u+70,0) := by
      apply eq3 <;> omega
    exact he.symm ▸ h)
  have h1 := second_ancestor (2*u+1) h0
  have h2 := third_ancestor (2*u+1) (by omega) h1
  have he : (116*(2*u+1)+43,6*(2*u+1)+1,0)=(232*u+159,12*u+7,0) := by
    apply eq3 <;> omega
  exact last_unreachable u (he ▸ h2)

#print axioms reset_mod32_twentytwo_unreachable
end BB6.CMod32TwentyTwo
