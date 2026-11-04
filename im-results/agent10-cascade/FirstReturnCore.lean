import SourceMacro
namespace CascadeResetInverse
open CascadeSource

/-- The exact exit on the first failed high sweep, including the two low-phase cases. -/
theorem exit (p h k : Nat) (hp : 1≤p)
   (hlow : 4*p≤h+k+4) (hhigh : h+k+5<8*p)
   (hnot : h+k+4≠4*p) :
   Cstep (4*p-2) (2*h+2*k+9-8*p) =
     some (4*p+(h+k)/2, 2*((h+k)%2)) := by
  have hpos : 3≤2*h+2*k+9-8*p := by omega
  have hlow2 : 2*(4*p-2) > (2*h+2*k+9-8*p)-2 := by omega
  have hodd : ((2*h+2*k+9-8*p)-2)%2=1 := by omega
  have hsum : 6*(4*p-2)+((2*h+2*k+9-8*p)-2)+5=16*p+2*(h+k) := by omega
  have hdiv : (16*p+2*(h+k))/4=4*p+(h+k)/2 := by omega
  have hmod : (16*p+2*(h+k))%4=2*((h+k)%2) := by omega
  simp [Cstep,show (2*h+2*k+9-8*p)≠0 by omega,
        show (2*h+2*k+9-8*p)≠1 by omega,
        show ¬(2*(4*p-2)≤(2*h+2*k+9-8*p)-2) by omega,
        hodd,hsum,hdiv,hmod]

/-- For q odd, the B=2 drain resets on its very next episode. -/
theorem drain_odd (q : Nat) (hq : 5≤q) (hpar : q%2=1) :
    Cstep (q-3) 2 = some ((3*q-5)/2,0) := by
  have hguard : ¬(2*(q-3)≤0) := by omega
  have heven : (6*(q-3)+8)%4=0 := by omega
  have hcalc : (6*(q-3)+8)/4=(3*q-5)/2 := by omega
  simp [Cstep,hguard,heven,hcalc]

/-- For q even, the B=2 drain scales q by 3/2 and keeps B=2. -/
theorem drain_even (q : Nat) (hq : 4≤q) (hpar : q%2=0) :
    Cstep (q-3) 2 = some (3*q/2-3,2) := by
  have hguard : ¬(2*(q-3)≤0) := by omega
  have hmod : (6*(q-3)+8)%4=2 := by omega
  have hcalc : (6*(q-3)+8)/4=3*q/2-3 := by omega
  simp [Cstep,hguard,hmod,hcalc]

#print axioms drain_odd
#print axioms drain_even
#print axioms exit
end CascadeResetInverse
