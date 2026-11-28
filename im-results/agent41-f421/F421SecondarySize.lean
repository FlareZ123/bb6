import F421SecondaryQGrowth

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

def prefixMass (a b : Nat) (cs : List PC) := a+b+pSum cs+qSum cs

/-- Exact aggregate prefix growth in one secondary cycle, independent of
    terminal deletions except via the number of surviving P-runs. -/
theorem prefixMassIdentity (a b : Nat) (cs : List PC)
    (ha : a=2*2^cs.length-1)
    (hp : pSum ((sNext b cs).2.2)=pSum cs+(2*2^cs.length-1)+3)
    (hq : qSum ((sNext b cs).2.2)=qSum cs+b+
         2*(2^cs.length-2^(drain 0 0 (dec cs)).1.length))
    (hl : (drain 0 0 (dec cs)).1.length≤cs.length) :
    let (a',b',ys) := sNext b cs
    prefixMass a' b' ys = prefixMass a b cs + 2*2^cs.length+
      8*2^(drain 0 0 (dec cs)).1.length+1 := by
  rcases he : drain 0 0 (dec cs) with ⟨as,A,r⟩
  rw [he] at hl
  simp only [Prod.fst] at hl
  have hs : 2^as.length≤2^cs.length :=
    Nat.pow_le_pow_right (n:=2) (by decide) hl
  have hd : 0<2^as.length := Nat.pow_pos (by decide)
  have hm : 0<2^cs.length := Nat.pow_pos (by decide)
  simp only [sNext,he,Prod.fst,Prod.snd] at hp hq ⊢
  unfold prefixMass
  omega

#print axioms prefixMassIdentity
end F421SecondaryLifetimes
