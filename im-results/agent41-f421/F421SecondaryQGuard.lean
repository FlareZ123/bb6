import F421SecondaryQGrowth
import F421SecondaryConservationGuard

namespace BB6Coverage.Agent41F421.EpochWords
open F421TertiaryGuard (QBudget drain)
open F421SecondaryLifetimes

theorem qAtLeastBudget (k B : Nat) (cs : List PC)
    (hq : QBudget k B cs) : qAtLeast B cs := by
  induction cs generalizing B with
  | nil => trivial
  | cons c cs ih =>
    refine ⟨?_,ih (2*B) hq.2⟩
    have h := hq.1
    omega

theorem decQBudget (k B : Nat) (cs : List PC)
    (hq : QBudget k B cs) : QBudget k B (dec cs) := by
  induction cs generalizing B with
  | nil => trivial
  | cons c cs ih => exact ⟨hq.1,ih (2*B) hq.2⟩

/-- Exact aggregate Q-mass law for every source-level guarded secondary
    cycle. Deletion and merge patterns influence only the survivor count. -/
theorem secondaryQMassGuarded (k a b : Nat) (cs : List PC)
    (hg : sPrimary (k+1) a b cs) :
    qSum ((sNext b cs).2.2) =
      qSum cs+b+2*(2^cs.length-2^(drain 0 0 (dec cs)).1.length) := by
  rcases hg with ⟨ha,hb,hp,hq,hlen⟩
  have hcap := capPOfPGood k 1 cs (by decide) hp
  have htime := drainHorizon 1 0 cs (by decide) hcap
  simp only [Nat.one_mul,Nat.sub_self] at htime
  have hqa := F421TertiaryGuard.drainQ (dec cs) 1 1 1 0 0
     (by decide) (by decide) (decQBudget 1 1 cs hq)
  rcases he : drain 0 0 (dec cs) with ⟨as,A,r⟩
  rw [he] at hqa
  rcases hqa with ⟨hqa,hlenA,hcount⟩
  have hqa' : qAtLeast 1 as := qAtLeastBudget 2 1 as hqa
  have hlen' : as.length≤cs.length := by
    simpa [dec] using hlenA
  have hD : 2^as.length≤2^cs.length :=
    Nat.pow_le_pow_right (n:=2) (by decide) hlen'
  have hM : 0<2^cs.length := Nat.pow_pos (by decide)
  have hb' : 2^cs.length≤b+1 := by
    have h := hb
    omega
  have h := secondaryQMass b cs hcap htime (by rw [he]; exact hqa')
    (by rw [he]; exact hD) hb'
  exact h

#print axioms secondaryQMassGuarded
end BB6Coverage.Agent41F421.EpochWords
