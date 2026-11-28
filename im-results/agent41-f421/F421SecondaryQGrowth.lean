import F421SecondaryQMass

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

def qAtLeast (B : Nat) : List PC → Prop
  | [] => True
  | c::cs => B≤c.q ∧ qAtLeast (2*B) cs

/-- Every exact-survivor-or-terminal-deletion drain exhausts the entire
    positional carry horizon, independent of all Q values. -/
theorem drainHorizon (B carry : Nat) (cs : List PC)
    (hB : 0<B) (hp : capP B (pProjection cs)) :
    (drain (B-1) carry (dec cs)).2.1 = B*2^cs.length-1 := by
  induction cs generalizing B carry with
  | nil => simp [drain,dec]
  | cons c cs ih =>
    have ht : capP (2*B) (pProjection cs) := hp.2
    have hb2 : 0<2*B := by omega
    have hcap : 2*(B-1)+1=2*B-1 := by omega
    have hpow : B*2^(cs.length+1)=(2*B)*2^cs.length := by
      rw [Nat.pow_succ]; ac_rfl
    rcases hp.1 with h|h
    · have hle : c.p-1≤2*B-1 := by omega
      have hstep : B-1+(c.p-1+1)/2=2*B-1 := by omega
      have hr := ih (2*B) (carry+c.q+B) hb2 ht
      simp only [dec,List.map_cons,drain,hcap,ite_eq_left hle,hstep,
        show (c.p-1+1)/2=B by omega,List.length_cons,hpow]
      rw [show B-1+B=2*B-1 by omega]
      simpa only [dec] using hr
    · have hnot : ¬c.p-1≤2*B-1 := by omega
      have hr := ih (2*B) 0 hb2 ht
      simp only [dec,List.map_cons,drain,hcap,ite_eq_right hnot,
        List.length_cons,hpow]
      simpa only [dec] using hr

/-- The drain cannot create more P cells than it started with. -/
theorem drainLengthLe (h carry : Nat) (cs : List PC) :
    (drain h carry cs).1.length≤cs.length := by
  induction cs generalizing h carry with
  | nil => simp [drain]
  | cons c cs ih =>
    by_cases hc : c.p≤2*h+1
    · simp only [drain,ite_eq_left hc,List.length_cons]
      have ht := ih (h+(c.p+1)/2) (carry+c.q+(c.p+1)/2)
      omega
    · simp only [drain,ite_eq_right hc,List.length_cons]
      have ht := ih (2*h+1) 0
      omega

theorem trimQMass (B : Nat) (cs : List PC) (hq : qAtLeast B cs) :
    qSum (trimQ B cs)+qBudgetSum B cs=qSum cs := by
  induction cs generalizing B with
  | nil => rfl
  | cons c cs ih =>
    have h := ih (2*B) hq.2
    simp only [trimQ,qSum,List.map_cons,List.sum_cons,qBudgetSum]
    change (c.q-B)+qSum (trimQ (2*B) cs) + (B+qBudgetSum (2*B) cs) = c.q + qSum cs
    have hq0 := hq.1
    omega

/-- Exact Q mass of one source secondary cycle, given the already proved
    full A-drain horizon and survivor Q budgets. -/
theorem secondaryQMass (b : Nat) (cs : List PC)
    (hp : capP 1 (pProjection cs))
    (hH : (drain 0 0 (dec cs)).2.1=2^cs.length-1)
    (hQ : qAtLeast 1 (drain 0 0 (dec cs)).1)
    (hD : 2^(drain 0 0 (dec cs)).1.length ≤ 2^cs.length)
    (hb : 2^cs.length ≤ b+1) :
    qSum ((sNext b cs).2.2)=qSum cs+b+2*(2^cs.length-2^(drain 0 0 (dec cs)).1.length) := by
  rcases he : drain 0 0 (dec cs) with ⟨as,A,r⟩
  rw [he] at hH hQ hD
  simp only [Prod.fst,Prod.snd] at hH hQ hD
  have hmass := drainQmass 1 0 cs (by decide) hp
  rw [he] at hmass
  simp only [Prod.fst,Prod.snd,Nat.zero_add] at hmass
  have htrim := trimQMass 1 as hQ
  have hbudget := qBudgetPow 1 as
  have hbudgetOld := qBudgetPow 1 cs
  simp only [Nat.one_mul] at hbudget hbudgetOld
  have hallow : 2^as.length≤b+1+A+r := by omega
  unfold sNext
  rw [he]
  simp only [Prod.fst,Prod.snd,qSum,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
  change qSum (trimQ 1 as)+(b+1+A+r-2^as.length) =
    qSum cs+b+2*(2^cs.length-2^as.length)
  omega

#print axioms drainHorizon
#print axioms drainLengthLe
#print axioms trimQMass
#print axioms secondaryQMass
end F421SecondaryLifetimes
